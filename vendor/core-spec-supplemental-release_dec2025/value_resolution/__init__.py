from enum import IntEnum

import value_resolution.value_clips as value_clips
from composition.stage import Layer, Prim, Spec, Stage, Tokens
from file_formats.parsers.binary.types import SpecForm, ValueType
from value_resolution.time_code import timeCode


class InterpolationType(IntEnum):
    """Interpolation Type Used"""

    Held = 0
    Linear = 1
    Spline = 2

    def __repr__(self):
        return self.name


class ValueResolutionProcess(IntEnum):
    """Value Resolution Process Used or error"""

    Default = 0
    DefaultWithTime = 1
    TimeSamples = 2
    Splines = 3
    ValueClips = 4
    Fallback = 5
    Sentinel = 6
    Error = 7

    def __repr__(self):
        return self.name


class ValueResolution:
    """value resolution for properties"""

    # convenience for debugging...
    TIME = 0
    DATA = 1

    fallbackVal: float = 0.0
    sentinel: float = float("nan")
    fallback_supported: bool = True

    def __init__(self, stage: Stage, prim: Spec):
        self._stage = stage
        self._interpolationType = InterpolationType.Linear
        self._prim = prim

    @staticmethod
    def _linear_interpolate(lowertime, lowervalue, uppertime, uppervalue, time):
        interpolate_time = (time - lowertime) / (uppertime - lowertime)
        return lowervalue + interpolate_time * (uppervalue - lowervalue)

    def _interpolate(self, timeSamples, time):
        # layout of timeSamples [0] is the time, and [1] is the Type
        # [(Time, Type:Value)]
        # assumes timeSamples is sorted by time
        minTime = timeSamples[0][self.TIME]
        maxTime = timeSamples[-1][self.TIME]

        # calculate pre and post values
        if time < minTime:
            return timeSamples[0][self.DATA].value
        if time > maxTime:
            return timeSamples[-1][self.DATA].value

        """
        # Linear search of the lower bound time sample
        lower_bound_index = None
        for index, (tc, value) in enumerate(timeSamples):
            if time < tc:
                 lower_bound_index = index -1
                 break
                 
        if lower_bound_index is None:
            lower_bound_index = len(timeSamples) - 2

        #TODO: Held is not correct here, it has to return the same value if time is the same as authored time code
        if self.interpolationType == InterpolationType.Held:
            return timeSamples[lower_bound_index][self.DATA].value

        else: # Assuming interpolation is linear
            ts0 = timeSamples[lower_bound_index]
            ts1 = timeSamples[lower_bound_index + 1]
            return self._linear_interpolate(ts0[self.TIME],ts0[self.DATA].value,ts1[self.TIME],ts1[self.DATA].value,time)  
        
        """

        # find where "time" intersects timeSamples
        for time_data in timeSamples:
            if time_data[self.TIME] == time:
                return time_data[self.DATA].value
            if time_data[self.TIME] > time:
                prev = timeSamples[timeSamples.index(time_data) - 1]

                if self._interpolationType == InterpolationType.Held:
                    return prev[self.DATA].value
                else:
                    # linear interpolation
                    previous_time = prev[self.TIME]
                    previous_value = prev[self.DATA].value
                    current_time = time_data[self.TIME]
                    current_value = time_data[self.DATA].value
                    return self._linear_interpolate(previous_time, previous_value, current_time, current_value, time)

        return None

    def _process_default(self, spec: Spec):
        if def_value := spec.fields.get("default"):
            return def_value.value
        return None

    def _process_timesamples(self, spec: Spec, time: float):
        if timeSamples := spec.fields.get(Tokens.timeSamples):
            timeSamplesData = timeSamples.value
            timeSamplesData.sort(key=lambda tc: tc[self.TIME])
            return self._interpolate(timeSamplesData, time)

        return None

    def _process_splines(self, spec: Spec, time: float):
        # TODO: implement spline processing
        return None

    def _process_fallback(self, spec: Spec) -> tuple[float, ValueResolutionProcess]:
        if self.fallback_supported:
            return self.fallbackVal, ValueResolutionProcess.Fallback
        else:
            return self.sentinel, ValueResolutionProcess.Sentinel

    def _get_clips_active(self, spec: Spec, path):
        clip = value_clips.setup_value_clip(self._stage, spec)
        if clip.is_valid() and clip.is_attribute_supported(path):
            return True

        return False

    def _process_spec_stack(self, prim_path: str, attribute: str, time: timeCode):
        """Iterate the spec stack looking for opinions that contribute to resolving
        time samples.  THe local stack has the highest priority followed by Value Clips
        If nothing is authored on the local stack check Value CLips as they might have been authored
        on the prim itself.  Once the appropriate spec has been found use the process as outlined in
        _process_value()"""

        prim: Prim = self._stage.root_layer.prims[prim_path]
        prim.specs.sort()
        full_attribute_path = ".".join((prim_path, attribute))

        # iterate the prim stack for all specs that have an opinion
        for spec in prim.specs:
            prop_value = spec.fields.get(Tokens.properties)

            if not prop_value:
                # check value clips
                if self._get_clips_active(spec, full_attribute_path):
                    ## Use full path as clips are in a different stage/file
                    if (val := self._process_value(spec, full_attribute_path, time)) is not None:
                        return val
                continue

            # check if the spec has our attribute
            properties = prop_value.value
            if attribute not in properties:
                # Always check for a Clip
                if self._get_clips_active(spec, full_attribute_path):
                    ## Use full path as clips are in a different stage/file can't simply use the spec
                    if (val := self._process_value(spec, full_attribute_path, time)) is not None:
                        return val
                continue

            prop_path = full_attribute_path
            prop_spec = spec.layer._scene.get(prop_path)

            if (val := self._process_value(prop_spec, prop_path, time)) is not None:
                return val

            """
            For now I don't think this is even necessary 
            # Always check for Clip
            if self._get_clips_active(spec, full_attribute_path):
                # Use full path as clips are in a different stage/file
                if (val := self._process_value(spec, full_attribute_path, time)) is not None:
                    return val
            """
        return None

    def _process_value(self, spec: Spec, spec_path, time: timeCode) -> tuple[float, ValueResolutionProcess]:
        # if default timecode is specified process default with fallback
        if time.is_default():
            val = self._process_default(spec)
            if val:
                return val, ValueResolutionProcess.Default
            else:
                val = self._process_fallback(spec)
                return self.fallbackVal, ValueResolutionProcess.Fallback

        # process timeSamples
        if (val := self._process_timesamples(spec, time.get_value())) is not None:
            return val, ValueResolutionProcess.TimeSamples

        # process Splines
        if (val := self._process_splines(spec, time.get_value())) is not None:
            return val, ValueResolutionProcess.Splines

        # process default
        if (val := self._process_default(spec)) is not None:
            return val, ValueResolutionProcess.DefaultWithTime

        # Process value clips
        if clips := self.initialise_clips(spec):
            if clips.is_valid():
                # ValueClipp take a path to the attribute as the data is another stage and is needed for remapping
                # to the clip attribute

                # Can use the TimeSamples version of this method to use the built-in `_process_timesamples()`
                if (val := clips.get_value_at_stagetime(time, spec_path)) is not None:
                    return val, ValueResolutionProcess.ValueClips

        return self.sentinel, ValueResolutionProcess.Error

    def get_value(self, spec: Spec, time: timeCode) -> tuple[float, ValueResolutionProcess]:
        """Get the resolved value for the given spec at the specified time code.  The order of processing is:
        1. If time is default (NaN), process default value
        2. Process timeSamples
        3. Process splines
        4. Process default with time
        5. Process value clips
        6. Process Fallback value
        7. Sentinel value

        Args:
            spec (Spec): The spec of the property to resolve
            time (timeCode): The time code at which to resolve the value

        Returns:
            tuple[float, ValueResolutionProcess]: The resolved value and the process used"""

        # Do some basic validation
        if spec is None or spec.form is not SpecForm.Attribute:
            return self.fallbackVal, ValueResolutionProcess.Error

        # Only float values are currently supported in example
        """
        if spec.fields["typeName"].value != "float":
            return None
        """

        # Get the path for the spec used by ValueClips
        spec_path = ""
        for path, data in self._stage.scene.items():
            if data == spec:
                spec_path = path

        prim, attribute = spec_path.split(".", 1)

        if (value := self._process_spec_stack(prim, attribute, time)) is not None:
            return value[0], value[1]

        # system or attribute defined fallback
        if (value := self._process_fallback(spec)) is not None:
            return value[0], value[1]

        # if all else fails return a common default "sentinel"
        return self.sentinel, ValueResolutionProcess.Sentinel

    @property
    def interpolation_type(self) -> InterpolationType:
        return self._interpolationType

    @interpolation_type.setter
    def interpolation_type(self, interp_type: InterpolationType):
        self._interpolationType = interp_type

    def initialise_clips(self, spec: Spec) -> value_clips.ValueClip:
        # Will use the first clip found, either default or the first of a sorted list.
        """This could be manipulated by ordering the clip_sets or explicitly accessing by name
        The ValueClipContainer provides access either by index or by name. 'setup_value_clip' will default
        to the first entry without apply reordering"""
        return value_clips.setup_value_clip(self._stage, spec)


if __name__ == "__main__":
    # Needs a fully qualified path to the file otherwise Stage.Open will force its own directory...
    filepath = "./tests/assets/timeSamples/entry.usd"
    if not os.path.exists(filepath):
        filepath = os.path.abspath(os.path.join(os.path.dirname(__file__), filepath))

    stage = Stage.Open(filepath)
    root = stage.get("/Root")
    attribute = stage.get("/Root.root")
    value_resolution = ValueResolution(stage, root)
    val = value_resolution.get_value(attribute, timeCode.default())
    print(f"Value: {val[0]}, Process: {val[1].name}")
