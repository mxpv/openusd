import os

from composition.stage import Spec, Stage
from file_formats.parsers.binary.types import SpecForm
from value_resolution.time_code import timeCode


def map_stagetime_to_cliptime(stagetime, times_array):
    """
    Map a stagetime to cliptime using the times array.
    Handles jump discontinuities where duplicate stagetimes represent:
    - First entry: "upto" value (stagetime - timeCode.safe_step())
    - Second entry: actual value at stagetime

    Args:
        stagetime (float): The stage time to map
        times_array (list): Array of [stagetime, cliptime] pairs

    Returns:
        #TODO Validate out of range return.
        float: The corresponding cliptime, or None if stagetime is out of range
        If the return value is None the calling code should assume stagetime.  None simply
        implies something in the mapping failed.
    """

    # No mapping specified, simply return the stagetime
    if not times_array or len(times_array) == 0:
        return stagetime

    # Process the times array to handle jump discontinuities
    processed_times = []

    i = 0
    while i < len(times_array):
        stage_t, clip_t = times_array[i]

        # Check if there's a duplicate stagetime (jump discontinuity)
        if i + 1 < len(times_array) and times_array[i + 1][0] == stage_t:
            # First entry is "upto" - use safe_step to make it slightly less than stagetime
            safe_time = timeCode.safe_step(stage_t, step_back=True)
            processed_times.append([safe_time.get_value(), clip_t])
            # Second entry is the actual value at stagetime
            processed_times.append([times_array[i + 1][0], times_array[i + 1][1]])
            i += 2  # Skip both entries
        else:
            # No duplicate, add as-is
            processed_times.append([stage_t, clip_t])
            i += 1

    # Sort processed times by stagetime to ensure proper ordering
    sorted_times = sorted(processed_times, key=lambda x: x[0])

    # Check if stagetime is before the first entry
    if stagetime < sorted_times[0][0]:
        return sorted_times[0][0]  # return the first available clip time

    # Check if stagetime is after the last entry
    if stagetime > sorted_times[-1][0]:
        return sorted_times[-1][0]  # return the first available clip time

    # Find exact match (or very close match for epsilon values)
    epsilon = 1e-9  # Default epsilon value for comparison
    for stage_t, clip_t in sorted_times:
        if abs(stagetime - stage_t) < epsilon / 2:
            return clip_t

    # Find the two points to interpolate between
    for i in range(len(sorted_times) - 1):
        stage_t1, clip_t1 = sorted_times[i]
        stage_t2, clip_t2 = sorted_times[i + 1]

        if stage_t1 <= stagetime <= stage_t2:
            # Linear interpolation between the two points
            if abs(stage_t2 - stage_t1) < epsilon:  # Avoid division by very small numbers
                return clip_t1

            # Interpolate: cliptime = clip_t1 + (stagetime - stage_t1) * (clip_t2 - clip_t1) / (stage_t2 - stage_t1)
            ratio = (stagetime - stage_t1) / (stage_t2 - stage_t1)
            cliptime = clip_t1 + ratio * (clip_t2 - clip_t1)
            return cliptime

    return None


def condense_timesamples(timesamples: list) -> list:
    """Simply flatten the data into a basic list removing the ValueRep"""

    time_value_pairs = []

    for time_float, data in timesamples:
        try:
            time_value_pairs.append((time_float, data.value))
        except ValueError:
            continue  # Skip invalid time entries

    return time_value_pairs


def get_value_from_timesamples(cliptime: float, timesamples: list):
    """
    Retrieve a value from timeSamples using linear interpolation.

    Args:
        cliptime : The clip time calculated from the mapping
        timesamples : times value to sample from

    Returns:
        float: The interpolated value, or None if cliptime is out of range
    """
    if len(timesamples) == 0:
        return None

    time_value_pairs = condense_timesamples(timesamples)

    if not time_value_pairs:
        return None

    # Sort by time
    time_value_pairs.sort(key=lambda x: x[0])

    # Check if cliptime is before the first sample
    if cliptime < time_value_pairs[0][0]:
        return time_value_pairs[0][1]  # Return first value

    # Check if cliptime is after the last sample
    if cliptime > time_value_pairs[-1][0]:
        return time_value_pairs[-1][1]  # Return last value

    # Find exact match
    for time_val, value in time_value_pairs:
        if cliptime == time_val:
            return value

    # Find the two points to interpolate between
    for i in range(len(time_value_pairs) - 1):
        time1, value1 = time_value_pairs[i]
        time2, value2 = time_value_pairs[i + 1]

        # Only linear is supported for now.
        # To use the time samples code in ValueResolution use ValueClip.get_timesamples_at_stagetime()
        if time1 <= cliptime <= time2:
            # Linear interpolation
            if time2 == time1:  # Avoid division by zero
                return value1

            ratio = (cliptime - time1) / (time2 - time1)
            interpolated_value = value1 + ratio * (value2 - value1)
            return interpolated_value

    return None


class ClipDataLoader:
    """
    A super basic class to handle loading of (USD) clip data and manifest files.
    Attribute inspection happens via the manifest file
    """

    def __init__(self, manifest_path, base_directory):
        """
        Initialize the ClipLoader.

        Args:
            manifest_path (str): Path to the manifest file containing supported attributes.
            If None, no attribute validation will be performed by the clip framework. The clips
            will be loaded and attributes verified then.
        """
        self._base_directory = base_directory

        self._clip_cache = {}  # Cache for loaded clip data
        self._manifest_cache = None  # Cache for manifest data
        self._manifest_path = manifest_path

    def load_usd_clip_data(self, asset_path):
        """
        Load USD clip data from file, with caching to avoid repeated file reads.

        Args:
            asset_path (str): Path to the clip file (relative or absolute)

        Returns:
            Stage: The loaded clip data, or None if loading failed
        """
        if asset_path in self._clip_cache:
            return self._clip_cache[asset_path]

        # Determine the full file path
        if os.path.isabs(asset_path):
            file_path = asset_path
        else:
            file_path = os.path.join(self._base_directory, asset_path)

        if not os.path.isfile(file_path):
            print(f"File '{file_path}' not found, but could still be loaded due to formatting issues...")

        clip_data = Stage.Open(file_path)
        if clip_data:
            # simple cache it
            self._clip_cache[asset_path] = clip_data

        return clip_data

    def get_clip_data_for_resolution(self, asset_path, attribute_name):
        """
        Get specific attribute data from a clip file, loading only when needed.

        Args:
            asset_path (str): Path to the clip file
            attribute_name (str): Name of the attribute to extract.  This needs to be
            fully formed name e.g "/Root.attribute"

        Returns:
            dict: The attribute data (including timeSamples), or None if not found
        """
        clip_data = self.load_usd_clip_data(asset_path)
        if not clip_data:
            return None

        # access the timesamples for the attribute
        spec = clip_data.get(attribute_name)
        if spec is None:
            return None

        if timeSamples := spec.fields.get("timeSamples"):
            return timeSamples

        return None

    def load_manifest(self) -> Stage:
        """
        Load the manifest file containing supported attributes.

        Returns:
            dict: The manifest data, or None if loading failed or no manifest path set
        """
        if not self._manifest_path:
            return None

        if self._manifest_cache is not None:
            return self._manifest_cache

        # Determine the full file path for manifest
        if os.path.isabs(self._manifest_path):
            manifest_file_path = self._manifest_path
        else:
            manifest_file_path = os.path.join(self._base_directory, self._manifest_path)

        if not os.path.isfile(manifest_file_path):
            print(f"File '{manifest_file_path}' not found...")
            return None

        # Load the manifest data
        manifest_data = Stage.Open(manifest_file_path)
        self._manifest_cache = manifest_data

        return manifest_data

    def clear_cache(self):
        """Clear both clip data cache and manifest cache."""
        self._clip_cache.clear()
        self._manifest_cache = None

    def is_clip_loaded(self, clip_path):
        """Simple test to see if clips have been loaded, useful to see if clips have been loaded
        before they should, for example when mainfests are missing"""

        return clip_path in self._clip_cache


class ValueClipContainer:
    """
    A container class to manage multiple ValueClip instances from a clips dictionary.
    Provides access to clips by name with 'default' as the fallback.  This allow processing
    of clip_sets
    """

    def __init__(self, stage: Stage = None, clips_dict=None):
        """
        Initialize a ValueClipContainer instance.

        Args:
            stage (Stage): The active tage
            clips_dict (dict): Dictionary containing all clip definitions
        """
        self._clips = {}
        self._stage = stage

        if clips_dict:
            self._load_clips_from_dict(clips_dict)

    def _load_clips_from_dict(self, clips_dict):
        """
        Load all clips from the clips dictionary, sorted lexicographically by clip name.

        Args:
            clips_dict (dict): Dictionary containing clip definitions
        """
        # Sort clip names lexicographically before processing
        for clip_name in sorted(clips_dict.keys()):
            clip_data = clips_dict[clip_name]
            if hasattr(clip_data, "value"):
                clip_data = clip_data.value

            value_clip = ValueClip(self._stage, clip_data)
            if value_clip.is_valid():
                self._clips[clip_name] = value_clip
            else:
                print(f"Failed to create valid ValueClip for '{clip_name}'")

    def get_clip(self, name=None):
        """
        Get a ValueClip by name. If no name is provided, returns the 'default' clip.

        Args:
            name (str, optional): Name of the clip to retrieve. Defaults to 'default'.

        Returns:
            ValueClip: The requested clip, or None if not found
        """
        if name is None:
            name = "default"

        return self._clips.get(name)

    def get_all_clips(self):
        """
        Get all clips in the container.

        Returns:
            dict: Dictionary of all clips {name: ValueClip}
        """
        return self._clips.copy()

    def get_clip_names(self):
        """
        Get all clip names in the container.

        Returns:
            list: List of clip names
        """
        return list(self._clips.keys())

    def has_clip(self, name):
        """
        Check if a clip with the given name exists.

        Args:
            name (str): Name of the clip to check

        Returns:
            bool: True if clip exists, False otherwise
        """
        return name in self._clips

    def is_valid(self):
        """
        Check if the container has any valid clips.

        Returns:
            bool: True if at least one clip exists, False otherwise
        """
        return bool(self._clips)

    def get_clip_by_index(self, index):
        """
        Get a ValueClip by index in lexicographical order.  This is convenient when access clip_sets

        Args:
            index (int): Index of the clip to retrieve (0-based)

        Returns:
            ValueClip: The clip at the specified index, or None if index is out of range
        """
        clip_names = list(self._clips.keys())
        if 0 <= index < len(clip_names):
            return self._clips[clip_names[index]]
        return None

    def __len__(self):
        """Return the number of clips in the container."""
        return len(self._clips)

    def __getitem__(self, key):
        """
        Allow access by index or name using square brackets.

        Args:
            key (int or str): Index (int) or name (str) of the clip

        Returns:
            ValueClip: The requested clip

        Raises:
            IndexError: If index is out of range
            KeyError: If clip name doesn't exist
            TypeError: If key is neither int nor str
        """
        if isinstance(key, int):
            clip_names = list(self._clips.keys())
            if 0 <= key < len(clip_names):
                return self._clips[clip_names[key]]
            else:
                raise IndexError(f"Clip index {key} out of range (0-{len(clip_names) - 1})")
        elif isinstance(key, str):
            if key in self._clips:
                return self._clips[key]
            else:
                raise KeyError(f"Clip '{key}' not found")
        else:
            raise TypeError(f"Key must be int (index) or str (name), got {type(key)}")

    def __str__(self):
        clip_names = ", ".join(self._clips.keys())
        return f"ValueClipContainer(clips=[{clip_names}], count={len(self._clips)})"

    def __repr__(self):
        return self.__str__()


class ValueClip:
    """
    A class to manage value clips data including times, active periods, and asset paths.
    Only load clip data files when needed for value resolution.
    The assumption is that there is a manifest file being used otherwise
    attributes are checked for each clip when requested.
    The manifest will not be created automatically as in OpenUSD
    """

    def __init__(
        self,
        stage: Stage = None,
        clip_data=None,
    ):
        """
        Initialize a ValueClip instance.

        Args:
            stage (Stage, optional): The active stage
            clip_data : Dictionary containing clip data
        """
        clip_data = clip_data or {}

        # Extract USD format data - each field needs special handling for USD objects
        self.active = self._extract_usd_field(clip_data, "active", [])
        self.times = self._extract_usd_field(clip_data, "times", [])
        self.asset_paths = self._extract_usd_field(clip_data, "assetPaths", [])
        self.prim_path = self._extract_usd_field(clip_data, "primPath", "")
        self.manifest_path = self._extract_usd_field(clip_data, "manifestAssetPath", None)

        # Squirrel away the path for later usage
        base_directory = None
        if stage is not None:
            base_path = os.path.abspath(stage.root_layer.file_path)
            base_directory, filename = os.path.split(base_path)
        # There is no real type checking and manifest can be writen as an array, which is not correct
        # e.g asset[] manifest - this code just protects against it...

        if isinstance(self.manifest_path, list):
            self.manifest_path = self.manifest_path[0]

        # Initialize the clip loader with manifest support
        self.clip_loader = ClipDataLoader(self.manifest_path, base_directory)

    @staticmethod
    def _extract_usd_field(clip_data, field_name, default_value):
        """
        Helper method to extract a field from USD clip data.

        Args:
            clip_data : Contains the USD Clip Dictionary
            field_name (str): Name of the field to extract
            default_value: Default value if field doesn't exist

        Returns:
            The extracted value or default_value if field doesn't exist
        """
        if field_name not in clip_data:
            return default_value

        field_obj = clip_data.get(field_name, {})
        if hasattr(field_obj, "to_dict"):
            return field_obj.to_dict()[1]
        return default_value

    def get_clip_time(self, stage_time: timeCode):
        """
        Get the clip time for a given stage time using the "times" mapping.

        Args:
            stage_time (timeCode): The stage time to convert

        Returns:
            float: The corresponding clip time, or 0 if not found.  This means that
            there should always be a clip to load.
        """
        return map_stagetime_to_cliptime(stage_time.get_value(), self.times)

    def get_active_clip_index(self, stage_time: timeCode):
        """
        Get the active clip index for a given stage time.
        The "active" array defines [start_time, clip_index] pairs.
        Returns the clip index that should be active at the given stage time.
        If no active periods are defined, defaults to the first clip (index 0).

        Args:
            stage_time (timeCode): The stage time to check

        Returns:
            int: The clip index (defaults to 0 if no active periods are defined)
        """
        # If no active periods are defined, use the first clip
        if not self.active:
            return 0

        # Sort active periods by start time and find the closest one
        # that includes this stage_time
        sorted_active = sorted(self.active, key=lambda x: x[0])

        # TODO validate the out of range uage - either the first or last clip should be used
        # For now default to the first clip.  This work if active is never supplied
        active_clip_index = 0  # Default to first clip

        for start_time, clip_index in sorted_active:
            if stage_time.get_value() >= start_time:
                active_clip_index = clip_index
            else:
                break

        return int(active_clip_index)

    def get_asset_path(self, clip_index=0):
        """
        Get the asset path for a specific clip index.

        Args:
            clip_index (int): The index of the clip asset

        Returns:
            str: The asset path, or None if index is out of range
        """
        if clip_index is not None and 0 <= clip_index < len(self.asset_paths):
            return self.asset_paths[clip_index]
        return None

    def _pre_validated_get_data(self, stage_time: timeCode, attribute_name):
        """
        Walks through pre validation befoer the data is queried
        1. Validating the attribute against the manifest (if available)
        2. Determining which clip is active at the stage time
        3. Mapping stagetime to cliptime using the "times" array
        4. Loading the appropriate clip file


        Args:
             stage_time (timeCode): The stage time
             attribute_name (str): The name of the attribute

        Returns:
             tuple: Success, attribute data, or None
        """

        if not self.is_clip_active(stage_time):
            print(f"stage time: '{stage_time}' is not in range of the clips: '{self.active}', so clips are not active")
            return False, None

        if not self.is_attribute_supported(attribute_name):
            print(
                f"Warning: Attribute '{attribute_name}' not supported according to manifest - skipping clip resolution"
            )
            return False, None

        # Step 2 Determine which clip is active
        clip_index = self.get_active_clip_index(stage_time)

        # Step 3: Convert stagetime to cliptime
        clip_time = self.get_clip_time(stage_time)
        if clip_time is None:
            return False, None

        # Step 4: Get the asset path for this clip
        asset_path = self.get_asset_path(clip_index)
        if not asset_path:
            print(f"No valid clip files found for clip index: '{clip_index}'")
            return False, None

        # make sure we have the correct clip attribute name
        clip_attribute_name = self.convert_path_to_clip_primpath(attribute_name)
        # Step 5: Load the specific attribute data from the clip
        attribute_data = self.clip_loader.get_clip_data_for_resolution(asset_path, clip_attribute_name)
        if not attribute_data:
            print(f"Warning: Attribute '{attribute_name}' not found in clip '{asset_path}' or has no timeSamples")
            return False, None

        return True, attribute_data

    def get_value_at_stagetime(self, stage_time: timeCode, attribute_name="size"):
        """
        Get the final interpolated value for a given stage_time by:

        Args:
            stage_time (timeCode): The stage time to evaluate
            attribute_name (str): Name of the attribute to query (default: "size")

        Returns:
            float: value
        """

        attribute_supported, attribute_data = self._pre_validated_get_data(stage_time, attribute_name)

        if attribute_supported:
            timesamples = attribute_data.value
            ct = self.get_clip_time(stage_time)
            res = get_value_from_timesamples(ct, timesamples)
            return res

        return None

    def get_timesamples_at_stagetime(self, stage_time: timeCode, attribute_name):
        """
        Get the raw timeSample for custom interpolation:

        Args:
            stage_time (timeCode): The stage time to evaluate
            attribute_name (str): Name of the attribute to query

        Returns:
            list: timesamples
        """
        success, attribute_data = self._pre_validated_get_data(stage_time, attribute_name)
        if success:
            timesamples = attribute_data.value
            return timesamples

        return None

    def to_dict(self):
        """
        Convert the ValueClip back to a dictionary format.

        Returns:
            dict: Dictionary representation of the clip data
        """
        return {
            "assetPaths": self.asset_paths,
            "primPath": self.prim_path,
            "active": self.active,
            "times": self.times,
            "manifest": self.manifest_path,
        }

    def convert_path_to_clip_primpath(self, attribute_path):
        """
        Convert a stage attribute path to a clip attribute path using the clip's prim path.

        Args:
            attribute_path (str): Full attribute path like "/Root.size"

        Returns:
            str: Converted clip attribute path like "/Model.size"

        Raises:
            ValueError: If attribute_path is malformed (no '.' separator)
        """
        if not isinstance(attribute_path, str) or "." not in attribute_path:
            raise ValueError(f"Invalid attribute path: '{attribute_path}'. Expected format 'prim.attribute'")

        try:
            prim_part, attribute_name = attribute_path.split(".", 1)
            clip_attribute_path = f"{self.prim_path}.{attribute_name}"
            return clip_attribute_path
        except ValueError as e:
            raise ValueError(f"Failed to parse attribute path '{attribute_path}': {e}")

    def get_supported_attributes(self):
        """
        Get list of supported attributes from the manifest. All attributes must have
        equivalent timesamples available in the Clips.  If not this is an error

        Returns:
            list: List of supported attribute names, or empty list if no manifest
            An empty list means that each clip will need to be queried for available attributes.

        """
        manifest = self.clip_loader.load_manifest()
        supported_attribute_list = []
        if not manifest and self.asset_paths.length == 0:
            return []

        if not manifest:
            # walk the clips to find attributes
            for clip in self.asset_paths:
                data = self.load_usd_clip(clip)
                for path, data in data.scene.items():
                    if data.form == SpecForm.Attribute:
                        supported_attribute_list.append(path)

            return list(supported_attribute_list)

        # read from manifest
        for path, data in manifest.scene.items():
            if data.form is SpecForm.Attribute:
                # add the name
                supported_attribute_list.append(path)

        return list(supported_attribute_list)

    def is_attribute_supported(self, attribute_name):
        """
        Check if an attribute is supported according to the manifest.

        Args:
            attribute_name (str): Name of the attribute to check

        Returns:
            bool: True if attribute is supported, False otherwise
        """
        manifest = self.clip_loader.load_manifest()

        clip_attribute_name = self.convert_path_to_clip_primpath(attribute_name)

        if manifest is None:
            # If no manifest is available, check against the first clip to see if the attribute exists
            # This is more efficient than checking all clips and provides early validation
            # Both clips should have the same attributes, it is still safer to use Manifest.
            if not self.asset_paths:
                return False

            try:
                first_clip_data = self.load_usd_clip(self.asset_paths[0])
                # Only check attributes, not all scene paths
                return any(
                    path == clip_attribute_name and data.form is SpecForm.Attribute
                    for path, data in first_clip_data.scene.items()
                )
            except Exception:
                # If we can't load the clip, assume attribute is not supported
                return False

        # Check if attribute exists in manifest and is an attribute type
        # Use generator expression for efficiency and add type filtering
        return any(path == attribute_name and data.form is SpecForm.Attribute for path, data in manifest.scene.items())

    def load_usd_clip(self, asset_path):
        """load the actuial clip defined in the CLip dictionary

        Args:
            asset_path (str): Path to the clip

        Returns the clip data
        """

        return self.clip_loader.load_usd_clip_data(asset_path)

    def is_valid(self):
        """Trivial check to see if clips are valid, here check if clips were registered
        It's possible to build a clip at runtime, but there should always be a clip file"""

        return bool(self.asset_paths)

    def is_clip_active(self, stage_time: timeCode):
        """At this time is the clip active - query the active time to verify if the clip is actively
        participating in value resolution. When defined active = [0,0] means that stage time 0 the first
        clip is active and can be queried"""

        active_time = self.active
        if active_time is None:
            return False

        sorted(active_time, key=lambda x: x[0])
        return not stage_time.get_value() < active_time[0][0]

    # Useful tools to build a clip set
    def add_clip_times(self, times):
        # Add a new time definition, useful to debugging the mapping
        self.times = times

    def add_asset_paths(self, asset_path):
        self.asset_paths.append(asset_path)

    def add_clip_active(self, active):
        self.active = active

    def __str__(self):
        return f"ValueClip(prim_path='{self.prim_path}', assets='{self.asset_paths}', active='{self.active}' times='{self.times}', active_periods='{len(self.active)}')"

    def __repr__(self):
        return self.__str__()


def setup_value_clip_container(stage: Stage, prim_path: Spec) -> ValueClipContainer:
    """Setup ValueClipContainer instance from clip dictionary data
    Processes all clips in the dictionary, not just 'default'

    Returns:
        ValueClipContainer: Container with all clips, check is_valid() to ensure it contains clips
    """
    clip_dict = prim_path.fields.get("clips")

    if clip_dict is None:
        return ValueClipContainer()

    clip_dict = clip_dict.value

    # Create container with all clips from the dictionary
    container = ValueClipContainer(stage, clip_dict)

    if not container.is_valid():
        print(f"Failed to find any valid clips in dictionary at path '{prim_path}'.")

    return container


def setup_value_clip(stage: Stage, prim_path: Spec) -> ValueClip:
    """Setup ValueClip instance from clip dictionary data
    Returns the 'default' clip for backward compatibility

    Returns:
        ValueClip: The default clip, check is_valid() to make sure it contains a full Value Clip
    """
    container = setup_value_clip_container(stage, prim_path)

    # Make sure the fact that there are no clips affect the Value Resolution
    if not container.is_valid():
        return ValueClip()

    # Return the default clip for backward compatibility
    # default_clip = container["default"]
    # for an example, always use the first clip in the set
    default_clip = container[0]
    if default_clip is not None:
        return default_clip

    # If no default clip, return an empty ValueClip
    print("No 'default' clip found in clips dictionary.")
    return ValueClip()


if __name__ == "__main__":
    # Run some basic tests...

    filepath = "./data/root.usd"
    if not os.path.exists(filepath):
        filepath = os.path.abspath(os.path.join(os.path.dirname(__file__), filepath))

    stage = Stage.Open(filepath)
    root = stage.get("/Model")
    print(root)
    if clip_dict := root.fields.get("clips"):
        print(clip_dict)

    # Test new container functionality
    container = setup_value_clip_container(stage, root)
    print(f"Container created: {container}")

    if container.is_valid():
        print(f"Available clips: {container.get_clip_names()}")

        # Test getting default clip
        default_clip = container.get_clip()  # Should return 'default'
        if default_clip and default_clip.is_valid():
            print(f"Default clip loaded: {default_clip}")

        # Test getting clip by name
        for clip_name in container.get_clip_names():
            clip = container.get_clip(clip_name)
            print(f"Clip '{clip_name}': {clip}")

    # Test backward compatibility
    new_clip = setup_value_clip(stage, root)

    if not new_clip.is_valid():
        print("Value Clip 'default' created but there are no active clips")

    # build the attribute
    attribute = new_clip.prim_path + ".size"
    active = new_clip.is_clip_active(timeCode(-15.0))

    if not new_clip.clip_loader.is_clip_loaded(new_clip.asset_paths[0]):
        print(f"Clip {new_clip.asset_paths[0]} is not loaded yet, as expected...")

    # test data uses size
    if spec_supported := new_clip.is_attribute_supported(attribute):
        print("Attribute supported...!")

    supported_list = new_clip.get_supported_attributes()
    print(f"Supported attributes, from Manifest: {new_clip.manifest_path} is: {supported_list}")
    # spec = clip_data.get(attribute)

    value = new_clip.get_value_at_stagetime(timeCode(0), attribute)

    if new_clip.clip_loader.is_clip_loaded(new_clip.asset_paths[0]):
        print(f"Clip {new_clip.asset_paths[0]} is now loaded as expected...")

    if spec_supported:  # .size
        test_stagetimes = [-1, 0, 10, timeCode.safe_step(20.0).get_value(), 20, 30, 15, 25, 30, 35, 40, 45, 50]
        for stagetime in test_stagetimes:
            value = new_clip.get_value_at_stagetime(timeCode(stagetime), attribute)
            print(stagetime, value)

    new_clip.clip_loader.clear_cache()
    if not new_clip.clip_loader.is_clip_loaded(new_clip.asset_paths[0]):
        print(f"Clip {new_clip.asset_paths[0]} is now unloaded...")

    # new active segment
    active = [[10, 0], [20, 1]]
    new_clip.add_clip_active(active)

    if not new_clip.is_clip_active(timeCode(0.0)):
        print(f"Clip {new_clip.asset_paths[0]} is not active... stage_time '0.0' is less than {active}")

    # Validate unsupported attribute
    attribute = "Model.bad"
    if not new_clip.is_attribute_supported(attribute):
        print(f"Attribute: '{attribute}' is not supported... ")
