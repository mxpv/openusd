# Compliance

The following provides pseudo code for compliance algorithms which simplify stages into single layers without
composition.

## Squash

Squashing a stage removes all composition inputs such that all queries at a path produce the same result. A squashed
stage may be used to validated composed stage population. A squashed stage may contain the `instanceable` keyword but
without composition operators, it is inert.

```
COMPOSITION_INPUTS = ("references", "payload", "inheritPaths", "specializes", "subLayers", "subLayerOffests",
                      "layerRelocates", "variantSetNames", "variantSelection")

def squash(stage: Stage) -> Layer:
    squashed_layer = Layer()
    # traverse all children, including "instance proxies"
    for object in stage.traverse_all_with_instance_proxies:
        for authored_field in object.authored_fields:
            # Be mindful that time samples and splines may be subject to retiming
            if authored_field.name not in COMPOSITION_INPUTS:
                squashed_layer[(object.path_or_proxy_path, authored_field.name)] = authored_field.resolved_value
    return squashed_layer
```

## Sample

Sampling a stage exercises value resolution including fallback resolution of metadata fields and schema defined
attributes, as well as time sampled attributes.
```
# COMPOSITION_INPUTS is reused from `squash`
ATTRIBUTE_VALUE_RESOLUTION_INPUTS = ("timeSamples", "spline", "default")

def sample(stage: Stage, samples: list[double]) -> Layer:
    sampled_layer = Layer()
    for object in stage:
        # Apply value resolution to all simple fields
        for field in object.fields:
            # Similar to squashing-- except
            #   a) Sample all fields, not just authored fields to verify fallbacks from prim definitions
            #   b) Specially handle attribute value resolution fields
            if field.name not in (*COMPOSITION_INPUTS, *ATTRIBUTE_VALUE_RESOLUTION_INPUTS):
                sampled_layer[(object.path, field.name)] = field.resolved_value
        if isinstance(object, Attribute):
            # default sampling should return the fallback value if
            # default is not authored
            if default := object.sample_default():
                sampled_layer[(object.path, "default")] = default
            # sampling relies on value resolution to negotiate time samples, fallback values, defaults, and splines
            if object.has_value:
                sampled_layer[(object.path, "timeSamples")] = {sample : object.sample(sample) for sample in samples}
    return sampled_layer
```