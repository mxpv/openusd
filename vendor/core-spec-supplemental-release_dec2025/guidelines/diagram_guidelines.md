# Purpose

USD specifications should make use of diagrams where a complex concept is being defined. Note that diagrams should 
**not** be used in place of written definitions, only to help clarify or visualize an existing definition.

# Types of Diagrams

The following types of diagrams might be useful for USD specifications.

## Railroad diagrams

Railroad diagrams are primarily used to visualize grammars or syntax formats, typically CFGs like BNF, etc. They work 
well with anything that can be described with a regular expression or PEG expression.

Basic example:  

![Basic railroad example](diagram_guidelines_general_railroad.svg)  

Railroad diagrams can become long in either direction depending on the expression (see extra-long vertical example in 
[Oleksiy's slides](https://docs.google.com/document/d/1W72Jxh09rNCRQQmuBS2DlDKu5HlHlCaenBsAuopEgpo/edit?tab=t.0)). Use 
your best judgment in these cases on whether it is still helpful to have the diagram or not.

## Workflow diagrams 

Workflow diagrams are used to visualize state or process flow. Workflow diagrams can sometimes be used to visualize 
standards compliance, by showing that all required "input" or "output" states are accessible via the workflow. 

Workflow diagrams are sometimes referred to as flowchart diagrams. Block diagrams are also a similar diagram form. 
Activity diagrams are also similar, but follow [a standardized format specified by UML](https://en.wikipedia.org/wiki/Activity_diagram). 

Very simple workflow example:

![Very simple workflow example](diagram_guidelines_basic_workflow.svg)

## Hierarchy diagrams

A hierarchy diagram is used to visualize hierarchical relationships. This can be used for visualizing a dataset, 
3D scene, class hierarchy, etc.

Example hierarchy diagram for a USD scene:

![Example hierarchy diagram](diagram_guidelines_hierarchy.svg)

## Other Diagram Types

**TBD, add as needed**.

Spline diagrams: See spline examples in Stage Composition specification and in the 
[Spline Animation in USD](https://github.com/PixarAnimationStudios/OpenUSD-proposals/blob/main/proposals/spline-animation/README.md) proposal. 

# Specific Diagrams to Consider

This section lists possible diagrams that specific specification documents might need.

**Path Grammar** 

Railroad diagrams might clarify some of the grammar definition rules. To be consistent, we might want to provide 
railroad diagrams for all the rules, but this might seem redundant for many of the basic rules. 

Example:

```
*Assignment \=* (*Spaces*)\* *Equals* (*Spaces*)\*  
```

![Path grammar assignment rule diagram](diagram_guidelines_grammar_assignment.svg)

**Foundational Data Types**

For list ops, it's possible some sort of Workflow (or even a Venn-diagram?) would be useful in visualizing examples of 
combining/reducing/chaining list ops, but this isn't necessary. 

**Document Data Model**

No areas that seem to be in immediate need of diagrams.

**Core File Formats**

Railroad diagrams for the various grammar rules. Similar to the path grammar specification, we should determine if we 
want to provide railroad diagrams for all rules for consistency, vs skipping diagrams for the most basic rules to avoid 
redundancy.

**Stage Population**

Already using diagrams to help visualize spline types.  
Possibly use workflow diagrams for illustrating stage populating state, instancing.

**Composition Engine**

Possibly use workflow diagrams to illustrate composition, highlighting the different phases? See also: composition layer 
state diagrams used in composition puzzles (useful for illustrating concrete composition examples): 
[https://github.com/usd-wg/assets/tree/main/docs/CompositionPuzzles/PayloadAndReference](https://github.com/usd-wg/assets/tree/main/docs/CompositionPuzzles/PayloadAndReference) 

# Diagramming Tools and Libraries

We're not restricting authors use specific tools for now. The following are recommended tools and libraries that some 
authors have had experience using.

## Tools

[**draw.io**](https://draw.io/)

Draw.io is a basic diagramming application available in-browser or as a standalone (wrapped) application. It can be used 
to author most diagram types, and has some basic freeform drawing functionality. 

Pixar is attempting to standardize on using [draw.io](https://draw.io/) for diagrams, using the "Editable Vector Image" 
format. The main reason is that draw.io provides a way to embed draw.io app-level metadata in the output SVG file, which 
ensures that the "source" data for the diagram lives with the SVG and can be re-edited easily in the future.

[**Grammar\_visualizer\_railroad.py**](https://github.com/encukou/cpython/blob/railroad-svg-simplify/Tools/peg_generator/pegen/grammar_visualizer_railroad.py)  **(cPython)**

Python script to generate railroad diagrams from PEG.

## Libraries

[**Blockdiag**](http://blockdiag.com/en/index.html#)

A set of Python libraries to generate multiple types of diagrams (block, sequence, activity, network). Can generate SVG, 
doesn't have external dependencies. Suitable for our doc pipeline scripts. 

[**Railroad-diagrams**](https://tabatkins.github.io/railroad-diagrams/)

Python/JS lib to generate railroad diagrams. Includes in-browser example tool:   
[https://tabatkins.github.io/railroad-diagrams/generator.html](https://tabatkins.github.io/railroad-diagrams/generator.html) 

## Related Tools

The following tools are not used to create diagrams specifically, but are used in our documentation workflow to handle 
building/rendering documentation content that may contain diagrams.

[**Pandoc**](https://pandoc.org/)

A document conversion tool that can be used to convert from Markdown to PDF and other formats (e.g. RST). Can use 
filters that can process/include various diagram formats.

# Diagramming Standards

For USD specifications we are using the following diagramming standards and standard practices.

Source format: We're not restricting authors to a specific source format (or diagramming tool), but it's important to 
keep and submit source files for diagrams, so future changes can be made.

Storing image files: We suggest storing the source and output image files adjacent to the markdown or other content file 
that references the images. Where possible, prepend the name of the content file to the image file, e.g. "composition\_workflow\_diagram\_1.svg" – this facilitates finding related image files, and avoids file name conflicts.

Output format: When possible, use SVG as the output format. SVG is portable and embeddable, easy to integrate into a PDF 
workflow, resolution-independent, and supported by most browser and document readers. If your tool or process can't 
output SVG, PNG would be the next best option. 

Embedded format: If your diagram is small, consider using Mermaid syntax embedded in your markdown. See 
[https://github.blog/developer-skills/github/include-diagrams-markdown-files-mermaid/](https://github.blog/developer-skills/github/include-diagrams-markdown-files-mermaid/) and [https://mermaid.js.org/intro/syntax-reference.html](https://mermaid.js.org/intro/syntax-reference.html) for more details. Note that this might require using additional filters for Pandoc (e.g. 
[https://github.com/raghur/mermaid-filter](https://github.com/raghur/mermaid-filter)).

Color vs black-and-white: **TBD whether there are any ISO requirements to have diagrams in black-and-white for 
accessibility reasons**. Until we determine otherwise, color diagrams should be allowed.

Diagram notation styles: **TBD collect any standard diagram styles (e.g. "crows feet" notation style for class diagrams) 
we end up using here**.

# See Also

Oleksiy’s experiments with generating railroad diagrams from code/PEG using cPython (or Parsimonious), to SVG and then 
to HTML/PDF using pandoc. Slides in AOUSD notes: 
[https://docs.google.com/document/d/1W72Jxh09rNCRQQmuBS2DlDKu5HlHlCaenBsAuopEgpo/edit?tab=t.0](https://docs.google.com/document/d/1W72Jxh09rNCRQQmuBS2DlDKu5HlHlCaenBsAuopEgpo/edit?tab=t.0)    


