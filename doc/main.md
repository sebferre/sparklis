<meta charset="UTF-8"/>

# Documentation of the Sparklis JS API

Two facts make it difficult to customize Sparklis by modifying its source code. First, Sparklis is developed in the [OCaml programming language](http://ocaml.org/), which is compiled to JavaScript with the [`js_of_ocaml`](https://ocsigen.org/js_of_ocaml/latest/manual/overview) tool. The reason for this unconventional choice is that it makes me much more productive, which is key given the limited amount of time that I can devote to it. Second, the internal working of Sparklis is quite complex, and has all sorts of interdependencies between its different parts. The suggestions depend on the query, on the focus in that query, and on the query results. Those results do not only depend on the query but also on the focus. The translations from the built query to its formalization in SPARQL and its verbalization in natural language are not trivial. The verbalization relies on the dynamic retrieval of labels based on the query results. In addition to the user query, various SPARQL queries are sent to the endpoint to retrieve the labels, the suggestions, and other information.

However, many people have expressed their wish to reuse Sparklis, and it is not possible to hard-code in it all the specific needs that the different use case require. Among the possible customization of Sparklis, one finds:

- changing the layout and appearance of components
- adding alternate views of results (e.g., charts)
- hiding some of the suggestion

To this purpose, Sparklis now provides a JS API that enables to introspect and customize its behavior. There is nothing to do to have a working Sparklis, the use of the API is only necessary as much as customization is needed, in a pay-as-you-go fashion. An important limitation to know is that it is not possible to have several instances of the Sparklis view, although it is possible to maintain several navigation states (called *places*).

## Overview

The Sparklis JS API is available through two JS objects:

- `sparklis`: for instropection and control of Sparklis internal states
- `sparklis_extension`: for customizing default behaviors, and capturing key events

The available properties and methods on those objects are described in the following sections. The last section below describes the Sparklis-specific datatypes used by those methods and properties.


## Introspection with object `sparklis`

Access and control of the endpoint:

- **`sparklis.endpoint(): string`**

  returns the current endpoint URL

- **`sparklis.changeEndpoint(url: string): void`**

  changes the current endpoint to the one specified by `url`

- **`sparklis.evalSparql(query: string, callback: sparklis-results => void, onError: int => void): void`**

  sends `query` to the current endpoint according to the current Sparklis configuration. If successful, `callback` is called on the *Sparklis results* (see datatypes), otherwise `onError` is called on the HTTP error code.


Access and control of the current navigation place:

- **`sparklis.currentPlace(): sparklis-place`**

  returns the current *Sparklis place* (see below for the API of Sparklis places)

- **`sparklis.setCurrentPlace(p: sparklis-place): void`**

  sets `p` as the new current place. This triggers the necessary computations and drawings to display the query, suggestions and results of the new place. The new place is pushed on top of the navigation history.

- **`sparklis.refresh(): void`**

  forces to refresh the Sparklis view


Access and control of the current constraints

- **`sparklis.termConstr(): sparklis-constr`**

  returns the current *Sparklis constraint* on term suggestions

- **`sparklis.conceptConstr(): sparklis-constr`**

  returns the current *Sparklis constraint* on concept suggestions (classes and properties)

- **`sparklis.modifierConstr(): sparklis-constr`**

  returns the current *Sparklis constraint* on modifier suggestions

- **`sparklis.setTermConstr(constr: sparklis-constr): void`**

  sets the current *Sparklis constraint* on term suggestions

- **`sparklis.setConceptConstr(constr: sparklis-constr): void`**

  sets the current *Sparklis constraint* on concept suggestions (classes and properties)

- **`sparklis.setModifierConstr(constr: sparklis-constr): void`**

  sets the current *Sparklis constraint* on modifier suggestions


Modifying the current query. The new place is pushed on top of the navigation history.

- **`sparklis.activateSuggestion(sugg: sparklis-suggestion): void`**

  is the programmatic equivalent of clickling a *Sparklis suggestion* (see datatypes) to insert or apply it in the query at the current focus

- **`sparklis.deleteFocus(): void`**

  is the programmatic equivalent of clicking the deletion cross at the right of the highlighted focus to delete the whole highlighted part of the query


Moving the focus in the syntactic tree structure of the query. The new place replaces the current place in the navigation history.

- **`sparklis.focusUp(): void`**

  moves the focus up, if possible

- **`sparklis.focusDown(): void`**

  moves the focus down (leftmost), if possible

- **`sparklis.focusLeft(): void`**

  moves the focus left, if possible

- **`sparklis.focusRight(): void`**

  moves the focus right, if possible


Control of the navigation history:

- **`sparklis.home(): void`**

  resets the Sparklis view with the initial query

- **`sparklis.back(): void`**

  moves back in navigation history, if possible

- **`sparklis.forward(): void`**

  moves forward in navigation history, if possible


Access to the labels of terms and concepts (lexicons):

- **`sparklis.termLabels(): sparklis-lexicon`**

  returns the lexicon for terms (labels)

- **`sparklis.classLabels(): sparklis-lexicon`**

  returns the lexicon for classes (labels)

- **`sparklis.propertyLabels(): sparklis-lexicon-syntagm`**

  returns the lexicon for properties (labels + syntagms)

- **`sparklis.argLabels(): sparklis-lexicon-syntagm`**

  returns the lexicon for property arguments (labels + syntagms)


## Sparklis places (datatype `sparklis-place`)

Let us assume a Sparklis place `p`, representing a navigation state. The following methods are available.

- **`p.query(): sparklis-query`**

  returns the abstract syntax tree (AST) of the NL query

- **`p.focusPath(): sparklis-focus-path`**

  returns the path in the query AST that leads to the current focus

- **`p.delta(): sparklis-delta`**

  returns the delta relative to the previous place. The previous place is the place from which place `p` was created. The delta describes the new focus ids introduced (see the description of `sparklis-delta`).

- **`p.permalink(): string`**

  returns a permalink to this place

- **`p.onEvaluated(callback: () => void): void`**

  calls `callback` when the place has been evaluated, i.e. when the SPARQL query, its results, and other related information is available.

- **`p.sparql(): string`**

  returns the SPARQL translation of the current query and focus. The place must be evaluated.

- **`p.results(): sparklis-results`**

  returns the *Sparklis results* (see datatypes) of the current query focus, as retrieved from the endpoint. They are structured as a table filled with RDF terms (and null values). The place must be evaluated.

- **`p.hasPartialResults(): bool`**

  returns whether the Sparklis results are partial or not. The place must be evaluated.

- **`p.getTermSuggestions(inverse: bool, termConstr: sparklis-constr, callback: (partial: bool, suggs: sparklis-suggestions) => void): void`**

  calls `callback` on the term suggestions (see datatype `sparklis-suggestions`) matching the given term constraint. The `partial` argument of the callback indicates wheter the passed suggestions are partial or not. The place must be evaluated.

- **`p.getConceptSuggestions(inverse: bool, conceptConstr: sparklis-constr, callback: (partial: bool, suggs: sparklis-suggestions) => void): void`**

  calls `callback` on the concept suggestions (see datatype `sparklis-suggestions`) matching the given concept constraint. The `partial` argument of the callback indicates wheter the passed suggestions are partial or not. The place must be evaluated.

- **`p.getModifierSuggestions(callback: (partial: bool, suggs: sparklis-suggestions) => void): void`**

  calls `callback` on the modifier suggestions (see datatype `sparklis-suggestions`). The `partial` argument of the callback indicates wheter the passed suggestions are partial or not (in practice, should always be false). The place must be evaluated.

- **`p.applySuggestion(sugg: sparklis-suggestion): sparklis-place`**

  generates a new Sparklis place resulting from the application of the given suggestion to place `p`. To allow for efficient chaining of this method, no call to the SPARQL endpoint is triggered before results and suggestions are explicitly asked for with methods `getResults` and `getXXXSuggestions`.


## Sparklis lexicons (datatypes `sparklis-lexicon` and `sparklis-lexicon-syntagm`)

Let us assume a Sparklis lexicon `lex`, which provides access to a
collection of labels. The following methods are available.

- **`lex.info(uri: string): string or { label: string, syntagm: ("Noun" | "InvNoun" | "TransVerb" | "TransAdj")}`**

  returns the labelling information for the passed URI. For datatype `sparklis-lexicon`, that information is a simple string. For datatype `sparklis-lexicon-syntagm`, that information is an object with two fields:
  - `label`: a string
  - `syntagm`: the part-of-speech tag of the label, which is one of
    - `"Noun"`: a noun (e.g., [has] child)
    - `"InvNoun"`: an inverse noun (e.g., [is] parent [of])
    - `"TransVerb"`: a transitive verb (e.g., knows, lives in)
    - `"TransAdj"`: a transitive adjective (e.g., next to)

- **`lex.enqueue(uri: string): void`**

  enqueues the passed URI in the next batch to retrieve labels

- **`lex.sync(callback: () => void): void`**

  synchronizes the lexicon by retrieving the labelling information for
  all queued URIs, and calls the callback function when done


## Customization with object `sparklis_extension`

This object has a number of properties that are undefined by default. By defining them, a developer can customize the behavior of Sparklis at key points inside the data workflow, without having to redefine the whole workflow. Customization can be adding a new behavior, modifying the default behavior, or removing altogether some behavior.

A common form of customization is a *hook*, i.e. a custom function that is called by Sparklis at some step in the data workflow. That function can have both side effects and a result. If the result is undefined, then only side effects occur and the data workflow is left unchanged.

- **`sparklis_extension.hookSparql: (string => string or undefined) or undefined`**

  can hold a function that will be called on each SPARQL translation of the user query, and that may return a modified SPARQL query, which will be the one sent to the SPARQL endpoint for evaluation. This can be used to handle features that are specific to the target endpoint.

- **`sparklis_extension.hookResults: (sparklis-results => sparklis-results or undefined) or undefined`**

  can hold a function that will be called on each Sparklis results, and that may return modified results, which will be the one displayed to the user. Side effects can here be used to generate and display an alternative view of results to the user (e.g., charts, a custom map). In combination with `hookSparql`, this can be used to post-process the results of a modified SPARQL query so that they align with the user query (e.g., removing some columns).

- **`sparklis_extension.hookSuggestions: (sparklis-suggestions => sparklis-suggestions or undefined) or undefined`**

  can hold a function that will be called on each set of suggestions (terms, concepts, and modifiers), and may return a modified set of suggestions, which will be the one displayed to the user. This can be used to filter out some suggestions or to forcibly add some suggestions.

- **`sparklis_extension.hookApplySuggestion: ((place: sparklis-place, sugg: sparklis-suggestion) => sparklis-place or undefined) or undefined`**

  can hold a function that will be called each time when a suggestion is applied to some Sparklis place. Given the place and the suggestion, the function may return a new Sparklis place, as a substitute for the default target place. This can be used to customize the application of suggestions, e.g. applying automatic focus moves after suggestion application.


## Sparklis-specific datatypes

We describe each datatype used in Sparklis JS API. Each datatype is a set of JSON values. We define the set of values in an intuitive way, combining type names and JSON notations:

* `string` denotes the set of strings
* `int` denotes the set of integers
* `number` denotes the set of numbers
* `bool` denotes the values `true` and `false`
* `"abc"` or any literal string denotes itself (a single value)
* `("X" | "Y" | "Z")` or any enumeration of strings denotes that set of strings
* `[T1, T2]` denotes length-2 array whose first item has type *T1* and whose second item ha type *T2* (this generalizes to any fixed length)
* `[T ..]` denotes the variable-length arrays whose items have type *T*
* `{p1: T1, p2: T2}` denotes the objects with properties *p1* of type *T1*, and *p2* of type *T2* (this generalizes to any set of property names and types)
* `T or null` denotes an optional value of type *T*
* `sparklis-rdfterm` or any sparklis datatype denotes the set of values defined for that datatype

When the values of a datatype fall into different cases, we provide the list of possible cases. Each case is either a string or an object with a `type` property identifying the case.

### Datatype `sparklis-rdfterm`

- `{ type: "uri", uri: string }`
- `{ type: "number", number: number, str: string, datatype: string }`
- `{ type: "typedLiteral", str: string, datatype: string }`
- `{ type: "plainLiteral", str: string, lang: string }`
- `{ type: "bnode", id: string }`
- `{ type: "var", name: string }`

The datatype for RDF terms covers usual kinds (URIs, typed literals, plain literals, and blank nodes), and adds numbers and SPARQL variables.
For numbers, property `number` holds a JS numeric value, property `str` is the lexical representation, and property `datatype` holds the RDF datatype (e.g., xsd:integer).

### Datatype `sparklis-delta`

- `"nil"`
- `{ type: "ids", ids: [number ..] }`
- `{ type: "duplicate", map: [ [number, number] ..] }`
- `{ type: "selection", whole: sparklis-delta, parts: [sparklis-delta ..] }`

Delta `"nil"` represents an empty delta, no new focus id is introduced.
Delta with type `"ids"` provides a list of new focus ids (integer numbers).
Delta with type `"duplicate"` happens when part of the query was duplicated with suggestion "_ and _". It provides a mapping from existing ids to new ids.
Delta with type `"selection"` happends when several suggestions were selected at once (as a selection). It provides the delta of each selected suggestion (field `parts`) as well as the delta resulting from their insertion into the query (field `whole`).

### Datatype `sparklis-results`

```
{ columns: [string ...],
  rows: [ [sparklis-rdfterm or null ...] ...] }
```

The array of columns is filled with the name of the variables from the evaluated SPARQL query. Each row is an array of the same length as `columns`. Each cell contains an RDF term or `null`. The `null` value corresponds to unbound variables in SPARQL results.

### Datatype `sparklis-search`

This datatype is used in `sparklis-constr`, and describes the available fulltext searches.

- `{ type: "TextQuery", kwds: [string ...] }`
- `{ type: "WikidataSearch", kwds: [string ...] }`

"TextQuery" refers to the fulltext search made available in Fuseki via the special predicate `text:query`.
"WikidataSearch" refers to the entity search service provided by Wikidata.

### Datatype `sparklis-constr`

This datatype is used to define the constraints that can be applied on the computation of suggestions.

- `"True"`
- `{ type: "MatchesAll", kwds: [string ...] }`
- `{ type: "MatchesAny", kwds: [string ...] }`
- `{ type: "IsExactly", kwd: string }`
- `{ type: "StartsWith", kwd: string }`
- `{ type: "EndsWith", kwd: string }`
- `{ type: "After", kwd: string }`
- `{ type: "Before", kwd: string }`
- `{ type: "FromTo", kwdFrom: string, kwdTo: string }`
- `{ type: "HigherThan", value: string }`
- `{ type: "LowerThan", value: string }`
- `{ type: "Between", valueFrom: string, valueTo: string }`
- `{ type: "HasLang", lang: string }`
- `{ type: "HasDatatype", datatype: string }`
- `{ type: "ExternalSearch",
    searchQuery: sparklis-search,
    resultTerms: [sparklis-rdfterm ...] or null }`

"True" is the void constraint.
"After", "Before" and "FromTo" rely on lexical order while "HigherThan", "LowerThan" and "Between" rely on numerical order.
In "ExternalSearch", unlike other constraints, the keywords are not included into the SPARQL translation of the user query but sent to an external search engine (or an independent SPARQL query). The result, a list of RDF terms, is what will be included into the SPARQL query as a membership constraint. To that purpose, the list of RDF terms is stored into the constraint, in property `resultTerms`.

### Datatype `sparklis-numconv`

This datatype is involved in various other datatypes, and helps to tackle the often inconsistent usage of datatypes in RDF datasets for numerical values, either missing datatypes or non-standard datatypes.

```
{ targetType: ("Integer" | "Decimal" | "Double"),
  forgetOriginalDatatype: bool }
  ```
Property `targetType` specifies to which datatype the literal should be converted to (SPARQL functions `xsd:integer`, `xsd:decimal` and `xsd:double` will be applied).
Property `forgetOriginalDatatype` tells whether the original datatype must be ignored, applying the 'str' function, before applying the conversion. In case of doubt, set this property to `true`.

### Datatype `sparklis-pred`

This datatype is used in datatype `sparklis-suggestion`. It describes possible predicates (in the logical sense) with arities 1, 2, and beyond.

- `{ type: "Class", uri: string }`
- `{ type: "Prop", uri: string }`
- `{ type: "SO", uriS: string, uriO: string }`
- `{ type: "EO", uriE: string, uriO: string }`

"Class" and "Prop" corresponds to the standard RDFS classes and properties, which are respectively unary and binary predicates.
"SO" and "EO" predicates correspond to reification patterns commonly found in RDF datasets.

In the "SO" pattern, the reification node has property `uriS` to the predicate subject (S), and property `uriO` to the predicate object (O). Here is the schematic graph pattern of the relation from S to O.

> `[ uriS S; uriO O; ... ]`

In the "EO" pattern, property `uriE` links the predicate subject (S) to the reification node (E), and property `uriO` links the reification node to the predicate object (O). Here is the schematic graph pattern of the relation from S to O.

> `S uriE [ uriO O; ... ]`

The ellipsis in the above patterns represent the possible addition of qualifying properties.

### Datatype `sparklis-arg`

This datatype is used in datatype `sparklis-suggestion`, and interplays with `sparklis-pred`. It identifies an argument of a predicate.

- `"S"`
- `"P"`
- `"O"`
- `{ type: "Q", uri: string }`

"S", "P" and "O" are the three standard arguments of a triple, and stand for subject, predicate, and object.
"Q" stands for *qualifier*, and enables to add arguments beyond subject and object to reification nodes. The argument role is then specified by a URI. Qualifiers are analogous to prepositions in natural languages.

### Datatype `sparklis-latlong`

This datatype is used in datatype `sparklis-suggestion` to define how geolocation is encoded in the target endpoint.

- `"WikidataGeolocation"`
- `{ type: "LatLong", uriLat: string, uriLong: string }`

"WikidataGeolocation" refers to the specific encoding of geolocation in Wikidata.
"LatLong" is for the cases where the geolocation of an entity is represented with two properties, `uriLat` for latitude and `uriLong` for longitude, without intermediate node.

### Datatype `sparklis-order`

This datatype is used in datatype `sparklis-suggestion` to specify an optional ordering over a single variable.

`{ type: ("ASC" | "DESC"), conv: sparklis-numconv or null } or null`

Property `conv` specifies whether a numerical conversion should be applied to the sorted terms.

### Datatype `sparklis-aggreg`

This datatype is used in datatype `sparklis-suggestion` to specify aggregation operators.

- `"COUNT_DISTINCT"`
- `"LIST"`
- `"SAMPLE"`
- `{ type: "SUM", conv: sparklis-numconv or null }`
- `{ type: "AVG", conv: sparklis-numconv or null }`
- `{ type: "MAX", conv: sparklis-numconv or null }`
- `{ type: "MIN", conv: sparklis-numconv or null }`

"COUNT_DISTINCT" is the *COUNT* aggregator, removing repeated values.
"LIST" is based on the *GROUP_CONCAT* aggregator, removing repeated values, converting all values to strings, and concatenating them with separator `/`.
For numerical aggregators, a numerical conversion may be specified.

### Datatype `sparklis-func`

This datatype is used in datatype `sparklis-suggestion` to specify function operators, which all come from the standard SPARQL functions.
They are all encoded as simple JSON strings so we simply list their names by category.

- *RDF terms*

  `Str Lang Datatype IRI STRDT STRLANG IsIRI IsBlank IsLiteral IsNumeric`
  
- *strings*

  `Strlen Substr2 Substr3 Strbefore Strafter Concat UCase LCase Encode_for_URI Replace StrStarts StrEnds Contains LangMatches REGEX REGEX_i`
  
- *type conversion*

  `Integer Decimal Double Indicator`
  
- *numbers*

  `Add Sub Mul Div Neg Abs Round Ceil Floor Random2`
  
- *date & time*

  `Date Time Year Month Day Hours Minutes Seconds TODAY NOW`
  
- *logics*

  `And Or Not BOUND IF`
  
- *comparisons*

  `EQ NEQ GT GEQ LT LEQ`

"Substr3" is the standard substring function taking as arguments the source string, the starting position, and the length of the substring.
"Substr2" only takes the source string and a starting position, considering the end position as the end of the source string.
"REGEX_i" is the case-insensitive version of "REGEX", both expecting two arguments, the source string and the regexp.
"Random2" takes two integers as arguments, defining the range in which random values should be taken. 

### Datatype `sparklis-suggestion`

This is the datatype of individual suggestions, whatever their category (terms, concepts or modifiers).

- `"IncrAnything"`
- `"IncrThatIs"`
- `"IncrSomethingThatIs"`
- `"IncrTriplify"`
- `"IncrSimRankIncr"`
- `"IncrSimRankDecr"`
- `"IncrAnd"`
- `"IncrDuplicate"`
- `"IncrOr"`
- `"IncrChoice"`
- `"IncrMaybe"`
- `"IncrNot"`
- `"IncrIn"`
- `"IncrInWhichThereIs"`
- `"IncrUnselect"`
- `"IncrForeach"`
- `"IncrForeachResult"`
- `{ type: "IncrSelection", op: ("And" | "Or" | "NAnd" | "NOr" | "Aggreg"), items: [sparklis-suggestion ...] }`
- `{ type: "IncrInput", value: string, inputType: ("IRI" | "String" | "Float" | "Integer" | "Date" | "Time" | "DateTime" | "Duration") }`
- `{ type: "IncrTerm", term: sparklis-rdfterm }`
- `{ type: "IncrId", id: int, conv: sparklis-numconv or null }`
- `{ type: "IncrPred", arg: sparklis-arg, pred: sparklis-pred }`
- `{ type: "IncrArg", uri: string }`
- `{ type: "IncrTriple", arg: sparklis-arg }`
- `{ type: "IncrType", uri: string }`
- `{ type: "IncrRel, uri: string, orientation: ("Fwd" | "Bwd") }`
- `{ type: "IncrLatLong", latlong: sparklis-latlong }`
- `{ type: "IncrHierarchy", transitiveRelInCtx: bool }`
- `{ type: "IncrSim", pred: sparklis-pred, argS: sparklis-arg, argO: sparklis-arg }`
- `{ type: "IncrOrder", order: sparklis-order }`
- `{ type: "IncrAggreg, aggreg: sparklis-aggreg }`
- `{ type: "IncrForeachId", id: int }`
- `{ type: "IncrAggregId", aggreg: sparklis-aggreg, id: int }`
- `{ type: "IncrFuncArg", boolResult: bool, func: sparklis-func, arity: int, argPos: int, resultConv: sparklis-numconv or null, argConv: sparklis-numconv or null }`
- `{ type: "IncrName", name: string }`

### Dataype `sparklis-suggestion-frequency`

This datatype is used to represent the frequency of a suggestion over the results.

```
{ value: int,
  maximum: int or null,
  partialCount: bool,
  unit: ("Results" | "Entities") }
```	

Property `value` is the frequency count.
Property `maximum`, if not null, indicates the maximum possible value, which allows to compute ratios.
Property `partialCount` indicates whether the count was partial (based on partial results) or not (complete results).
Property `unit` tells whether the count is a number of results (solutions to the SPARQL query) or a number of distinct entities.

### Datatype `sparklis-suggestion-forest`

This datatype is used to represent a *forest* of suggestions, i.e. a list of suggestion hierarchies. Such hierarchies are used to reflect ontologies over classes and properties, and also domain-specific terminologies.

```
[ { item: { suggestion: sparklis-suggestion,
            frequency: sparklis-suggestion-frequency or null },
    children: sparklis-suggestion-forest } ...]
```

A forest is a list of trees. Each tree is a JSON object where property `item` represents the root node, and where property `children` is a list of sub-trees, hence a forest. Note the recursivity of this type.
Each item is composed of a suggestion and its frequency.

### Datatype `sparklis-suggestions`

This datatype is used to represent the differents sets of suggestions in the JS API.

```
{ type: ("Entities" | "Concepts" | "Modifiers"),
  forest: sparklis-suggestion-forest or null }
  ```

Property `type` indicates the category of suggestions, while property `forest` provides the actual forest of suggestions.


### Datatype `sparklis-query`

This datatype is used for Sparklis queries. It represents them as
Abstract Syntax Trees (AST). It is defined as a set of mutually
recursive datatypes.

- `sparklis-query` = `query-s` (sentences)
  - `{ type: "Return", np: query-s1 }`
  - `{ type: "SAggreg", items: [query-aggreg ..] }`
  - `{ type: "SExpr", name: string, id: int, modif: query-modif, expr: query-expr, rel: query-p1 or null }`
  - `{ type: "SFilter", id: int, expr: query-expr }`
  - `{ type: "Seq", children: [query-s ..] }`
- `query-s1` (noun phrases)
  - `{ type: "Det", det: query-s2, rel: query-p1 or null }`
  - `{ type: "NAnd", children: [query-s1 ..] }`
  - `{ type: "NOr", children: [query-s1 ..] }`
  - `{ type: "NMaybe", child: query-s1 }`
  - `{ type: "NNot", child: query-s1 }`
- `query-s2` (noun phrase heads)
  - `{ type: "Term", term: sparklis-rdfterm }`
  - `{ type: "An", id: int, modif: query-modif, class: string or null }`
  - `{ type: "The", id: int }`
- `query-sn` (multi-complement phrases)
  - `{ type: "CNil" }`
  - `{ type: "CCons", arg: sparklis-arg, np: query-s1, cp: query-sn }`
  - `{ type: "CAnd", children: [query-sn ..] }`
  - `{ type: "COr", children: [query-sn ..] }`
  - `{ type: "CMaybe", child: query-sn }`
  - `{ type: "CNot", child: query-sn }`
- `query-p1` (verb phrases and relative clauses)
  - `{ type: "Is", np: query-s1 }`
  - `{ type: "Pred", arg: sparklis-arg, pred: sparklis-pred, cp: query-sn }`
  - `{ type: "Type", class: string }`
  - `{ type: "Rel", property: string, orientation: ("Fwd" | "Bwd"), np: query-s1 }`
  - `{ type: "Hier", id: int, pred: sparklis-pred, arg1: int, arg2: int, np: query-s1 }`
  - `{ type: "Triple", arg: sparklis-arg, np1: query-s1, np2: query-s1 }`
  - `{ type: "LatLong", latlong: sparklis-latlong, idlat: int, idlong: int }`
  - `{ type: "Search", constr: sparklis-constr }`
  - `{ type: "Filter", constr: sparklis-constr, filterType: ("OnlyIRIs" | "OnlyLiterals" | "Mixed" ) }`
  - `{ type: "And", children: [query-p1 ..] }`
  - `{ type: "Or", children: [query-p1 ..] }`
  - `{ type: "Maybe", child: query-p1 }`
  - `{ type: "Not", child: query-p1 }`
  - `{ type: "In", npg: query-s1, child: query-p1 }`
  - `{ type: "InWhichThereIs", np: query-s1 }`
  - `{ type: "IsThere" }`
- `query-aggreg` (grouping and aggregation phrases)
  - `{ type: "ForEachResult" }`
  - `{ type: "ForEach", id: int, modif: query-modif, rel: query-p1 or null, id2: int }`
  - `{ type: "ForTerm", term: sparklis-rdfterm, id2: int }`
  - `{ type: "TheAggreg", id: int, modif: query-modif, aggreg: sparklis-aggreg, rel: query-p1 or null, id2: int }`
- `query-expr` (expression phrases)
  - `{ type: "Undef" }`
  - `{ type: "Const", term: sparklis-rdfterm }`
  - `{ type: "Var", id: int }`
  - `{ type: "Apply", func: sparklis-func, args: [{expr: query-expr, conv: sparklis-numconv or null} ...] }`
  - `{ type: "Choice", children: [query-expr ..] }`
- `query-modif` = `{ select: bool, order: sparklis-order }`


### Datatype `sparklis-path`

This datatype specifies navigation paths in query ASTs, for instance
to locate the focus in a query. It is simply a list of instructions to
either go down in the tree (on the leftmost element), or to go right
to the next sibling element.

`[("DOWN" | "RIGHT") ...]`
