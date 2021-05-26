<meta charset="UTF-8"/>

# What is Sparklis?

Sparklis is a query builder in natural language that allows people to explore and query SPARQL endpoints with all the power of SPARQL and without any knowledge of SPARQL, nor of the endpoint vocabulary.

Sparklis is a Web client running entirely in the browser. It directly connects to SPARQL endpoints to retrieve query results and suggested query elements. It covers a large subset of SPARQL 1.1 `SELECT` queries: basic graph patterns including cycles, `UNION`, `OPTIONAL`, `NOT EXISTS`, `FILTER`, `BIND`, complex expressions, aggregations, `GROUP BY`, `ORDER BY`. All those features can be combined in a flexible way, like in SPARQL. Results are presented as tables, and also on maps. A
configuration panel offers a few configuration options to adapt to different endpoints (e.g., GET/POST, labelling properties and language tags). Sparklis also includes the YASGUI editor to let advanced users access and modify the SPARQL translation of the query.

Sparklis reconciles expressivity and usability in semantic search by tightly combining a Query Builder, a Natural Language Interface, and a Faceted Search system. As a *Query Builder* it lets users build complex queries by composing elementary queries in an incremental fashion. An elementary query can be a class (e.g., "a film"), a property (e.g., "that has a director"), a RDF node (e.g., "Tim Burton"), a reference to another node (e.g., "the film"), or an operator (e.g., "not", "or", "highest-to-lowest", "+", "average").

As a *Faceted Search system*, at every step, the query under construction is well-formed, query results are computed and displayed, and the suggested query elements are derived from actual data - not only from schema - so as to prevent the construction of non-sensical or empty results. The display of results and data-relevant suggestions at every step provides constant and acurate feedback to users during the construction process. This supports exploratory search, serendipity, and confidence about final results.

As a *Natural Language Interface*, everything presented to users - queries, suggested query elements, and results - are verbalized in natural language, completely hidding SPARQL behind the user interface. Compared to Query Answering (QA) systems, the hard problem of spontaneous NL understanding is avoided by controlling query formulation through guided query construction, and replaced by the simpler problem of NL generation. The user interface lends itself to multilinguality, and is so far available in English, French, Spanish, and Dutch.

When refering to Sparklis in scientific documents, please use the following citation.

> Sébastien Ferré: *Sparklis: An expressive query builder for SPARQL endpoints with guidance in natural language.* Semantic Web 8(3): 405-418 (2017)

# Where can I try Sparklis?

Simply follow those steps:
1. Go to the [online application](http://www.irisa.fr/LIS/ferre/sparklis/)
2. Select a SPARQL endpoint in the dropdown list at the top (the default one is *Core English DBpedia*, a core subset of DBpedia)
3. Build your query incrementally by clicking suggested query elements (in the three lists of suggestions, and through the hamburger menu in the query), and clicking different parts of the query to change focus. The suggestions are relative to the current focus.

We recommend to visit the [*Examples page*](http://www.irisa.fr/LIS/ferre/sparklis/examples.html) where there are 100+ example queries over several datasets. Every example query can be opened in Sparklis in one click, and the query can then be further modified. For a number of them, there is a YouTube screencast to show how they are built step by step.

# How can I use Sparklis on my own RDF dataset?

It is enough to have a SPARQL endpoint for your dataset that is visible from your machine. It can be a publicly open endpoint (like for DBpedia or Wikidata), or a localhost endpoint (I personally use Apache Jena Fuseki but other stores should work too). The one important condition is that the endpoint server be [CORS-enabled](https://www.w3.org/wiki/CORS_Enabled) so that HTTP requests can be made to it from your browser, where Sparklis runs.

Here a few recommendations about the contents of your store for best results:
* include RDFS/OWL triples declaring classes (`rdfs:Class`, `owl:Class`) and properties (`rdf:Property`, `owl:ObjectProperty`, `owl:DataProperty`), as well as their labels (`rdfs:label`) and their hierarchy (`rdfs:subClassOf`, `rdfs:subPropertyOf`)
* ensure that all URI-resources have their label defined, preferably with `rdfs:label` and possibly with other standard properties (e.g., `skos:prefLabel`)
* if named graphs are used, make sure to configure your store so that the default graphs contains the union of those named graphs

The *Configure* menu offers a number of options to adapt Sparklis to your endpoint, and control the display. Here is a non-exhaustive list:
* Endpoint and queries: max numbers of results/suggestions, GET vs POST, credentials
* Ontology: display of class/property hierarchies, filtering of classes/properties, use of Sparklis-specific schema properties (see below)
* Language and labels: interface language, labelling properties, fulltext search support

Sparklis makes use of standard and non-standard properties to get more control on the building of queries, and on the display of suggestions and results. For ech property, there is generally a configuration option to activate its use.
* `sdo:position` (`sdo: = https://schema.org/`): it is possible to control the ordering of suggestions (classes, properties, and individuals) by setting this property with the desired rank of the suggestion. The related option is in *Configure advanced features*.
* `sdo:logo`: it is possible to have small icons in front of entity labels by setting this property with URLs to those icons. Several icons can be attached to a same entity. The related option is in *Configure advanced features*, where the size of icons can be defined.
* `rdfs:inheritsThrough`: suppose you have a `ex:location` property whose range `ex:Place` is organized into a hierarchy through the property `ex:isPartOf`. By adding to your dataset the triple `ex:location rdfs:inheritsThrough ex:isPartOf`, you get that whenever property `ex:location` is inserted into the query, inheritance through the place hierarchy is performed, and place suggestions are displayed as a tree. This is a generalization of the well-known `rdf:type` inheritance through `rdfs:subClassOf`. By adding triple `ex:Place rdfs:inheritsThrough ex:isPartOf`, the same effect is obtained when inserting class `ex:Place`. The related option in *Configure the ontology* must be activated.
* `lis-owl:transitiveOf` (`lis-owl: = http://www.irisa.fr/LIS/ferre/vocab/owl#`): the use of `rdfs:inheritsThrough` entails the insertion of transitive paths (e.g., `ex:isPartOf*`) in the SPARQL query, which are very costly to evaluate. One solution is to materialize the transitive closure as a new property `ex:isPartOf_star` in the dataset, and to add the triple `ex:isPartOf_star lis-owl:transitiveOf ex:isPartOf`. By activating the related option in *Configure the ontology*, property path `ex:isPartOf*` will be replaced by `ex:isPartOf_star`.
* `nary:subjectObject` (`nary: = http://www.irisa.fr/LIS/ferre/vocab/nary#`): this property handles the case of a reified relationship where there is a property `PS` from reification node to subject, and a property `PO` from reification node to object. By adding triple `PS nary:subjectObject PO`, the reification becomes transparent in Sparkls. See cyan properties on the Mondial endpoint for examples. The related option in *Configure the ontology* must be activated.
* `nary:eventObject`: this is similar as above, except there is a property `PE` from subject to reification node (instead of the inverse `PS`). See cyan properties in the Wikidata endpoint for examples.

Once you have found a good configuration of your endpoint, you can generate a *permalink* with the button at the top, which you can share to the endpoint users. Those permalinks also include the current query and current focus, so you can also share example queries and template queries. You can also save queries by simply adding bookmarks in your browser.

If you find your endpoint of general interest, you are welcome to suggest me to add it to the list of SPARQL endpoints.

# How do I reuse Sparklis in my web site?

As Sparklis is only client-side code, it is possible to integrate Sparklis into your website by simply copying the contents of the `webapp` folder among your website files, and adding links to it from your web pages, with URL arguments containing the endpoint, the configuration, and possibly an initial query. To get those URLs, simply navigate in Sparklis and copy (and adapt as needed) the browser URL.

You can adapt the appearance of the main HTML file (`osparklis.html`, `osparklis.css`) as long as you retain the *Sparklis* name, and the credits in the page footer. You can for instance hide some configuration options and elements, you can change the look-and-feel, and the layout of elements. Be careful not to delete element ids and classes that are used by the JS code of Sparklis.

Let me know of successful integrations, and also of problems you encounter in the process.

# Credits

Author: [Sébastien Ferré](http://people.irisa.fr/Sebastien.Ferre/)

Affiliation: Univ. Rennes 1, team [SemLIS](http://www-semlis.irisa.fr/) at IRISA

Copyright © 2013 Sébastien Ferré, IRISA, Université de Rennes 1, France

Licence: Apache Licence 2.0

