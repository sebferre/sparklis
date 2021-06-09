console.log("example extension active");
sparklis_extension.hookSparql =
    function(sparql) {
	console.log("endpoint:", sparklis.endpoint());
	console.log("permalink:", sparklis.place.permalink());
	console.log("SPARQL query:", sparql);
	console.log("Here a dummy PREFIX is added.");
	return "PREFIX foo: <http://foo.com/>\n" + sparql
    };
sparklis_extension.hookResults =
    function(results) {
	console.log("results", results);
	sparklis.evalSparql("SELECT * WHERE { ?x a ?c } LIMIT 10",
			    function(res) { console.log("other results:", res); },
			    function(code) { console.log("failed to get the other results, error", code); });
	console.log("Here the first two rows of the results will be selected.");
	results.rows = results.rows.slice(0,2);
	return results
    };
