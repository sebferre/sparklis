console.log("example extension active");
sparklis_extension.hookSparql =
    function(sparql) {
	console.log(sparql);
	console.log("Here a dummy PREFIX is added.");
	return "PREFIX foo: <http://foo.com/>\n" + sparql
    };
sparklis_extension.hookResults =
    function(results) {
	console.log(results);
	console.log("Here the first two rows of the results will be selected.");
	results.rows = results.rows.slice(0,2);
	return results
    };
