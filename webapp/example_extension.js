console.log("example extension active");
sparklis_extension.hookResults =
    function(results) {
	window.alert("Here I will select the first two rows in the results.");
	results.rows = results.rows.slice(0,2);
	return results
    };
