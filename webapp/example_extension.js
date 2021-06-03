console.log("example extension active");
sparklis_extension.afterEndpointChange =
    function() {
	window.alert("New endpoint: " + sparklis.endpoint());
    };
