function registerSMCat(salix) {
	

	function mySMCat(attach, id, attrs, props, events, extra) {
    var _svg = document.createElement("div");
    _svg.innerHTML = sm.renderSvg(extra.model);
		_svg.id = id;
		attach(_svg);
		
		function patch(edits, attach) {
			for (var i = 0; i < edits.length; i++) {
				var edit = edits[i];
				var type = salix.nodeType(edit);

				switch (type) {
				
				case 'setAttr': 
					// _svg.setAttribute(edit[type].name, edit[type].val);
					break;
					
				case 'removeAttr': 
					// _svg.removeAttribute(edit[type].name);
					break;

				case 'setProp': 
					props[edit[type].name] = edit[type].val;
					rerender = true;
					break;
					
				case 'removeProp': 
					delete props[edit[type].name];
					rerender = true;
					break;

				case 'setExtra':
          if (edit.setExtra.name === 'model') {
            _svg.innerHTML = sm.renderSvg(edit.setExtra.value);
          }
					break;
				
				case 'replace':
					// salix.build(edit[type].html, attach);
					break;
				}
			}
			
			// if (newNodes && newEdges) {
			// 	var newG = dagreGraph(newNodes, newEdges, props);
			// 	nodes = newNodes;
			// 	edges = newEdges;
			// 	render(svgGroup, newG);
			// }
			// else if (newNodes) {
			// 	var newG = dagreGraph(newNodes, edges, props);
			// 	nodes = newNodes;
			// 	render(svgGroup, newG);
			// }
			// else if (newEdges) {
			// 	var newG = dagreGraph(nodes, newEdges, props);
			// 	edges = newEdges;
			// 	render(svgGroup, newG);
			// }
			// else if (rerender) { // because of props change
			// 	var newG = dagreGraph(nodes, edges, props);
			// 	render(svgGroup, newG);
			// }
			
		}
		       
		_svg.salix_native = {patch: patch};
		return _svg;
	}
	
	salix.registerNative('smCat', mySMCat);
};