/**
 * Copyright (c) Tijs van der Storm <Centrum Wiskunde & Informatica>.
 * All rights reserved.
 *
 * This file is licensed under the BSD 2-Clause License, which accompanies this project
 * and is available under https://opensource.org/licenses/BSD-2-Clause.
 * 
 * Contributors:
 *  - Tijs van der Storm - storm@cwi.nl - CWI
 */

function registerTreeView(salix) {
	
	function node2stateMap(nodes, map) {
		for (var i = 0; i < nodes.length; i++) {
			var node = nodes[i];
			map[node.data.id] = {};
			for (var k in node.state) {
				if (node.state.hasOwnProperty(k)) {
					map[node.data.id][k] = node.state[k];
				}
			}
			if (node.nodes) {
				node2stateMap(node.nodes, map);
			}
		}
		return map;
	}
	
	function fromTreeNode(treeNodes, prevState) {
		var tree = [];
		for (var i = 0; i < treeNodes.length; i++) {
			var cur = treeNodes[i];
			var node = {text: cur.tree.text};
			node.data = {id: cur.tree.text};
			if (cur.tree.nodes) {
				node.nodes = fromTreeNode(cur.tree.nodes, prevState);
			}
			if (cur.tree.attrs) {
				var attrs = cur.tree.attrs;
				if (attrs.id) {
					node.data = {id: attrs.id};
				}
				for (var k in attrs) {
					if (attrs.hasOwnProperty(k)) {
						if (k === 'checked' || k === 'disabled' || k === 'expanded' || k === 'selected') {
							if (!node.state) {
								node.state = {checked: false, disabled: false, expanded: false, selected: false};
							}
							node.state[k] = Boolean(attrs[k]);
						}
						else {
							node[k] = attrs[k];
						}
					}
				}
			}
			if (prevState && prevState.hasOwnProperty(node.data.id)) {
				var myState = prevState[node.data.id];
				for (var k in myState) {
					if (myState.hasOwnProperty(k)) {
						if (!node.state) {
							node.state = {};
						}
						if (!node.state.hasOwnProperty(k)) {
							// if it's not set by the server...
							node.state[k] = myState[k];
						}
					}
				}
			}
			tree.push(node);
		}
		return tree;
	}
	
	
	salix.Decoders.node = function (args) {
		return function (event, node) {
			return {type: 'nodeId', node: node.data.id};
		}
	};
	
//	salix.Decoders.results = function (args) {
//		return function (event, nodes) {
//			var nodeIds = [];
//			for (var i = 0; i < nodes.length; i++) {
//				nodeIds.push(nodes[i].data.id);
//			}
//			return  {type: 'listOfNodeId', results: JSON.stringify(toTreeNodes(nodes))};
//		};
//	};
	
	function addEvents(jqElt, myHandlers, events) {
		for (var key in events) {
			if (events.hasOwnProperty(key)) {
				var handler = salix.getNativeHandler(events[key]);
				myHandlers[key] = handler;
				jqElt.on(key, handler);
			}
		}
	}
	
	function reinstallHandlers(jqElt, myHandlers) {
		for (var ev in myHandlers) {
			if (myHandlers.hasOwnProperty(ev)) {
				jqElt.on(ev, myHandlers[ev]);
			}
		}
	}
	
	function treeView(attach, id, attrs, props, events, extra) {
		var div = document.createElement('div');
		div.id = id;
		attach(div);
		
		// for remove event.
		var myHandlers = {};
		
		var treeNode = extra.data;
		var options = attrs;
		options.data = fromTreeNode(treeNode);
		var dom = '#' + id;
		$(dom).treeview(options);
		addEvents($(dom), myHandlers, events);
		
		function patch(edits, attach) {
			edits = edits || [];

			for (var i = 0; i < edits.length; i++) {
				var edit = edits[i];
				var type = salix.nodeType(edit);

				switch (type) {
				
				case 'setExtra':
					var oldNodes = [];
					var root = $(dom).treeview(true).getNode(0);
					oldNodes.push(root);
					var siblings = $(dom).treeview(true).getSiblings(root);
					oldNodes = oldNodes.concat(siblings);
					//console.log($(dom).treeview(true));
					options.data = fromTreeNode(edit[type].value, node2stateMap(oldNodes, {}));
					// PROBLEM: this resets expanded/selected/etc.
					// state. So this would suggest that we
					// *do* want a dedicate tree data type to be
					// used as (view) model of viewTree...
					// but it also means that we need to deal
					// with all events that change this state.
					// or we just copy the old state elements to the new one
					// since nodes have ids anyway. 
					$(dom).treeview(options);
					reinstallHandlers($(dom), myHandlers);
					break;
					
				
				case 'setAttribute':
					options[edit[type].name] = edit[type].value;
					$(dom).treeview(options);
					reinstallHandlers($(dom), myHandlers);
					break;
					
				case 'removeAttribute':
					delete options[edit[type].name];
					$(dom).treeview(options);
					reinstallHandlers($(dom), myHandlers);
					break;
				
				case 'replace':
					salix.build(edit[type].html, attach);
					break;

				case 'setEvent': 
					var key = edit[type].name;
					var handler = salix.getNativeHandler(edit[type].handler);
					myHandlers[key] = handler;
					$(dom).on(key, handler);
					break
				
				case 'removeEvent':
					var key = edit[type].name
					$(dom).off(key, myHandlers[key]);
					delete myHandlers[key];
					break;
					
				default: 
					throw 'unsupported edit: ' + JSON.stringify(edit);
					
				}
			}
		}
		
		div.salix_native = {patch: patch};
	}
	
	function doCommand(cmd) {
		// TODO
	}
	
	salix.registerNative('treeView', treeView);
};