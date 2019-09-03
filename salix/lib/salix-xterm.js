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

function registerXTerm(salix) {
	
	var xterms = {};
	
	function val2result(x) {
		if (typeof x === 'undefined') {
			return {type: 'nothing'};
		}
		if (typeof x === 'string') {
			return {type: 'string', value: x}
		}
		if (typeof x === 'number') {
			return {type: 'integer', value: x};
		}
		if (typeof x === 'boolean') {
			return {type: 'boolean', value: x};
		}
	}
	
	function nothing() {
		return {type: 'nothing'};
	}
	
	salix.Commands.getOption = function (args) {
		return val2result(xterms[args.id].getOption(args.key));
	};

	salix.Commands.setOption = function (args) {
		xterms[args.id].setOption(args.key, args.val);
		return nothing();
	};

	salix.Commands.refresh = function (args) {
		xterms[args.id].refresh(args.start, args.end, args.queue);
		return nothing();
	};
	
	salix.Commands.resize = function (args) {
		xterms[args.id].resize(args.x, args.y);
		return nothing();
	};

	salix.Commands.scrollDisp = function (args) {
		xterms[args.id].scrollDisp(args.n);
		return nothing();
	};
	
	salix.Commands.scrollPages = function (args) {
		xterms[args.id].scrollPages(args.n);
		return nothing();
	};

	salix.Commands.write = function (args) {
		var term = xterms[args.id];
		var term2 = xterms.x;
		term.write(args.text);
		return nothing();
	};

	salix.Commands.writeln = function (args) {
		xterms[args.id].writeln(args.text);
		return nothing();
	};
	
	salix.Decoders.eventData = function (args) {
		return function (data) {
			return val2result(data);
		};
	}; 
	
	salix.Decoders.keyName = function (args) {
		return function (key, event) {
			return val2result(key);
		};
	};
		
	salix.Decoders.startEnd = function (args) {
		return function (data) {
			return {type: 'int-int', value1: data.start, value2: data.end};
		};
	};
		
	salix.Decoders.colsRows = function (args) {
		return function (data) {
			return {type: 'int-int', value1: data.cols, value2: data.rows};
		};
	};
		
	salix.Decoders.ydisp = function (args) {
		return function (n) {
			return val2result(n);
		};
	};
	
	function myXterm(attach, id, attrs, props, events, extra) {
		var rows = parseInt(props['rows']);
		var cols = parseInt(props['cols']);
		var term = new Terminal({
			cols: cols,
			rows: rows,
			cursorBlink: props['cursorBlink'] === 'true'
		});
		
		xterms[id] = term;
		
		var div = document.createElement('div');
		attach(div);

		term.open(div);

		var myHandlers = {};
		
		for (var key in events) {
			// TODO: code is dupe of setEvent
			if (events.hasOwnProperty(key)) {
				var handler = salix.getNativeHandler(events[key]);
				myHandlers[key] = handler;
				term.on(key, handler);
			}
		}

		function patch(edits, attach) {
			edits = edits || [];

			for (var i = 0; i < edits.length; i++) {
				var edit = edits[i];
				var type = salix.nodeType(edit);

				switch (type) {
				
				case 'replace':
					return salix.build(edit[type].html, attach);

				case 'setAttr':
					term.element.setAttribute(edit[type].name, edit[type].val);
					break;
					
				case 'setProp':
					var key = edit[type].name;
					if (key === 'cols') {
						term.resize(parseInt(props.cols), term.y);
					}
					else if (key === 'rows') {
						term.resize(term.y, parseInt(props.rows));
					}
					else {
						term.setOption(key, val);
					}
					break;
					
				case 'setEvent': 
					var key = edit[type].name;
					var handler = salix.getNativeHandler(edit[type].handler);
					myHandlers[key] = handler;
					term.on(key, handler);
					break

				case 'removeAttr': 
					term.element.removeAttribute(edit[type].name);
					break;

				case 'removeProp':
					if (key === 'cursorBlink') {
						cm.setOption(key, false);
					}
					// else do nothing
					break;
										
				case 'removeEvent':
					var key = edit[type].name
					term.off(key, myHandlers[key]);
					delete myHandlers[key];
					break;
					
				default: 
					throw 'unsupported edit: ' + JSON.stringify(edit);
					
				}
			}
		}
		
        
		div.salix_native = {patch: patch};
		return div;
	}
	
	salix.registerNative('xterm', myXterm);
};