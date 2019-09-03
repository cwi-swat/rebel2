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

function registerCharts(salix) {
	
	var charts = {};
	
	function parseDataTable(gtable) {
		var data = new google.visualization.DataTable();
		var cols = gtable.gtable.columns;
		for (var i = 0; i < cols.length; i++) {
			var col = cols[i].gcolumn;
			data.addColumn({type: col.type, role: col.role, label: col.label});
		}
		var rows = gtable.gtable.rows;
		for (var i = 0; i < rows.length; i++) {
			var cells = rows[i].grow.cells;
			var rowCells = [];
			for (var j = 0; j < cells.length; j++) {
				rowCells.push({v: cells[j].gcell.v, f: cells[j].gcell.formatted});
			}
			data.addRow(rowCells);
		}
		return data;
	}
	
	function myCharts(attach, id, attrs, props, events, extra) {
		var chartType = extra.chartType;

		// todo: attrs and props on this div.
		var div = document.createElement('div');
		attach(div);

		
		var chart = new google.visualization[chartType](div);
		chart.draw(parseDataTable(extra.dataTable), extra.options);
		charts[id] = chart;
		
		var myHandlers = {};

		function patch(edits, attach) {
			edits = edits || [];
			var patching = charts[id]; // TODO: this is not needed because of capturing data from myCharts.
			
			for (var i = 0; i < edits.length; i++) {
				var edit = edits[i];
				var type = salix.nodeType(edit);

				switch (type) {
				
				case 'setExtra':
					if (edit.setExtra.name === 'dataTable') {
						// todo: options may have changed to
						patching.draw(parseDataTable(edit.setExtra.value), extra.options);
					}
					else if (edit.setExtra.name === 'options') {
						console.log("ERROR: options not supported yet");
					}
					break;
				
				case 'replace':
					delete charts[id];
					salix.build(edit[type].html, attach);
					break;

				}
			}
		}
		
        
		div.salix_native = {patch: patch};
		return div;
	}
	
	salix.registerNative('charts', myCharts);
};