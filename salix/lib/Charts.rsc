module salix::lib::Charts

import salix::Node;
import salix::Core;

private data DataTable
  = gtable(list[Column] columns, list[Row] rows);

private data Row
  = grow(list[Cell] cells);  

private data Column
  = gcolumn(str \type, str role="", str label="", str id="");
  
private data Cell
  = gcell(value v, str formatted = "", map[str, value] props = ());
  

// Table options (TODO: extend to full list of options)
Attr legend(str pos) = attr("legend", pos); // e.g. left
Attr title(str t) = attr("title", t); 

// TODO: think about using keyword params after all for this
// the namespace is getting saturated...

data ColAttr
 = role(str name) 
 | label(str l)
 | id(str id)
 ;

data CellAttr 
  = formatted(str f)
  | property(str name, value val)
  ;



alias DT = void(C, R);
alias C = void(str, list[value]);
alias R = void(void(Ce));
alias Ce = void(value, list[value]);

// See here for what kind of data and options each chart type supports:
// https://developers.google.com/chart/interactive/docs/gallery
// NB: some charts need special loading instructions to Google Charts.

void annotationChart(str id, value vals...) = chart(id, "AnnotationChart", vals);
void areaChart(str id, value vals...) = chart(id, "AreaChart", vals);
void barChart(str id, value vals...) = chart(id, "BarChart", vals);
void bubbleChart(str id, value vals...) = chart(id, "BubbleChart", vals);
void calendarChart(str id, value vals...) = chart(id, "Calendar", vals);
void candlestickChart(str id, value vals...) = chart(id, "CandlestickChart", vals);
void columnChart(str id, value vals...) = chart(id, "ColumnChart", vals);
void comboChart(str id, value vals...) = chart(id, "ComboChart", vals);
void ganttChart(str id, value vals...) = chart(id, "Gantt", vals);
void gaugeChart(str id, value vals...) = chart(id, "Gauge", vals);
void geoChart(str id, value vals...) = chart(id, "GeoChart", vals);
void histogramChart(str id, value vals...) = chart(id, "Histogram", vals);
void lineChart(str id, value vals...) = chart(id, "LineChart", vals);
void mapChart(str id, value vals...) = chart(id, "Map", vals);
void pieChart(str id, value vals...) = chart(id, "PieChart", vals);
void sankeyChart(str id, value vals...) = chart(id, "Sankey", vals);
void scatterChart(str id, value vals...) = chart(id, "ScatterChart", vals);
void steppedAreaChart(str id, value vals...) = chart(id, "SteppedAreaChart", vals);
void tableChart(str id, value vals...) = chart(id, "Table", vals);
void timelineChart(str id, value vals...) = chart(id, "Timeline", vals);
void treeMapChart(str id, value vals...) = chart(id, "TreeMap", vals);
void wordTreeChart(str id, value vals...) = chart(id, "WordTree", vals);



@doc{Chart: draw a google chart; the API provides functions to "draw"
a Google Chart DataTable which will be rendered as a chart.

Example:

```
chart("bla", "BarChart", (C col, R row) {
  col("number"); col("string");
  for (bla <- foo) {
     row((Ce cell) { 
       cell(bla[0]);
       cell(bla[1]);
       ...
     }
  }
});
```

Grammar:

Chart ::= char(str id, str type, TAttr*, CRBlock?)
TAttr ::= (see above)
CRBlock ::= (C col, R row) { CRStat* }
CRStat ::= col(str type, ColAttr*) | row(RBlock)
ColAttr ::= (see above)
RBlock ::= (Ce cell) { RStat* }
RStat ::= cell(value, CellAttr*)
CellAttr ::= (see above) 
}
void chart(str id, str chartType, value vals...) {
  DataTable myTable = gtable([], []); 
  
  void col(str \type, value vals...) {
    Column c = gcolumn(\type);
    for (ColAttr a <- vals) {
      switch (a) {
        case label(str l): c.label = l;
        case role(str r): c.role = r;
        case id(str i): c.id = i;
      }
    }
    myTable.columns += [c]; 
  }
  
  void row(void(Ce) block) {
    list[Cell] myRow = [];
    
    void cell(value v, value vals...) {
      Cell c = gcell(v);
      for (CellAttr a <- vals) {
        switch (a) {
          case formatted(str f): c.formatted = f;
          case property(str k, value v): c.props?() += (k: v);
        }
      }
      myRow += [c];   
    }
    
    block(cell);
    
    myTable.rows += [grow(myRow)];
  }
  
  if (vals != [], DT dt := vals[-1]) {
    dt(col, row);
  }

  return build(vals, Node(list[Node] _, list[Attr] attrs) {
       return native("charts", id, (), (), (),
         extra = (
           "chartType": chartType,
           "dataTable": myTable,
           "options": attrsOf(attrs)
         ));
    });
} 

  