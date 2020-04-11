module salix::lib::Dagre

import salix::Core;
import salix::HTML;
import salix::Node;

import List;
import IO;

// SVG *attributes* from salix::SVG can be given to the dagre function and will be put on the SVG container
// The following props given to the dagre function will be interpreted as props for Dagre graph layout algo.
// This means that for now, you can't set props on the SVG dom object, only attributes.
// Source: https://github.com/cpettitt/dagre/wiki#configuring-the-layout

// Graph attributes/props
Attr rankdir(str rd) = prop("rankdir", rd);  // TB  Direction for rank nodes. Can be TB, BT, LR, or RL, where T = top, B = bottom, L = left, and R = right.
Attr align(str rd) = prop("align", rd); // TB  Alignment for rank nodes. Can be UL, UR, DL, or DR, where U = up, D = down, L = left, and R = right.
Attr nodesep(int ns) = prop("nodesep", "<ns>"); // 50  Number of pixels that separate nodes horizontally in the layout.
Attr edgesep(int es) = prop("edgesep", "<es>"); //10  Number of pixels that separate edges horizontally in the layout.
Attr ranksep(int rs) = prop("ranksep", "<rs>"); //50  Number of pixels between each rank in the layout.
Attr marginx(int mx) = prop("marginx", "<mx>"); // 0 Number of pixels to use as a margin around the left and right of the graph.
Attr marginy(int my) = prop("marginy", "<my>"); // 0 Number of pixels to use as a margin around the top and bottom of the graph.
Attr acyclicer() = prop("acyclicer", "greedy"); //undefined If set to greedy, uses a greedy heuristic for finding a feedback arc set for a graph. A feedback arc set is a set of edges that can be removed to make a graph acyclic.
Attr ranker(str name) = prop("ranker", name); // network-simplex  Type of algorithm to assigns a rank to each node in the input graph. Possible values: network-simplex, tight-tree or longest-path  network-


// Node rendering attributes (provide to N function)
// height/width are reused from SVG; style is also supported 
Attr shape(str name) = attr("shape", name); // // rect, circle, ellipse, diamond
Attr labelStyle(tuple[str,str] styles...) = attr("labelStyle", intercalate("; ", ["<k>: <v>" | <k, v> <- styles ]));
Attr labelStyle(map[str,str] styles) = attr("labelStyle", intercalate("; ", ["<k>: <styles[k]>" | k <- styles ]));
Attr fill(str color) = attr("fill", color);

// Edge attributes (provide to an E function)

// The following ones are from dagre-d3
Attr arrowheadStyle(tuple[str,str] styles...) = attr("arrowHeadStyle", intercalate("; ", ["<k>: <v>" | <k, v> <- styles ]));
Attr arrowheadStyle(map[str,str] styles) = attr("arrowHeadStyle", intercalate("; ", ["<k>: <styles[k]>" | k <- styles ])); 
Attr arrowheadClass(str class) = attr("arrowheadClass", class);

// See here for options: https://github.com/d3/d3-3.x-api-reference/blob/master/SVG-Shapes.md#line_interpolate
// cardinal, linear, basis, step, monotone
Attr lineInterpolate(str interp) = attr("lineInterpolate", interp);

// And these are from Dagre itself (height and width are also supported).
Attr minLen(int ml) = attr("minlen", "<ml>"); // 1 The number of ranks to keep between the source and target of the edge.
Attr weight(int w) = attr("weight", "<w>"); //  1 The weight to assign edges. Higher weight edges are generally made shorter and straighter than lower weight edges.
Attr labelPos(str pos) = attr("labelpos", pos); //  r Where to place the label relative to the edge. l = left, c = center r = right.
Attr labelOffset(int n) = attr("labeloffset", "<n>"); // 10  How many pixels to move the label away from the edge. Applies only when labelpos is l or r.
Attr edgeLabel(value val) = attr("label", "<val>");
// labelStyle also works on edges.


private data GNode = gnode(str id, map[str,str] attrs = (), Node label = txt(""));
private data GEdge = gedge(str from, str to, map[str, str] attrs = ());

alias N = void(str, list[value]);
alias E = void(str, str, list[value]);

alias G = void(N, E);

@doc{

A function to render Dagre-D3 graphs.

Usage:
dagre("myGraph", (N n, E e) {
   n("a", () {
     button(onClick(clicked()), "Hello");
   });
   
   n("b", ...)
   
   e("a", "b");
   e("b", "c");
});

The function accepts an graph id (gid) and any number of vals representing
 - attributes (put on the resulting SVG dom node)
 - props (put on the Dagre graph object (see above)
 - or a function of type G; as last argument 

The G function will be called from within `dagre` with two additional functions as arguments, n and e.
The function n is a node drawing function; e is an edge drawing function. Call these to draw nodes and edges, in
the body of the provided G function. 

N needs a node id as first argument, and accepts attrs/props and a block or string. 
If the block is given it is assumed to be a salix view function, the resulting (single) 
HTML node of which will  be embedded in the Dagre node. If it's a string it will simply 
be the node label. Attributes are interpreted as Dagre node attributes; props are ignored.

The E function receives two required node ids to draw an edge. Additionally it accepts
edge attributes (listed above).  

Grammar

Dagre ::= dagre(str, DAttr*, DBlock?)
DAttr ::= (see graph attributes above)
DBlock ::== (N n, E e) { NEStat* }
NEStat ::= n(str, NAttr*, NLabel); | e(str, str, EAttr*);
NLabel ::= str label | () { HTML } // NB: not HTML*
NAttr ::= (see node attributes above)
EAttr ::= (see edge attributes above)

NOTE: embedding another SVG image inside the HTML of a node label only works
on Firefox (as of March 2017).  
}
void dagre(str gid, value vals...) {
  list[GNode] nodes = [];
  list[GEdge] edges = [];
  
  void n(str id, value vals...) {
    GNode myNode = gnode(id);
    if (vals != []) {
      if (void() labelFunc := vals[-1]) {
        Node label = render(labelFunc);
        myNode.label = label;
      }
      else if (str label := vals[-1]) {
        myNode.label = txt(label);
      }
      myNode.attrs = attrsOf([ a | Attr a <- vals ]);
      nodes += [myNode];
    }
  }
  
  void e(str from, str to, value vals...) {
    GEdge myEdge = gedge(from, to);
    if (vals != []) {
      myEdge.attrs = attrsOf([ a | Attr a <- vals ]);
    }
    edges += [myEdge];
  }
  
  if (vals != [], G g := vals[-1]) {
    g(n, e);
  }

  build(vals, Node(list[Node] _, list[Attr] attrs) {
    return native("dagre", gid, attrsOf(attrs), propsOf(attrs), (),
      extra = ("nodes": nodes, "edges": edges));
  });
  
}

