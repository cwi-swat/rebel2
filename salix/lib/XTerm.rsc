@license{
  Copyright (c) Tijs van der Storm <Centrum Wiskunde & Informatica>.
  All rights reserved.
  This file is licensed under the BSD 2-Clause License, which accompanies this project
  and is available under https://opensource.org/licenses/BSD-2-Clause.
}
@contributor{Tijs van der Storm - storm@cwi.nl - CWI}

module salix::lib::XTerm

import salix::Core;
import salix::Node;


// http://xtermjs.org/docs/api/Terminal/

Cmd blur(Msg f, str id) = command("blur", encode(f), args = ("id": id));

Cmd clear(Msg f, str id) = command("clear", encode(f), args = ("id": id));

Cmd destroy(Msg f, str id) = command("destroy", encode(f), args = ("id": id));

Cmd focus(Msg f, str id) = command("focus", encode(f), args = ("id": id));

Cmd reset(Msg f, str id) = command("reset", encode(f), args = ("id": id));

Cmd scrollToTop(Msg f, str id) = command("scrollToTop", encode(f), args = ("id": id));

Cmd scrollToBottom(Msg f, str id) = command("scrollToBottom", encode(f), args = ("id": id));

Cmd getOption(Msg(str) f, str id, str key) 
  = command("getOption", encode(f), args = ("id": id, "key": key));

Cmd setOption(Msg f, str id, str key, value val) 
  = command("getOption", encode(f), args = ("id": id, "key": key, "val": val));

Cmd scrollDisp(Msg f, str id, int n)  
  = command("scrollDisp", encode(f), args = ("id": id, "n": n));

Cmd scrollPages(Msg f, str id, int n)
  = command("scrollPages", encode(f), args = ("id": id, "n": n));

Cmd write(Msg f, str id, str text) 
  = command("write", encode(f), args = ("id": id, "text": text));

Cmd writeln(Msg f, str id, str text)   
  = command("writeln", encode(f), args = ("id": id, "text": text));

Cmd refresh(Msg f, str id, int \start, int end, bool queue) 
  = command("refresh", encode(f), args = ("id": id, "start": \start, "end": end, "queue": queue));

Cmd resize(Msg f, str id, int x, int y)
  = command("resize", encode(f), args = ("id": id, "x": x, "y": y));
  
void xterm(str id, value vals...) 
  = build(vals, Node(list[Node] _, list[Attr] attrs) {
       return native("xterm", id, attrsOf(attrs), propsOf(attrs), eventsOf(attrs));
    });


// Attributes/properties/events

Attr cols(int val) = prop("cols", "<val>");

Attr rows(int val) = prop("rows", "<val>");

Attr cursorBlink(bool b) = prop("cursorBlink", "<b>");

// standard: blur, focus, keydown, keypress

Attr onData(Msg(str) str2msg) = event("data", handler("eventData", encode(str2msg)));

Attr onKey(Msg(str) str2msg) = event("key", handler("keyName", encode(str2msg)));

Attr onOpen(Msg msg) = event("open", succeed(encode(msg)));

Attr onRefresh(Msg(int, int) int22msg) = event("refresh", handler("startEnd", encode(int22msg)));

Attr onResize(Msg(int, int) int22msg) = event("resize", handler("colsRows", encode(int22msg)));

Attr onScroll(Msg(int) int2msg) = event("scroll", handler("ydisp", encode(int2msg)));

Msg parseMsg("int-int", Handle h, map[str, str] p)
  = applyMaps(h, decode(h, #Msg(int,int))(toInt(params["value1"]), toInt(params["value2"])));




