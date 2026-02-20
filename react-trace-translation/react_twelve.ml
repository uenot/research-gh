type attr 
  = Attr of string * string
  | OnClick of (unit -> unit)

type view =
  | Text : string -> view
  | Tag : attr list * view list -> view
  | Spec : 'a component * 'a -> view

and 'a component = 'a -> (bool ref * (unit -> view))

type tree =
  | Lit : string -> tree
  | Node : string * attr list * tree list -> tree
  | Path : (unit -> view) * tree ref * bool ref -> tree

let ctr = ref(0)
let fresh () =
  let x = "id" ^ (Int.to_string (!ctr)) in
  ctr := !ctr + 1; x

(*
types: string, bool, attr, view, tree, ID, a->a, ref a, [a], cell/pairs
destructors: bool, attr, view, tree, list
id functions: fresh, eq
refs
recursive functions

constants: map, init, check, scan, search, event-loop?
*)

let rec init v = match v with
  | Text str -> Lit str
  | Tag(attrs, children) -> Node(fresh(), attrs, List.map init children)
  | Spec(c, v') ->
    let (flag, thunk) = c v' in
    Path(thunk, ref(init(thunk ())), flag)

let rec check t = match t with
  | Lit _ -> ()
  | Node(_, _, children) -> List.iter check children
  | Path(thunk, child, flag) ->
    if !flag
      then (flag := false; child := init (thunk ()))
      else check !child

let rec scan a = match a with
  | Attr(_, _) -> ()
  | OnClick h -> h ()

let rec search id t = match t with
  | Lit _ -> ()
  | Path (_, t', _) -> search id !t'
  | Node(id', attrs, children) ->
    (if id = id'
      then List.iter scan attrs
    else ()); List.iter (search id) children

(*
let child prop =
  let x, xset = useState(prop) in
  Tag([OnClick(fun () -> xset (x+1))], [Text(Int.to_string x)])
*)

let child prop =
  let flag = ref(false) in
  let xl = ref(prop) in
  let xset = fun x -> xl := x; flag := true in
  let x = !xl in
  flag, fun () ->
    let x = !xl in
    Tag([OnClick(fun () -> xset (x + 1))], [Text(Int.to_string x)])

(*
let parent prop =
  let x, xset = useState(false) in
  let cs = List.init x (fun y -> Spec(child, y)) in
  Tag([OnClick(fun () -> xset (x+1))], cs)
*)
let parent () =
  let flag = ref(false) in
  let xl = ref(0) in
  let xset = fun x -> xl := x; flag := true in
  let x = !xl in
  let cs = List.init x (fun y -> Spec(child, y)) in
  flag, fun () ->
    let x = !xl in
    let cs = List.init x (fun y -> Spec(child, y)) in
    Tag([OnClick(fun () -> xset (x + 1))], cs)

let toplevel = Tag([Attr("color", "red")], [Spec(parent, ())])

type html
  = HtmlText of string
  | HtmlTag of string * attr list * html list

let rec realize t = match t with
  | Lit str -> HtmlText str
  | Node(id, attrs, children) -> HtmlTag(id, attrs, List.map realize children)
  | Path(_, t', _) -> realize !t'

let fmt_attr attr =  match attr with
  | Attr(k, v) -> k ^ "=" ^ v
  | OnClick _ -> "onClick={...}"

let rec fmt_html_indent i h = (String.make i ' ') ^ match h with
  | HtmlText txt -> txt
  | HtmlTag(tag, attrs, children) ->
    let pretty_attrs = "" ::List.map fmt_attr attrs |> String.concat " " in
    let prefix = "<" ^ tag ^ pretty_attrs in
    match children with
      | [] -> prefix ^ " />"
      | [HtmlText txt] -> prefix ^ ">" ^ txt ^ "</" ^ tag ^ ">"
      | _ -> 
          let pretty_children = List.map (fmt_html_indent (i+2)) children |> String.concat "\n" in
          prefix ^ ">\n" ^ pretty_children ^ "\n" ^ (String.make i ' ') ^ "</" ^ tag ^ ">"

let fmt_html = fmt_html_indent 0

let rec event_loop root =
  root |> realize |> fmt_html |> print_endline;
  let tgt = read_line() in
  if tgt = "quit"
  then ()
  else search tgt root; check root; event_loop root

let run () = event_loop (init toplevel)