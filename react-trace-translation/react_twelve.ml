type attr 
  = Attr of string * string
  | OnClick of (unit -> unit)

type view =
  | Text  of string
  | Tag of attr list * view list
  | Spec of (unit -> bool ref * (unit -> view))

type tree =
  | Lit of string
  | Node of string * attr list * tree list
  | Path of ((unit -> view) * tree * bool ref) ref

let ctr = ref(0)
let fresh () =
  let x = "id" ^ (Int.to_string (!ctr)) in
  ctr := !ctr + 1; x

let rec init v = match v with
  | Text str -> Lit str
  | Tag(attrs, children) -> Node(fresh(), attrs, List.map init children)
  | Spec(c) ->
    let (flag, thunk) = c () in
    let view = thunk () in
    let tree = init view in
    let cell = ref(thunk, tree, flag) in
    Path(cell)

let rec check t = match t with
  | Lit _ -> ()
  | Node(_, _, children) -> List.iter check children
  | Path(p) ->
    let thunk, child, flag = !p in
    if !flag
      then (flag := false; 
        let view = thunk () in
        let tree = init view in 
        p := (thunk, tree, flag))
      else check child

let rec scan a = match a with
  | Attr(_, _) -> ()
  | OnClick h -> h ()

let rec search id t = match t with
  | Lit _ -> ()
  | Path (p) -> let _, child, _ = !p in search id child
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
  let cs = List.init x (fun y -> Spec(fun () -> child y)) in
  flag, fun () ->
    let x = !xl in
    let cs = List.init x (fun y -> Spec(fun () -> child y)) in
    Tag([OnClick(fun () -> xset (x + 1))], cs)

(* generate a unique name for each useState 
make them option-types, initializing
map (heterogeneous), "box" type somehow?

tuple-of-state; 
*)

let toplevel = Tag([Attr("color", "red")], [Spec(fun () -> parent ())])

type html
  = HtmlText of string
  | HtmlTag of string * attr list * html list

let rec realize t = match t with
  | Lit str -> HtmlText str
  | Node(id, attrs, children) -> HtmlTag(id, attrs, List.map realize children)
  | Path(p) -> let _, child, _ = !p in realize child

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