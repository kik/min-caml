let limit = ref 1000

let rec erase { Expr.shape = t; Expr.ty = _ } =
  match t with
  | Expr.ECall({ Expr.shape = tf; Expr.ty = _ } as ef, args) -> begin
    match (tf, args) with
    | (Expr.EVar("not"), [e1]) -> Syntax.Not(erase e1) (* tenuki *)
  (*  | (Expr.EVar("and"), [e1; e2]) -> Syntax.(erase e1, erase e2) (* tenuki *)*)
  (*  | (Expr.EVar("or"), [e1; e2]) -> Syntax.(erase e1, erase e2) (* tenuki *)*)
    | (Expr.EVar("=="), [e1; e2]) -> Syntax.Eq(erase e1, erase e2) (* tenuki *)
    | (Expr.EVar("!="), [e1; e2]) -> Syntax.Not(Syntax.Eq(erase e1, erase e2)) (* tenuki *)
    | (Expr.EVar("<"), [e1; e2]) -> Syntax.Not(Syntax.Eq(erase e2, erase e1)) (* tenuki *)
    | (Expr.EVar(">"), [e1; e2]) -> Syntax.Not(Syntax.LE(erase e1, erase e2)) (* tenuki *)
    | (Expr.EVar("<="), [e1; e2]) -> Syntax.LE(erase e1, erase e2) (* tenuki *)
    | (Expr.EVar(">="), [e1; e2]) -> Syntax.LE(erase e2, erase e1) (* tenuki *)
    | (Expr.EVar("+"), [e1; e2]) -> Syntax.Add(erase e1, erase e2) (* tenuki *)
    | (Expr.EVar("-"), [e1; e2]) -> Syntax.Sub(erase e1, erase e2) (* tenuki *)
  (*  | (Expr.EVar("*"), [e1; e2]) -> Syntax.(erase e1, erase e2) (* tenuki *) *)
  (*  | (Expr.EVar("/"), [e1; e2]) -> Syntax.(erase e1, erase e2) (* tenuki *) *)
  (*  | (Expr.EVar("%"), [e1; e2]) -> Syntax.(erase e1, erase e2) (* tenuki *) *)
    | (Expr.EVar("unary-"), [e1]) -> Syntax.Neg(erase e1) (* tenuki *)
    | _ -> Syntax.App(erase ef, List.map erase args)
  end

  | Expr.EVar(name) -> Syntax.Var(name)
  | Expr.EBool(b) -> Syntax.Bool(b)
  | Expr.EInt(n) -> Syntax.Int(n)
  | Expr.EFun(params, _, e) ->
    let name = Id.genid "lambda" in
    Syntax.LetRec({
      Syntax.name = (name, Type.gentyp ());
      Syntax.args = List.map (function (name, _, _) -> (name, Type.gentyp ())) params;
      Syntax.body = erase e
    }, Syntax.Var(name))
  | Expr.ELet(name, e1, e2) -> Syntax.Let((name, eraset e1.Expr.ty), erase e1, erase e2)
  | Expr.EIf(e1, e2, e3) -> Syntax.If(erase e1, erase e2, erase e3)
  | Expr.ECast(e1, _, _) -> erase e1
and eraset t =
  match t with
  | Expr.TConst("unit") -> Type.Unit
  | Expr.TConst("bool") -> Type.Bool
  | Expr.TConst("int") -> Type.Int
  | Expr.TApp("array", [ty]) -> Type.Array(eraset t)
  | Expr.TArrow(params, ty) -> Type.Fun(List.map erasert params, erasert ty)
  | Expr.TVar(name) -> begin
    match !name with
    | Expr.Unbound(i, j) -> Type.gentyp ()
    | Expr.Link(t) -> eraset t
    | Expr.Generic(i) -> Type.gentyp ()
  end
  | _ ->
    Printf.printf "t_expr: %s\n" (Printing.string_of_t_ty t);
    assert false
and erasert rt =
  match rt with
  | Expr.Plain(t) -> eraset t
  | Expr.Named(_, t) -> eraset t
  | Expr.Refined(_, t, _) -> eraset t

let rec iter n e = (* 最適化処理をくりかえす (caml2html: main_iter) *)
  Format.eprintf "iteration %d@." n;
  if n = 0 then e else
  let e' = Elim.f (ConstFold.f (Inline.f (Assoc.f (Beta.f e)))) in
  if e = e' then e else
  iter (n - 1) e'

let lexbuf outchan l = (* バッファをコンパイルしてチャンネルへ出力する (caml2html: main_lexbuf) *)
  Id.counter := 0;
  Typing.extenv := M.empty;
  let expr = Rparser.expr_eof Rlexer.token l in
  Printf.printf "s_expr: %s\n" (Printing.string_of_s_expr expr);
  let expr = Infer.infer_expr Core.plain_env 0 expr in
  Refined.check_expr expr;
  Printf.printf "t_expr: %s\n" (Printing.string_of_t_expr expr);
  Emit.f outchan
    (RegAlloc.f
       (Simm.f
	  (Virtual.f
	     (Closure.f
		(iter !limit
		   (Alpha.f
		      (KNormal.f
			 (Typing.f
			    (erase expr)))))))))

let string s = lexbuf stdout (Lexing.from_string s) (* 文字列をコンパイルして標準出力に表示する (caml2html: main_string) *)

let file f = (* ファイルをコンパイルしてファイルに出力する (caml2html: main_file) *)
  let inchan = open_in (f ^ ".ml") in
  let outchan = open_out (f ^ ".s") in
  try
    lexbuf outchan (Lexing.from_channel inchan);
    close_in inchan;
    close_out outchan;
  with e -> (close_in inchan; close_out outchan; raise e)

let () = (* ここからコンパイラの実行が開始される (caml2html: main_entry) *)
  let files = ref [] in
  Arg.parse
    [("-inline", Arg.Int(fun i -> Inline.threshold := i), "maximum size of functions inlined");
     ("-iter", Arg.Int(fun i -> limit := i), "maximum number of optimizations iterated")]
    (fun s -> files := !files @ [s])
    ("Mitou Min-Caml Compiler (C) Eijiro Sumii\n" ^
     Printf.sprintf "usage: %s [-inline m] [-iter n] ...filenames without \".ml\"..." Sys.argv.(0));
  List.iter
    (fun f -> ignore (file f))
    !files
