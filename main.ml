(* ================== TIPOS DE DADOS ================== *)

type bop =
  | Sum | Sub | Mul | Div
  | Eq  | Neq | Lt | Gt
  | And | Or

type tipo =
  | TyInt
  | TyBool
  | TyRef of tipo
  | TyUnit

type endereco = int

(* Agora Loc representa uma localização na memória *)
type expr =
  | Num of int
  | Bool of bool
  | Id of string
  | If of expr * expr * expr
  | Binop of bop * expr * expr
  | Let of string * tipo * expr * expr
  | Wh of expr * expr
  | Asg of expr * expr
  | New of expr
  | Deref of expr
  | Unit
  | Seq of expr * expr
  | Read
  | Print of expr
  | Loc of endereco  (* Adicionado: para representar endereços como valores *)

(* ================== AMBIENTES ================== *)

type memoria = (endereco * expr) list
let input : int list ref = ref []
let output : int list ref = ref []

(* ================== EXCEÇÕES ================== *)

exception StepError of string
exception TypeError of string
exception NotValue of string

let msg_booleanos = "Ambos os operandos devem ser booleanos."
let msg_relacionais_aritmeticos = "Ambos os operandos devem ser inteiros."
let msg_thenelse = "As expressões do então e do senão devem ter o mesmo tipo."
let msg_condicao = "A condição do if deve ser booleana."
let msg_notvalue = "A expressão não é um valor."
let msg_atribuicao = "O primeiro argumento da atribuição deve ser uma referência do mesmo tipo do segundo."
let msg_deref = "A expressão de desreferência deve ser uma referência."

(* ================== FUNÇÕES AUXILIARES ================== *)

let value e =
  match e with
  | Num _ | Bool _ | Unit | Loc _ -> true
  | _ -> false

let rec lookup (g: (string * tipo) list) (x: string) : tipo option =
  match g with
  | [] -> None
  | (y,t)::ys -> if x = y then Some t else lookup ys x

let rec subs (v:expr) (x:string) (e:expr) =
  match e with
  | Num _ | Bool _ | Unit -> e
  | Binop(o,e1,e2) -> Binop(o, subs v x e1, subs v x e2)
  | If(e1,e2,e3) -> If(subs v x e1, subs v x e2, subs v x e3)
  | Id y -> if x = y then v else e
  | Let(y,t,e1,e2) -> if x = y then Let(y,t,subs v x e1,e2) else Let(y,t,subs v x e1,subs v x e2)
  | Wh(e1,e2) -> Wh(subs v x e1, subs v x e2)
  | Asg(e1,e2) -> Asg(subs v x e1, subs v x e2)
  | New e1 -> New (subs v x e1)
  | Deref e1 -> Deref (subs v x e1)
  | Seq(e1,e2) -> Seq(subs v x e1, subs v x e2)
  | Read -> Read
  | Print e1 -> Print (subs v x e1)
  | Loc _ -> e

let compute (op: bop) (v1:expr) (v2:expr) : expr =
  match (op,v1,v2) with
  | (Sum, Num n1, Num n2) -> Num (n1 + n2)
  | (Sub, Num n1, Num n2) -> Num (n1 - n2)
  | (Mul, Num n1, Num n2) -> Num (n1 * n2)
  | (Div, Num n1, Num n2) -> Num (n1 / n2)
  | (Eq, Num n1, Num n2)  -> Bool (n1 = n2)
  | (Neq, Num n1, Num n2) -> Bool (n1 <> n2)
  | (Lt, Num n1, Num n2)  -> Bool (n1 < n2)
  | (Gt, Num n1, Num n2)  -> Bool (n1 > n2)
  | (And, Bool b1, Bool b2) -> Bool (b1 && b2)
  | (Or,  Bool b1, Bool b2) -> Bool (b1 || b2)
  | _ -> raise (StepError msg_booleanos)

let rec step (e:expr) (mem:memoria) (inp:int list) (out:int list) : expr * memoria * int list * int list =
  match e with
  | Binop(o, v1, v2) when value v1 && value v2 -> (compute o v1 v2, mem, inp, out)
  | Binop(o, v1, e2) when value v1 -> let (e2',m,i,out') = step e2 mem inp out in (Binop(o,v1,e2'), m, i, out')
  | Binop(o, e1, e2) -> let (e1',m,i,out') = step e1 mem inp out in (Binop(o,e1',e2), m, i, out')

  | If(Bool true, e2, _) -> (e2, mem, inp, out)
  | If(Bool false, _, e3) -> (e3, mem, inp, out)
  | If(e1, e2, e3) -> let (e1',m,i,o) = step e1 mem inp out in (If(e1', e2, e3), m, i, o)

  | Let(x,t,v1,e2) when value v1 -> (subs v1 x e2, mem, inp, out)
  | Let(x,t,e1,e2) -> let (e1',m,i,o) = step e1 mem inp out in (Let(x,t,e1',e2), m, i, o)

  | Wh(e1,e2) -> (If(e1, Seq(e2, Wh(e1,e2)), Unit), mem, inp, out)

  | Asg(Loc l, v) when value v ->
      let mem' = (l, v) :: List.remove_assoc l mem in
      (Unit, mem', inp, out)
  | Asg(Loc l, e2) -> let (e2', m, i, o) = step e2 mem inp out in (Asg(Loc l, e2'), m, i, o)
  | Asg(e1, e2) -> let (e1', m, i, o) = step e1 mem inp out in (Asg(e1', e2), m, i, o)

  | New v when value v ->
      let l = List.length mem in
      (Loc l, (l,v)::mem, inp, out)
  | New e1 -> let (e1',m,i,o) = step e1 mem inp out in (New e1', m, i, o)

  | Deref(Loc l) ->
      (match List.assoc_opt l mem with
       | Some v -> (v, mem, inp, out)
       | None -> raise (StepError msg_deref))
  | Deref e1 -> let (e1',m,i,o) = step e1 mem inp out in (Deref e1', m, i, o)

  | Seq(Unit, e2) -> (e2, mem, inp, out)
  | Seq(e1, e2) -> let (e1',m,i,o) = step e1 mem inp out in (Seq(e1', e2), m, i, o)

  | Read -> (match inp with n::rest -> (Num n, mem, rest, out) | [] -> raise (StepError "input vazio"))
  | Print(Num n) -> (Unit, mem, inp, out @ [n])
  | Print(e1) -> let (e1',m,i,o) = step e1 mem inp out in (Print(e1'), m, i, o)

  | _ -> raise (StepError "expressão inválida no passo")

let rec eval (e:expr) (mem:memoria) : expr * memoria =
  try
    let (e', mem', _, _) = step e mem !input !output in
    eval e' mem'
  with StepError _ -> (e, mem)

(* ================== SISTEMA DE TIPOS ================== *)

type tyEnv = (string * tipo) list

let rec typeinfer (g:tyEnv) (e:expr) : tipo =
  match e with
  | Num _ -> TyInt
  | Bool _ -> TyBool
  | Unit -> TyUnit
  | Id x -> (match lookup g x with None -> raise (TypeError "id não encontrado") | Some t -> t)
  | Binop(o,e1,e2) ->
      let t1 = typeinfer g e1 in
      let t2 = typeinfer g e2 in
      (match o with
       | Sum | Sub | Mul | Div -> if t1 = TyInt && t2 = TyInt then TyInt else raise (TypeError msg_relacionais_aritmeticos)
       | Eq | Neq | Lt | Gt -> if t1 = TyInt && t2 = TyInt then TyBool else raise (TypeError msg_relacionais_aritmeticos)
       | And | Or -> if t1 = TyBool && t2 = TyBool then TyBool else raise (TypeError msg_booleanos))
  | If(e1,e2,e3) ->
      let t1 = typeinfer g e1 in
      let t2 = typeinfer g e2 in
      let t3 = typeinfer g e3 in
      if t1 = TyBool then if t2 = t3 then t2 else raise (TypeError msg_thenelse) else raise (TypeError msg_condicao)
  | Let(x,t,e1,e2) ->
      let t1 = typeinfer g e1 in
      if t1 = t then typeinfer ((x,t)::g) e2 else raise (TypeError "tipo incompatível em let")
  | Wh(e1,e2) ->
      let t1 = typeinfer g e1 in
      let t2 = typeinfer g e2 in
      if t1 = TyBool && t2 = TyUnit then TyUnit else raise (TypeError "tipos incorretos no while")
  | Asg(e1,e2) ->
      let t1 = typeinfer g e1 in
      let t2 = typeinfer g e2 in
      (match t1 with TyRef t when t = t2 -> TyUnit | TyRef _ -> raise (TypeError msg_atribuicao) | _ -> raise (TypeError msg_atribuicao))
  | New e1 -> TyRef (typeinfer g e1)
  | Deref e1 -> (match typeinfer g e1 with TyRef t -> t | _ -> raise (TypeError msg_deref))
  | Seq(e1,e2) -> if typeinfer g e1 = TyUnit then typeinfer g e2 else raise (TypeError "seq deve começar com unit")
  | Read -> TyInt
  | Print e1 -> if typeinfer g e1 = TyInt then TyUnit else raise (TypeError "print requer int")
  | Loc _ -> raise (TypeError "loc não deve aparecer estaticamente")

(* ================== INTERPRETADOR FINAL ================== *)

let rec strofvalue (v:expr) : string =
  match v with
  | Num n -> string_of_int n
  | Bool b -> string_of_bool b
  | Unit -> "()"
  | Loc l -> "l" ^ string_of_int l
  | _ -> raise (NotValue msg_notvalue)

let rec stroftipo (t:tipo) : string =
  match t with
  | TyInt -> "int"
  | TyBool -> "bool"
  | TyRef t -> "ref(" ^ stroftipo t ^ ")"
  | TyUnit -> "unit"

let inter (e:expr) : unit =
  try
    let t = typeinfer [] e in
    let (v, _) = eval e [] in
    print_endline ("= " ^ strofvalue v ^ ":" ^ stroftipo t)
  with
  | TypeError msg -> print_endline ("Erro de tipo: " ^ msg)
  | StepError msg -> print_endline ("Erro em tempo de execução: " ^ msg)
  | NotValue msg -> print_endline ("Erro: " ^ msg)
