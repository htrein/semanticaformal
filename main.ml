(*******************Tipos de Dados********************)
type bop =  
    | Sum | Sub | Mul | Div   
    | Eq  | Neq | Lt | Gt   
    | And | Or  

type tipo = 
    | TyInt
    | TyBool
    | TyRef of tipo
    | TyUnit

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


(*Memória*)
type endereco = int
type memoria = (endereco * expr) list

(*I/O*)
let input : int list ref = ref [] 
let output : int list ref = ref [] 
(*como modificar:
- inserir no inicio: input := elemento :: !input  
- inserir no final: input := !input @ [elemento]
*)

(*Exceções*)
exception AlgumErro of string (*remover depois*)
exception StepError of string
exception TypeError of string
exception NotValue of string
exception ComputeFailed of string
exception SubsError of string
exception EvalError of string
(*...*)
(*Mensagens*) (*adicionar mais mensagens de exceções*)
let msg_booleanos = "Ambos os operandos devem ser booleanos."
let msg_relacionais_aritmeticos = "Ambos os operandos devem ser inteiros."
let msg_thenelse = "As expressões do então e do senão devem ter o mesmo tipo."
let msg_condicao = "A condição do if deve ser booleana."
let msg_notvalue = "A expressão não é um valor."
let msg_atribuicao =  "O primeiro argumento da atribuição deve ser uma referência do mesmo tipo do segundo."
let msg_deref = "A expressão de desreferência deve ser uma referência."
let msg_compute = "Erro na computação de operações aritméticas ou lógicas."
let msg_subs = "Erro na substituição de variáveis."
let msg_read = "Erro na leitura de entrada. A lista de entrada está vazia."
let msg_stepError = "Erro ao dar um passo na execução da expressão."
(*...*)

(****************Avaliador***************************)
let value e = (*existem mais valores agora, acredito que precisamos adicionar*)
    match e
    | Num _ -> true
    | Bool _ -> true
    | Unit -> true 
    | _ -> false

let compute (op: bop) (v1:expr) (v2:expr) : expr = 
    match (op,v1,v2) with
    | (Sum,Num n1, Num n2) -> Num (n1 + n2) 
    | (Sub,Num n1, Num n2) -> Num (n1 - n2) 
    | (Mul,Num n1, Num n2) -> Num (n1 * n2)            
    | (Div,Num n1, Num n2) -> Num (n1 / n2)         
    | (Eq,Num n1, Num n2)  -> Bool (n1 = n2) 
    | (Neq,Num n1, Num n2) -> Bool (n1 != n2) 
    | (Lt,Num n1, Num n2)  -> Bool (n1 < n2)              
    | (Gt,Num n1, Num n2)  -> Bool (n1 > n2) 
    | (And, Bool b1, Bool b2) -> Bool (b1 && b2) 
    | (Or,  Bool b1, Bool b2) -> Bool (b1 || b2)                                  
    |  _ -> raise (ComputeFailed msg_compute)

let rec subs (v:expr) (x:string) (e:expr) = 
    match e with 
    | Num _ -> e
    | Bool _ -> e
    | Unit -> e
    | Binop(o,e1,e2) -> Binop(o,  subs v x e1,   subs v x e2)
    | If(e1,e2,e3) -> If(subs v x e1, subs v x e2, subs v x e3)           
    | Id y -> if x=y then v else e 
    | Let(y,t,e1,e2) -> if x=y then Let(y,t,subs v x e1,e2) else Let(y,t,subs v x e1,subs v x e2)
    | Wh(e1,e2) -> Wh(subs v x e1, subs v x e2)
    | Asg(e1,e2) -> Asg(subs v x e1, subs v x e2)
    | New(e1) -> New(subs v x e1)
    | Deref(e1) -> Deref(subs v x e1)
    | Seq(e1,e2) -> Seq(subs v x e1, subs v x e2)
    | Read -> Read
    | Print(e1) -> Print(subs v x e1)
    | Loc l -> Loc l (* Adicionado: endereços não são substituídos *)
    (*Tratamento de erro*)
    | _ -> raise (SubsError msg_subs)

let rec step (e:expr) (mem:memoria) (inp: int list) (out: int list): expr * memoria * int list * int list = 
    match e with
    (*Valores*)
    | Num _ -> TyInt 
    | Bool _ -> TyBool
    | Unit _ -> TyUnit
    (*Nao tem regra?*) (*verificar existencia de ID*)
    | Id x -> 
      (match lookup g x with
       | None -> raise AlgumErro
       | Some t -> t) (*pq Some?*)
    (*OP*)
    | Binop(o,v1,v2) when (value v1) && (value v2) -> (compute o v1 v2, mem, inp, out)
    (*OP2*)
    | Binop(o,v1,e2) when value v1 -> let (e2',mem',inp',out') = step e2 mem inp out in (Binop(o,v1,e2'), mem', inp', out')
    (*OP1*)
    | Binop(o,e1,e2) -> let (e1',mem',inp',out') = step e1 mem inp out in (Binop(o,e1',e2),mem', inp', out')      
    (*IF1*)
    | If(Bool true, e2, e3) -> (e2,mem,inp,out)
    (*IF2*)
    | If(Bool false, e2, e3) -> (e3,mem,inp,out) 
    (*IF3*)
    | If(e1, e2, e3) -> let (e1',mem',inp',out') = step e1 mem in (If(e1', e2, e3),mem',inp',out')            
    (*LET2*)
    | Let(x,t,v1,e2) when value v1 -> (subs v1 x e2, mem, inp, out)  
    (*LET1*)
    | Let(x,t,e1,e2) -> let (e1',mem',inp',out') = step e1 mem in (Let(x,t,e1',e2),mem',inp',out') 
    (*E-WHILE*)
    (*| Wh(e1,e2) -> step ((If(e1, Seq(e2, Wh(e1,e2)), Unit)), mem, inp, out)*)
    | Wh(e1,e2) -> (If(e1, Seq(e2, Wh(e1,e2)), Unit), mem, inp, out)
    (*ATR1*) (*implementar aqui*)
    | Asg(Loc l, v) when value v ->
          let mem' = (l, v) :: List.remove_assoc l mem in
          (Unit, mem', inp, out)
    (*ATR2*) (*verificar TyRef aqui*)
    (*| Asg(TyRef l,e) -> let (e', mem', inp', out') = step e mem inp out in (Asg(TyRef l, e'), mem', inp', out') *)
    | Asg(Loc l, e2) -> let (e2', m, i, o) = step e2 mem inp out in (Asg(Loc l, e2'), m, i, o)
    (*ATR*)
    | Asg(e1, e2) -> let (e1', mem', inp', out') = step e1 mem inp out in (Asg(e1', e2), mem', inp', out')
    (*NEW1*) (*implementar aqui*)
    | New v when value v ->
          let l = List.length mem in
          (Loc l, (l,v)::mem, inp, out)
    (*NEW*)
    | New e1 -> let (e1',m,i,o) = step e1 mem inp out in (New e1', m, i, o)
    (*DEREF1*)
    | Deref(Loc l) ->
        (List.assoc_opt l mem with
        | Some v -> (v, mem, inp, out)
        | None -> raise (StepError msg_deref)
        )
    (*DEREF*)
    | Deref(e) -> let (e', mem', inp', out') = step e mem inp out in (Deref(e'), mem', inp', out')
    (*SEQ*)
    | Seq(e1,e2) -> let (e1', mem', inp', out') = step e1 mem inp out in (Seq(e1',e2), mem', inp', out')
    (*SEQ1*) (*verificar TyUnit aqui*)
    | Seq(TyUnit e1, e2) -> (e2, mem, inp, out)
    (*| Seq(Unit, e2) -> (e2, mem, inp, out) *) (*gepeto que fez isso, verificar se é necessário*)
    (*| Seq(e1,e2) -> if typeinfer g e1 = TyUnit then typeinfer g e2 else raise (TypeError "seq deve começar com unit")*) (*gepeto que fez isso, verificar se é necessário*)
    (*READ*) (*verficar argumento do read*)
    | Read _    -> 
        (match inp with
        | n::rest -> (Num n, mem, rest, out)
        | [] -> raise (ReadError msg_read))
    (*PRINT-N*)
    | Print(Num e1) -> (Unit, mem, inp, !out @ [e1])
    (*PRINT*)
    | Print(e) -> let (e', mem', inp', out') = step e mem inp out in (Print(e'), mem', inp', out')

    | _ -> raise StepError msg_stepError



let rec eval (e:expr) (mem:memoria): expr * memoria = 
    try 
        let (e', mem', _, _) = step e mem in
        eval e' mem'
    with
        EvalError _ -> (e, mem)

(*Funcao auxiliar para procurar um valor numa lista*)
let rec procura valor lista = 
    match lista with
    | [] -> None
    | x::xs -> if x = valor then Some x else procura valor xs
    
(****************************************************)


(*******************TypeInfer************************)
type tyEnv = (string * tipo) list 

let rec lookup (g: tyEnv) (x: string) : tipo option =
    match g with
    | [] -> None
    | (y,t)::ys -> if x = y then Some t else lookup ys x

let rec typeinfer (g: tyEnv) (e: expr) : tipo =
    match e with
    (*T-INT*)
    | Num _ -> TyInt
    (*T-BOOL*)
    | Bool _ -> TyBool
    (*T-BINOP*)
    | Binop(o,e1,e2) -> 
        let t1 = typeinfer g e1  in
        let t2 = typeinfer g e2  in
        (match o with
           Sum | Sub | Mul | Div ->
            if (t1=TyInt) && (t2=TyInt) then TyInt else raise (TypeError msg_relacionais_aritmeticos)
        | Eq | Gt | Lt | Neq ->
            if (t1=TyInt) && (t2=TyInt) then TyBool else raise (TypeError msg_relacionais_aritmeticos)
        | And | Or ->
            if (t1=TyBool) && (t2=TyBool) then TyBool else raise (TypeError msg_booleanos))
    (*T-IF*)
    | If(e1,e2,e3) ->  
    let t1 = typeinfer g e1 in
    if (t1=TyBool) then
        let t2 = typeinfer g e2  in
        let t3 = typeinfer g e3  in
        if (t2=t3) then t2 else raise (TypeError msg_thenelse)
    else raise (TypeError msg_condicao)
    (*T-VAR*)           
    | Id x ->
        (match lookup g x with
            None -> (TypeError "id não encontrado")
            | Some t -> t)
    (*T-LET*)             
    | Let(x,t,e1,e2) -> 
        let t1 = typeinfer g e1 in 
        let g' = (x,t)::g in
        let t2 = typeinfer g' e2 in
        if t1=t then t2 else raise (TypeError "tipo incompatível em let")
    (*T-WHILE*)
    | Wh(e1,e2) -> 
        let t1 = typeinfer g e1 in
        let t2 = typeinfer g e2 in
        if(t1=TyBool) && (t2=TyUnit) then TyUnit else raise (TypeError "tipos incorretos no while")
    (*T-READ*)
    | Read -> TyInt
    (*T-SEQ*)
    | Seq(e1,e2) ->
        let t1 = typeinfer g e1 in
        let t2 = typeinfer g e2 in
        if(t1=TyUnit) then t2 else raise (TypeError "seq deve começar com unit")
    (*T-DEREF*)
    | Deref(e) ->
        let t1 = typeinfer g e in
        (match t1 with
        | TyRef(t) ->  t
        | _ -> raise (TypeError msg_deref)
    (*T-PRINT*)
    | Print(e) ->
        let t1 = typeinfer g e in 
        if(t1=TyInt) then TyUnit 
        else raise (TypeError "print requer int")
    (*T-UNIT*)
    | Unit -> TyUnit
    (*T-NEW*)
    | New(e) -> 
        let t1 = typeinfer g e in
        TyRef(t1)
    (*T-ATR*)
    | Asg(e1,e2) ->
        let t1 = typeinfer g e1 in
        let t2 = typeinfer g e2 in
        (match t1 with
        | TyRef(t) when t = t2 -> TyUnit
        | TyRef _ -> raise (TypeError msg_atribuicao)
        | _ -> raise (TypeError msg_atribuicao))
    | Loc _ -> raise (TypeError "loc não deve aparecer estaticamente")
(***********************************************)

(**************Interpretador********************)
exception NotValue
  
let rec strofvalue (v:expr) : string = (*verificar*)
  match v with 
  | Num n -> string_of_int n
  | Bool b -> string_of_bool b
  | Unit -> "()"
  | Loc l -> "loc " ^ string_of_int l
  | _    -> raise (NotValue msg_notvalue)
    
let rec stroftipo (t:tipo) : string = 
  match t with
  | TyInt -> "int"
  | TyBool -> "bool"
  | TyRef t' -> "ref " ^ (stroftipo t')
  | TyUnit -> "unit"
  
let rec inter (e:expr) : unit = 
  try
    let t = typeinfer []  e in
    let (v, mem) = eval e [] in
    print_endline ("= " ^ (strofvalue v) ^  ":" ^ (stroftipo t) )
  with 
    TypeError msg -> print_endline ("Erro de tipo: " ^ msg)