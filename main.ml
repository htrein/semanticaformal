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
    (*Não há let rec, app, fn*)    

(*Adionando memória*)
type endereco = int
type memoria = (endereco * expr) list

(*****************************************************)

exception AlgumErro

(****************Avaliador***************************)
let value e =
    match e with
    | Num _ -> true
    | Bool _ -> true
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
    |  _ -> raise AlgumErro

let rec subs (v:expr) (x:string) (e:expr) = 
    match e with 
    | Num _ -> e
    | Bool _ -> e
    | Binop(o,e1,e2) -> Binop(o,  subs v x e1,   subs v x e2)
    | If(e1,e2,e3) -> If(subs v x e1, subs v x e2, subs v x e3)           
    | Id y -> if x=y then v else e 
    | Let(y,t,e1,e2) -> if x=y then Let(y,t,subs v x e1,e2) else Let(y,t,subs v x e1,subs v x e2)   
    | _ -> raise AlgumErro

let rec step (e:expr) (mem:memoria): expr * memoria = 
    match e with
    | Num _ -> raise AlgumErro
    | Bool _ -> raise AlgumErro           
    | Binop(o,v1,v2) when (value v1) && (value v2) -> (compute o v1 v2, mem)
    | Binop(o,v1,e2) when value v1 -> let (e2',mem') = step e2 mem in (Binop(o,v1,e2'),mem')
    | Binop(o,e1,e2) -> let (e1',mem') = step e1 mem in (Binop(o,e1',e2),mem')               
    | If(Bool true, e2, e3) -> (e2,mem)
    | If(Bool false, e2, e3) -> (e3,mem) 
    | If(e1, e2, e3) -> let (e1',mem') = step e1 mem in (If(e1', e2, e3),mem')
    | Id _ -> raise AlgumErro              
    | Let(x,t,v1,e2) when value v1 -> (subs v1 x e2, mem)   
    | Let(x,t,e1,e2) -> let (e1',mem') = step e1 mem in (Let(x,t,e1',e2),mem') 
    | Wh(e1,e2) -> step ((If(e1, Seq(e2, Wh(e1,e2)), Unit)) mem) 
    | Asg(Num e1,e2) -> raise AlgumErro
    | New _ -> raise AlgumErro
    | Deref(e1) ->  raise AlgumErro
    | Unit -> raise AlgumErro
    | Seq(e1,e2) -> raise AlgumErro
    | Read -> raise AlgumErro
    | Print(Num e1) -> (Unit,mem)
    | Print(Num e1) -> let e1' = step e1 mem in Print(e1')
    | _ -> raise AlgumErro  

let rec eval (e:expr) (mem:memoria): expr * memoria = 
    try 
        let (e', mem') = step e mem in
        eval e' mem'
    with
        AlgumErro -> (e, mem)

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
            if (t1=TyInt) && (t2=TyInt) then TyInt else raise AlgumErro
         | Eq | Gt | Lt | Neq ->
            if (t1=TyInt) && (t2=TyInt) then TyBool 
            else if (t1=TyBool) && (t2=TyBool) then TyBool 
            else raise AlgumErro
        | And | Or ->
            if (t1=TyBool) && (t2=TyBool) then TyBool else raise AlgumErro)
    (*T-IF*)
    | If(e1,e2,e3) ->  
    let t1 = typeinfer g e1  in
    if (t1=TyBool) then
        let t2 = typeinfer g e2  in
        let t3 = typeinfer g e3  in
        if (t2=t3) then t2 else raise AlgumErro
    else raise AlgumErro
    (*T-VAR*)           
    | Id x ->
        (match lookup g x with
            None -> raise AlgumErro
            | Some t -> t)
    (*T-LET*)             
    | Let(x,t,e1,e2) -> 
        let t1 = typeinfer g e1 in 
        let g' = (x,t)::g in
        let t2 = typeinfer g' e2 in
        if t1=t then t2 else raise AlgumErro
    (*T-WHILE*)
    | Wh(e1,e2) -> 
        let t1 = typeinfer g e1 in
        let t2 = typeinfer g e2 in
        if(t1=TyBool) && (t2=TyUnit) then TyUnit else raise AlgumErro 
    (*T-READ*)
    | Read -> TyInt
    (*T-SEQ*)
    | Seq(e1,e2) ->
        let t1 = typeinfer g e1 in
        let t2 = typeinfer g e2 in
        if(t1=TyUnit) then t2 else raise AlgumErro
    (*T-DEREF*)
    | Deref(e) ->
        let t1 = typeinfer g e in
        (match t1 with
        | TyRef(t) ->  t
        | _ -> raise AlgumErro)
    (*T-PRINT*)
    | Print(e) ->
        let t1 = typeinfer g e in 
        if(t1=TyInt) then TyUnit 
        else raise AlgumErro
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
        | _ -> raise AlgumErro)

(***********************************************)

(**************Interpretador********************)
exception NotValue
  
let rec strofvalue (v:expr) : string = 
  match v with 
  | Num n -> string_of_int n
  | Bool b -> string_of_bool b
  | _    -> raise NotValue
    
let rec stroftipo (t:tipo) : string = 
  match t with
  | TyInt -> "int"
  | TyBool -> "bool"
  
let rec inter (e:expr) : unit = 
  try
    let t = typeinfer []  e in
    let v = eval e in
    print_endline ("= " ^ (strofvalue v) ^  ":" ^ (stroftipo t) )
  with 
    TypeError msg -> print_endline ("Erro de tipo: " ^ msg)