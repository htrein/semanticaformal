(*Tipos de Dados*)
type bop =  
    | Sum | Sub | Mul | Div   (* operações aritméticas *)
    | Eq  | Neq | Lt | Gt   (* operações relacionais  *)
    | And | Or   (* operações lógicas *) 

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
(*----------------*)

exception AlgumErro

let rec value e =
    match e with
    | Num _ -> true
    | Bool _ -> true
    | _ -> false


let compute (op: bop) (v1:expr) (v2:expr) : expr = 
    match (op,v1,v2) with
    | (Sum,Num n1, Num n2) -> Num (n1 + n2) (*Soma*)
    | (Sub,Num n1, Num n2) -> Num (n1 - n2) (*Subtração*)
    | (Mul,Num n1, Num n2) -> Num (n1 * n2) (*Multiplicação*)            
    | (Div,Num n1, Num n2) -> Num (n1 / n2) (*Divisão*)          
    | (Eq,Num n1, Num n2)  -> Bool (n1 = n2) (*Igualdade*)
    | (Neq,Num n1, Num n2) -> Bool (n1 != n2) (*Desigualdade*)
    | (Lt,Num n1, Num n2)  -> Bool (n1 < n2) (*Menor que*)              
    | (Gt,Num n1, Num n2)  -> Bool (n1 > n2) (*Maior que*)   
    | (And, Bool b1, Bool b2) -> Bool (b1 && b2) (*E lógico*)
    | (Or,  Bool b1, Bool b2) -> Bool (b1 || b2) (*OU lógico*)                                   
    |  _ -> raise AlgumErro

(*
let rec step (e:expr) : expr = 
    match e with
    (*Já estão em forma normal*)
    | Num _ -> raise AlgumErro
    | Bool _ -> raise AlgumErro
    | Id _ -> raise AlgumErro  
    (*Operações binárias*)
    | Binop(o,v1,v2) when (value v1) && (value v2) -> 
        compute o v1 v2
    | Binop(o,v1,e2) when value v1 ->
        let e2' = step e2 in Binop(o,v1,e2')
    | Binop(o,e1,e2)  ->
        let e1' = step e1 in Binop(o,e1',e2)
    (*Condicional*)
    | If(Bool true, e2, e3) -> e2
    | If(Bool false, e2, e3) -> e3 
    | If(e1, e2, e3) -> let e1' = step e1 in If(e1', e2, e3)
    (*Atribuição*)
    | Let(x,t,v1,e2) when value v1 -> subs v1 x e2   (*  {v1/x} e2 *)
    | Let(x,t,e1,e2) -> let e1' = step e1 in Let(x,t,e1',e2) 
    (*Novas implementações*)
    (******)
    (*Qualquer outra combinação deve ser exceção*)
    | _ -> raise AlgumErro

*)
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