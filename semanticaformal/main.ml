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
    |  _ -> raise BugTypeInfer (*Podemos melhorar essa exceção*)


let rec step (e:expr) : expr = 
    match e with
    (*Já estão em forma normal*)
    | Num _ -> raise NoRuleApplies
    | Bool _ -> raise NoRuleApplies
    | Id _ -> raise NoRuleApplies  
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
    | Wh 
    | Asg
    | New
    | Deref
    | Unit _ -> raise NoRuleApplies
    | Seq
    | Read(Unit) 
    | Print(e, )
    (*Qualquer outra combinação deve ser exceção*)
    | _ -> raise BugParser 



(*******************TypeInfer************************)
type tyEnv = (string * tipo) list 

let rec typeinfer (g: tyEnv) (e: expr) : tipo =
    match e with
    | Num _ -> TyInt
    | Bool _ -> TyBool
    | Binop(o,e1,e2) -> 
        let t1 = typeinfer g e1  in
        let t2 = typeinfer g e2  in
        (match o with
           Sum | Sub | Mul | Div ->
             if (t1=TyInt) && (t2=TyInt) then TyInt else raise (TypeError msg_aritmeticos)
         | Eq | Gt | Lt | Neq ->
             if (t1=TyInt) && (t2=TyInt) then TyBool else raise (TypeError msg_relacionais)
         | And | Or -> 
             if (t1=TyBool) && (t2=TyBool) then TyBool else raise (TypeError msg_booleanos))
    | If(e1,e2,e3) ->  
    let t1 = typeinfer g e1  in
    if (t1=TyBool) then
        let t2 = typeinfer g e2  in
        let t3 = typeinfer g e3  in
        if (t2=t3) then t2 else raise (TypeError msg_thenelse)
    else raise (TypeError msg_condif)
                    
    | Id x ->
        (match lookup g x with
            None -> raise (TypeError (msg_idndeclarado ^ " - " ^ x))
            | Some t -> t)
                        
    | Let(x,t,e1,e2) -> 
        let t1 = typeinfer g e1 in 
        let g' = (x,t)::g in
        let t2 = typeinfer g' e2 in
        if t1=t then t2 else raise (TypeError msg_letconflito)
        
    | Wh(e1,e2) -> 
        let t1 = typeinfer g e1 in
        let t2 = typeinfer g e2 in
        if(t1=TyBool) && (t2=Unit) then Unit else raise AlgumErro 
    | Read -> TyInt
    | Seq(e1,e2) ->
        let t1 = typeinfer g e1 in
        let t2 = typeinfer g e2 in
        if(t1=Unit) then t2 else raise AlgumErro
    | Deref(e) ->
        let t1 = typeinfer g e in

    | Print(e) ->
        let t1 = typeinfer g e in 
        if(t1=TyInt) then Unit 
        else raise AlgumErro
    | _ -> raise BugParser 

(***********************************************)