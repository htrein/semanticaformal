(*==TIPO DE DADOS==*)
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
    | Loc of int 
    | For of expr * expr * expr * expr 

type memoria = (int * expr) list (*Representação da Memória*)

(*==ESTADOS DE ENTRADA E SAÍDA==*)
let input : int list ref = ref [] 
let output : int list ref = ref [] 

(*==EXCEÇÕES E MENSAGENS DE ERRO==*)
exception StepError of string
exception TypeError of string
exception NotValue of string
exception ComputeFailed of string
exception SubsError of string
exception EvalError of string
exception ReadError of string
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
let msg_divisaoZero = "Divisão por zero."
let msg_atribuicao = "A atribuição deve ser feita a uma referência existente."
let msg_id = "Variável não declarada."
let msg_let = "Erro no tipo da variável na expressão let."
let msg_while = "A condição do while deve ser booleana e o corpo deve ser unit."
let msg_seq = "A primeira expressão do seq deve ser unit."
let msg_print = "A expressão do print deve ser um inteiro."
let msg_loc = "A expressão Loc deve ser usada apenas para referências."
let msg_for = "Erro no for: inicialização deve ser unit, condição booleana, corpo unit e incremento unit."

(*==AVALIADOR==*)
(*Verifica se uma expressão é um valor*)

(*==AVALIADOR==*)
(*Verifica se uma expressão é um valor*)
let value e = 
    match e with
    | Num _ -> true
    | Bool _ -> true
    | Unit -> true 
    | Loc _ -> true
    | _ -> false

(*Computa a operação binária entre dois valores*)
let compute (op: bop) (v1:expr) (v2:expr) : expr = 
    match (op,v1,v2) with
    | (Sum,Num n1, Num n2) -> Num (n1 + n2) 
    | (Sub,Num n1, Num n2) -> Num (n1 - n2) 
    | (Mul,Num n1, Num n2) -> Num (n1 * n2)            
    | (Div,Num n1, Num n2) -> 
        if n2 = 0 then raise (ComputeFailed msg_divisaoZero)
        else Num (n1 / n2)
    | (Eq,Num n1, Num n2)  -> Bool (n1 = n2) 
    | (Neq,Num n1, Num n2) -> Bool (n1 != n2) 
    | (Lt,Num n1, Num n2)  -> Bool (n1 < n2)              
    | (Gt,Num n1, Num n2)  -> Bool (n1 > n2) 
    | (And, Bool b1, Bool b2) -> Bool (b1 && b2) 
    | (Or,  Bool b1, Bool b2) -> Bool (b1 || b2)                                  
    |  _ -> raise (ComputeFailed msg_compute)

(*Substitui todas as ocorrências de x em e pelo valor v*)
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
    | Loc l -> Loc l 
    | For(e1, e2, e3, e4) -> For(subs v x e1, subs v x e2, subs v x e3, subs v x e4)

(*Regras da semântica small step*)
let rec step (e:expr) (mem:memoria) (inp: int list) (out: int list): expr * memoria * int list * int list = 
    match e with
    (*Valores*)
    | Num n -> (Num n, mem, inp, out)
    | Bool b -> (Bool b, mem, inp, out)
    | Unit -> (Unit, mem, inp, out)
    | Loc l -> (Loc l, mem, inp, out)
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
    | If(e1, e2, e3) -> let (e1',mem',inp',out') = step e1 mem inp out in (If(e1', e2, e3),mem',inp',out')            
    (*LET2*)
    | Let(x,t,v1,e2) when value v1 -> (subs v1 x e2, mem, inp, out)  
    (*LET1*)
    | Let(x,t,e1,e2) -> let (e1',mem',inp',out') = step e1 mem inp out in (Let(x,t,e1',e2),mem',inp',out') 
    (*E-WHILE*)
    (*se a condição do while for verdadeira, executa o corpo e repete*)
    | Wh(e1,e2) -> (If(e1, Seq(e2, Wh(e1,e2)), Unit), mem, inp, out)
    (*ATR1*)
    (*se existir uma chave l na memória, então atualiza o valor associado a l*)
    | Asg(Loc l, v) when value v ->
        if List.mem_assoc l mem then 
          let mem' = (l, v) :: List.remove_assoc l mem in 
          (Unit, mem', inp, out)
        else
          raise (StepError msg_atribuicao)
    (*ATR2*) 
    | Asg(Loc l, e2) -> let (e2', mem', inp', out') = step e2 mem inp out in (Asg(Loc l, e2'), mem', inp', out')
    (*ATR*)
    | Asg(e1, e2) -> let (e1', mem', inp', out') = step e1 mem inp out in (Asg(e1', e2), mem', inp', out')
    (*NEW1*)
    (*cria uma nova loc ao final da memória*)
    | New v when value v ->
        let l = List.length mem in
        let mem' = (l, v) :: mem in 
        (Loc l, mem', inp, out)
    (*NEW*)
    | New e1 -> let (e1',mem',inp',out') = step e1 mem inp out in (New e1', mem', inp', out')
    (*DEREF1*)
    (*procura o valor associado a chave l*)
    | Deref(Loc l) ->
        (match List.assoc_opt l mem with 
        | Some v -> (v, mem, inp, out) 
        | None -> raise (StepError msg_deref)) 
    (*DEREF*)
    | Deref(e) -> let (e', mem', inp', out') = step e mem inp out in (Deref(e'), mem', inp', out')
    (*SEQ1*) 
    | Seq(e1, e2) when value e1 && e1 = Unit -> (e2, mem, inp, out)
    (*SEQ*)
    | Seq(e1,e2) -> let (e1', mem', inp', out') = step e1 mem inp out in (Seq(e1',e2), mem', inp', out')

    (*READ*)
    (*retorna o primeiro do input e remove do input*)
    | Read -> 
        (match inp with
        | n::rest -> (Num n, mem, rest, out) 
        | [] -> raise (ReadError msg_read)) 

    (*PRINT-N*)
    (*out @ [n] concatena n em out*)
    | Print(Num n) -> (Unit, mem, inp, out @ [n])
    (*PRINT*)
    | Print(e) -> let (e', mem', inp', out') = step e mem inp out in (Print(e'), mem', inp', out')

    (*FOR*)
    (*transforma o for em um while: 
    1. executa a inicialização e1,
    2. executa um while com a condição e2 e o corpo composto por incremento e4 e conteúdo e3
    ex: For(Asg(Id "i", Num 0), Binop(Lt, Deref (Id "i"), Num 4), Asg(Id "i", Binop(Sum, Deref (Id "i"), Num 1)), Print(Deref (Id "i")))*)
    | For(e1,e2,e3,e4) ->
        let while_loop = Wh(e2, Seq(e4, e3)) in
        let full_expr = Seq(e1, while_loop) in
        (full_expr, mem, inp, out)

    | _ -> raise (StepError msg_stepError)

(*Avaliador de expressões*)
let rec eval (e:expr) (mem:memoria) (inp: int list) (out: int list): expr * memoria * int list * int list = 
    if value e then
        (e, mem, inp, out) 
    else
        let (e', mem', inp', out') = step e mem inp out in
        eval e' mem' inp' out'



(*==TYPEINFER==*)
(*Ambiente de tipos*)
type tyEnv = (string * tipo) list 

(*Procura o tipo associado a variável x*)
let rec lookup (g: tyEnv) (x: string) : tipo option =
    match g with
    | [] -> None
    | (y,t)::ys -> if x = y then Some t else lookup ys x

(*Dada uma expressão, retorna seu tipo, se não for bem tipada, levanta um erro*)
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
        | Some t -> t
        | None -> raise (TypeError msg_id))
    (*T-LET*)             
    | Let(x,t,e1,e2) -> 
        let t1 = typeinfer g e1 in 
        let g' = (x,t)::g in
        let t2 = typeinfer g' e2 in
        if t1=t then t2 else raise (TypeError msg_let)
    (*T-WHILE*)
    | Wh(e1,e2) -> 
        let t1 = typeinfer g e1 in
        let t2 = typeinfer g e2 in
        if(t1=TyBool) && (t2=TyUnit) then TyUnit else raise (TypeError msg_while)
    (*T-READ*)
    | Read -> TyInt
    (*T-SEQ*)
    | Seq(e1,e2) ->
        let t1 = typeinfer g e1 in
        let t2 = typeinfer g e2 in
        if(t1=TyUnit) then t2 else raise (TypeError msg_seq)
    (*T-DEREF*)
    | Deref(e) ->
        let t1 = typeinfer g e in
        (match t1 with
        | TyRef(t) ->  t
        | _ -> raise (TypeError msg_deref))
    (*T-PRINT*)
    | Print(e) ->
        let t1 = typeinfer g e in 
        if(t1=TyInt) then TyUnit 
        else raise (TypeError msg_print)
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
    | Loc _ -> raise (TypeError msg_loc)
    | For(e1,e2,e3,e4) ->
        let t1 = typeinfer g e1 in
        let t2 = typeinfer g e2 in
        let t3 = typeinfer g e3 in
        let t4 = typeinfer g e4 in
        if (t1=TyUnit) && (t2=TyBool) && (t3=TyUnit) && (t4=TyUnit) then TyUnit 
        else raise (TypeError msg_for)

(*==INTERPRETADOR==*)
(*Converte uma expressão do tipo expr para uma string representando o valor*)
let rec strofvalue (v:expr) : string = 
  match v with 
  | Num n -> string_of_int n
  | Bool b -> string_of_bool b
  | Unit -> "()"
  | Loc l -> "loc " ^ string_of_int l
  | _    -> raise (NotValue msg_notvalue)
    
(*Converte um tipo para uma string representando o tipo*)
let rec stroftipo (t:tipo) : string = 
  match t with
  | TyInt -> "int"
  | TyBool -> "bool"
  | TyRef t' -> "ref " ^ (stroftipo t')
  | TyUnit -> "unit"
  
(*Interpreta uma expressão e um input e imprime o resultado, tipo e saída*) 
let rec inter (e:expr) (initial_input: int list) : unit = 
  try
    let t = typeinfer []  e in (*inferencia de tipos, já pode lançar erro de tipos*)
    input := initial_input; (*define a entrada do programa*)
    output := []; (*limpa a saída do programa*)
    let (v,_, _, final_output) = eval e [] !input [] in (*avalia a expressão com memória vazia, entrada inicial e saída vazia*)
    print_endline ("- Type: " ^ (stroftipo t));
    print_endline ("- Result: " ^ (strofvalue v));
    print_endline ("- Output: [" ^ (String.concat "; " (List.map string_of_int final_output)) ^ "]")
  with 
    TypeError msg -> print_endline ("Erro de tipo: " ^ msg)
  | StepError msg -> print_endline ("Erro de execução: " ^ msg)
  | NotValue msg -> print_endline ("Erro de valor: " ^ msg)
  | ComputeFailed msg -> print_endline ("Erro de computação: " ^ msg) 
  | ReadError msg -> print_endline ("Erro de leitura: " ^ msg)      