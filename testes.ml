(* testes.ml *)

open Interpretador

(* ========== FUNÇÕES AUXILIARES PARA OS TESTES ========== *)

(* Função para rodar um único teste e imprimir os resultados de forma organizada.
   Ela também captura exceções para que um teste falho não pare os outros. *)
let run_test titulo expr (input_list : int list) =
  print_endline ("--[ TESTE: " ^ titulo ^ " ]--");
  try
    inter expr input_list
  with
  | ex -> print_endline ("!!!!!! ERRO INESPERADO NO TESTE: " ^ (Printexc.to_string ex))
;;

(* Função para imprimir um título de categoria *)
let print_category_title titulo =
  print_endline "\n========================================================";
  print_endline ("    " ^ titulo);
  print_endline "========================================================"
;;

(* ========== FATORIAL PARA O TESTE DO PROFESSOR ========== *)
let cndwhi = Binop(Gt, Deref (Id "z"),Num 0)
let asgny = Asg(Id "y", Binop(Mul, Deref (Id "y"),Deref(Id "z")))
let asgnz = Asg(Id "z", Binop(Sub, Deref (Id "z"),Num 1))
let bdwhi = Seq(asgny, asgnz)
let whi = Wh(cndwhi, bdwhi)
let prt = Print(Deref (Id "y"))
let seq = Seq(whi, prt)

let fat = Let("x", TyInt, Read,
              Let("z", TyRef TyInt, New (Id "x"),
                  Let("y", TyRef TyInt, New (Num 1),
                      seq)))

(* ========== DEFINIÇÕES PARA OS TESTES DO LAÇO FOR ========== *)

(* Cenário 1: FOR básico para imprimir de 0 a 3 *)
let for_test = Let("i", TyRef TyInt, New (Num 0),
    For(
        Asg(Id "i", Num 0),
        Binop(Lt, Deref (Id "i"), Num 4),
        Asg(Id "i", Binop(Sum, Deref (Id "i"), Num 1)),
        Print(Deref (Id "i"))
    )
)

(* Cenário 2: Laço FOR que não executa (condição inicial é falsa) *)
let for_no_exec_test = Let("i", TyRef TyInt, New (Num 0),
  Seq(
    For(
        Asg(Id "i", Num 5),
        Binop(Lt, Deref (Id "i"), Num 5),
        Asg(Id "i", Binop(Sum, Deref (Id "i"), Num 1)),
        Unit (* CORRIGIDO: O corpo não deve fazer nada *)
    ),
    Print(Deref(Id "i")) (* CORRIGIDO: Imprime apenas o valor final *)
  )
)

(* Cenário 3: Laços FOR aninhados *)
let nested_for_inner_loop = For(
    Asg(Id "j", Num 10),
    Binop(Lt, Deref(Id "j"), Num 12),
    Asg(Id "j", Binop(Sum, Deref(Id "j"), Num 1)),
    Print(Binop(Sum, Binop(Mul, Deref(Id "i"), Num 100), Deref(Id "j")))
)
let nested_for_outer_loop = For(
    Asg(Id "i", Num 0),
    Binop(Lt, Deref(Id "i"), Num 2),
    Asg(Id "i", Binop(Sum, Deref(Id "i"), Num 1)),
    nested_for_inner_loop
)
let nested_for_test = Let("i", TyRef TyInt, New (Num 0),
  Let("j", TyRef TyInt, New (Num 0),
    nested_for_outer_loop
  )
)

(* Cenário 4: Verificar valor final do contador após o laço *)
let for_final_value_test = Let("i", TyRef TyInt, New(Num 0),
  Seq(
      For(Asg(Id "i", Num 0),
          Binop(Lt, Deref (Id "i"), Num 4),
          Asg(Id "i", Binop(Sum, Deref (Id "i"), Num 1)),
          Unit (* Corpo do laço vazio, apenas para incrementar *)
      ),
      Print(Deref(Id "i")) (* Deve imprimir 4 *)
  )
)


(* ========== DEFINIÇÕES PARA TESTES DE ERRO DO FOR ========== *)

(* ERRO FOR: Condição não booleana *)
let for_error_cond_type = Let("i", TyRef TyInt, New (Num 0),
  For(
    Asg(Id "i", Num 0),
    Num 123, (* ERRO: Condição deve ser do tipo Bool *)
    Asg(Id "i", Binop(Sum, Deref (Id "i"), Num 1)),
    Print(Deref (Id "i"))
  )
)

(* ERRO FOR: Variável da condição não declarada *)
let for_error_unbound_var = Let("j", TyRef TyInt, New (Num 0),
  For(
    Asg(Id "j", Num 99), (* Inicializa 'j', mas a condição usa 'i' *)
    Binop(Lt, Deref (Id "i"), Num 4), (* ERRO: 'i' não foi declarado neste escopo *)
    Asg(Id "i", Binop(Sum, Deref (Id "i"), Num 1)),
    Print(Deref (Id "i"))
  )
)


(* ========== INÍCIO DA SUÍTE DE TESTES ========== *)
let () =

  print_category_title "CATEGORIA 1: OPERAÇÕES BÁSICAS";
  run_test "Soma simples" (Binop(Sum, Num 10, Num 5)) [];
  run_test "Subtração" (Binop(Sub, Num 10, Num 15)) [];
  run_test "Multiplicação com ordem de precedência" (Binop(Mul, Binop(Sum, Num 2, Num 3), Num 4)) [];
  run_test "Divisão" (Binop(Div, Num 20, Num 4)) [];
  run_test "Comparação 'Menor que' (true)" (Binop(Lt, Num 5, Num 10)) [];
  run_test "Comparação 'Igual a' (false)" (Binop(Eq, Num 5, Num 11)) [];
  run_test "Operador Lógico 'E'" (Binop(And, Binop(Eq, Num 5, Num 5), Binop(Lt, Num 10, Num 20))) [];
  run_test "Operador Lógico 'Ou'" (Binop(Or, Binop(Eq, Num 5, Num 6), Binop(Lt, Num 10, Num 20))) [];

  print_category_title "CATEGORIA 2: ESTRUTURAS DE CONTROLE";
  run_test "If com condição verdadeira" (If(Binop(Gt, Num 10, Num 5), Num 1, Num 0)) [];
  run_test "If com condição falsa" (If(Bool false, Num 1, Num 0)) [];
  run_test "Let simples" (Let("x", TyInt, Num 100, Binop(Sum, Id "x", Num 1))) [];
  run_test "Let aninhado e shadowing" (Let("x", TyInt, Num 5, Let("x", TyInt, Num 10, Id "x"))) [];
  run_test "Sequência (deve retornar o valor da 2ª expr)" (Seq(Num 12345, Num 99)) [];
  run_test "Sequência com unidade" (Let("x", TyInt, Num 10, Seq(Unit, Id "x"))) [];

  print_category_title "CATEGORIA 3: ESTADO, MEMÓRIA E REFERÊNCIAS";
  run_test "new e deref (!)" (Let("p", TyRef TyInt, New (Num 42), Deref(Id "p"))) [];
  run_test "new, assign (:=) e deref (!)"
    (Let("p", TyRef TyInt, New (Num 10),
      Seq(
        Asg(Id "p", Binop(Sum, Deref(Id "p"), Num 5)),
        Deref(Id "p")
      )
    )) [];
  run_test "Duas referências"
    (Let("p1", TyRef TyInt, New (Num 1),
      Let("p2", TyRef TyInt, New (Num 2),
        Seq(
          Asg(Id "p1", Binop(Sum, Deref(Id "p1"), Num 9)),
          Binop(Sum, Deref(Id "p1"), Deref(Id "p2"))
        )
      )
    )) [];

  print_category_title "CATEGORIA 4: LAÇOS DE REPETIÇÃO (WHILE)";
  run_test "While que não executa (condição falsa)"
    (Let("i", TyRef TyInt, New (Num 5),
      Seq(
        Wh(Binop(Lt, Deref(Id "i"), Num 5), Unit),
        Deref(Id "i")
      )
    )) [];
  run_test "While como contador"
    (Let("i", TyRef TyInt, New (Num 0),
      Seq(
        Wh(Binop(Lt, Deref(Id "i"), Num 3),
          Asg(Id "i", Binop(Sum, Deref(Id "i"), Num 1))
        ),
        Deref(Id "i")
      )
    )) [];

  print_category_title "CATEGORIA 5: LAÇOS DE REPETIÇÃO (FOR)";
  run_test "FOR para imprimir de 0 a 3" for_test [];
  run_test "FOR que não executa (deve imprimir 5)" for_no_exec_test [];
  run_test "FOR aninhados" nested_for_test [];
  run_test "FOR para verificar valor final do contador (deve imprimir 4)" for_final_value_test [];

  print_category_title "CATEGORIA 6: ENTRADA E SAÍDA (READ/PRINT)";
  run_test "Print simples" (Print (Num 123)) [];
  run_test "Read simples" (Read) [999];
  run_test "Read, computa e Print" (Print(Binop(Mul, Read, Num 2))) [21];
  run_test "Múltiplos Read e Print"
    (Let("a", TyInt, Read,
      Let("b", TyInt, Read,
        Seq(
          Print(Binop(Sum, Id "a", Id "b")),
          Print(Binop(Sub, Id "a", Id "b"))
        )
      )
    )) [10; 7];

  print_category_title "CATEGORIA 7: TESTES DE ERRO";
  run_test "ERRO DE TIPO: Soma de int e bool" (Binop(Sum, Num 1, Bool true)) [];
  run_test "ERRO DE TIPO: Condição do If não é bool" (If(Num 0, Num 1, Num 2)) [];
  run_test "ERRO DE TIPO: Tipos diferentes no Then/Else" (If(Bool true, Num 1, Bool false)) [];
  run_test "ERRO DE TIPO: Atribuição de tipo incorreto a ref"
    (Let("p", TyRef TyInt, New (Num 1), Asg(Id "p", Bool true))) [];
  run_test "ERRO DE TIPO: Deref em um não-ref" (Deref (Num 10)) [];
  run_test "ERRO DE TIPO: Variável não declarada" (Binop(Sum, Id "x", Num 5)) [];
  run_test "ERRO DE TIPO (FOR): Condição não booleana" for_error_cond_type [];
  run_test "ERRO DE TIPO (FOR): Variável da condição não declarada" for_error_unbound_var [];
  run_test "ERRO DE EXECUÇÃO: Divisão por zero" (Binop(Div, Num 10, Num 0)) [];
  run_test "ERRO DE EXECUÇÃO: Leitura de entrada vazia" (Read) [];
;;

print_category_title "CATEGORIA 8: TESTE DO PROFESSOR (FATORIAL)";
run_test "Fatorial de 5" fat [5];;

print_endline "\nFIM DOS TESTES."