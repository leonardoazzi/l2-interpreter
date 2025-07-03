(* Trabalho de Semântica Formal 

Leonardo Azzi Martins
Leonardo Dalpian Dutra

Objetivo: implementar em OCaml um interpretador para a linguagem L2 da especificação.
Bônus: com variações definidas que serão deixadas propositalmente subespecificadas.

*)

(* filepath: l2.ml *)
module L2 = struct

(* Exceções *)
exception BugTypeInfer  (* Declara exceção para erros de tipo inferido *)
exception NoRuleApplies (* Declara exceção para quando não há regra aplicável *)
exception TypeError of string (* Declara exceção para erros de tipo *)


(* ========= Sintaxe Abstrata ========= *)

(* Expressões binárias *)
(* bop ∈ {+, -, *, /, ==, <>, <, >, &&, ||}*)
type bop =  
  | Sum | Sub | Mul | Div   (* operações aritméticas *)
  | Eq  | Neq | Lt | Gt   (* operações relacionais  *)
  | And | Or   (* operações lógicas *) 

(* Identificadores *)
type ident = string 

(* Localização de uma variável no ambiente de execução *)
type loc = int

(* Tipos *)
type tipo =
  | TyBool        (* bool *)
  | TyInt         (* int *)
  | TyRef of tipo (* ref T *)
  | TyUnit        (* unit *)

(* Expressões *)
type expr = 
  | Num of int (* números inteiros *)                               (* n ∈ Z *)
  | Bool of bool (* valores booleanos *)                            (* b ∈ {true, false} *)
  | If of expr * expr * expr (* operação if else *)                 (* if e_1 then e_2 else e_3 *)
  | Binop of bop * expr * expr (* operações binárias *)             (* e_1 op e_2*)
  | Id of ident (* variável identificada por um nome *)             (* x *)
  | Let of ident * tipo * expr * expr (* declaração local *)               (* let x:T = e_1 in e_2*)
  | Asg of expr * expr (* atribuição de valor a local dememória *)  (* e_1 := e_2*)
  | Deref of expr (* Acessa o valor em uma posição de memória *)    (* !e *)
  | New of expr (* aloca valor em uma nova posição de memória *)    (* new e *)
  | Unit (* valor unitário, indica ausência de valor *)             (* () *)
  | Wh of expr * expr (* laço de repetição *)                       (* while e_1 do e_2 *)
  | Seq of expr * expr (* sequência de expressões *)                (* e_1; e_2 *)
  | Memloc of loc (* referência a uma posição de memória *)         (* l *)
  | Read (* lê uma entrada*)                                        (* read() *)
  | Print of expr (* imprime uma expressão *)                       (* print e *)

(* Valores *)

(* isvalue: e → bool
   Verifica se uma expressão é um valor, ou seja, se não pode ser avaliada mais. *) 
let isvalue (e:expr) : bool = 
  match e with  (* Se avaliarem para true, as expressões são valores*)
   Num _   -> true   (* n *)
  | Bool _  -> true   (* b *)
  | Unit  -> true     (* () *)
  | Memloc _ -> true  (* l *)
  | _ -> false

(* in *)
type inlist =
  | EmptyIn                   (* [] *)
  | ConsIn of int * inlist    (* n::in *)

(* out *)
type outlist =
  | EmptyOut                   (* [] *)
  | ConsOut of int * outlist   (* n::out *)

(* Função para converter uma operação binária em string *)
let rec string_of_op (op: bop)  : string = 
  match op with 
    Sum -> " + " 
  | Sub -> " - "
  | Mul -> " * "
  | Div -> " / "  
  | Eq  -> " = "
  | Neq -> " != "
  | Lt -> " < "
  | Gt -> " > "  
  | And -> " and "
  | Or -> " or "
  
(* Função para converter um tipo em string *)
let rec string_of_tipo (t: tipo)  : string = 
  match t with 
    TyInt  -> " int " 
  | TyBool -> " bool " 
  | TyRef t_ -> "ref " ^ string_of_tipo t_
  | TyUnit -> " unit "
  | _ -> 
      raise (TypeError "tipo não suportado para conversão em string") (* TODO: adicionar mais tipos *)
    
(* Função para converter uma expressão em string *)
let rec string_of_expr (e : expr) : string = 
  match e with
  | Num  n  -> string_of_int n
  | Bool b  -> string_of_bool b 
  | If(e1,e2,e3) -> " if "    ^ (string_of_expr e1) ^ 
                    " then "  ^ (string_of_expr e2) ^ 
                    " else "  ^ (string_of_expr e3) 
  | Binop (op,e1,e2)  ->  (string_of_expr e1)  ^ (string_of_op op) ^ (string_of_expr e2)
  | Id x -> x
  | Let (x, tipo, e1, e2) -> "let " ^ x ^ " : " ^ (string_of_tipo tipo) ^ 
                              " = " ^ (string_of_expr e1) ^ 
                              " in " ^ (string_of_expr e2)
  | Asg (e1, e2) -> (string_of_expr e1) ^ " := " ^ (string_of_expr e2)
  | Deref e1 -> "!" ^ (string_of_expr e1)
  | New e1 -> "new " ^ (string_of_expr e1)
  | Unit -> "()"
  | Wh (e1, e2) -> "while " ^ (string_of_expr e1) ^ 
                   " do " ^ (string_of_expr e2)
  | Seq (e1, e2) -> (string_of_expr e1) ^ "; " ^ (string_of_expr e2)
  | Memloc loc -> "l" ^ string_of_int loc
  | Read -> "read()"
  | Print e1 -> "print " ^ (string_of_expr e1)
  

(* ========= Semântica Operacional small-step ========= *)

(* Memória *)
(* Representação da memória como uma lista de pares (local, valor) *)
type tymem = (loc * expr) list 
let empty_mem : tymem = []

(* Expressão memória da semântica small-step *)
type expr_mem = expr * tymem * inlist * outlist

(* ========= Funções auxiliares ========= *)

(* read: read ()
Função para ler uma string da entrada padrão *)
let read (unit) : int =
  try
    print_endline "Digite um inteiro:";
    (* Lê uma linha da entrada padrão e retorna como string *)
    let input = read_int () in
    input;
  with _ -> raise (TypeError "entrada inválida para read_string()")

let print (e: expr_mem): unit =
  match e with
  | (Num n, _, _, _) -> print_endline (string_of_int n)  (* Imprime número *)
  | _ -> raise (TypeError "expressão não suportada para impressão")  (* Exceção para expressões não suportadas *)

(* isvalue: e → bool
   Verifica se uma expressão é um valor, ou seja, se não pode ser avaliada mais. *)

(* update_memory: σ[l → v]
  Atualiza a memória g com um valor v na localização l *)
let update_memory (g: tymem) (l: loc) (v: expr) : tymem =
  let rec aux mem = 
    match mem with
      [] -> [(l, v)]  (* Se a memória estiver vazia, adiciona o novo par *)
    | (loc, _) :: tail when loc = l -> (l, v) :: tail  (* Se a localização já existir, atualiza o valor *)
    | head :: tail -> head :: aux tail  (* Caso contrário, mantém o par e continua procurando *)
  in aux g

(* lookup_memory: !l
Recupera o valor em uma localização l, caso esteja na memória g*)
let lookup_memory (g: tymem) (l: loc) : expr option =
  let rec aux mem = 
    match mem with
      [] -> None  (* Se a memória estiver vazia, retorna None *)
    | (loc, v) :: tail when loc = l -> Some v  (* Se encontrar a localização, retorna o valor *)
    | _ :: tail -> aux tail  (* Caso contrário, continua procurando *)
  in aux g

(* subs: {v/x}
  Função para substituir uma variável x por um valor v em uma expressão e.
  Se a variável for a mesma, substitui pelo valor, caso contrário, mantém a expressão.
  Se a variável for uma localização de memória, substitui o valor na memória. *)
let rec subs (v: expr) (x: string) (e: expr) : expr =
  match e with
  | Num _ -> e
  | Bool _ -> e
  | Id y -> if y = x then v else e
  | Binop (op, e1, e2) -> Binop (op, subs v x e1, subs v x e2)
  | If (e1, e2, e3) -> If (subs v x e1, subs v x e2, subs v x e3)
  | Let (y, tipo, e1, e2) when y = x ->
      Let (y, tipo, subs v x e1, e2)  (* Não substitui em e2 por shadowing *)
  | Let (y, tipo, e1, e2) ->
      Let (y, tipo, subs v x e1, subs v x e2)
  | Asg (e1, e2) -> Asg (subs v x e1, subs v x e2)
  | Deref e1 -> Deref (subs v x e1)
  | New e1 -> New (subs v x e1)
  | Seq (e1, e2) -> Seq (subs v x e1, subs v x e2)
  | Wh (e1, e2) -> Wh (subs v x e1, subs v x e2)
  | Print e1 -> Print (subs v x e1)
  | Unit -> Unit
  | Memloc _ -> e
  | Read -> Read
  | _ -> raise (TypeError "expressão não suportada para substituição")

  (* append_out: outlist * int → outlist
   Função para adicionar um valor v a uma lista de saída out.
   Se a lista estiver vazia, cria uma nova lista com o valor.
   Caso contrário, adiciona o valor ao final da lista existente. *)
  let rec append_out (out: outlist) (v: int) : outlist =
    (* Debug: imprime o valor a ser adicionado e o estado atual da lista *)
    match out with
    | EmptyOut -> 
        ConsOut (v, EmptyOut)
    | ConsOut (h, t) -> 
        ConsOut (h, append_out t v)

(* step: -> 
  Função para aplicar uma avaliação small-step na expressão *)
let rec step (e, mem, in_, out_) = 
  print_endline ("step: " ^ string_of_expr e);
  match (e, mem, in_, out_) with 

  (* == VALORES ================================================================== *)
  | (Num n, mem, in_, out_)   -> raise NoRuleApplies
  | (Bool b, mem, in_, out_)  -> raise NoRuleApplies
  | (Unit, mem, in_, out_)    -> raise NoRuleApplies
  | (Memloc l, mem, in_, out_) -> raise NoRuleApplies

  (* == OP N ==================================================================== *)
  | (Binop (Sum, Num n1, Num n2), mem, in_, out_) ->                (* OP+ *)
      (Num (n1 + n2), mem, in_, out_)
  | (Binop (Lt, Num n1, Num n2), mem, in_, out_) when n1 < n2 ->    (* OP<TRUE *)
      (Bool true, mem, in_, out_)
  | (Binop (Lt, Num n1, Num n2), mem, in_, out_) when n1 >= n2 ->   (* OP<FALSE *)
      (Bool false, mem, in_, out_)  
  | (Binop (Gt, Num n1, Num n2), mem, in_, out_) when n1 > n2 ->    (* OP>TRUE *)
      (Bool true, mem, in_, out_)
  | (Binop (Gt, Num n1, Num n2), mem, in_, out_) when n1 <= n2 ->   (* OP>FALSE *)
      (Bool false, mem, in_, out_)
  | (Binop (And, Bool b1, Bool b2), mem, in_, out_) when b1 && b2 -> (* OP&&TRUE *)
      (Bool true, mem, in_, out_)
  | (Binop (And, Bool b1, Bool b2), mem, in_, out_) when not (b1 && b2) -> (* OP&&FALSE *)
      (Bool false, mem, in_, out_)
  | (Binop (Or, Bool b1, Bool b2), mem, in_, out_) when b1 || b2 -> (* OP||TRUE *)
      (Bool true, mem, in_, out_)
  | (Binop (Or, Bool b1, Bool b2), mem, in_, out_) when not (b1 || b2) -> (* OP||FALSE *)
      (Bool false, mem, in_, out_)
  | (Binop (Eq, Num n1, Num n2), mem, in_, out_) when n1 = n2 ->    (* OP=TRUE *)
      (Bool true, mem, in_, out_)
  | (Binop (Eq, Num n1, Num n2), mem, in_, out_) when n1 <> n2 -> (* OP=FALSE *)
      (Bool false, mem, in_, out_)
  | (Binop (Neq, Num n1, Num n2), mem, in_, out_) when n1 <> n2 -> (* OP<>TRUE *)
      (Bool true, mem, in_, out_)
  | (Binop (Neq, Num n1, Num n2), mem, in_, out_) when n1 = n2 -> (* OP<>FALSE *)
      (Bool false, mem, in_, out_)
  | (Binop (Sub, Num n1, Num n2), mem, in_, out_) -> (* OP- *)
      (Num (n1 - n2), mem, in_, out_)
  | (Binop (Mul, Num n1, Num n2), mem, in_, out_) -> (* OP* *)
      (Num (n1 * n2), mem, in_, out_)
  | (Binop (Div, Num n1, Num n2), mem, in_, out_) when n2 <> 0 -> (* OP/ *)
      (Num (n1 / n2), mem, in_, out_)
  | (Binop (Div, Num n1, Num n2), mem, in_, out_) when n2 = 0 -> (* OP/0 *)
      raise (TypeError "Divisão por zero")  (* Lança exceção se divisão por zero *)
     
  (* == OP ====================================================================== *)
  | (Binop (op,v1,e2), mem, in_, out_) when isvalue v1 ->           (* OP-2 *)
      let (e2', mem', in_', out_') = step (e2, mem, in_, out_) in 
      (Binop (op,v1,e2'), mem', in_', out_') 
  | (Binop (op,e1,e2), mem, in_, out_) ->                           (* OP-1 *) 
      let (e1', mem', in_', out_') = step (e1, mem, in_, out_) in 
      (Binop (op,e1',e2), mem', in_', out_') 


  (* == IF ====================================================================== *)
  | (If(Bool true,e2,e3), mem, in_, out_)  -> (e2, mem, in_, out_)  (* IF-1 *)
  | (If(Bool false,e2,e3), mem, in_, out_) -> (e3, mem, in_, out_)  (* IF-2 *)
  | (If(e1,e2,e3), mem, in_, out_) -> 
      let (e1', mem', in_', out_') = step (e1, mem, in_, out_) in 
        (If(e1', e2, e3), mem', in_', out_')                        (* IF-3 *)

  (* == E-LET =================================================================== *)

  (* E-LET2: aplica substituição se e1 já for um valor *)
  | (Let (x, tipo, v1, e2), mem, in_, out_) when isvalue v1 ->
      let e2' = subs v1 x e2 in
      (e2', mem, in_, out_)
  (* E-LET1: só aplica step em e1 se ele ainda não for um valor *)
  | (Let (x, tipo, e1, e2), mem, in_, out_) when not (isvalue e1) ->
      let (e1', mem', in_', out_') = step (e1, mem, in_, out_) in 
      (Let (x, tipo, e1', e2), mem', in_', out_')

  (* == ATR ===================================================================== *)
  | (Asg (e1, e2), mem, in_, out_) when not (isvalue e1) ->
      let (e1', mem', in_', out_') = step (e1, mem, in_, out_) in
      (Asg (e1', e2), mem', in_', out_')
  | (Asg (l, e2), mem, in_, out_) when isvalue l && not (isvalue e2) ->
      let (e2', mem', in_', out_') = step (e2, mem, in_, out_) in
      (Asg (l, e2'), mem', in_', out_')
  | (Asg (l, v1), mem, in_, out_) when isvalue l && isvalue v1 ->
      (Unit, update_memory mem (match l with
                                  Memloc loc -> loc
                                | _ -> raise NoRuleApplies) v1, in_, out_) 
  (* == DERREF ================================================================== *)
  | (Deref l, mem, in_, out_) when isvalue l ->                  (* DERREF1 *)
      (match lookup_memory mem (match l with 
                                Memloc loc -> loc 
                                | _ -> raise NoRuleApplies) with
       (* Se a localização existir, retorna o valor *)
       | Some v -> (v, mem, in_, out_)  
       (* Se não existir, lança exceção *) 
       | None -> raise NoRuleApplies)  
  | (Deref e, mem, in_, out_) ->                                 (* DERREF *)
      let (e', mem', in_', out_') = step (e, mem, in_, out_) in 
        (Deref e', mem', in_', out_')         

  (* == NEW ====================================================================== *)
  | (New (v), mem, in_, out_) when isvalue v ->                     (* NEW1 *)
      (* Nova localização baseada no tamanho atual da memória *)                           
      let loc = List.length mem in  
      (Memloc loc, update_memory mem loc v, in_, out_)  
  | (New (e), mem, in_, out_) ->                                    (* NEW *)
      let (e', mem', in_', out_') = step (e, mem, in_, out_) in 
        (New (e'), mem', in_', out_')            

  (* == SEQ ====================================================================== *)
  | (Seq (Unit, e2), mem, in_, out_) -> (e2, mem, in_, out_)        (* SEQ1 *)
  | (Seq (e1,e2), mem, in_, out_) ->                                (* SEQ2 *)
      let (e1', mem', in_', out_') = step (e1, mem, in_, out_) in 
      (Seq (e1', e2), mem', in_', out_')                                         

  (* == WHILE ==================================================================== *)
  | (Wh (e1, e2), mem, in_, out_) ->
      (If(e1, Seq(e2, Wh(e1, e2)), Unit), mem, in_, out_)
  (* == PRINT ==================================================================== *)
  | (Print n, mem, in_, out_) when isvalue n ->                     (* PRINT-N *)
    (match n with
     | Num v -> 
         let updated_out = append_out out_ v in
         (Unit, mem, in_, updated_out)
     | _ -> 
         raise (TypeError "Print só suporta números"))
  | (Print (Let (x, tipo, v1, e2)), mem, in_, out_) when isvalue v1 ->
      (Print (subs v1 x e2), mem, in_, out_)
  | (Print e, mem, in_, out_) when not (isvalue e) -> 
    let (e', mem', in_', out_') = step (e, mem, in_, out_) in     (* PRINT *)
    (Print e', mem', in_', out_')     
  | (Print n, mem, in_, out_) when isvalue n ->                     (* PRINT-N *)
    (match n with
     | Num v -> 
         let updated_out = append_out out_ v in
         (Unit, mem, in_, updated_out)
     | _ -> 
         raise (TypeError "Print só suporta números"))

  (* == READ ===================================================================== *)
  | (Read, mem, in_, out_) -> 
    (* Se a expressão for Read, lê um valor da entrada *)         (* READ *)
    (match in_ with
    | EmptyIn -> 
      raise (TypeError "entrada vazia")
    | ConsIn (n, rest) -> 
      (Num n, mem, rest, out_))



  (* == NONE ===================================================================== *) 
  | _ -> 
    raise (TypeError "Nenhuma regra se aplica à expressão fornecida")  (*Caso não haja regra aplicável*)
    
(* ========= Sistema de Tipos ========= *)
type tyenv = (string * tipo) list (* Γ Ambiente de tipos *)
let empty_env : tyenv = []

(* Função para inferir o tipo de uma expressão *)
let rec typeinfer (env: tyenv) (e:expr) : tipo =
  match e with 
  | Num _ -> TyInt                                (* T-INT *)
  | Bool _  -> TyBool                             (* T-BOOL *)                 
    
  | Binop (Sum,e1,e2) ->                          (* T-OP+ *)   
      let t1 = typeinfer env e1 in
      let t2 = typeinfer env e2 in
      if t1 = TyInt then 
        if t2 = t1 then TyInt
        else raise (TypeError "e2 não é do tipo int")
      else raise (TypeError "e1 não é do tipo int")

  | Binop (Sub,e1,e2) ->                          (* T-OP- *)   
      let t1 = typeinfer env e1 in 
      let t2 = typeinfer env e2 in
      if t1 = TyInt then
        if t2 = t1 then TyInt
        else raise (TypeError "e2 não é do tipo int")
      else raise (TypeError "e1 não é do tipo int")

  | Binop (Mul,e1,e2) ->                          (* T-OP* *)
      let t1 = typeinfer env e1 in
      let t2 = typeinfer env e2 in
      if t1 = TyInt then 
        if t2 = t1 then TyInt
        else raise (TypeError "e2 não é do tipo int")
      else raise (TypeError "e1 não é do tipo int")

  | Binop (Div,e1,e2) ->                          (* T-OP/ *)
      let t1 = typeinfer env e1 in
      let t2 = typeinfer env e2 in
      if t1 = TyInt then 
        if t2 = t1 then TyInt
        else raise (TypeError "e2 não é do tipo int")
      else raise (TypeError "e1 não é do tipo int")

  | Binop (Lt,e1,e2) ->                          (* T-OP< *)   
      let t1 = typeinfer env e1 in
      let t2 = typeinfer env e2 in
      if t1 = TyInt then 
        if t2 = t1 then TyBool
        else raise (TypeError "e2 não é do tipo int")
      else raise (TypeError "e1 não é do tipo int")

  | Binop (Gt,e1,e2) ->                          (* T-OP> *)   
      let t1 = typeinfer env e1 in
      let t2 = typeinfer env e2 in
      if t1 = TyInt then 
        if t2 = t1 then TyBool
        else raise (TypeError "e2 não é do tipo int")
      else raise (TypeError "e1 não é do tipo int")

  | Binop (Eq,e1,e2) ->                          (* T-OP= *)   
      let t1 = typeinfer env e1 in
      let t2 = typeinfer env e2 in
      if t1 = t2 then TyBool
      else raise (TypeError "e1 e e2 devem ser do mesmo tipo para comparação")

  | Binop (Neq,e1,e2) ->                          (* T-OP!= *)
      let t1 = typeinfer env e1 in
      let t2 = typeinfer env e2 in
      if t1 = t2 then TyBool
      else raise (TypeError "e1 e e2 devem ser do mesmo tipo para comparação")

  | Binop (And,e1,e2) ->                          (* T-OP&& *)
      let t1 = typeinfer env e1 in
      let t2 = typeinfer env e2 in
      if t1 = TyBool then
        if t2 = t1 then TyBool
        else raise (TypeError "e2 não é do tipo bool")
      else raise (TypeError "e1 não é do tipo bool")

  | Binop (Or,e1,e2) ->                           (* T-OP|| *)
      let t1 = typeinfer env e1 in
      let t2 = typeinfer env e2 in
      if t1 = TyBool then
        if t2 = t1 then TyBool
        else raise (TypeError "e2 não é do tipo bool")
      else raise (TypeError "e1 não é do tipo bool")

  | If (e1,e2,e3)         ->                     (* T-IF *)
      if (typeinfer env e1) = TyBool then
        let t2 = typeinfer env e2 in
        let t3 = typeinfer env e3 in 
        if t2 = t3 then t2 
        else raise (TypeError "then e else devem ser do mesmo tipo")
      else raise (TypeError "condição do if deve ser booleana ") 

  | Id x ->                                     (* T-ATR *)
      (try List.assoc x env
        with Not_found -> raise (TypeError ("variável livre: " ^ x)))

  | Let (x, tipo, e1, e2) ->                    (* T-LET *)
      let t1 = typeinfer env e1 in
        if t1 = tipo then
          let n_env = ((x, tipo) :: env) in     (* x |→ T *)
          typeinfer n_env e2
        else raise (TypeError ("tipo de e1 não corresponde ao tipo declarado para " ^ x))
      
  | Asg (e1, e2) ->                             (* T-ATR *)
      let t1 = typeinfer env e1 in
      let t2 = typeinfer env e2 in
      if t1 = TyRef t2 then TyUnit
      else raise (TypeError ("o tipo ref T de e1 precisa ter o ser do mesmo tipo T de e2"))

  | Deref e1 ->                                (* T-DERREF *)
      let t1 = typeinfer env e1 in
      (match t1 with
        TyRef t -> t  (* Se for um tipo de referência, retorna o tipo referenciado *)
      | _ -> raise (TypeError "e1 deve ser do tipo ref T"))

  | New e1 ->                                   (* T-NEW *)
      let t1 = typeinfer env e1 in TyRef t1
  
  | Unit -> TyUnit                              (* T-UNIT *)

  | Wh (e1, e2) ->                           (* T-WHILE *)
      if (typeinfer env e1) = TyBool then
        let t2 = typeinfer env e2 in
        if t2 = TyUnit then TyUnit
        else raise (TypeError "corpo do while deve ser do tipo unit")
      else raise (TypeError "condição do while deve ser booleana")

  | Seq (e1, e2) ->                             (* T-SEQ *)
      let t1 = typeinfer env e1 in
      let t2 = typeinfer env e2 in
      if t1 = TyUnit then t2
      else raise (TypeError "e1 deve ser do tipo unit")

  | Read -> TyInt                               (* T-READ *)

  | Print e1 ->                                 (* T-PRINT *)
      let t1 = typeinfer env e1 in
      if t1 = TyInt then TyUnit
      else raise (TypeError "print só suporta números inteiros")

  | _ -> 
        raise BugTypeInfer


(* ========= Interpretador ========= *)

(* Função principal de avaliação - versão tail-recursive para garantir avaliação completa de lets aninhados *)
let rec eval (e: expr_mem) : expr_mem  =
  let rec aux (e: expr_mem) =
    try 
      let e' = step e in
      aux e'
    with NoRuleApplies -> e
  in aux e

(* Função para imprimir a saída *)
let rec print_outlist out =
  match out with
  | EmptyOut -> ();
  | ConsOut (n, rest) ->
      print_string ("Saída: " ^ string_of_int n ^ "\n");
      print_outlist rest

(* Função para interpretar uma expressão e imprimir o resultado *)
let interp (env:tyenv) (e:expr_mem) : unit = 
  try
    let (e1, _, _, _) = e in
    let t = typeinfer env e1 in
    let v = eval e in
    let (v1, _, _, out) = v in
    print_string ((string_of_expr v1) ^ " : " ^ (string_of_tipo t) ^ "\n");
    print_outlist out;

    (* Imprime o estado atual da memória *)
    let rec print_mem mem =
      match mem with
      | [] -> ()
      | (loc, v)::rest ->
          print_string ("Mem[" ^ string_of_int loc ^ "] = " ^ string_of_expr v ^ "\n");
          print_mem rest
    in
    let (_, mem, _, _) = v in
    print_mem mem
  with
    TypeError msg ->  print_string ("erro de tipo - " ^ msg) 
  | BugTypeInfer  ->  print_string "corrigir bug em typeinfer"

(* ========= ASTs para TESTES ========= *)

(*         
           
let  x: int     =  read() in 
let  z: ref int = new x in 
let  y: ref int = new 1 in 

(while (!z > 0) (
        y :=  !y * !z;
        z :=  !z - 1);
print (! y))     

*)

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

end

(* ========== Testes de Avaliação ========= *)
let teste =
L2.interp L2.empty_env (L2.fat, L2.empty_mem, L2.ConsIn (4, L2.EmptyIn), L2.EmptyOut);