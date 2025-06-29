# l2-interpreter
L2 language interpreter implemented in OCaml. INF05516 - Semântica Formal (25/1)

![oCamel](./ocamel.jpg)

- [x] Sintaxe abstrata
  - [x] Expressões de L1
  - [x] Expressões de L2
- [x]  Semântica operacional
    - [x]  Implementar as novas expressões
    - [x]  Implementar novos valores
    - [x]  Implementar novos tipos
- [x]  Avaliação small-step
    - [x]  Implementar todas as regras com memória
    - [x]  Implementar todas as regras com in,out
- [x]  Sistema de tipos
    - [x]  Implementar todas as regras de tipo no typeinfer
- [x]  Interpretador
    - [x]  Verificar exceções
    - [ ]  Testar

# Setup

Para instalar o ambiente necessário para rodar o interpretador L2, siga os passos abaixo:

1. Instale o [OPAM](https://opam.ocaml.org/doc/Install.html), o gerenciador de pacotes do OCaml.
2. Inicialize o OPAM (caso seja a primeira vez):
    ```sh
    opam init
    eval $(opam env)
    ```
3. Instale o compilador OCaml recomendado:
    ```sh
    opam switch create 4.14.0
    eval $(opam env)
    ```
4. Instale as dependências do projeto:
    ```sh
    opam install ounit2
    ```
5. Clone este repositório e navegue até o diretório do projeto:
    ```sh
    git clone <url-do-repositorio>
    cd l2-interpreter
    ```

Agora o ambiente está pronto para compilar e rodar o interpretador.

**Observação:**  
Se o projeto utilizar um arquivo `dune`, pode ser necessário instalar o Dune:
```sh
opam install dune
```
E para rodar os testes:
```sh
dune runtest
```

# Como rodar arquivos `.ml`

Para executar arquivos OCaml (`.ml`), siga os passos abaixo:

## 1. Compilar e rodar com o interpretador interativo

Você pode usar o interpretador `ocaml` para testar comandos interativamente:

```sh
ocaml
```

Dentro do interpretador, carregue seu arquivo:

```ocaml
#use "l2.ml";;
```

## 2. Compilar para bytecode

Para compilar um arquivo `.ml` para bytecode e executar:

```sh
ocamlc -o l2 l2.ml
./l2
```

# Testes

## Como instalar e rodar testes com OUnit2

Para utilizar o OUnit2 para testes unitários no seu projeto OCaml, siga os passos abaixo:

### 1. Instale o OUnit2

Se ainda não instalou, execute:

```sh
opam install ounit2
```

### 2. Escreva seus testes

Crie um arquivo, por exemplo `test.ml`, com seus testes. Exemplo básico:

```ocaml
open OUnit2

let test_soma _ =
    assert_equal 4 (2 + 2)

let suite =
    "Testes" >::: [
        "test_soma" >:: test_soma;
    ]

let () =
    run_test_tt_main suite
```

### 3. Compile e execute os testes

Compile o arquivo de teste com as dependências do OUnit2:

```sh
ocamlfind ocamlc -o test -package ounit2 -linkpkg test.ml
./test
```

Se estiver usando Dune, basta rodar:

```sh
dune runtest
```

Os resultados dos testes aparecerão no terminal, indicando quais passaram ou falharam.