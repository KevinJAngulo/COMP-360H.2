%{
    open Ast.Expression
    open Ast.Stm
    open Ast.Program

    let rec left_assoc e es =
        match es with
        | [] -> e
        | (b, e') :: es -> left_assoc (Binop(b, e, e')) es
%}

%token <string> ID

%token <int> NUM
%token <bool> BOOL
%token <string> STRING

%token ASSIGN
%token PLUS
%token MINUS
%token TIMES
%token DIV
%token MOD
%token NOT
%token AND
%token OR
%token EQ
%token NE
%token LT
%token LE
%token GT
%token GE

%token LPAREN
%token RPAREN
%token LBRACE
%token RBRACE
%token SEMI
%token COMMA

%token FUNCTION

%token SKIP
%token VAR
%token IF
%token THEN
%token ELSE
%token WHILE
%token DO
%token RETURN

%token EOF

%start terminated_exp
%start terminated_stm
%start terminated_pgm

%type <Ast.Expression.t> terminated_exp
%type <Ast.Stm.t> terminated_stm
%type <Ast.Program.t> terminated_pgm

%%

operator_separated_list(O, next):
    | e = next ; opsexps = list(op_sep_list_rest(O, next))
        { (e, opsexps) }

op_sep_list_rest(O, next):
    | o = O ; e = next
        { (o, e) }

exp:
    | e = assignexp
        { e }

assignexp:
    | x = ID ; ASSIGN ; e = exp
        { Assign(x, e) }
    | e = orexp
        { e }

%inline orop:
    | OR    { Or }

orexp:
    | p = operator_separated_list(orop, andexp)
        { let (e, opsexps) = p in left_assoc e opsexps }

%inline andop:
    | AND   { And }

andexp:
    | p = operator_separated_list(andop, compexp)
        { let (e, opsexps) = p in left_assoc e opsexps }

%inline compop:
    | EQ    { Eq }
    | NE    { Ne }
    | LT    { Lt }
    | LE    { Le }
    | GT    { Gt }
    | GE    { Ge }

compexp:
    | e0 = pmexp ; op = compop ; e1 = pmexp
        { Binop(op, e0, e1) }
    | e = pmexp
        { e }

%inline pmops:
    | PLUS  { Plus }
    | MINUS { Minus }

pmexp:
    | p = operator_separated_list(pmops, mdexp)
        { let (e, opsexps) = p in left_assoc e opsexps }

%inline mdops:
    | TIMES { Times }
    | DIV   { Div }
    | MOD   { Mod }

mdexp:
    | p = operator_separated_list(mdops, nexp)
        { let (e, opsexps) = p in left_assoc e opsexps }

nexp:
    | MINUS ; e = aexp
        { Neg e }
    | NOT ; e = aexp
        { Not e }
    | e = aexp
        { e }

aexp:
    | x = ID
        { Var x }
    | i = NUM           
        { Num i }
    | b = BOOL                      
        { Bool b }
    | s = STRING
        { Str s}
    | f = ID ; LPAREN ; args = separated_list(COMMA, exp) ; RPAREN    
        { Call(f, args) }
    | LPAREN; e = exp ; RPAREN      
        { e }

prim_stm:
    | SKIP                          
        { Skip }
    | VAR ; assts = separated_nonempty_list(COMMA, assign)
        { VarDec assts }
    | e = exp                       
        { Expr e }
    | RETURN ; e = option(exp)              
        { Return e }

assign:
    | x = ID ; e = option(init)
        { (x, e) }

init:
    | ASSIGN ; e = exp
        { e }

prim_stm_term:
    | s = terminated(prim_stm, SEMI)
        { s }

block_stm:
    | LBRACE ; ss = nonempty_list(stm) ; RBRACE     
        { Block ss }

compound_stm:
    | IF ; e = exp ; THEN ; s0 = body_stm ; ELSE ; s1 = stm
        { If(e, s0, s1) }
    | IF ; e = exp ; THEN ; s0 = stm
        { If(e, s0, Skip) }
    | WHILE ; e = exp ; DO ; s = stm
        { While(e, s) }

body_stm:
    | s = prim_stm_term
        {s}
    | s = block_stm
        {s}

stm: 
    | s = prim_stm_term
        { s }
    | s = compound_stm
        { s }
    | s = block_stm
        { s }

fundef:
    | FUNCTION ; f = ID ; LPAREN ; ps = separated_list(COMMA, ID) ; RPAREN ; 
      LBRACE; ss = nonempty_list(stm); RBRACE        
        { FunDef (f, ps, ss) }

pgm:
    | fundefs = nonempty_list(fundef)        { Pgm fundefs }

terminated_exp:
    | e = exp; EOF                  { e }

terminated_stm:
    | s = stm; EOF                  { s }

terminated_pgm:
    | p = pgm ; EOF                 { p }

