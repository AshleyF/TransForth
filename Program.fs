open System
open System.IO
open System.Text

let mem = Array.create 65536 0
let s = 0 // data stack
let r = 1 // return stack
let h = 2 // dictionary pointer
let l = 3 // latest pointer
mem.[h] <- 0x0400
mem.[s] <- 0xF000
mem.[r] <- 0x10000
mem.[l] <- mem.[h]
let append v = mem.[mem.[h]] <- v; mem.[h] <- mem.[h] + 1
let appendat v = let at = mem.[h] in append v; at

let push' reg value = mem.[reg] <- mem.[reg] - 1; mem.[mem.[reg]] <- value
let pop' reg () = mem.[reg] <- mem.[reg] + 1; mem.[mem.[reg] - 1]
let push = push' s
let pop = pop' s
let rpush = push' r
let rpop = pop' r

let header (name : string) =
    let link = mem.[l]
    mem.[l] <- mem.[h]
    let len = name.Length
    append len
    for i in [0..2] do
        append (if len > i then int name.[i] else 0)
    append link
let lnka addr = addr + 4
let cfa addr = addr + 5
let find (name : string) =
    let rec find' addr =
        if addr = 0x0400 // first cell is DOSEMI
        then -1 else
            let len = name.Length
            if mem.[addr] &&& 0x7FFFFFFF = len then
                if (len < 1 || mem.[addr + 1] = int name.[0]) && (len < 2 || mem.[addr + 2] = int name.[1]) && (len < 3 || mem.[addr + 3] = int name.[2])
                then addr else find' mem.[lnka addr]
            else find' mem.[lnka addr]
    find' mem.[l]
let immediate () = mem.[mem.[l]] <- mem.[mem.[l]] ||| 0x80000000
let isimmediate addr = mem.[addr] &&& 0x80000000 = 0x80000000

let convertbool b = if b then -1 else 0

let dyadic fn = pop () |> fn (pop ()) |> push // applied in infix order
let comp fn = dyadic (fun a b -> fn a b |> convertbool)

let mutable (out : TextWriter) = null
let print v = out.Write(v.ToString()); out.Write(' ')
let dot = (pop >> print)

let mutable (inp : TextReader) = null
let token () =
    let isWhiteSpace = char >> Char.IsWhiteSpace
    while inp.Peek() |> isWhiteSpace do
        inp.Read() |> ignore
    let word = new StringBuilder()
    while inp.Peek() |> isWhiteSpace |> not && inp.Peek() <> -1 do
        word.Append(inp.Read() |> char) |> ignore
    word.ToString()

let create () = token () |> header

let load () = push mem.[pop ()]
let store () = mem.[pop ()] <- pop ()

let mutable interactive = true
let dointeractive () = interactive <- true
let docompiling () = interactive <- false
let isinteractive () = convertbool interactive |> push

let comment term =
    while inp.Peek() |> char <> term do
        inp.Read() |> ignore
    inp.Read() |> ignore

let _HALT = -1
let IMMEDIATE = 9 // TODO
let ADD = 25
let MULT = 26
let DIV = 14
let MOD = 4
let NAND = 5
let GREATER = 6
let EQUAL = 7
let DOT = 8
let NEXT = 0
let CREATE = 10
let VARIABLE = 11
let LOAD = 12
let STORE = 13
let LIT = 3
let BRANCH = 15
let ZEROBRANCH = 16
let TICK = 17
let INTERACTIVE = 19 // TODO: MODE
let COMPILING = 20 // TODO: MODE
let COMMENTLINE = 22
let COMMENTBLOCK = 23
let DOVAR = 24
let DOCOL = 1
let DOSEMI = 2
let APPENDDOCOLON = 27
let APPENDSEMI = 28
let KEY = 29
let ECHO = 30
let FIND = 31
let EXEC = 32
let ISINTERACITVE = 33
let LITADDR = 34
let LSH = 35
let RSH = 36
let UM = 37
let DEBUG = 999

let SEMI_ADDR = appendat DOSEMI
let HALT_INST = appendat _HALT
let HALT_ADDR = appendat HALT_INST; // don't need SEMI; will halt anyway

let variable () = create (); append DOVAR; append 0; append NEXT
let appendsemi () = append SEMI_ADDR
let appenddocolon () = append DOCOL

let mutable i = 0
let mutable w = 0
let mutable p = 0

let next () = w <- mem.[i]; i <- i + 1; p <- w
let docol () = rpush i; i <- w + 1; next ()
let dosemi () = i <- rpop (); next ()

let primitive name code = header name; append code; append NEXT
let primitivecfa name code = primitive name code; cfa mem.[l]
let LIT_ADDR = primitivecfa "LIT" LIT
let litaddr () = push LIT_ADDR

let branch () = i <- mem.[i]
let zerobranch () = if pop() = 0 then i <- mem.[i] else i <- i + 1

let dolit () = push mem.[i]; i <- i + 1
let tick () = append LIT_ADDR; append (token() |> find |> cfa)
let dovar () = push p; p <- p + 1

let key () =
    if inp.Peek() = -1 then
        printf "ok\n>"
        inp <- new StringReader(Console.ReadLine() + Environment.NewLine)
    inp.Read() |> push
let echo () = pop () |> char |> out.Write

let findtok () =
    let sb = new StringBuilder()
    let len = mem.[mem.[h]]
    let tok = mem.[h] + 1
    for i in [tok..tok + len - 1] do
        mem.[i] |> char |> sb.Append |> ignore
    sb.ToString() |> find |> push

let debug () = printfn "DEBUG: %A" (Array.rev mem.[mem.[s]..0xF000-1])

let um () =
    use file = File.Open(@"C:\Users\ashley.feniello\Desktop\SkyFolder\Projects\UM-32\bin\Debug\transforth.um", FileMode.Create)
    //use file = File.Open(@"C:\Users\ashleyf\Desktop\SkyFolder\Projects\UM-32\bin\Debug\transforth.um", FileMode.Create)
    for i in pop () .. pop () do
        let m = mem.[i]
        m >>> 24 |> byte |> file.WriteByte
        m >>> 16 |> byte |> file.WriteByte
        m >>> 8 |> byte |> file.WriteByte
        m |> byte |> file.WriteByte

let rec exec () =
    let c = pop () |> cfa
    p <- c
    w <- c
    i <- HALT_ADDR
    execute ()

and execinline () =
    let c = pop () |> cfa
    p <- c
    w <- c
    rpush i
    execute ()

and execute () =
    let instruction = mem.[p]
    p <- p + 1
    match instruction with
    | -1 -> ()
    | 0 -> next ()
    | 1 -> docol ()
    | 2 -> dosemi ()
    | 3 -> dolit ()
    | 4 -> dyadic (%)
    | 5 -> dyadic (fun a b -> ~~~(a &&& b))
    | 6 -> comp (>)
    | 7 -> comp (=)
    | 8 -> dot ()
    | 9 -> immediate ()
    | 10 -> create ()
    | 11 -> variable ()
    | 12 -> load ()
    | 13 -> store ()
    | 14 -> dyadic (/)
    | 15 -> branch ()
    | 16 -> zerobranch ()
    | 17 -> tick ()
    | 19 -> dointeractive ()
    | 20 -> docompiling ()
    | 22 -> comment '\n'
    | 23 -> comment ')'
    | 24 -> dovar ()
    | 25 -> dyadic (+)
    | 26 -> dyadic (*)
    | 27 -> appenddocolon ()
    | 28 -> appendsemi ()
    | 29 -> key ()
    | 30 -> echo ()
    | 31 -> findtok ()
    | 32 -> execinline ()
    | 33 -> isinteractive ()
    | 34 -> litaddr ()
    | 35 -> dyadic (<<<)
    | 36 -> dyadic (>>>)
    | 37 -> um ()
    | 999 -> debug ()
    | _ -> failwith "Unknown instruction"
    if instruction <> -1 then execute ()

primitive "IMMEDIATE" IMMEDIATE
primitive "+" ADD
primitive "*" MULT
primitive "/" DIV
primitive "MOD" MOD
primitive "NAND" NAND
primitive ">" GREATER
primitive "=" EQUAL
primitive "." DOT
primitive "VARIABLE" VARIABLE
primitive "@" LOAD
primitive "!" STORE
primitive "BRANCH" BRANCH
primitive "0BRANCH" ZEROBRANCH
primitive "'" TICK; immediate ()
primitive "\\" COMMENTLINE; immediate ()
primitive "(" COMMENTBLOCK; immediate ()
primitive "KEY" KEY
primitive "ECHO" ECHO
primitive "FIND" FIND
primitive "EXEC" EXEC
primitive "ISINTERACITVE" ISINTERACITVE
primitive "LITADDR" LITADDR
primitive "LSH" LSH
primitive "RSH" RSH
primitive "UM" UM
primitive "$" DEBUG

let INTERACTIVE_ADDR = primitivecfa "INTERACTIVE" INTERACTIVE in immediate ()
let APPENDDOCOLON_ADDR = primitivecfa "APPENDDOCOLON" APPENDDOCOLON
let APPENDSEMI_ADDR = primitivecfa "APPENDSEMI" APPENDSEMI
let CREATE_ADDR = primitivecfa "CREATE" CREATE
let COMPILING_ADDR = primitivecfa "COMPILING" COMPILING

let rep () =
    while inp.Peek() <> -1 do
        let word = token ()
        if word.Length > 0 then
            match find word with
            | -1 -> // literal?
                let number, value = Int32.TryParse word
                if number then
                    if interactive then push value else append LIT_ADDR; append value
                else word + "?" |> failwith
            | d ->
                if interactive || isimmediate d
                then push d; exec ()
                else cfa d |> append
let reps source = inp <- new StringReader(source); rep ()

header ";"; append DOCOL; append APPENDSEMI_ADDR; append INTERACTIVE_ADDR; append SEMI_ADDR; immediate ()
header ":"; append DOCOL; append CREATE_ADDR; append APPENDDOCOLON_ADDR; append COMPILING_ADDR; append SEMI_ADDR

out <- Console.Out
reps "
: S   0 ;
: R   1 ;
: H   2 ;
: L   3 ;
: S0   61439 ; \ 0xF000 - 1
: HERE   H @ ;
: LATEST   L @ ;
: SP@   S @ ;
: NEGATE   -1 * ;
: -  ( a b -- diff)  NEGATE + ;
: 1+ 1 + ;
: 1- 1 - ;
: DEPTH  ( -- n)  S0 SP@ - ;
: CLEAR   ( --)  S0 1+ S ! ;
: DROP   ( a -- )  SP@ 1+ S ! ;
: , ( v --) HERE ! HERE 1+ H ! ;
: BEGIN   HERE ; IMMEDIATE
: UNTIL   ' 0BRANCH , , ; IMMEDIATE
: PICK   SP@ + 1+ @ ;
: OVER  ( a b -- a b a)  1 PICK ;
: 2DUP  ( a b -- a b a b)  OVER OVER ;
: 2+ 2 + ;
: 2- 2 - ;
: 2* 2 * ;
: 2/ 2 / ;
: DUP  ( a -- a a)  0 PICK ;
: >R   R @ DUP DUP 1- R !  @ R @ !  ! ;
: R>   R @ 1+ @  R @ @ R @ 1+ !  R @ 1+ R ! ;
: R@   R @ 1+ @ ;
: ROLL   SP@ 1+ + DUP @ >R BEGIN DUP >R 1- DUP @ R> ! DUP SP@ 2+ = UNTIL DROP R> SP@ 1+ ! ;
: ?   @ . ;
: ROT  ( a b c -- b c a)  2 ROLL ;
: SWAP  ( a b -- b a)  1 ROLL ;
: +!  ( add a -- )  DUP @  ROT +  SWAP ! ;
: ++! ( a -- a++) DUP @ 1+ SWAP ! ;
: COUNTER   2* 3 + R @ + @ ;
: I   0 COUNTER ;
: J   1 COUNTER ;
: K   2 COUNTER ;
: -ROT  ( a b c -- c a b)  ROT ROT ;
: NIP  ( a b -- b)  SWAP DROP ;
: TUCK  ( a b -- b a b)  SWAP OVER ;
: 2DROP  ( a b -- )  DROP DROP ;
: 3DROP  ( a b c -- ) 2DROP DROP ;
: 2OVER  ( a b c d -- a b c d a b)  3 PICK 3 PICK ;
: 3DUP  ( a b c -- a b c a b c)  DUP 2OVER ROT ;
: SQUARE  ( a -- a^2)  DUP * ;
: CUBE  ( a -- a^3)  DUP DUP * * ;
: /MOD  ( a b -- rem quot)  2DUP MOD -ROT / ;
: TRUE  ( -- t)  -1 ; \ normally constant
: FALSE  ( -- f)  0 ; \ normally constant
: NOT  ( a -- ~a)  DUP NAND ;
: AND  ( a b -- a&b)  NAND NOT ;
: OR  ( a b -- a|b)  NOT SWAP NOT NAND ;
: NOR  ( a b -- ~a|b)  OR NOT ;
: XOR  ( a b -- a^b)  2DUP AND -ROT NOR NOR ;
: XNOR ( a b -- ~a^b)  XOR NOT ;
: <  ( a b -- a<b)  2DUP > -ROT = OR NOT ;
: <=  ( a b -- a<=b)  2DUP < -ROT = OR ;
: >=  ( a b -- a>=b)  2DUP > -ROT = OR ;
: <>  ( a b -- ?)  = NOT ;
: 0>   0 > ;
: 0=   0 = ;
: 0<   0 < ;
: 0<>   0 <> ;
: IF   ' 0BRANCH , HERE 0 , ; IMMEDIATE
: ELSE   ' BRANCH , HERE 0 , SWAP HERE SWAP ! ; IMMEDIATE
: THEN   HERE SWAP ! ; IMMEDIATE
: ABS  ( n -- |n|)  DUP 0< IF NEGATE THEN ;
: MIN   2DUP > IF SWAP THEN DROP ;
: MAX   2DUP < IF SWAP THEN DROP ;
: WHILE   ' 0BRANCH , HERE 0 , ; IMMEDIATE
: REPEAT   ' BRANCH , HERE 1+ SWAP ! , ; IMMEDIATE
: LEAVE   ' BRANCH , HERE SWAP 0 , ; IMMEDIATE
: DO   HERE ' >R , ' >R , ; IMMEDIATE
: LOOP   ' R> , ' R> , ' 1+ , ' 2DUP , ' = , ' 0BRANCH , , ' 2DROP , ; IMMEDIATE
: +LOOP   ' R> , ' R> , ' ROT , ' + , ' 2DUP , ' = , ' 0BRANCH , , ' 2DROP , ; IMMEDIATE
: .S   SP@ 1- S0 2DUP < IF DO I @ . -1 +LOOP ELSE 2DROP THEN ;
: CRLF 13 ECHO 10 ECHO ;
: SP 32 ;
: DUMP ( m n -- ) DO I . I @ . CRLF LOOP ;
: ?DELIM ( v d -- v ?) 2DUP SP = IF >= ELSE = THEN ;
: ?WS SP ?DELIM ;
: SKIPWS KEY ?WS IF DROP SKIPWS THEN ; \ leaves first non-whitespace char on stack
: TOKEN ( delim -- tok) >R HERE 1+ R@ SP =
    IF SKIPWS ELSE KEY THEN BEGIN
      OVER ! 1+ KEY R@ ?DELIM
    UNTIL R> 2DROP HERE - 1- HERE ! ;
: WORD SP TOKEN ;
: CFA ( addr -- c) 5 + ;
: LINKA ( addr -- l) 4 + ;
: HEADER  WORD   LATEST HERE LINKA !   HERE L !   HERE CFA H ! ;
: FORGET   WORD FIND DUP H !  LINKA @ L ! ;
: TOKENCHARS ( -- b a) HERE HERE @ + 1+ HERE 1+ ;
: 0-ASCII 48 ;
: 9-ASCII 57 ;
: ?DIGIT ( c -- c ?) DUP 0-ASCII >= OVER 9-ASCII <= AND ;
: ?NUMBER 0 TRUE TOKENCHARS DO I @ ?DIGIT SWAP >R AND SWAP 10 * R> + 0-ASCII - SWAP LOOP DUP NOT IF SWAP DROP THEN ;
: ?FOUND ( w -- ?) DUP 0 >= ;
: HIGHBIT -2147483648 ;
: ISIMMEDIATE ( addr -- ?) @ HIGHBIT AND HIGHBIT = ;
: OUTER WORD FIND ?FOUND IF
    DUP ISIMMEDIATE ISINTERACTIVE OR
    IF EXEC ELSE CFA , THEN
  ELSE
    DROP ?NUMBER IF
      ISINTERACTIVE NOT IF LITADDR , , THEN
    ELSE
      63 ECHO SP ECHO \ ?
    THEN
  THEN
  OUTER ;


\ UM-32 Assembler - see: http://www.boundvariable.org/task.shtml

: ORIGIN 32768 ;

VARIABLE target
ORIGIN target !

: m, target @ !  target ++! ;

: msave  target @ 1- ORIGIN UM ;

: instruction,  ( cbai-m )  22 LSH OR  3 LSH OR  3 LSH OR  m, ;

: cmove,     ( abc-m )          0 instruction, ;  \  c = b if a
: fetch,     ( abc-m )          1 instruction, ;  \  c = b[a]
: store,     ( abc-m )          2 instruction, ;  \  c[b] = a
: add,       ( abc-m )          3 instruction, ;  \  c = b + a
: mult,      ( abc-m )          4 instruction, ;  \  c = b * a
: div,       ( abc-m )          5 instruction, ;  \  c = b / a
: nand,      ( abc-m )          6 instruction, ;  \  c = b ~& a
: halt,      (    -m )  0 0 0   7 instruction, ;
: alloc,     (  ab-m )      0   8 instruction, ;  \  new(b) -> a
: free,      (   a-m )    0 0   9 instruction, ;
: echo,      (   a-m )    0 0  10 instruction, ;
: key,       (   a-m )    0 0  11 instruction, ;
: loadjump,  (  ab-m )      0  12 instruction, ;  \  load(b), jump(a)

: literal,  ( va -- m )  13 3 LSH OR  25 LSH OR  m, ;  \  a = v

: z 0 ;  \  Zero constant register
: t 1 ;  \  Internal temp register
: y 2 ;  \  Temp register

: jump,  (   a-m )  z loadjump, ;  \  jump(a)  (uses t)

: move,  (  ab-m )  1 t literal, t -ROT cmove, ;    \  b = a  (uses t)
: inc,   (   a-m )  DUP 1 t literal, t SWAP add, ;  \  a++  (uses t)
: not,   (  ab-m )  SWAP DUP ROT nand, ;            \  b = ~a
: neg,   (  ab-m )  DUP -ROT not, inc, ;            \  b = -a  (uses t, indirectly)
: sub,   ( abc-m )  2 PICK DUP neg, -ROT add, ;     \  c = b - a  (uses t, indirectly)
: dec,   (   a-m )  0 t literal, t t t nand, DUP t SWAP add, ;  \  a--  (uses t)

: address  target @ ORIGIN - ;
: branch,  ( a-m )  y literal, y jump, ;  \  jump to a  (uses y and t, indirectly)
: 0branch,  ( ab-m )  y literal, address 1+ y cmove, y jump, ;  \  if a = 0, jump to b  (uses y and t)

: forward  target @ 0 ;  \  leave target address on stack for later patching
: tohere  DUP  @ address OR  SWAP ! ;  \  patch previous forward branch,

: chr WORD HERE 1+ @ ;

\ Inner Interpreter

: x 3 ;  \  Temp register
: w 4 ;  \  Working register
: i 5 ;  \  Interpreter register
: s 6 ;  \  Stack (data) register
: r 7 ;  \  Return stack register

: push,  ( ab-m )  \  b.push(a)
    DUP
    dec,    \  b--
  z store,  \  M[b] = a
;

: pop,  ( ab-m )  \  b = a.pop()
    OVER SWAP
  z SWAP       \  aazb
    fetch,     \  b = M[a]
    inc,       \  a++ 
;

forward branch,  \  over dictionary

\  00000     60 y literal
\  00001      z y loadjump

\ enter

VARIABLE &enter  address &enter !

i r push,  \  r.push(i)
2 t literal, t w i add,   \ i = w + 8 (skip over enter,)
\ falls through to next,

\  00002      0 t literal
\  00003    t t t nand
\  00004    r t r add
\  00005    z r i store
\  00006      2 t literal
\  00007    i w t add

: enter,  &enter @ x literal,  x jump, ;

\ next

VARIABLE &next  address &next !

i z w fetch,  \  w = M[i]
    i inc,    \  i++
    w jump,

\  00008    w z i fetch
\  00009      1 t literal
\  00010    i t i add
\  00011      z w loadjump

: next,  &next @ x literal,  x jump, ;

\ Dictionary

VARIABLE &exit  address &exit !
r i pop,  \  i = r.pop()
    next,

\  00012    i z r fetch
\  00013      1 t literal
\  00014    r t r add
\  00015      8 x literal
\  00016      z x loadjump

VARIABLE &lit  address &lit !
i z y fetch,  \  y = M[i]
  y s push,   \  s.push(y)
    i inc,    \  i++
      next,

\  00017    y z i fetch
\  00018      0 t literal
\  00019    t t t nand
\  00020    s t s add
\  00021    z s y store
\  00022      1 t literal
\  00023    i t i add
\  00024      8 x literal
\  00025      z x loadjump

VARIABLE &pick  address &pick !
    s y pop,    \  y = s.pop()
    s x move,   \  x = s
  y x x add,    \  x = x + y
  x z x fetch,  \  x = M[x]
    x s push,   \  s.push(x)
        next,

\  00026    y z s fetch
\  00027      1 t literal
\  00028    s t s add
\  00029      1 t literal
\  00030    x s t cmove
\  00031    x x y add
\  00032    x z x fetch
\  00033      0 t literal
\  00034    t t t nand
\  00035    s t s add
\  00036    z s x store
\  00037      8 x literal
\  00038      z x loadjump

VARIABLE &add  address &add !  \  TODO: More efficient
    s y pop,    \  y = s.pop()
  s z x fetch,  \  x = M[s]
  y x x add,    \  x = x + y
  x s z store,  \  M[s] = x
        next,
\    s y pop,   \  y = s.pop()
\    s x pop,   \  x = s.pop()
\  y x x add,   \  x = x + y
\    x s push,  \  s.push(x)
\        next,

\  00039    y z s fetch
\  00040      1 t literal
\  00041    s t s add
\  00042    x z s fetch
\  00043    x x y add
\  00044    z s x store
\  00045      8 x literal
\  00046      z x loadjump

VARIABLE &halt  address &halt !
halt,

\  00047          halt

VARIABLE &dup  address &dup !
enter,
&lit  @ m,
0       m,
&pick @ m,
&exit @ m,

\  00048      2 x literal
\  00049      z x loadjump
\  00050      17
\  00051      0
\  00052      26
\  00053      12

VARIABLE &double  address &double !
enter,
&dup  @ m,
&add  @ m,
&exit @ m,

\  00054      2 x literal
\  00055      z x loadjump
\  00056      48
\  00057      39
\  00058      12

\ Initialization

VARIABLE terminate  address terminate !
&halt @ m,

\  00059

tohere

16383 r literal,  \  top of return stack, 3FFF
12287 s literal,  \  top of data stack, 2FFF
terminate @ i literal,

\  00060  16383 r literal
\  00061  12287 s literal
\  00062     59 i literal

42 x literal,  x s push,
&double @ w literal,
&double @ branch,

\  00063     42 x literal
\  00064      0 t literal
\  00065    t t t nand
\  00066    s t s add
\  00067    z s x store
\  00068     54 w literal
\  00069     54 y literal
\  00070      z y loadjump

\ Image padding

: pad,  16384 address  DO 0 m, LOOP ;
pad, msave

\  00000     60 y literal     y = 60
\  00001      z y loadjump    load(z:0), jump(y:60)
\  00060  16383 r literal     r = 16383
\  00061  12287 s literal     s = 12287
\  00062     59 i literal     i = 59
\  00063     42 x literal     x = 42
\  00064      0 t literal     t = 0
\  00065    t t t nand        t = t:0 ~& t:0
\  00066    s t s add         s = t:4294967295 + s:12287
\  00067    z s x store       M[z:0][s:12286] = x:42
\  00068     54 w literal     w = 54
\  00069     54 y literal     y = 54
\  00070      z y loadjump    load(z:0), jump(y:54)
\  00054      2 x literal     x = 2
\  00055      z x loadjump    load(z:0), jump(x:2)
\  00002      0 t literal     t = 0
\  00003    t t t nand        t = t:0 ~& t:0
\  00004    r t r add         r = t:4294967295 + r:16383
\  00005    z r i store       M[z:0][r:16382] = i:59
\  00006      2 t literal     t = 2
\  00007    i w t add         i = w:54 + t:2
\  00008    w z i fetch       w = M[z:0][i:56]
\  00009      1 t literal     t = 1
\  00010    i t i add         i = t:1 + i:56
\  00011      z w loadjump    load(z:0), jump(w:48)
\  00048      2 x literal     x = 2
\  00049      z x loadjump    load(z:0), jump(x:2)
\  00002      0 t literal     t = 0
\  00003    t t t nand        t = t:0 ~& t:0
\  00004    r t r add         r = t:4294967295 + r:16382
\  00005    z r i store       M[z:0][r:16381] = i:57
\  00006      2 t literal     t = 2
\  00007    i w t add         i = w:48 + t:2
\  00008    w z i fetch       w = M[z:0][i:50]
\  00009      1 t literal     t = 1
\  00010    i t i add         i = t:1 + i:50
\  00011      z w loadjump    load(z:0), jump(w:17)
\  00017    y z i fetch       y = M[z:0][i:51]
\  00018      0 t literal     t = 0
\  00019    t t t nand        t = t:0 ~& t:0
\  00020    s t s add         s = t:4294967295 + s:12286
\  00021    z s y store       M[z:0][s:12285] = y:0
\  00022      1 t literal     t = 1
\  00023    i t i add         i = t:1 + i:51
\  00024      8 x literal     x = 8
\  00025      z x loadjump    load(z:0), jump(x:8)
\  00008    w z i fetch       w = M[z:0][i:52]
\  00009      1 t literal     t = 1
\  00010    i t i add         i = t:1 + i:52
\  00011      z w loadjump    load(z:0), jump(w:26)
\  00026    y z s fetch       y = M[z:0][s:12285]
\  00027      1 t literal     t = 1
\  00028    s t s add         s = t:1 + s:12285
\  00029      1 t literal     t = 1
\  00030    x s t cmove       x = s:12286 if t:1
\  00031    x x y add         x = x:12286 + y:0
\  00032    x z x fetch       x = M[z:0][x:12286]
\  00033      0 t literal     t = 0
\  00034    t t t nand        t = t:0 ~& t:0
\  00035    s t s add         s = t:4294967295 + s:12286
\  00036    z s x store       M[z:0][s:12285] = x:42
\  00037      8 x literal     x = 8
\  00038      z x loadjump    load(z:0), jump(x:8)
\  00008    w z i fetch       w = M[z:0][i:53]
\  00009      1 t literal     t = 1
\  00010    i t i add         i = t:1 + i:53
\  00011      z w loadjump    load(z:0), jump(w:12)
\  00012    i z r fetch       i = M[z:0][r:16381]
\  00013      1 t literal     t = 1
\  00014    r t r add         r = t:1 + r:16381
\  00015      8 x literal     x = 8
\  00016      z x loadjump    load(z:0), jump(x:8)
\  00008    w z i fetch       w = M[z:0][i:57]
\  00009      1 t literal     t = 1
\  00010    i t i add         i = t:1 + i:57
\  00011      z w loadjump    load(z:0), jump(w:39)
\  00039    y z s fetch       y = M[z:0][s:12285]
\  00040      1 t literal     t = 1
\  00041    s t s add         s = t:1 + s:12285
\  00042    x z s fetch       x = M[z:0][s:12286]
\  00043    x x y add         x = x:42 + y:42
\  00044    z s x store       M[z:0][s:12286] = x:84
\  00045      8 x literal     x = 8
\  00046      z x loadjump    load(z:0), jump(x:8)
\  00008    w z i fetch       w = M[z:0][i:58]
\  00009      1 t literal     t = 1
\  00010    i t i add         i = t:1 + i:58
\  00011      z w loadjump    load(z:0), jump(w:12)
\  00012    i z r fetch       i = M[z:0][r:16382]
\  00013      1 t literal     t = 1
\  00014    r t r add         r = t:1 + r:16382
\  00015      8 x literal     x = 8
\  00016      z x loadjump    load(z:0), jump(x:8)
\  00008    w z i fetch       w = M[z:0][i:59]
\  00009      1 t literal     t = 1
\  00010    i t i add         i = t:1 + i:59
\  00011      z w loadjump    load(z:0), jump(w:47)
\  00047          halt
"

let rec repl () =
    out.Write "\n>"
    try
        inp <- new StringReader(Console.ReadLine() + Environment.NewLine)
        rep ()
        out.Write "ok"
        repl ()
    with ex -> out.Write ex.Message; repl ()

let case source expected =
    out <- new StringWriter()
    mem.[s] <- 61440
    source + Environment.NewLine |> reps
    let result = out.ToString()
    if result <> expected then
        printfn "FAILURE: %s (Expected: %s, Actual: %s)" source expected result

case "123 ." "123 " // literals
case "1 2 3 .S" "1 2 3 " // stack
case "5 6 + ." "11 " // addition
case "5 6 7 + + ." "18 " // addition
case "10 2 - ." "8 " // subtraction
case "10 2 - 3 - ." "5 " // subtraction
case "10 2 3 - - ." "11 " // subtraction
case "2 3 * ." "6 " // multiplication
case "2 3 4 * * ." "24 " // multiplication
case "5 2 / ." "2 " // division
case "5 2 MOD ." "1 " // modulo
case "1 2 3 DEPTH ." "3 " // stack depth
case "1 2 3 CLEAR DEPTH ." "0 " // depth of empty
case "1 2 3 CLEAR .S" "" // clear stack
case "1 2 3 4 3 PICK ." "1 " // pick
case "1 2 3 4  3 ROLL .S" "2 3 4 1 " // roll
case "1 2 3 DROP .S" "1 2 " // drop
case "1 2 3 DUP .S" "1 2 3 3 " // duplicate
case "1 2 3 SWAP .S" "1 3 2 " // swap
case "1 2 3 OVER .S" "1 2 3 2 " // over
case "1 2 3 ROT .S" "2 3 1 " // left rotate
case "1 2 3 -ROT .S" "3 1 2 " // right rotate
case "1 2 3 NIP .S" "1 3 " // drop 2nd
case "1 2 3 TUCK .S" "1 3 2 3 " // bury to 2nd
case "7 NEGATE ." "-7 " // negate positive
case "-7 NEGATE ." "7 " // negate negative
case "5 SQUARE ." "25 " // square
case "5 CUBE ." "125 " // cubed
case "22 4 /MOD . ." "5 2 " // quotient and remainder
case "7 \ comment\n 8 .S" "7 8 " // comment skipped
case "7 ( comment ) 8 .S" "7 8 " // comment skipped
case "1 2 3 2DROP .S" "1 " // drop pair
case "1 2 3 2DUP .S" "1 2 3 2 3 " // dup pair
case "1 2 3 4 2OVER .S" "1 2 3 4 1 2 " // over pairs
case "1 2 3 3DUP .S" "1 2 3 1 2 3 " // dup tripple
case "42 1+ ." "43 " // increment
case "42 1- ." "41 " // decrement
case "42 2+ ." "44 " // double inc
case "42 2- ." "40 " // double dec
case "42 2* ." "84 " // left shift
case "42 2/ ." "21 " // right shift
case "TRUE ." "-1 " // true constant
case "FALSE ." "0 " // false constant
case "0 0 NAND ." "-1 " // nand
case "0 -1 NAND ." "-1 " // nand
case "-1 0 NAND ." "-1 " // nand
case "-1 -1 NAND ." "0 " // nand
case "0 NOT ." "-1 " // not
case "-1 NOT ." "0 " // not
case "0 0 AND ." "0 " // and
case "0 -1 AND ." "0 " // and
case "-1 0 AND ." "0 " // and
case "-1 -1 AND ." "-1 " // and
case "0 0 OR ." "0 " // or
case "0 -1 OR ." "-1 " // or
case "-1 0 OR ." "-1 " // or
case "-1 -1 OR ." "-1 " // or
case "0 0 NOR ." "-1 " // nor
case "0 -1 NOR ." "0 " // nor
case "-1 0 NOR ." "0 " // nor
case "-1 -1 NOR ." "0 " // nor
case "0 0 XOR ." "0 " // xor
case "0 -1 XOR ." "-1 " // xor
case "-1 0 XOR ." "-1 " // xor
case "-1 -1 XOR ." "0 " // xor
case "0 0 XNOR ." "-1 " // xnor
case "0 -1 XNOR ." "0 " // xnor
case "-1 0 XNOR ." "0 " // xnor
case "-1 -1 XNOR ." "-1 " // xnor
case "42 6 > ." "-1 " // greater
case "6 42 > ." "0 " // greater
case "6 6 > ." "0 " // greater
case "6 42 = ." "0 " // equal
case "6 6 = ." "-1 " // equal
case "42 6 >= ." "-1 " // greater or equal
case "6 42 >= ." "0 " // greater or equal
case "6 6 >= ." "-1 " // greater or equal
case "42 6 < ." "0 " // less
case "6 42 < ." "-1 " // less
case "6 6 < ." "0 " // less
case "42 6 <= ." "0 " // less or equal
case "6 42 <= ." "-1 " // less or equal
case "6 6 <= ." "-1 " // less or equal
case "42 6 <> ." "-1 " // not equal
case "6 42 <> ." "-1 " // not equal
case "6 6 <> ." "0 " // not equal
case "-1 0> ." "0 " // greater than zero
case "0 0> ." "0 " // greater than zero
case "1 0> ." "-1 " // greater than zero
case "42 0= ." "0 " // equal to zero
case "0 0= ." "-1 " // equal to zero
case "-1 0< ." "-1 " // less than zero
case "0 0< ." "0 " // less than zero
case "1 0< ." "0 " // less than zero
case "0 0<> ." "0 " // not equal to zero
case "42 0<> ." "-1 " // not equal to zero
case "VARIABLE X  42 X !  X @ .  X ?  FORGET X" "42 42 " // variables
case "VARIABLE Y  40 Y !  Y ?  2 Y +!  Y ?  FORGET Y" "40 42 " // add variable
case "HERE : FOO 123 ; FORGET FOO HERE = ." "-1 " // forgetting frees heap
case ": FOO IF 1 THEN 2 ; TRUE FOO .S FORGET FOO" "1 2 " // if true
case ": FOO IF 1 THEN 2 ; FALSE FOO .S FORGET FOO" "2 " // if false
case ": FOO IF 1 ELSE 2 THEN 3 ; TRUE FOO .S FORGET FOO" "1 3 " // if then
case ": FOO IF 1 ELSE 2 THEN 3 ; FALSE FOO .S FORGET FOO" "2 3 " // else then
case "7 ABS ." "7 " // absolute value (positive)
case "-7 ABS ." "7 " // absolute value (negative)
case "10 4 MIN ." "4 " // min
case "10 4 MAX ." "10 " // max
case "-10 4 MIN ." "-10 " // min
case "-10 4 MAX ." "4 " // max
case ": FOO 123 ; FOO . : FOO 456 ; FOO . FORGET FOO FOO . FORGET FOO" "123 456 123 " // redefinition and forgetting
case "1 2 3 .S >R >R >R R@ . R> . R> . R> ." "1 2 3 1 1 2 3 " // return stack operators
case ": FAC   DUP 1 > IF DUP 1- FAC * THEN ; 7 FAC . FORGET FAC" "5040 " // recursive definition
case ": QUADRATIC ( a b c x -- n)  >R SWAP ROT R@ *  + R> *  + ; 2 7 9 3 QUADRATIC . FORGET QUADRATIC" "48 " // taken from Starting Forth, Pg 100
case ": LOOPY BEGIN 1+ DUP . DUP 9 > UNTIL ; 0 LOOPY 5 LOOPY 100 LOOPY FORGET LOOPY" "1 2 3 4 5 6 7 8 9 10 6 7 8 9 10 101 " // BEGIN ... UNTIL
case ": LOOPY BEGIN DUP 10 < WHILE 1+ DUP . REPEAT ; 0 LOOPY 5 LOOPY 100 LOOPY FORGET LOOPY" "1 2 3 4 5 6 7 8 9 10 6 7 8 9 10 " // BEGIN ... WHILE ... UNTIL
case ": LOOPY BEGIN 1+ DUP 10 > IF LEAVE THEN DUP . REPEAT ; 0 LOOPY 5 LOOPY 100 LOOPY FORGET LOOPY" "1 2 3 4 5 6 7 8 9 10 6 7 8 9 10 " // BEGIN ... IF ... LEAVE ... THEN ... UNTIL
case ": DECADE   10 0 DO I . LOOP ; DECADE FORGET DECADE" "0 1 2 3 4 5 6 7 8 9 " // DO ... LOOP
case ": MULTIPLICATIONS 11 1 DO DUP I * . LOOP DROP ; 7 MULTIPLICATIONS FORGET MULTIPLICATIONS" "7 14 21 28 35 42 49 56 63 70 " // DO ... LOOP with stack work
case ": NESTED   3 1 DO 3 1 DO 3 1 DO I J K * * . LOOP LOOP LOOP ; NESTED FORGET NESTED" "1 2 2 4 2 4 4 8 " // nested DO ... LOOPs
case ": COUNTDOWN 0 100 DO I . -10 +LOOP ; COUNTDOWN FORGET COUNTDOWN" "100 90 80 70 60 50 40 30 20 10 " // +LOOP
case "65 65 ?DELIM .S CLEAR" "65 -1 " // ?DELIM match
case "66 65 ?DELIM .S CLEAR" "66 0 " // ?DELIM mismatch
case "32 32 ?DELIM .S CLEAR" "32 -1 " // ?DELIM space match
case "33 32 ?DELIM .S CLEAR" "33 0 " // ?DELIM space mismatch
case "9 32 ?DELIM .S CLEAR" "9 -1 " // ?DELIM whitespace match
case "10 32 ?DELIM .S CLEAR" "10 -1 " // ?DELIM whitespace match
case "13 32 ?DELIM .S CLEAR" "13 -1 " // ?DELIM whitespace match
case "47 ?DIGIT .S CLEAR" "47 0 " // not ?DIGIT
case "48 ?DIGIT .S CLEAR" "48 -1 " // is ?DIGIT
case "57 ?DIGIT .S CLEAR" "57 -1 " // is ?DIGIT
case "58 ?DIGIT .S CLEAR" "58 0 " // not ?DIGIT
case "4 HERE ! 48 HERE 1+ ! 49 HERE 2+ ! 50 HERE 3 + ! 51 HERE 4 + ! ?NUMBER .S CLEAR" "123 -1 " // PARSENUM
case "4 HERE ! 48 HERE 1+ ! 49 HERE 2+ ! 65 HERE 3 + ! 51 HERE 4 + ! ?NUMBER .S CLEAR" "0 " // PARSENUM

Console.Title <- "TransForth"
out <- Console.Out
out.Write "Welcome to TransForth"
repl ()
