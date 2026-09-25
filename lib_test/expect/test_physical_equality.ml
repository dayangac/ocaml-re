module A = Re_private.Automata
module Ast = Re_private.Ast
module Category = Re_private.Category
module Cset = Re_private.Cset
module Pmark = Re_private.Pmark
module Re = Re_private.Re
module Import = Re_private.Import

let%expect_test "character-set equality and ordering with shared and copied tails" =
  let tail = Cset.set "cegikmoqsuwy" in
  let prefix () = Cset.add (Cset.of_char 'a') tail in
  let sets =
    [ Cset.empty
    ; tail
    ; Cset.offset 0 tail
    ; prefix ()
    ; prefix ()
    ; Cset.add (Cset.of_char 'b') tail
    ; Cset.set "acegikmoqsuwx"
    ; Cset.single (Cset.of_int 256)
    ]
  in
  let intervals t =
    Cset.fold_right t ~init:[] ~f:(fun a b rest -> (Cset.to_int a, Cset.to_int b) :: rest)
  in
  List.iter
    (fun x ->
       List.iter
         (fun y ->
            let expected = Stdlib.compare (intervals x) (intervals y) in
            assert (Cset.equal x y = (expected = 0));
            assert (Cset.compare x y = expected);
            if expected = 0 then assert (Cset.hash x = Cset.hash y))
         sets)
    sets;
  [%expect {| |}]
;;

let%expect_test "persistent-mark set equality is independent of sharing and tree shape" =
  let marks = List.init 32 (fun _ -> Pmark.gen ()) in
  let make marks =
    List.fold_left (fun set m -> Pmark.Set.add m set) Pmark.Set.empty marks
  in
  let set = make marks in
  let sets =
    [ Pmark.Set.empty
    ; set
    ; make marks
    ; make (List.rev marks)
    ; Pmark.Set.add (List.hd marks) set
    ; make (List.tl marks)
    ]
  in
  List.iter
    (fun x ->
       List.iter
         (fun y ->
            let expected = Stdlib.compare (Pmark.Set.elements x) (Pmark.Set.elements y) in
            assert (Pmark.Set.equal x y = (expected = 0));
            assert (Pmark.Set.compare x y = expected))
         sets)
    sets;
  [%expect {| |}]
;;

let%expect_test "state interning agrees for identical and recomputed derivatives" =
  let ids = A.Ids.create () in
  let a = A.cst ids (Cset.csingle 'a') in
  let mark = A.Mark.start in
  let pmark = Pmark.gen () in
  let captured =
    A.seq
      ids
      `First
      (A.mark ids mark)
      (A.seq
         ids
         `First
         (A.pmark ids pmark)
         (A.seq ids `First a (A.mark ids (A.Mark.next mark))))
  in
  let nested = A.seq ids `Longest (A.rep ids `Greedy `Longest a) captured in
  let run expr input =
    let wa = A.Working_area.create () in
    let state = ref (A.State.create Category.inexistant expr) in
    String.iter
      (fun c -> state := A.delta wa (Category.from_char c) (Cset.of_char c) !state)
      input;
    !state
  in
  List.iter
    (fun (expr, inputs) ->
       List.iter
         (fun input ->
            let state = run expr input in
            let copy = run expr input in
            let table = A.State.Table.create 1 in
            A.State.Table.add table state 42;
            assert (A.State.Table.find table state = 42);
            assert (A.State.Table.find table copy = 42);
            (* Populating only one status cache must not affect equality. *)
            ignore (A.State.status_no_mutex state);
            assert (A.State.Table.find table copy = 42))
         inputs)
    [ captured, [ ""; "a"; "a!"; "b" ]; nested, [ ""; "a"; "aa"; "aaa" ] ];
  [%expect {| |}]
;;

let%expect_test "generic comparisons still invoke non-reflexive callbacks" =
  let shared = [ 1; 2; 3 ] in
  assert (not (Import.List.equal ~eq:(fun _ _ -> false) shared shared));
  assert (Import.List.compare ~cmp:(fun _ _ -> 1) shared shared = 1);
  [%expect {| |}]
;;

let%expect_test "factoring must not identify even physically shared capture groups" =
  List.iter
    (fun wrap ->
       let prefix = wrap Re.(group (char 'a')) in
       let branch = Ast.handle_case false Re.(seq [ prefix; char 'b' ]) in
       assert (List.length (Ast.merge_sequences [ branch; branch ]) = 2);
       let re =
         Re.(compile (alt [ seq [ prefix; char 'x' ]; seq [ prefix; char 'y' ] ]))
       in
       let g = Re.exec re "ay" in
       assert (not (Re.Group.test g 1));
       assert (Re.Group.get g 2 = "a"))
    [ Fun.id
    ; Re.nest
    ; Re.first
    ; (fun x -> Re.alt [ x; Re.char 'c' ])
    ; (fun x -> Re.seq [ x; Re.epsilon ])
    ];
  [%expect {| |}]
;;
