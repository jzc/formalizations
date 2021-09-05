Variable f : bool -> bool.
Variable x : nat.

Fixpoint foo (n m : nat) :=
  match m with
  | 0 => true
  | S k => f (foo n k)
  end.

Fixpoint bar (n m : nat) :=
  match m with
  | 0 => true
  | S k => (fun _ => true) (bar n k)
  end.

Fixpoint quux (g : bool -> bool) (n m : nat) :=
  match m with
  | 0 => true
  | S k => g (quux g n k)
  end.

Compute foo x 0.
Compute bar x 0.
Compute quux f x 0.
Compute quux (fun _ => true) x 0.
Eval cbv delta iota in quux (fun _ => true) x 0. 
