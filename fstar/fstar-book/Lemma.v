From Stdlib Require Import Lists.List.

Notation "x :: l" := (cons x l)
                     (at level 60, right associativity).
Notation "[ ]" := nil.
Notation "[ x ; .. ; y ]" := (cons x .. (cons y nil) ..).
Notation "x ++ y" := (app x y)
                     (right associativity, at level 60).

Fixpoint reverse {a:Type} (l : list a) : list a :=
  match l with
  | [] => []
  | h :: t => (reverse t) ++ [h]
  end. 

Fixpoint rev_aux {a:Type} (l1 l2 : list a) : list a :=
  match l2 with
  | [] => l1
  | h :: t => rev_aux (h :: l1) t
  end.
  
Lemma rev_is_ok_aux : forall {a:Type} (l1 l2:list a),
  rev_aux l2 l1 = (reverse l1) ++ l2.

Proof.
  intros a.
  induction l1 as [| h l' IHl'].
  - intros l2. reflexivity.
  - intros l2. simpl. rewrite <- app_assoc. simpl.
    pose proof (IHl' (h :: l2)) as IHl2.
    apply IHl2.
Qed.    

Definition rev {a:Type} (l:list a) : list a :=
  rev_aux [] l.

Lemma rev_is_ok : forall {a:Type} (l:list a),
  rev l = reverse l.

Proof.
  intros a l.
  unfold rev.
  pose proof (rev_is_ok_aux l []).
  rewrite app_nil_r in H.
  apply H.
Qed.
