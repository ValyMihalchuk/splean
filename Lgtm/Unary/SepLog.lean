-- import Ssreflect.Lang
import Mathlib.Data.Finmap
import Mathlib.Data.Finset.Basic
import Mathlib.Data.Multiset.Nodup

import Lgtm.Unary.Util
import Lgtm.Unary.HProp
import Lgtm.Unary.XSimp

open trm val prim

local instance : Coe val trm where
  coe v := trm.trm_val v

/- ================= Separation Logic Reasoning Rules ================= -/

/- -------------- Definition of Separation Logic Triples -------------- -/

abbrev triple (t : trm) (H : hProp) (Q : val → hProp) : Prop :=
  forall s, H s → eval s t Q

notation "funloc" p "↦" H =>
  fun (r : val) ↦ hexists (fun p ↦ ⌜r = val_loc p⌝ ∗ H)


/- ---------------- Structural Properties of [eval] ---------------- -/

section evalProp

set_option maxHeartbeats 2500000
/- Is there a good way to automate this? The current problem is that
   [constructor] does not always infer the correct evaluation rule to use.
   Since many of the rules involve a function application, using [constructor]
   often incorrectly applys eval_app_arg1, so we must instead manually apply
   the correct rule -/
lemma eval_conseq s t Q1 Q2 :
  eval s t Q1 →
  Q1 ===> Q2 →
  eval s t Q2 :=
by
  move=> heval
  srw (qimpl) (himpl)=> Imp
  elim: heval Q2
  { move=> * ; sby constructor }
  { move=> * ; sby constructor }
  { move=> * ; sby constructor }
  { move=> * ; sby constructor }
  { move=> * ; sby apply eval.eval_app_arg2 }
  { move=> * ; sby apply eval.eval_app_fun }
  { move=> * ; sby apply eval.eval_app_fix }
  { move=> * ; apply eval.eval_seq =>//
    move=> * ; aesop }
  { move=> * ; sby constructor }
  { move=> * ; sby constructor }
  { move=> * ; apply eval.eval_unop=>//
    sby srw (purepostin) at * }
  { move=> * ; apply eval.eval_binop=>//
    sby srw (purepostin) at * }
  { move=> * ; sby apply eval.eval_ref }
  { move=> * ; sby apply eval.eval_get }
  { move=> * ; sby apply eval.eval_set }
  { move=> * ; sby constructor }
  { move=> * ; sby apply eval.eval_alloc }
  { move=> * ; sby constructor }
  move=> * ; sby constructor

/- ========= Useful Lemmas about disjointness and state operations ========= -/

lemma disjoint_update_not_r (h1 h2 : state) (x : loc) (v: val) :
  Finmap.Disjoint h1 h2 →
  x ∉ h2 →
  Finmap.Disjoint (Finmap.insert x v h1) h2 :=
by
  srw Finmap.Disjoint => ??
  srw Finmap.Disjoint Finmap.mem_insert => ?
  sby scase

lemma in_read_union_l (h1 h2 : state) (x : loc) :
  x ∈ h1 → read_state x (h1 ∪ h2) = read_state x h1 :=
by
  move=> ?
  srw []read_state
  sby srw (Finmap.lookup_union_left)

lemma disjoint_insert_l (h1 h2 : state) (x : loc) (v : val) :
  Finmap.Disjoint h1 h2 →
  x ∈ h1 →
  Finmap.Disjoint (Finmap.insert x v h1) h2 :=
by
  srw Finmap.Disjoint => *
  srw Finmap.Disjoint Finmap.mem_insert => ?
  sby scase

lemma insert_disjoint_l (h1 h2 : state) (x : loc) (v : val) :
  h2.Disjoint (h1.insert x v) →
  x ∉ h2 ∧ h2.Disjoint h1 := by
  unfold Finmap.Disjoint=> hdis ⟨|⟩
  { sby unfold Not=> /hdis }
  sby move=> >

lemma remove_disjoint_union_l (h1 h2 : state) (x : loc) :
  x ∈ h1 → Finmap.Disjoint h1 h2 →
  Finmap.erase x (h1 ∪ h2) = Finmap.erase x h1 ∪ h2 :=
by
  srw Finmap.Disjoint => * ; apply Finmap.ext_lookup => y
  scase: [x = y]=> hEq
  { scase: [y ∈ Finmap.erase x h1]=> hErase
    { srw Finmap.lookup_union_right
      rw [Finmap.lookup_erase_ne]
      apply Finmap.lookup_union_right
      srw Finmap.mem_erase at hErase=>//
      srw Not at * => * //
      sby srw Not }
    srw Finmap.lookup_union_left
    sby sdo 2 rw [Finmap.lookup_erase_ne] }
  srw -hEq
  srw Finmap.lookup_union_right=>//
  srw Finmap.lookup_erase
  apply Eq.symm
  sby srw Finmap.lookup_eq_none

lemma remove_not_in_l (h1 h2 : state) (p : loc) :
  p ∉ h1 →
  (h1 ∪ h2).erase p = h1 ∪ h2.erase p := by
  move=> ?
  apply Finmap.ext_lookup=> >
  scase: [x = p]
  { move=> ?
    srw Finmap.lookup_erase_ne=> //
    scase: [x ∈ h1]
    { move=> ? ; sby srw ?Finmap.lookup_union_right }
    move=> ? ; sby srw ?Finmap.lookup_union_left }
  move=> ->
  sby srw Finmap.lookup_union_right

lemma remove_not_in_r (h1 h2 : state) (p : loc) :
  p ∉ h2 →
  (h1 ∪ h2).erase p = h1.erase p ∪ h2 := by
  move=> ?
  apply Finmap.ext_lookup=> >
  scase: [x = p]
  { move=> ?
    srw Finmap.lookup_erase_ne=> //
    scase: [x ∈ h1]
    { move=> ? ; sby srw ?Finmap.lookup_union_right }
    move=> ? ; sby srw ?Finmap.lookup_union_left }
  move=> ->
  sby srw Finmap.lookup_union_left_of_not_in

lemma disjoint_remove_l (h1 h2 : state) (x : loc) :
  Finmap.Disjoint h1 h2 →
  Finmap.Disjoint (Finmap.erase x h1) h2 :=
by
  srw Finmap.Disjoint=> ??
  sby srw Finmap.mem_erase

lemma erase_disjoint (h1 h2 : state) (p : loc) :
  h1.Disjoint h2 →
  (h1.erase p).Disjoint h2 := by
  sby unfold Finmap.Disjoint=> ?? > /Finmap.mem_erase

lemma disjoint_single (h : state) :
  p ∉ h →
  h.Disjoint (Finmap.singleton p v) := by
  move=> ?
  unfold Finmap.Disjoint=> > ?
  sby scase: [x = p]

lemma insert_union (h1 h2 : state) (p : loc) (v : val) :
  p ∉ h1 ∪ h2 →
  (h1 ∪ h2).insert p v = (h1.insert p v) ∪ h2 := by
  move=> ?
  apply Finmap.ext_lookup=> >
  scase: [x = p]=> ?
  { srw Finmap.lookup_insert_of_ne=> //
    scase: [x ∈ h1]=> ?
    { sby srw ?Finmap.lookup_union_right }
    sby srw ?Finmap.lookup_union_left }
  sby subst x

lemma insert_mem_keys (s : state) :
  p ∈ s →
  (s.insert p v).keys = s.keys := by
  move=> ?
  apply Finset.ext=> >
  sby srw ?Finmap.mem_keys

lemma non_mem_union (h1 h2 : state) :
  a ∉ h1 ∪ h2 → a ∉ h1 ∧ a ∉ h2 := by sdone

lemma insert_delete_id (h : state) (p : loc) :
  p ∉ h →
  h = (h.insert p v).erase p := by
  move=> hin
  apply Finmap.ext_lookup=> >
  scase: [x = p]=> ?
  { sby srw Finmap.lookup_erase_ne }
  subst x
  move: hin=> /Finmap.lookup_eq_none ?
  sby srw Finmap.lookup_erase

lemma insert_same (h1 h2 : state) :
  p ∉ h1 → p ∉ h2 →
  (h1.insert p v).keys = (h2.insert p v').keys →
  h1.keys = h2.keys := by
  move=> ?? /Finset.ext_iff
  srw Finmap.mem_keys Finmap.mem_insert=> hin
  apply Finset.ext=> > ; srw ?Finmap.mem_keys
  scase: [a = p]=> ?
  { apply Iff.intro
    sdo 2 (sby move=> /(Or.intro_right (a = p)) /hin []) }
  sby subst a

lemma insert_same_eq (h1 h2 : state) :
  p ∉ h1 → p ∉ h2 →
  h1.insert p v = h2.insert p v →
  h1 = h2 := by
  move=> /Finmap.lookup_eq_none ? /Finmap.lookup_eq_none ? *
  apply Finmap.ext_lookup=> >
  scase: [x = p]
  { move=> /Finmap.lookup_insert_of_ne hlook
    sby srw -(hlook _ v h1) -(hlook _ v h2) }
  sby move=> []

lemma union_same_keys (h₁ h₂ h₃ : state) :
  h₁.Disjoint h₃ → h₂.Disjoint h₃ →
  (h₁ ∪ h₃).keys = (h₂ ∪ h₃).keys →
  h₁.keys = h₂.keys := by
  unfold Finmap.Disjoint
  move=> ?? /Finset.ext_iff
  srw Finmap.mem_keys Finmap.mem_union=> hin
  apply Finset.ext=> > ; srw ?Finmap.mem_keys
  apply Iff.intro
  sdo 2 (sby move=> /[dup] ? /(Or.intro_left (a ∈ h₃)) /hin [])

lemma insert_eq_union_single (h : state) :
  p ∉ h →
  h.insert p v = h ∪ (Finmap.singleton p v) := by
  move=> ?
  apply Finmap.ext_lookup=> >
  scase: [x = p]
  { move=> ?
    srw Finmap.lookup_insert_of_ne=> //
    sby srw Finmap.lookup_union_left_of_not_in }
  sby move=> []

lemma keys_eq_not_mem_r (h1 h2 : state) :
  h1.keys = h2.keys →
  p ∉ h2 →
  p ∉ h1 := by
  move=> /Finset.ext_iff
  sby srw Finmap.mem_keys

lemma keys_eq_not_mem_l (h1 h2 : state) :
  h1.keys = h2.keys →
  p ∉ h1 →
  p ∉ h2 := by
  move=> /Finset.ext_iff
  sby srw Finmap.mem_keys

lemma keys_eq_mem_r (h1 h2 : state) :
  h1.keys = h2.keys →
  p ∈ h2 →
  p ∈ h1 := by
  move=> /Finset.ext_iff
  sby srw Finmap.mem_keys

lemma state_eq_not_mem (p : loc) (h1 h2 : state) :
  h1 = h2 →
  p ∉ h1 →
  p ∉ h2 := by sdone

lemma erase_of_non_mem (h : state) :
  p ∉ h →
  h.erase p = h := by
  move=> /Finmap.lookup_eq_none ?
  apply Finmap.ext_lookup=> >
  scase: [x = p]
  { move=> /Finmap.lookup_erase_ne Hlook
    srw Hlook }
  move=> []
  sby srw Finmap.lookup_erase

lemma insert_neq_of_non_mem (h : state) :
  x ∉ h →
  x ≠ p →
  x ∉ h.insert p v := by
  move=> * ; unfold Not
  sby move=> /Finmap.mem_insert

lemma reinsert_erase_union (h1 h2 h3 : state) :
  h3.lookup p = some v →
  p ∉ h2 →
  h3.erase p = h1 ∪ h2 →
  h3 = (h1.insert p v) ∪ h2 := by
  move=> ?? heq
  apply Finmap.ext_lookup=> >
  scase: [x = p]
  { move=> /[dup] /Finmap.lookup_erase_ne hlook
    srw -hlook {hlook} heq
    scase: [x ∈ h1]
    { sby move=> * ; srw ?Finmap.lookup_union_right }
    move=> * ; sby srw ?Finmap.lookup_union_left }
  move=> []
  sby srw Finmap.lookup_union_left

lemma union_singleton_eq_erase (h h' : state) :
  h.Disjoint (Finmap.singleton p v) →
  h' = h ∪ Finmap.singleton p v →
  h = h'.erase p := by
  move=> hdisj []
  apply Finmap.ext_lookup=> >
  scase: [x = p]
  { move=> ?
    srw Finmap.lookup_erase_ne=> //
    sby srw Finmap.lookup_union_left_of_not_in }
  move=> []
  srw Finmap.lookup_erase
  srw Finmap.lookup_eq_none
  sby move: hdisj ; unfold Finmap.Disjoint Not=> /[apply]

lemma disjoint_keys (h₁ h₂ : state) :
  h₁.Disjoint h₂ →
  Disjoint h₁.keys h₂.keys := by
  unfold Finmap.Disjoint
  srw -Finmap.mem_keys Finset.disjoint_iff_ne
  move=> hFmap > /hFmap ? > hb
  sby srw Not

lemma non_mem_diff_helper1 (h₁ : state) (l : @AList loc fun _ ↦ val) :
  a ∉ l →
  p ∈ List.foldl (fun d s ↦ Finmap.erase s.fst d) (Finmap.erase a h₁) l.entries →
  p ≠ a := by
  elim: l h₁=> //
  move=> > ? ih > /== ??
  srw Finmap.erase_erase
  srw List.kerase_of_not_mem_keys=> // ?
  sby apply ih

lemma non_mem_diff_helper2 (h₁ : state) (l : @AList loc fun _ ↦ val) :
  p ∈ List.foldl (fun d s ↦ Finmap.erase s.fst d) (Finmap.erase a h₁) l.entries →
  p ∈ List.foldl (fun d s ↦ Finmap.erase s.fst d) h₁ l.entries := by
  elim: l h₁=> //
  move=> > ? ih >
  srw AList.insert_entries List.foldl_cons=> /=
  srw List.kerase_of_not_mem_keys=> // ?
  apply ih
  sby srw Finmap.erase_erase

theorem mem_diff_r (h₁ h₂ : state) :
  p ∈ h₁ \ h₂ → p ∉ h₂ := by
  refine Finmap.induction_on h₂ ?
  move=> >
  unfold Finmap.instSDiff Finmap.sdiff Finmap.foldl=> /==
  elim: a
  { sdone }
  move=> > ih1 ih2
  srw AList.insert_entries List.foldl_cons=> /=
  srw List.kerase_of_not_mem_keys=> //== ? ⟨|⟩
  { sby apply non_mem_diff_helper1 }
  apply ih2
  sby apply non_mem_diff_helper2

lemma mem_erase_right (s : state) :
  p ∈ s.erase x → p ∈ s := by
  sby move=> /Finmap.mem_erase

lemma list_foldl_erase_mem (h₁ : state) (l : @AList loc fun _ ↦ val) :
  p ∈ List.foldl (fun d s ↦ Finmap.erase s.fst d) h₁ l.entries → p ∈  h₁ := by
  elim: l h₁=> //
  move=> > ? ih /=
  srw List.kerase_of_not_mem_keys=> // > /ih
  sby srw Finmap.mem_erase

lemma mem_diff_helper (h₁ : state) (l : @AList loc fun _ ↦ val) :
  a ∉ l →
  (p ∈ List.foldl (fun d s ↦ Finmap.erase s.fst d) h₁ l.entries → p ∈ h₁) →
  p ∈ List.foldl (fun d s ↦ Finmap.erase s.fst d) (Finmap.erase a h₁) l.entries →
  p ∈ h₁ := by
  elim: l h₁=> >
  { sdone }
  move=> ? ih > /== ?
  srw List.kerase_of_not_mem_keys=> //
  srw Finmap.erase_erase=> ???
  apply (@mem_erase_right p a_1 h₁)
  sby apply ih=> // /list_foldl_erase_mem

theorem mem_diff_l (h₁ h₂ : state) :
  p ∈ h₁ \ h₂ → p ∈ h₁ := by
  refine Finmap.induction_on h₂ ? _
  move=> >
  unfold Finmap.instSDiff Finmap.sdiff Finmap.foldl=> /=
  elim: a=> > //
  move=> ? ih
  srw AList.insert_entries List.foldl_cons=> /=
  srw List.kerase_of_not_mem_keys=> //
  sby apply mem_diff_helper

lemma mem_diff_rev_helper (h₁ : state) (l : @AList loc fun _ ↦ val) :
  a ∉ l →
  (p ∈ h₁ ∧ p ∉ l.toFinmap → p ∈ List.foldl (fun d s ↦ Finmap.erase s.fst d) h₁ l.entries) →
  p ∈ h₁ ∧ p ∉ (AList.insert a b l).toFinmap →
  p ∈ List.foldl (fun d s ↦ Finmap.erase s.fst d) (Finmap.erase a h₁) l.entries := by
  elim: l h₁=> >
  { move=> ? /== _ ?
    unfold Not=> hsing ⟨| // ⟩
    move=> []
    apply hsing
    sby srw AList.mem_keys AList.keys_singleton }
  move=> ? ih > ? /=
  srw List.kerase_of_not_mem_keys=> // ?
  srw Finmap.erase_erase=> ?
  sby apply ih

theorem mem_diff_rev (h₁ h₂ : state) :
  p ∈ h₁ ∧ p ∉ h₂ → p ∈ h₁ \ h₂ := by
  refine Finmap.induction_on h₂ ? _
  move=> >
  unfold Finmap.instSDiff Finmap.sdiff Finmap.foldl=> /=
  elim: a=> > //
  move=> ? ih /=
  srw List.kerase_of_not_mem_keys=> // ?
  sby apply mem_diff_rev_helper

/- Main theorem about set difference for Finmaps -/
@[simp]
theorem mem_diff_iff (h₁ h₂ : state) :
  p ∈ h₁ \ h₂ ↔ p ∈ h₁ ∧ p ∉ h₂ := by
  apply Iff.intro
  { sby move=> /[dup] /mem_diff_l ? /mem_diff_r }
  apply mem_diff_rev

theorem diff_non_mem (h₁ h₂ : state) :
  p ∈ h₂ → p ∉ h₁ \ h₂ := by sdone

lemma union_difference_id (h₁ h₂ : state) :
  h₁.Disjoint h₂ →
  (h₁ ∪ h₂) \ h₂ = h₁ := by
  refine Finmap.induction_on h₂ ? _
  move=> >
  unfold Finmap.instSDiff Finmap.sdiff Finmap.foldl=> /=
  elim: a=> > //== ?
  srw List.kerase_of_not_mem_keys=> // ih
  srw -Finmap.insert_toFinmap=> /insert_disjoint_l ?
  srw remove_not_in_l=> //
  sby srw -insert_delete_id

lemma diff_disjoint (h₁ h₂ : state) :
  h₂.Disjoint (h₁ \ h₂) := by sdone

lemma disjoint_disjoint_diff (h₁ h₂ h₃ : state) :
  h₁.Disjoint h₂ →
  (h₁ \ h₃).Disjoint h₂ := by
  sby unfold Finmap.Disjoint

lemma lookup_diff (h₁ h₂ : state) :
  p ∉ h₂ →
  (h₁ \ h₂).lookup p = h₁.lookup p := by
  refine Finmap.induction_on h₂ ? _
  move=> >
  unfold Finmap.instSDiff Finmap.sdiff Finmap.foldl=> /==
  elim: a h₁=> > //
  move=> ? ih > /=
  sby srw List.kerase_of_not_mem_keys

lemma lookup_diff_none (h₁ h₂ : state) :
  p ∈ h₂ →
  (h₁ \ h₂).lookup p = none := by
  sby move=> /(diff_non_mem h₁) /Finmap.lookup_eq_none

lemma union_diff_disjoint_r (h₁ h₂ h₃ : state) :
  h₂.Disjoint h₃ →
  (h₁ ∪ h₂) \ h₃ = (h₁ \ h₃) ∪ h₂ := by
  unfold Finmap.Disjoint=> hdis
  apply Finmap.ext_lookup=> >
  scase: [x ∈ h₃]
  { move=> ?
    scase: [x ∈ h₁]
    { move=> ? ; sby srw lookup_diff }
    move=> ? ; srw Finmap.lookup_union_left=> //
    sby srw ?lookup_diff }
  move=> ?
  scase: [x ∈ h₂]
  { move=> ? ; srw Finmap.lookup_union_left_of_not_in=> //
    sby srw ?lookup_diff_none }
  sby move=> /hdis

  lemma intersect_comm (s2 d : state) (a₁ : loc) (b₁ : val) (a₂ : loc) (b₂ : val) :
  (fun s x _ ↦ if x ∈ s2 then s else Finmap.erase x s)
      ((fun s x _ ↦ if x ∈ s2 then s else Finmap.erase x s) d a₁ b₁) a₂ b₂ =
    (fun s x _ ↦ if x ∈ s2 then s else Finmap.erase x s)
      ((fun s x _ ↦ if x ∈ s2 then s else Finmap.erase x s) d a₂ b₂) a₁ b₁ := by
  dsimp
  scase: [a₁ ∈ s2]=> > /=
  scase: [a₂ ∈ s2]=> > /=
  apply Finmap.erase_erase

def intersect (s1 s2 : state) :=
  s1.foldl (fun s x _ ↦ if x ∈ s2 then s else s.erase x) (intersect_comm s2) s1

def st1 : state := (Finmap.singleton 0 1).insert 1 1
def st2 : state := ((Finmap.singleton 0 2).insert 2 2).insert 1 2
#reduce intersect st1 st2

lemma insert_eq_union_singleton (s : state) :
  p ∉ s →
  s.insert p v = Finmap.singleton p v ∪ s := by
  move=> ?
  apply Finmap.ext_lookup=> >
  scase: [x = p]
  { move=> ?
    sby srw Finmap.lookup_insert_of_ne }
  move=> ->
  sby srw Finmap.lookup_insert Finmap.lookup_union_left_of_not_in

lemma AList_erase_entries (l : @AList loc (fun _ ↦ val)) :
  (l.erase p).entries = (l.entries).kerase p := by sdone

lemma Alist_insert_delete_id (l : @AList loc (fun _ ↦ val)) :
  p ∉ l →
  (l.insert p v).erase p = l := by
  move=> ?
  elim: l p v=> > /==
  { move=> >
    apply AList.ext=> /=
    sby srw AList_erase_entries }
  move=> ? ? > ??>
  apply AList.ext=> /==
  srw AList_erase_entries=> /==
  sby srw List.kerase_of_not_mem_keys

lemma intersect_foldl_mem (s₂ : state) (l₁ l₂ : @AList loc fun _ ↦ val):
  p ∈ List.foldl (fun d s ↦ if s.fst ∈ s₂ then d else Finmap.erase s.fst d)
    l₁.toFinmap l₂.entries →
  p ∈ l₁ := by
  elim: l₂ l₁=> > //
  move=> ? ih /==
  srw List.kerase_of_not_mem_keys=> // >
  sby scase_if=> // ? /ih

lemma intersect_mem_l (s₁ s₂ : state) :
  p ∈ (intersect s₁ s₂) → p ∈ s₁ := by
  refine Finmap.induction_on s₁ ? _
  move=> >
  unfold intersect Finmap.foldl=> /==
  elim: a=> //=
  move=> > ? ih
  srw List.kerase_of_not_mem_keys=> //
  scase_if=> ? /==
  { sby move=> /intersect_foldl_mem }
  sby srw Alist_insert_delete_id

lemma intersect_mem_r_helper (s₂ : state) (l : @AList loc fun _ ↦ val) :
  (p ∈ List.foldl (fun d s ↦ if s.fst ∈ s₂ then d else Finmap.erase s.fst d)
    l.toFinmap l.entries → p ∈ s₂) →
  a ∈ s₂ →
  p ∈ List.foldl (fun d s ↦ if s.fst ∈ s₂ then d else Finmap.erase s.fst d)
    (AList.insert a b l).toFinmap l.entries →
  p ∈ s₂ := by
  elim: l=> > /==
  { sby move=> _ ? /AList.mem_keys }
  move=> ? ih1 >
  srw List.kerase_of_not_mem_keys=> //
  move=> ih2 ?
  sorry

lemma intersect_foldl_mem_s2 (s₂ : state) (l₁ : @AList loc fun _ ↦ val) :
  p ∈ List.foldl (fun d s ↦ if s.fst ∈ s₂ then d else Finmap.erase s.fst d)
    l₁.toFinmap l₁.entries →
  p ∈ s₂ := by
  elim: l₁=> // >
  move=> ? ih /==
  srw Alist_insert_delete_id=> //
  srw List.kerase_of_not_mem_keys=> //
  scase_if=> ? //
  sorry

lemma intersect_mem_r (s₁ s₂ : state) :
  p ∈ (intersect s₁ s₂) → p ∈ s₂  := by
  refine Finmap.induction_on s₁ ? _
  move=> >
  unfold intersect Finmap.foldl=> /=
  elim: a=> > //=
  move=> ? ih
  srw List.kerase_of_not_mem_keys=> //==
  srw Alist_insert_delete_id=> //
  scase_if=> //
  move: ih=> /== /intersect_mem_r_helper ih
  specialize (ih a b)
  sby move=> /ih

lemma mem_intersect :
  p ∈ s₁ ∧ p ∈ s₂ → p ∈ (intersect s₁ s₂) := by
  refine Finmap.induction_on s₁ ? _
  move=> >
  unfold intersect Finmap.foldl=> /==
  elim: a=> > //? ih ? /==
  move=> ?
  srw Alist_insert_delete_id=> //
  sorry

@[simp]
lemma intersect_mem_iff (s₁ s₂ : state) :
  p ∈ (intersect s₁ s₂) ↔ p ∈ s₁ ∧ p ∈ s₂ := by
  apply Iff.intro
  { sby move=> /[dup] /intersect_mem_l ? /intersect_mem_r }
  apply mem_intersect

lemma lookup_intersect (s₁ s₂ : state) :
  p ∈ s₁ ∧ p ∈ s₂ →
  (intersect s₁ s₂).lookup p = s₁.lookup p := by
  move=> ?
  refine Finmap.induction_on s₁ ? _
  move=> >
  unfold intersect Finmap.foldl=> /==
  elim: a=> > //
  move=> ? ih /==
  scase_if=> ? ; srw List.kerase_of_not_mem_keys=> //
  { sorry }
  srw Alist_insert_delete_id=> //
  sorry

lemma diff_insert_intersect_id (s₁ s₂ : state) :
  (s₁ \ s₂) ∪ (intersect s₁ s₂) = s₁ := by
  apply Finmap.ext_lookup=> >
  scase: [x ∈ s₁]
  { move=> /[dup] ? /Finmap.lookup_eq_none ->
    srw Finmap.lookup_union_right=> //
    have eqn:(x ∉ intersect s₁ s₂) := by sdone
    sby move: eqn=> /Finmap.lookup_eq_none }
  move=> ?
  scase: [x ∈ s₂]=> ?
  { srw Finmap.lookup_union_left=> //
    sby srw lookup_diff }
  srw Finmap.lookup_union_right=> //
  sby srw lookup_intersect

lemma union_monotone_r (s₃ s₁ s₂ : state) :
  s₁ = s₂ →
  s₁ ∪ s₃ = s₂ ∪ s₃ := by sdone

lemma disjoint_intersect_r (s₁ s₂ s₃ : state) :
  s₂.Disjoint s₃ →
  (intersect s₁ s₂).Disjoint s₃ := by
  sby unfold Finmap.Disjoint

lemma intersect_disjoint_cancel (s₁ s₂ s₃ : state) :
  s₁.Disjoint s₃ →
  (s₁ ∪ intersect s₂ s₃) \ s₃ = s₁ := by
  unfold Finmap.Disjoint=> hdis
  apply Finmap.ext_lookup=> >
  scase: [x ∈ s₁]
  { move=> /[dup] ? /Finmap.lookup_eq_none ->
    scase: [x ∈ s₃]
    { move=> ?
      srw lookup_diff=> //
      srw Finmap.lookup_union_right=> //
      sby srw Finmap.lookup_eq_none }
    sby move=> /lookup_diff_none }
  move=> /[dup] ? /hdis ?
  sby srw lookup_diff


/- ============== Necessary Lemmas about [eval] and [evalExact] ============== -/

lemma finite_state (s : state) :
  ∃ p, p ∉ s := by
  scase: [s.keys.Nonempty]
  { srw Finset.nonempty_iff_ne_empty=> /== ?
    exists 0 ; unfold Not
    sby srw -Finmap.mem_keys }
  move=> /Finset.max_of_nonempty [>]
  have eqn:(w < w + 1) := by sdone
  move: eqn=> /Finset.not_mem_of_max_lt /[apply] ?
  exists (w + 1)

lemma conseq_ind (n : ℕ) (v : val) (p : loc) :
  x ∈ conseq (make_list n v) p → x ≥ p := by
  elim: n p=> > //
  move=> ih >
  unfold conseq make_list=> /== [] //
  move=> /ih ; omega

lemma finite_state' n (s : state) :
  ∃ p, p ≠ null ∧
    Finmap.Disjoint s (conseq (make_list n val_uninit) p) := by
  scase: [s.keys.Nonempty]
  { srw Finset.nonempty_iff_ne_empty=> /== ?
    exists 1 ; unfold null Finmap.Disjoint=> /== >
    sby srw -Finmap.mem_keys }
  move=> /Finset.max_of_nonempty [>] hmax
  exists (w + 1)=> ⟨|⟩
  { sby unfold null }
  unfold Finmap.Disjoint=> >
  move: hmax=> /[swap]
  srw -Finmap.mem_keys=> /Finset.le_max_of_eq /[apply] ?
  unfold Not=> /conseq_ind /==
  sby srw Nat.lt_succ_iff

lemma eval_sat :
  eval h t Q -> ∃ h v, Q h v := by
  elim=> // >
  { move=> ??? ![>?]; sapply=> // }
  { move=> ??? ![>?]; sapply=> // }
  { move=> ?? ![>?]; sapply=> // }
  { move=> ?? ![>?]; sapply=> // }
  { scase=> >
    any_goals move=> pp; (sdo 2 econstructor); apply pp=> //
    move=> ? pp; sdo 2 econstructor; apply pp=> //}
  { scase=> >
    any_goals move=> pp; (sdo 2 econstructor); apply pp=> //
    any_goals move=> ? pp; (sdo 2 econstructor); apply pp=> // }
  { move=> ?? ![>] /[swap] /[apply]
    scase: (finite_state w_1)=> p hp
    sby move: hp=> /[swap] /[apply] ![>] }
  { sby move=> ?? ![>] /[swap] /[apply] }
  { move=> ?? /== ih
    scase: (finite_state' n.natAbs sa)
    sby move=> p [] /ih /[apply] ![>] }
  move=> ? /[swap]![>] /[swap] _ /[swap]/[apply]//

lemma evalExact_sat :
  evalExact s t Q → ∃ v s, Q v s := by
  elim=> > //
  { move=> _ _ _ ![] > /[swap] ; sapply }
  { move=> _ _ _ ![] > /[swap] ; sapply }
  { move=> _ _ ![] > /[swap] ; sapply }
  { move=> _ _ ![] > /[swap] ; sapply }
  { sby move=> [] }
  { sby move=> [] }
  { move=> ?? ![>] /[swap] /[apply]
    scase: (finite_state w_1)=> p hp
    sby move: hp=> /[swap] /[apply] ![>] }
  { sby move=> _ _ _ ![>] /[swap] /[apply] }
  { move=> ? _ /== ih
    scase: (finite_state' n.natAbs sa)
    sby move=> p [] /ih /[apply] ![>] }
  move=> ? /[swap]![>] /[swap] _ /[swap]/[apply]//

lemma evalExact_post :
  eval s t Q → evalExact s t Q' → Q' ===> Q:= by
  move=> H
  elim: H Q'=> >
  -- elim=> >
  { sby move=> ? > [] v h /== }
  { sby move=> ? > [] v h /== }
  { sby move=> ? > [] v h /== }
  { move=> ??? ih1 ih2 > [] // >
    { move=> > _ /[dup] h h'
      apply evalExact_sat in h=> ![] v s' /[dup] hQ1_1 hQ1_1'
      apply ih1 in h'=> himp hev
      apply himp in hQ1_1
      sby apply hev in hQ1_1'=> ? /ih2 }
    { move=> ?
      scase: op=> > ? //
      scase: a=> > ? // [] // }
    move=> ? [] // }
  { move=> ? _ _ ih1 ih2 > [] // > _ /[dup] h h'
    apply evalExact_sat in h=> ![] v s' /[dup] hQ1_1 hQ1_1'
    apply ih1 in h'=> himp hev
    apply himp in hQ1_1
    sby apply hev in hQ1_1'=> ? /ih2 }
  { sby move=> [] ?? > [] }
  { sby move=> [] ?? > [] }
  { move=> _ _ ih1 ih2 > [] > /[dup] h h'
    apply evalExact_sat in h=> ![] v s' > /[dup] hQ1_1 hQ1_1' hev
    apply ih1 in h'=> himp
    apply himp in hQ1_1
    sby apply hev in hQ1_1'=> ? /ih2 }
  { move=> _ _ ih1 ih2 > [] > /[dup] h /evalExact_sat ![] v s'
    move=> /[dup] hQ1_1 hQ1_1' hev
    apply ih1 in h=> himp
    apply himp in hQ1_1
    sby apply hev in hQ1_1'=> ? /ih2 }
  { sby move=> _ ih > [] }
  { unfold purepostin=> hOP ? > [] //
    apply evalunop_unique in hOP=> hP
    move=> > /hP []
    sby unfold purepost=> ?? }
  { unfold purepostin=> hOP ? > [] //
    { scase: op=> > //
      scase: a=> > // ? > ? [] // }
    apply evalbinop_unique in hOP=> hP
    move=> > /hP []
    sby unfold purepost=> ?? }
  { move=> ?? ih1 ih2 > [Q₁'] hevEx hev
    move=> > h
    move: hevEx hev
    move=> /[dup] /ih1 {} ih1 /evalExact_sat ![>] /[dup] /ih1 {}ih1
    move=> /[swap] /[apply]
    scase: (finite_state (h ∪ w_1))=> p /non_mem_union [] ? hp
    move: hp=> /[dup] hp /[swap] /[apply]
    move: ih1 hp=> /ih2 /[apply] {}ih2
    specialize (@ih2 fun v (s : state) ↦ Q' v (s.erase p))
    move: ih2=> /[apply]
    unfold qimpl himpl=> /== ?
    sby srw (insert_delete_id h p) }
  { sby move=> ?? > [] // _ ?? }
  { move=> [] ?? > [] //
    { move=> > ? [] // }
    sby move=> > _ [] ?? }
  { move=> _ _ ih1 ih2 > []
    { move=> Q₁' ? /[dup] /ih1 {}ih1 /evalExact_sat ![>] /[dup] /ih1 {} ih1
      move=> /[swap] /[apply]
      sby move: ih1=> /ih2 }
    move=> > ih1 ?
    have eqn:(evalExact s_1 n fun v s ↦ v = n ∧ s = s_1) := by constructor
    move: eqn=> /[dup] /ih1 {}ih1 /evalExact_sat [>] [>] /[dup] /ih1 /ih2 {}ih2
    move=> [] [] [] ?
    apply ih2
    sby apply evalExact.alloc }
  { move=> ? _ /== ih > hev
    move=> > h
    move: hev=> [] // _ /== hev
    scase: (finite_state' n.natAbs (sa ∪ h))
    move=> p [] /[dup] /ih {}ih /hev {}hev /Finmap.disjoint_union_left []
    move=> /[dup] /hev /[swap] /ih {}ih {hev} /ih {}ih /union_difference_id <-
    sby move=> /ih }
  { sby move=> ?? > [] }
  { move=> ?? ih1 ih2 > [] Q₁'
    move=> /[dup] /ih1 {}ih1 /evalExact_sat ![>] /[dup] /ih1 {}ih1
    move=> /[swap] /[apply]
    sby move: ih1=> /ih2 }

lemma evalExact_WellAlloc :
  evalExact s t Q →
  Q v s' →
  s'.keys = s.keys := by
  move=> hev
  elim: hev s' v
  { sby move=> > [] }
  { sby move=> > [] }
  { sby move=> > [] }
  { move=> > _ /evalExact_sat ![>] /[dup] hQ1 /[swap] _ /[swap] /[apply] heq
    move: hQ1=> /[swap] /[apply] /[apply]
    sby srw heq=> {}heq > /heq }
  { move=> > _ /evalExact_sat ![>] /[dup] hQ1 /[swap] _ /[swap] /[apply] heq
    move: hQ1=> /[swap] /[apply] /[apply]
    sby srw heq=> {}heq > /heq }
  { sby move=> > _ _ ih > /ih }
  { sby move=> > _ _ ih > /ih }
  { move=> > /evalExact_sat ![>] /[dup] hQ1 /[swap] _ /[swap] /[apply] heq
    move: hQ1=> /[swap] /[apply] /[apply]
    sby srw heq=> {}heq > /heq }
  { move=> > /evalExact_sat ![>] /[dup] hQ1 /[swap] _ /[swap] /[apply] heq
    move: hQ1=> /[swap] /[apply] /[apply]
    sby srw heq=> {}heq > /heq }
  { sby move=> > _ ih > /ih }
  { sby unfold purepost }
  { sby unfold purepost }
  { move=> > /evalExact_sat ![>] /[dup] hQ₁ /[swap] /[apply] ? ih1 ih2 >
    move: hQ₁=> /[dup] hQ₁ /ih1 {}ih1
    scase: (finite_state (s' ∪ w_1))=> p /non_mem_union []
    move=> /[dup] /insert_same hins ? /[dup] /hins {}hins
    move: hQ₁=> /ih2 /[apply] /== {}ih2
    srw [1](insert_delete_id s' p)=> //
    sby move=> /ih2 /hins }
  { sdone }
  { move=> > _ ? > /= [] _ []
    sby srw insert_mem_keys }
  { move=> > _ /evalExact_sat ![>] /[dup] hQ₁ /[swap] _ /[swap] /[apply] ?
    sby move: hQ₁=> /[swap] /[apply] ih > /ih }
  { move=> > ? _ ih >
    scase: (finite_state' n.natAbs (sa ∪ s'))
    move=> p [] /ih /== {}ih /Finmap.disjoint_union_left /[dup] hdisj [] /ih {}ih
    move=> /union_difference_id heq
    srw -[1]heq=> /ih
    srw [2]Finmap.union_comm_of_disjoint ; rotate_left
    { sby srw Finmap.Disjoint.symm_iff }
    sby move: hdisj=> [] /[swap] /union_same_keys /[apply] }
  { sby move=> > _ ih > /ih }
  move=> > /evalExact_sat ![>] /[dup] hQ1 /[swap] _ /[swap] /[apply] heq
  move: hQ1=> /[swap] /[apply] /[apply]
  sby srw heq=> {}heq > /heq

lemma evalExact_det :
  evalExact s t Q →
  Q v₁ s₁ →
  Q v₂ s₂ →
  v₁ = v₂ ∧ s₁ = s₂ := by
  move=> heval
  elim: heval v₁ v₂ s₁ s₂
  { sdone }
  { sdone }
  { sdone }
  { move=> > _ /evalExact_sat ![>] /[swap] _ /[swap] _ /[swap] /[apply] ih
    sby move=> > /ih /[apply] }
  { move=> > _ /evalExact_sat ![>] /[swap] _ /[swap] _ /[swap] /[apply] ih
    sby move=> > /ih /[apply] }
  { sby move=> > ?? ih > /ih /[apply] }
  { sby move=> > ?? ih > /ih /[apply] }
  { move=> > /evalExact_sat ![>] /[swap] _ /[swap] _ /[swap] /[apply] ih
    sby move=> > /ih /[apply] }
  { move=> > /evalExact_sat ![>] /[swap] _ /[swap] _ /[swap] /[apply] ih
    sby move=> > /ih /[apply] }
  { sby move=> > _ ih > /ih /[apply] }
  { unfold purepost=> > ; scase: op=> > //
    { sby move=> [>] }
    { sby move=> [>] }
    sorry } -- can't have val_rand
  { unfold purepost=> > ; scase: op=> // >
    scase: a=> //
    any_goals (sby move=> [>]) }
  { move=> > /evalExact.ref /[apply]
    sorry }
  -- { move=> >
  --   scase: (finite_state s_1)=> p ? hev₁ hev₂ hfree ih1 ih2
  --   have hev:(evalExact s_1 (trm_ref x t1 t2) Q_1) := by
  --     { apply evalExact.ref ; apply hev₁ ; apply hev₂ ; apply hfree }
  --   move: hev hev₁=> /evalExact_WellAlloc hev
  --   move=> /[dup] /evalExact_sat ![>] /[dup] /ih2 {}ih2 /evalExact_WellAlloc /[apply] heq
  --   have eqn:(p ∉ w_1) := by
  --     { unfold Not=> /Finmap.mem_keys ; sby srw heq }
  --   apply ih2 in eqn=> {}ih2 {heq}
  --   move=> > /[dup] /hev heq₁
  --   have hs₁:(p ∉ s₁) := by
  --     { unfold Not=> /Finmap.mem_keys ; sby srw heq₁ }
  --   srw [1](insert_delete_id s₁ p) ; rotate_left ; apply hs₁=> {heq₁}
  --   apply w=> /hfree /ih2 {}ih2 /[dup] /hev heq₂ {hev}
  --   have hs₂:(p ∉ s₂) := by
  --     { unfold Not=> /Finmap.mem_keys ; sby srw heq₂ }
  --   srw [1](insert_delete_id s₂ p) ; rotate_left ; apply hs₂=> {heq₂}
  --   apply w=> /hfree /ih2 {ih2} ? ⟨|⟩ //
  --   sby apply (@insert_same_eq p w s₁ s₂) }
  { sdone }
  { sdone }
  { sorry }
  { sorry }
  { sby move=> > _ ih > /ih /[apply] }
  move=> > /evalExact_sat ![>] /[swap] _ /[swap] _ /[swap] /[apply]
  sby move=> ih > /ih /[apply]

lemma eval_imp_exact :
  eval s t Q → ∃ Q', evalExact s t Q' := by
  elim=> >
  { sby move=> * ; exists (fun v' s' ↦ v' = v ∧ s' = s_1) }
  { sby move=> * ; exists (fun v' s' ↦ v' = (val_fun x t1) ∧ s' = s_1) }
  { sby move=> * ; exists (fun v' s' ↦ v' = (val_fix f x t1) ∧ s' = s_1) }
  { move=> ? /evalExact_post hpost ? [Q1'] /[dup] /hpost {}hpost
    move=> /[dup] /evalExact_det hdet /[dup] ? /evalExact_sat ![>] /[dup] /hdet {}hdet
    move=> /hpost /[swap] /[apply] [Q'] ?
    exists Q' ; apply evalExact.app_arg1=> //
    sby move=> > /hdet [] }
  { move=> ? /evalExact_post hpost ? [Q1'] /[dup] /hpost {}hpost
    move=> /[dup] /evalExact_det hdet /[dup] ? /evalExact_sat ![>] /[dup] /hdet {}hdet
    move=> /hpost /[swap] /[apply] [Q'] ?
    exists Q' ; apply evalExact.app_arg2=> //
    sby move=> > /hdet [] }
  { move=> [] ? [Q'] ?
    exists Q'
    sby apply evalExact.app_fun }
  { move=> [] ? [Q'] ?
    exists Q'
    sby apply evalExact.app_fix }
  { move=> /evalExact_post hpost ? [Q1'] /[dup] /hpost {}hpost
    move=> /[dup] /evalExact_det hdet /[dup] ? /evalExact_sat ![>] /[dup] /hdet {}hdet
    move=> /hpost /[swap] /[apply] [Q'] ?
    exists Q' ; apply evalExact.seq=> //
    sby move=> > /hdet [] }
  { move=> /evalExact_post hpost ? [Q1'] /[dup] /hpost {}hpost
    move=> /[dup] /evalExact_det hdet /[dup] ? /evalExact_sat ![>] /[dup] /hdet {}hdet
    move=> /hpost /[swap] /[apply] [Q'] ?
    exists Q' ; apply evalExact.let=> //
    sby move=> > /hdet [] }
  { move=> ? [Q'] ?
    exists Q'
    sby constructor }
  { move=> ??
    exists (purepost s_1 P)
    sby apply evalExact.unop }
  { move=> ??
    exists (purepost s_1 P)
    sby apply evalExact.binop }
  { sorry }
  -- { move=> /evalExact_post hpost hev₁ ? [Q1'] /[dup] /hpost {}hpost
  --   move=> /[dup] /evalExact_det hdet /[dup] ? /evalExact_sat ![>] /[dup] /hdet {}hdet
  --   move=> /hpost /[swap] /[apply]
  --   scase: (finite_state w_1)=> p /[swap] /[apply] [Q'] ?
  --   exists (fun v' s' ↦ Q' v' (s'.insert p w)) ; apply evalExact.ref
  --   { sdone }
  --   rotate_left ; rotate_left ; apply (fun p ↦ Q')
  --   { move=> > /hpost /hev₁ /[apply] } }
  -- { move=> *
  --   exists (fun v'' s' ↦ ∃ p, p ∉ s_1 ∧ v'' = p ∧ s' = s_1.insert p v')
  --   sby apply evalExact.ref }
  { move=> *
    exists (fun v' s' ↦ v' = read_state p s_1 ∧ s' = s_1)
    sby apply evalExact.get }
  { move=> *
    exists (fun v'' s' ↦ v'' = val_unit ∧ s' = s_1.insert p v')
    sby apply evalExact.set }
  { sorry }
  { sorry }
  { move=> ? [Q'] ?
    sby exists Q' }
  move=> /evalExact_post hpost ? [Q1'] /[dup] /hpost {}hpost
  move=> /[dup] /evalExact_det hdet /[dup] ? /evalExact_sat ![>] /[dup] /hdet {}hdet
  move=> /hpost /[swap] /[apply] [Q'] ?
  exists Q' ; apply evalExact.while=> //
  sby move=> > /hdet []


/- ----------------------------- Frame Rule ----------------------------- -/

abbrev tohProp (h : heap -> Prop) : hProp := h
abbrev ofhProp (h : val -> hProp) : val -> heap -> Prop := h

lemma frame_eq_rw :
  s.Disjoint h2 →
  (fun v' s' ↦ v' = v ∧ s' = s ∪ h2) =
  (qstar (fun v' s' ↦ v' = v ∧ s' = s) (tohProp (fun h ↦ h = h2))) := by
  move=> ? ; funext=> /==
  apply Iff.intro
  { move=> [] *
    exists s, h2 }
  unfold tohProp
  sby move=> ![] >

lemma evalExact_frame_val (v : val) (s h2 : state) :
  s.Disjoint h2 →
  evalExact (s ∪ h2) t (fun v' s' ↦ v' = v ∧ s' = s ∪ h2) →
  evalExact (s ∪ h2) t
    (qstar (fun v' s' ↦ v' = v ∧ s' = s) (tohProp (fun h ↦ h = h2))) := by
  move=> ?
  sby srw frame_eq_rw

lemma purepost_frame :
  s.Disjoint h2 →
  (purepost (s ∪ h2) P) =
  (qstar (purepost s P) (tohProp fun h ↦ h = h2)) := by
  move=> ?
  unfold purepost tohProp
  funext=> /==
  apply Iff.intro
  { move=> [] *
    exists s, h2 }
  sby move=> ![>]

lemma evalExact_frame_unop_binop :
  s.Disjoint h2 →
  evalExact (s ∪ h2) t (purepost (s ∪ h2) P) →
  evalExact (s ∪ h2) t (qstar (purepost s P) (tohProp fun h ↦ h = h2)) := by
  move=> ?
  sby srw purepost_frame

lemma read_state_frame :
  s.Disjoint h2 →
  p ∈ s →
  (fun v' s' ↦ v' = read_state p (s ∪ h2) ∧ s' = s ∪ h2 ) =
  (qstar (fun v' s' ↦ v' = read_state p s ∧ s' = s) (tohProp fun h ↦ h = h2)) := by
  move=> ??
  unfold tohProp
  funext=> /==
  apply Iff.intro
  { sby srw in_read_union_l }
  srw in_read_union_l
  sby move=> ![>]

lemma evalExact_frame_get :
  s.Disjoint h2 →
  p ∈ s →
  evalExact (s ∪ h2) t (fun v' s' ↦ v' = read_state p (s ∪ h2) ∧ s' = s ∪ h2 ) →
  evalExact (s ∪ h2) t
    (qstar (fun v' s' ↦ v' = read_state p s ∧ s' = s) (tohProp fun h ↦ h = h2)) := by
  move=> ??
  sby srw read_state_frame

lemma insert_frame :
  s.Disjoint h2 →
  p ∈ s →
  fun v'' s' ↦ v'' = val_unit ∧ s' = Finmap.insert p v' (s ∪ h2) =
  (qstar (fun v'' s' ↦ v'' = val_unit ∧ s' = Finmap.insert p v' s) (tohProp fun h ↦ h = h2)) := by
  move=> ??
  unfold tohProp
  funext=> /==
  apply Iff.intro
  { srw Finmap.insert_union
    move=> [] *
    exists Finmap.insert p v' s, h2=> /== ⟨|⟩ // ⟨|⟩
    sby apply disjoint_insert_l }
  move=> ![>] /== [] [] [] ? [] /==
  sby srw Finmap.insert_union

lemma evalExact_frame_set :
  s.Disjoint h2 →
  p ∈ s →
  evalExact (s ∪ h2) t
    (fun v'' s' ↦ v'' = val_unit ∧ s' = Finmap.insert p v' (s ∪ h2)) →
  evalExact (s ∪ h2) t
    (qstar (fun v'' s' ↦ v'' = val_unit ∧ s' = Finmap.insert p v' s) (tohProp fun h ↦ h = h2)) := by
  move=> ??
  sby srw insert_frame

lemma evalExact_frame (h1 h2 : state) t (Q : val → hProp) :
  evalExact h1 t (ofhProp Q) →
  Finmap.Disjoint h1 h2 →
  evalExact (h1 ∪ h2) t (Q ∗ (tohProp (fun h ↦ h = h2))) :=
by
  simp [ofhProp]
  move=> /== heval
  elim: heval h2
  { move=> > *
    sby apply evalExact_frame_val }
  { move=> > *
    sby apply evalExact_frame_val }
  { move=> > *
    sby apply evalExact_frame_val }
  { move=> ???????? ih1 ?? /ih1 ? ; constructor=>//
    sby move=> ?? ![] }
  { move=> ???????? ih1 ?? /ih1 ? ; apply evalExact.app_arg2=>//
    sby move=> ?? ![] }
  { sby move=> * ; apply evalExact.app_fun }
  { sby move=> * ; apply evalExact.app_fix }
  { move=> ??????? ih1 ih2 ? /ih1 ? ; apply evalExact.seq=>//
    move=> ? s2 ![??? hQ2 *] ; subst s2 hQ2
    sby apply ih2 }
  { move=> ???????? ih1 ih2 ? /ih1 ? ; apply evalExact.let=>//
    move=> ?? ![??? hQ2 ? hU] ; subst hU hQ2
    sby apply ih2}
  { sby move=> * }
  { move=> > ? > *
    apply evalExact_frame_unop_binop=> //
    sby apply evalExact.unop }
  { move=> > ? > *
    apply evalExact_frame_unop_binop=> //
    sby apply evalExact.binop }
  { move=> > ; unfold tohProp
    move=> _ _ ih1 ih2 > /ih1 {}ih1
    apply evalExact.ref
    { apply ih1 }
    move=> {ih1} > ![>] hQ₁ /= -> ? -> p ?
    have eqn:(p ∉ w) := by sdone
    have eqn':((w.insert p v1).Disjoint h2) := by sby apply disjoint_update_not_r
    move: hQ₁ eqn eqn'=> /ih2 /[apply] /[apply] {ih2}
    srw insert_union=> // hq
    apply evalExact_post_eq ; rotate_left ; apply hq
    apply funext=> v ; apply funext=> h ; apply propext=> ⟨|⟩
    { move=> ![>] /= ? -> ? ->
      exists (w_2.erase p), h2=> ⟨//|/==⟩ ⟨|⟩
      apply erase_disjoint=> //
      sby srw remove_not_in_r }
    move=> ![>] /= ? -> ?
    scase: [p ∈ h]
    { move=> ? ; srw erase_of_non_mem=> // []
      exists w_2, h2=> /== ⟨|⟩ //
      sby srw erase_of_non_mem }
    move=> /Finmap.mem_iff [v'] /reinsert_erase_union heq herase
    srw (heq w_2 h2)=> // {heq}
    exists (w_2.insert p v'), h2=> /== ⟨|⟩
    { srw -insert_delete_id=> //
      have eqn:(p ∉ h.erase p) := by apply Finmap.not_mem_erase_self
      move: eqn
      sby srw herase }
    sby apply disjoint_update_not_r }
  { move=> > ? > *
    apply evalExact_frame_get=> //
    sby apply evalExact.get }
  { move=> > [] ? > * * ;
    apply evalExact_frame_set=> //
    sby apply evalExact.set }
  -- { move=> * ; apply eval.eval_free=>//
  --   srw remove_disjoint_union_l ; apply hstar_intro=>//
  --   sby apply disjoint_remove_l }
  { move=> > ??? ih1 ih2 > /ih1 {ih1} ?
    apply evalExact.alloc_arg=> // >
    sby move=> ![>] }
  { unfold tohProp=> > ?? ih > ? ; apply evalExact.alloc=> // >
    move=> /ih /[apply] {}ih /Finmap.disjoint_union_left [] /[dup] /ih {}ih ?
    srw Finmap.Disjoint.symm_iff -Finmap.union_assoc=> ?
    have eqn:((sb ∪ sa).Disjoint h2) := by
      sby srw Finmap.disjoint_union_left
    apply ih in eqn=> {ih} hq ; apply evalExact_post_eq ; rotate_left ; apply hq
    apply funext=> v ; apply funext=> h ; apply propext=> ⟨|⟩
    { move=> ![>] /= ? -> ? ->
      exists (w \ sb), h2=> /== ⟨|⟩ // ⟨|⟩
      { sby apply disjoint_disjoint_diff }
      apply union_diff_disjoint_r
      sby apply Finmap.Disjoint.symm }
    move=> ![>] /= ? -> ? /[dup] heq
    have eqn:((w ∪ h2).Disjoint sb) := by
      { srw -heq ; unfold Finmap.Disjoint=> /== }
    move: eqn=> /Finmap.disjoint_union_left [ ? _]
    move=> /(union_monotone_r (intersect h sb))
    srw diff_insert_intersect_id Finmap.union_assoc [2]Finmap.union_comm_of_disjoint
    rotate_left
    { apply Finmap.Disjoint.symm ; sby apply disjoint_intersect_r }
    srw -Finmap.union_assoc=> ?
    exists (w ∪ intersect h sb), h2=> //== ⟨|⟩
    { sby srw intersect_disjoint_cancel }
    constructor=> //
    srw Finmap.disjoint_union_left ; constructor=> //
    sby apply disjoint_intersect_r }
  { move=> // }
  move=> > ?? ih₁ ih₂ ??; econstructor
  { apply ih₁=> // }
  sby move=> > ![]

lemma eval_frame (h1 h2 : state) t (Q : val -> hProp) :
  eval h1 t (ofhProp Q) →
  Finmap.Disjoint h1 h2 →
  eval (h1 ∪ h2) t (Q ∗ (tohProp (fun h ↦ h = h2))) :=
by
  unfold ofhProp tohProp
  move=> /[dup] hev /eval_imp_exact [Q'] /[dup] hex /evalExact_frame /[apply]
  move=> /exact_imp_eval /eval_conseq ; sapply=> ?
  srw ?qstarE
  apply himpl_frame_l
  apply evalExact_post
  sby apply hev

-- previous free proof

  -- { move=> > ; unfold tohProp
  --   move=> > ?? hin hfree ih1 ih2 > /ih1 {}ih1
  --   apply eval.eval_ref
  --   { apply ih1 }
  --   { move=> > ![>] hQ₁ *
  --     subst s₂
  --     have eqn:(p ∉ w) := by sdone
  --     have eqn':((w.insert p v).Disjoint w_1) := by sby apply disjoint_update_not_r
  --     move: hQ₁ eqn eqn'=> /ih2 /[apply] /[apply]
  --     sby srw insert_union }
  --   { sby move=> > ![>] /hin }
  --   move=> > ![>] /[dup] /hin ? /hfree hQ_1 /= [] ? []
  --   exists (w.erase p), h2=> /== ⟨|⟩ // ⟨|⟩
  --   apply erase_disjoint=> //
  --   sby apply remove_disjoint_union_l }

end evalProp


/- --------------------- Structural Rules --------------------- -/

/- For proofs below, [sorry] takes the place of [xsimp] -/

/- Consequence and Frame Rule -/

lemma triple_conseq t H' Q' H Q :
  triple t H' Q' →
  H ==> H'→
  Q' ===> Q →
  triple t H Q :=
by
  move=> /triple *
  srw triple => ??
  sby apply (eval_conseq _ _ Q' _)

lemma triple_frame t H (Q : val -> hProp) H' :
  triple t H Q →
  triple t (H ∗ H') (Q ∗ H') :=
by
  move=> /triple hEval
  srw triple=>? ![?? hs ? hDisj hU] ; srw hU
  apply eval_conseq
  { apply (eval_frame _ _ _ _ (hEval _ hs) hDisj) =>// }
  { move=> ?
    sby srw ?qstarE ; xsimp }


/- Extraction Rules -/

lemma triple_hpure t P H Q :
  (P → triple t H Q) →
  triple t (⌜P⌝ ∗ H) Q :=
by
  move=> ?
  srw triple=> ? ![?? [? /hempty_inv hEmp] ?? hU]
  sby srw hU hEmp Finmap.empty_union

lemma triple_hexists t A (J : A → hProp) Q :
  (forall x, triple t (J x) Q) →
  triple t (hexists J) Q :=
by
  sby srw []triple => hJ ? [] ? /hJ

lemma triple_hforall t A (x : A) (J : A → hProp) Q:
  triple t (J x) Q →
  triple t (hforall J) Q :=
by
  move=> /triple_conseq ; sapply => ?
  sapply ; sdone

lemma triple_hwand_hpure_l t (P : Prop) H Q :
  P →
  triple t H Q →
  triple t (⌜P⌝ -∗ H) Q :=
by
  move=> ? /triple_conseq ; sapply
  rw [hwand_hpure_l] <;> sdone
  sby move=> ??

/- A useful corollary of [triple_hpure] -/
lemma triple_hpure' t (P : Prop) Q :
  (P → triple t emp Q) →
  triple t ⌜P⌝ Q :=
by
  move=> /triple_hpure
  sby srw hstar_hempty_r

/- Heap -naming rule -/
lemma triple_named_heap t H Q :
  (forall h, H h → triple t (fun h' ↦ h' = h) Q) →
  triple t H Q :=
by
  sby move=> hH ? /hH

/- Combined and ramified rules -/

lemma triple_conseq_frame H2 H1 Q1 t H Q :
  triple t H1 Q1 →
  H ==> H1 ∗ H2 →
  Q1 ∗ H2 ===> Q →
  triple t H Q :=
by
  move=> /triple_frame hFra /triple_conseq hCons /hCons
  sapply ; apply hFra

lemma triple_ramified_frame H1 Q1 t H Q :
  triple t H1 Q1 →
  H ==> H1 ∗ (Q1 -∗ Q) →
  triple t H Q :=
by
  move=> ??;
  apply triple_conseq_frame=>//
  sby srw -qwand_equiv=> ?


/- ---------------------- Rules for Terms ---------------------- -/

lemma triple_eval_like t1 t2 H Q :
  eval_like t1 t2 →
  triple t1 H Q →
  triple t2 H Q :=
by
  srw eval_like=> hLike ? ??
  sby apply hLike

lemma triple_val v H Q :
  H ==> Q v →
  triple (trm_val v) H Q :=
by
  move=> ? ??
  sby apply eval.eval_val

lemma triple_val_minimal v :
  triple (trm_val v) emp (fun r ↦ ⌜r = v⌝) :=
by
  apply triple_val
  xsimp

lemma triple_fun x t1 H Q :
  H ==> Q (val_fun x t1) →
  triple (trm_fun x t1) H Q :=
by
  move=> ? ??
  sby apply eval.eval_fun

lemma triple_fix f x t1 H Q :
  H ==> Q (val_fix f x t1) →
  triple (trm_fix f x t1) H Q :=
by
  move=> ? ??
  sby apply eval.eval_fix

lemma triple_seq t1 t2 H Q H1 :
  triple t1 H (fun _ ↦ H1) →
  triple t2 H1 Q →
  triple (trm_seq t1 t2) H Q :=
by
  srw triple=> hH ? ??
  apply eval.eval_seq
  { sby apply hH }
  sdone

lemma triple_let x t1 t2 Q1 H Q :
  triple t1 H Q1 →
  (forall v1, triple (subst x v1 t2) (Q1 v1) Q) →
  triple (trm_let x t1 t2) H Q :=
by
  srw triple=> hH ? ??
  apply eval.eval_let
  { sby apply hH }
  sdone

-- WIP
/- wp (trm_ref x (val_int n) t) Q =
   (p ~~> n) -* wp (subst x t) (Q * ∃ʰ n, (p ~~> n)) -/
lemma triple_ref (v : val) :
  (forall (p : loc), triple (subst x p t2) (H ∗ (p ~~> v)) (Q ∗ ∃ʰ v, p ~~> v)) →
  triple (trm_ref x (trm_val v) t2) H Q := by
  move=> htriple h ?
  apply eval.eval_ref
  { sby apply (eval.eval_val h v (fun v' h' ↦ v' = v ∧ h' = h)) }
  move=> > [->->] > ?
  move: (htriple p)=> /triple_conseq {}htriple
  have eqn:(triple (subst x p t2) (H ∗ p ~~> v) fun v s ↦ Q v (s.erase p)) := by
    apply htriple=> //
    move=> > h /= ![>] ? /hexists_inv [v'] /hsingl_inv ->
    sby move=> /union_singleton_eq_erase /[apply] <-
  move=> {htriple}
  apply eqn
  exists h, Finmap.singleton p v
  move=> ⟨//|⟩ ⟨|⟩
  apply hsingle_intro=> ⟨|⟩
  apply disjoint_single=>//
  sby apply insert_eq_union_single=> //

lemma triple_let_val x v1 t2 H Q :
  triple (subst x v1 t2) H Q →
  triple (trm_let x v1 t2) H Q :=
by
  move=> ?
  apply triple_let _ _ _ (fun v ↦ ⌜v = v1⌝ ∗ H)
  { apply triple_val ; xsimp }
  move=> ?
  sby apply triple_hpure

lemma triple_if (b : Bool) t1 t2 H Q :
  triple (if b then t1 else t2) H Q →
  triple (trm_if b t1 t2) H Q :=
by
  move=> ? ??
  sby apply eval.eval_if

lemma triple_app_fun x v1 v2 t1 H Q :
  v1 = val_fun x t1 →
  triple (subst x v2 t1) H Q →
  triple (trm_app v1 v2) H Q :=
by
  move=> * ??
  sby apply eval.eval_app_fun

lemma triple_app_fun_direct x v2 t1 H Q :
  triple (subst x v2 t1) H Q →
  triple (trm_app (val_fun x t1) v2) H Q :=
by
  move=> ?
  sby apply triple_app_fun

lemma triple_app_fix v1 v2 f x t1 H Q :
  v1 = val_fix f x t1 →
  triple (subst x v2 (subst f v1 t1)) H Q →
  triple (trm_app v1 v2) H Q :=
by
  move=> * ??
  sby apply eval.eval_app_fix

lemma triple_app_fix_direct v2 f x t1 H Q :
  f ≠ x →
  triple (subst x v2 (subst f (val_fix f x t1) t1)) H Q →
  triple (trm_app (val_fix f x t1) v2) H Q :=
by
  move=> * ??
  sby apply triple_app_fix


/- Rules for Heap-Manipulating Primitive Operations -/

lemma read_state_single p v :
  read_state p (Finmap.singleton p v) = v :=
by
  srw read_state Finmap.lookup_singleton_eq

lemma triple_get v (p : loc) :
  triple (trm_app val_get p)
    (p ~~> v)
    (fun r ↦ ⌜r = v⌝ ∗ (p ~~> v)) :=
by
  move=> ? []
  apply eval.eval_get=>//
  srw hstar_hpure_l => ⟨|⟩ //
  apply read_state_single

lemma triple_set w p (v : val) :
  triple (trm_app val_set (val_loc p) v)
    (p ~~> w)
    (fun r ↦ ⌜r = val_unit⌝ ∗ (p ~~> v)) :=
by
  move=> ? []
  apply eval.eval_set=>//
  sby srw Finmap.insert_singleton_eq hstar_hpure_l

-- lemma triple_free' p v :
--   triple (trm_app val_free (val_loc p))
--     (p ~~> v)
--     (fun r ↦ ⌜r = val_unit⌝) :=
-- by
--   move=> ? []
--   apply eval.eval_free=>//
--   srw hpure hexists hempty
--   exists rfl
--   apply Finmap.ext_lookup => ?
--   sby srw Finmap.lookup_empty Finmap.lookup_eq_none Finmap.mem_erase

-- lemma triple_free p v:
--   triple (trm_app val_free (val_loc p))
--     (p ~~> v)
--     (fun _ ↦ emp) :=
-- by
--   apply (triple_conseq _ _ _ _ _ (triple_free' p v))
--   { sdone }
--   xsimp ; xsimp

/- Rules for Other Primitive Operations -/

lemma triple_unop op v1 (P : val → Prop) :
  evalunop op v1 P →
  triple (trm_app op v1) emp (fun r ↦ ⌜P r⌝) :=
by
  move=> ? ? []
  apply (eval_conseq _ _ (fun v s ↦ P v ∧ s = ∅))
  { apply eval.eval_unop=>//
    sby srw purepostin }
  { move=> ?? [] ? hEmp
    sby srw hEmp }

lemma triple_binop op v1 v2 (P : val → Prop) :
  evalbinop op v1 v2 P →
  triple (trm_app op v1 v2) emp (fun r ↦ ⌜P r⌝) :=
by
  move=> ? ? []
  apply (eval_conseq _ _ (fun v s ↦ P v ∧ s = ∅))
  { apply eval.eval_binop=>//
    sby srw purepostin }
  { move=> ?? [] ? hEmp
    sby srw hEmp }

lemma triple_add n1 n2 :
  triple (trm_app val_add (val_int n1) (val_int n2))
    emp
    (fun r ↦ ⌜r = val_int (n1 + n2)⌝) :=
by
  sby apply triple_binop

lemma triple_div n1 n2 :
  n2 ≠ 0 →
  triple (trm_app val_div (val_int n1) (val_int n2))
    emp
    (fun r ↦ ⌜r = val_int (n1 / n2)⌝) :=
by
  move=> ?
  sby apply triple_binop

lemma triple_rand n :
  n > 0 →
  triple (trm_app val_rand (val_int n))
    emp
    (fun r ↦ ⌜exists n1, r = val_int n1 ∧ 0 <= n1 ∧ n1 < n⌝) :=
by
  move=> ?
  sby apply triple_unop

lemma triple_neg (b1 : Bool) :
  triple (trm_app val_neg b1)
    emp
    (fun r ↦ ⌜r = val_bool (¬b1)⌝) :=
by
  sby apply triple_unop

lemma triple_opp n1 :
  triple (trm_app val_opp (val_int n1))
    emp
    (fun r ↦ ⌜r = val_int (-n1)⌝) :=
by
  sby apply triple_unop

lemma triple_eq v1 v2 :
  triple (trm_app val_eq (trm_val v1) (trm_val v2))
    emp
    (fun r ↦ ⌜r = is_true (v1 = v2)⌝) :=
by
  sby apply triple_binop

lemma triple_neq v1 v2 :
  triple (trm_app val_neq (trm_val v1) (trm_val v2))
    emp
    (fun r ↦ ⌜r = is_true (v1 ≠ v2)⌝) :=
by
  sby apply triple_binop

lemma triple_sub n1 n2 :
  triple (trm_app val_sub (val_int n1) (val_int n2))
    emp
    (fun r ↦ ⌜r = val_int (n1 - n2)⌝):=
by
  sby apply triple_binop

lemma triple_mul n1 n2 :
  triple (trm_app val_mul (val_int n1) (val_int n2))
    emp
    (fun r ↦ ⌜r = val_int (n1 * n2)⌝):=
by
  sby apply triple_binop

lemma triple_mod n1 n2 :
  n2 ≠ 0 →
  triple (trm_app val_mod (val_int n1) (val_int n2))
    emp
    (fun r ↦ ⌜r = val_int (n1 % n2)⌝) :=
by
  move=> ?
  sby apply triple_binop

lemma triple_le n1 n2 :
  triple (trm_app val_le (val_int n1) (val_int n2))
    emp
    (fun r ↦ ⌜r = val_bool (n1 <= n2)⌝) :=
by
  sby apply triple_binop

lemma triple_lt n1 n2 :
  triple (trm_app val_lt (val_int n1) (val_int n2))
    emp
    (fun r ↦ ⌜r = val_bool (n1 < n2)⌝) :=
by
  sby apply triple_binop

lemma triple_ge n1 n2 :
  triple (trm_app val_ge (val_int n1) (val_int n2))
    emp
    (fun r ↦ ⌜r = val_bool (n1 >= n2)⌝) :=
by
  sby apply triple_binop

lemma triple_gt n1 n2 :
  triple (trm_app val_gt (val_int n1) (val_int n2))
    emp
    (fun r ↦ ⌜r = val_bool (n1 > n2)⌝) :=
by
  sby apply triple_binop

private lemma abs_nonneg n :
  n ≥ 0 → Int.natAbs n = n :=
by
  move=> ?
  sby elim: n

lemma triple_ptr_add (p : loc) (n : ℤ) :
  p + n >= 0 →
  triple (trm_app val_ptr_add p n)
    emp
    (fun r ↦ ⌜r = val_loc ((p + n).natAbs)⌝) :=
by
  move=> ?
  apply triple_binop
  apply evalbinop.evalbinop_ptr_add
  sby srw abs_nonneg

lemma triple_ptr_add_nat p (f : ℕ) :
  triple (trm_app val_ptr_add (val_loc p) (val_int (Int.ofNat f)))
    emp
    (fun r ↦ ⌜r = val_loc (p + f)⌝) :=
by
  apply triple_conseq _ _ _ _ _ (triple_ptr_add p f _)=>// ? /=
  sby xsimp

/- --------------------- Strongest Post Condition --------------------- -/

abbrev sP h t :=fun v => h∀ (Q : val -> hProp), ⌜eval h t Q⌝ -∗ Q v

open Classical
lemma hpure_intr :
  (P -> H s) -> (⌜P⌝ -∗ H) s := by
  move=> ?
  scase: [P]=> p
  { exists ⊤, s, ∅; repeat' constructor=> //
    { xsimp=>// }
    sorry }
  sorry

lemma hforall_impl (J₁ J₂ : α -> hProp) :
  (forall x, J₁ x ==> J₂ x) ->
  hforall J₁ ==> hforall J₂ := by
  move=> ? h /[swap]  x/(_ x)//

lemma sP_strongest :
  eval h t Q -> sP h t ===> Q := by
  move=> ev v; unfold sP;
  apply himpl_hforall_l _ Q
  srw hwand_hpure_l=> //

set_option maxHeartbeats 800000 in
lemma sP_post :
  eval h t Q -> eval h t (sP h t) := by
  elim=> >
  { move=> ?; constructor=> Q; apply hpure_intr=> []// }
  { move=> ?; constructor=> Q; apply hpure_intr=> []// }
  { move=> ?; constructor=> Q; apply hpure_intr=> []// }
  { move=> ? evv ev' ih ih'; apply eval.eval_app_arg1=> //
    move=> > ?; apply eval_conseq=> //
    apply ih'
    { apply sP_strongest; apply evv=> // }
    move=> v; dsimp [sP]; apply himpl_hforall=> Q/=
    xsimp=> ev; srw hwand_hpure_l=> //
    scase: ev=> //
    { move=> ?? /sP_strongest himp; sapply
      sby apply himp }
    { scase=> // [] // ?? []// }
    move=> >? []// }
  { move=> ? ev₁; intro ih ih' sp
    apply eval.eval_app_arg2=> // > sp'
    apply eval_conseq=> //
    apply sp
    { apply sP_strongest; apply ev₁=> // }
    move=> v; dsimp [sP]; apply himpl_hforall=> Q/=
    xsimp=> ev; srw hwand_hpure_l=> //
    scase: ev=> // ??/sP_strongest himp; sapply=> //
    sby apply himp }
  { move=> -> ? ih; apply eval.eval_app_fun=> //
    apply eval_conseq=> //
    move=> v; dsimp [sP]; apply himpl_hforall=> Q/=
    xsimp=> ev; srw hwand_hpure_l=> //
    scase: ev=> // }
  { move=> -> ? ih; apply eval.eval_app_fix=> //
    apply eval_conseq=> //
    move=> v; dsimp [sP]; apply himpl_hforall=> Q/=
    xsimp=> ev; srw hwand_hpure_l=> //
    scase: ev=> // }
  { move=> ev₁ _ sp ih₂; constructor; apply sp
    move=> > ?
    apply eval_conseq=> //; apply ih₂
    { apply sP_strongest; apply ev₁=> // }
    move=> v; dsimp [sP]; apply himpl_hforall=> Q/=
    xsimp=> ev; srw hwand_hpure_l=> //
    scase: ev=> // ? ev₁; sapply
    apply sP_strongest; apply ev₁=> // }
  { move=> ev₁ _ sp ih₂; constructor; apply sp
    move=> > ?
    apply eval_conseq=> //; apply ih₂
    { apply sP_strongest; apply ev₁=> // }
    move=> v; dsimp [sP]; apply himpl_hforall=> Q/=
    xsimp=> ev; srw hwand_hpure_l=> //
    scase: ev=> // ? ev₁; sapply
    apply sP_strongest; apply ev₁=> // }
  { move=> ev sp; constructor
    apply eval_conseq=> // v
    dsimp [sP]; apply himpl_hforall=> Q/=
    xsimp=> ev; srw hwand_hpure_l=> //
    scase: ev=> // }
  { move=> eop pp; apply eval.eval_unop=> // ? ??
    apply hpure_intr=> []//??; sapply
    scase: eop
    { move=> ? [] //== }
    { move=> ? [] // }
    move=> ? [] // }
  { move=> eop pp; apply eval.eval_binop=> // ? ??
    apply hpure_intr=> []//?
    { move=> ? [] // [] // }
    move=> eop'; sapply; scase: eop
    any_goals (try scase: eop'=> //)
    any_goals (try move=> ?? [] //)
    move=> ???->? []// }
  { sorry
    -- move=> ->?; apply eval.eval_ref=> // ???
    -- apply hpure_intr=> []//
     }
  { move=> ??; apply eval.eval_get=> // ?
    apply hpure_intr=> []// }
  { move=> ->??; apply eval.eval_set=> // ?
    apply hpure_intr=> []// ?? []// }
  -- { move=> ??; apply eval.eval_free=> // ?
  --   apply hpure_intr=> []// }
  -- { move=> ??; apply eval.eval_alloc=> // *?
  --   apply hpure_intr=> []// }
  { sorry }
  { sorry }
  { move=> ev₁ ev₂; constructor
    apply eval_conseq=> // v
    dsimp [sP]; apply himpl_hforall=> Q/=
    xsimp=> ev; srw hwand_hpure_l=> //
    sby scase: ev }
  move=> ev₁ ev₂ evsP ih ⟨|//|⟩ > ?
  apply eval_conseq=> //; apply ih
  { apply sP_strongest; apply ev₁=> // }
  move=> v; dsimp [sP]; apply himpl_hforall=> Q/=
  xsimp=> ev; srw hwand_hpure_l=> //
  scase: ev=> // ? ev; sapply
  apply sP_strongest; sby apply ev
