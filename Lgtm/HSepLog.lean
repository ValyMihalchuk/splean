-- import Ssreflect.Lang
import Mathlib.Data.Finmap

import Lgtm.Util
import Lgtm.HProp
import Lgtm.HHProp
import Lgtm.XSimp
import Lgtm.SepLog

section HSepLog

open Classical

variable {α : Type}

def htrm := α -> trm
def hval := α -> val

local notation "hheap"  => @hheap α
local notation "hhProp" => @hhProp α
local notation "htrm"   => @htrm α /- Program Product -/
local notation "hval"   => @hval α

open trm val

/- ================= Hyper Semantics for Program Products ================= -/

section heval

/- -------------- Hyper-Evaluation Definition -------------- -/

def heval_nonrel (s : Set α) (hh : hheap) (ht : htrm) (hQ : α -> val -> hProp) : Prop :=
  ∀ a ∈ s, eval (hh a) (ht a) (hQ a)

@[simp]
noncomputable def fun_insert {α β} (f g : α -> β) (s : Set α ) :=
  fun a => if a ∈ s then f a else g a

notation f " ∪_" s:max g => fun_insert f g s

lemma fun_insert_ss :
  ((f ∪_s g) ∪_s h) = f ∪_s h := by
    sby move=> !? /=; scase_if

lemma fun_insert_ff :
  (f ∪_s f) = f := by
    sby move=> !?


lemma fun_insert_ss' :
  (f ∪_s g ∪_s h) = f ∪_s h := by
    sby move=> !? /=; scase_if


lemma fun_insert_assoc :
  ((f ∪_s₁ g) ∪_(s₁ ∪ s₂)  h) = f ∪_s₁ g ∪_s₂ h := by
    sby move=> !? /==; scase_if=> //; scase_if


def heval (s : Set α) (hh : hheap) (ht : htrm) (hQ : hval -> hhProp) : Prop :=
  ∃ (hQ' : α -> val -> hProp),
    heval_nonrel s hh ht hQ' ∧
    ∀ hv, bighstarDef s (fun a => hQ' a (hv a)) hh ==> h∃ hv', hQ (hv ∪_s hv')
    /-                    hQ'                      ==>         hQ -/

/- -------------- Hyper-Evaluation Properties -------------- -/

/- **Frame** Rule -/
lemma heval_nonrel_conseq (s : Set α) :
  heval_nonrel s hh t Q1 →
  (∀ a, qimpl (Q1 a) $ Q2 a) →
  heval_nonrel s hh t Q2 := by
  sby move=> hev qimp a /hev/eval_conseq /(_ (qimp a))

lemma heval_conseq :
  heval s hh t Q1 →
  Q1 ===> Q2 →
  heval s hh t Q2 := by
  scase! => ?? himp qimp ⟨//|⟩
  sby constructor=> // hv ? /himp; apply hhimpl_hhexists

lemma heval_nonrel_frame :
  heval_nonrel s hh1 t Q →
  hdisjoint hh1 hh2 →
  heval_nonrel s (hh1 ∪ hh2) t (fun a => Q a ∗ (fun hh ↦ hh = hh2 a)) := by
  sby move=> hev ?? /hev /eval_frame

lemma heval_frame :
  heval s hh1 t Q →
  hdisjoint hh1 hh2 →
  heval s (hh1 ∪ hh2) t (Q ∗ (· = hh2)) := by
  scase! => hQ ? himp ?
  exists fun a => hQ a ∗ (· = hh2 a)=> ⟨|hv⟩
  { sby apply heval_nonrel_frame }
  srw qstarE hqstarE -bighstarDef_hhstar // bighstarDef_eq
  srw -hhstar_hhexists_l
  sby apply hhimpl_hhstar_trans_l


/- **Prod** Rule -/

/-   ∀ i ∈ s, { Hᵢ } [P i] { Qᵢ }
 ----------------------------------------
 { ∗_(i ∈ s) Hᵢ } [s : P] { ∗_(i ∈ s) Qᵢ }
 -/
lemma heval_prod (hQ : α -> val -> hProp) :
  (∀ a, eval (hh a) (ht a) (hQ a)) ->
  heval s hh ht fun hv => bighstarDef s (fun a => hQ a (hv a)) hh := by
  move=> hev; exists hQ=> ⟨|hv ⟩ //
  sby apply (hhimpl_hhexists_r hv); srw fun_insert_ff

/- Stronges Hyper Post Condition -/

abbrev isHStrongestPostNonrel (s : Set α) h t (sP : α -> _) :=
  ∀ Q, heval_nonrel s h t Q -> ∀ a ∈ s, qimpl (sP a) (Q a)

abbrev hStrongestPostNonrel (hh : hheap) (ht : htrm) :=
  fun a => sP (hh a) (ht a)


lemma hstrongest_postP :
  isHStrongestPostNonrel s hh ht (hStrongestPostNonrel hh ht) := by
  move=> Q ? a ?? /=; apply himpl_hforall_l _ (Q a)
  sby srw hwand_hpure_l


lemma hstrongest_post_provable :
  heval_nonrel s hh ht hQ -> heval_nonrel s hh ht (hStrongestPostNonrel hh ht) := by
  move=> hev a /hev; unfold hStrongestPostNonrel
  apply sP_post

lemma heval_strongest :
  heval s hh ht hQ ->
  ∃ (hQ' : α -> val -> hProp),
    isHStrongestPostNonrel s hh ht hQ' ∧
    heval_nonrel s hh ht hQ' ∧
    ∀ hv, bighstarDef s (fun a => hQ' a (hv a)) hh ==> h∃ hv', hQ (hv ∪_s hv') := by
  scase! => hQ ? himp; exists hStrongestPostNonrel hh ht
  repeat' constructor
  { sby apply hstrongest_postP }
  { sby apply hstrongest_post_provable }
  move=> hv; apply hhimpl_trans_r; apply himp
  apply bighstarDef_himpl=> ??
  sby apply hstrongest_postP


/- **Unfocus** Rule -/

lemma heval_nonrel_split :
  heval_nonrel s₁ hh ht hQ ->
  heval_nonrel s₂ hh ht hQ ->
  heval_nonrel (s₁ ∪ s₂) hh ht hQ := by
  sby move=> hev₁ hev₂ ? /== [/hev₁|/hev₂]

lemma heval_nonrel_sat :
  heval_nonrel s h t Q ->
    ∃ (hh : hheap) (hv : hval), ∀ a ∈ s, Q a (hv a) (hh a) := by
    move=> ev
    shave: ∃ (hhv : α -> heap × val), ∀ a ∈ s, Q a (hhv a).2 (hhv a).1
    { srw -(@skolem _ (fun _ => heap × val) (fun a b => a ∈ s -> Q a b.2 b.1))
      move=> x; scase: [x ∈ s]
      { move=> ?; constructor=> // }
      move=> /ev /eval_sat ![]h v ?
      sby exists (v,h)=> ? }
    scase=> hhv H; exists (fun a => (hhv a).1), (fun a => (hhv a).2)


lemma heval_unfocus (s₁ s₂ : Set α) :
  Disjoint s₁ s₂ ->
  heval (s₁ ∪ s₂) hh ht hQ ->
  heval s₁ hh ht (fun hv₁ => (heval s₂ · ht (hQ $ hv₁ ∪_s₁ ·))) := by
  move=> /Set.disjoint_left dj ![hQ₁ hev] /= himp
  exists (fun a => if a ∈ s₁ then hQ₁ a else (fun _ => (· = hh a)))
  constructor=> [|hv/= hh' /= H']
  { sby move=> ?? /=; scase_if }
  exists (fun _ => val_unit)=> /=; srw fun_insert_ss
  exists (fun a => if a ∈ s₂ then hQ₁ a else (fun _ => (· = hh' a)))
  constructor
  { move=> a /[dup]/dj/=; scase_if=> //== ??
    sby move: (H' a); scase_if=> // ? ->; apply hev }
  move=> hv' /=; srw -fun_insert_assoc
  apply hhimpl_trans_r; apply himp
  move=> hh /= /[swap] a /(_ a) /==
  sby move: (H' a); scase_if


/- **Focus** Rule -/

lemma heval_focus (s₁ s₂ : Set α) :
  Disjoint s₁ s₂ ->
  heval s₁ hh ht (fun hv₁ => (heval s₂ · ht (hQ $ hv₁ ∪_s₁ ·))) ->
  heval (s₁ ∪ s₂) hh ht hQ := by
  move=> /Set.disjoint_left dj ![hQ₁ hev] /= himp
  scase!: (heval_nonrel_sat hev)=> hh' hv H
  move: (himp hv)
  move=> /(_ fun a => if a ∈ s₁ then hh' a else hh a) /= H
  specialize H ?_=> //; scase: H=> hv' /= /heval_strongest ![hQ₂ hstr hev' /= himp']
  exists (fun a => if a ∈ s₁ then hQ₁ a else hQ₂ a)=> ⟨|⟩
  { apply heval_nonrel_split=> [a|a /[dup]?/dj] /=; scase_if=> //
    sby move: (hev' a)=> // }
  clear hv H himp'=> hv hh' /= H'
  move: (himp hv)
  move=> /(_ fun a => if a ∈ s₁ then hh' a else hh a) /= H
  specialize H ?_
  { sby move=> a; scase_if=> //; move: (H' a)=> /==; scase_if }
  scase: H=> hv'' ![hQ₂' hev /=]
  srw fun_insert_ss -fun_insert_assoc=> /(_ hv) /fun_insert_ff
  sapply=> a; scase_if=> //; rotate_left
  { sby move: (H' a)=> /==; scase_if }
  move: (H' a)=> /==; scase_if=> ?; scase_if=> // ??
  sby apply hstr=> // a /[dup]/dj ? /hev /=; scase_if


end heval


end HSepLog


/- ------------------ Function Substitution ------------------ -/
open Function (partialInv)

section hsubst

open Classical

variable {α β: Type}
variable (σ : α -> β)

def hlocal (s : Set α) (h : @hheap α) := ∀ a, a ∉ s -> h a = ∅

noncomputable def partialInvSet (s : Set α) (σ : α -> β) : β -> Option α :=
  fun b =>
    match partialInv σ b with
    | .some a => if a ∈ s then some a else none
    | .none => none

noncomputable def fsubst {γ : Type} [Inhabited γ] (s : Set α) (g : α -> γ) : β -> γ :=
  fun b => (g <$> partialInvSet s σ b).get!

@[inline] abbrev ssubst (s : Set α) : Set α -> Set β := fsubst σ s

def validSubst (s : Set α) (g : α -> γ) : Prop :=
  ∀ a ∈ s, ∀ b ∈ s, σ a = σ b -> g a = g b

lemma fsubst_in (s : Set α) : a ∈ s -> σ a ∈ ssubst σ s s := by
  move=> In; unfold Membership.mem Set.instMembership Set.Mem ssubst fsubst=> /==

def hsubst (s : Set α) : @hhProp α -> @hhProp β :=
  fun H h =>
    ∃ h', h = fsubst σ s h' ∧ H h' ∧ hlocal s h'


def hsubst_heval_nonrel (s : Set α) :
  heval_nonrel (fsubst σ s s) (fsubst σ s hh) ht (fsubst σ s Q) ->
  heval_nonrel s hh (ht ∘ f) Q := by
  move=> ev a /=


def hsubst_heval (s : Set α) :
  heval (ssubst σ s s) (fsubst σ s hh) ht (fun hv => hsubst f s (Q (hv ∘ f))) ->
  heval s hh (ht ∘ f) Q := by sorry

end hsubst
