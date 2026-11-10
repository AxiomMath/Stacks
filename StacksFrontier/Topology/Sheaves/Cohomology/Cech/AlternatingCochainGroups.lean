module

public import Mathlib.Algebra.Category.Grp.Basic
public import Mathlib.AlgebraicTopology.SimplexCategory.Basic
public import Mathlib.Data.Fin.Tuple.Sort
public import Mathlib.GroupTheory.Perm.Fin
public import Mathlib.Order.Int.ConditionallyCompleteOrder
public import Mathlib.Tactic.Abel
public import Mathlib.Tactic.LinearCombination
public import Mathlib.Topology.Sheaves.Presheaf

@[expose] public section

set_option backward.isDefEq.respectTransparency false

/-
# Problem Description

This formalizes Lemma 20.23.3 of the Stacks project (Tag 01FJ).

Fix a topological space `X`, a family `U : I → Opens X` (an open covering of an open
`U ⊆ X`; the covering condition is not actually needed for the lemma, see the
"Generality" note), and an abelian presheaf `ℱ` on `X`.

For a tuple `(i_0, …, i_p) ∈ I^{p+1}` we write
`U_{i_0…i_p} = U_{i_0} ∩ U_{i_1} ∩ … ∩ U_{i_p}`.
For `t ∈ ℱ(V)` and `W ≤ V` we write `t|_W ∈ ℱ(W)` for the image under the
presheaf restriction map.

Definition 1 (Čech complex):
  `Č^p(𝒰, ℱ) = ∏_{(i_0,…,i_p) ∈ I^{p+1}} ℱ(U_{i_0…i_p})`,
with differential
  `d(s)_{i_0…i_{p+1}} = ∑_{j=0}^{p+1} (-1)^j s_{i_0…î_j…i_{p+1}}|_{U_{i_0…i_{p+1}}}`.
This is a complex (`d ∘ d = 0`).

Definition 2 (Alternating Čech complex): the subgroup of `s` such that
  - `s_{i_0…i_p} = 0` whenever `i_n = i_m` for some `n ≠ m`, and
  - swapping two *distinct* entries of the index tuple negates the value.
The differential `d` restricts to it, making it a subcomplex.

Definition 3 (Ordered Čech complex): assume `I` is totally ordered; take the product
only over strictly increasing tuples `i_0 < i_1 < … < i_p`, with the same `d`.
This is a complex (`d ∘ d = 0`).

Definition 4 (Comparison map `c`): `c : Č_ord → Č` defined for distinct indices by
  `c(s)_{i_0…i_p} = sgn(σ) · s_{i_{σ(0)}…i_{σ(p)}}`
where `σ` is the permutation sorting the indices into increasing order, and `0` if the
indices are not pairwise distinct.

Main Statement (Tag 01FJ): `c` is a morphism of complexes whose image lies in the
alternating subcomplex, and the induced map `c : Č_ord → Č_alt` is an isomorphism of
complexes.  Concretely:
  (1) `c` is a chain map;
  (2) the image of `c` lies in `Č_alt`;
  (3) the corestriction `c : Č_ord^p → Č_alt^p` is an isomorphism of abelian groups.
The differentials are group homomorphisms, the comparison map `c` is a group
homomorphism, and the bijection of (3) is packaged as an `AddEquiv` onto the
alternating subgroup.
-/

open CategoryTheory TopologicalSpace Opposite

namespace CechCochains

variable {X : TopCat} {I : Type*} (U : I → Opens X) (ℱ : TopCat.Presheaf Ab X)

/-! ## Intersections of the cover -/

/-- The open `U_{i_0…i_{p-1}} = ⋂_k U_{i_k}` associated to a tuple of indices. It depends
only on the underlying set of indices, since intersection is independent of order and
multiplicity. -/
def inter {p : ℕ} (i : Fin p → I) : Opens X := ⨅ k, U (i k)

/-- Omitting an index makes the intersection larger. -/
theorem inter_le_omit {p : ℕ} (i : Fin (p + 1) → I) (j : Fin (p + 1)) :
    inter U i ≤ inter U (i ∘ j.succAbove) := by
  refine le_iInf fun k => ?_
  exact iInf_le (fun k => U (i k)) (j.succAbove k)

/-- The intersection is invariant under permuting the index tuple. -/
theorem inter_comp_perm {p : ℕ} (i : Fin p → I) (e : Equiv.Perm (Fin p)) :
    inter U (i ∘ e) = inter U i := by
  change (⨅ k, U (i (e k))) = ⨅ k, U (i k)
  exact e.iInf_comp (g := fun k => U (i k))

/-! ## The (full) Čech complex -/

/-- A degree-`p` Čech cochain: a section of `ℱ` on every `(p+1)`-fold intersection,
indexed by all tuples `i : Fin (p+1) → I`. As a product of abelian groups it is itself an
abelian group. -/
def Cochain (p : ℕ) : Type _ := (i : Fin (p + 1) → I) → (ℱ.obj (op (inter U i)) : Type _)

/-- Čech cochains form an abelian group under pointwise operations. -/
instance (p : ℕ) : AddCommGroup (Cochain U ℱ p) := by
  unfold Cochain; infer_instance

/-- Addition of Čech cochains is pointwise. -/
@[simp] theorem Cochain.add_apply {p : ℕ} (s t : Cochain U ℱ p) (i : Fin (p + 1) → I) :
    (s + t) i = s i + t i := rfl

/-- The zero Čech cochain vanishes at every tuple. -/
@[simp] theorem Cochain.zero_apply {p : ℕ} (i : Fin (p + 1) → I) :
    (0 : Cochain U ℱ p) i = 0 := rfl

/-- Negation of Čech cochains is pointwise. -/
@[simp] theorem Cochain.neg_apply {p : ℕ} (s : Cochain U ℱ p) (i : Fin (p + 1) → I) :
    (-s) i = -(s i) := rfl

/-- Restriction map `ℱ(V) → ℱ(W)` for `W ≤ V`, as a group homomorphism on sections. -/
def restr {V W : Opens X} (h : W ≤ V) : (ℱ.obj (op V) : Type _) →+ (ℱ.obj (op W) : Type _) :=
  (ℱ.map (homOfLE h).op).hom

/-- Restriction is functorial: restricting along `W ≤ V` then `Z ≤ W` equals restricting
along `Z ≤ V`. (Both are `ℱ.map` of the unique morphism `Z ⟶ V` in the poset `Opens X`.)
This is the key compatibility used to compose face restrictions when proving `d ∘ d = 0`. -/
theorem restr_restr {V W Z : Opens X} (h1 : W ≤ V) (h2 : Z ≤ W) (x : (ℱ.obj (op V) : Type _)) :
    restr ℱ h2 (restr ℱ h1 x) = restr ℱ (h2.trans h1) x := by
  unfold restr
  rw [← CategoryTheory.comp_apply, ← Functor.map_comp, ← op_comp]
  rfl

/-- The Čech differential `d : Č^p → Č^{p+1}` of Definition 1, as a group homomorphism:
`d(s)_{i_0…i_{p+1}} = ∑_{j=0}^{p+1} (-1)^j s_{i_0…î_j…i_{p+1}}|_{U_{i_0…i_{p+1}}}`. -/
def cechD (p : ℕ) : Cochain U ℱ p →+ Cochain U ℱ (p + 1) where
  toFun s := fun i =>
    ∑ j : Fin (p + 2),
      ((-1 : ℤ) ^ (j : ℕ)) • restr ℱ (inter_le_omit U i j) (s (i ∘ j.succAbove))
  map_zero' := by
    funext i
    rw [Cochain.zero_apply]
    refine Finset.sum_eq_zero fun j _ => ?_
    rw [Cochain.zero_apply, map_zero, smul_zero]
  map_add' s t := by
    funext i
    rw [Cochain.add_apply, ← Finset.sum_add_distrib]
    refine Finset.sum_congr rfl fun j _ => ?_
    rw [Cochain.add_apply, map_add, smul_add]

/-! ## The alternating Čech complex -/

/-- The canonical identification `ℱ(U_i) → ℱ(U_{i ∘ σ})` for a permutation `σ`,
coming from the equality of opens `U_{i ∘ σ} = U_i`. -/
def permIso {p : ℕ} (i : Fin (p + 1) → I) (σ : Equiv.Perm (Fin (p + 1))) :
    (ℱ.obj (op (inter U i)) : Type _) →+ (ℱ.obj (op (inter U (i ∘ σ))) : Type _) :=
  (ℱ.map (eqToHom (by rw [inter_comp_perm U i σ])).op).hom

/-- `permIso` for the identity permutation is the identity map. -/
theorem permIso_one {p : ℕ} (i : Fin (p + 1) → I) (x : (ℱ.obj (op (inter U i)) : Type _)) :
    permIso U ℱ i (1 : Equiv.Perm (Fin (p+1))) x = x := by
  unfold permIso
  have h : (eqToHom (show inter U (i ∘ (1 : Equiv.Perm (Fin (p+1)))) = inter U i by
      rw [inter_comp_perm])).op = 𝟙 _ := by
    rw [← op_id]; congr 1
  rw [h]
  simp

/-- `permIso` is compatible with composition of permutations. -/
theorem permIso_comp {p : ℕ} (i : Fin (p + 1) → I) (σ τ : Equiv.Perm (Fin (p + 1)))
    (x : (ℱ.obj (op (inter U i)) : Type _)) :
    permIso U ℱ (i ∘ σ) τ (permIso U ℱ i σ x) = permIso U ℱ i (σ * τ) x := by
  unfold permIso
  rw [← CategoryTheory.comp_apply, ← Functor.map_comp,
    ← op_comp, eqToHom_trans]
  congr 1

/-- Transport along an equality of opens is a restriction map. -/
private theorem map_eqToHom_op_apply {V W : Opens X} (h : W = V) (x : (ℱ.obj (op V) : Type _)) :
    ℱ.map (eqToHom h).op x = restr ℱ h.le x := rfl

/-- `permIso` is a restriction map. -/
private theorem permIso_apply {p : ℕ} (i : Fin (p + 1) → I) (σ : Equiv.Perm (Fin (p + 1)))
    (x : (ℱ.obj (op (inter U i)) : Type _)) :
    permIso U ℱ i σ x = restr ℱ (inter_comp_perm U i σ).le x := rfl

/-- Restricted sections agree along equal indices, whatever the restriction proofs. -/
private theorem restr_congr {α : Type*} (F : α → Opens X)
    (x : (a : α) → (ℱ.obj (op (F a)) : Type _))
    {a b : α} (hab : a = b) {W : Opens X} (h1 : W ≤ F a) (h2 : W ≤ F b) :
    restr ℱ h1 (x a) = restr ℱ h2 (x b) := by
  subst hab
  rfl

/-- The two defining conditions of an alternating cochain (Definition 2): it vanishes on
tuples with a repeated index, and swapping two *distinct* positions `a ≠ b` of the index
tuple negates the value (after the canonical identification `U_{i ∘ swap a b} = U_i`). -/
def IsAlternating {p : ℕ} (s : Cochain U ℱ p) : Prop :=
  (∀ i : Fin (p + 1) → I, ¬ Function.Injective i → s i = 0) ∧
  (∀ (i : Fin (p + 1) → I) (a b : Fin (p + 1)), a ≠ b →
      s (i ∘ Equiv.swap a b) = - permIso U ℱ i (Equiv.swap a b) (s i))

/-- The alternating cochains form a subgroup `Č_alt^p ⊆ Č^p`. -/
@[stacks 01FG "the group `Č_alt^p(𝒰, ℱ)` of alternating cochains"]
def alternatingSubgroup (p : ℕ) : AddSubgroup (Cochain U ℱ p) where
  carrier := {s | IsAlternating U ℱ s}
  zero_mem' := by
    refine ⟨fun i _ => rfl, fun i a b _ => ?_⟩
    rw [Cochain.zero_apply, Cochain.zero_apply, map_zero, neg_zero]
  add_mem' {s t} hs ht := by
    refine ⟨fun i hi => by rw [Cochain.add_apply, hs.1 i hi, ht.1 i hi, add_zero],
      fun i a b hab => ?_⟩
    rw [Cochain.add_apply, hs.2 i a b hab, ht.2 i a b hab, Cochain.add_apply, map_add]
    abel
  neg_mem' {s} hs := by
    refine ⟨fun i hi => by rw [Cochain.neg_apply, hs.1 i hi, neg_zero],
      fun i a b hab => ?_⟩
    rw [Cochain.neg_apply, hs.2 i a b hab, Cochain.neg_apply, map_neg]

/-! ## The ordered Čech complex -/

variable [LinearOrder I]

/-- A strictly increasing tuple of indices. -/
abbrev OrdIndex (p : ℕ) : Type _ := {i : Fin (p + 1) → I // StrictMono i}

/-- A degree-`p` ordered Čech cochain (Definition 3): a section of `ℱ` on every
`(p+1)`-fold intersection coming from a strictly increasing tuple. -/
def OrdCochain (p : ℕ) : Type _ :=
  (i : OrdIndex (I := I) p) → (ℱ.obj (op (inter U i.1)) : Type _)

/-- Ordered Čech cochains form an abelian group under pointwise operations. -/
instance (p : ℕ) : AddCommGroup (OrdCochain U ℱ p) := by
  unfold OrdCochain; infer_instance

/-- Addition of ordered Čech cochains is pointwise. -/
@[simp] theorem OrdCochain.add_apply {p : ℕ} (s t : OrdCochain U ℱ p) (i : OrdIndex (I := I) p) :
    (s + t) i = s i + t i := rfl

/-- The zero ordered Čech cochain vanishes at every strictly increasing tuple. -/
@[simp] theorem OrdCochain.zero_apply {p : ℕ} (i : OrdIndex (I := I) p) :
    (0 : OrdCochain U ℱ p) i = 0 := rfl

/-- Negation of ordered Čech cochains is pointwise. -/
@[simp] theorem OrdCochain.neg_apply {p : ℕ} (s : OrdCochain U ℱ p) (i : OrdIndex (I := I) p) :
    (-s) i = -(s i) := rfl

/-- Omitting an index from a strictly increasing tuple yields a strictly increasing
tuple. -/
theorem strictMono_omit {p : ℕ} {i : Fin (p + 1) → I} (hi : StrictMono i)
    (j : Fin (p + 1)) : StrictMono (i ∘ j.succAbove) :=
  hi.comp (Fin.strictMono_succAbove j)

/-- The ordered Čech differential `d : Č_ord^p → Č_ord^{p+1}` of Definition 3, as a group
homomorphism. -/
def ordD (p : ℕ) : OrdCochain U ℱ p →+ OrdCochain U ℱ (p + 1) where
  toFun s := fun i =>
    ∑ j : Fin (p + 2),
      ((-1 : ℤ) ^ (j : ℕ)) •
        restr ℱ (inter_le_omit U i.1 j) (s ⟨i.1 ∘ j.succAbove, strictMono_omit i.2 j⟩)
  map_zero' := by
    funext i
    rw [OrdCochain.zero_apply]
    refine Finset.sum_eq_zero fun j _ => ?_
    rw [OrdCochain.zero_apply, map_zero, smul_zero]
  map_add' s t := by
    funext i
    rw [OrdCochain.add_apply, ← Finset.sum_add_distrib]
    refine Finset.sum_congr rfl fun j _ => ?_
    rw [OrdCochain.add_apply, map_add, smul_add]

/-! ## The comparison map `c` -/

/-- For an injective tuple `i`, sorting it gives a strictly increasing tuple. -/
theorem strictMono_sort {p : ℕ} (i : Fin (p + 1) → I) (hi : Function.Injective i) :
    StrictMono (i ∘ (Tuple.sort i)) :=
  (Tuple.monotone_sort i).strictMono_of_injective (hi.comp (Tuple.sort i).injective)

/-- The comparison map `c : Č_ord^p → Č^p` (Definition 4), as a group homomorphism.  On a
tuple `i` it returns `0` if `i` has a repeated index, and otherwise `sgn(σ) · s` evaluated
at the sorted tuple, where `σ = Tuple.sort i` is the permutation arranging the indices in
increasing order.  The value `s ⟨sorted i⟩ ∈ ℱ(U_{sorted i})` is transported to `ℱ(U_i)`
along the equality of opens `U_i = U_{sorted i}`. -/
noncomputable def c (p : ℕ) : OrdCochain U ℱ p →+ Cochain U ℱ p where
  toFun s := fun i =>
    if hi : Function.Injective i then
      (Equiv.Perm.sign (Tuple.sort i) : ℤ) •
        ℱ.map (eqToHom (by rw [inter_comp_perm U i (Tuple.sort i)])).op
          (s ⟨i ∘ (Tuple.sort i), strictMono_sort i hi⟩)
    else 0
  map_zero' := by
    funext i
    rw [Cochain.zero_apply]
    by_cases hi : Function.Injective i
    · simp only [dite_eq_left hi, OrdCochain.zero_apply, map_zero, smul_zero]
    · simp only [dite_eq_right hi]
  map_add' s t := by
    funext i
    rw [Cochain.add_apply]
    by_cases hi : Function.Injective i
    · simp only [dite_eq_left hi, OrdCochain.add_apply, map_add, smul_add]
    · simp only [dite_eq_right hi, add_zero]

/-- The projection `π : Č^p → Č_ord^p` restricting a cochain to strictly increasing
tuples (the candidate inverse to `c`), as a group homomorphism. -/
def pi (p : ℕ) : Cochain U ℱ p →+ OrdCochain U ℱ p where
  toFun t := fun i => t i.1
  map_zero' := by funext i; rfl
  map_add' s t := by funext i; rfl

/-- Transport of a section along equal ordered tuples. -/
theorem map_eqToHom_ordIndex {p : ℕ} (s : OrdCochain U ℱ p) (j j' : OrdIndex (I := I) p)
    (h : j = j') (e : inter U j.1 = inter U j'.1) :
    ℱ.map (eqToHom (by rw [e])).op (s j) = s j' := by
  subst h
  simp

/-- Value of `c s` on an injective tuple. -/
theorem c_apply_injective {p : ℕ} (s : OrdCochain U ℱ p) (i : Fin (p + 1) → I)
    (hi : Function.Injective i) :
    (c U ℱ p s) i =
      (Equiv.Perm.sign (Tuple.sort i) : ℤ) •
        ℱ.map (eqToHom (by rw [inter_comp_perm U i (Tuple.sort i)])).op
          (s ⟨i ∘ (Tuple.sort i), strictMono_sort i hi⟩) := by
  simp only [c, AddMonoidHom.coe_mk, ZeroHom.coe_mk, dite_eq_left hi]

/-- Value of `c s` on a non-injective tuple. -/
theorem c_apply_not_injective {p : ℕ} (s : OrdCochain U ℱ p) (i : Fin (p + 1) → I)
    (hi : ¬ Function.Injective i) :
    (c U ℱ p s) i = 0 := by
  simp only [c, AddMonoidHom.coe_mk, ZeroHom.coe_mk, dite_eq_right hi]

/-- Transport of equal sections along (proof-irrelevant) open equalities. -/
theorem sect_transport {p : ℕ} (s : OrdCochain U ℱ p) (A : Opens X)
    (j j' : OrdIndex (I := I) p) (h : j = j')
    (e : A = inter U j.1) (e' : A = inter U j'.1) :
    ℱ.map (eqToHom e).op (s j) = ℱ.map (eqToHom e').op (s j') := by
  subst h
  rfl

/-! ## Main statements (Stacks Tag 01FJ) -/

/-- (2) The image of `c` lies in the alternating subcomplex. -/
theorem c_isAlternating (p : ℕ) (s : OrdCochain U ℱ p) :
    IsAlternating U ℱ (c U ℱ p s) := by
  refine ⟨c_apply_not_injective U ℱ s, fun i a b hab => ?_⟩
  by_cases hinj : Function.Injective i
  · have hswap : Function.Injective (i ∘ Equiv.swap a b) := hinj.comp (Equiv.injective _)
    set σ := Tuple.sort i
    set σ' := Tuple.sort (i ∘ Equiv.swap a b)
    have hcomp : (i ∘ Equiv.swap a b) ∘ σ' = i ∘ σ := Tuple.comp_perm_comp_sort_eq_comp_sort
    have hsign : (Equiv.Perm.sign σ' : ℤ) = -(Equiv.Perm.sign σ : ℤ) := by
      have h : Equiv.swap a b * σ' = σ := Equiv.ext fun k => hinj (congrFun hcomp k)
      rw [← h, map_mul, Equiv.Perm.sign_swap hab]
      push_cast
      ring
    have hwmono : StrictMono (i ∘ σ) := strictMono_sort i hinj
    have eC : inter U (i ∘ Equiv.swap a b) = inter U (i ∘ σ) := by
      rw [← hcomp]
      exact (inter_comp_perm U (i ∘ Equiv.swap a b) σ').symm
    have hwmono' : StrictMono ((i ∘ Equiv.swap a b) ∘ σ') := strictMono_sort _ hswap
    have hjeq : (⟨(i ∘ Equiv.swap a b) ∘ σ', hwmono'⟩ : OrdIndex (I := I) p)
        = ⟨i ∘ σ, hwmono⟩ := Subtype.ext hcomp
    rw [c_apply_injective U ℱ s _ hswap, c_apply_injective U ℱ s i hinj]
    have hLHS :
        (Equiv.Perm.sign σ' : ℤ) •
          ℱ.map (eqToHom (by rw [inter_comp_perm U (i ∘ Equiv.swap a b) σ'])).op
          (s ⟨(i ∘ Equiv.swap a b) ∘ σ', hwmono'⟩)
          = (-(Equiv.Perm.sign σ : ℤ)) • ℱ.map (eqToHom eC).op (s ⟨i ∘ σ, hwmono⟩) := by
      rw [hsign]
      congr 1
      exact sect_transport U ℱ s (inter U (i ∘ Equiv.swap a b))
        ⟨(i ∘ Equiv.swap a b) ∘ σ', hwmono'⟩ ⟨i ∘ σ, hwmono⟩ hjeq _ _
    have hRHS :
        -(permIso U ℱ i (Equiv.swap a b))
          ((Equiv.Perm.sign σ : ℤ) •
            ℱ.map (eqToHom (by rw [inter_comp_perm U i σ])).op (s ⟨i ∘ σ, hwmono⟩))
          = (-(Equiv.Perm.sign σ : ℤ)) • ℱ.map (eqToHom eC).op (s ⟨i ∘ σ, hwmono⟩) := by
      rw [map_zsmul, neg_smul, permIso_apply, map_eqToHom_op_apply, map_eqToHom_op_apply,
        restr_restr]
    change (Equiv.Perm.sign σ' : ℤ) •
          ℱ.map (eqToHom (by rw [inter_comp_perm U (i ∘ Equiv.swap a b) σ'])).op
          (s ⟨(i ∘ Equiv.swap a b) ∘ σ', hwmono'⟩)
        = -(permIso U ℱ i (Equiv.swap a b))
          ((Equiv.Perm.sign σ : ℤ) •
            ℱ.map (eqToHom (by rw [inter_comp_perm U i σ])).op (s ⟨i ∘ σ, hwmono⟩))
    rw [hLHS, hRHS]
  · have hswap : ¬ Function.Injective (i ∘ Equiv.swap a b) := fun h =>
      hinj (h.of_comp_right (Equiv.surjective _))
    rw [c_apply_not_injective U ℱ s _ hswap, c_apply_not_injective U ℱ s i hinj, map_zero,
      neg_zero]

/-- (3a) `π` is a left inverse of `c`: `π (c s) = s`. -/
theorem pi_c (p : ℕ) (s : OrdCochain U ℱ p) : pi U ℱ p (c U ℱ p s) = s := by
  funext i
  obtain ⟨i, hi⟩ := i
  have hinj : Function.Injective i := hi.injective
  have hsort : Tuple.sort i = Equiv.refl _ :=
    Tuple.sort_eq_refl_iff_monotone.2 hi.monotone
  change (c U ℱ p s) i = s ⟨i, hi⟩
  rw [c_apply_injective U ℱ s i hinj]
  have hsign : (Equiv.Perm.sign (Tuple.sort i) : ℤ) = 1 := by
    simp [hsort]
  rw [hsign, one_smul]
  have hjj : (⟨i ∘ (Tuple.sort i), strictMono_sort i hinj⟩ : OrdIndex (I := I) p)
      = ⟨i, hi⟩ := by
    apply Subtype.ext
    change i ∘ (Tuple.sort i) = i
    rw [hsort]
    rfl
  exact map_eqToHom_ordIndex U ℱ s _ _ hjj (by rw [hjj])

omit [LinearOrder I] in
/-- **Key sub-lemma (generalized swap law).** For an alternating cochain `s`, applying any
permutation `σ` to the index tuple multiplies the value by `sgn σ` (after the canonical
`permIso` transport).  This is the iteration of the single-swap clause `IsAlternating.2`
over a factorization of `σ` into transpositions.

INFORMAL PROOF.  Induct on `σ` using the generation of `Equiv.Perm (Fin (p+1))` by
transpositions (`Equiv.Perm.swap_induction_on'` / `Equiv.Perm.swap_induction_on`).
• Base case `σ = 1`: `sign 1 = 1`, `i ∘ 1 = i`, and `permIso _ 1` is the identity
  (`permIso_one`), so both sides equal `s i`.
• Inductive step `σ = τ * swap a b` (with `a ≠ b`): then
  `s (i ∘ (τ * swap a b)) = s ((i ∘ τ) ∘ swap a b)` (composition reindexing)
  `= - permIso (i ∘ τ) (swap a b) (s (i ∘ τ))`  (by `ht.2` applied to the tuple `i ∘ τ`)
  `= - permIso (i ∘ τ) (swap a b) (sign τ • permIso i τ (s i))`  (induction hypothesis)
  `= sign (τ * swap a b) • permIso i (τ * swap a b) (s i)`,
  using `map_zsmul`, `permIso_comp` (to merge `permIso (i∘τ) (swap a b) ∘ permIso i τ
  = permIso i (τ * swap a b)`), `sign_mul`, `sign_swap hab`, and the arithmetic
  `-(sign τ) = sign τ * sign (swap a b) = sign τ * (-1)`.

FORMALIZATION STRATEGY.  `induction σ using Equiv.Perm.swap_induction_on'`; close the base
case with `permIso_one`, `Equiv.Perm.sign_one`, `one_smul`, and `i ∘ 1 = i`; in the step,
rewrite with `ht.2`, the IH, `map_zsmul`/`map_neg`, `permIso_comp`, `map_mul`,
`Equiv.Perm.sign_swap`, and finish the sign bookkeeping with `push_cast; ring`.  All the
needed helpers (`permIso_one`, `permIso_comp`) are already proved above. -/
theorem alt_perm {p : ℕ} (s : Cochain U ℱ p) (hs : IsAlternating U ℱ s)
    (i : Fin (p + 1) → I) (σ : Equiv.Perm (Fin (p + 1))) :
    s (i ∘ σ) = (Equiv.Perm.sign σ : ℤ) • permIso U ℱ i σ (s i) := by
  -- SANITY CHECK PASSED
  induction σ using Equiv.Perm.swap_induction_on' with
  | one =>
    rw [permIso_one, Equiv.Perm.sign_one, Units.val_one, one_smul]
    -- both sides reduce to `s i`; `i ∘ ⇑1` is defeq to `i`
    simp only [Equiv.Perm.coe_one, Function.comp_id]
  | mul_swap f a b hab ih =>
    have hsign : (Equiv.Perm.sign (f * Equiv.swap a b) : ℤ)
        = -(Equiv.Perm.sign f : ℤ) := by
      rw [map_mul, Equiv.Perm.sign_swap hab]
      push_cast
      ring
    calc s (i ∘ ⇑(f * Equiv.swap a b))
        = s ((i ∘ ⇑f) ∘ ⇑(Equiv.swap a b)) := rfl
      _ = -(permIso U ℱ (i ∘ ⇑f) (Equiv.swap a b)) (s (i ∘ ⇑f)) :=
          hs.2 (i ∘ ⇑f) a b hab
      _ = -(permIso U ℱ (i ∘ ⇑f) (Equiv.swap a b))
            ((Equiv.Perm.sign f : ℤ) • permIso U ℱ i f (s i)) := by rw [ih]
      _ = -((Equiv.Perm.sign f : ℤ) •
            (permIso U ℱ (i ∘ ⇑f) (Equiv.swap a b)) (permIso U ℱ i f (s i))) := by
            rw [map_zsmul]
      _ = -((Equiv.Perm.sign f : ℤ) • permIso U ℱ i (f * Equiv.swap a b) (s i)) := by
            rw [permIso_comp]
      _ = (Equiv.Perm.sign (f * Equiv.swap a b) : ℤ) •
            permIso U ℱ i (f * Equiv.swap a b) (s i) := by
            rw [hsign, neg_smul]

/-- (3b) On the alternating subcomplex, `c` is a left inverse of `π`: if `t` is
alternating then `c (π t) = t`. -/
theorem c_pi_of_isAlternating (p : ℕ) (t : Cochain U ℱ p) (ht : IsAlternating U ℱ t) :
    c U ℱ p (pi U ℱ p t) = t := by
  -- SANITY CHECK PASSED
  /-
  INFORMAL PROOF.  Componentwise at a tuple `i`.
  • If `i` is not injective, `c (π t)_i = 0` (`c_apply_not_injective`) and `t_i = 0`
    (`ht.1`), so both sides agree.
  • If `i` is injective, let `σ = Tuple.sort i`.  By `c_apply_injective` and the definition
    of `π` (which forgets the StrictMono witness, so `(π t) ⟨i ∘ σ, _⟩ = t (i ∘ σ)`),
      `c (π t)_i = sgn σ • map(eqToHom) (t (i ∘ σ))`.
    By the key sub-lemma `alt_perm`, `t (i ∘ σ) = sgn σ • permIso i σ (t i)`.  Substituting
    and using `sgn σ * sgn σ = 1` (signs are `±1`) together with the fact that
    `map(eqToHom_{U_i = U_{i∘σ}}) ∘ permIso i σ = id` (the two `eqToHom` transports along
    `inter U (i∘σ) = inter U i` and its reverse compose to the identity, by
    `Functor.map_comp`/`eqToHom_trans`/`eqToHom_refl`), we get `c (π t)_i = t_i`.

  This reduces the whole lemma to `alt_perm` plus the elementary transport cancellation.
  -/
  funext i
  by_cases hi : Function.Injective i
  · rw [c_apply_injective U ℱ (pi U ℱ p t) i hi]
    -- `(pi t) ⟨i ∘ sort i, _⟩` is definitionally `t (i ∘ sort i)`.
    change (Equiv.Perm.sign (Tuple.sort i) : ℤ) •
        ℱ.map (eqToHom (by rw [inter_comp_perm U i (Tuple.sort i)])).op
          (t (i ∘ (Tuple.sort i))) = t i
    rw [alt_perm U ℱ t ht i (Tuple.sort i), map_zsmul, smul_smul,
      show (↑(Equiv.Perm.sign (Tuple.sort i)) * ↑(Equiv.Perm.sign (Tuple.sort i)) : ℤ) = 1 by
        simp,
      one_smul]
    rw [permIso_apply, map_eqToHom_op_apply, restr_restr]
    simp [restr]
  · rw [c_apply_not_injective U ℱ (pi U ℱ p t) i hi, (ht.1 i hi).symm]

/-- (3) **[Stacks, Tag 01FJ], the degreewise clause.** In every degree, `c` corestricted to the
alternating subgroup is an isomorphism of abelian groups `Č_ord^p ≃+ Č_alt^p`, with inverse the
projection `π`.

This is the degreewise statement only: it says nothing about the differentials.  That `c`
commutes with them is `c_chainMap`, and the two clauses are assembled into the isomorphism of
cochain complexes the source asserts by `Stacks.Cech.orderedIsoAlternatingCechComplex`. -/
@[stacks 01FJ "the degreewise isomorphism"]
noncomputable def cAddEquiv (p : ℕ) : OrdCochain U ℱ p ≃+ alternatingSubgroup U ℱ p where
  toFun s := ⟨c U ℱ p s, c_isAlternating U ℱ p s⟩
  invFun t := pi U ℱ p t.1
  left_inv s := pi_c U ℱ p s
  right_inv t := Subtype.ext (c_pi_of_isAlternating U ℱ p t.1 t.2)
  map_add' s t := Subtype.ext (map_add (c U ℱ p) s t)

/-! ## Complex / subcomplex structure -/

/-- Sign bookkeeping for omitting two positions in either order. -/
private theorem sign_succAbove_predAbove (n : ℕ) (k : Fin (n + 2)) (j : Fin (n + 1)) :
    ((-1 : ℤ) ^ (k : ℕ)) * ((-1 : ℤ) ^ (j : ℕ))
      = -(((-1 : ℤ) ^ ((k.succAbove j : Fin (n + 2)) : ℕ))
            * ((-1 : ℤ) ^ ((j.predAbove k : Fin (n + 1)) : ℕ))) := by
  rw [← pow_add, ← pow_add]
  rcases lt_or_ge j.castSucc k with h | h
  · rw [Fin.succAbove_of_castSucc_lt k j h, Fin.predAbove_of_castSucc_lt j k h,
      Fin.val_castSucc, Fin.val_pred]
    have hk : 0 < (k : ℕ) := by
      have h0 : j.castSucc.val < k.val := h
      omega
    have heq : (k : ℕ) + (j : ℕ) = ((j : ℕ) + ((k : ℕ) - 1)) + 1 := by omega
    rw [heq, pow_succ]; ring
  · rw [Fin.succAbove_of_le_castSucc k j h, Fin.predAbove_of_le_castSucc j k h,
      Fin.val_succ, Fin.coe_castPred]
    have heq : (j : ℕ) + 1 + (k : ℕ) = ((k : ℕ) + (j : ℕ)) + 1 := by omega
    rw [heq, pow_succ]; ring

/-- The double sum of a family invariant under `(k, j) ↦ (k.succAbove j, j.predAbove k)`,
weighted by the signs `(-1)^(k + j)`, vanishes: the involution pairs up opposite terms. -/
private theorem sum_sign_smul_eq_zero {G : Type*} [AddCommGroup G] {n : ℕ}
    (g : Fin (n + 3) → Fin (n + 2) → G)
    (h : ∀ k j, g (k.succAbove j) (j.predAbove k) = g k j) :
    ∑ k : Fin (n + 3), ∑ j : Fin (n + 2),
      (((-1 : ℤ) ^ (k : ℕ)) * ((-1 : ℤ) ^ (j : ℕ))) • g k j = 0 := by
  rw [Finset.sum_sigma' (Finset.univ : Finset (Fin (n + 3)))
    fun _ => (Finset.univ : Finset (Fin (n + 2)))]
  apply Finset.sum_involution
    (g := fun (x : (_ : Fin (n + 3)) × Fin (n + 2)) _ =>
      (⟨x.fst.succAbove x.snd, x.snd.predAbove x.fst⟩ : (_ : Fin (n + 3)) × Fin (n + 2)))
  · rintro ⟨k, j⟩ _
    rw [sign_succAbove_predAbove (n + 1) k j, neg_smul, h]
    abel
  · rintro ⟨k, j⟩ _ _ h
    exact Fin.succAbove_ne k j (congrArg Sigma.fst h)
  · exact fun _ _ => Finset.mem_univ _
  · rintro ⟨k, j⟩ _
    refine Sigma.ext (Fin.succAbove_succAbove_predAbove k j) ?_
    rw [Fin.succAbove_succAbove_predAbove k j]
    exact heq_of_eq (Fin.predAbove_predAbove_succAbove k j)

omit [LinearOrder I] in
/-- The full Čech complex is a complex: `d ∘ d = 0`. -/
theorem cechD_cechD (p : ℕ) (s : Cochain U ℱ p) :
    cechD U ℱ (p + 1) (cechD U ℱ p s) = 0 := by
  funext i
  rw [Cochain.zero_apply]
  change (∑ k : Fin (p + 3),
      ((-1 : ℤ) ^ (k : ℕ)) • restr ℱ (inter_le_omit U i k)
        ((cechD U ℱ p s) (i ∘ k.succAbove))) = 0
  -- Unfold the inner differential and merge the two nested restrictions.
  have step1 : ∀ k : Fin (p+3),
      ((-1 : ℤ) ^ (k : ℕ)) • restr ℱ (inter_le_omit U i k) ((cechD U ℱ p s) (i ∘ k.succAbove))
      = ∑ j : Fin (p+2),
          (((-1:ℤ)^(k:ℕ)) * ((-1:ℤ)^(j:ℕ))) •
            restr ℱ ((inter_le_omit U i k).trans (inter_le_omit U (i ∘ k.succAbove) j))
              (s ((i ∘ k.succAbove) ∘ j.succAbove)) := by
    intro k
    change ((-1 : ℤ) ^ (k : ℕ)) • restr ℱ (inter_le_omit U i k)
        (∑ j : Fin (p + 2),
          ((-1 : ℤ) ^ (j : ℕ)) • restr ℱ (inter_le_omit U (i ∘ k.succAbove) j)
            (s ((i ∘ k.succAbove) ∘ j.succAbove))) = _
    rw [map_sum, Finset.smul_sum]
    refine Finset.sum_congr rfl fun j _ => ?_
    rw [map_zsmul, restr_restr, smul_smul]
  rw [Finset.sum_congr rfl (fun k _ => step1 k)]
  refine sum_sign_smul_eq_zero
    (fun k j => restr ℱ ((inter_le_omit U i k).trans (inter_le_omit U (i ∘ k.succAbove) j))
      (s ((i ∘ k.succAbove) ∘ j.succAbove))) fun k j => ?_
  exact restr_congr ℱ (inter U) s
    (funext fun x => congrArg i (Fin.succAbove_succAbove_succAbove_predAbove k j x)) _ _

/-- The ordered Čech complex is a complex: `d ∘ d = 0`. -/
theorem ordD_ordD (p : ℕ) (s : OrdCochain U ℱ p) :
    ordD U ℱ (p + 1) (ordD U ℱ p s) = 0 := by
  funext i
  rw [OrdCochain.zero_apply]
  change (∑ k : Fin (p + 3),
      ((-1 : ℤ) ^ (k : ℕ)) • restr ℱ (inter_le_omit U i.1 k)
        ((ordD U ℱ p s) ⟨i.1 ∘ k.succAbove, strictMono_omit i.2 k⟩)) = 0
  -- Unfold the inner differential and merge the two nested restrictions.
  have step1 : ∀ k : Fin (p+3),
      ((-1 : ℤ) ^ (k : ℕ)) • restr ℱ (inter_le_omit U i.1 k)
        ((ordD U ℱ p s) ⟨i.1 ∘ k.succAbove, strictMono_omit i.2 k⟩)
      = ∑ j : Fin (p+2),
          (((-1:ℤ)^(k:ℕ)) * ((-1:ℤ)^(j:ℕ))) •
            restr ℱ ((inter_le_omit U i.1 k).trans
                (inter_le_omit U (i.1 ∘ k.succAbove) j))
              (s ⟨(i.1 ∘ k.succAbove) ∘ j.succAbove,
                strictMono_omit (strictMono_omit i.2 k) j⟩) := by
    intro k
    change ((-1 : ℤ) ^ (k : ℕ)) • restr ℱ (inter_le_omit U i.1 k)
        (∑ j : Fin (p + 2),
          ((-1 : ℤ) ^ (j : ℕ)) • restr ℱ (inter_le_omit U (i.1 ∘ k.succAbove) j)
            (s ⟨(i.1 ∘ k.succAbove) ∘ j.succAbove,
              strictMono_omit (strictMono_omit i.2 k) j⟩)) = _
    rw [map_sum, Finset.smul_sum]
    refine Finset.sum_congr rfl fun j _ => ?_
    rw [map_zsmul, restr_restr, smul_smul]
  rw [Finset.sum_congr rfl (fun k _ => step1 k)]
  refine sum_sign_smul_eq_zero
    (fun k j => restr ℱ ((inter_le_omit U i.1 k).trans
        (inter_le_omit U (i.1 ∘ k.succAbove) j))
      (s ⟨(i.1 ∘ k.succAbove) ∘ j.succAbove,
        strictMono_omit (strictMono_omit i.2 k) j⟩)) fun k j => ?_
  exact restr_congr ℱ (fun i : OrdIndex (I := I) p => inter U i.1) s
    (a := ⟨(i.1 ∘ (k.succAbove j).succAbove) ∘ (j.predAbove k).succAbove,
      strictMono_omit (strictMono_omit i.2 _) _⟩)
    (b := ⟨(i.1 ∘ k.succAbove) ∘ j.succAbove, strictMono_omit (strictMono_omit i.2 k) j⟩)
    (Subtype.ext (funext fun x =>
      congrArg i.1 (Fin.succAbove_succAbove_succAbove_predAbove k j x))) _ _

/-- **Simplicial face-permutation helper_01fj.**  Pre-composing a permutation `w` of the
`p+2` positions with the `j`-th face map `j.succAbove` equals the `(w j)`-th face map
post-composed with an induced permutation `θ` of the remaining `p+1` positions; moreover
the signs match the simplicial bookkeeping `sgn w · (-1)^j = (-1)^{w j} · sgn θ`.

INFORMAL PROOF.  Take `θ = (w j).succAbove⁻¹ ∘ (w ∘ j.succAbove)` realized as a permutation
of `Fin (p+1)` (its image avoids `w j`, so it factors through `(w j).succAbove`).  Concretely
`θ` is built from `w` by deleting row `j` and column `w j`; the sign relation is the Laplace
expansion of `sgn w` along that row/column, i.e. `sgn w = (-1)^{j + w j} · sgn θ`, which
rearranges (mod 2) to `sgn w · (-1)^j = (-1)^{w j} · sgn θ`.  Build `θ` via
`Fin.cycleRange`/`Fin.sign_cycleRange` (`Fin.cycleRange_succAbove`,
`Fin.sign_cycleRange`) and finish the sign with a `castSucc`/`succ` case split as in the
`sign_lemma` of `cechD_cechD`. -/
lemma cechD_face_perm {p : ℕ} (w : Equiv.Perm (Fin (p + 2))) (j : Fin (p + 2)) :
    ∃ θ : Equiv.Perm (Fin (p + 1)),
      w ∘ j.succAbove = (w j).succAbove ∘ θ ∧
      (Equiv.Perm.sign w : ℤ) * ((-1 : ℤ) ^ (j : ℕ))
        = ((-1 : ℤ) ^ ((w j : Fin (p + 2)) : ℕ)) * (Equiv.Perm.sign θ : ℤ) := by
  -- SANITY CHECK PASSED (exhaustive `decide` for p=0,1,2; sign conventions confirmed)
  set σ : Equiv.Perm (Fin (p+2)) := (w j).cycleRange * w * (j.cycleRange)⁻¹ with hσ
  have h0 : σ 0 = 0 := by
    simp only [hσ, Equiv.Perm.mul_apply]
    rw [show ((j.cycleRange)⁻¹) 0 = j by
      rw [Equiv.Perm.inv_eq_iff_eq]; exact (Fin.cycleRange_self j).symm]
    rw [Fin.cycleRange_self (w j)]
  set θ : Equiv.Perm (Fin (p+1)) := (Equiv.Perm.decomposeFin σ).2 with hθ
  have hdecomp : Equiv.Perm.decomposeFin.symm (0, θ) = σ := by
    have h1 : (Equiv.Perm.decomposeFin σ).1 = (0 : Fin (p+2)) := by
      rw [show (Equiv.Perm.decomposeFin σ).1 = σ 0 by simp [Equiv.Perm.decomposeFin], h0]
    rw [hθ]
    conv_rhs => rw [← Equiv.symm_apply_apply Equiv.Perm.decomposeFin σ]
    congr 1
    rw [Prod.ext_iff]
    exact ⟨h1.symm, rfl⟩
  have hsucc : ∀ x : Fin (p+1), σ x.succ = (θ x).succ := by
    intro x
    rw [← hdecomp, Equiv.Perm.decomposeFin_symm_apply_succ]
    simp
  refine ⟨θ, ?_, ?_⟩
  · funext m
    simp only [Function.comp_apply]
    have key : (w j).cycleRange (w (j.succAbove m)) = (θ m).succ := by
      have : σ (m.succ) = (w j).cycleRange (w (j.succAbove m)) := by
        simp only [hσ, Equiv.Perm.mul_apply]
        congr 2
        rw [show ((j.cycleRange)⁻¹) m.succ = j.succAbove m by
          rw [Equiv.Perm.inv_eq_iff_eq]; exact (Fin.cycleRange_succAbove j m).symm]
      rw [← this, hsucc]
    exact (w j).cycleRange.injective (key.trans (Fin.cycleRange_succAbove (w j) (θ m)).symm)
  · have hs : Equiv.Perm.sign θ = Equiv.Perm.sign σ := by
      rw [← hdecomp]; simp
    have hsσ : Equiv.Perm.sign σ
        = (Equiv.Perm.sign (w j).cycleRange) * (Equiv.Perm.sign w)
            * (Equiv.Perm.sign (j.cycleRange)⁻¹) := by
      rw [hσ, Equiv.Perm.sign_mul, Equiv.Perm.sign_mul]
    rw [hs, hsσ]
    rw [Equiv.Perm.sign_inv, Fin.sign_cycleRange, Fin.sign_cycleRange]
    push_cast
    have hsq : ((-1 : ℤ) ^ ((w j : Fin (p+2)) : ℕ)) * ((-1 : ℤ) ^ ((w j : Fin (p+2)) : ℕ)) = 1 := by
      rw [← pow_add, ← two_mul, pow_mul]
      norm_num
    linear_combination (-((Equiv.Perm.sign w : ℤ) * (-1 : ℤ) ^ (j : ℕ))) * hsq

omit [LinearOrder I] in
/-- The differential `cechD` preserves the alternating subgroup, so the latter is a
subcomplex of the full Čech complex. -/
@[stacks 01FG "`d` maps `Č_alt^p` into `Č_alt^{p+1}`, the verification the source omits"]
theorem cechD_mem_alternating (p : ℕ) (s : Cochain U ℱ p) (hs : IsAlternating U ℱ s) :
    IsAlternating U ℱ (cechD U ℱ p s) := by
  -- Sign bookkeeping for a transposition `swap x y`, from the `cechD_face_perm` sign identity.
  have hscalar : ∀ {x y j j' : Fin (p + 2)} {θ : Equiv.Perm (Fin (p + 1))}, x ≠ y →
      (Equiv.Perm.sign (Equiv.swap x y) : ℤ) * ((-1 : ℤ) ^ (j : ℕ))
        = ((-1 : ℤ) ^ (j' : ℕ)) * (Equiv.Perm.sign θ : ℤ) →
      ((-1 : ℤ) ^ (j : ℕ)) * (Equiv.Perm.sign θ : ℤ) = -((-1 : ℤ) ^ (j' : ℕ)) := by
    intro x y j j' θ hxy h
    have hsq : (Equiv.Perm.sign θ : ℤ) * Equiv.Perm.sign θ = 1 := by simp
    rw [Equiv.Perm.sign_swap hxy] at h
    push_cast at h
    linear_combination (-(Equiv.Perm.sign θ : ℤ)) * h - ((-1 : ℤ) ^ (j' : ℕ)) * hsq
  refine ⟨fun i hi => ?_, fun i a b hab => ?_⟩
  · obtain ⟨a, b, hab_eq, hab⟩ := Function.not_injective_iff.mp hi
    have hzero : ∀ j : Fin (p + 2), j ≠ a → j ≠ b → s (i ∘ j.succAbove) = 0 := by
      intro j hja hjb
      obtain ⟨a', ha'⟩ := Fin.exists_succAbove_eq (Ne.symm hja)
      obtain ⟨b', hb'⟩ := Fin.exists_succAbove_eq (Ne.symm hjb)
      refine hs.1 _ fun hinj => hab ?_
      have hval : (i ∘ j.succAbove) a' = (i ∘ j.succAbove) b' := by
        simp only [Function.comp_apply, ha', hb']
        exact hab_eq
      rw [← ha', ← hb', hinj hval]
    have hcancel : ∀ x y : Fin (p + 2), i x = i y → x ≠ y →
        ((-1 : ℤ) ^ (x : ℕ)) • restr ℱ (inter_le_omit U i x) (s (i ∘ x.succAbove))
          + ((-1 : ℤ) ^ (y : ℕ)) • restr ℱ (inter_le_omit U i y) (s (i ∘ y.succAbove)) = 0 := by
      intro x y hxy hxyne
      have hiswap : i ∘ Equiv.swap x y = i := by
        funext m
        rcases eq_or_ne m x with rfl | hmx
        · simp [Equiv.swap_apply_left, hxy]
        · rcases eq_or_ne m y with rfl | hmy
          · simp [Equiv.swap_apply_right, hxy]
          · rw [Function.comp_apply, Equiv.swap_apply_of_ne_of_ne hmx hmy]
      obtain ⟨θ, hθcomp, hθsign⟩ := cechD_face_perm (Equiv.swap x y) x
      rw [Equiv.swap_apply_left] at hθcomp hθsign
      have harg : i ∘ x.succAbove = (i ∘ y.succAbove) ∘ θ :=
        calc i ∘ x.succAbove = (i ∘ Equiv.swap x y) ∘ x.succAbove := by rw [hiswap]
          _ = (i ∘ y.succAbove) ∘ θ := congrArg (i ∘ ·) hθcomp
      rw [restr_congr ℱ (inter U) s harg (inter_le_omit U i x)
          (le_trans (inter_le_omit U i x) (le_of_eq (by rw [harg]))),
        alt_perm U ℱ s hs (i ∘ y.succAbove) θ, map_zsmul, smul_smul,
        hscalar hxyne hθsign, neg_smul, permIso_apply, restr_restr, neg_add_cancel]
    change (∑ j : Fin (p + 2),
        ((-1 : ℤ) ^ (j : ℕ)) • restr ℱ (inter_le_omit U i j) (s (i ∘ j.succAbove))) = 0
    apply Finset.sum_involution (g := fun (j : Fin (p + 2)) _ => Equiv.swap a b j)
    · intro j _
      rcases eq_or_ne j a with rfl | hja
      · rw [Equiv.swap_apply_left]
        exact hcancel _ _ hab_eq hab
      · rcases eq_or_ne j b with rfl | hjb
        · rw [Equiv.swap_apply_right]
          exact hcancel _ _ hab_eq.symm hab.symm
        · rw [Equiv.swap_apply_of_ne_of_ne hja hjb,
            hzero j hja hjb, map_zero, smul_zero, add_zero]
    · intro j _ hfj
      contrapose! hfj
      have hja : j ≠ a := by
        rintro rfl
        rw [Equiv.swap_apply_left] at hfj
        exact hab hfj.symm
      have hjb : j ≠ b := by
        rintro rfl
        rw [Equiv.swap_apply_right] at hfj
        exact hab hfj
      rw [hzero j hja hjb, map_zero, smul_zero]
    · exact fun j _ => Finset.mem_univ _
    · intro j _
      simp
  · change (∑ j : Fin (p + 2),
        ((-1 : ℤ) ^ (j : ℕ)) • restr ℱ (inter_le_omit U (i ∘ Equiv.swap a b) j)
          (s ((i ∘ Equiv.swap a b) ∘ j.succAbove)))
      = - permIso U ℱ i (Equiv.swap a b)
          (∑ j : Fin (p + 2),
            ((-1 : ℤ) ^ (j : ℕ)) • restr ℱ (inter_le_omit U i j) (s (i ∘ j.succAbove)))
    rw [map_sum, ← Finset.sum_neg_distrib]
    have hRHS : ∀ k : Fin (p + 2),
        -(permIso U ℱ i (Equiv.swap a b))
            (((-1 : ℤ) ^ (k : ℕ)) • restr ℱ (inter_le_omit U i k) (s (i ∘ k.succAbove)))
        = ((-1 : ℤ) ^ (k : ℕ)) • -(restr ℱ
            (show inter U (i ∘ Equiv.swap a b) ≤ inter U (i ∘ k.succAbove) from
              le_trans (le_of_eq (inter_comp_perm U i (Equiv.swap a b))) (inter_le_omit U i k))
            (s (i ∘ k.succAbove))) := by
      intro k
      rw [map_zsmul, smul_neg, permIso_apply, restr_restr]
    rw [Finset.sum_congr rfl (fun k _ => hRHS k), ← Equiv.sum_comp (Equiv.swap a b)
      (fun k => ((-1 : ℤ) ^ (k : ℕ)) • -(restr ℱ
        (show inter U (i ∘ Equiv.swap a b) ≤ inter U (i ∘ k.succAbove) from
          le_trans (le_of_eq (inter_comp_perm U i (Equiv.swap a b))) (inter_le_omit U i k))
        (s (i ∘ k.succAbove))))]
    refine Finset.sum_congr rfl fun j _ => ?_
    obtain ⟨θ, hθcomp, hθsign⟩ := cechD_face_perm (Equiv.swap a b) j
    have harg : (i ∘ Equiv.swap a b) ∘ j.succAbove
        = (i ∘ ((Equiv.swap a b) j).succAbove) ∘ θ := congrArg (i ∘ ·) hθcomp
    rw [restr_congr ℱ (inter U) s harg (inter_le_omit U (i ∘ Equiv.swap a b) j)
        (le_trans (inter_le_omit U (i ∘ Equiv.swap a b) j) (le_of_eq (by rw [harg]))),
      alt_perm U ℱ s hs (i ∘ ((Equiv.swap a b) j).succAbove) θ, map_zsmul, smul_smul,
      hscalar hab hθsign, neg_smul, smul_neg, permIso_apply, restr_restr]

/-- `c` is injective, since `π` is a left inverse (`pi_c`). -/
theorem c_injective {p : ℕ} : Function.Injective (c U ℱ p) :=
  Function.LeftInverse.injective (pi_c U ℱ p)

/-- Evaluating `c s` at the underlying tuple of a strictly increasing index returns `s`
there (a restatement of `pi_c`).  This is because on an already-sorted tuple the sorting
permutation is the identity, the sign is `+1`, and the `eqToHom` transport is trivial. -/
theorem c_on_ord {p : ℕ} (s : OrdCochain U ℱ p) (j : OrdIndex (I := I) p) :
    (c U ℱ p s) j.1 = s j := by
  simpa [pi] using congrFun (pi_c U ℱ p s) j

/-- (1) **[Stacks, Tag 01FJ], the chain-map clause.** `c` is a chain map: `c ∘ d = d ∘ c`.

This is the first half of what the source asserts about `c`; the degreewise bijectivity is
`cAddEquiv`, and `Stacks.Cech.orderedIsoAlternatingCechComplex` assembles the two into the
isomorphism of cochain complexes `Č_ord^• → Č_alt^•`. -/
@[stacks 01FJ "c is a morphism of complexes"]
theorem c_chainMap (p : ℕ) (s : OrdCochain U ℱ p) :
    c U ℱ (p + 1) (ordD U ℱ p s) = cechD U ℱ p (c U ℱ p s) := by
  -- SANITY CHECK PASSED
  /-
  INFORMAL PROOF (reduction to the ordered side via injectivity of `c`).

  STEP 1.  `cechD (c s)` is alternating.  Indeed `c s` is alternating (`c_isAlternating`)
  and `cechD` preserves the alternating subgroup (`cechD_mem_alternating`).  Hence by
  `c_pi_of_isAlternating`, `c (π (cechD (c s))) = cechD (c s)`, i.e. `cechD (c s)` is in the
  image of `c`, namely `c (π (cechD (c s)))`.

  STEP 2.  `c` is injective (`c_injective`, from `pi_c`).  So to prove
  `c (ordD s) = cechD (c s) = c (π (cechD (c s)))` it suffices to prove the identity of
  ORDERED cochains
        `ordD s = π (cechD (c s))`.                                        (★)

  STEP 3 (proof of ★).  Both sides are ordered cochains; evaluate at a strictly increasing
  index `i = ⟨i.1, hi⟩`.
    RHS:  `π (cechD (c s)) i = (cechD (c s)) i.1
             = ∑_{k : Fin (p+2)} (-1)^k · restr (inter_le_omit) ((c s) (i.1 ∘ k.succAbove))`.
    For each `k`, the face tuple `i.1 ∘ k.succAbove` is STRICTLY INCREASING
    (`strictMono_omit i.2 k`), so by `c_on_ord` (the restatement of `pi_c`)
        `(c s) (i.1 ∘ k.succAbove) = s ⟨i.1 ∘ k.succAbove, strictMono_omit i.2 k⟩`.
    Substituting,
        `π (cechD (c s)) i = ∑_k (-1)^k · restr (s ⟨i.1 ∘ k.succAbove, _⟩) = (ordD s) i`,
    which is exactly the definition of `ordD s` evaluated at `i`.  Hence ★ holds.

  This route entirely avoids re-deriving the sign/sorting combinatorics on unordered tuples
  for the chain-map identity: the only inputs are `c_isAlternating`, `cechD_mem_alternating`,
  `c_pi_of_isAlternating`, `c_injective`, and `c_on_ord` (all `pi_c`-based).

  FORMALIZATION STRATEGY.
    have halt : IsAlternating U ℱ (cechD U ℱ p (c U ℱ p s)) :=
      cechD_mem_alternating U ℱ p (c U ℱ p s) (c_isAlternating U ℱ p s)
    -- rewrite RHS as `c (π (cechD (c s)))`
    rw [← c_pi_of_isAlternating U ℱ (p+1) (cechD U ℱ p (c U ℱ p s)) halt]
    -- reduce to ★ by injectivity
    apply congrArg (c U ℱ (p+1))   -- or `refine congrArg _ ?_`
    -- now goal: `ordD s = π (cechD (c s))`; `funext i; obtain ⟨i, hi⟩`; unfold both
    -- differentials; rewrite each face term with `c_on_ord` (using `strictMono_omit`);
    -- the two sums are then syntactically equal (`Finset.sum_congr rfl`).
  Note: instead of `apply congrArg`, one may `apply c_injective U ℱ` after rewriting both
  sides into `c _` form; both close STEP 2.
  -/
  have halt : IsAlternating U ℱ (cechD U ℱ p (c U ℱ p s)) :=
    cechD_mem_alternating U ℱ p (c U ℱ p s) (c_isAlternating U ℱ p s)
  rw [← c_pi_of_isAlternating U ℱ (p + 1) (cechD U ℱ p (c U ℱ p s)) halt]
  apply congrArg (c U ℱ (p + 1))
  -- Goal: ordD s = π (cechD (c s)).  Componentwise computation using `c_on_ord`.
  funext i
  obtain ⟨i, hi⟩ := i
  change (∑ j : Fin (p + 2),
        ((-1 : ℤ) ^ (j : ℕ)) •
          restr ℱ (inter_le_omit U (⟨i, hi⟩ : OrdIndex (I := I) (p + 1)).1 j)
            (s ⟨(⟨i, hi⟩ : OrdIndex (I := I) (p + 1)).1 ∘ j.succAbove,
                strictMono_omit (⟨i, hi⟩ : OrdIndex (I := I) (p + 1)).2 j⟩))
      = ∑ j : Fin (p + 2),
        ((-1 : ℤ) ^ (j : ℕ)) • restr ℱ (inter_le_omit U i j)
          ((c U ℱ p s) (i ∘ j.succAbove))
  refine Finset.sum_congr rfl (fun j _ => ?_)
  rw [c_on_ord U ℱ s ⟨i ∘ j.succAbove, strictMono_omit hi j⟩]

end CechCochains
