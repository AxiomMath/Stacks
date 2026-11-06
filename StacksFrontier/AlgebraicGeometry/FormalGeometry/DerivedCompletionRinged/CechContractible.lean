module

public import StacksFrontier.AlgebraicGeometry.FormalGeometry.DerivedCompletionRinged.ExtendedCech

/-!
# Contractibility of the extended alternating Čech complex at a unit

Let `F` be a system of objects `S ↦ F_S` indexed by the subsets of `Fin r` in a preadditive
category with finite products, and let `j ∈ Fin r` be an index such that every transition map
`F_S ⟶ F_T` which only adjoins `j` is invertible. Then the extended alternating Čech complex

`F_∅ → ∏_{|S| = 1} F_S → ∏_{|S| = 2} F_S → ⋯ → F_{Fin r}`

is homotopic to zero: the contracting homotopy sends the factor indexed by `A ∪ {j}` to the
factor indexed by `A`, with the sign with which `j` enters `A ∪ {j}`.

For the extended alternating Čech complex of sheaves of modules on a ringed site `(𝒞, 𝒪)`
attached to global sections `f_1, …, f_r` of `𝒪`, the hypothesis holds as soon as one `f_j` is
already invertible in `𝒪`: inverting a section that is already a unit changes nothing, so
`𝒪_{f_S} ⟶ 𝒪_{f_{S ∪ {j}}}` is an isomorphism. That complex is therefore a zero object of
`D(𝒪)`.

## Main definitions

* `CategoryTheory.AlternatingCech.dAux` and `CategoryTheory.AlternatingCech.hAux`: the
  alternating differential and the contracting homotopy, both written for an arbitrary pair of
  degrees related by `p + 1 = q` so that no transport along an equality of degrees is needed.
* `CategoryTheory.AlternatingCech.backMap`: the inverse of a transition map which only adjoins
  `j`, read on the factor it projects from.
* `CategoryTheory.AlternatingCech.homotopyIdZero`: the contracting homotopy, as a homotopy
  between the identity of the complex and zero.

## Main results

* `CategoryTheory.AlternatingCech.cechSign_erase_add_cechSign_insert`: the sign cancellation
  behind the homotopy identity.
* `CategoryTheory.AlternatingCech.hAux_comp_dAux_add_dAux_comp_hAux`: the homotopy identity
  `h ∘ d + d ∘ h = id` in each degree, which is the whole content.
* `CategoryTheory.AlternatingCech.isZero_Q_complex`: the complex is a zero object of the
  derived category.
* `SheafOfModules.isIso_unitRestrictScalarsMap`: an isomorphism of sheaves of rings over `R` is
  an isomorphism of the two sheaves viewed as sheaves of `R`-modules.
* `AlgebraicGeometry.RingedSite.isIso_awayTransition_of_isUnit` and
  `AlgebraicGeometry.RingedSite.isIso_awayModuleTransition_of_subset_insert`: for
  `S ⊆ T ⊆ S ∪ {j}` with `f_j` a unit, the transition map `𝒪_{f_S} ⟶ 𝒪_{f_T}` is an
  isomorphism.
* `AlgebraicGeometry.RingedSite.homotopyIdZero_extendedAlternatingCech` and
  `AlgebraicGeometry.RingedSite.isZero_Q_extendedAlternatingCech_of_isUnit`: the extended
  alternating Čech complex of `f_1, …, f_r` is homotopic to zero, hence a zero object of
  `D(𝒪)`, as soon as one of the `f_j` is a unit.

## Implementation notes

The degree-`p` term of the complex is a product indexed by `AlternatingCech.Idx r p`, the
subsets of `Fin r` of cardinality `p`. A morphism out of the degree-`p` term into the
degree-`(p-1)` term therefore has to be given by its components at the subsets `A` of
cardinality `p - 1`, and the component at `A` is the projection onto the factor `A ∪ {j}`
followed by the inverse of `F_A ⟶ F_{A ∪ {j}}` — or zero when `j ∈ A`, there being then no
factor to project from. Since the index `A ∪ {j}` of the factor is built from `A`, while in the
course of the proof the relevant factor arrives instead as `B` with `B = A ∪ {j}` only
propositionally, the projection is isolated as `backMap`, which takes the index of the factor
as a separate argument; `backMap_comp_map_of_eq` then transports along the equality of indices
by `subst`, which is what keeps the proof free of `eqToHom`.

`dAux` duplicates `CategoryTheory.AlternatingCech.d` with the target degree as a separate
argument constrained by `p + 1 = q`. This is not a second differential: `complex_d_eq`
identifies it with the differential of the complex, and the point of the reformulation is that
the homotopy identity in degree `p` involves the differential out of degree `p - 1`, whose
target would otherwise be the term in degree `(p - 1) + 1` rather than in degree `p`.

The hypothesis is stated for every inclusion `S ⊆ T` with `T ⊆ S ∪ {j}` rather than only for
`S ⊆ S ∪ {j}`. The two are equivalent, such a `T` being either `S` or `S ∪ {j}`, but the stated
form is the one the proof uses and the one a ringed-site application proves directly.

In the case `j ∉ B` of the homotopy identity the two sides are compared after composition with
the transition map `F_B ⟶ F_{B ∪ {j}}`, which is invertible by hypothesis and therefore a
monomorphism. That is what removes every occurrence of an inverse from the computation: both
sides become alternating sums of projections followed by transition maps, and the identity
reduces to the sign cancellation.

No `@[stacks]` attribute is attached here. This is the contractibility step in the proof of
[Stacks, Tag 099B], not that tag, whose carrier is
`AlgebraicGeometry.RingedSite.isRightAdjoint_ι_isDerivedComplete_of_forall_isNilpotent` of
`StacksFrontier/AlgebraicGeometry/FormalGeometry/DerivedCompletionRinged/NilpotentIdeal.lean`.

## References

* [Stacks Project, Tag 099B](https://stacks.math.columbia.edu/tag/099B)
* [Stacks Project, Tag 0G6F](https://stacks.math.columbia.edu/tag/0G6F)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits

universe u v w

namespace CategoryTheory.AlternatingCech

/-! ### Signs -/

variable {r : ℕ}

/-- The Čech sign is a square root of one. -/
theorem cechSign_mul_self (S : Finset (Fin r)) (i : Fin r) :
    Cech.cechSign S i * Cech.cechSign S i = 1 := by
  simp only [Cech.cechSign, ← pow_add]
  exact Even.neg_one_pow ⟨_, rfl⟩

/-- **The sign identity behind the contracting homotopy.** For `k ∈ B` and `j ∉ B`, removing `k`
from `B` and adjoining `j` afterwards picks up the opposite sign to adjoining `j` to `B` and
removing `k` afterwards. -/
theorem cechSign_erase_add_cechSign_insert {B : Finset (Fin r)} {j k : Fin r}
    (hk : k ∈ B) (hj : j ∉ B) :
    Cech.cechSign B k * Cech.cechSign (B.erase k) j +
      Cech.cechSign B j * Cech.cechSign (insert j B) k = 0 := by
  have hkj : k ≠ j := fun h ↦ hj (h ▸ hk)
  have hswap := Cech.cechSign_swap (B.erase k) hkj (Finset.notMem_erase k B)
    (fun h ↦ hj (Finset.mem_of_mem_erase h))
  rw [Cech.cechSign_erase, Finset.insert_erase hk] at hswap
  rw [← Cech.cechSign_erase (insert j B) k, Finset.erase_insert_of_ne (Ne.symm hkj)]
  have hb := cechSign_mul_self B j
  have hc := cechSign_mul_self (B.erase k) j
  linear_combination (Cech.cechSign B j * Cech.cechSign (B.erase k) j) * hswap -
    (Cech.cechSign B k * Cech.cechSign (B.erase k) j) * hb -
    (Cech.cechSign B j * Cech.cechSign (insert j (B.erase k)) k) * hc

/-! ### Index bookkeeping -/

/-- Removing an element of `T` from a subset of cardinality `q` gives one of cardinality `p`,
for `p + 1 = q`. -/
def idxErase {p q : ℤ} (T : Idx r q) (k : T.1) (hpq : p + 1 = q) : Idx r p :=
  ⟨T.1.erase k, by
    have h := T.2
    have h1 : 1 ≤ T.1.card := Finset.card_pos.mpr ⟨k.1, k.2⟩
    rw [Finset.card_erase_of_mem k.2]
    omega⟩

/-- The underlying subset of `idxErase T k hpq` is `T` with `k` removed. -/
@[simp]
theorem val_idxErase {p q : ℤ} (T : Idx r q) (k : T.1) (hpq : p + 1 = q) :
    (idxErase T k hpq).1 = T.1.erase k :=
  rfl

/-- Adjoining an element not in `A` to a subset of cardinality `q` gives one of cardinality `p`,
for `q + 1 = p`. -/
def idxInsert {p q : ℤ} (j : Fin r) (A : Idx r q) (hj : j ∉ A.1) (hqp : q + 1 = p) : Idx r p :=
  ⟨insert j A.1, by
    have h := A.2
    rw [Finset.card_insert_of_notMem hj]
    push_cast
    omega⟩

/-- The underlying subset of `idxInsert j A hj hqp` is `A` with `j` adjoined. -/
@[simp]
theorem val_idxInsert {p q : ℤ} (j : Fin r) (A : Idx r q) (hj : j ∉ A.1) (hqp : q + 1 = p) :
    (idxInsert j A hj hqp).1 = insert j A.1 :=
  rfl

/-- Splitting a sum over the elements of `insert a s` into the term at `a` and the sum over the
elements of `s`. -/
theorem sum_attach_insert {M : Type*} [AddCommMonoid M] {a : Fin r} {s : Finset (Fin r)}
    (ha : a ∉ s) (g : {x // x ∈ insert a s} → M) :
    ∑ k ∈ (insert a s).attach, g k =
      g ⟨a, Finset.mem_insert_self a s⟩ +
        ∑ k ∈ s.attach, g ⟨k.1, Finset.mem_insert_of_mem k.2⟩ := by
  classical
  have hinj : ∀ x ∈ s.attach, ∀ y ∈ s.attach,
      (⟨x.1, Finset.mem_insert_of_mem x.2⟩ : {x // x ∈ insert a s}) =
        ⟨y.1, Finset.mem_insert_of_mem y.2⟩ → x = y :=
    fun x _ y _ h ↦
      Subtype.ext (congrArg (fun z : {x // x ∈ insert a s} => (z : Fin r)) h)
  have hnot : (⟨a, Finset.mem_insert_self a s⟩ : {x // x ∈ insert a s}) ∉
      s.attach.image fun x : {x // x ∈ s} ↦
        (⟨x.1, Finset.mem_insert_of_mem x.2⟩ : {x // x ∈ insert a s}) := by
    simp only [Finset.mem_image, not_exists, not_and]
    intro x _ hx
    have hxa : (x : Fin r) = a :=
      congrArg (fun z : {x // x ∈ insert a s} => (z : Fin r)) hx
    exact ha (by rw [← hxa]; exact x.2)
  rw [Finset.attach_insert, Finset.sum_insert hnot, Finset.sum_image hinj]

/-- `sum_attach_insert` for a subset only propositionally of the form `insert a s`. -/
theorem sum_attach_insert_of_eq {M : Type*} [AddCommMonoid M] {a : Fin r} {s V : Finset (Fin r)}
    (hV : V = insert a s) (ha : a ∉ s) (g : {x // x ∈ V} → M) :
    ∑ k ∈ V.attach, g k =
      g ⟨a, hV ▸ Finset.mem_insert_self a s⟩ +
        ∑ k ∈ s.attach, g ⟨k.1, hV ▸ Finset.mem_insert_of_mem k.2⟩ := by
  subst hV
  exact sum_attach_insert ha g

/-! ### The differential, with the target degree as an argument -/

variable {𝒜 : Type u} [Category.{v} 𝒜] [Preadditive 𝒜] [HasFiniteProducts 𝒜]

omit [Preadditive 𝒜] [HasFiniteProducts 𝒜] in
/-- Transition maps compose, in the form in which the inclusions are given separately. -/
theorem map_homOfLE_comp (F : Finset (Fin r) ⥤ 𝒜) {S T W : Finset (Fin r)} (h1 : S ⊆ T)
    (h2 : T ⊆ W) (h3 : S ⊆ W) :
    F.map (homOfLE h1) ≫ F.map (homOfLE h2) = F.map (homOfLE h3) := by
  rw [← F.map_comp]
  exact congrArg F.map (Subsingleton.elim _ _)

omit [Preadditive 𝒜] in
/-- A projection followed by a transition map depends on the factor only through its index. -/
theorem pi_comp_map_congr (F : Finset (Fin r) ⥤ 𝒜) {p : ℤ} {A A' : Idx r p} (hAA' : A = A')
    {W : Finset (Fin r)} (h : A.1 ⊆ W) (h' : A'.1 ⊆ W) :
    Pi.π (fun S : Idx r p => F.obj S.1) A ≫ F.map (homOfLE h) =
      Pi.π (fun S : Idx r p => F.obj S.1) A' ≫ F.map (homOfLE h') := by
  subst hAA'; rfl

/-- The alternating differential `term F p ⟶ term F q` for `p + 1 = q`. It is the differential
`CategoryTheory.AlternatingCech.d` of the complex, written so that the target degree is an
argument rather than the expression `p + 1`. -/
def dAux (F : Finset (Fin r) ⥤ 𝒜) {p q : ℤ} (hpq : p + 1 = q) : term F p ⟶ term F q :=
  Pi.lift fun T : Idx r q => ∑ k ∈ T.1.attach, Cech.cechSign T.1 k.1 •
    proj F (idxErase T k hpq) (Finset.erase_subset _ _)

/-- The component of `dAux` at a subset of cardinality `q`, written with the projections and
transition maps displayed. -/
theorem dAux_comp_pi (F : Finset (Fin r) ⥤ 𝒜) {p q : ℤ} (hpq : p + 1 = q) (T : Idx r q) :
    dAux F hpq ≫ Pi.π (fun S : Idx r q => F.obj S.1) T =
      ∑ k ∈ T.1.attach, Cech.cechSign T.1 k.1 •
        (Pi.π (fun S : Idx r p => F.obj S.1) (idxErase T k hpq) ≫
          F.map (homOfLE (Finset.erase_subset (k : Fin r) T.1))) :=
  Pi.lift_comp_π _ _

/-- `dAux` is the differential of the extended alternating Čech complex. -/
theorem complex_d_eq (F : Finset (Fin r) ⥤ 𝒜) {p q : ℤ} (hpq : p + 1 = q) :
    (complex F).d p q = dAux F hpq := by
  subst hpq
  rw [complex_d]
  rfl

/-! ### The contracting homotopy -/

section Contractible

variable (F : Finset (Fin r) ⥤ 𝒜) (j : Fin r)
  (hiso : ∀ {S T : Finset (Fin r)} (hST : S ⊆ T), T ⊆ insert j S → IsIso (F.map (homOfLE hST)))

include hiso

/-- The inverse of a transition map which only adjoins `j`, read on the factor of the
degree-`p` term indexed by `B`. -/
def backMap {p q : ℤ} (A : Idx r q) (B : Idx r p) (hAB : A.1 ⊆ B.1)
    (hBA : B.1 ⊆ insert j A.1) : term F p ⟶ F.obj A.1 :=
  letI : IsIso (F.map (homOfLE hAB)) := hiso hAB hBA
  Pi.π (fun S : Idx r p => F.obj S.1) B ≫ inv (F.map (homOfLE hAB))

omit [Preadditive 𝒜] in
/-- Following `backMap` by the transition map it inverts gives back the projection. -/
theorem backMap_comp_map {p q : ℤ} (A : Idx r q) (B : Idx r p) (hAB : A.1 ⊆ B.1)
    (hBA : B.1 ⊆ insert j A.1) :
    backMap F j hiso A B hAB hBA ≫ F.map (homOfLE hAB) =
      Pi.π (fun S : Idx r p => F.obj S.1) B := by
  have : IsIso (F.map (homOfLE hAB)) := hiso hAB hBA
  show (Pi.π (fun S : Idx r p => F.obj S.1) B ≫ inv (F.map (homOfLE hAB))) ≫
    F.map (homOfLE hAB) = _
  rw [Category.assoc, IsIso.inv_hom_id, Category.comp_id]

omit [Preadditive 𝒜] in
/-- Following `backMap` by a transition map out of `A` gives the projection onto the factor it
projects from, followed by the transition map out of that factor. -/
theorem backMap_comp_map_proj {p q : ℤ} (A : Idx r q) (B : Idx r p) (hAB : A.1 ⊆ B.1)
    (hBA : B.1 ⊆ insert j A.1) {W : Finset (Fin r)} (hAW : A.1 ⊆ W) (hBW : B.1 ⊆ W) :
    backMap F j hiso A B hAB hBA ≫ F.map (homOfLE hAW) =
      Pi.π (fun S : Idx r p => F.obj S.1) B ≫ F.map (homOfLE hBW) := by
  rw [← map_homOfLE_comp F hAB hBW hAW, ← Category.assoc, backMap_comp_map]

omit [Preadditive 𝒜] in
/-- `backMap` depends on the factor it projects from only through its index. -/
theorem backMap_congr {p q : ℤ} (A : Idx r q) {B B' : Idx r p} (hBB' : B = B')
    (hAB : A.1 ⊆ B.1) (hBA : B.1 ⊆ insert j A.1)
    (hAB' : A.1 ⊆ B'.1) (hB'A : B'.1 ⊆ insert j A.1) :
    backMap F j hiso A B hAB hBA = backMap F j hiso A B' hAB' hB'A := by
  subst hBB'; rfl

omit [Preadditive 𝒜] in
/-- Following `backMap` by two successive transition maps, the first out of `A`. -/
theorem backMap_comp_map_comp_map {p q : ℤ} (A : Idx r q) (B : Idx r p) (hAB : A.1 ⊆ B.1)
    (hBA : B.1 ⊆ insert j A.1) {W V : Finset (Fin r)} (hAW : A.1 ⊆ W) (hWV : W ⊆ V)
    (hBV : B.1 ⊆ V) :
    (backMap F j hiso A B hAB hBA ≫ F.map (homOfLE hAW)) ≫ F.map (homOfLE hWV) =
      Pi.π (fun S : Idx r p => F.obj S.1) B ≫ F.map (homOfLE hBV) := by
  rw [Category.assoc, map_homOfLE_comp F hAW hWV (hAW.trans hWV),
    backMap_comp_map_proj F j hiso A B hAB hBA (hAW.trans hWV) hBV]

omit [Preadditive 𝒜] in
/-- When the factor `backMap` projects from is identified with another index, following
`backMap` by the transition map it inverts gives the projection at that other index. -/
theorem backMap_comp_map_of_eq {p q : ℤ} (A : Idx r q) {B B' : Idx r p} (hB'B : B' = B)
    (hAB' : A.1 ⊆ B'.1) (hB'A : B'.1 ⊆ insert j A.1) (hAB : A.1 ⊆ B.1) :
    backMap F j hiso A B' hAB' hB'A ≫ F.map (homOfLE hAB) =
      Pi.π (fun S : Idx r p => F.obj S.1) B := by
  subst hB'B
  exact backMap_comp_map F j hiso A B' hAB' hB'A

/-- **The contracting homotopy** of the extended alternating Čech complex at a unit index `j`,
as a map `term F p ⟶ term F q` for `q + 1 = p`: its component at a subset `A` of cardinality
`q` is the projection onto the factor indexed by `A ∪ {j}` followed by the inverse of the
transition map `F_A ⟶ F_{A ∪ {j}}`, with the sign with which `j` enters `A ∪ {j}`, and is zero
when `j` already lies in `A`. -/
def hAux {p q : ℤ} (hqp : q + 1 = p) : term F p ⟶ term F q :=
  Pi.lift fun A : Idx r q =>
    if hA : j ∈ A.1 then 0
    else Cech.cechSign A.1 j •
      backMap F j hiso A (idxInsert j A hA hqp) (Finset.subset_insert j A.1)
        (Finset.Subset.refl _)

/-- The component of the homotopy at a subset containing `j` vanishes. -/
theorem hAux_comp_pi_of_mem {p q : ℤ} (hqp : q + 1 = p) (A : Idx r q) (hA : j ∈ A.1) :
    hAux F j hiso hqp ≫ Pi.π (fun S : Idx r q => F.obj S.1) A = 0 := by
  rw [hAux, Pi.lift_comp_π, dite_eq_left hA]

/-- The component of the homotopy at a subset not containing `j`. -/
theorem hAux_comp_pi_of_notMem {p q : ℤ} (hqp : q + 1 = p) (A : Idx r q) (hA : j ∉ A.1) :
    hAux F j hiso hqp ≫ Pi.π (fun S : Idx r q => F.obj S.1) A =
      Cech.cechSign A.1 j •
        backMap F j hiso A (idxInsert j A hA hqp) (Finset.subset_insert j A.1)
          (Finset.Subset.refl _) := by
  rw [hAux, Pi.lift_comp_π, dite_eq_right hA]

/-- The component of the homotopy at a subset not containing `j`, read on a factor whose index
is only propositionally `A ∪ {j}`. -/
theorem hAux_comp_pi_of_eq {p q : ℤ} (hqp : q + 1 = p) (A : Idx r q) (hA : j ∉ A.1)
    (B : Idx r p) (hBA' : B.1 = insert j A.1) (hAB : A.1 ⊆ B.1)
    (hBA : B.1 ⊆ insert j A.1) :
    hAux F j hiso hqp ≫ Pi.π (fun S : Idx r q => F.obj S.1) A =
      Cech.cechSign A.1 j • backMap F j hiso A B hAB hBA := by
  rw [hAux_comp_pi_of_notMem F j hiso hqp A hA,
    backMap_congr F j hiso A (show idxInsert j A hA hqp = B from Subtype.ext hBA'.symm)
      (Finset.subset_insert j A.1) (Finset.Subset.refl _) hAB hBA]

/-- The homotopy followed by the differential, read on the factor indexed by `B`. -/
private theorem hAux_comp_dAux_comp_pi {p q : ℤ} (hqp : q + 1 = p) (B : Idx r p) :
    hAux F j hiso hqp ≫ dAux F hqp ≫ Pi.π (fun S : Idx r p => F.obj S.1) B =
      ∑ k ∈ B.1.attach, Cech.cechSign B.1 k.1 •
        ((hAux F j hiso hqp ≫
            Pi.π (fun S : Idx r q => F.obj S.1) (idxErase B k hqp)) ≫
          F.map (homOfLE (Finset.erase_subset (k : Fin r) B.1))) := by
  rw [dAux_comp_pi F hqp B, Preadditive.comp_sum]
  refine Finset.sum_congr rfl fun k _ ↦ ?_
  rw [Preadditive.comp_zsmul, ← Category.assoc]

/-- **The homotopy identity.** In each degree the identity of the extended alternating Čech
complex is the sum of the two composites of the differential with the contracting homotopy. -/
theorem hAux_comp_dAux_add_dAux_comp_hAux {p q s : ℤ} (hqp : q + 1 = p) (hps : p + 1 = s) :
    hAux F j hiso hqp ≫ dAux F hqp + dAux F hps ≫ hAux F j hiso hps = 𝟙 (term F p) := by
  classical
  refine Pi.hom_ext _ _ fun B ↦ ?_
  rw [Preadditive.add_comp, Category.id_comp, Category.assoc, Category.assoc]
  by_cases hB : j ∈ B.1
  · -- Only the composite `h` then `d` contributes, and only through the factor `B ∖ {j}`.
    have hzero : ∀ b ∈ B.1.attach, b ≠ (⟨j, hB⟩ : {x // x ∈ B.1}) →
        Cech.cechSign B.1 b.1 • ((hAux F j hiso hqp ≫
            Pi.π (fun S : Idx r q => F.obj S.1) (idxErase B b hqp)) ≫
          F.map (homOfLE (Finset.erase_subset (b : Fin r) B.1))) = 0 := by
      intro b _ hb
      have hjb : j ∈ (idxErase B b hqp).1 :=
        Finset.mem_erase.mpr ⟨fun h ↦ hb (Subtype.ext h.symm), hB⟩
      rw [hAux_comp_pi_of_mem F j hiso hqp _ hjb, zero_comp, smul_zero]
    have hA : j ∉ (idxErase B (⟨j, hB⟩ : {x // x ∈ B.1}) hqp).1 := Finset.notMem_erase j B.1
    have hidx : idxInsert j (idxErase B (⟨j, hB⟩ : {x // x ∈ B.1}) hqp) hA hqp = B :=
      Subtype.ext (by simpa using Finset.insert_erase hB)
    have key : backMap F j hiso (idxErase B (⟨j, hB⟩ : {x // x ∈ B.1}) hqp)
          (idxInsert j (idxErase B (⟨j, hB⟩ : {x // x ∈ B.1}) hqp) hA hqp)
          (Finset.subset_insert j _) (Finset.Subset.refl _) ≫
          F.map (homOfLE (Finset.erase_subset ((⟨j, hB⟩ : {x // x ∈ B.1}) : Fin r) B.1)) =
        Pi.π (fun S : Idx r p => F.obj S.1) B :=
      backMap_comp_map_of_eq F j hiso _ hidx _ _ _
    rw [hAux_comp_pi_of_mem F j hiso hps B hB, comp_zero, add_zero,
      hAux_comp_dAux_comp_pi F j hiso hqp B,
      Finset.sum_eq_single_of_mem (⟨j, hB⟩ : {x // x ∈ B.1}) (Finset.mem_attach _ _) hzero,
      hAux_comp_pi_of_notMem F j hiso hqp _ hA, Preadditive.zsmul_comp, smul_smul, key,
      val_idxErase, Cech.cechSign_erase, cechSign_mul_self, one_smul]
  · -- The two composites are compared after the invertible transition map `F_B ⟶ F_{B ∪ {j}}`.
    obtain ⟨T, hTB⟩ : ∃ T : Idx r s, T.1 = insert j B.1 := ⟨idxInsert j B hB hps, rfl⟩
    have hBT : B.1 ⊆ T.1 := hTB ▸ Finset.subset_insert j B.1
    have hTins : T.1 ⊆ insert j B.1 := hTB ▸ Finset.Subset.refl _
    have hisoBT : IsIso (F.map (homOfLE hBT)) := hiso hBT hTins
    have hjmem : ∀ k : {x // x ∈ B.1}, j ∉ (idxErase B k hqp).1 := fun k h ↦
      hB (Finset.mem_of_mem_erase h)
    have hsub : ∀ k : {x // x ∈ B.1},
        (idxInsert j (idxErase B k hqp) (hjmem k) hqp).1 ⊆ T.1 :=
      fun k ↦ hTB ▸ Finset.insert_subset_insert _ (Finset.erase_subset _ _)
    have hsignj : Cech.cechSign T.1 j = Cech.cechSign B.1 j := by
      rw [hTB]; exact Cech.cechSign_insert j B.1
    have hsignT : ∀ k : {x // x ∈ B.1},
        Cech.cechSign T.1 k.1 = Cech.cechSign (insert j B.1) k.1 := fun k ↦ by rw [hTB]
    have heraseJ : T.1.erase j = B.1 := by rw [hTB]; exact Finset.erase_insert hB
    have heraseK : ∀ k : {x // x ∈ B.1}, T.1.erase k.1 = insert j (B.1.erase k.1) := fun k ↦ by
      rw [hTB]
      exact Finset.erase_insert_of_ne (fun h : j = k.1 ↦ hB (h ▸ k.2))
    have hT1 : (hAux F j hiso hqp ≫ dAux F hqp ≫
          Pi.π (fun S : Idx r p => F.obj S.1) B) ≫ F.map (homOfLE hBT) =
        ∑ k ∈ B.1.attach,
          (Cech.cechSign B.1 k.1 * Cech.cechSign (idxErase B k hqp).1 j) •
            (Pi.π (fun S : Idx r p => F.obj S.1)
                (idxInsert j (idxErase B k hqp) (hjmem k) hqp) ≫
              F.map (homOfLE (hsub k))) := by
      rw [hAux_comp_dAux_comp_pi F j hiso hqp B, Preadditive.sum_comp]
      refine Finset.sum_congr rfl fun k _ ↦ ?_
      rw [Preadditive.zsmul_comp, hAux_comp_pi_of_notMem F j hiso hqp _ (hjmem k),
        Preadditive.zsmul_comp, Preadditive.zsmul_comp, smul_smul]
      exact congrArg
        (fun z => (Cech.cechSign B.1 k.1 * Cech.cechSign (idxErase B k hqp).1 j) • z)
        (backMap_comp_map_comp_map F j hiso (idxErase B k hqp)
          (idxInsert j (idxErase B k hqp) (hjmem k) hqp) (Finset.subset_insert j _)
          (Finset.Subset.refl _) (Finset.erase_subset _ _) hBT (hsub k))
    have hT2 : (dAux F hps ≫ hAux F j hiso hps ≫
          Pi.π (fun S : Idx r p => F.obj S.1) B) ≫ F.map (homOfLE hBT) =
        (Pi.π (fun S : Idx r p => F.obj S.1) B ≫ F.map (homOfLE hBT)) +
          ∑ k ∈ B.1.attach,
            (Cech.cechSign B.1 j * Cech.cechSign T.1 k.1) •
              (Pi.π (fun S : Idx r p => F.obj S.1)
                  (idxInsert j (idxErase B k hqp) (hjmem k) hqp) ≫
                F.map (homOfLE (hsub k))) := by
      rw [hAux_comp_pi_of_eq F j hiso hps B hB T hTB hBT hTins,
        Preadditive.comp_zsmul, Preadditive.zsmul_comp, Category.assoc,
        backMap_comp_map F j hiso B T hBT hTins, dAux_comp_pi F hps T, Finset.smul_sum,
        sum_attach_insert_of_eq hTB hB]
      congr 1
      · rw [smul_smul, hsignj, cechSign_mul_self, one_smul]
        exact pi_comp_map_congr F (show idxErase T
            (⟨j, hTB ▸ Finset.mem_insert_self j B.1⟩ : {x // x ∈ T.1}) hps = B from
          Subtype.ext heraseJ) _ hBT
      · refine Finset.sum_congr rfl fun k _ ↦ ?_
        rw [smul_smul]
        exact congrArg (fun z => (Cech.cechSign B.1 j * Cech.cechSign T.1 k.1) • z)
          (pi_comp_map_congr F (show idxErase T
              (⟨k.1, hTB ▸ Finset.mem_insert_of_mem k.2⟩ : {x // x ∈ T.1}) hps =
                idxInsert j (idxErase B k hqp) (hjmem k) hqp from
            Subtype.ext (heraseK k)) _ (hsub k))
    rw [← cancel_mono (F.map (homOfLE hBT)), Preadditive.add_comp, hT1, hT2,
      show ∀ (Z : 𝒜) (a b c : term F p ⟶ Z), a + (b + c) = (a + c) + b from
        fun _ a b c ↦ by abel,
      ← Finset.sum_add_distrib,
      Finset.sum_eq_zero (fun k _ ↦ by
        rw [← add_smul, val_idxErase, hsignT k, cechSign_erase_add_cechSign_insert k.2 hB,
          zero_smul]),
      zero_add]

/-- **The extended alternating Čech complex is homotopic to zero** when one index `j` is such
that every transition map adjoining only `j` is invertible. -/
def homotopyIdZero : Homotopy (𝟙 (complex F)) 0 :=
  (CochainComplex.HomComplex.Cochain.equivHomotopy _ _).symm
    ⟨CochainComplex.HomComplex.Cochain.mk
      (fun p q hpq => hAux F j hiso (show q + 1 = p by omega)), by
      ext p
      rw [CochainComplex.HomComplex.Cochain.ofHom_v,
        CochainComplex.HomComplex.Cochain.add_v,
        CochainComplex.HomComplex.δ_v (-1) 0 (neg_add_cancel 1) _ p p (add_zero p) (p - 1)
          (p + 1) rfl rfl]
      simp only [CochainComplex.HomComplex.Cochain.ofHom_v, Int.negOnePow_zero, one_smul,
        HomologicalComplex.id_f, HomologicalComplex.zero_f, add_zero]
      rw [complex_d_eq F (show p - 1 + 1 = p by omega),
        complex_d_eq F (show p + 1 = p + 1 from rfl)]
      exact (hAux_comp_dAux_add_dAux_comp_hAux F j hiso (show p - 1 + 1 = p by omega)
        (show p + 1 = p + 1 from rfl)).symm⟩

end Contractible

section Derived

/-- A cochain complex whose identity is null-homotopic is a zero object of the derived
category. -/
theorem isZero_Q_obj_of_homotopy_id_zero {𝒞 : Type u} [Category.{v} 𝒞] [Abelian 𝒞]
    [HasDerivedCategory.{w} 𝒞] (K : CochainComplex 𝒞 ℤ) (h : Homotopy (𝟙 K) 0) :
    IsZero (DerivedCategory.Q.obj K) := by
  rw [IsZero.iff_id_eq_zero, ← DerivedCategory.Q.map_id,
    DerivedCategory.Q_map_eq_of_homotopy (C := 𝒞) h]
  exact Functor.map_zero _ _ _

/-- **The extended alternating Čech complex is a zero object of the derived category** when one
index `j` is such that every transition map adjoining only `j` is invertible. -/
theorem isZero_Q_complex {𝒞 : Type u} [Category.{v} 𝒞] [Abelian 𝒞]
    [HasDerivedCategory.{w} 𝒞] (F : Finset (Fin r) ⥤ 𝒞) (j : Fin r)
    (hiso : ∀ {S T : Finset (Fin r)} (hST : S ⊆ T), T ⊆ insert j S →
      IsIso (F.map (homOfLE hST))) :
    IsZero (DerivedCategory.Q.obj (complex F)) :=
  isZero_Q_obj_of_homotopy_id_zero _ (homotopyIdZero F j hiso)

end Derived

end CategoryTheory.AlternatingCech

namespace SheafOfModules

variable {C : Type u} [Category.{v} C] {J : GrothendieckTopology C}
  {R A B : Sheaf J RingCat.{w}}

/-- An isomorphism of sheaves of rings over `R` is an isomorphism of the two sheaves viewed as
sheaves of `R`-modules. -/
theorem isIso_unitRestrictScalarsMap {αA : R ⟶ A} {αB : R ⟶ B} (β : A ⟶ B) [IsIso β]
    (h : αA ≫ β = αB) : IsIso (unitRestrictScalarsMapOfComp.{u, v, w} β h) := by
  have h' : αB ≫ inv β = αA := by
    rw [← h, Category.assoc, IsIso.hom_inv_id, Category.comp_id]
  refine ⟨⟨unitRestrictScalarsMapOfComp.{u, v, w} (inv β) h', ?_, ?_⟩⟩
  · rw [unitRestrictScalarsMap_comp h h'
        (by rw [IsIso.hom_inv_id, Category.comp_id]),
      unitRestrictScalarsMap_congr _ (Category.comp_id αA) (IsIso.hom_inv_id β),
      unitRestrictScalarsMap_id]
  · rw [unitRestrictScalarsMap_comp h' h
        (by rw [IsIso.inv_hom_id, Category.comp_id]),
      unitRestrictScalarsMap_congr _ (Category.comp_id αB) (IsIso.inv_hom_id β),
      unitRestrictScalarsMap_id]

end SheafOfModules

namespace AlgebraicGeometry.RingedSite

open CategoryTheory.AlternatingCech

variable (X : RingedSite.{u, u, u}) [HasWeakSheafify X.J CommRingCat.{u}] {r : ℕ}
  (f : Fin r → Presheaf.globalSections (X.O.obj ⋙ forget CommRingCat.{u}))

/-- An endomorphism of `𝒪_{f_S}` fixing the map `𝒪 ⟶ 𝒪_{f_S}` is the identity. -/
private theorem eq_id_of_toAwaySheaf_comp_eq (S : Finset (Fin r))
    (g : awaySheaf (prodGlobalSection f S) ⟶ awaySheaf (prodGlobalSection f S))
    (h : toAwaySheaf (prodGlobalSection f S) ≫ g = toAwaySheaf (prodGlobalSection f S)) :
    g = 𝟙 _ := by
  obtain ⟨φ, -, huniq⟩ := existsUnique_lift_toAwaySheaf (prodGlobalSection f S)
    (awaySheaf (prodGlobalSection f S)) (toAwaySheaf (prodGlobalSection f S))
    (isUnit_toAwaySheaf (prodGlobalSection f S))
  rw [huniq g h, huniq (𝟙 (awaySheaf (prodGlobalSection f S))) (Category.comp_id _)]

/-- **Inverting `f_T` changes nothing over `𝒪_{f_S}` when `f_T` is already invertible there.**
The lift of `𝒪 ⟶ 𝒪_{f_S}` through `𝒪_{f_T}` is then a two-sided inverse of the transition map,
both composites lifting the same map out of `𝒪`. -/
theorem isIso_awayTransition_of_isUnit {S T : Finset (Fin r)} (hST : S ⊆ T)
    (hu : ∀ (U : X.Cᵒᵖ) (n : ℕ),
      IsUnit (((toAwaySheaf (prodGlobalSection f S)).hom.app U).hom
        (globalSectionVal (prodGlobalSection f T) U ^ n))) :
    IsIso (awayTransition f hST) := by
  obtain ⟨ψ, hψ, -⟩ := existsUnique_lift_toAwaySheaf (prodGlobalSection f T)
    (awaySheaf (prodGlobalSection f S)) (toAwaySheaf (prodGlobalSection f S)) hu
  refine ⟨⟨ψ, eq_id_of_toAwaySheaf_comp_eq X f S _ ?_, eq_id_of_toAwaySheaf_comp_eq X f T _ ?_⟩⟩
  · rw [← Category.assoc, toAwaySheaf_comp_awayTransition, hψ]
  · rw [← Category.assoc, hψ, toAwaySheaf_comp_awayTransition]

/-- **For `S ⊆ T ⊆ S ∪ {j}` with `f_j` a unit, `𝒪_{f_S} ⟶ 𝒪_{f_T}` is an isomorphism** as a map
of sheaves of `𝒪`-modules: the quotient `f_T / f_S` is a power of `f_j` up to the already
invertible `f_S`, hence a unit. -/
theorem isIso_awayModuleTransition_of_subset_insert (j : Fin r)
    (hj : ∀ U : X.Cᵒᵖ, IsUnit (globalSectionVal (f j) U))
    {S T : Finset (Fin r)} (hST : S ⊆ T) (hTS : T ⊆ insert j S) :
    IsIso (awayModuleTransition X f hST) := by
  have hu : ∀ (U : X.Cᵒᵖ) (n : ℕ),
      IsUnit (((toAwaySheaf (prodGlobalSection f S)).hom.app U).hom
        (globalSectionVal (prodGlobalSection f T) U ^ n)) := by
    intro U n
    have hTS' : T \ S ⊆ {j} := fun x hx ↦ by
      rcases Finset.mem_insert.mp (hTS (Finset.mem_sdiff.mp hx).1) with h | h
      · exact Finset.mem_singleton.mpr h
      · exact absurd h (Finset.mem_sdiff.mp hx).2
    have hsd : IsUnit (∏ i ∈ T \ S, globalSectionVal (f i) U) := by
      rcases Finset.subset_singleton_iff.mp hTS' with h | h
      · rw [h, Finset.prod_empty]; exact isUnit_one
      · rw [h, Finset.prod_singleton]; exact hj U
    have hsplit : globalSectionVal (prodGlobalSection f T) U ^ n =
        (∏ i ∈ T \ S, globalSectionVal (f i) U) ^ n *
          globalSectionVal (prodGlobalSection f S) U ^ n := by
      rw [globalSectionVal_prodGlobalSection, globalSectionVal_prodGlobalSection, ← mul_pow,
        Finset.prod_sdiff hST]
    rw [hsplit, map_mul]
    exact ((hsd.pow n).map _).mul (isUnit_toAwaySheaf (prodGlobalSection f S) U n)
  have : IsIso (awayTransition f hST) := isIso_awayTransition_of_isUnit X f hST hu
  exact SheafOfModules.isIso_unitRestrictScalarsMap
    ((sheafCompose X.J (forget₂ CommRingCat.{u} RingCat.{u})).map (awayTransition f hST)) _

section Derived

attribute [local instance] HasDerivedCategory.standard

/-- **The extended alternating Čech complex of `f_1, …, f_r` is homotopic to zero when one of
the sections is a unit.** This is the contractibility step in the proof of [Stacks, Tag 099B]:
in `𝒪_{f_j}` the sections `f_1, …, f_r` generate the unit ideal, and the Čech complex formed
there is contractible. -/
def homotopyIdZero_extendedAlternatingCech (j : Fin r)
    (hj : ∀ U : X.Cᵒᵖ, IsUnit (globalSectionVal (f j) U)) :
    Homotopy (𝟙 (extendedAlternatingCech X f)) 0 :=
  AlternatingCech.homotopyIdZero (awayLocalizationFunctor X f) j
    fun hST hTS ↦ isIso_awayModuleTransition_of_subset_insert X f j hj hST hTS

/-- **The extended alternating Čech complex of `f_1, …, f_r` is a zero object of `D(𝒪)` when one
of the sections is a unit.** -/
theorem isZero_Q_extendedAlternatingCech_of_isUnit (j : Fin r)
    (hj : ∀ U : X.Cᵒᵖ, IsUnit (globalSectionVal (f j) U)) :
    IsZero (DerivedCategory.Q.obj (extendedAlternatingCech X f)) :=
  AlternatingCech.isZero_Q_obj_of_homotopy_id_zero _
    (homotopyIdZero_extendedAlternatingCech X f j hj)

end Derived

end AlgebraicGeometry.RingedSite

end
