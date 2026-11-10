module

public import Mathlib.Algebra.Homology.Refinements
public import Mathlib.CategoryTheory.Preadditive.Projective.Basic
public import StacksFrontier.Algebra.Homology.CupProductBoundaryDelta

/-!
# The cup product of two cohomology classes and the boundary maps of two short exact sequences

`Stacks.CupProduct.gamma_cup_boundary_delta` states the sign rule of Tag 07MC for *chosen
cochain representatives*: the two cochains `α₁`, `β₃` lift `d(α₂)`, `d(β₂)` for lifts `α₂`,
`β₂` of two cocycles.  This file states the identity
`γ₁(∂a₃ ∪ b₁) = (-1)^{n+1} γ₃(a₃ ∪ ∂b₁)` for *classes* `a₃ ∈ Hⁿ(F₃)` and `b₁ ∈ Hᵐ(G₁)` of
complexes in abelian categories, with `∂` the boundary maps of the two short exact sequences and
`∪` the cup product on cohomology.

The two things that have to be supplied are:

* the cup product of two *classes*, which needs a cocycle representative of a class and the
  independence of the result of the choice of representative;
* the two lifts `α₂`, `β₂`, which are data of `gamma_cup_boundary_delta` because the test
  object there is arbitrary.

Both come from the same place: the cochains of the source are *sections*, i.e. morphisms out of
`ℤ`, and `ℤ` is projective.  So everything below is stated for a cup product of a `P`-valued
class with a `Q`-valued class, for `P`, `Q` **projective** objects.  Then

* a class `P ⟶ Hⁱ(K)` is the class of an honest cocycle `P ⟶ Kⁱ`
  (`Stacks.CupProduct.exists_liftCycles_homologyπ_eq`),
* two cocycles with the same class differ by an honest coboundary
  (`Stacks.CupProduct.exists_eq_add_comp_d_of_liftCycles_homologyπ_eq`), and
* the lifts `α₂`, `β₂` exist, because `S.g` is degreewise epimorphic
  (`Stacks.CupProduct.exists_comp_g_f`), so no lift hypothesis survives in the statement.

## Main definitions

* `Stacks.CupProduct.cocycleRep`: a cocycle representative of a class valued in a projective
  object.
* `Stacks.CupProduct.cupClass`: **the cup product of two cohomology classes**, a morphism
  `Φ(P, Q) ⟶ H^{p+q}(Tot Φ(K, L))` attached to classes `P ⟶ Hᵖ(K)` and `Q ⟶ Hᵠ(L)`.

## Main results

* `Stacks.CupProduct.liftCycles_cupPair_homologyπ_eq_of_left_boundary` and
  `Stacks.CupProduct.liftCycles_cupPair_homologyπ_eq_of_right_boundary`: the class of a cup
  product of cochains is unchanged when either factor is changed by a coboundary — the graded
  Leibniz rule `Stacks.CupProduct.cupPair_comp_d` exhibits the difference as a coboundary.
  No projectivity is used here.
* `Stacks.CupProduct.liftCycles_cupPair_homologyπ_eq_cupClass`: consequently `cupClass` is
  computed by *any* pair of cocycle representatives, which is what makes it the cup product on
  cohomology rather than an artefact of the choice.
* `Stacks.CupProduct.gamma_cup_boundary_cupClass`: the identity for classes —
  `γ₁(∂a₃ ∪ b₁) = (-1)^{n+1} γ₃(a₃ ∪ ∂b₁)` in `H^{n+m+1}(H)`, with `∂` the connecting morphisms
  of the two short exact sequences of complexes and no cochain-level data in the statement.
* `Stacks.CupProduct.gamma_cup_boundary_rep`: the same identity at the level of cochains, for
  arbitrary representatives — the identity holds for *arbitrary* cocycle representatives `α₁` of
  `∂a₃` and `β₃` of `∂b₁`, rather than only for ones produced from a chosen lift as in
  `Stacks.CupProduct.gamma_cup_boundary_delta`.

## Implementation notes

The cup product of classes is *not* definable for a general test object `P`: a class
`P ⟶ Hⁱ(K)` lifts to a cocycle only along the epimorphism `Hⁱ(K)`-wards from the cycles, and
only `P` projective makes that lift exist.  For a general `P` Mathlib's calculus of refinements
gives the lift after an epimorphism `A' ↠ P`, which is what
`HomologicalComplex.eq_liftCycles_homologyπ_up_to_refinements` says; projectivity of `P` is
exactly what splits that epimorphism.  Both directions of "same class iff differ by a
coboundary" are used: the hard direction (equal classes give a coboundary) needs `P` projective,
the easy one does not.

`Φ` is assumed additive in each variable, which is what lets a cup product be expanded along a
sum of cochains; in the source `Φ = ⊗_𝐙`, which is additive in each variable.

For the statement of Tag 07MC on a topological space, with the total Čech complexes of an open
covering, see `Stacks.Cech.Hypercohomology.cup_boundary`.

## References

* [Stacks Project, Tag 07MC](https://stacks.math.columbia.edu/tag/07MC)
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits ComplexShape

universe v₁ v₂ v u₁ u₂ u

namespace Stacks.CupProduct

/-! ### Cocycle representatives of a class valued in a projective object -/

section Rep

variable {C : Type u₁} [Category.{v₁} C] [Abelian C] {ι : Type*} {c : ComplexShape ι}

/-- **A class valued in a projective object is the class of an honest cocycle.**  Mathlib's
calculus of refinements produces a cocycle after an epimorphism `A' ⟶ P`, and projectivity of
`P` splits that epimorphism. -/
theorem exists_liftCycles_homologyπ_eq (K : HomologicalComplex C c) {P : C} [Projective P]
    (i j : ι) (hj : c.next i = j) (γ : P ⟶ K.homology i) :
    ∃ (z : P ⟶ K.X i) (hz : z ≫ K.d i j = 0),
      K.liftCycles z j hj hz ≫ K.homologyπ i = γ := by
  obtain ⟨A', π, hπ, z, hz, hzγ⟩ := K.eq_liftCycles_homologyπ_up_to_refinements γ j hj
  refine ⟨Projective.factorThru (𝟙 P) π ≫ z, by rw [Category.assoc, hz, comp_zero], ?_⟩
  rw [← K.comp_liftCycles z j hj hz (Projective.factorThru (𝟙 P) π), Category.assoc, ← hzγ,
    ← Category.assoc, Projective.factorThru_comp, Category.id_comp]

/-- **Two cocycles valued in a projective object with the same class differ by a coboundary.**
This is the direction of the comparison that needs projectivity. -/
theorem exists_eq_add_comp_d_of_liftCycles_homologyπ_eq (K : HomologicalComplex C c) {P : C}
    [Projective P] (i j k : ι) (hi : c.prev j = i) (hk : c.next j = k)
    (x x' : P ⟶ K.X j) (hx : x ≫ K.d j k = 0) (hx' : x' ≫ K.d j k = 0)
    (h : K.liftCycles x k hk hx ≫ K.homologyπ j = K.liftCycles x' k hk hx' ≫ K.homologyπ j) :
    ∃ σ : P ⟶ K.X i, x = x' + σ ≫ K.d i j := by
  rw [K.liftCycles_comp_homologyπ_eq_iff_up_to_refinements i j k hi hk x x' hx hx'] at h
  obtain ⟨A', π, hπ, x₁, hx₁⟩ := h
  refine ⟨Projective.factorThru (𝟙 P) π ≫ x₁, ?_⟩
  simpa only [Preadditive.comp_add, ← Category.assoc, Projective.factorThru_comp,
    Category.id_comp] using congrArg (Projective.factorThru (𝟙 P) π ≫ ·) hx₁

/-- **Two cocycles that differ by a coboundary have the same class.**  No projectivity. -/
theorem liftCycles_homologyπ_eq_of_eq_add_comp_d (K : HomologicalComplex C c) {P : C}
    (i j k : ι) (hi : c.prev j = i) (hk : c.next j = k)
    (x x' : P ⟶ K.X j) (hx : x ≫ K.d j k = 0) (hx' : x' ≫ K.d j k = 0)
    (σ : P ⟶ K.X i) (hσ : x = x' + σ ≫ K.d i j) :
    K.liftCycles x k hk hx ≫ K.homologyπ j = K.liftCycles x' k hk hx' ≫ K.homologyπ j := by
  rw [K.liftCycles_comp_homologyπ_eq_iff_up_to_refinements i j k hi hk x x' hx hx']
  exact ⟨P, 𝟙 P, inferInstance, σ, by rw [Category.id_comp, Category.id_comp, hσ]⟩

/-- A cocycle representative of a class valued in a projective object, chosen by
`exists_liftCycles_homologyπ_eq`. -/
noncomputable def cocycleRep (K : CochainComplex C ℤ) {P : C} [Projective P] (i : ℤ)
    (γ : P ⟶ K.homology i) : P ⟶ K.X i :=
  (exists_liftCycles_homologyπ_eq K i (i + 1) (CochainComplex.next ℤ i) γ).choose

/-- The cocycle representative `cocycleRep K i γ` is a cocycle: its differential vanishes. -/
@[simp]
theorem cocycleRep_comp_d (K : CochainComplex C ℤ) {P : C} [Projective P] (i : ℤ)
    (γ : P ⟶ K.homology i) : cocycleRep K i γ ≫ K.d i (i + 1) = 0 :=
  (exists_liftCycles_homologyπ_eq K i (i + 1) (CochainComplex.next ℤ i) γ).choose_spec.choose

/-- The cohomology class of the cocycle representative `cocycleRep K i γ` is `γ`. -/
@[simp]
theorem liftCycles_cocycleRep_homologyπ (K : CochainComplex C ℤ) {P : C} [Projective P] (i : ℤ)
    (γ : P ⟶ K.homology i) :
    K.liftCycles (cocycleRep K i γ) (i + 1) (CochainComplex.next ℤ i)
        (cocycleRep_comp_d K i γ) ≫ K.homologyπ i = γ :=
  (exists_liftCycles_homologyπ_eq K i (i + 1) (CochainComplex.next ℤ i) γ).choose_spec.choose_spec

end Rep

/-! ### A short exact sequence of complexes is degreewise epi in its second map -/

section Degreewise

variable {C : Type u₁} [Category.{v₁} C] [Abelian C] {ι : Type*} {c : ComplexShape ι}
  {S : ShortComplex (HomologicalComplex C c)}

/-- **A short exact sequence of complexes is degreewise epimorphic in its second map.** -/
theorem epi_g_f (hS : S.ShortExact) (k : ι) : Epi (S.g.f k) :=
  (hS.map_of_exact (HomologicalComplex.eval C c k)).epi_g

/-- A cochain of `S.X₂` killed by `S.g` comes from `S.X₁`, by degreewise exactness. -/
theorem exists_comp_f_f (hS : S.ShortExact) (k : ι) {P : C} (x : P ⟶ S.X₂.X k)
    (hx : x ≫ S.g.f k = 0) : ∃ y : P ⟶ S.X₁.X k, y ≫ S.f.f k = x := by
  have := (hS.map_of_exact (HomologicalComplex.eval C c k)).mono_f
  exact (hS.map_of_exact (HomologicalComplex.eval C c k)).exact.lift' x hx

/-- **A cochain of `S.X₃` valued in a projective object lifts to `S.X₂`.**  This is what
discharges the lift hypotheses `α₂`, `β₂` of `Stacks.CupProduct.gamma_cup_boundary_delta`, which
in the source are produced by refining the open covering. -/
theorem exists_comp_g_f (hS : S.ShortExact) (k : ι) {P : C} [Projective P] (x : P ⟶ S.X₃.X k) :
    ∃ y : P ⟶ S.X₂.X k, y ≫ S.g.f k = x := by
  have := epi_g_f hS k
  exact ⟨Projective.factorThru x (S.g.f k), Projective.factorThru_comp _ _⟩

end Degreewise

/-! ### The class of a cup product depends only on the classes of the two factors -/

section Invariance

variable {A : Type u₁} {B : Type u₂} {D : Type u}
  [Category.{v₁} A] [Category.{v₂} B] [Category.{v} D]
  [Preadditive A] [Preadditive B] [Abelian D]
  (Φ : A ⥤ B ⥤ D) [Φ.Additive] [∀ X, (Φ.obj X).Additive]

/-- The cup product is additive in its first factor. -/
lemma cupPair_add_left {P : A} {Q : B} (K : CochainComplex A ℤ) (L : CochainComplex B ℤ)
    [HomologicalComplex.HasMapBifunctor K L Φ (up ℤ)] (p q t : ℤ) (ht : p + q = t)
    (α α' : P ⟶ K.X p) (β : Q ⟶ L.X q) :
    cupPair Φ K L p q t ht (α + α') β =
      cupPair Φ K L p q t ht α β + cupPair Φ K L p q t ht α' β := by
  simp only [cupPair, Φ.map_add, NatTrans.app_add, Preadditive.add_comp]

/-- The cup product is additive in its second factor. -/
lemma cupPair_add_right {P : A} {Q : B} (K : CochainComplex A ℤ) (L : CochainComplex B ℤ)
    [HomologicalComplex.HasMapBifunctor K L Φ (up ℤ)] (p q t : ℤ) (ht : p + q = t)
    (α : P ⟶ K.X p) (β β' : Q ⟶ L.X q) :
    cupPair Φ K L p q t ht α (β + β') =
      cupPair Φ K L p q t ht α β + cupPair Φ K L p q t ht α β' := by
  simp only [cupPair, Functor.map_add, Preadditive.add_comp, Preadditive.comp_add]

private lemma negOnePow_smul_negOnePow_smul {G : Type*} [AddCommGroup G] (p : ℤ) (x : G) :
    (p.negOnePow : ℤ) • ((p.negOnePow : ℤ) • x) = x := by
  rw [smul_smul, ← Units.val_mul, Int.units_mul_self, Units.val_one, one_smul]

/-- **Changing the first cochain by a coboundary does not change the class of the cup product.**
If `α = α' + d(σ)` and `β` is a cocycle, the graded Leibniz rule `cupPair_comp_d` exhibits
`α ∪ β - α' ∪ β` as the coboundary of `σ ∪ β`. -/
theorem liftCycles_cupPair_homologyπ_eq_of_left_boundary {P : A} {Q : B}
    (K : CochainComplex A ℤ) (L : CochainComplex B ℤ)
    [HomologicalComplex.HasMapBifunctor K L Φ (up ℤ)]
    (p' p q s t : ℤ) (hp : p' + 1 = p) (hs : p' + q = s) (ht : s + 1 = t)
    (α α' : P ⟶ K.X p) (hα : α ≫ K.d p (p + 1) = 0) (hα' : α' ≫ K.d p (p + 1) = 0)
    (β : Q ⟶ L.X q) (hβ : β ≫ L.d q (q + 1) = 0)
    (σ : P ⟶ K.X p') (hσ : α = α' + σ ≫ K.d p' p) :
    (HomologicalComplex.mapBifunctor K L Φ (up ℤ)).liftCycles
          (cupPair Φ K L p q t (by omega) α β) (t + 1) (CochainComplex.next ℤ t)
          (cupPair_comp_d_eq_zero Φ K L p q t (by omega) α β hα hβ) ≫
        (HomologicalComplex.mapBifunctor K L Φ (up ℤ)).homologyπ t =
      (HomologicalComplex.mapBifunctor K L Φ (up ℤ)).liftCycles
          (cupPair Φ K L p q t (by omega) α' β) (t + 1) (CochainComplex.next ℤ t)
          (cupPair_comp_d_eq_zero Φ K L p q t (by omega) α' β hα' hβ) ≫
        (HomologicalComplex.mapBifunctor K L Φ (up ℤ)).homologyπ t := by
  subst hp ht
  have hLeib := cupPair_comp_d Φ K L p' q s hs σ β
  rw [hβ, cupPair_zero_right, smul_zero, add_zero] at hLeib
  refine liftCycles_homologyπ_eq_of_eq_add_comp_d _ s (s + 1) (s + 1 + 1)
    (by rw [CochainComplex.prev]; omega) (CochainComplex.next ℤ (s + 1)) _ _ _ _
    (cupPair Φ K L p' q s hs σ β) ?_
  rw [hσ, cupPair_add_left, hLeib]

/-- **Changing the second cochain by a coboundary does not change the class of the cup
product.**  If `β = β' + d(τ)` and `α` is a cocycle, the graded Leibniz rule `cupPair_comp_d`
exhibits `α ∪ β - α ∪ β'` as the coboundary of `(-1)^p (α ∪ τ)`. -/
theorem liftCycles_cupPair_homologyπ_eq_of_right_boundary {P : A} {Q : B}
    (K : CochainComplex A ℤ) (L : CochainComplex B ℤ)
    [HomologicalComplex.HasMapBifunctor K L Φ (up ℤ)]
    (p q' q s t : ℤ) (hq : q' + 1 = q) (hs : p + q' = s) (ht : s + 1 = t)
    (α : P ⟶ K.X p) (hα : α ≫ K.d p (p + 1) = 0)
    (β β' : Q ⟶ L.X q) (hβ : β ≫ L.d q (q + 1) = 0) (hβ' : β' ≫ L.d q (q + 1) = 0)
    (τ : Q ⟶ L.X q') (hτ : β = β' + τ ≫ L.d q' q) :
    (HomologicalComplex.mapBifunctor K L Φ (up ℤ)).liftCycles
          (cupPair Φ K L p q t (by omega) α β) (t + 1) (CochainComplex.next ℤ t)
          (cupPair_comp_d_eq_zero Φ K L p q t (by omega) α β hα hβ) ≫
        (HomologicalComplex.mapBifunctor K L Φ (up ℤ)).homologyπ t =
      (HomologicalComplex.mapBifunctor K L Φ (up ℤ)).liftCycles
          (cupPair Φ K L p q t (by omega) α β') (t + 1) (CochainComplex.next ℤ t)
          (cupPair_comp_d_eq_zero Φ K L p q t (by omega) α β' hα hβ') ≫
        (HomologicalComplex.mapBifunctor K L Φ (up ℤ)).homologyπ t := by
  subst hq ht
  have hLeib := cupPair_comp_d Φ K L p q' s hs α τ
  rw [hα, cupPair_zero_left, zero_add] at hLeib
  have hkey : cupPair Φ K L p (q' + 1) (s + 1) (by omega) α (τ ≫ L.d q' (q' + 1)) =
      (p.negOnePow : ℤ) •
        (cupPair Φ K L p q' s hs α τ ≫
          (HomologicalComplex.mapBifunctor K L Φ (up ℤ)).d s (s + 1)) := by
    rw [hLeib, negOnePow_smul_negOnePow_smul]
  refine liftCycles_homologyπ_eq_of_eq_add_comp_d _ s (s + 1) (s + 1 + 1)
    (by rw [CochainComplex.prev]; omega) (CochainComplex.next ℤ (s + 1)) _ _ _ _
    ((p.negOnePow : ℤ) • cupPair Φ K L p q' s hs α τ) ?_
  rw [hτ, cupPair_add_right, hkey, Preadditive.zsmul_comp]

end Invariance

/-! ### The cup product of two cohomology classes -/

section Class

variable {A : Type u₁} {B : Type u₂} {D : Type u}
  [Category.{v₁} A] [Category.{v₂} B] [Category.{v} D]
  [Abelian A] [Abelian B] [Abelian D]
  (Φ : A ⥤ B ⥤ D) [Φ.Additive] [∀ X, (Φ.obj X).Additive]

/-- **The cup product of two cohomology classes.**  A `P`-valued class of `Hᵖ(K)` and a
`Q`-valued class of `Hᵠ(L)` are cupped by cupping cocycle representatives; the result is
independent of the representatives by `liftCycles_cupPair_homologyπ_eq_cupClass`. -/
noncomputable def cupClass (K : CochainComplex A ℤ) (L : CochainComplex B ℤ)
    [HomologicalComplex.HasMapBifunctor K L Φ (up ℤ)] {P : A} {Q : B} [Projective P]
    [Projective Q] (p q t : ℤ) (ht : p + q = t) (a : P ⟶ K.homology p)
    (b : Q ⟶ L.homology q) :
    (Φ.obj P).obj Q ⟶ (HomologicalComplex.mapBifunctor K L Φ (up ℤ)).homology t :=
  (HomologicalComplex.mapBifunctor K L Φ (up ℤ)).liftCycles
      (cupPair Φ K L p q t ht (cocycleRep K p a) (cocycleRep L q b)) (t + 1)
      (CochainComplex.next ℤ t)
      (cupPair_comp_d_eq_zero Φ K L p q t ht _ _ (cocycleRep_comp_d K p a)
        (cocycleRep_comp_d L q b)) ≫
    (HomologicalComplex.mapBifunctor K L Φ (up ℤ)).homologyπ t

/-- **`cupClass` is computed by any pair of cocycle representatives.**  This is what makes it
the cup product on cohomology rather than an artefact of the chosen representatives. -/
theorem liftCycles_cupPair_homologyπ_eq_cupClass (K : CochainComplex A ℤ)
    (L : CochainComplex B ℤ) [HomologicalComplex.HasMapBifunctor K L Φ (up ℤ)] {P : A} {Q : B}
    [Projective P] [Projective Q] (p q t : ℤ) (ht : p + q = t) (a : P ⟶ K.homology p)
    (b : Q ⟶ L.homology q) (z : P ⟶ K.X p) (hz : z ≫ K.d p (p + 1) = 0)
    (hza : K.liftCycles z (p + 1) (CochainComplex.next ℤ p) hz ≫ K.homologyπ p = a)
    (w : Q ⟶ L.X q) (hw : w ≫ L.d q (q + 1) = 0)
    (hwb : L.liftCycles w (q + 1) (CochainComplex.next ℤ q) hw ≫ L.homologyπ q = b) :
    (HomologicalComplex.mapBifunctor K L Φ (up ℤ)).liftCycles
          (cupPair Φ K L p q t ht z w) (t + 1) (CochainComplex.next ℤ t)
          (cupPair_comp_d_eq_zero Φ K L p q t ht z w hz hw) ≫
        (HomologicalComplex.mapBifunctor K L Φ (up ℤ)).homologyπ t =
      cupClass Φ K L p q t ht a b := by
  obtain ⟨σ, hσ⟩ := exists_eq_add_comp_d_of_liftCycles_homologyπ_eq K (p - 1) p (p + 1)
    (CochainComplex.prev ℤ p) (CochainComplex.next ℤ p) z (cocycleRep K p a) hz
    (cocycleRep_comp_d K p a) (by rw [hza, liftCycles_cocycleRep_homologyπ])
  obtain ⟨τ, hτ⟩ := exists_eq_add_comp_d_of_liftCycles_homologyπ_eq L (q - 1) q (q + 1)
    (CochainComplex.prev ℤ q) (CochainComplex.next ℤ q) w (cocycleRep L q b) hw
    (cocycleRep_comp_d L q b) (by rw [hwb, liftCycles_cocycleRep_homologyπ])
  exact (liftCycles_cupPair_homologyπ_eq_of_left_boundary Φ K L (p - 1) p q (p - 1 + q) t
    (by omega) rfl (by omega) z (cocycleRep K p a) hz (cocycleRep_comp_d K p a) w hw
    σ hσ).trans
      (liftCycles_cupPair_homologyπ_eq_of_right_boundary Φ K L p (q - 1) q (p + (q - 1)) t
        (by omega) rfl (by omega) (cocycleRep K p a) (cocycleRep_comp_d K p a) w
        (cocycleRep L q b) hw (cocycleRep_comp_d L q b) τ hτ)

/-- `cupClass` followed by the map induced by a pairing `γ` out of the total complex, computed
by any pair of cocycle representatives. -/
theorem liftCycles_cupPair_comp_gamma_homologyπ_eq_cupClass (K : CochainComplex A ℤ)
    (L : CochainComplex B ℤ) [HomologicalComplex.HasMapBifunctor K L Φ (up ℤ)]
    {H : CochainComplex D ℤ} (γ : HomologicalComplex.mapBifunctor K L Φ (up ℤ) ⟶ H)
    {P : A} {Q : B} [Projective P] [Projective Q] (p q t : ℤ) (ht : p + q = t)
    (a : P ⟶ K.homology p) (b : Q ⟶ L.homology q) (z : P ⟶ K.X p) (hz : z ≫ K.d p (p + 1) = 0)
    (hza : K.liftCycles z (p + 1) (CochainComplex.next ℤ p) hz ≫ K.homologyπ p = a)
    (w : Q ⟶ L.X q) (hw : w ≫ L.d q (q + 1) = 0)
    (hwb : L.liftCycles w (q + 1) (CochainComplex.next ℤ q) hw ≫ L.homologyπ q = b) :
    H.liftCycles (cupPair Φ K L p q t ht z w ≫ γ.f t) (t + 1) (CochainComplex.next ℤ t)
          (cupPair_comp_gamma_comp_d_eq_zero Φ K L γ p q t ht z w hz hw) ≫ H.homologyπ t =
      cupClass Φ K L p q t ht a b ≫ HomologicalComplex.homologyMap γ t := by
  rw [← liftCycles_cupPair_homologyπ_eq_cupClass Φ K L p q t ht a b z hz hza w hw hwb,
    Category.assoc, HomologicalComplex.homologyπ_naturality, ← Category.assoc,
    HomologicalComplex.liftCycles_comp_cyclesMap]

end Class

/-! ### A canonical choice of the three pairings -/

section Certificate

variable {A : Type u₁} {B : Type u₂} {D : Type u}
  [Category.{v₁} A] [Category.{v₂} B] [Category.{v} D]
  [Preadditive A] [Preadditive B] [Preadditive D]
  (Φ : A ⥤ B ⥤ D) [Φ.Additive] [∀ X, (Φ.obj X).Additive]
  {S : ShortComplex (CochainComplex A ℤ)} {T : ShortComplex (CochainComplex B ℤ)}
  [HomologicalComplex.HasMapBifunctor S.X₁ T.X₂ Φ (up ℤ)]
  [HomologicalComplex.HasMapBifunctor S.X₁ T.X₃ Φ (up ℤ)]
  [HomologicalComplex.HasMapBifunctor S.X₂ T.X₁ Φ (up ℤ)]
  [HomologicalComplex.HasMapBifunctor S.X₂ T.X₂ Φ (up ℤ)]
  [HomologicalComplex.HasMapBifunctor S.X₂ T.X₃ Φ (up ℤ)]
  [HomologicalComplex.HasMapBifunctor S.X₃ T.X₁ Φ (up ℤ)]

omit [HomologicalComplex.HasMapBifunctor S.X₂ T.X₁ Φ (up ℤ)]
  [HomologicalComplex.HasMapBifunctor S.X₃ T.X₁ Φ (up ℤ)] in
/-- **The first commutative square of the source holds for a canonical, nonzero, choice of the
pairings.**  Take `H := Tot(Φ(F₂, G₁))`, let `γ₁` be the map induced by `F₁ ⟶ F₂` and `γ₂` the
map induced by `G₂ ⟶ G₁`.  The first square is then the naturality of `Φ` in its two variables.
Together with `canonical_gamma_compat₂` this is a non-vacuity certificate for the hypotheses
`h₁`, `h₂` of `gamma_cup_boundary_cupClass`: nothing in them forces the pairings to vanish. -/
theorem canonical_gamma_compat₁ :
    HomologicalComplex.mapBifunctorMap (𝟙 S.X₁) T.g Φ (up ℤ) ≫
        HomologicalComplex.mapBifunctorMap S.f (𝟙 T.X₃) Φ (up ℤ) =
      HomologicalComplex.mapBifunctorMap S.f (𝟙 T.X₂) Φ (up ℤ) ≫
        HomologicalComplex.mapBifunctorMap (𝟙 S.X₂) T.g Φ (up ℤ) := by
  ext j i₁ i₂ h
  simp

omit [HomologicalComplex.HasMapBifunctor S.X₁ T.X₂ Φ (up ℤ)]
  [HomologicalComplex.HasMapBifunctor S.X₁ T.X₃ Φ (up ℤ)] in
/-- **The second commutative square of the source holds for the same canonical pairings, with
`γ₃ = 0`**, because the composite `G₃ ⟶ G₂ ⟶ G₁` of a short complex is zero. -/
theorem canonical_gamma_compat₂ :
    HomologicalComplex.mapBifunctorMap (𝟙 S.X₂) T.f Φ (up ℤ) ≫
        HomologicalComplex.mapBifunctorMap (𝟙 S.X₂) T.g Φ (up ℤ) =
      HomologicalComplex.mapBifunctorMap S.g (𝟙 T.X₁) Φ (up ℤ) ≫
        (0 : HomologicalComplex.mapBifunctor S.X₃ T.X₁ Φ (up ℤ) ⟶
          HomologicalComplex.mapBifunctor S.X₂ T.X₃ Φ (up ℤ)) := by
  ext j i₁ i₂ h
  simp only [HomologicalComplex.comp_f, HomologicalComplex.ι_mapBifunctorMap_assoc,
    HomologicalComplex.ι_mapBifunctorMap, HomologicalComplex.id_f, CategoryTheory.Functor.map_id,
    NatTrans.id_app, Category.id_comp, HomologicalComplex.zero_f, comp_zero]
  rw [← Category.assoc, ← Functor.map_comp, ← HomologicalComplex.comp_f, T.zero]
  simp

end Certificate

/-! ### The identity for cohomology classes -/

section Main

variable {A : Type u₁} {B : Type u₂} {D : Type u}
  [Category.{v₁} A] [Category.{v₂} B] [Category.{v} D]
  [Abelian A] [Abelian B] [Abelian D]
  (Φ : A ⥤ B ⥤ D) [Φ.Additive] [∀ X, (Φ.obj X).Additive]
  {S : ShortComplex (CochainComplex A ℤ)} {T : ShortComplex (CochainComplex B ℤ)}
  {H : CochainComplex D ℤ}
  [HomologicalComplex.HasMapBifunctor S.X₁ T.X₃ Φ (up ℤ)]
  [HomologicalComplex.HasMapBifunctor S.X₁ T.X₂ Φ (up ℤ)]
  [HomologicalComplex.HasMapBifunctor S.X₂ T.X₂ Φ (up ℤ)]
  [HomologicalComplex.HasMapBifunctor S.X₂ T.X₁ Φ (up ℤ)]
  [HomologicalComplex.HasMapBifunctor S.X₃ T.X₁ Φ (up ℤ)]

/-- A projective-valued cocycle `z` of `S.X₃` lifts to `α₂` in `S.X₂`, and `d α₂` lifts to a cocycle
`α₁` of `S.X₁` whose class is `∂` of the class of `z`. -/
private theorem exists_lift_liftCycles_eq_δ {C : Type u₁} [Category.{v₁} C] [Abelian C]
    {S : ShortComplex (CochainComplex C ℤ)} (hS : S.ShortExact) {P : C} [Projective P] (n : ℤ)
    (a : P ⟶ S.X₃.homology n) (z : P ⟶ S.X₃.X n) (hz : z ≫ S.X₃.d n (n + 1) = 0)
    (hza : S.X₃.liftCycles z (n + 1) (CochainComplex.next ℤ n) hz ≫ S.X₃.homologyπ n = a) :
    ∃ (α₂ : P ⟶ S.X₂.X n) (_ : α₂ ≫ S.g.f n = z) (α₁ : P ⟶ S.X₁.X (n + 1))
      (_ : α₁ ≫ S.f.f (n + 1) = α₂ ≫ S.X₂.d n (n + 1)) (hα : α₁ ≫ S.X₁.d (n + 1) (n + 1 + 1) = 0),
      S.X₁.liftCycles α₁ (n + 1 + 1) (CochainComplex.next ℤ (n + 1)) hα ≫
        S.X₁.homologyπ (n + 1) = a ≫ hS.δ n (n + 1) rfl := by
  obtain ⟨α₂, hα₂⟩ := exists_comp_g_f hS n z
  obtain ⟨α₁, hα₁⟩ := exists_comp_f_f hS (n + 1) (α₂ ≫ S.X₂.d n (n + 1))
    (by rw [Category.assoc, ← S.g.comm, ← Category.assoc, hα₂, hz])
  have := mono_f_f hS (n + 1 + 1)
  exact ⟨α₂, hα₂, α₁, hα₁, comp_d_eq_zero_of_comp_eq_comp_d S.f n α₂ α₁ hα₁,
    by rw [liftCycles_homologyπ_eq_δ hS n z hz α₂ hα₂ α₁ hα₁, hza]⟩

/-- **The cup product and the boundary maps, for cohomology classes.**  For short exact
sequences `0 ⟶ F₁ ⟶ F₂ ⟶ F₃ ⟶ 0` of complexes of `A` and `0 ⟶ G₃ ⟶ G₂ ⟶ G₁ ⟶ 0` of complexes
of `B`, pairings `γᵢ : Tot(Φ(Fᵢ, Gᵢ)) ⟶ H` making the two squares commute, and classes
`a₃ ∈ Hⁿ(F₃)`, `b₁ ∈ Hᵐ(G₁)` valued in projective objects,

`γ₁(∂a₃ ∪ b₁) = (-1)^{n+1} γ₃(a₃ ∪ ∂b₁)`  in  `H^{n+m+1}(H)`,

where `∂` are the connecting morphisms of the two short exact sequences and `∪` is the cup
product on cohomology `Stacks.CupProduct.cupClass`.  The lifts of
`Stacks.CupProduct.gamma_cup_boundary_delta` are produced by `Stacks.CupProduct.exists_comp_g_f`
and `Stacks.CupProduct.exists_comp_f_f`. -/
theorem gamma_cup_boundary_cupClass (hS : S.ShortExact) (hT : T.ShortExact) {P : A} {Q : B}
    [Projective P] [Projective Q]
    (γ₁ : HomologicalComplex.mapBifunctor S.X₁ T.X₃ Φ (up ℤ) ⟶ H)
    (γ₂ : HomologicalComplex.mapBifunctor S.X₂ T.X₂ Φ (up ℤ) ⟶ H)
    (γ₃ : HomologicalComplex.mapBifunctor S.X₃ T.X₁ Φ (up ℤ) ⟶ H)
    (h₁ : HomologicalComplex.mapBifunctorMap (𝟙 S.X₁) T.g Φ (up ℤ) ≫ γ₁ =
      HomologicalComplex.mapBifunctorMap S.f (𝟙 T.X₂) Φ (up ℤ) ≫ γ₂)
    (h₂ : HomologicalComplex.mapBifunctorMap (𝟙 S.X₂) T.f Φ (up ℤ) ≫ γ₂ =
      HomologicalComplex.mapBifunctorMap S.g (𝟙 T.X₁) Φ (up ℤ) ≫ γ₃)
    (n m : ℤ) (a₃ : P ⟶ S.X₃.homology n) (b₁ : Q ⟶ T.X₃.homology m) :
    cupClass Φ S.X₁ T.X₃ (n + 1) m (n + m + 1) (by omega) (a₃ ≫ hS.δ n (n + 1) rfl) b₁ ≫
        HomologicalComplex.homologyMap γ₁ (n + m + 1) =
      ((n + 1).negOnePow : ℤ) •
        (cupClass Φ S.X₃ T.X₁ n (m + 1) (n + m + 1) (by omega) a₃ (b₁ ≫ hT.δ m (m + 1) rfl) ≫
          HomologicalComplex.homologyMap γ₃ (n + m + 1)) := by
  obtain ⟨a₃', ha₃', ha₃cls⟩ :=
    exists_liftCycles_homologyπ_eq S.X₃ n (n + 1) (CochainComplex.next ℤ n) a₃
  obtain ⟨b₁', hb₁', hb₁cls⟩ :=
    exists_liftCycles_homologyπ_eq T.X₃ m (m + 1) (CochainComplex.next ℤ m) b₁
  obtain ⟨α₂, hα₂, α₁, hα₁, hα₁c, hα₁cls⟩ := exists_lift_liftCycles_eq_δ hS n a₃ a₃' ha₃' ha₃cls
  obtain ⟨β₂, hβ₂, β₃, hβ₃, hβ₃c, hβ₃cls⟩ := exists_lift_liftCycles_eq_δ hT m b₁ b₁' hb₁' hb₁cls
  rw [← liftCycles_cupPair_comp_gamma_homologyπ_eq_cupClass Φ S.X₁ T.X₃ γ₁ (n + 1) m
      (n + m + 1) (by omega) (a₃ ≫ hS.δ n (n + 1) rfl) b₁ α₁ hα₁c hα₁cls b₁' hb₁' hb₁cls,
    ← liftCycles_cupPair_comp_gamma_homologyπ_eq_cupClass Φ S.X₃ T.X₁ γ₃ n (m + 1)
      (n + m + 1) (by omega) a₃ (b₁ ≫ hT.δ m (m + 1) rfl) a₃' ha₃' ha₃cls β₃ hβ₃c hβ₃cls]
  exact gamma_cup_boundary_delta Φ hS hT γ₁ γ₂ γ₃ h₁ h₂ n m a₃' ha₃' b₁' hb₁' α₂ hα₂ β₂ hβ₂
    α₁ hα₁ β₃ hβ₃

/-- **The cup product and the boundary maps, for arbitrary cocycle representatives.**  The
identity of `Stacks.CupProduct.gamma_cup_boundary_delta` holds for arbitrary cocycles `α₁`
representing `∂a₃` and `β₃` representing `∂b₁`, not only for ones produced from lifts `α₂`,
`β₂`: the classes agree by `Stacks.CupProduct.liftCycles_cupPair_homologyπ_eq_cupClass` and
`Stacks.CupProduct.gamma_cup_boundary_cupClass`. -/
theorem gamma_cup_boundary_rep (hS : S.ShortExact) (hT : T.ShortExact) {P : A} {Q : B}
    [Projective P] [Projective Q]
    (γ₁ : HomologicalComplex.mapBifunctor S.X₁ T.X₃ Φ (up ℤ) ⟶ H)
    (γ₂ : HomologicalComplex.mapBifunctor S.X₂ T.X₂ Φ (up ℤ) ⟶ H)
    (γ₃ : HomologicalComplex.mapBifunctor S.X₃ T.X₁ Φ (up ℤ) ⟶ H)
    (h₁ : HomologicalComplex.mapBifunctorMap (𝟙 S.X₁) T.g Φ (up ℤ) ≫ γ₁ =
      HomologicalComplex.mapBifunctorMap S.f (𝟙 T.X₂) Φ (up ℤ) ≫ γ₂)
    (h₂ : HomologicalComplex.mapBifunctorMap (𝟙 S.X₂) T.f Φ (up ℤ) ≫ γ₂ =
      HomologicalComplex.mapBifunctorMap S.g (𝟙 T.X₁) Φ (up ℤ) ≫ γ₃)
    (n m : ℤ) (a₃ : P ⟶ S.X₃.homology n) (b₁ : Q ⟶ T.X₃.homology m)
    (z : P ⟶ S.X₃.X n) (hz : z ≫ S.X₃.d n (n + 1) = 0)
    (hza : S.X₃.liftCycles z (n + 1) (CochainComplex.next ℤ n) hz ≫ S.X₃.homologyπ n = a₃)
    (w : Q ⟶ T.X₃.X m) (hw : w ≫ T.X₃.d m (m + 1) = 0)
    (hwb : T.X₃.liftCycles w (m + 1) (CochainComplex.next ℤ m) hw ≫ T.X₃.homologyπ m = b₁)
    (α₁ : P ⟶ S.X₁.X (n + 1)) (hα₁ : α₁ ≫ S.X₁.d (n + 1) (n + 1 + 1) = 0)
    (hα₁cls : S.X₁.liftCycles α₁ (n + 1 + 1) (CochainComplex.next ℤ (n + 1)) hα₁ ≫
      S.X₁.homologyπ (n + 1) = a₃ ≫ hS.δ n (n + 1) rfl)
    (β₃ : Q ⟶ T.X₁.X (m + 1)) (hβ₃ : β₃ ≫ T.X₁.d (m + 1) (m + 1 + 1) = 0)
    (hβ₃cls : T.X₁.liftCycles β₃ (m + 1 + 1) (CochainComplex.next ℤ (m + 1)) hβ₃ ≫
      T.X₁.homologyπ (m + 1) = b₁ ≫ hT.δ m (m + 1) rfl) :
    H.liftCycles (cupPair Φ S.X₁ T.X₃ (n + 1) m (n + m + 1) (by omega) α₁ w ≫
            γ₁.f (n + m + 1)) (n + m + 1 + 1) (CochainComplex.next ℤ (n + m + 1))
          (cupPair_comp_gamma_comp_d_eq_zero Φ S.X₁ T.X₃ γ₁ (n + 1) m (n + m + 1) (by omega)
            α₁ w hα₁ hw) ≫
        H.homologyπ (n + m + 1) =
      ((n + 1).negOnePow : ℤ) •
        (H.liftCycles (cupPair Φ S.X₃ T.X₁ n (m + 1) (n + m + 1) (by omega) z β₃ ≫
              γ₃.f (n + m + 1)) (n + m + 1 + 1) (CochainComplex.next ℤ (n + m + 1))
            (cupPair_comp_gamma_comp_d_eq_zero Φ S.X₃ T.X₁ γ₃ n (m + 1) (n + m + 1) (by omega)
              z β₃ hz hβ₃) ≫
          H.homologyπ (n + m + 1)) := by
  rw [liftCycles_cupPair_comp_gamma_homologyπ_eq_cupClass Φ S.X₁ T.X₃ γ₁ (n + 1) m (n + m + 1)
      (by omega) (a₃ ≫ hS.δ n (n + 1) rfl) b₁ α₁ hα₁ hα₁cls w hw hwb,
    liftCycles_cupPair_comp_gamma_homologyπ_eq_cupClass Φ S.X₃ T.X₁ γ₃ n (m + 1) (n + m + 1)
      (by omega) a₃ (b₁ ≫ hT.δ m (m + 1) rfl) z hz hza β₃ hβ₃ hβ₃cls]
  exact gamma_cup_boundary_cupClass Φ hS hT γ₁ γ₂ γ₃ h₁ h₂ n m a₃ b₁

end Main

end Stacks.CupProduct

end
