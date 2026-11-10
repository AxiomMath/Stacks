module

public import Mathlib.Algebra.Homology.DerivedCategory.HomologySequence
public import Mathlib.Algebra.Homology.HomotopyCategory.HomComplexSingle
public import Mathlib.Algebra.Homology.SingleHomology
public import Mathlib.CategoryTheory.Monoidal.Rigid.Basic
public import StacksFrontier.Algebra.Homology.KoszulSymmetric
public import StacksFrontier.Homology.HomComplex.ProjectiveRHom
public import StacksFrontier.Homology.KFlat.Flat
public import StacksFrontier.Homology.KFlat.Resolution
public import StacksFrontier.Homology.LeftDual
public import StacksFrontier.Homology.Perfect.Basic
public import StacksFrontier.Homology.Perfect.Duality.DerivedDual
import StacksCore.Tactic.StacksAttribute

/-!
# Tensor products and Tor amplitude of perfect complexes

Let `A` be a ring. This file proves that the derived tensor product of two perfect objects of
`D(A)` is perfect, and that dualizing a perfect complex reverses its Tor amplitude.

## Main results

* `StacksDraft.Perfect.isPerfect_derivedTensorProduct` ([stacks 0GM0]): the derived tensor
  product of two perfect objects is perfect.
* `StacksDraft.Perfect.hasFlatRepresentative_derivedDual` ([stacks 0H81]): if a perfect object has
  Tor amplitude in `[a, b]` then its derived dual has Tor amplitude in `[-b, -a]`.

## References

* [Stacks Project, Tag 0GM0](https://stacks.math.columbia.edu/tag/0GM0)
* [Stacks Project, Tag 0H81](https://stacks.math.columbia.edu/tag/0H81)
-/

@[expose] public noncomputable section

open CategoryTheory MonoidalCategory CochainComplex CochainComplex.HomComplex
  HomologicalComplex

universe u v w

namespace StacksDraft.Perfect

open StacksDraft.DerivedHom Stacks.HomComplex.MonoidalClosed

variable {R : Type u} [CommRing R]
  [HasDerivedCategory.{w} (ModuleCat.{max u v} (ULift.{v} R))]

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

/-! ## Derived tensor products of perfect complexes -/

section TensorProduct

/-- A direct sum of finite modules, all but finitely many of which vanish, is finite. -/
private lemma finite_directSum_of_support {S : Type u} [CommRing S] {J : Type*}
    (F : J → Type u) [∀ j, AddCommGroup (F j)] [∀ j, Module S (F j)]
    (s : Finset J) (hfin : ∀ j, Module.Finite S (F j))
    (hzero : ∀ j ∉ s, Subsingleton (F j)) :
    Module.Finite S (DirectSum J F) := by
  classical
  have hsurj : Function.Surjective
      (DirectSum.toModule S ↥s (DirectSum J F)
        (fun j : ↥s => DirectSum.lof S J F j.1)) := by
    intro x
    induction x using DirectSum.induction_on with
    | zero => exact ⟨0, map_zero _⟩
    | of j y =>
        by_cases hj : j ∈ s
        · refine ⟨DirectSum.lof S ↥s (fun k : ↥s => F k.1) ⟨j, hj⟩ y, ?_⟩
          rw [DirectSum.toModule_lof, DirectSum.lof_eq_of]
        · refine ⟨0, ?_⟩
          have hy : y = 0 := (hzero j hj).elim y 0
          rw [hy, map_zero, map_zero]
    | add x y hx hy =>
        obtain ⟨a, ha⟩ := hx
        obtain ⟨b, hb⟩ := hy
        exact ⟨a + b, by rw [map_add, ha, hb]⟩
  let : ∀ j, Module.Finite S (F j) := hfin
  let : Module.Finite S (∀ j : ↥s, F j.1) := Module.Finite.pi
  let : Module.Finite S (DirectSum ↥s (fun j : ↥s => F j.1)) :=
    Module.Finite.equiv
      (DirectSum.linearEquivFunOnFintype S ↥s (fun j : ↥s => F j.1)).symm
  exact Module.Finite.of_surjective _ hsurj

/-- The tensor product of two modules is zero if one of them is. -/
private lemma isZero_tensor_of_isZero_or {S : Type u} [CommRing S] {X Y : ModuleCat.{u} S}
    (h : Limits.IsZero X ∨ Limits.IsZero Y) : Limits.IsZero (X ⊗ Y) :=
  h.elim (fun hX ↦ (tensorRight Y).map_isZero hX) fun hY ↦ (tensorLeft X).map_isZero hY

/-- Boundedness of the total tensor complex from below. -/
private lemma tensor_isStrictlyGE {S : Type u} [CommRing S]
    (P Q : CochainComplex (ModuleCat.{u} S) ℤ) (a b : ℤ)
    [P.IsStrictlyGE a] [Q.IsStrictlyGE b] :
    CochainComplex.IsStrictlyGE (HomologicalComplex.tensorObj P Q) (a + b) := by
  rw [CochainComplex.isStrictlyGE_iff]
  intro i hi
  apply (Limits.IsZero.iff_id_eq_zero _).mpr
  apply HomologicalComplex.mapBifunctor.hom_ext
  intro p q hpq
  refine (isZero_tensor_of_isZero_or ?_).eq_of_src _ _
  by_cases hp : p < a
  · exact .inl (P.isZero_of_isStrictlyGE a p hp)
  · exact .inr (Q.isZero_of_isStrictlyGE b q (by dsimp at hpq; omega))

/-- The terms of the total tensor complex of two bounded complexes of finite projective modules
are finite and projective. -/
private lemma tensor_X_finite_projective {S : Type u} [CommRing S]
    (P Q : CochainComplex (ModuleCat.{u} S) ℤ) (a b c d : ℤ)
    [P.IsStrictlyGE a] [P.IsStrictlyLE b] [Q.IsStrictlyGE c] [Q.IsStrictlyLE d]
    (hPfin : ∀ i, Module.Finite S (P.X i)) (hPproj : ∀ i, Module.Projective S (P.X i))
    (hQfin : ∀ i, Module.Finite S (Q.X i)) (hQproj : ∀ i, Module.Projective S (Q.X i))
    (i : ℤ) :
    Module.Finite S ((HomologicalComplex.tensorObj P Q).X i) ∧
      Module.Projective S ((HomologicalComplex.tensorObj P Q).X i) := by
  classical
  let (j : ℤ) : Module.Finite S (P.X j) := hPfin j
  let (j : ℤ) : Module.Projective S (P.X j) := hPproj j
  let (j : ℤ) : Module.Finite S (Q.X j) := hQfin j
  let (j : ℤ) : Module.Projective S (Q.X j) := hQproj j
  let J := {pq : ℤ × ℤ // pq.1 + pq.2 = i}
  let F : J → ModuleCat.{u} S := fun pq ↦ P.X pq.1.1 ⊗ Q.X pq.1.2
  have hFfin : ∀ j, Module.Finite S (F j) := fun j ↦ by
    change Module.Finite S (TensorProduct S (P.X j.1.1) (Q.X j.1.2))
    infer_instance
  have hFproj : ∀ j, Module.Projective S (F j) := fun j ↦ by
    change Module.Projective S (TensorProduct S (P.X j.1.1) (Q.X j.1.2))
    exact Module.Projective.tensorProduct
  have hsupport : ∀ j ∉ (((Finset.Icc a b) ×ˢ (Finset.Icc c d)).subtype
      (fun pq : ℤ × ℤ ↦ pq.1 + pq.2 = i)), Subsingleton (F j) := by
    intro j hj
    rw [Finset.mem_subtype] at hj
    simp only [Finset.mem_product, Finset.mem_Icc, not_and_or, not_le] at hj
    refine ModuleCat.subsingleton_of_isZero (isZero_tensor_of_isZero_or ?_)
    rcases hj with (h | h) | (h | h)
    · exact .inl (P.isZero_of_isStrictlyGE a _ h)
    · exact .inl (P.isZero_of_isStrictlyLE b _ h)
    · exact .inr (Q.isZero_of_isStrictlyGE c _ h)
    · exact .inr (Q.isZero_of_isStrictlyLE d _ h)
  let : Module.Finite S (DirectSum J (fun j ↦ (F j : Type u))) :=
    finite_directSum_of_support (S := S) (fun j ↦ (F j : Type u)) _ hFfin hsupport
  let : Module.Projective S (DirectSum J (fun j ↦ (F j : Type u))) :=
    Module.Projective.directSum
  have hiso := ModuleCat.coprodIsoDirectSum F
  exact ⟨Module.Finite.equiv hiso.toLinearEquiv.symm,
    Module.Projective.of_equiv hiso.toLinearEquiv.symm⟩

/-- **Stacks 0GM0.** The derived tensor product of two perfect objects of `D(A)` is perfect. -/
@[stacks 0GM0, sga "6 I 4.19" "D(R), R a ring"]
theorem isPerfect_derivedTensorProduct
    (K L : DerivedCategory (ModuleCat.{max u v} (ULift.{v} R)))
    (hK : IsPerfect K) (hL : IsPerfect L) :
    IsPerfect ((derivedHomData (R := R)).tensor.obj (K, L)) := by
  obtain ⟨P, a, b, hPge, hPle, hPfin, hPproj, ⟨eP⟩⟩ := hK
  obtain ⟨Q, c, d, hQge, hQle, hQfin, hQproj, ⟨eQ⟩⟩ := hL
  let : P.IsStrictlyGE a := hPge
  let : P.IsStrictlyLE b := hPle
  let : Q.IsStrictlyGE c := hQge
  let : Q.IsStrictlyLE d := hQle
  let (j : ℤ) : Module.Projective (ULift.{v} R) (Q.X j) := hQproj j
  have hQflat : Q.KFlat := kFlatOfFlat Q d
  have hterms := tensor_X_finite_projective P Q a b c d hPfin hPproj hQfin hQproj
  refine ⟨HomologicalComplex.tensorObj P Q, a + c, b + d,
    tensor_isStrictlyGE P Q a c, TotalTensorComplex.tensor_isStrictlyLE P Q b d,
    fun j ↦ (hterms j).1, fun j ↦ (hterms j).2, ⟨?_⟩⟩
  exact (derivedHomData (R := R)).tensor.mapIso (eP.prod eQ) ≪≫
    (derivedHomData (R := R)).tensorIso P Q hQflat

end TensorProduct

/-! ## Tor amplitude of the derived dual -/

section TorAmplitude

variable {A : Type u} [CommRing A]

attribute [local instance] HasDerivedCategory.standard

/-- The degree-`n` term of the Hom complex into the unit is the linear dual of the degree-`-n`
term. -/
noncomputable def homComplexTermLinearEquiv
    {S : Type*} [CommRing S] (P : CochainComplex (ModuleCat S) ℤ) (n : ℤ) :
    (CochainComplex.HomComplexR S P
        ((CochainComplex.singleFunctor (ModuleCat S) 0).obj (ModuleCat.of S S))).X n ≃ₗ[S]
      Module.Dual S (P.X (-n)) :=
  ((CochainComplex.HomComplex.Cochain.toSingleEquiv
      (K := P) (X := ModuleCat.of S S) (by omega : -n + n = 0)).toLinearEquiv
        (by
          intro (c : S) x
          ext y
          change c * _ = c * _
          rfl)).trans ModuleCat.homLinearEquiv

/-- The terms of the Hom complex into the unit of a complex of finite projective modules are
projective, hence flat. -/
private lemma homComplexTerm_flat
    {S : Type*} [CommRing S] (P : CochainComplex (ModuleCat S) ℤ)
    (hfinite : ∀ i, Module.Finite S (P.X i))
    (hprojective : ∀ i, Module.Projective S (P.X i)) (n : ℤ) :
    Module.Flat S
      ((CochainComplex.HomComplexR S P
        ((CochainComplex.singleFunctor (ModuleCat S) 0).obj (ModuleCat.of S S))).X n) := by
  let := hfinite (-n)
  let := hprojective (-n)
  let : Module.Projective S (Module.Dual S (P.X (-n))) := inferInstance
  let : Module.Projective S
      ((CochainComplex.HomComplexR S P
        ((CochainComplex.singleFunctor (ModuleCat S) 0).obj (ModuleCat.of S S))).X n) :=
    Module.Projective.of_equiv' (homComplexTermLinearEquiv P n).symm
  exact Module.Flat.of_projective

/-- Where the complex vanishes, so does the Hom complex into the unit. -/
theorem homComplexTerm_isZero
    {S : Type*} [CommRing S] (P : CochainComplex (ModuleCat S) ℤ) (n : ℤ)
    (h : CategoryTheory.Limits.IsZero (P.X (-n))) :
    CategoryTheory.Limits.IsZero
      ((CochainComplex.HomComplexR S P
        ((CochainComplex.singleFunctor (ModuleCat S) 0).obj (ModuleCat.of S S))).X n) := by
  apply ModuleCat.isZero_iff_subsingleton.mpr
  let : Subsingleton (P.X (-n)) := ModuleCat.isZero_iff_subsingleton.mp h
  exact (homComplexTermLinearEquiv P n).injective.subsingleton

/-- **Stacks 0H81.** If a perfect complex has Tor amplitude in `[a, b]` -- that is, a flat
representative supported in `[a, b]` -- then its derived dual has Tor amplitude in `[-b, -a]`. -/
@[stacks 0H81, sga "6 I 7.3" "finite Tor-dim stability"]
theorem hasFlatRepresentative_derivedDual
    (K : DerivedCategory (ModuleCat.{max u v} (ULift.{v} A)))
    (hK : IsPerfect K) {a b : ℤ}
    (hKamp : HasFlatRepresentative K a b) :
    HasFlatRepresentative (derivedDual K) (-b) (-a) := by
  let S := ULift.{v} A
  obtain ⟨hpseudo, -⟩ :=
    (isPerfect_iff_pseudoCoherent_and_finiteTorDimension K).1.mp hK
  obtain ⟨P, hP, hPGE, hPLE, ⟨i⟩⟩ :=
    (isPerfect_iff_pseudoCoherent_and_finiteTorDimension K).2 a b hpseudo hKamp
  let E := CochainComplex.HomComplexR S P (unitComplex (R := A))
  refine ⟨E, homComplexTerm_flat P (fun j ↦ (hP j).1) (fun j ↦ (hP j).2), ?_, ?_, ?_⟩
  · rw [CochainComplex.isStrictlyGE_iff]
    intro n hn
    exact homComplexTerm_isZero P n
      (CochainComplex.isZero_of_isStrictlyLE P b (-n) (by omega))
  · rw [CochainComplex.isStrictlyLE_iff]
    intro n hn
    exact homComplexTerm_isZero P n
      (CochainComplex.isZero_of_isStrictlyGE P a (-n) (by omega))
  · let D := derivedHomData (R := A)
    let p := projectiveHomComparisonULift (R := A)
    let : P.IsStrictlyLE b := hPLE
    let : ∀ j, Module.Projective S (P.X j) := fun j ↦ (hP j).2
    exact ⟨D.hom.mapIso (i.symm.op.prod (Iso.refl _)) ≪≫
      p.iso P (unitComplex (R := A)) b⟩

end TorAmplitude

end StacksDraft.Perfect

end
