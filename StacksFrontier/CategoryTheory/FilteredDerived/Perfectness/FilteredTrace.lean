module

public import Mathlib.Algebra.BigOperators.Finprod
public import StacksCore.Tactic.StacksAttribute
public import StacksFrontier.CategoryTheory.FilteredDerived.Category.BoundedEquivalence
public import StacksFrontier.CategoryTheory.FilteredDerived.Category.Projective
public import StacksFrontier.CategoryTheory.FilteredDerived.Perfectness.FilteredModuleTrace
public import StacksFrontier.CategoryTheory.FilteredDerived.Perfectness.Trace
public import StacksFrontier.Homology.FilteredDerivedCategory.Triangulated

/-!
# Additivity of trace for a filtered perfect complex

The trace of an endomorphism of a filtered perfect complex is the sum of the traces of its graded
endomorphisms.

## Main definitions

* `CategoryTheory.FilteredDerived.FilteredPerfectData`: a bounded filtered finite projective
  representative of a filtered derived object.

## Main results

* `CategoryTheory.FilteredDerived.FilteredPerfectData.forgetPerfect` and
  `CategoryTheory.FilteredDerived.FilteredPerfectData.gradedPerfect`: the underlying and the
  graded derived objects of a filtered perfect complex are perfect.
* `CategoryTheory.FilteredDerived.perfectDerivedTrace_eq_sum_grDF`: additivity of trace along the
  filtration.

## Implementation notes

The category `DF_perf` of the source is represented by filtered derived objects together with a
bounded filtered finite projective representative, which is the data in `FilteredPerfectData`.
Both the underlying and the graded derived objects of such an object are perfect, so the trace of
an endomorphism of either is the one of Tag 03TI and can be computed on the corresponding complex
of modules. Additivity then reduces to the degreewise additivity of Tag 03TL, after exchanging
the two finitely supported sums over the degree and the filtration index.

Both the forgetful functor and the `p`-th graded functor are instances of the lift of an
additive functor inverting the filtered quasi-isomorphisms, so the comparison between the trace
of an endomorphism of a filtered derived object and the alternating trace of a representing
cochain map is proved once for such a lift and then instantiated twice.

## References

* [Stacks Project, Tag 03TK](https://stacks.math.columbia.edu/tag/03TK)
-/

@[expose] public noncomputable section

open CategoryTheory
open CategoryTheory.Limits Opposite
open scoped BigOperators

universe u v

namespace CategoryTheory.FilteredDerived

attribute [local instance] HasDerivedCategory.standard

/-- A filtered perfect derived object, represented by a bounded complex of
filtered finite-projective modules. -/
@[sga "4½ Rapport 4.4"]
public structure FilteredPerfectData (R : Type u) [Ring R] where
  /-- The filtered derived object. -/
  obj : CochainComplex.FilteredDerivedCategory (ModuleCat.{max u v} R)
  /-- The cochain complex of finite filtered modules representing `obj`. -/
  representative : CochainComplex (FiniteFilteredObject (ModuleCat.{max u v} R)) ℤ
  /-- The representative is bounded below and bounded above. -/
  bounded : CochainComplex.plus _ representative ∧ CochainComplex.minus _ representative
  /-- Every term of the representative is filtered finite projective. -/
  finiteProjective : ∀ i : ℤ, IsFilteredFiniteProjective (representative.X i)
  /-- The image of the representative in the filtered derived category is isomorphic to `obj`. -/
  iso : Nonempty ((CochainComplex.FilteredDerivedCategory.Qh
    (𝒜 := ModuleCat.{max u v} R)).obj
      ((HomotopyCategory.quotient _ _).obj representative) ≅ obj)

/-- The image of a bounded complex of filtered modules under an additive functor to modules is
a bounded complex of finite projective modules if all its terms are finite projective. -/
private lemma finiteProjectiveComplex_of_bounded (R : Type u) [Ring R]
    (G : FiniteFilteredObject (ModuleCat.{max u v} R) ⥤ ModuleCat.{max u v} R) [G.Additive]
    (P : CochainComplex (FiniteFilteredObject (ModuleCat.{max u v} R)) ℤ)
    (hbounded : CochainComplex.plus _ P ∧ CochainComplex.minus _ P)
    (h : ∀ i : ℤ, Module.Projective R (G.obj (P.X i)) ∧ Module.Finite R (G.obj (P.X i))) :
    finiteProjectiveComplex R ((G.mapHomologicalComplex (ComplexShape.up ℤ)).obj P) := by
  refine ⟨⟨?_, ?_⟩, h⟩
  · obtain ⟨n, hn⟩ := hbounded.1
    exact ⟨n, by let : P.IsStrictlyGE n := hn; infer_instance⟩
  · obtain ⟨n, hn⟩ := hbounded.2
    exact ⟨n, by let : P.IsStrictlyLE n := hn; infer_instance⟩

/-- The complex of underlying modules of a bounded complex of filtered finite projective modules
is a bounded complex of finite projective modules. -/
@[sga "4½ Rapport 4.4" "partial"]
private lemma finiteProjectiveComplex_forget (R : Type u) [Ring R]
    (P : CochainComplex (FiniteFilteredObject (ModuleCat.{max u v} R)) ℤ)
    (hbounded : CochainComplex.plus _ P ∧ CochainComplex.minus _ P)
    (hP : ∀ i : ℤ, IsFilteredFiniteProjective (P.X i)) :
    finiteProjectiveComplex R
      (((FiniteFilteredObject.forget (𝒜 := ModuleCat.{max u v} R)).mapHomologicalComplex
        (ComplexShape.up ℤ)).obj P) :=
  finiteProjectiveComplex_of_bounded R _ P hbounded fun i =>
    ⟨(hP i).finite_projective_forget.2, (hP i).finite_projective_forget.1⟩

/-- The complex of `p`-th graded pieces of a bounded complex of filtered finite projective
modules is a bounded complex of finite projective modules. -/
private lemma finiteProjectiveComplex_grP (R : Type u) [Ring R]
    (P : CochainComplex (FiniteFilteredObject (ModuleCat.{max u v} R)) ℤ)
    (hbounded : CochainComplex.plus _ P ∧ CochainComplex.minus _ P)
    (hP : ∀ i : ℤ, IsFilteredFiniteProjective (P.X i)) (p : ℤ) :
    finiteProjectiveComplex R
      (((FiniteFilteredObject.grP (𝒜 := ModuleCat.{max u v} R) p).mapHomologicalComplex
        (ComplexShape.up ℤ)).obj P) :=
  finiteProjectiveComplex_of_bounded R _ P hbounded fun i =>
    ⟨(IsProjective.iff_projective (R := R)
      (P := (FiniteFilteredObject.grP (𝒜 := ModuleCat.{max u v} R) p).obj (P.X i))).2
        (hP i p).2, (hP i p).1⟩

/-- If the image of the representative of a filtered perfect complex under an additive functor
inverting the filtered quasi-isomorphisms is finite projective, the image of the complex is
perfect. -/
private lemma isPerfect_liftDF_obj (R : Type u) [Ring R]
    (G : FiniteFilteredObject (ModuleCat.{max u v} R) ⥤ ModuleCat.{max u v} R) [G.Additive]
    (hG : (HomotopyCategory.filteredQuasiIso
      (ModuleCat.{max u v} R)).IsInvertedBy
        (G.mapHomotopyCategory (ComplexShape.up ℤ) ⋙ DerivedCategory.Qh))
    (K : FilteredPerfectData.{u, v} R)
    (hGP : finiteProjectiveComplex R
      ((G.mapHomologicalComplex (ComplexShape.up ℤ)).obj K.representative)) :
    StacksDraft.Perfect.IsPerfect
      ((CochainComplex.FilteredDerivedCategory.liftDF G hG).obj K.obj) := by
  let P := (G.mapHomologicalComplex (ComplexShape.up ℤ)).obj K.representative
  let qP := (HomotopyCategory.quotient (FiniteFilteredObject
    (ModuleCat.{max u v} R)) (ComplexShape.up ℤ)).obj K.representative
  obtain ⟨e⟩ := K.iso
  let η := CategoryTheory.Localization.fac
    (G.mapHomotopyCategory (ComplexShape.up ℤ) ⋙ DerivedCategory.Qh) hG
    (CochainComplex.FilteredDerivedCategory.Qh
      (𝒜 := ModuleCat.{max u v} R))
  have he : Nonempty (DerivedCategory.Q.obj P ≅
      (CochainComplex.FilteredDerivedCategory.liftDF G hG).obj K.obj) :=
    ⟨((DerivedCategory.quotientCompQhIso (ModuleCat.{max u v} R)).app P).symm ≪≫
      (η.app qP).symm ≪≫
      (CochainComplex.FilteredDerivedCategory.liftDF G hG).mapIso e⟩
  exact (isPerfect_iff R _).2 ⟨P, hGP, he⟩

/-- Forgetting the filtration of a filtered perfect complex gives a perfect
derived complex. -/
public theorem FilteredPerfectData.forgetPerfect (R : Type u) [Ring R]
    (K : FilteredPerfectData.{u, v} R) : StacksDraft.Perfect.IsPerfect
      ((CochainComplex.FilteredDerivedCategory.forgetDF).obj K.obj) :=
  isPerfect_liftDF_obj R _ _ K
    (finiteProjectiveComplex_forget R K.representative K.bounded K.finiteProjective)

/-- Every graded piece of a filtered perfect complex is perfect. -/
@[sga "4½ Rapport 4.4" "partial"]
public theorem FilteredPerfectData.gradedPerfect (R : Type u) [Ring R]
    (K : FilteredPerfectData.{u, v} R) (p : ℤ) : StacksDraft.Perfect.IsPerfect
      ((CochainComplex.FilteredDerivedCategory.grDF p).obj K.obj) :=
  isPerfect_liftDF_obj R _ _ K
    (finiteProjectiveComplex_grP R K.representative K.bounded K.finiteProjective p)

/-- Every endomorphism of the image in the filtered derived category of a bounded-above complex
of filtered projective objects is represented by a cochain map. -/
private theorem exists_filtered_representative_map (R : Type u) [Ring R]
    (P : CochainComplex (FiniteFilteredObject (ModuleCat.{max u v} R)) ℤ)
    (hbounded : CochainComplex.plus _ P ∧ CochainComplex.minus _ P)
    (hproj : ∀ i : ℤ, IsFilteredProjective (P.X i))
    (φ : (CochainComplex.FilteredDerivedCategory.Qh).obj
      ((HomotopyCategory.quotient _ _).obj P) ⟶
        (CochainComplex.FilteredDerivedCategory.Qh).obj
          ((HomotopyCategory.quotient _ _).obj P)) :
    ∃ g : P ⟶ P,
      (CochainComplex.FilteredDerivedCategory.Qh).map
        ((HomotopyCategory.quotient _ _).map g) = φ := by
  let A := ModuleCat.{max u v} R
  obtain ⟨n, hn⟩ := hbounded.2
  let qP := (HomotopyCategory.quotient (FiniteFilteredObject A)
    (ComplexShape.up ℤ)).obj P
  let X : (CochainComplex.FilteredDerivedCategory.Kminus (𝒜 := A)).FullSubcategory :=
    ⟨qP, CochainComplex.FilteredDerivedCategory.kminus_quotient_obj n⟩
  have hX : filteredProjectiveMinus A X := by
    show (filteredProjectiveMinusC A).strictMap
      (HomotopyCategory.quotient _ _) qP
    exact ObjectProperty.strictMap.mk _ ⟨⟨n, hn⟩, hproj⟩
  let Y : (filteredProjectiveMinus A).FullSubcategory := ⟨X, hX⟩
  let F := filteredProjectiveMinusToDerivedMinus A
  let : F.IsEquivalence := filteredProjectiveMinusToDerivedMinus_isEquivalence A
  let ψ : F.obj Y ⟶ F.obj Y := ObjectProperty.homMk (by
    show (CochainComplex.FilteredDerivedCategory.Qh).obj qP ⟶
      (CochainComplex.FilteredDerivedCategory.Qh).obj qP
    exact φ)
  have hψ : (CochainComplex.FilteredDerivedCategory.minus A).ι.map ψ = φ := rfl
  obtain ⟨h, hh⟩ := F.map_surjective ψ
  let h₁ : X ⟶ X := (filteredProjectiveMinus A).ι.map h
  let h₂ : qP ⟶ qP :=
    (CochainComplex.FilteredDerivedCategory.Kminus (𝒜 := A)).ι.map h₁
  have hh' : (CochainComplex.FilteredDerivedCategory.Qh).map h₂ = φ := by
    have hh0 := congrArg
      ((CochainComplex.FilteredDerivedCategory.minus A).ι.map) hh
    rw [hψ] at hh0
    simpa [F, filteredProjectiveMinusToDerivedMinus,
      CochainComplex.FilteredDerivedCategory.Qminus, h₂, h₁] using hh0
  obtain ⟨g, hg⟩ := (HomotopyCategory.quotient (FiniteFilteredObject A)
    (ComplexShape.up ℤ)).map_surjective h₂
  refine ⟨g, ?_⟩
  rw [hg]
  exact hh'

/-- The trace on the `p`-th graded piece of the `i`-th term of a bounded complex of filtered
finite projective modules. -/
private noncomputable def filteredGrModuleTrace (R : Type u) [Ring R]
    (P : CochainComplex (FiniteFilteredObject (ModuleCat.{max u v} R)) ℤ)
    (hP : ∀ i : ℤ, IsFilteredFiniteProjective (P.X i))
    (g : P ⟶ P) (i p : ℤ) : AdditiveCommutatorQuotient R := by
  let M := (FiniteFilteredObject.grP (𝒜 := ModuleCat.{max u v} R) p).obj (P.X i)
  have : Projective M := (hP i p).2
  have : Module.Finite R M := (hP i p).1
  have : Module.Projective R M :=
    (IsProjective.iff_projective (R := R) (P := M)).2 inferInstance
  exact Stacks.Trace.projectiveModuleTrace R M
    (((FiniteFilteredObject.grP (𝒜 := ModuleCat.{max u v} R) p).map (g.f i)).hom)

/-- The trace on the underlying module of the `i`-th term of a bounded complex of filtered finite
projective modules. -/
private noncomputable def filteredForgetModuleTrace (R : Type u) [Ring R]
    (P : CochainComplex (FiniteFilteredObject (ModuleCat.{max u v} R)) ℤ)
    (hP : ∀ i : ℤ, IsFilteredFiniteProjective (P.X i))
    (g : P ⟶ P) (i : ℤ) : AdditiveCommutatorQuotient R := by
  let M := (FiniteFilteredObject.forget (𝒜 := ModuleCat.{max u v} R)).obj (P.X i)
  have : Module.Finite R M := (hP i).finite_projective_forget.1
  have : Module.Projective R M := (hP i).finite_projective_forget.2
  exact Stacks.Trace.projectiveModuleTrace R M
    (((FiniteFilteredObject.forget (𝒜 := ModuleCat.{max u v} R)).map (g.f i)).hom)

/-- The degree `i` term, with its sign, of the alternating trace on the `p`-th graded piece. -/
private noncomputable def filteredGrAlternatingTerm (R : Type u) [Ring R]
    (P : CochainComplex (FiniteFilteredObject (ModuleCat.{max u v} R)) ℤ)
    (hP : ∀ i : ℤ, IsFilteredFiniteProjective (P.X i))
    (g : P ⟶ P) (i p : ℤ) : AdditiveCommutatorQuotient R :=
  if Even i then filteredGrModuleTrace R P hP g i p
  else -filteredGrModuleTrace R P hP g i p

/-- The degree `i` term, with its sign, of the alternating trace on the underlying complex. -/
private noncomputable def filteredForgetAlternatingTerm (R : Type u) [Ring R]
    (P : CochainComplex (FiniteFilteredObject (ModuleCat.{max u v} R)) ℤ)
    (hP : ∀ i : ℤ, IsFilteredFiniteProjective (P.X i))
    (g : P ⟶ P) (i : ℤ) : AdditiveCommutatorQuotient R :=
  if Even i then filteredForgetModuleTrace R P hP g i
  else -filteredForgetModuleTrace R P hP g i

/-- The alternating trace on the underlying complex of a bounded complex of filtered finite
projective modules is the sum over the filtration index of the alternating traces on the graded
pieces. -/
@[sga "4½ Rapport 4.2" "more general",
  sga "4½ Rapport 4.4" "special case",
  sga "5 IIIB 5.6" "special case"]
private theorem alternatingTrace_forget_eq_sum_grP (R : Type u) [Ring R]
    (P : CochainComplex (FiniteFilteredObject (ModuleCat.{max u v} R)) ℤ)
    (hbounded : CochainComplex.plus _ P ∧ CochainComplex.minus _ P)
    (hP : ∀ i : ℤ, IsFilteredFiniteProjective (P.X i))
    (g : P ⟶ P) :
    alternatingTrace R
        (((FiniteFilteredObject.forget (𝒜 := ModuleCat.{max u v} R)).mapHomologicalComplex
          (ComplexShape.up ℤ)).obj P)
        (finiteProjectiveComplex_forget R P hbounded hP)
        (((FiniteFilteredObject.forget (𝒜 := ModuleCat.{max u v} R)).mapHomologicalComplex
          (ComplexShape.up ℤ)).map g) =
      ∑ᶠ p : ℤ, alternatingTrace R
        (((FiniteFilteredObject.grP (𝒜 := ModuleCat.{max u v} R) p).mapHomologicalComplex
          (ComplexShape.up ℤ)).obj P)
        (finiteProjectiveComplex_grP R P hbounded hP p)
        (((FiniteFilteredObject.grP (𝒜 := ModuleCat.{max u v} R) p).mapHomologicalComplex
          (ComplexShape.up ℤ)).map g) := by
  let a : ℤ → ℤ := fun i => Classical.choose (P.X i).property.exists_isIso_ι
  let b : ℤ → ℤ := fun i => Classical.choose (P.X i).property.exists_isZero_obj
  have ha (i : ℤ) : IsIso ((P.X i).obj.filtration.ι.app (op (a i))) :=
    Classical.choose_spec (P.X i).property.exists_isIso_ι
  have hb (i : ℤ) : IsZero ((P.X i).obj.filtration.obj (op (b i))) :=
    Classical.choose_spec (P.X i).property.exists_isZero_obj
  obtain ⟨lo, hlo⟩ := hbounded.1
  obtain ⟨hi, hhi⟩ := hbounded.2
  let t : ℤ × ℤ → AdditiveCommutatorQuotient R := fun ip =>
    filteredGrAlternatingTerm R P hP g ip.1 ip.2
  let S : Set (ℤ × ℤ) := ⋃ i ∈ Set.Icc lo hi,
    (fun p => (i, p)) '' Set.Ico (a i) (b i)
  have hS : S.Finite := by
    apply Set.Finite.biUnion (Set.finite_Icc lo hi)
    intro i hiI
    exact (Set.finite_Ico (a i) (b i)).image (fun p => (i, p))
  have hsupport : Function.support t ⊆ S := by
    intro ip hip
    change t ip ≠ 0 at hip
    by_contra hout
    have hnot : ¬ (lo ≤ ip.1 ∧ ip.1 ≤ hi ∧ a ip.1 ≤ ip.2 ∧ ip.2 < b ip.1) := by
      intro hmem
      apply hout
      simp only [S, Set.mem_iUnion]
      refine ⟨ip.1, ?_, ?_⟩
      · exact ⟨hmem.1, hmem.2.1⟩
      · refine ⟨ip.2, ?_, ?_⟩
        · exact ⟨hmem.2.2.1, hmem.2.2.2⟩
        · rfl
    have hout' : ip.1 < lo ∨ hi < ip.1 ∨ ip.2 < a ip.1 ∨ b ip.1 ≤ ip.2 := by
      omega
    have t_zero (i p : ℤ)
        (hzero : IsZero ((FiniteFilteredObject.grP
          (𝒜 := ModuleCat.{max u v} R) p).obj (P.X i))) : t (i, p) = 0 := by
      let M := (FiniteFilteredObject.grP
        (𝒜 := ModuleCat.{max u v} R) p).obj (P.X i)
      let : Projective M := (hP i p).2
      let : Module.Finite R M := (hP i p).1
      let : Module.Projective R M :=
        (IsProjective.iff_projective (R := R) (P := ↑M)).2 inferInstance
      let : Subsingleton M := ModuleCat.subsingleton_of_isZero hzero
      have htr : filteredGrModuleTrace R P hP g i p = 0 := by
        unfold filteredGrModuleTrace
        exact projectiveModuleTrace_eq_zero_of_subsingleton R _ _
      simp [t, filteredGrAlternatingTerm, htr]
    have hzg : IsZero ((FiniteFilteredObject.grP
        (𝒜 := ModuleCat.{max u v} R) ip.2).obj (P.X ip.1)) := by
      rcases hout' with hlow | hhigh | hfilLow | hfilHigh
      · let : P.IsStrictlyGE lo := hlo
        exact (FiniteFilteredObject.grP (𝒜 := ModuleCat.{max u v} R) ip.2).map_isZero
          (P.isZero_of_isStrictlyGE lo ip.1 hlow)
      · let : P.IsStrictlyLE hi := hhi
        exact (FiniteFilteredObject.grP (𝒜 := ModuleCat.{max u v} R) ip.2).map_isZero
          (P.isZero_of_isStrictlyLE hi ip.1 hhigh)
      · exact FilteredObject.isZero_gr_obj_of_isIso_ι_app (P.X ip.1).obj (by omega) (ha ip.1)
      · exact FilteredObject.isZero_gr_obj_of_isZero (P.X ip.1).obj hfilHigh (hb ip.1)
    exact hip (t_zero ip.1 ip.2 hzg)
  have htfinite : Function.HasFiniteSupport t := hS.subset hsupport
  have hdegree (i : ℤ) : filteredForgetAlternatingTerm R P hP g i =
      ∑ᶠ p : ℤ, t (i, p) := by
    by_cases hi : Even i
    · simpa only [t, filteredForgetAlternatingTerm, filteredForgetModuleTrace,
        filteredGrAlternatingTerm, filteredGrModuleTrace, ite_eq_left hi] using
        projectiveModuleTrace_eq_sum_grP R (P.X i) (hP i) (g.f i)
    · have hneg := finsum_neg_distrib
        (fun p : ℤ => filteredGrModuleTrace R P hP g i p)
      have hTL := congrArg Neg.neg
        (projectiveModuleTrace_eq_sum_grP R (P.X i) (hP i) (g.f i))
      have hodd : -filteredForgetModuleTrace R P hP g i =
          ∑ᶠ p : ℤ, -filteredGrModuleTrace R P hP g i p := by
        rw [hneg]
        simpa only [filteredForgetModuleTrace, filteredGrModuleTrace] using hTL
      simpa only [t, filteredForgetAlternatingTerm, filteredGrAlternatingTerm,
        ite_eq_right hi] using hodd
  calc
    _ = ∑ᶠ i : ℤ, filteredForgetAlternatingTerm R P hP g i := by
          simp [alternatingTrace, filteredForgetAlternatingTerm,
            filteredForgetModuleTrace]
    _ = ∑ᶠ i : ℤ, ∑ᶠ p : ℤ, t (i, p) := finsum_congr hdegree
    _ = ∑ᶠ p : ℤ, ∑ᶠ i : ℤ, t (i, p) := by
      calc
        ∑ᶠ i : ℤ, ∑ᶠ p : ℤ, t (i, p) = ∑ᶠ x : ℤ × ℤ, t x :=
          (finsum_curry t htfinite).symm
        _ = ∑ᶠ x : ℤ × ℤ, t (x.2, x.1) :=
          (finsum_comp_equiv (Equiv.prodComm ℤ ℤ) (f := t)).symm
        _ = ∑ᶠ p : ℤ, ∑ᶠ i : ℤ, t (i, p) :=
          finsum_curry (fun x : ℤ × ℤ => t (x.2, x.1)) (by
            show Function.HasFiniteSupport (fun x : ℤ × ℤ =>
              t (Equiv.prodComm ℤ ℤ x))
            show ((Equiv.prodComm ℤ ℤ) ⁻¹' Function.support t).Finite
            exact Set.Finite.preimage
              (s := Function.support t)
              ((Equiv.prodComm ℤ ℤ).injective.injOn) htfinite)
    _ = _ := by
      apply finsum_congr
      intro p
      simp [alternatingTrace, t, filteredGrAlternatingTerm,
        filteredGrModuleTrace]

/-- An additive functor out of filtered objects which inverts the filtered quasi-isomorphisms
carries a representing cochain map of an endomorphism of a filtered derived object to a
representing cochain map of the induced endomorphism of its image. -/
private theorem filtered_derived_map_eq_chain_map (R : Type u) [Ring R]
    (G : FiniteFilteredObject (ModuleCat.{max u v} R) ⥤ ModuleCat.{max u v} R)
    [G.Additive]
    (hG : (HomotopyCategory.filteredQuasiIso
      (ModuleCat.{max u v} R)).IsInvertedBy
        (G.mapHomotopyCategory (ComplexShape.up ℤ) ⋙ DerivedCategory.Qh))
    (P : CochainComplex (FiniteFilteredObject (ModuleCat.{max u v} R)) ℤ)
    (g : P ⟶ P) (X : CochainComplex.FilteredDerivedCategory
      (ModuleCat.{max u v} R))
    (e : (CochainComplex.FilteredDerivedCategory.Qh).obj
      ((HomotopyCategory.quotient _ _).obj P) ≅ X)
    (f : X ⟶ X)
    (hgf : (CochainComplex.FilteredDerivedCategory.Qh).map
        ((HomotopyCategory.quotient _ _).map g) = e.hom ≫ f ≫ e.inv) :
    ∃ e' : DerivedCategory.Q.obj ((G.mapHomologicalComplex
      (ComplexShape.up ℤ)).obj P) ≅ (CochainComplex.FilteredDerivedCategory.liftDF
        G hG).obj X,
      DerivedCategory.Q.map ((G.mapHomologicalComplex
        (ComplexShape.up ℤ)).map g) = e'.hom ≫
          (CochainComplex.FilteredDerivedCategory.liftDF G hG).map f ≫ e'.inv := by
  let H := HomotopyCategory.quotient (FiniteFilteredObject
    (ModuleCat.{max u v} R)) (ComplexShape.up ℤ)
  let qP := H.obj P
  let qg := H.map g
  let U := (G.mapHomologicalComplex (ComplexShape.up ℤ)).obj P
  let qcomp := DerivedCategory.quotientCompQhIso (ModuleCat.{max u v} R)
  let β := G.mapHomotopyCategoryFactors (ComplexShape.up ℤ)
  let γ := Functor.isoWhiskerRight β.symm DerivedCategory.Qh
  let η := CategoryTheory.Localization.fac
    (G.mapHomotopyCategory (ComplexShape.up ℤ) ⋙ DerivedCategory.Qh)
    hG (CochainComplex.FilteredDerivedCategory.Qh
      (𝒜 := ModuleCat.{max u v} R))
  let L := CochainComplex.FilteredDerivedCategory.liftDF G hG
  let gc := (G.mapHomologicalComplex (ComplexShape.up ℤ)).map g
  let α := (qcomp.app U).symm ≪≫ (γ.app P) ≪≫ (η.app qP).symm ≪≫ L.mapIso e
  have hq : DerivedCategory.Q.map gc ≫ (qcomp.app U).symm.hom =
      (qcomp.app U).symm.hom ≫ DerivedCategory.Qh.map
        ((HomotopyCategory.quotient (ModuleCat.{max u v} R)
          (ComplexShape.up ℤ)).map gc) := by
    simp [U]
  have hγ : DerivedCategory.Qh.map
        ((HomotopyCategory.quotient (ModuleCat.{max u v} R)
          (ComplexShape.up ℤ)).map gc) ≫ (γ.app P).hom =
      (γ.app P).hom ≫ DerivedCategory.Qh.map
        ((G.mapHomotopyCategory (ComplexShape.up ℤ)).map qg) := by
    simpa [Functor.map_comp, gc, qg, H] using γ.hom.naturality g
  have hη : DerivedCategory.Qh.map
        ((G.mapHomotopyCategory (ComplexShape.up ℤ)).map qg) ≫
          (η.app qP).symm.hom =
      (η.app qP).symm.hom ≫ L.map
        ((CochainComplex.FilteredDerivedCategory.Qh).map qg) := by
    simpa [qP, Functor.map_comp] using η.symm.hom.naturality qg
  have hmap : DerivedCategory.Qh.map ((G.mapHomotopyCategory
      (ComplexShape.up ℤ)).map qg) ≫ (η.app qP).symm.hom ≫
        L.map e.hom = (η.app qP).symm.hom ≫ L.map e.hom ≫ L.map f := by
    calc
      _ = (DerivedCategory.Qh.map ((G.mapHomotopyCategory
          (ComplexShape.up ℤ)).map qg) ≫ (η.app qP).symm.hom) ≫
            L.map e.hom := by
            simp only [Category.assoc]
      _ = ((η.app qP).symm.hom ≫ L.map
          ((CochainComplex.FilteredDerivedCategory.Qh).map qg)) ≫ L.map e.hom := by
            rw [hη]
      _ = (η.app qP).symm.hom ≫ L.map e.hom ≫ L.map f := by
            have hgf' : (CochainComplex.FilteredDerivedCategory.Qh).map qg =
                e.hom ≫ f ≫ e.inv := by simpa [qg, H] using hgf
            rw [hgf']
            simp only [Category.assoc]
            rw [← Functor.map_comp]
            simp only [Functor.map_comp, Category.assoc, Iso.inv_hom_id,
              Category.comp_id]
  have hconj : DerivedCategory.Q.map gc ≫ α.hom = α.hom ≫ L.map f := by
    dsimp only [α, Iso.trans_hom, Functor.mapIso_hom]
    calc
      _ = (qcomp.app U).symm.hom ≫ DerivedCategory.Qh.map
          ((HomotopyCategory.quotient (ModuleCat.{max u v} R)
            (ComplexShape.up ℤ)).map gc) ≫ (γ.app P).hom ≫
              (η.app qP).symm.hom ≫ L.map e.hom := by
                simpa only [Category.assoc] using congrArg
                  (fun k => k ≫ (γ.app P).hom ≫ (η.app qP).symm.hom ≫ L.map e.hom) hq
      _ = (qcomp.app U).symm.hom ≫ (γ.app P).hom ≫
          DerivedCategory.Qh.map ((G.mapHomotopyCategory
            (ComplexShape.up ℤ)).map qg) ≫
              (η.app qP).symm.hom ≫ L.map e.hom := by
                simpa only [Category.assoc] using congrArg
                  (fun k => (qcomp.app U).symm.hom ≫ k ≫
                    (η.app qP).symm.hom ≫ L.map e.hom) hγ
      _ = (qcomp.app U).symm.hom ≫ (γ.app P).hom ≫
          (η.app qP).symm.hom ≫ L.map e.hom ≫ L.map f := by
                simpa only [Category.assoc] using congrArg
                  (fun k => (qcomp.app U).symm.hom ≫ (γ.app P).hom ≫ k) hmap
      _ = _ := by simp only [Category.assoc]
  refine ⟨α, ?_⟩
  calc
    DerivedCategory.Q.map gc = DerivedCategory.Q.map gc ≫ α.hom ≫ α.inv := by
      simp only [Iso.hom_inv_id, Category.comp_id]
    _ = α.hom ≫ L.map f ≫ α.inv := by
      simpa only [Category.assoc] using congrArg (fun k => k ≫ α.inv) hconj

/-- The trace of an endomorphism of the image of a filtered derived object under an additive
functor which inverts the filtered quasi-isomorphisms is the alternating trace of a representing
cochain map on the image complex. -/
private theorem perfectDerivedTrace_liftDF_eq_alternatingTrace (R : Type u) [Ring R]
    (G : FiniteFilteredObject (ModuleCat.{max u v} R) ⥤ ModuleCat.{max u v} R)
    [G.Additive]
    (hG : (HomotopyCategory.filteredQuasiIso
      (ModuleCat.{max u v} R)).IsInvertedBy
        (G.mapHomotopyCategory (ComplexShape.up ℤ) ⋙ DerivedCategory.Qh))
    (P : CochainComplex (FiniteFilteredObject (ModuleCat.{max u v} R)) ℤ)
    (hGP : finiteProjectiveComplex R
      ((G.mapHomologicalComplex (ComplexShape.up ℤ)).obj P))
    (X : CochainComplex.FilteredDerivedCategory (ModuleCat.{max u v} R))
    (hX : StacksDraft.Perfect.IsPerfect
      ((CochainComplex.FilteredDerivedCategory.liftDF G hG).obj X))
    (e : (CochainComplex.FilteredDerivedCategory.Qh).obj
      ((HomotopyCategory.quotient _ _).obj P) ≅ X)
    (f : X ⟶ X) (g : P ⟶ P)
    (hg : (CochainComplex.FilteredDerivedCategory.Qh).map
      ((HomotopyCategory.quotient _ _).map g) = e.hom ≫ f ≫ e.inv) :
    perfectDerivedTrace R
        ⟨(CochainComplex.FilteredDerivedCategory.liftDF G hG).obj X, hX⟩
        ((CochainComplex.FilteredDerivedCategory.liftDF G hG).map f) =
      alternatingTrace R ((G.mapHomologicalComplex (ComplexShape.up ℤ)).obj P) hGP
        ((G.mapHomologicalComplex (ComplexShape.up ℤ)).map g) := by
  obtain ⟨e', hg'⟩ := filtered_derived_map_eq_chain_map R G hG P g X e f hg
  exact perfectDerivedTrace_eq_alternatingTrace R _ _ _ hGP e' _ hg'

/-- **Stacks 03TK.** Trace is additive along the filtration of a perfect
filtered derived complex. -/
@[stacks 03TK, sga "4½ Rapport 4.4" "(4.4.1)", sga "5 IIIB 5.6" "(5.6.5), F = A"]
public theorem perfectDerivedTrace_eq_sum_grDF (R : Type u) [Ring R]
    (K : FilteredPerfectData.{u, v} R) (f : K.obj ⟶ K.obj) :
    perfectDerivedTrace R
      ⟨(CochainComplex.FilteredDerivedCategory.forgetDF).obj K.obj,
        K.forgetPerfect R⟩
      ((CochainComplex.FilteredDerivedCategory.forgetDF).map f) =
      ∑ᶠ p : ℤ, perfectDerivedTrace R
        ⟨(CochainComplex.FilteredDerivedCategory.grDF p).obj K.obj,
          K.gradedPerfect R p⟩
        ((CochainComplex.FilteredDerivedCategory.grDF p).map f) := by
  obtain ⟨e⟩ := K.iso
  obtain ⟨g, hg⟩ := exists_filtered_representative_map R K.representative K.bounded
    (fun i => (K.finiteProjective i).isFilteredProjective)
    (e.hom ≫ f ≫ e.inv)
  rw [perfectDerivedTrace_liftDF_eq_alternatingTrace R
      (FiniteFilteredObject.forget (𝒜 := ModuleCat.{max u v} R))
      (CochainComplex.FilteredDerivedCategory.forget_inverts
        (𝒜 := ModuleCat.{max u v} R)) K.representative
      (finiteProjectiveComplex_forget R K.representative K.bounded K.finiteProjective)
      K.obj (K.forgetPerfect R) e f g hg,
    alternatingTrace_forget_eq_sum_grP R K.representative K.bounded K.finiteProjective g]
  refine finsum_congr fun p => ?_
  rw [perfectDerivedTrace_liftDF_eq_alternatingTrace R
      (FiniteFilteredObject.grP (𝒜 := ModuleCat.{max u v} R) p)
      (CochainComplex.FilteredDerivedCategory.grP_inverts
        (𝒜 := ModuleCat.{max u v} R) p) K.representative
      (finiteProjectiveComplex_grP R K.representative K.bounded K.finiteProjective p)
      K.obj (K.gradedPerfect R p) e f g hg]

end CategoryTheory.FilteredDerived
