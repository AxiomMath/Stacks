module

public import Mathlib.Algebra.Homology.DerivedCategory.ExactFunctor
public import Mathlib.Algebra.Homology.DerivedCategory.Fractions
public import Mathlib.Algebra.Homology.DerivedCategory.TStructure
public import Mathlib.Algebra.Homology.FullSubcategory
public import StacksFrontier.Algebra.Category.ModuleCat.Sheaf.GeneratedByGlobalSections
public import StacksFrontier.AlgebraicGeometry.DerivedQCoh.AffineDiagonalEquivalence
public import StacksFrontier.AlgebraicGeometry.DerivedQCoh.ComparisonAffine
public import StacksFrontier.AlgebraicGeometry.Perfect.BoundedLocallyFreeComplexes.FiniteLocallyFreeReplacement
public import StacksFrontier.AlgebraicGeometry.Perfect.PseudoCoherentComplex.LocallyFiniteCohomology
public import StacksFrontier.AlgebraicGeometry.PseudoCoherent.QuasicoherentCohomology

/-!
# Quasi-coherent presentations of perfect objects

Let `X` be a scheme with affine diagonal.  The comparison functor of [Stacks, Tag 06VT] is then
an equivalence `D(QCoh(𝒪_X)) ≃ D_QCoh(𝒪_X)` by [Stacks, Tag 08DB], so the functor
`D(ι) : D(QCoh(𝒪_X)) ⥤ D(𝒪_X)` induced by the exact inclusion of the quasi-coherent modules is
fully faithful and every object with quasi-coherent cohomology is in its image.  This file
records that fully faithfulness and derives from it the presentation of a perfect object by a
bounded below complex of quasi-coherent modules.

## Main results

* `Stacks.Perfect.BoundedLocallyFreeComplexes.full_mapDerivedCategory_isQuasicoherent_ι`: the
  derived inclusion of quasi-coherent modules is full.
* `Stacks.Perfect.BoundedLocallyFreeComplexes.faithful_mapDerivedCategory_isQuasicoherent_ι`: the
  derived inclusion of quasi-coherent modules is faithful.
* `Stacks.Perfect.BoundedLocallyFreeComplexes.isPerfect_of_boundedFiniteLocallyFree`: a bounded
  complex of finite locally free modules represents a perfect object.
* `Stacks.Perfect.BoundedLocallyFreeComplexes.exists_plus_quasicoherent_representative`: a
  perfect object of `D(𝒪_X)` on a quasi-compact scheme with affine diagonal is represented by a
  bounded below complex of quasi-coherent modules.

## Implementation notes

The derived categories are those of `CategoryTheory.HasDerivedCategory.standard`, the model of
[Stacks, Tag 0F8E].  [Stacks, Tag 08DB] is available at the locally small model only, and is
moved to the standard one by
`Stacks.DerivedQCoh.isEquivalence_derivedQuasicoherentComparison_of_model`, which says that
whether the comparison functor is an equivalence does not depend on the two models chosen.

Affineness of the diagonal is `IsAffineHom (pullback.diagonal (terminal.from X))`.  It is a
consequence of quasi-compactness, quasi-separatedness and the resolution property by
[Stacks, Tag 0F8C].

## References

* [Stacks Project, Tag 06VT](https://stacks.math.columbia.edu/tag/06VT)
* [Stacks Project, Tag 08DB](https://stacks.math.columbia.edu/tag/08DB)
* [Stacks Project, Tag 08E5](https://stacks.math.columbia.edu/tag/08E5)
* [Stacks Project, Tag 0F8E](https://stacks.math.columbia.edu/tag/0F8E)
* [Stacks Project, Tag 0FEP](https://stacks.math.columbia.edu/tag/0FEP)
-/

@[expose] public noncomputable section

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits TopologicalSpace
open Stacks.AlgebraicGeometry.QuasicoherentDerived Stacks.Cohomology.PerfectComplexes

universe u

namespace Stacks.Perfect.BoundedLocallyFreeComplexes

attribute [local instance 10000] HasDerivedCategory.standard

/-! ### Finite locally free modules are quasi-coherent -/

/-- A finite locally free `𝒪_X`-module on a scheme is quasi-coherent. -/
theorem isQuasicoherent_of_isFiniteLocallyFree (X : Scheme.{u}) (M : X.Modules)
    (hM : Stacks.FiniteLocallyFree.IsFiniteLocallyFree (R := X.ringCatSheaf) M) :
    M.IsQuasicoherent := by
  have : Stacks.FiniteLocallyFree.IsFiniteLocallyFree (R := X.ringCatSheaf) M := hM
  obtain ⟨σ, -⟩ := (Stacks.FiniteLocallyFree.isFinitePresentation M).1
  exact σ.isQuasicoherent

/-- Every term of a bounded complex of finite locally free modules is quasi-coherent. -/
theorem isQuasicoherent_X_of_boundedFiniteLocallyFree (X : Scheme.{u})
    (E : CochainComplex X.Modules ℤ) (hE : boundedFiniteLocallyFreeComplex X E) (i : ℤ) :
    (E.X i).IsQuasicoherent :=
  isQuasicoherent_of_isFiniteLocallyFree X (E.X i) (hE.2 i)

/-! ### Bounded complexes of finite locally free modules are perfect -/

/-- **A bounded complex of finite locally free `𝒪_X`-modules represents a perfect object of
`D(𝒪_X)`.** -/
theorem isPerfect_of_boundedFiniteLocallyFree (X : Scheme.{u})
    (E : CochainComplex X.Modules ℤ) (hE : boundedFiniteLocallyFreeComplex X E) :
    IsPerfect (X := X.toRingedSpace) (DerivedCategory.Q.obj E) :=
  Stacks.Cohomology.PerfectComplexTriangles.isPerfect_of_iso.{u, u + 1}
    ((DerivedCategory.quotientCompQhIso X.Modules).app E)
    (perfect_of_boundedFiniteLocallyFree X
      ⟨(HomotopyCategory.quotient X.Modules (ComplexShape.up ℤ)).obj E,
        (ObjectProperty.strictMap_iff _ _ _).2 ⟨E, hE, rfl⟩⟩)

/-- An object of `D(𝒪_X)` isomorphic to a perfect object is perfect. -/
theorem isPerfect_of_iso {X : Scheme.{u}} {K L : DerivedCategory X.Modules} (e : K ≅ L)
    (hK : IsPerfect (X := X.toRingedSpace) K) : IsPerfect (X := X.toRingedSpace) L :=
  Stacks.Cohomology.PerfectComplexTriangles.isPerfect_of_iso.{u, u + 1} e hK

/-! ### Perfect objects on a quasi-compact scheme are bounded below -/

/-- **A perfect object of `D(𝒪_X)` on a quasi-compact scheme is bounded below.** -/
theorem exists_isZero_homology_of_isPerfect (X : Scheme.{u}) [CompactSpace X]
    (K : DerivedCategory X.Modules) (hK : IsPerfect (X := X.toRingedSpace) K) :
    ∃ a : ℤ, ∀ i < a, IsZero ((DerivedCategory.homologyFunctor X.Modules i).obj K) := by
  classical
  have hlocal (x : X) : ∃ U : X.Opens, x ∈ U ∧ {n : ℤ | ∃ y : X, y ∈ U ∧
      y ∈ SheafOfModules.supp ((DerivedCategory.homologyFunctor
        (StrictlyPerfect.OXMod.{u} X.toRingedSpace) n).obj K)}.Finite :=
    Stacks.AlgebraicGeometry.PerfectCohomology.locally_finite_homology X K hK x
  choose W hxW hW using hlocal
  obtain ⟨t, ht⟩ := (isCompact_univ : IsCompact (Set.univ : Set (X : Type u))).elim_finite_subcover
    (fun x : (X : Type u) => (W x : Set (X : Type u))) (fun x => (W x).isOpen)
    fun x _ => Set.mem_iUnion.mpr ⟨x, hxW x⟩
  have hS : {n : ℤ | ∃ x : X, x ∈ SheafOfModules.supp ((DerivedCategory.homologyFunctor
      (StrictlyPerfect.OXMod.{u} X.toRingedSpace) n).obj K)}.Finite := by
    refine (t.finite_toSet.biUnion fun x _ => hW x).subset ?_
    rintro n ⟨x, hx⟩
    obtain ⟨i, hit, hxi⟩ := Set.mem_iUnion₂.mp (ht (Set.mem_univ x))
    exact Set.mem_iUnion₂.mpr ⟨i, hit, x, hxi, hx⟩
  obtain ⟨a, ha⟩ := hS.bddBelow
  refine ⟨a, fun i hi => ?_⟩
  refine isZero_of_faithful (SheafOfModules.toSheaf X.ringCatSheaf) ?_
  refine (TopCat.Sheaf.isZero_iff_stalkFunctor_obj_isZero _).2 fun x => ?_
  exact AddCommGrpCat.isZero_iff_subsingleton.mpr <|
    not_nontrivial_iff_subsingleton.mp fun hx => (not_le_of_gt hi) (ha
      ⟨x, (SheafOfModules.mem_supp_iff_nontrivial_stalk ((DerivedCategory.homologyFunctor
        (StrictlyPerfect.OXMod.{u} X.toRingedSpace) i).obj K) x).2 hx⟩)

/-! ### Fully faithfulness of the derived inclusion of quasi-coherent modules -/

section AffineDiagonal

variable (X : Scheme.{u}) [CompactSpace X]
  [IsAffineHom (pullback.diagonal (terminal.from X))]

/-- **The comparison functor of [Stacks, Tag 06VT] is an equivalence at the standard derived
categories.** -/
theorem isEquivalence_derivedQuasicoherentComparison_standard :
    (derivedQuasicoherentComparison X).IsEquivalence :=
  Stacks.DerivedQCoh.isEquivalence_derivedQuasicoherentComparison_of_model X _ _ _ _
    (Stacks.DerivedQCoh.derivedQuasicoherentComparison_isEquivalence_of_affineDiagonal X)

/-- **The derived inclusion `D(QCoh(𝒪_X)) ⥤ D(𝒪_X)` is full** on a quasi-compact scheme with
affine diagonal. -/
theorem full_mapDerivedCategory_isQuasicoherent_ι :
    (SheafOfModules.isQuasicoherent X.ringCatSheaf).ι.mapDerivedCategory.Full :=
  have := isEquivalence_derivedQuasicoherentComparison_standard X
  Functor.Full.of_iso (derivedQuasicoherentComparisonCompι X)

/-- **The derived inclusion `D(QCoh(𝒪_X)) ⥤ D(𝒪_X)` is faithful** on a quasi-compact scheme with
affine diagonal. -/
theorem faithful_mapDerivedCategory_isQuasicoherent_ι :
    (SheafOfModules.isQuasicoherent X.ringCatSheaf).ι.mapDerivedCategory.Faithful :=
  have := isEquivalence_derivedQuasicoherentComparison_standard X
  Functor.Faithful.of_iso (derivedQuasicoherentComparisonCompι X)

/-! ### Bounded below quasi-coherent representatives of perfect objects -/

/-- **A perfect object of `D(𝒪_X)` on a quasi-compact scheme with affine diagonal is represented
by a bounded below complex of quasi-coherent `𝒪_X`-modules.** -/
theorem exists_plus_quasicoherent_representative (K : DerivedCategory X.Modules)
    (hK : IsPerfect (X := X.toRingedSpace) K) :
    ∃ G : CochainComplex X.Modules ℤ, CochainComplex.plus X.Modules G ∧
      (∀ i : ℤ, (G.X i).IsQuasicoherent) ∧
        Nonempty ((DerivedCategory.Q (C := X.Modules)).obj G ≅ K) := by
  let P := SheafOfModules.isQuasicoherent X.ringCatSheaf
  let I := P.ι
  have : I.Additive := I.additive_of_preserves_binary_products
  have hpc : AlgebraicGeometry.RingedSpace.IsPseudoCoherent (X := X.toRingedSpace) K :=
    (Stacks.Cohomology.TorAmplitude.isPseudoCoherent_iff_isPseudoCoherent'
      (X := X.toRingedSpace) K).mp
        (Stacks.Cohomology.TorAmplitude.isPseudoCoherent_of_isPerfect K hK)
  have := isEquivalence_derivedQuasicoherentComparison_standard X
  obtain ⟨A, ⟨eA⟩⟩ := Functor.EssSurj.mem_essImage (derivedQuasicoherentComparison X)
    (⟨K, AlgebraicGeometry.isQuasicoherentDerived_of_isPseudoCoherent X K hpc⟩ :
      (DerivedCategoryB.derivedCategoryB P).FullSubcategory)
  obtain ⟨a, ha⟩ := exists_isZero_homology_of_isPerfect X K hK
  let eUnder : I.mapDerivedCategory.obj A ≅ K :=
    ((derivedQuasicoherentComparisonCompι X).app A).symm ≪≫
      (DerivedCategoryB.derivedCategoryB P).ι.mapIso eA
  have : A.IsGE a := (DerivedCategory.isGE_iff A a).2 fun i hi => by
    refine IsZero.of_full_of_faithful_of_isZero I _ ?_
    refine IsZero.of_iso ?_ ((StacksDraft.PseudoCoherence.mapDerivedCategoryCompHomologyFunctorIso
      I i).app A).symm
    exact ((ha i hi).of_iso ((DerivedCategory.homologyFunctor X.Modules i).mapIso eUnder))
  obtain ⟨F, hFGE, ⟨eFA⟩⟩ := A.exists_iso_Q_obj_of_isGE a
  refine ⟨(I.mapHomologicalComplex (ComplexShape.up ℤ)).obj F, ?_,
    fun i => (F.X i).property, ⟨?_⟩⟩
  · exact (CochainComplex.plus_iff X.Modules _).2 ⟨a,
      (CochainComplex.isStrictlyGE_iff _ a).2 fun i hi =>
        I.map_isZero ((CochainComplex.isStrictlyGE_iff F a).1 hFGE i hi)⟩
  · exact ((Functor.mapDerivedCategoryFactors I).app F).symm ≪≫
      I.mapDerivedCategory.mapIso eFA.symm ≪≫ eUnder

end AffineDiagonal

end Stacks.Perfect.BoundedLocallyFreeComplexes

end
