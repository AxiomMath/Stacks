module

public import StacksFrontier.AlgebraicGeometry.Flatness.BlowUpSquare.ChartPrincipalityTransfer
public import StacksFrontier.AlgebraicGeometry.Flatness.BlowUpSquare.AffineChartRestrict
public import StacksFrontier.AlgebraicGeometry.Flatness.BlowUpSquare.ChartPullback
public import StacksFrontier.AlgebraicGeometry.DerivedTildePerfect
public import StacksFrontier.AlgebraicGeometry.Divisors.Norm.NonvanishingLocus
public import StacksFrontier.AlgebraicGeometry.Perfect.PerfectApproximation.Affine
public import StacksFrontier.Homology.Eta.Perfect.SectionsBasisPresentation
public import StacksFrontier.Homology.Perfect.BoundedComplexFittingMinorIdeal
import StacksCore.Tactic.EgaSgaAttribute

/-!
# Affine charts of a perfect complex

A perfect object `E` of `D(𝒪_X)` on a scheme `X` is, near every point, represented on an affine
open `U` by a bounded complex of finite free `Γ(X, U)`-modules. This file records that in the
vocabulary of `AlgebraicGeometry.ComplexAndDivisorSituation.AffineChart`, for the situation
`(X, ∅, E)` with the empty divisor, and proves that the ideals of minors `Fit_{i,k}` of the chart
complexes are compatible on overlaps.

## Main definitions

* `AlgebraicGeometry.ComplexAndDivisorSituation.ofPerfect`: the situation of a perfect object
  with the empty divisor.

## Main results

* `AlgebraicGeometry.ComplexAndDivisorSituation.exists_isPerfect_presentation`: on an affine open
  `V`, `E|_V` is the sheaf of a perfect object of `D(Γ(X, V))` (Stacks 06Z0 and 08EB).
* `AlgebraicGeometry.ComplexAndDivisorSituation.exists_affineChart_ofPerfect`: every point lies,
  inside any given neighbourhood, in the domain of an affine chart.
* `AlgebraicGeometry.ComplexAndDivisorSituation.AffineChart.map_fittingMinorIdeal_eq`: the ideal
  of minors `Fit_{i,k}` of a chart restricts to that of any chart with smaller domain.

## Implementation notes

A perfect complex over a ring is a bounded complex of finite projective modules, which becomes
free only locally: `AlgebraicGeometry.IsAffineOpen.exists_basicOpen_free_baseChange` makes the
finitely many nonzero terms free on a basic open neighbourhood of the point, and the base change
to that basic open is the chart complex. The divisor of the situation plays no role; it is the
unit ideal, with equation `1`.

## References

* [Stacks Project, Tag 0ESP](https://stacks.math.columbia.edu/tag/0ESP)
* [Stacks Project, Tag 06Z0](https://stacks.math.columbia.edu/tag/06Z0)
* [Stacks Project, Tag 08EB](https://stacks.math.columbia.edu/tag/08EB)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits StrictlyPerfect

universe u

attribute [local instance 10000] HasDerivedCategory.standard

namespace Module

variable {R S T : Type u} [CommRing R] [CommRing S] [CommRing T]

open TensorProduct in
/-- Freeness after base change persists under a further base change. -/
theorem free_baseChange_of_free_baseChange [Algebra R S] [Algebra S T] [Algebra R T]
    [IsScalarTower R S T] (M : Type u) [AddCommGroup M] [Module R M]
    [Module.Free S (S ⊗[R] M)] : Module.Free T (T ⊗[R] M) :=
  Module.Free.of_equiv (AlgebraTensorModule.cancelBaseChange R S T T M)

open TensorProduct in
/-- A finitely presented module whose localization at a prime is free becomes free after base
change to some localization away from an element outside the prime, in any model of that
localization. -/
@[ega "IV 6.11.9" "more general"]
theorem exists_free_baseChange_away (p : Ideal R) [p.IsPrime] (M : Type u) [AddCommGroup M]
    [Module R M] [Module.FinitePresentation R M]
    [Module.Free (Localization.AtPrime p) (LocalizedModule p.primeCompl M)] :
    ∃ r : R, r ∉ p ∧ ∀ (S : Type u) [CommRing S] [Algebra R S] [IsLocalization.Away r S],
      Module.Free S (S ⊗[R] M) := by
  obtain ⟨r, hr, hfree, -⟩ := Module.FinitePresentation.exists_free_localizedModule_powers
    p.primeCompl (LocalizedModule.mkLinearMap p.primeCompl M) (Localization.AtPrime p)
  refine ⟨r, hr, fun S _ _ _ => ?_⟩
  have : Module.Free (Localization.Away r) (Localization.Away r ⊗[R] M) :=
    Module.Free.of_equiv
      ((IsLocalizedModule.isBaseChange (Submonoid.powers r) (Localization.Away r)
        (LocalizedModule.mkLinearMap (Submonoid.powers r) M)).equiv.symm)
  let e := IsLocalization.algEquiv (Submonoid.powers r) (Localization.Away r) S
  let : Algebra (Localization.Away r) S := e.toAlgHom.toRingHom.toAlgebra
  have : IsScalarTower R (Localization.Away r) S := IsScalarTower.of_algebraMap_eq fun a => by
    show algebraMap R S a = e (algebraMap R (Localization.Away r) a)
    simp
  exact free_baseChange_of_free_baseChange (S := Localization.Away r) M

end Module

namespace AlgebraicGeometry.IsAffineOpen

open TensorProduct

variable {X : Scheme.{u}}

/-- **Finitely many finite projective modules become free near a point.** For finitely many
finite projective modules over the sections of an affine open `V` and a point `x ∈ V`, there is
a basic open neighbourhood `D(g) ⊆ V` of `x` over whose sections all their base changes are
free. -/
theorem exists_basicOpen_free_baseChange {V : X.Opens} (hV : IsAffineOpen V) {x : X}
    (hx : x ∈ V) (s : Finset ℤ) (M : ℤ → Type u) [∀ i, AddCommGroup (M i)]
    [∀ i, Module Γ(X, V) (M i)] [∀ i, Module.Finite Γ(X, V) (M i)]
    [∀ i, Module.Projective Γ(X, V) (M i)] :
    ∃ g : Γ(X, V), x ∈ X.basicOpen g ∧
      ∀ i ∈ s, Module.Free Γ(X, X.basicOpen g) (Γ(X, X.basicOpen g) ⊗[Γ(X, V)] M i) := by
  classical
  induction s using Finset.induction with
  | empty => exact ⟨1, by rwa [Scheme.basicOpen_one], by simp⟩
  | insert i₀ s _ ih =>
    obtain ⟨g, hxg, hg⟩ := ih
    let p := (hV.primeIdealOf ⟨x, hx⟩).asIdeal
    have : Module.FinitePresentation Γ(X, V) (M i₀) :=
      Module.finitePresentation_of_projective _ _
    have : Module.Free (Localization.AtPrime p) (LocalizedModule p.primeCompl (M i₀)) :=
      Module.free_of_flat_of_isLocalRing
    obtain ⟨r, hr, hfree⟩ := Module.exists_free_baseChange_away p (M i₀)
    have hxr : x ∈ X.basicOpen r := (hV.mem_basicOpen_iff_notMem_primeIdealOf r hx).2 hr
    refine ⟨g * r, by rw [Scheme.basicOpen_mul]; exact ⟨hxg, hxr⟩, ?_⟩
    intro i hi
    -- freeness over `D(h)` passes to `D(g r)` whenever `D(g r) ≤ D(h)`
    have key : ∀ (h : Γ(X, V)) (hle : X.basicOpen (g * r) ≤ X.basicOpen h) (m : ℤ),
        Module.Free Γ(X, X.basicOpen h) (Γ(X, X.basicOpen h) ⊗[Γ(X, V)] M m) →
        Module.Free Γ(X, X.basicOpen (g * r)) (Γ(X, X.basicOpen (g * r)) ⊗[Γ(X, V)] M m) :=
      fun h hle m _ => by
        let : Algebra Γ(X, X.basicOpen h) Γ(X, X.basicOpen (g * r)) :=
          (X.presheaf.map (homOfLE hle).op).hom.toAlgebra
        have : IsScalarTower Γ(X, V) Γ(X, X.basicOpen h) Γ(X, X.basicOpen (g * r)) :=
          IsScalarTower.of_algebraMap_eq fun a => by
            show (X.presheaf.map _).hom a = (X.presheaf.map _).hom ((X.presheaf.map _).hom a)
            rw [← CommRingCat.comp_apply, ← Functor.map_comp]
            rfl
        exact Module.free_baseChange_of_free_baseChange (S := Γ(X, X.basicOpen h)) (M m)
    rcases Finset.mem_insert.mp hi with rfl | hi
    · have : IsLocalization.Away r Γ(X, X.basicOpen r) := hV.isLocalization_basicOpen r
      exact key r (by rw [Scheme.basicOpen_mul]; exact inf_le_right) i (hfree _)
    · exact key g (by rw [Scheme.basicOpen_mul]; exact inf_le_left) i (hg i hi)

end AlgebraicGeometry.IsAffineOpen

namespace AlgebraicGeometry.ComplexAndDivisorSituation

/-- The situation of a perfect object with the empty divisor. -/
abbrev ofPerfect (X : Scheme.{u}) (E : DerivedCategory (OXMod.{u, u} X.toRingedSpace))
    (hE : Stacks.Cohomology.PerfectComplexes.IsPerfect E) :
    ComplexAndDivisorSituation.{u, u + 1} where
  X := X
  D := ⊤
  isEffectiveCartierDivisor := Stacks.Divisors.isEffectiveCartierDivisor_top
  hasDerivedCategory := HasDerivedCategory.standard _
  M := E
  isPerfect := (Stacks.Cohomology.PerfectComplexes.isPerfect_iff_ringedSpace E).1 hE

variable {X : Scheme.{u}} {E : DerivedCategory (OXMod.{u, u} X.toRingedSpace)}

/-- Restriction along an open immersion carries perfect objects to perfect objects. -/
theorem isPerfect_restrictFunctor_mapDerivedCategory {Y : Scheme.{u}} (j : Y ⟶ X)
    [IsOpenImmersion j] (hE : Stacks.Cohomology.PerfectComplexes.IsPerfect.{u, u, u + 1} E) :
    Stacks.Cohomology.PerfectComplexes.IsPerfect.{u, u, u + 1} (X := Y.toRingedSpace)
      ((Scheme.Modules.restrictFunctor j).mapDerivedCategory.obj E) :=
  Stacks.Cohomology.PerfectComplexTriangles.isPerfect_of_iso (X := Y.toRingedSpace)
    ((Scheme.Modules.derivedRestrictIsoDerivedPullback j).app E).symm
    (RingedSpace.KFlatDerivedPullback.isPerfect_derivedPullback j.toLRSHom.toShHom E hE)

/-- **A perfect object is presented over an affine open by a perfect complex of modules.** Over
an affine open `V` of `X`, a perfect object `E` of `D(𝒪_X)` is the sheaf, transported along
`V ≅ Spec Γ(X, V)`, of a perfect object of `D(Γ(X, V))` (Stacks 06Z0 and 08EB). -/
theorem exists_isPerfect_presentation
    (hE : Stacks.Cohomology.PerfectComplexes.IsPerfect.{u, u, u + 1} E) (V : X.affineOpens) :
    ∃ ω : DerivedCategory (ModuleCat.{u} Γ(X, V.1)), StacksDraft.Perfect.IsPerfect ω ∧
      Nonempty ((Scheme.Modules.restrictFunctor V.1.ι).mapDerivedCategory.obj E ≅
        (tilde.functor Γ(X, V.1) ⋙
          Scheme.Modules.restrictFunctor V.2.isoSpec.hom).mapDerivedCategory.obj ω) := by
  obtain ⟨ω, ⟨e⟩⟩ := Stacks.Duality.exists_nonempty_iso_tilde_of_isQuasicoherent (K := E) V.2
    (PerfectApproximation.isQuasicoherent_homology_of_isPerfect _ E hE)
  refine ⟨ω, (isPerfect_tilde_iff ω).1 ?_, ⟨e⟩⟩
  exact Stacks.Cohomology.PerfectComplexTriangles.isPerfect_of_iso
    (X := (Spec Γ(X, V.1)).toRingedSpace)
    ((Scheme.Modules.restrictFunctor V.2.isoSpec.inv).mapDerivedCategory.mapIso e ≪≫
      (Stacks.AffineTilde.tildeIsoSpecCancelIso V.2).app ω)
    (isPerfect_restrictFunctor_mapDerivedCategory V.2.isoSpec.inv
      (isPerfect_restrictFunctor_mapDerivedCategory V.1.ι hE))

/-- **Every point of a scheme lies in an affine chart of a perfect object.** For a perfect object
`E` of `D(𝒪_X)`, a point `x` and an open neighbourhood `W` of `x`, there is an affine open
`U ⊆ W` containing `x` together with a bounded complex of finite free `Γ(X, U)`-modules whose
associated complex of `𝒪_U`-modules represents `E|_U`; this is an affine chart of the
situation `(X, ∅, E)`.

Over an affine open `V ∋ x` the object `E|_V` comes from a perfect object of `D(Γ(X, V))`
(`AlgebraicGeometry.ComplexAndDivisorSituation.exists_isPerfect_presentation`), represented by a
bounded complex `P` of finite projective modules; on a basic open `D(g) ∋ x` the finitely many
nonzero terms of `P` become free, and the base change of `P` to `Γ(X, D(g))` is the chart. -/
theorem exists_affineChart_ofPerfect
    (hE : Stacks.Cohomology.PerfectComplexes.IsPerfect.{u, u, u + 1} E) (x : X) (W : X.Opens)
    (hx : x ∈ W) :
    ∃ C : AffineChart (ofPerfect X E hE), x ∈ (C.U : X.Opens) ∧ (C.U : X.Opens) ≤ W := by
  classical
  obtain ⟨_, ⟨V, hV, rfl⟩, hxV, hVW⟩ :=
    X.isBasis_affineOpens.exists_subset_of_mem_open hx W.isOpen
  obtain ⟨ω, ⟨P, a, b, hGE, hLE, hfin, hproj, ⟨eP⟩⟩, ⟨e⟩⟩ :=
    exists_isPerfect_presentation hE ⟨V, hV⟩
  obtain ⟨g, hxg, hfree⟩ :=
    hV.exists_basicOpen_free_baseChange hxV (Finset.Icc a b) (fun i => P.X i)
  let φ := (X.presheaf.map (homOfLE (X.basicOpen_le g)).op).hom
  let := Stacks.Duality.preservesFiniteLimits_extendScalars_basicOpen ⟨V, hV⟩ g
  obtain ⟨e₁⟩ := Stacks.Duality.nonempty_iso_extendScalars_basicOpen (K := E) ⟨V, hV⟩ g ω e
  let F := ModuleCat.extendScalars.{u, u, u} φ
  let P' := (F.mapHomologicalComplex (ComplexShape.up ℤ)).obj P
  have hzero : ∀ i, i ∉ Finset.Icc a b → IsZero (P'.X i) := by
    intro i hi
    rw [Finset.mem_Icc, not_and_or, not_le, not_le] at hi
    rcases hi with h | h
    · exact F.map_isZero (P.isZero_of_isStrictlyGE a i h)
    · exact F.map_isZero (P.isZero_of_isStrictlyLE b i h)
  have hfree' : ∀ i, Module.Free Γ(X, X.basicOpen g) (P'.X i) := by
    intro i
    by_cases hi : i ∈ Finset.Icc a b
    · exact hfree i hi
    · have : Subsingleton (P'.X i) := ModuleCat.isZero_iff_subsingleton.mp (hzero i hi)
      exact Module.Free.of_subsingleton _ _
  have hfin' : ∀ i, Module.Finite Γ(X, X.basicOpen g) (P'.X i) := by
    intro i
    let := φ.toAlgebra
    have := hfin i
    exact Module.Finite.base_change Γ(X, V) Γ(X, X.basicOpen g) (P.X i)
  have hsupp : {i : ℤ | ¬ Subsingleton (P'.X i)}.Finite :=
    (Finset.Icc a b).finite_toSet.subset fun i hi =>
      by_contra fun hni => hi (ModuleCat.isZero_iff_subsingleton.mp (hzero i hni))
  obtain ⟨B⟩ := Stacks.Eta.BasisPresentation.exists_of_free hfree' hfin' hsupp
  let U : X.affineOpens := X.affineBasicOpen (U := ⟨V, hV⟩) g
  let T := tilde.functor Γ(X, U.1) ⋙ Scheme.Modules.restrictFunctor U.2.isoSpec.hom
  let E₀ := DerivedCategory.Q.objPreimage E
  let e₀ : DerivedCategory.Q.obj E₀ ≅ E := DerivedCategory.Q.objObjPreimageIso E
  refine ⟨{ U := U
            f := 1
            regular := isRegular_one
            divisor_ideal := by simp [Scheme.IdealSheafData.ideal_top]
            complex := B.toBoundedComplex
            represents := ⟨E₀, ⟨e₀⟩, ⟨?_⟩⟩ }, hxg, (X.basicOpen_le g).trans hVW⟩
  exact ((Scheme.Modules.restrictFunctor U.1.ι).mapDerivedCategoryFactors.app E₀).symm ≪≫
    (Scheme.Modules.restrictFunctor U.1.ι).mapDerivedCategory.mapIso e₀ ≪≫ e₁ ≪≫
    T.mapDerivedCategory.mapIso (F.mapDerivedCategory.mapIso eP ≪≫
      F.mapDerivedCategoryFactors.app P ≪≫ DerivedCategory.Q.mapIso B.iso) ≪≫
    T.mapDerivedCategoryFactors.app B.toBoundedComplex.toCochainComplex

section Compat

attribute [local instance 100000] modulesHasDerivedCategory

/-- **The Fitting minor ideals of two affine charts agree on the smaller chart.** If the domain
of an affine chart `C'` is contained in that of `C`, then the ideal of minors
`Fit_{i, k}` of the complex of `C'` is the extension of that of `C` along the restriction map.

The restriction of `C` to the domain of `C'` and `C'` itself both represent the restriction of
the perfect object, so their complexes are isomorphic in the derived category of the ring of
sections (Stacks 06Z0), and the ideal of minors only depends on that object
(`BoundedComplex.fittingMinorIdeal_eq_of_derivedIso`). -/
theorem AffineChart.map_fittingMinorIdeal_eq {S : ComplexAndDivisorSituation.{u, u + 1}}
    (C C' : AffineChart S) (hle : (C'.U : S.X.Opens) ≤ (C.U : S.X.Opens)) (i k : ℤ) :
    Ideal.map (S.X.presheaf.map (homOfLE hle).op).hom (C.complex.fittingMinorIdeal i k) =
      C'.complex.fittingMinorIdeal i k := by
  rw [BoundedComplex.map_fittingMinorIdeal]
  exact BoundedComplex.fittingMinorIdeal_eq_of_derivedIso _ _
    (Stacks.Duality.nonempty_iso_of_nonempty_iso_tilde C'.U.2
      (AffineChart.representsDerivedIso (C.restrict C'.U hle))
      (AffineChart.representsDerivedIso C')) i k

end Compat

end AlgebraicGeometry.ComplexAndDivisorSituation
