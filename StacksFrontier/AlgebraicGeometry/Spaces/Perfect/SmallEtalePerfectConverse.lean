module

import StacksCore.Tactic.StacksAttribute
public import StacksFrontier.AlgebraicGeometry.Spaces.Perfect.SmallEtalePerfectForwardPseudoCoherent
public import StacksFrontier.AlgebraicGeometry.Descent.AssociatedModule.SmallEtaleFlatDescent
public import StacksFrontier.AlgebraicGeometry.Descent.AssociatedModule.SmallEtaleSliceBoundedAbove
public import StacksFrontier.AlgebraicGeometry.PseudoCoherentSites.TruncatingApproximationsGeneral
public import StacksFrontier.AlgebraicGeometry.Sites.OverMapComp
public import StacksFrontier.AlgebraicGeometry.Topologies.Etale.JointlySurjectiveSieves
public import StacksFrontier.Algebra.Homology.DerivedCategory.TruncGEIsoOfCohomologyIsomorphisms
public import StacksFrontier.CategoryTheory.Sites.Cohomology.StrictlyPerfect.FlatLowestTerm
public import StacksFrontier.CategoryTheory.Sites.Cohomology.StrictlyPerfect.OpcyclesFinitePresentation
public import StacksFrontier.CategoryTheory.Sites.Cohomology.TorAmplitude.PerfectnessCriterionGeneral
public import StacksFrontier.CategoryTheory.Sites.Cohomology.StrictlyPerfect.IteratedSliceFiniteFreeSummands
public import StacksFrontier.CategoryTheory.Sites.Cohomology.TorAmplitude.PerfectnessCriterion
public import StacksFrontier.CategoryTheory.Sites.Cohomology.PseudoCoherent.BoundedLocalApproximationsGeneral
public import StacksFrontier.CategoryTheory.Sites.Cohomology.StrictlyPerfect.LocalRepresentationOfADerivedMapGeneral

/-!
# Stacks 08HG

Let `S` be a scheme and `E` an object of `D(𝒪_S)`. Stacks 08HG: `E` is a perfect object of
`D(𝒪_S)` if and only if `ε^*E` is a perfect object of `D(𝒪_étale)`, `ε` being the comparison
morphism of ringed sites of Stacks 08H7. The forward direction is
`AlgebraicGeometry.SmallEtale.perfectToAssociatedModule_of_slice_exact`; this module proves the
converse and registers the equivalence.

## The argument

The source derives the converse from Stacks 08G8 — perfect is pseudo-coherent and locally of
finite Tor dimension — and the converses of Stacks 08HE and Stacks 08HF. Here the proof of
Stacks 08G7 is followed instead, with its one use of Tor dimension replaced by the flatness of a
single module, which descends along `ε` by the same faithfulness that makes Stacks 08HF work.
Fix a point `x` of an open `U` of `S`.

1. `ε^*E` is perfect, so `x` lies in the image open of an étale `T ⟶ U` over which `ε^*E` is
   represented by a strictly perfect complex `P` vanishing below some `a`; the cohomology of `E`
   then vanishes below `a` near `x` (`exists_etale_model_of_isPerfectComplex`).
2. `E` is `(a - 1)`-pseudo-coherent (Stacks 08HE, clause (2) ⇒ (1)), so near `x` a strictly
   perfect `R` maps to a representative of `E` by a map invertible on cohomology in degrees
   `≥ a`. Then `τ_{≥ a}R` represents `E` near `x`, and it is strictly perfect as soon as its
   lowest term, the opcycles `M = Coker(R^{a-1} ⟶ R^a)`, is locally a direct summand of a finite
   free module. As `M` is of finite presentation, Stacks 08FD reduces this to flatness of `M`
   (`exists_strictlyPerfect_model_of_isFlat_opcycles`).
3. `M` is flat (`isFlat_opcycles_of_etale_model`): over every étale object mapping to `T`, the
   complex `τ_{≥ a}ε^*R` with flat terms above `a` and the strictly perfect `P` represent the same
   object and both vanish below `a`, so the lowest term `ε^*M` is flat étale locally
   (`Stacks.SheafOfModules.exists_coveringSieve_isFlat_opcycles`, the cone argument of
   `StacksFrontier/CategoryTheory/Sites/Cohomology/StrictlyPerfect/FlatLowestTerm.lean`), and
   flatness descends along `ε`
   (`AlgebraicGeometry.SmallEtale.isFlat_over_of_isFlat_over_associatedModule`).

No derived tensor product on the small étale site is used: the small étale ringed site is a
`RingedSite.{u + 1, u, u}`, and the étale-side statements above are proved at independent
universes.

## Main results

* `AlgebraicGeometry.SmallEtale.isPerfectZariski_of_isPerfectSmallEtale`: the converse.
* `AlgebraicGeometry.SmallEtale.isPerfectZariski_iff_isPerfectSmallEtale`: **Stacks 08HG**.

## References

* [Stacks Project, Tag 08HG](https://stacks.math.columbia.edu/tag/08HG)
* [Stacks Project, Tag 08G7](https://stacks.math.columbia.edu/tag/08G7)
* [Stacks Project, Tag 08G8](https://stacks.math.columbia.edu/tag/08G8)
* [Stacks Project, Tag 08HE](https://stacks.math.columbia.edu/tag/08HE)
* [Stacks Project, Tag 08HF](https://stacks.math.columbia.edu/tag/08HF)
* [Stacks Project, Tag 08FD](https://stacks.math.columbia.edu/tag/08FD)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits TopologicalSpace

universe u d d'

namespace Stacks.SheafOfModules

/-- A strictly perfect complex vanishes below some degree. -/
theorem exists_isZero_X_lt_of_isStrictlyPerfect {C : Type*} [Category C]
    {J : GrothendieckTopology C} {R : Sheaf J RingCat.{u}}
    [HasWeakSheafify J AddCommGrpCat.{u}] [J.WEqualsLocallyBijective AddCommGrpCat.{u}]
    [J.HasSheafCompose (forget₂ RingCat.{u} AddCommGrpCat.{u})]
    {P : CochainComplex (_root_.SheafOfModules.{u} R) ℤ} (hP : IsStrictlyPerfect R P) :
    ∃ a : ℤ, ∀ i : ℤ, i < a → IsZero (P.X i) := by
  obtain ⟨r, hr⟩ := hP.bounded.bddBelow
  refine ⟨r, fun i hi => ?_⟩
  by_contra h
  exact absurd (hr (by simpa only [Set.mem_ofPred_eq] using h)) (by omega)

end Stacks.SheafOfModules

namespace AlgebraicGeometry.SmallEtale

variable (B : BigEtaleSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)
  [HasDerivedCategory.{d} (SheafOfModules.{u} S.ringCatSheaf)]
  [HasDerivedCategory.{d'} (SheafOfModules.{u} (structureSheaf B S hS))]

/-- **The étale datum at a point.** If `ε^*E` is perfect, represented by a perfect complex `E'`,
every point `x` of an open `U` of `S` lies in the image open of an étale object `T` over `U`,
and there is an integer `a` such that `E'` is represented over `T` by a strictly perfect complex
vanishing below `a` and the cohomology sheaves of `E` vanish below `a` on that image open. -/
theorem exists_etale_model_of_isPerfectComplex
    (E : DerivedCategory (SheafOfModules.{u} S.ringCatSheaf))
    (E' : CochainComplex (SheafOfModules.{u} (structureSheaf B S hS)) ℤ)
    (hE' : (smallEtaleRingedSite B S hS).IsPerfectComplex E')
    (eE' : DerivedCategory.Q.obj E' ≅ (associatedModuleOfSheaf B S hS).mapDerivedCategory.obj E)
    (U : S.Opens) (x : ↥S) (hx : x ∈ U) :
    ∃ (T : SmallEtale B S hS) (a : ℤ)
      (P : CochainComplex (SheafOfModules.{u} ((structureSheaf B S hS).over T)) ℤ),
      imageOpen B S hS T ≤ U ∧ x ∈ imageOpen B S hS T ∧
      IsStrictlyPerfect _ P ∧ (∀ i, i < a → IsZero (P.X i)) ∧
      (∃ α : P ⟶ ((SheafOfModules.overFunctor.{u} (structureSheaf B S hS) T).mapHomologicalComplex
        (ComplexShape.up ℤ)).obj E', QuasiIso α) ∧
      ∀ i, i < a → IsZero ((((DerivedCategory.homologyFunctor _ i).obj E)).over
        (imageOpen B S hS T)) := by
  obtain ⟨Sp0, hSp0, hmod0⟩ := hE' ((opensToSmallEtale B S hS).obj U)
  obtain ⟨Z0, g0, hg0, hxZ0⟩ := exists_mem_arrows_mem_range B S hS hSp0
    (⟨x, hx⟩ : (toScheme B S hS).obj ((opensToSmallEtale B S hS).obj U))
  obtain ⟨T, q, f₀, hf₀, rfl⟩ := hg0
  obtain ⟨P0, hP0, α0, hα0⟩ := hmod0 f₀ hf₀
  obtain ⟨a, ha⟩ := Stacks.SheafOfModules.exists_isZero_X_lt_of_isStrictlyPerfect hP0
  have hxZ : x ∈ imageOpen B S hS T := by
    obtain ⟨z, hz⟩ := hxZ0
    refine imageOpen_le_imageOpen B S hS q ⟨z, ?_⟩
    rw [BigEtaleOver.hom_hom_eq B S hS (q ≫ f₀).hom]
    exact congrArg Subtype.val hz
  refine ⟨T, a, P0, (imageOpen_le_imageOpen B S hS f₀).trans (imageOpen_opensObj B S hS U).le,
    hxZ, hP0, ha, ⟨α0, hα0⟩, fun i hi => ?_⟩
  refine isZero_homology_over_of_isZero_homology_over_associatedModule B S hS _ E i ?_
  refine isZero_over_opensObj_imageOpen_of_isZero_over B S hS T _ ?_
  let G := SheafOfModules.overFunctor.{u} (structureSheaf B S hS) T
  have : PreservesFiniteLimits G :=
    Stacks.SheafOfModules.LocalCokernel.overFunctor_preservesFiniteLimits.{u + 1, u, u, u} _
  have : G.Additive := Functor.additive_of_preserves_binary_products _
  have : PreservesFiniteColimits G :=
    Stacks.SheafOfModules.LocalCokernel.overFunctor_preservesFiniteColimits.{u + 1, u, u, u} _
  have e1 : G.obj (E'.homology i) ≅ P0.homology i :=
    (ShortComplex.mapHomologyIso (E'.sc i) G).symm ≪≫
      (have := hα0; (asIso (HomologicalComplex.homologyMap α0 i)).symm)
  have e2 : (DerivedCategory.homologyFunctor _ i).obj
      ((associatedModuleOfSheaf B S hS).mapDerivedCategory.obj E) ≅ E'.homology i :=
    (DerivedCategory.homologyFunctor _ i).mapIso eE'.symm ≪≫
      (DerivedCategory.homologyFunctorFactors _ i).app E'
  exact (HomologicalComplex.ExactAt.of_isZero (ha i hi)).isZero_homology.of_iso
    (G.mapIso e2 ≪≫ e1)

/-! ### The étale side: the opcycles of a Zariski approximation are flat -/

attribute [local instance] Stacks.hasSheafCompose_forget₂_commRingCat

/-- The restriction along an arrow of the small étale site is exact. -/
local instance etaleOverMapPreservesFiniteLimits {Z Z' : SmallEtale B S hS} (f : Z' ⟶ Z) :
    PreservesFiniteLimits (SheafOfModules.overMap.{u} (structureSheaf B S hS) f) :=
  Stacks.SheafOfModules.LocalCokernel.overMap_preservesFiniteLimits.{u + 1, u, u} f

/-- The restriction along an arrow of the small étale site is exact. -/
local instance etaleOverMapPreservesFiniteColimits {Z Z' : SmallEtale B S hS} (f : Z' ⟶ Z) :
    PreservesFiniteColimits (SheafOfModules.overMap.{u} (structureSheaf B S hS) f) :=
  Stacks.SheafOfModules.LocalCokernel.overMap_preservesFiniteColimits.{u + 1, u, u} f

private instance etaleOverMapAdditive {Z Z' : SmallEtale B S hS} (f : Z' ⟶ Z) :
    (SheafOfModules.overMap.{u} (structureSheaf B S hS) f).Additive := ⟨by intros; ext; rfl⟩

private instance etaleOverMapPreservesHomology {Z Z' : SmallEtale B S hS} (f : Z' ⟶ Z) :
    (SheafOfModules.overMap.{u} (structureSheaf B S hS) f).PreservesHomology :=
  Functor.preservesHomologyOfExact _

/-- Over an étale object `Z` mapping to both `ε(W)` and `T`, the restriction of the étale model `P`
and that of `ε_W^*(K'|_W)` are isomorphic in the derived category. -/
theorem nonempty_iso_Q_overMap_sliceAssociatedModule_restrictComplex
    (E : DerivedCategory (SheafOfModules.{u} S.ringCatSheaf))
    (E' : CochainComplex (SheafOfModules.{u} (structureSheaf B S hS)) ℤ)
    (eE' : DerivedCategory.Q.obj E' ≅ (associatedModuleOfSheaf B S hS).mapDerivedCategory.obj E)
    (T : SmallEtale B S hS)
    (P : CochainComplex (SheafOfModules.{u} ((structureSheaf B S hS).over T)) ℤ)
    (α₀ : P ⟶ ((SheafOfModules.overFunctor.{u} (structureSheaf B S hS) T).mapHomologicalComplex
        (ComplexShape.up ℤ)).obj E') (hα₀ : QuasiIso α₀)
    (K' : CochainComplex (SheafOfModules.{u} S.ringCatSheaf) ℤ)
    (eK' : DerivedCategory.Q.obj K' ≅ E) (W : S.Opens) {Z : SmallEtale B S hS}
    (g : Z ⟶ (opensToSmallEtale B S hS).obj W) (h : Z ⟶ T)
    [HasDerivedCategory (SheafOfModules.{u} ((structureSheaf B S hS).over Z))] :
    Nonempty (DerivedCategory.Q.obj
        (((SheafOfModules.overMap.{u} (structureSheaf B S hS) h).mapHomologicalComplex
          (ComplexShape.up ℤ)).obj P) ≅
      DerivedCategory.Q.obj
        (((SheafOfModules.overMap.{u} (structureSheaf B S hS) g).mapHomologicalComplex
          (ComplexShape.up ℤ)).obj (((sliceAssociatedModule B S hS W).mapHomologicalComplex
            (ComplexShape.up ℤ)).obj (S.zariskiRingedSite.restrictComplex K' W)))) := by
  let F := associatedModuleOfSheaf B S hS
  let G := SheafOfModules.overMap.{u} (structureSheaf B S hS) g
  let H := SheafOfModules.overMap.{u} (structureSheaf B S hS) h
  let GC := G.mapHomologicalComplex (ComplexShape.up ℤ)
  let HC := H.mapHomologicalComplex (ComplexShape.up ℤ)
  let oZ := SheafOfModules.overFunctor.{u} (structureSheaf B S hS) Z
  have : PreservesFiniteLimits oZ :=
    Stacks.SheafOfModules.LocalCokernel.overFunctor_preservesFiniteLimits.{u + 1, u, u, u} Z
  have : PreservesFiniteColimits oZ :=
    Stacks.SheafOfModules.LocalCokernel.overFunctor_preservesFiniteColimits.{u + 1, u, u, u} Z
  have : oZ.Additive := Functor.additive_of_preserves_binary_products _
  let oT := SheafOfModules.overFunctor.{u} (structureSheaf B S hS) T
  let c₁ : HC.obj ((oT.mapHomologicalComplex (ComplexShape.up ℤ)).obj E') ≅
      (oZ.mapHomologicalComplex (ComplexShape.up ℤ)).obj E' :=
    (Stacks.SheafOfModules.overFunctorMapComplexIso (structureSheaf B S hS) h).app E'
  have := (DerivedCategory.isIso_Q_map_iff_quasiIso _ _).2
    (inferInstance : QuasiIso (HC.map α₀ ≫ c₁.hom))
  exact ⟨asIso (DerivedCategory.Q.map (HC.map α₀ ≫ c₁.hom)) ≪≫
    (oZ.mapDerivedCategoryFactors.app E').symm ≪≫
      oZ.mapDerivedCategory.mapIso (eE' ≪≫ F.mapDerivedCategory.mapIso eK'.symm ≪≫
        F.mapDerivedCategoryFactors.app K') ≪≫
      oZ.mapDerivedCategoryFactors.app _ ≪≫ DerivedCategory.Q.mapIso
        (((Stacks.SheafOfModules.overFunctorMapComplexIso (structureSheaf B S hS) g).app
          ((F.mapHomologicalComplex (ComplexShape.up ℤ)).obj K')).symm ≪≫
        GC.mapIso ((associatedModuleOverComplexIso B S hS W).app K').symm)⟩

/-- **Étale-local flatness of the lowest opcycles.** In the setting of
`AlgebraicGeometry.SmallEtale.isFlat_opcycles_of_etale_model`, over an étale object `Z` mapping to
both `ε(W)` and `T`, the lowest opcycles of `ε_W^*R` restricted to `Z` are flat étale locally. -/
theorem exists_coveringSieve_isFlat_opcycles_overMap_sliceAssociatedModule
    (E : DerivedCategory (SheafOfModules.{u} S.ringCatSheaf))
    (E' : CochainComplex (SheafOfModules.{u} (structureSheaf B S hS)) ℤ)
    (eE' : DerivedCategory.Q.obj E' ≅ (associatedModuleOfSheaf B S hS).mapDerivedCategory.obj E)
    (T : SmallEtale B S hS) (a : ℤ)
    (P : CochainComplex (SheafOfModules.{u} ((structureSheaf B S hS).over T)) ℤ)
    (hP : IsStrictlyPerfect _ P) (hPa : ∀ i, i < a → IsZero (P.X i))
    (α₀ : P ⟶ ((SheafOfModules.overFunctor.{u} (structureSheaf B S hS) T).mapHomologicalComplex
        (ComplexShape.up ℤ)).obj E') (hα₀ : QuasiIso α₀)
    (K' : CochainComplex (SheafOfModules.{u} S.ringCatSheaf) ℤ)
    (eK' : DerivedCategory.Q.obj K' ≅ E) (W : S.Opens)
    (R : CochainComplex (SheafOfModules.{u} (S.ringCatSheaf.over W)) ℤ)
    (hR : IsStrictlyPerfect _ R) (α : R ⟶ S.zariskiRingedSite.restrictComplex K' W)
    (hα : ∀ i, a ≤ i → IsIso (HomologicalComplex.homologyMap α i))
    (hK' : ∀ i, i < a → IsZero ((K'.homology i).over W)) {Z : SmallEtale B S hS}
    (g : Z ⟶ (opensToSmallEtale B S hS).obj W) (h : Z ⟶ T) :
    ∃ SZ : Sieve Z, SZ ∈ topology B S hS Z ∧ ∀ ⦃Z' : SmallEtale B S hS⦄ (f : Z' ⟶ Z), SZ f →
      AlgebraicGeometry.SheafOfModules.IsFlat.{u, u + 1, u, u}
        (O := ((smallEtaleRingedSite B S hS).over Z').O)
        ((SheafOfModules.overMap.{u} (structureSheaf B S hS) f).obj
          ((((SheafOfModules.overMap.{u} (structureSheaf B S hS) g).mapHomologicalComplex
            (ComplexShape.up ℤ)).obj (((sliceAssociatedModule B S hS W).mapHomologicalComplex
              (ComplexShape.up ℤ)).obj R)).opcycles a)) := by
  let Es := smallEtaleRingedSite B S hS
  let L := sliceAssociatedModule B S hS W
  have : L.PreservesHomology := Functor.preservesHomologyOfExact _
  let G := SheafOfModules.overMap.{u} (structureSheaf B S hS) g
  let H := SheafOfModules.overMap.{u} (structureSheaf B S hS) h
  let : HasDerivedCategory (SheafOfModules.{u} ((structureSheaf B S hS).over Z)) :=
    HasDerivedCategory.standard _
  let GC := G.mapHomologicalComplex (ComplexShape.up ℤ)
  let LC := L.mapHomologicalComplex (ComplexShape.up ℤ)
  let K'W : CochainComplex (SheafOfModules.{u} (S.ringCatSheaf.over W)) ℤ :=
    S.zariskiRingedSite.restrictComplex K' W
  have hY' : ∀ i, i < a → IsZero ((GC.obj (LC.obj K'W)).homology i) := fun i hi =>
    (G.map_isZero ((L.map_isZero ((hK' i hi).of_iso (restrictComplexHomologyIso S W K' i))).of_iso
      (ShortComplex.mapHomologyIso (K'W.sc i) L))).of_iso
        (ShortComplex.mapHomologyIso ((LC.obj K'W).sc i) G)
  obtain ⟨e⟩ :=
    nonempty_iso_Q_overMap_sliceAssociatedModule_restrictComplex B S hS E E' eE' T P α₀ hα₀ K' eK'
      W g h
  let : HasDerivedCategory (SheafOfModules.{u}
      ((Stacks.SheafOfModules.Tensor.ringSheaf Es.O).over Z)) :=
    ‹HasDerivedCategory (SheafOfModules.{u} ((structureSheaf B S hS).over Z))›
  exact Stacks.SheafOfModules.exists_coveringSieve_isFlat_opcycles Es Z
    (Stacks.SheafOfModules.isStrictlyPerfect_restrictComplexAlong_general _ h hP)
    (Stacks.SheafOfModules.isStrictlyPerfect_restrictComplexAlong_general _ g
      (isStrictlyPerfect_sliceAssociatedModule B S hS W hR))
    (GC.map (LC.map α)) a
    (fun i hi => AlgebraicGeometry.RingedSite.isIso_homologyMap_map G _ i
      (AlgebraicGeometry.RingedSite.isIso_homologyMap_map L α i (hα i hi))) hY' e
    (fun i hi => H.map_isZero (hPa i hi))

/-- **The lowest opcycles of a Zariski approximation are flat.** Let `E` be an object of `D(𝒪_S)`
with `ε^*E` represented by a complex `E'` which, over an étale object `T`, receives a
quasi-isomorphism from a strictly perfect complex `P` vanishing below `a`. Let `K'` represent `E`
and let `α : R ⟶ K'|_{W}` be a strictly perfect approximation over an open `W` below the image
open of `T`, invertible on cohomology in degrees `≥ a`, with `K'|_W` acyclic below `a`. Then the
opcycles `Coker(R^{a-1} ⟶ R^a)` are a flat `𝒪_W`-module.

Over every étale `Z ⟶ ε(W)` factoring through `T` — these form a covering sieve of `ε(W)`, `T`
covering `ε(im T)` — the complex `ε_W^*R` restricted to `Z` approximates `ε^*E|_Z`, which is also
represented by the strictly perfect complex `P|_Z` vanishing below `a`; so its lowest opcycles,
which are `ε^*` of those of `R`, are flat étale locally on `Z`
(`Stacks.SheafOfModules.exists_coveringSieve_isFlat_opcycles`). Flatness descends along `ε`
(`AlgebraicGeometry.SmallEtale.isFlat_over_of_isFlat_over_associatedModule`). -/
theorem isFlat_opcycles_of_etale_model
    (E : DerivedCategory (SheafOfModules.{u} S.ringCatSheaf))
    (E' : CochainComplex (SheafOfModules.{u} (structureSheaf B S hS)) ℤ)
    (eE' : DerivedCategory.Q.obj E' ≅ (associatedModuleOfSheaf B S hS).mapDerivedCategory.obj E)
    (T : SmallEtale B S hS) (a : ℤ)
    (P : CochainComplex (SheafOfModules.{u} ((structureSheaf B S hS).over T)) ℤ)
    (hP : IsStrictlyPerfect _ P) (hPa : ∀ i, i < a → IsZero (P.X i))
    (α₀ : P ⟶ ((SheafOfModules.overFunctor.{u} (structureSheaf B S hS) T).mapHomologicalComplex
        (ComplexShape.up ℤ)).obj E') (hα₀ : QuasiIso α₀)
    (K' : CochainComplex (SheafOfModules.{u} S.ringCatSheaf) ℤ)
    (eK' : DerivedCategory.Q.obj K' ≅ E)
    (W : S.Opens) (hW : W ≤ imageOpen B S hS T)
    (R : CochainComplex (SheafOfModules.{u} (S.ringCatSheaf.over W)) ℤ)
    (hR : IsStrictlyPerfect _ R) (α : R ⟶ S.zariskiRingedSite.restrictComplex K' W)
    (hα : ∀ i, a ≤ i → IsIso (HomologicalComplex.homologyMap α i))
    (hK' : ∀ i, i < a → IsZero ((K'.homology i).over W)) :
    AlgebraicGeometry.SheafOfModules.IsFlat.{u, u, u, u} (O := (S.zariskiRingedSite.over W).O)
      (R.opcycles a) := by
  let Es := smallEtaleRingedSite B S hS
  let εW := (opensToSmallEtale B S hS).obj W
  let L := sliceAssociatedModule B S hS W
  have : L.PreservesHomology := Functor.preservesHomologyOfExact _
  -- The étale objects over `ε(W)` which factor through `T`.
  let Sv₀ : Sieve εW := (Sieve.ofArrows (fun _ : Unit => T)
    (fun _ => toImageOpen B S hS T)).pullback ((opensToSmallEtale B S hS).map (homOfLE hW))
  have hSv₀ : Sv₀ ∈ topology B S hS εW :=
    (topology B S hS).pullback_stable _ (ofArrows_toImageOpen_mem_topology B S hS T)
  have key := fun ⦃Z : SmallEtale B S hS⦄ (g : Z ⟶ εW) (hg : Sv₀ g) =>
    exists_coveringSieve_isFlat_opcycles_overMap_sliceAssociatedModule B S hS E E' eE' T a P
      hP hPa α₀ hα₀ K' eK' W R hR α hα hK' g
      ((Sieve.mem_ofArrows_iff _ _ _).1 hg).choose_spec.choose
  choose SZ hSZ hflatZ using key
  let Sv : Sieve εW := Sieve.bind Sv₀.arrows (fun Z g hg => SZ g hg)
  have hSv : Sv ∈ topology B S hS εW :=
    (topology B S hS).bind_covering hSv₀ (fun Z g hg => hSZ g hg)
  let N := (opensRestrictionSection S W).obj (R.opcycles a)
  refine Stacks.SheafOfModules.isFlat_of_iso_freeUniverse (X := S.zariskiRingedSite.over W)
    ((opensRestrictionSectionIso S W).app (R.opcycles a))
    (isFlat_over_of_isFlat_over_associatedModule B S hS N W Sv hSv ?_)
  intro Z' k hk
  obtain ⟨Z, f, g, hg, hf, rfl⟩ := hk
  let G := SheafOfModules.overMap.{u} (structureSheaf B S hS) g
  let LC := L.mapHomologicalComplex (ComplexShape.up ℤ)
  let i₁ : ((G.mapHomologicalComplex (ComplexShape.up ℤ)).obj (LC.obj R)).opcycles a ≅
      G.obj (L.obj (R.opcycles a)) :=
    ShortComplex.mapOpcyclesIso ((LC.obj R).sc a) G ≪≫
      G.mapIso (ShortComplex.mapOpcyclesIso (R.sc a) L)
  let i₂ : L.obj (R.opcycles a) ≅ ((associatedModule B S hS).obj N).over εW :=
    L.mapIso ((opensRestrictionSectionIso S W).app (R.opcycles a)).symm ≪≫
      (associatedModuleOverIso B S hS W).app N
  let i₃ := (Stacks.SheafOfModules.overMapCompIso (structureSheaf B S hS) g f).app
    (((associatedModule B S hS).obj N).over εW)
  let i₄ := (SheafOfModules.overFunctorMap.{u} (structureSheaf B S hS) (f ≫ g)).app
    ((associatedModule B S hS).obj N)
  exact Stacks.SheafOfModules.isFlat_of_iso_freeUniverse (X := Es.over Z')
    ((SheafOfModules.overMap.{u} (structureSheaf B S hS) f).mapIso (i₁ ≪≫ G.mapIso i₂) ≪≫
      i₃ ≪≫ i₄) (hflatZ g hg f hf)

/-! ### The Zariski side: flat opcycles give strictly perfect models -/

section Zariski

variable (S : Scheme.{u})

attribute [local instance] Stacks.hasSheafCompose_forget₂_commRingCat

/-- The restriction along an arrow of the small Zariski site is exact. -/
local instance zariskiOverMapPreservesFiniteLimits {W W' : S.Opens} (f : W' ⟶ W) :
    PreservesFiniteLimits (SheafOfModules.overMap.{u}
      (Stacks.SheafOfModules.Tensor.ringSheaf S.zariskiRingedSite.O) f) :=
  Stacks.SheafOfModules.LocalCokernel.overMap_preservesFiniteLimits f

/-- The restriction along an arrow of the small Zariski site is exact. -/
local instance zariskiOverMapPreservesFiniteColimits {W W' : S.Opens} (f : W' ⟶ W) :
    PreservesFiniteColimits (SheafOfModules.overMap.{u}
      (Stacks.SheafOfModules.Tensor.ringSheaf S.zariskiRingedSite.O) f) :=
  Stacks.SheafOfModules.LocalCokernel.overMap_preservesFiniteColimits f

/-- **Flat lowest opcycles make a strictly perfect approximation a local model.** Let `W` be an
open of `S`, `α : R ⟶ K'` a morphism of complexes of `𝒪_W`-modules with `R` strictly perfect,
invertible on cohomology in degrees `≥ a`, with `K'` acyclic below `a`, and suppose the opcycles
`Coker(R^{a-1} ⟶ R^a)` are flat. Then every point of `W` has an open neighbourhood `W'' ≤ W`
over which `K'` receives a quasi-isomorphism from a strictly perfect complex.

Stacks 08FD makes the opcycles, which are of finite presentation (Stacks 0H98), a direct summand
of a finite free module locally; there `τ_{≥ a}R` is strictly perfect and represents `K'`, and
Stacks 08FR turns that derived isomorphism into a quasi-isomorphism of complexes locally. This
is the end of the proof of Stacks 08G7, with the flatness obtained otherwise. -/
theorem exists_strictlyPerfect_model_of_isFlat_opcycles (W : S.Opens)
    {R K' : CochainComplex (SheafOfModules.{u}
      ((Stacks.SheafOfModules.Tensor.ringSheaf S.zariskiRingedSite.O).over W)) ℤ}
    (hR : IsStrictlyPerfect _ R) (α : R ⟶ K') (a : ℤ)
    (hα : ∀ i, a ≤ i → IsIso (HomologicalComplex.homologyMap α i))
    (hK' : ∀ i, i < a → IsZero (K'.homology i))
    (hflat : AlgebraicGeometry.SheafOfModules.IsFlat.{u, u, u, u}
      (O := (S.zariskiRingedSite.over W).O) (R.opcycles a))
    (x : ↥S) (hx : x ∈ W) :
    ∃ (W'' : S.Opens) (f : W'' ⟶ W), x ∈ W'' ∧
      ∃ P : CochainComplex (SheafOfModules.{u}
          ((Stacks.SheafOfModules.Tensor.ringSheaf S.zariskiRingedSite.O).over W'')) ℤ,
        IsStrictlyPerfect _ P ∧
        ∃ q : P ⟶ ((SheafOfModules.overMap.{u}
            (Stacks.SheafOfModules.Tensor.ringSheaf S.zariskiRingedSite.O) f).mapHomologicalComplex
            (ComplexShape.up ℤ)).obj K', QuasiIso q := by
  let X := S.zariskiRingedSite
  let R₀ := Stacks.SheafOfModules.Tensor.ringSheaf X.O
  open Stacks.SheafOfModules.DerivedTensorProduct in
  obtain ⟨S₁, hS₁, h₁⟩ :=
    exists_coveringSieve_isDirectSummandOfFiniteFree_overMap_of_isFinitePresentation
      (J := X.J) W X.O (R.opcycles a)
      (Stacks.SheafOfModules.isFinitePresentation_opcycles_general (X.over W) hR a) hflat
      (Over.mk (𝟙 W))
  obtain ⟨W', f, hf, hxW'⟩ := ((Opens.mem_grothendieckTopology _).1
    ((X.J.mem_over_iff S₁).1 hS₁)) x hx
  rw [Sieve.overEquiv_iff] at hf
  have hsum := h₁ _ hf
  simp only [Over.mk_left, Over.mk_hom, Category.comp_id] at hsum
  let F := SheafOfModules.overMap.{u} R₀ f
  let FC := F.mapHomologicalComplex (ComplexShape.up ℤ)
  have : F.Additive := ⟨by intros; ext; rfl⟩
  have : F.PreservesHomology := Functor.preservesHomologyOfExact _
  let Y : CochainComplex (SheafOfModules.{u} (R₀.over W')) ℤ := FC.obj R
  have hRf : IsStrictlyPerfect (R₀.over W') Y :=
    Stacks.SheafOfModules.isStrictlyPerfect_restrictComplexAlong_general R₀ f hR
  have hP₁ : IsStrictlyPerfect (R₀.over W') (Y.truncGE a) :=
    SheafOfModules.isStrictlyPerfect_truncGE_general hRf a
      (IsDirectSummandOfFiniteFree.of_iso _ (ShortComplex.mapOpcyclesIso (R.sc a) F) hsum)
  let : HasDerivedCategory (SheafOfModules.{u} (R₀.over W')) := HasDerivedCategory.standard _
  have : (DerivedCategory.Q.obj (FC.obj K')).IsGE a := (DerivedCategory.isGE_iff _ _).2
    fun i hi => (F.map_isZero (hK' i hi)).of_iso
      ((DerivedCategory.homologyFunctorFactors _ i).app (FC.obj K') ≪≫
        ShortComplex.mapHomologyIso (K'.sc i) F)
  obtain ⟨e⟩ := CochainComplex.exists_iso_Q_truncGE_of_isIso_homologyMap a (FC.map α)
    fun i hi => AlgebraicGeometry.RingedSite.isIso_homologyMap_map F α i (hα i hi)
  obtain ⟨S₂, hS₂, h₂⟩ :=
    AlgebraicGeometry.RingedSite.exists_coveringSieve_quasiIso_of_derivedIso_general X W' hP₁ e
  obtain ⟨W'', g, hg, hxW''⟩ := ((Opens.mem_grothendieckTopology _).1 hS₂) x hxW'
  obtain ⟨β, hβ⟩ := h₂ g hg
  refine ⟨W'', g ≫ f, hxW'', _,
    Stacks.SheafOfModules.isStrictlyPerfect_restrictComplexAlong_general R₀ g hP₁,
    β ≫ ((Functor.mapHomologicalComplexCompIso
      (Stacks.SheafOfModules.overMapCompIso R₀ f g) (ComplexShape.up ℤ)).app K').hom, ?_⟩
  have := hβ
  infer_instance

end Zariski

/-! ### The converse -/

section Converse

variable [HasDerivedCategory.{d} (SheafOfModules.{u} S.ringCatSheaf)]
  [HasDerivedCategory.{d'} (SheafOfModules.{u} (structureSheaf B S hS))]

/-- **A strictly perfect local model at every point.** If `ε^*E` is perfect and `K` represents
`E`, every point of an open `U` of `S` has an open neighbourhood `W ≤ U` over which `K` receives
a quasi-isomorphism from a strictly perfect complex. -/
theorem exists_local_model_of_isPerfect_associatedModule
    (E : DerivedCategory (SheafOfModules.{u} S.ringCatSheaf))
    (hE : (smallEtaleRingedSite B S hS).IsPerfect
      ((associatedModuleOfSheaf B S hS).mapDerivedCategory.obj E))
    (K : CochainComplex (SheafOfModules.{u} S.ringCatSheaf) ℤ)
    (eK : DerivedCategory.Q.obj K ≅ E) (U : S.Opens) (x : ↥S) (hx : x ∈ U) :
    ∃ W : S.Opens, W ≤ U ∧ x ∈ W ∧
      ∃ P : CochainComplex (SheafOfModules.{u}
          ((Stacks.SheafOfModules.Tensor.ringSheaf S.zariskiRingedSite.O).over W)) ℤ,
        IsStrictlyPerfect _ P ∧
        ∃ q : P ⟶ S.zariskiRingedSite.restrictComplex K W, QuasiIso q := by
  let Zs := S.zariskiRingedSite
  let R₀ := Stacks.SheafOfModules.Tensor.ringSheaf Zs.O
  let : HasDerivedCategory.{d} (SheafOfModules.{u} R₀) :=
    ‹HasDerivedCategory.{d} (SheafOfModules.{u} S.ringCatSheaf)›
  obtain ⟨E', hE', ⟨eE'⟩⟩ := hE
  obtain ⟨T, a, P₀, hTU, hxT, hP₀, hP₀a, ⟨α₀, hα₀⟩, hvan⟩ :=
    exists_etale_model_of_isPerfectComplex B S hS E E' hE' eE' U x hx
  -- An `(a - 1)`-pseudo-coherent representative of `E`, Stacks 08HE (2) ⇒ (1).
  obtain ⟨K', hK', ⟨eK'⟩⟩ := associatedModuleToPseudoCoherent B S hS E (a - 1)
    (AlgebraicGeometry.RingedSite.isPseudoCoherentFrom_of_isPerfect_general
      (smallEtaleRingedSite B S hS) ⟨E', hE', ⟨eE'⟩⟩ (a - 1))
  obtain ⟨Sp, hSp, hmod⟩ := hK' (imageOpen B S hS T)
  obtain ⟨V, f, ⟨W₁, h, g, hg, rfl⟩, hxV⟩ := (Opens.mem_grothendieckTopology _).1 hSp x hxT
  obtain ⟨R, hR, α, hα, -⟩ := hmod g hg
  have hW₁ : W₁ ≤ imageOpen B S hS T := leOfHom g
  -- The cohomology of `K'` vanishes below `a` over `W₁`.
  have hK'van : ∀ i, i < a → IsZero ((K'.homology i).over W₁) := by
    intro i hi
    let e₀ : K'.homology i ≅ (DerivedCategory.homologyFunctor (SheafOfModules.{u} R₀) i).obj E :=
      ((DerivedCategory.homologyFunctorFactors (SheafOfModules.{u} R₀) i).app K').symm ≪≫
        (DerivedCategory.homologyFunctor (SheafOfModules.{u} R₀) i).mapIso eK'
    exact (Stacks.SheafOfModules.isZero_over_of_hom _ g (hvan i hi)).of_iso
      ((SheafOfModules.overFunctor.{u} R₀ W₁).mapIso e₀)
  have hα' : ∀ i, a ≤ i → IsIso (HomologicalComplex.homologyMap α i) :=
    fun i hi => hα i (by omega)
  have hflat := isFlat_opcycles_of_etale_model B S hS E E' eE' T a P₀ hP₀ hP₀a α₀ hα₀ K' eK'
    W₁ hW₁ R hR α hα' hK'van
  obtain ⟨W₂, f₂, hxW₂, P₂, hP₂, q₂, hq₂⟩ := exists_strictlyPerfect_model_of_isFlat_opcycles S W₁
    hR α a hα' (fun i hi => (hK'van i hi).of_iso (restrictComplexHomologyIso S W₁ K' i)) hflat
    x (leOfHom h hxV)
  -- Pass from the representative `K'` to `K`.
  let : HasDerivedCategory (SheafOfModules.{u} (R₀.over W₂)) := HasDerivedCategory.standard _
  let o₂ := SheafOfModules.overFunctor.{u} R₀ W₂
  let c₂ := (Stacks.SheafOfModules.overFunctorMapComplexIso R₀ f₂).app K'
  have := hq₂
  have : IsIso (DerivedCategory.Q.map (q₂ ≫ c₂.hom)) :=
    (DerivedCategory.isIso_Q_map_iff_quasiIso _ _).2 inferInstance
  let e : DerivedCategory.Q.obj P₂ ≅ DerivedCategory.Q.obj (Zs.restrictComplex K W₂) :=
    asIso (DerivedCategory.Q.map (q₂ ≫ c₂.hom)) ≪≫
      (o₂.mapDerivedCategoryFactors.app K').symm ≪≫
      o₂.mapDerivedCategory.mapIso (eK' ≪≫ eK.symm) ≪≫ o₂.mapDerivedCategoryFactors.app K
  obtain ⟨S₃, hS₃, h₃⟩ :=
    AlgebraicGeometry.RingedSite.exists_coveringSieve_quasiIso_of_derivedIso_general Zs W₂ hP₂ e
  obtain ⟨W, f₃, hf₃, hxW⟩ := (Opens.mem_grothendieckTopology _).1 hS₃ x hxW₂
  obtain ⟨β, hβ⟩ := h₃ f₃ hf₃
  refine ⟨W, (leOfHom f₃).trans ((leOfHom f₂).trans (hW₁.trans hTU)), hxW, _,
    Stacks.SheafOfModules.isStrictlyPerfect_restrictComplexAlong_general R₀ f₃ hP₂,
    β ≫ ((Stacks.SheafOfModules.overFunctorMapComplexIso R₀ f₃).app K).hom, ?_⟩
  have := hβ
  infer_instance

end Converse

section Statement

variable [HasDerivedCategory.{d}
    (SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf S.zariskiRingedSite.O))]
  [HasDerivedCategory.{d'} (SheafOfModules.{u} (structureSheaf B S hS))]

/-- **The converse direction of Stacks 08HG**: if `ε^*E` is a perfect object of `D(𝒪_étale)`
then `E` is a perfect object of `D(𝒪_S)`.

Every point of every open of `S` has a neighbourhood carrying a strictly perfect model of a fixed
representative of `E` (`exists_local_model_of_isPerfect_associatedModule`), which is the
definition of perfectness, Stacks 08G5. -/
theorem isPerfectZariski_of_isPerfectSmallEtale
    (E : DerivedCategory (SheafOfModules.{u}
      (Stacks.SheafOfModules.Tensor.ringSheaf S.zariskiRingedSite.O)))
    (hE : IsPerfectSmallEtale B S hS E) : IsPerfectZariski S E := by
  let : HasDerivedCategory.{d} (SheafOfModules.{u} S.ringCatSheaf) :=
    ‹HasDerivedCategory.{d} (SheafOfModules.{u}
      (Stacks.SheafOfModules.Tensor.ringSheaf S.zariskiRingedSite.O))›
  obtain ⟨K, eK⟩ : Σ' K : CochainComplex (SheafOfModules.{u}
      (Stacks.SheafOfModules.Tensor.ringSheaf S.zariskiRingedSite.O)) ℤ,
      DerivedCategory.Q.obj K ≅ E :=
    ⟨DerivedCategory.Q.objPreimage E, DerivedCategory.Q.objObjPreimageIso E⟩
  refine ⟨K, fun U => ⟨fun W _ => ∃ P : CochainComplex (SheafOfModules.{u}
      ((Stacks.SheafOfModules.Tensor.ringSheaf S.zariskiRingedSite.O).over W)) ℤ,
        IsStrictlyPerfect _ P ∧
        ∃ q : P ⟶ S.zariskiRingedSite.restrictComplex K W, QuasiIso q, ?_,
      fun W _ hW => hW⟩, ⟨eK⟩⟩
  refine (Opens.mem_grothendieckTopology _).2 fun x hx => ?_
  obtain ⟨W, hWU, hxW, hmodel⟩ :=
    exists_local_model_of_isPerfect_associatedModule B S hS E hE K eK U x hx
  exact ⟨W, homOfLE hWU, ⟨W, 𝟙 W, homOfLE hWU, hmodel, Category.id_comp _⟩, hxW⟩

/-- **Stacks 08HG.** Let `S` be a scheme and `E` an object of `D(𝒪_S)`. Then `E` is a perfect
object of `D(𝒪_S)` if and only if `ε^*E` is a perfect object of `D(𝒪_étale)`, where
`ε : (S_étale, 𝒪) ⟶ (S_Zar, 𝒪_S)` is the morphism of ringed sites of Stacks 08H7 and `ε^*` its
pullback on the derived category — the termwise associated-module functor, `ε` being flat
(Stacks 08H8).

Perfectness on either side is Stacks 08G5. The direction `E` perfect ⟹ `ε^*E` perfect is
`AlgebraicGeometry.SmallEtale.perfectToAssociatedModule_of_slice_exact`; the converse is
`AlgebraicGeometry.SmallEtale.isPerfectZariski_of_isPerfectSmallEtale`. -/
@[stacks 08HG]
theorem isPerfectZariski_iff_isPerfectSmallEtale
    (E : DerivedCategory (SheafOfModules.{u}
      (Stacks.SheafOfModules.Tensor.ringSheaf S.zariskiRingedSite.O))) :
    IsPerfectZariski S E ↔ IsPerfectSmallEtale B S hS E :=
  ⟨perfectToAssociatedModule_of_slice_exact B S hS E,
    isPerfectZariski_of_isPerfectSmallEtale B S hS E⟩

end Statement

end AlgebraicGeometry.SmallEtale

end
