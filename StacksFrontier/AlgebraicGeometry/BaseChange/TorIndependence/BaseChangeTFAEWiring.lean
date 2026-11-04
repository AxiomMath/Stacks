module

public import StacksFrontier.AlgebraicGeometry.BaseChange.TorIndependence.AffineChartGermCriterion
public import StacksFrontier.AlgebraicGeometry.BaseChange.TorIndependence.BaseChangeTFAE
public import StacksFrontier.AlgebraicGeometry.BaseChange.TorIndependence.PointwiseStalkTransport

/-!
# Stacks 0DJ8, reduced to one statement about one chart at one point

`AlgebraicGeometry.baseChange_tfae_of_chartCriterion` proves the three-way equivalence of Stacks
0DJ8 from the per-chart criterion, and
`AlgebraicGeometry.BaseChangeChart.isIso_comparison_iff_forall_germ` reads condition (2) at a chart
as the invertibility, in every degree and at every point `y` of `Spec 𝒪_{X'}(U')`, of the chart's
ring-level map of Stacks 0DJ7 base changed along the germ map at `y`. Composing the two leaves a
single statement to prove: that at one chart, one point and one degree, *that* base-changed
ring-level map is invertible exactly when the pointwise map of Stacks 0DJ7 at the corresponding
point of `X'` is.

This module performs that composition, and then cuts the remaining statement down to its source
half. The source half is the hypothesis `hsource` of
`AlgebraicGeometry.baseChange_tfae_of_sourceBridge`, and the equivalence is conditional on it.

The cut is this. The two maps of the remaining statement have the *same target*, by
`AlgebraicGeometry.bijective_homologyDerivedStalkAffineSectionsRestrictIso`; invertibility of a
map of modules transports along bijections of its source and its target, by
`ModuleCat.isIso_iff_isIso_of_bijective_comm`, over rings which need not agree. So a bijection of
the two sources commuting with the two maps is enough, and that bijection is the only thing left:
it is the statement that the comparison of Stacks 065Z is natural along the cube of localizations
relating the chart's four coordinate rings to the four local rings at a point of `U'`.

## Main results

* `AlgebraicGeometry.baseChange_tfae_of_bridge`: the three conditions of Stacks 0DJ8 are
  equivalent, granted the one-point bridge.
* `AlgebraicGeometry.baseChange_tfae_of_sourceBridge`: the same, granted only a bijection of the
  two maps' sources commuting with them.

## Implementation notes

The bridge is stated with the point bound as `PrimeSpectrum ↑ch.A'`, matching
`isIso_comparison_iff_forall_germ`, while `baseChangeCohomologyMap` is read at `ch.incU' y`; the
carrier of `Spec ch.A'` is `PrimeSpectrum ↑ch.A'`, so the open immersion applies to such a point
unchanged.

The two criteria quantify in opposite orders — degree before point in the chart reading, point
before degree in the criterion that Stacks 0DJ8's three conditions consume — so the composition is
a quantifier exchange away from being immediate.

## References

* [Stacks Project, Tag 0DJ7](https://stacks.math.columbia.edu/tag/0DJ7)
* [Stacks Project, Tag 0DJ8](https://stacks.math.columbia.edu/tag/0DJ8)
-/

-- This file uses the locally small derived-category models below, which are not
-- global instances (see `StacksFrontier.Homology.DerivedCategory.LocallySmall`):
-- `D(R)` for `R`-modules.
-- `D(𝒪_X)` for a scheme.
attribute [local instance] ModuleCat.hasDerivedCategory
attribute [local instance] AlgebraicGeometry.Scheme.Modules.hasDerivedCategory

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits

universe u

namespace AlgebraicGeometry

/-- **Stacks 0DJ8, granted the one-point bridge.** If at every Cartesian affine-open chart, every
point `y` of `Spec 𝒪_{X'}(U')` and every degree, the chart's ring-level map of Stacks 0DJ7 base
changed along the germ map at `y` is invertible exactly when the pointwise map of Stacks 0DJ7 at
`ch.incU' y` is, then the three conditions of Stacks 0DJ8 are equivalent. -/
public theorem baseChange_tfae_of_bridge {X X' S S' : Scheme.{u}}
    (f : X ⟶ S) (g : S' ⟶ S) (f' : X' ⟶ S') (g' : X' ⟶ X) (sq : IsPullback g' f' f g)
    (K : DerivedCategory X.Modules) (K' : DerivedCategory X'.Modules)
    (φ : (Stacks.Duality.derivedPullback g').obj K ⟶ K')
    (hbridge : ∀ ch : BaseChangeChart f g f' g',
      letI := ch.a.hom.toAlgebra
      letI := ch.b.hom.toAlgebra
      letI := ch.c.hom.toAlgebra
      letI := ch.d.hom.toAlgebra
      letI := (ch.c.hom.comp ch.a.hom).toAlgebra
      haveI : IsScalarTower ch.R ch.A ch.A' := IsScalarTower.of_algebraMap_eq fun _ => rfl
      haveI : IsScalarTower ch.R ch.R' ch.A' :=
        IsScalarTower.of_algebraMap_eq fun r => DFunLike.congr_fun ch.isPushout_hom r
      ∀ (n : ℤ) (y : PrimeSpectrum (ch.A' : Type u)),
        IsIso ((ModuleCat.extendScalars.{u, u, u} (specGermRingHom ch.A' y)).map
            (RingTheory.TorIndependence.ringBaseChangeCohomologyMapGeneral
              (R := ch.R) (R' := ch.R')
              ((affineDerivedSections ch.incU).obj K)
              ((affineDerivedSections ch.incU').obj K')
              (ch.sectionsBaseChangeMap K ≫ (affineDerivedSections ch.incU').map φ) n)) ↔
          IsIso (baseChangeCohomologyMap f g f' g' sq.w K K' φ (ch.incU' y) n)) :
    List.TFAE
      [∀ (x' : X') (i : ℤ), IsIso (baseChangeCohomologyMap f g f' g' sq.w K K' φ x' i),
       ∀ ch : BaseChangeChart f g f' g', IsIso (ch.comparison K K' φ),
       ∃ 𝒞 : Set (BaseChangeChart f g f' g'),
         (∀ ch ∈ 𝒞, IsIso (ch.comparison K K' φ)) ∧
           ∀ x' : X', ∃ ch ∈ 𝒞, ∃ y : Spec ch.A', ch.incU' y = x'] := by
  refine baseChange_tfae_of_chartCriterion f g f' g' sq K K' φ fun ch => ?_
  rw [ch.isIso_comparison_iff_forall_germ K K' φ]
  exact ⟨fun h y n => (hbridge ch n y).mp (h n y), fun h n y => (hbridge ch n y).mpr (h y n)⟩

/-- **Stacks 0DJ8, granted only the identification of the two sources.** The bridge of
`AlgebraicGeometry.baseChange_tfae_of_bridge` asks for an equivalence of two invertibility
statements; this asks instead for a bijection `θ` between the two maps' *sources*, commuting
with them through the bijection of their targets. That target bijection is already available —
`AlgebraicGeometry.bijective_homologyDerivedStalkAffineSectionsRestrictIso`, the germ
localization of the cohomology of the derived sections being the cohomology of the derived
stalk — so `θ` is all that the three-way equivalence of Stacks 0DJ8 still needs.

`K'` is asked to have quasi-coherent cohomology sheaves, which is the hypothesis of
`AlgebraicGeometry.derivedStalkAffineSectionsRestrictIso` and so of the target bijection; it is
also what the source asks of `K'`.

The source of the germ-localized chart map is
`𝒪_{X'}(U')_y ⊗_{𝒪_X(U) ⊗_{𝒪_S(V)} 𝒪_{S'}(V')} H^n(RΓ(U,K) ⊗ᴸ_{𝒪_S(V)} 𝒪_{S'}(V'))` and the
source of the pointwise map of Stacks 0DJ7 at `ch.incU' y` is the same expression for the four
local rings of the square at that point; `θ` is a bijection between them. Both types are left
implicit here, as they are determined by the two maps the commutation equation names.

The inverse of the germ comparison at `y` is taken as data — a ring map `ε'` and the two
equations inverting it — exactly as `AlgebraicGeometry.derivedStalkAffineSectionsRestrictIso`
takes it, rather than as `CategoryTheory.inv` of the comparison. The proof instantiates it at
that categorical inverse, which `ch.isOpenImmersion_incU' sq` makes available. -/
public theorem baseChange_tfae_of_sourceBridge {X X' S S' : Scheme.{u}}
    (f : X ⟶ S) (g : S' ⟶ S) (f' : X' ⟶ S') (g' : X' ⟶ X) (sq : IsPullback g' f' f g)
    (K : DerivedCategory X.Modules) (K' : DerivedCategory X'.Modules)
    (hK' : ∀ n : ℤ, ((DerivedCategory.homologyFunctor X'.Modules n).obj K').IsQuasicoherent)
    (φ : (Stacks.Duality.derivedPullback g').obj K ⟶ K')
    (hsource : ∀ ch : BaseChangeChart f g f' g',
      letI := ch.a.hom.toAlgebra
      letI := ch.b.hom.toAlgebra
      letI := ch.c.hom.toAlgebra
      letI := ch.d.hom.toAlgebra
      letI := (ch.c.hom.comp ch.a.hom).toAlgebra
      haveI : IsScalarTower ch.R ch.A ch.A' := IsScalarTower.of_algebraMap_eq fun _ => rfl
      haveI : IsScalarTower ch.R ch.R' ch.A' :=
        IsScalarTower.of_algebraMap_eq fun r => DFunLike.congr_fun ch.isPushout_hom r
      ∀ (n : ℤ) (y : PrimeSpectrum (ch.A' : Type u))
          (ε' : (Spec ch.A').presheaf.stalk y →+* X'.presheaf.stalk (ch.incU' y))
          (h₁ : ∀ x, ε' ((ch.incU'.stalkMap y).hom x) = x)
          (h₂ : ∀ z, (ch.incU'.stalkMap y).hom (ε' z) = z),
        ∃ θ : _ → _, Function.Bijective θ ∧
          ∀ m, (baseChangeCohomologyMap f g f' g' sq.w K K' φ (ch.incU' y) n).hom (θ m) =
            (homologyDerivedStalkAffineSectionsRestrictIso ch.incU' y K' hK'
                ε' h₁ h₂ n).hom.hom
              (((ModuleCat.extendScalars.{u, u, u} (specGermRingHom ch.A' y)).map
                (RingTheory.TorIndependence.ringBaseChangeCohomologyMapGeneral
                  (R := ch.R) (R' := ch.R')
                  ((affineDerivedSections ch.incU).obj K)
                  ((affineDerivedSections ch.incU').obj K')
                  (ch.sectionsBaseChangeMap K ≫
                    (affineDerivedSections ch.incU').map φ) n)).hom m)) :
    List.TFAE
      [∀ (x' : X') (i : ℤ), IsIso (baseChangeCohomologyMap f g f' g' sq.w K K' φ x' i),
       ∀ ch : BaseChangeChart f g f' g', IsIso (ch.comparison K K' φ),
       ∃ 𝒞 : Set (BaseChangeChart f g f' g'),
         (∀ ch ∈ 𝒞, IsIso (ch.comparison K K' φ)) ∧
           ∀ x' : X', ∃ ch ∈ 𝒞, ∃ y : Spec ch.A', ch.incU' y = x'] := by
  refine baseChange_tfae_of_bridge f g f' g' sq K K' φ fun ch => ?_
  intro n y
  have := ch.isOpenImmersion_incU' sq
  have : IsIso (ch.incU'.stalkMap y) := ch.isIso_stalkCompA' y sq
  obtain ⟨θ, hθ, hcomm⟩ := hsource ch n y (inv (ch.incU'.stalkMap y)).hom
    (inv_stalkMap_stalkMap_apply ch.incU' y) (stalkMap_inv_stalkMap_apply ch.incU' y)
  exact ModuleCat.isIso_iff_isIso_of_bijective_comm _ _ hθ
    (bijective_homologyDerivedStalkAffineSectionsRestrictIso ch.incU' y K' hK'
      (inv (ch.incU'.stalkMap y)).hom (inv_stalkMap_stalkMap_apply ch.incU' y)
      (stalkMap_inv_stalkMap_apply ch.incU' y) n) hcomm

end AlgebraicGeometry

end
