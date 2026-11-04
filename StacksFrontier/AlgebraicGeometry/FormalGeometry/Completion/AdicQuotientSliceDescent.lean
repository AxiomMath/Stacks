module

public import StacksFrontier.AlgebraicGeometry.FormalGeometry.Completion.AdicQuotientCanonicalComparison
public import StacksFrontier.AlgebraicGeometry.FormalGeometry.Completion.IdealSheafSiteFiniteType
public import StacksFrontier.AlgebraicGeometry.FormalGeometry.DerivedCompletionRinged.LocalizationCompletionFiniteType
public import StacksFrontier.AlgebraicGeometry.FormalGeometry.DerivedCompletionRinged.SliceRestrictionDescent
public import StacksFrontier.AlgebraicGeometry.Perfect.Coherator.InverseLimitQuasiCoherent
public import StacksFrontier.CategoryTheory.Sites.Cohomology.Slice.DerivedIsomorphismLocality
public import StacksFrontier.Homology.DerivedCategory.InverseSystem.DerivedLimitWithProjectionsFunctor
import StacksCore.Tactic.StacksAttribute

/-!
# Descent of the canonical comparison `ℱ^∧ ⟶ (lim ℱ/𝓘ⁿℱ)[0]` along the affine slices

Let `X` be a locally Noetherian scheme, `𝓘 ⊂ 𝒪_X` a quasi-coherent sheaf of ideals and `ℱ` a
coherent `𝒪_X`-module, and let

`c : ℱ^∧ ⟶ (lim ℱ/𝓘ⁿℱ)[0]`

be the canonical comparison `Stacks.Algebraization.comparisonDerivedCompletionLimitAdicQuotient`,
which reduces part (3) of [Stacks, Tag 0A0K] to the statement that the canonical maps
`ℱ^∧ ⟶ (ℱ/𝓘ⁿℱ)[0]` are the projections of a derived-limit presentation of `ℱ^∧`. That statement
is **not** available on `X` itself: the Koszul presentation of `ℱ^∧` rests on the pro-vanishing
of the Koszul cohomology sheaves below the top degree, which is genuinely false on a scheme that
is not quasi-compact — at `r = 1`, `f = x`, `ℱ = 𝒪` on `⊔ᵢ Spec k[x]/(xⁱ)` the Artin–Rees level
needed to kill `H⁰` on the `i`-th chart is `n + i`, so no single level works for all charts.
The presentation exists only on the affine slices, where no compactness is bought —
`Stacks.KoszulProZero.exists_koszulDualSystemOn_over_homologyMap_eq_zero_of_section` — and the
invertibility of `c` has therefore to be **descended** from the slices to `X`.

This file performs that descent. Its hypothesis is a derived-limit presentation of `(ℱ|_V)^∧`
over the *restriction* of the adic quotient tower, with the restrictions of the canonical maps
`ℱ^∧ ⟶ (ℱ/𝓘ⁿℱ)[0]` as projections, for `V` ranging over the affine opens; its conclusion is
`IsIso c`, hence part (3) at the tag's own hypotheses.

## Main results

* `Stacks.Algebraization.restrictComparisonLimitAdicQuotient` and
  `Stacks.Algebraization.restrictCompletionToAdicQuotient` — **the slice's own canonical
  comparison `(ℱ|_V)^∧ ⟶ (lim ℱ/𝓘ⁿℱ)[0]|_V` and its own canonical maps onto the terms of the
  restricted tower**, both built from the restriction of `c`, resp. of the canonical maps, by the
  comparison of [Stacks, Tag 0A0F].
* `Stacks.Algebraization.derivedCompletionUnit_comp_restrictComparisonLimitAdicQuotient`,
  `derivedCompletionUnit_comp_restrictCompletionToAdicQuotient` and
  `Stacks.Algebraization.eq_restrictComparisonLimitAdicQuotient` — **those really are the slice's
  own canonical maps**: each restricts along the completion unit of the slice to the restriction of
  the limit lift, resp. of the quotient projection, and the comparison is the **only** map out of
  `(ℱ|_V)^∧` doing so, the restricted limit being derived complete along `𝓘|_V`.
* `Stacks.Algebraization.exists_isDerivedLimitWithProjections_restrict_single_limit` — **the
  restriction of the limit side is a derived limit of the restricted tower through the
  restrictions of the limit projections**; this is part (4) carried to the slice.
* `Stacks.Algebraization.isIso_restrictComparisonLimitAdicQuotient` — the per-slice invertibility.
* `Stacks.Algebraization.isIso_comparison_of_isIso_map_affineOpens` — invertibility of `c` is
  local on the affine opens.
* `Stacks.Algebraization.isIso_comparison_of_affineOpens` — **the descent**, and with it part (3)
  of [Stacks, Tag 0A0K] read through its canonical comparison map.

## The hypothesis on the slices

The invertibility of `c` is thereby a statement about the affine slices, and nothing global is
left in it. No passage between the slice of the opens site over an open `U` and the open
subscheme `U` is involved; the Koszul chain is available on the slice at ringed-site level with
the pro-vanishing as a hypothesis, which is
`AlgebraicGeometry.RingedSite.isDerivedLimitWithProjections_koszulTopSingle_completion`.

The tower appearing in the hypothesis is the restriction
`Stacks.Algebraization.adicQuotientSystem I ℱ ⋙ (-)|_V` of the scheme's tower, while the Koszul
chain on the slice presents `(ℱ|_V)^∧` over the slice's own towers — the Koszul top-cohomology
tower `n ↦ (ℱ|_V)/(f_1^{n+1}, …, f_r^{n+1})(ℱ|_V)`, and, after the pigeonhole comparison, the
slice's adic quotient tower `n ↦ (ℱ|_V)/(𝓘|_V)ⁿ(ℱ|_V)`. Matching the two takes two
identifications, both about towers rather than about maps into them: the site-level pigeonhole
comparison at an arbitrary coefficient, whose target is `Stacks.Sites.idealSmulQuotient`, and the
identification of the restricted tower with the slice's own, which compares
`Stacks.AlgebraicGeometry.IdealPower.idealPowerMultiple I n ℱ` with
`Stacks.Sites.idealPowSmul (idealSheafSiteSubmodule I) n ⊤` and then restricts by
`AlgebraicGeometry.RingedSite.overIdeal_idealPow`.

## Implementation notes

The descent runs on three inputs.

* **The source.** `AlgebraicGeometry.RingedSite.derivedCompletionRestrictIso` is [Stacks, Tag
  0A0F], `(K|_V)^∧ ≅ K^∧|_V`, and
  `derivedCompletionUnit_app_comp_derivedCompletionRestrictIso_hom_app` says it carries the
  completion unit of `K|_V` to the restriction of the completion unit of `K`. That one equation
  is the whole proof of the first main result below.
* **The target.** Restriction to a slice preserves the countable products of the derived
  categories, because extension by zero is left adjoint to it already there ([Stacks, Tag 08FJ])
  and a right adjoint preserves every limit; that is
  `AlgebraicGeometry.RingedSite.preservesProductsOfShape_nat_overFunctor_mapDerivedCategory`. No
  exactness of countable products of sheaves of modules is used, and none is available —
  Grothendieck's AB4* fails there.
* **The transport.** `NoetherianAdicCompletion.IsDerivedLimitWithProjections.map` carries a
  derived-limit presentation along a triangulated functor preserving that product, *with the
  images of the projections as projections*. The bare predicate
  `CategoryTheory.Pretriangulated.IsDerivedLimit` would not do: it pins no cone, and the whole
  point here is that the projections downstairs are the restrictions of the canonical maps.

The per-slice invertibility is then the same two-sided-inverse argument as
`Stacks.Algebraization.isIso_comparison_of_isDerivedLimitWithProjections`, run on the slice:
`Stacks.Algebraization.hom_ext_of_comp_proj` pins a map into a derived limit of a tower of
modules in degree zero by its composites with the projections, and
`AlgebraicGeometry.RingedSite.hom_ext_derivedCompletionUnit` pins a map out of a derived
completion by its restriction along the unit. The degree bounds `hom_ext_of_comp_proj` consumes
hold on the slice because restriction is exact and therefore commutes with the single functor,
`CategoryTheory.Functor.mapDerivedCategorySingleFunctor`.

Two spellings of the category of `𝒪_X`-modules meet here, exactly as for `c` itself:
`AlgebraicGeometry.Scheme.Modules` is a `def` for `SheafOfModules X.ringCatSheaf`, while the
reflector of [Stacks, Tag 099F] and the restriction functor are stated for
`SheafOfModules ((Stacks.SheafOfModules.Tensor.ringSheaf (opensRingedSite X.sheaf).O))`. Every
statement below is at the second spelling, which is the one `c` lives at, and the crossings are
confined to `show … from` at the statement boundary and to the `:=` that transports part (4).

`Stacks.Cohomology.SiteModules.site_hasSheafify_addCommGrp` and
`site_wEqualsLocallyBijective_addCommGrp` are installed as local instances; they are theorems
about an arbitrary site, and they are what makes the slice binders of
`Stacks.SheafOfModules.isIso_of_coversTop_mapDerivedCategory` resolve on the opens site of a
scheme.

## References

* [Stacks Project, Tag 0A0K](https://stacks.math.columbia.edu/tag/0A0K)
* [Stacks Project, Tag 0A0F](https://stacks.math.columbia.edu/tag/0A0F)
* [Stacks Project, Tag 08FJ](https://stacks.math.columbia.edu/tag/08FJ)
* [Stacks Project, Tag 08JJ](https://stacks.math.columbia.edu/tag/08JJ)
-/

@[expose] public noncomputable section

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits CategoryTheory.Pretriangulated
open Opposite TopologicalSpace
open scoped AlgebraicGeometry

open AlgebraicGeometry.RingedSite (derivedCompletion derivedCompletionUnit overIdeal
  derivedCompletionRestrictIso
  derivedCompletionUnit_app_comp_derivedCompletionRestrictIso_hom_app)
open Stacks.SheafOfModules (opensRingedSite)

universe u

attribute [local instance] AlgebraicGeometry.Scheme.Modules.submoduleCompleteLattice

namespace Stacks.Algebraization

attribute [local instance] monoSubmoduleι
attribute [local instance] modulesEnoughInjectives
attribute [local instance 100000] HasDerivedCategory.standard
attribute [local instance] AlgebraicGeometry.RingedSite.hasSheafCompose_forget₂_ringCat
attribute [local instance] Stacks.Cohomology.SiteModules.site_hasSheafify_addCommGrp
attribute [local instance] Stacks.Cohomology.SiteModules.site_wEqualsLocallyBijective_addCommGrp

variable {X : Scheme.{u}} [IsLocallyNoetherian X] (I : X.IdealSheafData) (ℱ : X.Modules)
  [ℱ.IsCoherent] (V : X.Opens)

/-- **[Stacks, Tag 099F] for `𝓘|_V` on the slice over an open of a locally Noetherian scheme.**
`AlgebraicGeometry.RingedSite.isRightAdjoint_ι_isDerivedComplete_overIdeal` is an instance and
applies on the nose, but instance search does not find it at the restriction of
`Stacks.Algebraization.idealSheafSiteSubmodule`; this is that application, installed so that the
derived completion of the slice may be written in the statements below. -/
local instance isRightAdjoint_ι_isDerivedComplete_overIdeal_idealSheafSiteSubmodule :
    (ObjectProperty.ι (AlgebraicGeometry.RingedSite.IsDerivedComplete.{u, u, u, u}
      ((opensRingedSite X.sheaf).over V)
      (overIdeal (idealSheafSiteSubmodule I) V))).IsRightAdjoint :=
  AlgebraicGeometry.RingedSite.isRightAdjoint_ι_isDerivedComplete_overIdeal
    (opensRingedSite X.sheaf) (idealSheafSiteSubmodule I) V

/-! ### Restriction to a slice and the single functor -/

/-- Restriction to a slice commutes with placing a sheaf of modules in degree zero
(`CategoryTheory.Functor.mapDerivedCategorySingleFunctor`). -/
private noncomputable def restrictSingleIso (M : SheafOfModules.{u}
    ((Stacks.SheafOfModules.Tensor.ringSheaf (opensRingedSite X.sheaf).O))) :
    (DerivedCategory.singleFunctor (SheafOfModules.{u}
        (((Stacks.SheafOfModules.Tensor.ringSheaf (opensRingedSite X.sheaf).O)).over V)) 0).obj
      ((SheafOfModules.overFunctor.{u} ((Stacks.SheafOfModules.Tensor.ringSheaf
        (opensRingedSite X.sheaf).O)) V).obj M) ≅
    (SheafOfModules.overFunctor.{u} ((Stacks.SheafOfModules.Tensor.ringSheaf
      (opensRingedSite X.sheaf).O)) V).mapDerivedCategory.obj
      ((DerivedCategory.singleFunctor (SheafOfModules.{u} ((Stacks.SheafOfModules.Tensor.ringSheaf
        (opensRingedSite X.sheaf).O))) 0).obj M) :=
  (((SheafOfModules.overFunctor.{u} ((Stacks.SheafOfModules.Tensor.ringSheaf
    (opensRingedSite X.sheaf).O)) V).mapDerivedCategorySingleFunctor 0).app M).symm

omit [IsLocallyNoetherian X] in
/-- A sheaf of modules placed in degree zero and then restricted to a slice is concentrated in
degrees `≤ 0`: restriction is exact, so it commutes with the single functor. -/
theorem isLE_restrict_single (M : SheafOfModules.{u} ((Stacks.SheafOfModules.Tensor.ringSheaf
    (opensRingedSite X.sheaf).O))) :
    ((SheafOfModules.overFunctor.{u} ((Stacks.SheafOfModules.Tensor.ringSheaf
      (opensRingedSite X.sheaf).O)) V).mapDerivedCategory.obj
      ((DerivedCategory.singleFunctor (SheafOfModules.{u} ((Stacks.SheafOfModules.Tensor.ringSheaf
        (opensRingedSite X.sheaf).O)))
        0).obj M)).IsLE 0 :=
  DerivedCategory.TStructure.t.isLE_of_iso (restrictSingleIso V M) 0

omit [IsLocallyNoetherian X] in
/-- A sheaf of modules placed in degree zero and then restricted to a slice is concentrated in
degrees `≥ 0`. -/
theorem isGE_restrict_single (M : SheafOfModules.{u} ((Stacks.SheafOfModules.Tensor.ringSheaf
    (opensRingedSite X.sheaf).O))) :
    ((SheafOfModules.overFunctor.{u} ((Stacks.SheafOfModules.Tensor.ringSheaf
      (opensRingedSite X.sheaf).O)) V).mapDerivedCategory.obj
      ((DerivedCategory.singleFunctor (SheafOfModules.{u} ((Stacks.SheafOfModules.Tensor.ringSheaf
        (opensRingedSite X.sheaf).O)))
        0).obj M)).IsGE 0 :=
  DerivedCategory.TStructure.t.isGE_of_iso (restrictSingleIso V M) 0

/-! ### The slice's own canonical maps out of `(ℱ|_V)^∧` -/

/-- The completion unit of `K|_V` composed with the comparison of [Stacks, Tag 0A0F] and the
restriction of `g` is the restriction of the unit of `K` composed with `g`. -/
private theorem unit_comp_restrict_iso_comp_map
    {K Y : DerivedCategory (SheafOfModules.{u} ((Stacks.SheafOfModules.Tensor.ringSheaf
      (opensRingedSite X.sheaf).O)))}
    {g : (derivedCompletion (opensRingedSite X.sheaf) (idealSheafSiteSubmodule I)).obj K ⟶ Y}
    {h : K ⟶ Y} (hg : (derivedCompletionUnit (opensRingedSite X.sheaf)
      (idealSheafSiteSubmodule I)).app K ≫ g = h) :
    (derivedCompletionUnit ((opensRingedSite X.sheaf).over V)
          (overIdeal (idealSheafSiteSubmodule I) V)).app _ ≫
        ((derivedCompletionRestrictIso (opensRingedSite X.sheaf)
          (idealSheafSiteSubmodule I) V).hom.app K ≫
          (SheafOfModules.overFunctor.{u} ((Stacks.SheafOfModules.Tensor.ringSheaf
            (opensRingedSite X.sheaf).O)) V).mapDerivedCategory.map g) =
      (SheafOfModules.overFunctor.{u} ((Stacks.SheafOfModules.Tensor.ringSheaf
        (opensRingedSite X.sheaf).O)) V).mapDerivedCategory.map h := by
  refine (Category.assoc _ _ _).symm.trans ?_
  rw [derivedCompletionUnit_app_comp_derivedCompletionRestrictIso_hom_app]
  exact ((SheafOfModules.overFunctor.{u} ((Stacks.SheafOfModules.Tensor.ringSheaf
    (opensRingedSite X.sheaf).O)) V).mapDerivedCategory.map_comp _ _).symm.trans
    (congrArg _ hg)

/-- **The slice's canonical map `(ℱ|_V)^∧ ⟶ (ℱ/𝓘ⁿℱ)[0]|_V`**: the comparison
`(ℱ|_V)^∧ ≅ ℱ^∧|_V` of [Stacks, Tag 0A0F] followed by the restriction of
`Stacks.Algebraization.completionToAdicQuotient`.

It deserves the name: `Stacks.Algebraization`
`.derivedCompletionUnit_comp_restrictCompletionToAdicQuotient` identifies it as the unique map
restricting along the completion unit of the slice to the restriction of the quotient projection
`ℱ ⟶ ℱ/𝓘ⁿℱ`, the terms of the restricted tower being derived complete along `𝓘|_V`. -/
def restrictCompletionToAdicQuotient (n : ℕ) :
    (derivedCompletion ((opensRingedSite X.sheaf).over V)
        (overIdeal (idealSheafSiteSubmodule I) V)).obj
        ((SheafOfModules.overFunctor.{u} ((Stacks.SheafOfModules.Tensor.ringSheaf
          (opensRingedSite X.sheaf).O))
          V).mapDerivedCategory.obj
          ((DerivedCategory.singleFunctor (SheafOfModules.{u}
            ((Stacks.SheafOfModules.Tensor.ringSheaf (opensRingedSite X.sheaf).O)))
            0).obj
            (ℱ : SheafOfModules.{u} ((Stacks.SheafOfModules.Tensor.ringSheaf
              (opensRingedSite X.sheaf).O))))) ⟶
      (SheafOfModules.overFunctor.{u} ((Stacks.SheafOfModules.Tensor.ringSheaf
        (opensRingedSite X.sheaf).O))
        V).mapDerivedCategory.obj
        ((DerivedCategory.singleFunctor (SheafOfModules.{u} ((Stacks.SheafOfModules.Tensor.ringSheaf
          (opensRingedSite X.sheaf).O)))
          0).obj
          ((adicQuotientSystem I ℱ).obj ⟨n⟩ : SheafOfModules.{u}
            ((Stacks.SheafOfModules.Tensor.ringSheaf (opensRingedSite X.sheaf).O)))) :=
  (derivedCompletionRestrictIso (opensRingedSite X.sheaf) (idealSheafSiteSubmodule I) V).hom.app
      ((DerivedCategory.singleFunctor (SheafOfModules.{u} ((Stacks.SheafOfModules.Tensor.ringSheaf
        (opensRingedSite X.sheaf).O)))
        0).obj
        (ℱ : SheafOfModules.{u} ((Stacks.SheafOfModules.Tensor.ringSheaf
          (opensRingedSite X.sheaf).O)))) ≫
    (SheafOfModules.overFunctor.{u} ((Stacks.SheafOfModules.Tensor.ringSheaf
      (opensRingedSite X.sheaf).O)) V).mapDerivedCategory.map
      (completionToAdicQuotient I ℱ n)

/-- **The slice's canonical comparison `(ℱ|_V)^∧ ⟶ (lim ℱ/𝓘ⁿℱ)[0]|_V`**: the comparison
`(ℱ|_V)^∧ ≅ ℱ^∧|_V` of [Stacks, Tag 0A0F] followed by the restriction of the canonical comparison
`c` of `Stacks.Algebraization.comparisonDerivedCompletionLimitAdicQuotient`.

`Stacks.Algebraization.derivedCompletionUnit_comp_restrictComparisonLimitAdicQuotient` and
`Stacks.Algebraization.eq_restrictComparisonLimitAdicQuotient` say that it is the **unique** map
restricting along the completion unit of the slice to the restriction of the limit lift
`ℱ ⟶ lim ℱ/𝓘ⁿℱ`; so the restriction of `c` *is* the slice's own canonical comparison. -/
def restrictComparisonLimitAdicQuotient :
    (derivedCompletion ((opensRingedSite X.sheaf).over V)
        (overIdeal (idealSheafSiteSubmodule I) V)).obj
        ((SheafOfModules.overFunctor.{u} ((Stacks.SheafOfModules.Tensor.ringSheaf
          (opensRingedSite X.sheaf).O))
          V).mapDerivedCategory.obj
          ((DerivedCategory.singleFunctor (SheafOfModules.{u}
            ((Stacks.SheafOfModules.Tensor.ringSheaf (opensRingedSite X.sheaf).O)))
            0).obj
            (ℱ : SheafOfModules.{u} ((Stacks.SheafOfModules.Tensor.ringSheaf
              (opensRingedSite X.sheaf).O))))) ⟶
      (SheafOfModules.overFunctor.{u} ((Stacks.SheafOfModules.Tensor.ringSheaf
        (opensRingedSite X.sheaf).O))
        V).mapDerivedCategory.obj
        ((DerivedCategory.singleFunctor (SheafOfModules.{u} ((Stacks.SheafOfModules.Tensor.ringSheaf
          (opensRingedSite X.sheaf).O)))
          0).obj
          ((limit (adicQuotientSystem I ℱ) : X.Modules) : SheafOfModules.{u}
            ((Stacks.SheafOfModules.Tensor.ringSheaf (opensRingedSite X.sheaf).O)))) :=
  (derivedCompletionRestrictIso (opensRingedSite X.sheaf) (idealSheafSiteSubmodule I) V).hom.app
      ((DerivedCategory.singleFunctor (SheafOfModules.{u} ((Stacks.SheafOfModules.Tensor.ringSheaf
        (opensRingedSite X.sheaf).O)))
        0).obj
        (ℱ : SheafOfModules.{u} ((Stacks.SheafOfModules.Tensor.ringSheaf
          (opensRingedSite X.sheaf).O)))) ≫
    (SheafOfModules.overFunctor.{u} ((Stacks.SheafOfModules.Tensor.ringSheaf
      (opensRingedSite X.sheaf).O)) V).mapDerivedCategory.map
      (comparisonDerivedCompletionLimitAdicQuotient I ℱ)

/-- **The restriction of `c` is the slice's own canonical comparison.** Composing the completion
unit of `ℱ|_V` with `Stacks.Algebraization.restrictComparisonLimitAdicQuotient` gives the
restriction of the limit lift `ℱ ⟶ lim ℱ/𝓘ⁿℱ`.

[Stacks, Tag 0A0F] carries the completion unit of `ℱ|_V` to the restriction of the completion
unit of `ℱ` (`AlgebraicGeometry.RingedSite`
`.derivedCompletionUnit_app_comp_derivedCompletionRestrictIso_hom_app`), and the composite of the
unit with `c` is the limit lift by
`Stacks.Algebraization.derivedCompletionUnit_comp_comparisonDerivedCompletionLimitAdicQuotient`. -/
theorem derivedCompletionUnit_comp_restrictComparisonLimitAdicQuotient :
    (derivedCompletionUnit ((opensRingedSite X.sheaf).over V)
          (overIdeal (idealSheafSiteSubmodule I) V)).app _ ≫ restrictComparisonLimitAdicQuotient I ℱ
            V =
      (SheafOfModules.overFunctor.{u} ((Stacks.SheafOfModules.Tensor.ringSheaf
        (opensRingedSite X.sheaf).O))
        V).mapDerivedCategory.map
        ((DerivedCategory.singleFunctor (SheafOfModules.{u} ((Stacks.SheafOfModules.Tensor.ringSheaf
          (opensRingedSite X.sheaf).O)))
          0).map
          (toLimitAdicQuotientSystem I ℱ)) := by
  exact unit_comp_restrict_iso_comp_map I V
    (derivedCompletionUnit_comp_comparisonDerivedCompletionLimitAdicQuotient I ℱ)

omit [ℱ.IsCoherent] in
/-- **The restriction of the `n`-th canonical map `ℱ^∧ ⟶ (ℱ/𝓘ⁿℱ)[0]` is the slice's own.**
Composing the completion unit of `ℱ|_V` with
`Stacks.Algebraization.restrictCompletionToAdicQuotient` gives the restriction of the quotient
projection `ℱ ⟶ ℱ/𝓘ⁿℱ`. -/
theorem derivedCompletionUnit_comp_restrictCompletionToAdicQuotient (n : ℕ) :
    (derivedCompletionUnit ((opensRingedSite X.sheaf).over V)
          (overIdeal (idealSheafSiteSubmodule I) V)).app _ ≫
        restrictCompletionToAdicQuotient I ℱ V n =
      (SheafOfModules.overFunctor.{u} ((Stacks.SheafOfModules.Tensor.ringSheaf
        (opensRingedSite X.sheaf).O))
        V).mapDerivedCategory.map
        ((DerivedCategory.singleFunctor (SheafOfModules.{u} ((Stacks.SheafOfModules.Tensor.ringSheaf
          (opensRingedSite X.sheaf).O)))
          0).map
          ((adicQuotientCone I ℱ).π.app ⟨n⟩)) := by
  exact unit_comp_restrict_iso_comp_map I V
    (derivedCompletionUnit_comp_completionToAdicQuotient I ℱ n)

/-- **The restricted limit `(lim ℱ/𝓘ⁿℱ)[0]|_V` is derived complete along `𝓘|_V`.** The limit
itself is derived complete along `𝓘` on a locally Noetherian scheme at an arbitrary
quasi-coherent sheaf of ideals
(`Stacks.Algebraization.isDerivedComplete_single_limit_adicQuotientSystem`), and restriction to a
slice preserves derived completeness, which is the first step of [Stacks, Tag 0A0F]. -/
theorem isDerivedComplete_restrict_single_limit_adicQuotientSystem :
    AlgebraicGeometry.RingedSite.IsDerivedComplete.{u, u, u, u}
      ((opensRingedSite X.sheaf).over V)
      (overIdeal (idealSheafSiteSubmodule I) V)
      ((SheafOfModules.overFunctor.{u} ((Stacks.SheafOfModules.Tensor.ringSheaf
        (opensRingedSite X.sheaf).O))
        V).mapDerivedCategory.obj
        ((DerivedCategory.singleFunctor (SheafOfModules.{u} ((Stacks.SheafOfModules.Tensor.ringSheaf
          (opensRingedSite X.sheaf).O)))
          0).obj
          ((limit (adicQuotientSystem I ℱ) : X.Modules) : SheafOfModules.{u}
            ((Stacks.SheafOfModules.Tensor.ringSheaf (opensRingedSite X.sheaf).O))))) := by
  obtain ⟨_, _, _, h⟩ := AlgebraicGeometry.RingedSite.restrict_isDerivedComplete_overIdeal
    (opensRingedSite X.sheaf) (idealSheafSiteSubmodule I) V _
    (isDerivedComplete_single_limit_adicQuotientSystem I ℱ)
  exact h

/-- **`Stacks.Algebraization.restrictComparisonLimitAdicQuotient` is the only map out of
`(ℱ|_V)^∧` restricting along the completion unit of the slice to the restriction of the limit
lift.** So the restriction
of `c` *is* the slice's own canonical comparison, and not merely a map with the same source and
target: the restricted limit is derived complete along `𝓘|_V`
(`Stacks.Algebraization.isDerivedComplete_restrict_single_limit_adicQuotientSystem`), so a map
out of `(ℱ|_V)^∧` into it is determined by its restriction along the unit. -/
theorem eq_restrictComparisonLimitAdicQuotient
    {g : (derivedCompletion ((opensRingedSite X.sheaf).over V)
        (overIdeal (idealSheafSiteSubmodule I) V)).obj
        ((SheafOfModules.overFunctor.{u} ((Stacks.SheafOfModules.Tensor.ringSheaf
          (opensRingedSite X.sheaf).O))
          V).mapDerivedCategory.obj
          ((DerivedCategory.singleFunctor (SheafOfModules.{u}
            ((Stacks.SheafOfModules.Tensor.ringSheaf (opensRingedSite X.sheaf).O)))
            0).obj
            (ℱ : SheafOfModules.{u} ((Stacks.SheafOfModules.Tensor.ringSheaf
              (opensRingedSite X.sheaf).O))))) ⟶
      (SheafOfModules.overFunctor.{u} ((Stacks.SheafOfModules.Tensor.ringSheaf
        (opensRingedSite X.sheaf).O))
        V).mapDerivedCategory.obj
        ((DerivedCategory.singleFunctor (SheafOfModules.{u} ((Stacks.SheafOfModules.Tensor.ringSheaf
          (opensRingedSite X.sheaf).O)))
          0).obj
          ((limit (adicQuotientSystem I ℱ) : X.Modules) : SheafOfModules.{u}
            ((Stacks.SheafOfModules.Tensor.ringSheaf (opensRingedSite X.sheaf).O))))}
    (hg : (derivedCompletionUnit ((opensRingedSite X.sheaf).over V)
          (overIdeal (idealSheafSiteSubmodule I) V)).app _ ≫ g =
      (SheafOfModules.overFunctor.{u} ((Stacks.SheafOfModules.Tensor.ringSheaf
        (opensRingedSite X.sheaf).O))
        V).mapDerivedCategory.map
        ((DerivedCategory.singleFunctor (SheafOfModules.{u} ((Stacks.SheafOfModules.Tensor.ringSheaf
          (opensRingedSite X.sheaf).O)))
          0).map
          (toLimitAdicQuotientSystem I ℱ))) :
    g = restrictComparisonLimitAdicQuotient I ℱ V :=
  AlgebraicGeometry.RingedSite.hom_ext_derivedCompletionUnit _ _
    (isDerivedComplete_restrict_single_limit_adicQuotientSystem I ℱ V)
    (hg.trans (derivedCompletionUnit_comp_restrictComparisonLimitAdicQuotient I ℱ V).symm)

/-! ### The limit side, restricted -/

/-- **Part (4) of [Stacks, Tag 0A0K] carried to a slice.** The restriction of
`(lim ℱ/𝓘ⁿℱ)[0]` is a derived inverse limit of the restriction of the adic quotient tower,
through the restrictions of the limit projections.

Part (4) with its projections pinned is
`Stacks.Algebraization.exists_isDerivedLimitWithProjections_single_limit_adicQuotientSystem`;
restriction to a slice is triangulated and preserves the countable products of the derived
categories (`AlgebraicGeometry.RingedSite`
`.preservesProductsOfShape_nat_overFunctor_mapDerivedCategory`, [Stacks, Tag 08FJ]), so
`NoetherianAdicCompletion.IsDerivedLimitWithProjections.map` carries the presentation over with
the restricted projections. -/
theorem exists_isDerivedLimitWithProjections_restrict_single_limit :
    ∃ h : HasProduct (fun n : ℕ =>
        ((adicQuotientSystem I ℱ ⋙ DerivedCategory.singleFunctor
            (SheafOfModules.{u} ((Stacks.SheafOfModules.Tensor.ringSheaf
              (opensRingedSite X.sheaf).O))) 0) ⋙
          (SheafOfModules.overFunctor.{u} ((Stacks.SheafOfModules.Tensor.ringSheaf
            (opensRingedSite X.sheaf).O))
            V).mapDerivedCategory).obj ⟨n⟩),
      @NoetherianAdicCompletion.IsDerivedLimitWithProjections _ _ _ _ _ _ _
        ((adicQuotientSystem I ℱ ⋙ DerivedCategory.singleFunctor
            (SheafOfModules.{u} ((Stacks.SheafOfModules.Tensor.ringSheaf
              (opensRingedSite X.sheaf).O))) 0) ⋙
          (SheafOfModules.overFunctor.{u} ((Stacks.SheafOfModules.Tensor.ringSheaf
            (opensRingedSite X.sheaf).O))
            V).mapDerivedCategory) h
        ((SheafOfModules.overFunctor.{u} ((Stacks.SheafOfModules.Tensor.ringSheaf
          (opensRingedSite X.sheaf).O))
          V).mapDerivedCategory.obj
          ((DerivedCategory.singleFunctor (SheafOfModules.{u}
            ((Stacks.SheafOfModules.Tensor.ringSheaf (opensRingedSite X.sheaf).O)))
            0).obj
            ((limit (adicQuotientSystem I ℱ) : X.Modules) : SheafOfModules.{u}
              ((Stacks.SheafOfModules.Tensor.ringSheaf (opensRingedSite X.sheaf).O)))))
        (fun n : ℕ => (SheafOfModules.overFunctor.{u} ((Stacks.SheafOfModules.Tensor.ringSheaf
          (opensRingedSite X.sheaf).O))
          V).mapDerivedCategory.map
          ((DerivedCategory.singleFunctor (SheafOfModules.{u}
            ((Stacks.SheafOfModules.Tensor.ringSheaf (opensRingedSite X.sheaf).O)))
            0).map
            (limit.π (adicQuotientSystem I ℱ) ⟨n⟩))) := by
  have h4 : ∃ h : HasProduct (fun n : ℕ =>
      (adicQuotientSystem I ℱ ⋙ DerivedCategory.singleFunctor
        (SheafOfModules.{u} ((Stacks.SheafOfModules.Tensor.ringSheaf
          (opensRingedSite X.sheaf).O))) 0).obj ⟨n⟩),
      @NoetherianAdicCompletion.IsDerivedLimitWithProjections _ _ _ _ _ _ _
        (adicQuotientSystem I ℱ ⋙ DerivedCategory.singleFunctor
          (SheafOfModules.{u} ((Stacks.SheafOfModules.Tensor.ringSheaf
            (opensRingedSite X.sheaf).O))) 0) h
        ((DerivedCategory.singleFunctor (SheafOfModules.{u} ((Stacks.SheafOfModules.Tensor.ringSheaf
          (opensRingedSite X.sheaf).O)))
          0).obj
          ((limit (adicQuotientSystem I ℱ) : X.Modules) : SheafOfModules.{u}
            ((Stacks.SheafOfModules.Tensor.ringSheaf (opensRingedSite X.sheaf).O))))
        (fun n : ℕ => (DerivedCategory.singleFunctor (SheafOfModules.{u}
          ((Stacks.SheafOfModules.Tensor.ringSheaf (opensRingedSite X.sheaf).O))) 0).map
          (limit.π (adicQuotientSystem I ℱ) ⟨n⟩)) :=
    exists_isDerivedLimitWithProjections_single_limit_adicQuotientSystem I ℱ
  obtain ⟨hp4, hlim4⟩ := h4
  have := hp4
  have : PreservesLimitsOfShape (Discrete ℕ)
      (SheafOfModules.overFunctor.{u} ((Stacks.SheafOfModules.Tensor.ringSheaf
        (opensRingedSite X.sheaf).O)) V).mapDerivedCategory :=
    AlgebraicGeometry.RingedSite.preservesProductsOfShape_nat_overFunctor_mapDerivedCategory
      (opensRingedSite X.sheaf) V
  have := CategoryTheory.Limits.hasProduct_comp_of_preservesLimit
    (SheafOfModules.overFunctor.{u} ((Stacks.SheafOfModules.Tensor.ringSheaf
      (opensRingedSite X.sheaf).O)) V).mapDerivedCategory
    (adicQuotientSystem I ℱ ⋙ DerivedCategory.singleFunctor
      (SheafOfModules.{u} ((Stacks.SheafOfModules.Tensor.ringSheaf (opensRingedSite X.sheaf).O))) 0)
  exact ⟨inferInstance, hlim4.map _⟩

/-- **The slice's canonical comparison followed by the restricted `n`-th limit projection is the
slice's `n`-th canonical map onto the tower.** This is
`Stacks.Algebraization.comparison_comp_single_limit_π` carried along the restriction functor. -/
theorem restrictComparisonLimitAdicQuotient_comp_map_single_limit_π (n : ℕ) :
    restrictComparisonLimitAdicQuotient I ℱ V ≫
        (SheafOfModules.overFunctor.{u} ((Stacks.SheafOfModules.Tensor.ringSheaf
          (opensRingedSite X.sheaf).O))
          V).mapDerivedCategory.map
          ((DerivedCategory.singleFunctor (SheafOfModules.{u}
            ((Stacks.SheafOfModules.Tensor.ringSheaf (opensRingedSite X.sheaf).O)))
            0).map
            (limit.π (adicQuotientSystem I ℱ) ⟨n⟩)) =
      restrictCompletionToAdicQuotient I ℱ V n :=
  (Category.assoc _ _ _).trans
    (congrArg
      (fun z => (derivedCompletionRestrictIso (opensRingedSite X.sheaf)
          (idealSheafSiteSubmodule I) V).hom.app
          ((DerivedCategory.singleFunctor (SheafOfModules.{u}
            ((Stacks.SheafOfModules.Tensor.ringSheaf (opensRingedSite X.sheaf).O)))
            0).obj
            (ℱ : SheafOfModules.{u} ((Stacks.SheafOfModules.Tensor.ringSheaf
              (opensRingedSite X.sheaf).O)))) ≫ z)
      (((SheafOfModules.overFunctor.{u} ((Stacks.SheafOfModules.Tensor.ringSheaf
        (opensRingedSite X.sheaf).O))
        V).mapDerivedCategory.map_comp _ _).symm.trans
        (congrArg (SheafOfModules.overFunctor.{u} ((Stacks.SheafOfModules.Tensor.ringSheaf
          (opensRingedSite X.sheaf).O))
          V).mapDerivedCategory.map
          (comparison_comp_single_limit_π I ℱ n))))

/-! ### The per-slice invertibility and the descent -/

/-- **The slice's canonical comparison is invertible as soon as `(ℱ|_V)^∧` is presented as a
derived limit of the restricted tower through the slice's own canonical maps.**

The target is presented over the same tower through the restrictions of the limit projections
(`Stacks.Algebraization.exists_isDerivedLimitWithProjections_restrict_single_limit`), the two
cones are matched by
`Stacks.Algebraization.restrictComparisonLimitAdicQuotient_comp_map_single_limit_π`, and
`Stacks.Algebraization.isIso_of_isDerivedLimitWithProjections_of_comp_proj` concludes: maps out
of `(ℱ|_V)^∧` are determined by their restriction along the completion unit of the slice, whose
source is concentrated in degrees `≤ 0`. -/
theorem isIso_restrictComparisonLimitAdicQuotient
    (hq : ∃ h : HasProduct (fun n : ℕ =>
        ((adicQuotientSystem I ℱ ⋙ DerivedCategory.singleFunctor
            (SheafOfModules.{u} ((Stacks.SheafOfModules.Tensor.ringSheaf
              (opensRingedSite X.sheaf).O))) 0) ⋙
          (SheafOfModules.overFunctor.{u} ((Stacks.SheafOfModules.Tensor.ringSheaf
            (opensRingedSite X.sheaf).O))
            V).mapDerivedCategory).obj ⟨n⟩),
      @NoetherianAdicCompletion.IsDerivedLimitWithProjections _ _ _ _ _ _ _
        ((adicQuotientSystem I ℱ ⋙ DerivedCategory.singleFunctor
            (SheafOfModules.{u} ((Stacks.SheafOfModules.Tensor.ringSheaf
              (opensRingedSite X.sheaf).O))) 0) ⋙
          (SheafOfModules.overFunctor.{u} ((Stacks.SheafOfModules.Tensor.ringSheaf
            (opensRingedSite X.sheaf).O))
            V).mapDerivedCategory) h
        ((derivedCompletion ((opensRingedSite X.sheaf).over V)
          (overIdeal (idealSheafSiteSubmodule I) V)).obj
          ((SheafOfModules.overFunctor.{u} ((Stacks.SheafOfModules.Tensor.ringSheaf
            (opensRingedSite X.sheaf).O))
            V).mapDerivedCategory.obj
            ((DerivedCategory.singleFunctor (SheafOfModules.{u}
              ((Stacks.SheafOfModules.Tensor.ringSheaf (opensRingedSite X.sheaf).O))) 0).obj
              (ℱ : SheafOfModules.{u} ((Stacks.SheafOfModules.Tensor.ringSheaf
                (opensRingedSite X.sheaf).O))))))
        (restrictCompletionToAdicQuotient I ℱ V)) :
    IsIso (restrictComparisonLimitAdicQuotient I ℱ V) := by
  obtain ⟨hp4, hlim4⟩ := exists_isDerivedLimitWithProjections_restrict_single_limit I ℱ V
  obtain ⟨hpq, hlimq⟩ := hq
  have := hpq
  have hGE : ∀ n : ℕ,
      (((adicQuotientSystem I ℱ ⋙ DerivedCategory.singleFunctor
            (SheafOfModules.{u} ((Stacks.SheafOfModules.Tensor.ringSheaf
              (opensRingedSite X.sheaf).O))) 0) ⋙
        (SheafOfModules.overFunctor.{u} ((Stacks.SheafOfModules.Tensor.ringSheaf
          (opensRingedSite X.sheaf).O))
          V).mapDerivedCategory).obj ⟨n⟩).IsGE 0 :=
    fun n => isGE_restrict_single V ((adicQuotientSystem I ℱ).obj ⟨n⟩)
  refine isIso_of_isDerivedLimitWithProjections_of_comp_proj hGE hlimq hlim4
    (isLE_restrict_single V _) ?_ _ (restrictComparisonLimitAdicQuotient_comp_map_single_limit_π I ℱ
      V)
  intro g₁ g₂ hg
  refine AlgebraicGeometry.RingedSite.hom_ext_derivedCompletionUnit _ _
    (AlgebraicGeometry.RingedSite.isDerivedComplete_derivedCompletion_obj _ _ _) ?_
  refine hom_ext_of_comp_proj hlimq hGE (isLE_restrict_single V _) fun n => ?_
  exact ((Category.assoc _ _ _).trans
    (congrArg (fun z => _ ≫ z) (hg n))).trans (Category.assoc _ _ _).symm

/-- The restriction of `c` to the slice over `V` is invertible whenever the slice's canonical
comparison is, the two differing by the isomorphism of [Stacks, Tag 0A0F]. -/
theorem isIso_map_comparison_of_isIso_restrictComparisonLimitAdicQuotient
    (h : IsIso (restrictComparisonLimitAdicQuotient I ℱ V)) :
    IsIso ((SheafOfModules.overFunctor.{u} ((Stacks.SheafOfModules.Tensor.ringSheaf
      (opensRingedSite X.sheaf).O))
      V).mapDerivedCategory.map
      (comparisonDerivedCompletionLimitAdicQuotient I ℱ)) := by
  have : IsIso ((derivedCompletionRestrictIso (opensRingedSite X.sheaf)
        (idealSheafSiteSubmodule I) V).hom.app _ ≫
      (SheafOfModules.overFunctor.{u} ((Stacks.SheafOfModules.Tensor.ringSheaf
        (opensRingedSite X.sheaf).O))
        V).mapDerivedCategory.map
        (comparisonDerivedCompletionLimitAdicQuotient I ℱ)) := h
  exact IsIso.of_isIso_comp_left ((derivedCompletionRestrictIso (opensRingedSite X.sheaf)
    (idealSheafSiteSubmodule I) V).hom.app ((DerivedCategory.singleFunctor _ 0).obj
      (ℱ : SheafOfModules _))) _

/-- **Invertibility of `c` is local on the affine opens.** The affine opens cover the small
Zariski site (`Stacks.Algebraization.coversTop_affineOpens`) and invertibility in `D(𝒪_X)` is
local on the site (`Stacks.SheafOfModules.isIso_of_coversTop_mapDerivedCategory`), so `c` is
invertible as soon as each of its restrictions to an affine slice is. -/
theorem isIso_comparison_of_isIso_map_affineOpens
    (h : ∀ U : X.affineOpens,
      IsIso ((SheafOfModules.overFunctor.{u} ((Stacks.SheafOfModules.Tensor.ringSheaf
        (opensRingedSite X.sheaf).O))
        U.1).mapDerivedCategory.map
        (comparisonDerivedCompletionLimitAdicQuotient I ℱ))) :
    IsIso (comparisonDerivedCompletionLimitAdicQuotient I ℱ) :=
  Stacks.SheafOfModules.isIso_of_coversTop_mapDerivedCategory
    (coversTop_affineOpens (X := X)) (comparisonDerivedCompletionLimitAdicQuotient I ℱ) h

/-- **The descent, and with it part (3) of [Stacks, Tag 0A0K] read through its canonical
comparison map.** If over every affine open `V` the derived completion `(ℱ|_V)^∧` is a derived
inverse limit of the restriction of the adic quotient tower through the slice's own canonical
maps `Stacks.Algebraization.restrictCompletionToAdicQuotient`, then the canonical comparison
`c : ℱ^∧ ⟶ (lim ℱ/𝓘ⁿℱ)[0]` is an isomorphism.

The per-slice invertibility is `Stacks.Algebraization.isIso_restrictComparisonLimitAdicQuotient`,
and invertibility of `c` itself follows by
`Stacks.Algebraization.isIso_comparison_of_isIso_map_affineOpens`.

No quasi-compactness of `X` and no global generating family for `𝓘` appear, which is the point:
the Koszul presentation the hypothesis asks for is available on an affine slice without either
(`Stacks.KoszulProZero.exists_isDerivedLimit_adicReductionTower_completion_overIdeal_affine`) and
is false on `X` itself when `X` is not quasi-compact. -/
theorem isIso_comparison_of_affineOpens
    (hq : ∀ U : X.affineOpens, ∃ h : HasProduct (fun n : ℕ =>
        ((adicQuotientSystem I ℱ ⋙ DerivedCategory.singleFunctor
            (SheafOfModules.{u} ((Stacks.SheafOfModules.Tensor.ringSheaf
              (opensRingedSite X.sheaf).O))) 0) ⋙
          (SheafOfModules.overFunctor.{u} ((Stacks.SheafOfModules.Tensor.ringSheaf
            (opensRingedSite X.sheaf).O))
            U.1).mapDerivedCategory).obj ⟨n⟩),
      @NoetherianAdicCompletion.IsDerivedLimitWithProjections _ _ _ _ _ _ _
        ((adicQuotientSystem I ℱ ⋙ DerivedCategory.singleFunctor
            (SheafOfModules.{u} ((Stacks.SheafOfModules.Tensor.ringSheaf
              (opensRingedSite X.sheaf).O))) 0) ⋙
          (SheafOfModules.overFunctor.{u} ((Stacks.SheafOfModules.Tensor.ringSheaf
            (opensRingedSite X.sheaf).O))
            U.1).mapDerivedCategory) h
        ((derivedCompletion ((opensRingedSite X.sheaf).over U.1)
          (overIdeal (idealSheafSiteSubmodule I) U.1)).obj
          ((SheafOfModules.overFunctor.{u} ((Stacks.SheafOfModules.Tensor.ringSheaf
            (opensRingedSite X.sheaf).O))
            U.1).mapDerivedCategory.obj
            ((DerivedCategory.singleFunctor (SheafOfModules.{u}
              ((Stacks.SheafOfModules.Tensor.ringSheaf (opensRingedSite X.sheaf).O))) 0).obj
              (ℱ : SheafOfModules.{u} ((Stacks.SheafOfModules.Tensor.ringSheaf
                (opensRingedSite X.sheaf).O))))))
        (restrictCompletionToAdicQuotient I ℱ U.1)) :
    IsIso (comparisonDerivedCompletionLimitAdicQuotient I ℱ) :=
  isIso_comparison_of_isIso_map_affineOpens I ℱ
    fun U => isIso_map_comparison_of_isIso_restrictComparisonLimitAdicQuotient I ℱ U.1
      (isIso_restrictComparisonLimitAdicQuotient I ℱ U.1 (hq U))

end Stacks.Algebraization

end
