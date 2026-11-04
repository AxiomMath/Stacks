module

public import StacksCore.Tactic.StacksAttribute
public import StacksFrontier.AlgebraicGeometry.Quot.QuotFunctorSpaceDescent
public import StacksFrontier.AlgebraicGeometry.Quot.QuotientFunctorSpaceDescent

/-!
# The points of the Quot functor with values in an algebraic space

In Situation 09TR — a morphism `f : X ⟶ B` of finite presentation of algebraic spaces over `S`
and a quasi-coherent `𝒪_X`-module `F` — the morphisms of sheaves from an algebraic space `T`
into `Quot_{F/X/B}` are described as

`Mor_{Sh((Sch/S)_fppf)}(T, Quot_{F/X/B}) = {(h, F_T ⟶ Q) : h : T ⟶ B, Q of finite presentation,`
`flat over T with support proper over T}`.

## Main results

* `AlgebraicGeometry.Space.QuotSituation.morEquivSpaceProperlySupportedQuotientOfAlgebraicSpace`:
  the bijection above, for every algebraic space `T`.
* `AlgebraicGeometry.Space.QuotSituation.mem_spaceProperlySupportedQuotients_of_spaceChart`:
  the four conditions of Stacks 09TR descend along a surjective étale chart.
* `AlgebraicGeometry.Space.QuotSituation.spaceQuotientRestrict_mem_properlySupportedQuotients`:
  they are stable under restriction to schemes.

## References

* [Stacks Project, Tag 0D3V](https://stacks.math.columbia.edu/tag/0D3V)
* [Stacks Project, Tag 0D3U](https://stacks.math.columbia.edu/tag/0D3U)
* [Stacks Project, Tag 09TR](https://stacks.math.columbia.edu/tag/09TR)
* [Stacks Project, Tag 09TT](https://stacks.math.columbia.edu/tag/09TT)
* [Stacks Project, Tag 0422](https://stacks.math.columbia.edu/tag/0422)
* [Stacks Project, Tag 089C](https://stacks.math.columbia.edu/tag/089C)
* [Stacks Project, Tag 0CZJ](https://stacks.math.columbia.edu/tag/0CZJ)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits Opposite

namespace AlgebraicGeometry.Space

universe u

attribute [local instance] pointTopology

-- The modules here have their sections in the universe `u` of the schemes; the ambient-universe
-- abelian structure of the cohomology of modules would be selected ahead of
-- `SheafOfModules.instAbelian`.
attribute [-instance] Stacks.Cohomology.SiteModules.moduleSheavesAbelian
  Stacks.Cohomology.SiteModules.moduleSheavesGrothendieck

variable {B : BigFppfSite.{u}} {S : Scheme.{u}} {hS : B.Contains S}

namespace QuotSituation

variable (D : QuotSituation B S hS) {T : AlgebraicSpaces B S hS}

/-- A finite type quasi-coherent quotient of `F_T` whose restriction to a surjective étale
chart `U ⟶ T` has support proper over `U` has support proper over `T`. -/
theorem spaceIsProperlySupportedOver_of_spaceChart (C : QuotientSituation.SpaceChart T)
    (h : T ⟶ D.Y) (K : Subobject (D.spaceBaseModule h))
    (hqc : (cokernel K.arrow).IsQuasicoherentOnSite)
    (hft : SheafOfModules.IsFiniteTypeOnSite (cokernel K.arrow))
    (hK : D.IsProperlySupportedOver (D.testAt (C.α ≫ h))
      (D.quotientModule _ (D.spaceQuotientRestrict h C.α K))) :
    D.SpaceIsProperlySupportedOver h (cokernel K.arrow) :=
  D.spaceIsProperlySupportedOver_of_spaceQuotientRestrict h (a := C.α.hom)
    ((surjective_iff_surjective_pointsMap B S hS T.1 T.2 C.U C.α.hom).2 C.surjective)
    ((isEtale_iff_presheaf_of_yoneda B S hS C.α.hom).1 C.etale) K hqc hft hK

/-- The restriction of a pair over `T` in `Quot_{F/X/B}` to a scheme `U` of the site mapping
to `T` lies in `Quot_{F/X/B}(U)`. -/
theorem spaceQuotientRestrict_mem_properlySupportedQuotients (h : T ⟶ D.Y)
    {U : BigFppfOver B S hS} (α : (schemeSpaceFunctor B S hS).obj U ⟶ T)
    {K : Subobject (D.spaceBaseModule h)} (hK : K ∈ D.spaceProperlySupportedQuotients h) :
    D.spaceQuotientRestrict h α K ∈ D.properlySupportedQuotients (D.testAt (α ≫ h)) :=
  ⟨D.spaceQuotientRestrict_mem_finitePresentationQuotients h α hK.1,
    D.isProperlySupportedOver_spaceQuotientRestrict h α K hK.1.1.1
      (let := hK.1.2; inferInstance) hK.2⟩

/-- A quasi-coherent quotient of `F_T` whose restriction to a surjective étale chart `U ⟶ T`
lies in `Quot_{F/X/B}(U)` lies in `Quot_{F/X/B}` over `T`. -/
theorem mem_spaceProperlySupportedQuotients_of_spaceChart (C : QuotientSituation.SpaceChart T)
    (h : T ⟶ D.Y) (K : Subobject (D.spaceBaseModule h))
    (hqc : (cokernel K.arrow).IsQuasicoherentOnSite)
    (hK : D.spaceQuotientRestrict h C.α K ∈ D.properlySupportedQuotients (D.testAt (C.α ≫ h))) :
    K ∈ D.spaceProperlySupportedQuotients h := by
  have hfp := D.mem_spaceFinitePresentationQuotients_of_spaceQuotientRestrict C h K hqc hK.1
  exact ⟨hfp, D.spaceIsProperlySupportedOver_of_spaceChart C h K hqc
    (let := hfp.2; inferInstance) hK.2⟩

/-- In Situation 09TR, let `T` be an algebraic space over `S`. The morphisms of sheaves on the
big fppf site of `S` from `T` into `Quot_{F/X/B}` are in bijection with the pairs `(h, F_T ⟶ Q)`
consisting of a morphism `h : T ⟶ B` of algebraic spaces and a quotient `Q` of the pullback
`F_T` of `F` to the algebraic space `X ×_{B, h} T`, with `Q` quasi-coherent, of finite
presentation, flat over `T` and with support proper over `T`.

The left-hand side is the Quot presheaf `AlgebraicGeometry.Space.QuotSituation.quotSitePresheaf`,
with the sheaf of `T` lifted to its universe. The inverse sends a pair to the transformation
restricting it along the chart `t : V ⟶ T` of every section `t` of `T` over a scheme `V` of the
site. -/
@[stacks 0D3V "the displayed identification, read as a bijection, for an arbitrary algebraic \
space T over S"]
def morEquivSpaceProperlySupportedQuotientOfAlgebraicSpace (T : AlgebraicSpaces B S hS) :
    (T.obj ⋙ uliftFunctor.{u + 1, u} ⟶ D.quotSitePresheaf) ≃
      D.SpaceProperlySupportedQuotients T :=
  (Iso.homCongr (Iso.refl _) D.quotSitePresheafIsoTotal).trans
    (D.morEquivSpaceQuotientOfDescends
      (fun h _ α _ hK ↦ D.spaceQuotientRestrict_mem_properlySupportedQuotients h α hK)
      (modulePushforwardCoherence B S hS)
      (fun m K hK ↦ D.quotientPullback_mem_properlySupportedQuotients m K hK)
      (fun _ _ hK ↦ hK.1.1.1)
      (fun C h K hqc hK ↦ D.mem_spaceProperlySupportedQuotients_of_spaceChart C h K hqc hK))

/-- The inverse of the identification of Stacks 0D3V restricts a pair along the chart of each
section of `T`. -/
theorem morEquivSpaceProperlySupportedQuotientOfAlgebraicSpace_symm_app
    {T : AlgebraicSpaces B S hS} (q : D.SpaceProperlySupportedQuotients T)
    {V : BigFppfOver B S hS} (t : T.obj.obj (op V)) :
    ((D.morEquivSpaceProperlySupportedQuotientOfAlgebraicSpace T).symm q).app (op V)
        (ULift.up t) =
      ⟨ObjectProperty.homMk (yonedaEquiv.symm t) ≫ q.hom,
        D.spaceQuotientRestrict q.hom (ObjectProperty.homMk (yonedaEquiv.symm t)) q.ker,
        D.spaceQuotientRestrict_mem_properlySupportedQuotients q.hom _ q.mem⟩ :=
  rfl

end QuotSituation

end AlgebraicGeometry.Space

end
