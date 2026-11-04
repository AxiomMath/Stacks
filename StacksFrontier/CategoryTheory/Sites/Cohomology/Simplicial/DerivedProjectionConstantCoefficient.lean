module

public import
  StacksFrontier.CategoryTheory.Sites.Cohomology.ChaoticSite.SimplexMooreConstantCoefficient
public import
  StacksFrontier.CategoryTheory.Sites.Cohomology.Simplicial.DerivedProjectionMooreComplexModules
import StacksCore.Tactic.StacksAttribute

/-!
# `Lπ_!` of a constant simplicial module is its value

Let `(C, J)` be a small site, let `O` be a sheaf of rings on it, let `π : Δ × C ⥤ C` be the
projection of [Stacks, Tag 09D0] and let `Δ × C` carry the topology it inherits from `(C, J)`
along `π`. A sheaf of `π^{-1}O`-modules on `Δ × C` is a simplicial sheaf of `O`-modules
(`Stacks.SimplicialModules.fibrewiseMod`), and
`Stacks.SimplicialModules.derivedProjectionLowerShriekIsoMooreComplexModules` — the
module-coefficient form of the untagged paragraph of Cohomology on Sites, Section 09D0 — computes

`Lπ_!(ℱ[0]) ≅ s(ℱ_•)`,

the alternating-face-map complex of that simplicial module. This file reads that computation at a
**constant** simplicial module: if `ℱ_• ≅ 𝒢` constantly, then

`Lπ_!(ℱ[0]) ≅ 𝒢[0]`,

because the Moore complex of a constant simplicial object is a resolution of its value
(`Stacks.ChaoticSite.SimplexValued.quasiIso_mooreCochainAugmentation_const`) and the colimit over
`Δᵒᵖ` of a constant diagram is its value
(`Stacks.ChaoticSite.SimplexValued.colimConstIso`).

## Main definitions

* `Stacks.SimplicialModules.derivedProjectionLowerShriekIsoOfFibrewiseConst`: the isomorphism
  above, for a sheaf of `π^{-1}O`-modules whose fibrewise reading is identified with a constant
  simplicial module.
* `Stacks.SimplicialModules.fibrewiseModInverseImageConstIso`: the fibrewise reading of `π^{-1}𝒢`
  **is** the constant simplicial module on `𝒢`.
* `Stacks.SimplicialModules.derivedProjectionLowerShriekInverseImageIso`: the two put together,
  `Lπ_!(π^{-1}𝒢[0]) ≅ 𝒢[0]`, with nothing assumed.

## Implementation notes

**No tag is claimed here.** The isomorphism is the module-coefficient Section 09D0 computation
read at one class of objects, and Section 09D0 is already registered on
`Stacks.SimplicialModules.derivedProjectionLowerShriekIsoMooreComplexModules`; a second
registration on a special case of it would put the tag on a component.

**What this is, and is not, for [Stacks, Tag 09DH].** The third term of the Atiyah triangle of Tag
09DH is `Lπ_!(ℱ)` for `ℱ` the coefficient module, and `Lπ_!` there
(`CategoryTheory.Sheaf.resolutionLowerShriek`) is the functor of Tag 09D3, a *composite* of derived
extension of scalars along the augmentation `ε : 𝒫_• ⟶ ℬ` with the `Lπ_!` of Tag 09CY computed
here:

`resolutionLowerShriek = derivedBaseChangeToProjectionRing ε ⋙ derivedProjectionLowerShriek`

(that equality is the definition of `CategoryTheory.Sheaf.resolutionLowerShriek`, so no bridging
lemma is needed for it). This file discharges the **second** factor at the coefficient module: the
coefficient module of Tag 09DH is `π^{-1}ℱ` with `𝒫_•` acting through `ε`, so once the first factor
has been applied the result is `Lπ_!` of something whose fibrewise reading is constant, and that is
what is computed here.

The **first** factor is not formal and is not done here. `- ⊗^𝐋_{𝒫_•} π^{-1}ℬ` applied to the
coefficient module is *not* `π^{-1}ℱ`: the underived counit is an isomorphism only because `ε` is
surjective in each degree, while the derived one carries `Tor^{𝒫_n}_{>0}(ℱ, ℬ)` in every degree.
The ring-theoretic form of this is explicit in the module documentation of
`StacksFrontier/Cotangent/DerivedLowerShriekRestrictedCoefficients.lean` ("**This is not formal**"),
where the corresponding step of [Stacks, Tag 09DD] is carried out: it needs the invertibility of
the derived counit, which comes from [Stacks, Tag 08QJ] and the coefficient hypothesis of
[Stacks, Tag 08RX], and whose conclusion is [Stacks, Tag 08QE]. The sheaf-of-rings analogue of
that chain is what the third-term identification of Tag 09DH still owes, and it is a development of
its own, not a spelling bridge.

## References

* [Stacks Project, Tag 09D0](https://stacks.math.columbia.edu/tag/09D0)
* [Stacks Project, Tag 09D1](https://stacks.math.columbia.edu/tag/09D1)
* [Stacks Project, Tag 09DH](https://stacks.math.columbia.edu/tag/09DH)
* [Stacks Project, Tag 08QE](https://stacks.math.columbia.edu/tag/08QE)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits Opposite AlgebraicTopology

namespace Stacks.SimplicialModules

open Stacks.Cohomology.DerivedLowerShriek

universe w

attribute [local instance] HasDerivedCategory.standard

variable (C : Type w) [SmallCategory C] (J : GrothendieckTopology C)
  [Stacks.Sites.PreservesCoveringPullbacks (projectionTopology C J) (projection C)]
  (O : Sheaf J RingCat.{w})
  [HasSheafify (projectionTopology C J) AddCommGrpCat.{w}]
  [(projectionTopology C J).WEqualsLocallyBijective AddCommGrpCat.{w}]
  [HasSheafify J AddCommGrpCat.{w}] [J.WEqualsLocallyBijective AddCommGrpCat.{w}]
  [HasExt.{w} (Sheaf (projectionTopology C J) AddCommGrpCat.{w})]
  [(SheafOfModules.pushforward.{w} (F := projection C)
    (idRingMap (projectionTopology C J) J (projection C) O)).IsRightAdjoint]
  [∀ V : SimplexCategory × C, (SheafOfModules.pushforward.{w} (F := Over.forget V)
    (𝟙 ((projectionRing C J O).over V) :
      (projectionRing C J O).over V ⟶ (projectionRing C J O).over V)).IsRightAdjoint]
  [∀ U : C, (SheafOfModules.pushforward.{w} (F := Over.forget U)
    (𝟙 (O.over U) : O.over U ⟶ O.over U)).IsRightAdjoint]
  [EnoughInjectives (SheafOfModules.{w} (projectionRing C J O))]
  [EnoughInjectives (SheafOfModules.{w} O)]
  [IsGrothendieckAbelian.{w} (SheafOfModules.{w} O)]
  [HasColimitsOfShape SimplexCategoryᵒᵖ (SheafOfModules.{w} O)]

/-- **`Lπ_!` of a constant simplicial module is its value.** If the fibrewise reading of a sheaf of
`π^{-1}O`-modules `ℱ` is identified with the constant simplicial module on a sheaf of `O`-modules
`𝒢`, then `Lπ_!(ℱ[0]) ≅ 𝒢[0]` in `D(O)`.

The module-coefficient Section 09D0 computation
`Stacks.SimplicialModules.derivedProjectionLowerShriekIsoMooreComplexModules` represents
`Lπ_!(ℱ[0])` by the extended Moore complex of `ℱ_•`; transported along the identification this is
the extended Moore complex of the constant simplicial module on `𝒢`, whose augmentation to
`(colim 𝒢)[0] = 𝒢[0]` is a quasi-isomorphism by
`Stacks.ChaoticSite.SimplexValued.quasiIso_mooreCochainAugmentation_const` and
`Stacks.ChaoticSite.SimplexValued.colimConstIso`. -/
def derivedProjectionLowerShriekIsoOfFibrewiseConst
    (F : SheafOfModules.{w} (projectionRing C J O)) (G : SheafOfModules.{w} O)
    (e : (fibrewiseMod C J O).obj F ≅ (Functor.const SimplexCategoryᵒᵖ).obj G) :
    (derivedProjectionLowerShriek C J O).obj
        (DerivedCategory.Q.obj
          ((HomologicalComplex.single (SheafOfModules.{w} (projectionRing C J O))
            (ComplexShape.up ℤ) 0).obj F)) ≅
      DerivedCategory.Q.obj
        ((HomologicalComplex.single (SheafOfModules.{w} O) (ComplexShape.up ℤ) 0).obj G) :=
  haveI : QuasiIso ((Stacks.ChaoticSite.GeneralValued.mooreCochainAugmentation
      (𝟭 SimplexCategory)).app ((Functor.const SimplexCategoryᵒᵖ).obj G)) :=
    Stacks.ChaoticSite.SimplexValued.quasiIso_mooreCochainAugmentation_const G
  derivedProjectionLowerShriekIsoMooreComplexModules C J O F ≪≫
    DerivedCategory.Q.mapIso
      ((Stacks.ChaoticSite.GeneralValued.mooreCochainComplex (𝟭 SimplexCategory)
        (SheafOfModules.{w} O)).mapIso e) ≪≫
    asIso (DerivedCategory.Q.map ((Stacks.ChaoticSite.GeneralValued.mooreCochainAugmentation
      (𝟭 SimplexCategory)).app ((Functor.const SimplexCategoryᵒᵖ).obj G))) ≪≫
    DerivedCategory.Q.mapIso
      ((HomologicalComplex.single (SheafOfModules.{w} O) (ComplexShape.up ℤ) 0).mapIso
        (Stacks.ChaoticSite.SimplexValued.colimConstIso G))

/-- **`Lπ_!(π^{-1}𝒢[0]) ≅ 𝒢[0]`.** Derived lower shriek of [Stacks, Tag 09CY] along the projection
`π : Δ × C ⥤ C`, applied to the restriction along `π` of a sheaf of `O`-modules `𝒢` placed in
cohomological degree zero, is `𝒢` placed in cohomological degree zero.

Nothing is assumed: the fibrewise reading of the restriction along `π` *is* the constant simplicial
module on `𝒢` (`Stacks.SimplicialModules.fibrewiseModCompRestrictionIso`), and
`Stacks.SimplicialModules.derivedProjectionLowerShriekIsoOfFibrewiseConst` computes `Lπ_!` there.

The functor `restrictionModules (projectionTopology C J) J (projection C) O` is `π^{-1}` on sheaves
of modules; it is the same functor as
`Stacks.SheafOfModules.inverseImage (projectionTopology C J) J (projection C) O`, in which
`CategoryTheory.Sheaf.projectionCoefficients` — the coefficient module of the Atiyah triangle of
[Stacks, Tag 09DH] — is written, both being
`SheafOfModules.pushforward` along `π` for the identity of `π^{-1}O`. -/
def derivedProjectionLowerShriekRestrictionIso (G : SheafOfModules.{w} O) :
    (derivedProjectionLowerShriek C J O).obj
        (DerivedCategory.Q.obj
          ((HomologicalComplex.single (SheafOfModules.{w} (projectionRing C J O))
            (ComplexShape.up ℤ) 0).obj
            ((restrictionModules (projectionTopology C J) J (projection C) O).obj G))) ≅
      DerivedCategory.Q.obj
        ((HomologicalComplex.single (SheafOfModules.{w} O) (ComplexShape.up ℤ) 0).obj G) :=
  derivedProjectionLowerShriekIsoOfFibrewiseConst C J O _ G
    ((fibrewiseModCompRestrictionIso C J O).app G)

end Stacks.SimplicialModules

end
