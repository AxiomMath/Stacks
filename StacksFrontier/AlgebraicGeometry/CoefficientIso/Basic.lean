module

public import StacksFrontier.AlgebraicGeometry.CechSiteChange.Absolute
public import StacksFrontier.AlgebraicGeometry.CoveringResolutionQuasiIso.Main
public import StacksFrontier.AlgebraicGeometry.CoefficientIso.Lift
public import StacksFrontier.AlgebraicGeometry.Crystalline.Restrict

/-!
# The coefficient presheaf of [Stacks, Tag 01XL] is the one [Stacks, Tag 02FU] is proved for

`Stacks.CechSiteChange.absoluteCechComplexOpensIso` rewrote the absolute Čech complex of
[Stacks, Tag 01XL] as a Čech complex over the site `X.Opens` of open sets, for the family of the
open ranges of an affine open cover, with coefficients the presheaf

`absoluteCechOpensPresheaf X : V ↦ (V.ι)_* (V.ι)^* ℱ`.

The resolution [Stacks, Tag 02FU] is proved for the Čech complex of the *same* site and the
*same* kind of family, but with coefficients
  `Stacks.CechTotalComplex.CoveringResolution.cechDiagram`, whose value at `V` is
`Stacks.CechTotalComplex.CoveringResolution.infPushforward`, the direct image of the restriction of
  the universe-enlarged `ℱ`
to `V`.  This file identifies the two coefficient functors **at each open set, naturally in the
quasi-coherent module**.

The route avoids computing with sections altogether, and in particular avoids the scalar actions
across `AlgebraicGeometry.Scheme.Modules.restrictAppIso`.  Both functors are a
`SheafOfModules.pushforward` of sheaves of modules along a functor of open sets:

* `AlgebraicGeometry.Scheme.Modules.restrictFunctor V.ι` is the pushforward along
  `V.ι.opensFunctor`, and `AlgebraicGeometry.Scheme.Modules.pushforward V.ι` the pushforward
  along `Opens.map V.ι.base`;
* their composite functor of open sets is `W ↦ V.ι ''ᵁ (V.ι ⁻¹ᵁ W) = W ⊓ V`, which is
  `Stacks.CechTotalComplex.CoveringResolution.infFunctor X V`, with composite ring map
    `Stacks.CechTotalComplex.CoveringResolution.infRestriction`.

So the comparison is `SheafOfModules.pushforwardComp`, then
`SheafOfModules.pushforwardNatIso` along `infFunctorIso`, then
`SheafOfModules.pushforwardCongr` along `infRingHom_eq` — the three steps of Mathlib's own
`AlgebraicGeometry.Scheme.Modules.restrictFunctorAdjCounitIso`, which is the same construction
for the other composite `V.ι ⁻¹ᵁ (V.ι ''ᵁ ·) = 𝟭`.

## Main results

* `Stacks.Tag01XLCoefficientIso.infFunctorIso`:
  `Stacks.CechTotalComplex.CoveringResolution.infFunctor X V` is
  `Opens.map V.ι.base ⋙ V.ι.opensFunctor`.
* `Stacks.Tag01XLCoefficientIso.infRingHom_eq`: and the ring maps agree, which is
  `Scheme.Hom.app_appIso_inv` plus thinness of the lattice of open sets.
* `Stacks.Tag01XLCoefficientIso.restrictPushforwardInfIso`:
  `(V.ι)_* ∘ restrict V.ι ≅ Stacks.CechTotalComplex.CoveringResolution.infPushforward`, with no
    `ULift`.
* `Stacks.Tag01XLCoefficientIso.pullbackPushforwardInfIso`: **`(V.ι)_* (V.ι)^* ≅
  Stacks.CechTotalComplex.CoveringResolution.infPushforwardFunctor`** — the coefficient comparison,
    as an isomorphism of functors
  of the module sheaf.
* `Stacks.Tag01XLCoefficientIso.absoluteCechOpensPresheafEvalIso`: **the same statement in the
  spelling of the two tagged statements**: at each open set `V`, the coefficient presheaf of
  [Stacks, Tag 01XL] over the site of open sets agrees with the Čech diagram of
  [Stacks, Tag 02FU], naturally in the quasi-coherent module.

## What is NOT proved here, and is what the fourth label of [Stacks, Tag 01XL] still owes

`absoluteCechOpensPresheafEvalIso` is natural in `ℱ` and holds for each `V`, but it is **not**
assembled into an isomorphism of the presheaves on `(X.Opens)ᵒᵖ`: the naturality in `V` is not
proved.  That square compares
  `Stacks.CechTotalComplex.CoveringResolution.infPushforwardRestriction` — a restriction map of
sections, given by `Stacks.CechTotalComplex.CoveringResolution.infFunctorLE` — with the restriction
  map of the coefficient system
of [Stacks, Tag 01XL], which by
`Stacks.AlgebraicGeometry.RelativeCechComplex.relativeCechRestriction_eq` is
`Stacks.AlgebraicGeometry.RelativeCechComplex.relativeUnit'`, built from the unit of
`AlgebraicGeometry.Scheme.Modules.pullbackPushforwardAdjunction` and from
`AlgebraicGeometry.Scheme.Modules.pullbackComp`.  What is absent is a value for `relativeUnit`
or `relativeUnit'` *on sections*: no declaration in either tree concludes one.

Both of its two ingredients are, however, pinned down in pinned Mathlib, so the obligation is a
computation rather than a gap.  The unit of `pullbackPushforwardAdjunction` at an open immersion
is determined by the explicit unit of `restrictAdjunction`
(`AlgebraicGeometry.Scheme.Modules.restrictAdjunction_unit_app_app`, a single presheaf
restriction map) together with
`CategoryTheory.Adjunction.unit_leftAdjointUniq_hom_app`, because
`AlgebraicGeometry.Scheme.Modules.restrictFunctorIsoPullback` *is*
`CategoryTheory.Adjunction.leftAdjointUniq` of those two adjunctions; and `pullbackComp` is
determined by `AlgebraicGeometry.Scheme.Modules.conjugateEquiv_pullbackComp_inv`, whose
right-hand side `pushforwardComp` has identity components
(`pushforwardComp_hom_app_app`).  Once `relativeUnit'` is computed this way, the Čech complexes
are isomorphic by functoriality of `CategoryTheory.cechComplexFunctor` in the coefficient
presheaf alone.

## Implementation notes

**`Stacks.CechTotalComplex.CoveringResolution` must be instantiated at `X.carrier`, not at
  `X.toTopCat`.**
`AlgebraicGeometry.LocallyRingedSpace.toTopCat` is a semireducible `def` whose body is the
carrier, so `Opens.grothendieckTopology X.toTopCat` and `Opens.grothendieckTopology X.carrier`
are different terms with the same value, and instance search sees only the one it is asked for.
Written at `X.toTopCat`, the instances `(Opens.map V.ι.base).IsContinuous`,
`V.ι.opensFunctor.IsContinuous` and their composite are all unavailable, while at `X.carrier`
every one of them is found; the error names `IsContinuous`, not the `def`.

## References

* [Stacks Project, Tag 01XL](https://stacks.math.columbia.edu/tag/01XL)
* [Stacks Project, Tag 02FU](https://stacks.math.columbia.edu/tag/02FU)
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits Opposite TopologicalSpace
open AlgebraicGeometry AlgebraicGeometry.Scheme.Modules

universe u

namespace Stacks.Tag01XLCoefficientIso

variable (X : Scheme.{u}) (V : X.Opens)

/-! ### Restriction along an open immersion as a pushforward of sheaves of modules -/

/-- The morphism of presheaves of commutative rings underlying
`AlgebraicGeometry.Scheme.Modules.restrictFunctor V.ι`: the inverse of the canonical isomorphism
`Γ(V, U) ≅ Γ(X, V.ι ''ᵁ U)`. This is `AlgebraicGeometry.Scheme.Opens.restrictPresheafHom`. -/
noncomputable def restrictNatTrans :
    V.toScheme.presheaf ⟶ V.ι.opensFunctor.op ⋙ X.presheaf :=
  V.restrictPresheafHom

/-- **The morphism of sheaves of rings underlying
`AlgebraicGeometry.Scheme.Modules.restrictFunctor V.ι`.**  On sections it is
`AlgebraicGeometry.Scheme.Opens.restrictPresheafHom`, the inverse of the canonical isomorphism
`Γ(V, U) ≅ Γ(X, V.ι ''ᵁ U)`. -/
noncomputable def restrictRingHom :
    V.toScheme.ringCatSheaf ⟶
      (V.ι.opensFunctor.sheafPushforwardContinuous RingCat.{u}
        (Opens.grothendieckTopology V.toScheme.carrier)
        (Opens.grothendieckTopology X.carrier)).obj X.ringCatSheaf :=
  ⟨Functor.whiskerRight V.restrictPresheafHom (forget₂ CommRingCat RingCat)⟩

/-- Restriction along the inclusion of an open subscheme **is** the pushforward of sheaves of
modules along `V.ι.opensFunctor` and `restrictRingHom`. -/
theorem restrictFunctor_eq :
    Scheme.Modules.restrictFunctor V.ι =
      SheafOfModules.pushforward.{u} (F := V.ι.opensFunctor) (restrictRingHom X V) :=
  rfl

/-- The direct image along the inclusion of an open subscheme **is** the pushforward of sheaves of
modules along `Opens.map V.ι.base`. -/
theorem pushforward_eq :
    Scheme.Modules.pushforward V.ι = SheafOfModules.pushforward.{u} V.ι.toRingCatSheafHom :=
  rfl

/-! ### The composite functor of open sets is intersection with `V` -/

/-- **The image of the preimage of an open set under the inclusion of an open subscheme is its
intersection with that subscheme.**  This is the functor of open sets along which
[Stacks, Tag 02FU] takes its direct images. -/
theorem image_preimage_ι (W : X.Opens) : V.ι ''ᵁ (V.ι ⁻¹ᵁ W) = W ⊓ V := by
  rw [Scheme.Hom.image_preimage_eq_opensRange_inf, Scheme.Opens.opensRange_ι, inf_comm]

/-- **`Stacks.CechTotalComplex.CoveringResolution.infFunctor X V` is the composite `Opens.map
  V.ι.base ⋙ V.ι.opensFunctor`.**  The
components are `eqToIso` of `image_preimage_ι`, and naturality is automatic, the lattice of open
sets being a thin category. -/
noncomputable def infFunctorIso :
    Stacks.CechTotalComplex.CoveringResolution.infFunctor X.carrier V ≅
      TopologicalSpace.Opens.map V.ι.base ⋙ V.ι.opensFunctor :=
  NatIso.ofComponents (fun W ↦ eqToIso (image_preimage_ι X V W).symm)
    (fun _ ↦ Subsingleton.elim _ _)

/-- The morphism of sheaves of rings that `SheafOfModules.pushforwardComp` produces for the
composite of `restrictFunctor V.ι` and `(V.ι)_*`. -/
noncomputable def compRingHom :
    X.ringCatSheaf ⟶ (((TopologicalSpace.Opens.map V.ι.base) ⋙
      V.ι.opensFunctor).sheafPushforwardContinuous RingCat.{u}
        (Opens.grothendieckTopology X.carrier)
        (Opens.grothendieckTopology X.carrier)).obj X.ringCatSheaf :=
  V.ι.toRingCatSheafHom ≫
    ((TopologicalSpace.Opens.map V.ι.base).sheafPushforwardContinuous RingCat.{u}
      (Opens.grothendieckTopology X.carrier)
      (Opens.grothendieckTopology V.toScheme.carrier)).map (restrictRingHom X V)

/-- **The composite ring map is `Stacks.CechTotalComplex.CoveringResolution.infRestriction`.**
  Over an open set `W` the composite
is `V.ι.app W` followed by the inverse of the canonical isomorphism, which is
`Scheme.Hom.app_appIso_inv`, followed by the restriction along `image_preimage_ι`; and any two
morphisms of open sets with the same source and target are equal. -/
theorem infRingHom_eq :
    compRingHom X V ≫ (Functor.sheafPushforwardContinuousNatTrans
        (infFunctorIso X V).hom RingCat.{u} (Opens.grothendieckTopology X.carrier)
          (Opens.grothendieckTopology X.carrier)).app X.ringCatSheaf =
      infSheafHom X.carrier X.ringCatSheaf V := by
  refine Sheaf.hom_ext (NatTrans.ext (funext fun U ↦ ?_))
  have h : V.ι.app U.unop ≫ (V.ι.appIso (V.ι ⁻¹ᵁ U.unop)).inv ≫
      X.presheaf.map (eqToHom (image_preimage_ι X V U.unop).symm).op =
      X.presheaf.map (homOfLE (inf_le_left : U.unop ⊓ V ≤ U.unop)).op := by
    rw [Scheme.Hom.app_appIso_inv_assoc]
    exact (X.presheaf.map_comp _ _).symm.trans (congrArg _ (Subsingleton.elim _ _))
  exact congrArg (forget₂ CommRingCat RingCat).map h

/-! ### The coefficient comparison -/

/-- **The direct image of the restriction to an open subscheme is the direct image of the
restriction to the open set**, with no universe enlargement.  Assembled from
`SheafOfModules.pushforwardComp`, `SheafOfModules.pushforwardNatIso` and
`SheafOfModules.pushforwardCongr`. -/
noncomputable def restrictPushforwardInfIso :
    Scheme.Modules.restrictFunctor V.ι ⋙ Scheme.Modules.pushforward V.ι ≅
      infDirectImage.{u, u, u} X.carrier X.ringCatSheaf V :=
  SheafOfModules.pushforwardComp.{u} V.ι.toRingCatSheafHom (restrictRingHom X V) ≪≫
    SheafOfModules.pushforwardNatIso.{u} (compRingHom X V) (infFunctorIso X V) ≪≫
    SheafOfModules.pushforwardCongr (infRingHom_eq X V)

/-- **The coefficient comparison for [Stacks, Tag 01XL] against [Stacks, Tag 02FU]:**
`(V.ι)_* (V.ι)^* ≅ Stacks.CechTotalComplex.CoveringResolution.infPushforwardFunctor X V`, as an
  isomorphism of functors of the
module sheaf.  The inverse image is replaced by restriction along the open immersion by
`AlgebraicGeometry.Scheme.Modules.restrictFunctorIsoPullback`, and the universe enlargement of
[Stacks, Tag 02FU] is removed by `moduleUniverseLiftIso`. -/
noncomputable def pullbackPushforwardInfIso :
    Scheme.Modules.pullback V.ι ⋙ Scheme.Modules.pushforward V.ι ≅
      Stacks.CechTotalComplex.CoveringResolution.infPushforwardFunctor.{u, u, u, u} X.carrier
        X.ringCatSheaf V :=
  Functor.isoWhiskerRight (Scheme.Modules.restrictFunctorIsoPullback V.ι).symm
      (Scheme.Modules.pushforward V.ι) ≪≫
    restrictPushforwardInfIso X V ≪≫
    (infPushforwardFunctorIso.{u, u, u, u} X.carrier X.ringCatSheaf V).symm

/-! ### The comparison in the spelling of the two tagged statements -/

/-- The coefficient presheaf of [Stacks, Tag 01XL] over the site of open sets, evaluated at one
open set, **is** `(V.ι)_* (V.ι)^*` on the quasi-coherent subcategory. -/
theorem absoluteCechOpensPresheaf_comp_evaluation :
    Stacks.CechSiteChange.absoluteCechOpensPresheaf X ⋙
        (CategoryTheory.evaluation (X.Opens)ᵒᵖ X.Modules).obj (op V) =
      ObjectProperty.ι (SheafOfModules.isQuasicoherent X.ringCatSheaf) ⋙
        Scheme.Modules.pullback V.ι ⋙ Scheme.Modules.pushforward V.ι :=
  rfl

/-- The Čech diagram of [Stacks, Tag 02FU], evaluated at one open set, **is** its degree-`p`
coefficient functor. -/
theorem cechDiagram_comp_evaluation :
    Stacks.CechTotalComplex.CoveringResolution.cechDiagram.{u, u, u, u} X.carrier X.ringCatSheaf ⋙
        (CategoryTheory.evaluation (X.Opens)ᵒᵖ X.Modules).obj (op V) =
      Stacks.CechTotalComplex.CoveringResolution.infPushforwardFunctor.{u, u, u, u} X.carrier
        X.ringCatSheaf V :=
  rfl

/-- **The coefficient presheaf of [Stacks, Tag 01XL] over the site of open sets agrees, at every
open set and naturally in the quasi-coherent module, with the Čech diagram of
[Stacks, Tag 02FU].**  The naturality in the open set is not proved here; see the module
docstring. -/
noncomputable def absoluteCechOpensPresheafEvalIso :
    Stacks.CechSiteChange.absoluteCechOpensPresheaf X ⋙
        (CategoryTheory.evaluation (X.Opens)ᵒᵖ X.Modules).obj (op V) ≅
      ObjectProperty.ι (SheafOfModules.isQuasicoherent X.ringCatSheaf) ⋙
        Stacks.CechTotalComplex.CoveringResolution.cechDiagram.{u, u, u, u} X.carrier X.ringCatSheaf
          ⋙
          (CategoryTheory.evaluation (X.Opens)ᵒᵖ X.Modules).obj (op V) :=
  eqToIso (absoluteCechOpensPresheaf_comp_evaluation X V) ≪≫
    Functor.isoWhiskerLeft _ (pullbackPushforwardInfIso X V) ≪≫
    eqToIso (congrArg _ (cechDiagram_comp_evaluation X V).symm)

end Stacks.Tag01XLCoefficientIso

end
