module

public import StacksFrontier.AlgebraicGeometry.Spaces.RepresentedModulePushforwardInverseSquareSections
public import StacksFrontier.AlgebraicGeometry.Spaces.SheafOfDifferentialsChartPushforward
public import StacksFrontier.AlgebraicGeometry.Spaces.SheafOfDifferentialsSchemeZariskiDerivation

/-!
# The comparison `Φ` of Stacks 05ZC and Stacks 05ZD, and its action on sections

For a morphism `k : U' ⟶ U` of schemes of the big fppf site over `S` and an `𝒪`-module `C` on
the small étale site of `yoneda.obj U'`, this file constructs the comparison

```
Φ : restrictModule_U (Ψ_U (k_*C)) ≅ (k_s)_* (restrictModule_{U'} (Ψ_{U'} C))
```

of Stacks 05ZC and Stacks 05ZD, where `Ψ_T` is
`AlgebraicGeometry.Space.representedModuleRestriction`, `restrictModule_T` is restriction to the
small Zariski site of the scheme `T`, and `k_s` is the morphism of schemes underlying `k`, as a
composite of three factors, and computes the action of `Φ` and of its factors on sections. Over an
open of `U`, `Φ` is the chart comparison of Stacks 03G2 (4) at the object of the small étale site
of `yoneda.obj U` which the open names, followed by restriction along
`AlgebraicGeometry.Space.representedSquareOpensNat`.

## Main definitions

* `AlgebraicGeometry.Space.representedOpensComparison`: the identification of the base change of
  an open with the preimage open, read on the small étale site of `yoneda.obj T'`.
* `AlgebraicGeometry.Space.representedSquareMiddleNat`: the middle factor of `Φ`, with the two
  iterated direct images written out rather than contracted.
* `AlgebraicGeometry.Space.representedSquareOpensNat`: the restriction along which `Φ` acts on
  sections over an open of `U`.
* `AlgebraicGeometry.Space.representedSquareChartComparison`: the first factor of `Φ` at a
  single module, named and opaque.
* `AlgebraicGeometry.Space.representedSquareComparison`: **the comparison `Φ`.**

## Main results

* `AlgebraicGeometry.Space.representedSquareComparison_app_apply`: **the comparison `Φ` on
  sections over an open of the scheme `U`** — the chart comparison of Stacks 03G2 (4) at the
  object of the small étale site of `yoneda.obj U` which the open names, followed by restriction
  along `AlgebraicGeometry.Space.representedSquareOpensNat`.
* `AlgebraicGeometry.Space.representedSquareMiddleNat_app_val_app_apply`: the middle factor on
  sections.
* `AlgebraicGeometry.Space.restrictModuleBaseChange_representedModuleRestriction_app_apply`:
  **the third factor on sections**, over an open of the scheme `T`, with the morphism of the
  site a variable.
* `AlgebraicGeometry.Space.representedSquareComparison_middle_app_apply` and
  `AlgebraicGeometry.Space.representedSquareComparison_chart_restrict_apply`: **the first two
  factors on sections**, the first with the chart comparison a variable;
  `AlgebraicGeometry.Space.representedSquareChartComparison_app_apply` and
  `AlgebraicGeometry.Space.representedSquareComparison_chart_middle_app_apply` are the same two
  at the named chart comparison, separately and composed.
* `AlgebraicGeometry.Space.representedSquareComparison_middle_baseChange_app_apply`: the second
  and third factors together, at a variable section.
* `AlgebraicGeometry.Space.representedSquareOpensNat_map_apply`: restriction along
  `AlgebraicGeometry.Space.representedSquareOpensNat` split into its two halves.

## Implementation notes

The target of `PresheafOfModules.map f` is a `ModuleCat.restrictScalars` along `f`, so a reading
of one of these comparisons on sections, written at a concrete component, makes the elaborator
normalise that component. The readings are therefore stated with the morphism being read either a
variable or a definition that is not unfolded, and with the section between two factors a
variable; `AlgebraicGeometry.Space.representedSquareChartComparison` is a definition of its own,
made `irreducible` after `AlgebraicGeometry.Space.representedSquareChartComparison_eq`; and
`AlgebraicGeometry.Space.representedSmallEtaleEquivalence`,
`AlgebraicGeometry.Space.smallBaseChange` and `AlgebraicGeometry.SmallEtale.opensToSmallEtale`
are `local irreducible` for the rest of the file. Everything on the chart side is written at
`AlgebraicGeometry.Space.representedSpaceMap`.

## References

* [Stacks Project, Tag 05ZC](https://stacks.math.columbia.edu/tag/05ZC)
* [Stacks Project, Tag 05ZD](https://stacks.math.columbia.edu/tag/05ZD)
* [Stacks Project, Tag 03G2](https://stacks.math.columbia.edu/tag/03G2)
* [Stacks Project, Tag 03LU](https://stacks.math.columbia.edu/tag/03LU)
* [Stacks Project, Tag 03LC](https://stacks.math.columbia.edu/tag/03LC)
-/

@[expose] public noncomputable section

open CategoryTheory Opposite

universe u

namespace AlgebraicGeometry.Scheme.Modules

/-- Applying a threefold composite of morphisms of `𝒪_X`-modules on sections. -/
theorem comp3_app_apply {X : Scheme.{u}} {M N P Q : X.Modules} (f : M ⟶ N) (g : N ⟶ P)
    (h : P ⟶ Q) (W : X.Opens) (x : Γ(M, W)) :
    Hom.app (f ≫ g ≫ h) W x = Hom.app h W (Hom.app g W (Hom.app f W x)) := rfl

end AlgebraicGeometry.Scheme.Modules

namespace AlgebraicGeometry.SmallEtale

variable (B : BigEtaleSite.{u}) (X : Scheme.{u}) (hX : B.Contains X)

/-- The sections action of `restrictModuleBaseChangeIso` on an element.  This is
`AlgebraicGeometry.SmallEtale.restrictModuleBaseChangeIso_hom_app_app` read on a section. -/
theorem restrictModuleBaseChangeIso_hom_app_app_apply {X Y : B.Scheme} (a : X ⟶ Y)
    (M : SheafOfModules.{u} (structureSheaf B X.obj X.property)) (V : Y.obj.Opens)
    (x : Γ((SheafOfModules.pushforward.{u} (smallEtaleStructureMapRing B a) ⋙
      restrictModule B Y.obj Y.property).obj M, V)) :
    Scheme.Modules.Hom.app ((restrictModuleBaseChangeIso B a).hom.app M) V x =
      M.val.presheaf.map ((baseChangeOpensIso B a).hom.app V).op x := rfl

/-- The sections action of restriction to the small Zariski site on a morphism. -/
theorem restrictModule_map_app_apply
    {M N : SheafOfModules.{u} (structureSheaf B X hX)} (h : M ⟶ N) (W : X.Opens)
    (x : Γ((restrictModule B X hX).obj M, W)) :
    Scheme.Modules.Hom.app ((restrictModule B X hX).map h) W x =
      h.val.app (op ((opensToSmallEtale B X hX).obj W)) x := rfl

end AlgebraicGeometry.SmallEtale

namespace AlgebraicGeometry.Space

attribute [local instance] BigFppfSite.hasPullbacks_schemes

variable (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)

/-- The sections action of `representedModuleRestriction` on a morphism. -/
theorem representedModuleRestriction_map_val_app_apply (T : BigFppfOver B S hS)
    {M N : SheafOfModules.{u} (representedStructureRingSheaf B S hS T)} (h : M ⟶ N)
    (A : (_root_.AlgebraicGeometry.SmallEtale (associatedBigEtaleSite B)
      ((BigFppfOver.toScheme B S hS).obj T) T.left.property)ᵒᵖ)
    (x : ((representedModuleRestriction B S hS T).obj M).val.obj A) :
    ((representedModuleRestriction B S hS T).map h).val.app A x =
      h.val.app (op ((representedSmallEtaleEquivalence B S hS T).inverse.obj A.unop)) x := rfl

/-- The sections action of `representedModuleRestriction` on a restriction map. -/
theorem representedModuleRestriction_obj_val_map_apply (T : BigFppfOver B S hS)
    (M : SheafOfModules.{u} (representedStructureRingSheaf B S hS T))
    {A₁ A₂ : (_root_.AlgebraicGeometry.SmallEtale (associatedBigEtaleSite B)
      ((BigFppfOver.toScheme B S hS).obj T) T.left.property)ᵒᵖ} (i : A₁ ⟶ A₂)
    (x : ((representedModuleRestriction B S hS T).obj M).val.obj A₁) :
    ((representedModuleRestriction B S hS T).obj M).val.map i x =
      M.val.map ((representedSmallEtaleEquivalence B S hS T).inverse.map i.unop).op x := rfl

/-- The sections action of `representedModuleRestriction` on a restriction map, read on the
underlying presheaf of abelian groups. -/
theorem representedModuleRestriction_obj_val_presheaf_map_apply (T : BigFppfOver B S hS)
    (M : SheafOfModules.{u} (representedStructureRingSheaf B S hS T))
    {A₁ A₂ : (_root_.AlgebraicGeometry.SmallEtale (associatedBigEtaleSite B)
      ((BigFppfOver.toScheme B S hS).obj T) T.left.property)ᵒᵖ} (i : A₁ ⟶ A₂)
    (x : ((representedModuleRestriction B S hS T).obj M).val.obj A₁) :
    ((representedModuleRestriction B S hS T).obj M).val.presheaf.map i x =
      M.val.map ((representedSmallEtaleEquivalence B S hS T).inverse.map i.unop).op x := rfl

attribute [local instance] BigFppfSite.hasPullbacks_schemes

/-- Restriction of a module on the small étale site of `yoneda.obj T` to the small Zariski site
of the scheme `T`, on a morphism and on sections over an open, with the direct image written as
a `SheafOfModules.pushforward`. -/
theorem restrictModule_pushforward_map_app_apply (T : BigFppfOver B S hS)
    {M N : SheafOfModules.{u} (representedStructureRingSheaf B S hS T)} (h : M ⟶ N)
    (W : ((BigFppfOver.toScheme B S hS).obj T).Opens)
    (x : Γ((_root_.AlgebraicGeometry.SmallEtale.restrictModule (associatedBigEtaleSite B)
        ((BigFppfOver.toScheme B S hS).obj T) T.left.property).obj
      ((SheafOfModules.pushforward.{u} (representedStructureMapInverse B S hS T)).obj M), W)) :
    Scheme.Modules.Hom.app
        ((_root_.AlgebraicGeometry.SmallEtale.restrictModule (associatedBigEtaleSite B)
          ((BigFppfOver.toScheme B S hS).obj T) T.left.property).map
            ((SheafOfModules.pushforward.{u}
              (representedStructureMapInverse B S hS T)).map h)) W x =
      h.val.app (op ((representedSmallEtaleEquivalence B S hS T).inverse.obj
        ((_root_.AlgebraicGeometry.SmallEtale.opensToSmallEtale (associatedBigEtaleSite B)
        ((BigFppfOver.toScheme B S hS).obj T) T.left.property).obj W))) x := rfl

/-- The identification of the base change of an open of the scheme `T` with the preimage open,
read on the small étale site of `yoneda.obj T'`. -/
def representedOpensComparison {T' T : BigFppfOver B S hS} (g : T' ⟶ T)
    (V : ((BigFppfOver.toScheme B S hS).obj T).Opens) :
    (representedSmallEtaleEquivalence B S hS T').inverse.obj
        ((_root_.AlgebraicGeometry.SmallEtale.opensToSmallEtale (associatedBigEtaleSite B)
            ((BigFppfOver.toScheme B S hS).obj T') T'.left.property).obj
          ((TopologicalSpace.Opens.map
            (_root_.AlgebraicGeometry.SmallEtale.schemeHom
              (associatedBigEtaleSite B) g.left).base).obj V)) ⟶
      (representedSmallEtaleEquivalence B S hS T').inverse.obj
        ((representedSchemeBaseChange B S hS g).obj
          ((_root_.AlgebraicGeometry.SmallEtale.opensToSmallEtale (associatedBigEtaleSite B)
            ((BigFppfOver.toScheme B S hS).obj T) T.left.property).obj V)) :=
  (representedSmallEtaleEquivalence B S hS T').inverse.map
    ((_root_.AlgebraicGeometry.SmallEtale.baseChangeOpensIso
      (associatedBigEtaleSite B) g.left).hom.app V)

/-- **The comparison of the two composite restrictions, read on a module of the small étale site
of a representable algebraic space.**  Over an open `V` of the scheme `T` it is restriction along
the identification of the base change of `V` with the preimage open, read across the
identification of the two small étale sites. -/
theorem restrictModuleBaseChange_representedModuleRestriction_app_apply
    {T' T : BigFppfOver B S hS} (g : T' ⟶ T)
    (M : SheafOfModules.{u} (representedStructureRingSheaf B S hS T'))
    (V : ((BigFppfOver.toScheme B S hS).obj T).Opens)
    (x : Γ((_root_.AlgebraicGeometry.SmallEtale.restrictModule (associatedBigEtaleSite B)
          ((BigFppfOver.toScheme B S hS).obj T) T.left.property).obj
        ((SheafOfModules.pushforward.{u} (representedStructureMapInverse B S hS T') ⋙
          SheafOfModules.pushforward.{u}
            (representedSchemeStructureMapRing B S hS g)).obj M), V)) :
    Scheme.Modules.Hom.app
        ((_root_.AlgebraicGeometry.SmallEtale.restrictModuleBaseChangeIso
          (associatedBigEtaleSite B) g.left).hom.app
          ((SheafOfModules.pushforward.{u} (representedStructureMapInverse B S hS T')).obj M)) V x =
      M.val.map (representedOpensComparison B S hS g V).op x := rfl

variable {U' U : BigFppfOver B S hS} (k : U' ⟶ U)
  (hk : yoneda.relativelyRepresentable (yoneda.map k))

/-- The middle factor and the expansion of the forward route, composed. -/
def representedSquareMiddleScheme :
    SheafOfModules.pushforward.{u} (representedSquareSharpInverse B S hS k hk) ⟶
      SheafOfModules.pushforward.{u} (representedStructureMapInverse B S hS U') ⋙
        SheafOfModules.pushforward.{u} (representedSchemeStructureMapRing B S hS k) :=
  representedSquareMiddle B S hS k hk ≫
    (representedSquarePushforwardSchemeIso B S hS k).inv

/-- **The middle factor on sections, before the inverse route is expanded.** -/
theorem representedSquareMiddleScheme_app_val_app_apply
    (C : SheafOfModules.{u} (representedStructureRingSheaf B S hS U'))
    (T : _root_.AlgebraicGeometry.SmallEtale (associatedBigEtaleSite B)
      ((BigFppfOver.toScheme B S hS).obj U) U.left.property)
    (y : ((SheafOfModules.pushforward.{u}
      (representedSquareSharpInverse B S hS k hk)).obj C).val.obj (op T)) :
    ((representedSquareMiddleScheme B S hS k hk).app C).val.app (op T) y =
      C.val.map ((representedSquareInverseNat B S hS k hk).app T).op y :=
  (Stacks.SectionsComponents.comp_val_app_apply _ _ (op T) y).trans
    ((representedSquarePushforwardSchemeIso_inv_app_val_app_apply B S hS k C (op T) _).trans
      (representedSquareMiddle_app_val_app_apply B S hS k hk C T y))

/-- **The middle factor of the comparison of the two iterated direct images round the square**,
with the inverse route expanded. -/
def representedSquareMiddleNat :
    SheafOfModules.pushforward.{u}
          (smallBaseChangeSharp B S hS (representedSpaceMap B S hS k) hk) ⋙
        SheafOfModules.pushforward.{u} (representedStructureMapInverse B S hS U) ⟶
      SheafOfModules.pushforward.{u} (representedStructureMapInverse B S hS U') ⋙
        SheafOfModules.pushforward.{u} (representedSchemeStructureMapRing B S hS k) :=
  (representedSquarePushforwardInverseIso B S hS k hk).hom ≫
    representedSquareMiddleScheme B S hS k hk

/-- **The middle factor on sections** is restriction along the component of the comparison of
the two routes round the square. -/
theorem representedSquareMiddleNat_app_val_app_apply
    (C : SheafOfModules.{u} (representedStructureRingSheaf B S hS U'))
    (T : _root_.AlgebraicGeometry.SmallEtale (associatedBigEtaleSite B)
      ((BigFppfOver.toScheme B S hS).obj U) U.left.property)
    (y : ((SheafOfModules.pushforward.{u}
        (smallBaseChangeSharp B S hS (representedSpaceMap B S hS k) hk) ⋙
      SheafOfModules.pushforward.{u} (representedStructureMapInverse B S hS U)).obj
        C).val.obj (op T)) :
    ((representedSquareMiddleNat B S hS k hk).app C).val.app (op T) y =
      C.val.map ((representedSquareInverseNat B S hS k hk).app T).op y :=
  (Stacks.SectionsComponents.comp_val_app_apply _ _ (op T) y).trans
    (representedSquareMiddleScheme_app_val_app_apply B S hS k hk C T _)

/-- The composite restriction along which the comparison acts on sections over an open of the
scheme `U`: the identification of the base change of the open with the preimage open, read on
the small étale site of `yoneda.obj U'`, followed by the comparison of the two routes round the
square. -/
def representedSquareOpensNat (W : ((BigFppfOver.toScheme B S hS).obj U).Opens) :
    (representedSmallEtaleEquivalence B S hS U').inverse.obj
        ((_root_.AlgebraicGeometry.SmallEtale.opensToSmallEtale (associatedBigEtaleSite B)
            ((BigFppfOver.toScheme B S hS).obj U') U'.left.property).obj
          ((TopologicalSpace.Opens.map
            (_root_.AlgebraicGeometry.SmallEtale.schemeHom
              (associatedBigEtaleSite B) k.left).base).obj W)) ⟶
      (smallBaseChange B S hS (representedSpaceMap B S hS k) hk).obj
        ((representedSmallEtaleEquivalence B S hS U).inverse.obj
          ((_root_.AlgebraicGeometry.SmallEtale.opensToSmallEtale (associatedBigEtaleSite B)
            ((BigFppfOver.toScheme B S hS).obj U) U.left.property).obj W)) :=
  representedOpensComparison B S hS k W ≫
    (representedSquareInverseNat B S hS k hk).app
      ((_root_.AlgebraicGeometry.SmallEtale.opensToSmallEtale (associatedBigEtaleSite B)
        ((BigFppfOver.toScheme B S hS).obj U) U.left.property).obj W)

/-- Restriction along `AlgebraicGeometry.Space.representedSquareOpensNat` is restriction along
the comparison of the two routes round the square followed by restriction along the
identification of the base change of the open. -/
theorem representedSquareOpensNat_map_apply
    (C : SheafOfModules.{u} (representedStructureRingSheaf B S hS U'))
    (W : ((BigFppfOver.toScheme B S hS).obj U).Opens)
    (v : C.val.obj (op ((smallBaseChange B S hS (representedSpaceMap B S hS k) hk).obj
      ((representedSmallEtaleEquivalence B S hS U).inverse.obj
        ((_root_.AlgebraicGeometry.SmallEtale.opensToSmallEtale (associatedBigEtaleSite B)
          ((BigFppfOver.toScheme B S hS).obj U) U.left.property).obj W))))) :
    C.val.map (representedSquareOpensNat B S hS k hk W).op v =
      C.val.map (representedOpensComparison B S hS k W).op
        (C.val.map ((representedSquareInverseNat B S hS k hk).app
          ((_root_.AlgebraicGeometry.SmallEtale.opensToSmallEtale (associatedBigEtaleSite B)
            ((BigFppfOver.toScheme B S hS).obj U) U.left.property).obj W)).op v) :=
  PresheafOfModules.map_comp_apply C.val _ _ v

attribute [local irreducible] representedSmallEtaleEquivalence smallBaseChange
  _root_.AlgebraicGeometry.SmallEtale.opensToSmallEtale

/-- **The chart comparison of Stacks 03G2 (4) at a single module**, with the direct image of
Stacks 03LU on the left and the concrete base-change direct image on the right. -/
def representedSquareChartComparison
    (C : SheafOfModules.{u} (representedStructureRingSheaf B S hS U')) :
    (modulePushforward B S hS (representedSpaceMap B S hS k)).obj C ⟶
      (SheafOfModules.pushforward.{u}
        (smallBaseChangeSharp B S hS (representedSpaceMap B S hS k) hk)).obj C :=
  (modulePushforwardChartIso B S hS (representedSpaceMap B S hS k) hk).hom.app C

/-- **The named chart comparison is the component of
`AlgebraicGeometry.Space.modulePushforwardChartIso`.** -/
theorem representedSquareChartComparison_eq
    (C : SheafOfModules.{u} (representedStructureRingSheaf B S hS U')) :
    representedSquareChartComparison B S hS k hk C =
      (modulePushforwardChartIso B S hS (representedSpaceMap B S hS k) hk).hom.app C :=
  rfl

attribute [irreducible] representedSquareChartComparison

/-- **The comparison `Φ` of Stacks 05ZC and Stacks 05ZD**: the restriction to the small Zariski
site of `U` of the direct image along `k` of a module on the small étale site of
`yoneda.obj U'`, read as the direct image along the morphism of schemes of its restriction to
the small Zariski site of `U'`. -/
def representedSquareComparison
    (C : Modules.{u, u} B S hS (schemeSpace U').1 (schemeSpace U').2) :
    (_root_.AlgebraicGeometry.SmallEtale.restrictModule (associatedBigEtaleSite B)
          ((BigFppfOver.toScheme B S hS).obj U) U.left.property).obj
        ((SheafOfModules.pushforward.{u} (representedStructureMapInverse B S hS U)).obj
          ((modulePushforward B S hS (representedSpaceMap B S hS k)).obj C)) ⟶
      (Scheme.Modules.pushforward
          (_root_.AlgebraicGeometry.SmallEtale.schemeHom (associatedBigEtaleSite B) k.left)).obj
        ((_root_.AlgebraicGeometry.SmallEtale.restrictModule (associatedBigEtaleSite B)
            ((BigFppfOver.toScheme B S hS).obj U') U'.left.property).obj
          ((SheafOfModules.pushforward.{u} (representedStructureMapInverse B S hS U')).obj C)) :=
  (_root_.AlgebraicGeometry.SmallEtale.restrictModule (associatedBigEtaleSite B)
        ((BigFppfOver.toScheme B S hS).obj U) U.left.property).map
      ((SheafOfModules.pushforward.{u} (representedStructureMapInverse B S hS U)).map
        (representedSquareChartComparison B S hS k hk C)) ≫
    (_root_.AlgebraicGeometry.SmallEtale.restrictModule (associatedBigEtaleSite B)
          ((BigFppfOver.toScheme B S hS).obj U) U.left.property).map
        ((representedSquareMiddleNat B S hS k hk).app C) ≫
      (_root_.AlgebraicGeometry.SmallEtale.restrictModuleBaseChangeIso
        (associatedBigEtaleSite B) k.left).hom.app
        ((SheafOfModules.pushforward.{u} (representedStructureMapInverse B S hS U')).obj C)

/-- Restriction of a module on the small étale site of `yoneda.obj T` to the small Zariski site
of the scheme `T`, on a morphism and on sections over an open. -/
theorem restrictModule_representedModuleRestriction_map_app_apply (T : BigFppfOver B S hS)
    {M N : SheafOfModules.{u} (representedStructureRingSheaf B S hS T)} (h : M ⟶ N)
    (W : ((BigFppfOver.toScheme B S hS).obj T).Opens)
    (x : Γ((_root_.AlgebraicGeometry.SmallEtale.restrictModule (associatedBigEtaleSite B)
        ((BigFppfOver.toScheme B S hS).obj T) T.left.property).obj
      ((representedModuleRestriction B S hS T).obj M), W)) :
    Scheme.Modules.Hom.app
        ((_root_.AlgebraicGeometry.SmallEtale.restrictModule (associatedBigEtaleSite B)
            ((BigFppfOver.toScheme B S hS).obj T) T.left.property).map
          ((representedModuleRestriction B S hS T).map h)) W x =
      h.val.app (op ((representedSmallEtaleEquivalence B S hS T).inverse.obj
        ((_root_.AlgebraicGeometry.SmallEtale.opensToSmallEtale (associatedBigEtaleSite B)
          ((BigFppfOver.toScheme B S hS).obj T) T.left.property).obj W))) x := rfl

/-- **The second factor of the comparison on sections**: restriction along the comparison of the
two routes round the square, at the object of the small étale site of the scheme `U` which the
open `W` names. -/
theorem representedSquareComparison_middle_app_apply
    (C : SheafOfModules.{u} (representedStructureRingSheaf B S hS U'))
    (W : ((BigFppfOver.toScheme B S hS).obj U).Opens)
    (z : Γ((_root_.AlgebraicGeometry.SmallEtale.restrictModule (associatedBigEtaleSite B)
          ((BigFppfOver.toScheme B S hS).obj U) U.left.property).obj
        ((SheafOfModules.pushforward.{u}
            (smallBaseChangeSharp B S hS (representedSpaceMap B S hS k) hk) ⋙
          SheafOfModules.pushforward.{u} (representedStructureMapInverse B S hS U)).obj C), W)) :
    Scheme.Modules.Hom.app
        ((_root_.AlgebraicGeometry.SmallEtale.restrictModule (associatedBigEtaleSite B)
            ((BigFppfOver.toScheme B S hS).obj U) U.left.property).map
          ((representedSquareMiddleNat B S hS k hk).app C)) W z =
      C.val.map ((representedSquareInverseNat B S hS k hk).app
        ((_root_.AlgebraicGeometry.SmallEtale.opensToSmallEtale (associatedBigEtaleSite B)
          ((BigFppfOver.toScheme B S hS).obj U) U.left.property).obj W)).op z :=
  (_root_.AlgebraicGeometry.SmallEtale.restrictModule_map_app_apply (associatedBigEtaleSite B)
      ((BigFppfOver.toScheme B S hS).obj U) U.left.property _ W z).trans
    (representedSquareMiddleNat_app_val_app_apply B S hS k hk C
      ((_root_.AlgebraicGeometry.SmallEtale.opensToSmallEtale (associatedBigEtaleSite B)
        ((BigFppfOver.toScheme B S hS).obj U) U.left.property).obj W) z)

/-- The first factor of the comparison, under the restriction along the comparison of the two
routes round the square.  Stated with the first factor a variable. -/
theorem representedSquareComparison_chart_restrict_apply
    (C : SheafOfModules.{u} (representedStructureRingSheaf B S hS U'))
    {M : SheafOfModules.{u} (representedStructureRingSheaf B S hS U)}
    (h : M ⟶ (SheafOfModules.pushforward.{u}
      (smallBaseChangeSharp B S hS (representedSpaceMap B S hS k) hk)).obj C)
    (W : ((BigFppfOver.toScheme B S hS).obj U).Opens)
    (x : Γ((_root_.AlgebraicGeometry.SmallEtale.restrictModule (associatedBigEtaleSite B)
        ((BigFppfOver.toScheme B S hS).obj U) U.left.property).obj
      ((SheafOfModules.pushforward.{u} (representedStructureMapInverse B S hS U)).obj M), W)) :
    C.val.map ((representedSquareInverseNat B S hS k hk).app
        ((_root_.AlgebraicGeometry.SmallEtale.opensToSmallEtale (associatedBigEtaleSite B)
          ((BigFppfOver.toScheme B S hS).obj U) U.left.property).obj W)).op
        (Scheme.Modules.Hom.app
          ((_root_.AlgebraicGeometry.SmallEtale.restrictModule (associatedBigEtaleSite B)
            ((BigFppfOver.toScheme B S hS).obj U) U.left.property).map
              ((SheafOfModules.pushforward.{u}
                (representedStructureMapInverse B S hS U)).map h)) W x) =
      C.val.map ((representedSquareInverseNat B S hS k hk).app
          ((_root_.AlgebraicGeometry.SmallEtale.opensToSmallEtale (associatedBigEtaleSite B)
            ((BigFppfOver.toScheme B S hS).obj U) U.left.property).obj W)).op
        (h.val.app (op ((representedSmallEtaleEquivalence B S hS U).inverse.obj
          ((_root_.AlgebraicGeometry.SmallEtale.opensToSmallEtale (associatedBigEtaleSite B)
        ((BigFppfOver.toScheme B S hS).obj U) U.left.property).obj W))) x) :=
  congrArg (fun y ↦ C.val.map _ y)
    (restrictModule_pushforward_map_app_apply B S hS U h W x)

/-- **The first factor of `Φ` on sections**: the chart comparison of Stacks 03G2 (4), read at
the object of the small étale site of `yoneda.obj U` which the open `W` names. -/
theorem representedSquareChartComparison_app_apply
    (C : SheafOfModules.{u} (representedStructureRingSheaf B S hS U'))
    (W : ((BigFppfOver.toScheme B S hS).obj U).Opens)
    (x : Γ((_root_.AlgebraicGeometry.SmallEtale.restrictModule (associatedBigEtaleSite B)
          ((BigFppfOver.toScheme B S hS).obj U) U.left.property).obj
        ((SheafOfModules.pushforward.{u} (representedStructureMapInverse B S hS U)).obj
          ((modulePushforward B S hS (representedSpaceMap B S hS k)).obj C)), W)) :
    Scheme.Modules.Hom.app
        ((_root_.AlgebraicGeometry.SmallEtale.restrictModule (associatedBigEtaleSite B)
            ((BigFppfOver.toScheme B S hS).obj U) U.left.property).map
          ((SheafOfModules.pushforward.{u} (representedStructureMapInverse B S hS U)).map
            (representedSquareChartComparison B S hS k hk C))) W x =
      (representedSquareChartComparison B S hS k hk C).val.app
        (op ((representedSmallEtaleEquivalence B S hS U).inverse.obj
          ((_root_.AlgebraicGeometry.SmallEtale.opensToSmallEtale (associatedBigEtaleSite B)
            ((BigFppfOver.toScheme B S hS).obj U) U.left.property).obj W))) x :=
  restrictModule_pushforward_map_app_apply B S hS U
    (representedSquareChartComparison B S hS k hk C) W x

/-- **The first factor of `Φ` on sections, under the restriction the middle factor
contributes.** -/
theorem representedSquareChartComparison_restrict_apply
    (C : SheafOfModules.{u} (representedStructureRingSheaf B S hS U'))
    (W : ((BigFppfOver.toScheme B S hS).obj U).Opens)
    (x : Γ((_root_.AlgebraicGeometry.SmallEtale.restrictModule (associatedBigEtaleSite B)
          ((BigFppfOver.toScheme B S hS).obj U) U.left.property).obj
        ((SheafOfModules.pushforward.{u} (representedStructureMapInverse B S hS U)).obj
          ((modulePushforward B S hS (representedSpaceMap B S hS k)).obj C)), W)) :
    C.val.map ((representedSquareInverseNat B S hS k hk).app
          ((_root_.AlgebraicGeometry.SmallEtale.opensToSmallEtale (associatedBigEtaleSite B)
            ((BigFppfOver.toScheme B S hS).obj U) U.left.property).obj W)).op
        (Scheme.Modules.Hom.app
          ((_root_.AlgebraicGeometry.SmallEtale.restrictModule (associatedBigEtaleSite B)
              ((BigFppfOver.toScheme B S hS).obj U) U.left.property).map
            ((SheafOfModules.pushforward.{u} (representedStructureMapInverse B S hS U)).map
              (representedSquareChartComparison B S hS k hk C))) W x) =
      C.val.map ((representedSquareInverseNat B S hS k hk).app
          ((_root_.AlgebraicGeometry.SmallEtale.opensToSmallEtale (associatedBigEtaleSite B)
            ((BigFppfOver.toScheme B S hS).obj U) U.left.property).obj W)).op
        ((representedSquareChartComparison B S hS k hk C).val.app
          (op ((representedSmallEtaleEquivalence B S hS U).inverse.obj
            ((_root_.AlgebraicGeometry.SmallEtale.opensToSmallEtale (associatedBigEtaleSite B)
              ((BigFppfOver.toScheme B S hS).obj U) U.left.property).obj W))) x) :=
  representedSquareComparison_chart_restrict_apply B S hS k hk C _ W x

/-- **The first two factors of `Φ` on sections**, composed: the chart comparison of
Stacks 03G2 (4) at the object of the small étale site of `yoneda.obj U` which the open `W`
names, followed by restriction along the comparison of the two routes round the square. -/
theorem representedSquareComparison_chart_middle_app_apply
    (C : SheafOfModules.{u} (representedStructureRingSheaf B S hS U'))
    (W : ((BigFppfOver.toScheme B S hS).obj U).Opens)
    (x : Γ((_root_.AlgebraicGeometry.SmallEtale.restrictModule (associatedBigEtaleSite B)
          ((BigFppfOver.toScheme B S hS).obj U) U.left.property).obj
        ((SheafOfModules.pushforward.{u} (representedStructureMapInverse B S hS U)).obj
          ((modulePushforward B S hS (representedSpaceMap B S hS k)).obj C)), W)) :
    Scheme.Modules.Hom.app
        ((_root_.AlgebraicGeometry.SmallEtale.restrictModule (associatedBigEtaleSite B)
            ((BigFppfOver.toScheme B S hS).obj U) U.left.property).map
          ((representedSquareMiddleNat B S hS k hk).app C)) W
        (Scheme.Modules.Hom.app
          ((_root_.AlgebraicGeometry.SmallEtale.restrictModule (associatedBigEtaleSite B)
              ((BigFppfOver.toScheme B S hS).obj U) U.left.property).map
            ((SheafOfModules.pushforward.{u} (representedStructureMapInverse B S hS U)).map
              (representedSquareChartComparison B S hS k hk C))) W x) =
      C.val.map ((representedSquareInverseNat B S hS k hk).app
          ((_root_.AlgebraicGeometry.SmallEtale.opensToSmallEtale (associatedBigEtaleSite B)
            ((BigFppfOver.toScheme B S hS).obj U) U.left.property).obj W)).op
        ((representedSquareChartComparison B S hS k hk C).val.app
          (op ((representedSmallEtaleEquivalence B S hS U).inverse.obj
            ((_root_.AlgebraicGeometry.SmallEtale.opensToSmallEtale (associatedBigEtaleSite B)
              ((BigFppfOver.toScheme B S hS).obj U) U.left.property).obj W))) x) :=
  (representedSquareComparison_middle_app_apply B S hS k hk C W _).trans
    (representedSquareChartComparison_restrict_apply B S hS k hk C W x)

/-- **The second and third factors of `Φ` on sections, read at a variable section**: together
they are restriction along `AlgebraicGeometry.Space.representedSquareOpensNat`. -/
theorem representedSquareComparison_middle_baseChange_app_apply
    (C : SheafOfModules.{u} (representedStructureRingSheaf B S hS U'))
    (W : ((BigFppfOver.toScheme B S hS).obj U).Opens)
    (y : Γ((_root_.AlgebraicGeometry.SmallEtale.restrictModule (associatedBigEtaleSite B)
          ((BigFppfOver.toScheme B S hS).obj U) U.left.property).obj
        ((SheafOfModules.pushforward.{u}
            (smallBaseChangeSharp B S hS (representedSpaceMap B S hS k) hk) ⋙
          SheafOfModules.pushforward.{u} (representedStructureMapInverse B S hS U)).obj C), W)) :
    Scheme.Modules.Hom.app
        ((_root_.AlgebraicGeometry.SmallEtale.restrictModuleBaseChangeIso
            (associatedBigEtaleSite B) k.left).hom.app
          ((SheafOfModules.pushforward.{u} (representedStructureMapInverse B S hS U')).obj C)) W
        (Scheme.Modules.Hom.app
          ((_root_.AlgebraicGeometry.SmallEtale.restrictModule (associatedBigEtaleSite B)
              ((BigFppfOver.toScheme B S hS).obj U) U.left.property).map
            ((representedSquareMiddleNat B S hS k hk).app C)) W y) =
      C.val.map (representedSquareOpensNat B S hS k hk W).op y :=
  ((congrArg _ (representedSquareComparison_middle_app_apply B S hS k hk C W y)).trans
      (restrictModuleBaseChange_representedModuleRestriction_app_apply B S hS k C W _)).trans
    (representedSquareOpensNat_map_apply B S hS k hk C W _).symm

/-- **The comparison `Φ` of Stacks 05ZC and Stacks 05ZD on sections over an open `W` of the
scheme `U`**: the chart comparison of Stacks 03G2 (4), read at the object of the small étale
site of `yoneda.obj U` which `W` names, followed by restriction along
`AlgebraicGeometry.Space.representedSquareOpensNat`. -/
theorem representedSquareComparison_app_apply
    (C : SheafOfModules.{u} (representedStructureRingSheaf B S hS U'))
    (W : ((BigFppfOver.toScheme B S hS).obj U).Opens)
    (x : Γ((_root_.AlgebraicGeometry.SmallEtale.restrictModule (associatedBigEtaleSite B)
          ((BigFppfOver.toScheme B S hS).obj U) U.left.property).obj
        ((SheafOfModules.pushforward.{u} (representedStructureMapInverse B S hS U)).obj
          ((modulePushforward B S hS (representedSpaceMap B S hS k)).obj C)), W)) :
    Scheme.Modules.Hom.app (representedSquareComparison B S hS k hk C) W x =
      C.val.map (representedSquareOpensNat B S hS k hk W).op
        ((representedSquareChartComparison B S hS k hk C).val.app
          (op ((representedSmallEtaleEquivalence B S hS U).inverse.obj
            ((_root_.AlgebraicGeometry.SmallEtale.opensToSmallEtale (associatedBigEtaleSite B)
              ((BigFppfOver.toScheme B S hS).obj U) U.left.property).obj W))) x) :=
  ((Scheme.Modules.comp3_app_apply _ _ _ W x).trans
      (representedSquareComparison_middle_baseChange_app_apply B S hS k hk C W _)).trans
    (congrArg (fun y ↦ C.val.map _ y)
      (representedSquareChartComparison_app_apply B S hS k hk C W x))

end AlgebraicGeometry.Space

end
