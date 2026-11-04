module

public import StacksFrontier.AlgebraicGeometry.Spaces.SheafOfDifferentialsSchemeSquareCommutes
public import StacksFrontier.AlgebraicGeometry.Spaces.SheafOfDifferentialsSchemeSquareDerivation
import StacksCore.Tactic.StacksAttribute

/-!
# Stacks 05ZC and Stacks 05ZD

Let `k : U' ⟶ U`, `r : U ⟶ V`, `r' : U' ⟶ V'`, `l : V' ⟶ V` be morphisms of schemes of the big
fppf site over `S` forming a commutative square whose underlying square of schemes is cartesian.
`StacksFrontier/AlgebraicGeometry/Spaces/SheafOfDifferentialsSchemeSquareCommutes.lean` proves that
the square

```
Derivation'_{yoneda.obj V}(k_*C)  ←--- restrictDerivation ---  (Ω_{U'/V'} ⟶ C)
          |                                                         |
schemeZariskiDerivationEquiv r                            schemeZariskiHomEquiv r'
          v                                                         v
SheafDerivation(restrictModule_U(Ψ_U(k_*C))) -Φ→ (Ω_{U/V} ⟶ (k_s)_*(restrictModule_{U'}(Ψ_{U'}C)))
```

commutes, where the right-hand vertical is the scheme-level restriction of derivations of
Morphisms, Lemma 01V0.  **This file proves that its other three maps are bijections and
concludes that the left-hand vertical is one**, which is
`AlgebraicGeometry.Space.IsSchemeSquareDerivationRestriction` — the one input Stacks 05ZC and
Stacks 05ZD still needed.  Both tags then follow unconditionally.

## The four maps

* the bottom horizontal `AlgebraicGeometry.Space.schemeZariskiDerivationEquiv` is an `Equiv`;
* the top horizontal is the universal property of `Ω_{yU'/yV'}` — Stacks 04CT,
  `AlgebraicGeometry.Space.universalDerivation_isUniversal` — followed by the `Equiv`
  `AlgebraicGeometry.Space.schemeZariskiHomEquiv`;
* the right-hand vertical is Morphisms, Lemma 01V0 in derivation form,
  `AlgebraicGeometry.Scheme.Hom.bijective_restrictRelativeDerivation_of_isPullback`, and this is
  the only place cartesianness is used;
* the matching of the two targets is postcomposition with the comparison `Φ` of the two tags,
  `AlgebraicGeometry.Space.representedSquareComparison`, and **that is what this file has to
  prove invertible.**  Each of its three factors is: the first is a component of the chart
  comparison of Stacks 03G2 (4) (`AlgebraicGeometry.Space.modulePushforwardChartIso`) carried by
  two functors, the third a component of
  `AlgebraicGeometry.SmallEtale.restrictModuleBaseChangeIso`, and the middle one —
  `AlgebraicGeometry.Space.representedSquareMiddle` — is `SheafOfModules.pushforwardNatTrans`
  along the comparison of the two routes round the square followed by a
  `SheafOfModules.pushforwardCongr`.

The middle factor is the one that needs an argument: it was deliberately built as
`pushforwardNatTrans` followed by `pushforwardCongr`, rather than extracted from
`AlgebraicGeometry.Space.representedModulePushforwardInverseSquareIso`, because that is the only
form whose action on sections can be read (see the implementation notes of
`StacksFrontier/AlgebraicGeometry/Spaces/RepresentedModulePushforwardInverseSquare.lean`).  So its
invertibility has to be re-derived, and it is: `SheafOfModules.pushforwardNatIso`'s `.hom` *is*
`SheafOfModules.pushforwardNatTrans`, which makes
`SheafOfModules.isIso_pushforwardNatTrans` a one-liner, and the comparison of the two routes is
invertible by `AlgebraicGeometry.Space.representedSquareInverseNat_eq`.

## Main results

* `AlgebraicGeometry.Space.isIso_representedSquareComparison`: **the comparison `Φ` of
  Stacks 05ZC and Stacks 05ZD is an isomorphism.**
* `AlgebraicGeometry.Space.bijective_restrictDerivation_schemeSquare`: **restriction of
  derivations along the top edge of a cartesian square of schemes of the site, read as
  represented algebraic spaces, is a bijection.**
* `AlgebraicGeometry.Space.schemeSquareDerivationRestriction`:
  `AlgebraicGeometry.Space.IsSchemeSquareDerivationRestriction` holds.
* `AlgebraicGeometry.Space.isIso_sheafOfDifferentialsMap_of_isPullback`: **Stacks 05ZC.**
* `AlgebraicGeometry.Space.isIso_biprodDesc_sheafOfDifferentialsMap_of_isPullback`:
  **Stacks 05ZD.**
* `PresheafOfModules.Derivation.bijective_postcomp`, `SheafOfModules.isIso_val` and
  `SheafOfModules.isIso_pushforwardNatTrans`: the three generic inputs, each with every site and
  structure map a variable.

## Implementation notes

**Invertibility facts are explicit arguments here, never instances.**  `letI` of an
invertibility fact followed by `CategoryTheory.IsIso.comp_isIso` fires on a generic composite
and does *not* fire at these geometric instantiations.
`CategoryTheory.IsIso.comp_isIso'` takes both facts as explicit arguments and does, and the same
substitution is why `Stacks.IsIsoComponents.isIso_map` and
`Stacks.IsIsoComponents.isIso_app` exist beside `CategoryTheory.Functor.map_isIso` and
`CategoryTheory.NatIso.isIso_app_of_isIso`.

**`attribute [local irreducible] representedSmallEtaleEquivalence smallBaseChange
SmallEtale.opensToSmallEtale` is confined to `section Composition`.**  With the three factors
supplied as explicit terms of exactly the shapes the body of
`AlgebraicGeometry.Space.representedSquareComparison` has, the composition still exhausts the
200000-heartbeat budget at `whnf`: the delta step on the definition is cheap, but matching the
three factors against it normalises objects of the small étale site.  The attribute removes that
outright, since this composition needs those objects only symbolically — the same measurement as
in `StacksFrontier/AlgebraicGeometry/Spaces/SheafOfDifferentialsSchemeSquareComparison.lean`.  It
is *not* in effect for the rest of the file: the two bijection statements below it do mention the
structure sheaf of the small étale site of the space and need the identification it hides, which
is the same reason it cannot be used at all in
`StacksFrontier/AlgebraicGeometry/Spaces/SheafOfDifferentialsSchemeSquareCommutes.lean`.

**`rw` with the commuting square does not fire on the composite.**
`Function.Bijective.comp` produces a `Function.comp`, and the eta-expanded lambda that `funext`
of the square gives is not a syntactic subterm of it.
`Stacks.IsIsoComponents.bijective_congr` — a bijection stays one under pointwise equality —
transports it with no pattern match at all.

**What this file does not give: Stacks 06BI.**  The residue of that tag is
`AlgebraicGeometry.Space.IsSchemeTriangleDifferentialsMono`
(`StacksFrontier/AlgebraicGeometry/Spaces/SheafOfDifferentialsTriangleChartReduction.lean`), and it
is not a consequence of anything here, for a structural reason worth recording.  The square above
controls *postcomposition* with the comparison map of Stacks 04CX — by
`Space.derivationDirectImageEquiv_sheafOfDifferentialsMap_comp_eq_restrictDerivation`,
restriction of derivations is `c ≫ -` read through a bijection — so it decides invertibility of
`c` by Yoneda and would equally decide epimorphy.  Stacks 06BI needs `c` to be a
**monomorphism**, which is a statement about the morphisms *into* the source of `c`; no amount of
information about `c ≫ -` gives it.  Its triangle is also not cartesian — the bottom edge is an
identity — so the right-hand vertical is not a bijection there in the first place.  What that tag
needs is the comparison map identified as a morphism across the identification of Stacks 04CS,
which is the compatibility of Stacks 03LC (1) with the universal derivations that this whole route
was built to avoid.

## References

* [Stacks Project, Tag 05ZC](https://stacks.math.columbia.edu/tag/05ZC)
* [Stacks Project, Tag 05ZD](https://stacks.math.columbia.edu/tag/05ZD)
* [Stacks Project, Tag 01V0](https://stacks.math.columbia.edu/tag/01V0), the scheme-level
  restriction of derivations, which is the right-hand vertical.
* [Stacks Project, Tag 01V1](https://stacks.math.columbia.edu/tag/01V1), the scheme case of
  Stacks 05ZD.
* [Stacks Project, Tag 04CX](https://stacks.math.columbia.edu/tag/04CX), the comparison map of a
  commutative square and its uniqueness.
* [Stacks Project, Tag 04CT](https://stacks.math.columbia.edu/tag/04CT), the sheaf of
  differentials and its universal derivation.
* [Stacks Project, Tag 04CU](https://stacks.math.columbia.edu/tag/04CU), the étale localization
  through which the two tags are reduced to the case of a square of schemes.
* [Stacks Project, Tag 03G2](https://stacks.math.columbia.edu/tag/03G2), part (4), base change
  of étale scheme charts.
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits Opposite

universe u

namespace PresheafOfModules.Derivation

universe v₁ v₂ u₁ u₂

variable {C : Type u₁} [Category.{v₁} C] {D : Type u₂} [Category.{v₂} D]
  {S : Cᵒᵖ ⥤ CommRingCat.{u}} {F : C ⥤ D} {R : Dᵒᵖ ⥤ CommRingCat.{u}}
  {M N : PresheafOfModules.{u} (R ⋙ forget₂ CommRingCat.{u} RingCat.{u})}
  {φ : S ⟶ F.op ⋙ R}

/-- **Postcomposition with an invertible morphism of presheaves of modules is a bijection on
derivations.**  The inverse is postcomposition with the inverse morphism: postcomposing twice is
postcomposing with the composite and postcomposing with an identity changes nothing, both by
`rfl`, so the two round trips are `congrArg` of `CategoryTheory.IsIso.hom_inv_id` and
`CategoryTheory.IsIso.inv_hom_id`.

`PresheafOfModules.Derivation.postcompEquiv`
(`StacksFrontier/Cotangent/SheavesOfRings/InverseImageCotangentComplex.lean`) is the same
statement for a `PresheafOfModules.Derivation'` and an `Iso` rather than an `IsIso`; it is not in
this file's import closure, and the named composition and identity laws it is stated beside —
`PresheafOfModules.Derivation.postcomp_postcomp` there — are why this proof does not restate
them.

The invertibility hypothesis is an explicit argument rather than an instance: at a geometric
instantiation instance resolution does not find a term of this type even when one is in
context. -/
theorem bijective_postcomp (f : M ⟶ N) (hf : IsIso f) (φ : S ⟶ F.op ⋙ R) :
    Function.Bijective (fun d : M.Derivation φ ↦ d.postcomp f) := by
  let := hf
  have hleft : ∀ d : M.Derivation φ, (d.postcomp f).postcomp (inv f) = d := fun d ↦
    congrArg d.postcomp (IsIso.hom_inv_id f)
  have hright : ∀ e : N.Derivation φ, (e.postcomp (inv f)).postcomp f = e := fun e ↦
    congrArg e.postcomp (IsIso.inv_hom_id f)
  exact ⟨fun d₁ d₂ h ↦ (hleft d₁).symm.trans
      ((congrArg (fun d : N.Derivation φ ↦ d.postcomp (inv f)) h).trans (hleft d₂)),
    fun e ↦ ⟨e.postcomp (inv f), hright e⟩⟩

end PresheafOfModules.Derivation

namespace SheafOfModules

universe v₁ u₁

variable {C : Type u₁} [Category.{v₁} C] {J : GrothendieckTopology C}

/-- **The underlying morphism of presheaves of modules of an invertible morphism of sheaves of
modules is invertible.**  The forgetful functor carries it. -/
theorem isIso_val {R : Sheaf J RingCat.{u}} {M N : SheafOfModules.{u} R} (f : M ⟶ N)
    (hf : IsIso f) : IsIso f.val := by
  let := hf
  rw [← SheafOfModules.forget_map R f]
  exact Functor.map_isIso (SheafOfModules.forget R) f

variable {D : Type u₁} [Category.{v₁} D] {K : GrothendieckTopology D} {F G : C ⥤ D}
  {T : Sheaf J RingCat.{u}} {S : Sheaf K RingCat.{u}}
  [F.IsContinuous J K] [G.IsContinuous J K]

/-- **Transporting a direct image of modules along an invertible comparison of the index functors
is invertible.**  It is the `.hom` of `SheafOfModules.pushforwardNatIso` at the isomorphism the
comparison names.

Stated with every site, structure map and comparison a variable, and with the invertibility an
explicit argument: that is the only form that is cheap to instantiate at a geometric square. -/
theorem isIso_pushforwardNatTrans
    (φ : T ⟶ (G.sheafPushforwardContinuous RingCat.{u} J K).obj S) (α : F ⟶ G) (hα : IsIso α) :
    IsIso (SheafOfModules.pushforwardNatTrans.{u} φ α) :=
  let := hα
  (SheafOfModules.pushforwardNatIso.{u} φ (asIso α)).isIso_hom

end SheafOfModules

namespace Stacks.IsIsoComponents

/-- A function pointwise equal to a bijection is a bijection.  This exists so that a commuting
square read pointwise can be transported to the composite without a `rw`, whose pattern match
against a `Function.comp` fails. -/
theorem bijective_congr {α : Sort*} {β : Sort*} {f g : α → β} (hf : Function.Bijective f)
    (h : ∀ a, f a = g a) : Function.Bijective g := funext h ▸ hf

universe v₁ v₂ u₁ u₂

variable {C : Type u₁} [Category.{v₁} C] {D : Type u₂} [Category.{v₂} D]

/-- A functor carries an invertible morphism to an invertible morphism, with the invertibility
an explicit argument.  `CategoryTheory.Functor.map_isIso` takes it as an instance, and instance
resolution does not find it at the geometric instantiations below. -/
theorem isIso_map (F : C ⥤ D) {X Y : C} (f : X ⟶ Y) (hf : IsIso f) : IsIso (F.map f) :=
  let := hf
  F.map_isIso f

/-- A component of an invertible natural transformation is invertible, with the invertibility an
explicit argument.  `CategoryTheory.NatIso.isIso_app_of_isIso` takes it as an instance. -/
theorem isIso_app {F G : C ⥤ D} (α : F ⟶ G) (hα : IsIso α) (X : C) : IsIso (α.app X) :=
  let := hα
  NatIso.isIso_app_of_isIso α X

end Stacks.IsIsoComponents

namespace AlgebraicGeometry.Space

attribute [local instance] BigFppfSite.hasPullbacks_schemes

variable (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)
  {U' U : BigFppfOver B S hS} (k : U' ⟶ U)
  (hk : yoneda.relativelyRepresentable (yoneda.map k))

/-- The comparison of the two routes round the square of small étale sites is invertible: it is
the inverse of `AlgebraicGeometry.Space.representedSmallEtaleBaseChangeInverseIso`. -/
theorem isIso_representedSquareInverseNat :
    IsIso (representedSquareInverseNat B S hS k hk) := by
  rw [representedSquareInverseNat_eq]
  exact (representedSmallEtaleBaseChangeInverseIso B S hS k hk).isIso_inv

/-- **The middle factor of the comparison is invertible.**  It is
`SheafOfModules.pushforwardNatTrans` at the comparison of the two routes round the square —
invertible by `AlgebraicGeometry.Space.isIso_representedSquareInverseNat` and
`SheafOfModules.isIso_pushforwardNatTrans` — followed by a `SheafOfModules.pushforwardCongr`,
which is an isomorphism by construction. -/
theorem isIso_representedSquareMiddle :
    IsIso (representedSquareMiddle B S hS k hk) :=
  IsIso.comp_isIso'
    (SheafOfModules.isIso_pushforwardNatTrans (representedSquareSharpInverse B S hS k hk)
      (representedSquareInverseNat B S hS k hk)
      (isIso_representedSquareInverseNat B S hS k hk))
    (SheafOfModules.pushforwardCongr.{u}
      (representedSquareSharpInverse_natTrans B S hS k hk)).isIso_hom

/-- **The middle factor, before the inverse route is expanded, is invertible.**  The contraction
of the forward route is an isomorphism by construction and the middle factor is
`AlgebraicGeometry.Space.isIso_representedSquareMiddle`. -/
theorem isIso_representedSquareMiddleScheme :
    IsIso (representedSquareMiddleScheme B S hS k hk) :=
  IsIso.comp_isIso' (isIso_representedSquareMiddle B S hS k hk)
    (representedSquarePushforwardSchemeIso B S hS k).isIso_inv

/-- **The middle factor of the comparison, with the inverse route expanded, is invertible.**  The
contraction of the iterated direct image at its source is an isomorphism by construction and the
rest is `AlgebraicGeometry.Space.isIso_representedSquareMiddleScheme`. -/
theorem isIso_representedSquareMiddleNat :
    IsIso (representedSquareMiddleNat B S hS k hk) :=
  IsIso.comp_isIso' (representedSquarePushforwardInverseIso B S hS k hk).isIso_hom
    (isIso_representedSquareMiddleScheme B S hS k hk)

/-- **The first factor of the comparison at a module is invertible.**  By
`AlgebraicGeometry.Space.representedSquareChartComparison_eq` it is a component of the chart
comparison `AlgebraicGeometry.Space.modulePushforwardChartIso` of Stacks 03G2 (4), which is an
isomorphism of functors. -/
theorem isIso_representedSquareChartComparison
    (C : SheafOfModules.{u} (representedStructureRingSheaf B S hS U')) :
    IsIso (representedSquareChartComparison B S hS k hk C) := by
  rw [representedSquareChartComparison_eq]
  exact ((modulePushforwardChartIso B S hS (representedSpaceMap B S hS k) hk).app C).isIso_hom

/-- **The first factor of the comparison `Φ` is invertible**: the chart comparison of
Stacks 03G2 (4) at `C`, carried by the direct image along the structure map of the
identification of the two small étale sites and then by restriction to the small Zariski site
of `U`. -/
theorem isIso_representedSquareComparison_chart
    (C : Modules.{u, u} B S hS (schemeSpace U').1 (schemeSpace U').2) :
    IsIso ((_root_.AlgebraicGeometry.SmallEtale.restrictModule (associatedBigEtaleSite B)
        ((BigFppfOver.toScheme B S hS).obj U) U.left.property).map
      ((SheafOfModules.pushforward.{u} (representedStructureMapInverse B S hS U)).map
        (representedSquareChartComparison B S hS k hk C))) :=
  Stacks.IsIsoComponents.isIso_map
    (_root_.AlgebraicGeometry.SmallEtale.restrictModule (associatedBigEtaleSite B)
      ((BigFppfOver.toScheme B S hS).obj U) U.left.property) _
    (Stacks.IsIsoComponents.isIso_map
      (SheafOfModules.pushforward.{u} (representedStructureMapInverse B S hS U)) _
      (isIso_representedSquareChartComparison B S hS k hk C))

/-- **The second factor of the comparison `Φ` is invertible**: the comparison of the two
iterated direct images round the square at `C`, carried by restriction to the small Zariski site
of `U`. -/
theorem isIso_representedSquareComparison_middle
    (C : Modules.{u, u} B S hS (schemeSpace U').1 (schemeSpace U').2) :
    IsIso ((_root_.AlgebraicGeometry.SmallEtale.restrictModule (associatedBigEtaleSite B)
        ((BigFppfOver.toScheme B S hS).obj U) U.left.property).map
      ((representedSquareMiddleNat B S hS k hk).app C)) :=
  Stacks.IsIsoComponents.isIso_map
    (_root_.AlgebraicGeometry.SmallEtale.restrictModule (associatedBigEtaleSite B)
      ((BigFppfOver.toScheme B S hS).obj U) U.left.property) _
    (Stacks.IsIsoComponents.isIso_app (representedSquareMiddleNat B S hS k hk)
      (isIso_representedSquareMiddleNat B S hS k hk) C)

/-- **The third factor of the comparison `Φ` is invertible**: it is a component of
`AlgebraicGeometry.SmallEtale.restrictModuleBaseChangeIso`, the comparison of the two composite
restrictions, which is an isomorphism of functors. -/
theorem isIso_representedSquareComparison_baseChange
    (C : Modules.{u, u} B S hS (schemeSpace U').1 (schemeSpace U').2) :
    IsIso ((_root_.AlgebraicGeometry.SmallEtale.restrictModuleBaseChangeIso
        (associatedBigEtaleSite B) k.left).hom.app
      ((SheafOfModules.pushforward.{u} (representedStructureMapInverse B S hS U')).obj C)) :=
  ((_root_.AlgebraicGeometry.SmallEtale.restrictModuleBaseChangeIso
    (associatedBigEtaleSite B) k.left).app
      ((SheafOfModules.pushforward.{u} (representedStructureMapInverse B S hS U')).obj C)).isIso_hom

section Composition

attribute [local irreducible] representedSmallEtaleEquivalence smallBaseChange
  _root_.AlgebraicGeometry.SmallEtale.opensToSmallEtale

/-- **The comparison `Φ` of Stacks 05ZC and Stacks 05ZD is an isomorphism.**  All three of its
factors are, and this is what the derivation square of the two tags needs of it. -/
theorem isIso_representedSquareComparison
    (C : Modules.{u, u} B S hS (schemeSpace U').1 (schemeSpace U').2) :
    IsIso (representedSquareComparison B S hS k hk C) :=
  IsIso.comp_isIso' (isIso_representedSquareComparison_chart B S hS k hk C)
    (IsIso.comp_isIso' (isIso_representedSquareComparison_middle B S hS k hk C)
      (isIso_representedSquareComparison_baseChange B S hS k C))

end Composition

/-- **Postcomposition with the comparison `Φ` is a bijection on Zariski derivations.**  This is
`PresheafOfModules.Derivation.bijective_postcomp` at
`AlgebraicGeometry.Space.isIso_representedSquareComparison`, through
`SheafOfModules.isIso_val`. -/
theorem bijective_postcomp_representedSquareComparison {V : BigFppfOver B S hS} (r : U ⟶ V)
    (C : Modules.{u, u} B S hS (schemeSpace U').1 (schemeSpace U').2) :
    Function.Bijective (fun D : ((_root_.AlgebraicGeometry.SmallEtale.restrictModule
            (associatedBigEtaleSite B) ((BigFppfOver.toScheme B S hS).obj U)
            U.left.property).obj ((representedModuleRestriction B S hS U).obj
          ((modulePushforward B S hS (schemeSpaceMap k)).obj C))).val.Derivation'
        (inverseImageStructureMap (_root_.AlgebraicGeometry.SmallEtale.schemeHom
          (associatedBigEtaleSite B) r.left)).hom ↦
      D.postcomp (representedSquareComparison B S hS k
        (relativelyRepresentable_yoneda_map B S hS k) C).val) :=
  PresheafOfModules.Derivation.bijective_postcomp
    (representedSquareComparison B S hS k (relativelyRepresentable_yoneda_map B S hS k) C).val
    (SheafOfModules.isIso_val
      (representedSquareComparison B S hS k (relativelyRepresentable_yoneda_map B S hS k) C)
      (isIso_representedSquareComparison B S hS k
        (relativelyRepresentable_yoneda_map B S hS k) C)) _

/-- **The top horizontal of the square of Stacks 05ZC and Stacks 05ZD is a bijection.**  It is
the universal property of `Ω_{yU'/yV'}` — Stacks 04CT,
`AlgebraicGeometry.Space.universalDerivation_isUniversal` — followed by the identification
`AlgebraicGeometry.Space.schemeZariskiHomEquiv` of the derivations of the small étale site of
`yoneda.obj U'` with the morphisms out of `Ω_{U'/V'}`. -/
theorem bijective_schemeZariskiHomEquiv_universalDerivation_postcomp
    {V' : BigFppfOver B S hS} (r' : U' ⟶ V')
    (C : Modules.{u, u} B S hS (schemeSpace U').1 (schemeSpace U').2) :
    Function.Bijective (⇑(schemeZariskiHomEquiv B S hS r' C) ∘
      fun g : sheafOfDifferentials B S hS (schemeSpaceMap r') ⟶ C ↦
        (universalDerivation B S hS (schemeSpaceMap r')).postcomp g.val) :=
  (schemeZariskiHomEquiv B S hS r' C).bijective.comp
    ((Function.bijective_iff_existsUnique _).2
      (universalDerivation_isUniversal B S hS (schemeSpaceMap r') C))

/-- **Restriction of derivations along the top edge of a cartesian square of schemes of the
site, read as represented algebraic spaces, is a bijection.**

Three of the four maps of the square of
`StacksFrontier/AlgebraicGeometry/Spaces/SheafOfDifferentialsSchemeSquareCommutes.lean` are
bijections — the bottom horizontal `AlgebraicGeometry.Space.schemeZariskiDerivationEquiv` is an
`Equiv`, the top horizontal is
`AlgebraicGeometry.Space.bijective_schemeZariskiHomEquiv_universalDerivation_postcomp`, the
right-hand vertical is Morphisms, Lemma 01V0 in derivation form
(`AlgebraicGeometry.Scheme.Hom.bijective_restrictRelativeDerivation_of_isPullback`) — and the
matching of the two targets, postcomposition with `Φ`, is a bijection by
`AlgebraicGeometry.Space.bijective_postcomp_representedSquareComparison`.  The square commutes,
so the left-hand vertical is a bijection too. -/
theorem bijective_restrictDerivation_schemeSquare {V V' : BigFppfOver B S hS} (r : U ⟶ V)
    (r' : U' ⟶ V') (l : V' ⟶ V)
    (hkr : schemeSpaceMap k ≫ schemeSpaceMap r = schemeSpaceMap r' ≫ schemeSpaceMap l)
    (hcart : IsPullback ((BigFppfOver.toScheme B S hS).map k)
      ((BigFppfOver.toScheme B S hS).map r') ((BigFppfOver.toScheme B S hS).map r)
      ((BigFppfOver.toScheme B S hS).map l))
    (C : Modules.{u, u} B S hS (schemeSpace U').1 (schemeSpace U').2) :
    Function.Bijective (restrictDerivation B S hS (schemeSpaceMap k) (schemeSpaceMap r)
      (schemeSpaceMap r') (schemeSpaceMap l) hkr C) := by
  have hcart' : IsPullback
      (_root_.AlgebraicGeometry.SmallEtale.schemeHom (associatedBigEtaleSite B) k.left)
      (_root_.AlgebraicGeometry.SmallEtale.schemeHom (associatedBigEtaleSite B) r'.left)
      (_root_.AlgebraicGeometry.SmallEtale.schemeHom (associatedBigEtaleSite B) r.left)
      (_root_.AlgebraicGeometry.SmallEtale.schemeHom (associatedBigEtaleSite B) l.left) := hcart
  exact ((schemeZariskiDerivationEquiv B S hS r
        ((modulePushforward B S hS (schemeSpaceMap k)).obj C)).bijective.of_comp_iff' _).1
    (((bijective_postcomp_representedSquareComparison B S hS k r C).of_comp_iff' _).1
      (Stacks.IsIsoComponents.bijective_congr
        ((Scheme.Hom.bijective_restrictRelativeDerivation_of_isPullback _ _ _ _ hcart'
          ((_root_.AlgebraicGeometry.SmallEtale.restrictModule (associatedBigEtaleSite B)
            ((BigFppfOver.toScheme B S hS).obj U') U'.left.property).obj
          ((representedModuleRestriction B S hS U').obj C))).comp
          (bijective_schemeZariskiHomEquiv_universalDerivation_postcomp B S hS r' C))
        fun g ↦ (representedSquareDerivation_restrictRelativeDerivation_schemeSpace B S hS k r
          r' l hkr hcart'.w C g).symm))

/-- **The one input of Stacks 05ZC and Stacks 05ZD holds.**  For every cartesian square of
schemes of the big fppf site over `S`, read as a square of represented algebraic spaces,
restriction of derivations along the top edge is a bijection on every `𝒪`-module of the small
étale site of the source.  Each instance is
`AlgebraicGeometry.Space.bijective_restrictDerivation_schemeSquare`. -/
theorem schemeSquareDerivationRestriction : IsSchemeSquareDerivationRestriction B S hS :=
  fun _ _ _ _ k r r' l hkr hcart C ↦
    bijective_restrictDerivation_schemeSquare B S hS k r r' l hkr hcart C

variable {X Y X' Y' : AlgebraicSpaces B S hS}

/-- **Stacks 05ZC.**  Let `X ⟶ Y` be a morphism of algebraic spaces over `S` and let
`g : Y' ⟶ Y` be a morphism of algebraic spaces over `S`.  Let `X' = X_{Y'}` be the base change
of `X` and let `g' : X' ⟶ X` be the projection.  Then the map
`(g')^*Ω_{X/Y} ⟶ Ω_{X'/Y'}` of Stacks 04CX is an isomorphism.

The base change is presented as a cartesian square `IsPullback g' p' p g` of algebraic spaces,
and the map of Stacks 04CX by the property `AlgebraicGeometry.Space.IsSheafOfDifferentialsMap`
that characterizes it — existence is
`AlgebraicGeometry.Space.isSheafOfDifferentialsMap_sheafOfDifferentialsMap` and uniqueness
`AlgebraicGeometry.Space.eq_of_isSheafOfDifferentialsMap`, so naming the map this way asserts
nothing beyond the square.

The proof is the source's own: the case of a square of schemes, Morphisms, Lemma 01V0, together
with the étale localization of Stacks 04CU.  The scheme case enters as
`AlgebraicGeometry.Scheme.Hom.bijective_restrictRelativeDerivation_of_isPullback` through
`AlgebraicGeometry.Space.schemeSquareDerivationRestriction`. -/
@[stacks 05ZC "the map of 04CX for the base change of X along g is an isomorphism, with the base
  change presented as a cartesian square and the map by the property characterizing it.  The
  étale localization of 04CU and the scheme case 01V0 are both applied as proved"]
theorem isIso_sheafOfDifferentialsMap_of_isPullback (g' : X' ⟶ X) (p' : X' ⟶ Y') (p : X ⟶ Y)
    (g : Y' ⟶ Y) (h : IsPullback g' p' p g)
    {c : (modulePullback B S hS g').obj (sheafOfDifferentials B S hS p) ⟶
      sheafOfDifferentials B S hS p'}
    (hc : IsSheafOfDifferentialsMap B S hS g' p p' c) : IsIso c :=
  isIso_of_isSheafOfDifferentialsMap_of_isPullback_of_derivationRestriction B S hS
    (schemeSquareDerivationRestriction B S hS) g' p' p g h hc

/-- **Stacks 05ZD.**  Let `f : X ⟶ T` and `g : Y ⟶ T` be morphisms of algebraic spaces over `S`
with the same target and let `p : W ⟶ X`, `q : W ⟶ Y` be the projections of the fibre product
`W = X ×_T Y`.  Then the maps of Stacks 04CX give an isomorphism
`p^*Ω_{X/T} ⊕ q^*Ω_{Y/T} ⟶ Ω_{W/T}`.

The fibre product is presented as a cartesian square `IsPullback p q f g` and the two summands
by the property `AlgebraicGeometry.Space.IsSheafOfDifferentialsMap` that characterizes the map
of Stacks 04CX for the square they come from, so the conclusion is about those two maps and not
about some decomposition of `Ω_{W/T}`.

The proof is the source's own: the case of schemes, Morphisms, Lemma 01V1, together with the
étale localization of Stacks 04CU, the scheme case entering through
`AlgebraicGeometry.Space.schemeSquareDerivationRestriction`. -/
@[stacks 05ZD "the two maps of 04CX out of p^*Omega_{X/T} and q^*Omega_{Y/T} give an
  isomorphism onto Omega_{X x_T Y/T}, with the fibre product presented as a cartesian square and
  each summand by the property characterizing it.  The étale localization of 04CU and the scheme
  case 01V1 are both applied as proved"]
theorem isIso_biprodDesc_sheafOfDifferentialsMap_of_isPullback {W T : AlgebraicSpaces B S hS}
    (p : W ⟶ X) (q : W ⟶ Y) (f : X ⟶ T) (g : Y ⟶ T) (h : IsPullback p q f g)
    (a : (modulePullback B S hS p).obj (sheafOfDifferentials B S hS f) ⟶
      sheafOfDifferentials B S hS (p ≫ f))
    (b : (modulePullback B S hS q).obj (sheafOfDifferentials B S hS g) ⟶
      sheafOfDifferentials B S hS (p ≫ f))
    (ha : IsSheafOfDifferentialsMap B S hS p f (p ≫ f) a)
    (hb : IsSheafOfDifferentialsMap B S hS q g (p ≫ f) b) :
    IsIso (biprod.desc a b) :=
  isIso_biprodDesc_of_isPullback_of_derivationRestriction B S hS
    (schemeSquareDerivationRestriction B S hS) p q f g h a b ha hb

end AlgebraicGeometry.Space

end
