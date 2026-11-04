module

public import Mathlib.CategoryTheory.Adjunction.PartialAdjoint
public import StacksCore.Tactic.StacksAttribute
public import StacksFrontier.AlgebraicGeometry.Stacks.AssociatedSite
public import StacksFrontier.AlgebraicGeometry.Stacks.Sheaves.Representable
public import StacksFrontier.AlgebraicGeometry.Topologies.Fppf.FibreProducts
public import StacksFrontier.CategoryTheory.FiberedInGroupoids.TwoFibreProduct
public import StacksFrontier.CategoryTheory.Sites.CoverLifting
public import StacksFrontier.CategoryTheory.Sites.InheritedTopology.Functoriality
public import StacksFrontier.CategoryTheory.Sites.Localization.PushforwardAdjunction
public import StacksFrontier.CategoryTheory.Sites.MorphismOfSites.MorphismDefs

/-!
# The right adjoint of a representable morphism of categories fibred in groupoids

Let `F : 𝒳 ⥤ 𝒴` be a representable 1-morphism of categories fibred in groupoids over the big
fppf category of a scheme `S`. Then `F` has a right adjoint `u : 𝒴 ⥤ 𝒳`, and for each of the
five associated topologies of Stacks 06TP the functor `u` is continuous and defines a morphism
of sites `(𝒳, τ) ⟶ (𝒴, τ)`. The morphism of topoi it induces is the one induced by `F`.

Existence of the right adjoint is representability read through Stacks 06W7: the value of a
right adjoint at `y` is exactly a representing object for `x ↦ Hom(F x, y)`, so the partial
right adjoint of `F` is defined everywhere. Continuity of `u` is formal once `F` is known to be
cocontinuous, which is Stacks 06NW, and the morphism-of-sites condition then only needs a left
exact left adjoint of `u^s`, which is `F^s` by uniqueness of adjoints.

## Main results

* `AlgebraicGeometry.BigFppfOver.isLeftAdjoint_of_isRepresentableMorphism`: **Stacks 06W8**, a
  representable 1-morphism has a right adjoint.
* `AlgebraicGeometry.BigFppfOver.isContinuous_rightAdjoint`: **Stacks 06W8**, that right
  adjoint is continuous for the associated topologies.
* `AlgebraicGeometry.BigFppfOver.isMorphismOfSites_rightAdjoint`: **Stacks 06W8**, it defines a
  morphism of sites.

## Implementation notes

The source writes the right adjoint as a chosen functor `u`; here it is Mathlib's
`CategoryTheory.Functor.rightAdjoint`, available from the `Functor.IsLeftAdjoint` instance that
the first result produces, and determined up to canonical isomorphism by it.

The topology argument is an arbitrary Grothendieck topology on the underlying category of
schemes, as in `AlgebraicGeometry.Stack.associatedTopology`; the five statements of the source
are its values at the five big topologies.

The two remaining assertions of the source — that the presheaf-level direct image along `u` is
restriction along `u.op`, and that the direct image of the morphism of topoi attached to `u` is
the one attached to `F` — are already available in the stated generality and are registered
below rather than restated.

## References

* [Stacks Project, Tag 06W8](https://stacks.math.columbia.edu/tag/06W8)
* [Stacks Project, Tag 06W7](https://stacks.math.columbia.edu/tag/06W7)
-/

@[expose] public section

open CategoryTheory

namespace AlgebraicGeometry.BigFppfOver

universe u v

variable (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)
  {𝒳 𝒴 : Type v} [Category.{u + 1} 𝒳] [Category.{u + 1} 𝒴]
  (p𝒳 : 𝒳 ⥤ BigFppfOver B S hS) (p𝒴 : 𝒴 ⥤ BigFppfOver B S hS) (F : 𝒳 ⥤ 𝒴)

/-- A representable 1-morphism of categories fibred in groupoids over the big fppf category of
`S` has a right adjoint: its value at `y` is a representing object for the presheaf
`x ↦ Hom(F x, y)`, which exists by Stacks 06W7. -/
@[stacks 06W8 "existence of the right adjoint"]
theorem isLeftAdjoint_of_isRepresentableMorphism (hF : F ⋙ p𝒴 = p𝒳)
    (h𝒳 : p𝒳.IsFiberedInGroupoids) (h𝒴 : p𝒴.IsFiberedInGroupoids)
    (hrep : Stacks.RepresentableMorphism.IsRepresentableMorphism p𝒳 p𝒴 F) :
    F.IsLeftAdjoint := by
  apply Functor.isLeftAdjoint_of_rightAdjointObjIsDefined_eq_top
  ext y
  rw [Functor.rightAdjointObjIsDefined_iff]
  exact ⟨fun _ ↦ trivial, fun _ ↦
    (isRepresentableMorphism_iff_forall_isRepresentable B S hS p𝒳 p𝒴 F hF h𝒳 h𝒴).mp hrep y⟩

variable (hF : F ⋙ p𝒴 = p𝒳) (h𝒳 : p𝒳.IsFiberedInGroupoids) (h𝒴 : p𝒴.IsFiberedInGroupoids)
  (hrep : Stacks.RepresentableMorphism.IsRepresentableMorphism p𝒳 p𝒴 F)

include hF h𝒳 h𝒴 hrep

/-- The right adjoint of a representable 1-morphism is continuous for the topologies associated
(Stacks 06TP) to a topology `τ` on the underlying category of schemes: `F` is cocontinuous by
Stacks 06NW, and a right adjoint of a cocontinuous functor is continuous. -/
@[stacks 06W8 "continuity of the right adjoint"]
theorem isContinuous_rightAdjoint (τ : GrothendieckTopology B.Schemes) :
    letI : F.IsLeftAdjoint :=
      isLeftAdjoint_of_isRepresentableMorphism B S hS p𝒳 p𝒴 F hF h𝒳 h𝒴 hrep
    F.rightAdjoint.IsContinuous (Stack.associatedTopology B S hS p𝒴 τ)
      (Stack.associatedTopology B S hS p𝒳 τ) := by
  have : p𝒳.IsFibered := h𝒳.isFibered
  have : p𝒴.IsFibered := h𝒴.isFibered
  have : F.IsLeftAdjoint :=
    isLeftAdjoint_of_isRepresentableMorphism B S hS p𝒳 p𝒴 F hF h𝒳 h𝒴 hrep
  have : F.IsCocontinuous (Stack.associatedTopology B S hS p𝒳 τ)
      (Stack.associatedTopology B S hS p𝒴 τ) :=
    ((h𝒴.isFibredOneMorphism hF).isContinuous_and_isCocontinuous_inheritedTopology
      (τ.over (B.obj hS))).2
  exact (Adjunction.ofIsLeftAdjoint F).isContinuous_of_isCocontinuous _ _

/-- The right adjoint of a representable 1-morphism defines a morphism of sites from the
associated site of `𝒳` to that of `𝒴`: it is continuous, and the left exact left adjoint of its
pushforward on sheaves is the pushforward along `F`. -/
@[stacks 06W8 "the morphism of sites"]
theorem isMorphismOfSites_rightAdjoint (τ : GrothendieckTopology B.Schemes) :
    letI : F.IsLeftAdjoint :=
      isLeftAdjoint_of_isRepresentableMorphism B S hS p𝒳 p𝒴 F hF h𝒳 h𝒴 hrep
    IsMorphismOfSites.{u + 1} F.rightAdjoint (Stack.associatedTopology B S hS p𝒴 τ)
      (Stack.associatedTopology B S hS p𝒳 τ) := by
  have : p𝒳.IsFibered := h𝒳.isFibered
  have : p𝒴.IsFibered := h𝒴.isFibered
  have : F.IsLeftAdjoint :=
    isLeftAdjoint_of_isRepresentableMorphism B S hS p𝒳 p𝒴 F hF h𝒳 h𝒴 hrep
  have hFcart := h𝒴.isFibredOneMorphism hF
  have : F.IsContinuous (Stack.associatedTopology B S hS p𝒳 τ)
      (Stack.associatedTopology B S hS p𝒴 τ) :=
    (hFcart.isContinuous_and_isCocontinuous_inheritedTopology (τ.over (B.obj hS))).1
  have : F.rightAdjoint.IsContinuous (Stack.associatedTopology B S hS p𝒴 τ)
      (Stack.associatedTopology B S hS p𝒳 τ) :=
    isContinuous_rightAdjoint B S hS p𝒳 p𝒴 F hF h𝒳 h𝒴 hrep τ
  exact ⟨⟨F.sheafPushforwardContinuous (Type (u + 1)) _ _,
    ⟨(Adjunction.ofIsLeftAdjoint F).sheafPushforwardAdjunction (Type (u + 1))⟩,
    hFcart.preservesFiniteLimits_inverseImage (τ.over (B.obj hS)) (Type (u + 1))⟩⟩

/-! ### The remaining assertions of Stacks 06W8

The presheaf-level direct image along a right adjoint `u` of `F` is restriction along `u.op`
(so `(f_*ℱ)(y) = ℱ(u y)`), and the direct image of the morphism of topoi attached to `u` by
cocontinuity of `F` agrees with the pushforward attached to continuity of `u`. Both hold for an
arbitrary adjoint pair of functors of sites, so they are registered rather than restated. -/

add_to_stacks 06W8 "the presheaf direct image along the right adjoint is restriction"
  CategoryTheory.Functor.ranIsoRestrictionOfAdjunction

add_to_stacks 06W8 "agreement of the two direct images"
  CategoryTheory.Adjunction.sheafPushforwardCocontinuousIso

end AlgebraicGeometry.BigFppfOver

end
