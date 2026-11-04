module

public import StacksCore.Tactic.StacksAttribute
public import StacksFrontier.Algebra.Category.ModuleCat.Sheaf.DirectImage
public import StacksFrontier.AlgebraicGeometry.Stacks.Sheaves.Injectives

/-!
# Direct image preserves injective sheaves (Stacks 06WX)

Let `f : 𝒳 ⥤ 𝒴` be a 1-morphism of categories fibred in groupoids over the big fppf category
of a scheme `S`, and let `τ` be a topology on the underlying category of schemes. Each of `𝒳`
and `𝒴` carries the site it inherits from the localization of `τ` at `S` (Stacks 06TP), and `f`
induces a morphism of topoi between them (Stacks 06NW) whose inverse image `f⁻¹` is restriction
along `f` and whose direct image `f_*` is right Kan extension along `f.op`. When `τ` is coarser
than the fppf topology, `𝒳` and `𝒴` carry their structure sheaves `O_𝒳` and `O_𝒴`, and
`O_𝒳 = f⁻¹ O_𝒴`, so `f_*` carries `O_𝒳`-modules to `O_𝒴`-modules.

**Stacks 06WX** says that `f_*` carries injective abelian sheaves to injective abelian sheaves,
and injective `O_𝒳`-modules to injective `O_𝒴`-modules. Both follow from Homology, Lemma 015Z:
`f_*` has the exact left adjoint `f⁻¹`.

## Main results

* `AlgebraicGeometry.Stack.preservesInjectiveObjects_abelianDirectImage`: **Stacks 06WX (1)**,
  the direct image of abelian sheaves preserves injective objects.
* `AlgebraicGeometry.Stack.preservesInjectiveObjects_sheafOfModulesDirectImage`:
  **Stacks 06WX (2)**, the direct image of sheaves of modules preserves injective objects.

## Implementation notes

Both direct images are constructed, not assumed. On abelian sheaves `f_*` is
`CategoryTheory.Functor.sheafPushforwardCocontinuous`, whose value at an object `y` of `𝒴` is a
limit indexed by the pairs `(x, f x ⟶ y)`. Those pairs form a `Type (max v₁ w₂)` when `𝒳` has
objects in `Type v₁` and `𝒴` has morphisms in `Type w₂`, so the limits exist for abelian groups
in any universe containing both, and the coefficients are taken to be
`AddCommGrpCat.{max v₁ w₂ t}`. On sheaves of modules `f_*` is
`SheafOfModules.directImageOfEq`, whose sections over `y` are the compatible families of
sections indexed by the same pairs, again in modules over a universe containing `v₁` and `w₂`;
its underlying abelian sheaf is the abelian direct image, and it is right adjoint to
`SheafOfModules.pushforward` along the identification
`AlgebraicGeometry.Stack.ringStructureSheafCoreHom` of `O_𝒳` with `f⁻¹ O_𝒴`, which is the
inverse image of modules.

The source fixes `τ` among the Zariski, étale, smooth, syntomic and fppf topologies. Part (1)
holds for an arbitrary topology `τ` on the category of schemes and for a 1-morphism of fibred
categories, and part (2) for every `τ` coarser than the fppf topology, which is what makes
`O_𝒳` and `O_𝒴` sheaves; the five topologies of the source are among these.

## References

* [Stacks Project, Tag 06WX](https://stacks.math.columbia.edu/tag/06WX)
* [Stacks Project, Tag 015Z](https://stacks.math.columbia.edu/tag/015Z)
-/

@[expose] public section

open CategoryTheory

namespace AlgebraicGeometry.Stack

universe u v₁ v₂ w₁ w₂ t

variable (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)
  {𝒳 : Type v₁} [Category.{w₁} 𝒳] {𝒴 : Type v₂} [Category.{w₂} 𝒴]
  (p : 𝒳 ⥤ BigFppfOver B S hS) (q : 𝒴 ⥤ BigFppfOver B S hS) (F : 𝒳 ⥤ 𝒴)
  (τ : GrothendieckTopology B.Schemes)

/-- **Stacks 06WX, part (1).** Direct image along a 1-morphism of fibred categories over the
big fppf category of a scheme carries injective abelian sheaves to injective abelian sheaves,
for the site each side inherits from an arbitrary topology on the base. The direct image is the
right Kan extension along `F.op`, which exists for abelian groups in any universe containing
the objects of the source and the morphisms of the target. -/
@[stacks 06WX "part (1)"]
theorem preservesInjectiveObjects_abelianDirectImage
    [p.IsFibered] [q.IsFibered] (hF : p.IsFibredOneMorphism q F) :
    letI := (hF.isContinuous_and_isCocontinuous_inheritedTopology (τ.over (B.obj hS))).2
    (F.sheafPushforwardCocontinuous AddCommGrpCat.{max v₁ w₂ t}
      (associatedTopology B S hS p τ)
      (associatedTopology B S hS q τ)).PreservesInjectiveObjects :=
  preservesInjectiveObjects_sheafPushforwardCocontinuous.{u, v₁, v₂, w₁, w₂, max v₁ w₂ t}
    B S hS p q F τ hF

/-- The structure sheaf of the source of a 1-morphism of categories fibred in groupoids is
equal to the inverse image of the structure sheaf of the target: both are the structure
presheaf of the base restricted along the structure functor of the source. -/
theorem ringStructureSheafCore_eq_sheafPushforwardContinuous_obj
    (hp : p.IsFiberedInGroupoids) (hq : q.IsFiberedInGroupoids) (hcomp : F ⋙ q = p)
    (hτ : τ ≤ B.topology) :
    letI : p.IsFibered := hp.isFibered
    letI : q.IsFibered := hq.isFibered
    letI := ((hq.isFibredOneMorphism hcomp).isContinuous_and_isCocontinuous_inheritedTopology
      (τ.over (B.obj hS))).1
    ringStructureSheafCore B S hS p hp τ hτ =
      (F.sheafPushforwardContinuous RingCat.{u}
        (associatedTopology B S hS p τ) (associatedTopology B S hS q τ)).obj
        (ringStructureSheafCore B S hS q hq τ hτ) := by
  cases hcomp
  rfl

/-- **Stacks 06WX, part (2).** Direct image along a 1-morphism of categories fibred in
groupoids over the big fppf category of a scheme carries injective sheaves of
`O_𝒳`-modules to injective sheaves of `O_𝒴`-modules, for every topology coarser than the fppf
topology. The direct image is `SheafOfModules.directImageOfEq`, the right Kan extension along
`F.op` with its module structure, which is right adjoint to the inverse image of modules. -/
@[stacks 06WX "part (2)"]
theorem preservesInjectiveObjects_sheafOfModulesDirectImage
    (hp : p.IsFiberedInGroupoids) (hq : q.IsFiberedInGroupoids) (hcomp : F ⋙ q = p)
    (hτ : τ ≤ B.topology) :
    letI : p.IsFibered := hp.isFibered
    letI : q.IsFibered := hq.isFibered
    letI := ((hq.isFibredOneMorphism hcomp).isContinuous_and_isCocontinuous_inheritedTopology
      (τ.over (B.obj hS))).1
    letI := ((hq.isFibredOneMorphism hcomp).isContinuous_and_isCocontinuous_inheritedTopology
      (τ.over (B.obj hS))).2
    (SheafOfModules.directImageOfEq.{u, max v₁ w₂ t} F (associatedTopology B S hS p τ)
      (associatedTopology B S hS q τ) (ringStructureSheafCore B S hS q hq τ hτ)
      (ringStructureSheafCore_eq_sheafPushforwardContinuous_obj B S hS p q F τ hp hq hcomp
        hτ)).PreservesInjectiveObjects := by
  let : p.IsFibered := hp.isFibered
  let : q.IsFibered := hq.isFibered
  let := ((hq.isFibredOneMorphism hcomp).isContinuous_and_isCocontinuous_inheritedTopology
    (τ.over (B.obj hS))).1
  let := ((hq.isFibredOneMorphism hcomp).isContinuous_and_isCocontinuous_inheritedTopology
    (τ.over (B.obj hS))).2
  exact preservesInjectiveObjects_of_adjunction_sheafOfModules_pushforward.{u, v₁, v₂, w₁, w₂,
    max v₁ w₂ t} B S hS p q F τ hp hq hcomp hτ _
    (SheafOfModules.pushforwardDirectImageAdjunctionOfEq.{u, max v₁ w₂ t} F _ _ _
      (ringStructureSheafCore_eq_sheafPushforwardContinuous_obj B S hS p q F τ hp hq hcomp hτ))

end AlgebraicGeometry.Stack

end
