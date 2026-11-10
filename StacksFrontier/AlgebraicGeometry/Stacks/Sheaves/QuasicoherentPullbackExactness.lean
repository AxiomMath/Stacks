module

public import Mathlib.CategoryTheory.Limits.ExactFunctor
public import StacksFrontier.AlgebraicGeometry.Stacks.Quasicoherent.BigSiteColimits.AffineSectionBaseChangeExit
public import StacksFrontier.AlgebraicGeometry.Stacks.Sheaves.StackificationModules

/-!
# Exactness of the pullback of quasi-coherent modules (Stacks 076X)

Let `f : 𝒳 ⥤ 𝒴` be a 1-morphism of categories fibred in groupoids over the big fppf category of
a scheme `S`. The inverse image of sheaves of modules of Stacks 06WE preserves quasi-coherence
by Stacks 06WH, hence restricts to a functor `f^* : QCoh(𝒪_𝒴) ⥤ QCoh(𝒪_𝒳)`, which is
`AlgebraicGeometry.Stack.quasicoherentPullback`. Stacks 076X asserts that this functor is exact
when `f` is flat, and right exact for every `f`. Here `f^*` is shown to preserve all small
colimits, hence to be right exact, and the inverse image of all sheaves of modules is shown to
be exact.

## Main results

* `AlgebraicGeometry.Stack.exactFunctor_modulePullback`: the inverse image of sheaves of modules
  along a 1-morphism of categories fibred in groupoids is an exact functor, together with its
  two halves `AlgebraicGeometry.Stack.preservesFiniteLimits_modulePullback` and
  `AlgebraicGeometry.Stack.preservesFiniteColimits_modulePullback`.
* `AlgebraicGeometry.Stack.preservesColimitsOfSize_quasicoherentPullback` and
  `AlgebraicGeometry.Stack.preservesFiniteColimits_quasicoherentPullback`: the inverse image of
  quasi-coherent modules preserves all small colimits, and in particular is right exact —
  **Stacks 076X, right exactness.**

## Implementation notes

For the quasi-coherent statements the two fibred categories are taken in `Type u` with morphisms
in `Type u`, the universe of the rings of the big fppf site, which is the universe
`AlgebraicGeometry.Stack.quasicoherentPullback` is available at and the one in which the
colimits of Stacks 06WV (4) are small. Every algebraic stack is essentially small in that
universe (`AlgebraicGeometry.Stack.essentiallySmall_obj_algebraicStack`). The results about the
inverse image of all sheaves of modules are stated at the universes of
`AlgebraicGeometry.Stack.modulePullback` itself, with no smallness assumed.

## References

* [Stacks Project, Tag 076X](https://stacks.math.columbia.edu/tag/076X)
* [Stacks Project, Tag 06WE](https://stacks.math.columbia.edu/tag/06WE)
* [Stacks Project, Tag 06WH](https://stacks.math.columbia.edu/tag/06WH)
* [Stacks Project, Tag 06WV](https://stacks.math.columbia.edu/tag/06WV)
-/

@[expose] public section

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits

universe u v w m v' w'

namespace AlgebraicGeometry.Stack

section ModulePullback

variable (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)
  {𝒳 : Type v} [Category.{w} 𝒳] {𝒴 : Type v'} [Category.{w'} 𝒴]
  (p : 𝒳 ⥤ BigFppfOver B S hS) (q : 𝒴 ⥤ BigFppfOver B S hS)
  (hp : p.IsFiberedInGroupoids) (hq : q.IsFiberedInGroupoids)
  (f : 𝒳 ⥤ 𝒴) (hf : f ⋙ q = p)
  (τ : GrothendieckTopology B.Schemes) (hτ : τ ≤ B.topology)

include hp hq hf

/-- The inverse image of sheaves of modules along a 1-morphism of categories fibred in groupoids
is left exact. -/
theorem preservesFiniteLimits_modulePullback :
    PreservesFiniteLimits
      (modulePullback.{u, v, w, m, v', w'} B S hS p q hp hq f hf τ hτ) := by
  let : p.IsFibered := hp.isFibered
  let : q.IsFibered := hq.isFibered
  let := ((hq.isFibredOneMorphism hf).isContinuous_and_isCocontinuous_inheritedTopology
    (τ.over (B.obj hS))).1
  exact inferInstanceAs (PreservesFiniteLimits (SheafOfModules.pushforward.{m}
    (F := f) (J := associatedTopology B S hS p τ) (K := associatedTopology B S hS q τ)
    ⟨eqToHom (ringStructureSheafCore_obj_eq B S hS p q hp hq f hf τ hτ)⟩))

/-- The inverse image of sheaves of modules along a 1-morphism of categories fibred in groupoids
is right exact. -/
theorem preservesFiniteColimits_modulePullback :
    PreservesFiniteColimits
      (modulePullback.{u, v, w, max u v w m v' w', v', w'} B S hS p q hp hq f hf τ hτ) :=
  have : (modulePullback.{u, v, w, max u v w m v' w', v', w'}
      B S hS p q hp hq f hf τ hτ).IsLeftAdjoint :=
    (moduleSheafAdjunction.{u, v, w, m, v', w'} B S hS p q hp hq f hf τ hτ).isLeftAdjoint
  inferInstance

/-- **The inverse image of sheaves of modules along a 1-morphism of categories fibred in
groupoids is an exact functor.** -/
theorem exactFunctor_modulePullback :
    exactFunctor
      (SheafOfModules.{max u v w m v' w'} (ringStructureSheafCore B S hS q hq τ hτ))
      (SheafOfModules.{max u v w m v' w'} (ringStructureSheafCore B S hS p hp τ hτ))
      (modulePullback.{u, v, w, max u v w m v' w', v', w'} B S hS p q hp hq f hf τ hτ) :=
  (exactFunctor_iff _).mpr
    ⟨preservesFiniteLimits_modulePullback.{u, v, w, max u v w m v' w', v', w'}
        B S hS p q hp hq f hf τ hτ,
      preservesFiniteColimits_modulePullback.{u, v, w, m, v', w'} B S hS p q hp hq f hf τ hτ⟩

end ModulePullback

section Quasicoherent

variable (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)
  {𝒳 : Type u} [Category.{u} 𝒳] {𝒴 : Type u} [Category.{u} 𝒴]
  (p : 𝒳 ⥤ BigFppfOver B S hS) (q : 𝒴 ⥤ BigFppfOver B S hS)
  (hp : p.IsFiberedInGroupoids) (hq : q.IsFiberedInGroupoids)
  (f : 𝒳 ⥤ 𝒴) (hF : p.IsFibredOneMorphism q f)

/-- The inverse image of quasi-coherent modules along a 1-morphism of categories fibred in
groupoids over the big fppf category of `S`, `f^* : QCoh(𝒪_𝒴) ⥤ QCoh(𝒪_𝒳)`, preserves all small
colimits. -/
theorem preservesColimitsOfSize_quasicoherentPullback :
    PreservesColimitsOfSize.{u, u} (quasicoherentPullback B S hS p q hp hq f hF) := by
  have hι : PreservesColimitsOfSize.{u, u}
      (SheafOfModules.isQuasicoherentOnSite.{u, u, u, u}
        (ringStructureSheafCore B S hS q hq B.topology le_rfl)).ι :=
    FibredSite.preservesColimitsOfSize_quasicoherentInclusion' B S hS q hq
  have hL : (modulePullback.{u, u, u, u, u, u} B S hS p q hp hq f hF.comp_eq
      B.topology le_rfl).IsLeftAdjoint :=
    (moduleSheafAdjunction.{u, u, u, u, u, u} B S hS p q hp hq f hF.comp_eq
      B.topology le_rfl).isLeftAdjoint
  have : PreservesColimitsOfSize.{u, u}
      (quasicoherentPullback B S hS p q hp hq f hF ⋙
        (SheafOfModules.isQuasicoherentOnSite.{u, u, u, u}
          (ringStructureSheafCore B S hS p hp B.topology le_rfl)).ι) := by
    change PreservesColimitsOfSize.{u, u}
      ((SheafOfModules.isQuasicoherentOnSite.{u, u, u, u}
          (ringStructureSheafCore B S hS q hq B.topology le_rfl)).ι ⋙
        modulePullback.{u, u, u, u, u, u} B S hS p q hp hq f hF.comp_eq B.topology le_rfl)
    infer_instance
  exact ⟨preservesColimitsOfShape_of_reflects_of_preserves _
    (SheafOfModules.isQuasicoherentOnSite.{u, u, u, u}
      (ringStructureSheafCore B S hS p hp B.topology le_rfl)).ι⟩

/-- The inverse image of quasi-coherent modules along a 1-morphism of categories fibred in
groupoids over the big fppf category of `S`, `f^* : QCoh(𝒪_𝒴) ⥤ QCoh(𝒪_𝒳)`, is right exact. -/
@[stacks 076X "right exactness"]
theorem preservesFiniteColimits_quasicoherentPullback :
    PreservesFiniteColimits (quasicoherentPullback B S hS p q hp hq f hF) :=
  have := preservesColimitsOfSize_quasicoherentPullback B S hS p q hp hq f hF
  PreservesColimitsOfSize.preservesFiniteColimits _

end Quasicoherent

end AlgebraicGeometry.Stack

end
