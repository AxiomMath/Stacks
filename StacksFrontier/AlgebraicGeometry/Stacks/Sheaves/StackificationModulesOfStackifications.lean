module

public import StacksCore.Tactic.StacksAttribute
public import StacksFrontier.AlgebraicGeometry.Stacks.Sheaves.StackificationModulesAnyUniverse
public import StacksFrontier.AlgebraicGeometry.Stacks.Sheaves.StackificationOfEquivalence

/-!
# Stackification and sheaves of modules (Stacks 06WR)

Let `f : 𝒳 ⥤ 𝒴` be a 1-morphism of categories fibred in groupoids over the big fppf category of
a scheme `S`.  Stacks 06WR asserts that if `f` induces an equivalence of stackifications, then
the inverse image `f^*` of Stacks 06WE is an equivalence `Mod(𝒪_𝒴) ⥤ Mod(𝒪_𝒳)` and restricts to
an equivalence `QCoh(𝒪_𝒴) ⥤ QCoh(𝒪_𝒳)`.

The two fibred categories have their objects in independent universes and their morphisms in a
common universe `w`, and the modules have their sections in any universe containing the universe
`u` of the rings of the big fppf site.

## Main results

Both are in the namespace `AlgebraicGeometry.Stack`.

* `isEquivalence_modulePullback_of_isStackification_of_isEquivalenceOver`:
  **Stacks 06WR, the `Mod` clause.**
* `isEquivalence_quasicoherentPullback_of_isStackification_of_isEquivalenceOver`:
  **Stacks 06WR, the `QCoh` clause.**

## Implementation notes

The hypothesis that `f` induces an equivalence of stackifications is stated with the
stackifications given: stackifications `G_𝒳 : 𝒳 ⥤ 𝒳'` and `G_𝒴 : 𝒴 ⥤ 𝒴'`
(`CategoryTheory.Functor.IsFibredOneMorphism.IsStackification`, the conclusion of Stacks 02ZN), a
1-morphism `f' : 𝒳' ⥤ 𝒴'` which is an equivalence over the base, and a vertical 2-isomorphism
`f ⋙ G_𝒴 ≅ G_𝒳 ⋙ f'`.  It implies the two local criteria of Stacks 02ZN for `f`
(`CategoryTheory.Functor.IsFibredOneMorphism.isStackificationEquivalence'_of_isEquivalenceOver`),
under which `StacksFrontier.AlgebraicGeometry.Stacks.Sheaves.StackificationModulesAnyUniverse`
proves both clauses.

## References

* [Stacks Project, Tag 06WR](https://stacks.math.columbia.edu/tag/06WR)
* [Stacks Project, Tag 06WQ](https://stacks.math.columbia.edu/tag/06WQ)
* [Stacks Project, Tag 02ZN](https://stacks.math.columbia.edu/tag/02ZN)
-/

@[expose] public section

open CategoryTheory

universe u v₁ v₂ w m u₃ u₄

namespace AlgebraicGeometry.Stack

variable {B : BigFppfSite.{u}} {S : Scheme.{u}} {hS : B.Contains S}
  {𝒳 : Type v₁} [Category.{w} 𝒳] {𝒴 : Type v₂} [Category.{w} 𝒴]
  {p : 𝒳 ⥤ BigFppfOver B S hS} {q : 𝒴 ⥤ BigFppfOver B S hS}
  (hp : p.IsFiberedInGroupoids) (hq : q.IsFiberedInGroupoids)
  {f : 𝒳 ⥤ 𝒴} (hF : p.IsFibredOneMorphism q f)

variable {𝒳' : Type u₃} [Category.{w} 𝒳'] {𝒴' : Type u₄} [Category.{w} 𝒴']
  {p' : 𝒳' ⥤ BigFppfOver B S hS} {q' : 𝒴' ⥤ BigFppfOver B S hS} [p'.IsFibered] [q'.IsFibered]
  {GX : 𝒳 ⥤ 𝒳'} {GY : 𝒴 ⥤ 𝒴'} {f' : 𝒳' ⥤ 𝒴'}

include hp hq hF in
/-- **Stacks 06WR, the `Mod` clause.**  Let `f : 𝒳 ⥤ 𝒴` be a 1-morphism of categories fibred in
groupoids over the big fppf category of `S`, and suppose `f` induces an equivalence of
stackifications: `G_𝒳 : 𝒳 ⥤ 𝒳'` and `G_𝒴 : 𝒴 ⥤ 𝒴'` are stackifications in the sense of
Stacks 02ZN, and the 1-morphism `f' : 𝒳' ⥤ 𝒴'` with a vertical 2-isomorphism
`f ⋙ G_𝒴 ≅ G_𝒳 ⋙ f'` is an equivalence over the base.  Then the inverse image of sheaves of
modules of Stacks 06WE is an equivalence `Mod(𝒪_𝒴) ⥤ Mod(𝒪_𝒳)`, for modules with sections in any
universe containing `u`.

The hypothesis gives the two local criteria of Stacks 02ZN for `f`
(`CategoryTheory.Functor.IsFibredOneMorphism.isStackificationEquivalence'_of_isEquivalenceOver`),
from which `isEquivalence_modulePullback_of_isStackificationEquivalence_anyUniverse`
concludes. -/
@[stacks 06WR "the Mod clause: f^* is an equivalence Mod(𝒪_𝒴) ⥤ Mod(𝒪_𝒳), for categories fibred \
in groupoids in arbitrary universes and modules in any universe containing that of the rings"]
theorem isEquivalence_modulePullback_of_isStackification_of_isEquivalenceOver
    {hGX : p.IsFibredOneMorphism p' GX} {hGY : q.IsFibredOneMorphism q' GY}
    (hGXs : letI : p.IsFibered := hp.isFibered
      hGX.IsStackification (BigFppfOver.topology B S hS))
    (hGYs : letI : q.IsFibered := hq.isFibered
      hGY.IsStackification (BigFppfOver.topology B S hS))
    (hf' : p'.IsFibredOneMorphism q' f') (hf'eq : Functor.IsEquivalenceOver p' q' f')
    (α : f ⋙ GY ≅ GX ⋙ f') (hα : ∀ a : 𝒳, q'.IsHomLift (𝟙 (p.obj a)) (α.hom.app a)) :
    (modulePullback.{u, v₁, w, max u m, v₂, w} B S hS p q hp hq f hF.comp_eq
      B.topology le_rfl).IsEquivalence :=
  letI : p.IsFibered := hp.isFibered
  letI : q.IsFibered := hq.isFibered
  isEquivalence_modulePullback_of_isStackificationEquivalence_anyUniverse.{u, v₁, v₂, w, m}
    (hp := hp) (hq := hq)
    (hF.isStackificationEquivalence'_of_isEquivalenceOver hf' hf'eq α hα hq hGXs hGYs)

include hp hq hF in
/-- **Stacks 06WR, the `QCoh` clause.**  Let `f : 𝒳 ⥤ 𝒴` be a 1-morphism of categories fibred in
groupoids over the big fppf category of `S`, and suppose `f` induces an equivalence of
stackifications: `G_𝒳 : 𝒳 ⥤ 𝒳'` and `G_𝒴 : 𝒴 ⥤ 𝒴'` are stackifications in the sense of
Stacks 02ZN, and the 1-morphism `f' : 𝒳' ⥤ 𝒴'` with a vertical 2-isomorphism
`f ⋙ G_𝒴 ≅ G_𝒳 ⋙ f'` is an equivalence over the base.  Then the inverse image of quasi-coherent
modules is an equivalence `QCoh(𝒪_𝒴) ⥤ QCoh(𝒪_𝒳)`, for modules with sections in any universe
containing `u`.

The hypothesis gives the two local criteria of Stacks 02ZN for `f`
(`CategoryTheory.Functor.IsFibredOneMorphism.isStackificationEquivalence'_of_isEquivalenceOver`),
from which
`isEquivalence_quasicoherentPullback_of_isStackificationEquivalence_anyUniverse`
concludes. -/
@[stacks 06WR "the QCoh clause: f^* is an equivalence QCoh(𝒪_𝒴) ⥤ QCoh(𝒪_𝒳), for categories \
fibred in groupoids in arbitrary universes and modules in any universe containing that of the \
rings"]
theorem isEquivalence_quasicoherentPullback_of_isStackification_of_isEquivalenceOver
    {hGX : p.IsFibredOneMorphism p' GX} {hGY : q.IsFibredOneMorphism q' GY}
    (hGXs : letI : p.IsFibered := hp.isFibered
      hGX.IsStackification (BigFppfOver.topology B S hS))
    (hGYs : letI : q.IsFibered := hq.isFibered
      hGY.IsStackification (BigFppfOver.topology B S hS))
    (hf' : p'.IsFibredOneMorphism q' f') (hf'eq : Functor.IsEquivalenceOver p' q' f')
    (α : f ⋙ GY ≅ GX ⋙ f') (hα : ∀ a : 𝒳, q'.IsHomLift (𝟙 (p.obj a)) (α.hom.app a)) :
    (quasicoherentPullback'.{u, v₁, w, max u m, v₂, w} B S hS p q hp hq f
      hF.comp_eq).IsEquivalence :=
  letI : p.IsFibered := hp.isFibered
  letI : q.IsFibered := hq.isFibered
  isEquivalence_quasicoherentPullback_of_isStackificationEquivalence_anyUniverse.{u, v₁, v₂, w, m}
    (hp := hp) (hq := hq)
    (hF.isStackificationEquivalence'_of_isEquivalenceOver hf' hf'eq α hα hq hGXs hGYs)

end AlgebraicGeometry.Stack

end
