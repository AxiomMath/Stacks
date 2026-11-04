module

public import StacksFrontier.CategoryTheory.Preadditive.Injective.Basic
public import StacksFrontier.Homology.Injectives.Sheaf.PresheavesOfModules
public import StacksCore.Tactic.StacksAttribute
public import Mathlib.CategoryTheory.Category.ULift

/-!
# Enough injectives for module-valued functors

Presheaves of modules over an arbitrary diagram of rings on an arbitrary category have enough
injectives. In particular the category of module-valued functors on the algebras admitted by a
big site has enough injectives, which is what makes higher Ext groups of adequate functors
available.

## Main results

* `AdequateFunctor.moduleValuedFunctor_enoughInjectives` — presheaves of modules over any ring
  diagram have enough injectives.

## Implementation notes

For the site-restricted category of algebras one takes the ring diagram
`AdequateFunctor.algebraRingDiagramOn (AdequateFunctor.siteAlgebraInclusion A P)`, so that
`AdequateFunctor.ModuleValuedFunctorOn` is the presheaf-of-modules category appearing here;
taking the unrestricted diagram instead recovers `AdequateFunctor.ModuleValuedFunctor`. The
value universe contains those of the indexing category and of its ring diagram, as in the
functorial injective embeddings of Tag 01DV, and the independent parameter `t` allows any
larger value universe. That theorem is applied after replacing the indexing category by an
`AsSmall` model in the common universe, transporting injective presentations across the
induced equivalence of presheaf categories.

## References

* [Stacks Project, Tag 06Z7](https://stacks.math.columbia.edu/tag/06Z7)
-/

@[expose] public section

open CategoryTheory

universe u v w t

namespace AdequateFunctor

/-- **Stacks Project, Tag 06Z7.** Module-valued functors on any category of algebras, in
particular the algebras admitted by a big site, have enough injectives. -/
@[stacks 06Z7 "module_valued_functors_enough_injectives"]
instance moduleValuedFunctor_enoughInjectives (C : Type u) [Category.{v} C]
    (R : Cᵒᵖ ⥤ RingCat.{w}) :
    EnoughInjectives (PresheafOfModules.{max u v w t} R) := by
  let e : C ≌ AsSmall.{max w t} C := AsSmall.equiv
  let E : PresheafOfModules.{max u v w t} (e.inverse.op ⋙ R) ≌
      PresheafOfModules.{max u v w t} R :=
    { functor := PresheafOfModules.pushforward₀ e.functor (e.inverse.op ⋙ R)
      inverse := PresheafOfModules.pushforward₀ e.inverse R
      unitIso := Iso.refl _
      counitIso := Iso.refl _ }
  have : EnoughInjectives (PresheafOfModules.{max u v w t} (e.inverse.op ⋙ R)) :=
    enoughInjectives_of_hasFunctorialInjectiveEmbeddings
      (𝒜 := PresheafOfModules.{max u v w t} (e.inverse.op ⋙ R))
      (Stacks.Injectives.presheafOfModules_hasFunctorialInjectiveEmbeddings
        (AsSmall.{max w t} C) (e.inverse.op ⋙ R))
  exact (Equivalence.enoughInjectives_iff E).mp inferInstance

end AdequateFunctor
