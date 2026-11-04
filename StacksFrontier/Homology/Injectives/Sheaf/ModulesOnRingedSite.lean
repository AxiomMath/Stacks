module

public import Mathlib.CategoryTheory.Abelian.GrothendieckAxioms.SheafOfModules
public import Mathlib.CategoryTheory.Abelian.GrothendieckCategory.EnoughInjectives
public import StacksFrontier.CategoryTheory.Preadditive.Injective.Basic
public import StacksFrontier.Algebra.Category.ModuleCat.Sheaf.Abelian
import StacksCore.Tactic.StacksAttribute

/-!
# Injectives in the category of sheaves of modules

Let `J` be a Grothendieck topology on a small category and let `O` be a sheaf of rings for
`J`. The category of sheaves of `O`-modules has enough injectives, and the embeddings can be
chosen functorially.

Both assertions come from the fact that sheaves of modules form a Grothendieck abelian
category. Enough injectives is then Mathlib's theorem for such categories. For the functorial
strengthening one uses, in addition, the functorial factorization of the monomorphisms by
their right lifting property: factoring the zero map `A ⟶ 0` functorially gives a
monomorphism `A ⟶ Z A`, and for a map whose target is a zero object the right lifting
property against all monomorphisms is exactly injectivity of `Z A`.

## Main definitions

No new definitions are introduced.

## Main results

* `Stacks.Injectives.sheafOfModules_hasFunctorialInjectiveEmbeddings`: sheaves of modules
  over a sheaf of rings on a site admit functorial injective embeddings.

## Implementation notes

Functorial injective embeddings are expressed by `HasFunctorialInjectiveEmbeddings`, which is
the stronger assertion of the source and in particular implies that the category has enough
injectives. The enough-injectives half is supplied directly by Mathlib's result for
Grothendieck abelian categories, registered against this tag rather than restated.

The construction of the embedding functor out of a functorial factorization uses nothing about
sheaves of modules, so it is carried out for an arbitrary abelian category admitting such a
factorization.

## References

* [Stacks Project, Tag 01DU](https://stacks.math.columbia.edu/tag/01DU)
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits CategoryTheory.MorphismProperty
open scoped ZeroObject

universe u v

add_to_stacks 01DU "enough injectives" CategoryTheory.IsGrothendieckAbelian.enoughInjectives
add_to_sga "3 I 5.3.1.1" "more general" CategoryTheory.IsGrothendieckAbelian.enoughInjectives
add_to_sga "4 I 7.13" CategoryTheory.IsGrothendieckAbelian.enoughInjectives
add_to_sga "4 V 0.1.1" CategoryTheory.IsGrothendieckAbelian.enoughInjectives
add_to_sga "4 V 0.2.1" CategoryTheory.IsGrothendieckAbelian.enoughInjectives
add_to_sga "4 V 2.5.2" "more general" CategoryTheory.IsGrothendieckAbelian.enoughInjectives

namespace Stacks.Injectives

/-- The functor sending an object to the zero map out of it, viewed as an arrow. -/
private noncomputable def zeroArrowFunctor (C : Type u) [Category.{v} C] [HasZeroObject C] :
    C ⥤ Arrow C where
  obj X := Arrow.mk ((isZero_zero C).from_ X)
  map f := Arrow.homMk f (𝟙 _) (by exact (isZero_zero C).eq_of_tgt _ _)
  map_id X := by apply Arrow.hom_ext <;> rfl
  map_comp f g := by apply Arrow.hom_ext <;> simp

/-- The candidate embedding functor: factor the zero map out of `X` functorially as
`X ⟶ Z X ⟶ 0`, and keep the first half. -/
private noncomputable def embeddingArrowFunctor (C : Type u) [Category.{v} C]
    [HasZeroObject C]
    [HasFunctorialFactorization (monomorphisms C) (monomorphisms C).rlp] : C ⥤ Arrow C := by
  let z := zeroArrowFunctor C
  let d := functorialFactorizationData (monomorphisms C) (monomorphisms C).rlp
  refine
    { obj X := Arrow.mk (d.i.app (z.obj X))
      map {X Y} f := Arrow.homMk (z.map f).left (d.Z.map (z.map f))
        (by simpa only [Arrow.leftFunc, Comma.fst, Arrow.mk_hom, Arrow.mk_left,
          Arrow.mk_right] using d.i.naturality (z.map f))
      map_id X := ?_
      map_comp f g := ?_ }
  all_goals apply Arrow.hom_ext <;> (simp; rfl)

/-- In an abelian category whose monomorphisms factor functorially through their right
lifting property, the injective embeddings can be chosen functorially: factor `A ⟶ 0`
as `A ⟶ Z A ⟶ 0`. The middle term has the right lifting property against all
monomorphisms relative to a map onto a zero object, which is exactly injectivity. -/
private theorem hasFunctorialInjectiveEmbeddings_of_functorialFactorization
    (C : Type u) [Category.{v} C] [Abelian C]
    [HasFunctorialFactorization (monomorphisms C) (monomorphisms C).rlp] :
    HasFunctorialInjectiveEmbeddings C :=
  ⟨embeddingArrowFunctor C,
    rfl,
    fun X => (functorialFactorizationData _ _).hi _,
    fun X => by
      let fac := (functorialFactorizationData
        (monomorphisms C) (monomorphisms _).rlp).factorizationData
        ((isZero_zero _).from_ X)
      show Injective fac.Z
      simpa only [injective_iff_rlp_monomorphisms_zero,
        (isZero_zero _).eq_of_tgt fac.p 0] using fac.hp⟩

/-- **Stacks Project, Tag 01DU.** The category of sheaves of modules over a sheaf of rings on
a site has functorial injective embeddings (and consequently enough injectives). -/
@[stacks 01DU]
theorem sheafOfModules_hasFunctorialInjectiveEmbeddings
    {C : Type u} [SmallCategory C] (J : GrothendieckTopology C)
    (O : Sheaf J RingCat.{u}) :
    HasFunctorialInjectiveEmbeddings (SheafOfModules.{u} O) := by
  let : IsGrothendieckAbelian.{u} (SheafOfModules.{u} O) := inferInstance
  exact hasFunctorialInjectiveEmbeddings_of_functorialFactorization _

end Stacks.Injectives
