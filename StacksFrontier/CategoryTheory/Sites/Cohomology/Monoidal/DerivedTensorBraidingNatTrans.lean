module

public import StacksFrontier.CategoryTheory.Sites.Cohomology.Monoidal.DerivedTensorReseatConstraints

/-!
# The commutativity constraint of the derived tensor product as a natural transformation

Let `(C, 𝒪)` be a ringed site.  The commutativity constraint of the symmetric monoidal derived
category of [Stacks, Tag 0FPT] is
`Stacks.SheafOfModules.DerivedMonoidal.canonicalBraidingHom`, the braiding of
`Stacks.SheafOfModules.DerivedMonoidal.canonicalDerivedSymmetric`.  This file packages it as a
single natural transformation

`- ⊗^𝐋_𝒪 - ⟶ swap ⋙ (- ⊗^𝐋_𝒪 -)`

of functors `D(𝒪) × D(𝒪) ⥤ D(𝒪)`, the derived tensor product being written uncurried.

## Main definitions

* `Stacks.SheafOfModules.DerivedMonoidal.canonicalBraidingNatTrans`: the commutativity constraint
  as a transformation of the uncurried derived tensor bifunctor into its composite with the swap
  of the two factors.

## Main results

* `Stacks.SheafOfModules.DerivedMonoidal.canonicalBraidingHom_naturality`: the commutativity
  constraint is natural in both derived modules, with the bifunctor written uncurried.

## Implementation notes

The components are `canonicalBraidingHom` and the naturality is
`CategoryTheory.BraidedCategory.braiding_naturality` for `canonicalDerivedSymmetric`; the
monoidal product of that structure is `Stacks.DerivedTensor.RingedSite.derivedTensorProductFunctor`
on the nose, since `Stacks.SheafOfModules.DerivedMonoidal.curriedTensor_canonicalDerivedMonoidal`
is an equality of bifunctors.

## References

* [Stacks Project, Tag 0FPT](https://stacks.math.columbia.edu/tag/0FPT)
* [Stacks Project, Tag 06YU](https://stacks.math.columbia.edu/tag/06YU)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits CategoryTheory.MonoidalCategory
open scoped CategoryTheory.Prod

universe d u

namespace Stacks.SheafOfModules.DerivedMonoidal

variable {C : Type u} [SmallCategory.{u} C] {J : GrothendieckTopology C}
  (R : Sheaf J CommRingCat.{u})
variable [HasSheafify J AddCommGrpCat.{u}]
  [J.WEqualsLocallyBijective AddCommGrpCat.{u}]
variable [HasDerivedCategory.{d} (Mod R)]

/-- The commutativity constraint `Stacks.SheafOfModules.DerivedMonoidal.canonicalBraidingHom` is
natural in both derived modules, with the derived tensor product written uncurried. -/
theorem canonicalBraidingHom_naturality {G G' H H' : DerivedModules R}
    (u : G ⟶ H) (v : G' ⟶ H') :
    (Functor.uncurry.obj
          (Stacks.DerivedTensor.RingedSite.derivedTensorProductFunctor R)).map (u ×ₘ v) ≫
        canonicalBraidingHom R H H' =
      canonicalBraidingHom R G G' ≫
        (Functor.uncurry.obj
          (Stacks.DerivedTensor.RingedSite.derivedTensorProductFunctor R)).map (v ×ₘ u) :=
  let := canonicalDerivedMonoidal R
  let := canonicalDerivedSymmetric R
  BraidedCategory.braiding_naturality u v

/-- The commutativity constraint of the derived tensor product as a natural transformation of the
uncurried derived tensor bifunctor into its composite with the swap of the two factors, with
components `Stacks.SheafOfModules.DerivedMonoidal.canonicalBraidingHom`. -/
def canonicalBraidingNatTrans :
    Functor.uncurry.obj (Stacks.DerivedTensor.RingedSite.derivedTensorProductFunctor R) ⟶
      CategoryTheory.Prod.swap _ _ ⋙
        Functor.uncurry.obj
          (Stacks.DerivedTensor.RingedSite.derivedTensorProductFunctor R) where
  app MN := canonicalBraidingHom R MN.1 MN.2
  naturality _ _ g := canonicalBraidingHom_naturality R g.1 g.2

/-- The components of `canonicalBraidingNatTrans` are `canonicalBraidingHom`. -/
theorem canonicalBraidingNatTrans_app (M N : DerivedModules R) :
    (canonicalBraidingNatTrans R).app (M, N) = canonicalBraidingHom R M N :=
  rfl

end Stacks.SheafOfModules.DerivedMonoidal

end
