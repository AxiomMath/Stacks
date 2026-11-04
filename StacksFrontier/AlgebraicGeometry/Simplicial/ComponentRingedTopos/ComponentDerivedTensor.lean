module

public import StacksFrontier.AlgebraicGeometry.Simplicial.ComponentRingedTopos.ComponentTensorComplex
public import StacksFrontier.AlgebraicGeometry.Simplicial.ComponentRingedTopos.DerivedModuleSystemOfObject
public import StacksFrontier.CategoryTheory.Sites.Cohomology.DerivedTensor.ExactFunctorDerivedTensor
import StacksCore.Tactic.StacksAttribute

/-!
# The derived monoidal comparison for the component inverse image

Let `S` be a simplicial-site situation, `O` a sheaf of commutative rings on its total site and
`g_n` the inclusion of the degree-`n` component. This file states

`Lg_n^*(A ⊗^L_O B) ≅ Lg_n^*A ⊗^L_{O_n} Lg_n^*B`

for `A, B ∈ D(O)`, as an isomorphism of the two uncurried bifunctors on `D(O) × D(O)`, so that
naturality in both variables is part of its type. This is **Stacks 07A4** at `g_n`.

## Main definitions

* `CategoryTheory.SimplicialSiteSituation.componentDerivedTensorIso`: the comparison displayed
  above.

## Main results

* `CategoryTheory.SimplicialSiteSituation.componentDerivedTensorIso_hom_app_model`: its value at
  a pair of K-flat complexes with flat terms, which is where it has a formula.

## Implementation notes

*Why Stacks 07A4 is not simply instantiated.*
`Stacks.Sheaves.DerivedPullback.derivedPullbackTensorIso` is 07A4 for an
`AlgebraicGeometry.RingedToposSiteHom` together with a
`CategoryTheory.Functor.IsMorphismOfSites` hypothesis, i.e. for a morphism of ringed topoi
presented by a *continuous functor of the underlying sites in the opposite direction*. The
component inclusion `componentFunctor S n : 𝒞_n ⥤ 𝒞_total` points at the source and is continuous
*and* cocontinuous; `g_n` is the geometric morphism
`CategoryTheory.SimplicialSiteSituation.componentMorphism` of Stacks 09WG built from that
cocontinuity, and `componentRingedToposHom` is accordingly an `AlgebraicGeometry.RingedToposHom`
with no functor of sites inside it. There is no functor `𝒞_total ⥤ 𝒞_n` to supply, so 07A4 in that
form has no instance at `g_n` at all.

*What is used instead.* `Stacks.DerivedTensor.ExactFunctorTensor.derivedTensorIso` runs the
source's argument for any *exact* functor of sheaves of modules which preserves K-flatness of
complexes with flat terms and commutes with the total tensor complex. Restriction to a component
is exact, and the other two inputs are
`CategoryTheory.SimplicialSiteSituation.kFlat_componentModulesRestrictionComplex` (Stacks 0G7E at
`g_n`) and `CategoryTheory.SimplicialSiteSituation.componentRestrictionTensorTotalIso` with its
naturality (Stacks 03EL on total complexes at `g_n`).

*The derived functor is the same one the consumers use.*
`CategoryTheory.SimplicialSiteSituation.derivedComponentModuleRestriction` is by definition
`CategoryTheory.Functor.mapDerivedCategory` of `componentModulesRestriction`, which is the functor
the general statement is about, so the conclusion is stated directly in terms of it rather than
transported.

## References

* [Stacks Project, Tag 07A4](https://stacks.math.columbia.edu/tag/07A4)
* [Stacks Project, Tag 06YU](https://stacks.math.columbia.edu/tag/06YU)
* [Stacks Project, Tag 0G7E](https://stacks.math.columbia.edu/tag/0G7E)
* [Stacks Project, Tag 03EL](https://stacks.math.columbia.edu/tag/03EL)
* [Stacks Project, Tag 0D72](https://stacks.math.columbia.edu/tag/0D72)
* [Stacks Project, Tag 09WG](https://stacks.math.columbia.edu/tag/09WG)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry

universe u

namespace CategoryTheory.SimplicialSiteSituation

attribute [local instance] HasDerivedCategory.standard hasWeakSheafifyComponent hasSheafifyTotal
  GrothendieckTopology.hasSheafify_addCommGrpCat

variable (S : SimplicialSiteSituation.{u}) (O : Sheaf S.totalTopology CommRingCat.{u})
  (n : SimplexCategory)

/-- **The derived tensor comparison at the inclusion of a simplicial component.** The canonical
bifunctorial isomorphism

`g_n^*(A ⊗^L_O B) ≅ g_n^*A ⊗^L_{O_n} g_n^*B`

for the derived restriction `Lg_n^*` of sheaves of modules to the degree-`n` component of a
simplicial-site situation, stated between the two uncurried bifunctors on `D(O) × D(O)`, so that
naturality in both variables is part of its type.

Its value on a pair of K-flat complexes with flat terms is
`Stacks.DerivedTensor.ExactFunctorTensor.modelIso`, and the passage to arbitrary objects of `D(O)`
is the descent of that value along the localization of pairs of models. -/
@[stacks 07A4 "the canonical bifunctorial isomorphism, for the component inverse image"]
def componentDerivedTensorIso :
    Functor.uncurry.obj (Stacks.DerivedTensor.RingedSite.derivedTensorProductFunctor
          (S.totalRingedTopos O).O) ⋙
        S.derivedComponentModuleRestriction O n ≅
      (S.derivedComponentModuleRestriction O n).prod
          (S.derivedComponentModuleRestriction O n) ⋙
        Functor.uncurry.obj (Stacks.DerivedTensor.RingedSite.derivedTensorProductFunctor
          (S.componentRingedTopos O n).O) :=
  Stacks.DerivedTensor.ExactFunctorTensor.derivedTensorIso
    (X := S.componentRingedTopos O n) (Y := S.totalRingedTopos O)
    (S.componentModulesRestriction O n)
    (fun K hK hflatK => S.kFlat_componentModulesRestrictionComplex O n K hK hflatK)
    (fun K L => S.componentRestrictionTensorTotalIso O n K L)
    (fun a b => S.componentRestrictionTensorTotalIso_hom_naturality O n a b)

/-- **The comparison at a pair of K-flat complexes with flat terms.** Everything proved about
`CategoryTheory.SimplicialSiteSituation.componentDerivedTensorIso` beyond its bifunctoriality is
proved here: it is `Localization.liftNatIso` of a value defined on models, so at a general pair of
objects of `D(O)` neither side has a formula. -/
lemma componentDerivedTensorIso_hom_app_model
    (P N : CochainComplex (S.totalRingedTopos O).Modules ℤ)
    (hP : CochainComplex.KFlatBifunctor.KFlat
      (Stacks.SheafOfModules.Tensor.sheafTensor (S.totalRingedTopos O).O) P)
    (hN : CochainComplex.KFlatBifunctor.KFlat
      (Stacks.SheafOfModules.Tensor.sheafTensor (S.totalRingedTopos O).O) N)
    (hflatP : ∀ i : ℤ, AlgebraicGeometry.SheafOfModules.IsFlat.{u, u, u, u}
      (O := (S.totalRingedTopos O).O) (P.X i))
    (hflatN : ∀ i : ℤ, AlgebraicGeometry.SheafOfModules.IsFlat.{u, u, u, u}
      (O := (S.totalRingedTopos O).O) (N.X i)) :
    (S.componentDerivedTensorIso O n).hom.app
        (DerivedCategory.Q.obj P, DerivedCategory.Q.obj N) =
      (Stacks.DerivedTensor.ExactFunctorTensor.modelIso
        (X := S.componentRingedTopos O n) (Y := S.totalRingedTopos O)
        (S.componentModulesRestriction O n)
        (fun K hK hflatK => S.kFlat_componentModulesRestrictionComplex O n K hK hflatK)
        (fun K L => S.componentRestrictionTensorTotalIso O n K L)
        P N hP hN hflatP hflatN).hom :=
  Stacks.DerivedTensor.ExactFunctorTensor.derivedTensorIso_hom_app_model
    (X := S.componentRingedTopos O n) (Y := S.totalRingedTopos O)
    (S.componentModulesRestriction O n)
    (fun K hK hflatK => S.kFlat_componentModulesRestrictionComplex O n K hK hflatK)
    (fun K L => S.componentRestrictionTensorTotalIso O n K L)
    (fun a b => S.componentRestrictionTensorTotalIso_hom_naturality O n a b)
    P N hP hN hflatP hflatN

end CategoryTheory.SimplicialSiteSituation

end
