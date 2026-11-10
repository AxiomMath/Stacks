module

public import StacksFrontier.AlgebraicGeometry.Simplicial.ComponentRingedTopos.ComponentPullbackRestriction
public import StacksFrontier.CategoryTheory.Sites.Cohomology.DerivedPullback.KFlatPullbackOfToposHom
public import StacksFrontier.CategoryTheory.Sites.Cohomology.DerivedPullback.KFlatTransport
public import StacksFrontier.CategoryTheory.Sites.Cohomology.DerivedPullback.PullbackTensorAlongASiteMorphism
public import StacksFrontier.CategoryTheory.Sites.Simplicial.ComponentSheafify
import StacksCore.Tactic.StacksAttribute

/-!
# Restriction to a simplicial component commutes with the total tensor complex

Let `S` be a simplicial-site situation, `O` a sheaf of commutative rings on its total site and
`g_n` the inclusion of the degree-`n` component. For cochain complexes `K`, `L` of `O`-modules
there is a comparison

`g_n^*Tot(K ⊗_O L) ≅ Tot(g_n^*K ⊗_{O_n} g_n^*L)`,

natural in `K` and in `L`, whose component on the summand of bidegree `(p, q)` is the comparison
`g_n^*(K^p ⊗_O L^q) ≅ g_n^*K^p ⊗_{O_n} g_n^*L^q` of **Stacks 03EL**. This is the complex-level
form, at `g_n`, of the derived comparison `Lg_n^*(A ⊗^L_O B) ≅ Lg_n^*A ⊗^L_{O_n} Lg_n^*B` of Stacks
07A4.

## Main definitions

* `CategoryTheory.SimplicialSiteSituation.componentModulesRestrictionComplex`: degreewise
  restriction of cochain complexes of modules to a component.
* `CategoryTheory.SimplicialSiteSituation.componentPullbackComplexRestrictionIso`: Stacks 0D72 on
  cochain complexes — degreewise pullback along `g_n` is degreewise restriction.
* `CategoryTheory.SimplicialSiteSituation.componentRestrictionTensorTotalIso`: the comparison
  displayed above.

## Main results

* `CategoryTheory.SimplicialSiteSituation.componentRestrictionTensorTotalIso_hom_naturality`: the
  comparison is natural in the pair of complexes.
* `CategoryTheory.SimplicialSiteSituation.isFlat_componentModulesRestrictionComplex_X` and
  `kFlat_componentModulesRestrictionComplex`: **Stacks 0G7E at `g_n`** — the restriction of a
  K-flat complex with flat terms is a K-flat complex with flat terms.

## Implementation notes

Restriction to a component is not a pullback along a morphism of sites: `g_n` is the geometric
morphism `CategoryTheory.SimplicialSiteSituation.componentMorphism` of Stacks 09WG, and the
comparisons are those for the morphism of ringed topoi
`CategoryTheory.SimplicialSiteSituation.componentRingedToposHom`, transported along
`CategoryTheory.SimplicialSiteSituation.componentPullbackModulesRestrictionIso`, the identification
of `g_n^*` with restriction.

## References

* [Stacks Project, Tag 03EL](https://stacks.math.columbia.edu/tag/03EL)
* [Stacks Project, Tag 07A4](https://stacks.math.columbia.edu/tag/07A4)
* [Stacks Project, Tag 0G7E](https://stacks.math.columbia.edu/tag/0G7E)
* [Stacks Project, Tag 0D72](https://stacks.math.columbia.edu/tag/0D72)
* [Stacks Project, Tag 09WG](https://stacks.math.columbia.edu/tag/09WG)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry
open Stacks.Sheaves.RingedToposModules

universe u

namespace CategoryTheory.SimplicialSiteSituation

attribute [local instance] hasWeakSheafifyComponent hasSheafifyTotal
  GrothendieckTopology.hasSheafify_addCommGrpCat

variable (S : SimplicialSiteSituation.{u}) (O : Sheaf S.totalTopology CommRingCat.{u})
  (n : SimplexCategory)

/-- Degreewise restriction of cochain complexes of sheaves of modules to the degree-`n`
component. -/
abbrev componentModulesRestrictionComplex :
    CochainComplex (S.totalRingedTopos O).Modules ℤ ⥤
      CochainComplex (S.componentRingedTopos O n).Modules ℤ :=
  (S.componentModulesRestriction O n).mapHomologicalComplex (ComplexShape.up ℤ)

/-- **Stacks 0D72 on cochain complexes.** Degreewise pullback of complexes of modules along the
component morphism of ringed topoi is degreewise restriction to the component. -/
@[stacks 0D72 "degreewise pullback of complexes along g_n is degreewise restriction"]
def componentPullbackComplexRestrictionIso :
    Stacks.Sheaves.DerivedPullback.pullbackComplexFunctor
        (X := S.componentRingedTopos O n) (Y := S.totalRingedTopos O)
        (componentRingedToposHom S O n).toModulesHom ≅
      S.componentModulesRestrictionComplex O n :=
  NatIso.mapHomologicalComplex (componentPullbackModulesRestrictionIso S O n)
    (ComplexShape.up ℤ)

/-- **Stacks 03EL on total complexes, at the component inclusion.** Restriction to the degree-`n`
component commutes with the total tensor complex:
`g_n^*Tot(K ⊗_O L) ≅ Tot(g_n^*K ⊗_{O_n} g_n^*L)`, the comparison on the summand of bidegree
`(p, q)` being `g_n^*(K^p ⊗_O L^q) ≅ g_n^*K^p ⊗_{O_n} g_n^*L^q`. -/
@[stacks 03EL "on total complexes, for restriction to a simplicial component"]
def componentRestrictionTensorTotalIso
    (K L : CochainComplex (S.totalRingedTopos O).Modules ℤ) :
    (S.componentModulesRestrictionComplex O n).obj
        (HomologicalComplex.mapBifunctor K L
          (Stacks.SheafOfModules.Tensor.sheafTensor (S.totalRingedTopos O).O)
          (ComplexShape.up ℤ)) ≅
      HomologicalComplex.mapBifunctor ((S.componentModulesRestrictionComplex O n).obj K)
        ((S.componentModulesRestrictionComplex O n).obj L)
        (Stacks.SheafOfModules.Tensor.sheafTensor (S.componentRingedTopos O n).O)
        (ComplexShape.up ℤ) :=
  ((componentPullbackComplexRestrictionIso S O n).app
      (HomologicalComplex.mapBifunctor K L
        (Stacks.SheafOfModules.Tensor.sheafTensor (S.totalRingedTopos O).O)
        (ComplexShape.up ℤ))).symm ≪≫
    Stacks.Sheaves.DerivedPullback.pullbackTensorTotalIso
      (X := S.componentRingedTopos O n) (Y := S.totalRingedTopos O)
      (componentRingedToposHom S O n).toModulesHom K L ≪≫
    Stacks.Sheaves.DerivedPullback.mapBifunctorMapIso
      (Stacks.SheafOfModules.Tensor.sheafTensor (S.componentRingedTopos O n).O)
      ((componentPullbackComplexRestrictionIso S O n).app K)
      ((componentPullbackComplexRestrictionIso S O n).app L)

/-- The second and third isomorphisms of
`CategoryTheory.SimplicialSiteSituation.componentRestrictionTensorTotalIso` compose to a square
natural in the pair of complexes: the comparison of Stacks 03EL for the pullback presentation,
followed by the identification of the pullback with restriction in each tensor factor. -/
private lemma componentRestrictionTensorTotalIso_hom_naturality_aux
    {K K' L L' : CochainComplex (S.totalRingedTopos O).Modules ℤ} (a : K ⟶ K') (b : L ⟶ L') :
    (Stacks.Sheaves.DerivedPullback.pullbackComplexFunctor
            (X := S.componentRingedTopos O n) (Y := S.totalRingedTopos O)
            (componentRingedToposHom S O n).toModulesHom).map
          (HomologicalComplex.mapBifunctorMap a b
            (Stacks.SheafOfModules.Tensor.sheafTensor (S.totalRingedTopos O).O)
            (ComplexShape.up ℤ)) ≫
        (Stacks.Sheaves.DerivedPullback.pullbackTensorTotalIso
            (X := S.componentRingedTopos O n) (Y := S.totalRingedTopos O)
            (componentRingedToposHom S O n).toModulesHom K' L' ≪≫
          Stacks.Sheaves.DerivedPullback.mapBifunctorMapIso
            (Stacks.SheafOfModules.Tensor.sheafTensor (S.componentRingedTopos O n).O)
            ((componentPullbackComplexRestrictionIso S O n).app K')
            ((componentPullbackComplexRestrictionIso S O n).app L')).hom =
      (Stacks.Sheaves.DerivedPullback.pullbackTensorTotalIso
            (X := S.componentRingedTopos O n) (Y := S.totalRingedTopos O)
            (componentRingedToposHom S O n).toModulesHom K L ≪≫
          Stacks.Sheaves.DerivedPullback.mapBifunctorMapIso
            (Stacks.SheafOfModules.Tensor.sheafTensor (S.componentRingedTopos O n).O)
            ((componentPullbackComplexRestrictionIso S O n).app K)
            ((componentPullbackComplexRestrictionIso S O n).app L)).hom ≫
        HomologicalComplex.mapBifunctorMap ((S.componentModulesRestrictionComplex O n).map a)
          ((S.componentModulesRestrictionComplex O n).map b)
          (Stacks.SheafOfModules.Tensor.sheafTensor (S.componentRingedTopos O n).O)
          (ComplexShape.up ℤ) :=
  Stacks.Sheaves.DerivedPullback.trans_naturality
    (Stacks.Sheaves.DerivedPullback.pullbackTensorTotalIso_hom_naturality
      (X := S.componentRingedTopos O n) (Y := S.totalRingedTopos O)
      (componentRingedToposHom S O n).toModulesHom a b)
    (Stacks.Sheaves.DerivedPullback.mapBifunctorMapIso_naturality
      (Stacks.SheafOfModules.Tensor.sheafTensor (S.componentRingedTopos O n).O)
      ((componentPullbackComplexRestrictionIso S O n).app K)
      ((componentPullbackComplexRestrictionIso S O n).app L)
      ((componentPullbackComplexRestrictionIso S O n).app K')
      ((componentPullbackComplexRestrictionIso S O n).app L')
      ((Stacks.Sheaves.DerivedPullback.pullbackComplexFunctor
        (X := S.componentRingedTopos O n) (Y := S.totalRingedTopos O)
        (componentRingedToposHom S O n).toModulesHom).map a)
      ((Stacks.Sheaves.DerivedPullback.pullbackComplexFunctor
        (X := S.componentRingedTopos O n) (Y := S.totalRingedTopos O)
        (componentRingedToposHom S O n).toModulesHom).map b)
      ((S.componentModulesRestrictionComplex O n).map a)
      ((S.componentModulesRestrictionComplex O n).map b)
      ((componentPullbackComplexRestrictionIso S O n).hom.naturality a)
      ((componentPullbackComplexRestrictionIso S O n).hom.naturality b))

/-- **The comparison of total tensor complexes for restriction to a component is natural in the
pair of complexes.** -/
lemma componentRestrictionTensorTotalIso_hom_naturality
    {K K' L L' : CochainComplex (S.totalRingedTopos O).Modules ℤ} (a : K ⟶ K') (b : L ⟶ L') :
    (S.componentModulesRestrictionComplex O n).map (HomologicalComplex.mapBifunctorMap a b
          (Stacks.SheafOfModules.Tensor.sheafTensor (S.totalRingedTopos O).O)
          (ComplexShape.up ℤ)) ≫
        (S.componentRestrictionTensorTotalIso O n K' L').hom =
      (S.componentRestrictionTensorTotalIso O n K L).hom ≫
        HomologicalComplex.mapBifunctorMap ((S.componentModulesRestrictionComplex O n).map a)
          ((S.componentModulesRestrictionComplex O n).map b)
          (Stacks.SheafOfModules.Tensor.sheafTensor (S.componentRingedTopos O n).O)
          (ComplexShape.up ℤ) :=
  Stacks.Sheaves.DerivedPullback.trans_naturality
    ((componentPullbackComplexRestrictionIso S O n).inv.naturality
      (HomologicalComplex.mapBifunctorMap a b
        (Stacks.SheafOfModules.Tensor.sheafTensor (S.totalRingedTopos O).O)
        (ComplexShape.up ℤ)))
    (componentRestrictionTensorTotalIso_hom_naturality_aux S O n a b)

/-! ### Stacks 0G7E at the component inclusion -/

/-- **The flat-terms clause of Stacks 0G7E at `g_n`.** The restriction to a component of a
complex of `O`-modules with flat terms has flat terms. -/
@[stacks 0G7E "the flat-terms clause, for restriction to a simplicial component"]
theorem isFlat_componentModulesRestrictionComplex_X
    (K : CochainComplex (S.totalRingedTopos O).Modules ℤ)
    (hflatK : ∀ i : ℤ, AlgebraicGeometry.SheafOfModules.IsFlat.{u, u, u, u}
      (O := (S.totalRingedTopos O).O) (K.X i)) (i : ℤ) :
    AlgebraicGeometry.SheafOfModules.IsFlat.{u, u, u, u}
      (O := (S.componentRingedTopos O n).O)
      (((S.componentModulesRestrictionComplex O n).obj K).X i) :=
  Stacks.Sheaves.DerivedPullback.KFlatTransport.isFlat_X_of_iso
    ((componentPullbackComplexRestrictionIso S O n).app K)
    (Stacks.Sheaves.DerivedPullback.KFlatPullbackOfToposHom.isFlat_pullbackComplex_X
      (componentRingedToposHom S O n) K hflatK) i

/-- **The K-flatness clause of Stacks 0G7E at `g_n`.** The restriction to a component of a
K-flat complex of `O`-modules with flat terms is K-flat. -/
@[stacks 0G7E "the K-flatness clause, for restriction to a simplicial component"]
theorem kFlat_componentModulesRestrictionComplex
    (K : CochainComplex (S.totalRingedTopos O).Modules ℤ)
    (hK : Stacks.SheafOfModules.KFlat (S.totalRingedTopos O).O K)
    (hflatK : ∀ i : ℤ, AlgebraicGeometry.SheafOfModules.IsFlat.{u, u, u, u}
      (O := (S.totalRingedTopos O).O) (K.X i)) :
    Stacks.SheafOfModules.KFlat (S.componentRingedTopos O n).O
      ((S.componentModulesRestrictionComplex O n).obj K) :=
  CochainComplex.KFlatBifunctor.KFlat.of_iso _
    (Stacks.Sheaves.DerivedPullback.KFlatPullbackOfToposHom.kFlat_pullbackComplex
      (componentRingedToposHom S O n) K hK hflatK)
    ((componentPullbackComplexRestrictionIso S O n).app K)

end CategoryTheory.SimplicialSiteSituation

end
