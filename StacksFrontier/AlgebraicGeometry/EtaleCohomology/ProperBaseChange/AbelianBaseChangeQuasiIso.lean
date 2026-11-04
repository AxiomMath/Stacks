module

public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.ProperBaseChange.AbelianBaseChangeResolution
public import StacksFrontier.Algebra.Homology.DerivedCategory.DerivedBaseChangeResolution

/-!
# The abelian base change comparison through an acyclic resolution, on complexes

Let
```
X' --g'--> X
|f'        |f
v          v
Y' --g---> Y
```
be a commutative square of schemes, `K` a bounded below complex of abelian sheaves on `X_étale`
with `f_*`-acyclic terms and `q : (g')^{-1} K ⟶ K'` a quasi-isomorphism onto a bounded below
complex with `f'_*`-acyclic terms. If the base change map `g^{-1} Rf_* K ⟶ Rf'_* (g')^{-1} K` is
invertible, then the morphism of complexes `g^{-1} f_* K ⟶ f'_* (g')^{-1} K ⟶ f'_* K'` is a
quasi-isomorphism.

## Main results

* `Stacks.EtaleCohomology.isIso_Q_map_etaleAbelianBaseChange_comp_of_quasiIso`: the morphism of
  complexes `g^{-1} f_* K ⟶ f'_* K'` is a quasi-isomorphism.

## References

* [Stacks Project, Tag 0DDE](https://stacks.math.columbia.edu/tag/0DDE)
* [Stacks Project, Tag 015E](https://stacks.math.columbia.edu/tag/015E)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits
open AlgebraicGeometry AlgebraicGeometry.Scheme

attribute [local instance] HasDerivedCategory.standard

universe u v

namespace Stacks.EtaleCohomology

section Abelian

variable {X X' Y Y' : Scheme.{u}} (f : X ⟶ Y) (g : Y' ⟶ Y) (g' : X' ⟶ X) (f' : X' ⟶ Y')
  (h : g' ≫ f = f' ≫ g)

attribute [local instance 10000] CategoryTheory.Abelian.toPreadditive
  Preadditive.preadditiveHasZeroMorphisms

/-- Let `K` be a bounded below complex with `f_*`-acyclic terms and `q : (g')^{-1} K ⟶ K'` a
quasi-isomorphism onto a bounded below complex with `f'_*`-acyclic terms. If the base change map
is invertible at `K`, then the morphism of complexes `g^{-1} f_* K ⟶ f'_* (g')^{-1} K ⟶ f'_* K'`
is an isomorphism in the derived category, i.e. a quasi-isomorphism. -/
theorem isIso_Q_map_etaleAbelianBaseChange_comp_of_quasiIso
    (K : CochainComplex (Sheaf X.smallEtaleTopology AddCommGrpCat.{max (u + 1) v}) ℤ)
    (hK : CochainComplex.plus (Sheaf X.smallEtaleTopology AddCommGrpCat.{max (u + 1) v}) K)
    (hac : ∀ n : ℤ, (etaleAbelianDirectImage.{u, v} f).rightAcyclic (K.X n))
    (K' : CochainComplex (Sheaf X'.smallEtaleTopology AddCommGrpCat.{max (u + 1) v}) ℤ)
    (hK' : CochainComplex.plus (Sheaf X'.smallEtaleTopology AddCommGrpCat.{max (u + 1) v}) K')
    (hac' : ∀ n : ℤ, (etaleAbelianDirectImage.{u, v} f').rightAcyclic (K'.X n))
    (q : ((etaleAbelianInverseImage.{u, v} g').mapHomologicalComplex (ComplexShape.up ℤ)).obj K ⟶
      K') [QuasiIso q]
    (hbc : IsIso ((etaleAbelianDerivedBaseChange.{u, v} f g g' f' h).app
      (DerivedCategory.Qh.obj ((HomotopyCategory.quotient
        (Sheaf X.smallEtaleTopology AddCommGrpCat.{max (u + 1) v}) (ComplexShape.up ℤ)).obj K)))) :
    IsIso (DerivedCategory.Q.map
      ((NatTrans.mapHomologicalComplex (etaleAbelianBaseChange.{u, v} f g g' f' h)
          (ComplexShape.up ℤ)).app K ≫
        ((etaleAbelianDirectImage.{u, v} f').mapHomologicalComplex (ComplexShape.up ℤ)).map q)) :=
  Stacks.Cohomology.DerivedBaseChangeResolution.isIso_Q_map_comp_of_isIso_derivedBaseChange
    (etaleAbelianDirectImage.{u, v} f) (etaleAbelianInverseImage.{u, v} g)
    (etaleAbelianInverseImage.{u, v} g') (etaleAbelianDirectImage.{u, v} f')
    (etaleAbelianBaseChange.{u, v} f g g' f' h)
    (etaleAbelianDerivedDirectImage.{u, v} f) (etaleAbelianDerivedDirectImage.{u, v} f')
    (etaleAbelianDerivedDirectImageUnit.{u, v} f) (etaleAbelianDerivedDirectImageUnit.{u, v} f')
    (etaleAbelianDerivedBaseChange.{u, v} f g g' f' h)
    (etaleAbelianHomotopyBaseChange.{u, v} f g g' f' h) K K' q
    (etaleAbelianHomotopyBaseChange_app_quotient_obj.{u, v} f g g' f' h K)
    (etaleAbelianDerivedBaseChange_fac.{u, v} f g g' f' h _)
    (isIso_etaleAbelianDerivedDirectImageUnit_app_of_plus_of_rightAcyclic.{u, v} f K hK hac)
    (isIso_etaleAbelianDerivedDirectImageUnit_app_of_plus_of_rightAcyclic.{u, v} f' K' hK' hac')
    hbc

end Abelian

end Stacks.EtaleCohomology

end
