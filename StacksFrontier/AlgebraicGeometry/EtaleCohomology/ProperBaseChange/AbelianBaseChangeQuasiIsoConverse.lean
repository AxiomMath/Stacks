module

public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.ProperBaseChange.AbelianBaseChangeResolution
public import StacksFrontier.Algebra.Homology.DerivedCategory.DerivedBaseChangeResolutionConverse

/-!
# The abelian base change map is invertible where its degreewise comparison is a quasi-isomorphism

This is the converse of
`Stacks.EtaleCohomology.isIso_Q_map_etaleAbelianBaseChange_comp_of_quasiIso`
(`StacksFrontier/AlgebraicGeometry/EtaleCohomology/ProperBaseChange/AbelianBaseChangeQuasiIso.lean`)
: for a bounded below complex `K` of
abelian sheaves on `X_étale` with `f_*`-acyclic terms and a quasi-isomorphism
`q : (g')^{-1} K ⟶ K'` onto a bounded below complex with `f'_*`-acyclic terms, the base change map
`g^{-1} Rf_* K ⟶ Rf'_* (g')^{-1} K` is invertible as soon as the morphism of complexes
`g^{-1} f_* K ⟶ f'_* (g')^{-1} K ⟶ f'_* K'` is a quasi-isomorphism. It is
`Stacks.Cohomology.DerivedBaseChangeResolution.isIso_derivedBaseChange_of_isIso_Q_map_comp` for
the étale direct and inverse images.

## Implementation notes

As for the original, the statement carries the spelling of
`StacksFrontier/AlgebraicGeometry/EtaleCohomology/ProperBaseChange/BaseChangeMap.lean`
and the module has few imports, so that the kernel checks
the instantiation within its budget.

## Main results

* `Stacks.EtaleCohomology.isIso_etaleAbelianDerivedBaseChange_of_isIso_Q_map_comp`.
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

/- The base change map and its characterization
(`StacksFrontier/AlgebraicGeometry/EtaleCohomology/ProperBaseChange/BaseChangeMap.lean`) are
stated with `CategoryTheory.Abelian.toPreadditive` as the preferred `Preadditive` structure on
categories of abelian sheaves; the statement below carries the same spelling, so that the
abstract lemma is instantiated by them without conversions the kernel cannot afford. -/
attribute [local instance 10000] CategoryTheory.Abelian.toPreadditive
  Preadditive.preadditiveHasZeroMorphisms

/-- **The abelian base change map is invertible where the degreewise comparison through an
acyclic resolution is a quasi-isomorphism.** For a bounded below complex `K` with `f_*`-acyclic
terms and a quasi-isomorphism `q : (g')^{-1} K ⟶ K'` onto a bounded below complex with
`f'_*`-acyclic terms, if `g^{-1} f_* K ⟶ f'_* (g')^{-1} K ⟶ f'_* K'` is an isomorphism of the
derived category, then so is the base change map at `K`. -/
theorem isIso_etaleAbelianDerivedBaseChange_of_isIso_Q_map_comp
    (K : CochainComplex (Sheaf X.smallEtaleTopology AddCommGrpCat.{max (u + 1) v}) ℤ)
    (hK : CochainComplex.plus (Sheaf X.smallEtaleTopology AddCommGrpCat.{max (u + 1) v}) K)
    (hac : ∀ n : ℤ, (etaleAbelianDirectImage.{u, v} f).rightAcyclic (K.X n))
    (K' : CochainComplex (Sheaf X'.smallEtaleTopology AddCommGrpCat.{max (u + 1) v}) ℤ)
    (hK' : CochainComplex.plus (Sheaf X'.smallEtaleTopology AddCommGrpCat.{max (u + 1) v}) K')
    (hac' : ∀ n : ℤ, (etaleAbelianDirectImage.{u, v} f').rightAcyclic (K'.X n))
    (q : ((etaleAbelianInverseImage.{u, v} g').mapHomologicalComplex (ComplexShape.up ℤ)).obj K ⟶
      K') [QuasiIso q]
    (hq : IsIso (DerivedCategory.Q.map
      ((NatTrans.mapHomologicalComplex (etaleAbelianBaseChange.{u, v} f g g' f' h)
          (ComplexShape.up ℤ)).app K ≫
        ((etaleAbelianDirectImage.{u, v} f').mapHomologicalComplex (ComplexShape.up ℤ)).map q))) :
    IsIso ((etaleAbelianDerivedBaseChange.{u, v} f g g' f' h).app
      (DerivedCategory.Qh.obj ((HomotopyCategory.quotient
        (Sheaf X.smallEtaleTopology AddCommGrpCat.{max (u + 1) v}) (ComplexShape.up ℤ)).obj K))) :=
by
  refine Stacks.Cohomology.DerivedBaseChangeResolution.isIso_derivedBaseChange_of_isIso_Q_map_comp
    (etaleAbelianDirectImage.{u, v} f) (etaleAbelianInverseImage.{u, v} g)
    (etaleAbelianInverseImage.{u, v} g') (etaleAbelianDirectImage.{u, v} f')
    (etaleAbelianBaseChange.{u, v} f g g' f' h)
    (etaleAbelianDerivedDirectImage.{u, v} f) (etaleAbelianDerivedDirectImage.{u, v} f')
    (etaleAbelianDerivedDirectImageUnit.{u, v} f) (etaleAbelianDerivedDirectImageUnit.{u, v} f')
    (etaleAbelianDerivedBaseChange.{u, v} f g g' f' h)
    (etaleAbelianHomotopyBaseChange.{u, v} f g g' f' h) K K' q ?_ ?_ ?_ ?_ ?_
  · exact etaleAbelianHomotopyBaseChange_app_quotient_obj.{u, v} f g g' f' h K
  · exact etaleAbelianDerivedBaseChange_fac.{u, v} f g g' f' h _
  · exact isIso_etaleAbelianDerivedDirectImageUnit_app_of_plus_of_rightAcyclic.{u, v} f K hK hac
  · exact isIso_etaleAbelianDerivedDirectImageUnit_app_of_plus_of_rightAcyclic.{u, v} f' K' hK' hac'
  · exact hq

end Abelian

end Stacks.EtaleCohomology

end
