module

public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.ProperBaseChange.AcyclicResolutionBaseChange
public import StacksFrontier.Algebra.Homology.DerivedCategory.DerivedBaseChangePlus

/-!
# The abelian base change map through an acyclic resolution of the inverse image

Let
```
X' --g'--> X
|f'        |f
v          v
Y' --g---> Y
```
be a commutative square of schemes, `K` a bounded below complex of abelian sheaves on `X_étale`
whose terms are acyclic for `f_*`, and `q : (g')^{-1} K ⟶ K'` a quasi-isomorphism into a bounded
below complex whose terms are acyclic for `f'_*`. If the base change map
`g^{-1} Rf_* K ⟶ Rf'_* (g')^{-1} K` is invertible, then the morphism of complexes
`g^{-1} f_* K ⟶ f'_* (g')^{-1} K ⟶ f'_* K'`, the degreewise comparison followed by `f'_*(q)`, is
a quasi-isomorphism. In `Stacks.EtaleCohomology.etaleAbelianDerivedBaseChange_fac` both units
of `Rf_*` are invertible by Leray's lemma, and the unit of `Rf'_*` at `(g')^{-1} K` is carried by
`q` to the unit at `K'`, invertible by Leray's lemma again.

This is the form in which the abelian proper base change theorem is compared with its version
for sheaves of modules: there `K` and `K'` are the underlying abelian complexes of injective
resolutions, whose terms are acyclic for direct images
(`Stacks.EtaleCohomology.rightAcyclic_etaleAbelianDirectImage_etaleModuleForgetUniv_obj`) though
not injective, and `(g')^{-1} K` is not acyclic.

## Main results

* `Stacks.EtaleCohomology.isIso_Qh_map_etaleAbelianHomotopyBaseChange_comp_of_quasiIso`.

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

variable {X X' Y Y' : Scheme.{u}} (f : X ⟶ Y) (g : Y' ⟶ Y) (g' : X' ⟶ X) (f' : X' ⟶ Y')
  (h : g' ≫ f = f' ≫ g)

/-- **The base change map through an acyclic resolution of the inverse image.** If the base
change map is invertible at a bounded below complex `K` with `f_*`-acyclic terms, then the
degreewise comparison `g^{-1} f_* K ⟶ f'_* (g')^{-1} K` followed by `f'_*` of a
quasi-isomorphism `(g')^{-1} K ⟶ K'` onto a bounded below complex with `f'_*`-acyclic terms is an
isomorphism of the derived category. -/
public theorem isIso_Qh_map_etaleAbelianHomotopyBaseChange_comp_of_quasiIso
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
    IsIso (DerivedCategory.Qh.map ((etaleAbelianHomotopyBaseChange.{u, v} f g g' f' h).app
        ((HomotopyCategory.quotient (Sheaf X.smallEtaleTopology AddCommGrpCat.{max (u + 1) v})
          (ComplexShape.up ℤ)).obj K) ≫
      ((etaleAbelianDirectImage.{u, v} f').mapHomotopyCategory (ComplexShape.up ℤ)).map
        ((HomotopyCategory.quotient
          (Sheaf X'.smallEtaleTopology AddCommGrpCat.{max (u + 1) v})
            (ComplexShape.up ℤ)).map q))) := by
  have h₁ := isIso_etaleAbelianDerivedDirectImageUnit_app_of_plus_of_rightAcyclic f K hK hac
  have h₂ := isIso_etaleAbelianDerivedDirectImageUnit_app_of_plus_of_rightAcyclic f' K' hK' hac'
  have hfac := etaleAbelianDerivedBaseChange_fac.{u, v} f g g' f' h
    ((HomotopyCategory.quotient (Sheaf X.smallEtaleTopology AddCommGrpCat.{max (u + 1) v})
      (ComplexShape.up ℤ)).obj K)
  -- the composite `Qh(degreewise comparison) ≫ unit'` is invertible
  have hA : IsIso (DerivedCategory.Qh.map ((etaleAbelianHomotopyBaseChange.{u, v} f g g' f' h).app
        ((HomotopyCategory.quotient (Sheaf X.smallEtaleTopology AddCommGrpCat.{max (u + 1) v})
          (ComplexShape.up ℤ)).obj K)) ≫
      (etaleAbelianDerivedDirectImageUnit.{u, v} f').app
        (((etaleAbelianInverseImage.{u, v} g').mapHomotopyCategory (ComplexShape.up ℤ)).obj
          ((HomotopyCategory.quotient
            (Sheaf X.smallEtaleTopology AddCommGrpCat.{max (u + 1) v}) (ComplexShape.up ℤ)).obj
              K))) := by
    have hL : IsIso ((etaleAbelianInverseImage.{u, v} g).mapDerivedCategoryFactorsh.inv.app
        (((etaleAbelianDirectImage.{u, v} f).mapHomotopyCategory (ComplexShape.up ℤ)).obj
          ((HomotopyCategory.quotient
            (Sheaf X.smallEtaleTopology AddCommGrpCat.{max (u + 1) v}) (ComplexShape.up ℤ)).obj
              K)) ≫
        (etaleAbelianDerivedInverseImage.{u, v} g).map
          ((etaleAbelianDerivedDirectImageUnit.{u, v} f).app
            ((HomotopyCategory.quotient
              (Sheaf X.smallEtaleTopology AddCommGrpCat.{max (u + 1) v}) (ComplexShape.up ℤ)).obj
                K)) ≫
        (etaleAbelianDerivedBaseChange.{u, v} f g g' f' h).app
          (DerivedCategory.Qh.obj ((HomotopyCategory.quotient
            (Sheaf X.smallEtaleTopology AddCommGrpCat.{max (u + 1) v}) (ComplexShape.up ℤ)).obj
              K))) := inferInstance
    rw [hfac, ← Category.assoc] at hL
    exact IsIso.of_isIso_comp_right _
      ((etaleAbelianDerivedDirectImage.{u, v} f').map
        ((etaleAbelianInverseImage.{u, v} g').mapDerivedCategoryFactorsh.inv.app
          ((HomotopyCategory.quotient
            (Sheaf X.smallEtaleTopology AddCommGrpCat.{max (u + 1) v}) (ComplexShape.up ℤ)).obj K)))
  -- transport the unit along `q`
  have hq : IsIso (DerivedCategory.Qh.map ((HomotopyCategory.quotient
      (Sheaf X'.smallEtaleTopology AddCommGrpCat.{max (u + 1) v}) (ComplexShape.up ℤ)).map q)) := by
    rw [DerivedCategory.isIso_Qh_map_iff, HomotopyCategory.quotient_map_mem_quasiIso_iff]
    show QuasiIso q
    infer_instance
  have hnat := (etaleAbelianDerivedDirectImageUnit.{u, v} f').naturality
    ((HomotopyCategory.quotient
      (Sheaf X'.smallEtaleTopology AddCommGrpCat.{max (u + 1) v}) (ComplexShape.up ℤ)).map q)
  set a := DerivedCategory.Qh.map ((etaleAbelianHomotopyBaseChange.{u, v} f g g' f' h).app
    ((HomotopyCategory.quotient (Sheaf X.smallEtaleTopology AddCommGrpCat.{max (u + 1) v})
      (ComplexShape.up ℤ)).obj K)) with ha
  set qb := (HomotopyCategory.quotient
    (Sheaf X'.smallEtaleTopology AddCommGrpCat.{max (u + 1) v}) (ComplexShape.up ℤ)).map q with hqb
  have e : a ≫ DerivedCategory.Qh.map
        (((etaleAbelianDirectImage.{u, v} f').mapHomotopyCategory (ComplexShape.up ℤ)).map qb) ≫
      (etaleAbelianDerivedDirectImageUnit.{u, v} f').app
        ((HomotopyCategory.quotient
          (Sheaf X'.smallEtaleTopology AddCommGrpCat.{max (u + 1) v}) (ComplexShape.up ℤ)).obj K') =
      (a ≫ (etaleAbelianDerivedDirectImageUnit.{u, v} f').app
        (((etaleAbelianInverseImage.{u, v} g').mapHomotopyCategory (ComplexShape.up ℤ)).obj
          ((HomotopyCategory.quotient
            (Sheaf X.smallEtaleTopology AddCommGrpCat.{max (u + 1) v}) (ComplexShape.up ℤ)).obj
              K))) ≫
        (etaleAbelianDerivedDirectImage.{u, v} f').map (DerivedCategory.Qh.map qb) := by
    rw [Category.assoc]
    exact congrArg (a ≫ ·) hnat
  have hB : IsIso ((a ≫ DerivedCategory.Qh.map
        (((etaleAbelianDirectImage.{u, v} f').mapHomotopyCategory (ComplexShape.up ℤ)).map qb)) ≫
      (etaleAbelianDerivedDirectImageUnit.{u, v} f').app
        ((HomotopyCategory.quotient
          (Sheaf X'.smallEtaleTopology AddCommGrpCat.{max (u + 1) v}) (ComplexShape.up ℤ)).obj
            K')) := by
    rw [Category.assoc, e]
    have hr : IsIso
        ((etaleAbelianDerivedDirectImage.{u, v} f').map (DerivedCategory.Qh.map qb)) := by
      have := hq
      infer_instance
    exact IsIso.comp_isIso' hA hr
  rw [Functor.map_comp]
  have := h₂
  exact (isIso_comp_right_iff _ _).1 hB

attribute [local instance 10000] CategoryTheory.Abelian.toPreadditive
  Preadditive.preadditiveHasZeroMorphisms in
/-- **The degreewise base change comparison in the homotopy category, at a complex**: the class of
the morphism of complexes `g^{-1} f_* K ⟶ f'_* (g')^{-1} K`. -/
public theorem etaleAbelianHomotopyBaseChange_app_quotient_obj
    (K : CochainComplex (Sheaf X.smallEtaleTopology AddCommGrpCat.{max (u + 1) v}) ℤ) :
    (etaleAbelianHomotopyBaseChange.{u, v} f g g' f' h).app
        ((HomotopyCategory.quotient _ (ComplexShape.up ℤ)).obj K) =
      (HomotopyCategory.quotient _ (ComplexShape.up ℤ)).map
        ((NatTrans.mapHomologicalComplex (etaleAbelianBaseChange.{u, v} f g g' f' h)
          (ComplexShape.up ℤ)).app K) := by
  have hdef : etaleAbelianHomotopyBaseChange.{u, v} f g g' f' h =
      (Functor.mapHomotopyCategoryCompIso
            (Iso.refl (etaleAbelianDirectImage.{u, v} f ⋙ etaleAbelianInverseImage.{u, v} g))
            (ComplexShape.up ℤ)).hom ≫
        NatTrans.mapHomotopyCategory (etaleAbelianBaseChange.{u, v} f g g' f' h)
            (ComplexShape.up ℤ) ≫
          (Functor.mapHomotopyCategoryCompIso
            (Iso.refl (etaleAbelianInverseImage.{u, v} g' ⋙ etaleAbelianDirectImage.{u, v} f'))
            (ComplexShape.up ℤ)).inv :=
    rfl
  exact (congrArg
      (fun t => NatTrans.app t ((HomotopyCategory.quotient _ (ComplexShape.up ℤ)).obj K))
      hdef).trans
    (Cohomology.DerivedBaseChangePlus.mapHomotopyCategoryCompIso_hom_comp_comp_inv_app_quotient_obj
      _ _ _ _ _ K)
