module

public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.ProperBaseChange.Basic
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.SmallEtaleAbelianDerivedFunctors
public import StacksFrontier.CategoryTheory.Adjunction.BaseChangeSquare

/-!
# The base change map for étale cohomology

Let
```
X' --g'--> X
|f'        |f
v          v
Y' --g---> Y
```
be a **commutative** square of schemes. This file constructs the canonical base change map
$$
g^{-1} Rf_* \longrightarrow Rf'_* (g')^{-1}
$$
of functors `D(X_étale) ⥤ D(Y'_étale)` on the **unbounded** derived categories of abelian
sheaves for the small étale topology, and its specialization to a single abelian sheaf placed
in degree zero.

Nothing is assumed of the square beyond commutativity: it need not be cartesian, `f` need not
be proper or even quasi-compact, and the coefficients are arbitrary objects of the unbounded
derived category, with no boundedness or torsion condition.

## Main definitions

* `Stacks.EtaleCohomology.etaleAbelianBaseChange` — the underived comparison
  `f_* ⋙ g^{-1} ⟶ (g')^{-1} ⋙ f'_*`.
* `Stacks.EtaleCohomology.etaleAbelianHomotopyBaseChange` — the same comparison applied
  degreewise on homotopy categories of unbounded complexes.
* `Stacks.EtaleCohomology.etaleAbelianDerivedBaseChange` — the base change map
  `g^{-1} Rf_* ⟶ Rf'_* (g')^{-1}` on unbounded derived categories.
* `Stacks.EtaleCohomology.etaleAbelianSheafDerivedBaseChange` — its component at an abelian
  sheaf placed in degree zero, the map `g^{-1} Rf_* F ⟶ Rf'_* (g')^{-1} F`.

## Main results

* `Stacks.EtaleCohomology.etaleAbelianDerivedBaseChange_fac` characterizes the base change map
  on **every** unbounded complex: precomposed with the localization functor and with the
  derived-functor unit of `Rf_*`, it is the degreewise comparison followed by the
  derived-functor unit of `Rf'_*`.
* `Stacks.EtaleCohomology.etaleAbelianHomotopyBaseChange_app` reads the degreewise comparison at
  a complex as the degreewise action of the underived comparison, between the two identity
  comparisons of the actions of a composite.

## References

* [Stacks Project, Tag 0A2A](https://stacks.math.columbia.edu/tag/0A2A)
* [Stacks Project, Tag 0A4A](https://stacks.math.columbia.edu/tag/0A4A)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits
open AlgebraicGeometry AlgebraicGeometry.Scheme

attribute [local instance] HasDerivedCategory.standard

attribute [local instance 10000] CategoryTheory.Abelian.toPreadditive

universe u v

namespace Stacks.EtaleCohomology

variable {X X' Y Y' : Scheme.{u}} (f : X ⟶ Y) (g : Y' ⟶ Y) (g' : X' ⟶ X) (f' : X' ⟶ Y')
  (h : g' ≫ f = f' ≫ g)

/-- The canonical comparison `g^{-1} f_* ⟶ f'_* (g')^{-1}` of underived functors on abelian
sheaves of the small étale sites, attached to a commutative square `g' ≫ f = f' ≫ g` of
schemes. It is the mate, along the two inverse-image/direct-image adjunctions for `f` and `f'`,
of the identification of the two composite inverse images around the square. -/
public def etaleAbelianBaseChange :
    etaleAbelianDirectImage.{u, v} f ⋙ etaleAbelianInverseImage.{u, v} g ⟶
      etaleAbelianInverseImage.{u, v} g' ⋙ etaleAbelianDirectImage.{u, v} f' :=
  Stacks.CategoryTheory.BaseChange.twoSquare
    (etaleAbelianInverseImageDirectImageAdj.{u, v} f)
    (etaleAbelianInverseImageDirectImageAdj.{u, v} f')
    (etaleAbelianInverseImageCompIso.{u, v} f' g).symm
    ((etaleAbelianInverseImageCompIso.{u, v} g' f).symm ≪≫
      eqToIso (congrArg (fun k : X' ⟶ Y ↦ etaleAbelianInverseImage.{u, v} k) h))

/-- The underived base change comparison applied degreewise to unbounded complexes and passed
to the homotopy categories. -/
public def etaleAbelianHomotopyBaseChange :
    (etaleAbelianDirectImage.{u, v} f).mapHomotopyCategory (ComplexShape.up ℤ) ⋙
        (etaleAbelianInverseImage.{u, v} g).mapHomotopyCategory (ComplexShape.up ℤ) ⟶
      (etaleAbelianInverseImage.{u, v} g').mapHomotopyCategory (ComplexShape.up ℤ) ⋙
        (etaleAbelianDirectImage.{u, v} f').mapHomotopyCategory (ComplexShape.up ℤ) :=
  (Functor.mapHomotopyCategoryCompIso
      (Iso.refl (etaleAbelianDirectImage.{u, v} f ⋙ etaleAbelianInverseImage.{u, v} g))
      (ComplexShape.up ℤ)).hom ≫
    NatTrans.mapHomotopyCategory (etaleAbelianBaseChange.{u, v} f g g' f' h)
      (ComplexShape.up ℤ) ≫
    (Functor.mapHomotopyCategoryCompIso
      (Iso.refl (etaleAbelianInverseImage.{u, v} g' ⋙ etaleAbelianDirectImage.{u, v} f'))
      (ComplexShape.up ℤ)).inv

/-- The derived-functor unit exhibiting `Rf_* ⋙ g^{-1}` as a right derived functor of
degreewise `f_* ⋙ g^{-1}`: the unit of `Rf_*` whiskered with `g^{-1}`. -/
private abbrev bcUnit :
    etaleAbelianPushforwardToDerivedCategory.{u, v} f ⋙
        etaleAbelianDerivedInverseImage.{u, v} g ⟶
      DerivedCategory.Qh ⋙ (etaleAbelianDerivedDirectImage.{u, v} f ⋙
        etaleAbelianDerivedInverseImage.{u, v} g) :=
  Functor.whiskerRight (etaleAbelianDerivedDirectImageUnit.{u, v} f)
      (etaleAbelianDerivedInverseImage.{u, v} g) ≫ (Functor.associator _ _ _).hom

/-- Applying `f_*` and then `g^{-1}` degreewise and localizing is isomorphic to applying `f_*`
degreewise, localizing, and then applying the derived `g^{-1}`. -/
private def bcSourceIso :
    ((etaleAbelianDirectImage.{u, v} f).mapHomotopyCategory (ComplexShape.up ℤ) ⋙
        (etaleAbelianInverseImage.{u, v} g).mapHomotopyCategory (ComplexShape.up ℤ)) ⋙
          DerivedCategory.Qh ≅
      etaleAbelianPushforwardToDerivedCategory.{u, v} f ⋙
        etaleAbelianDerivedInverseImage.{u, v} g :=
  Functor.associator _ _ _ ≪≫
    Functor.isoWhiskerLeft
      ((etaleAbelianDirectImage.{u, v} f).mapHomotopyCategory (ComplexShape.up ℤ))
      (etaleAbelianInverseImage.{u, v} g).mapDerivedCategoryFactorsh.symm ≪≫
    Functor.associator _ _ _

/-- The degreewise base change comparison, followed by the derived-functor unit of `Rf'_*` and
the exactness comparison for `(g')^{-1}`. -/
private def bcBetaOrig :
    ((etaleAbelianDirectImage.{u, v} f).mapHomotopyCategory (ComplexShape.up ℤ) ⋙
        (etaleAbelianInverseImage.{u, v} g).mapHomotopyCategory (ComplexShape.up ℤ)) ⋙
          DerivedCategory.Qh ⟶
      DerivedCategory.Qh ⋙ (etaleAbelianDerivedInverseImage.{u, v} g' ⋙
        etaleAbelianDerivedDirectImage.{u, v} f') :=
  Functor.whiskerRight (etaleAbelianHomotopyBaseChange.{u, v} f g g' f' h)
      DerivedCategory.Qh ≫
    (Functor.associator _ _ _).hom ≫
    Functor.whiskerLeft
      ((etaleAbelianInverseImage.{u, v} g').mapHomotopyCategory (ComplexShape.up ℤ))
      (etaleAbelianDerivedDirectImageUnit.{u, v} f') ≫
    (Functor.associator _ _ _).inv ≫
    Functor.whiskerRight
      (etaleAbelianInverseImage.{u, v} g').mapDerivedCategoryFactorsh.inv
      (etaleAbelianDerivedDirectImage.{u, v} f') ≫
    (Functor.associator _ _ _).hom

/-- The transformation to be descended, read on the source of the derived-functor unit. -/
private def bcBeta :
    etaleAbelianPushforwardToDerivedCategory.{u, v} f ⋙
        etaleAbelianDerivedInverseImage.{u, v} g ⟶
      DerivedCategory.Qh ⋙ (etaleAbelianDerivedInverseImage.{u, v} g' ⋙
        etaleAbelianDerivedDirectImage.{u, v} f') :=
  (bcSourceIso.{u, v} f g).inv ≫ bcBetaOrig.{u, v} f g g' f' h

/-- The canonical base change map `g^{-1} Rf_* ⟶ Rf'_* (g')^{-1}` on the
unbounded derived categories of abelian sheaves for the small étale topology, attached to a
commutative square `g' ≫ f = f' ≫ g` of schemes. -/
@[stacks 0A2A, no_expose]
public def etaleAbelianDerivedBaseChange :
    etaleAbelianDerivedDirectImage.{u, v} f ⋙ etaleAbelianDerivedInverseImage.{u, v} g ⟶
      etaleAbelianDerivedInverseImage.{u, v} g' ⋙ etaleAbelianDerivedDirectImage.{u, v} f' :=
  (etaleAbelianDerivedDirectImage.{u, v} f ⋙
      etaleAbelianDerivedInverseImage.{u, v} g).rightDerivedDesc
    (bcUnit.{u, v} f g)
    (HomotopyCategory.quasiIso
      (Sheaf X.smallEtaleTopology AddCommGrpCat.{max (u + 1) v}) (ComplexShape.up ℤ))
    (etaleAbelianDerivedInverseImage.{u, v} g' ⋙ etaleAbelianDerivedDirectImage.{u, v} f')
    (bcBeta.{u, v} f g g' f' h)

variable (K : HomotopyCategory (Sheaf X.smallEtaleTopology AddCommGrpCat.{max (u + 1) v})
  (ComplexShape.up ℤ))

/-- The degreewise base change comparison at a complex is the degreewise action of
`Stacks.EtaleCohomology.etaleAbelianBaseChange` on the representing complex, read between the two
comparisons which identify the action of a composite of two inverse/direct images with the
composite of the two actions. -/
public theorem etaleAbelianHomotopyBaseChange_app :
    (etaleAbelianHomotopyBaseChange.{u, v} f g g' f' h).app K =
      (Functor.mapHomotopyCategoryCompIso
            (Iso.refl (etaleAbelianDirectImage.{u, v} f ⋙ etaleAbelianInverseImage.{u, v} g))
            (ComplexShape.up ℤ)).hom.app K ≫
        (NatTrans.mapHomotopyCategory (etaleAbelianBaseChange.{u, v} f g g' f' h)
            (ComplexShape.up ℤ)).app K ≫
          (Functor.mapHomotopyCategoryCompIso
            (Iso.refl (etaleAbelianInverseImage.{u, v} g' ⋙ etaleAbelianDirectImage.{u, v} f'))
            (ComplexShape.up ℤ)).inv.app K := by
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
  refine (congrArg (fun t => NatTrans.app t K) hdef).trans ?_
  refine (NatTrans.comp_app _ _ K).trans ?_
  exact congrArg (fun y => (Functor.mapHomotopyCategoryCompIso
      (Iso.refl (etaleAbelianDirectImage.{u, v} f ⋙ etaleAbelianInverseImage.{u, v} g))
      (ComplexShape.up ℤ)).hom.app K ≫ y) (NatTrans.comp_app _ _ K)

/-- The component of the derived-functor unit of `Rf_* ⋙ g^{-1}` is the derived `g^{-1}`
applied to the component of the unit of `Rf_*`. -/
private theorem bcUnit_app :
    (bcUnit.{u, v} f g).app K =
      (etaleAbelianDerivedInverseImage.{u, v} g).map
        ((etaleAbelianDerivedDirectImageUnit.{u, v} f).app K) := by
  simp [bcUnit]

/-- The component of the source identification is the exactness comparison for `g^{-1}` at the
degreewise direct image of the complex. -/
private theorem bcSourceIso_hom_app :
    (bcSourceIso.{u, v} f g).hom.app K =
      (etaleAbelianInverseImage.{u, v} g).mapDerivedCategoryFactorsh.inv.app
        (((etaleAbelianDirectImage.{u, v} f).mapHomotopyCategory
          (ComplexShape.up ℤ)).obj K) := by
  simp [bcSourceIso]

/-- Undoing the source identification recovers the degreewise comparison. -/
private theorem bcSourceIso_hom_app_comp_bcBeta :
    (bcSourceIso.{u, v} f g).hom.app K ≫ (bcBeta.{u, v} f g g' f' h).app K =
      (bcBetaOrig.{u, v} f g g' f' h).app K := by
  simp [bcBeta]

/-- The component of the transformation being descended, written out. -/
private theorem bcBetaOrig_app :
    (bcBetaOrig.{u, v} f g g' f' h).app K =
      DerivedCategory.Qh.map ((etaleAbelianHomotopyBaseChange.{u, v} f g g' f' h).app K) ≫
        (etaleAbelianDerivedDirectImageUnit.{u, v} f').app
          (((etaleAbelianInverseImage.{u, v} g').mapHomotopyCategory
            (ComplexShape.up ℤ)).obj K) ≫
        (etaleAbelianDerivedDirectImage.{u, v} f').map
          ((etaleAbelianInverseImage.{u, v} g').mapDerivedCategoryFactorsh.inv.app K) := by
  simp [bcBetaOrig]

/-- For every complex `K` of abelian sheaves on `X_étale`, the base change map at the object it
represents, precomposed with the exactness comparison for `g^{-1}` and with the derived-functor
unit of `Rf_*`, is the degreewise base change comparison followed by the derived-functor unit
of `Rf'_*`. -/
@[stacks 0A2A "canonical comparison on unbounded complexes"]
public theorem etaleAbelianDerivedBaseChange_fac :
    (etaleAbelianInverseImage.{u, v} g).mapDerivedCategoryFactorsh.inv.app
        (((etaleAbelianDirectImage.{u, v} f).mapHomotopyCategory
          (ComplexShape.up ℤ)).obj K) ≫
      (etaleAbelianDerivedInverseImage.{u, v} g).map
        ((etaleAbelianDerivedDirectImageUnit.{u, v} f).app K) ≫
      (etaleAbelianDerivedBaseChange.{u, v} f g g' f' h).app (DerivedCategory.Qh.obj K) =
    DerivedCategory.Qh.map ((etaleAbelianHomotopyBaseChange.{u, v} f g g' f' h).app K) ≫
      (etaleAbelianDerivedDirectImageUnit.{u, v} f').app
        (((etaleAbelianInverseImage.{u, v} g').mapHomotopyCategory
          (ComplexShape.up ℤ)).obj K) ≫
      (etaleAbelianDerivedDirectImage.{u, v} f').map
        ((etaleAbelianInverseImage.{u, v} g').mapDerivedCategoryFactorsh.inv.app K) := by
  have hfac := (etaleAbelianDerivedDirectImage.{u, v} f ⋙
      etaleAbelianDerivedInverseImage.{u, v} g).rightDerived_fac_app
    (bcUnit.{u, v} f g)
    (HomotopyCategory.quasiIso
      (Sheaf X.smallEtaleTopology AddCommGrpCat.{max (u + 1) v}) (ComplexShape.up ℤ))
    (etaleAbelianDerivedInverseImage.{u, v} g' ⋙ etaleAbelianDerivedDirectImage.{u, v} f')
    (bcBeta.{u, v} f g g' f' h) K
  calc
    _ = (bcSourceIso.{u, v} f g).hom.app K ≫ (bcUnit.{u, v} f g).app K ≫
          (etaleAbelianDerivedBaseChange.{u, v} f g g' f' h).app
            (DerivedCategory.Qh.obj K) := by
      rw [bcSourceIso_hom_app, bcUnit_app]
    _ = (bcSourceIso.{u, v} f g).hom.app K ≫ (bcBeta.{u, v} f g g' f' h).app K :=
      congrArg (fun t => (bcSourceIso.{u, v} f g).hom.app K ≫ t) hfac
    _ = (bcBetaOrig.{u, v} f g g' f' h).app K :=
      bcSourceIso_hom_app_comp_bcBeta.{u, v} f g g' f' h K
    _ = _ := bcBetaOrig_app.{u, v} f g g' f' h K

/-- The base change map for a single abelian sheaf `F` on `X_étale`, placed in
degree zero: the canonical morphism `g^{-1} Rf_* F ⟶ Rf'_* (g')^{-1} F` in the derived category
of `Y'_étale`, attached to a commutative square `g' ≫ f = f' ≫ g` of schemes. It is the
component of `Stacks.EtaleCohomology.etaleAbelianDerivedBaseChange` at `F[0]`. -/
@[stacks 0A4A]
public def etaleAbelianSheafDerivedBaseChange
    (F : Sheaf X.smallEtaleTopology AddCommGrpCat.{max (u + 1) v}) :
    (etaleAbelianDerivedInverseImage.{u, v} g).obj
        ((etaleAbelianDerivedDirectImage.{u, v} f).obj
          ((DerivedCategory.singleFunctor
            (Sheaf X.smallEtaleTopology AddCommGrpCat.{max (u + 1) v}) 0).obj F)) ⟶
      (etaleAbelianDerivedDirectImage.{u, v} f').obj
        ((etaleAbelianDerivedInverseImage.{u, v} g').obj
          ((DerivedCategory.singleFunctor
            (Sheaf X.smallEtaleTopology AddCommGrpCat.{max (u + 1) v}) 0).obj F)) :=
  (etaleAbelianDerivedBaseChange.{u, v} f g g' f' h).app
    ((DerivedCategory.singleFunctor
      (Sheaf X.smallEtaleTopology AddCommGrpCat.{max (u + 1) v}) 0).obj F)

end Stacks.EtaleCohomology

end
