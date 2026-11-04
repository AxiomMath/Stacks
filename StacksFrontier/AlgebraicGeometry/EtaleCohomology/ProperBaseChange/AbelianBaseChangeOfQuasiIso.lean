module

public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.ProperBaseChange.AbelianBaseChangeResolution
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.ProperBaseChange.AbelianBaseChangeQuasiIsoConverse

/-!
# The abelian base change map from the comparison through an acyclic resolution

Let
```
X' --g'--> X
|f'        |f
v          v
Y' --g---> Y
```
be a commutative square of schemes, `K` a bounded below complex of abelian sheaves on `X_étale`
with `f_*`-acyclic terms and `q : (g')^{-1} K ⟶ K'` a quasi-isomorphism onto a bounded below
complex with `f'_*`-acyclic terms. If the morphism of complexes
`g^{-1} f_* K ⟶ f'_* (g')^{-1} K ⟶ f'_* K'` is a quasi-isomorphism, then the base change map
`g^{-1} Rf_* K ⟶ Rf'_* (g')^{-1} K` (`Stacks.EtaleCohomology.etaleAbelianDerivedBaseChange`) is
invertible at `K`. This is the converse of
`Stacks.EtaleCohomology.isIso_Q_map_etaleAbelianBaseChange_comp_of_quasiIso`, and is
`Stacks.Cohomology.DerivedBaseChangeResolution.isIso_derivedBaseChange_of_isIso_Q_map_comp`
for the étale direct and inverse images, fed with the characterization
`Stacks.EtaleCohomology.etaleAbelianDerivedBaseChange_fac` and Leray's acyclicity lemma.

## Implementation notes

As in `StacksFrontier/AlgebraicGeometry/EtaleCohomology/ProperBaseChange/AbelianBaseChangeQuasiIso.lean`, the statement carries
`CategoryTheory.Abelian.toPreadditive` as preferred `Preadditive` structure, the spelling of
`StacksFrontier/AlgebraicGeometry/EtaleCohomology/ProperBaseChange/BaseChangeMap.lean`, and the module has few imports.

## Main results

* `Stacks.EtaleCohomology.isIso_etaleAbelianDerivedBaseChange_app_of_isIso_Q_map_conj_comp`: the
  same for the comparison conjugated by other constructions of the inverse images.

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

/-- **The abelian base change map from a conjugated degreewise comparison.** The statement of
`Stacks.EtaleCohomology.isIso_etaleAbelianDerivedBaseChange_of_isIso_Q_map_comp` for a
comparison `β : f_* ⋙ P ⟶ P' ⋙ f'_*` which is `Stacks.EtaleCohomology.etaleAbelianBaseChange`
conjugated by identifications `ιs : P ≅ g⁻¹` and `ιx : P' ≅ g'⁻¹` of other inverse images, and a
quasi-isomorphism `q : P'(K) ⟶ K'`: if `β_K ≫ f'_*(q)` is an isomorphism of the derived category,
the base change map is invertible at `K`. Stating it with the inverse images and their
identifications as variables lets a consumer instantiate it with another construction of the
inverse images without the kernel comparing the two constructions. -/
theorem isIso_etaleAbelianDerivedBaseChange_app_of_isIso_Q_map_conj_comp
    (Ps : Sheaf Y.smallEtaleTopology AddCommGrpCat.{max (u + 1) v} ⥤
      Sheaf Y'.smallEtaleTopology AddCommGrpCat.{max (u + 1) v}) [Ps.Additive]
    (Px : Sheaf X.smallEtaleTopology AddCommGrpCat.{max (u + 1) v} ⥤
      Sheaf X'.smallEtaleTopology AddCommGrpCat.{max (u + 1) v}) [Px.Additive]
    (ιs : Ps ≅ etaleAbelianInverseImage.{u, v} g) (ιx : Px ≅ etaleAbelianInverseImage.{u, v} g')
    (β : etaleAbelianDirectImage.{u, v} f ⋙ Ps ⟶ Px ⋙ etaleAbelianDirectImage.{u, v} f')
    (hβ : β = Functor.whiskerLeft _ ιs.hom ≫ etaleAbelianBaseChange.{u, v} f g g' f' h ≫
      Functor.whiskerRight ιx.inv _)
    (K : CochainComplex (Sheaf X.smallEtaleTopology AddCommGrpCat.{max (u + 1) v}) ℤ)
    (hK : CochainComplex.plus (Sheaf X.smallEtaleTopology AddCommGrpCat.{max (u + 1) v}) K)
    (hac : ∀ n : ℤ, (etaleAbelianDirectImage.{u, v} f).rightAcyclic (K.X n))
    (K' : CochainComplex (Sheaf X'.smallEtaleTopology AddCommGrpCat.{max (u + 1) v}) ℤ)
    (hK' : CochainComplex.plus (Sheaf X'.smallEtaleTopology AddCommGrpCat.{max (u + 1) v}) K')
    (hac' : ∀ n : ℤ, (etaleAbelianDirectImage.{u, v} f').rightAcyclic (K'.X n))
    (q : (Px.mapHomologicalComplex (ComplexShape.up ℤ)).obj K ⟶ K') (hq : QuasiIso q)
    (hy : IsIso (DerivedCategory.Q.map
      ((NatTrans.mapHomologicalComplex β (ComplexShape.up ℤ)).app K ≫
        ((etaleAbelianDirectImage.{u, v} f').mapHomologicalComplex (ComplexShape.up ℤ)).map q))) :
    IsIso ((etaleAbelianDerivedBaseChange.{u, v} f g g' f' h).app
      (DerivedCategory.Qh.obj ((HomotopyCategory.quotient
        (Sheaf X.smallEtaleTopology AddCommGrpCat.{max (u + 1) v})
          (ComplexShape.up ℤ)).obj K))) := by
  subst hβ
  let q₁ := (NatIso.mapHomologicalComplex ιx (ComplexShape.up ℤ)).inv.app K ≫ q
  have : QuasiIso q₁ := quasiIso_comp (hφ := inferInstance) (hφ' := hq) _ _
  let A := (NatIso.mapHomologicalComplex (Functor.isoWhiskerLeft
    (etaleAbelianDirectImage.{u, v} f) ιs) (ComplexShape.up ℤ)).hom.app K
  have hcomp : (NatTrans.mapHomologicalComplex (Functor.whiskerLeft _ ιs.hom ≫
        etaleAbelianBaseChange.{u, v} f g g' f' h ≫ Functor.whiskerRight ιx.inv _)
        (ComplexShape.up ℤ)).app K ≫
      ((etaleAbelianDirectImage.{u, v} f').mapHomologicalComplex (ComplexShape.up ℤ)).map q =
      A ≫ ((NatTrans.mapHomologicalComplex (etaleAbelianBaseChange.{u, v} f g g' f' h)
          (ComplexShape.up ℤ)).app K ≫
        ((etaleAbelianDirectImage.{u, v} f').mapHomologicalComplex
          (ComplexShape.up ℤ)).map q₁) := by
    refine HomologicalComplex.hom_ext _ _ fun n => ?_
    simp [A, q₁]
  rw [hcomp] at hy
  exact isIso_etaleAbelianDerivedBaseChange_of_isIso_Q_map_comp.{u, v} f g g' f' h K hK hac K'
    hK' hac' q₁ ((DerivedCategory.isIso_Q_map_iff_quasiIso _ _).2
      ((quasiIso_iff_comp_left _ _).1 ((DerivedCategory.isIso_Q_map_iff_quasiIso _ _).1 hy)))

end Abelian

end Stacks.EtaleCohomology

end
