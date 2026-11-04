module

public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.ProperBaseChange.BaseChangeMap

/-!
# The derived base change map at a complex computing both direct images

Let
```
X' --g'--> X
|f'        |f
v          v
Y' --g---> Y
```
be a commutative square of schemes and `K` a complex of abelian sheaves on `X_étale`. If the
degreewise direct image computes `Rf_*` at `K` and `Rf'_*` at `(g')^{-1} K`, and the underived
comparison `g^{-1} f_* ⟶ f'_* (g')^{-1}` is invertible at every term of `K`, then the derived base
change map `g^{-1} Rf_* ⟶ Rf'_* (g')^{-1}` is invertible at `K`. This is the computation of the
base change map through a resolution that Stacks uses in Tags 0A4B and 03Q8.

The file imports only the definition of the base change map: the degreewise comparison is
read with exactly the instances used to define it.

## Main results

* `Stacks.EtaleCohomology.isIso_etaleAbelianDerivedBaseChange_app_Qh_of_isIso` — the criterion
  above.
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits
open AlgebraicGeometry AlgebraicGeometry.Scheme

attribute [local instance] HasDerivedCategory.standard

universe u v

namespace Stacks.EtaleCohomology

/-- If `a ≫ b ≫ x = r` with `a`, `b` and `r` invertible, then `x` is invertible. -/
theorem isIso_of_comp_comp_eq {C : Type*} [Category* C] {P Q R S : C} (a : P ⟶ Q) (b : Q ⟶ R)
    (x : R ⟶ S) (r : P ⟶ S) (e : a ≫ b ≫ x = r) [IsIso a] [IsIso b] (hr : IsIso r) :
    IsIso x := by
  have : x = inv b ≫ inv a ≫ r := by rw [← e]; simp
  rw [this]
  infer_instance

/-- Applying a natural transformation degreewise gives, at a complex whose terms all have
invertible components, an invertible morphism of the homotopy category. -/
theorem isIso_mapHomotopyCategory_app_quotient {V W : Type*} [Category* V] [Category* W]
    [Preadditive V] [Preadditive W] {F G : V ⥤ W} [F.Additive] [G.Additive] (α : F ⟶ G)
    (C : CochainComplex V ℤ) (hC : ∀ n, IsIso (α.app (C.X n))) :
    IsIso ((NatTrans.mapHomotopyCategory α (ComplexShape.up ℤ)).app
      ((HomotopyCategory.quotient V (ComplexShape.up ℤ)).obj C)) := by
  rw [NatTrans.mapHomotopyCategory_app]
  exact @Functor.map_isIso _ _ _ _ _ _ _ _
    (@HomologicalComplex.Hom.isIso_of_components _ _ _ _ _ _ _ _ hC)

section Criterion

variable {X X' Y Y' : Scheme.{u}} (f : X ⟶ Y) (g : Y' ⟶ Y) (g' : X' ⟶ X) (f' : X' ⟶ Y')
  (h : g' ≫ f = f' ≫ g)

/-- The degreewise base change comparison, unfolded. -/
theorem etaleAbelianHomotopyBaseChange_eq :
    etaleAbelianHomotopyBaseChange.{u, v} f g g' f' h =
    (Functor.mapHomotopyCategoryCompIso
      (Iso.refl (etaleAbelianDirectImage.{u, v} f ⋙ etaleAbelianInverseImage.{u, v} g))
      (ComplexShape.up ℤ)).hom ≫
    NatTrans.mapHomotopyCategory (etaleAbelianBaseChange.{u, v} f g g' f' h)
      (ComplexShape.up ℤ) ≫
    (Functor.mapHomotopyCategoryCompIso
      (Iso.refl (etaleAbelianInverseImage.{u, v} g' ⋙ etaleAbelianDirectImage.{u, v} f'))
      (ComplexShape.up ℤ)).inv := by
  rw [etaleAbelianHomotopyBaseChange]

/-- The invertibility of the degreewise comparison for a variable transformation of the shape
of the base change comparison, so that the kernel only instantiates it and never unfolds the
base change comparison, which is a mate. -/
private theorem isIso_comp_mapHomotopyCategory_app_of_baseChangeShape
    (α : etaleAbelianDirectImage.{u, v} f ⋙ etaleAbelianInverseImage.{u, v} g ⟶
      etaleAbelianInverseImage.{u, v} g' ⋙ etaleAbelianDirectImage.{u, v} f')
    (C : CochainComplex (Sheaf X.smallEtaleTopology AddCommGrpCat.{max (u + 1) v}) ℤ)
    (hC : ∀ n : ℤ, IsIso (α.app (C.X n))) :
    IsIso (((Functor.mapHomotopyCategoryCompIso
      (Iso.refl (etaleAbelianDirectImage.{u, v} f ⋙ etaleAbelianInverseImage.{u, v} g))
      (ComplexShape.up ℤ)).hom ≫
    NatTrans.mapHomotopyCategory α (ComplexShape.up ℤ) ≫
    (Functor.mapHomotopyCategoryCompIso
      (Iso.refl (etaleAbelianInverseImage.{u, v} g' ⋙ etaleAbelianDirectImage.{u, v} f'))
      (ComplexShape.up ℤ)).inv).app
        ((HomotopyCategory.quotient (Sheaf X.smallEtaleTopology AddCommGrpCat.{max (u + 1) v})
          (ComplexShape.up ℤ)).obj C)) := by
  have := isIso_mapHomotopyCategory_app_quotient α C hC
  rw [NatTrans.comp_app, NatTrans.comp_app]
  infer_instance

/-- The degreewise base change comparison on homotopy categories is invertible at a complex
whose terms all have invertible underived comparison. -/
theorem isIso_etaleAbelianHomotopyBaseChange_app
    (C : CochainComplex (Sheaf X.smallEtaleTopology AddCommGrpCat.{max (u + 1) v}) ℤ)
    (h3 : ∀ n : ℤ, IsIso ((etaleAbelianBaseChange.{u, v} f g g' f' h).app (C.X n))) :
    IsIso ((etaleAbelianHomotopyBaseChange.{u, v} f g g' f' h).app
      ((HomotopyCategory.quotient (Sheaf X.smallEtaleTopology AddCommGrpCat.{max (u + 1) v})
        (ComplexShape.up ℤ)).obj C)) := by
  rw [etaleAbelianHomotopyBaseChange_eq]
  exact isIso_comp_mapHomotopyCategory_app_of_baseChangeShape f g g' f' _ C h3

/-- **The derived base change map at a complex computing both direct images.** -/
theorem isIso_etaleAbelianDerivedBaseChange_app_Qh_of_isIso
    (C : CochainComplex (Sheaf X.smallEtaleTopology AddCommGrpCat.{max (u + 1) v}) ℤ)
    (h1 : IsIso ((etaleAbelianDerivedDirectImageUnit.{u, v} f).app
      ((HomotopyCategory.quotient (Sheaf X.smallEtaleTopology AddCommGrpCat.{max (u + 1) v})
        (ComplexShape.up ℤ)).obj C)))
    (h2 : IsIso ((etaleAbelianDerivedDirectImageUnit.{u, v} f').app
      (((etaleAbelianInverseImage.{u, v} g').mapHomotopyCategory (ComplexShape.up ℤ)).obj
        ((HomotopyCategory.quotient (Sheaf X.smallEtaleTopology AddCommGrpCat.{max (u + 1) v})
          (ComplexShape.up ℤ)).obj C))))
    (h3 : ∀ n, IsIso ((etaleAbelianBaseChange.{u, v} f g g' f' h).app (C.X n))) :
    IsIso ((etaleAbelianDerivedBaseChange.{u, v} f g g' f' h).app
      (DerivedCategory.Qh.obj
        ((HomotopyCategory.quotient (Sheaf X.smallEtaleTopology AddCommGrpCat.{max (u + 1) v})
          (ComplexShape.up ℤ)).obj C))) := by
  have h4 : IsIso ((etaleAbelianHomotopyBaseChange.{u, v} f g g' f' h).app
      ((HomotopyCategory.quotient (Sheaf X.smallEtaleTopology AddCommGrpCat.{max (u + 1) v})
        (ComplexShape.up ℤ)).obj C)) :=
    isIso_etaleAbelianHomotopyBaseChange_app.{u, v} f g g' f' h C h3
  exact isIso_of_comp_comp_eq _ _ _ _
    (etaleAbelianDerivedBaseChange_fac.{u, v} f g g' f' h
      ((HomotopyCategory.quotient (Sheaf X.smallEtaleTopology AddCommGrpCat.{max (u + 1) v})
        (ComplexShape.up ℤ)).obj C))
    (IsIso.comp_isIso' (Functor.map_isIso DerivedCategory.Qh _)
      (IsIso.comp_isIso' h2 inferInstance))

end Criterion

end Stacks.EtaleCohomology

end
