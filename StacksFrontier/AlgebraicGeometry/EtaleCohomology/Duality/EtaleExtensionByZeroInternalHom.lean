module

public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.Duality.EtaleRestrictionInternalHom
public import StacksFrontier.CategoryTheory.Sites.AbelianInternalHomSwap
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.ExtensionByZero.OpenClosedSequence

/-!
# The internal adjunction `ℋom(j_! A, B) ≅ j_* ℋom(A, j⁻¹ B)`

For an étale morphism `j : U ⟶ X`, abelian sheaves `A` on `U_étale` and `B` on `X_étale`, the
internal Hom out of an extension by zero is a direct image:
`ℋom(j_! A, B) ≅ j_* ℋom(A, j⁻¹ B)`, naturally in `A` and `B`. By Yoneda it is the composite of
the bijections, natural in a test sheaf `T`,
`Hom(T, ℋom(j_! A, B)) ≃ Hom(j_! A, ℋom(T, B)) ≃ Hom(A, j⁻¹ ℋom(T, B))
  ≃ Hom(A, ℋom(j⁻¹ T, j⁻¹ B)) ≃ Hom(j⁻¹ T, ℋom(A, j⁻¹ B)) ≃ Hom(T, j_* ℋom(A, j⁻¹ B))`:
swapping the arguments of the internal Hom, `j_! ⊣ j⁻¹`, restriction commuting with the internal
Hom (`Stacks.EtaleCohomology.etaleRestrictionInternalHomIso`), swapping again, and `j⁻¹ ⊣ j_*`.

## Main definitions

* `Stacks.EtaleCohomology.internalHomExtensionByZeroIso`.
* `Stacks.EtaleCohomology.internalHomExtensionByZeroNatIso`: the same, as an isomorphism of
  functors of `B`.
-/

@[expose] public noncomputable section

open CategoryTheory AlgebraicGeometry Opposite Stacks.AbelianInternalHom

universe u

namespace Stacks.EtaleCohomology

variable {U X : Scheme.{u}} (j : U ⟶ X) [Etale j]

/-- `j⁻¹ ℋom(F, G) ≅ ℋom(j⁻¹ F, j⁻¹ G)` is natural in `F`. -/
lemma etaleRestrictionInternalHomIso_hom_naturality_left
    {F F' : Sheaf X.smallEtaleTopology AddCommGrpCat.{u + 1}} (f : F ⟶ F')
    (G : Sheaf X.smallEtaleTopology AddCommGrpCat.{u + 1}) :
    (etaleRestriction.{u, 0} j).map (internalHomSheafMapLeft _ f G) ≫
        (etaleRestrictionInternalHomIso j F G).hom =
      (etaleRestrictionInternalHomIso j F' G).hom ≫
        internalHomSheafMapLeft _ ((etaleRestriction.{u, 0} j).map f)
          ((etaleRestriction.{u, 0} j).obj G) :=
  Sheaf.hom_ext (internalHomPresheafPrecomp_naturality_left (Scheme.Etale.smallEtaleCompose j)
    (G := G.obj) f.hom)

/-- `j⁻¹ ℋom(F, G) ≅ ℋom(j⁻¹ F, j⁻¹ G)` is natural in `G`. -/
lemma etaleRestrictionInternalHomIso_hom_naturality_right
    (F : Sheaf X.smallEtaleTopology AddCommGrpCat.{u + 1})
    {G G' : Sheaf X.smallEtaleTopology AddCommGrpCat.{u + 1}} (g : G ⟶ G') :
    (etaleRestriction.{u, 0} j).map (internalHomSheafMapRight _ F g) ≫
        (etaleRestrictionInternalHomIso j F G').hom =
      (etaleRestrictionInternalHomIso j F G).hom ≫
        internalHomSheafMapRight _ ((etaleRestriction.{u, 0} j).obj F)
          ((etaleRestriction.{u, 0} j).map g) :=
  Sheaf.hom_ext (internalHomPresheafPrecomp_naturality_right (Scheme.Etale.smallEtaleCompose j)
    (F := F.obj) g.hom)

variable (A : Sheaf U.smallEtaleTopology AddCommGrpCat.{u + 1})
  (B : Sheaf X.smallEtaleTopology AddCommGrpCat.{u + 1})

/-- The bijection `Hom(T, ℋom(j_! A, B)) ≃ Hom(T, j_* ℋom(A, j⁻¹ B))`, natural in `T`. -/
def internalHomExtensionByZeroEquiv (T : Sheaf X.smallEtaleTopology AddCommGrpCat.{u + 1}) :
    (T ⟶ internalHomSheaf X.smallEtaleTopology ((extensionByZero.{u, 0} j).obj A) B) ≃
      (T ⟶ (etaleAbelianDirectImage.{u, 0} j).obj
        (internalHomSheaf U.smallEtaleTopology A ((etaleRestriction.{u, 0} j).obj B))) :=
  (internalHomSheafSwap _ T ((extensionByZero.{u, 0} j).obj A) B).trans
    (((extensionByZeroAdj.{u, 0} j).homEquiv A _).trans
      (((Iso.refl A).homCongr (etaleRestrictionInternalHomIso j T B)).trans
        ((internalHomSheafSwap _ A ((etaleRestriction.{u, 0} j).obj T)
          ((etaleRestriction.{u, 0} j).obj B)).trans
          ((etaleRestrictionAbelianDirectImageAdj.{u, 0} j).homEquiv T _))))

/-- `internalHomExtensionByZeroEquiv` is natural in the test sheaf `T`: it commutes with
precomposition by `f : T' ⟶ T`. -/
lemma internalHomExtensionByZeroEquiv_comp
    {T T' : Sheaf X.smallEtaleTopology AddCommGrpCat.{u + 1}} (f : T' ⟶ T)
    (φ : T ⟶ internalHomSheaf X.smallEtaleTopology ((extensionByZero.{u, 0} j).obj A) B) :
    internalHomExtensionByZeroEquiv j A B T' (f ≫ φ) =
      f ≫ internalHomExtensionByZeroEquiv j A B T φ := by
  simp only [internalHomExtensionByZeroEquiv, Equiv.trans_apply, Iso.homCongr_apply,
    Iso.refl_inv, Category.id_comp]
  have e₁ := internalHomSheafSwap_comp X.smallEtaleTopology
    (G := (extensionByZero.{u, 0} j).obj A) (I := B) f φ
  have e₂ := (extensionByZeroAdj.{u, 0} j).homEquiv_naturality_right
    ((internalHomSheafSwap X.smallEtaleTopology T ((extensionByZero.{u, 0} j).obj A) B) φ)
    (internalHomSheafMapLeft X.smallEtaleTopology f B)
  rw [e₁, e₂, Category.assoc, etaleRestrictionInternalHomIso_hom_naturality_left j f B,
    ← Category.assoc]
  have e₄ := internalHomSheafSwap_comp_map U.smallEtaleTopology (X := A)
    (I := (etaleRestriction.{u, 0} j).obj B) ((etaleRestriction.{u, 0} j).map f)
    (((extensionByZeroAdj.{u, 0} j).homEquiv A _)
      ((internalHomSheafSwap X.smallEtaleTopology T ((extensionByZero.{u, 0} j).obj A) B) φ) ≫
      (etaleRestrictionInternalHomIso j T B).hom)
  rw [e₄, Adjunction.homEquiv_naturality_left]

/-- `internalHomExtensionByZeroEquiv` is natural in `B`: postcomposition by `ℋom(j_! A, b)`
corresponds to postcomposition by `j_* ℋom(A, j⁻¹ b)`. -/
lemma internalHomExtensionByZeroEquiv_comp_mapRight
    {B B' : Sheaf X.smallEtaleTopology AddCommGrpCat.{u + 1}} (b : B ⟶ B')
    (T : Sheaf X.smallEtaleTopology AddCommGrpCat.{u + 1})
    (φ : T ⟶ internalHomSheaf X.smallEtaleTopology ((extensionByZero.{u, 0} j).obj A) B) :
    internalHomExtensionByZeroEquiv j A B' T
        (φ ≫ internalHomSheafMapRight _ ((extensionByZero.{u, 0} j).obj A) b) =
      internalHomExtensionByZeroEquiv j A B T φ ≫ (etaleAbelianDirectImage.{u, 0} j).map
        (internalHomSheafMapRight _ A ((etaleRestriction.{u, 0} j).map b)) := by
  simp only [internalHomExtensionByZeroEquiv, Equiv.trans_apply, Iso.homCongr_apply,
    Iso.refl_inv, Category.id_comp]
  have e₁ := internalHomSheafSwap_comp_mapRight X.smallEtaleTopology (X := T)
    (G := (extensionByZero.{u, 0} j).obj A) b φ
  have e₂ := (extensionByZeroAdj.{u, 0} j).homEquiv_naturality_right
    ((internalHomSheafSwap X.smallEtaleTopology T ((extensionByZero.{u, 0} j).obj A) B) φ)
    (internalHomSheafMapRight X.smallEtaleTopology T b)
  rw [e₁, e₂, Category.assoc, etaleRestrictionInternalHomIso_hom_naturality_right j T b,
    ← Category.assoc]
  have e₄ := internalHomSheafSwap_comp_mapRight U.smallEtaleTopology (X := A)
    (G := (etaleRestriction.{u, 0} j).obj T) ((etaleRestriction.{u, 0} j).map b)
    (((extensionByZeroAdj.{u, 0} j).homEquiv A _)
      ((internalHomSheafSwap X.smallEtaleTopology T ((extensionByZero.{u, 0} j).obj A) B) φ) ≫
      (etaleRestrictionInternalHomIso j T B).hom)
  rw [e₄, Adjunction.homEquiv_naturality_right]

/-- `internalHomExtensionByZeroEquiv` is natural in `A`: postcomposition by `ℋom(j_! a, B)`
corresponds to postcomposition by `j_* ℋom(a, j⁻¹ B)`. -/
lemma internalHomExtensionByZeroEquiv_comp_mapLeft
    {A A' : Sheaf U.smallEtaleTopology AddCommGrpCat.{u + 1}} (a : A' ⟶ A)
    (T : Sheaf X.smallEtaleTopology AddCommGrpCat.{u + 1})
    (φ : T ⟶ internalHomSheaf X.smallEtaleTopology ((extensionByZero.{u, 0} j).obj A) B) :
    internalHomExtensionByZeroEquiv j A' B T
        (φ ≫ internalHomSheafMapLeft _ ((extensionByZero.{u, 0} j).map a) B) =
      internalHomExtensionByZeroEquiv j A B T φ ≫ (etaleAbelianDirectImage.{u, 0} j).map
        (internalHomSheafMapLeft _ a ((etaleRestriction.{u, 0} j).obj B)) := by
  simp only [internalHomExtensionByZeroEquiv, Equiv.trans_apply, Iso.homCongr_apply,
    Iso.refl_inv, Category.id_comp]
  have e₁ := internalHomSheafSwap_comp_map X.smallEtaleTopology (X := T) (I := B)
    ((extensionByZero.{u, 0} j).map a) φ
  rw [e₁, Adjunction.homEquiv_naturality_left, Category.assoc]
  have e₄ := internalHomSheafSwap_comp U.smallEtaleTopology
    (G := (etaleRestriction.{u, 0} j).obj T) (I := (etaleRestriction.{u, 0} j).obj B) a
    (((extensionByZeroAdj.{u, 0} j).homEquiv A _)
      ((internalHomSheafSwap X.smallEtaleTopology T ((extensionByZero.{u, 0} j).obj A) B) φ) ≫
      (etaleRestrictionInternalHomIso j T B).hom)
  rw [e₄, Adjunction.homEquiv_naturality_right]

/-- **`ℋom(j_! A, B) ≅ j_* ℋom(A, j⁻¹ B)`** for `j` étale. -/
def internalHomExtensionByZeroIso :
    internalHomSheaf X.smallEtaleTopology ((extensionByZero.{u, 0} j).obj A) B ≅
      (etaleAbelianDirectImage.{u, 0} j).obj
        (internalHomSheaf U.smallEtaleTopology A ((etaleRestriction.{u, 0} j).obj B)) where
  hom := internalHomExtensionByZeroEquiv j A B _ (𝟙 _)
  inv := (internalHomExtensionByZeroEquiv j A B _).symm (𝟙 _)
  hom_inv_id := by
    apply (internalHomExtensionByZeroEquiv j A B _).injective
    rw [internalHomExtensionByZeroEquiv_comp, Equiv.apply_symm_apply, Category.comp_id]
  inv_hom_id := by
    rw [← internalHomExtensionByZeroEquiv_comp, Category.comp_id, Equiv.apply_symm_apply]

/-- Composing `φ : T ⟶ ℋom(j_! A, B)` with `internalHomExtensionByZeroIso` gives
`internalHomExtensionByZeroEquiv` applied to `φ`. -/
lemma comp_internalHomExtensionByZeroIso_hom
    {T : Sheaf X.smallEtaleTopology AddCommGrpCat.{u + 1}}
    (φ : T ⟶ internalHomSheaf X.smallEtaleTopology ((extensionByZero.{u, 0} j).obj A) B) :
    φ ≫ (internalHomExtensionByZeroIso j A B).hom = internalHomExtensionByZeroEquiv j A B T φ := by
  show φ ≫ internalHomExtensionByZeroEquiv j A B _ (𝟙 _) = _
  rw [← internalHomExtensionByZeroEquiv_comp, Category.comp_id]

/-- `ℋom(j_! A, B) ≅ j_* ℋom(A, j⁻¹ B)` is natural in `B`. -/
lemma internalHomExtensionByZeroIso_hom_naturality_right
    {B B' : Sheaf X.smallEtaleTopology AddCommGrpCat.{u + 1}} (b : B ⟶ B') :
    internalHomSheafMapRight _ ((extensionByZero.{u, 0} j).obj A) b ≫
        (internalHomExtensionByZeroIso j A B').hom =
      (internalHomExtensionByZeroIso j A B).hom ≫ (etaleAbelianDirectImage.{u, 0} j).map
        (internalHomSheafMapRight _ A ((etaleRestriction.{u, 0} j).map b)) := by
  rw [comp_internalHomExtensionByZeroIso_hom, ← Category.id_comp
      (internalHomSheafMapRight _ ((extensionByZero.{u, 0} j).obj A) b),
    internalHomExtensionByZeroEquiv_comp_mapRight]
  rfl

/-- `ℋom(j_! A, B) ≅ j_* ℋom(A, j⁻¹ B)` is natural in `A`. -/
lemma internalHomExtensionByZeroIso_hom_naturality_left
    {A A' : Sheaf U.smallEtaleTopology AddCommGrpCat.{u + 1}} (a : A' ⟶ A) :
    internalHomSheafMapLeft _ ((extensionByZero.{u, 0} j).map a) B ≫
        (internalHomExtensionByZeroIso j A' B).hom =
      (internalHomExtensionByZeroIso j A B).hom ≫ (etaleAbelianDirectImage.{u, 0} j).map
        (internalHomSheafMapLeft _ a ((etaleRestriction.{u, 0} j).obj B)) := by
  rw [comp_internalHomExtensionByZeroIso_hom, ← Category.id_comp
      (internalHomSheafMapLeft _ ((extensionByZero.{u, 0} j).map a) B),
    internalHomExtensionByZeroEquiv_comp_mapLeft]
  rfl

/-- **`ℋom(j_! A, -) ≅ j_* ℋom(A, j⁻¹ -)`**, as an isomorphism of functors. -/
def internalHomExtensionByZeroNatIso :
    internalHomRightFunctor X.smallEtaleTopology ((extensionByZero.{u, 0} j).obj A) ≅
      etaleRestriction.{u, 0} j ⋙ internalHomRightFunctor U.smallEtaleTopology A ⋙
        etaleAbelianDirectImage.{u, 0} j :=
  NatIso.ofComponents (fun B => internalHomExtensionByZeroIso j A B)
    (fun b => internalHomExtensionByZeroIso_hom_naturality_right j A b)

end Stacks.EtaleCohomology

end
