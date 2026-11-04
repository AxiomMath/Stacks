module

public import StacksFrontier.AlgebraicGeometry.ProEtale.Constructible.ConstantAdicQuotientTower
public import StacksFrontier.CategoryTheory.Sites.DerivedTensorModuleSheaf.DerivedTensorSingle

/-!
# The tower of termwise reductions of a complex of sheaves of modules

Let `(C, J)` be a site, `A` a commutative ring and `𝔞 ⊆ A` an ideal. For a complex `K` of
sheaves of `A`-modules, the termwise tensor products `p ↦ K^p ⊗_A \underline{A/𝔞ʲ}` form a tower
of complexes indexed by `j`, the transition maps being induced by the reductions
`A/𝔞ʲ⁺¹ → A/𝔞ʲ`, and the maps `K ≅ K ⊗_A \underline{A} → K ⊗_A \underline{A/𝔞ʲ}` form a cone
over it. For a K-flat complex `K` this tower computes the derived reductions
`K ⊗_A^L \underline{A/𝔞ʲ}`.

## Main definitions

* `Stacks.ModuleSheaf.rowComplexUnitIso`: the termwise right unitor
  `K ⊗_A \underline{A} ≅ K`.
* `Stacks.ModuleSheaf.rowAdicTower`: the tower `j ↦ K ⊗_A \underline{A/𝔞ʲ}` (termwise).
* `Stacks.ModuleSheaf.rowAdicTowerCone`: the cone `K ⟶ K ⊗_A \underline{A/𝔞ʲ}`.

## Main results

* `CochainComplex.KFlatBifunctor.rowComplexMap_comp_rowComplexMapRight`: the termwise complex
  `p ↦ F(K^p, M)` is functorial in both variables.
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits MonoidalCategory Opposite

universe w v u

namespace CochainComplex.KFlatBifunctor

variable {A B D : Type*} [Category A] [Category B] [Category D] [Abelian A] [Abelian B] [Abelian D]
  (F : A ⥤ B ⥤ D) [F.Additive]

/-- **The termwise complex `p ↦ F(K^p, M)` is functorial in both variables**: a morphism of
complexes `K ⟶ K'` and a morphism `M ⟶ M'` induce commuting squares. -/
@[reassoc]
theorem rowComplexMap_comp_rowComplexMapRight [∀ X, (F.obj X).Additive]
    {K K' : CochainComplex A ℤ} (f : K ⟶ K') {M M' : B} (g : M ⟶ M') :
    rowComplexMap F f M ≫ rowComplexMapRight F K' g =
      rowComplexMapRight F K g ≫ rowComplexMap F f M' :=
  HomologicalComplex.hom_ext _ _ fun p => ((F.map (f.f p)).naturality g).symm

end CochainComplex.KFlatBifunctor

namespace Stacks.ModuleSheaf

open CochainComplex.KFlatBifunctor

attribute [local instance] Sheaf.monoidalCategory

variable {C : Type u} [Category.{v} C] (J : GrothendieckTopology C) {A : Type w} [CommRing A]
  [UnivLE.{max u v, w}]

/-- The termwise right unitor: the termwise tensor product of a complex `K` of sheaves of
`A`-modules with the constant sheaf `\underline{A}` is `K`. -/
def rowComplexUnitIso (K : CochainComplex (Sheaf J (ModuleCat.{w} A)) ℤ) :
    (rowFunctor (curriedTensor _) K).obj
      ((constantSheaf J (ModuleCat.{w} A)).obj (ModuleCat.of A A)) ≅ K :=
  HomologicalComplex.Hom.isoOfComponents (fun p => ρ_ (K.X p)) (fun p q _ =>
    (rightUnitor_naturality (K.d p q)).symm)

/-- The termwise right unitor is natural in the complex. -/
@[reassoc]
theorem rowComplexUnitIso_hom_naturality {K K' : CochainComplex (Sheaf J (ModuleCat.{w} A)) ℤ}
    (f : K ⟶ K') :
    rowComplexMap (curriedTensor _) f _ ≫ (rowComplexUnitIso J K').hom =
      (rowComplexUnitIso J K).hom ≫ f :=
  HomologicalComplex.hom_ext _ _ fun p => rightUnitor_naturality (f.f p)

/-- **The tower of termwise reductions** `j ↦ K ⊗_A \underline{A/𝔞ʲ}` of a complex `K` of
sheaves of `A`-modules, with the transition maps induced by the reductions `A/𝔞ʲ⁺¹ → A/𝔞ʲ`. -/
abbrev rowAdicTower (𝔞 : Ideal A) (K : CochainComplex (Sheaf J (ModuleCat.{w} A)) ℤ) :
    ℕᵒᵖ ⥤ CochainComplex (Sheaf J (ModuleCat.{w} A)) ℤ :=
  constantAdicQuotientTower J A 𝔞 (ModuleCat.of A A) ⋙ rowFunctor (curriedTensor _) K

/-- The cone of reductions `K ≅ K ⊗_A \underline{A} ⟶ K ⊗_A \underline{A/𝔞ʲ}` over the tower of
termwise reductions. -/
def rowAdicTowerCone (𝔞 : Ideal A) (K : CochainComplex (Sheaf J (ModuleCat.{w} A)) ℤ) :
    (Functor.const ℕᵒᵖ).obj K ⟶ rowAdicTower J 𝔞 K :=
  (Functor.const ℕᵒᵖ).map (rowComplexUnitIso J K).inv ≫
    (Functor.constComp ℕᵒᵖ _ (rowFunctor (curriedTensor _) K)).inv ≫
      Functor.whiskerRight (constantAdicQuotientCone J A 𝔞 (ModuleCat.of A A))
        (rowFunctor (curriedTensor _) K)

/-- The component at `j` of the cone of reductions is the inverse of the termwise right unitor
followed by the termwise map induced by the reduction `\underline{A} → \underline{A/𝔞ʲ}`. -/
theorem rowAdicTowerCone_app (𝔞 : Ideal A) (K : CochainComplex (Sheaf J (ModuleCat.{w} A)) ℤ)
    (j : ℕᵒᵖ) :
    (rowAdicTowerCone J 𝔞 K).app j = (rowComplexUnitIso J K).inv ≫
      rowComplexMapRight (curriedTensor _) K
        ((constantAdicQuotientCone J A 𝔞 (ModuleCat.of A A)).app j) := by
  simp only [Functor.const_obj_obj, Functor.comp_obj, rowAdicTowerCone, NatTrans.comp_app,
    Functor.const_map_app, Functor.constComp_inv_app, Functor.whiskerRight_app, rowFunctor_map]
  rfl

/-- The tower of termwise reductions is functorial in the complex. -/
def rowAdicTowerMap (𝔞 : Ideal A) {K K' : CochainComplex (Sheaf J (ModuleCat.{w} A)) ℤ}
    (f : K ⟶ K') : rowAdicTower J 𝔞 K ⟶ rowAdicTower J 𝔞 K' where
  app _ := rowComplexMap (curriedTensor _) f _
  naturality _ _ _ := (rowComplexMap_comp_rowComplexMapRight _ f _).symm

/-- The component at `j` of the map of towers induced by `f : K ⟶ K'` is the termwise map
`K ⊗_A \underline{A/𝔞ʲ} ⟶ K' ⊗_A \underline{A/𝔞ʲ}` induced by `f`. -/
@[simp]
theorem rowAdicTowerMap_app (𝔞 : Ideal A) {K K' : CochainComplex (Sheaf J (ModuleCat.{w} A)) ℤ}
    (f : K ⟶ K') (j : ℕᵒᵖ) :
    (rowAdicTowerMap J 𝔞 f).app j = rowComplexMap (curriedTensor _) f _ :=
  rfl

end Stacks.ModuleSheaf
