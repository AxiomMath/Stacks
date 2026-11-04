module

public import StacksFrontier.CategoryTheory.Sites.Cohomology.InternalHom.DualityDescentDiagrams
public import StacksFrontier.Topology.Sheaves.Cohomology.InternalHom.DerivedAssociatorComparison

/-!
# The associativity constraint of `D(O_X)` against the canonical map to the total tensor complex

Let `(X, O_X)` be a ringed space and let `A`, `B`, `D` be complexes of `O_X`-modules.  Write
`t_{A,B} : QA ⊗^L QB ⟶ Q(Tot(A ⊗ B))` for the canonical map of Stacks 06YU from the derived tensor
product to the total tensor complex.  Then

`(t_{A,B} ▷ QD) ≫ t_{A ⊗ B, D} ≫ Q(α_{A,B,D}) = α_{QA,QB,QD} ≫ (QA ◁ t_{B,D}) ≫ t_{A, B ⊗ D}`,

with no flatness hypothesis on `A`, `B` or `D`: the associativity constraint of the monoidal
structure of Stacks 0FPT on `D(O_X)` is carried by `t` to the associator of total tensor
complexes.

## Main definitions

* `Stacks.SheafOfModules.derivedToTensorHom`: the canonical map `t_{A,B}` of Stacks 06YU.

## Main results

* `Stacks.SheafOfModules.derivedToTensorHom_naturality`: `t_{A,B}` is natural in `A` and `B`.
* `Stacks.SheafOfModules.derivedAssociator_toTensor`: the displayed identity, for arbitrary
  complexes `A`, `B`, `D`.
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.MonoidalCategory TopologicalSpace Opposite AlgebraicGeometry

universe u

/-- **Descent of an associativity square along isomorphisms**, for an arbitrary bifunctor `F`
with a family of associativity morphisms.  If the square holds for `A'`, `B'`, `D'`, the maps `t`
are natural along `a`, `b`, `d`, `q` and the associativity morphisms are natural along `a`, `b`,
`d`, with `a`, `b`, `d` invertible, then it holds for `A`, `B`, `D`. -/
private alias assoc_descent := Stacks.Cohomology.DualityDescent.assoc_descent

namespace Stacks.SheafOfModules

attribute [local instance] HasDerivedCategory.standard

variable {X : TopCat.{u}} (Rc : TopCat.Sheaf CommRingCat.{u} X)
  [HasSheafify (Opens.grothendieckTopology X) AddCommGrpCat.{u}]
  [(Opens.grothendieckTopology X).WEqualsLocallyBijective AddCommGrpCat.{u}]

attribute [local instance] Stacks.SheafOfModules.monoidalSpace'
  Stacks.SheafOfModules.symmetricSpace' Stacks.SheafOfModules.monoidalPreadditiveSpace'
  Stacks.SheafOfModules.monoidalClosedSpace'

variable [(Tensor.sheafTensor.{u, u, u, u, u} Rc).Additive]
  [∀ M, ((Tensor.sheafTensor.{u, u, u, u, u} Rc).obj M).Additive]
  [∀ (K₁ K₂ : CochainComplex (SheafOfModules.{u} (Tensor.ringSheaf.{u, u, u} Rc)) ℤ),
    HomologicalComplex.HasMapBifunctor K₁ K₂ (Tensor.sheafTensor Rc) (ComplexShape.up ℤ)]

attribute [local instance 10000] CochainComplex.symmetricCategory
attribute [local instance 100000] monoidalCategoryStructComplexesAC

omit [(Tensor.sheafTensor.{u, u, u, u, u} Rc).Additive]
  [∀ M, ((Tensor.sheafTensor.{u, u, u, u, u} Rc).obj M).Additive]
  [∀ (K₁ K₂ : CochainComplex (SheafOfModules.{u} (Tensor.ringSheaf.{u, u, u} Rc)) ℤ),
    HomologicalComplex.HasMapBifunctor K₁ K₂ (Tensor.sheafTensor Rc) (ComplexShape.up ℤ)] in
/-- The associator of total tensor complexes is natural in all three complexes. -/
theorem complexAssociator_naturality
    {A A' B B' D D' : CochainComplex (StructureSheafModules Rc) ℤ}
    (a : A' ⟶ A) (b : B' ⟶ B) (d : D' ⟶ D) :
    ((a ⊗ₘ b) ⊗ₘ d) ≫ (α_ A B D).hom = (α_ A' B' D').hom ≫ (a ⊗ₘ (b ⊗ₘ d)) :=
  @associator_naturality _ _
    (Stacks.Cohomology.MonoidalComplexesOfModules.cochainComplexMonoidalCategory Rc) _ _ _ _ _ _
    a b d

omit [(Tensor.sheafTensor.{u, u, u, u, u} Rc).Additive]
  [∀ M, ((Tensor.sheafTensor.{u, u, u, u, u} Rc).obj M).Additive]
  [∀ (K₁ K₂ : CochainComplex (SheafOfModules.{u} (Tensor.ringSheaf.{u, u, u} Rc)) ℤ),
    HomologicalComplex.HasMapBifunctor K₁ K₂ (Tensor.sheafTensor Rc) (ComplexShape.up ℤ)] in
/-- The associator of total tensor complexes, read in `D(O_X)`, is natural in all three
complexes. -/
theorem complexAssociatorHomSpace_naturality
    {A A' B B' D D' : CochainComplex (StructureSheafModules Rc) ℤ}
    (a : A' ⟶ A) (b : B' ⟶ B) (d : D' ⟶ D) :
    DerivedCategory.Q.map ((a ⊗ₘ b) ⊗ₘ d) ≫ complexAssociatorHomSpace Rc A B D =
      complexAssociatorHomSpace Rc A' B' D' ≫ DerivedCategory.Q.map (a ⊗ₘ (b ⊗ₘ d)) := by
  rw [complexAssociatorHomSpace, complexAssociatorHomSpace, ← Functor.map_comp,
    ← Functor.map_comp, complexAssociator_naturality Rc a b d]

/-- **The canonical map of Stacks 06YU** from the derived tensor product to the total tensor
complex, at the `⊗` spelling of its target. -/
def derivedToTensorHom (A B : CochainComplex (StructureSheafModules Rc) ℤ) :
    ((derivedTensor Rc).obj (DerivedCategory.Q.obj A)).obj (DerivedCategory.Q.obj B) ⟶
      DerivedCategory.Q.obj ((A ⊗ B : CochainComplex (StructureSheafModules Rc) ℤ)) :=
  (canonicalDerivedTensorProduct (ringedSite Rc)).toTensor A B

/-- On two K-flat complexes the canonical map is the K-flat comparison. -/
theorem derivedToTensorHom_eq_comparisonHom (A B : CochainComplex (StructureSheafModules Rc) ℤ)
    (hA : KFlat.KFlat Rc A) (hB : KFlat.KFlat Rc B) :
    derivedToTensorHom Rc A B = derivedTensorComparisonHom Rc A B hA hB := by
  rw [derivedToTensorHom, derivedTensorComparisonHom,
    (canonicalDerivedTensorProduct (ringedSite Rc)).toTensor_eq_comparisonRight A B hB,
    (canonicalDerivedTensorProduct (ringedSite Rc)).comparisonRight_eq_comparison A B hA hB]
  rfl

/-- The canonical map is natural in both complexes. -/
theorem derivedToTensorHom_naturality {A A' B B' : CochainComplex (StructureSheafModules Rc) ℤ}
    (f : A ⟶ A') (g : B ⟶ B') :
    derivedWhiskerRight Rc (DerivedCategory.Q.map f) (DerivedCategory.Q.obj B) ≫
        derivedWhiskerLeft Rc (DerivedCategory.Q.obj A') (DerivedCategory.Q.map g) ≫
        derivedToTensorHom Rc A' B' =
      derivedToTensorHom Rc A B ≫ DerivedCategory.Q.map (f ⊗ₘ g) :=
  (canonicalDerivedTensorProduct (ringedSite Rc)).toTensor_naturality f g

/-- On K-flat complexes `A`, `B`, `D`, the associativity constraint of `D(O_X)` is carried by
the canonical map `derivedToTensorHom` to the associator of total tensor complexes. -/
theorem derivedAssociator_toTensor_of_kFlat (A B D : CochainComplex (StructureSheafModules Rc) ℤ)
    (hA : KFlat.KFlat Rc A) (hB : KFlat.KFlat Rc B) (hD : KFlat.KFlat Rc D) :
    derivedWhiskerRight Rc (derivedToTensorHom Rc A B) (DerivedCategory.Q.obj D) ≫
        derivedToTensorHom Rc (A ⊗ B) D ≫ complexAssociatorHomSpace Rc A B D =
      derivedAssociatorHom Rc (DerivedCategory.Q.obj A) (DerivedCategory.Q.obj B)
          (DerivedCategory.Q.obj D) ≫
        derivedWhiskerLeft Rc (DerivedCategory.Q.obj A) (derivedToTensorHom Rc B D) ≫
          derivedToTensorHom Rc A (B ⊗ D) := by
  rw [derivedToTensorHom_eq_comparisonHom Rc A B hA hB,
    derivedToTensorHom_eq_comparisonHom Rc B D hB hD,
    derivedToTensorHom_eq_comparisonHom Rc (A ⊗ B) D
      (DerivedMonoidal.kFlat_tensor_complexes Rc hA hB) hD,
    derivedToTensorHom_eq_comparisonHom Rc A (B ⊗ D) hA
      (DerivedMonoidal.kFlat_tensor_complexes Rc hB hD)]
  exact derivedAssociator_comparison Rc A B D hA hB hD

/-- The associativity constraint of `D(O_X)` is natural in all three variables, in the bifunctor
spelling of `Stacks.SheafOfModules.derivedAssociatorHom`. -/
theorem derivedAssociatorHom_naturality
    {A A' B B' D D' : DerivedCategory (StructureSheafModules Rc)}
    (a : A' ⟶ A) (b : B' ⟶ B) (d : D' ⟶ D) :
    derivedWhiskerRight Rc (derivedWhiskerRight Rc a B' ≫ derivedWhiskerLeft Rc A b) D' ≫
        derivedWhiskerLeft Rc _ d ≫ derivedAssociatorHom Rc A B D =
      derivedAssociatorHom Rc A' B' D' ≫ derivedWhiskerRight Rc a _ ≫
        derivedWhiskerLeft Rc A (derivedWhiskerRight Rc b D' ≫ derivedWhiskerLeft Rc B d) := by
  let := derivedMonoidalStructure Rc
  have h := associator_naturality a b d
  rw [tensorHom_def, tensorHom_def, tensorHom_def, tensorHom_def, Category.assoc] at h
  exact h

/-- Every complex receives a K-flat complex by a map that becomes invertible in `D(O_X)`. -/
private theorem exists_kFlat_isIso_Q_map (A : CochainComplex (StructureSheafModules Rc) ℤ) :
    ∃ (A' : CochainComplex (StructureSheafModules Rc) ℤ) (a : A' ⟶ A),
      KFlat.KFlat Rc A' ∧ IsIso (DerivedCategory.Q.map a) := by
  obtain ⟨A', a, hA', h⟩ := Stacks.DerivedTensor.RingedSite.exists_kFlat_quasiIso Rc A
  exact ⟨A', a, hA', (DerivedCategory.isIso_Q_map_iff_quasiIso _ _).2 h⟩

/-- **The associativity constraint of `D(O_X)` is the associator of total tensor complexes**,
carried across by the canonical map `t` of Stacks 06YU: for arbitrary complexes `A`, `B`, `D` of
`O_X`-modules,

`(t_{A,B} ▷ QD) ≫ t_{A ⊗ B, D} ≫ Q(α_{A,B,D}) = α_{QA,QB,QD} ≫ (QA ◁ t_{B,D}) ≫ t_{A, B ⊗ D}`. -/
theorem derivedAssociator_toTensor (A B D : CochainComplex (StructureSheafModules Rc) ℤ) :
    derivedWhiskerRight Rc (derivedToTensorHom Rc A B) (DerivedCategory.Q.obj D) ≫
        derivedToTensorHom Rc (A ⊗ B) D ≫ complexAssociatorHomSpace Rc A B D =
      derivedAssociatorHom Rc (DerivedCategory.Q.obj A) (DerivedCategory.Q.obj B)
          (DerivedCategory.Q.obj D) ≫
        derivedWhiskerLeft Rc (DerivedCategory.Q.obj A) (derivedToTensorHom Rc B D) ≫
          derivedToTensorHom Rc A (B ⊗ D) := by
  obtain ⟨A', a, hA', _⟩ := exists_kFlat_isIso_Q_map Rc A
  obtain ⟨B', b, hB', _⟩ := exists_kFlat_isIso_Q_map Rc B
  obtain ⟨D', d, hD', _⟩ := exists_kFlat_isIso_Q_map Rc D
  exact assoc_descent (derivedTensor Rc) (DerivedCategory.Q.map a) (DerivedCategory.Q.map b)
    (DerivedCategory.Q.map d) (derivedToTensorHom Rc A B) (derivedToTensorHom Rc A' B')
    (DerivedCategory.Q.map (a ⊗ₘ b)) (derivedToTensorHom_naturality Rc a b)
    (derivedToTensorHom Rc B D) (derivedToTensorHom Rc B' D')
    (DerivedCategory.Q.map (b ⊗ₘ d)) (derivedToTensorHom_naturality Rc b d)
    (derivedToTensorHom Rc (A ⊗ B) D) (derivedToTensorHom Rc (A' ⊗ B') D')
    (DerivedCategory.Q.map ((a ⊗ₘ b) ⊗ₘ d)) (derivedToTensorHom_naturality Rc (a ⊗ₘ b) d)
    (derivedToTensorHom Rc A (B ⊗ D)) (derivedToTensorHom Rc A' (B' ⊗ D'))
    (DerivedCategory.Q.map (a ⊗ₘ (b ⊗ₘ d))) (derivedToTensorHom_naturality Rc a (b ⊗ₘ d))
    (complexAssociatorHomSpace Rc A B D) (complexAssociatorHomSpace Rc A' B' D')
    (complexAssociatorHomSpace_naturality Rc a b d)
    (derivedAssociatorHom Rc _ _ _) (derivedAssociatorHom Rc _ _ _)
    (derivedAssociatorHom_naturality Rc _ _ _)
    (derivedAssociator_toTensor_of_kFlat Rc A' B' D' hA' hB' hD')

end Stacks.SheafOfModules

end
