module

public import Mathlib.CategoryTheory.Localization.Prod
public import StacksFrontier.Homology.Tor.DerivedTensorComparisonLeft
public import StacksFrontier.Homology.Tor.DerivedTensorUniverse
public import StacksFrontier.CategoryTheory.CommutingSquares

/-!
# Restriction of scalars along a ring isomorphism carries the derived tensor product over

Let `e : R ≃+* S` be an isomorphism of commutative rings and let `ρ = restrictScalars e` be
restriction of scalars along it, an equivalence `Mod(S) ≌ Mod(R)`.  This file descends the
complex-level comparison `CochainComplex.DerivedTensor.restrictScalarsTensorComplexIso` along the
K-flat localizations to an isomorphism of bifunctors on derived categories

`ρ(x ⊗^𝐋_S y) ≅ ρ x ⊗^𝐋_R ρ y`

for `x, y ∈ D(S)`, where both derived tensor products are the canonical ones of Tag 064M.

## Main definitions

* `CochainComplex.DerivedTensor.RestrictScalars.restrictOfTensor` and
  `CochainComplex.DerivedTensor.RestrictScalars.tensorOfRestricts` — the two bifunctors
  `D(S) × D(S) ⥤ D(R)` being compared.
* `CochainComplex.DerivedTensor.RestrictScalars.restrictScalarsDerivedTensorIso` — **the
  comparison**, bifunctorial in both variables.
* `CochainComplex.DerivedTensor.RestrictScalars.restrictScalarsDerivedTensorComparison` — its
  underlying morphism of bifunctors.
* `CochainComplex.DerivedTensor.RestrictScalars.modelComparison` — the comparison on a pair of
  K-flat representatives.

## Main results

* `CochainComplex.DerivedTensor.RestrictScalars.isIso_restrictScalarsDerivedTensorComparison` —
  the comparison is invertible.

## References

* [Stacks Project, Tag 064M](https://stacks.math.columbia.edu/tag/064M)
* [Stacks Project, Tag 06Y4](https://stacks.math.columbia.edu/tag/06Y4)
* [Stacks Project, Tag 079U](https://stacks.math.columbia.edu/tag/079U)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits
open CochainComplex.KFlatBifunctor
open scoped MonoidalCategory CategoryTheory.Prod

universe u

namespace CochainComplex.DerivedTensor.RestrictScalars

attribute [local instance] HasDerivedCategory.standard

variable {R S : Type u} [CommRing R] [CommRing S] (e : R ≃+* S)

/-! ### The two bifunctors to be compared -/

/-- Restriction of scalars along `e`, on modules: the functor of
`ModuleCat.restrictScalarsEquivalenceOfRingEquiv e`. -/
abbrev restrictModules : ModuleCat.{u} S ⥤ ModuleCat.{u} R :=
  ModuleCat.restrictScalars e.toRingHom

/-- Restriction of scalars along `e`, on cochain complexes. -/
abbrev restrictComplexes :
    CochainComplex (ModuleCat.{u} S) ℤ ⥤ CochainComplex (ModuleCat.{u} R) ℤ :=
  (restrictModules e).mapHomologicalComplex (ComplexShape.up ℤ)

/-- Restriction of scalars along `e`, on derived categories. -/
abbrev restrictDerived : DObj S ⥤ DObj R := (restrictModules e).mapDerivedCategory

/-- The bifunctor `(x, y) ↦ ρ(x ⊗^𝐋_S y)` on `D(S) × D(S)`. -/
abbrev restrictOfTensor : DObj S × DObj S ⥤ DObj R :=
  Functor.uncurry.obj (canonicalDerivedTensorProductFunctor S) ⋙ restrictDerived e

/-- The bifunctor `(x, y) ↦ ρ x ⊗^𝐋_R ρ y` on `D(S) × D(S)`. -/
abbrev tensorOfRestricts : DObj S × DObj S ⥤ DObj R :=
  (restrictDerived e).prod (restrictDerived e) ⋙
    Functor.uncurry.obj (canonicalDerivedTensorProductFunctor R)

/-! ### The two legs on a pair of K-flat complexes -/

/-- **The first leg**, `ρ(QK ⊗^𝐋_S QL) ≅ Q(ρ(K ⊗_S L))` at a pair of K-flat complexes: the
K-flat comparison of Tag 064M over `S`, carried over by `ρ`, followed by the identification of
`ρ ∘ Q` with `Q ∘ ρ`. -/
def leftIso (K L : CochainComplex (ModuleCat.{u} S) ℤ) (hK : K.KFlat) (hL : L.KFlat) :
    (restrictOfTensor e).obj (DerivedCategory.Q.obj K, DerivedCategory.Q.obj L) ≅
      DerivedCategory.Q.obj ((restrictComplexes e).obj (K ⊗ L)) :=
  (restrictDerived e).mapIso ((canonicalDerivedTensorProduct S).comparison K L hK hL) ≪≫
    (restrictModules e).mapDerivedCategoryFactors.app (K ⊗ L)

/-- **The second leg**, `ρ(QK) ⊗^𝐋_R ρ(QL) ≅ Q(ρ(K ⊗_S L))` at a pair of K-flat complexes: the
identification of `ρ ∘ Q` with `Q ∘ ρ` in both variables, the K-flat comparison of Tag 064M over
`R` at the restricted complexes — K-flat by
`CochainComplex.DerivedTensor.isKFlat_restrictScalars_of_ringEquiv` — and the complex-level
comparison `CochainComplex.DerivedTensor.restrictScalarsTensorComplexIso`. -/
def rightIso (K L : CochainComplex (ModuleCat.{u} S) ℤ) (hK : K.KFlat) (hL : L.KFlat) :
    (tensorOfRestricts e).obj (DerivedCategory.Q.obj K, DerivedCategory.Q.obj L) ≅
      DerivedCategory.Q.obj ((restrictComplexes e).obj (K ⊗ L)) :=
  (Functor.uncurry.obj (canonicalDerivedTensorProductFunctor R)).mapIso
      (Iso.prod ((restrictModules e).mapDerivedCategoryFactors.app K)
        ((restrictModules e).mapDerivedCategoryFactors.app L)) ≪≫
    (canonicalDerivedTensorProduct R).comparison ((restrictComplexes e).obj K)
        ((restrictComplexes e).obj L) (isKFlat_restrictScalars_of_ringEquiv e K hK)
        (isKFlat_restrictScalars_of_ringEquiv e L hL) ≪≫
      DerivedCategory.Q.mapIso (restrictScalarsTensorComplexIso e K L)

/-! ### Naturality of the two legs -/

/-- Two factorizations of one morphism have the same image under a functor. -/
private lemma map_comp_eq {C D : Type*} [Category C] [Category D] (F : C ⥤ D)
    {A B B' Z : C} (f : A ⟶ B) (g : B ⟶ Z) (f' : A ⟶ B') (g' : B' ⟶ Z)
    (h : f ≫ g = f' ≫ g') : F.map f ≫ F.map g = F.map f' ≫ F.map g' := by
  rw [← F.map_comp, ← F.map_comp, h]

/-- Three naturality squares pasted into one. -/
private lemma three_squares {C : Type*} [Category C] {X Y Z W X' Y' Z' W' : C}
    (f : X ⟶ Y) (g : Y ⟶ Z) (h : Z ⟶ W) (f' : X' ⟶ Y') (g' : Y' ⟶ Z') (h' : Z' ⟶ W')
    (α : X ⟶ X') (β : Y ⟶ Y') (γ : Z ⟶ Z') (δ : W ⟶ W')
    (h₁ : α ≫ f' = f ≫ β) (h₂ : β ≫ g' = g ≫ γ) (h₃ : γ ≫ h' = h ≫ δ) :
    α ≫ (f' ≫ g' ≫ h') = (f ≫ g ≫ h) ≫ δ := by
  simp only [reassoc_of% h₁, reassoc_of% h₂, h₃, Category.assoc]

/-- **The first leg is natural** in cochain maps between K-flat complexes. -/
theorem leftIso_naturality {K K' L L' : CochainComplex (ModuleCat.{u} S) ℤ}
    (a : K ⟶ K') (b : L ⟶ L') (hK : K.KFlat) (hK' : K'.KFlat) (hL : L.KFlat) (hL' : L'.KFlat) :
    (restrictOfTensor e).map (DerivedCategory.Q.map a ×ₘ DerivedCategory.Q.map b) ≫
        (leftIso e K' L' hK' hL').hom =
      (leftIso e K L hK hL).hom ≫
        DerivedCategory.Q.map ((restrictComplexes e).map
          (HomologicalComplex.mapBifunctorMap a b (moduleTensor S) (ComplexShape.up ℤ))) := by
  have h₁ := (Category.assoc _ _ _).trans
    ((canonicalDerivedTensorProduct S).comparison_naturality a b hK hK' hL hL')
  have h₂ := (restrictModules e).mapDerivedCategoryFactors_hom_naturality
    (HomologicalComplex.mapBifunctorMap a b (moduleTensor S) (ComplexShape.up ℤ))
  exact CategoryTheory.map_comp_naturality (restrictDerived e) _ _ _ _ _ _ _ h₁ h₂

/-- The identification of `ρ ∘ Q` with `Q ∘ ρ` is natural in a pair of cochain maps. -/
theorem prodFactors_naturality {K K' L L' : CochainComplex (ModuleCat.{u} S) ℤ}
    (a : K ⟶ K') (b : L ⟶ L') :
    ((restrictDerived e).map (DerivedCategory.Q.map a) ×ₘ
          (restrictDerived e).map (DerivedCategory.Q.map b)) ≫
        ((restrictModules e).mapDerivedCategoryFactors.hom.app K' ×ₘ
          (restrictModules e).mapDerivedCategoryFactors.hom.app L') =
      ((restrictModules e).mapDerivedCategoryFactors.hom.app K ×ₘ
          (restrictModules e).mapDerivedCategoryFactors.hom.app L) ≫
        (DerivedCategory.Q.map ((restrictComplexes e).map a) ×ₘ
          DerivedCategory.Q.map ((restrictComplexes e).map b)) :=
  Prod.ext ((restrictModules e).mapDerivedCategoryFactors_hom_naturality a)
    ((restrictModules e).mapDerivedCategoryFactors_hom_naturality b)

/-- **The second leg is natural** in cochain maps between K-flat complexes. -/
theorem rightIso_naturality {K K' L L' : CochainComplex (ModuleCat.{u} S) ℤ}
    (a : K ⟶ K') (b : L ⟶ L') (hK : K.KFlat) (hK' : K'.KFlat) (hL : L.KFlat) (hL' : L'.KFlat) :
    (tensorOfRestricts e).map (DerivedCategory.Q.map a ×ₘ DerivedCategory.Q.map b) ≫
        (rightIso e K' L' hK' hL').hom =
      (rightIso e K L hK hL).hom ≫
        DerivedCategory.Q.map ((restrictComplexes e).map
          (HomologicalComplex.mapBifunctorMap a b (moduleTensor S) (ComplexShape.up ℤ))) := by
  refine three_squares
    ((Functor.uncurry.obj (canonicalDerivedTensorProductFunctor R)).map
      ((restrictModules e).mapDerivedCategoryFactors.hom.app K ×ₘ
        (restrictModules e).mapDerivedCategoryFactors.hom.app L))
    ((canonicalDerivedTensorProduct R).comparison ((restrictComplexes e).obj K)
      ((restrictComplexes e).obj L) (isKFlat_restrictScalars_of_ringEquiv e K hK)
      (isKFlat_restrictScalars_of_ringEquiv e L hL)).hom
    (DerivedCategory.Q.map (restrictScalarsTensorComplexIso e K L).hom)
    ((Functor.uncurry.obj (canonicalDerivedTensorProductFunctor R)).map
      ((restrictModules e).mapDerivedCategoryFactors.hom.app K' ×ₘ
        (restrictModules e).mapDerivedCategoryFactors.hom.app L'))
    ((canonicalDerivedTensorProduct R).comparison ((restrictComplexes e).obj K')
      ((restrictComplexes e).obj L') (isKFlat_restrictScalars_of_ringEquiv e K' hK')
      (isKFlat_restrictScalars_of_ringEquiv e L' hL')).hom
    (DerivedCategory.Q.map (restrictScalarsTensorComplexIso e K' L').hom) _
    ((Functor.uncurry.obj (canonicalDerivedTensorProductFunctor R)).map
      (DerivedCategory.Q.map ((restrictComplexes e).map a) ×ₘ
        DerivedCategory.Q.map ((restrictComplexes e).map b)))
    (DerivedCategory.Q.map (HomologicalComplex.mapBifunctorMap ((restrictComplexes e).map a)
      ((restrictComplexes e).map b) (moduleTensor R) (ComplexShape.up ℤ))) _ ?_ ?_ ?_
  · exact map_comp_eq (Functor.uncurry.obj (canonicalDerivedTensorProductFunctor R)) _ _ _ _
      (prodFactors_naturality e a b)
  · exact (Category.assoc _ _ _).trans
      ((canonicalDerivedTensorProduct R).comparison_naturality ((restrictComplexes e).map a)
        ((restrictComplexes e).map b) (isKFlat_restrictScalars_of_ringEquiv e K hK)
        (isKFlat_restrictScalars_of_ringEquiv e K' hK')
        (isKFlat_restrictScalars_of_ringEquiv e L hL)
        (isKFlat_restrictScalars_of_ringEquiv e L' hL'))
  · exact map_comp_eq DerivedCategory.Q _ _ _ _
      (restrictScalarsTensorComplexIso_naturality e a b)

/-! ### The comparison on K-flat representatives -/

/-- **The comparison at a pair of K-flat complexes**: both legs land in `Q(ρ(K ⊗_S L))`, so they
compose to `ρ(QK ⊗^𝐋_S QL) ≅ ρ(QK) ⊗^𝐋_R ρ(QL)`. -/
def modelComparison (K L : CochainComplex (ModuleCat.{u} S) ℤ) (hK : K.KFlat) (hL : L.KFlat) :
    (restrictOfTensor e).obj (DerivedCategory.Q.obj K, DerivedCategory.Q.obj L) ≅
      (tensorOfRestricts e).obj (DerivedCategory.Q.obj K, DerivedCategory.Q.obj L) :=
  leftIso e K L hK hL ≪≫ (rightIso e K L hK hL).symm

/-- The comparison at a pair of K-flat complexes is natural in cochain maps between them. -/
theorem modelComparison_naturality {K K' L L' : CochainComplex (ModuleCat.{u} S) ℤ}
    (a : K ⟶ K') (b : L ⟶ L') (hK : K.KFlat) (hK' : K'.KFlat) (hL : L.KFlat) (hL' : L'.KFlat) :
    (restrictOfTensor e).map (DerivedCategory.Q.map a ×ₘ DerivedCategory.Q.map b) ≫
        (modelComparison e K' L' hK' hL').hom =
      (modelComparison e K L hK hL).hom ≫
        (tensorOfRestricts e).map (DerivedCategory.Q.map a ×ₘ DerivedCategory.Q.map b) :=
  CategoryTheory.comp_symm_naturality (leftIso e K L hK hL) (rightIso e K L hK hL)
    (leftIso e K' L' hK' hL') (rightIso e K' L' hK' hL') _ _ _
    (leftIso_naturality e a b hK hK' hL hL') (rightIso_naturality e a b hK hK' hL hL')

/-! ### Descent along the K-flat localization -/

/-- The K-flat complexes of `S`-modules, viewed in `D(S)`. -/
abbrev kFlatQModules := kFlatQ (MonoidalCategory.curriedTensor (ModuleCat.{u} S))

/-- Pairs of K-flat complexes, viewed in `D(S) × D(S)`. -/
abbrev kFlatQModulesPair := (kFlatQModules (S := S)).prod (kFlatQModules (S := S))

/-- The quasi-isomorphisms between pairs of K-flat complexes. -/
abbrev kFlatQuasiIsoModulesPair :=
  (kFlatQuasiIso (MonoidalCategory.curriedTensor (ModuleCat.{u} S))).prod
    (kFlatQuasiIso (MonoidalCategory.curriedTensor (ModuleCat.{u} S)))

/-- **`D(S) × D(S)` is the localization of the pairs of K-flat complexes at the
quasi-isomorphisms.** -/
theorem kFlatQModulesPair_isLocalization :
    (kFlatQModulesPair (S := S)).IsLocalization (kFlatQuasiIsoModulesPair (S := S)) := by
  have : (kFlatQuasiIso (MonoidalCategory.curriedTensor
      (ModuleCat.{u} S))).ContainsIdentities := by infer_instance
  exact Functor.IsLocalization.prod (kFlatQModules (S := S)) _ (kFlatQModules (S := S)) _

/-- The image in `D(S) × D(S)` of a pair of K-flat objects of the homotopy category is the image
of the underlying pair of complexes. -/
def kFlatQModulesPairIso
    (M : (kFlatObjects (MonoidalCategory.curriedTensor (ModuleCat.{u} S))).FullSubcategory ×
      (kFlatObjects (MonoidalCategory.curriedTensor (ModuleCat.{u} S))).FullSubcategory) :
    (kFlatQModulesPair (S := S)).obj M ≅
      (DerivedCategory.Q.obj M.1.obj.as, DerivedCategory.Q.obj M.2.obj.as) :=
  ((DerivedCategory.quotientCompQhIso _).app M.1.obj.as).prod
    ((DerivedCategory.quotientCompQhIso _).app M.2.obj.as)

/-- `kFlatQModulesPairIso` is natural, the target morphism being the image of chosen cochain
representatives of the two homotopy classes. -/
theorem kFlatQModulesPairIso_naturality
    {M N : (kFlatObjects (MonoidalCategory.curriedTensor (ModuleCat.{u} S))).FullSubcategory ×
      (kFlatObjects (MonoidalCategory.curriedTensor
        (ModuleCat.{u} S))).FullSubcategory} (g : M ⟶ N) :
    (kFlatQModulesPair (S := S)).map g ≫ (kFlatQModulesPairIso N).hom =
      (kFlatQModulesPairIso M).hom ≫
        (DerivedCategory.Q.map g.1.hom.out ×ₘ DerivedCategory.Q.map g.2.hom.out) := by
  have key : ∀ {A B : (kFlatObjects (MonoidalCategory.curriedTensor
        (ModuleCat.{u} S))).FullSubcategory} (f : A ⟶ B),
      DerivedCategory.Qh.map f.hom ≫ (DerivedCategory.quotientCompQhIso _).hom.app B.obj.as =
        (DerivedCategory.quotientCompQhIso _).hom.app A.obj.as ≫
          DerivedCategory.Q.map f.hom.out := fun f => by
    have h := DerivedCategory.quotientCompQhIso_hom_naturality
      (C := ModuleCat.{u} S) f.hom.out
    rw [HomotopyCategory.quotient_map_out] at h
    exact h
  exact Prod.ext (key g.1) (key g.2)

/-- **The comparison on K-flat representatives, as an isomorphism of functors** on pairs of
K-flat objects of the homotopy category.  Its value at a pair is `modelComparison`, transported
along `kFlatQModulesPairIso`. -/
def modelsComparison :
    kFlatQModulesPair (S := S) ⋙ restrictOfTensor e ≅
      kFlatQModulesPair (S := S) ⋙ tensorOfRestricts e :=
  NatIso.ofComponents
    (fun M => (restrictOfTensor e).mapIso (kFlatQModulesPairIso M) ≪≫
      modelComparison e M.1.obj.as M.2.obj.as M.1.property M.2.property ≪≫
        ((tensorOfRestricts e).mapIso (kFlatQModulesPairIso M)).symm)
    (fun {M N} g => by
      refine CategoryTheory.naturality_transport _ _ (kFlatQModulesPairIso M)
        (kFlatQModulesPairIso N) (modelComparison e M.1.obj.as M.2.obj.as M.1.property M.2.property)
        (modelComparison e N.1.obj.as N.2.obj.as N.1.property N.2.property)
        ((kFlatQModulesPair (S := S)).map g) _ (kFlatQModulesPairIso_naturality g) ?_
      exact modelComparison_naturality e g.1.hom.out g.2.hom.out
        M.1.property N.1.property M.2.property N.2.property)

attribute [local instance] kFlatQModulesPair_isLocalization

/-- **Restriction of scalars along a ring isomorphism carries the derived tensor product to the
derived tensor product.**

`ρ(x ⊗^𝐋_S y) ≅ ρ x ⊗^𝐋_R ρ y`,

bifunctorial in `x, y ∈ D(S)`. -/
def restrictScalarsDerivedTensorIso : restrictOfTensor e ≅ tensorOfRestricts e :=
  Localization.liftNatIso (kFlatQModulesPair (S := S)) (kFlatQuasiIsoModulesPair (S := S)) _ _ _ _
    (modelsComparison e)

/-- The morphism of bifunctors underlying `restrictScalarsDerivedTensorIso`. -/
def restrictScalarsDerivedTensorComparison :
    Functor.uncurry.obj (canonicalDerivedTensorProductFunctor S) ⋙ restrictDerived e ⟶
      (restrictDerived e).prod (restrictDerived e) ⋙
        Functor.uncurry.obj (canonicalDerivedTensorProductFunctor R) :=
  (restrictScalarsDerivedTensorIso e).hom

/-- The comparison is invertible. -/
instance isIso_restrictScalarsDerivedTensorComparison :
    IsIso (restrictScalarsDerivedTensorComparison e) :=
  inferInstanceAs (IsIso (restrictScalarsDerivedTensorIso e).hom)

end CochainComplex.DerivedTensor.RestrictScalars

end
