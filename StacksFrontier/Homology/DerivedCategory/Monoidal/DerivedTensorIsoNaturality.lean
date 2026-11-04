module

public import StacksFrontier.Topology.Sheaves.Cohomology.InternalHom.DerivedMonoidalStructure
public import StacksFrontier.CategoryTheory.Sites.Cohomology.Monoidal.DerivedCategory

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits CategoryTheory.MonoidalCategory

universe w v u

namespace CochainComplex.KFlatMonoidal

variable (A : Type u) [Category.{v} A] [Abelian A] [MonoidalCategory A]
  [(curriedTensor A).Additive] [∀ X : A, ((curriedTensor A).obj X).Additive]
  [∀ X₁ X₂ : GradedObject ℤ A, GradedObject.HasTensor X₁ X₂]
  [∀ X₁ : A, PreservesColimit (Functor.empty.{0} A) ((curriedTensor A).obj X₁)]
  [∀ X₂ : A, PreservesColimit (Functor.empty.{0} A) ((curriedTensor A).flip.obj X₂)]
  [∀ X₁ X₂ X₃ X₄ : GradedObject ℤ A, GradedObject.HasTensor₄ObjExt X₁ X₂ X₃ X₄]
  [∀ X₁ X₂ X₃ : GradedObject ℤ A, GradedObject.HasGoodTensor₁₂Tensor X₁ X₂ X₃]
  [∀ X₁ X₂ X₃ : GradedObject ℤ A, GradedObject.HasGoodTensorTensor₂₃ X₁ X₂ X₃]
  [SymmetricCategory (CochainComplex A ℤ)] [HasDerivedCategory.{w} A]
  (hres : ∀ G : CochainComplex A ℤ, ∃ (P : CochainComplex A ℤ) (f : P ⟶ G),
    _root_.CochainComplex.KFlatBifunctor.KFlat (curriedTensor A) P ∧ QuasiIso f)

/-- For a morphism `g : K₁ ⟶ K₂` of K-flat cochain complexes and a K-flat complex `L`, the
comparison isomorphisms `Q(K) ⊗ Q(L) ≅ Q(K ⊗ L)` given by `derivedTensorIso` are natural in the
left variable: `Q(g) ▷ Q(L)` followed by the comparison at `K₂` equals the comparison at `K₁`
followed by `Q(g ▷ L)`. -/
theorem derivedTensorIso_hom_natural_left {K₁ K₂ L : CochainComplex A ℤ} (g : K₁ ⟶ K₂)
    (h₁ : _root_.CochainComplex.KFlatBifunctor.KFlat (curriedTensor A) K₁)
    (h₂ : _root_.CochainComplex.KFlatBifunctor.KFlat (curriedTensor A) K₂)
    (hL : _root_.CochainComplex.KFlatBifunctor.KFlat (curriedTensor A) L) :
    letI := derivedMonoidal A hres
    DerivedCategory.Q.map g ▷ DerivedCategory.Q.obj L ≫ (derivedTensorIso A hres h₂ hL).hom =
      (derivedTensorIso A hres h₁ hL).hom ≫ DerivedCategory.Q.map (g ▷ L) := by
  let := derivedMonoidal A hres
  let := kFlatQRestrictionMonoidal A hres
  rw [← mu_kFlatQRestriction A hres h₂ hL, ← mu_kFlatQRestriction A hres h₁ hL]
  exact Functor.LaxMonoidal.μ_natural_left (kFlatQRestriction A)
    (ObjectProperty.homMk g :
      (⟨K₁, h₁⟩ : (_root_.CochainComplex.KFlatBifunctor.kFlatComplexes
        (curriedTensor A)).FullSubcategory) ⟶ ⟨K₂, h₂⟩) ⟨L, hL⟩

/-- For a morphism `j : K ⟶ K'` of cochain complexes with `K'` and `L` K-flat, there is an
isomorphism `Θ : Q(K ⊗ L) ≅ Q(K) ⊗ Q(L)` such that `Θ` followed by `Q(j) ▷ Q(L)` equals
`Q(j ▷ L)` followed by the inverse of the comparison isomorphism `derivedTensorIso` at `K'`
and `L`. -/
theorem exists_iso_whiskerRight_comp {K K' L : CochainComplex A ℤ} (j : K ⟶ K')
    (hK' : _root_.CochainComplex.KFlatBifunctor.KFlat (curriedTensor A) K')
    (hL : _root_.CochainComplex.KFlatBifunctor.KFlat (curriedTensor A) L) :
    letI := derivedMonoidal A hres
    ∃ Θ : DerivedCategory.Q.obj (K ⊗ L) ≅ DerivedCategory.Q.obj K ⊗ DerivedCategory.Q.obj L,
      Θ.hom ≫ (DerivedCategory.Q.map j ▷ DerivedCategory.Q.obj L) =
        DerivedCategory.Q.map (j ▷ L) ≫ (derivedTensorIso A hres hK' hL).inv := by
  let := derivedMonoidal A hres
  obtain ⟨P, p, hP, hp⟩ := hres K
  have hpL : IsIso (DerivedCategory.Q.map (p ▷ L)) :=
    (DerivedCategory.isIso_Q_map_iff_quasiIso (C := A) _).2
      (_root_.CochainComplex.KFlatBifunctor.quasiIso_of_kFlat (curriedTensor A) L hL p hp)
  have hpQ : IsIso (DerivedCategory.Q.map p) :=
    (DerivedCategory.isIso_Q_map_iff_quasiIso (C := A) _).2 hp
  have hnat := derivedTensorIso_hom_natural_left A hres (p ≫ j) hP hK' hL
  refine ⟨(asIso (DerivedCategory.Q.map (p ▷ L))).symm ≪≫ (derivedTensorIso A hres hP hL).symm ≪≫
    whiskerRightIso (asIso (DerivedCategory.Q.map p)) _, ?_⟩
  simp only [Iso.trans_hom, Iso.symm_hom, asIso_inv, whiskerRightIso_hom, asIso_hom,
    Category.assoc, ← comp_whiskerRight, ← Functor.map_comp]
  rw [← Iso.eq_comp_inv] at hnat
  rw [hnat, MonoidalCategory.comp_whiskerRight, Functor.map_comp]
  simp

end CochainComplex.KFlatMonoidal

namespace Stacks.SheafOfModules.DerivedMonoidal

attribute [local instance] SheafOfModules.monoidalCategorySheafTensor
  SheafOfModules.symmetricCategorySheafTensor SheafOfModules.monoidalPreadditiveSheafTensor
  SheafOfModules.monoidalClosedSheafTensor
  SheafOfModules.preservesColimit_tensorRight_sheafTensor
  CochainComplex.symmetricCategory

variable {C : Type u} [SmallCategory.{u} C] {J : GrothendieckTopology C}
  (R : Sheaf J CommRingCat.{u})
  [HasSheafify J AddCommGrpCat.{u}] [J.WEqualsLocallyBijective AddCommGrpCat.{u}]
  [HasDerivedCategory.{w} (Mod R)]

/-- **A one-sided comparison for the derived tensor product on a ringed site.** For a morphism
`j : K ⟶ K'` of complexes of `O`-modules with `K'` and `L` K-flat, there is an isomorphism
`Q(K ⊗ L) ≅ Q(K) ⊗^L Q(L)` carrying `Q(j ▷ L)`, followed by the comparison of Stacks 0FPT at
`K'` and `L`, to `Q(j) ▷ Q(L)`. -/
theorem exists_iso_whiskerRight_comp {K K' L : Complexes R} (j : K ⟶ K') (hK' : KFlat R K')
    (hL : KFlat R L) :
    letI := derivedMonoidal R
    ∃ Θ : DerivedCategory.Q.obj (K ⊗ L) ≅ DerivedCategory.Q.obj K ⊗ DerivedCategory.Q.obj L,
      Θ.hom ≫ (DerivedCategory.Q.map j ▷ DerivedCategory.Q.obj L) =
        DerivedCategory.Q.map (j ▷ L) ≫ ((symmetricMonoidalDerived R).comparison K' L hK' hL).inv :=
  CochainComplex.KFlatMonoidal.exists_iso_whiskerRight_comp (Mod R) (exists_kFlat_resolution R) j
    hK' hL

end Stacks.SheafOfModules.DerivedMonoidal
