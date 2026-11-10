module

public import StacksFrontier.Algebra.Homology.DerivedCategory.AcyclicResolutionIso

/-!
# Naturality of `RG(A[0]) ≅ G(R)` for acyclic resolutions

For a morphism `a : A ⟶ A'` and a morphism `g : R ⟶ R'` of `G`-acyclic resolutions
`q : A[0] ⟶ R`, `q' : A'[0] ⟶ R'` with `q ≫ g = a[0] ≫ q'`, the isomorphisms
`Q(G(R)) ≅ ι(RG(A[0]))` of `CategoryTheory.Functor.rightDerivedFunctorPlusSingleIsoOfAcyclic` form
a commutative square with `Q(G(g))` and `ι(RG(a[0]))`.

## Main results

* `CategoryTheory.Functor.rightDerivedFunctorPlusSingleIsoOfAcyclic_hom_naturality`.
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits

namespace CategoryTheory.Functor

attribute [local instance 2000] HomotopyCategory.Plus.instHasPointwiseRightDerivedFunctorQuasiIso

variable {C D : Type*} [Category* C] [Category* D] [Abelian C] [Abelian D]
  [HasDerivedCategory C] [HasDerivedCategory D] [EnoughInjectives C] (G : C ⥤ D) [G.Additive]

/-- The morphism of `HomotopyCategory.Plus C` induced by a morphism of bounded below complexes. -/
abbrev plusQuotientMap {R R' : CochainComplex C ℤ} (n₀ : ℤ) [R.IsStrictlyGE n₀] [R'.IsStrictlyGE n₀]
    (g : R ⟶ R') :
    (⟨(HomotopyCategory.quotient C _).obj R,
        (HomotopyCategory.plus_quotient_obj_iff R).2 ⟨n₀, inferInstance⟩⟩ :
        HomotopyCategory.Plus C) ⟶
      ⟨(HomotopyCategory.quotient C _).obj R',
        (HomotopyCategory.plus_quotient_obj_iff R').2 ⟨n₀, inferInstance⟩⟩ :=
  ObjectProperty.homMk ((HomotopyCategory.quotient C _).map g)

omit [EnoughInjectives C] in
/-- Naturality of `plusQhObjIsoSingleOfQuasiIso`. -/
theorem plusQhObjIsoSingleOfQuasiIso_hom_naturality {A A' : C} (a : A ⟶ A')
    (R R' : CochainComplex C ℤ) (n₀ : ℤ) [R.IsStrictlyGE n₀] [R'.IsStrictlyGE n₀]
    (q : (HomologicalComplex.single C (ComplexShape.up ℤ) 0).obj A ⟶ R) [QuasiIso q]
    (q' : (HomologicalComplex.single C (ComplexShape.up ℤ) 0).obj A' ⟶ R') [QuasiIso q']
    (g : R ⟶ R') (hg : q ≫ g = (HomologicalComplex.single C (ComplexShape.up ℤ) 0).map a ≫ q') :
    DerivedCategory.Plus.Qh.map (plusQuotientMap n₀ g) ≫
        (plusQhObjIsoSingleOfQuasiIso A' R' n₀ q').hom =
      (plusQhObjIsoSingleOfQuasiIso A R n₀ q).hom ≫
        (DerivedCategory.Plus.singleFunctor C 0).map a := by
  apply (ObjectProperty.fullyFaithfulι _).map_injective
  have hq : DerivedCategory.Q.map q ≫ DerivedCategory.Q.map g =
      DerivedCategory.Q.map ((HomologicalComplex.single C (ComplexShape.up ℤ) 0).map a) ≫
        DerivedCategory.Q.map q' := by
    rw [← Functor.map_comp, hg, Functor.map_comp]
  have h₁ := (DerivedCategory.quotientCompQhIso C).hom.naturality g
  simp only [Functor.comp_map] at h₁
  change DerivedCategory.Qh.map ((HomotopyCategory.quotient C _).map g) ≫
      ((DerivedCategory.quotientCompQhIso C).hom.app R' ≫
        CategoryTheory.inv (DerivedCategory.Q.map q')) =
    ((DerivedCategory.quotientCompQhIso C).hom.app R ≫
        CategoryTheory.inv (DerivedCategory.Q.map q)) ≫
      DerivedCategory.Q.map ((HomologicalComplex.single C (ComplexShape.up ℤ) 0).map a)
  rw [← Category.assoc, h₁, Category.assoc, Category.assoc]
  congr 1
  rw [IsIso.eq_inv_comp, ← Category.assoc, hq, Category.assoc, IsIso.hom_inv_id, Category.comp_id]

/-- **Naturality of `RG(A[0]) ≅ G(R)`**: for `a : A ⟶ A'` and a morphism `g : R ⟶ R'` of
`G`-acyclic resolutions with `q ≫ g = a[0] ≫ q'`, the isomorphisms
`CategoryTheory.Functor.rightDerivedFunctorPlusSingleIsoOfAcyclic` commute with `Q(G(g))` and
`ι(RG(a[0]))`. -/
theorem rightDerivedFunctorPlusSingleIsoOfAcyclic_hom_naturality {A A' : C} (a : A ⟶ A')
    (R R' : CochainComplex C ℤ) (n₀ : ℤ) [R.IsStrictlyGE n₀] [R'.IsStrictlyGE n₀]
    (q : (HomologicalComplex.single C (ComplexShape.up ℤ) 0).obj A ⟶ R) [hq : QuasiIso q]
    (q' : (HomologicalComplex.single C (ComplexShape.up ℤ) 0).obj A' ⟶ R') [hq' : QuasiIso q']
    (hR : ∀ n, G.rightAcyclic (R.X n)) (hR' : ∀ n, G.rightAcyclic (R'.X n)) (g : R ⟶ R')
    (hg : q ≫ g = (HomologicalComplex.single C (ComplexShape.up ℤ) 0).map a ≫ q') :
    DerivedCategory.Q.map ((G.mapHomologicalComplex _).map g) ≫
        (G.rightDerivedFunctorPlusSingleIsoOfAcyclic A' R' n₀ q' hR').hom =
      (G.rightDerivedFunctorPlusSingleIsoOfAcyclic A R n₀ q hR).hom ≫
        DerivedCategory.Plus.ι.map
          (G.rightDerivedFunctorPlus.map ((DerivedCategory.Plus.singleFunctor C 0).map a)) := by
  have h₁ := (DerivedCategory.quotientCompQhIso D).inv.naturality
    ((G.mapHomologicalComplex (ComplexShape.up ℤ)).map g)
  have h₂ := (G.mapHomotopyCategoryFactors (ComplexShape.up ℤ)).inv.naturality g
  have h₃ := G.rightDerivedFunctorPlusUnith.naturality (plusQuotientMap n₀ g)
  have h₄ := plusQhObjIsoSingleOfQuasiIso_hom_naturality a R R' n₀ q q' g hg
  simp only [Functor.comp_map] at h₁ h₂ h₃
  simp only [rightDerivedFunctorPlusSingleIsoOfAcyclic, Iso.trans_hom, Iso.app_hom, Iso.symm_hom,
    Functor.mapIso_hom, asIso_hom, Category.assoc]
  rw [reassoc_of% h₁]
  congr 1
  rw [← Functor.map_comp_assoc, h₂, Functor.map_comp_assoc]
  congr 1
  have h₀ : DerivedCategory.Qh.map ((G.mapHomotopyCategory (ComplexShape.up ℤ)).map
      ((HomotopyCategory.quotient C (ComplexShape.up ℤ)).map g)) =
      DerivedCategory.Plus.ι.map (DerivedCategory.Plus.Qh.map
        (G.mapHomotopyCategoryPlus.map (plusQuotientMap n₀ g))) := rfl
  rw [h₀, ← Functor.map_comp_assoc, h₃, Functor.map_comp_assoc,
    ← Functor.map_comp DerivedCategory.Plus.ι (G.rightDerivedFunctorPlus.map _),
    ← Functor.map_comp G.rightDerivedFunctorPlus, h₄, Functor.map_comp G.rightDerivedFunctorPlus,
    Functor.map_comp DerivedCategory.Plus.ι]

end CategoryTheory.Functor

end
