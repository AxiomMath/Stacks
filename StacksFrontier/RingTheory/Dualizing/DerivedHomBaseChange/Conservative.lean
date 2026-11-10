module

public import Mathlib.Algebra.Homology.DerivedCategory.ExactFunctor
public import Mathlib.Algebra.Homology.DerivedCategory.HomologySequence

/-!
# Exact functors on derived categories reflect isomorphisms

Let `F : C₁ ⥤ C₂` be an exact additive functor between abelian categories. Cohomology commutes
with `F` on cochain complexes, and on derived categories there is a natural isomorphism
`F.mapDerivedCategory ⋙ Hⁿ ≅ Hⁿ ⋙ F`. Consequently `F.mapDerivedCategory` reflects isomorphisms
as soon as `F` does.

## Main results

* `CategoryTheory.Functor.mapHomologicalComplexCompHomologyFunctorIso` — cohomology commutes
  with an exact functor on cochain complexes.
* `CategoryTheory.Functor.mapDerivedCategoryCompHomologyFunctorIso` — the same on the derived
  category.
* `CategoryTheory.Functor.reflectsIsomorphisms_mapDerivedCategory` — an exact functor which
  reflects isomorphisms induces a conservative functor on derived categories.
* `CategoryTheory.Functor.isIso_app_iff_forall_isIso_app_homology` — a natural transformation of
  the derived functors of two exact functors, induced by a natural transformation of the functors
  themselves, is invertible at an object exactly when the latter is invertible at all of its
  cohomology objects.

## References

* [Stacks Project, Tag 0E2A](https://stacks.math.columbia.edu/tag/0E2A)
-/

@[expose] public section

open CategoryTheory Limits

universe w₁ w₂ v₁ v₂ u₁ u₂

namespace CategoryTheory.Functor

variable {C₁ : Type u₁} [Category.{v₁} C₁] [Abelian C₁] [HasDerivedCategory.{w₁} C₁]
  {C₂ : Type u₂} [Category.{v₂} C₂] [Abelian C₂] [HasDerivedCategory.{w₂} C₂]
  (F : C₁ ⥤ C₂) [F.Additive] [PreservesFiniteLimits F] [PreservesFiniteColimits F]

/-- Degree-`n` cohomology of cochain complexes commutes with an exact functor. -/
noncomputable def mapHomologicalComplexCompHomologyFunctorIso (n : ℤ) :
    F.mapHomologicalComplex (ComplexShape.up ℤ) ⋙
        HomologicalComplex.homologyFunctor C₂ (ComplexShape.up ℤ) n ≅
      HomologicalComplex.homologyFunctor C₁ (ComplexShape.up ℤ) n ⋙ F :=
  NatIso.ofComponents (fun K ↦ (K.sc n).mapHomologyIso F) (fun {_ _} f ↦
    ShortComplex.mapHomologyIso_hom_naturality
      ((HomologicalComplex.shortComplexFunctor C₁ (ComplexShape.up ℤ) n).map f) F)

/-- Degree-`n` cohomology on the derived category commutes with the functor induced by an exact
functor: the isomorphism induced by `mapHomologicalComplexCompHomologyFunctorIso` along the
localisation `DerivedCategory.Q`. -/
noncomputable def mapDerivedCategoryCompHomologyFunctorIso (n : ℤ) :
    F.mapDerivedCategory ⋙ DerivedCategory.homologyFunctor C₂ n ≅
      DerivedCategory.homologyFunctor C₁ n ⋙ F := by
  letI : Localization.Lifting (DerivedCategory.Q (C := C₁))
      (HomologicalComplex.quasiIso C₁ (ComplexShape.up ℤ))
      (F.mapHomologicalComplex (ComplexShape.up ℤ) ⋙
        HomologicalComplex.homologyFunctor C₂ (ComplexShape.up ℤ) n)
      (F.mapDerivedCategory ⋙ DerivedCategory.homologyFunctor C₂ n) :=
    ⟨associator _ _ _ ≪≫ isoWhiskerRight F.mapDerivedCategoryFactors _ ≪≫
      associator _ _ _ ≪≫ isoWhiskerLeft _ (DerivedCategory.homologyFunctorFactors C₂ n)⟩
  letI : Localization.Lifting (DerivedCategory.Q (C := C₁))
      (HomologicalComplex.quasiIso C₁ (ComplexShape.up ℤ))
      (HomologicalComplex.homologyFunctor C₁ (ComplexShape.up ℤ) n ⋙ F)
      (DerivedCategory.homologyFunctor C₁ n ⋙ F) :=
    ⟨associator _ _ _ ≪≫ isoWhiskerRight (DerivedCategory.homologyFunctorFactors C₁ n) _⟩
  exact Localization.liftNatIso DerivedCategory.Q
    (HomologicalComplex.quasiIso C₁ (ComplexShape.up ℤ)) _ _ _ _
    (F.mapHomologicalComplexCompHomologyFunctorIso n)

/-- An exact functor which reflects isomorphisms induces a conservative functor on derived
categories: a morphism of `DerivedCategory C₁` is invertible as soon as its image is. -/
instance reflectsIsomorphisms_mapDerivedCategory [F.ReflectsIsomorphisms] :
    F.mapDerivedCategory.ReflectsIsomorphisms where
  reflects {X Y} φ h := by
    rw [DerivedCategory.isIso_iff]
    intro n
    have h₂ : IsIso ((F.mapDerivedCategory ⋙ DerivedCategory.homologyFunctor C₂ n).map φ) :=
      have := h
      inferInstanceAs
        (IsIso ((DerivedCategory.homologyFunctor C₂ n).map (F.mapDerivedCategory.map φ)))
    have h₃ : IsIso (F.map ((DerivedCategory.homologyFunctor C₁ n).map φ)) := by
      rw [show F.map ((DerivedCategory.homologyFunctor C₁ n).map φ) =
          (DerivedCategory.homologyFunctor C₁ n ⋙ F).map φ from rfl,
        ← NatIso.naturality_1 (F.mapDerivedCategoryCompHomologyFunctorIso n) φ]
      infer_instance
    exact isIso_of_reflects_iso ((DerivedCategory.homologyFunctor C₁ n).map φ) F

/-- The comparison of cohomology with an exact functor, evaluated at the image of a cochain
complex: it is the comparison on complexes, conjugated by the two identifications of the
cohomology of a localized complex with the cohomology of the complex. -/
theorem mapDerivedCategoryCompHomologyFunctorIso_hom_app_Q (n : ℤ) (X : CochainComplex C₁ ℤ) :
    (F.mapDerivedCategoryCompHomologyFunctorIso n).hom.app (DerivedCategory.Q.obj X) =
      (DerivedCategory.homologyFunctor C₂ n).map (F.mapDerivedCategoryFactors.hom.app X) ≫
        (DerivedCategory.homologyFunctorFactors C₂ n).hom.app
          ((F.mapHomologicalComplex (ComplexShape.up ℤ)).obj X) ≫
        (F.mapHomologicalComplexCompHomologyFunctorIso n).hom.app X ≫
        F.map ((DerivedCategory.homologyFunctorFactors C₁ n).inv.app X) := by
  simp [mapDerivedCategoryCompHomologyFunctorIso, Localization.liftNatTrans_app,
    Localization.Lifting.iso]

section Naturality

variable {F}
variable {G : C₁ ⥤ C₂} [G.Additive] [PreservesFiniteLimits G] [PreservesFiniteColimits G]
  (α : F ⟶ G)

omit [HasDerivedCategory C₁] [HasDerivedCategory C₂] in
/-- Cohomology of a complex is natural in the exact functor: the comparisons of
`mapHomologicalComplexCompHomologyFunctorIso` for two exact functors are exchanged by a natural
transformation between them. -/
theorem mapHomologicalComplexCompHomologyFunctorIso_hom_naturality
    (n : ℤ) (X : CochainComplex C₁ ℤ) :
    (HomologicalComplex.homologyFunctor C₂ (ComplexShape.up ℤ) n).map
          ((NatTrans.mapHomologicalComplex α (ComplexShape.up ℤ)).app X) ≫
        (G.mapHomologicalComplexCompHomologyFunctorIso n).hom.app X =
      (F.mapHomologicalComplexCompHomologyFunctorIso n).hom.app X ≫
        α.app ((HomologicalComplex.homologyFunctor C₁ (ComplexShape.up ℤ) n).obj X) := by
  change ShortComplex.homologyMap ((X.sc n).mapNatTrans α) ≫
      ((X.sc n).mapHomologyIso G).hom =
    ((X.sc n).mapHomologyIso F).hom ≫ α.app (X.sc n).homology
  rw [ShortComplex.homologyMap_mapNatTrans]
  simp

omit [HasDerivedCategory C₂] in
/-- The naturality of `mapHomologicalComplexCompHomologyFunctorIso` in the exact functor,
followed by the image of the inverse of `DerivedCategory.homologyFunctorFactors`. -/
theorem mapHomologicalComplexCompHomologyFunctorIso_hom_comp_map_homologyFunctorFactors_inv
    (n : ℤ) (X : CochainComplex C₁ ℤ) :
    (HomologicalComplex.homologyFunctor C₂ (ComplexShape.up ℤ) n).map
          ((NatTrans.mapHomologicalComplex α (ComplexShape.up ℤ)).app X) ≫
        (G.mapHomologicalComplexCompHomologyFunctorIso n).hom.app X ≫
        G.map ((DerivedCategory.homologyFunctorFactors C₁ n).inv.app X) =
      (F.mapHomologicalComplexCompHomologyFunctorIso n).hom.app X ≫
        F.map ((DerivedCategory.homologyFunctorFactors C₁ n).inv.app X) ≫
        α.app ((DerivedCategory.homologyFunctor C₁ n).obj (DerivedCategory.Q.obj X)) := by
  rw [← Category.assoc, mapHomologicalComplexCompHomologyFunctorIso_hom_naturality,
    Category.assoc]
  exact _ ≫= (α.naturality ((DerivedCategory.homologyFunctorFactors C₁ n).inv.app X)).symm

/-- The naturality of the comparison of cohomology with an exact functor in that functor, at the
image of a cochain complex in the derived category, written through
`DerivedCategory.homologyFunctorFactors`. -/
theorem homologyFunctor_map_Q_map_mapHomologicalComplex_comp (n : ℤ) (X : CochainComplex C₁ ℤ) :
    (DerivedCategory.homologyFunctor C₂ n).map (DerivedCategory.Q.map
          ((NatTrans.mapHomologicalComplex α (ComplexShape.up ℤ)).app X)) ≫
        (DerivedCategory.homologyFunctorFactors C₂ n).hom.app
          ((G.mapHomologicalComplex (ComplexShape.up ℤ)).obj X) ≫
        (G.mapHomologicalComplexCompHomologyFunctorIso n).hom.app X ≫
        G.map ((DerivedCategory.homologyFunctorFactors C₁ n).inv.app X) =
      (DerivedCategory.homologyFunctorFactors C₂ n).hom.app
          ((F.mapHomologicalComplex (ComplexShape.up ℤ)).obj X) ≫
        (F.mapHomologicalComplexCompHomologyFunctorIso n).hom.app X ≫
        F.map ((DerivedCategory.homologyFunctorFactors C₁ n).inv.app X) ≫
        α.app ((DerivedCategory.homologyFunctor C₁ n).obj (DerivedCategory.Q.obj X)) := by
  rw [DerivedCategory.homologyFunctorFactors_hom_naturality_assoc]
  exact _ ≫=
    mapHomologicalComplexCompHomologyFunctorIso_hom_comp_map_homologyFunctorFactors_inv α n X

variable (δ : F.mapDerivedCategory ⟶ G.mapDerivedCategory)
  (hδ : ∀ X : CochainComplex C₁ ℤ,
    δ.app (DerivedCategory.Q.obj X) ≫ G.mapDerivedCategoryFactors.hom.app X =
      F.mapDerivedCategoryFactors.hom.app X ≫
        DerivedCategory.Q.map ((NatTrans.mapHomologicalComplex α (ComplexShape.up ℤ)).app X))

include hδ

/-- A natural transformation of the derived functors of two exact functors which is induced by a
natural transformation `α` of the functors themselves, in the sense that the two agree at the
image of every cochain complex, is exchanged with `α` by the comparisons of cohomology with an
exact functor. -/
theorem whiskerRight_comp_mapDerivedCategoryCompHomologyFunctorIso_hom (n : ℤ) :
    Functor.whiskerRight δ (DerivedCategory.homologyFunctor C₂ n) ≫
        (G.mapDerivedCategoryCompHomologyFunctorIso n).hom =
      (F.mapDerivedCategoryCompHomologyFunctorIso n).hom ≫
        Functor.whiskerLeft (DerivedCategory.homologyFunctor C₁ n) α := by
  refine Localization.natTrans_ext DerivedCategory.Q
    (HomologicalComplex.quasiIso C₁ (ComplexShape.up ℤ)) fun X ↦ ?_
  dsimp only [NatTrans.comp_app, Functor.whiskerRight_app, Functor.whiskerLeft_app]
  rw [mapDerivedCategoryCompHomologyFunctorIso_hom_app_Q,
    mapDerivedCategoryCompHomologyFunctorIso_hom_app_Q, ← Functor.map_comp_assoc, hδ X,
    Functor.map_comp_assoc]
  simp only [Category.assoc]
  exact _ ≫= homologyFunctor_map_Q_map_mapHomologicalComplex_comp α n X

/-- **Invertibility of a derived transition is detected on cohomology.** With `δ` induced by `α`
as above, `δ` is invertible at an object of `D(C₁)` exactly when `α` is invertible at all of its
cohomology objects. -/
theorem isIso_app_iff_forall_isIso_app_homology (K : DerivedCategory C₁) :
    IsIso (δ.app K) ↔
      ∀ n : ℤ, IsIso (α.app ((DerivedCategory.homologyFunctor C₁ n).obj K)) := by
  rw [DerivedCategory.isIso_iff]
  refine forall_congr' fun n ↦ ?_
  have h := congr_app (whiskerRight_comp_mapDerivedCategoryCompHomologyFunctorIso_hom α δ hδ n) K
  dsimp only [NatTrans.comp_app, Functor.whiskerRight_app, Functor.whiskerLeft_app] at h
  rw [← isIso_comp_right_iff _ ((G.mapDerivedCategoryCompHomologyFunctorIso n).hom.app K), h,
    isIso_comp_left_iff]

end Naturality

end CategoryTheory.Functor

end
