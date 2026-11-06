module

public import Mathlib.Algebra.Homology.ShortComplex.ModuleCat
public import Mathlib.Algebra.Homology.ShortComplex.PreservesHomology
public import StacksFrontier.CategoryTheory.Sites.Cohomology.Cech.ComplexOnTheSlice

/-!
# Changing the coefficient category of a Čech complex

An additive functor `Φ : A ⥤ A'` which preserves `w`-indexed products commutes with the Čech
complex: degreewise because each term is a product of values of the presheaf, and on
differentials because each differential is an alternating sum of structure maps. If `Φ` moreover
preserves homology, it commutes with Čech cohomology, so vanishing of Čech cohomology transports
along it. The main instance is `CategoryTheory.forget₂ (ModuleCat R) AddCommGrpCat`, which relates
the Amitsur complex of [Stacks, Tag 03FJ] and [Stacks, Tag 023M], a complex of `R`-modules, to
Čech cohomology with coefficients in abelian groups.

## Main definitions

* `Stacks.CechSite.sliceCechComplexCompCoefficientsIso` and
  `Stacks.CechSite.cechComplexCompCoefficientsIso`: `Φ` applied degreewise to the Čech complex
  of `G` is the Čech complex of `G ⋙ Φ`.
* `Stacks.CechSite.sliceCechCohomologyCompCoefficientsIso`: the same for Čech cohomology.

## Main results

* `Stacks.CechSite.isZero_sliceCechCohomology_comp_coefficients` and
  `Stacks.CechSite.isZero_cechCohomology_comp_coefficients`: vanishing of Čech cohomology
  transports along an additive, product- and homology-preserving functor.
* `Stacks.CechSite.isZero_sliceCechCohomology_forget₂_moduleCat`: the case
  `CategoryTheory.forget₂ (ModuleCat R) AddCommGrpCat`.
* `Stacks.CechSite.isZero_cechCohomology_of_isZero_sliceModule`: an abelian-group-valued
  presheaf on the ambient category whose restriction to the slice at the target underlies a
  presheaf of `R`-modules with vanishing Čech cohomology has vanishing Čech cohomology.
* `Stacks.CechSite.isZero_map_of_isZero`: an additive functor carries a zero object to a zero
  object.

## References

* [Stacks Project, Tag 03AM](https://stacks.math.columbia.edu/tag/03AM)
* [Stacks Project, Tag 023M](https://stacks.math.columbia.edu/tag/023M)
* [Stacks Project, Tag 03FJ](https://stacks.math.columbia.edu/tag/03FJ)
-/
@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits AlgebraicTopology Opposite

universe w v v' v'' u u' u''

namespace Stacks.CechSite

section Preadditive

variable {C : Type u} [Category.{v} C] {X : C} (E : PreZeroHypercover.{w} X)
  [∀ (n : ℕ) (i : Fin (n + 1) → E.I₀), HasProduct (fun a ↦ Over.mk (E.f (i a)))]
  {A : Type u'} [Category.{v'} A] [HasProducts.{w} A] [Preadditive A]
  {A' : Type u''} [Category.{v''} A'] [HasProducts.{w} A'] [Preadditive A']
  (Φ : A ⥤ A') [Φ.Additive] [∀ J : Type w, PreservesLimitsOfShape (Discrete J) Φ]

/-- An additive functor `Φ` preserving `w`-indexed products, applied degreewise to the Čech
complex of a presheaf `G` on the slice, gives the Čech complex of `G ⋙ Φ`. -/
public def sliceCechComplexCompCoefficientsIso (G : (Over X)ᵒᵖ ⥤ A) :
    (Φ.mapHomologicalComplex (ComplexShape.up ℕ)).obj (sliceCechComplex E G) ≅
      sliceCechComplex E (G ⋙ Φ) := by
  let T : CosimplicialObject A := (cechSimplicialObject E).rightOp ⋙
    (FormalCoproduct.evalOp.{w} (Over X) A).obj G
  let e₀ : (FormalCoproduct.evalOp.{w} (Over X) A).obj G ⋙ Φ ≅
      (FormalCoproduct.evalOp.{w} (Over X) A').obj (G ⋙ Φ) :=
    NatIso.ofComponents (fun Y ↦ PreservesProduct.iso Φ (fun i ↦ G.obj (op (Y.unop.obj i))))
      fun _ ↦ Pi.hom_ext _ _ fun _ ↦ by
        dsimp only [Functor.comp_map, Functor.comp_obj, FormalCoproduct.evalOp]
        simp only [PreservesProduct.iso_hom, Category.assoc, piComparison_comp_π,
          Pi.lift_comp_π, piComparison_comp_π_assoc, ← Φ.map_comp]
  let e : T ⋙ Φ ≅ (cechSimplicialObject E).rightOp ⋙
      (FormalCoproduct.evalOp.{w} (Over X) A').obj (G ⋙ Φ) :=
    Functor.isoWhiskerLeft (cechSimplicialObject E).rightOp e₀
  let e' : (Φ.mapHomologicalComplex (ComplexShape.up ℕ)).obj (sliceCechComplex E G) ≅
      (alternatingCofaceMapComplex A').obj (T ⋙ Φ) := by
    refine HomologicalComplex.Hom.isoOfComponents (fun n ↦ Iso.refl _) fun i j hij ↦ ?_
    obtain rfl : i + 1 = j := hij
    change 𝟙 _ ≫ (AlternatingCofaceMapComplex.obj (T ⋙ Φ)).d i (i + 1) =
      Φ.map ((AlternatingCofaceMapComplex.obj T).d i (i + 1)) ≫ 𝟙 _
    rw [Category.id_comp, Category.comp_id]
    simp only [AlternatingCofaceMapComplex.obj, CochainComplex.of_d,
      AlternatingCofaceMapComplex.objD, Functor.map_sum, Functor.map_zsmul]
    rfl
  exact e' ≪≫ (alternatingCofaceMapComplex A').mapIso e

/-- `Stacks.CechSite.sliceCechComplexCompCoefficientsIso` for a presheaf on the ambient
category. -/
public def cechComplexCompCoefficientsIso (I : Cᵒᵖ ⥤ A) :
    (Φ.mapHomologicalComplex (ComplexShape.up ℕ)).obj (cechComplex E I) ≅
      cechComplex E (I ⋙ Φ) :=
  sliceCechComplexCompCoefficientsIso E Φ ((Over.forget X).op ⋙ I)

end Preadditive

section Abelian

variable {C : Type u} [Category.{v} C] {X : C} (E : PreZeroHypercover.{w} X)
  [∀ (n : ℕ) (i : Fin (n + 1) → E.I₀), HasProduct (fun a ↦ Over.mk (E.f (i a)))]
  {A : Type u'} [Category.{v'} A] [HasProducts.{w} A] [Abelian A]
  {A' : Type u''} [Category.{v''} A'] [HasProducts.{w} A'] [Abelian A']
  (Φ : A ⥤ A') [Φ.Additive] [∀ J : Type w, PreservesLimitsOfShape (Discrete J) Φ]

omit [HasProducts.{w} A] [HasProducts.{w} A']
  [∀ J : Type w, PreservesLimitsOfShape (Discrete J) Φ] in
/-- An additive functor carries a zero object to a zero object. -/
public theorem isZero_map_of_isZero {Z : A} (h : IsZero Z) : IsZero (Φ.obj Z) :=
  (isZero_zero A').of_iso (Φ.mapIso h.isoZero ≪≫ Φ.mapZeroObject)

/-- An additive homology-preserving functor on coefficients commutes with Čech cohomology. -/
public def sliceCechCohomologyCompCoefficientsIso [Φ.PreservesHomology]
    (G : (Over X)ᵒᵖ ⥤ A) (p : ℕ) :
    sliceCechCohomology E (G ⋙ Φ) p ≅ Φ.obj (sliceCechCohomology E G p) :=
  (HomologicalComplex.homologyFunctor A' (ComplexShape.up ℕ) p).mapIso
      (sliceCechComplexCompCoefficientsIso E Φ G).symm ≪≫
    ShortComplex.mapHomologyIso ((sliceCechComplex E G).sc p) Φ

/-- If the Čech cohomology of `G` vanishes in degree `p`, so does that of `G ⋙ Φ`, for `Φ`
additive and preserving `w`-indexed products and homology. -/
public theorem isZero_sliceCechCohomology_comp_coefficients [Φ.PreservesHomology]
    (G : (Over X)ᵒᵖ ⥤ A) (p : ℕ) (h : IsZero (sliceCechCohomology E G p)) :
    IsZero (sliceCechCohomology E (G ⋙ Φ) p) :=
  (isZero_map_of_isZero Φ h).of_iso (sliceCechCohomologyCompCoefficientsIso E Φ G p)

/-- `Stacks.CechSite.isZero_sliceCechCohomology_comp_coefficients` for a presheaf on the
ambient category. -/
public theorem isZero_cechCohomology_comp_coefficients [Φ.PreservesHomology] (I : Cᵒᵖ ⥤ A)
    (p : ℕ) (h : IsZero (cechCohomology E I p)) :
    IsZero (cechCohomology E (I ⋙ Φ) p) :=
  isZero_sliceCechCohomology_comp_coefficients E Φ ((Over.forget X).op ⋙ I) p h

end Abelian

section ModuleCat

variable {C : Type u} [Category.{v} C] {X : C} (E : PreZeroHypercover.{w} X)
  [∀ (n : ℕ) (i : Fin (n + 1) → E.I₀), HasProduct (fun a ↦ Over.mk (E.f (i a)))]
  (R : Type u'') [Ring R]

/-- If the Čech cohomology of a presheaf of `R`-modules on the slice vanishes in degree `p`, so
does the Čech cohomology of the underlying presheaf of abelian groups. -/
public theorem isZero_sliceCechCohomology_forget₂_moduleCat
    (G : (Over X)ᵒᵖ ⥤ ModuleCat.{w} R) (p : ℕ)
    (h : IsZero (sliceCechCohomology E G p)) :
    IsZero (sliceCechCohomology E (G ⋙ forget₂ (ModuleCat.{w} R) AddCommGrpCat.{w}) p) :=
  isZero_sliceCechCohomology_comp_coefficients E
    (forget₂ (ModuleCat.{w} R) AddCommGrpCat.{w}) G p h

/-- An abelian-group-valued presheaf on the ambient category whose restriction to the slice at
the target is the underlying presheaf of a presheaf of `R`-modules with vanishing Čech
cohomology has vanishing Čech cohomology. -/
public theorem isZero_cechCohomology_of_isZero_sliceModule
    (F : Cᵒᵖ ⥤ AddCommGrpCat.{w}) (G : (Over X)ᵒᵖ ⥤ ModuleCat.{w} R)
    (e : (Over.forget X).op ⋙ F ≅ G ⋙ forget₂ (ModuleCat.{w} R) AddCommGrpCat.{w}) (p : ℕ)
    (h : IsZero (sliceCechCohomology E G p)) :
    IsZero (cechCohomology E F p) :=
  isZero_cechCohomology_of_isZero_slice E e p
    (isZero_sliceCechCohomology_forget₂_moduleCat E R G p h)

end ModuleCat

end Stacks.CechSite

end
