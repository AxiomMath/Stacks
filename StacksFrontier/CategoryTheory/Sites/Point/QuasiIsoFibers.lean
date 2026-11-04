module

public import Mathlib.CategoryTheory.Sites.Point.Conservative
public import Mathlib.CategoryTheory.Sites.Point.Skyscraper
public import Mathlib.Algebra.Homology.QuasiIso
public import Mathlib.Algebra.Category.ModuleCat.FilteredColimits
public import Mathlib.Algebra.Category.ModuleCat.Colimits

/-!
# Quasi-isomorphisms of complexes of sheaves are detected on fibers

Let `P` be a conservative family of points of a site and `R` a ring. A morphism of complexes
of sheaves of `R`-modules is a quasi-isomorphism as soon as its
fibers at all points of `P` are quasi-isomorphisms: the fiber functors are exact, so they commute
with homology, and they jointly reflect isomorphisms.

## Main results

* `CategoryTheory.ObjectProperty.IsConservativeFamilyOfPoints.quasiIso_of_sheafFiber`
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits

universe w v v' u u'

namespace CategoryTheory.ObjectProperty.IsConservativeFamilyOfPoints

variable {C : Type u} [Category.{v} C] {J : GrothendieckTopology C} {R : Type u'} [Ring R]
  {P : ObjectProperty (GrothendieckTopology.Point.{max u' w} J)}
  (hP : P.IsConservativeFamilyOfPoints)
  [LocallySmall.{max u' w} C]
  [J.HasSheafCompose (forget (ModuleCat.{max u' w} R))] [HasSheafify J (ModuleCat.{max u' w} R)]

omit [HasSheafify J (ModuleCat.{max u' w} R)] in
include hP in
/-- **A morphism of complexes of sheaves whose fibers at a conservative family of points are
quasi-isomorphisms is a quasi-isomorphism.** -/
theorem quasiIso_of_sheafFiber {ι : Type*} {c : ComplexShape ι}
    {K L : HomologicalComplex (Sheaf J (ModuleCat.{max u' w} R)) c} (φ : K ⟶ L)
    [CategoryWithHomology (Sheaf J (ModuleCat.{max u' w} R))]
    [CategoryWithHomology (ModuleCat.{max u' w} R)]
    [∀ Φ : P.FullSubcategory,
      (Φ.obj.sheafFiber (A := ModuleCat.{max u' w} R)).PreservesZeroMorphisms]
    [∀ Φ : P.FullSubcategory, (Φ.obj.sheafFiber (A := ModuleCat.{max u' w} R)).PreservesHomology]
    (h : ∀ Φ : P.FullSubcategory,
      QuasiIso (((Φ.obj.sheafFiber (A := ModuleCat.{max u' w} R)).mapHomologicalComplex c).map φ)) :
    QuasiIso φ := by
  rw [quasiIso_iff]
  intro i
  rw [quasiIsoAt_iff, ShortComplex.quasiIso_iff]
  have : PreservesFilteredColimitsOfSize.{max u' w, max u' w}
      (forget (ModuleCat.{max u' w} R)) := by
    show PreservesFilteredColimitsOfSize.{max u' w, max u' w}
      (forget₂ (ModuleCat.{max u' w} R) AddCommGrpCat.{max u' w} ⋙ forget AddCommGrpCat.{max u' w})
    infer_instance
  refine ((hP.jointlyReflectIsomorphisms (ModuleCat.{max u' w} R)).isIso_iff _).2 fun Φ => ?_
  have hΦ := h Φ
  rw [quasiIso_iff] at hΦ
  have hi := hΦ i
  rw [quasiIsoAt_iff, ShortComplex.quasiIso_iff] at hi
  let F := Φ.obj.sheafFiber (A := ModuleCat.{max u' w} R)
  let f := (HomologicalComplex.shortComplexFunctor (Sheaf J (ModuleCat.{max u' w} R)) c i).map φ
  have e := ShortComplex.mapHomologyIso_hom_naturality f F
  have hi' : IsIso (ShortComplex.homologyMap (F.mapShortComplex.map f)) := hi
  have : F.map (ShortComplex.homologyMap f) =
      (((HomologicalComplex.shortComplexFunctor (Sheaf J (ModuleCat.{max u' w} R)) c i).obj
        K).mapHomologyIso F).inv ≫
      ShortComplex.homologyMap (F.mapShortComplex.map f) ≫
      (((HomologicalComplex.shortComplexFunctor (Sheaf J (ModuleCat.{max u' w} R)) c i).obj
        L).mapHomologyIso F).hom := by
    rw [e, Iso.inv_hom_id_assoc]
  show IsIso (F.map (ShortComplex.homologyMap f))
  rw [this]
  infer_instance

end CategoryTheory.ObjectProperty.IsConservativeFamilyOfPoints

end
