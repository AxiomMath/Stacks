module

public import Mathlib.Algebra.Homology.ShortComplex.FunctorEquivalence
public import StacksFrontier.Algebra.Category.ModuleCat.Sheaf.ToposPushforwardModules.HasSheafComposeForget
public import StacksFrontier.CategoryTheory.Sites.Modules.RingedSite
public import StacksFrontier.Homology.KFlat.Flat
public import Mathlib.CategoryTheory.Abelian.GrothendieckAxioms.Colim
public import Mathlib.CategoryTheory.Functor.ReflectsIso.Exact
public import Mathlib.CategoryTheory.Functor.ReflectsIso.Jointly
public import StacksFrontier.Algebra.Category.ModuleCat.Sheaf.TensorPreservesColimits
public import StacksFrontier.Topology.Sheaves.Cohomology.KFlat.Defs
public import StacksFrontier.CategoryTheory.Sites.Modules.Colimits
import StacksFrontier.CategoryTheory.Limits.FunctorCategory.ShortExactColimit
import StacksCore.Tactic.StacksAttribute
public import StacksFrontier.Algebra.Category.ModuleCat.Sheaf.ToposPushforwardModules.HasSheafComposeForget

/-!
# A sequential colimit of K-flat complexes is K-flat

Let `R` be a sheaf of commutative rings on a site. A cochain complex of `R`-modules is K-flat when
tensoring it with any acyclic complex gives an acyclic complex. A sequential colimit of K-flat
complexes is again K-flat.

## Main results

* `Stacks.SheafOfModules.kFlat_colimit`: a sequential colimit of K-flat complexes of sheaves of
  modules is K-flat.

## References

* [Stacks Project, Tag 06YE](https://stacks.math.columbia.edu/tag/06YE)
-/

@[expose] public section

attribute [local implicit_reducible] CategoryTheory.sheafCompose

open CategoryTheory CategoryTheory.Limits

universe v u w

namespace Stacks.SheafOfModules


variable {C : Type u} [Category.{v} C] {J : GrothendieckTopology C}
  (R : Sheaf J CommRingCat.{w})
  [HasWeakSheafify J AddCommGrpCat.{w}]
  [J.WEqualsLocallyBijective AddCommGrpCat.{w}]
  [(Stacks.SheafOfModules.Tensor.sheafTensor.{u, v, w, w, w} R).Additive]
  [∀ M, ((Stacks.SheafOfModules.Tensor.sheafTensor.{u, v, w, w, w} R).obj M).Additive]
  [∀ (K₁ K₂ : CochainComplex (SheafOfModules (Stacks.SheafOfModules.Tensor.ringSheaf R)) ℤ),
    HomologicalComplex.HasMapBifunctor K₁ K₂
      (Stacks.SheafOfModules.Tensor.sheafTensor.{u, v, w, w, w} R) (ComplexShape.up ℤ)]

/-- The sections of `Stacks.SheafOfModules.Tensor.ringSheaf R` over `X` form a commutative ring. -/
noncomputable local instance (X : Cᵒᵖ) :
    CommRing ((Stacks.SheafOfModules.Tensor.ringSheaf R).obj.obj X) :=
  inferInstanceAs (CommRing (R.obj.obj X))

set_option backward.isDefEq.respectTransparency false in
/-- Presheaves of modules over `Stacks.SheafOfModules.Tensor.ringSheaf R` have `w`-small
colimits. -/
noncomputable local instance :
    HasColimitsOfSize.{w, w}
      (PresheafOfModules.{w} (Stacks.SheafOfModules.Tensor.ringSheaf R).obj) :=
  ⟨fun K _ => PresheafOfModules.hasColimitsOfShape _ K⟩

set_option backward.isDefEq.respectTransparency false in
/-- Coproducts of presheaves of modules over `Stacks.SheafOfModules.Tensor.ringSheaf R`. -/
noncomputable local instance (K : Type w) :
    HasColimitsOfShape (Discrete K)
      (PresheafOfModules.{w} (Stacks.SheafOfModules.Tensor.ringSheaf R).obj) :=
  PresheafOfModules.hasColimitsOfShape _ _

set_option backward.isDefEq.respectTransparency false in
/-- Coproducts of sheaves of modules over `Stacks.SheafOfModules.Tensor.ringSheaf R`. -/
noncomputable local instance (K : Type w) :
    HasColimitsOfShape (Discrete K)
      (SheafOfModules.{w} (Stacks.SheafOfModules.Tensor.ringSheaf R)) :=
  SheafOfModules.instHasColimitsOfShapeOfPresheafOfModulesObjFunctorOppositeRingCatIsSheaf _ _


/-- A sequential colimit of K-flat complexes of sheaves of modules is K-flat. -/
@[stacks 06YE]
theorem kFlat_colimit
    (K : ℕ ⥤ CochainComplex (SheafOfModules (Stacks.SheafOfModules.Tensor.ringSheaf R)) ℤ)
    (hK : ∀ n : ℕ, IsKFlat R (K.obj n)) :
    IsKFlat R (colimit K) := by
  intro F hF
  let A := SheafOfModules.{w} (Stacks.SheafOfModules.Tensor.ringSheaf R)
  let := Stacks.hasSheafCompose_forget₂_commRingCat.{w, v, u} J
  let B :=
    (Stacks.SheafOfModules.Tensor.sheafTensor.{u, v, w, w, w} R).mapBifunctorHomologicalComplex
      (ComplexShape.up ℤ) (ComplexShape.up ℤ)
  let T := B.obj F ⋙ HomologicalComplex₂.totalFunctor A
    (ComplexShape.up ℤ) (ComplexShape.up ℤ) (ComplexShape.up ℤ)
  have hX : ∀ M : A, PreservesColimitsOfShape ℕ
      ((Stacks.SheafOfModules.Tensor.sheafTensor.{u, v, w, w, w} R).obj M) := by
    intro M
    let : PreservesColimitsOfSize.{w, w}
        ((Stacks.SheafOfModules.Tensor.sheafTensor.{u, v, w, w, w} R).obj M) :=
      TensorColimits.tensorLeft_preservesColimits J R M
    let : PreservesColimitsOfSize.{0, 0}
        ((Stacks.SheafOfModules.Tensor.sheafTensor.{u, v, w, w, w} R).obj M) :=
      preservesSmallestColimits_of_preservesColimits _
    infer_instance
  let : ∀ M : A, PreservesColimitsOfShape ℕ
      ((Stacks.SheafOfModules.Tensor.sheafTensor.{u, v, w, w, w} R).obj M) :=
    hX
  let : PreservesColimit K (B.obj F) :=
    CochainComplex.KFlat.preservesColimit_mapBifunctorObj K F
      (Stacks.SheafOfModules.Tensor.sheafTensor.{u, v, w, w, w} R)
  let : PreservesColimit (K ⋙ B.obj F)
      (HomologicalComplex₂.totalFunctor A (ComplexShape.up ℤ) (ComplexShape.up ℤ)
        (ComplexShape.up ℤ)) :=
    CochainComplex.KFlat.preservesColimit_totalFunctor (ComplexShape.up ℤ) (K ⋙ B.obj F)
  let : PreservesColimit K T := comp_preservesColimit _ _
  let : Abelian A :=
    AlgebraicGeometry.SheafOfModules.instAbelianSheafOfModules
      (Stacks.SheafOfModules.Tensor.ringSheaf R)
  let : AB5OfSize.{w, w} A :=
    AlgebraicGeometry.SheafOfModules.instAB5SheafOfModules (Stacks.SheafOfModules.Tensor.ringSheaf
      R)
  let : AB5OfSize.{0, 0} A := AB5OfSize_shrink A
  let : HasExactColimitsOfShape ℕ A := inferInstance
  have hE : (colimit (K ⋙ T)).Acyclic :=
    CochainComplex.KFlat.acyclic_colimit (K ⋙ T) (fun n ↦ by
      simpa [T, B, Stacks.SheafOfModules.Tensor.tensorComplex] using hK n F hF)
  let e : T.obj (colimit K) ≅ colimit (K ⋙ T) :=
    (preservesColimitIso T K).trans (HasColimit.isoOfNatIso (Iso.refl _))
  show (T.obj (colimit K)).Acyclic
  intro i
  exact ShortComplex.exact_of_iso
    (((HomologicalComplex.shortComplexFunctor A (ComplexShape.up ℤ) i).mapIso e).symm)
    (hE i)

end Stacks.SheafOfModules
