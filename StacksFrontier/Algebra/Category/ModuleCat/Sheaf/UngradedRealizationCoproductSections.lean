module

public import StacksFrontier.Algebra.Category.ModuleCat.Sheaf.SheafificationTensor
public import StacksFrontier.Algebra.Category.ModuleCat.Sheaf.UngradedRealizationModuleDirectSum

/-!
# The coproduct comparison of a graded module, on the coproduct injections

`SheafOfModules.GradedModule.coprodIsoUngradedSheaf` identifies the coproduct `∐ₙ Mₙ` of the
homogeneous pieces of a graded module concentrated in nonnegative degrees with the module
underlying the total module `SheafOfModules.GradedModule.ungradedSheaf`. This file computes
that comparison on the coproduct injections: it sends the `n`-th injection of a local section to
the homogeneous local section it names, `SheafOfModules.GradedModule.ungradedIncl`.

## Main results

* `Stacks.sheafification_map_inclHom_comp_sheafifyDirectSumIso_hom`: the sheafified direct sum
  comparison `Stacks.sheafifyDirectSumIso` carries the sheafification of the `i`-th inclusion of
  the objectwise direct sum to the `i`-th coproduct injection, up to the sheafification counit
  of the `i`-th summand.
* `Stacks.sheafifyHomOfPresheafHom_unit_apply`: the morphism out of a sheafification determined
  by a morphism into a sheaf agrees with it on the unit image of a local section.
* `SheafOfModules.GradedModule.counit_comp_sigma_ι_comp_coprodIsoUngradedSheaf_hom`: the
  morphism-level form of the main computation.
* `SheafOfModules.GradedModule.coprodIsoUngradedSheaf_hom_sigma_ι`: the comparison sends the
  `n`-th coproduct injection of a local section to `ungradedIncl n` of it.
* `SheafOfModules.GradedModule.ungradedIncl_smul_ungradedIncl`: the action of the ungraded
  realization on the total module, on homogeneous local sections.
* `SheafOfModules.GradedModule.coprodIsoUngradedSheaf_hom_sigma_ι_smul`: multiplication by a
  homogeneous section of the algebra is degreewise under the comparison: it carries the
  degree-`n` injection to the degree-`m` injection of the degreewise action, for `n + k = m`.

## References

* [Stacks Project, Section 17.21](https://stacks.math.columbia.edu/tag/01CF)
* [Stacks Project, Tag 0897](https://stacks.math.columbia.edu/tag/0897)
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits Opposite

universe v u w

namespace Stacks

/-! ### The sheafified direct sum comparison on the inclusions -/

section DirectSumIota

variable {C : Type u} [Category.{v} C] {J : GrothendieckTopology C} {R : Sheaf J RingCat.{w}}
  [HasWeakSheafify J AddCommGrpCat.{w}] [J.WEqualsLocallyBijective AddCommGrpCat.{w}]
  {ι : Type} [DecidableEq ι] (N : ι → SheafOfModules.{w} R) [HasCoproduct N]

/-- The sheafification of the `i`-th inclusion of the objectwise direct sum, followed by
`Stacks.sheafifyDirectSumIso`, is the `i`-th coproduct injection precomposed with the
sheafification counit of the `i`-th summand. -/
theorem sheafification_map_inclHom_comp_sheafifyDirectSumIso_hom (i : ι) :
    (PresheafOfModules.sheafification (𝟙 R.obj)).map (inclHom (fun j => (N j).val) i) ≫
        (sheafifyDirectSumIso N).hom =
      (PresheafOfModules.sheafificationAdjunction (𝟙 R.obj)).counit.app (N i) ≫ Sigma.ι N i :=
  IsColimit.comp_coconePointUniqueUpToIso_hom
    (isColimitOfPreserves (PresheafOfModules.sheafification (𝟙 R.obj))
      (directSumIsColimit fun j => (N j).val))
    ((IsColimit.precomposeHomEquiv (sheafificationDirectSumComponentIso N) _).symm
      (colimit.isColimit (Discrete.functor N))) (Discrete.mk i)

/-- The sheafification counit of the `i`-th summand, followed by the `i`-th coproduct
injection and the inverse of `Stacks.sheafifyDirectSumIso`, is the sheafification of the `i`-th
inclusion of the objectwise direct sum. -/
@[reassoc]
theorem counit_comp_sigma_ι_comp_sheafifyDirectSumIso_inv (i : ι) :
    (PresheafOfModules.sheafificationAdjunction (𝟙 R.obj)).counit.app (N i) ≫
        Sigma.ι N i ≫ (sheafifyDirectSumIso N).inv =
      (PresheafOfModules.sheafification (𝟙 R.obj)).map (inclHom (fun j => (N j).val) i) := by
  rw [← Category.assoc]
  exact (Iso.comp_inv_eq _).2 (sheafification_map_inclHom_comp_sheafifyDirectSumIso_hom N i).symm

end DirectSumIota

/-! ### The transpose of a morphism into a sheaf, on unit images -/

section Sheafify

variable {C : Type u} [Category.{v} C] {J : GrothendieckTopology C} {R : Sheaf J RingCat.{w}}
  [HasWeakSheafify J AddCommGrpCat.{w}] [J.WEqualsLocallyBijective AddCommGrpCat.{w}]
  {M₀ : PresheafOfModules.{w} R.obj} {M : SheafOfModules.{w} R}

/-- The defining property of `Stacks.sheafifyHomOfPresheafHom`: restricted along the
sheafification unit it is the morphism it was built from. -/
theorem sheafifyUnit_comp_sheafifyHomOfPresheafHom (c : M₀ ⟶ M.val) :
    (PresheafOfModules.sheafificationAdjunction (𝟙 R.obj)).unit.app M₀ ≫
        (SheafOfModules.forget R ⋙ PresheafOfModules.restrictScalars (𝟙 R.obj)).map
          (sheafifyHomOfPresheafHom c) = c :=
  (PresheafOfModules.sheafificationAdjunction_homEquiv_apply (𝟙 R.obj)
      (sheafifyHomOfPresheafHom c)).trans
    ((PresheafOfModules.sheafificationHomEquiv (𝟙 R.obj) (P := M₀) (F := M)).apply_symm_apply c)

/-- `Stacks.sheafifyHomOfPresheafHom` agrees with the morphism it was built from on the unit
image of a local section. -/
theorem sheafifyHomOfPresheafHom_unit_apply (c : M₀ ⟶ M.val) (X : Cᵒᵖ) (z : M₀.obj X) :
    PresheafOfModules.Hom.app (sheafifyHomOfPresheafHom c).val X
        (PresheafOfModules.Hom.app
          ((PresheafOfModules.sheafificationAdjunction (𝟙 R.obj)).unit.app M₀) X z) =
      PresheafOfModules.Hom.app c X z :=
  PresheafOfModules.hom_congr_apply' (sheafifyUnit_comp_sheafifyHomOfPresheafHom c) X z

end Sheafify

end Stacks

namespace SheafOfModules

open Stacks

namespace GradedModule

section Ungraded

variable {C : Type u} [Category.{v} C] {J : GrothendieckTopology C} {R : Sheaf J RingCat.{w}}
  [HasSheafify J RingCat.{w}] [J.WEqualsLocallyBijective RingCat.{w}]
  [HasWeakSheafify J AddCommGrpCat.{w}] [J.WEqualsLocallyBijective AddCommGrpCat.{w}]
  {A : GradedAlgebra.{w, w} R} [A.IsCommutative] (M : GradedModule.{w, w, w} A)

/-- Coproducts indexed by `ℕ` of sheaves of modules, supplied directly: instance search for them
times out. -/
local instance hasColimitsOfShapeDiscreteNat :
    HasColimitsOfShape (Discrete ℕ) (SheafOfModules.{w} R) :=
  haveI := PresheafOfModules.hasColimitsOfShape.{w} R.obj (Discrete ℕ)
  SheafOfModules.instHasColimitsOfShapeOfPresheafOfModulesObjFunctorOppositeRingCatIsSheaf R _

/-- The comparison morphism from the direct sum over the nonnegative degrees, evaluated on a
homogeneous local section: it is the homogeneous section, read in the total module. -/
theorem coprodDirectSumHom_of (U : Cᵒᵖ) (n : ℕ) (x : (M.piece (n : ℤ)).val.obj U) :
    PresheafOfModules.Hom.app M.coprodDirectSumHom U
        (DirectSum.of (fun i : ℕ => ((M.piece (i : ℤ)).val.obj U : Type w)) n x) =
      M.ungradedIncl (n : ℤ) x := by
  rw [show PresheafOfModules.Hom.app M.coprodDirectSumHom U
        (DirectSum.of (fun i : ℕ => ((M.piece (i : ℤ)).val.obj U : Type w)) n x) =
      PresheafOfModules.Hom.app
        (M.toPresheafGradedModule.directSumHom A.ungradedStructureMap
          (A.toPresheafGradedAlgebra.toTotalSheaf J) M.ungradedSheaf M.toUngradedSheaf
          (GradedModule.structureHom_comp_toTotalSheaf (A := A) (J := J))) U
        (Stacks.directSumNatToIntApp (fun m : ℤ => (M.piece m).val) U
          (DirectSum.of _ n x)) from rfl,
    Stacks.directSumNatToIntApp_of]
  rfl

/-- The coproduct comparison of a graded module on the coproduct injections, at the level of
morphisms: the sheafification counit of the `n`-th piece, followed by the `n`-th coproduct
injection and the comparison, is the sheafification of the `n`-th inclusion of the objectwise
direct sum followed by `Stacks.sheafifyHomOfPresheafHom` of the direct sum comparison. -/
theorem counit_comp_sigma_ι_comp_coprodIsoUngradedSheaf_hom
    (hzero : ∀ n : ℤ, n < 0 → Limits.IsZero (M.piece n)) (n : ℕ) :
    (PresheafOfModules.sheafificationAdjunction (𝟙 R.obj)).counit.app (M.piece (n : ℤ)) ≫
        Sigma.ι (fun i : ℕ => M.piece (i : ℤ)) n ≫ (M.coprodIsoUngradedSheaf hzero).hom =
      (PresheafOfModules.sheafification (𝟙 R.obj)).map
          (Stacks.inclHom (fun i : ℕ => (M.piece (i : ℤ)).val) n) ≫
        Stacks.sheafifyHomOfPresheafHom M.coprodDirectSumHom :=
  Stacks.counit_comp_sigma_ι_comp_sheafifyDirectSumIso_inv_assoc
    (fun i : ℕ => M.piece (i : ℤ)) n
    (Stacks.sheafifyHomOfPresheafHom M.coprodDirectSumHom)

/-- The coproduct comparison of a graded module sends the `n`-th coproduct injection of a local
section to the homogeneous local section it names. -/
theorem coprodIsoUngradedSheaf_hom_sigma_ι
    (hzero : ∀ n : ℤ, n < 0 → Limits.IsZero (M.piece n)) (U : Cᵒᵖ) (n : ℕ)
    (x : (M.piece (n : ℤ)).val.obj U) :
    (M.coprodIsoUngradedSheaf hzero).hom.val.app U
        (PresheafOfModules.Hom.app
          (Sigma.ι (fun i : ℕ => M.piece (i : ℤ)) n).val U x) =
      M.ungradedIncl (n : ℤ) x := by
  have hx : PresheafOfModules.Hom.app
      ((SheafOfModules.forget R ⋙ PresheafOfModules.restrictScalars (𝟙 R.obj)).map
        ((PresheafOfModules.sheafificationAdjunction (𝟙 R.obj)).counit.app
          (M.piece (n : ℤ)))) U
      (PresheafOfModules.Hom.app
        ((PresheafOfModules.sheafificationAdjunction (𝟙 R.obj)).unit.app
          ((M.piece (n : ℤ)).val)) U x) = x :=
    PresheafOfModules.hom_congr_apply'
      ((PresheafOfModules.sheafificationAdjunction (𝟙 R.obj)).right_triangle_components
        (M.piece (n : ℤ))) U x
  refine Eq.trans (congrArg (fun y => (M.coprodIsoUngradedSheaf hzero).hom.val.app U
    (PresheafOfModules.Hom.app (Sigma.ι (fun i : ℕ => M.piece (i : ℤ)) n).val U y)) hx.symm) ?_
  refine Eq.trans (congrArg
    (fun f => f.val.app U
      (PresheafOfModules.Hom.app
        ((PresheafOfModules.sheafificationAdjunction (𝟙 R.obj)).unit.app
          ((M.piece (n : ℤ)).val)) U x))
    (M.counit_comp_sigma_ι_comp_coprodIsoUngradedSheaf_hom hzero n)) ?_
  refine Eq.trans (congrArg
    (fun y => PresheafOfModules.Hom.app
      (Stacks.sheafifyHomOfPresheafHom M.coprodDirectSumHom).val U y)
    (PresheafOfModules.unit_naturality_apply (α := 𝟙 R.obj)
      (Stacks.inclHom (fun i : ℕ => (M.piece (i : ℤ)).val) n) U x)) ?_
  exact (Stacks.sheafifyHomOfPresheafHom_unit_apply M.coprodDirectSumHom U
    (DirectSum.of (fun i : ℕ => ((M.piece (i : ℤ)).val.obj U : Type w)) n x)).trans
    (M.coprodDirectSumHom_of U n x)

/-! ### Multiplication by a homogeneous section of the algebra -/

/-- The action of the ungraded realization on the total module, on homogeneous local sections:
a homogeneous section `y` of degree `i` of the algebra carries the degree-`n` section `x` to the
degree-`n + i` section `M.smul n i U x y`. -/
theorem ungradedIncl_smul_ungradedIncl (U : Cᵒᵖ) (i n : ℤ) (y : (A.piece i).val.obj U)
    (x : (M.piece n).val.obj U) :
    A.ungradedIncl i y • M.ungradedIncl n x = M.ungradedIncl (n + i) (M.smul n i U x y) :=
  ((M.toUngradedSheaf.app U).hom.map_smul (A.toPresheafGradedAlgebra.incl i y)
      (M.toPresheafGradedModule.incl n x)).symm.trans
    (congrArg (fun z => M.toUngradedSheaf.app U z)
      (M.toPresheafGradedModule.incl_smul_incl i n y x))

/-- Transporting a homogeneous local section along an equality of degrees does not change the
section it names in the total module. -/
theorem ungradedIncl_eqToHom (U : Cᵒᵖ) {d d' : ℤ} (e : d = d') (z : (M.piece d).val.obj U) :
    M.ungradedIncl d' ((eqToHom (congrArg M.piece e)).val.app U z) = M.ungradedIncl d z := by
  subst e; rfl

/-- Multiplication by a homogeneous section of the algebra, read through the coproduct
comparison: multiplying the degree-`n` section `x` by the degree-`k` section `y` gives the
comparison image of the `m`-th coproduct injection of the degreewise action `M.smul n k U x y`,
transported along `n + k = m`. -/
theorem coprodIsoUngradedSheaf_hom_sigma_ι_smul
    (hzero : ∀ n : ℤ, n < 0 → Limits.IsZero (M.piece n)) (U : Cᵒᵖ) (k n m : ℕ)
    (hm : (n : ℤ) + (k : ℤ) = (m : ℤ)) (y : (A.piece (k : ℤ)).val.obj U)
    (x : (M.piece (n : ℤ)).val.obj U) :
    A.ungradedIncl (k : ℤ) y • M.ungradedIncl (n : ℤ) x =
      (M.coprodIsoUngradedSheaf hzero).hom.val.app U
        (PresheafOfModules.Hom.app (Sigma.ι (fun i : ℕ => M.piece (i : ℤ)) m).val U
          ((eqToHom (congrArg M.piece hm)).val.app U (M.smul (n : ℤ) (k : ℤ) U x y))) := by
  rw [M.coprodIsoUngradedSheaf_hom_sigma_ι hzero U m
      ((eqToHom (congrArg M.piece hm)).val.app U (M.smul (n : ℤ) (k : ℤ) U x y)),
    M.ungradedIncl_eqToHom U hm (M.smul (n : ℤ) (k : ℤ) U x y),
    M.ungradedIncl_smul_ungradedIncl U (k : ℤ) (n : ℤ) y x]

end Ungraded

end GradedModule

end SheafOfModules

end
