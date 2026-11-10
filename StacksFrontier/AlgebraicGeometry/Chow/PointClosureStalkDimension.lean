module

public import StacksFrontier.Topology.Dimension.DimensionFunctionIsCatenary
public import Mathlib.AlgebraicGeometry.IdealSheaf.Functorial
public import Mathlib.FieldTheory.FinTrdeg
public import StacksFrontier.AlgebraicGeometry.Chow.RelativeDimension
public import StacksFrontier.AlgebraicGeometry.Chow.GysinConstruction.IntegralComponent
public import StacksFrontier.AlgebraicGeometry.Chow.Vocabulary
public import StacksFrontier.AlgebraicGeometry.CoherentPushforwardCriteria.ClosureSubscheme
public import StacksFrontier.AlgebraicGeometry.Morphisms.FiniteType.DimensionFormula
public import StacksFrontier.AlgebraicGeometry.Variety.Defs.Dimension.NoetherianFibre
public import StacksFrontier.RingTheory.DimensionFormula
public import StacksFrontier.RingTheory.Nagata.Japanese
public import StacksFrontier.Topology.Dimension.CatenaryOfDimensionFunction
import StacksCore.Tactic.EgaSgaAttribute

/-!
# The delta-dimension drop along a specialization equals a stalk dimension

Let `S` be a locally Noetherian universally catenary scheme carrying a dimension function `δ`,
let `f : X ⟶ S` be locally of finite type, and let `x ⤳ y` be a specialization in `X`. Then the
drop `relativeDimension δ f x - relativeDimension δ f y` is a natural number `n`, and `n` is the
Krull dimension of the local ring at `y` of the integral closed subscheme `closure {x}` of `X`.

## Main results

* `Stacks.Chow.ringKrullDim_stalk_eq_dimensionFunction_sub_genericPoint`: on an integral scheme
  with a dimension function `d`, the Krull dimension of the local ring at `y` is the drop of `d`
  from the generic point to `y`.
* `Stacks.Chow.genericPoint_subscheme_vanishingIdeal_closure_singleton`: `x` is the generic
  point of the reduced closed subscheme supported on `closure {x}`.
* `Stacks.Chow.relativeDimension_sub_eq_of_ringKrullDim_pointClosureStalk_eq`: if the stalk at
  `y` of the reduced closed subscheme supported on `closure {x}` has Krull dimension `n`, then
  `relativeDimension δ f` drops by `n` along `x ⤳ y`.
* `Stacks.Chow.relativeDimension_sub_eq_one_of_isImmediateSpecialization`,
  `Stacks.Chow.relativeDimension_sub_eq_two_of_isImmediateSpecialization`: the drop along one,
  and along two successive, immediate specializations.

## References

* [Stacks Project, Tag 02JU](https://stacks.math.columbia.edu/tag/02JU)
* [Stacks Project, Tag 02JW](https://stacks.math.columbia.edu/tag/02JW)
-/

@[expose] public noncomputable section

open CategoryTheory AlgebraicGeometry TopologicalSpace

universe u

open TopologicalSpace.IrreducibleCloseds (closureSingleton coe_closureSingleton)

namespace Stacks.Chow

/-! ### Transporting a dimension function along a closed embedding -/

/-- The dimension function pulled back along a closed embedding `e` takes the value of `d` at
`e y`. -/
@[simp] lemma pullbackDimensionFunctionOfClosedEmbedding_apply {X Y : Type*}
    [TopologicalSpace X] [TopologicalSpace Y] {e : Y → X} (he : Topology.IsClosedEmbedding e)
    (d : DimensionFunction X) (y : Y) :
    pullbackDimensionFunctionClosed he d y = d (e y) := rfl

/-- On an integral scheme with a dimension function `d`, the Krull dimension of the local ring at
`y` is the drop of `d` from the generic point to `y`. -/
lemma ringKrullDim_stalk_eq_dimensionFunction_sub_genericPoint
    {T : Scheme.{u}} [IsIntegral T] (d : DimensionFunction T) (y : T) :
    ringKrullDim (T.presheaf.stalk y) =
      ↑(((d (genericPoint T) - d y).toNat : ℕ∞)) := by
  classical
  let _ : PartialOrder T := specializationOrder T
  set η := genericPoint T
  have hη : closure ({η} : Set T) = Set.univ := (genericPoint_spec T).def
  have hmax (z : IrreducibleCloseds T) : z ≤ closureSingleton η := by
    change (z : Set T) ⊆ closure ({η} : Set T)
    rw [hη]
    exact Set.subset_univ _
  have hcod := codim_closure_singleton_eq_delta_diff
    (scheme_stacksSober T) d (TopologicalSpace.DimensionFunction.isDimensionFunctionForCatenary d)
    η y (genericPoint_specializes y)
  have hcod' : IrreducibleClosedsCodim.topCodim
      (closureSingleton y) (closureSingleton η) = Order.coheight y := by
    rw [topCodim_eq_coheight_of_isMax _ _ hmax,
      coheight_closureSingleton_eq_coheight_point]
  rw [ringKrullDim_stalk_eq_coheight, ← hcod', hcod]

/-- The ideal sheaf of the closure of a point pushes forward to the ideal sheaf of the closure of
its image. -/
lemma map_vanishingIdeal_closure_singleton {X Y : Scheme.{u}} (f : X ⟶ Y) (x : X) :
    (Scheme.IdealSheafData.vanishingIdeal (Closeds.closure ({x} : Set X))).map f =
      Scheme.IdealSheafData.vanishingIdeal (Closeds.closure ({f x} : Set Y)) := by
  rw [Scheme.IdealSheafData.map_vanishingIdeal]
  congr 1
  apply Closeds.ext
  change closure (f '' closure ({x} : Set X)) = closure ({f x} : Set Y)
  rw [closure_image_closure f.continuous, Set.image_singleton]

/-- The point `x` is the generic point of the reduced closed subscheme supported on
`closure {x}`, as a point of that subscheme. -/
lemma genericPoint_subscheme_vanishingIdeal_closure_singleton {X : Scheme.{u}} (x : X) :
    letI : IsIntegral (Scheme.IdealSheafData.vanishingIdeal
        (Closeds.closure ({x} : Set X))).subscheme :=
      Scheme.IdealSheafData.isIntegral_subscheme_vanishingIdeal_closure x
    genericPoint
        (Scheme.IdealSheafData.vanishingIdeal (Closeds.closure ({x} : Set X))).subscheme =
      ⟨x, subset_closure (Set.mem_singleton x)⟩ := by
  classical
  set I := Scheme.IdealSheafData.vanishingIdeal (Closeds.closure ({x} : Set X)) with hI
  let : IsIntegral I.subscheme :=
    Scheme.IdealSheafData.isIntegral_subscheme_vanishingIdeal_closure x
  set i : I.subscheme ⟶ X := I.subschemeι with hi
  set tx : I.subscheme := ⟨x, subset_closure (Set.mem_singleton x)⟩ with htx
  have htxgen : IsGenericPoint tx (Set.univ : Set I.subscheme) := by
    refine isGenericPoint_iff_specializes.mpr fun z => ?_
    have hzsupport : z.1 ∈ (I.support : Set X) := z.property
    have hzmem : z.1 ∈ Closeds.closure ({x} : Set X) := by
      simpa [hI, Scheme.IdealSheafData.coe_support_vanishingIdeal] using hzsupport
    exact iff_of_true ((subtype_specializes_iff _ _).mpr (specializes_iff_mem_closure.mpr hzmem))
      (Set.mem_univ z)
  exact (htxgen.eq (genericPoint_spec I.subscheme)).symm

/-- The local ring at `y` of the reduced closed subscheme supported on `closure {x}` has Krull
dimension one when `x` specializes immediately to `y`. -/
@[sga "2 VIII 2.5" "Direction"]
lemma ringKrullDim_pointClosureStalk_eq_one_of_isImmediateSpecialization {X : Scheme.{u}}
    {x y : X} (hxy : x ⤳ y) (himm : IsImmediateSpecialization x y) :
    ringKrullDim ((Scheme.IdealSheafData.vanishingIdeal
      (Closeds.closure ({x} : Set X))).subscheme.presheaf.stalk
      ⟨y, specializes_iff_mem_closure.mp hxy⟩) = 1 := by
  set I := Scheme.IdealSheafData.vanishingIdeal (Closeds.closure ({x} : Set X)) with hI
  let : IsIntegral I.subscheme :=
    Scheme.IdealSheafData.isIntegral_subscheme_vanishingIdeal_closure x
  set i : I.subscheme ⟶ X := I.subschemeι with hi
  set tx : I.subscheme := ⟨x, subset_closure (Set.mem_singleton x)⟩ with htx
  set ty : I.subscheme := ⟨y, specializes_iff_mem_closure.mp hxy⟩ with hty
  have hix : i tx = x := by simpa [hi, htx] using I.subschemeι_apply tx
  have hiy : i ty = y := by simpa [hi, hty] using I.subschemeι_apply ty
  have hIgen : genericPoint I.subscheme = tx := by
    simpa [hI, htx] using genericPoint_subscheme_vanishingIdeal_closure_singleton x
  have hηy : genericPoint I.subscheme ⤳ ty := by
    rw [hIgen]
    exact (subtype_specializes_iff _ _).mpr hxy
  apply ringKrullDim_eq_one_of_immediate_generic hηy
  rw [hIgen]
  apply immediate_pullback_closedEmbedding i.isClosedEmbedding
  simpa [hix, hiy] using himm

/-! ### The drop along a specialization -/

/-- If the local ring at `y` of the reduced closed subscheme supported on `closure {x}` has Krull
dimension `n`, then the relative dimension drops by `n` along `x ⤳ y`. -/
theorem relativeDimension_sub_eq_of_ringKrullDim_pointClosureStalk_eq
    {X S : Scheme.{u}} [IsLocallyNoetherian S]
    (hS : Scheme.IsUniversallyCatenary S) (δ : DimensionFunction S)
    (f : X ⟶ S) [LocallyOfFiniteType f] {x y : X} (hxy : x ⤳ y) {n : ℕ}
    (hn : ringKrullDim ((Scheme.IdealSheafData.vanishingIdeal
      (Closeds.closure ({x} : Set X))).subscheme.presheaf.stalk
      ⟨y, specializes_iff_mem_closure.mp hxy⟩) = (n : ℕ∞)) :
    relativeDimension δ f x - relativeDimension δ f y = n := by
  obtain ⟨m, hdrop, hlocal⟩ := relativeDimension_drop_of_specialization hS δ f hxy
  rw [hn] at hlocal
  rw [hdrop, show m = n by exact_mod_cast hlocal.symm]

/-- Along an immediate specialization `x ⤳ y` the relative dimension drops by exactly one. -/
theorem relativeDimension_sub_eq_one_of_isImmediateSpecialization
    {X S : Scheme.{u}} [IsLocallyNoetherian S]
    (hS : Scheme.IsUniversallyCatenary S) (δ : DimensionFunction S)
    (f : X ⟶ S) [LocallyOfFiniteType f] {x y : X} (hxy : IsImmediateSpecialization x y) :
    relativeDimension δ f x - relativeDimension δ f y = 1 :=
  relativeDimension_sub_eq_of_ringKrullDim_pointClosureStalk_eq hS δ f hxy.1 (n := 1) <| by
    simpa using ringKrullDim_pointClosureStalk_eq_one_of_isImmediateSpecialization hxy.1 hxy

/-- Along two successive immediate specializations `x ⤳ z ⤳ y` the relative dimension drops by
exactly two. -/
theorem relativeDimension_sub_eq_two_of_isImmediateSpecialization
    {X S : Scheme.{u}} [IsLocallyNoetherian S]
    (hS : Scheme.IsUniversallyCatenary S) (δ : DimensionFunction S)
    (f : X ⟶ S) [LocallyOfFiniteType f] {x z y : X}
    (hxz : IsImmediateSpecialization x z) (hzy : IsImmediateSpecialization z y) :
    relativeDimension δ f x - relativeDimension δ f y = 2 := by
  have h₁ := relativeDimension_sub_eq_one_of_isImmediateSpecialization hS δ f hxz
  have h₂ := relativeDimension_sub_eq_one_of_isImmediateSpecialization hS δ f hzy
  omega

end Stacks.Chow
