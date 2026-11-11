module

public import StacksCore.Tactic.StacksAttribute
public import StacksFrontier.AlgebraicGeometry.Spaces.LiftDifferenceDescent
public import StacksFrontier.AlgebraicGeometry.Spaces.Points
public import StacksFrontier.AlgebraicGeometry.Spaces.Thickenings
public import StacksFrontier.AlgebraicGeometry.Spaces.UniversalFirstOrderThickening
public import StacksFrontier.AlgebraicGeometry.Spaces.Thickenings.LiftDifferenceBaseAgreement
public import StacksFrontier.AlgebraicGeometry.Spaces.Thickenings.LiftDifferenceRingSurjectivity
public import StacksFrontier.AlgebraicGeometry.Spaces.Thickenings.LiftDifferenceTargetValues

/-!
# The difference of two lifts into an undeformed target

Let `Z ⊂ X` be a first order thickening of algebraic spaces over a scheme `S`, let `b : W ⟶ V`
be a morphism of algebraic spaces and let `a : Z ⟶ W` be a morphism.  Two *lifts of `a` over
`V`* are two morphisms `c, c' : X ⟶ W` with

* `i ≫ c = a = i ≫ c'`, their common restriction to the thickening, and
* `c ≫ b = c' ≫ b`, both being morphisms over `V`.

This file attaches to such a pair the `𝒪_Z`-linear map

`θ : a^*Ω_{W/V} ⟶ 𝒞_{Z/X}`

by which the two differ, and proves that a lift does not differ from itself and that the
differences along a chain of three lifts add up.

## Main definitions

* `AlgebraicGeometry.Space.undeformedLiftDifferenceData`: the two comorphisms of the two lifts,
  read in the single sheaf of rings `a_*(i^{-1}𝒪_X)` on the small étale site of `W`, as a
  `Stacks.Sites.LiftDifferenceData` for the identity of `𝒪_W`.
* `AlgebraicGeometry.Space.undeformedLiftDiff`: the `𝒪_Z`-linear map `a^*Ω_{W/V} ⟶ 𝒞_{Z/X}` by
  which the two lifts differ.

## Main results

* `AlgebraicGeometry.Space.undeformedLiftDifferenceData_descend_eq_zero`: the descended
  difference kills every regular function read from the base `V`.
* `AlgebraicGeometry.Space.undeformedLiftDiff_self`: a lift does not differ from itself.
* `AlgebraicGeometry.Space.undeformedLiftDiff_add_undeformedLiftDiff`: the differences along a
  chain of three lifts add up.
* `AlgebraicGeometry.Space.isThickening_top`: an algebraic space is a thickening of itself.

## References

* [Stacks Project, Tag 0618](https://stacks.math.columbia.edu/tag/0618)
* [Stacks Project, Tag 0619](https://stacks.math.columbia.edu/tag/0619)
* [Stacks Project, Tag 061A](https://stacks.math.columbia.edu/tag/061A)
* [Stacks Project, Tag 061D](https://stacks.math.columbia.edu/tag/061D)
* [Stacks Project, Tag 04CT](https://stacks.math.columbia.edu/tag/04CT)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits Opposite
open Stacks.Sheaves.ToposPullback Stacks.Sheaves.ToposPushforward

universe u

namespace AlgebraicGeometry.Space

variable (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)
  {X W V : AlgebraicSpaces B S hS} (Z : ClosedSubspaces B S hS X.1)
  (hZ : IsFirstOrderThickening B S hS X Z.1)
  (a : (⟨Z.1.toFunctor, Z.2.1⟩ : AlgebraicSpaces B S hS) ⟶ W)

/-- An algebraic space is a thickening of itself: its top closed subspace. -/
@[stacks 05ZK "part (1): an algebraic space is a thickening of itself"]
theorem isThickening_top (Y : AlgebraicSpaces B S hS) : IsThickening B S hS Y ⊤ := by
  refine ⟨isClosedSubspace_top B S hS Y, fun y ↦
    ⟨pointsMap B S hS Y.1 (inv (⊤ : Subfunctor Y.1).ι) y, ?_⟩⟩
  have hid : pointsMap B S hS Y.1
      (inv (⊤ : Subfunctor Y.1).ι ≫ (⊤ : Subfunctor Y.1).ι) = id := by
    rw [IsIso.inv_hom_id, pointsMap_id]
  exact congrArg (fun f ↦ f y)
    ((pointsMap_comp B S hS Y.1 (inv (⊤ : Subfunctor Y.1).ι) (⊤ : Subfunctor Y.1).ι).symm.trans hid)

/-- For two morphisms `c, c' : X ⟶ W` whose restrictions to the first order thickening
`Z ⊂ X` are both `a`, their comorphisms read in `a_*(i^{-1}𝒪_X)` are a pair of lifts into the
square-zero ideal `a_*𝒞_{Z/X}` of `AlgebraicGeometry.Space.squareZeroValuesAt`, for the identity
of `𝒪_W` as quotient map. -/
def undeformedLiftDifferenceData (c c' : X ⟶ W)
    (h : subspaceInclusion B S hS X Z ≫ c = a)
    (h' : subspaceInclusion B S hS X Z ≫ c' = a) :
    Stacks.Sites.LiftDifferenceData
      (𝟙 (structureRingSheaf B S hS W)) (squareZeroValuesAt B S hS Z W a hZ) where
  f := structureSharpThroughThickeningAt B S hS Z c a h
  g := structureSharpThroughThickeningAt B S hS Z c' a h'
  ι_smul {_} x m := squareZeroValuesAt_ι_smul B S hS Z W a hZ (𝟙 _)
    (structureSharpThroughThickeningAt B S hS Z c a h)
    ((structureSharpThroughThickeningAt_comp_reduction B S hS Z c a h).trans
      (Category.id_comp _).symm) x m
  diff {_} x := sharpDiffAt B S hS Z W a hZ
    (structureSharpThroughThickeningAt B S hS Z c a h)
    (structureSharpThroughThickeningAt B S hS Z c' a h')
    (structureSharpThroughThickeningAt_comp_reduction_eq B S hS Z c c' a h h') x
  ι_diff {_} x := squareZeroValuesAt_ι_sharpDiffAt B S hS Z W a hZ _ _ _ x
  app_eq_of_app_eq_zero {_} x hx := by
    have hx0 : x = 0 := hx
    rw [hx0, map_zero, map_zero]

/-- The first comorphism of `undeformedLiftDifferenceData` is that of `c`. -/
theorem undeformedLiftDifferenceData_f (c c' : X ⟶ W)
    (h : subspaceInclusion B S hS X Z ≫ c = a)
    (h' : subspaceInclusion B S hS X Z ≫ c' = a) :
    (undeformedLiftDifferenceData B S hS Z hZ a c c' h h').f =
      structureSharpThroughThickeningAt B S hS Z c a h := rfl

/-- The second comorphism of `undeformedLiftDifferenceData` is that of `c'`. -/
theorem undeformedLiftDifferenceData_g (c c' : X ⟶ W)
    (h : subspaceInclusion B S hS X Z ≫ c = a)
    (h' : subspaceInclusion B S hS X Z ≫ c' = a) :
    (undeformedLiftDifferenceData B S hS Z hZ a c c' h h').g =
      structureSharpThroughThickeningAt B S hS Z c' a h' := rfl

/-- The identity of the structure sheaf of rings is locally surjective as a morphism of
sheaves. -/
theorem isLocallySurjective_sheafHom_id_structureRingSheaf :
    Sheaf.IsLocallySurjective (𝟙 (structureRingSheaf B S hS W)) where
  imageSieve_mem {Vv} y := by
    refine (SmallEtale.topology B S hS W.1).superset_covering (fun {Q} g _ ↦ ?_)
      (GrothendieckTopology.top_mem _ _)
    exact ⟨(structureRingSheaf B S hS W).obj.map g.op y, rfl⟩

variable (b : W ⟶ V)

/-- For two lifts over `V`, the descended difference of their comorphisms kills every section
coming from `b^{-1}𝒪_V` through `b^♯ : b^{-1}𝒪_V ⟶ 𝒪_W`. -/
theorem undeformedLiftDifferenceData_descend_eq_zero (c c' : X ⟶ W)
    (h : subspaceInclusion B S hS X Z ≫ c = a)
    (h' : subspaceInclusion B S hS X Z ≫ c' = a) (hb : c ≫ b = c' ≫ b)
    (Vv : (SmallEtale B S hS W.1)ᵒᵖ)
    (s : (inverseImageStructureSheaf B S hS b).obj.obj Vv) :
    letI := isLocallySurjective_sheafHom_id_structureRingSheaf B S hS (W := W)
    (undeformedLiftDifferenceData B S hS Z hZ a c c' h h').toQuotientDerivation.descend
      ((structureSharpInverseImage B S hS b).hom.app Vv s) = 0 := by
  let := isLocallySurjective_sheafHom_id_structureRingSheaf B S hS (W := W)
  have hbridge : (structureSharpInverseImage B S hS b).hom.app Vv s =
      (structureSharpRingInverseImage B S hS b).hom.app Vv s := by
    rw [structureSharpRingInverseImage_eq_forget₂]
    rfl
  rw [hbridge]
  exact Stacks.Sites.LiftDifferenceData.descend_eq_zero_of_comp_eq
    (undeformedLiftDifferenceData B S hS Z hZ a c c' h h')
    (structureSharpRingInverseImage B S hS b) (structureSharpRingInverseImage B S hS b)
    (Category.comp_id _)
    (structureSharpRingInverseImage_comp_structureSharpThroughThickeningAt_eq'
      B S hS Z c c' b a h h' hb) s

/-- **The `𝒪_Z`-linear map `a^*Ω_{W/V} ⟶ 𝒞_{Z/X}` by which two lifts into an undeformed target
differ.**  The sectionwise difference of their two comorphisms, read as a `V`-derivation of
`𝒪_W` with values in `a_*𝒞_{Z/X}` and transposed to a map out of `a^*Ω_{W/V}`. -/
@[stacks 0619 "the difference read as a map out of the pulled back differentials, for an \
undeformed target"]
def undeformedLiftDiff (c c' : X ⟶ W)
    (h : subspaceInclusion B S hS X Z ≫ c = a)
    (h' : subspaceInclusion B S hS X Z ≫ c' = a) (hb : c ≫ b = c' ≫ b) :
    (modulePullback B S hS a).obj (sheafOfDifferentials B S hS b) ⟶
      conormalModule B S hS X Z :=
  letI := isLocallySurjective_sheafHom_id_structureRingSheaf B S hS (W := W)
  liftDifferenceDifferentialsHom B S hS b a (conormalModule B S hS X Z)
    (undeformedLiftDifferenceData B S hS Z hZ a c c' h h')
    (undeformedLiftDifferenceData_descend_eq_zero B S hS Z hZ a b c c' h h' hb)

/-- The defining equation of `AlgebraicGeometry.Space.undeformedLiftDiff`. -/
theorem undeformedLiftDiff_eq (c c' : X ⟶ W)
    (h : subspaceInclusion B S hS X Z ≫ c = a)
    (h' : subspaceInclusion B S hS X Z ≫ c' = a) (hb : c ≫ b = c' ≫ b) :
    undeformedLiftDiff B S hS Z hZ a b c c' h h' hb =
      letI := isLocallySurjective_sheafHom_id_structureRingSheaf B S hS (W := W)
      liftDifferenceDifferentialsHom B S hS b a (conormalModule B S hS X Z)
        (undeformedLiftDifferenceData B S hS Z hZ a c c' h h')
        (undeformedLiftDifferenceData_descend_eq_zero B S hS Z hZ a b c c' h h' hb) := rfl

/-- **A lift does not differ from itself.** -/
theorem undeformedLiftDiff_self (c : X ⟶ W)
    (h : subspaceInclusion B S hS X Z ≫ c = a) :
    undeformedLiftDiff B S hS Z hZ a b c c h h rfl = 0 :=
  let := isLocallySurjective_sheafHom_id_structureRingSheaf B S hS (W := W)
  liftDifferenceDifferentialsHom_eq_zero B S hS b a (conormalModule B S hS X Z)
    (undeformedLiftDifferenceData B S hS Z hZ a c c h h)
    (undeformedLiftDifferenceData_descend_eq_zero B S hS Z hZ a b c c h h rfl)
    ((undeformedLiftDifferenceData_f B S hS Z hZ a c c h h).trans
      (undeformedLiftDifferenceData_g B S hS Z hZ a c c h h).symm)

/-- **The differences along a chain of three lifts add up.** -/
theorem undeformedLiftDiff_add_undeformedLiftDiff (c₁ c₂ c₃ : X ⟶ W)
    (h₁ : subspaceInclusion B S hS X Z ≫ c₁ = a)
    (h₂ : subspaceInclusion B S hS X Z ≫ c₂ = a)
    (h₃ : subspaceInclusion B S hS X Z ≫ c₃ = a)
    (hb₁₂ : c₁ ≫ b = c₂ ≫ b) (hb₂₃ : c₂ ≫ b = c₃ ≫ b) (hb₁₃ : c₁ ≫ b = c₃ ≫ b) :
    undeformedLiftDiff B S hS Z hZ a b c₁ c₂ h₁ h₂ hb₁₂ +
        undeformedLiftDiff B S hS Z hZ a b c₂ c₃ h₂ h₃ hb₂₃ =
      undeformedLiftDiff B S hS Z hZ a b c₁ c₃ h₁ h₃ hb₁₃ := by
  rw [undeformedLiftDiff_eq B S hS Z hZ a b c₁ c₂ h₁ h₂ hb₁₂,
    undeformedLiftDiff_eq B S hS Z hZ a b c₂ c₃ h₂ h₃ hb₂₃,
    undeformedLiftDiff_eq B S hS Z hZ a b c₁ c₃ h₁ h₃ hb₁₃]
  let := isLocallySurjective_sheafHom_id_structureRingSheaf B S hS (W := W)
  exact liftDifferenceDifferentialsHom_add B S hS b a (conormalModule B S hS X Z)
    (undeformedLiftDifferenceData B S hS Z hZ a c₁ c₂ h₁ h₂)
    (undeformedLiftDifferenceData B S hS Z hZ a c₂ c₃ h₂ h₃)
    (undeformedLiftDifferenceData B S hS Z hZ a c₁ c₃ h₁ h₃)
    (undeformedLiftDifferenceData_descend_eq_zero B S hS Z hZ a b c₁ c₂ h₁ h₂ hb₁₂)
    (undeformedLiftDifferenceData_descend_eq_zero B S hS Z hZ a b c₂ c₃ h₂ h₃ hb₂₃)
    (undeformedLiftDifferenceData_descend_eq_zero B S hS Z hZ a b c₁ c₃ h₁ h₃ hb₁₃)
    ((undeformedLiftDifferenceData_g B S hS Z hZ a c₁ c₂ h₁ h₂).trans
      (undeformedLiftDifferenceData_f B S hS Z hZ a c₂ c₃ h₂ h₃).symm)
    ((undeformedLiftDifferenceData_f B S hS Z hZ a c₁ c₂ h₁ h₂).trans
      (undeformedLiftDifferenceData_f B S hS Z hZ a c₁ c₃ h₁ h₃).symm)
    ((undeformedLiftDifferenceData_g B S hS Z hZ a c₂ c₃ h₂ h₃).trans
      (undeformedLiftDifferenceData_g B S hS Z hZ a c₁ c₃ h₁ h₃).symm)

end AlgebraicGeometry.Space

end
