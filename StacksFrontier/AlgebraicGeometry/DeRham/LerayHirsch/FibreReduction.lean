module

public import StacksFrontier.AlgebraicGeometry.DeRham.LerayHirsch.FibreDetection
public import StacksFrontier.AlgebraicGeometry.DeRham.LerayHirsch.ResidueFieldPoint
public import StacksFrontier.AlgebraicGeometry.DeRham.ProperSmoothDeRhamBaseChange
public import StacksFrontier.AlgebraicGeometry.DeRham.DeRhamCohomologyDirectImage
public import StacksFrontier.AlgebraicGeometry.Perfect.VectorBundleComparisonSurjective
public import StacksFrontier.Topology.Sheaves.Cohomology.PerfectComplexes.TriangulatedSubcategory

/-!
# The Leray--Hirsch morphism is an isomorphism once it is one on cohomology of the fibres

Let `f : X ⟶ Y` be proper and smooth and let `a_i : 𝒪_Y[-n_i] ⟶ Rf_*Ω^•_{X/Y}` be morphisms of
`D(𝒪_Y)`. If at every point `y` of `Y` the classes induced by the `a_i` in the de Rham cohomology
of the fibre `X_y` form a basis over `κ(y)`, then `⨁ a_i : ⨁_i 𝒪_Y[-n_i] ⟶ Rf_*Ω^•_{X/Y}` is an
isomorphism.

## Main definitions

* `AlgebraicGeometry.DeRhamLerayHirsch.residuePoint`: `i_y` as a morphism of ringed spaces.
* `AlgebraicGeometry.DeRhamLerayHirsch.fibreBaseChange`: the base change isomorphism
  `Li_y^*Rf_*Ω^•_{X/Y} ⟶ R(f_y)_*Ω^•_{X_y/κ(y)}`.

## Main results

* `AlgebraicGeometry.DeRhamLerayHirsch.isPerfect_biproduct_unitComplex`: `⨁_i 𝒪_Y[-n_i]` is
  perfect.
* `AlgebraicGeometry.DeRhamLerayHirsch.isIso_fibreBaseChange`: the base change map to a fibre is
  an isomorphism.
* `AlgebraicGeometry.DeRhamLerayHirsch.isIso_biproduct_desc_of_forall_basis`: `⨁ a_i` is an
  isomorphism once the classes of the `a_i` form a basis of the cohomology of every fibre.
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry
open Stacks.Cohomology.DerivedGlobalCupProduct Stacks.Cohomology.GlobalKunneth
open Stacks.Cohomology.DerivedAdjunctionOnRingedSpaces Stacks.Cohomology.DerivedBaseChange
open Stacks.Cohomology.HomologyPullback Stacks.Cohomology.ResidueFieldPoint
open Stacks.DeRhamDirectImage Stacks.DeRhamBaseChange AlgebraicGeometry.ProperSmoothDeRham
open AlgebraicGeometry.DeRhamCohomologyDirectImage

universe u

namespace AlgebraicGeometry.DeRhamLerayHirsch

attribute [local instance 2000] HasDerivedCategory.standard

/-! ### Perfectness of the source -/

/-- **`𝒪_Y[-m]` is a perfect object of `D(𝒪_Y)`.** -/
theorem isPerfect_unitComplex (Y : Scheme.{u}) (m : ℤ) :
    Stacks.Cohomology.PerfectComplexes.IsPerfect (X := Y.toRingedSpace)
      (DerivedCategory.Q.obj (unitComplex Y.toRingedSpace m)) :=
  Stacks.Cohomology.PerfectComplexTriangles.isPerfect_of_iso.{u, u + 1}
    ((DerivedCategory.singleFunctorIsoCompQ Y.Modules m).app _)
    (Stacks.Perfect.BoundedLocallyFreeComplexes.isPerfect_singleFunctor_shift Y _
      (isFiniteLocallyFree_unit Y) m)

/-- **`⨁_i 𝒪_Y[-n_i]` is a perfect object of `D(𝒪_Y)`.** -/
theorem isPerfect_biproduct_unitComplex (Y : Scheme.{u}) {N : ℕ} (n : Fin N → ℤ) :
    Stacks.Cohomology.PerfectComplexes.IsPerfect (X := Y.toRingedSpace)
      (⨁ fun i => DerivedCategory.Q.obj (unitComplex Y.toRingedSpace (n i))) :=
  ObjectProperty.prop_of_iso (Stacks.Cohomology.PerfectComplexes.IsPerfect (X := Y.toRingedSpace))
    (biproduct.isoProduct _).symm
    (ObjectProperty.prop_product _ fun i => isPerfect_unitComplex Y (n i))

/-! ### The fibre square and base change -/

section Fibre

variable {X Y : Scheme.{u}} (f : X ⟶ Y)

/-- The point `i_y : Spec κ(y) ⟶ Y`, as a morphism of ringed spaces. -/
abbrev residuePoint (y : Y) : (Spec (Y.residueField y)).toRingedSpace ⟶ Y.toRingedSpace :=
  (Y.fromSpecResidueField y).toLRSHom.toShHom

/-- The fibre square `X_y ⟶ X`, `X_y ⟶ Spec κ(y)` of `f` over `y` is cartesian. -/
alias isPullback_fiber := AlgebraicGeometry.isPullback_fiberι_fiberToSpecResidueField

/-- **The base change map of `Rf_*Ω^•_{X/Y}` to a fibre**:
`Li_y^* Rf_*Ω^•_{X/Y} ⟶ R(f_y)_*Ω^•_{X_y/κ(y)}`, the derived base change map of [Stacks, Tag 08HY]
for the fibre square followed by the canonical map of de Rham complexes, read on the two
localizations of the de Rham complexes. -/
def fibreBaseChange (y : Y) :
    (derivedPullback (residuePoint y)).obj (derivedDeRhamDirectImageUnbounded f) ⟶
      derivedDeRhamDirectImageUnbounded (f.fiberToSpecResidueField y) :=
  (derivedPullback (residuePoint y)).map ((derivedPushforward (inverseImageBaseProjection f)).map
      ((DerivedCategory.quotientCompQhIso _).inv.app (deRhamComplexInt f))) ≫
    (derivedBaseChangeMap (inverseImageBaseMap (f.fiberι y) (f.fiberToSpecResidueField y) f
        (Y.fromSpecResidueField y) pullback.condition)
      (inverseImageBaseProjection (f.fiberToSpecResidueField y)) (inverseImageBaseProjection f)
      (Y.fromSpecResidueField y).toLRSHom.toShHom
      (inverseImageBaseMap_comp_inverseImageBaseProjection _ _ f _ pullback.condition)
      (DerivedCategory.Qh.obj ((HomotopyCategory.quotient _ (ComplexShape.up ℤ)).obj
        (deRhamComplexInt f))) ≫
    (derivedPushforward (inverseImageBaseProjection (f.fiberToSpecResidueField y))).map
      (deRhamBaseChangeComparison (f.fiberι y) (f.fiberToSpecResidueField y) f
        (Y.fromSpecResidueField y) pullback.condition)) ≫
    (derivedPushforward (inverseImageBaseProjection (f.fiberToSpecResidueField y))).map
      ((DerivedCategory.quotientCompQhIso _).hom.app
        (deRhamComplexInt (f.fiberToSpecResidueField y)))

/-- **Base change to a fibre**: for `f` proper and smooth, `fibreBaseChange` is an isomorphism
([Stacks, Tag 0FM0]). -/
instance isIso_fibreBaseChange [IsProper f] [Smooth f] (y : Y) : IsIso (fibreBaseChange f y) := by
  have := isIso_derivedBaseChangeMap_deRhamComplex (isPullback_fiber f y)
  dsimp only [fibreBaseChange]
  infer_instance

/-- The residue field `κ(y)`, as a type. -/
abbrev ResidueType (y : Y) : Type u := Y.residueField y

/-- **The fibre criterion.** Let `f` be proper and smooth and let
`a_i : 𝒪_Y[-n_i] ⟶ Rf_*Ω^•_{X/Y}` be morphisms of `D(𝒪_Y)`. Suppose that at every point `y` the
classes obtained from the pullback of the class of `1` to `Spec κ(y)` by
`Li_y^*a_i` followed by base change to the fibre form a basis of the total cohomology
`⨁_k H^k(Spec κ(y), R(f_y)_*Ω^•_{X_y/κ(y)})` over `κ(y)`. Then `⨁ a_i` is an isomorphism. -/
theorem isIso_biproduct_desc_of_forall_basis [IsProper f] [Smooth f] {N : ℕ} (n : Fin N → ℤ)
    (a : ∀ i, DerivedCategory.Q.obj (unitComplex Y.toRingedSpace (n i)) ⟶
      derivedDeRhamDirectImageUnbounded f)
    (h : ∀ y : Y, ∃ b : Module.Basis (Fin N) (ResidueType y)
        (DirectSum ℤ fun k => (restrictToField (ResidueType y)).obj (cohomologyModule
          (derivedDeRhamDirectImageUnbounded (f.fiberToSpecResidueField y)) k)),
      ∀ i, b i = DirectSum.lof (ResidueType y) ℤ (fun k => (restrictToField (ResidueType y)).obj
          (cohomologyModule (derivedDeRhamDirectImageUnbounded (f.fiberToSpecResidueField y)) k))
        (n i) (((DerivedCategory.homologyFunctor _ (n i)).map ((baseSections _).map
          ((derivedPullback (residuePoint y)).map (a i) ≫ fibreBaseChange f y))).hom
          (homologyPullback (residuePoint y) _ (n i) (unitCycleClass Y.toRingedSpace (n i))))) :
    IsIso (biproduct.desc a) := by
  let φ := biproduct.desc a
  refine DerivedFibreDetection.isIso_of_forall_isIso_derivedPullback φ
    (isPerfect_biproduct_unitComplex Y n) (isPerfect_derivedPushforward_deRhamComplex f)
    fun y => ?_
  obtain ⟨b, hb⟩ := h y
  have hd := Stacks.Cohomology.OnePointDetection.isIso_biproduct_desc_of_basis
      (fun k => pointCohomology (ResidueType y) k)
      (fun φ hφ => isIso_of_forall_isIso_pointCohomology (ResidueType y) φ hφ) n
      (fun i => (derivedPullback (residuePoint y)).obj
        (DerivedCategory.Q.obj (unitComplex Y.toRingedSpace (n i))))
      _ (fun i => (derivedPullback (residuePoint y)).map (a i) ≫ fibreBaseChange f y)
      (fun i => homologyPullback (residuePoint y) _ (n i) (unitCycleClass Y.toRingedSpace (n i)))
      (fun i j x => exists_lof_eq_smul_homologyPullback (ResidueType y) (residuePoint y) (n i) j x)
      b hb
  have hcomp : (derivedPullback (residuePoint y)).map φ ≫ fibreBaseChange f y =
      ((derivedPullback (residuePoint y)).mapBiproduct _).hom ≫
        biproduct.desc (fun i => (derivedPullback (residuePoint y)).map (a i) ≫
          fibreBaseChange f y) := by
    refine (congrArg (· ≫ fibreBaseChange f y)
      (biproduct.mapBiproduct_hom_desc (derivedPullback (residuePoint y)) _ a).symm).trans ?_
    refine (Category.assoc _ _ _).trans (congrArg (_ ≫ ·) ?_)
    refine biproduct.hom_ext' _ _ fun i => ?_
    rw [biproduct.ι_desc_assoc, biproduct.ι_desc]
  have : IsIso ((derivedPullback (residuePoint y)).map φ ≫ fibreBaseChange f y) := by
    rw [hcomp]
    exact @IsIso.comp_isIso _ _ _ _ _ _ _ inferInstance hd
  exact IsIso.of_isIso_comp_right _ (fibreBaseChange f y)

end Fibre

end AlgebraicGeometry.DeRhamLerayHirsch
