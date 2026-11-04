module

public import StacksFrontier.AlgebraicGeometry.DeRham.SmoothSpectralSequenceFiltered
import StacksFrontier.CategoryTheory.Sites.Cohomology.UnboundedDerivedFunctor.LeftTExactness
public import StacksFrontier.Algebra.Category.ModuleCat.Sheaf.AbelianOfSmallSite
public import StacksFrontier.Algebra.Homology.DerivedCategory.Filtered.DerivedFunctor
public import StacksFrontier.Algebra.Homology.DegreewiseKernelCokernel
public import StacksFrontier.AlgebraicGeometry.DeRham.WedgeFiltrationDegreewise
import StacksCore.Tactic.EgaSgaAttribute

/-!
# The spectral sequence of a smooth morphism: vanishing below the cut and far along the filtration

Vanishing statements for the filtration of Section 0FMK of the relative de Rham complex of a
composite `X ⟶ Y ⟶ S` of morphisms of schemes, and for the higher direct images of its steps and
graded pieces, as they enter the spectral sequence of [Stacks, Tag 0FMM].

## Main results

* `Stacks.DeRhamSmooth.isZero_higherDirectImage_deRhamSmoothFiltration`: `R^nf_*F^pΩ^•_{X/S} = 0`
  for `0 < p` and `n < p`.
* `Stacks.DeRhamSmooth.isZero_relativeDifferentialForms_of_neg`: `Ω^p_{Y/S} = 0` for `p < 0`.
* `Stacks.DeRhamSmooth.isZero_gradedPiece_of_neg` and
  `Stacks.DeRhamSmooth.isZero_higherDirectImage_gradedPiece_of_neg`: the graded pieces below the
  cut, and their higher direct images, vanish.

## References

* [Stacks Project, Tag 0FMM](https://stacks.math.columbia.edu/tag/0FMM)
* [Stacks Project, Tag 0FMK](https://stacks.math.columbia.edu/tag/0FMK)
-/

@[expose] public noncomputable section

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits Opposite TopologicalSpace
open RingedSpaceModuleAdjunction Stacks.Cohomology.FilteredComplex Stacks.DeRhamDirectImage

attribute [local instance 2000] HasDerivedCategory.standard

universe u

namespace Stacks.DeRhamSmooth

attribute [local instance] Stacks.SheafOfModules.abelianOfSmallSite

/-- `gradedPiece Z p K` is the graded piece `(FilteredObject.gr p).obj K` of the filtered
complex `K`. -/
theorem gradedPiece_eq (Z : RingedSpace.{u, u}) (p : ℤ)
    (K : CochainComplex.Filtered (SheafOfModules.{u} (structureSheafRing Z))) :
    gradedPiece Z p K = (FilteredObject.gr p).obj K :=
  rfl

variable {X Y S : Scheme.{u}} (f : X ⟶ Y) (g : Y ⟶ S)

/-- If a complex is strictly `≥ q`, its higher direct images vanish in degrees `n < q`. -/
private theorem isZero_higherDirectImage_of_isStrictlyGE
    (K : CochainComplex
      (SheafOfModules.{u} (structureSheafRing (inverseImageBase (f ≫ g)))) ℤ)
    (q n : ℤ) (hn : n < q) (hGE : K.IsStrictlyGE q) :
    IsZero (higherDirectImage (derivedRelativePushforward f g) K n) := by
  have hQ : (DerivedCategory.Q.obj K).IsGE q := by
    rw [DerivedCategory.isGE_Q_obj_iff]
    infer_instance
  exact Stacks.DerivedFunctor.isZero_homology_totalRightDerived_obj
    (modulePushforward (relativeBase f g)) (DerivedCategory.Q.obj K) q n hn

/-- **The higher direct images of the far steps of the filtration vanish**: for `0 < p` and
`n < p` one has `R^nf_*F^pΩ^•_{X/S} = 0`. -/
theorem isZero_higherDirectImage_deRhamSmoothFiltration (p n : ℤ) (hp : 0 < p) (hn : n < p) :
    IsZero (higherDirectImage (derivedRelativePushforward f g)
      ((deRhamSmoothFiltration f g).filtration.obj (op p)) n) := by
  exact isZero_higherDirectImage_of_isStrictlyGE f g _ p n hn
    ((CochainComplex.isStrictlyGE_iff _ _).2 fun m hm ↦
      AlgebraicGeometry.SheafOfModules.isZero_wedgeFiltered_filtration_obj_X _ _ _ _ p hp m hm)

/-- **The relative differential forms vanish in negative degrees**: `Ω^p_{Y/S} = 0` for `p < 0`.
-/
@[ega "IV 16.6.1" "Ω^p_{X/S} = 0 for p < 0"]
theorem isZero_relativeDifferentialForms_of_neg (p : ℤ) (hp : p < 0) :
    IsZero (AlgebraicGeometry.Scheme.Hom.relativeDifferentialForms g p) := by
  rw [IsZero.iff_id_eq_zero]
  apply SheafOfModules.hom_ext
  apply PresheafOfModules.hom_ext
  intro U
  apply ModuleCat.hom_ext
  apply LinearMap.ext
  intro x
  have hx : x = 0 :=
    (SheafOfModules.algebras _
      (AlgebraicGeometry.Scheme.Hom.relativeDifferentials g)).exteriorPiece_eq_zero_of_neg
      p hp U x
  rw [hx]
  simp

/-- **The graded pieces below the cut vanish**: `gr^pΩ^•_{X/S} = 0` for `p < 0`. -/
theorem isZero_gradedPiece_of_neg (p : ℤ) (hp : p < 0) :
    IsZero (gradedPiece (inverseImageBase (f ≫ g)) p (deRhamSmoothFiltration f g)) :=
  FilteredObject.isZero_gr_obj_of_isIso_ι_app (deRhamSmoothFiltration f g) (by omega)
    ((deRhamSmoothFiltration_spec f g).2.2.2 0 le_rfl)

/-- **The higher direct images of the graded pieces below the cut vanish**: for `p < 0` one has
`R^nf_*gr^pΩ^•_{X/S} = 0` in every degree `n`. -/
theorem isZero_higherDirectImage_gradedPiece_of_neg (p n : ℤ) (hp : p < 0) :
    IsZero (higherDirectImage (derivedRelativePushforward f g)
      (gradedPiece (inverseImageBase (f ≫ g)) p (deRhamSmoothFiltration f g)) n) := by
  exact isZero_higherDirectImage_of_isStrictlyGE f g _ (n + 1) n (by omega)
    ((CochainComplex.isStrictlyGE_iff _ _).2 fun m _ ↦
      Functor.map_isZero (HomologicalComplex.eval _ _ m) (isZero_gradedPiece_of_neg f g p hp))

end Stacks.DeRhamSmooth

end
