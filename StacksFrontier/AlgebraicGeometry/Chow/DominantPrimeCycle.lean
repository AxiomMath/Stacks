module

public import StacksFrontier.AlgebraicGeometry.Chow.GysinConstruction.IntegralComponent
public import StacksFrontier.AlgebraicGeometry.Chow.ProperPushforwardChow.Functoriality
public import StacksFrontier.AlgebraicGeometry.Morphisms.QuasiFinite.ResidueField
public import StacksCore.Tactic.StacksAttribute

/-!
# A prime cycle dominating the target of a proper dominant morphism

Let `f : X ⟶ Y` be a proper dominant morphism with `Y` integral, and let `k` be the
delta-dimension of `Y`. Then `X` carries an integral closed subscheme `Z` whose delta-dimension
is again `k` and whose proper pushforward is a positive multiple of the fundamental cycle of
`Y`:

`f_* [Z]_k = m [Y]_k` with `m > 0`.

## Main results

* `Stacks.Chow.exists_point_eq_genericPoint_and_finite_residueField`: a proper dominant morphism
  onto an integral scheme has a point over the generic point of the target whose residue field
  extension is finite.
* `Stacks.Chow.relativeDimension_eq_of_finite_residueField`: a point whose residue field is
  finite over that of its image has the same relative dimension as its image.
* `Stacks.Chow.cycleAssociatedToClosedSubscheme_eq_single`: the fundamental cycle of an integral
  closed subscheme is the prime cycle of its generic point with coefficient one.
* `Stacks.Chow.exists_properPushforward_eq_nsmul_fundamentalCycle`: the statement displayed
  above.

## References

* [Stacks Project, Tag 01TF](https://stacks.math.columbia.edu/tag/01TF)
* [Stacks Project, Tag 02R4](https://stacks.math.columbia.edu/tag/02R4)
-/

@[expose] public noncomputable section

open AlgebraicGeometry CategoryTheory TopologicalSpace

universe u

namespace Stacks.Chow

/-! ### A closed point of the fibre over the generic point -/

/-- A point of a fibre, viewed in the fibre over the image of the point of the ambient scheme it
determines: the two fibres have equal underlying sets, and the identification carries one
description of the point to the other. -/
private theorem homeomorph_fiber_apply {X Y : Scheme.{u}} (f : X ⟶ Y) (y : Y) (z : f.fiber y)
    (hset : f.base ⁻¹' {y} = f.base ⁻¹' {f.base (f.fiberι y z)}) :
    ((f.fiberHomeo y).trans
        ((Homeomorph.setCongr hset).trans (f.fiberHomeo _).symm)) z =
      f.asFiber (f.fiberι y z) := by
  apply (f.fiberι (f.base (f.fiberι y z))).isEmbedding.injective
  rw [Scheme.Hom.fiberι_asFiber]
  change f.fiberι _ ((f.fiberHomeo _).symm _) = _
  rw [Scheme.Hom.fiberι_fiberHomeo_symm]
  rfl

/-- A proper dominant morphism onto an integral scheme has a point above the generic point of the
target whose residue field is finite over the residue field of the generic point. -/
theorem exists_point_eq_genericPoint_and_finite_residueField {X Y : Scheme.{u}} (f : X ⟶ Y)
    [IsProper f] [IsDominant f] [IsIntegral Y] :
    ∃ x : X, f.base x = genericPoint Y ∧
      letI := (f.residueFieldMap x).hom.toAlgebra
      Module.Finite (Y.residueField (f.base x)) (X.residueField x) := by
  classical
  obtain ⟨x₀, hx₀⟩ := f.surjective (genericPoint Y)
  have : Nonempty (f.fiber (genericPoint Y)) := ⟨(f.fiberHomeo _).symm ⟨x₀, hx₀⟩⟩
  obtain ⟨y, -, hyClosed⟩ :=
    nonempty_inter_closedPoints (X := f.fiber (genericPoint Y)) (Z := Set.univ)
      Set.univ_nonempty isClosed_univ.isLocallyClosed
  have hxη : f.base (f.fiberι (genericPoint Y) y) = genericPoint Y := by
    have hmem : f.fiberι (genericPoint Y) y ∈ f.base ⁻¹' {genericPoint Y} := by
      rw [← f.range_fiberι (genericPoint Y)]
      exact Set.mem_range_self y
    exact hmem
  refine ⟨f.fiberι (genericPoint Y) y, hxη, ?_⟩
  refine (isClosed_asFiber_iff_finite_residueField f (f.fiberι (genericPoint Y) y)).mp ?_
  have hset : f.base ⁻¹' {genericPoint Y} =
      f.base ⁻¹' {f.base (f.fiberι (genericPoint Y) y)} := by rw [hxη]
  simpa only [Set.image_singleton, homeomorph_fiber_apply f (genericPoint Y) y hset] using
    ((f.fiberHomeo (genericPoint Y)).trans
      ((Homeomorph.setCongr hset).trans (f.fiberHomeo _).symm)).isClosedMap _ hyClosed

/-! ### Relative dimension across a finite residue field extension -/

/-- A point whose residue field is finite over the residue field of its image has the same
relative dimension over the base as that image. -/
theorem relativeDimension_eq_of_finite_residueField {S X Y : Scheme.{u}}
    (δ : DimensionFunction S) (sY : Y ⟶ S) [LocallyOfFiniteType sY] (f : X ⟶ Y)
    [LocallyOfFiniteType f] (x : X)
    (hx : letI := (f.residueFieldMap x).hom.toAlgebra
      Module.Finite (Y.residueField (f.base x)) (X.residueField x)) :
    relativeDimension δ (f ≫ sY) x = relativeDimension δ sY (f.base x) := by
  let := (f.residueFieldMap x).hom.toAlgebra
  let := hx
  have halg : Algebra.IsAlgebraic (Y.residueField (f.base x)) (X.residueField x) :=
    Algebra.IsAlgebraic.of_finite _ _
  have hzero : residueTrdeg f x = 0 := trdeg_eq_zero_iff.mpr halg
  rw [relativeDimension_comp_eq_add_trdeg δ sY f x, hzero]
  simp

/-! ### The fundamental cycle of an integral closed subscheme as a prime cycle -/

/-- The fundamental cycle `[Z]_k` of an integral closed subscheme `i : Z ⟶ X` of
delta-dimension `k` is the prime cycle of the image of the generic point of `Z`, with
coefficient one. -/
theorem cycleAssociatedToClosedSubscheme_eq_single (C : ChowSituation.{u}) {X Z : Scheme.{u}}
    (p : X ⟶ C.S) [LocallyOfFiniteType p] (i : Z ⟶ X) [IsClosedImmersion i] [IsIntegral Z]
    (k : ℤ) (hk : relativeDimension C.dimensionFunction p (i.base (genericPoint Z)) = k) :
    (cycleAssociatedToClosedSubscheme C p i k).1 =
      @Function.locallyFinsuppWithin.single X _ ℤ (Classical.decEq X) _
        (i.base (genericPoint Z)) (1 : ℤ) := by
  classical
  have hmem : genericPoint Z ∈ genericPoints Z := genericPoint_mem_genericPoints Z
  refine Function.locallyFinsuppWithin.ext fun y ↦ ?_
  by_cases hy : y = i.base (genericPoint Z)
  · subst y
    rw [cycleAssociatedToClosedSubscheme_apply C p i k ⟨genericPoint Z, hmem⟩ hk,
      componentMultiplicity_eq_one i hmem]
    simp
  · rw [cycleAssociatedToClosedSubscheme_apply_eq_zero C p i k y ?_]
    · simp [hy]
    · rintro ⟨ζ, hζ, -⟩
      refine hy ?_
      have hζgen : (ζ : Z) = genericPoint Z := by
        have : (ζ : Z) ∈ ({genericPoint Z} : Set Z) := by
          rw [← genericPoints_eq_singleton]
          exact ζ.2
        exact this
      rw [← hζ, hζgen]

/-! ### The pushforward of the prime cycle -/

/-- For `f : X ⟶ Y` proper and dominant with `Y` integral of delta-dimension `k`, there is an
integral closed subscheme `Z ⊆ X` with `f_*[Z]_k = m[Y]_k` for some `m > 0`. -/
theorem exists_properPushforward_eq_nsmul_fundamentalCycle (C : ChowSituation.{u})
    {X Y : Scheme.{u}} (sX : X ⟶ C.S) [LocallyOfFiniteType sX] (sY : Y ⟶ C.S)
    [LocallyOfFiniteType sY] (f : X ⟶ Y) [IsProper f] [IsDominant f] (hf : f ≫ sY = sX)
    [IsIntegral Y] (k : ℤ)
    (hk : relativeDimension C.dimensionFunction sY (genericPoint Y) = k) :
    ∃ (W : X.IdealSheafData) (hW : IsIntegral W.subscheme) (m : ℕ), m ≠ 0 ∧
      letI := hW
      properPushforward C sX sY f hf k
          (cycleAssociatedToClosedSubscheme C sX W.subschemeι k) =
        m • cycleAssociatedToClosedSubscheme C sY (𝟙 Y) k := by
  classical
  obtain ⟨x, hxη, hxfin⟩ := exists_point_eq_genericPoint_and_finite_residueField f
  let := (f.residueFieldMap x).hom.toAlgebra
  let := hxfin
  have hxdim : relativeDimension C.dimensionFunction sX x = k := by
    rw [← hf, relativeDimension_eq_of_finite_residueField C.dimensionFunction sY f x hxfin, hxη]
    exact hk
  have hW : IsIntegral (integralComponentAt x).subscheme := isIntegral_integralComponentAt x
  let := hW
  have hgen : (integralComponentAt x).subschemeι.base
      (genericPoint (integralComponentAt x).subscheme) = x :=
    genericPointOf_integralComponentAt x
  have hαsingle : (cycleAssociatedToClosedSubscheme C sX
      (integralComponentAt x).subschemeι k).1 =
      @Function.locallyFinsuppWithin.single X _ ℤ (Classical.decEq X) _ x (1 : ℤ) := by
    rw [cycleAssociatedToClosedSubscheme_eq_single C sX (integralComponentAt x).subschemeι k
      (by rw [hgen]; exact hxdim), hgen]
  have hβsingle : (cycleAssociatedToClosedSubscheme C sY (𝟙 Y) k).1 =
      @Function.locallyFinsuppWithin.single Y _ ℤ (Classical.decEq Y) _ (genericPoint Y)
        (1 : ℤ) :=
    cycleAssociatedToClosedSubscheme_eq_single C sY (𝟙 Y) k hk
  have hdegpos : 0 < f.residueDegree x := by
    dsimp [Scheme.Hom.residueDegree]
    exact Module.finrank_pos
  refine ⟨integralComponentAt x, hW, f.residueDegree x, hdegpos.ne', Subtype.ext ?_⟩
  rw [properPushforward_single C sX sY f hf k x _ hαsingle, hxη, ite_eq_left hk]
  change _ = f.residueDegree x • (cycleAssociatedToClosedSubscheme C sY (𝟙 Y) k).1
  rw [hβsingle]
  refine Function.locallyFinsuppWithin.ext fun y ↦ ?_
  by_cases hy : y = genericPoint Y <;> simp [hy]

end Stacks.Chow

end
