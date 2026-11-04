module

public import Mathlib.AlgebraicGeometry.Artinian
public import Mathlib.AlgebraicGeometry.ZariskisMainTheorem
public import StacksFrontier.AlgebraicGeometry.Chow.PrincipalDivisorPushforward.Codimension
public import StacksFrontier.AlgebraicGeometry.Chow.ProperPushforwardChow.Functoriality
public import StacksFrontier.AlgebraicGeometry.Morphisms.Dominant.IntegralSchemes

/-!
# A proper dominant morphism is finite near a point of codimension one

Let `C = (S, δ)` be a Chow situation, let `X` and `Y` be integral and locally of finite type over
`S` of the same delta-dimension `n`, and let `p : X ⟶ Y` be a proper dominant morphism over `S`.
This file shows that `p` is finite over an open neighbourhood of every point `y` of `Y` of
codimension one; this is the step that lets the coefficient of `p_*div(f)` at the generic point of
a prime divisor of `Y` be computed in a single pair of affine rings.

The Stacks Project obtains this from the general statement that a proper, generically quasi-finite
morphism is finite near a point whose local ring has dimension at most one (Stacks 0AB7, resting
on Stacks 0AB6). In the situation at hand the dimension function of Stacks 02JW makes the argument
immediate: every point `x` above `y` has relative dimension exactly `n - 1`, because the relative
dimension can only drop from the generic point of `X` and it grows along `p` by the transcendence
degree of the residue-field extension. Since the relative dimension strictly decreases along every
nontrivial specialization, no two distinct points of the fibre can specialize to one another, so
the fibre is `T1`; being also sober and locally Noetherian it has topological Krull dimension zero,
hence is discrete, hence (being quasi-compact, as `p` is proper) finite. Mathlib's form of
Stacks 02UP, `AlgebraicGeometry.exists_isFinite_morphismRestrict_of_finite_preimage_singleton`,
then produces the neighbourhood.

## Main results

* `Stacks.Chow.topologicalKrullDim_nonpos_of_t1Space` — a sober `T1` space has topological Krull
  dimension at most zero.
* `Stacks.Chow.finite_preimage_singleton_of_specializes_imp_eq` — a fibre of a quasi-compact
  morphism locally of finite type with no nontrivial specializations is finite.
* `Stacks.Chow.relativeDimension_eq_sub_one_of_mem_fibre` — every point of `X` above a point of
  `Y` of codimension one has relative dimension `n - 1`.
* `Stacks.Chow.exists_isFinite_morphismRestrict_of_coheight_eq_one` — `p` is finite over a
  neighbourhood of a point of codimension one.

## References

* [Stacks Project, Tag 02RT](https://stacks.math.columbia.edu/tag/02RT)
* [Stacks Project, Tag 0AB7](https://stacks.math.columbia.edu/tag/0AB7)
* [Stacks Project, Tag 02UP](https://stacks.math.columbia.edu/tag/02UP)
-/

@[expose] public noncomputable section

open AlgebraicGeometry CategoryTheory Limits TopologicalSpace

universe u

namespace Stacks.Chow

/-! ### Fibres with no nontrivial specializations -/

/-- A sober `T1` space has topological Krull dimension at most zero: every irreducible closed
subset is the closure of a point, hence a singleton, so there are no strict inclusions between
irreducible closed subsets. -/
theorem topologicalKrullDim_nonpos_of_t1Space (T : Type*) [TopologicalSpace T] [QuasiSober T]
    [T1Space T] : topologicalKrullDim T ≤ 0 := by
  rw [topologicalKrullDim, Order.krullDim_nonpos_iff_forall_isMax]
  intro Z W hZW
  obtain ⟨z, hz⟩ := QuasiSober.sober Z.isIrreducible' Z.isClosed'
  obtain ⟨w, hw⟩ := QuasiSober.sober W.isIrreducible' W.isClosed'
  have hZ : Z.carrier = {z} := by rw [← hz.def, closure_singleton]
  have hW : W.carrier = {w} := by rw [← hw.def, closure_singleton]
  have hsub : Z.carrier ⊆ W.carrier := hZW
  have hzw : z = w := by simpa [hW] using hsub (by simp [hZ] : z ∈ Z.carrier)
  show W.carrier ⊆ Z.carrier
  simp [hZ, hW, hzw]

/-- The fibre of a quasi-compact morphism locally of finite type over a point `y` is finite as
soon as no point above `y` specializes to a different point above `y`.

The fibre is then `T1`, and a locally Noetherian scheme whose space is `T1` is Artinian, hence
discrete; a quasi-compact discrete space is finite. -/
theorem finite_preimage_singleton_of_specializes_imp_eq {X Y : Scheme.{u}} (f : X ⟶ Y)
    [LocallyOfFiniteType f] [QuasiCompact f] (y : Y)
    (h : ∀ x x' : X, f.base x = y → f.base x' = y → x ⤳ x' → x = x') :
    (f.base ⁻¹' {y}).Finite := by
  have : IsLocallyNoetherian (f.fiber y) :=
    inferInstanceAs (IsLocallyNoetherian (pullback f (Y.fromSpecResidueField y)))
  have hmem : ∀ z : f.fiber y, f.base (f.fiberι y z) = y := by
    intro z
    have hz : f.fiberι y z ∈ Set.range (f.fiberι y).base := ⟨z, rfl⟩
    rw [Scheme.Hom.range_fiberι] at hz
    simpa using hz
  have : T1Space (f.fiber y) := t1Space_iff_specializes_imp_eq.mpr fun {z z'} hzz' ↦
    (f.fiberι y).isEmbedding.injective
      (h _ _ (hmem z) (hmem z') (hzz'.map (f.fiberι y).continuous))
  have : IsLocallyArtinian (f.fiber y) :=
    .of_topologicalKrullDim_le_zero (topologicalKrullDim_nonpos_of_t1Space (f.fiber y))
  have : Finite (f.fiber y) := finite_of_compact_of_discrete
  exact Set.finite_coe_iff.mp ((f.fiberHomeo y).finite_iff.mp inferInstance)

/-! ### The fibres of a proper dominant morphism over a point of codimension one -/

variable (C : ChowSituation.{u}) {X Y : Scheme.{u}} (sX : X ⟶ C.S) [LocallyOfFiniteType sX]
  (sY : Y ⟶ C.S) [LocallyOfFiniteType sY] [IsIntegral X] [IsIntegral Y] {n : ℤ}

/-- For a dominant morphism `p : X ⟶ Y` over the base between integral schemes of the same
delta-dimension `n`, every point of `X` above a point `y` of `Y` of codimension one has relative
dimension `n - 1`.

The relative dimension at such a point is `n - 1` plus the transcendence degree of the
residue-field extension of `p`, and it is at most `n - 1` because the point is not the generic
point of `X`; so the transcendence degree vanishes. -/
theorem relativeDimension_eq_sub_one_of_mem_fibre
    (hnX : schemeDeltaDimension C sX = (n : EInt))
    (hnY : schemeDeltaDimension C sY = (n : EInt))
    (p : X ⟶ Y) [LocallyOfFiniteType p] [IsDominant p] (hp : p ≫ sY = sX)
    {y : Y} (hy : Order.coheight y = 1) {x : X} (hx : p.base x = y) :
    relativeDimension C.dimensionFunction sX x = n - 1 := by
  have hpgen : p.base (genericPoint X) = genericPoint Y :=
    ((tfae_isDominant_of_isIntegral p).out 1 2).mp (inferInstance : IsDominant p)
  have hne : x ≠ genericPoint X := by
    rintro rfl
    rw [hpgen] at hx
    have hmax : IsMax (genericPoint Y) := fun b _ ↦ genericPoint_specializes b
    rw [← hx, Order.coheight_eq_zero.mpr hmax] at hy
    exact zero_ne_one hy
  have hle := relativeDimension_le_sub_one_of_ne_genericPoint C sX hnX hne
  have hstep := relativeDimension_comp_eq_add_trdeg C.dimensionFunction sY p x
  rw [hp, hx, relativeDimension_eq_sub_one_of_coheight_eq_one C sY hnY hy] at hstep
  omega

/-- **Stacks 02RT, the local step.** A proper dominant morphism `p : X ⟶ Y` over the base between
integral schemes of the same delta-dimension is finite over an open neighbourhood of every point
of `Y` of codimension one. -/
theorem exists_isFinite_morphismRestrict_of_coheight_eq_one
    (hnX : schemeDeltaDimension C sX = (n : EInt))
    (hnY : schemeDeltaDimension C sY = (n : EInt))
    (p : X ⟶ Y) [IsProper p] [IsDominant p] (hp : p ≫ sY = sX)
    (y : Y) (hy : Order.coheight y = 1) :
    ∃ V : Y.Opens, y ∈ V ∧ IsFinite (p ∣_ V) := by
  refine exists_isFinite_morphismRestrict_of_finite_preimage_singleton p y
    (finite_preimage_singleton_of_specializes_imp_eq p y fun x x' hx hx' hspec ↦ ?_)
  by_contra hne
  have hlt := (deltaDimensionFunction C sX).strictAnti_specializes hspec hne
  rw [deltaDimensionFunction_apply, deltaDimensionFunction_apply,
    relativeDimension_eq_sub_one_of_mem_fibre C sX sY hnX hnY p hp hy hx,
    relativeDimension_eq_sub_one_of_mem_fibre C sX sY hnX hnY p hp hy hx'] at hlt
  omega

end Stacks.Chow

end
