module

public import StacksFrontier.AlgebraicGeometry.Duality.TwistedInverseImageFTS.NewShriekStructureSheafRestrict
public import StacksFrontier.AlgebraicGeometry.Duality.UpperShriekFibreDimensionCharts
public import StacksFrontier.AlgebraicGeometry.Duality.UpperShriekFibreDimensionFlatCharts
public import StacksFrontier.AlgebraicGeometry.Morphisms.FibreDimension.Comparison

/-!
# The fibre-dimension bounds for `f_new^! 𝒪_Y`

In Situation [Stacks, Tag 0AU4], let `f : X ⟶ Y` be a morphism of schemes of finite type over
`S`, not necessarily separated, and let `x ∈ X` with image `y ∈ Y`. With `f^!` replaced by
`f_new^!` ([Stacks, Tag 0BV9]):

* [Stacks, Tag 0BV5]: `H^i(f_new^! 𝒪_Y)_x ≠ 0 ⟹ -dim_x(X_y) ≤ i`;
* the first assertion of [Stacks, Tag 0BV6]: if `f` is flat, `H^i(f_new^! 𝒪_Y)_x ≠ 0 ⟹
  -dim_x(X_y) ≤ i ≤ 0`.

The proof is the source's: the statements are local on `X`, on an affine open `V ∋ x` the
restriction of `f_new^! 𝒪_Y` is `(V → Y)^! 𝒪_Y`
(`Stacks.Duality.NormalizedOnOpens.nontrivial_stalk_homology_newShriek_iff`), and `V → Y` is a
morphism of `FTS_Y` with the same local fibre dimension at `x`, to which
[Stacks, Tag 0BV5] and [Stacks, Tag 0BV6] apply.

## Main results

* `Stacks.Duality.NormalizedOnOpens.neg_fibreDim_le_of_nontrivial_stalk_homology_newShriek`
* `Stacks.Duality.NormalizedOnOpens.fibreDim_bounds_of_nontrivial_stalk_homology_newShriek_of_flat`

## References

* [Stacks Project, Tag 0BV9](https://stacks.math.columbia.edu/tag/0BV9)
* [Stacks Project, Tag 0BV5](https://stacks.math.columbia.edu/tag/0BV5)
* [Stacks Project, Tag 0BV6](https://stacks.math.columbia.edu/tag/0BV6)
-/

-- This file uses the locally small derived-category models below, which are not
-- global instances (see `StacksFrontier.Homology.DerivedCategory.LocallySmall`):
-- `D(𝒪_X)` for a scheme.
attribute [local instance] AlgebraicGeometry.Scheme.Modules.hasDerivedCategory

@[expose] public noncomputable section

open AlgebraicGeometry CategoryTheory Opposite

universe u

namespace Stacks.Duality

namespace NormalizedOnOpens

variable (c : ∀ {X Y : Scheme.{u}} (f : X ⟶ Y), IsShriekable f → CompactificationOf (Over.mk f))
  {X Y S : Scheme.{u}} {f : X ⟶ Y} {q : Y ⟶ S} {p : X ⟶ S}
  {hp : IsFiniteTypeOverNoetherian p} {hq : IsFiniteTypeOverNoetherian q}
  {ωS : quasiCoherentDerivedCategoryPlusOfModel S}
  (𝒦X : NormalizedOnOpens (UpperShriek.ofCompactifications c) hp ωS)
  (𝒦Y : NormalizedOnOpens (UpperShriek.ofCompactifications c) hq ωS)
  (hpe : f ≫ q = p) (hωS : haveI := hp.base_noetherian; IsDualizingComplex ωS.obj.obj)

include hpe hωS in
/-- **[Stacks, Tag 0BV5] for `f_new^!`.** For a morphism `f : X ⟶ Y` of schemes of finite type
over the base of [Stacks, Tag 0AU4], not necessarily separated, and `x ∈ X`,

  `H^i(f_new^! 𝒪_Y)_x ≠ 0 ⟹ -dim_x(X_y) ≤ i`,

the local dimension `dim_x(X_y)` of the fibre being named by `hd`. -/
theorem neg_fibreDim_le_of_nontrivial_stalk_homology_newShriek (x : X) (d : ℕ)
    (hd : topologicalKrullDimAt (f.fiber (f x)) (f.asFiber x) = (d : WithBot ℕ∞)) (i : ℤ)
    (hi : Nontrivial (((@DerivedCategory.homologyFunctor X.Modules _ _
      (PerfectApproximation.standardModel X) i).obj
        (newShriekStructureSheaf c f 𝒦X 𝒦Y)).presheaf.stalk x)) :
    -(d : ℤ) ≤ i := by
  have := hq.source_noetherian
  obtain ⟨V, hV, hxV, -⟩ :=
    exists_isAffineOpen_mem_and_subset (X := X) (x := x) (U := ⊤) (by simp)
  have hsh := hp.isShriekable_ι_comp_of_isAffineOpen hq hpe hV
  have hi' := (nontrivial_stalk_homology_newShriek_iff c 𝒦X 𝒦Y hpe hωS V hsh i ⟨x, hxV⟩).1 hi
  exact neg_fibreDim_le_of_nontrivial_stalk_homology_upperShriek_unconditional (ftsHomSelf hsh)
    (c _ hsh) ⟨x, hxV⟩ d ((fiberDimensionAt_comp_openImmersion V.ι f ⟨x, hxV⟩).trans hd) i hi'

include hpe hωS in
/-- **The first assertion of [Stacks, Tag 0BV6] for `f_new^!`.** For a flat morphism
`f : X ⟶ Y` of schemes of finite type over the base of [Stacks, Tag 0AU4], not necessarily
separated, and `x ∈ X`,

  `H^i(f_new^! 𝒪_Y)_x ≠ 0 ⟹ -dim_x(X_y) ≤ i ≤ 0`,

the local dimension `dim_x(X_y)` of the fibre being named by `hd`. -/
theorem fibreDim_bounds_of_nontrivial_stalk_homology_newShriek_of_flat [Flat f] (x : X) (d : ℕ)
    (hd : topologicalKrullDimAt (f.fiber (f x)) (f.asFiber x) = (d : WithBot ℕ∞)) (i : ℤ)
    (hi : Nontrivial (((@DerivedCategory.homologyFunctor X.Modules _ _
      (PerfectApproximation.standardModel X) i).obj
        (newShriekStructureSheaf c f 𝒦X 𝒦Y)).presheaf.stalk x)) :
    -(d : ℤ) ≤ i ∧ i ≤ 0 := by
  have := hq.source_noetherian
  obtain ⟨V, hV, hxV, -⟩ :=
    exists_isAffineOpen_mem_and_subset (X := X) (x := x) (U := ⊤) (by simp)
  have hsh := hp.isShriekable_ι_comp_of_isAffineOpen hq hpe hV
  have hi' := (nontrivial_stalk_homology_newShriek_iff c 𝒦X 𝒦Y hpe hωS V hsh i ⟨x, hxV⟩).1 hi
  have : Flat (ftsHomSelf hsh).left := inferInstanceAs (Flat (V.ι ≫ f))
  exact fibreDim_bounds_of_nontrivial_stalk_homology_upperShriek_of_flat_unconditional
    (ftsHomSelf hsh) (c _ hsh) ⟨x, hxV⟩ d
    ((fiberDimensionAt_comp_openImmersion V.ι f ⟨x, hxV⟩).trans hd) i hi'

end NormalizedOnOpens

end Stacks.Duality

end
