module

public import StacksFrontier.AlgebraicGeometry.Morphisms.Fibres.BertiniFlatFamily
public import StacksFrontier.AlgebraicGeometry.Curves.NodalFamilyCriterion
public import StacksFrontier.AlgebraicGeometry.FibreDimensionBaseChange.Basic
public import StacksFrontier.AlgebraicGeometry.Morphisms.Smooth.LocusBaseChange
public import StacksFrontier.AlgebraicGeometry.Picard.SmoothCurveLocalDimension
public import StacksFrontier.AlgebraicGeometry.Morphisms.FibreDimension.Comparison

/-!
# Smoothness of a family cut out by sections, from one fibre

The family of curves of SGA 4, Exposé XI, Proposition 3.3 is cut out of `X̄ × 𝔸^{d-1}` by `d - 1`
sections of an invertible module, and what the construction controls is the fibre through the
given point. This file provides the two steps that pass from the fibre to the family.

* **Flatness, one equation at a time.** If `P → S` is flat and locally of finite presentation and
  `g` is a section of an invertible module whose restriction to an integral open of the fibre
  through `z` does not vanish identically, then near `z` the zero scheme of `g` is flat over `S`.
  This is [Stacks, Tag 062Y] (3): the fibre of the zero scheme is an effective Cartier divisor
  there, a nonzero section of an invertible module on an integral scheme being regular.
* **Smoothness from the fibre.** If a closed subscheme `Q ⊆ X` is flat and locally of finite
  presentation over `S` and the corresponding closed subscheme of the fibre `X_s` is smooth of
  relative dimension `n` near a point, then `Q → S` is smooth at the image point, with fibre of
  dimension `n` there ([Stacks, Tag 02V4] for the flat `Q → S`, and [Stacks, Tag 02FY] (1)).

## Main results

* `AlgebraicGeometry.exists_flat_zeroScheme_of_fibre`.
* `AlgebraicGeometry.mem_smoothLocus_and_fiberDimensionAt_of_fibre`.

## References

* SGA 4, Tome 3, Exposé XI, Proposition 3.3.
* [Stacks Project, Tag 062Y](https://stacks.math.columbia.edu/tag/062Y)
* [Stacks Project, Tag 02V4](https://stacks.math.columbia.edu/tag/02V4)
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits

universe u

namespace AlgebraicGeometry

/-- **The zero scheme of a section is flat over the base near a point where the fibre does not
contain it.** Let `f : P ⟶ S` be flat and locally of finite presentation, `L` an invertible module
on `P` and `g` a global section, and let `z` be a point of the zero scheme of `g`. If on some
integral open `U` of the fibre `P_{f z}` containing `z` the pullback of `g` is nonzero, then on an
open neighbourhood `V` of `z` the zero scheme of `g` is flat over `S` ([Stacks, Tag 062Y] (3)). -/
theorem exists_flat_zeroScheme_of_fibre {P S : Scheme.{u}} (f : P ⟶ S) [Flat f]
    [LocallyOfFinitePresentation f] (L : P.Modules)
    [SheafOfModules.IsInvertible P.sheaf.obj P.ringCatSheaf.property L] (g : Γ(L, ⊤)) (z : P)
    (hz : z ∈ (zeroScheme P L g).support) (U : (f.fiber (f z)).Opens) (hzU : f.asFiber z ∈ U)
    [IsIntegral U.toScheme]
    (hg : pullbackGlobalSections (U.ι ≫ f.fiberι (f z)) L g ≠ 0) :
    ∃ V : P.Opens, z ∈ V ∧ Flat (((zeroScheme P L g).comap V.ι).subschemeι ≫ V.ι ≫ f) := by
  have hfib : Stacks.Divisors.IsEffectiveCartierDivisor
      (((zeroScheme P L g).comap (f.fiberι (f z))).comap U.ι) := by
    rw [← Scheme.IdealSheafData.comap_comp]
    exact isEffectiveCartierDivisor_comap_zeroScheme_of_ne_zero _ L g hg
  obtain ⟨V, hzV, -, hV⟩ :=
    Stacks.Divisors.exists_isRelativeEffectiveCartierDivisor_of_ideal_isPrincipal
      f (zeroScheme P L g) z hz (isLocallyPrincipal_zeroScheme P L g z) ⟨U, hzU, hfib⟩
  exact ⟨V, hzV, hV.2⟩

/-- **A flat closed subscheme is smooth where its fibre is.** Let `I` cut out a closed subscheme of
`X` which is flat and locally of finite presentation over `S` through `f`, let `s ∈ S`, and let `y`
be a point of the closed subscheme `I_s` of the fibre `X_s` cut out by the inverse image of `I`.
If `I_s` is smooth of relative dimension `n` over `κ(s)` on an open neighbourhood of `y`, then the
image of `y` in the closed subscheme of `X` is a point of smoothness of it over `S`, and its fibre
there has dimension `n`. -/
theorem mem_smoothLocus_and_fiberDimensionAt_of_fibre {X S : Scheme.{u}} (f : X ⟶ S)
    (I : X.IdealSheafData) [Flat (I.subschemeι ≫ f)]
    [LocallyOfFinitePresentation (I.subschemeι ≫ f)]
    (s : S) (n : ℕ) (y : (I.comap (f.fiberι s)).subscheme)
    (U : (I.comap (f.fiberι s)).subscheme.Opens) (hyU : y ∈ U)
    [SmoothOfRelativeDimension n
      (U.ι ≫ (I.comap (f.fiberι s)).subschemeι ≫ f.fiberToSpecResidueField s)] :
    ((I.comapIso (f.fiberι s)).hom ≫ pullback.snd _ _) y ∈ (I.subschemeι ≫ f).smoothLocus ∧
      topologicalKrullDimAt ((I.subschemeι ≫ f).fiber
          ((I.subschemeι ≫ f) (((I.comapIso (f.fiberι s)).hom ≫ pullback.snd _ _) y)))
        ((I.subschemeι ≫ f).asFiber (((I.comapIso (f.fiberι s)).hom ≫ pullback.snd _ _) y)) =
        (n : WithBot ℕ∞) := by
  have hsq := isPullback_subschemeι_comap_fiberι f I s
  set g := (I.comap (f.fiberι s)).subschemeι ≫ f.fiberToSpecResidueField s
  have : LocallyOfFinitePresentation g := MorphismProperty.of_isPullback hsq inferInstance
  have : LocallyOfFiniteType (I.subschemeι ≫ f) := inferInstance
  have hsm : Smooth (U.ι ≫ g) := SmoothOfRelativeDimension.smooth n _
  have hyg : y ∈ g.smoothLocus := by
    have h : (U.ι ≫ g).smoothLocus = ⊤ := Scheme.Hom.smoothLocus_eq_top_iff.2 hsm
    rw [← Scheme.Hom.preimage_smoothLocus_eq] at h
    have h' : (⟨y, hyU⟩ : U.toScheme) ∈ U.ι ⁻¹ᵁ g.smoothLocus := h ▸ trivial
    exact h'
  refine ⟨?_, ?_⟩
  · have h := Scheme.Hom.smoothLocus_eq_preimage_of_isPullback hsq (Or.inl inferInstance)
    rw [h] at hyg
    exact hyg
  · rw [← topologicalKrullDimAt_fiber_eq_of_isPullback hsq y]
    have h := fiberDimensionAt_eq_of_smoothOfRelativeDimension (U.ι ≫ g) n ⟨y, hyU⟩
    exact (fiberDimensionAt_comp_openImmersion U.ι g ⟨y, hyU⟩).symm.trans h

end AlgebraicGeometry

end
