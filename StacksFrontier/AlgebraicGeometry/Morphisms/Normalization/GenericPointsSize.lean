module

public import StacksFrontier.AlgebraicGeometry.Morphisms.Normalization.Scheme
public import StacksFrontier.AlgebraicGeometry.Morphisms.Normalization.Size
public import StacksFrontier.AlgebraicGeometry.Size.OpenCover

/-!
# The size of the normalization of a scheme

The *size* of a scheme (`AlgebraicGeometry.Scheme.size`, Stacks Section 000H) is the maximum of `ℵ₀`, the
number of its affine opens, and the cardinalities of its rings of sections over affine opens,
and containment in a big fppf site is exactly a bound on it. For the *relative* normalization
of a quasi-compact quasi-separated morphism the bound is
`AlgebraicGeometry.Scheme.Hom.size_normalization_le`, and that is what makes a big site contain
the relative normalization of a morphism of its objects.

The *absolute* normalization `X^ν` of Tag 035N is the relative normalization of the canonical
morphism `X^0 ⟶ X` from the spectra of the residue fields at the generic points of `X`, so the
relative bound reduces its size to that of `X^0`, and this file supplies

`size (genericPointResidueSpectrum X) ≤ size X` and hence `size (X.normalizationScheme hX) ≤
size X`.

Without this the containment of a normalization in a big fppf site has to be *assumed*, as it
is in `AlgebraicGeometry.Space.NormalizationData.ofRepresentable`.

## Main results

* `AlgebraicGeometry.Scheme.mk_genericPoints_le_size`: a scheme whose quasi-compact opens have
  finitely many irreducible components has at most `size X` generic points.
* `AlgebraicGeometry.Scheme.size_genericPointResidueSpectrum_le`: the spectra of the residue
  fields at the generic points have size at most `size X`.
* `AlgebraicGeometry.Scheme.size_normalizationScheme_le`: the normalization of `X` has size at
  most `size X`.

## Implementation notes

The generic points are counted by choosing, for each of them, an affine open containing it: the
affine opens number at most `size X`, and only finitely many generic points lie in each of them
because an affine open is quasi-compact. That finiteness is `AlgebraicGeometry.genericPoints`
of the open being finite, transported along
`AlgebraicGeometry.Scheme.genericPointsInOpenEquiv`.

The cardinality of a residue field is bounded by that of the stalk, which is
`AlgebraicGeometry.Scheme.mk_stalk_le_size`; the same two steps are
`AlgebraicGeometry.Scheme.lambdaCard_le_size`, which cannot be cited here because it lives above
the algebraic spaces and this file is imported by them.

No tag is carried. Tag 000R lists the constructions under which a size bound is preserved and
the normalization is not among them; the clause for the relative normalization is supplied by
`StacksFrontier.AlgebraicGeometry.Morphisms.Normalization.Size`, and what is added here is the
bound for the scheme `X^0` of Tag 035M, which is a coproduct and so is clause (8) of Tag 000R
read at a family of spectra of residue fields.

## References

* [Stacks Project, Section 000H](https://stacks.math.columbia.edu/tag/000H)
* [Stacks Project, Tag 000R](https://stacks.math.columbia.edu/tag/000R)
* [Stacks Project, Tag 035M](https://stacks.math.columbia.edu/tag/035M)
* [Stacks Project, Tag 035N](https://stacks.math.columbia.edu/tag/035N)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits TopologicalSpace Cardinal

universe u

namespace AlgebraicGeometry.Scheme

/-- **A scheme with locally finitely many irreducible components has at most `size X` generic
points.** Each generic point lies in an affine open, the affine opens number at most `size X`,
and an affine open is quasi-compact so only finitely many generic points lie in it. -/
theorem mk_genericPoints_le_size (X : Scheme.{u})
    (hX : ∀ U : X.Opens, IsCompact (U : Set X) → (irreducibleComponents U).Finite) :
    #(genericPoints X) ≤ X.size := by
  classical
  have hcov : ∀ η : genericPoints X, ∃ V : X.affineOpens, η.1 ∈ V.1 := by
    intro η
    obtain ⟨V, hVaff, hyV, -⟩ :=
      (Opens.isBasis_iff_nbhd.mp (Scheme.isBasis_affineOpens X))
        (show η.1 ∈ (⊤ : X.Opens) from trivial)
    exact ⟨⟨V, hVaff⟩, hyV⟩
  have hinj : Function.Injective
      (fun η : genericPoints X => (⟨(hcov η).choose, ⟨η, (hcov η).choose_spec⟩⟩ :
        (V : X.affineOpens) × {η : genericPoints X // η.1 ∈ V.1})) := by
    intro a b hab
    simpa using congrArg (fun p => p.2.1) hab
  refine (Cardinal.mk_le_of_injective hinj).trans ?_
  rw [Cardinal.mk_sigma]
  refine (Cardinal.sum_le_sum _ (fun _ => ℵ₀) ?_).trans ?_
  · intro V
    have _ : Finite (genericPoints (V.1 : Set X)) :=
      (genericPoints.finite (hX V.1 V.2.isCompact)).to_subtype
    have _ : Finite {η : genericPoints X // η.1 ∈ V.1} :=
      Finite.of_injective (Scheme.genericPointsInOpenEquiv X V.1)
        (Scheme.genericPointsInOpenEquiv X V.1).injective
    exact Cardinal.mk_le_aleph0
  · rw [Cardinal.sum_const']
    exact Cardinal.mul_le_of_le X.aleph0_le_size X.mk_affineOpens_le_size X.aleph0_le_size

/-- **The scheme of generic-point residue fields has size at most that of `X`.** It is a
coproduct indexed by the generic points, which number at most `size X`, of spectra of residue
fields, which are quotients of stalks and so have cardinality at most `size X`. -/
theorem size_genericPointResidueSpectrum_le (X : Scheme.{u})
    (hX : ∀ U : X.Opens, IsCompact (U : Set X) → (irreducibleComponents U).Finite) :
    (genericPointResidueSpectrum X).size ≤ X.size := by
  refine schemeSize_coproduct_le _ X.size X.aleph0_le_size
    (X.mk_genericPoints_le_size hX) fun η => ?_
  rw [Scheme.size_of_isAffine]
  refine max_le X.aleph0_le_size ?_
  refine le_trans (le_of_eq (Cardinal.mk_congr
    (Scheme.ΓSpecIso (.of (X.residueField η.1))).commRingCatIsoToRingEquiv.toEquiv)) ?_
  exact (Cardinal.mk_le_of_surjective (X.residue_surjective η.1)).trans
    (X.mk_stalk_le_size η.1)

/-- **The normalization of a scheme has size at most that of the scheme.** The normalization is
the relative normalization of the quasi-compact quasi-separated morphism `X^0 ⟶ X`, so
`AlgebraicGeometry.Scheme.Hom.size_normalization_le` bounds it by the maximum of the sizes of
`X^0` and of `X`, and the first of those is at most the second. -/
theorem size_normalizationScheme_le (X : Scheme.{u})
    (hX : ∀ U : X.Opens, IsCompact (U : Set X) → (irreducibleComponents U).Finite) :
    (X.normalizationScheme hX).size ≤ X.size := by
  have _ := quasiCompactFromGenericPointResidueFields X hX
  have _ := quasiSeparatedFromGenericPointResidueFields X
  exact (Scheme.Hom.size_normalization_le (fromGenericPointResidueFields X)).trans
    (max_le (X.size_genericPointResidueSpectrum_le hX) le_rfl)

end AlgebraicGeometry.Scheme

end
