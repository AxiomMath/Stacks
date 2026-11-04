module

public import StacksCore.Tactic.StacksAttribute
public import StacksFrontier.AlgebraicGeometry.Size.FiniteType
public import StacksFrontier.AlgebraicGeometry.Spaces.Groupoids.GroupSpaces.BaseChange
public import StacksFrontier.AlgebraicGeometry.Stacks.Sheaves.FiniteFreeAlgebra.Spectrum
public import StacksFrontier.AlgebraicGeometry.Stacks.Sheaves.FiniteFreeAlgebra.UniversalCover

/-!
# Site membership of the scheme of structure constants

The affine scheme `X` of free `d`-dimensional algebra structures of **Stacks 05YM**
(`AlgebraicGeometry.FiniteFreeAlgebra.scheme`) carries a tautological structure,
`AlgebraicGeometry.FiniteFreeAlgebra.universalStructure` of
`StacksFrontier.AlgebraicGeometry.Stacks.Sheaves.FiniteFreeAlgebra.UniversalCover`, which every
point of `X` pulls back to its own structure.

Both `X` and the spectrum of the algebra of a free `d`-dimensional structure over an affine base
lie in every big fppf site, by **Stacks 000R (9)(b)**: the universal ring is a finite-type
`ℤ`-algebra, being a quotient of a polynomial ring on the finitely many structure constants, and
the algebra of a structure is module-finite over its base.

These are the facts the presentation clause of **Stacks 026O** for the category `ℋ_d` of
degree-`d` finite locally free covers needs in order to be *stated* with `X` as the atlas: an
atlas must be an object of the site, and so must the cover over it.

## Main results

* `AlgebraicGeometry.FiniteFreeAlgebra.contains_scheme`: the scheme of structure constants lies
  in every big fppf site.
* `AlgebraicGeometry.FiniteFreeAlgebra.contains_specCover`: the spectrum of the algebra of a free
  `d`-dimensional structure lies in every big fppf site containing the spectrum of its base ring.

## Implementation notes

No `@[stacks 000R]` attribute is attached to either size estimate. Clause (9)(b) of that tag is
`AlgebraicGeometry.Scheme.size_Spec_lt_of_finiteType`, where it is registered; the two results
below are that clause *applied* at a particular ring, in the same way as
`AlgebraicGeometry.Space.contains_generalLinearScheme`, which is likewise untagged.

The two size estimates are the cardinality form of Stacks 000R (9), through
`AlgebraicGeometry.Scheme.size_Spec_lt_of_mk_le_max`: the universal ring is bounded by
`Cardinal.mk_le_of_algebra_finiteType` over `ℤ` — whose spectrum is in the site by
`AlgebraicGeometry.Space.contains_specULiftZ` — and the algebra of a structure by the same lemma
over its base ring, the structure's basis making it module-finite and hence of finite type.

## References

* [Stacks Project, Tag 000R](https://stacks.math.columbia.edu/tag/000R)
* [Stacks Project, Tag 026O](https://stacks.math.columbia.edu/tag/026O)
* [Stacks Project, Tag 05YM](https://stacks.math.columbia.edu/tag/05YM)
-/

@[expose] public section

open CategoryTheory

universe u

namespace AlgebraicGeometry.FiniteFreeAlgebra

variable (d : ℕ) [NeZero d]

/-! ### Membership in a big fppf site -/

variable (𝒞 : BigFppfSite.{u})

/-- The universal ring, lifted to universe `u`, has cardinality at most `max ℵ₀ #(ULift ℤ)`. -/
private theorem mk_universalRing_le_max :
    Cardinal.mk (ULift.{u} (universalRing d)) ≤ max Cardinal.aleph0 (Cardinal.mk (ULift.{u} ℤ)) :=
  le_trans (by
      rw [Cardinal.mk_uLift]
      exact Cardinal.lift_le_aleph0.2
        ((Cardinal.mk_le_of_algebra_finiteType ℤ (universalRing d)).trans (by simp)))
    (le_max_left _ _)

/-- **Stacks 000R (9)(b).** The scheme of structure constants of free `d`-dimensional algebras
belongs to every big fppf site: its coordinate ring is a quotient of a polynomial ring on the
finitely many structure constants over the integers, hence a finite-type `ℤ`-algebra. -/
theorem contains_scheme : 𝒞.Contains (scheme.{u} d) :=
  Scheme.size_Spec_lt_of_mk_le_max 𝒞.aleph0_lt_cutoff 𝒞.cutoff_isStrongPrelimit
    (AlgebraicGeometry.Space.contains_specULiftZ 𝒞)
    (mk_universalRing_le_max d)

variable {d}

/-- **Stacks 000R (9)(b).** The spectrum of the algebra of a free `d`-dimensional structure over
a ring belongs to every big fppf site containing the spectrum of that ring: the algebra is free
of rank `d` over the ring, hence module-finite, hence of finite type. -/
theorem contains_specCover {R : Type u} [CommRing R] (m : FiniteFreeAlgebra R d)
    (hR : 𝒞.Contains (Spec (.of R))) : 𝒞.Contains (specCover m).left :=
  Scheme.size_Spec_lt_of_mk_le_max 𝒞.aleph0_lt_cutoff 𝒞.cutoff_isStrongPrelimit hR
    (Cardinal.mk_le_of_algebra_finiteType R (Carrier m))

/-- The spectrum of the algebra of the universal structure belongs to every big fppf site. This
is the universal degree-`d` cover: it is finite locally free of degree `d` over the spectrum of
the global sections of the scheme of structure constants by
`AlgebraicGeometry.FiniteFreeAlgebra.isFiniteLocallyFreeOfRank_specCover`. -/
theorem contains_specCover_universalStructure :
    𝒞.Contains (specCover (universalStructure.{u} d)).left :=
  contains_specCover 𝒞 (universalStructure.{u} d)
    (Scheme.size_Spec_lt_of_mk_le_max 𝒞.aleph0_lt_cutoff 𝒞.cutoff_isStrongPrelimit
      (AlgebraicGeometry.Space.contains_specULiftZ 𝒞)
      (le_trans (le_of_eq (Cardinal.mk_congr
          (Scheme.ΓSpecIso (.of (ULift.{u} (universalRing d)))).commRingCatIsoToRingEquiv.toEquiv))
        (mk_universalRing_le_max d)))

end AlgebraicGeometry.FiniteFreeAlgebra

end
