module

public import StacksFrontier.AlgebraicGeometry.SectionExtension.Basic
public import Mathlib.AlgebraicGeometry.Morphisms.QuasiSeparated
public import Mathlib.AlgebraicGeometry.QuasiAffine

/-!
# Stacks Tag 01PW for a globally trivial invertible module

`Stacks.SectionExtension.IsSectionRatio` is the surjectivity half of Stacks Tag 01PW; clause (3)
of Stacks Tag 01Q3 and the ample-pullback cluster reduce to it. This file proves it in the case
where every tensor power of `L` carries a nowhere-vanishing global basis.

In that case the whole statement collapses onto the structure sheaf: `X_s` is a basic open
`X.basicOpen r` (`Stacks.Ample.NonvanishingBasis.exists_basicOpen_eq`), a function on it is a
fraction `y / r^e` by the **Qcqs lemma**
(`AlgebraicGeometry.exists_eq_pow_mul_of_isCompact_of_isQuasiSeparated`), and the numerator and
the denominator are read back as global sections of `L ^⊗ 0` through the basis in degree zero. No
positive power of `L` is involved in the answer, which is why nothing has to be said about how the
powers of `L` multiply.

The hypotheses are exactly Tag 01PW's: `X` quasi-compact and quasi-separated. Both hold for a
quasi-affine scheme, which is the case this covers in substance: by Stacks Tag 01QE
(`Stacks.Ample.isQuasiAffine_iff_isAmple`) a scheme whose structure sheaf is ample is quasi-affine,
and `Stacks.Ample.unitTensorPowBasis` gives the structure sheaf a global basis in every degree.

## Main results

* `Stacks.SectionExtension.isSectionRatio_of_nonvanishingBasis`: **Stacks Tag 01PW, surjectivity,
  for a globally trivial invertible module on a quasi-compact quasi-separated scheme.**
* `Stacks.SectionExtension.isSectionRatio_unitModule`: the same for the structure sheaf, where the
  basis is supplied unconditionally.
* `Stacks.SectionExtension.isSectionRatio_unitModule_of_isQuasiAffine`: the structure sheaf of a
  quasi-affine scheme, where the two hypotheses on `X` are instances.

## Relation to Tag 01PW

What is proved is Stacks Tag 01PW part (2) restricted to a globally trivial `L` and to
`𝓕 = 𝒪_X`, and stated as the ratio predicate rather than as the bijectivity of the comparison map
of the source. That is a strict special case on two counts, so no `@[stacks]` attribute is
attached.

## References

* [Stacks Project, Tag 01PW](https://stacks.math.columbia.edu/tag/01PW)
* [Stacks Project, Tag 01QE](https://stacks.math.columbia.edu/tag/01QE)
* [Stacks Project, Tag 01Q3](https://stacks.math.columbia.edu/tag/01Q3)
-/

@[expose] public section

open AlgebraicGeometry CategoryTheory TopologicalSpace Opposite
open Stacks.Ample Stacks.NonvanishingOpen

universe u

namespace Stacks.SectionExtension

variable (X : Scheme.{u}) (L : X.Modules) [IsInvertibleModule X L]

/-- **Stacks Tag 01PW, the surjectivity half, for a globally trivial invertible module.** If every
tensor power of `L` has a nowhere-vanishing global basis and `X` is quasi-compact and
quasi-separated, then every function on an `X_s` is the ratio of two global sections of one tensor
power of `L` — in fact of `L ^⊗ 0`, the structure sheaf. -/
theorem isSectionRatio_of_nonvanishingBasis
    (hc : IsCompact ((⊤ : X.Opens) : Set X)) (hqs : IsQuasiSeparated ((⊤ : X.Opens) : Set X))
    (b : ∀ n : ℕ, NonvanishingBasis (tensorPowModule X L (n : ℤ))) : IsSectionRatio X L := by
  intro n _ s
  obtain ⟨r, rfl⟩ := (b n).surjective s
  -- The nonvanishing locus of `a • gen` is the basic open of `a`.
  have hopen : ∀ (p : ℕ) (a : Γ(X, ⊤)),
      Stacks.AmpleTheory.powNonvanishingOpen X L p (a • (b p).gen) = X.basicOpen a := fun p a =>
    Opens.ext ((b p).nonvanishingLocus_smul_gen a)
  rw [hopen]
  intro g
  obtain ⟨e, y, he⟩ :=
    AlgebraicGeometry.exists_eq_pow_mul_of_isCompact_of_isQuasiSeparated X ⊤ hc hqs r g
  -- A positive exponent on `r`, so that `X.basicOpen (r ^ (e + 1)) = X.basicOpen r`.
  refine ⟨0, (r * y) • (b 0).gen, r ^ (e + 1) • (b 0).gen, ?_, ?_⟩
  · rw [hopen, X.basicOpen_pow r (Nat.succ_pos e)]
  · have hres : ∀ a : Γ(X, ⊤),
        resTop (X.basicOpen r) (a • (b 0).gen)
          = X.presheaf.map (homOfLE (le_top : X.basicOpen r ≤ ⊤)).op a •
              resTop (X.basicOpen r) (b 0).gen :=
      fun a => Scheme.Modules.map_smul _ _ a (b 0).gen
    dsimp only [TopCat.Presheaf.restrictOpenCommRingCat_apply] at he
    rw [hres, hres, map_mul, map_pow, smul_smul, he]
    congr 1
    ring

/-- **Stacks Tag 01PW, the surjectivity half, for the structure sheaf of a quasi-compact
quasi-separated scheme.** `Stacks.Ample.unitTensorPowBasis` supplies the global basis of every
tensor power of `𝒪_X`, so this is unconditional in `L`. -/
theorem isSectionRatio_unitModule (Y : Scheme.{u})
    (hc : IsCompact ((⊤ : Y.Opens) : Set Y)) (hqs : IsQuasiSeparated ((⊤ : Y.Opens) : Set Y)) :
    IsSectionRatio Y (unitModule Y) :=
  isSectionRatio_of_nonvanishingBasis Y _ hc hqs fun n => unitTensorPowBasis Y (n : ℤ)

/-- **Stacks Tag 01PW, the surjectivity half, for the structure sheaf of a quasi-affine scheme.**
A quasi-affine scheme is quasi-compact by definition and separated — hence quasi-separated — by
`AlgebraicGeometry.Scheme.IsQuasiAffine`'s instances, so both hypotheses are discharged by
instance search. By Stacks Tag 01QE this is the case in which `𝒪_X` is ample. -/
theorem isSectionRatio_unitModule_of_isQuasiAffine (Y : Scheme.{u}) [Y.IsQuasiAffine] :
    IsSectionRatio Y (unitModule Y) := by
  have hqs : QuasiSeparatedSpace Y := Y.toSpecΓ.isOpenEmbedding.quasiSeparatedSpace
  refine isSectionRatio_unitModule Y ?_ ?_
  · simpa using isCompact_univ (X := Y)
  · simpa using isQuasiSeparated_univ (α := Y)

end Stacks.SectionExtension

end
