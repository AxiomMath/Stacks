module

public import Mathlib.RingTheory.AdicCompletion.Basic
public import StacksFrontier.AlgebraicGeometry.Topologies.Fppf
public import StacksFrontier.AlgebraicGeometry.Variety.CompleteLocal.Stalk

/-!
# The completed local ring of a scheme in a big fppf site

The objects of a big fppf site are the schemes below a cardinal cutoff `κ` which is a strong
prelimit, so the cutoff is closed under the cardinal operations that scheme constructions
perform. This file records the two instances the deformation theory of
[Stacks, Tag 07YM] needs: the spectrum of the local ring of a Noetherian scheme in the site is
in the site, and so is the spectrum of its completion.

Both are size bounds and nothing more. The local ring is handled by
`AlgebraicGeometry.Scheme.size_lt_of_mono_quasiCompact`, the canonical morphism out of
`Spec 𝒪_{X,x}` being a quasi-compact monomorphism when `X` is Noetherian; the completion is a
quotient of a subset of `ℕ → 𝒪_{X,x}`, whose cardinality is below `2 ^ max ℵ₀ #𝒪_{X,x}` and
therefore below the cutoff.

## Main results

* `AlgebraicGeometry.BigFppfSite.contains_spec_stalk_of_contains` — the spectrum of a local ring
  of any scheme in the site is in the site.
* `AlgebraicGeometry.BigFppfSite.contains_spec_stalk` — the spectrum of a local ring of a
  Noetherian scheme in the site is in the site.
* `AlgebraicGeometry.BigFppfSite.contains_spec_completedLocalRing` — so is the spectrum of the
  completed local ring.

## Implementation notes

`AlgebraicGeometry.Scheme.completedLocalRing` is by definition the adic completion of the
stalk at its maximal ideal, so the bound is a statement about `AdicCompletion` and is proved
for an arbitrary ideal. Nothing about the ideal or about Noetherianity enters the cardinal
bound: the completion is the image of the Cauchy sequences, which form a subtype of `ℕ → R`.

## References

* [Stacks Project, Tag 021R](https://stacks.math.columbia.edu/tag/021R)
* [Stacks Project, Tag 07YM](https://stacks.math.columbia.edu/tag/07YM)
-/

@[expose] public noncomputable section

open CategoryTheory Cardinal

universe u

namespace AlgebraicGeometry

/-- An adic completion has at most as many elements as the ring's sequences. -/
public theorem cardinal_mk_adicCompletion_le {R : Type u} [CommRing R] (I : Ideal R) :
    Cardinal.mk (AdicCompletion I R) ≤ Cardinal.mk R ^ Cardinal.aleph0 := by
  calc
    Cardinal.mk (AdicCompletion I R) ≤ Cardinal.mk (AdicCompletion.AdicCauchySequence I R) :=
      Cardinal.mk_le_of_surjective (AdicCompletion.mk_surjective I R)
    _ ≤ Cardinal.mk (ℕ → R) := Cardinal.mk_le_of_injective Subtype.val_injective
    _ = Cardinal.mk R ^ Cardinal.aleph0 := by simp

/-- The sequences of a ring are no more numerous than the subsets of `max ℵ₀ #R`. -/
public theorem cardinal_power_aleph0_le_two_pow (R : Type u) :
    Cardinal.mk R ^ Cardinal.aleph0 ≤ 2 ^ max Cardinal.aleph0 (Cardinal.mk R) := by
  calc
    Cardinal.mk R ^ Cardinal.aleph0
        ≤ (2 ^ max Cardinal.aleph0 (Cardinal.mk R)) ^ Cardinal.aleph0 :=
      Cardinal.power_le_power_right
        ((Cardinal.cantor _).le.trans
          (Cardinal.power_le_power_left two_ne_zero (le_max_right _ _)))
    _ = 2 ^ (max Cardinal.aleph0 (Cardinal.mk R) * Cardinal.aleph0) := Cardinal.power_mul.symm
    _ = 2 ^ max Cardinal.aleph0 (Cardinal.mk R) := by
      refine congrArg (fun c => (2 : Cardinal.{u}) ^ c) ?_
      exact Cardinal.mul_eq_left (le_max_left _ _) (le_max_left _ _)
        (by simpa using (Cardinal.aleph0_pos).ne')

namespace BigFppfSite

variable (B : BigFppfSite.{u})

/-- The spectrum of a ring is in the site iff `max ℵ₀ #R` is below the cutoff. -/
private theorem contains_spec_iff {R : Type u} [CommRing R] :
    B.Contains (Spec (.of R)) ↔ max Cardinal.aleph0 (Cardinal.mk R) < B.cutoff := by
  change (Spec (.of R)).size < B.cutoff ↔ _
  rw [Scheme.size_Spec]

/-- **The spectrum of a local ring of a scheme in the site is in the site**, with no Noetherian
hypothesis. The stalk of `X` at a point has cardinality at most the size of `X`, which is below
the cutoff because `X` belongs to the site, and the size of an affine scheme is the cardinality
of its ring together with `ℵ₀`. -/
public theorem contains_spec_stalk_of_contains {X : Scheme.{u}} (hX : B.Contains X) (x : X) :
    B.Contains (Spec (.of (X.presheaf.stalk x))) := by
  rw [contains_spec_iff]
  exact max_lt B.aleph0_lt_cutoff (lt_of_le_of_lt (Scheme.mk_stalk_le_size X x) hX)

/-- **The spectrum of a local ring of a Noetherian scheme in the site is in the site.** The
canonical morphism out of `Spec 𝒪_{X,x}` is a monomorphism, and it is quasi-compact because
every open of a Noetherian scheme is. -/
public theorem contains_spec_stalk {X : Scheme.{u}} (hX : B.Contains X) [IsNoetherian X]
    (x : X) : B.Contains (Spec (.of (X.presheaf.stalk x))) := by
  have : QuasiCompact (X.fromSpecStalk x) := by
    rw [quasiCompact_iff_forall_isAffineOpen]
    intro U _
    exact TopologicalSpace.NoetherianSpace.isCompact _
  exact Scheme.size_lt_of_mono_quasiCompact (X.fromSpecStalk x) hX

/-- **The spectrum of the completed local ring of a Noetherian scheme in the site is in the
site.** The completion is the image of a set of sequences in the stalk, so its cardinality is
at most `2 ^ max ℵ₀ #𝒪_{X,x}`, which is below the cutoff because the cutoff is a strong
prelimit. -/
public theorem contains_spec_completedLocalRing {X : Scheme.{u}} (hX : B.Contains X)
    [IsNoetherian X] (x : X) :
    B.Contains (Spec (.of (AlgebraicGeometry.Scheme.completedLocalRing X x))) := by
  have hsize := (contains_spec_iff B).1 (B.contains_spec_stalk hX x)
  rw [contains_spec_iff]
  refine max_lt B.aleph0_lt_cutoff (lt_of_le_of_lt ?_ (B.cutoff_isStrongPrelimit hsize))
  exact (cardinal_mk_adicCompletion_le _).trans
    (cardinal_power_aleph0_le_two_pow (X.presheaf.stalk x))

end BigFppfSite

end AlgebraicGeometry

end
