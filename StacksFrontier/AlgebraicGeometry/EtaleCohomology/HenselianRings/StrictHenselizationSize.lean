module

public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.HenselianRings.StrictHenselization
public import StacksFrontier.AlgebraicGeometry.Size.Cutoff
public import StacksFrontier.RingTheory.Henselian.Henselization.Cardinality
public import Mathlib.RingTheory.Algebraic.Cardinality

/-!
# The strict henselization stays inside a big étale site

Let `B` be a big étale site containing a scheme `S` and let `s` be a geometric point of `S`. The
étale local ring `𝒪^{sh}_{S,s}` has cardinality at most `size S`: it is a strict henselization of
the local ring `𝒪_{S,s}`, whose cardinality is at most `size S`, with residue field a separable
algebraic extension of that of `𝒪_{S,s}`
(`IsLocalRing.IsHenselization.cardinalMk_le_max`). By Stacks 000P and 000R (9) the strict
henselization `Spec 𝒪^{sh}_{S,s}` is therefore an object of the site, and so, by
`AlgebraicGeometry.Scheme.size_pullback_lt`, is the base change `X ×_S Spec 𝒪^{sh}_{S,s}` of any
scheme `X` of the site.

## Main results

* `AlgebraicGeometry.cardinalMk_etaleLocalRing_le_size` — `#𝒪^{sh}_{S,s} ≤ size S`.
* `AlgebraicGeometry.contains_strictHenselization` — `B` contains `Spec 𝒪^{sh}_{S,s}`.

## References

* [Stacks Project, Tag 000P](https://stacks.math.columbia.edu/tag/000P)
* [Stacks Project, Tag 000R](https://stacks.math.columbia.edu/tag/000R)
* [Stacks Project, Tag 03PS](https://stacks.math.columbia.edu/tag/03PS)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits Cardinal IsLocalRing

universe u

namespace AlgebraicGeometry

variable (B : BigEtaleSite.{u}) (S : Scheme.{u}) (hS : B.Contains S) (s : GeometricPoint S)

/-- **The étale local ring is no larger than the scheme.** The cardinality of the étale local ring
of `S` at a geometric point is at most the size of `S`. -/
theorem cardinalMk_etaleLocalRing_le_size : #(etaleLocalRing B S hS s) ≤ S.size := by
  set A := S.presheaf.stalk (s.hom (closedPoint s.residueField))
  set T := geometricHenselizationTower S s
  have hA : #A ≤ S.size := Scheme.mk_stalk_le_size S _
  have hκA : #(ResidueField A) ≤ #A :=
    mk_le_of_surjective (Ideal.Quotient.mk_surjective (I := maximalIdeal A))
  have hsep : #(separableClosure (ResidueField A) s.residueField) ≤ max #(ResidueField A) ℵ₀ :=
    Algebra.IsAlgebraic.cardinalMk_le_max (ResidueField A) _
  have hres : #(ResidueField T.strictHenselization) =
      #(separableClosure (ResidueField A) s.residueField) :=
    (mk_congr T.strictHenselizationResidueEquiv.toEquiv).symm
  have hsh : #T.strictHenselization ≤ max (max #A #(ResidueField T.strictHenselization)) ℵ₀ :=
    IsLocalRing.IsHenselization.cardinalMk_le_max
      (L := separableClosure (ResidueField A) s.residueField)
  have h0 : ℵ₀ ≤ S.size := S.aleph0_le_size
  rw [← mk_congr (etaleLocalRingEquivStrictHenselization B S hS s).toEquiv]
  refine hsh.trans (max_le (max_le hA ?_) h0)
  rw [hres]
  exact hsep.trans (max_le (hκA.trans hA) h0)

/-- **The strict henselization at a geometric point of a scheme of a big étale site is in the
site.** This is Stacks 000R (9) for the étale local ring, whose cardinality is at most the size
of the scheme (`AlgebraicGeometry.cardinalMk_etaleLocalRing_le_size`). -/
theorem contains_strictHenselization : B.Contains (strictHenselization B S hS s) :=
  Scheme.size_Spec_lt_of_mk_le B.aleph0_lt_cutoff B.cutoff_isStrongPrelimit _ hS
    ((cardinalMk_etaleLocalRing_le_size B S hS s).trans (self_le_power _ one_le_aleph0))

end AlgebraicGeometry
