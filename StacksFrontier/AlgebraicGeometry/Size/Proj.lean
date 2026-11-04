module

public import Mathlib.AlgebraicGeometry.ProjectiveSpectrum.Basic
public import StacksFrontier.AlgebraicGeometry.Size.Affine
public import StacksFrontier.AlgebraicGeometry.Size.Cutoff
public import StacksFrontier.AlgebraicGeometry.Size.OpenCover
public import StacksFrontier.AlgebraicGeometry.Topologies.Fppf

/-!
# The size of `Proj` of a graded ring

The projective spectrum of a graded ring `𝒜` on a ring `A` has size at most `max ℵ₀ #A`: one
cardinal, the cardinality of the ring, bounds it. Consequently `Proj 𝒜` is an object of a big
fppf site as soon as `#A` is below the site's cutoff — and that containment needs no
set-theoretic property of the cutoff beyond `ℵ₀ < B.cutoff`: not `Cardinal.IsStrongPrelimit`,
not uncountable cofinality, and certainly not regularity.

The estimate has three steps.

* *Each piece.* The standard affine charts of `AlgebraicGeometry.Proj.affineOpenCover` are the
  spectra of the degree-zero localizations `A_(f)` at the homogeneous elements `f` of positive
  degree. Such a localization is a *subring* of the ordinary localization `A_f` — that is
  `HomogeneousLocalization.val_injective` — so it has at most `max ℵ₀ #A` elements by
  `Cardinal.mk_localization_powers_le`, and Stacks 000P turns that into the same bound on the
  size of its spectrum.
* *The index set.* The charts are indexed by `Σ i : ℕ+, 𝒜 i`, a countable union of subsets of
  `A`, so there are at most `max ℵ₀ #A` of them.
* *The total.* Stacks 000Q (`AlgebraicGeometry.Scheme.size_le_of_iSup_eq_top`) assembles the
  two into the bound on `Proj 𝒜`.

## Main results

* `Cardinal.mk_homogeneousLocalizationAway_le`: `#(Away 𝒜 f) ≤ max ℵ₀ #A`.
* `AlgebraicGeometry.Scheme.size_Proj_le`: `(Proj 𝒜).size ≤ max ℵ₀ #A`.
* `AlgebraicGeometry.BigFppfSite.contains_Proj`: `Proj 𝒜` is a scheme of the site when `#A` is
  below the cutoff.

## Implementation notes

The bound is by the cardinality of the *whole* graded ring and not by any function of its
individual homogeneous pieces, which is what makes it usable against a cutoff that need not be
regular: there is a single bounding cardinal here rather than one per chart, so the assembly
step needs no supremum over an index set of uncontrolled cofinality. Turning degreewise bounds
on the pieces into a bound on the whole ring is a separate step and does cost a power; it is
not done here.

## References

* [Stacks Project, Tag 000P](https://stacks.math.columbia.edu/tag/000P)
* [Stacks Project, Tag 000Q](https://stacks.math.columbia.edu/tag/000Q)
* [Stacks Project, Tag 000R](https://stacks.math.columbia.edu/tag/000R)
-/

@[expose] public section

open AlgebraicGeometry Cardinal CategoryTheory HomogeneousLocalization

universe u

variable {σ : Type*} {A : Type u} [CommRing A] [SetLike σ A] [AddSubgroupClass σ A]
  (𝒜 : ℕ → σ) [GradedRing 𝒜]

namespace Cardinal

omit [AddSubgroupClass σ A] [GradedRing 𝒜] in
/-- **A degree-zero localization of a graded ring is no larger than the ring, up to `ℵ₀`.**
`HomogeneousLocalization.Away 𝒜 f` embeds in the ordinary localization of `A` at the powers of
`f` by `HomogeneousLocalization.val_injective`, and a localization at the powers of one element
has at most `max ℵ₀ #A` elements. -/
theorem mk_homogeneousLocalizationAway_le (f : A) :
    #(HomogeneousLocalization.Away 𝒜 f) ≤ max ℵ₀ #A :=
  (mk_le_of_injective
      (HomogeneousLocalization.val_injective (𝒜 := 𝒜) (x := Submonoid.powers f))).trans
    (Cardinal.mk_localization_powers_le f)

omit [CommRing A] [AddSubgroupClass σ A] [GradedRing 𝒜] in
/-- **There are at most `max ℵ₀ #A` homogeneous elements of positive degree.** They are indexed
by a countable union of subsets of `A`. This is the index set of
`AlgebraicGeometry.Proj.affineOpenCover`. -/
theorem mk_sigma_pnat_graded_le : #(Σ i : ℕ+, 𝒜 i) ≤ max ℵ₀ #A := by
  have e : (Σ i : ULift.{u} ℕ+, (𝒜 (i.down : ℕ) : Type u)) ≃ Σ i : ℕ+, (𝒜 (i : ℕ) : Type u) :=
    Equiv.sigmaCongrLeft (β := fun i : ℕ+ => (𝒜 (i : ℕ) : Type u)) Equiv.ulift
  rw [← mk_congr e]
  calc #(Σ i : ULift.{u} ℕ+, (𝒜 (i.down : ℕ) : Type u))
      = Cardinal.sum (fun i : ULift.{u} ℕ+ => #(𝒜 (i.down : ℕ))) := mk_sigma _
    _ ≤ #(ULift.{u} ℕ+) * ⨆ i : ULift.{u} ℕ+, #(𝒜 (i.down : ℕ)) := sum_le_mk_mul_iSup _
    _ ≤ max ℵ₀ #A * max ℵ₀ #A :=
        mul_le_mul (mk_le_aleph0.trans (le_max_left _ _))
          (ciSup_le' fun _ => (mk_le_of_injective Subtype.val_injective).trans
            (le_max_right _ _)) (by positivity) (by positivity)
    _ = max ℵ₀ #A := mul_eq_self (le_max_left _ _)

end Cardinal

namespace AlgebraicGeometry

/-- **The projective spectrum of a graded ring has size at most the cardinality of the ring.**
No hypothesis is placed on the grading; in particular the homogeneous pieces need not be
finitely generated and the ring need not be Noetherian.

The standard affine charts of `AlgebraicGeometry.Proj.affineOpenCover` cover `Proj 𝒜`, there
are at most `max ℵ₀ #A` of them (`Cardinal.mk_sigma_pnat_graded_le`) and each is the spectrum
of a degree-zero localization, which has at most `max ℵ₀ #A` elements
(`Cardinal.mk_homogeneousLocalizationAway_le`), so Stacks 000Q gives the bound. -/
theorem Scheme.size_Proj_le : (Proj 𝒜).size ≤ max ℵ₀ #A := by
  have : Nonempty (Proj.affineOpenCover 𝒜).openCover.I₀ :=
    ⟨⟨1, (0 : A), zero_mem _⟩⟩
  refine (Scheme.size_le_of_iSup_eq_top
    (fun i => ((Proj.affineOpenCover 𝒜).openCover.f i).opensRange)
    (Proj.affineOpenCover 𝒜).openCover.iSup_opensRange).trans
    (max_le (Cardinal.mk_sigma_pnat_graded_le 𝒜) (ciSup_le' fun i => ?_))
  rw [← Scheme.size_congr ((Proj.affineOpenCover 𝒜).openCover.f i).isoOpensRange]
  change (Spec (CommRingCat.of (HomogeneousLocalization.Away 𝒜 (i.2 : A)))).size ≤ max ℵ₀ #A
  rw [Scheme.size_Spec]
  exact max_le (le_max_left _ _) (Cardinal.mk_homogeneousLocalizationAway_le 𝒜 _)

/-- **The projective spectrum of a graded ring whose cardinality is below the cutoff is a
scheme of the site.** `AlgebraicGeometry.Scheme.size_Proj_le` bounds the size by `max ℵ₀ #A`,
and both `ℵ₀` and `#A` are below the cutoff.

Only `AlgebraicGeometry.BigFppfSite.aleph0_lt_cutoff` is used; neither the strong prelimit
property nor the uncountable cofinality of the cutoff is needed, because the bound is a single
cardinal rather than a supremum or a power. -/
theorem BigFppfSite.contains_Proj (B : BigFppfSite.{u}) (hA : #A < B.cutoff) :
    B.Contains (Proj 𝒜) :=
  (Scheme.size_Proj_le 𝒜).trans_lt (max_lt B.aleph0_lt_cutoff hA)

end AlgebraicGeometry

end
