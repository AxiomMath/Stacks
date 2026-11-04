module

public import Mathlib.AlgebraicGeometry.QuasiAffine

/-!
# An affine open around a finite set, by prime avoidance

Stacks Tag 01ZY asserts that a finite set of points of a scheme `X` lies in a single affine open
under any of four hypotheses, and Stacks Tags 0F20 and 09NV refine the conclusion to an affine
*nonvanishing locus* of a global section of an invertible module. All of them rest on one
elementary construction, which this file isolates: if `X` carries an open immersion
`j : X ⟶ Spec R` then a finite `E ⊆ W` is contained in `j ⁻¹ᵁ D(g)` for a single `g : R`, with
that open affine and contained in `W`.

The construction is prime avoidance. Each `x ∈ E` has a basic open `D(r x) ⊆ j ''ᵁ W` around
`j x`, because the basic opens are a basis of `Spec R`; the ideal `I = (r x : x ∈ E)` is then
contained in none of the finitely many primes `j x`, so it has an element `g` outside all of
them. Membership of `E` in `D(g)` is exactly that avoidance, `D(g) ⊆ D(I) ⊆ j ''ᵁ W` gives the
containment in `W`, and `D(g) ⊆ j ''ᵁ W` lies inside the range of `j`, so `j` carries
`j ⁻¹ᵁ D(g)` isomorphically onto the affine `D(g)`.

## Main results

* `Stacks.AmpleCluster.exists_affine_preimage_basicOpen_of_finite`: the construction above.
* `Stacks.AmpleCluster.exists_affine_basicOpen_of_finite_of_isQuasiAffine`: its specialisation to
  `j = X.toSpecΓ` on a quasi-affine scheme, where `j ⁻¹ᵁ D(g)` is literally `X.basicOpen g` for a
  global section `g` of the structure sheaf.

## Implementation notes

Mathlib's prime avoidance is `Ideal.subset_union_prime`, whose index set is a `Finset`; the
`Finset` here is `Finset.univ` on the subtype `↥E`, whose `Fintype` instance comes from
`Set.Finite.fintype`. Its two distinguished indices `a b` are only there to let the statement
cover index sets of size at most two, so any element of `↥E` serves; a nonempty `E` is needed to
produce one, and the empty case is discharged separately by `g = 0`, for which `D(0) = ⊥`.

Three spelling hazards were met, all about the two descriptions of the points of `Spec R`.

**1. `Ideal.subset_union_prime` must be applied, not rewritten with.** For `p : ↥(Spec R)` the
projection `p.asIdeal` elaborates, but when the family `f : ι → Ideal R` of the lemma is left to
be solved by a `rw`, the assignment `f := fun x => (j x).asIdeal` is rejected: at `implicit`
transparency `↥(Spec R)` and `PrimeSpectrum ↑R` are different types. Naming the family in a
preceding `set` and passing it as `(f := P)` removes the unification problem.

**2. The coercion of a basic open has two candidate ambient types.** Writing
`(PrimeSpectrum.basicOpen g : Set ↥(Spec R))` is a type error, since the open set lives in
`Opens (PrimeSpectrum ↑R)`. The containment of the basic open in the range of `j` is therefore
stated as an inequality of `Opens` against `Scheme.Hom.opensRange`, which never names either
`Set` type; `Scheme.Hom.image_le_opensRange` supplies it.

**3. `↑(j ''ᵁ W)` is not syntactically `j '' ↑W`.** `Scheme.Hom.coe_image` is the bridge, and is
needed before any `Set.image_preimage_eq_of_subset`.

## References

* [Stacks Project, Tag 01ZY](https://stacks.math.columbia.edu/tag/01ZY)
* [Stacks Project, Tag 0F20](https://stacks.math.columbia.edu/tag/0F20)

## What is not done

The graded analogue is not proved here. Stacks Tag 01ZY's own argument reduces its four cases to
a locally closed subscheme of `Proj S` and runs this same avoidance in the graded ring, which
needs a homogeneous element of a graded ideal avoiding finitely many primes (Stacks, Algebra,
Lemma 10.57.6). Mathlib has no such lemma at the pin:
`Mathlib/RingTheory/GradedAlgebra/Radical.lean` has only `Ideal.IsHomogeneous.isPrime_iff` and
the homogeneous-radical theory. The repository proves it separately, as
`Stacks.GradedAvoidance.exists_homogeneous_pos_forall_notMem`
(`../GradedSections/Avoidance.lean`), and that — not anything in this file — is what serves the
`Proj` case of Tag 01ZY, which is proved as
`Stacks.AmpleCluster.exists_affineOpen_containing_finite_of_immersion_proj`
(`ProjImmersion.lean`). The ample case, part (3), is proved too, as
`Stacks.AmpleAffineAvoidance.exists_affineOpen_containing_finite_of_ample`
(`../AmpleAffineAvoidance/AmpleFiniteSet.lean`), and it does not route through `Proj` at all: it
goes through part (1), for which this file's avoidance *is* the input.
-/

@[expose] public section

open AlgebraicGeometry CategoryTheory TopologicalSpace

universe u

namespace Stacks.AmpleCluster

/-- **A finite set in an open of a scheme with an open immersion into an affine scheme lies in an
affine basic open inside that open.** Given `j : X ⟶ Spec R` an open immersion and a finite
`E ⊆ W` with `W` open, there is `g : R` with `E ⊆ j ⁻¹ᵁ D(g) ⊆ W` and `j ⁻¹ᵁ D(g)` affine. This
is the prime-avoidance core of Stacks Tag 01ZY. -/
theorem exists_affine_preimage_basicOpen_of_finite {X : Scheme.{u}} {R : CommRingCat.{u}}
    (j : X ⟶ Spec R) [IsOpenImmersion j] {E : Set X} (hE : E.Finite)
    (W : X.Opens) (hEW : E ⊆ (W : Set X)) :
    ∃ g : R, IsAffineOpen (j ⁻¹ᵁ PrimeSpectrum.basicOpen g) ∧
      E ⊆ (j ⁻¹ᵁ PrimeSpectrum.basicOpen g : Set X) ∧
      j ⁻¹ᵁ PrimeSpectrum.basicOpen g ≤ W := by
  rcases Set.eq_empty_or_nonempty E with rfl | hne
  · have hb : j ⁻¹ᵁ PrimeSpectrum.basicOpen (0 : R) = ⊥ :=
      Opens.ext (Set.eq_empty_iff_forall_notMem.mpr fun y hy =>
        (PrimeSpectrum.mem_basicOpen _ _).mp hy (Ideal.zero_mem _))
    exact ⟨0, hb ▸ isAffineOpen_bot X, Set.empty_subset _, hb ▸ bot_le⟩
  have key : ∀ x : E, ∃ r : R, j x.1 ∈ PrimeSpectrum.basicOpen r ∧
      PrimeSpectrum.basicOpen r ≤ j ''ᵁ W := by
    intro x
    obtain ⟨V, ⟨r, rfl⟩, hxV, hVle⟩ := Opens.isBasis_iff_nbhd.mp
      (PrimeSpectrum.isBasis_basic_opens (R := R))
      (show j x.1 ∈ j ''ᵁ W from Set.mem_image_of_mem _ (hEW x.2))
    exact ⟨r, hxV, hVle⟩
  choose r hr1 hr2 using key
  have : Fintype E := hE.fintype
  set P : E → Ideal R := fun x => (j x.1).asIdeal with hP
  have hgen : ∀ x : E, r x ∈ Ideal.span (Set.range r) := fun x => Ideal.subset_span ⟨x, rfl⟩
  have hr1' : ∀ x : E, r x ∉ P x := fun x => (PrimeSpectrum.mem_basicOpen _ _).mp (hr1 x)
  obtain ⟨x₀, hx₀⟩ := hne
  have H := Ideal.subset_union_prime (I := Ideal.span (Set.range r)) (f := P)
    (s := (Finset.univ : Finset E)) ⟨x₀, hx₀⟩ ⟨x₀, hx₀⟩ (fun i _ _ _ => (j i.1).isPrime)
  have havoid : ¬ ((Ideal.span (Set.range r) : Set R) ⊆
      ⋃ x ∈ ((Finset.univ : Finset E) : Set E), ((P x : Ideal R) : Set R)) := by
    intro h
    obtain ⟨x, -, hle⟩ := H.mp h
    exact hr1' x (hle (hgen x))
  obtain ⟨g, hgI, hgnot⟩ := Set.not_subset.mp havoid
  simp only [Finset.coe_univ, Set.mem_univ, Set.iUnion_true, Set.mem_iUnion, SetLike.mem_coe,
    not_exists] at hgnot
  have hDle : PrimeSpectrum.basicOpen g ≤ j ''ᵁ W := by
    intro p hp
    by_contra hc
    refine (PrimeSpectrum.mem_basicOpen _ _).mp hp (Ideal.span_le.mpr ?_ hgI)
    rintro _ ⟨x, rfl⟩
    by_contra hrx
    exact hc (hr2 x ((PrimeSpectrum.mem_basicOpen _ _).mpr hrx))
  have himg : j ''ᵁ (j ⁻¹ᵁ PrimeSpectrum.basicOpen g) = PrimeSpectrum.basicOpen g := by
    refine Opens.ext ?_
    rw [Scheme.Hom.coe_image]
    exact Set.image_preimage_eq_of_subset (hDle.trans (j.image_le_opensRange W))
  refine ⟨g, ?_, fun x hx => ?_, fun y hy => ?_⟩
  · rw [← j.isAffineOpen_iff_of_isOpenImmersion, himg]
    exact IsAffineOpen.Spec_basicOpen g
  · exact (PrimeSpectrum.mem_basicOpen _ _).mpr (hgnot ⟨x, hx⟩)
  · have h2 : y ∈ j ⁻¹ᵁ (j ''ᵁ W) := hDle hy
    rwa [j.preimage_image_eq] at h2

/-- **On a quasi-affine scheme a finite subset of an open lies in an affine basic open inside
that open.** The basic open is that of a global section of the structure sheaf, because
`X.toSpecΓ ⁻¹ᵁ D(g)` is `X.basicOpen g`. -/
theorem exists_affine_basicOpen_of_finite_of_isQuasiAffine {X : Scheme.{u}} [X.IsQuasiAffine]
    {E : Set X} (hE : E.Finite) (W : X.Opens) (hEW : E ⊆ (W : Set X)) :
    ∃ g : Γ(X, ⊤), IsAffineOpen (X.basicOpen g) ∧ E ⊆ (X.basicOpen g : Set X) ∧
      X.basicOpen g ≤ W := by
  obtain ⟨g, haff, hEU, hUW⟩ := exists_affine_preimage_basicOpen_of_finite X.toSpecΓ hE W hEW
  rw [X.toSpecΓ_preimage_basicOpen] at haff hEU hUW
  exact ⟨g, haff, hEU, hUW⟩

end Stacks.AmpleCluster

end
