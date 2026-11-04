module

public import Mathlib.RingTheory.Ideal.Quotient.Noetherian
public import Mathlib.RingTheory.Ideal.Quotient.Operations
public import StacksFrontier.AlgebraicGeometry.LocalCohomology.CodimensionOneObstruction.PoleLocus

/-!
# The pole locus at an associated point

Let `X` be a locally Noetherian scheme, `V₀` an affine open, and `x`, `z` two points of `V₀` with
`z` in the closure of `x`. This file proves that if the local ring of the closure of `x` at `z`
has dimension at most one, then for every open `S` avoiding `z` the opens `S ⊓ D(g)`, for `g` not
vanishing at `z`, shrink along the closure of `x` to arbitrarily small neighbourhoods of `x`.

This generalizes `Stacks.AlgebraicGeometry.CodimensionOneObstruction.exists_basicOpen_inter_le`
from the generic point of an integral scheme to an arbitrary point `x`, which is what the first
paragraph of [Stacks, Tag 0AWC] needs for a general associated point of a coherent module: there
`x` runs over `Ass(𝓕)` and the relevant one-dimensionality hypothesis is on
`𝒪_{\overline{\{x\}}, z}`, not on `𝒪_{X, z}`.

## Main results

* `Stacks.AlgebraicGeometry.CodimensionOneObstruction.mem_primeIdealOf_iff_germ_mem_maximalIdeal`:
  a function on an affine open vanishes at a point exactly when its germ there is a nonunit.
* `Stacks.AlgebraicGeometry.CodimensionOneObstruction.primeIdealOf_le_primeIdealOf_of_specializes`
  and `specializes_of_primeIdealOf_le`: specialization between points of an affine open is
  inclusion of the attached primes.
* `exists_notMem_forall_le_of_height_quotient_le_one`, in the same namespace: the
  ring-theoretic pole-locus statement relative to a prime `p ≤ q`.
* `Stacks.AlgebraicGeometry.CodimensionOneObstruction.exists_basicOpen_forall_mem_basicOpen`: its
  geometric form on a scheme.

## Implementation notes

The relative pole-locus statement is deduced from the absolute one
(`exists_notMem_forall_le_of_height_le_one`, proved in
`StacksFrontier.AlgebraicGeometry.LocalCohomology.CodimensionOneObstruction.PoleLocus`) by passing to
the Noetherian domain `R ⧸ p`; the one-dimensionality hypothesis is stated as
`(q.map (Ideal.Quotient.mk p)).height ≤ 1`, which is the Krull dimension of the local ring of the
closed subscheme `V(p)` at `q`.

Unlike the absolute statement, the geometric form is proved without passing through
`Spec Γ(X, V₀)`: specialization between points of an affine open is read off the attached primes
by `primeIdealOf_le_primeIdealOf_of_specializes` and `specializes_of_primeIdealOf_le`, and
membership of a basic open is read off the prime by
`Stacks.AlgebraicGeometry.CodimensionOneObstruction.mem_basicOpen_iff_notMem_primeIdealOf`.

## References

* [Stacks Project, Tag 0AWC](https://stacks.math.columbia.edu/tag/0AWC)
* [Stacks Project, Tag 02IZ](https://stacks.math.columbia.edu/tag/02IZ)
-/

@[expose] public section

open AlgebraicGeometry CategoryTheory TopologicalSpace Opposite

universe u

namespace Stacks.AlgebraicGeometry.CodimensionOneObstruction

variable {X : Scheme.{u}}

/-! ### Reading the prime of a point off germs -/

/-- A function on an affine open lies in the prime attached to a point exactly when its germ
there lies in the maximal ideal of the local ring. -/
theorem mem_primeIdealOf_iff_germ_mem_maximalIdeal {V : X.Opens} (hV : IsAffineOpen V) {x : X}
    (hx : x ∈ V) (f : Γ(X, V)) :
    f ∈ (hV.primeIdealOf ⟨x, hx⟩).asIdeal ↔
      X.presheaf.germ V x hx f ∈ IsLocalRing.maximalIdeal (X.presheaf.stalk x) := by
  rw [← not_iff_not, IsLocalRing.notMem_maximalIdeal, ← X.mem_basicOpen f x hx,
    mem_basicOpen_iff_notMem_primeIdealOf hV hx f]

/-- The prime of a specialization contains the prime of the point it specializes from. Here
`x ⤳ z` is the Mathlib spelling of `z ∈ closure {x}`. -/
theorem primeIdealOf_le_primeIdealOf_of_specializes {V : X.Opens} (hV : IsAffineOpen V) {x z : X}
    (hx : x ∈ V) (hz : z ∈ V) (hxz : x ⤳ z) :
    (hV.primeIdealOf ⟨x, hx⟩).asIdeal ≤ (hV.primeIdealOf ⟨z, hz⟩).asIdeal := by
  intro a ha
  by_contra hna
  have hzmem : z ∈ ((X.basicOpen a : X.Opens) : Set X) :=
    (mem_basicOpen_iff_notMem_primeIdealOf hV hz a).mpr hna
  exact (mem_basicOpen_iff_notMem_primeIdealOf hV hx a).mp
    (hxz.mem_open (X.basicOpen a).isOpen hzmem) ha

/-- A point of an affine open whose prime contains the prime of `z` is a point that `z`
specializes to. -/
theorem specializes_of_primeIdealOf_le {V : X.Opens} (hV : IsAffineOpen V) {y z : X}
    (hy : y ∈ V) (hz : z ∈ V)
    (hle : (hV.primeIdealOf ⟨z, hz⟩).asIdeal ≤ (hV.primeIdealOf ⟨y, hy⟩).asIdeal) :
    z ⤳ y := by
  have h1 : (hV.primeIdealOf ⟨z, hz⟩) ⤳ (hV.primeIdealOf ⟨y, hy⟩) :=
    (PrimeSpectrum.le_iff_specializes _ _).mp hle
  have h2 := h1.map hV.fromSpec.base.hom.continuous
  rwa [hV.fromSpec_primeIdealOf ⟨y, hy⟩, hV.fromSpec_primeIdealOf ⟨z, hz⟩] at h2

/-! ### The relative pole-locus lemma -/

/-- **The relative pole-locus lemma.** Let `R` be Noetherian, let `p ≤ q` be primes such that the
image of `q` in `R ⧸ p` has height at most one, and let `b ∉ p`. Then there is `g ∉ q` such that
every prime containing `p` and `b` but not `g` contains `q`.

This is the relative form of
`Stacks.AlgebraicGeometry.CodimensionOneObstruction.exists_notMem_forall_le_of_height_le_one`,
which is the case `p = ⊥` of a domain. On `Spec R` it says that the vanishing locus of `b` meets
`V(p) ∩ D(g)` only inside the closure of `q`. -/
theorem exists_notMem_forall_le_of_height_quotient_le_one {R : Type u} [CommRing R]
    [IsNoetherianRing R] {p q : Ideal R} [hp : p.IsPrime] [hq : q.IsPrime] (hpq : p ≤ q)
    (hq1 : (q.map (Ideal.Quotient.mk p)).height ≤ 1) {b : R} (hb : b ∉ p) :
    ∃ g : R, g ∉ q ∧ ∀ r : Ideal R, r.IsPrime → p ≤ r → b ∈ r → g ∉ r → q ≤ r := by
  classical
  have hsurj : Function.Surjective (Ideal.Quotient.mk p) := Ideal.Quotient.mk_surjective
  have hkb : RingHom.ker (Ideal.Quotient.mk p) = p := Ideal.mk_ker
  have hkb2 : Ideal.comap (Ideal.Quotient.mk p) (⊥ : Ideal (R ⧸ p)) = p := by
    ext c; simp [Ideal.Quotient.eq_zero_iff_mem]
  have : IsDomain (R ⧸ p) := Ideal.Quotient.isDomain p
  have : IsNoetherianRing (R ⧸ p) := Ideal.Quotient.isNoetherianRing p
  have hprime : ∀ r : Ideal R, p ≤ r → r.IsPrime → (r.map (Ideal.Quotient.mk p)).IsPrime :=
    fun _ hr _ => Ideal.map_isPrime_of_surjective hsurj (hkb.le.trans hr)
  have hqp := hprime q hpq hq
  have hb' : Ideal.Quotient.mk p b ≠ 0 := by
    rw [Ne, Ideal.Quotient.eq_zero_iff_mem]; exact hb
  obtain ⟨g', hg'q, hg'⟩ := exists_notMem_forall_le_of_height_le_one (R := R ⧸ p) hq1 hb'
  obtain ⟨g, rfl⟩ := hsurj g'
  have hmem : ∀ (r : Ideal R), p ≤ r → ∀ c : R,
      Ideal.Quotient.mk p c ∈ r.map (Ideal.Quotient.mk p) ↔ c ∈ r := by
    intro r hr c
    refine ⟨fun hc => ?_, fun hc => Ideal.mem_map_of_mem _ hc⟩
    have hcc : c ∈ (r.map (Ideal.Quotient.mk p)).comap (Ideal.Quotient.mk p) := hc
    rw [Ideal.comap_map_of_surjective _ hsurj, hkb2, sup_eq_left.mpr hr] at hcc
    exact hcc
  refine ⟨g, fun hgq => hg'q ((hmem q hpq g).mpr hgq), fun r hrp hpr hbr hgr => ?_⟩
  have hle := hg' (r.map (Ideal.Quotient.mk p)) (hprime r hpr hrp)
    ((hmem r hpr b).mpr hbr) (fun h => hgr ((hmem r hpr g).mp h))
  intro c hc
  exact (hmem r hpr c).mp (hle (Ideal.mem_map_of_mem _ hc))

/-! ### The cofinality statement at a non-generic point -/

/-- **The pole locus at a point specializing to `z`.** Let `X` be locally Noetherian, `V₀` an
affine open containing points `x` and `z` with `z` in the closure of `x`, let the image of the
prime of `z` in `Γ(X, V₀) ⧸ p_x` have height at most one, and let `S` be an open of `X` avoiding
`z`. Then for every `s : Γ(X, V₀)` not vanishing at `x` there is a `g : Γ(X, V₀)` not vanishing at
`z` such that every point of `S ⊓ D(g)` lying in the closure of `x` lies in `D(s)`.

Geometrically: on a neighbourhood of `z` cut out by `g`, the divisor of `s` meets the closure of
`x` only inside the closure of `z`, which `S` avoids. This is the non-generic analogue of
`Stacks.AlgebraicGeometry.CodimensionOneObstruction.exists_basicOpen_inter_le`; the hypothesis on
the height is the hypothesis `dim 𝒪_{\overline{\{x\}}, z} ≤ 1` of [Stacks, Tag 0AWC], read on the
affine chart `V₀`. -/
theorem exists_basicOpen_forall_mem_basicOpen [IsLocallyNoetherian X] {V₀ : X.Opens}
    (hV₀ : IsAffineOpen V₀) {x z : X} (hx : x ∈ V₀) (hz : z ∈ V₀) (hxz : x ⤳ z)
    (hdim : ((hV₀.primeIdealOf ⟨z, hz⟩).asIdeal.map
        (Ideal.Quotient.mk (hV₀.primeIdealOf ⟨x, hx⟩).asIdeal)).height ≤ 1)
    {S : X.Opens} (hzS : z ∉ S) {s : Γ(X, V₀)} (hxs : x ∈ X.basicOpen s) :
    ∃ g : Γ(X, V₀), z ∈ X.basicOpen g ∧
      ∀ (y : X) (hy : y ∈ V₀), y ∈ S → y ∈ X.basicOpen g →
        (hV₀.primeIdealOf ⟨x, hx⟩).asIdeal ≤ (hV₀.primeIdealOf ⟨y, hy⟩).asIdeal →
        y ∈ X.basicOpen s := by
  have : Nonempty V₀ := ⟨⟨z, hz⟩⟩
  have : IsNoetherianRing Γ(X, V₀) := IsLocallyNoetherian.component_noetherian ⟨V₀, hV₀⟩
  have hp : ((hV₀.primeIdealOf ⟨x, hx⟩).asIdeal).IsPrime := (hV₀.primeIdealOf ⟨x, hx⟩).isPrime
  have hq : ((hV₀.primeIdealOf ⟨z, hz⟩).asIdeal).IsPrime := (hV₀.primeIdealOf ⟨z, hz⟩).isPrime
  have hpq := primeIdealOf_le_primeIdealOf_of_specializes hV₀ hx hz hxz
  have hsp : s ∉ (hV₀.primeIdealOf ⟨x, hx⟩).asIdeal :=
    (mem_basicOpen_iff_notMem_primeIdealOf hV₀ hx s).mp hxs
  obtain ⟨g, hgq, hg⟩ := exists_notMem_forall_le_of_height_quotient_le_one hpq hdim hsp
  refine ⟨g, (mem_basicOpen_iff_notMem_primeIdealOf hV₀ hz g).mpr hgq, ?_⟩
  intro y hy hyS hyg hple
  by_contra hys
  have hsy : s ∈ (hV₀.primeIdealOf ⟨y, hy⟩).asIdeal :=
    not_not.mp fun h => hys ((mem_basicOpen_iff_notMem_primeIdealOf hV₀ hy s).mpr h)
  have hgy : g ∉ (hV₀.primeIdealOf ⟨y, hy⟩).asIdeal :=
    (mem_basicOpen_iff_notMem_primeIdealOf hV₀ hy g).mp hyg
  have hqle := hg (hV₀.primeIdealOf ⟨y, hy⟩).asIdeal
    (hV₀.primeIdealOf ⟨y, hy⟩).isPrime hple hsy hgy
  exact hzS ((specializes_of_primeIdealOf_le hV₀ hy hz hqle).mem_open S.isOpen hyS)

end Stacks.AlgebraicGeometry.CodimensionOneObstruction

end
