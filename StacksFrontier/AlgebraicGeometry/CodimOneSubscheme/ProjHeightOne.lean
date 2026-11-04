module

public import StacksFrontier.AlgebraicGeometry.CodimOneSubscheme.Basic
public import StacksFrontier.AlgebraicGeometry.MoreMorphisms.NowhereDenseFibres.Topology
public import StacksFrontier.AlgebraicGeometry.ProjChartKernel.Localization
public import StacksFrontier.AlgebraicGeometry.ProjIdealSheaf.HomogeneousGenerator
public import StacksFrontier.AlgebraicGeometry.ProjNoetherian.Basic
public import StacksFrontier.AlgebraicGeometry.ProjPolyChart.Cover
public import StacksFrontier.AlgebraicGeometry.ProjSaturation.Basic
public import StacksFrontier.AlgebraicGeometry.ProjSaturation.IdealOfClosedSubscheme
public import StacksFrontier.AlgebraicGeometry.ProjectiveSpace.Dimension.Basic
public import StacksFrontier.AlgebraicGeometry.Variety.Projective.DimensionOfProjectiveSpace
public import StacksFrontier.RingTheory.GradedAlgebra.Proj.ChartAssociatedPrimes
public import StacksFrontier.Topology.Dimension.NowhereDense
import StacksCore.Tactic.EgaSgaAttribute

/-!
# The homogeneous ideal of a codimension-one closed subscheme of `Proj` is principal

Let `A = ⨁_{n ≥ 0} 𝒜 n` be a Noetherian graded ring generated in degree one over `𝒜 0` and let
`i : Z ⟶ Proj 𝒜` be a closed immersion whose source has no embedded points and all of whose
irreducible components have codimension one in `Proj 𝒜`. This file shows that every associated
prime of the homogeneous ideal `I(Z) ⊆ A` has height one, and deduces **Tag 0BXL**: over a
Noetherian unique factorization domain, the homogeneous ideal of such a subscheme of projective
space is principal.

Over a *field* the codimension hypothesis is a statement about dimensions, and the file closes
with **Tag 0BXU**: a closed subscheme of `P^n_k` with no embedded points all of whose irreducible
components have dimension `n - 1` has principal homogeneous ideal.

The height statement is the input that
`AlgebraicGeometry.ProjectiveSpectrum.Proj.idealOfClosedSubscheme_isPrincipal_of_height_eq_one`
needs, and it is proved by reading the prime on a standard chart, in four steps.

* An associated prime `p` of `I(Z)` is a homogeneous prime that does not contain the irrelevant
  ideal — this is
  `isHomogeneous_and_not_irrelevant_le_of_mem_associatedPrimes_idealOfClosedSubscheme`, which
  combines homogeneity of associated primes of a homogeneous ideal with saturatedness of `I(Z)`.
* Hence, degree one generating the irrelevant ideal, some `f ∈ 𝒜 1` avoids `p`, so the point of
  `Proj 𝒜` cut out by `p` lies in the standard open `D₊(f)`. That is
  `exists_mem_degreeOne_notMem`.
* On that chart the question is unchanged: the height of `p` is the height of the corresponding
  prime of the degree-zero chart ring `A₍f₎` (`height_eq_height_under_away_of_isNoetherianRing`),
  and that prime is associated to the ideal `I(Z)` cuts out there
  (`under_mem_associatedPrimes_under_of_mem`).
* Finally `map_awayToSection_under_eq_ker` identifies the ideal `I(Z)` cuts out on the chart with
  the kernel `Ker(Γ(Proj 𝒜, D₊(f)) ⟶ Γ(Z, i⁻¹ D₊(f)))` that cuts `Z` out there — this is Tag
  0801's chart comparison — and
  `AlgebraicGeometry.height_eq_one_of_mem_associatedPrimes_ker_app` says the associated primes of
  *that* ideal have height one, which is where the geometric hypotheses on `Z` are consumed.

## Main results

* `AlgebraicGeometry.ProjectiveSpectrum.Proj.exists_mem_degreeOne_notMem`: an ideal not containing
  the irrelevant ideal of a graded ring generated in degree one omits some degree-one element.
* `AlgebraicGeometry.ProjectiveSpectrum.Proj.map_awayToSection_under_eq_ker`: **Tag 0801 on a
  standard chart, as an equality of ideals of the ring of sections.**
* `AlgebraicGeometry.ProjectiveSpectrum.Proj`
  `.height_eq_one_of_mem_associatedPrimes_idealOfClosedSubscheme`: **the height statement.**
* `AlgebraicGeometry.ProjectiveSpectrum.Proj`
  `.idealOfClosedSubscheme_isPrincipal_of_codimension_one`:
  **Tag 0BXL** for `Proj` of any graded Noetherian unique factorization domain generated in degree
  one, and
  `AlgebraicGeometry.ProjectiveSpectrum.Proj`
  `.projectiveSpace_idealOfClosedSubscheme_isPrincipal_of_codimension_one`: the same for
  `P^n_R`, which is the statement of the source.
* `codimension_eq_one_of_topologicalKrullDim_add_one`: in an irreducible space of dimension `d`,
  an irreducible closed subset of dimension `d - 1` has codimension one.
* `AlgebraicGeometry.ProjectiveSpectrum.Proj`
  `.projectiveSpace_idealOfClosedSubscheme_isPrincipal_of_dimension`: **Tag 0BXU**, the
  dimension form of Tag 0BXL over a field.

## Implementation notes

The source deduces principality from `Pic(P^n_R) = ℤ` (Tag 0BXJ) and the effective Cartier divisor
criterion of Tag 0BXH. The route here is the one recorded in
`StacksFrontier/AlgebraicGeometry/Divisors/ProjPrincipalCodimOne.lean`: an ideal of a Noetherian
unique factorization domain all of whose associated primes have height one is principal. Neither
0BXJ nor 0BXH is needed, and the result is obtained for `Proj` of an arbitrary graded Noetherian
UFD generated in degree one rather than only for projective space.

No unique factorization is used in the height statement itself, and no identification of the
chart ring with a polynomial ring (Tag 01NG): `height_eq_one_of_mem_associatedPrimes_ker_app`
holds over an arbitrary affine open of an arbitrary ambient scheme. Unique factorization enters
only in the last step, where principality is deduced, and there it is needed on `A` itself.

`Z` is locally Noetherian rather than assumed so: `Proj` of a Noetherian graded ring is a
Noetherian scheme (Tag 0B5Q, `Stacks.AlgebraicGeometry.Proj.isNoetherian_proj`), a closed
immersion is locally of finite type, and
`AlgebraicGeometry.LocallyOfFiniteType.isLocallyNoetherian` transports the property to the source.

The ring of sections over `D₊(f)` is identified with the degree-zero chart ring by Mathlib's
`AlgebraicGeometry.Proj.basicOpenIsoAway`, whose underlying ring homomorphism is
`AlgebraicGeometry.Proj.awayToSection` definitionally — which is also the map
`AlgebraicGeometry.ProjectiveSpectrum.Proj.chartFraction` is defined through, so the chart
comparison of Tag 0801 transfers across the isomorphism with no bridge lemma.

Dimensions are `topologicalKrullDim`, valued in `WithBot ℕ∞`, so the hypothesis of Tag 0BXU is
written additively as `dim W + 1 = n` and no truncated subtraction appears; for `n = 0` it says
that `Z` has no irreducible component, which is what `dim W = -1` means for the source.
Codimension one is obtained from it with no transcendence degree and no dimension formula: the
ambient space is irreducible of dimension `n` (Tag 0B2P), and `dim W + codim W ≤ dim P^n_k`
already forces the codimension to be one.

## References

* [Stacks Project, Tag 0BXL](https://stacks.math.columbia.edu/tag/0BXL)
* [Stacks Project, Tag 0BXU](https://stacks.math.columbia.edu/tag/0BXU)
* [Stacks Project, Tag 0B2P](https://stacks.math.columbia.edu/tag/0B2P)
* [Stacks Project, Tag 0801](https://stacks.math.columbia.edu/tag/0801)
* [Stacks Project, Tag 0BXK](https://stacks.math.columbia.edu/tag/0BXK)
* [Stacks Project, Tag 0B5Q](https://stacks.math.columbia.edu/tag/0B5Q)
-/

@[expose] public noncomputable section

open CategoryTheory TopologicalSpace HomogeneousLocalization
open Stacks.GradedChartAssociatedPrimes Stacks.GradedLaurent

universe u

/-! ### Codimension one from the dimension of a subset -/

/-- **In an irreducible space of dimension `d`, an irreducible closed subset of dimension `d - 1`
has codimension one**, the hypothesis being written without subtraction as
`dim B + 1 = d`.

The inequality `dim B + codim B ≤ dim T` bounds the codimension by one, and a codimension of
zero would make `B` maximal, hence the whole of the irreducible space `T`, whose dimension is
`d` and not `d - 1`. -/
theorem codimension_eq_one_of_topologicalKrullDim_add_one {T : Type*} [TopologicalSpace T]
    [IrreducibleSpace T] {d : ℕ} (hT : topologicalKrullDim T = (d : WithBot ℕ∞))
    (B : IrreducibleCloseds T) (hB : topologicalKrullDim (B : Set T) + 1 = (d : WithBot ℕ∞)) :
    codimension B = 1 := by
  have hheight : Order.height B + 1 = (d : ℕ∞) := by
    rw [topologicalKrullDim_coe_eq_height B] at hB
    exact_mod_cast hB
  have hne : Order.height B ≠ ⊤ := fun h => by simp [h] at hheight
  refine le_antisymm ?_ ?_
  · have hle := AlgebraicGeometry.topologicalKrullDim_add_codimension_le B
    rw [topologicalKrullDim_coe_eq_height B, hT] at hle
    have hle' : Order.height B + codimension B ≤ (d : ℕ∞) := by exact_mod_cast hle
    rw [← hheight] at hle'
    exact (ENat.add_le_add_iff_left hne).mp hle'
  · rw [Order.one_le_iff_ne_zero]
    intro h0
    have hmax : IsMax B := Order.coheight_eq_zero.mp (codimension_eq_coheight B ▸ h0)
    have hBuniv : (B : Set T) = Set.univ :=
      Set.univ_subset_iff.mp
        (hmax (b := ⟨Set.univ, IrreducibleSpace.isIrreducible_univ T, isClosed_univ⟩)
          fun x _ => Set.mem_univ x)
    have hBheight : (Order.height B : WithBot ℕ∞) = (d : WithBot ℕ∞) := by
      rw [← topologicalKrullDim_coe_eq_height B, hBuniv, topologicalKrullDim_univ, hT]
    rw [(by exact_mod_cast hBheight : Order.height B = (d : ℕ∞))] at hheight
    exact absurd (by exact_mod_cast hheight : d + 1 = d) (by omega)

namespace AlgebraicGeometry.ProjectiveSpectrum.Proj

open AlgebraicGeometry

/-! ### A prime omitting the irrelevant ideal omits a degree-one element -/

section DegreeOne

variable {S : Type*} {σ : Type*} [CommRing S] [SetLike σ S] [AddSubgroupClass σ S]
  (𝒮 : ℕ → σ) [GradedRing 𝒮]

/-- **An ideal that does not contain the irrelevant ideal omits a degree-one element**, when the
graded ring is generated in degree one over its degree-zero part.

This is what puts the point of `Proj 𝒮` cut out by a relevant homogeneous prime inside a standard
open `D₊(f)` with `f` of degree *one* — which is the degree the chart comparisons of this
development require, and which a general homogeneous element of positive degree would not
supply. -/
@[ega "II 2.1.3" "special case"]
theorem exists_mem_degreeOne_notMem (hgen : Algebra.adjoin (𝒮 0) ((𝒮 1 : Set S)) = ⊤)
    {p : Ideal S} (hirr : ¬(HomogeneousIdeal.irrelevant 𝒮).toIdeal ≤ p) :
    ∃ f ∈ 𝒮 1, f ∉ p := by
  by_contra! hc
  exact hirr (span_degreeOne_eq_irrelevant 𝒮 hgen ▸ Ideal.span_le.mpr hc)

end DegreeOne

/-! ### The homogeneous ideal and the chart ideal agree -/

variable {R : Type*} {A : Type u} [CommRing R] [CommRing A] [Algebra R A]
variable (𝒜 : ℕ → Submodule R A) [GradedAlgebra 𝒜] {f : A}

/-- **Tag 0801 on a standard chart, as an equality of ideals of the ring of sections.** Over a
Noetherian graded ring generated in degree one, the ideal that the homogeneous ideal of a closed
subscheme `Z ⊆ Proj 𝒜` cuts out on the degree-zero chart ring `A₍f₎` is carried by the chart
identification `A₍f₎ ≅ Γ(Proj 𝒜, D₊(f))` exactly onto the kernel
`Ker(Γ(Proj 𝒜, D₊(f)) ⟶ Γ(Z, i⁻¹ D₊(f)))` that cuts `Z` out there.

Both inclusions are `mem_ker_app_basicOpen_iff` read through
`Stacks.GradedChartAssociatedPrimes.mem_under_map_iff`: the former describes the kernel as the
chart functions `b / f ^ n` of homogeneous `b ∈ I(Z)`, the latter describes the contracted ideal
by the same fractions, and `chartFraction` is by definition `awayToSection` applied to
`HomogeneousLocalization.Away.mk`. -/
theorem map_awayToSection_under_eq_ker [IsNoetherianRing A]
    (hgen : Algebra.adjoin (𝒜 0) ((𝒜 1 : Set A)) = ⊤) (hf : f ∈ 𝒜 1)
    {Z : Scheme.{u}} (i : Z ⟶ Proj 𝒜) [IsClosedImmersion i] :
    Ideal.map (Proj.awayToSection 𝒜 f).hom
        (((idealOfClosedSubscheme 𝒜 i).map
          (algebraMap A (Localization.Away f))).under (Away 𝒜 f))
      = RingHom.ker (i.app (Proj.basicOpen 𝒜 f)).hom := by
  obtain ⟨t, ht1, hcov⟩ := exists_finite_degreeOne_cover 𝒜 hgen
  have hiff := mem_ker_app_basicOpen_iff 𝒜 Nat.one_pos
    (fun j : {x : A // x ∈ t} => (j : A)) (fun j => ht1 _ j.2) hcov hf i
  refine le_antisymm (Ideal.map_le_iff_le_comap.mpr fun x hx => ?_) fun s hs => ?_
  · obtain ⟨n, b, hb, hbI, rfl⟩ := (mem_under_map_iff 𝒜 hf x).mp hx
    exact (hiff _).mpr ⟨n, ⟨b, hb⟩, hbI, rfl⟩
  · obtain ⟨m, c, hc, rfl⟩ := (hiff s).mp hs
    exact Ideal.mem_map_of_mem _ ((mem_under_map_iff 𝒜 hf _).mpr ⟨m, (c : A), c.2, hc, rfl⟩)

/-! ### The height statement -/

/-- **Every associated prime of the homogeneous ideal of a codimension-one closed subscheme of
`Proj` has height one.**

Let `A` be a Noetherian graded ring generated in degree one over `𝒜 0` and let `Z` be a closed
subscheme of `Proj 𝒜` with no embedded points all of whose irreducible components have
codimension one. Then every prime associated to the homogeneous ideal `I(Z)` has height one.

This is the geometric input that Tag 0BXL needs, read on a standard chart `D₊(f)` with `f` of
degree one avoiding the prime; see the module docstring for the four steps. -/
theorem height_eq_one_of_mem_associatedPrimes_idealOfClosedSubscheme [IsNoetherianRing A]
    (hgen : Algebra.adjoin (𝒜 0) ((𝒜 1 : Set A)) = ⊤) {Z : Scheme.{u}} (i : Z ⟶ Proj 𝒜)
    [IsClosedImmersion i] (hno : HasNoEmbeddedPoints Z)
    (hcodim : ∀ W ∈ irreducibleComponents Z, ∀ x : Z,
      IsGenericPoint x W → codimension (IrreducibleCloseds.closureSingleton (i.base x)) = 1)
    {p : Ideal A} (hp : p ∈ Submodule.associatedPrimes (idealOfClosedSubscheme 𝒜 i)) :
    p.height = 1 := by
  have hprime : p.IsPrime := hp.1
  obtain ⟨hhom, hirr⟩ :=
    isHomogeneous_and_not_irrelevant_le_of_mem_associatedPrimes_idealOfClosedSubscheme 𝒜 hgen i hp
  obtain ⟨f, hf, hfp⟩ := exists_mem_degreeOne_notMem 𝒜 hgen hirr
  -- the chart `D₊(f)` contains the point cut out by `p`, and is affine
  have hZ : IsLocallyNoetherian Z := LocallyOfFiniteType.isLocallyNoetherian i
  -- the corresponding prime of the chart ring is associated to the chart ideal
  have hq := under_mem_associatedPrimes_under_of_mem 𝒜 hf
    (idealOfClosedSubscheme_isHomogeneous 𝒜 i) hfp hp
  -- transport it to the ring of sections, where the geometric statement lives. The underlying
  -- ring homomorphism of the chart isomorphism is `awayToSection` definitionally, so `exact`
  -- crosses the two spellings where `rw` would not.
  let e : Away 𝒜 f ≃+* Γ(Proj 𝒜, Proj.basicOpen 𝒜 f) :=
    (Proj.basicOpenIsoAway 𝒜 f hf Nat.one_pos).commRingCatIsoToRingEquiv
  have hqe : Ideal.map (Proj.awayToSection 𝒜 f).hom
      ((p.map (algebraMap A (Localization.Away f))).under (Away 𝒜 f))
        ∈ Submodule.associatedPrimes (RingHom.ker (i.app (Proj.basicOpen 𝒜 f)).hom) := by
    rw [← map_awayToSection_under_eq_ker 𝒜 hgen hf i]
    exact map_mem_associatedPrimes_map_of_ringEquiv e hq
  -- heights: the graded prime, the chart prime, and its image in the sections all agree
  have hheight := RingEquiv.height_map e
    ((p.map (algebraMap A (Localization.Away f))).under (Away 𝒜 f))
  rw [height_eq_height_under_away_of_isNoetherianRing 𝒜 hf hhom hfp, ← hheight]
  exact height_eq_one_of_mem_associatedPrimes_ker_app i hno hcodim
    (Proj.isAffineOpen_basicOpen 𝒜 f hf Nat.one_pos) hqe

/-! ### Tag 0BXL -/

/-- **Stacks Project, Tag 0BXL, for `Proj` of a graded Noetherian UFD generated in degree one.**
Let `A = ⨁_{n ≥ 0} 𝒜 n` be a graded ring which is a Noetherian unique factorization domain and is
generated in degree one over `𝒜 0`. Let `Z` be a closed subscheme of `Proj 𝒜` which has no
embedded points and every irreducible component of which has codimension one in `Proj 𝒜`. Then
the homogeneous ideal `I(Z) ⊆ A` of `Z` is principal.

This is `height_eq_one_of_mem_associatedPrimes_idealOfClosedSubscheme` fed to
`idealOfClosedSubscheme_isPrincipal_of_height_eq_one`. -/
theorem idealOfClosedSubscheme_isPrincipal_of_codimension_one [IsDomain A] [IsNoetherianRing A]
    [UniqueFactorizationMonoid A] (hgen : Algebra.adjoin (𝒜 0) ((𝒜 1 : Set A)) = ⊤)
    {Z : Scheme.{u}} (i : Z ⟶ Proj 𝒜) [IsClosedImmersion i] (hno : HasNoEmbeddedPoints Z)
    (hcodim : ∀ W ∈ irreducibleComponents Z, ∀ x : Z,
      IsGenericPoint x W → codimension (IrreducibleCloseds.closureSingleton (i.base x)) = 1) :
    (idealOfClosedSubscheme 𝒜 i).IsPrincipal :=
  idealOfClosedSubscheme_isPrincipal_of_height_eq_one 𝒜 i fun _ hp =>
    height_eq_one_of_mem_associatedPrimes_idealOfClosedSubscheme 𝒜 hgen i hno hcodim hp

section ProjectiveSpace

attribute [local instance] MvPolynomial.gradedAlgebra

/-- **Stacks Project, Tag 0BXL.** Let `R` be a Noetherian unique factorization domain and let `Z`
be a closed subscheme of `P^n_R = Proj R[T₀, …, Tₙ]` which has no embedded points and every
irreducible component of which has codimension one in `P^n_R`. Then the homogeneous ideal
`I(Z) ⊆ R[T₀, …, Tₙ]` corresponding to `Z` is principal.

A polynomial ring over a Noetherian UFD is a Noetherian UFD and is generated in degree one, so
this is the general `Proj` statement
`idealOfClosedSubscheme_isPrincipal_of_codimension_one`. For the conclusion in the form of a
single homogeneous equation see
`projectiveSpace_exists_homogeneous_eq_idealOfClosedSubscheme`. -/
@[stacks 0BXL]
theorem projectiveSpace_idealOfClosedSubscheme_isPrincipal_of_codimension_one (R : Type u)
    [CommRing R] [IsDomain R] [IsNoetherianRing R] [UniqueFactorizationMonoid R] (n : ℕ)
    {Z : Scheme.{u}} (i : Z ⟶ Proj (MvPolynomial.homogeneousSubmodule (Fin (n + 1)) R))
    [IsClosedImmersion i] (hno : HasNoEmbeddedPoints Z)
    (hcodim : ∀ W ∈ irreducibleComponents Z, ∀ x : Z,
      IsGenericPoint x W → codimension (IrreducibleCloseds.closureSingleton (i.base x)) = 1) :
    (idealOfClosedSubscheme
      (MvPolynomial.homogeneousSubmodule (Fin (n + 1)) R) i).IsPrincipal :=
  idealOfClosedSubscheme_isPrincipal_of_codimension_one _
    (MvPolynomial.adjoin_homogeneousSubmodule_one_eq_top (Fin (n + 1)) R) i hno hcodim

/-- **Tag 0BXL with a homogeneous equation.** The homogeneous ideal of a closed subscheme of
`P^n_R` over a Noetherian unique factorization domain which has no embedded points and all of
whose irreducible components have codimension one is generated by a single homogeneous
polynomial.

This is the form in which the source's *proof* exhibits the generator; the statement of Tag 0BXL
asserts only principality, so the tag sits on
`projectiveSpace_idealOfClosedSubscheme_isPrincipal_of_codimension_one` alone and not here. -/
theorem projectiveSpace_exists_homogeneous_eq_idealOfClosedSubscheme_of_codimension_one
    (R : Type u) [CommRing R] [IsDomain R] [IsNoetherianRing R] [UniqueFactorizationMonoid R]
    (n : ℕ) {Z : Scheme.{u}} (i : Z ⟶ Proj (MvPolynomial.homogeneousSubmodule (Fin (n + 1)) R))
    [IsClosedImmersion i] (hno : HasNoEmbeddedPoints Z)
    (hcodim : ∀ W ∈ irreducibleComponents Z, ∀ x : Z,
      IsGenericPoint x W → codimension (IrreducibleCloseds.closureSingleton (i.base x)) = 1) :
    ∃ (d : ℕ) (F : MvPolynomial (Fin (n + 1)) R),
      F ∈ MvPolynomial.homogeneousSubmodule (Fin (n + 1)) R d ∧
        idealOfClosedSubscheme (MvPolynomial.homogeneousSubmodule (Fin (n + 1)) R) i =
          Ideal.span {F} :=
  projectiveSpace_exists_homogeneous_eq_idealOfClosedSubscheme R n i fun _ hp =>
    height_eq_one_of_mem_associatedPrimes_idealOfClosedSubscheme _
      (MvPolynomial.adjoin_homogeneousSubmodule_one_eq_top (Fin (n + 1)) R) i hno hcodim hp

/-! ### Tag 0BXU: dimension `n - 1` over a field -/

/-- **A subset of dimension `n - 1` of a closed subscheme of `P^n_k` has codimension-one closure
in `P^n_k`.** Let `k` be a field, let `Z` be a closed subscheme of `P^n_k` and let `x ∈ Z` be the
generic point of a subset `W` of dimension `n - 1`, written without subtraction as
`dim W + 1 = n`. Then the closure of the image of `x` has codimension one in `P^n_k`.

Projective space over a field is irreducible and of dimension `n`, the closure of the image of
`x` is the image of `W` because a closed immersion is a closed embedding, and that image is
homeomorphic to `W`; so this is
`codimension_eq_one_of_topologicalKrullDim_add_one`. -/
theorem projectiveSpace_codimension_closureSingleton_eq_one (k : Type u) [Field k] (n : ℕ)
    {Z : Scheme.{u}} (i : Z ⟶ Proj (MvPolynomial.homogeneousSubmodule (Fin (n + 1)) k))
    [IsClosedImmersion i] {W : Set Z} {x : Z} (hx : IsGenericPoint x W)
    (hW : topologicalKrullDim W + 1 = (n : WithBot ℕ∞)) :
    codimension (IrreducibleCloseds.closureSingleton (i.base x)) = 1 := by
  have hdimP : topologicalKrullDim
      (Proj (MvPolynomial.homogeneousSubmodule (Fin (n + 1)) k)) = (n : WithBot ℕ∞) := by
    simpa using Stacks.ProjectiveSpace.topologicalKrullDim_proj_fin k (r := n + 1) n.succ_pos
  refine codimension_eq_one_of_topologicalKrullDim_add_one hdimP _ ?_
  have himage : (IrreducibleCloseds.closureSingleton (i.base x) :
      Set (Proj (MvPolynomial.homogeneousSubmodule (Fin (n + 1)) k))) = i.base '' W := by
    rw [IrreducibleCloseds.coe_closureSingleton, ← hx.def, ← Set.image_singleton,
      i.isClosedEmbedding.closure_image_eq]
  rw [himage, ← hW,
    IsHomeomorph.topologicalKrullDim_eq _ (i.isClosedEmbedding.isEmbedding.homeomorphImage
      W).isHomeomorph]

/-- **Stacks Project, Tag 0BXU.** Let `k` be a field and let `Z` be a closed subscheme of
`P^n_k = Proj k[T₀, …, Tₙ]` which has no embedded points and every irreducible component of which
has dimension `n - 1`. Then the homogeneous ideal `I(Z) ⊆ k[T₀, …, Tₙ]` corresponding to `Z` is
principal.

The dimension hypothesis is written without subtraction as `dim W + 1 = n`. A field is a
Noetherian unique factorization domain, and in projective space over a field a component of
dimension `n - 1` has codimension one, so this is a special case of Tag 0BXL in the form
`projectiveSpace_idealOfClosedSubscheme_isPrincipal_of_codimension_one`. -/
@[stacks 0BXU]
theorem projectiveSpace_idealOfClosedSubscheme_isPrincipal_of_dimension (k : Type u) [Field k]
    (n : ℕ) {Z : Scheme.{u}} (i : Z ⟶ Proj (MvPolynomial.homogeneousSubmodule (Fin (n + 1)) k))
    [IsClosedImmersion i] (hno : HasNoEmbeddedPoints Z)
    (hdim : ∀ W ∈ irreducibleComponents Z, topologicalKrullDim W + 1 = (n : WithBot ℕ∞)) :
    (idealOfClosedSubscheme
      (MvPolynomial.homogeneousSubmodule (Fin (n + 1)) k) i).IsPrincipal :=
  projectiveSpace_idealOfClosedSubscheme_isPrincipal_of_codimension_one k n i hno
    fun W hW _ hx => projectiveSpace_codimension_closureSingleton_eq_one k n i hx (hdim W hW)

end ProjectiveSpace

end AlgebraicGeometry.ProjectiveSpectrum.Proj

end
