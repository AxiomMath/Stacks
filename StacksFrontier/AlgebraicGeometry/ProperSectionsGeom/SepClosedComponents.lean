module

public import Mathlib.RingTheory.Etale.Field
public import Mathlib.RingTheory.Etale.Pi
public import StacksFrontier.AlgebraicGeometry.Curves.GenusCurve.CohomologyComparison
public import StacksFrontier.AlgebraicGeometry.ProperSectionsGeom.Components
import StacksCore.Tactic.EgaSgaAttribute

/-!
# `h⁰` counts the connected components, over a separably closed field

Let `Ω` be a separably closed field and let `Z` be proper over `Ω`. The ring of global functions
`Γ(Z, 𝒪_Z)` is a finite product of Artinian local `Ω`-algebras, one factor for each connected
component of `Z` ([Stacks, Tag 0BUG] (1) and (2), which is
`Stacks.AlgebraicGeometry.ProperSectionsGeom.componentwiseArtinianDecomposition`). Each factor is
nonzero, so the number of connected components is at most `dim_Ω Γ(Z, 𝒪_Z)`; the two agree exactly
when every factor is `Ω` itself, and over a separably closed field that is what geometric
reducedness of `Z` buys.

## Main results

All of these live in the namespace `Stacks.AlgebraicGeometry.ProperSectionsGeom`.

* `card_connectedComponents_le_finrank_globalSections`: for an arbitrary proper `Z` over an
  arbitrary field, the number of connected components is at most `dim_k Γ(Z, 𝒪_Z)`.
* `finrank_globalSections_eq_card_connectedComponents`: for `Z` proper and geometrically reduced
  over a separably closed `Ω`, `dim_Ω Γ(Z, 𝒪_Z)` is exactly the number of connected components.
* `finrank_structureSheafCohomology_zero_eq_card_connectedComponents`: the same equality written
  with `AlgebraicGeometry.structureSheafCohomology`, i.e. as `h⁰(Z, 𝒪_Z) = #π₀(Z)`.

## Implementation notes

**Which hypotheses are load-bearing.**

* *Properness* is used twice, and only through [Stacks, Tag 0BUG]: it makes `Γ(Z, 𝒪_Z)` a finite
  `Ω`-module, and it makes `Z` a Noetherian space, so that there are finitely many connected
  components and each of them is open. Both the inequality and the equality below use it only
  through that one decomposition. Nothing below uses the dimension of `Z`, so no curve or
  dimension hypothesis appears; finite type is already part of properness, and is what finiteness
  of the component count rests on.
* *Finiteness of the component count* therefore needs no hypothesis beyond properness and is not
  assumed: `Nat.card` is used rather than `ENat.card` precisely because the count is finite here,
  and because the equality is then an equality of natural numbers with `Module.finrank`. (Both
  sides degenerate to `0` on the infinite/infinite-dimensional side of the convention, so an
  `ENat`-valued statement would be no stronger.)
* *Geometric* reducedness, not reducedness, is what makes each factor `Ω`. Reducedness alone makes
  each factor a field finite over `Ω` ([Stacks, Tag 0BUG] (3)), but over a separably closed field
  that is not enough: if `Ω` is the separable closure of `𝔽_p(t)` then `Spec Ω(t^{1/p})` is
  reduced, connected and finite — hence proper — over `Ω`, with one connected component and
  `dim_Ω Γ = p`. Geometric reducedness excludes exactly this, by making the factors *separable*
  over `Ω` ([Stacks, Tag 0BUG] (4)); a finite separable extension of a separably closed field is
  trivial.
* *Separably* closed is the right closedness hypothesis, and the statement for an algebraically
  closed `Ω` is the special case: over a perfect field reduced implies geometrically reduced
  (`AlgebraicGeometry.geometricallyReduced_of_isReduced`), so for `Ω` algebraically closed the
  hypothesis may be read as plain reducedness of `Z`.

**How the factors are shown to be `Ω`.** Not through the field decomposition of
[Stacks, Tag 0BUG] (3), whose index set is the maximal spectrum of `Γ(Z, 𝒪_Z)` and would have to
be matched up with the set of components. Instead the component decomposition is used as it
stands: `Γ(Z, 𝒪_Z)` is etale over `Ω`
(`Stacks.AlgebraicGeometry.ProperSectionsGeom.etale_globalSections_of_geometricallyReduced`,
clauses (1), (3) and (4) packaged together), formal etaleness passes to the factors of a finite
product (`Algebra.FormallyEtale.pi_iff`), and over a separably closed field an etale algebra is
the product of copies of the base indexed by its prime spectrum
(`Algebra.FormallyEtale.equivPiOfIsSepClosed`). A factor is Artinian and local, so it has exactly
one prime, and the product has one term.

## References

* [Stacks Project, Tag 0BUG](https://stacks.math.columbia.edu/tag/0BUG)
-/

@[expose] public noncomputable section

open AlgebraicGeometry CategoryTheory Opposite

universe u

namespace Stacks.AlgebraicGeometry.ProperSectionsGeom

/-- An Artinian local algebra, essentially of finite type and formally etale over a separably
closed field, is the field itself: it is the product of copies of the base indexed by its prime
spectrum, and an Artinian local ring has exactly one prime. -/
private theorem finrank_eq_one_of_formallyEtale (Ω : Type u) [Field Ω] [IsSepClosed Ω]
    (B : Type u) [CommRing B] [Algebra Ω B] [IsArtinianRing B] [IsLocalRing B]
    [Algebra.EssFiniteType Ω B] [Algebra.FormallyEtale Ω B] :
    Module.finrank Ω B = 1 := by
  have huniq : Unique (PrimeSpectrum B) :=
    { default := ⟨IsLocalRing.maximalIdeal B, (IsLocalRing.maximalIdeal.isMaximal B).isPrime⟩
      uniq := fun p => PrimeSpectrum.ext
        (IsLocalRing.eq_maximalIdeal (IsArtinianRing.isMaximal_of_isPrime p.asIdeal)) }
  rw [(Algebra.FormallyEtale.equivPiOfIsSepClosed Ω B).toLinearEquiv.finrank_eq,
    Module.finrank_pi]
  exact Fintype.card_eq_one_iff.mpr ⟨huniq.default, huniq.uniq⟩

variable (Ω : Type u) [Field Ω] {Z : Scheme.{u}} (q : Z ⟶ Spec (.of Ω))

/-- A proper scheme over a field has finitely many connected components, and its global functions
are the product, over them, of finite Artinian local `Ω`-algebras. -/
private theorem exists_pi_decomposition_globalSections [IsProper q] :
    letI : Algebra Ω Γ(Z, ⊤) := ((Scheme.ΓSpecIso (.of Ω)).inv ≫ q.appTop).hom.toAlgebra
    Finite (_root_.ConnectedComponents Z) ∧
    ∃ (A : _root_.ConnectedComponents Z → Type u) (_ : ∀ c, CommRing (A c))
      (_ : ∀ c, Algebra Ω (A c)), Nonempty (Γ(Z, ⊤) ≃ₐ[Ω] (∀ c, A c)) ∧
      (∀ c, Module.Finite Ω (A c)) ∧ (∀ c, IsArtinianRing (A c)) ∧ ∀ c, IsLocalRing (A c) := by
  let algTop : Algebra Ω Γ(Z, ⊤) := ((Scheme.ΓSpecIso (.of Ω)).inv ≫ q.appTop).hom.toAlgebra
  let D := componentwiseArtinianDecomposition Ω q
  let U : _root_.ConnectedComponents Z → Z.Opens := fun c =>
    connectedComponentOpen Z c (D.isOpen_component c)
  let algU : ∀ c, Algebra Ω Γ(Z, U c) := fun c =>
    (((Scheme.ΓSpecIso (.of Ω)).inv ≫ q.appTop) ≫
      Z.presheaf.map (homOfLE (le_top : U c ≤ ⊤)).op).hom.toAlgebra
  have hE : Γ(Z, ⊤) ≃ₐ[Ω] (∀ c, Γ(Z, U c)) := D.algEquiv
  have hfinTop : Module.Finite Ω Γ(Z, ⊤) := moduleFinite_globalSections_of_isProper Ω q
  have hfinPi : Module.Finite Ω (∀ c, Γ(Z, U c)) := Module.Finite.equiv hE.toLinearEquiv
  exact ⟨D.finite_connectedComponents, fun c => Γ(Z, U c), inferInstance, algU, ⟨hE⟩,
    fun c => Module.Finite.of_surjective
      (LinearMap.proj c : (∀ d, Γ(Z, U d)) →ₗ[Ω] Γ(Z, U c)) (LinearMap.proj_surjective c),
    D.isArtinianRing, D.isLocalRing⟩

/-- **A proper scheme over a field has at most `dim_k Γ(Z, 𝒪_Z)` connected components.** This is
all that properness alone gives: `Γ(Z, 𝒪_Z)` is the product of the rings of functions on the
connected components, each of which is a nonzero finite-dimensional `k`-vector space, so it
contributes at least one dimension — but possibly more, and then the count of components is a
count of the factors without their multiplicities.

Reducedness is not assumed, and the inequality is genuinely strict in general: a double point
`Spec k[x]/(x²)` is connected and proper over `k` with `dim_k Γ = 2`. -/
theorem card_connectedComponents_le_finrank_globalSections [IsProper q] :
    letI : Algebra Ω Γ(Z, ⊤) := ((Scheme.ΓSpecIso (.of Ω)).inv ≫ q.appTop).hom.toAlgebra
    Nat.card (_root_.ConnectedComponents Z) ≤ Module.finrank Ω Γ(Z, ⊤) := by
  let algTop : Algebra Ω Γ(Z, ⊤) := ((Scheme.ΓSpecIso (.of Ω)).inv ≫ q.appTop).hom.toAlgebra
  obtain ⟨hfin, A, _, _, ⟨hE⟩, hfinA, -, hloc⟩ := exists_pi_decomposition_globalSections Ω q
  let _ : Fintype (_root_.ConnectedComponents Z) := Fintype.ofFinite _
  calc Nat.card (_root_.ConnectedComponents Z)
      = ∑ _c : _root_.ConnectedComponents Z, 1 := by
        simp [Nat.card_eq_fintype_card]
    _ ≤ ∑ c, Module.finrank Ω (A c) := Finset.sum_le_sum fun c _ => by
        have := hfinA c
        have := (hloc c).toNontrivial
        exact Module.finrank_pos
    _ = Module.finrank Ω Γ(Z, ⊤) := by
      rw [hE.toLinearEquiv.finrank_eq, Module.finrank_pi_fintype Ω]

/-- **Over a separably closed field the dimension of the global functions on a proper
geometrically reduced scheme is its number of connected components.**

`Γ(Z, 𝒪_Z)` is the product of the rings of functions on the connected components of `Z`
([Stacks, Tag 0BUG] (1) and (2)), and geometric reducedness makes each factor a finite separable
extension of `Ω` ([Stacks, Tag 0BUG] (3) and (4)), hence `Ω` itself, `Ω` being separably closed.

Reducedness on its own is not enough over a merely separably closed field, and geometric
reducedness is not a convenience of the proof: `Spec Ω(t^{1/p})` for `Ω` the separable closure of
`𝔽_p(t)` is reduced, connected and proper over `Ω` with `dim_Ω Γ = p`. For `Ω` algebraically
closed the hypothesis is implied by reducedness of `Z`
(`AlgebraicGeometry.geometricallyReduced_of_isReduced`, an algebraically closed field being
perfect). Properness enters only through [Stacks, Tag 0BUG]; no dimension, irreducibility or
connectedness hypothesis is needed, and finiteness of the component count is part of the
conclusion rather than an assumption. -/
@[sga "1 IX 6.1" "special case",
  sga "4½ Arcata 2.2.2" "more general",
  sga "7 X 1.13" "H^0(Y, special case"]
theorem finrank_globalSections_eq_card_connectedComponents [IsSepClosed Ω] [IsProper q]
    [GeometricallyReduced q] :
    letI : Algebra Ω Γ(Z, ⊤) := ((Scheme.ΓSpecIso (.of Ω)).inv ≫ q.appTop).hom.toAlgebra
    Module.finrank Ω Γ(Z, ⊤) = Nat.card (_root_.ConnectedComponents Z) := by
  let algTop : Algebra Ω Γ(Z, ⊤) := ((Scheme.ΓSpecIso (.of Ω)).inv ≫ q.appTop).hom.toAlgebra
  obtain ⟨hfin, A, _, _, ⟨hE⟩, hfinA, hart, hloc⟩ := exists_pi_decomposition_globalSections Ω q
  let _ : Fintype (_root_.ConnectedComponents Z) := Fintype.ofFinite _
  obtain ⟨hetale, -⟩ := etale_globalSections_of_geometricallyReduced Ω q
  have hfe : ∀ c, Algebra.FormallyEtale Ω (A c) :=
    (Algebra.FormallyEtale.pi_iff _).mp (Algebra.FormallyEtale.of_equiv hE)
  have h3 : ∀ c, Module.finrank Ω (A c) = 1 := fun c => by
    have := hfinA c
    have := hart c
    have := hloc c
    have := hfe c
    have : Algebra.FiniteType Ω (A c) := Module.Finite.finiteType (A c)
    exact finrank_eq_one_of_formallyEtale Ω (A c)
  rw [hE.toLinearEquiv.finrank_eq, Module.finrank_pi_fintype Ω,
    Finset.sum_congr rfl fun c _ => h3 c]
  simp [Nat.card_eq_fintype_card]

/-- **`h⁰(Z, 𝒪_Z)` is the number of connected components of `Z`**, for `Z` proper and
geometrically reduced over a separably closed field `Ω`. This is
`finrank_globalSections_eq_card_connectedComponents` written with
`AlgebraicGeometry.structureSheafCohomology`, the degree-zero cohomology of the structure sheaf
that the genus of [Stacks, Tag 0BY7] is defined from, which is the shape the `h⁰` of a scheme over
a field is taken in elsewhere in the tree. -/
@[sga "7 X 1.13" "H^0(Y, special case"]
theorem finrank_structureSheafCohomology_zero_eq_card_connectedComponents [IsSepClosed Ω]
    [IsProper q] [GeometricallyReduced q] :
    Module.finrank Ω (structureSheafCohomology q 0) = Nat.card (_root_.ConnectedComponents Z) := by
  let algTop : Algebra Ω Γ(Z, ⊤) := ((Scheme.ΓSpecIso (.of Ω)).inv ≫ q.appTop).hom.toAlgebra
  rw [(structureSheafCohomologyIsoCohomologyOverField Ω q 0).toLinearEquiv.finrank_eq,
    finrank_cohomologyOverField_zero_unit_eq_finrank_globalSections Ω q]
  exact finrank_globalSections_eq_card_connectedComponents Ω q

end Stacks.AlgebraicGeometry.ProperSectionsGeom

end
