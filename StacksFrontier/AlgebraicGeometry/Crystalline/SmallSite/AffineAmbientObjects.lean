module

public import Mathlib.AlgebraicGeometry.Morphisms.Affine
public import StacksFrontier.AlgebraicGeometry.Crystalline.SmallSite.AffineCofinality

/-!
# The objects of the small crystalline site with affine ambient scheme

Fix a global crystalline situation `(p, (S, I, γ), X)`.  This file isolates the collection of
objects `(U, T, δ)` of the small crystalline site `Cris(X/S)` whose ambient divided power scheme
`T` is affine, and proves that it is closed under the operations the Čech criterion
`Stacks.CechSite.subsingleton_ext_of_cechCohomology_isZero` ([Stacks, Tag 03F9] with the morphism
universe of the site free) performs on a system of coverings: passing to a member of a covering by
restrictions to affine opens, and passing to the domain of a finite fibre product of such members
over the covered object.

The second closure property is where the mathematics sits.  By
`SmallSite.CrystallineThickening.leftIsoRestrictOpenIInf` the domain of a finite product, in
`Over A`, of restrictions `A|_{V a} ⟶ A` is the restriction of `A` to the intersection `⨅ a, V a`,
and the ambient scheme of a restriction to an open is that open subscheme.  So the statement is
that a finite intersection of affine opens of an affine scheme is affine, which is
`AlgebraicGeometry.IsAffineOpen.iInf`.

## Main definitions

Everything below lives in the namespace `Crystalline.GlobalCrystallineSituation.SmallSite`.

* `affineAmbientObjects` — the collection `B` of objects of `Cris(X/S)` with affine ambient
  scheme, in the shape `Stacks.CechSite.subsingleton_ext_of_cechCohomology_isZero` takes its
  collection of objects.
* `affineAmbientRestrictCoverings` — the system of coverings of the criterion: the coverings by
  restrictions to affine opens, `SmallSite.affineRestrictCoverings`, of an object belonging to
  `affineAmbientObjects`.

## Main results

* `affineAmbientObjects_of_iso` — membership of `affineAmbientObjects` is transported along an
  isomorphism of `Cris(X/S)`.
* `restrictOpen_mem_affineAmbientObjects` — a restriction to an affine open belongs to
  `affineAmbientObjects`.
* `left_pi_mem_affineAmbientObjects` — the domain of a finite fibre product of members of a
  covering by restrictions to affine opens of an object of `affineAmbientObjects` belongs to
  `affineAmbientObjects`.
* `affineAmbientRestrictCoverings_covObjects` — **the hypothesis `hCovObjects` of
  `Stacks.CechSite.subsingleton_ext_of_cechCohomology_isZero`**, stated verbatim, for the
  collection `affineAmbientObjects` and the system `affineAmbientRestrictCoverings`.
* `hasProduct_of_mem_affineAmbientRestrictCoverings` and
  `affineAmbientRestrictCoverings_cofinal` — the hypotheses `hProducts` and `hCovCofinal` of the
  same criterion for that system, inherited from `SmallSite.affineRestrictCoverings`.

## Implementation notes

The system of coverings is `SmallSite.affineRestrictCoverings` *restricted to the objects with
affine ambient scheme*, and not `affineRestrictCoverings` itself.  The restriction is forced: the
hypothesis `hCovObjects` of the criterion asks, of every object `A` admitting a covering in the
system, that `A` itself belong to the collection `B`, and it asks this with no hypothesis on `A`.
Since the affine opens of any scheme form a basis, `affineRestrictCoverings A` is nonempty for
every object `A` of `Cris(X/S)` — that is the content of
`SmallSite.affineRestrictCoverings_cofinal` — so `hCovObjects` for the unrestricted system would
assert that every object of `Cris(X/S)` has affine ambient scheme.  Cutting the system down to the
objects of `B` is in any case what a consumer needs: the remaining hypothesis of the criterion,
the vanishing of the higher Čech cohomology, is quantified over every covering in the system, and
is available only over an affine object.  The two hypotheses of the criterion that
`SmallSite.AffineCofinality` establishes survive the restriction unchanged — `hProducts` because
membership of the restricted system implies membership of `affineRestrictCoverings`, and
`hCovCofinal` because it is already stated only for objects of `B`.

Finiteness of the index of the intersection is load-bearing twice over, and in the second case it
is not merely a hypothesis of a lemma but the difference between two notions.
`AlgebraicGeometry.IsAffineOpen.iInf` needs `[Finite ι]` and, separately, `[Nonempty ι]`; and
`TopologicalSpace.Opens.coe_iInf`, which the identification of the product in
`SmallSite.CrystallineThickening.isLimit_restrictOpenFan` rests on, holds only for a finite family
— for an infinite family the infimum of a family of opens is the *interior* of the intersection,
not the intersection.  Both are supplied by the index `Fin (p + 1)` of the criterion, which is
finite and nonempty; neither generalises to an arbitrary family.

The separatedness condition of `AlgebraicGeometry.IsAffineOpen.iInf` is stated as
`[IsAffineHom (pullback.diagonal (terminal.from X))]`, affineness of the diagonal over the
terminal scheme.  For an affine `X` it is found by instance search, from
`AlgebraicGeometry.isAffineHom_of_isAffine` together with the affineness of a fibre product of
affine schemes, so no explicit bridge is needed.

The transfer of affineness of the ambient scheme along an isomorphism of `Cris(X/S)` goes through
the functor `Crystalline.GlobalCrystallineSituation.ambient` to schemes, precomposed with the
inclusion `Cris(X/S) ⥤ CRIS(X/S)`; the scheme-level statement is
`AlgebraicGeometry.IsAffine.of_isIso`.

## References

* [Stacks Project, Tag 07IG](https://stacks.math.columbia.edu/tag/07IG)
* [Stacks Project, Tag 03F9](https://stacks.math.columbia.edu/tag/03F9)
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry TopologicalSpace
open scoped AlgebraicGeometry

universe u

noncomputable section

namespace Crystalline.GlobalCrystallineSituation.SmallSite

variable {S : GlobalCrystallineSituation.{u}}

/-! ### The objects with affine ambient scheme -/

/-- **The objects of the small crystalline site `Cris(X/S)` whose ambient divided power scheme is
affine**, as a collection of objects in the shape
`Stacks.CechSite.subsingleton_ext_of_cechCohomology_isZero` takes its collection `B`.  No
condition is imposed on the thickened scheme `U` of an object `(U, T, δ)`; it is affine as soon as
`T` is, by `SmallSite.isAffineObject_of_isAffine`. -/
def affineAmbientObjects (S : GlobalCrystallineSituation.{u}) :
    Set (CrystallineThickening S) :=
  {A : CrystallineThickening S | IsAffine A.obj.thickening.target.scheme}

/-- Membership of `affineAmbientObjects` unfolds to affineness of the ambient divided power
scheme. -/
theorem mem_affineAmbientObjects_iff {A : CrystallineThickening S} :
    A ∈ affineAmbientObjects S ↔ IsAffine A.obj.thickening.target.scheme :=
  Iff.rfl

/-- **An object of `Cris(X/S)` isomorphic to one with affine ambient scheme has affine ambient
scheme.**  An isomorphism of `Cris(X/S)` induces one of the ambient schemes, through the functor
`ambient`, and affineness of a scheme is invariant under isomorphism. -/
theorem affineAmbientObjects_of_iso {A B : CrystallineThickening S} (e : A ≅ B)
    (hB : B ∈ affineAmbientObjects S) : A ∈ affineAmbientObjects S :=
  have : IsAffine B.obj.thickening.target.scheme := hB
  have e' : A.obj.thickening.target.scheme ≅ B.obj.thickening.target.scheme :=
    (CrystallineThickening.ι S ⋙ ambient S).mapIso e
  IsAffine.of_isIso e'.hom

/-- **The restriction of an object of `Cris(X/S)` to an affine open of its ambient scheme has
affine ambient scheme**, that ambient scheme being the open subscheme.  This is
`SmallSite.CrystallineThickening.isAffine_restrictOpen`, recorded as membership of
`affineAmbientObjects`. -/
theorem restrictOpen_mem_affineAmbientObjects (A : CrystallineThickening S)
    {V : A.obj.thickening.target.scheme.Opens} (hV : IsAffineOpen V) :
    A.restrictOpen V ∈ affineAmbientObjects S :=
  CrystallineThickening.isAffine_restrictOpen A hV

/-! ### Closure under the finite fibre products of a covering by affine opens -/

/-- **The domain of a finite fibre product of members of a covering by restrictions to affine
opens has affine ambient scheme**, provided the covered object does.  By
`SmallSite.CrystallineThickening.leftIsoRestrictOpenIInf` that domain is the restriction of the
covered object to the intersection of the opens involved, and a finite nonempty intersection of
affine opens of an affine scheme is affine by `AlgebraicGeometry.IsAffineOpen.iInf`.

This is the third clause of the hypothesis `hCovObjects` of
`Stacks.CechSite.subsingleton_ext_of_cechCohomology_isZero`, stated with the instance of
existence of the product that the criterion supplies it with. -/
theorem left_pi_mem_affineAmbientObjects {A : CrystallineThickening S}
    (hA : A ∈ affineAmbientObjects S)
    (E : { E : PreZeroHypercover.{u + 1} A // E.sieve₀ ∈ smallTopology S A })
    (hE : E ∈ affineRestrictCoverings A) (p : ℕ) (i : Fin (p + 1) → E.1.I₀) :
    letI : ∀ (q : ℕ) (j : Fin (q + 1) → E.1.I₀),
      HasProduct (fun a ↦ Over.mk (E.1.f (j a))) :=
      hasProduct_of_mem_affineRestrictCoverings E hE
    (∏ᶜ (fun a ↦ Over.mk (E.1.f (i a)))).left ∈ affineAmbientObjects S := by
  obtain ⟨E, hEcov⟩ := E
  obtain ⟨I, V, hVaff, hcov, hEeq⟩ := hE
  change E = A.restrictOpenCover V at hEeq
  subst hEeq
  have : IsAffine A.obj.thickening.target.scheme := hA
  have : HasProduct (fun a ↦ Over.mk (A.restrictOpenHom (V (i a)))) :=
    CrystallineThickening.hasProduct_restrictOpenHom A fun a ↦ V (i a)
  exact affineAmbientObjects_of_iso
    (CrystallineThickening.leftIsoRestrictOpenIInf A (fun a ↦ V (i a)) (limit.isLimit _))
    (restrictOpen_mem_affineAmbientObjects A (IsAffineOpen.iInf fun a ↦ hVaff (i a)))

/-! ### The system of coverings of the Čech criterion -/

/-- **The system of coverings of `Cris(X/S)` the Čech criterion is applied to**: for an object `A`
with affine ambient scheme, the coverings of `A` by restrictions to affine opens of that scheme,
and for any other object, nothing.

The cut to the objects of `affineAmbientObjects` is what the hypothesis `hCovObjects` of
`Stacks.CechSite.subsingleton_ext_of_cechCohomology_isZero` requires — it asks of every object
admitting a covering in the system that the object itself lie in the collection — and is also what
a consumer of the criterion needs, the vanishing of higher Čech cohomology being available only
over an affine object. -/
def affineAmbientRestrictCoverings (A : CrystallineThickening S) :
    Set { E : PreZeroHypercover.{u + 1} A // E.sieve₀ ∈ smallTopology S A } :=
  {E | A ∈ affineAmbientObjects S ∧ E ∈ affineRestrictCoverings A}

/-- **The iterated fibre products of a covering in `affineAmbientRestrictCoverings` exist.**  This
is the hypothesis `hProducts` of `Stacks.CechSite.subsingleton_ext_of_cechCohomology_isZero` for
that system, stated verbatim; it is inherited from
`SmallSite.hasProduct_of_mem_affineRestrictCoverings`. -/
theorem hasProduct_of_mem_affineAmbientRestrictCoverings {A : CrystallineThickening S}
    (E : { E : PreZeroHypercover.{u + 1} A // E.sieve₀ ∈ smallTopology S A })
    (hE : E ∈ affineAmbientRestrictCoverings A) (p : ℕ) (i : Fin (p + 1) → E.1.I₀) :
    HasProduct fun a ↦ Over.mk (E.1.f (i a)) :=
  hasProduct_of_mem_affineRestrictCoverings E hE.2 p i

/-- **The coverings in `affineAmbientRestrictCoverings` are cofinal over the objects with affine
ambient scheme**: every covering sieve of such an object is refined by one of them.  This is the
hypothesis `hCovCofinal` of `Stacks.CechSite.subsingleton_ext_of_cechCohomology_isZero` for that
system and the collection `affineAmbientObjects`, stated verbatim; it is
`SmallSite.affineRestrictCoverings_cofinal`, whose conclusion lands in the restricted system
because the object is assumed to belong to the collection. -/
theorem affineAmbientRestrictCoverings_cofinal (S : GlobalCrystallineSituation.{u}) :
    ∀ A ∈ affineAmbientObjects S, ∀ R ∈ smallTopology S A,
      ∃ E : { E : PreZeroHypercover.{u + 1} A // E.sieve₀ ∈ smallTopology S A },
        E ∈ affineAmbientRestrictCoverings A ∧ E.1.sieve₀ ≤ R := by
  intro A hA R hR
  obtain ⟨E, hE, hle⟩ := affineRestrictCoverings_cofinal S (affineAmbientObjects S) A hA R hR
  exact ⟨E, ⟨hA, hE⟩, hle⟩

/-- **The objects of a covering in `affineAmbientRestrictCoverings`, and the domains of the finite
fibre products of its members, have affine ambient scheme.**  This is the hypothesis
`hCovObjects` of `Stacks.CechSite.subsingleton_ext_of_cechCohomology_isZero` for the system
`affineAmbientRestrictCoverings` and the collection `affineAmbientObjects`, stated verbatim.

The first clause is membership of the covered object, which is part of membership of the system;
the second is `restrictOpen_mem_affineAmbientObjects`; the third is
`left_pi_mem_affineAmbientObjects`. -/
theorem affineAmbientRestrictCoverings_covObjects {A : CrystallineThickening S}
    (E : { E : PreZeroHypercover.{u + 1} A // E.sieve₀ ∈ smallTopology S A })
    (hE : E ∈ affineAmbientRestrictCoverings A) :
    A ∈ affineAmbientObjects S ∧ (∀ i, E.1.X i ∈ affineAmbientObjects S) ∧
      ∀ (p : ℕ) (i : Fin (p + 1) → E.1.I₀),
        letI : ∀ (q : ℕ) (j : Fin (q + 1) → E.1.I₀),
          HasProduct (fun a ↦ Over.mk (E.1.f (j a))) :=
          hasProduct_of_mem_affineAmbientRestrictCoverings E hE
        (∏ᶜ (fun a ↦ Over.mk (E.1.f (i a)))).left ∈ affineAmbientObjects S := by
  obtain ⟨hA, hEaff⟩ := hE
  refine ⟨hA, ?_, fun p i ↦ left_pi_mem_affineAmbientObjects hA E hEaff p i⟩
  obtain ⟨I, V, hVaff, -, hEeq⟩ := hEaff
  rw [hEeq]
  exact fun i ↦ restrictOpen_mem_affineAmbientObjects A (hVaff i)

end Crystalline.GlobalCrystallineSituation.SmallSite

end

end
