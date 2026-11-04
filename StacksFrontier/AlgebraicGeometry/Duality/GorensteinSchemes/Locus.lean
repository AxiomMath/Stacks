module

public import StacksFrontier.AlgebraicGeometry.Duality.GorensteinSchemes.Basic
public import StacksFrontier.AlgebraicGeometry.Duality.RelativeDualizing.DualizingComplexScheme
public import StacksFrontier.RingTheory.Dualizing.GorensteinOpenLocus
public import StacksFrontier.RingTheory.Dualizing.GorensteinTransport

/-!
# The Gorenstein locus of a scheme with a dualizing complex

On a locally Noetherian scheme carrying a dualizing complex, the points whose local ring is
Gorenstein form an open subset, and the open subscheme they carry is a Gorenstein scheme.

## Main definitions

* `Stacks.Duality.gorensteinLocus` — the Gorenstein locus as an open subset of the scheme.

## Main results

* `Stacks.Duality.isOpen_setOf_isGorensteinLocalRing` — the Gorenstein locus is open.
* `Stacks.Duality.isGorenstein_gorensteinLocus` — the Gorenstein locus is a Gorenstein scheme.
* `Stacks.Duality.exists_isOpen_isGorenstein` — **[Stacks, Tag 0BFQ], clause (1)(c)**: the two
  together.

## Implementation notes

Openness is purely ring-theoretic. At an affine open `U` a dualizing complex on `X` is, by the
definition of `Stacks.Duality.IsDualizingComplex`, the associated sheaf of a dualizing complex
over `Γ(X, U)`, so `Γ(X, U)` is a Noetherian ring *admitting* a dualizing complex and
`Dualizing.isOpen_gorensteinLocus` applies to it; only the existence of the model is used and the
isomorphism it carries is discarded. The resulting open subset of `Spec Γ(X, U)` is transported
back along the comparison map `U ⟶ Spec Γ(X, U)`, whose value at a point is by definition the
prime `AlgebraicGeometry.IsAffineOpen.primeIdealOf` produces, and the stalk at that point is the
localization at that prime by `AlgebraicGeometry.IsAffineOpen.isLocalization_stalk`.
Gorensteinness is moved across the comparison isomorphism of rings by
`Stacks.Duality.isGorensteinLocalRing_ringEquiv_iff`.

The derived category of `X.Modules` is an instance *argument*, matching
`Stacks.Duality.IsDualizingComplex`, so the results read at whatever model the caller works in.
The two derived categories that `Stacks.Duality.HasDualizingModelOn` chooses internally at
`HasDerivedCategory.standard` must be reintroduced by any proof that destructs it, which is what
the instance-introducing `let`s below do.

## References

* [Stacks Project, Tag 0A87](https://stacks.math.columbia.edu/tag/0A87)
* [Stacks Project, Tag 0BFQ](https://stacks.math.columbia.edu/tag/0BFQ)
* [Stacks Project, Tag 0DW9](https://stacks.math.columbia.edu/tag/0DW9)
-/

@[expose] public noncomputable section

open AlgebraicGeometry CategoryTheory

universe u w

namespace Stacks.Duality

variable {X : Scheme.{u}} [IsLocallyNoetherian X] [HasDerivedCategory.{w} X.Modules]

/-- At an affine open of a locally Noetherian scheme carrying a dualizing complex, the Gorenstein
locus of the ring of sections is open.

Only the *existence* of the dualizing model of `Stacks.Duality.HasDualizingModelOn` is used; the
isomorphism it carries is discarded. -/
private lemma isOpen_gorensteinLocus_sections {K : DerivedCategory X.Modules}
    (hK : IsDualizingComplex K) (U : X.Opens) (hU : IsAffineOpen U) [IsNoetherianRing Γ(X, U)] :
    IsOpen {p : PrimeSpectrum Γ(X, U) |
      Dualizing.IsGorensteinLocalRing (Localization.AtPrime p.asIdeal)} := by
  let := HasDerivedCategory.standard U.toScheme.Modules
  let := HasDerivedCategory.standard (ModuleCat.{u} Γ(X, U))
  obtain ⟨ω, hω, -⟩ := hK U hU
  exact Dualizing.isOpen_gorensteinLocus ω hω

/-- **The Gorenstein locus is open.** On a locally Noetherian scheme carrying a dualizing
complex, the set of points whose local ring is Gorenstein is open. This is the first half of
[Stacks, Tag 0BFQ], clause (1)(c); the clause is `Stacks.Duality.exists_isOpen_isGorenstein`. -/
public theorem isOpen_setOf_isGorensteinLocalRing (K : DerivedCategory X.Modules)
    (hK : IsDualizingComplex K) :
    IsOpen {x : X | Dualizing.IsGorensteinLocalRing (X.presheaf.stalk x)} := by
  rw [isOpen_iff_forall_mem_open]
  intro x hx
  obtain ⟨-, ⟨V, hV, rfl⟩, hxV, -⟩ :=
    X.isBasis_affineOpens.exists_subset_of_mem_open (Set.mem_univ x) isOpen_univ
  let : IsNoetherianRing Γ(X, V) := IsLocallyNoetherian.component_noetherian ⟨V, hV⟩
  -- The Gorenstein locus in `Spec Γ(X, V)`.
  set W : Set (PrimeSpectrum Γ(X, V)) :=
    {p : PrimeSpectrum Γ(X, V) |
      Dualizing.IsGorensteinLocalRing (Localization.AtPrime p.asIdeal)} with hWdef
  have hWopen : IsOpen W := isOpen_gorensteinLocus_sections hK V hV
  -- Gorensteinness of the stalk at a point of `V` is a statement about the prime it defines.
  have hstalk : ∀ y : V, Dualizing.IsGorensteinLocalRing (X.presheaf.stalk y.1) ↔
      hV.primeIdealOf y ∈ W := by
    intro y
    let : Algebra Γ(X, V) (X.presheaf.stalk y.1) :=
      X.presheaf.algebra_section_stalk ⟨y.1, y.2⟩
    let : (hV.primeIdealOf y).asIdeal.IsPrime := (hV.primeIdealOf y).isPrime
    let : IsLocalization.AtPrime (X.presheaf.stalk y.1) (hV.primeIdealOf y).asIdeal :=
      hV.isLocalization_stalk y
    exact isGorensteinLocalRing_ringEquiv_iff
      (IsLocalization.algEquiv (hV.primeIdealOf y).asIdeal.primeCompl
        (X.presheaf.stalk y.1)
        (Localization.AtPrime (hV.primeIdealOf y).asIdeal)).toRingEquiv
  -- Transport `W` back to an open subset of `V`, then to an open subset of `X`.
  have hpre : IsOpen (hV.isoSpec.hom.base ⁻¹' W) := hWopen.preimage hV.isoSpec.hom.base.hom.2
  refine ⟨Subtype.val '' (hV.isoSpec.hom.base ⁻¹' W), ?_, ?_, ?_⟩
  · rintro z ⟨y, hy, rfl⟩
    exact (hstalk y).mpr hy
  · exact V.2.isOpenMap_subtype_val _ hpre
  · exact ⟨⟨x, hxV⟩, (hstalk ⟨x, hxV⟩).mp hx, rfl⟩

/-- The Gorenstein locus of a locally Noetherian scheme carrying a dualizing complex, as an open
subset. -/
public def gorensteinLocus (K : DerivedCategory X.Modules) (hK : IsDualizingComplex K) :
    X.Opens :=
  ⟨{x : X | Dualizing.IsGorensteinLocalRing (X.presheaf.stalk x)},
    isOpen_setOf_isGorensteinLocalRing K hK⟩

/-- A point lies in the Gorenstein locus if and only if its local ring is Gorenstein. -/
@[simp]
public theorem mem_gorensteinLocus (K : DerivedCategory X.Modules) (hK : IsDualizingComplex K)
    (x : X) :
    x ∈ gorensteinLocus K hK ↔ Dualizing.IsGorensteinLocalRing (X.presheaf.stalk x) :=
  Iff.rfl

/-- **The Gorenstein locus is a Gorenstein scheme.** The open subscheme of points with
Gorenstein local ring is a Gorenstein scheme. This is the second half of [Stacks, Tag 0BFQ],
clause (1)(c); the clause is `Stacks.Duality.exists_isOpen_isGorenstein`. -/
public theorem isGorenstein_gorensteinLocus (K : DerivedCategory X.Modules)
    (hK : IsDualizingComplex K) :
    AlgebraicGeometry.IsGorenstein (gorensteinLocus K hK).toScheme := by
  refine { toIsLocallyNoetherian := inferInstance, isGorensteinLocalRing := fun x => ?_ }
  exact (isGorensteinLocalRing_ringEquiv_iff
    ((gorensteinLocus K hK).stalkIso x).commRingCatIsoToRingEquiv).mpr x.2

/-- **Stacks Project, Tag 0BFQ, clause (1)(c).** On a locally Noetherian scheme carrying a
dualizing complex, `U = {x ∈ X | 𝒪_{X,x} is Gorenstein}` is open and, as an open subscheme, is a
Gorenstein scheme. -/
@[stacks 0BFQ "(1)(c): the Gorenstein locus is an open Gorenstein subscheme"]
public theorem exists_isOpen_isGorenstein (K : DerivedCategory X.Modules)
    (hK : IsDualizingComplex K) :
    ∃ hU : IsOpen {x : X | Dualizing.IsGorensteinLocalRing (X.presheaf.stalk x)},
      AlgebraicGeometry.IsGorenstein (Scheme.Opens.toScheme (X := X) ⟨_, hU⟩) :=
  ⟨isOpen_setOf_isGorensteinLocalRing K hK, isGorenstein_gorensteinLocus K hK⟩

end Stacks.Duality

end
