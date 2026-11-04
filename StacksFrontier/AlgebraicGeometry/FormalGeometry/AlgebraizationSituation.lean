module

public import Mathlib.AlgebraicGeometry.Morphisms.ClosedImmersion
public import StacksCore.Tactic.StacksAttribute

/-!
# The affine algebraization situation

The chapter on algebraic and formal geometry runs almost all of its arguments in a single
standing situation: a Noetherian commutative ring `A` together with a nested pair of ideals
`I ⊆ 𝔞`. From that data one forms the affine scheme `X = Spec(A)`, its two closed subschemes
`Y = V(I) = Spec(A/I)` and `Z = V(𝔞) = Spec(A/𝔞)`, and the open complement `U = X \ Z`. The
algebraization theorems of the chapter compare modules on `U`, on the formal completion of `X`
along `Y`, and on `X` itself, so every one of them needs this data fixed first.

This file bundles that data as `AlgebraizationSituation` and provides its canonical
constructions: the three schemes, the two closed-subscheme morphisms, and the open `U`.

## Main definitions

* `Stacks.Algebraization.AlgebraizationSituation` — a Noetherian ring with nested ideals
  `I ≤ 𝔞`.
* `Stacks.Algebraization.AlgebraizationSituation.X`, `Y`, `Z` — the three affine schemes
  `Spec(A)`, `Spec(A/I)` and `Spec(A/𝔞)`.
* `Stacks.Algebraization.AlgebraizationSituation.Yι`, `Zι` — the canonical closed-subscheme
  morphisms to `X`, together with their `IsClosedImmersion` instances.
* `Stacks.Algebraization.AlgebraizationSituation.U` — the open `X \ V(𝔞)`, as an element of
  `X.Opens`.

## Implementation notes

The closed subschemes `V(I)` and `V(𝔞)` are represented by the spectra of the quotient rings
with their canonical maps to `X`, rather than as subobjects of `X`; this is what makes the
closed immersions available from `IsClosedImmersion.spec_of_quotient_mk`. The open `U` is an
element of `X.Opens`, so the open subscheme it determines is `U.toScheme`.

The commutative-ring and Noetherian hypotheses are instance-implicit fields of the structure
and are registered as instances, so a section opening with `(S : AlgebraizationSituation)` has
`CommRing S.A` and `IsNoetherianRing S.A` available without further binders.

## References

* [Stacks Project, Tag 0EHC](https://stacks.math.columbia.edu/tag/0EHC)
-/

@[expose] public section

open AlgebraicGeometry

universe u

namespace Stacks.Algebraization

noncomputable section

/-- **Stacks Project, Tag 0EHC (standing data).** A Noetherian ring with nested ideals
`I ⊆ 𝔞`. -/
@[stacks 0EHC "the ring and ideals"]
public structure AlgebraizationSituation where
  /-- The Noetherian ring. -/
  A : Type u
  /-- The commutative-ring structure on `A`. -/
  [commRingA : CommRing A]
  /-- The Noetherian hypothesis on `A`. -/
  [noetherianA : IsNoetherianRing A]
  /-- The ideal defining `Y`. -/
  I : Ideal A
  /-- The larger ideal defining `Z`. -/
  a : Ideal A
  /-- The inclusion `I ⊆ 𝔞`. -/
  I_le_a : I ≤ a

attribute [instance] AlgebraizationSituation.commRingA AlgebraizationSituation.noetherianA

namespace AlgebraizationSituation

/-- **Stacks Project, Tag 0EHC (`X`).** The affine scheme `X = Spec(A)`. -/
@[stacks 0EHC "the scheme X"]
public abbrev X (S : AlgebraizationSituation) : Scheme := Spec (.of S.A)

/-- **Stacks Project, Tag 0EHC (`Y`).** The closed subscheme `Y = V(I) = Spec(A/I)`. -/
@[stacks 0EHC "the closed subscheme Y"]
public abbrev Y (S : AlgebraizationSituation) : Scheme := Spec (.of (S.A ⧸ S.I))

/-- **Stacks Project, Tag 0EHC (`Z`).** The closed subscheme `Z = V(𝔞) = Spec(A/𝔞)`. -/
@[stacks 0EHC "the closed subscheme Z"]
public abbrev Z (S : AlgebraizationSituation) : Scheme := Spec (.of (S.A ⧸ S.a))

/-- The canonical closed-subscheme morphism `Y ⟶ X`. -/
public def Yι (S : AlgebraizationSituation) : S.Y ⟶ S.X :=
  Spec.map (CommRingCat.ofHom (Ideal.Quotient.mk S.I))

/-- The canonical closed-subscheme morphism `Z ⟶ X`. -/
public def Zι (S : AlgebraizationSituation) : S.Z ⟶ S.X :=
  Spec.map (CommRingCat.ofHom (Ideal.Quotient.mk S.a))

/-- The canonical morphism `Yι : Y ⟶ X` is a closed immersion: `Y = V(I)` is a closed
subscheme of `X`. -/
public instance (S : AlgebraizationSituation) : IsClosedImmersion S.Yι := by
  change IsClosedImmersion (Spec.map (CommRingCat.ofHom (Ideal.Quotient.mk S.I)))
  exact IsClosedImmersion.spec_of_quotient_mk (R := CommRingCat.of S.A) S.I

/-- The canonical morphism `Zι : Z ⟶ X` is a closed immersion: `Z = V(𝔞)` is a closed
subscheme of `X`. -/
public instance (S : AlgebraizationSituation) : IsClosedImmersion S.Zι := by
  change IsClosedImmersion (Spec.map (CommRingCat.ofHom (Ideal.Quotient.mk S.a)))
  exact IsClosedImmersion.spec_of_quotient_mk (R := CommRingCat.of S.A) S.a

/-- **Stacks Project, Tag 0EHC (`U`).** The open subset `U = X \ Z`, namely the complement of
`V(𝔞)` in `Spec(A)`. -/
@[stacks 0EHC "the open complement U"]
public def U (S : AlgebraizationSituation) : S.X.Opens :=
  ⟨(PrimeSpectrum.zeroLocus (S.a : Set S.A))ᶜ,
    (PrimeSpectrum.isClosed_zeroLocus (S.a : Set S.A)).isOpen_compl⟩

end AlgebraizationSituation

end

end Stacks.Algebraization
