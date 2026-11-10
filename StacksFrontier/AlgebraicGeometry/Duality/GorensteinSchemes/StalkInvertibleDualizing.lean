module

public import StacksFrontier.AlgebraicGeometry.Duality.GorensteinSchemes.InvertibleDualizing
public import StacksFrontier.RingTheory.Dualizing.LocalCriterionInvertible
import all StacksFrontier.RingTheory.Dualizing.LocalCriterionInvertible

/-!
# Gorenstein local rings of a scheme and invertibility of the dualizing complex at a point

Let `X` be a locally Noetherian scheme carrying a dualizing complex `ω^•`. [Stacks, Tag 0BFQ]
clause (1)(b) says that the local ring `𝒪_{X,x}` is Gorenstein exactly when `ω^•_{X,x}` is an
invertible object of `D(𝒪_{X,x})`, and proves it by reducing to the affine case, which is
[Stacks, Tag 0DW9] clause (1)(b).

## Main results

* `Stacks.Duality.isGorensteinLocalRing_stalk_iff_isInvertible_localizedDualizing`: the local
  ring at a point of an affine open is Gorenstein iff the derived localization there of a
  dualizing complex over the sections of that open is invertible.
* `Stacks.Duality.isGorensteinLocalRing_stalk_iff_isInvertible_localizedDualizingModel`: the
  same equivalence with the complex being localized an affine-local model of a given dualizing
  complex on `X`.

## Implementation notes

**How `ω^•_{X,x}` is read.** At an affine open `U ∋ x` the definition of
`Stacks.Duality.IsDualizingComplex` presents `ω^•|_U` as the associated sheaf of a dualizing
complex `ω` over `Γ(X, U)`, and the local ring `𝒪_{X,x}` is the localization of `Γ(X, U)` at the
prime `AlgebraicGeometry.IsAffineOpen.primeIdealOf` attaches to `x`
(`AlgebraicGeometry.IsAffineOpen.isLocalization_stalk`). The stalk of the dualizing complex at `x`
is therefore read as the derived localization of that model at that prime, and the statements
below are the equivalence of Gorensteinness of `𝒪_{X,x}` with invertibility of that derived
localization in the derived category of `Localization.AtPrime (hU.primeIdealOf x).asIdeal`. This
is the same affine-local reading as in
`Stacks.Duality.isGorenstein_iff_isInvertible_dualizingModel` (clause (1)(a)).

**No derived comparison is used.** Unlike the fully geometric form of clause (1)(a) — that every
point has an affine open `V` with `ω^•|_V ≅ 𝒪_V[n]` — the statement at a point needs no
identification of `(ω^~)|_{D(f)}` with `(ω_f)^~`, the comparison of [Stacks, Tag 0A86]. Both sides
of clause (1)(b) are already affine-local data of the model: Gorensteinness of `𝒪_{X,x}` is
Gorensteinness of a localization of `Γ(X, U)`, transported along the comparison isomorphism of
rings by `Stacks.Duality.isGorensteinLocalRing_ringEquiv_iff`, and invertibility of `ω^•_{X,x}` is
invertibility of a derived localization of `ω`. Nothing has to be moved between `D(𝒪_U)` and
`D(Γ(X, U))`, so in the first statement below the isomorphism carried by
`Stacks.Duality.HasDualizingModelOn` does not appear at all, and in the second it is carried along
untouched.

**Why there are two statements.** The first quantifies over the dualizing complexes of
`Γ(X, U)` and states the equivalence for each of them, so it applies to the affine-local model of
any dualizing complex on `X` and needs no global complex. The second names a dualizing complex
`K` on `X` and asserts the existence of a model of `K` on `U` whose localization at `x` is
invertible, which is clause (1)(b) read for `K` itself; the two are interchangeable because
`Stacks.Duality.IsDualizingComplex` supplies a model of `K` at every affine open.

The monoidal structure is `Dualizing.derivedCategoryMonoidal`, the structure that
[Stacks, Tag 0DW9] clause (1)(b) is stated at; a derived category carries no ambient monoidal
structure, so it is introduced where it is needed. The derived category of `X.Modules` is an
instance *argument*, matching `Stacks.Duality.IsDualizingComplex`, so the results read at whatever
model the caller works in; the derived categories of the rings and of `U` that
`Stacks.Duality.HasDualizingModelOn` and the ring-level criterion
`Dualizing.isGorensteinLocalRing_iff_isInvertible_localization` choose at
`HasDerivedCategory.standard` are reintroduced by the instance-introducing `let`s below.

## References

* [Stacks Project, Tag 0A87](https://stacks.math.columbia.edu/tag/0A87)
* [Stacks Project, Tag 0BFQ](https://stacks.math.columbia.edu/tag/0BFQ)
* [Stacks Project, Tag 0DW9](https://stacks.math.columbia.edu/tag/0DW9)
* [Stacks Project, Tag 0FNQ](https://stacks.math.columbia.edu/tag/0FNQ)
-/

@[expose] public noncomputable section

open AlgebraicGeometry CategoryTheory

universe u w

namespace Stacks.Duality

variable {X : Scheme.{u}} [IsLocallyNoetherian X]

/-- Let `X` be a locally Noetherian scheme, `U` an affine open and `x` a point of `U`. For every
dualizing complex `ω` over `Γ(X, U)`, the local ring of `X` at `x` is Gorenstein exactly when the
derived localization of `ω` at the prime `x` defines is an invertible object of the derived
category of that localization. -/
@[stacks 0BFQ "(1)(b): the local ring at a point is Gorenstein iff the dualizing complex \
localized at that point is invertible, read at the affine-local models"]
public theorem isGorensteinLocalRing_stalk_iff_isInvertible_localizedDualizing
    {U : X.Opens} (hU : IsAffineOpen U) (x : U) :
    letI : IsNoetherianRing Γ(X, U) := IsLocallyNoetherian.component_noetherian ⟨U, hU⟩
    letI := HasDerivedCategory.standard (ModuleCat.{u} Γ(X, U))
    letI : (hU.primeIdealOf x).asIdeal.IsPrime := (hU.primeIdealOf x).isPrime
    letI := HasDerivedCategory.standard
      (ModuleCat.{u} (Localization.AtPrime (hU.primeIdealOf x).asIdeal))
    letI := Dualizing.derivedCategoryMonoidal.{u, u}
      (Localization.AtPrime (hU.primeIdealOf x).asIdeal)
    ∀ ω : DerivedCategory (ModuleCat.{u} Γ(X, U)), Dualizing.IsDualizingComplex ω →
      (Dualizing.IsGorensteinLocalRing (X.presheaf.stalk x.1) ↔
        MonoidalCategory.IsInvertible
          ((StacksDraft.PseudoCoherence.derivedExtensionScalars
              (algebraMap Γ(X, U)
                (Localization.AtPrime (hU.primeIdealOf x).asIdeal))).obj ω)) := by
  let : IsNoetherianRing Γ(X, U) := IsLocallyNoetherian.component_noetherian ⟨U, hU⟩
  let := HasDerivedCategory.standard (ModuleCat.{u} Γ(X, U))
  let : (hU.primeIdealOf x).asIdeal.IsPrime := (hU.primeIdealOf x).isPrime
  let := HasDerivedCategory.standard
    (ModuleCat.{u} (Localization.AtPrime (hU.primeIdealOf x).asIdeal))
  let := Dualizing.derivedCategoryMonoidal.{u, u}
    (Localization.AtPrime (hU.primeIdealOf x).asIdeal)
  have hstalk : Dualizing.IsGorensteinLocalRing (X.presheaf.stalk x.1) ↔
      Dualizing.IsGorensteinLocalRing
        (Localization.AtPrime (hU.primeIdealOf x).asIdeal) := by
    let : Algebra Γ(X, U) (X.presheaf.stalk x.1) :=
      X.presheaf.algebra_section_stalk ⟨x.1, x.2⟩
    let : IsLocalization.AtPrime (X.presheaf.stalk x.1) (hU.primeIdealOf x).asIdeal :=
      hU.isLocalization_stalk x
    exact isGorensteinLocalRing_ringEquiv_iff
      (IsLocalization.algEquiv (hU.primeIdealOf x).asIdeal.primeCompl
        (X.presheaf.stalk x.1)
        (Localization.AtPrime (hU.primeIdealOf x).asIdeal)).toRingEquiv
  intro ω hω
  exact hstalk.trans (Dualizing.isGorensteinLocalRing_iff_isInvertible_localization ω hω
    (hU.primeIdealOf x).asIdeal)

variable [HasDerivedCategory.{w} X.Modules]

/-- Let `K` be a dualizing complex on a locally Noetherian scheme `X`, and `x` a point of an
affine open `U`. The local ring of `X` at `x` is Gorenstein exactly when `K` has a dualizing model
on `U` whose derived localization at the prime of `x` is invertible. -/
@[stacks 0BFQ "(1)(b): the local ring at a point is Gorenstein iff the dualizing complex of the \
scheme, localized at that point, is invertible, read at the affine-local models"]
public theorem isGorensteinLocalRing_stalk_iff_isInvertible_localizedDualizingModel
    (K : DerivedCategory X.Modules) (hK : IsDualizingComplex K)
    {U : X.Opens} (hU : IsAffineOpen U) (x : U) :
    letI : IsNoetherianRing Γ(X, U) := IsLocallyNoetherian.component_noetherian ⟨U, hU⟩
    letI := HasDerivedCategory.standard U.toScheme.Modules
    letI := HasDerivedCategory.standard (ModuleCat.{u} Γ(X, U))
    letI : (hU.primeIdealOf x).asIdeal.IsPrime := (hU.primeIdealOf x).isPrime
    letI := HasDerivedCategory.standard
      (ModuleCat.{u} (Localization.AtPrime (hU.primeIdealOf x).asIdeal))
    letI := Dualizing.derivedCategoryMonoidal.{u, u}
      (Localization.AtPrime (hU.primeIdealOf x).asIdeal)
    Dualizing.IsGorensteinLocalRing (X.presheaf.stalk x.1) ↔
      ∃ ω : DerivedCategory (ModuleCat.{u} Γ(X, U)),
        Dualizing.IsDualizingComplex ω ∧
          Nonempty ((Scheme.Modules.restrictFunctor U.ι).mapDerivedCategory.obj K ≅
            (tilde.functor Γ(X, U) ⋙
              Scheme.Modules.restrictFunctor hU.isoSpec.hom).mapDerivedCategory.obj ω) ∧
            MonoidalCategory.IsInvertible
              ((StacksDraft.PseudoCoherence.derivedExtensionScalars
                  (algebraMap Γ(X, U)
                    (Localization.AtPrime (hU.primeIdealOf x).asIdeal))).obj ω) := by
  let : IsNoetherianRing Γ(X, U) := IsLocallyNoetherian.component_noetherian ⟨U, hU⟩
  let := HasDerivedCategory.standard U.toScheme.Modules
  let := HasDerivedCategory.standard (ModuleCat.{u} Γ(X, U))
  let : (hU.primeIdealOf x).asIdeal.IsPrime := (hU.primeIdealOf x).isPrime
  let := HasDerivedCategory.standard
    (ModuleCat.{u} (Localization.AtPrime (hU.primeIdealOf x).asIdeal))
  let := Dualizing.derivedCategoryMonoidal.{u, u}
    (Localization.AtPrime (hU.primeIdealOf x).asIdeal)
  constructor
  · intro hG
    obtain ⟨ω, hω, hiso⟩ := hK U hU
    exact ⟨ω, hω, hiso,
      (isGorensteinLocalRing_stalk_iff_isInvertible_localizedDualizing hU x ω hω).mp hG⟩
  · rintro ⟨ω, hω, -, hinv⟩
    exact (isGorensteinLocalRing_stalk_iff_isInvertible_localizedDualizing hU x ω hω).mpr hinv

end Stacks.Duality

end
