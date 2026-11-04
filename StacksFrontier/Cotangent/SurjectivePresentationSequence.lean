module

public import Mathlib.RingTheory.Smooth.Basic
public import StacksCore.Tactic.StacksAttribute
public import StacksFrontier.Cotangent.HomologyZero
public import StacksFrontier.Cotangent.StandardResolutionOverPolynomialBase

/-!
# The four term exact sequence at a surjective polynomial presentation

Let `A → B` be a ring map and work on the site `C_{B/A}` of polynomial `A`-algebras augmented
to `B`. Stacks 09D5 singles out the full subcategory `C'_{B/A}` of those objects `α : P → B`
whose augmentation is *surjective*, and records that on `C'_{B/A}` there is an exact sequence of
sheaves

```
0 ⟶ H₁(L_{B/A}) ⟶ 𝒥/𝒥² --d--> Ω ⟶ H₀(L_{B/A}) ⟶ 0,
```

whose outer terms are *constant*. At an object `α : P → B` of `C'_{B/A}` the sheaf `𝒥/𝒥²` has
sections `J/J²` for `J = ker α` and the sheaf `Ω = Ω_{𝒪/A} ⊗_𝒪 B̲` has sections
`Ω_{P/A} ⊗_P B`; these are `Algebra.Extension.Cotangent` and
`Algebra.Extension.CotangentSpace` of the extension `P → B`, and `d` is
`Algebra.Extension.cotangentComplex`. This file proves the sequence exact at every such object,
proves that the two identifications of the outer terms are compatible with the morphisms of
`C'_{B/A}` — which is what makes `Ker(d)` and `Coker(d)` constant — and identifies the right-hand
term with the degree-zero homology of the cotangent complex of Tag 08PN.

## Main definitions

* `Stacks.Cotangent.selfExtensionHom`: the morphism of extensions `A[B] ⟶ P` sending the variable
  `b` to `P.σ b`, through which the canonical presentation `A[B] → B` maps to any extension.
* `Stacks.Cotangent.h1CotangentIncl`: the left-hand map `H₁(L_{B/A}) ⟶ J/J²` of the sequence.
* `Stacks.Cotangent.cokerCotangentComplexEquiv`: the right-hand identification
  `Coker(d) = Ω[B⁄A]`.
* `Stacks.Cotangent.cokerCotangentComplexIsoHomologyZero`: `Coker(d) = H₀(L_{B/A})`.

## Main results

* `Stacks.Cotangent.h1CotangentIncl_bijective`: for `P` a polynomial algebra over `A` the map
  `H₁(L_{B/A}) → P.H1Cotangent` is bijective, so the left-hand term of the sequence really is the
  presentation-independent `Algebra.H1Cotangent A B`.
* `Stacks.Cotangent.surjectivePresentation_exact`: **Stacks 09D5**, the sequence is exact.
* `Stacks.Cotangent.outerTerms_constant`: **Stacks 09D5**, both outer identifications commute
  with an arbitrary morphism of extensions, so `Ker(d)` and `Coker(d)` are constant on
  `C'_{B/A}`.

## Implementation notes

**Which clauses of 09D5 this covers, and which it does not.** The remark has five assertions.
The one formalized here is the exact sequence of sheaves on `C'_{B/A}` together with the
constancy of its outer terms. The other four — that the spectral sequence differential
`H₂(C_{B/A}, 𝒥/𝒥²) → H₀(C_{B/A}, Tor₁^𝒪(𝒥, B̲))` is an isomorphism, that `Ker(d)` and
`Coker(d)` have vanishing higher homology on `C_{B/A}`, that
`H_n(C_{B/A}, 𝒥/𝒥²) → H_n(L_{B/A})` is an isomorphism for `n ≥ 2`, and the resulting formula
`H₂(L_{B/A}) = H₀(C_{B/A}, Tor₁^𝒪(𝒥, B̲))` — all need the derived lower shriek of Tag 08PF on
sheaves of `𝒪`-modules, the Tor sheaves `Tor_q^𝒪(𝒥, B̲)` and the spectral sequence of
`𝒥 ⊗^L_𝒪 B̲` of Tag 08R7. None of those is in this library; see the implementation notes of
`StacksFrontier/Cotangent/PolynomialAlgebraSiteAugmentationIdeal.lean`, which records that of
Tag 08R7 only the augmentation and its ideal are available.

**A correction to the source.** The source writes the right-hand term of the sequence as
`H₂(L_{B/A})`; it is `H₀(L_{B/A})`, the cokernel of `d` being `Ω_{B/A}` by the agreement of the
cotangent complex with the naive cotangent complex that the source itself invokes. The corrected
form is what is proved here.

**The left-hand term.** `Algebra.H1Cotangent A B` is `H¹` of the naive cotangent complex of the
canonical presentation `A[B] → B`; Tag 08RB in degree `-1`, which would identify it with
`H₁(L_{B/A})` for the cotangent complex of Tag 08PN, is not in this library — see the final note
of `StacksFrontier/Cotangent/NaiveComparison.lean`. The right-hand term, by contrast, *is* tied to
Tag 08PN here, through Tag 08QF.

**No choice is made.** The left-hand map is not extracted from an existence statement: the
morphism of extensions `selfExtensionHom` is written down, as `MvPolynomial.aeval P.σ` for the
section `σ` that an `Algebra.Extension` carries, and `Algebra.Extension.H1Cotangent.map_eq` says
that the induced map on `H¹` does not depend on which morphism of extensions is used.

## References

* [Stacks Project, Tag 09D5](https://stacks.math.columbia.edu/tag/09D5)
* [Stacks Project, Tag 08R7](https://stacks.math.columbia.edu/tag/08R7)
* [Stacks Project, Tag 08RB](https://stacks.math.columbia.edu/tag/08RB)
* [Stacks Project, Tag 08QF](https://stacks.math.columbia.edu/tag/08QF)
-/

@[expose] public noncomputable section

open CategoryTheory TensorProduct

universe w u v

namespace Stacks.Cotangent

section Objectwise

variable {A : Type u} [CommRing A] {B : Type v} [CommRing B] [Algebra A B]

/-- The morphism of extensions from the canonical presentation `A[B] → B` to an arbitrary
extension `P → B`, sending the variable `X b` to `P.σ b`. -/
def selfExtensionHom (P : Algebra.Extension.{w} A B) :
    Algebra.Extension.Hom (Algebra.Generators.self A B).toExtension P where
  toRingHom := (MvPolynomial.aeval (R := A) P.σ : MvPolynomial B A →ₐ[A] P.Ring).toRingHom
  toRingHom_algebraMap x := (MvPolynomial.aeval (R := A) P.σ).commutes x
  algebraMap_toRingHom x := by
    have h : (IsScalarTower.toAlgHom A P.Ring B).comp
        (MvPolynomial.aeval (R := A) P.σ) = MvPolynomial.aeval (R := A) (id : B → B) :=
      MvPolynomial.algHom_ext fun b => by simp
    exact DFunLike.congr_fun h x

/-- The left-hand map `H₁(L_{B/A}) ⟶ J/J²` of the sequence of Stacks 09D5: the map on `H¹` of
the naive cotangent complex induced by `Stacks.Cotangent.selfExtensionHom`, followed by the
inclusion of `H¹` into `J/J²`. -/
def h1CotangentIncl (P : Algebra.Extension.{w} A B) :
    Algebra.H1Cotangent A B →ₗ[B] P.Cotangent :=
  P.h1Cotangentι ∘ₗ Algebra.Extension.H1Cotangent.map (selfExtensionHom P)

/-- For an extension whose ring is a polynomial algebra over `A`, the map on `H¹` induced by
`Stacks.Cotangent.selfExtensionHom` is bijective: both the canonical presentation and `P` are
formally smooth over `A`, and any morphism between formally smooth extensions induces an
isomorphism on `H¹`. -/
@[sga "6 0 4.4" "partial"]
theorem h1CotangentIncl_bijective (P : Algebra.Extension.{w} A B)
    (hP : Algebra.IsPolynomialAlgebra A P.Ring) :
    Function.Bijective (Algebra.Extension.H1Cotangent.map (selfExtensionHom P)) := by
  have : Algebra.FormallySmooth A P.Ring := hP.formallySmooth
  have : Algebra.FormallySmooth A (Algebra.Generators.self A B).toExtension.Ring :=
    inferInstanceAs (Algebra.FormallySmooth A (MvPolynomial B A))
  have hfun : ⇑(Algebra.Extension.H1Cotangent.map (selfExtensionHom P)) =
      Algebra.Extension.H1Cotangent.equivOfFormallySmooth
        (Algebra.Generators.self A B).toExtension P := funext fun x =>
    (Algebra.Extension.H1Cotangent.equivOfFormallySmooth_apply (selfExtensionHom P) x).symm
  rw [hfun]
  exact (Algebra.Extension.H1Cotangent.equivOfFormallySmooth _ P).bijective

/-- **Stacks 09D5**, the exact sequence of sheaves on `C'_{B/A}`, read at an object: for a
surjection `α : P → B` with `P` a polynomial algebra over `A` and `J = ker α`, the sequence

```
0 ⟶ H₁(L_{B/A}) ⟶ J/J² --d--> Ω_{P/A} ⊗_P B ⟶ Ω[B⁄A] ⟶ 0
```

is exact. The source writes the right-hand term as `H₂(L_{B/A})`, which is a slip for
`H₀(L_{B/A})`; that term is `Ω[B⁄A]`, and
`Stacks.Cotangent.cokerCotangentComplexIsoHomologyZero` identifies it with the degree-zero
homology of the cotangent complex of Tag 08PN. -/
@[stacks 09D5 "the exact sequence 0 → H₁(L_{B/A}) → J/J² → Ω → Ω_{B/A} → 0 at an object of \
C'_{B/A}"]
theorem surjectivePresentation_exact (P : Algebra.Extension.{w} A B)
    (hP : Algebra.IsPolynomialAlgebra A P.Ring) :
    Function.Injective (h1CotangentIncl P) ∧
      Function.Exact (h1CotangentIncl P) P.cotangentComplex ∧
        Function.Exact P.cotangentComplex P.toKaehler ∧
          Function.Surjective P.toKaehler :=
  ⟨P.h1Cotangentι_injective.comp (h1CotangentIncl_bijective P hP).1,
    (h1CotangentIncl_bijective P hP).2.comp_exact_iff_exact.mpr
      P.exact_hCotangentι_cotangentComplex,
    P.exact_cotangentComplex_toKaehler, P.toKaehler_surjective⟩

/-- **Stacks 09D5**, the outer terms of the sequence are the constant sheaves on `C'_{B/A}`:
for any morphism `f : P ⟶ P'` of extensions of `B` over `A`, the left-hand map
`H₁(L_{B/A}) ⟶ J/J²` is carried to the one of `P'` by `f`, and the right-hand map
`Ω_{P/A} ⊗_P B ⟶ Ω[B⁄A]` is the composite of `f` with the one of `P'`. Hence the identifications
`Ker(d) = H₁(L_{B/A})` and `Coker(d) = Ω[B⁄A]` of
`Stacks.Cotangent.surjectivePresentation_exact` do not depend on the object. -/
@[stacks 09D5 "Ker(d) and Coker(d) are the constant sheaves on C'_{B/A}"]
theorem outerTerms_constant {P P' : Algebra.Extension.{w} A B} (f : P.Hom P') :
    Algebra.Extension.Cotangent.map f ∘ₗ h1CotangentIncl P = h1CotangentIncl P' ∧
      P'.toKaehler ∘ₗ Algebra.Extension.CotangentSpace.map f = P.toKaehler := by
  constructor
  · ext y
    have h : Algebra.Extension.Cotangent.map f (P.h1Cotangentι
        (Algebra.Extension.H1Cotangent.map (selfExtensionHom P) y)) =
          P'.h1Cotangentι (Algebra.Extension.H1Cotangent.map f
            (Algebra.Extension.H1Cotangent.map (selfExtensionHom P) y)) :=
      DFunLike.congr_fun (Algebra.Extension.Cotangent.map_comp_h1Cotangentι f) _
    refine h.trans ?_
    rw [← Algebra.Extension.H1Cotangent.map_comp_apply,
      Algebra.Extension.H1Cotangent.map_eq (f.comp (selfExtensionHom P)) (selfExtensionHom P')]
    rfl
  · ext x
    simp

/-- The right-hand identification of the sequence of Stacks 09D5: the cokernel of
`d : J/J² → Ω_{P/A} ⊗_P B` is `Ω[B⁄A]`, because `Ω_{P/A} ⊗_P B → Ω[B⁄A]` is surjective with
kernel the image of `d`. -/
def cokerCotangentComplexEquiv (P : Algebra.Extension.{w} A B) :
    (P.CotangentSpace ⧸ LinearMap.range P.cotangentComplex) ≃ₗ[B] Ω[B⁄A] :=
  (Submodule.quotEquivOfEq _ _
      (LinearMap.exact_iff.mp P.exact_cotangentComplex_toKaehler).symm).trans
    (LinearMap.quotKerEquivOfSurjective _ P.toKaehler_surjective)

end Objectwise

section Site

variable (A : Type u) [CommRing A] (B : CommAlgCat.{max u v} A)

/-- **Stacks 09D5**, the right-hand term of the sequence is `H₀(L_{B/A})`: at an object
`α : P → B` of `C'_{B/A}` the cokernel of `d : J/J² → Ω_{P/A} ⊗_P B` is the degree-zero homology
of the cotangent complex of Tag 08PN, by Tag 08QF. -/
@[stacks 09D5 "Coker(d) = H₀(L_{B/A})"]
def cokerCotangentComplexIsoHomologyZero (P : Algebra.Extension.{max u v} A B) :
    ModuleCat.of (B : Type (max u v))
        (P.CotangentSpace ⧸ LinearMap.range P.cotangentComplex) ≅
      (CommAlgCat.cotangentComplex A B).homology 0 :=
  (cokerCotangentComplexEquiv P).toModuleIso ≪≫
    (CommAlgCat.cotangentComplex_homologyZeroIso A B).symm

end Site

end Stacks.Cotangent

end
