module

public import StacksFrontier.CategoryTheory.DifferentialObject
public import StacksCore.Algebra.Homology.ExactCouple.SpectralSequence

/-!
# The spectral sequence of a differential object with an injective endomorphism

Let `𝒜` be an abelian category, `(A, d)` a differential object of `𝒜` and `α : A → A` an
injective endomorphism of `A` commuting with `d`. Then `α` is a monomorphism of differential
objects, and its cokernel `A/αA` carries the induced differential, so that
`0 → (A, d) → (A, d) → (A/αA, d) → 0` is a short exact sequence of differential objects. Its
long exact homology sequence (Stacks 011Y) is an exact couple
`(H(A, d), H(A/αA, d), H(α), δ, H(π))`, whose spectral sequence (Stacks 011S) is
`(E_r, d_r)_{r ≥ 1}` with `E_1 = H(A/αA, d)`. Setting `E_0 = A/αA` and `d_0 = d`, so that
`E_1 = H(E_0, d_0)`, extends it to a spectral sequence `(E_r, d_r)_{r ≥ 0}`: the spectral
sequence associated to `(A, d, α)`.

## Main definitions

* `StacksDifferentialObject.quotientByEndo A α`: the differential object `(A/αA, d)`.
* `StacksDifferentialObject.shortExactSequenceOfEndo A α`: the short exact sequence
  `0 → (A, d) → (A, d) → (A/αA, d) → 0`.
* `StacksDifferentialObject.exactCoupleOfEndo A α`: the exact couple
  `(H(A, d), H(A/αA, d), H(α), δ, H(π))`.
* `StacksDifferentialObject.spectralSequenceOfEndo A α`: the spectral sequence
  `(E_r, d_r)_{r ≥ 0}` associated to `(A, d, α)`.

## Main results

* `StacksDifferentialObject.spectralSequenceOfEndoXZeroIso`,
  `StacksDifferentialObject.spectralSequenceOfEndo_d_zero`: `(E_0, d_0) = (A/αA, d)`.
* `StacksDifferentialObject.spectralSequenceOfEndoXSuccIso`,
  `StacksDifferentialObject.spectralSequenceOfEndo_d_succ`: `(E_{n+1}, d_{n+1})` is the
  `E`-object and differential of the `n`-th derived couple of the exact couple.

## Implementation notes

Injectivity of `α` is the hypothesis `Mono α.f` on the underlying morphism of `𝒜`.

## References

* [Stacks, Tag 011Z](https://stacks.math.columbia.edu/tag/011Z)
-/

@[expose] public section

namespace StacksDifferentialObject

open CategoryTheory Limits SpectralSequence

universe v u

variable {𝒜 : Type u} [Category.{v} 𝒜] [Abelian 𝒜] (A : StacksDifferentialObject 𝒜) (α : A ⟶ A)

/-- The quotient differential object `(A/αA, d)` of `(A, d)` by an endomorphism `α` commuting
with `d`: the cokernel of `α` with the differential induced by `d`. -/
@[simps]
noncomputable def quotientByEndo : StacksDifferentialObject 𝒜 where
  X := cokernel α.f
  d := cokernel.map α.f α.f A.d A.d α.comm
  d_sq := by
    ext
    simp [cokernel.map, reassoc_of% A.d_sq]

/-- The projection `(A, d) ⟶ (A/αA, d)`. -/
@[simps]
noncomputable def toQuotientByEndo : A ⟶ A.quotientByEndo α where
  f := cokernel.π α.f
  comm := cokernel.π_desc _ _ _

variable [Mono α.f]

/-- For an injective endomorphism `α` of `(A, d)`, the short exact sequence of differential
objects `0 → (A, d) → (A, d) → (A/αA, d) → 0`. -/
@[simps]
noncomputable def shortExactSequenceOfEndo : ShortExactSequence 𝒜 where
  A := A
  B := A
  C := A.quotientByEndo α
  f := α
  g := A.toQuotientByEndo α
  zero := cokernel.condition α.f
  shortExact := ShortComplex.ShortExact.mk' (ShortComplex.exact_cokernel α.f)
    (by dsimp; infer_instance)
    (show Epi (cokernel.π α.f) by infer_instance)

/-- The exact couple `(H(A, d), H(A/αA, d), H(α), δ, H(π))` given by the homology sequence
(Stacks 011Y) of `0 → (A, d) → (A, d) → (A/αA, d) → 0`. -/
@[simps]
noncomputable def exactCoupleOfEndo : ExactCouple 𝒜 where
  A := A.homology
  E := (A.quotientByEndo α).homology
  α := End.of (homologyMap α)
  f := (A.shortExactSequenceOfEndo α).δ
  g := homologyMap (A.toQuotientByEndo α)
  α_g := (A.shortExactSequenceOfEndo α).homologyMap₁_comp_homologyMap₂
  g_f := (A.shortExactSequenceOfEndo α).homologyMap₂_comp_δ
  f_α := (A.shortExactSequenceOfEndo α).δ_comp_homologyMap₁
  exact_α := (A.shortExactSequenceOfEndo α).toComplexes_shortExact.homology_exact₂ ()
  exact_g := (A.shortExactSequenceOfEndo α).toComplexes_shortExact.homology_exact₃ () () rfl
  exact_f := (A.shortExactSequenceOfEndo α).toComplexes_shortExact.homology_exact₁ () () rfl

/-- The objects of the spectral sequence of `(A, d, α)`: `E_0 = A/αA` and `E_{n+1} = E^{(n)}`,
the `E`-object of the `n`-th derived couple of `exactCoupleOfEndo A α`. -/
noncomputable def spectralSequenceOfEndoObj : ℕ → 𝒜
  | 0 => (A.quotientByEndo α).X
  | n + 1 => ((A.exactCoupleOfEndo α).derivedIter n).E

/-- The differentials of the spectral sequence of `(A, d, α)`: `d_0 = d` on `A/αA` and
`d_{n+1} = d^{(n)}`. -/
noncomputable def spectralSequenceOfEndoD :
    (n : ℕ) → A.spectralSequenceOfEndoObj α n ⟶ A.spectralSequenceOfEndoObj α n
  | 0 => (A.quotientByEndo α).d
  | n + 1 => ((A.exactCoupleOfEndo α).derivedIter n).d

/-- The differentials of the spectral sequence of `(A, d, α)` square to zero: `d_n ∘ d_n = 0`. -/
lemma spectralSequenceOfEndoD_comp_self (n : ℕ) :
    A.spectralSequenceOfEndoD α n ≫ A.spectralSequenceOfEndoD α n = 0 := by
  cases n with
  | zero => exact (A.quotientByEndo α).d_sq
  | succ n => exact ((A.exactCoupleOfEndo α).derivedIter n).d_comp_d

/-- The identifications `Ker d_n / Im d_n ≅ E_{n+1}`: for `n = 0` this is
`H(A/αA, d) = E^{(0)}`, and for `n + 1` it is `Ker d^{(n)}/Im d^{(n)} ≅ E^{(n+1)}`. -/
noncomputable def spectralSequenceOfEndoHomologyIso : (n : ℕ) →
    (ShortComplex.mk (A.spectralSequenceOfEndoD α n) (A.spectralSequenceOfEndoD α n)
      (A.spectralSequenceOfEndoD_comp_self α n)).homology ≅ A.spectralSequenceOfEndoObj α (n + 1)
  | 0 => Iso.refl _
  | n + 1 => (A.exactCoupleOfEndo α).derivedIterSuccIso n

/-- The spectral sequence `(E_r, d_r)_{r ≥ 0}` associated to a differential object `(A, d)`
and an injective endomorphism `α` commuting with `d`: `(E_0, d_0) = (A/αA, d)`, and for `r ≥ 1`
it is the spectral sequence of the exact couple `(H(A, d), H(A/αA, d), H(α), δ, H(π))`, so
`E_1 = H(A/αA, d)`. -/
@[stacks 011Z]
noncomputable abbrev spectralSequenceOfEndo : Ungraded 𝒜 0 :=
  Ungraded.ofNat 0 (A.spectralSequenceOfEndoObj α) (A.spectralSequenceOfEndoD α)
    (A.spectralSequenceOfEndoD_comp_self α) (A.spectralSequenceOfEndoHomologyIso α)

/-- `E_0 ≅ A/αA`. -/
noncomputable def spectralSequenceOfEndoXZeroIso :
    (A.spectralSequenceOfEndo α).X 0 ≅ (A.quotientByEndo α).X :=
  Ungraded.ofNatPageXIso _ _ _ _ _ 0 le_rfl 0 rfl

/-- `d_0 = d` under `E_0 ≅ A/αA`. -/
lemma spectralSequenceOfEndo_d_zero :
    (A.spectralSequenceOfEndo α).d 0 ≫ (A.spectralSequenceOfEndoXZeroIso α).hom =
      (A.spectralSequenceOfEndoXZeroIso α).hom ≫ (A.quotientByEndo α).d :=
  Ungraded.ofNat_d_ofNatPageXIso_hom _ _ _ _ _ 0 le_rfl 0 rfl

/-- `E_{n+1} ≅ E^{(n)}`, the `E`-object of the `n`-th derived couple of
`exactCoupleOfEndo A α`. -/
noncomputable def spectralSequenceOfEndoXSuccIso (n : ℕ) :
    (A.spectralSequenceOfEndo α).X (n + 1) ≅ ((A.exactCoupleOfEndo α).derivedIter n).E :=
  Ungraded.ofNatPageXIso _ _ _ _ _ (n + 1) (by omega) (n + 1) (by omega)

/-- `d_{n+1} = d^{(n)}` under `E_{n+1} ≅ E^{(n)}`. -/
lemma spectralSequenceOfEndo_d_succ (n : ℕ) :
    (A.spectralSequenceOfEndo α).d (n + 1) ≫ (A.spectralSequenceOfEndoXSuccIso α n).hom =
      (A.spectralSequenceOfEndoXSuccIso α n).hom ≫ ((A.exactCoupleOfEndo α).derivedIter n).d :=
  Ungraded.ofNat_d_ofNatPageXIso_hom _ _ _ _ _ (n + 1) (by omega) (n + 1) (by omega)

end StacksDifferentialObject
