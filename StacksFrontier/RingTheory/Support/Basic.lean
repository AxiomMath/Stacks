module

public import Mathlib.Algebra.Module.LocalizedModule.Basic
public import Mathlib.Algebra.Order.Floor.Extended
public import Mathlib.Algebra.Order.Interval.Basic
public import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
public import Mathlib.Analysis.SpecialFunctions.Bernstein
public import Mathlib.Analysis.SpecialFunctions.Gamma.Basic
public import Mathlib.Analysis.SpecialFunctions.Trigonometric.DerivHyp
public import Mathlib.Combinatorics.Enumerative.DyckWord
public import Mathlib.Combinatorics.SimpleGraph.Triangle.Removal
public import Mathlib.Data.NNRat.Floor
public import Mathlib.Data.Nat.Choose.Multinomial
public import Mathlib.Geometry.Euclidean.Altitude
public import Mathlib.NumberTheory.Chebyshev
public import Mathlib.NumberTheory.Height.NumberField
public import Mathlib.NumberTheory.Height.Projectivization
public import Mathlib.NumberTheory.LucasLehmer
public import Mathlib.NumberTheory.SelbergSieve
public import Mathlib.Order.CompletePartialOrder
public import Mathlib.RingTheory.Henselian
public import Mathlib.RingTheory.Radical.NatInt
public import Mathlib.RingTheory.RegularLocalRing.Defs
public import Mathlib.RingTheory.SimpleRing.Principal
public import Mathlib.RingTheory.Spectrum.Prime.Basic
public import Mathlib.RingTheory.Spectrum.Prime.Module
public import Mathlib.Tactic.Echelon.Zsqrtd
public import Mathlib.Tactic.NormNum.Irrational
public import Mathlib.Tactic.NormNum.IsCoprime
public import Mathlib.Tactic.NormNum.IsSquare
public import Mathlib.Tactic.NormNum.LegendreSymbol
public import Mathlib.Tactic.NormNum.ModEq
public import Mathlib.Tactic.NormNum.NatFib
public import Mathlib.Tactic.NormNum.NatLog
public import Mathlib.Tactic.NormNum.NatSqrt
public import Mathlib.Tactic.NormNum.Ordinal
public import Mathlib.Tactic.NormNum.Parity
public import Mathlib.Tactic.NormNum.Prime
public import Mathlib.Tactic.NormNum.RealSqrt
public import Mathlib.Topology.Sheaves.Init
import StacksCore.Tactic.StacksAttribute
import StacksCore.Tactic.EgaSgaAttribute

/-!
# The support of a base change of a finite module

Let `R → S` be a ring map and let `M` be a finite `R`-module. Then the support of the base
change of `M` to `S` is the inverse image of `Supp(M)` under the induced map
`Spec(S) → Spec(R)`: a prime `𝔮 ⊆ S` lies in `Supp_S(S ⊗_R M)` if and only if the prime of `R`
it lies over lies in `Supp_R(M)`.

Both inclusions are read off from a description of the support of a finite module. For `⊆`, the
support is the set of primes containing the annihilator, and `Ann_R(M)` is carried into
`Ann_S(N)` — for which no finiteness is needed. For `⊇`, finiteness enters through Nakayama's
lemma, in the form that `𝔭 ∈ Supp_R(M)` if and only if `M ⊗_R κ(𝔭) = M_𝔭 / 𝔭 M_𝔭` is a nonzero
`κ(𝔭)`-vector space: the fibre `(S ⊗_R M) ⊗_S κ(𝔮)` is `(M ⊗_R κ(𝔭)) ⊗_{κ(𝔭)} κ(𝔮)`, and the
field extension `κ(𝔭) → κ(𝔮)` is faithfully flat, so it is nonzero for every `𝔮` over `𝔭`.

## Main results

* `IsBaseChange.annihilator_le_comap_annihilator`: the annihilator of `M` is carried into the
  annihilator of a base change of `M`, that is `Ann_R(M) S ≤ Ann_S(N)`. For `N = S ⊗_R M` with
  `M` finite and `S` flat over `R` this inclusion is an equality (Stacks 07T8); the inclusion
  itself needs neither hypothesis.
* `IsBaseChange.support_eq_preimage_comap`: the support of a base change of a finite module is
  the inverse image of the support.
* `support_isClosed_and_compl_isCompact_of_finitePresentation`: the support of a finitely
  presented module with finitely generated annihilator is closed with quasi-compact complement.

## Implementation notes

The base change is taken abstractly: `N` is any `S`-module admitting an `R`-linear
`f : M →ₗ[R] N` with `IsBaseChange S f`, rather than the construction `S ⊗[R] M`. Besides the
source's statement for that construction (`TensorProduct.isBaseChange` is the instance), this
covers with no extra work the base changes a reader meets already presented — `M ⧸ I M` along
`R → R ⧸ I`, or a localization `M_f` along `R → R_f`.

The name mutates `Module.support_subset_preimage_comap`, which for an arbitrary scalar tower
`R → S` bounds `Supp_S(N)` by the inverse image of `Supp_R(N)`: the same module with its two
structures, hence a different set from the one here. Passing from `Supp_R(N)` to `Supp_R(M)` is
the content of the statement below, and is where the base change hypothesis and, for `⊇`,
finiteness enter.

The elementary theory of the support — the definition itself (Stacks 00L1), its description as
the zero locus of the annihilator for a finite module and the resulting closedness (00L2), its
behaviour in short exact sequences (00L3), and the vanishing criterion (0585) — lives in
Mathlib's `Mathlib/RingTheory/Support.lean`. Only the `add_to_stacks` / `add_to_ega` pointers
to those declarations are recorded here.

## References

* [StackProject 0BUR](https://stacks.math.columbia.edu/tag/0BUR)
-/

@[expose] public section

open TensorProduct

namespace PrimeSpectrum

/-- The fibre of `S ⊗_R M` at a prime `𝔮 ⊆ S` is the fibre of `M` at `𝔭 = 𝔮 ∩ R` extended along
the residue field extension `κ(𝔭) → κ(𝔮)`; being a field extension it is faithfully flat, so the
fibre at `𝔮` is nonzero as soon as the fibre at `𝔭` is. -/
theorem nontrivial_residueField_tensorProduct_baseChange {R S M : Type*} [CommRing R]
    [CommRing S] [Algebra R S] [AddCommGroup M] [Module R M] {p : PrimeSpectrum R}
    (q : PrimeSpectrum S) (hpq : p.asIdeal = q.asIdeal.comap (algebraMap R S))
    [Nontrivial (p.asIdeal.ResidueField ⊗[R] M)] :
    Nontrivial (q.asIdeal.ResidueField ⊗[S] (S ⊗[R] M)) := by
  let φ := Ideal.ResidueField.mapₐ (R := R) p.asIdeal q.asIdeal (Algebra.ofId R S) hpq
  let _ : Algebra p.asIdeal.ResidueField q.asIdeal.ResidueField := φ.toRingHom.toAlgebra
  have : IsScalarTower R p.asIdeal.ResidueField q.asIdeal.ResidueField := .of_algHom φ
  rw [(AlgebraTensorModule.cancelBaseChange R S q.asIdeal.ResidueField
        q.asIdeal.ResidueField M).toEquiv.nontrivial_congr,
    ← (AlgebraTensorModule.cancelBaseChange R p.asIdeal.ResidueField q.asIdeal.ResidueField
        q.asIdeal.ResidueField M).toEquiv.nontrivial_congr]
  infer_instance

end PrimeSpectrum

namespace IsBaseChange

/-- The annihilator of `M` is carried into the annihilator of any base change of `M`: if
`f : M →ₗ[R] N` exhibits `N` as `S ⊗_R M`, then every `a ∈ Ann_R(M)` has
`algebraMap R S a ∈ Ann_S(N)`. -/
theorem annihilator_le_comap_annihilator {R S M N : Type*} [CommRing R] [CommRing S]
    [Algebra R S] [AddCommGroup M] [Module R M] [AddCommGroup N] [Module R N] [Module S N]
    [IsScalarTower R S N] {f : M →ₗ[R] N} (h : IsBaseChange S f) :
    Module.annihilator R M ≤ (Module.annihilator S N).comap (algebraMap R S) := fun a ha =>
  have H : LinearMap.lsmul S N (algebraMap R S a) = 0 :=
    h.algHom_ext _ _ fun m => by simp [← map_smul, Module.mem_annihilator.mp ha]
  Module.mem_annihilator.mpr fun n => congr($H n)

/-- **Stacks 0BUR**. Let `R → S` be a ring map, let `M` be a finite `R`-module and let
`f : M →ₗ[R] N` exhibit the `S`-module `N` as the base change `S ⊗_R M`. Then `Supp_S(N)` is the
inverse image of `Supp_R(M)` under the map `Spec(S) → Spec(R)` induced by `R → S`. -/
@[stacks 0BUR]
theorem support_eq_preimage_comap {R S M N : Type*} [CommRing R] [CommRing S]
    [Algebra R S] [AddCommGroup M] [Module R M] [Module.Finite R M] [AddCommGroup N]
    [Module R N] [Module S N] [IsScalarTower R S N] {f : M →ₗ[R] N} (h : IsBaseChange S f) :
    Module.support S N = PrimeSpectrum.comap (algebraMap R S) ⁻¹' Module.support R M := by
  have : Module.Finite S N := .equiv h.equiv
  refine subset_antisymm (fun q hq => ?_) ?_
  · simp only [Set.mem_preimage, Module.mem_support_iff_of_finite,
      PrimeSpectrum.comap_asIdeal] at hq ⊢
    exact h.annihilator_le_comap_annihilator.trans (Ideal.comap_mono hq)
  · rw [← h.equiv.support_eq]
    intro q hq
    simp only [Set.mem_preimage,
      Module.mem_support_iff_nontrivial_residueField_tensorProduct] at hq ⊢
    exact PrimeSpectrum.nontrivial_residueField_tensorProduct_baseChange q
      (PrimeSpectrum.comap_asIdeal _ q)

end IsBaseChange

end

@[expose] public section

-- Mathlib's `Module.support` already carries `@[stacks 00L1]`; the former local alias
-- `moduleSupport` was definitionally equal to it, and `Module.mem_support_iff` is the
-- membership criterion.
add_to_ega "0 1.7.1" "definition of Supp(M)" Module.support
add_to_sga "2 III 1.1" "the Supp M clause" Module.support

-- Mathlib's `Module.support_eq_zeroLocus` already carries `@[stacks 00L2]`; the closedness
-- half of the tag is `Module.isClosed_support`.
add_to_ega "0 1.7.4" Module.support_eq_zeroLocus
add_to_stacks 00L2 "the support of a finite module is closed" Module.isClosed_support
add_to_sga "3 VIA 2.1.3" "special case" Module.isClosed_support
add_to_ega "0 16.1.7" "partial" Module.isClosed_support
add_to_ega "0 5.2.2" "special case" Module.isClosed_support
add_to_ega "I 4.1.2" "affine case" Module.isClosed_support
add_to_ega "IV 5.1.12" "special case" Module.isClosed_support
add_to_ega "IV 8.9.1" "closedness of Supp(F)" Module.isClosed_support

-- Mathlib's `Module.support_quotient`, `Module.support_subset_of_injective`,
-- `Module.support_subset_of_surjective` and `Module.support_of_exact` already carry the four
-- clauses of `@[stacks 00L3]`.
add_to_ega "0 1.7.2" Module.support_of_exact

-- Mathlib's `Module.support_eq_empty_iff` is the vanishing criterion of Stacks 0585.
add_to_stacks 0585 Module.support_eq_empty_iff
add_to_ega "0 1.7.1" "M = 0 ⇔ Supp M = ∅" Module.support_eq_empty_iff

end

@[expose] public section


/-- The support of a submodule is contained in the support of the ambient module. -/
@[stacks 00L3 "(2)", ega "0 1.7.2" "partial"]
theorem support_submodule_subset
    {R : Type*} {M : Type*} [CommRing R] [AddCommGroup M] [Module R M]
    (N : Submodule R M) :
    Module.support R N ⊆ Module.support R M :=
  Module.support_subset_of_injective N.subtype Subtype.val_injective

end

@[expose] public section


open PrimeSpectrum

variable {R : Type*} [CommRing R] (M : Type*) [AddCommGroup M] [Module R M]

/--
If the support of a module equals the zero locus of some finitely generated ideal `I`, then
the support is closed in `Spec R` and its complement is quasi-compact. -/
lemma support_isClosed_and_compl_isCompact_of_eq_zeroLocus_FG
    {I : Ideal R} (hI : I.FG)
    (hsupp : Module.support R M = zeroLocus (I : Set R)) :
    IsClosed (Module.support R M) ∧ IsCompact (Module.support R M)ᶜ := by
  have hClosed : IsClosed (Module.support R M) := by
    rw [hsupp]; exact isClosed_zeroLocus _
  exact ⟨hClosed, (isCompact_isOpen_iff_ideal.mpr ⟨I, hI, by rw [hsupp]⟩).left⟩

/--
The support of a finitely presented module whose annihilator is finitely generated is closed
with quasi-compact complement.

The argument factors as: for a finite module `M`, `Supp M = V(Ann M)`; and
closed-with-quasi-compact-complement is a topological consequence of being `V(I)` for `I`
finitely generated. The statement for every finitely presented module, with no hypothesis on
the annihilator, is `isClosed_support_and_isCompact_compl_support`, which uses the zeroth
Fitting ideal in place of the annihilator.
-/
@[ega "0 16.1.7" "special case",
  ega "0 5.2.2" "special case"]
theorem support_isClosed_and_compl_isCompact_of_finitePresentation
    [Module.FinitePresentation R M]
    (hAnn : (Module.annihilator R M).FG) :
    IsClosed (Module.support R M) ∧ IsCompact (Module.support R M)ᶜ :=
  support_isClosed_and_compl_isCompact_of_eq_zeroLocus_FG M hAnn
    Module.support_eq_zeroLocus

end

@[expose] public section

open PrimeSpectrum in
/-- A prime `p` lies in the zero locus of the annihilator of `R ∙ m` exactly when the image of
`m` in the localization `M_p` is nonzero. -/
@[ega "0 1.7.1" "partial", ega "0 1.7.4" "more general"]
theorem mem_zeroLocus_annihilator_iff_localization_ne_zero {R M : Type*} [CommSemiring R]
    [AddCommMonoid M] [Module R M] (m : M) (p : PrimeSpectrum R) :
    p ∈ zeroLocus ((R ∙ m).annihilator : Set R) ↔
      LocalizedModule.mkLinearMap p.asIdeal.primeCompl M m ≠ 0 := by
  rw [mem_zeroLocus, ne_eq, IsLocalizedModule.eq_zero_iff p.asIdeal.primeCompl]
  exact ⟨fun hp ⟨⟨s, hs⟩, hsm⟩ ↦
      hs (hp ((Submodule.mem_annihilator_span_singleton _ _).mpr hsm)),
    fun hne r hr ↦ not_not.mp fun hrp ↦
      hne ⟨⟨r, hrp⟩, (Submodule.mem_annihilator_span_singleton _ _).mp hr⟩⟩

end

add_to_ega "I 10.8.12" "affine case, M finite" Module.support_quotient
