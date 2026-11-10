module

public import StacksFrontier.AlgebraicGeometry.Chow.DvrTameSymbol.MilnorTameSymbol
public import StacksFrontier.RingTheory.IntegralClosure.OneDimensionalLocalDomain

/-!
# The tame symbol of a one-dimensional Noetherian local domain, in every degree

Let `A` be a Noetherian local domain of dimension one with fraction field `F` and residue field
`κ`. Stacks 0EAY extends the tame symbol `∂ : K^M_{i+1}(F) → K^M_i(κ)` of a discrete valuation
ring to such an `A` "using normalization and norm maps on `K_i^M`" (Kato): the normalization `A'`
of `A` in `F` is a semi-local Dedekind domain whose local rings `A'_𝔫` at its maximal ideals are
discrete valuation rings with fraction field `F` and residue fields finite over `κ`
(Krull–Akizuki, `Stacks.Normalization.semilocalDvrFamily`), and

`∂_A = ∑_{𝔫 ∈ MaxSpec A'} N_{κ(𝔫)/κ} ∘ ∂_{A'_𝔫}`.

This file carries that recipe out over any finite family of discrete valuation rings with
fraction field `F` and finite residue extensions over `κ`
(`Stacks.Normalization.SemilocalDvrFamily`), for a family `N` of additive maps
`K^M_*(L) → K^M_*(K)` indexed by the finite field extensions `L/K`, and then specializes the
family to the normalization.

## Main definitions

* `Stacks.Chow.MilnorKNormFamily` — the shape of the norm maps: one additive map
  `K^M_*(L) → K^M_*(K)` for each finite extension `L/K`.
* `Stacks.Normalization.SemilocalDvrFamily.tameShiftAt`,
  `Stacks.Normalization.SemilocalDvrFamily.tameShift` — `N_{κ(A_m)/κ} ∘ ∂_{A_m}` and their sum,
  on the whole Milnor K-ring.
* `Stacks.Normalization.SemilocalDvrFamily.tameSymbol` — the same, from degree `i + 1` to degree
  `i`.
* `Stacks.Chow.normalizationDvrFamily` — the family cut out by the normalization of a
  one-dimensional Noetherian local domain.

## Main results

* `Stacks.Normalization.SemilocalDvrFamily.tameShift_milnorKSymbolProd_eq_zero` — the symbol
  kills a symbol `{u_1, …, u_r}` of units of `A`, in every degree.

## References

* [Stacks Project, Tag 0EAY](https://stacks.math.columbia.edu/tag/0EAY)
-/

@[expose] public noncomputable section

open IsLocalRing IsDiscreteValuationRing

universe u

namespace Stacks.Chow

/-- **The shape of the norm maps of Milnor K-theory**: an additive map `K^M_*(L) → K^M_*(K)` for
every finite extension of fields `L/K` in the universe `u`. -/
abbrev MilnorKNormFamily : Type (u + 1) :=
  ∀ (K L : Type u) [Field K] [Field L] [Algebra K L] [FiniteDimensional K L],
    MilnorKRing L →+ MilnorKRing K

/-- A family of norm maps preserves the degree. -/
def MilnorKNormFamily.PreservesGrading (N : MilnorKNormFamily.{u}) : Prop :=
  ∀ (K L : Type u) [Field K] [Field L] [Algebra K L] [FiniteDimensional K L] (i : ℕ)
    (x : MilnorKRing L), x ∈ milnorKGrading L i → N K L x ∈ milnorKGrading K i

end Stacks.Chow

namespace Stacks.Normalization.SemilocalDvrFamily

open Stacks.Chow

attribute [local instance] finite_index commRing isDomain isDiscreteValuationRing algebraBase
  isLocalHom algebraFractionField isScalarTower isFractionRing moduleFiniteResidueField

variable {A : Type u} [CommRing A] [IsLocalRing A] {F : Type u} [Field F] [Algebra A F]
  (𝓕 : SemilocalDvrFamily.{u, u, u} A F) (N : MilnorKNormFamily.{u})

/-- **The contribution of one member of the family**: the tame symbol `∂_{A_m}` of the discrete
valuation ring `A_m`, on the whole Milnor K-ring of `F`, followed by the norm from the residue
field of `A_m` to that of `A`. -/
def tameShiftAt (m : 𝓕.Index) : MilnorKRing F →+ MilnorKRing (ResidueField A) :=
  (N (ResidueField A) (ResidueField (𝓕.Dvr m))).comp
    ((MilnorKShift.shiftHom (ResidueField (𝓕.Dvr m))).comp
      (dvrMilnorShiftMap (A := 𝓕.Dvr m) (F := F)
        (exists_irreducible (𝓕.Dvr m)).choose_spec).toAddMonoidHom)

/-- The contribution of `A_m` at `x` is the norm of the shifted tame symbol `∂_{A_m}(x)`. -/
theorem tameShiftAt_apply (m : 𝓕.Index) (x : MilnorKRing F) :
    𝓕.tameShiftAt N m x = N (ResidueField A) (ResidueField (𝓕.Dvr m))
      (MilnorKShift.shift (dvrMilnorShiftMap (A := 𝓕.Dvr m) (F := F)
        (exists_irreducible (𝓕.Dvr m)).choose_spec x)) := rfl

/-- **The tame symbol of the family on the whole Milnor K-ring**:
`∂ = ∑_m N_{κ(A_m)/κ} ∘ ∂_{A_m}`. -/
def tameShift : MilnorKRing F →+ MilnorKRing (ResidueField A) :=
  letI := Fintype.ofFinite 𝓕.Index
  ∑ m, 𝓕.tameShiftAt N m

/-- The tame symbol of the family at `x` is the sum over the members of their contributions. -/
theorem tameShift_apply (x : MilnorKRing F) :
    𝓕.tameShift N x =
      letI := Fintype.ofFinite 𝓕.Index
      ∑ m, 𝓕.tameShiftAt N m x := by
  rw [tameShift, AddMonoidHom.finsetSum_apply]

/-- A unit of `A`, read in `F`, has valuation zero at every member of the family. -/
theorem dvrFracOrd_eq_zero_of_unit (m : 𝓕.Index) {ϖ : 𝓕.Dvr m} (hϖ : Irreducible ϖ) {f : Fˣ}
    (hf : ∃ u : Aˣ, algebraMap A F (u : A) = (f : F)) : dvrFracOrd hϖ f = 0 := by
  obtain ⟨u, hu⟩ := hf
  refine dvrFracOrd_eq_zero_of_eq_algebraMap_unit (u := Units.map (algebraMap A (𝓕.Dvr m)) u)
    hϖ ?_
  rw [← hu, Units.coe_map, MonoidHom.coe_ofClass, ← IsScalarTower.algebraMap_apply]

/-- **The contribution of a member kills a symbol of units of `A`.** -/
theorem tameShiftAt_milnorKSymbolProd_eq_zero (m : 𝓕.Index) {l : List Fˣ}
    (hl : ∀ f ∈ l, ∃ u : Aˣ, algebraMap A F (u : A) = (f : F)) :
    𝓕.tameShiftAt N m (milnorKSymbolProd F l) = 0 := by
  rw [tameShiftAt_apply, dvrMilnorShiftMap_shift_milnorKSymbolProd_eq_zero _
    fun f hf ↦ 𝓕.dvrFracOrd_eq_zero_of_unit m _ (hl f hf), map_zero]

/-- **The tame symbol of the family kills a symbol of units of `A`**, in every degree: such a
symbol has no valuation at any member of the family. -/
theorem tameShift_milnorKSymbolProd_eq_zero {l : List Fˣ}
    (hl : ∀ f ∈ l, ∃ u : Aˣ, algebraMap A F (u : A) = (f : F)) :
    𝓕.tameShift N (milnorKSymbolProd F l) = 0 := by
  rw [tameShift_apply]
  exact Finset.sum_eq_zero fun m _ ↦ 𝓕.tameShiftAt_milnorKSymbolProd_eq_zero N m hl

variable {N}

/-- The contribution of a member lowers the degree by one. -/
theorem tameShiftAt_mem (hN : N.PreservesGrading) (m : 𝓕.Index) (i : ℕ) {x : MilnorKRing F}
    (hx : x ∈ milnorKGrading F (i + 1)) :
    𝓕.tameShiftAt N m x ∈ milnorKGrading (ResidueField A) i :=
  hN _ _ i _ (dvrMilnorShiftMap_shift_mem _ i hx)

/-- The tame symbol of the family lowers the degree by one. -/
theorem tameShift_mem (hN : N.PreservesGrading) (i : ℕ) {x : MilnorKRing F}
    (hx : x ∈ milnorKGrading F (i + 1)) :
    𝓕.tameShift N x ∈ milnorKGrading (ResidueField A) i := by
  rw [tameShift_apply]
  exact sum_mem fun m _ ↦ 𝓕.tameShiftAt_mem hN m i hx

/-- **The tame symbol of the family, `∂ : K^M_{i+1}(F) → K^M_i(κ)`.** -/
def tameSymbol (hN : N.PreservesGrading) (i : ℕ) :
    MilnorKTheory F (i + 1) →+ MilnorKTheory (ResidueField A) i :=
  ((𝓕.tameShift N).comp (milnorKGrading F (i + 1)).subtype).codRestrict _
    fun y ↦ 𝓕.tameShift_mem hN i y.2

/-- The degree-`i` tame symbol of the family agrees with `tameShift` on the underlying Milnor
K-ring. -/
@[simp]
theorem coe_tameSymbol (hN : N.PreservesGrading) (i : ℕ) (y : MilnorKTheory F (i + 1)) :
    (𝓕.tameSymbol hN i y : MilnorKRing (ResidueField A)) = 𝓕.tameShift N (y : MilnorKRing F) :=
  rfl

end Stacks.Normalization.SemilocalDvrFamily

namespace Stacks.Chow

variable (A : Type u) [CommRing A] [IsDomain A] [IsLocalRing A] [IsNoetherianRing A]
  (F : Type u) [Field F] [Algebra A F] [IsFractionRing A F]

omit [IsNoetherianRing A] in
/-- A domain of Krull dimension one has dimension at most one in the sense of
`Ring.DimensionLEOne`: its nonzero primes are maximal. -/
theorem dimensionLEOne_of_ringKrullDim_eq_one (hdim : ringKrullDim A = 1) :
    Ring.DimensionLEOne A :=
  have : Ring.KrullDimLE 1 A := Ring.krullDimLE_iff.2 (by rw [hdim]; exact_mod_cast le_rfl)
  ⟨fun hp hpp ↦ Ring.krullDimLE_one_iff_of_isPrime_bot.mp ‹_› _ hp hpp⟩

omit [IsDomain A] [IsNoetherianRing A] in
/-- The maximal ideal of a local ring of Krull dimension one is nonzero. -/
theorem maximalIdeal_ne_bot_of_ringKrullDim_eq_one (hdim : ringKrullDim A = 1) :
    maximalIdeal A ≠ ⊥ := by
  intro h
  have hfield : IsField A := (isField_iff_maximalIdeal_eq).mpr h
  rw [ringKrullDim_eq_zero_of_isField hfield] at hdim
  exact zero_ne_one hdim

/-- **The normalization of a one-dimensional Noetherian local domain, as a family of discrete
valuation rings**: the local rings of the integral closure of `A` in `F` at its finitely many
maximal ideals. -/
def normalizationDvrFamily (hdim : ringKrullDim A = 1) :
    Stacks.Normalization.SemilocalDvrFamily.{u, u, u} A F :=
  letI := dimensionLEOne_of_ringKrullDim_eq_one A hdim
  Stacks.Normalization.semilocalDvrFamily A F (maximalIdeal_ne_bot_of_ringKrullDim_eq_one A hdim)

end Stacks.Chow

end
