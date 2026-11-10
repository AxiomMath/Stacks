module

public import StacksFrontier.AlgebraicGeometry.Chow.DeterminantsFiniteLength.RestrictScalars
public import StacksFrontier.AlgebraicGeometry.Chow.PeriodicComplexesDeterminants.Comparison
public import StacksFrontier.AlgebraicGeometry.Chow.Symbols.Basic
public import StacksFrontier.AlgebraicGeometry.Chow.Symbols.Invariance
public import StacksFrontier.AlgebraicGeometry.Chow.Symbols.MilnorBoundary
public import StacksFrontier.AlgebraicGeometry.Chow.Symbols.PeriodicExactness
public import StacksFrontier.AlgebraicGeometry.Chow.Symbols.TameSymbol
public import StacksFrontier.AlgebraicGeometry.Chow.TameSymbol.Fraction

/-!
# Transporting the tame symbol along an isomorphism of a local ring and its fraction field

The tame symbol `∂_A` of Stacks 02Q1 of a one-dimensional Noetherian local domain `A` with
fraction field `K` takes its values in the units of the residue field of `A`, so a statement
comparing the tame symbols of two different such pairs has to move that residue field as well.
This file provides the comparison for an isomorphism of pairs: given isomorphisms `ε : A ≃+* B`
and `η : K ≃+* L` with `η` carrying the image of `a` to the image of `ε a` for every `a` in `A`,

`κ(ε) (∂_A(f, g)) = ∂_B(η f, η g)`,

where `κ(ε)` is the induced isomorphism of residue fields; and the corresponding square for the
boundary `K₂ᴹ(K) ⟶ K₁ᴹ(κ(A))` obtained by descending the tame symbol to Milnor K-theory commutes.

Three layers are needed. At the bottom is the symbol `d_A(a, b)` of Stacks 02PZ on pairs of
elements, transported in the same sense. In the middle is the tame symbol on units of the
fraction field, where the transport is obtained by *uniqueness*: the development carries a tame
symbol as the data of a two-variable map which is multiplicative in each variable and agrees with
`d_A` on pairs of elements of `A`, and such a datum is in fact unique, because every unit of `K`
is a quotient of two nonzerodivisors of `A`. So the symbol of `A` conjugated by `ε` and `η` is a
datum of that kind for `B`, hence is the tame symbol of `B`. At the top are the Milnor K-groups,
which an isomorphism of fields transports because its presentations are built from the unit group
and the Steinberg relations, both of which an isomorphism of fields respects.

The bottom layer is where the work is. The symbol `d_A(a, b)` is the periodic determinant of
Stacks 02PJ of the two-periodic complex on `A / abA` whose differentials are multiplication by
`a` and by `b`, and the periodic determinant is characterized by a comparison of two determinant
maps of finite-length modules. So the transport has to be carried out at that level, and the
mechanism is already in the development:
Stacks 02PC says that restricting scalars along a local homomorphism which induces an
isomorphism of residue fields changes neither the length nor the determinant of a finite-length
module, and `Module.FiniteLength.determinantRestrictScalarsEquiv_exact` says the comparison
respects the determinant map of a short exact sequence. Feeding that into the uniqueness of the
periodic determinant gives the restriction-of-scalars statement, and an isomorphism `ε` is the
special case where `B` is an `A`-algebra through `ε` itself.

## What is carried

No further input is assumed. The two general statements below need only a local homomorphism
with bijective induced map of residue fields; the statements for an isomorphism need only that
isomorphism, since a surjection of local rings is a local homomorphism and an isomorphism induces
a bijection of residue fields.

## Restatements of private results of the base

Three results of the development are `private` and so cannot be named from another module. They
are restated here under new names, with the same proofs:

* `Stacks.Chow.periodicGamma_determinantRestrictScalarsEquiv` restates
  `periodicGamma_restrictScalars` of
  `StacksFrontier.AlgebraicGeometry.Chow.PeriodicComplexHomologyCycles`.
* `Stacks.Chow.map_periodicDeterminant_restrictScalars` restates
  `periodicDeterminant_restrictScalars` of the same module. This is the mathematical heart: it is
  what the tame-symbol transport ultimately rests on.
* `Stacks.Chow.moduleSymbol_eq_of_linearEquiv` restates `moduleSymbol_eq_of_linearEquiv` of
  `StacksFrontier.AlgebraicGeometry.Chow.Symbols.MinimalPrimes`, a one-line consequence of the
  public Stacks 02Q4.

## Main definitions

* `Stacks.Chow.symbolOfPeriodicMaps` — the periodic determinant of the complex on `M / φψM` cut
  out by two commuting injective endomorphisms of `M`. This is `AlgebraicGeometry.moduleSymbol`
  with the two multiplication maps replaced by the endomorphisms themselves, which is what lets
  the two differentials be rewritten; the symbol of Stacks 02PZ is the case of multiplication by
  two ring elements.
* `Stacks.Chow.tameSymbolTransport` — the tame symbol of `A` conjugated by `ε` and `η`, as a
  datum of the kind the development's `AlgebraicGeometry.TameSymbol` records for `B`.
* `Stacks.Chow.milnorKOneRingEquiv`, `Stacks.Chow.milnorKTwoRingEquiv` — the degree-one and
  degree-two Milnor K-groups transported along an isomorphism of fields.
* `Stacks.Chow.milnorKTwoUnitsTensorEquiv` — the tensor square of the unit group transported
  along an isomorphism of fields.

## Main results

* `Stacks.Chow.map_periodicDeterminant_restrictScalars` — the periodic determinant is unchanged
  by restriction of scalars along a local homomorphism with bijective induced map of residue
  fields.
* `Stacks.Chow.map_symbolOfPeriodicMaps_restrictScalars`,
  `Stacks.Chow.map_moduleSymbol_restrictScalars` — the same for the symbol of Stacks 02PZ.
* `Stacks.Chow.map_moduleSymbol_ringEquiv` — the transport of the symbol of Stacks 02PZ along an
  isomorphism: for `ε : A ≃+* B` an isomorphism of Noetherian local rings of support dimension
  one, the induced isomorphism of residue fields carries `d_A(a, b)` to `d_B(ε a, ε b)`.
* `Stacks.Chow.tameSymbolData_eq`, `Stacks.Chow.eq_tameSymbol` — **the tame symbol of Stacks 02Q1
  is unique**: the data the development carries is determined by its restriction to pairs of
  nonzerodivisors of the ring.
* `Stacks.Chow.map_tameSymbol_ringEquiv` — **the transport of the tame symbol along an
  isomorphism of pairs**.
* `Stacks.Chow.map_milnorKTwoSteinbergSubmodule` — an isomorphism of fields carries the Steinberg
  submodule of the tensor square onto the Steinberg submodule.
* `Stacks.Chow.milnorKTwoRingEquiv_pureSymbol` — the degree-two transport sends a pure symbol to
  the pure symbol of the images.
* `Stacks.Chow.milnorKTwoTameSymbol_ringEquiv` — **the transport of the Milnor K₂ tame-symbol
  boundary of Stacks 0GU9 along an isomorphism of pairs**.

## References

* [Stacks Project, Tag 02PC](https://stacks.math.columbia.edu/tag/02PC)
* [Stacks Project, Tag 02PJ](https://stacks.math.columbia.edu/tag/02PJ)
* [Stacks Project, Tag 02PZ](https://stacks.math.columbia.edu/tag/02PZ)
* [Stacks Project, Tag 02Q1](https://stacks.math.columbia.edu/tag/02Q1)
* [Stacks Project, Tag 02Q4](https://stacks.math.columbia.edu/tag/02Q4)
* [Stacks Project, Tag 02Q9](https://stacks.math.columbia.edu/tag/02Q9)
* [Stacks Project, Tag 0EAY](https://stacks.math.columbia.edu/tag/0EAY)
* [Stacks Project, Tag 0GU9](https://stacks.math.columbia.edu/tag/0GU9)
-/

@[expose] public section

noncomputable section

-- `RingHomInvPair` for the residue-field equivalence and for its inverse: both are needed to
-- elaborate the semilinear determinant comparison of Stacks 02PC.
attribute [local instance] RingHomInvPair.of_ringEquiv
attribute [local instance] RingHomInvPair.of_ringEquiv_symm

open AlgebraicGeometry Module.FiniteLength

universe u v w

namespace Stacks.Chow

/-! ### Restriction of scalars for the periodic determinant -/

section RestrictScalars

variable {R₀ : Type u} {R : Type v} [CommRing R₀] [IsLocalRing R₀]
  [CommRing R] [IsLocalRing R] [Algebra R₀ R] [IsLocalHom (algebraMap R₀ R)]
  {M : Type w} [AddCommGroup M] [Module R₀ M] [Module R M] [IsScalarTower R₀ R M]

/-- **The determinant map of an exact periodic complex is unchanged by restriction of scalars.**
The map `AlgebraicGeometry.periodicGamma` is a determinant map of a short exact sequence, and the
comparison of Stacks 02PC respects those.

This restates the `private` lemma `periodicGamma_restrictScalars` of
`StacksFrontier.AlgebraicGeometry.Chow.PeriodicComplexHomologyCycles`, which cannot be named from
another module. -/
theorem periodicGamma_determinantRestrictScalarsEquiv
    (hκ : Function.Bijective (IsLocalRing.ResidueField.map (algebraMap R₀ R)))
    (φ ψ : M →ₗ[R] M) (hψφ : Function.Exact ψ φ) (hM : IsFiniteLength R M)
    (a : determinant R (LinearMap.range ψ)) (b : determinant R (LinearMap.range φ)) :
    determinantRestrictScalarsEquiv hκ hM
        (periodicGamma φ ψ hψφ hM (TensorProduct.tmul (IsLocalRing.ResidueField R) a b)) =
      periodicGamma (φ.restrictScalars R₀) (ψ.restrictScalars R₀) hψφ
        (isFiniteLength_restrictScalars hκ hM)
        (TensorProduct.tmul (IsLocalRing.ResidueField R₀)
          (determinantRestrictScalarsEquiv hκ
            (hM.of_injective (LinearMap.range ψ).subtype_injective) a)
          (determinantRestrictScalarsEquiv hκ
            (hM.of_surjective (LinearMap.range_eq_top.mp
              (LinearMap.range_rangeRestrict φ))) b)) := by
  unfold AlgebraicGeometry.periodicGamma
  exact determinantRestrictScalarsEquiv_exact hκ _ _ _ _ _ _ _ _ a b

/-- **The periodic determinant of Stacks 02PJ is unchanged by restriction of scalars** along a
local homomorphism inducing an isomorphism of residue fields: the periodic determinant of the
restricted complex is carried to that of the complex itself by the induced map of residue fields.

The proof is the uniqueness of the periodic determinant. The image of the determinant of the
complex over `R` satisfies, over `R₀`, the signed comparison of determinant maps which
characterizes the periodic determinant: the comparison of Stacks 02PC is compatible with the
determinant maps by `Stacks.Chow.periodicGamma_determinantRestrictScalarsEquiv`, and the two
lengths occurring in the sign agree by Stacks 02PC again.

This restates the `private` lemma `periodicDeterminant_restrictScalars` of
`StacksFrontier.AlgebraicGeometry.Chow.PeriodicComplexHomologyCycles`, which cannot be named from
another module. -/
theorem map_periodicDeterminant_restrictScalars
    (hκ : Function.Bijective (IsLocalRing.ResidueField.map (algebraMap R₀ R)))
    (φ ψ : M →ₗ[R] M) (hφψ : Function.Exact φ ψ) (hψφ : Function.Exact ψ φ)
    (hM : IsFiniteLength R M) :
    Units.map (IsLocalRing.ResidueField.map (algebraMap R₀ R)).toMonoidHom
        (periodicDeterminant (φ.restrictScalars R₀) (ψ.restrictScalars R₀) hφψ hψφ
        (isFiniteLength_restrictScalars hκ hM)) =
      periodicDeterminant φ ψ hφψ hψφ hM := by
  let ρ := RingEquiv.ofBijective (IsLocalRing.ResidueField.map (algebraMap R₀ R)) hκ
  let hM₀ := isFiniteLength_restrictScalars hκ hM
  let d₀ := periodicDeterminant (φ.restrictScalars R₀) (ψ.restrictScalars R₀) hφψ hψφ hM₀
  have hlenφ := moduleLength_restrictScalars hκ
    (hM.of_injective (LinearMap.range φ).subtype_injective)
  have hlenψ := moduleLength_restrictScalars hκ
    (hM.of_injective (LinearMap.range ψ).subtype_injective)
  apply eq_periodicDeterminant
  unfold AlgebraicGeometry.IsPeriodicDeterminant
  apply TensorProduct.ext'
  intro a b
  apply (determinantRestrictScalarsEquiv hκ hM).injective
  simp only [LinearMap.comp_apply, TensorProduct.comm_tmul, LinearEquiv.coe_coe,
    LinearMap.smul_apply, map_smulₛₗ]
  rw [periodicGamma_determinantRestrictScalarsEquiv,
    periodicGamma_determinantRestrictScalarsEquiv]
  have hd := LinearMap.congr_fun (periodicDeterminant_spec
    (φ.restrictScalars R₀) (ψ.restrictScalars R₀) hφψ hψφ hM₀)
      (TensorProduct.tmul (IsLocalRing.ResidueField R₀)
        (determinantRestrictScalarsEquiv hκ
          (hM.of_injective (LinearMap.range ψ).subtype_injective) a)
        (determinantRestrictScalarsEquiv hκ
          (hM.of_injective (LinearMap.range φ).subtype_injective) b))
  simp only [LinearMap.comp_apply, LinearEquiv.coe_coe, LinearMap.smul_apply] at hd
  convert hd using 1
  · congr 1
  · congr 1
    change ρ.symm ((-1) ^ (moduleLength R (LinearMap.range φ) *
        moduleLength R (LinearMap.range ψ)) *
          ρ (d₀ : IsLocalRing.ResidueField R₀)) = _
    simp only [map_mul, map_pow, map_neg, map_one, RingEquiv.symm_apply_apply]
    rw [hlenφ, hlenψ]
    rfl

end RestrictScalars

/-! ### The symbol of two commuting injective endomorphisms -/

section SymbolOfMaps

variable {A : Type u} {M : Type w} [CommRing A] [IsNoetherianRing A] [IsLocalRing A]
  [AddCommGroup M] [Module A M] [Module.Finite A M]

/-- **The symbol of Stacks 02PZ, with the two differentials given as endomorphisms.** For two
injective endomorphisms `φ`, `ψ` of a finite module `M` of support dimension one whose composites
in the two orders have the same image, the periodic determinant of the two-periodic complex they
cut out on `M / φψM`.

`AlgebraicGeometry.moduleSymbol` is the case of multiplication by two ring elements, and is that
case by definition. Naming the general form is what makes the two differentials rewritable: the
module of the complex depends on them, so an equality of ring elements over two different base
rings cannot be substituted into `AlgebraicGeometry.moduleSymbol` directly, while an equality of
endomorphisms can be substituted here. -/
def symbolOfPeriodicMaps (φ ψ : M →ₗ[A] M) (hφ : Function.Injective φ)
    (hψ : Function.Injective ψ)
    (hcomm : LinearMap.range (φ ∘ₗ ψ) = LinearMap.range (ψ ∘ₗ φ))
    (hdim : Module.supportDim A M = 1) : (IsLocalRing.ResidueField A)ˣ :=
  periodicDeterminant (periodicQuotientPhi φ ψ hcomm) (periodicQuotientPsi φ ψ hcomm)
    (exact_periodicQuotient_phi_psi φ ψ hψ hcomm)
    (exact_periodicQuotient_psi_phi φ ψ hφ hcomm)
    (Module.isFiniteLength_quotient_range_of_injective (φ ∘ₗ ψ) (hφ.comp hψ) hdim)

/-- The symbol depends on its two endomorphisms only through the endomorphisms, not through the
chosen witnesses of injectivity, commutation or dimension. -/
theorem symbolOfPeriodicMaps_congr {φ φ' ψ ψ' : M →ₗ[A] M} (hφφ : φ = φ') (hψψ : ψ = ψ')
    (hφ : Function.Injective φ) (hψ : Function.Injective ψ)
    (hcomm : LinearMap.range (φ ∘ₗ ψ) = LinearMap.range (ψ ∘ₗ φ))
    (hφ' : Function.Injective φ') (hψ' : Function.Injective ψ')
    (hcomm' : LinearMap.range (φ' ∘ₗ ψ') = LinearMap.range (ψ' ∘ₗ φ'))
    (hdim : Module.supportDim A M = 1) :
    symbolOfPeriodicMaps φ ψ hφ hψ hcomm hdim =
      symbolOfPeriodicMaps φ' ψ' hφ' hψ' hcomm' hdim := by
  subst hφφ
  subst hψψ
  rfl

omit [IsNoetherianRing A] [IsLocalRing A] [Module.Finite A M] in
/-- The two multiplication maps commute, so they cut out a two-periodic complex. -/
theorem range_lsmul_comp_eq (a b : A) :
    LinearMap.range (LinearMap.lsmul A M a ∘ₗ LinearMap.lsmul A M b) =
      LinearMap.range (LinearMap.lsmul A M b ∘ₗ LinearMap.lsmul A M a) :=
  congrArg LinearMap.range (by
    ext m
    simp only [LinearMap.comp_apply, LinearMap.lsmul_apply]
    exact smul_comm a b m)

/-- **The symbol of Stacks 02PZ is the symbol of the two multiplication maps.** This holds by
definition; the point of the statement is that the right-hand side has the two differentials as
arguments. -/
theorem moduleSymbol_eq_symbolOfPeriodicMaps (a b : A) (ha : IsSMulRegular M a)
    (hb : IsSMulRegular M b) (hdim : Module.supportDim A M = 1) :
    moduleSymbol (M := M) a b ha hb hdim =
      symbolOfPeriodicMaps (LinearMap.lsmul A M a) (LinearMap.lsmul A M b) ha hb
        (range_lsmul_comp_eq a b) hdim := rfl

/-- **Stacks Project, Tag 02Q4 for an isomorphism of modules.** Isomorphic finite modules of
support dimension one have the same symbol: the kernel and cokernel of an isomorphism are zero,
so the public form of the tag applies.

This restates the `private` lemma `moduleSymbol_eq_of_linearEquiv` of
`StacksFrontier.AlgebraicGeometry.Chow.Symbols.MinimalPrimes`, which cannot be named from another
module. -/
theorem moduleSymbol_eq_of_linearEquiv {N : Type*} [AddCommGroup N] [Module A N]
    [Module.Finite A N] (e : M ≃ₗ[A] N) (a b : A) (ha : IsSMulRegular M a)
    (hb : IsSMulRegular M b) (ha' : IsSMulRegular N a) (hb' : IsSMulRegular N b)
    (hdim : Module.supportDim A M = 1) (hdim' : Module.supportDim A N = 1) :
    moduleSymbol (M := M) a b ha hb hdim = moduleSymbol (M := N) a b ha' hb' hdim' := by
  refine moduleSymbol_eq_of_ker_coker_supportDim_le_zero e.toLinearMap a b ha hb ha' hb'
    hdim hdim' ?_ ?_
  · have : Subsingleton (LinearMap.ker e.toLinearMap) := by
      rw [LinearMap.ker_eq_bot.mpr e.injective]
      infer_instance
    simp [Module.supportDim_eq_bot_of_subsingleton]
  · have : Subsingleton (N ⧸ LinearMap.range e.toLinearMap) := by
      rw [LinearMap.range_eq_top.mpr e.surjective]
      infer_instance
    simp [Module.supportDim_eq_bot_of_subsingleton]

end SymbolOfMaps

/-! ### Restriction of scalars for the symbol -/

section SymbolRestrictScalars

variable {R₀ : Type u} {R : Type v} [CommRing R₀] [IsNoetherianRing R₀] [IsLocalRing R₀]
  [CommRing R] [IsNoetherianRing R] [IsLocalRing R] [Algebra R₀ R]
  [IsLocalHom (algebraMap R₀ R)]
  {M : Type w} [AddCommGroup M] [Module R₀ M] [Module R M] [IsScalarTower R₀ R M]
  [Module.Finite R₀ M] [Module.Finite R M]

/-- The symbol of two commuting injective endomorphisms is unchanged by restriction of scalars
along a local homomorphism inducing an isomorphism of residue fields: the two periodic complexes
have the same differentials, so this is
`Stacks.Chow.map_periodicDeterminant_restrictScalars`. -/
theorem map_symbolOfPeriodicMaps_restrictScalars
    (hκ : Function.Bijective (IsLocalRing.ResidueField.map (algebraMap R₀ R)))
    (φ ψ : M →ₗ[R] M) (hφ : Function.Injective φ) (hψ : Function.Injective ψ)
    (hcomm : LinearMap.range (φ ∘ₗ ψ) = LinearMap.range (ψ ∘ₗ φ))
    (hcomm₀ : LinearMap.range (φ.restrictScalars R₀ ∘ₗ ψ.restrictScalars R₀) =
      LinearMap.range (ψ.restrictScalars R₀ ∘ₗ φ.restrictScalars R₀))
    (hdim₀ : Module.supportDim R₀ M = 1) (hdim : Module.supportDim R M = 1) :
    Units.map (IsLocalRing.ResidueField.map (algebraMap R₀ R)).toMonoidHom
        (symbolOfPeriodicMaps (φ.restrictScalars R₀) (ψ.restrictScalars R₀) hφ hψ hcomm₀
          hdim₀) =
      symbolOfPeriodicMaps φ ψ hφ hψ hcomm hdim :=
  map_periodicDeterminant_restrictScalars hκ (periodicQuotientPhi φ ψ hcomm)
    (periodicQuotientPsi φ ψ hcomm) (exact_periodicQuotient_phi_psi φ ψ hψ hcomm)
    (exact_periodicQuotient_psi_phi φ ψ hφ hcomm)
    (Module.isFiniteLength_quotient_range_of_injective (φ ∘ₗ ψ) (hφ.comp hψ) hdim)

omit [IsNoetherianRing R₀] [IsLocalRing R₀] [IsNoetherianRing R] [IsLocalRing R]
  [IsLocalHom (algebraMap R₀ R)] [Module.Finite R₀ M] [Module.Finite R M] in
/-- Multiplication by a ring element is multiplication by its image, after restriction of
scalars. -/
theorem lsmul_restrictScalars (a : R₀) :
    LinearMap.lsmul R₀ M a = (LinearMap.lsmul R M (algebraMap R₀ R a)).restrictScalars R₀ := by
  ext m
  exact (algebraMap_smul R a m).symm

/-- **The symbol of Stacks 02PZ is unchanged by restriction of scalars** along a local
homomorphism inducing an isomorphism of residue fields: the symbol of `a` and `b` over `R₀` is
carried by the induced map of residue fields to the symbol of their images over `R`. -/
theorem map_moduleSymbol_restrictScalars
    (hκ : Function.Bijective (IsLocalRing.ResidueField.map (algebraMap R₀ R)))
    (a b : R₀) (ha₀ : IsSMulRegular M a) (hb₀ : IsSMulRegular M b)
    (ha : IsSMulRegular M (algebraMap R₀ R a)) (hb : IsSMulRegular M (algebraMap R₀ R b))
    (hdim₀ : Module.supportDim R₀ M = 1) (hdim : Module.supportDim R M = 1) :
    Units.map (IsLocalRing.ResidueField.map (algebraMap R₀ R)).toMonoidHom
        (moduleSymbol (M := M) a b ha₀ hb₀ hdim₀) =
      moduleSymbol (M := M) (algebraMap R₀ R a) (algebraMap R₀ R b) ha hb hdim := by
  rw [moduleSymbol_eq_symbolOfPeriodicMaps, moduleSymbol_eq_symbolOfPeriodicMaps,
    symbolOfPeriodicMaps_congr (lsmul_restrictScalars (R := R) (M := M) a)
      (lsmul_restrictScalars (R := R) (M := M) b) ha₀ hb₀ (range_lsmul_comp_eq a b) ha hb
      (by rw [← lsmul_restrictScalars (R := R) (M := M) a,
        ← lsmul_restrictScalars (R := R) (M := M) b]; exact range_lsmul_comp_eq a b) hdim₀]
  exact map_symbolOfPeriodicMaps_restrictScalars hκ (LinearMap.lsmul R M (algebraMap R₀ R a))
    (LinearMap.lsmul R M (algebraMap R₀ R b)) ha hb (range_lsmul_comp_eq _ _) _ hdim₀ hdim

end SymbolRestrictScalars

/-! ### Transport along an isomorphism of local rings -/

section RingEquivTransport

variable {A B : Type u} [CommRing A] [IsNoetherianRing A] [IsLocalRing A]
  [CommRing B] [IsNoetherianRing B] [IsLocalRing B]

/-- **The symbol of Stacks 02PZ transported along an isomorphism of local rings.** Let
`ε : A ≃+* B` be an isomorphism of Noetherian local rings of support dimension one over
themselves. Then the induced isomorphism of residue fields carries `d_A(a, b)` to
`d_B(ε a, ε b)`.

The proof makes `B` an `A`-algebra through `ε`, which is a local homomorphism inducing an
isomorphism of residue fields. Over `A`, the modules `A` and `B` are then isomorphic through `ε`
itself, so Stacks 02Q4 replaces the symbol of `A` by the symbol of `B` over `A`; and the
restriction-of-scalars statement replaces the latter by the symbol of `B` over `B`. -/
theorem map_moduleSymbol_ringEquiv (ε : A ≃+* B) (a b : A)
    (ha : IsSMulRegular A a) (hb : IsSMulRegular A b)
    (ha' : IsSMulRegular B (ε a)) (hb' : IsSMulRegular B (ε b))
    (hdim : Module.supportDim A A = 1) (hdim' : Module.supportDim B B = 1) :
    Units.map (IsLocalRing.ResidueField.mapEquiv ε).toMonoidHom
        (moduleSymbol (M := A) a b ha hb hdim) =
      moduleSymbol (M := B) (ε a) (ε b) ha' hb' hdim' := by
  let _ : Algebra A B := ε.toRingHom.toAlgebra
  have _ : IsLocalHom (algebraMap A B) := ε.surjective.isLocalHom
  have _ : Module.Finite A B :=
    Module.Finite.of_surjective (Algebra.linearMap A B) ε.surjective
  have hκ : Function.Bijective (IsLocalRing.ResidueField.map (algebraMap A B)) :=
    (IsLocalRing.ResidueField.mapEquiv ε).bijective
  -- `ε` as an isomorphism of `A`-modules, where `A` acts on `B` through `ε`.
  let e : A ≃ₗ[A] B :=
    { ε with map_smul' := fun r x => map_mul ε r x }
  have hdimB : Module.supportDim A B = 1 :=
    (Module.supportDim_eq_of_equiv e).symm.trans hdim
  have hsmul : ∀ (r : A) (x : B), r • x = ε r • x := fun r x => (algebraMap_smul B r x).symm
  have hreg : ∀ r : A, IsSMulRegular B (ε r) → IsSMulRegular B r := fun r hr x y hxy =>
    hr (by simpa only [hsmul] using hxy)
  have haB := hreg a ha'
  have hbB := hreg b hb'
  rw [moduleSymbol_eq_of_linearEquiv e a b ha hb haB hbB hdim hdimB]
  exact map_moduleSymbol_restrictScalars (R := B) hκ a b haB hbB ha' hb' hdimB hdim'

end RingEquivTransport

/-! ### The tame symbol of Stacks 02Q1 is determined by its restriction to the ring -/

section TameSymbolUnique

variable {A : Type u} [CommRing A] [IsDomain A] [IsNoetherianRing A] [IsLocalRing A]
  {K : Type v} [Field K] [Algebra A K] [IsFractionRing A K]

/-- The tame symbol is trivial when its second argument is `1`. -/
theorem tameSymbolData_one_right (hdim : ringKrullDim A = 1)
    (T : AlgebraicGeometry.TameSymbol (K := K) hdim) (x : Kˣ) : T x 1 = 1 := by
  have h : T x 1 = T x 1 * T x 1 := by simpa only [mul_one] using T.map_mul_right x 1 1
  exact (mul_left_cancel (a := T x 1) (by rw [mul_one]; exact h)).symm

/-- The tame symbol is trivial when its first argument is `1`. -/
theorem tameSymbolData_one_left (hdim : ringKrullDim A = 1)
    (T : AlgebraicGeometry.TameSymbol (K := K) hdim) (y : Kˣ) : T 1 y = 1 := by
  have h : T 1 y = T 1 y * T 1 y := by simpa only [mul_one] using T.map_mul_left 1 1 y
  exact (mul_left_cancel (a := T 1 y) (by rw [mul_one]; exact h)).symm

/-- The tame symbol inverts its second argument. -/
theorem tameSymbolData_inv_right (hdim : ringKrullDim A = 1)
    (T : AlgebraicGeometry.TameSymbol (K := K) hdim) (x y : Kˣ) : T x y⁻¹ = (T x y)⁻¹ := by
  refine eq_inv_of_mul_eq_one_left ?_
  rw [← T.map_mul_right, inv_mul_cancel, tameSymbolData_one_right]

/-- The tame symbol inverts its first argument. -/
theorem tameSymbolData_inv_left (hdim : ringKrullDim A = 1)
    (T : AlgebraicGeometry.TameSymbol (K := K) hdim) (x y : Kˣ) : T x⁻¹ y = (T x y)⁻¹ := by
  refine eq_inv_of_mul_eq_one_left ?_
  rw [← T.map_mul_left, inv_mul_cancel, tameSymbolData_one_left]

/-- **The tame symbol on a pair of nonzerodivisors of `A` is the symbol of Stacks 02PZ.** This is
the defining property of `AlgebraicGeometry.TameSymbol`, read for a nonzerodivisor rather than
for an element together with a proof of regularity. -/
theorem tameSymbolData_regularFractionUnit (hdim : ringKrullDim A = 1)
    (T : AlgebraicGeometry.TameSymbol (K := K) hdim) (a c : nonZeroDivisors A) :
    T (regularFractionUnit (Q := K) a) (regularFractionUnit (Q := K) c) =
      moduleSymbol (M := A) (a : A) (c : A)
        (isRegular_iff_mem_nonZeroDivisors.mpr a.2).isSMulRegular
        (isRegular_iff_mem_nonZeroDivisors.mpr c.2).isSMulRegular
        ((Module.supportDim_self_eq_ringKrullDim A).trans hdim) :=
  T.eq_moduleSymbol (a : A) (c : A) (isRegular_iff_mem_nonZeroDivisors.mpr a.2)
    (isRegular_iff_mem_nonZeroDivisors.mpr c.2)

/-- **The tame symbol of Stacks 02Q1 is unique.** Any two terms of
`AlgebraicGeometry.TameSymbol` for the same ring, fraction field and dimension agree: every unit
of the fraction field is a quotient of two nonzerodivisors of the ring, the symbol is
multiplicative in each variable, and its values on pairs of nonzerodivisors are prescribed to be
the symbol of Stacks 02PZ.

The source does not claim uniqueness, and the development carries the symbol as data for that
reason. Uniqueness is what lets a symbol transported along an isomorphism be recognized as *the*
tame symbol of the target, so it is proved here. -/
theorem tameSymbolData_eq (hdim : ringKrullDim A = 1)
    (T T' : AlgebraicGeometry.TameSymbol (K := K) hdim) (f g : Kˣ) : T f g = T' f g := by
  obtain ⟨a, b, hf⟩ := exists_regularFractionUnit_div (A := A) (Q := K) f
  obtain ⟨c, d, hg⟩ := exists_regularFractionUnit_div (A := A) (Q := K) g
  have key : ∀ S : AlgebraicGeometry.TameSymbol (K := K) hdim,
      S f g = S (regularFractionUnit a) (regularFractionUnit c) *
        (S (regularFractionUnit a) (regularFractionUnit (Q := K) d))⁻¹ *
        ((S (regularFractionUnit b) (regularFractionUnit (Q := K) c))⁻¹ *
          S (regularFractionUnit b) (regularFractionUnit (Q := K) d)) := by
    intro S
    rw [hf, hg, S.map_mul_left, tameSymbolData_inv_left, S.map_mul_right,
      S.map_mul_right, tameSymbolData_inv_right, tameSymbolData_inv_right, mul_inv, inv_inv]
  rw [key T, key T']
  simp only [tameSymbolData_regularFractionUnit]

/-- Every term of `AlgebraicGeometry.TameSymbol` is the tame symbol of Stacks 02Q1. -/
theorem eq_tameSymbol (hdim : ringKrullDim A = 1)
    (T : AlgebraicGeometry.TameSymbol (K := K) hdim) (f g : Kˣ) :
    T f g = tameSymbol (K := K) hdim f g :=
  tameSymbolData_eq hdim T _ f g

end TameSymbolUnique

/-! ### The tame symbol transported along an isomorphism of pairs -/

section TameSymbolTransport

variable {A B : Type u} [CommRing A] [IsDomain A] [IsNoetherianRing A] [IsLocalRing A]
  [CommRing B] [IsDomain B] [IsNoetherianRing B] [IsLocalRing B]
  {K : Type v} [Field K] [Algebra A K] [IsFractionRing A K]
  {L : Type v} [Field L] [Algebra B L] [IsFractionRing B L]

omit [IsNoetherianRing A] [IsNoetherianRing B] in
/-- An isomorphism of domains carries nonzerodivisors to nonzerodivisors, since in a domain a
nonzerodivisor is just a nonzero element. -/
theorem isRegular_ringEquiv_symm (ε : A ≃+* B) {y : B} (hy : IsRegular y) :
    IsRegular (ε.symm y) := by
  refine isRegular_iff_mem_nonZeroDivisors.mpr (mem_nonZeroDivisors_iff_ne_zero.mpr ?_)
  intro h
  exact (mem_nonZeroDivisors_iff_ne_zero.mp (isRegular_iff_mem_nonZeroDivisors.mp hy))
    (by rw [← ε.apply_symm_apply y, h, map_zero])

omit [IsDomain A] [IsNoetherianRing A] [IsLocalRing A] [IsDomain B] [IsNoetherianRing B]
  [IsLocalRing B] [IsFractionRing A K] [IsFractionRing B L] in
/-- Where the two fraction fields are matched up compatibly with the two rings, the inverse
field isomorphism carries the image of an element of `B` to the image of its preimage in `A`. -/
theorem ringEquiv_symm_algebraMap (ε : A ≃+* B) (η : K ≃+* L)
    (hcompat : ∀ a : A, η (algebraMap A K a) = algebraMap B L (ε a)) (y : B) :
    η.symm (algebraMap B L y) = algebraMap A K (ε.symm y) := by
  refine η.injective ?_
  rw [η.apply_symm_apply, hcompat, ε.apply_symm_apply]

/-- **The tame symbol of Stacks 02Q1 transported along an isomorphism of pairs.** An isomorphism
`ε : A ≃+* B` of one-dimensional Noetherian local domains together with a compatible isomorphism
`η : K ≃+* L` of their fraction fields turns the tame symbol of `A` into a term of
`AlgebraicGeometry.TameSymbol` for `B`: conjugate the two arguments by `η` and the value by the
induced isomorphism of residue fields.

Multiplicativity in each variable is immediate. The defining property, agreement with the symbol
of Stacks 02PZ on pairs of elements of `B`, is exactly
`Stacks.Chow.map_moduleSymbol_ringEquiv`. -/
def tameSymbolTransport (ε : A ≃+* B) (η : K ≃+* L)
    (hcompat : ∀ a : A, η (algebraMap A K a) = algebraMap B L (ε a))
    (hA : ringKrullDim A = 1) (hB : ringKrullDim B = 1) :
    AlgebraicGeometry.TameSymbol (A := B) (K := L) hB where
  toFun x y := Units.map (IsLocalRing.ResidueField.mapEquiv ε).toMonoidHom
    (tameSymbol (K := K) hA (Units.map (η.symm : L →+* K).toMonoidHom x)
      (Units.map (η.symm : L →+* K).toMonoidHom y))
  map_mul_left x x' y := by
    rw [map_mul, (tameSymbol (K := K) hA).map_mul_left, map_mul]
  map_mul_right x y y' := by
    rw [map_mul, (tameSymbol (K := K) hA).map_mul_right, map_mul]
  eq_moduleSymbol y₁ y₂ hy₁ hy₂ := by
    have hu : ∀ (y : B) (hy : IsRegular y),
        Units.map (η.symm : L →+* K).toMonoidHom
            (IsLocalization.map_units L
              (⟨y, isRegular_iff_mem_nonZeroDivisors.mp hy⟩ : nonZeroDivisors B)).unit =
          (IsLocalization.map_units K
            (⟨ε.symm y, isRegular_iff_mem_nonZeroDivisors.mp
              (isRegular_ringEquiv_symm ε hy)⟩ : nonZeroDivisors A)).unit := by
      intro y hy
      exact Units.ext (ringEquiv_symm_algebraMap ε η hcompat y)
    rw [hu y₁ hy₁, hu y₂ hy₂,
      (tameSymbol (K := K) hA).eq_moduleSymbol (ε.symm y₁) (ε.symm y₂)
        (isRegular_ringEquiv_symm ε hy₁) (isRegular_ringEquiv_symm ε hy₂),
      map_moduleSymbol_ringEquiv ε (ε.symm y₁) (ε.symm y₂) _ _
        (by rw [ε.apply_symm_apply]; exact hy₁.isSMulRegular)
        (by rw [ε.apply_symm_apply]; exact hy₂.isSMulRegular)
        ((Module.supportDim_self_eq_ringKrullDim A).trans hA)
        ((Module.supportDim_self_eq_ringKrullDim B).trans hB)]
    simp only [ε.apply_symm_apply]

/-- **The tame symbol of Stacks 02Q1 is transported by an isomorphism of pairs.** Let
`ε : A ≃+* B` be an isomorphism of one-dimensional Noetherian local domains and let
`η : K ≃+* L` be an isomorphism of their fraction fields compatible with `ε`. Then the induced
isomorphism of residue fields carries `∂_A(f, g)` to `∂_B(η f, η g)`.

This is `Stacks.Chow.tameSymbolTransport` recognized as the tame symbol of `B` by the uniqueness
`Stacks.Chow.tameSymbolData_eq`. -/
theorem map_tameSymbol_ringEquiv (ε : A ≃+* B) (η : K ≃+* L)
    (hcompat : ∀ a : A, η (algebraMap A K a) = algebraMap B L (ε a))
    (hA : ringKrullDim A = 1) (hB : ringKrullDim B = 1) (f g : Kˣ) :
    Units.map (IsLocalRing.ResidueField.mapEquiv ε).toMonoidHom
        (tameSymbol (K := K) hA f g) =
      tameSymbol (K := L) hB (Units.map (η : K →+* L).toMonoidHom f)
        (Units.map (η : K →+* L).toMonoidHom g) := by
  have h := eq_tameSymbol hB (tameSymbolTransport ε η hcompat hA hB)
    (Units.map (η : K →+* L).toMonoidHom f) (Units.map (η : K →+* L).toMonoidHom g)
  refine Eq.trans ?_ h
  have hinv : ∀ u : Kˣ, Units.map (η.symm : L →+* K).toMonoidHom
      (Units.map (η : K →+* L).toMonoidHom u) = u := fun u => Units.ext (η.symm_apply_apply _)
  change _ = Units.map (IsLocalRing.ResidueField.mapEquiv ε).toMonoidHom
    (tameSymbol (K := K) hA _ _)
  rw [hinv, hinv]

end TameSymbolTransport

/-! ### Milnor K-groups transported along an isomorphism of fields -/

section MilnorTransport

variable {k₁ k₂ : Type u} [Field k₁] [Field k₂]

/-- **The degree-one Milnor K-group transported along an isomorphism of fields.** In degree one
the Milnor K-group is the unit group of the field read additively, so an isomorphism of fields
induces an isomorphism of degree-one Milnor K-groups. -/
def milnorKOneRingEquiv (φ : k₁ ≃+* k₂) : MilnorKTheory k₁ 1 ≃+ MilnorKTheory k₂ 1 :=
  (milnorKTheoryOneAddEquiv k₁).trans
    ((MulEquiv.toAdditive (Units.mapEquiv φ.toMulEquiv)).trans
      (milnorKTheoryOneAddEquiv k₂).symm)

/-- The degree-one transport is the map of unit groups, read through the identification of the
degree-one Milnor K-group with the unit group. -/
theorem milnorKOneRingEquiv_apply (φ : k₁ ≃+* k₂) (u : k₁ˣ) :
    milnorKOneRingEquiv φ ((milnorKTheoryOneAddEquiv k₁).symm (Additive.ofMul u)) =
      (milnorKTheoryOneAddEquiv k₂).symm (Additive.ofMul (Units.map φ.toMonoidHom u)) := by
  simp only [milnorKOneRingEquiv, AddEquiv.trans_apply, AddEquiv.apply_symm_apply]
  rfl

/-- The tensor square of the unit group, transported along an isomorphism of fields. -/
def milnorKTwoUnitsTensorEquiv (φ : k₁ ≃+* k₂) :
    TensorProduct ℤ (Additive k₁ˣ) (Additive k₁ˣ) ≃ₗ[ℤ]
      TensorProduct ℤ (Additive k₂ˣ) (Additive k₂ˣ) :=
  TensorProduct.congr
    (AddEquiv.toIntLinearEquiv (MulEquiv.toAdditive (Units.mapEquiv φ.toMulEquiv)))
    (AddEquiv.toIntLinearEquiv (MulEquiv.toAdditive (Units.mapEquiv φ.toMulEquiv)))

/-- `milnorKTwoUnitsTensorEquiv φ` sends `u ⊗ v` to `φ u ⊗ φ v`. -/
@[simp] theorem milnorKTwoUnitsTensorEquiv_tmul (φ : k₁ ≃+* k₂) (u v : k₁ˣ) :
    milnorKTwoUnitsTensorEquiv φ (Additive.ofMul u ⊗ₜ[ℤ] Additive.ofMul v) =
      Additive.ofMul (Units.map (φ : k₁ →+* k₂).toMonoidHom u) ⊗ₜ[ℤ]
        Additive.ofMul (Units.map (φ : k₁ →+* k₂).toMonoidHom v) := rfl

/-- **An isomorphism of fields carries the Steinberg submodule onto the Steinberg submodule.**
The generators are the tensors `x ⊗ (1 - x)` for `x` neither `0` nor `1`, and an isomorphism of
fields permutes those elements and commutes with `x ↦ 1 - x`. -/
theorem map_milnorKTwoSteinbergSubmodule (φ : k₁ ≃+* k₂) :
    Submodule.map (milnorKTwoUnitsTensorEquiv φ : _ →ₗ[ℤ] _)
        (milnorKTwoSteinbergSubmodule k₁) = milnorKTwoSteinbergSubmodule k₂ := by
  classical
  have hgen : ∀ (x : k₁) (hx0 : x ≠ 0) (hx1 : x ≠ 1),
      milnorKTwoUnitsTensorEquiv φ (Additive.ofMul (Units.mk0 x hx0) ⊗ₜ[ℤ]
          Additive.ofMul (Units.mk0 (1 - x) (sub_ne_zero.mpr (Ne.symm hx1)))) =
        Additive.ofMul (Units.mk0 (φ x) (by simpa using hx0)) ⊗ₜ[ℤ]
          Additive.ofMul (Units.mk0 (1 - φ x)
            (sub_ne_zero.mpr (Ne.symm (by simpa using hx1)))) := by
    intro x hx0 hx1
    rw [milnorKTwoUnitsTensorEquiv_tmul]
    refine congrArg₂ (TensorProduct.tmul ℤ) (congrArg Additive.ofMul (Units.ext rfl))
      (congrArg Additive.ofMul (Units.ext ?_))
    change φ (1 - x) = 1 - φ x
    rw [map_sub, map_one]
  rw [milnorKTwoSteinbergSubmodule, milnorKTwoSteinbergSubmodule, Submodule.map_span]
  refine congrArg (Submodule.span ℤ) (Set.ext fun z => ⟨?_, ?_⟩)
  · rintro ⟨-, ⟨x, rfl⟩, rfl⟩
    exact ⟨⟨φ x.1, by simpa using x.2.1,
      by simpa using x.2.2⟩,
      (hgen x.1 x.2.1 x.2.2).symm⟩
  · rintro ⟨y, rfl⟩
    have hy0 : φ.symm y.1 ≠ 0 := by simpa using y.2.1
    have hy1 : φ.symm y.1 ≠ 1 := by simpa using y.2.2
    refine ⟨_, ⟨⟨φ.symm y.1, hy0, hy1⟩, rfl⟩, ?_⟩
    refine (hgen (φ.symm y.1) hy0 hy1).trans ?_
    refine congrArg₂ (TensorProduct.tmul ℤ)
      (congrArg Additive.ofMul (Units.ext (φ.apply_symm_apply y.1)))
      (congrArg Additive.ofMul (Units.ext ?_))
    change (1 : k₂) - φ (φ.symm y.1) = 1 - y.1
    rw [φ.apply_symm_apply]

/-- **The degree-two Milnor K-group transported along an isomorphism of fields.** The group is
presented as the tensor square of the unit group modulo the Steinberg relations, and an
isomorphism of fields carries that presentation to the presentation of the target. -/
def milnorKTwoRingEquiv (φ : k₁ ≃+* k₂) : MilnorKTheory k₁ 2 ≃+ MilnorKTheory k₂ 2 :=
  ((milnorKTwoEquivTensorProductQuotient k₁).trans
    ((Submodule.Quotient.equiv (milnorKTwoSteinbergSubmodule k₁)
        (milnorKTwoSteinbergSubmodule k₂) (milnorKTwoUnitsTensorEquiv φ)
        (map_milnorKTwoSteinbergSubmodule φ)).trans
      (milnorKTwoEquivTensorProductQuotient k₂).symm)).toAddEquiv

/-- The degree-two transport sends a pure symbol to the pure symbol of the images. -/
theorem milnorKTwoRingEquiv_pureSymbol (φ : k₁ ≃+* k₂) (f g : k₁ˣ) :
    milnorKTwoRingEquiv φ (milnorKTwoPureSymbol k₁ f g) =
      milnorKTwoPureSymbol k₂ (Units.map (φ : k₁ →+* k₂).toMonoidHom f)
        (Units.map (φ : k₁ →+* k₂).toMonoidHom g) := by
  have key : ∀ t : TensorProduct ℤ (Additive k₁ˣ) (Additive k₁ˣ),
      milnorKTwoRingEquiv φ
          ((milnorKTwoEquivTensorProductQuotient k₁).symm (Submodule.Quotient.mk t)) =
        (milnorKTwoEquivTensorProductQuotient k₂).symm
          (Submodule.Quotient.mk (milnorKTwoUnitsTensorEquiv φ t)) := by
    intro t
    change (milnorKTwoEquivTensorProductQuotient k₂).symm
        ((Submodule.Quotient.equiv (milnorKTwoSteinbergSubmodule k₁)
            (milnorKTwoSteinbergSubmodule k₂) (milnorKTwoUnitsTensorEquiv φ)
            (map_milnorKTwoSteinbergSubmodule φ))
          ((milnorKTwoEquivTensorProductQuotient k₁)
            ((milnorKTwoEquivTensorProductQuotient k₁).symm (Submodule.Quotient.mk t)))) =
      (milnorKTwoEquivTensorProductQuotient k₂).symm
        (Submodule.Quotient.mk (milnorKTwoUnitsTensorEquiv φ t))
    rw [LinearEquiv.apply_symm_apply]
    rfl
  rw [milnorKTwoPureSymbol, key, milnorKTwoUnitsTensorEquiv_tmul, milnorKTwoPureSymbol]

end MilnorTransport

/-! ### The Milnor K₂ tame-symbol boundary transported along an isomorphism of pairs -/

section MilnorBoundaryTransport

variable {A B : Type u} [CommRing A] [IsDomain A] [IsNoetherianRing A] [IsLocalRing A]
  [CommRing B] [IsDomain B] [IsNoetherianRing B] [IsLocalRing B]
  {K : Type u} [Field K] [Algebra A K] [IsFractionRing A K]
  {L : Type u} [Field L] [Algebra B L] [IsFractionRing B L]

/-- **The Milnor K₂ tame-symbol boundary is transported by an isomorphism of pairs.** Let
`ε : A ≃+* B` be an isomorphism of one-dimensional Noetherian local domains and let
`η : K ≃+* L` be a compatible isomorphism of their fraction fields. Then the square

`K₂ᴹ(K) ⟶ K₁ᴹ(κ(A))`, `K₂ᴹ(L) ⟶ K₁ᴹ(κ(B))`

formed by the two boundary maps of Stacks 0GU9 and the transports along `η` and along the induced
isomorphism of residue fields commutes.

This is what identifies the local component of the first differential of Stacks 0GU9, built from
the local ring at an intermediate point, with the summand of the local algebraic vanishing, built
from the localization of the local ring below at the corresponding height-one prime: the two rings
are isomorphic, and so are the two fraction fields, but nothing transported the boundary between
them.

The proof reduces to a pure symbol by `AlgebraicGeometry.milnorKTwo_induction` and is then
`Stacks.Chow.map_tameSymbol_ringEquiv`. -/
theorem milnorKTwoTameSymbol_ringEquiv (ε : A ≃+* B) (η : K ≃+* L)
    (hcompat : ∀ a : A, η (algebraMap A K a) = algebraMap B L (ε a))
    (hA : ringKrullDim A = 1) (hB : ringKrullDim B = 1) (α : MilnorKTheory K 2) :
    milnorKOneRingEquiv (IsLocalRing.ResidueField.mapEquiv ε)
        (milnorKTwoTameSymbol (A := A) (K := K) hA α) =
      milnorKTwoTameSymbol (A := B) (K := L) hB (milnorKTwoRingEquiv η α) := by
  induction α using milnorKTwo_induction with
  | hsymb f g =>
      rw [milnorKTwoTameSymbol_pureSymbol, milnorKOneRingEquiv_apply,
        milnorKTwoRingEquiv_pureSymbol, milnorKTwoTameSymbol_pureSymbol,
        map_tameSymbol_ringEquiv ε η hcompat hA hB f g]
  | hadd a b ha hb => rw [map_add, map_add, map_add, map_add, ha, hb]

end MilnorBoundaryTransport

end Stacks.Chow

end

end
