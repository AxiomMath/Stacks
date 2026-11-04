module

public import Mathlib.LinearAlgebra.Dimension.DivisionRing
public import Mathlib.LinearAlgebra.Dimension.RankNullity
public import Mathlib.RingTheory.Ideal.Cotangent
public import Mathlib.RingTheory.Ideal.Quotient.Operations
public import Mathlib.RingTheory.LocalRing.ResidueField.Basic

/-!
# The dimension of the second order jets of a local ring

Let `(R, 𝔪)` be a local ring and let `k` be a field mapping to `R`. The quotient `R/𝔪²`, the
second order jets of `R`, sits in the exact sequence

`0 → 𝔪/𝔪² → R/𝔪² → κ → 0`

of `k`-vector spaces, where `κ = R/𝔪` is the residue field, so its dimension over `k` is the
sum of the dimension of the cotangent space and the degree of the residue field.

## Main definitions

* `Stacks.LocalRing.MaximalIdealSq.toResidueField`: the `k`-algebra map `R/𝔪² → κ`.
* `Stacks.LocalRing.MaximalIdealSq.cotangentToQuotSq`: the `k`-linear inclusion `𝔪/𝔪² → R/𝔪²`.
* `Stacks.LocalRing.MaximalIdealSq.cotangentSpaceEquivKer`: the cotangent space is the kernel of
  `R/𝔪² → κ`.

## Main results

* `Stacks.LocalRing.MaximalIdealSq.finrank_quotient_maximalIdeal_sq`: **the dimension of `R/𝔪²`
  over `k` is `dim 𝔪/𝔪² + dim κ`.**

## Implementation notes

The two maps of the exact sequence are Mathlib's: `Ideal.cotangentToQuotientSquare` is the
injection `𝔪/𝔪² → R/𝔪²` and the surjection is `Ideal.Quotient.liftₐ` of the residue map, which
kills `𝔪²`. Both are `R`-linear and are restricted to `k` along the algebra map; the exactness
in the middle is the computation `Ideal.mk_mem_cotangentIdeal` of the image, matched against
`Ideal.Quotient.eq_zero_iff_mem` for the kernel.

Finiteness over `k` of `R/𝔪²`, which the rank-nullity theorem needs, is not assumed: it follows
from the two outer terms through `Module.Finite.of_submodule_quotient`, the cotangent space
being finite over `κ` for a Noetherian ring and `κ` finite over `k` by hypothesis.

No `@[stacks]` attribute is attached: this is a lemma of local algebra used in the dimension
count of [Stacks, Tag 0FD6], not the assertion of a tag.
-/

@[expose] public noncomputable section

open IsLocalRing

namespace Stacks.LocalRing.MaximalIdealSq

variable (k R : Type*) [Field k] [CommRing R] [IsLocalRing R] [Algebra k R]

/-- **The reduction `R/𝔪² → κ` of the second order jets to the residue field**, as a map of
`k`-algebras: the residue map kills `𝔪` and so in particular `𝔪²`. -/
def toResidueField : (R ⧸ maximalIdeal R ^ 2) →ₐ[k] ResidueField R :=
  Ideal.Quotient.liftₐ _ (IsScalarTower.toAlgHom k R (ResidueField R)) fun _ ha =>
    Ideal.Quotient.eq_zero_iff_mem.2 (Ideal.pow_le_self two_ne_zero ha)

/-- The reduction to the residue field sends the class of `a` to the residue of `a`. -/
@[simp]
theorem toResidueField_mk (a : R) :
    toResidueField k R (Ideal.Quotient.mk (maximalIdeal R ^ 2) a) = residue R a :=
  rfl

/-- The reduction to the residue field is surjective. -/
theorem surjective_toResidueField : Function.Surjective (toResidueField k R) :=
  Function.Surjective.of_comp (g := Ideal.Quotient.mk (maximalIdeal R ^ 2))
    (f := toResidueField k R) Ideal.Quotient.mk_surjective

/-- **The cotangent space inside the second order jets**: the injection `𝔪/𝔪² → R/𝔪²`, read
`k`-linearly. -/
def cotangentToQuotSq : CotangentSpace R →ₗ[k] (R ⧸ maximalIdeal R ^ 2) :=
  (Ideal.cotangentToQuotientSquare (maximalIdeal R)).restrictScalars k

/-- The inclusion `𝔪/𝔪² → R/𝔪²` is injective. -/
theorem injective_cotangentToQuotSq : Function.Injective (cotangentToQuotSq k R) :=
  Ideal.cotangentToQuotientSquare_injective _

/-- **Exactness in the middle**: the image of `𝔪/𝔪²` in `R/𝔪²` is the kernel of the reduction
to the residue field. -/
theorem range_cotangentToQuotSq :
    LinearMap.range (cotangentToQuotSq k R) =
      LinearMap.ker (toResidueField k R).toLinearMap := by
  refine le_antisymm ?_ fun q => Submodule.Quotient.induction_on _ q fun a hq => ?_
  · rintro _ ⟨c, rfl⟩
    obtain ⟨b, rfl⟩ := Ideal.toCotangent_surjective (maximalIdeal R) c
    exact (Ideal.Quotient.eq_zero_iff_mem.2 b.2 : residue R (b : R) = 0)
  · have h0 : residue R a = 0 := hq
    exact ⟨Ideal.toCotangent _ ⟨a, Ideal.Quotient.eq_zero_iff_mem.1 h0⟩, rfl⟩

/-- **The cotangent space is the kernel of the reduction `R/𝔪² → κ`.** -/
def cotangentSpaceEquivKer :
    CotangentSpace R ≃ₗ[k] LinearMap.ker (toResidueField k R).toLinearMap :=
  (LinearEquiv.ofInjective _ (injective_cotangentToQuotSq k R)).trans
    (LinearEquiv.ofEq _ _ (range_cotangentToQuotSq k R))

/-- The residue field of a local ring acts on its cotangent space compatibly with any field
mapping to the ring. -/
instance isScalarTower_residueField_cotangentSpace :
    IsScalarTower k (ResidueField R) (CotangentSpace R) :=
  IsScalarTower.of_algebraMap_smul fun c m => by
    rw [IsScalarTower.algebraMap_apply k R (ResidueField R), algebraMap_smul, algebraMap_smul]

variable [IsNoetherianRing R] [Module.Finite k (ResidueField R)]

/-- The cotangent space of a Noetherian local ring is finite over a field `k` mapping to the ring
whenever the residue field is finite over `k`. -/
instance finite_cotangentSpace : Module.Finite k (CotangentSpace R) :=
  Module.Finite.trans (ResidueField R) (CotangentSpace R)

/-- **The second order jets of a local ring have dimension `dim 𝔪/𝔪² + dim κ`** over a field
mapping to the ring: the exact sequence `0 → 𝔪/𝔪² → R/𝔪² → κ → 0` and rank-nullity. -/
theorem finrank_quotient_maximalIdeal_sq :
    Module.finrank k (R ⧸ maximalIdeal R ^ 2) =
      Module.finrank k (CotangentSpace R) + Module.finrank k (ResidueField R) := by
  set N := LinearMap.ker (toResidueField k R).toLinearMap with hN
  have equotient : ((R ⧸ maximalIdeal R ^ 2) ⧸ N) ≃ₗ[k] ResidueField R :=
    LinearMap.quotKerEquivOfSurjective _ (surjective_toResidueField k R)
  have : Module.Finite k N := Module.Finite.equiv (cotangentSpaceEquivKer k R)
  have : Module.Finite k ((R ⧸ maximalIdeal R ^ 2) ⧸ N) := Module.Finite.equiv equotient.symm
  have : Module.Finite k (R ⧸ maximalIdeal R ^ 2) := Module.Finite.of_submodule_quotient N
  have h := Submodule.finrank_quotient_add_finrank N
  rw [equotient.finrank_eq, ← (cotangentSpaceEquivKer k R).finrank_eq] at h
  omega

end Stacks.LocalRing.MaximalIdealSq

end
