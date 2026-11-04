module

public import Mathlib.Algebra.Category.ModuleCat.ChangeOfRings
public import Mathlib.RingTheory.RingHom.Flat
public import Mathlib.RingTheory.TensorProduct.Basic

/-!
# Extension of scalars: the base ring, and flatness

Let `f : R →+* S` be a homomorphism of commutative rings. Extension of scalars along `f` sends
the base ring `R` to `S ⊗_R R`, which is `S`, and sends an injective `R`-linear map to an
injective `S`-linear map as soon as `S` is flat over `R`.

## Main definitions

* `ModuleCat.ExtendScalars.objSelfIso`: the isomorphism `S ⊗_R R ≅ S`, the value of extension of
  scalars on the base ring.

## Main results

* `ModuleCat.ExtendScalars.hom_ext_one_tmul`: two `S`-linear maps out of `S ⊗_R M` agree as
  soon as they agree on the elements `1 ⊗ m`.
* `ModuleCat.ExtendScalars.objSelfIso_hom_tmul` and
  `ModuleCat.ExtendScalars.objSelfIso_inv_apply`: the isomorphism is `s ⊗ r ↦ s · f r`, with
  inverse `s ↦ s ⊗ 1`.
* `ModuleCat.ExtendScalars.injective_map_of_flat`: **extension of scalars along a flat ring map
  preserves injectivity.**

## Implementation notes

The `Module R S` instance carried by `(ModuleCat.extendScalars f).obj M` is
`Module.compHom S f`, not `Algebra.toModule` for `f.toAlgebra`. The two are definitionally equal
but not syntactically so: a rewrite across that boundary fails to match, and the motive it would
need is not type-correct at the transparency `rw` uses.

## References

* [Stacks Project, Tag 00HL](https://stacks.math.columbia.edu/tag/00HL)
-/

@[expose] public noncomputable section

open CategoryTheory TensorProduct
open scoped ChangeOfRings

universe u

namespace ModuleCat.ExtendScalars

variable {R S : Type u} [CommRing R] [CommRing S] (f : R →+* S)

/-- Two `S`-linear maps out of `S ⊗_R M` agree as soon as they agree on the elements `1 ⊗ m`.
This is `ModuleCat.ExtendScalars.hom_ext` with the hypothesis written in the `⊗ₜ[R,f]` spelling
of the tensor product. -/
lemma hom_ext_one_tmul {M : ModuleCat.{u} R} {N : ModuleCat.{u} S}
    {α β : (ModuleCat.extendScalars f).obj M ⟶ N}
    (h : ∀ m : M, α ((1 : S) ⊗ₜ[R,f] m) = β ((1 : S) ⊗ₜ[R,f] m)) : α = β :=
  ModuleCat.ExtendScalars.hom_ext h

/-- **Extension of scalars takes the base ring to the base ring:** `S ⊗_R R ≅ S`. This is the
right unitor `TensorProduct.AlgebraTensorModule.rid`, read in the `ModuleCat.extendScalars`
spelling of the tensor product. -/
def objSelfIso : (ModuleCat.extendScalars f).obj (ModuleCat.of R R) ≅ ModuleCat.of S S :=
  let _ := f.toAlgebra
  (TensorProduct.AlgebraTensorModule.rid R S S).toModuleIso

/-- The isomorphism `objSelfIso f : S ⊗_R R ≅ S` sends `s ⊗ r` to `s * f r`. -/
@[simp] lemma objSelfIso_hom_tmul (s : S) (r : R) :
    (objSelfIso f).hom (s ⊗ₜ[R,f] r) = s * f r := by
  let _ := f.toAlgebra
  show (TensorProduct.AlgebraTensorModule.rid R S S) (s ⊗ₜ[R] r) = _
  rw [TensorProduct.AlgebraTensorModule.rid_tmul, Algebra.smul_def, mul_comm]
  rfl

/-- The inverse of `objSelfIso f : S ⊗_R R ≅ S` sends `s` to `s ⊗ 1`. -/
@[simp] lemma objSelfIso_inv_apply (s : S) :
    (objSelfIso f).inv s = s ⊗ₜ[R,f] (1 : R) := by
  let _ := f.toAlgebra
  show (TensorProduct.AlgebraTensorModule.rid R S S).symm s = _
  rfl

/-- **Extension of scalars along a flat ring map preserves injectivity.** -/
lemma injective_map_of_flat (hf : f.Flat) {M N : ModuleCat.{u} R} (u : M ⟶ N)
    (hu : Function.Injective u.hom) :
    Function.Injective ((ModuleCat.extendScalars f).map u) := by
  let _ := f.toAlgebra
  have _ : Module.Flat R S := hf
  have h := Module.Flat.lTensor_preserves_injective_linearMap (M := S) u.hom hu
  rwa [← LinearMap.baseChange_eq_ltensor] at h

end ModuleCat.ExtendScalars

end
