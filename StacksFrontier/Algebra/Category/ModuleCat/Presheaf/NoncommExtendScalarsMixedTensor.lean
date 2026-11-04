module

public import StacksFrontier.Algebra.Category.ModuleCat.NoncommBaseChangeComm
public import StacksFrontier.Algebra.Category.ModuleCat.Presheaf.NoncommBaseChange
public import StacksFrontier.CategoryTheory.Sites.Modules.MixedUniverseTensor

/-!
# Objectwise extension of scalars, read back, is the objectwise tensor product

Let `α : 𝒪 ⟶ 𝒜` be a morphism of presheaves of rings on a category `C` whose source is the
presheaf of rings underlying a presheaf `R₁` of *commutative* rings, and suppose the sections of
`𝒜` commute.  Objectwise extension of scalars along `α`,
`Stacks.NoncommChangeOfRings.Presheaf.extendScalarsObj`, has sections `𝒜(V) ⊗_{𝒪(V)} M(V)`
carrying their `𝒜(V)`-action; reading those back as `𝒪(V)`-modules along `α` gives the objectwise
tensor product `PresheafOfModules.MixedTensor.tensorObj` of `𝒜`, read as a presheaf of
`𝒪`-modules, with `M`.

This is the identification that the tensor-product clause of Stacks 03M1 needs in order to apply
to a change of rings: the quasi-coherence of a tensor product is proved on a site for the
sheafification of the universe lift `PresheafOfModules.uliftSections` of
`PresheafOfModules.MixedTensor.tensorObj`, and extension of scalars for sheaves of modules is
`extendScalarsObj` sheafified, so the two are compared here, before any sheafification.

## Main definitions

* `Stacks.NoncommChangeOfRings.restrictExtendTensorEquiv`: the sectionwise comparison, an
  `A`-linear equivalence `B ⊗[A] M ≃ₗ[A] B ⊗[A] M` between the relative tensor product of
  `Stacks.NoncommChangeOfRings.BaseChange` read along `f : A →+* B` and the tensor product of
  `ModuleCat.MixedTensor.tensorObj`.
* `Stacks.NoncommChangeOfRings.Presheaf.tensorObjIsoRestrictExtend`: **the identification itself**,
  as an isomorphism of presheaves of `𝒪`-modules.

## Implementation notes

The mathematical content — that the relative tensor product along a ring homomorphism of
commutative rings is Mathlib's tensor product — is *not* re-proved here: it is
`Stacks.NoncommChangeOfRings.baseChangeTensorEquiv`, together with its values on pure tensors.
What is added is the linearity over the source ring, which that additive equivalence does not
record, and the packaging as an isomorphism of presheaves of modules.

`Stacks.NoncommChangeOfRings.extendScalarsCompRestrictScalarsIsoTensorLeft` of
`StacksFrontier/Cotangent/SurjectionSiteProNilpotent.lean` is the functor-level statement of the
same sectionwise comparison, for Mathlib's monoidal `CategoryTheory.tensorLeft` rather than for
`ModuleCat.MixedTensor.tensorObj`.  It is not used, and could not be: it is built by uniqueness
of left adjoints, so nothing is known about its value on a pure tensor, and the naturality square
below is proved by computing both sides on pure tensors.  The equivalence here, whose value on
`b ⊗ m` is `b ⊗ m` by `rfl`, makes that square hold by `rfl`.

**Commutativity is a plain hypothesis, not an instance.**
`Stacks.NoncommChangeOfRings.baseChangeTensorEquiv` is stated for `[CommRing B]` and the
structure map of an algebra, whereas the sections of a presheaf of rings on a site carry only a
`Ring` instance.  Introducing `CommRing` as an instance in the *statement* would change which
`Ring` instance `ModuleCat.of B B` is formed with, and the statement would then no longer be
about the given presheaf of modules.  So commutativity of the sections is taken as an
argument and the `CommRing` and `Algebra` instances are introduced inside the proof, where they
are definitionally the ones already there.

The isomorphism is built in the direction *out of* the tensor product.  That is what makes it
cheap: a morphism out of a tensor product is determined by its values on pure tensors
(`ModuleCat.MixedTensor.tensor_ext`), the inverse comparison sends `b ⊗ m` to `b ⊗ m` by
`Stacks.NoncommChangeOfRings.baseChangeTensorEquiv_symm_tmul`, which is `rfl`, and the
restriction maps of both sides are given on pure tensors by `rfl` as well
(`Stacks.NoncommChangeOfRings.Presheaf.extendScalarsObj_map_objTmul` and
`PresheafOfModules.MixedTensor.tensorObj_map_tmul`).  Stated in the other direction the same
square would have to be checked on a morphism *into* a tensor product, for which there is no
such extensionality.

Stacks 03CZ is the adjunction between extension and restriction of scalars; what is below is not
that adjunction but a comparison of two constructions of one and the same presheaf of modules.

## References

* [Stacks Project, Tag 03CZ](https://stacks.math.columbia.edu/tag/03CZ)
* [Stacks Project, Tag 03CU](https://stacks.math.columbia.edu/tag/03CU)
* [Stacks Project, Tag 03M1](https://stacks.math.columbia.edu/tag/03M1)
-/

@[expose] public section

open CategoryTheory TensorProduct

universe v₁ u₁ u

namespace Stacks.NoncommChangeOfRings

/-! ### The sectionwise comparison -/

section Mod

variable {A : Type u} [CommRing A] {B : Type u} [Ring B] (f : A →+* B)
  (hcomm : ∀ a b : B, a * b = b * a) (M : ModuleCat.{u} A)

include hcomm in
/-- **The relative tensor product along `f : A →+* B`, read back as an `A`-module, is the tensor
product of `B` with `M` over `A`.**  Here `B` is commutative, by the hypothesis `hcomm`, and is
read as an `A`-module along `f`.

The map is `Stacks.NoncommChangeOfRings.baseChangeTensorEquiv`, which carries a pure tensor to
the pure tensor with the same factors; what is proved is that it is linear over `A`, the scalar
`r` acting on the source through `f`. -/
noncomputable def restrictExtendTensorEquiv :
    ((ModuleCat.restrictScalars f).obj ((extendScalars f).obj M) : Type u) ≃ₗ[A]
      (ModuleCat.MixedTensor.tensorObj
        ((ModuleCat.restrictScalars f).obj (ModuleCat.of B B)) M : Type u) := by
  letI : CommRing B := { ‹Ring B› with mul_comm := hcomm }
  letI : Algebra A B := f.toAlgebra
  refine AddEquiv.toLinearEquiv (baseChangeTensorEquiv (A := A) (B := B) (M := M))
    (fun (r : A) x => ?_)
  exact (map_smul (toTensor (A := A) (B := B) (M := (M : Type u))) (f r) x).trans
    (algebraMap_smul B r _)

end Mod

/-! ### The comparison of presheaves of modules -/

namespace Presheaf

variable {C : Type u₁} [Category.{v₁} C] {R₁ : Cᵒᵖ ⥤ CommRingCat.{u}}
  {R' : Cᵒᵖ ⥤ RingCat.{u}}
  (α : (R₁ ⋙ forget₂ CommRingCat.{u} RingCat.{u}) ⟶ R')
  (hcomm : ∀ (V : Cᵒᵖ) (a b : R'.obj V), a * b = b * a)

include hcomm in
/-- **The objectwise tensor product of `R'`, read as a presheaf of `R₁`-modules, with `M` is the
objectwise extension of scalars of `M` along `α`, read back as a presheaf of `R₁`-modules.**

Both sides have `R'(V) ⊗_{R₁(V)} M(V)` for their sections over `V`, with the `R₁(V)`-action
through `α`; the comparison is `Stacks.NoncommChangeOfRings.restrictExtendTensorEquiv` over each
object, and its naturality holds by `rfl`, both restriction maps being the tensor of the two
restriction maps on pure tensors. -/
noncomputable def tensorObjIsoRestrictExtend
    (M : PresheafOfModules.{u} (R₁ ⋙ forget₂ CommRingCat.{u} RingCat.{u})) :
    PresheafOfModules.tensorObj (O := R₁)
        ((PresheafOfModules.restrictScalars α).obj (PresheafOfModules.unit R')) M ≅
      (PresheafOfModules.restrictScalars α).obj (extendScalarsObj.{u} α M) :=
  PresheafOfModules.isoMk
    (fun V => (restrictExtendTensorEquiv (α.app V).hom (hcomm V) (M.obj V)).symm.toModuleIso)
    (fun {_ _} _ => ModuleCat.MixedTensor.tensor_ext fun _ _ => rfl)

end Presheaf

end Stacks.NoncommChangeOfRings

end
