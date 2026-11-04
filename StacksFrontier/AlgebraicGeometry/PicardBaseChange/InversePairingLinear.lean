module

public import StacksFrontier.AlgebraicGeometry.PicardBaseChange.InversePairing

/-!
# The multiplication against the inverse tensor power as a linear map

`StacksFrontier/AlgebraicGeometry/PicardBaseChange/InversePairing.lean` defines the product
`Stacks.SheafOfModules.Invertible.globalSectionsMulNegOne` of a global section of an invertible
module sheaf `L` on a scheme and a global section of its inverse tensor power `L^{⊗ -1}`, as a
*function* of the two sections. [Stacks, Tag 0CDX] asserts that this product is an isomorphism
of `Γ(X, 𝒪_X)`-modules

`Γ(X, L) ⊗_{Γ(X, 𝒪_X)} Γ(X, L^{⊗ -1}) ≅ Γ(X, 𝒪_X)`,

so the product has first of all to be presented as a linear map out of the tensor product. This
file does that, and does it with no linearity side conditions to prove: the product is a
composition of three linear maps, so the linear map is assembled rather than verified.

## Main definitions

* `Stacks.SheafOfModules.Invertible.tensorPowerModule`: the integer tensor power of an
  invertible module sheaf on a scheme, ascribed at `X.Modules`.
* `Stacks.SheafOfModules.Invertible.globalSectionsMulNegOneLinear`: the product of a global
  section of `L` and a global section of `L^{⊗ -1}`, as a `Γ(X, 𝒪_X)`-linear map out of
  `Γ(X, L) ⊗_{Γ(X, 𝒪_X)} Γ(X, L^{⊗ -1})`.

## Main results

* `Stacks.SheafOfModules.Invertible.globalSectionsMulNegOneLinear_tmul`: it is the product, on
  a pure tensor. This is what makes a statement about the linear map a statement about
  multiplication, rather than about an unspecified map of modules.

## Implementation notes

**Why the ascription at `X.Modules` is the whole trick.** `tensorPower X.presheaf
X.ringCatSheaf.property L n` has type `SheafOfModules
  (Stacks.SheafOfModules.TensorSheafification.structureSheaf X.presheaf
X.ringCatSheaf.property)`, which is definitionally but not syntactically `X.Modules`, and
instance search is syntactic. So the `Γ(X, 𝒪_X)`-module structure on its global sections is not
found, and a statement about it has to carry the structure explicitly as
`letI : Module Γ(X, ⊤) _ := (…).isModule`, which is how the Chapter 33 decomposition of
Tag 0CDX and `StacksFrontier/AlgebraicGeometry/PicardBaseChange/InverseSections.lean` state the invertibility clauses. That
ascription is enough for an invertibility *statement*, but not for a tensor product: `→ₗ` over
the tensor product needs an `AddCommMonoid` on a space of linear maps, hence the `Module`
instance on the *domain*, and the `letI` is not seen there. `tensorPowerModule` is the `abbrev`
at the consumer's spelling that removes the problem at the root — the same cure as
`Stacks.AlgebraicGeometry.PicardBaseChange.unitModule`. With it, no `letI` and no transparency
lever appears anywhere below.

**Why there are no linearity proofs.** Writing the product as an honest composition

`Γ(X, L) ⊗ Γ(X, L^{⊗ -1}) --(α ⊗ id)--> Γ(X, L^{⊗ 1}) ⊗ Γ(X, L^{⊗ -1})`
`  --β--> Γ(X, T) --γ--> Γ(X, 𝒪_X)`

— with `α` the identification `L ≅ L^{⊗ 1}`, `β` the sheafification unit of the tensor presheaf
and `γ` the multiplication isomorphism `tensorPowerMulIsoNegOne` — makes bilinearity a
consequence of the construction, and `globalSectionsMulNegOneLinear_tmul` is `rfl`. Proving
bilinearity instead, from the same three maps, requires rewriting with
`TensorProduct.tmul_add`/`tmul_smul` inside the goal, and those rewrites do not fire: the
tensor product's scalars are spelled `(X.presheaf ⋙ forget₂ CommRingCat RingCat).obj (op ⊤)`
where the lemma's pattern wants a bare `CommSemiring`, and `rw` does not match it at reducible
transparency. The three component maps are each ascribed at the `Γ(X, ⊤)` spelling, which is
what lets them be composed at all: composing the `ModuleCat` morphisms directly fails to
synthesize `RingHomCompTriple` for the three definitionally-equal spellings of the ring.

**What this is for, and what is still owed.** With this map as its `μ`, the multiplication
clause of Tag 0CDX reduces — under `Module.Invertible.exists_mulEquiv_of_lTensor_surjective`
of `StacksFrontier/AlgebraicGeometry/PicardBaseChange/Basic.lean`, whose two `Module.Invertible` hypotheses are the clauses
proved in `StacksFrontier/AlgebraicGeometry/PicardBaseChange/Sections.lean` and `StacksFrontier/AlgebraicGeometry/PicardBaseChange/InverseSections.lean`
— to the single goal

`Function.Surjective (LinearMap.lTensor Γ(X_B, 𝒪_{X_B}) globalSectionsMulNegOneLinear)`,

and to nothing else: the two invertibilities, the faithful flatness of
`Γ(X, 𝒪_X) → Γ(X_B, 𝒪_{X_B})` and the identification of the equivalence with the product on
pure tensors are all discharged. The compatibility of the product with
the base change is available in the development: `Stacks.RingedSpace.pullbackBilinear`
and `Stacks.RingedSpace.pullbackBilinear_pullbackUnit` of
`StacksFrontier/AlgebraicGeometry/PullbackTensor/Bilinear.lean` pull a bilinear map of
sections back along a morphism of ringed spaces and prove that the pullback of a product is the
product of the pullbacks, unconditionally. What remains is to present
`tensorPowerMulIsoNegOne` as a `SheafOfModules.BilinearMap`, read that identity at the total
open, and combine it with
`Stacks.AlgebraicGeometry.SectionsBaseChange.isBaseChange_appTop_pullbackSections`.

## References

* [Stacks Project, Tag 0CDX](https://stacks.math.columbia.edu/tag/0CDX)
* [Stacks Project, Tag 01CU](https://stacks.math.columbia.edu/tag/01CU)
-/

@[expose] public noncomputable section

open CategoryTheory Opposite TopologicalSpace AlgebraicGeometry TensorProduct
open AlgebraicGeometry.SheafOfModules (IsInvertible)

universe u

namespace Stacks.SheafOfModules.Invertible

/-- **The integer tensor power of an invertible module sheaf on a scheme, ascribed at
`X.Modules`.** `tensorPower X.presheaf X.ringCatSheaf.property L n` is only *definitionally*
an object of `X.Modules`, so the `Γ(X, 𝒪_X)`-module structure on its sections is not found by
instance search; at this spelling it is. -/
abbrev tensorPowerModule {X : Scheme.{u}} (L : X.Modules)
    [IsInvertible X.presheaf X.ringCatSheaf.property L] (n : ℤ) : X.Modules :=
  tensorPower X.presheaf X.ringCatSheaf.property L n

variable {X : Scheme.{u}} (L : X.Modules)
  [IsInvertible X.presheaf X.ringCatSheaf.property L]

/-- **The product of a global section of `L` and a global section of `L^{⊗ -1}`, as a linear
map out of the tensor product of the two modules of global sections.** This is the map that
[Stacks, Tag 0CDX] asserts to be an isomorphism.

It is the composition of the identification `L ≅ L^{⊗ 1}` in the first factor, the
sheafification unit of the tensor presheaf, and the multiplication isomorphism
`Stacks.SheafOfModules.Invertible.tensorPowerMulIsoNegOne`; being a composition of linear maps,
it needs no bilinearity verification. -/
def globalSectionsMulNegOneLinear :
    Γ(L, ⊤) ⊗[Γ(X, ⊤)] Γ(tensorPowerModule L (-1), ⊤) →ₗ[Γ(X, ⊤)] Γ(X, ⊤) :=
  let T : X.Modules :=
    (((Stacks.SheafOfModules.Tensor.sheafTensor
      ⟨X.presheaf, Presheaf.isSheaf_of_isSheaf_comp _ (X.presheaf) (forget₂ CommRingCat RingCat)
        (X.ringCatSheaf.property)⟩).obj ((tensorPowerModule L 1))).obj
          ((tensorPowerModule L (-1))))
  let γ : Γ(T, ⊤) →ₗ[Γ(X, ⊤)] Γ(X, ⊤) :=
    ((tensorPowerMulIsoNegOne X.presheaf X.ringCatSheaf.property L).hom.val.app (.op ⊤)).hom
  let β : Γ(tensorPowerModule L 1, ⊤) ⊗[Γ(X, ⊤)] Γ(tensorPowerModule L (-1), ⊤) →ₗ[Γ(X, ⊤)]
      Γ(T, ⊤) :=
    ((Stacks.SheafOfModules.TensorSheafification.toSheafify X.presheaf X.ringCatSheaf.property
      ((PresheafOfModules.tensorObj (O := X.presheaf) ((tensorPowerModule L
        1).val) ((tensorPowerModule L (-1)).val)))).app (.op ⊤)).hom
  let α : Γ(L, ⊤) →ₗ[Γ(X, ⊤)] Γ(tensorPowerModule L 1, ⊤) :=
    ((tensorPowerOneIso X.presheaf X.ringCatSheaf.property L).inv.val.app (.op ⊤)).hom
  (γ.comp β).comp (TensorProduct.map α LinearMap.id)

/-- **The linear map is the product.** On a pure tensor,
`globalSectionsMulNegOneLinear` is `globalSectionsMulNegOne`. -/
@[simp]
theorem globalSectionsMulNegOneLinear_tmul (s : Γ(L, ⊤))
    (t : Γ(tensorPowerModule L (-1), ⊤)) :
    globalSectionsMulNegOneLinear L (s ⊗ₜ[Γ(X, ⊤)] t) = globalSectionsMulNegOne L s t :=
  rfl

end Stacks.SheafOfModules.Invertible

end
