module

public import StacksCore.Tactic.StacksAttribute
public import StacksFrontier.AlgebraicGeometry.PicardBaseChange.MulIsomorphism
public import StacksFrontier.AlgebraicGeometry.TensorPowerCoherence.NegOne

/-!
# The multiplication clause of Tag 0CDX, stated with the coherent multiplication of Tag 01CU

Let `X` be a quasi-compact, quasi-separated scheme over a ring `A`, let `φ : A →+* B` be
faithfully flat, and let `L` be an invertible `𝒪_X`-module whose pullback to `X_B` is trivial.
[Stacks, Tag 0CDX](https://stacks.math.columbia.edu/tag/0CDX) asserts, among other things, that
the canonical multiplication

`Γ(X, L) ⊗_{Γ(X, 𝒪_X)} Γ(X, L^{⊗ -1}) ⟶ Γ(X, 𝒪_X)`

is an isomorphism, where the multiplication is the one supplied by the coherent multiplication
of the integer tensor powers of [Stacks, Tag 01CU](https://stacks.math.columbia.edu/tag/01CU).

`StacksFrontier/AlgebraicGeometry/PicardBaseChange/MulIsomorphism.lean` proves the statement
with the multiplication spelled `Stacks.SheafOfModules.Invertible.globalSectionsMulNegOne`, the
composite built by hand out of the braiding, `tensorPowerOneIso` and one step of the defining
integer iteration. `StacksFrontier/AlgebraicGeometry/TensorPowerCoherence/NegOne.lean` proves
that that composite *is* the coherent multiplication in degrees `(1, -1)`. This file combines
the two, so the statement below is about Tag 01CU's own multiplication and is the clause the tag
asserts.

## Main results

* `Stacks.AlgebraicGeometry.PicardBaseChange`
  `.exists_mulEquiv_globalSections_coherentMul_of_faithfullyFlat_trivialization`:
  **Stacks Project, Tag 0CDX, the clause that the multiplication is an isomorphism**, with the
  multiplication written out as the coherent multiplication of Tag 01CU.

## Implementation notes

The multiplication is written out rather than abbreviated: the pure tensor `s ⊗ t` of a global
section of `L` and a global section of `L^{⊗ -1}` is carried by `tensorPowerOneIso` into the
first tensor power, then by the sheafification unit
  `Stacks.SheafOfModules.TensorSheafification.toSheafify` into the sheaf tensor
product `L^{⊗ 1} ⊗ L^{⊗ -1}`, where the coherent multiplication isomorphism
`(tensorPowerCoherence _ _ L).mulIso 1 (-1)` evaluates it. Specifying the multiplication this way
is what makes the statement a statement about multiplication rather than about the existence of
some module isomorphism.

The module structure on `(L^{⊗ -1}).val.obj (op ⊤)` is supplied explicitly: the tensor power has
type `SheafOfModules (Stacks.SheafOfModules.TensorSheafification.structureSheaf X.presheaf
  X.ringCatSheaf.property)`, which is
only definitionally `X.Modules`, so the `Γ(·, ·)` notation's instances are not found for it.

The invertibility class is `AlgebraicGeometry.SheafOfModules.IsInvertible`, written out in full
because a bare `IsInvertible` binder inside a `Stacks.*` namespace resolves by prefix and can
silently name `Stacks.SheafOfModules.IsInvertible`, a different class with no bridge by instance
search. The integer tensor power is `Stacks.SheafOfModules.Invertible.tensorPower`
(`StacksFrontier/AlgebraicGeometry/Divisors/TensorPower.lean`), which is the one keyed on that same
class; the repository's other `tensorPower` of the same tag,
`Stacks.SheafOfModules.TensorPower.tensorPower`, is keyed on the other class, and nothing here
identifies the two.

## References

* [Stacks Project, Tag 0CDX](https://stacks.math.columbia.edu/tag/0CDX)
* [Stacks Project, Tag 01CU](https://stacks.math.columbia.edu/tag/01CU)
-/

@[expose] public noncomputable section

universe u

open CategoryTheory CategoryTheory.Limits TopologicalSpace Opposite AlgebraicGeometry
open Stacks.SheafOfModules.Invertible
open scoped TensorProduct

namespace Stacks.AlgebraicGeometry.PicardBaseChange

/-- **Stacks Project, Tag 0CDX, the clause that the multiplication is an isomorphism.** For a
quasi-compact, quasi-separated scheme `X` over `A`, a faithfully flat ring map `φ : A →+* B` and
an invertible `𝒪_X`-module `L` whose pullback to `X_B` is trivial, the canonical multiplication

`Γ(X, L) ⊗_{Γ(X, 𝒪_X)} Γ(X, L^{⊗ -1}) ⟶ Γ(X, 𝒪_X)`

is an isomorphism. The multiplication is the coherent multiplication of Tag 01CU in degrees
`(1, -1)`, written out on pure tensors. -/
@[stacks 0CDX "multiplication is an isomorphism"]
theorem exists_mulEquiv_globalSections_coherentMul_of_faithfullyFlat_trivialization
    {A B : Type u} [CommRing A] [CommRing B] (φ : A →+* B) (hφ : φ.FaithfullyFlat)
    {X : Scheme.{u}} (f : X ⟶ Spec (.of A)) [CompactSpace X] [QuasiSeparatedSpace X]
    (L : X.Modules)
    [_root_.AlgebraicGeometry.SheafOfModules.IsInvertible X.presheaf X.ringCatSheaf.property L]
    (hL : _root_.AlgebraicGeometry.SheafOfModules.IsTrivial
      (Limits.pullback f (Spec.map (CommRingCat.ofHom φ))).presheaf
      (Limits.pullback f (Spec.map (CommRingCat.ofHom φ))).ringCatSheaf.property
      ((Scheme.Modules.pullback
        (Limits.pullback.fst f (Spec.map (CommRingCat.ofHom φ)))).obj L)) :
    letI : Module Γ(X, ⊤)
        ((tensorPower X.presheaf X.ringCatSheaf.property L (-1)).val.obj (.op ⊤)) :=
      ((tensorPower X.presheaf X.ringCatSheaf.property L (-1)).val.obj (.op ⊤)).isModule
    ∃ e : TensorProduct Γ(X, ⊤) Γ(L, ⊤)
        ((tensorPower X.presheaf X.ringCatSheaf.property L (-1)).val.obj (.op ⊤))
        ≃ₗ[Γ(X, ⊤)] Γ(X, ⊤),
      ∀ s t, e (TensorProduct.tmul Γ(X, ⊤) s t) =
        (((tensorPowerCoherence X.presheaf X.ringCatSheaf.property L).mulIso 1 (-1)).hom.val.app
            (.op ⊤)).hom
          (((Stacks.SheafOfModules.TensorSheafification.toSheafify X.presheaf
            X.ringCatSheaf.property
            ((PresheafOfModules.tensorObj (O := X.presheaf)
              ((tensorPower X.presheaf X.ringCatSheaf.property L 1).val)
              ((tensorPower X.presheaf X.ringCatSheaf.property L (-1)).val)))).app (.op ⊤)).hom
            ((((tensorPowerOneIso X.presheaf X.ringCatSheaf.property L).inv.val.app
              (.op ⊤)).hom s) ⊗ₜ[Γ(X, ⊤)] t)) := by
  obtain ⟨e, he⟩ :=
    exists_mulEquiv_globalSections_of_faithfullyFlat_trivialization φ hφ f L hL
  exact ⟨e, fun s t => (he s t).trans (globalSectionsMulNegOne_eq_coherent L s t)⟩

end Stacks.AlgebraicGeometry.PicardBaseChange

end
