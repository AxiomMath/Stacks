module

public import StacksCore.Tactic.StacksAttribute
public import StacksFrontier.Topology.Sheaves.Modules.AssociatedSheaf.Free

/-!
# Basis sections of a free sheaf of modules

On a ringed space `(X, 𝒪_X)`, the free sheaf of `𝒪_X`-modules on a type `I` is the sheaf
associated to the free `Γ(X, 𝒪_X)`-module on `I`, compatibly with the basis sections.

## Main definitions

* `Stacks.AssociatedSheaf.basisSection`: the `i`-th basis section of the free sheaf of modules on
  an open set, the image of `1` under the `i`-th summand inclusion.

## Main results

* `Stacks.AssociatedSheaf.exists_free_iso_associatedSheaf_freeModule`: the first half of
  **Tag 01BL**, the identification of the free sheaf of modules with the sheaf associated to a
  free module, carrying basis sections to the images of the standard basis under the unit of the
  tensor-sheafification adjunction.

## Implementation notes

`SheafOfModules.free` and `SheafOfModules.ιFree` are the library names for the coproduct of copies
of the structure sheaf and for its summand inclusions; `freeSheafIn` and
`freeSheafInι` are these, composed with a universe lift which is vacuous once the module universe
equals the universe of the ringed space. That specialisation is made here, so no lift appears.

The content is `Stacks.AssociatedSheaf.freeIsoAssociatedSheaf` together with
`Stacks.AssociatedSheaf.freeIsoAssociatedSheaf_hom_app_top`; this file only packages it in the
form the source statement takes, with the coefficient map the identity of the global sections.

## References

* [Stacks Project, Tag 01BL](https://stacks.math.columbia.edu/tag/01BL)
-/

@[expose] public noncomputable section

open AlgebraicGeometry CategoryTheory Opposite TopologicalSpace

namespace Stacks.AssociatedSheaf

universe u

attribute [local instance] hasModuleSheafify moduleSheafifyWEqualsLocallyBijective

/-- The `i`-th basis section of the free sheaf of `𝒪_X`-modules on an open set: the image of the
unit section of the structure sheaf under the `i`-th summand inclusion. -/
def basisSection (X : RingedSpace.{u, u}) (U : Opens X.carrier) {I : Type u} (i : I) :
    (SheafOfModules.free (R := structureSheafRing X) I).val.obj (op U) :=
  (SheafOfModules.ιFree (R := structureSheafRing X) i).val.app (op U)
    (1 : (structureSheafRing X).obj.obj (op U))

/-- **Stacks 01BL, first half.** The free sheaf of `𝒪_X`-modules on `I` is isomorphic to the sheaf
associated to the free `Γ(X, 𝒪_X)`-module on `I`, by an isomorphism carrying the `i`-th basis
section to the image of `Finsupp.single i 1` under the unit of the tensor-sheafification
adjunction. -/
@[stacks 01BL "associated free-module sheaves"]
theorem exists_free_iso_associatedSheaf_freeModule (X : RingedSpace.{u, u}) (I : Type u) :
    ∃ s : SheafOfModules.free (R := structureSheafRing X) I ≅
        associatedSheaf X (RingHom.id (X.presheaf.obj (op ⊤)))
          (ModuleCat.of (X.presheaf.obj (op ⊤))
            (I →₀ X.presheaf.obj (op ⊤))),
      ∀ i : I, s.hom.val.app (op ⊤) (basisSection X ⊤ i) =
        ((associatedSheafAdjunction.{u, u} X
          (RingHom.id (X.presheaf.obj (op ⊤)))).unit.app
          (ModuleCat.of (X.presheaf.obj (op ⊤))
            (I →₀ X.presheaf.obj (op ⊤)))) (Finsupp.single i 1) :=
  ⟨freeIsoAssociatedSheaf X (RingHom.id (X.presheaf.obj (op ⊤))) I,
    freeIsoAssociatedSheaf_hom_app_top X (RingHom.id (X.presheaf.obj (op ⊤))) I⟩

end Stacks.AssociatedSheaf
