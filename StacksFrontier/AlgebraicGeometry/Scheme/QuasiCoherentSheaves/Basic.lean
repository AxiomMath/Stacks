module

public import StacksFrontier.AlgebraicGeometry.Modules.TildeAssociatedSheaf
public import StacksCore.Tactic.StacksAttribute

/-!
# Quasi-coherent sheaves on an affine scheme

For a commutative ring `R` and an `R`-module `M`, the sheaf `M̃` on `Spec R` agrees canonically
with the sheaf obtained by sheafifying `U ↦ 𝒪(U) ⊗_R M`, and the comparison is natural in `M`.
The comparison is pinned down by its effect on global sections, where it sends `m` to `1 ⊗ m`.
Consequently `M̃` is quasi-coherent, and maps out of it are determined by their action on global
sections.

## Main definitions

* `AlgebraicGeometry.tildeAssociatedSheafNatIso` is the canonical natural comparison between the
  two constructions, together with the equation on global sections that characterizes it.

## Main results

* `AlgebraicGeometry.tilde.adjunction` is the mapping property with global sections.

## Implementation notes

The comparison is produced as a natural isomorphism rather than as separate isomorphisms for
each module, and the subtype bundles it with the equation on global sections that fixes the
canonical choice: the bare natural isomorphism is already
`AlgebraicGeometry.tilde.associatedSheafNatIso`, and what is added here is its characterization.

Both constructions are left adjoints of global sections with scalars restricted along
`R → Γ(Spec R, 𝒪)`, so uniqueness of left adjoints supplies the comparison. The adjunction for
tensor sheafification is `Stacks.AssociatedSheaf.associatedSheafAdjunction`, and the equation on
global sections is read off its unit: that unit is the explicit map `m ↦ 1 ⊗ m` of
`Stacks.PresheafOfModules.ChangeOfRings.unitApp_apply` followed by sheafification, because the
middle constituent of the adjunction is
`Stacks.PresheafOfModules.ChangeOfRings.changeOfRingsAdjunction`, the data form of Tag 03CU.

Quasi-coherence and the mapping property are Mathlib's quasi-coherence instance for `M̃` and
`AlgebraicGeometry.tilde.adjunction`.

## References

* [Stacks Project, Tag 01I7](https://stacks.math.columbia.edu/tag/01I7)
-/

@[expose] public noncomputable section

open AlgebraicGeometry CategoryTheory Opposite TopologicalSpace
open Stacks.AssociatedSheaf

universe u

namespace AlgebraicGeometry

/-- The canonical comparison between the affine construction `M ↦ M̃` on `Spec R` and tensor
sheafification along `R → Γ(Spec R, 𝒪)`: a natural isomorphism of the two functors, together
with the equation that on global sections it sends `m` to `1 ⊗ m`. -/
@[stacks 01I7 "canonical functorial comparison", ega "I 1.8.6" "u = id on Spec R"]
noncomputable def tildeAssociatedSheafNatIso (R : CommRingCat.{u}) :
    { e : tilde.functor R ≅
        associatedSheafFunctor (Spec R).toRingedSpace
          (Scheme.ΓSpecIso R).inv.hom //
      ∀ (M : ModuleCat R) (m : M),
        (e.hom.app M).val.app (op ⊤) (tilde.toOpen M ⊤ m) =
          tensorUnitSection (X := (Spec R).toRingedSpace)
            (Scheme.ΓSpecIso R).inv.hom M (op ⊤) m } := by
  let X := (Spec R).toRingedSpace
  let θ := globalSectionsMap X (Scheme.ΓSpecIso R).inv.hom
  let adjCR : Stacks.PresheafOfModules.ChangeOfRings.changeOfRings θ ⊣
      Stacks.PresheafOfModules.ChangeOfRings.restrictScalars θ :=
    Stacks.PresheafOfModules.ChangeOfRings.changeOfRingsAdjunction θ
  let adjT := tilde.adjunction (R := R)
  let adjA : associatedSheafFunctor (Spec R).toRingedSpace
      (Scheme.ΓSpecIso R).inv.hom ⊣ moduleSpecΓFunctor :=
    associatedSheafAdjunction.{u, u} (Spec R).toRingedSpace (Scheme.ΓSpecIso R).inv.hom
  let e := adjT.leftAdjointUniq adjA
  refine ⟨e, ?_⟩
  intro M m
  have h := adjT.homEquiv_leftAdjointUniq_hom_app adjA M
  rw [adjT.homEquiv_unit] at h
  have h' := congrArg (fun f => f m) h
  let G := constantModulePresheaf X M
  let : Algebra R (X.presheaf.obj (op ⊤)) := (θ.app (op ⊤)).hom.toAlgebra
  have hCR : (adjCR.unit.app G).app (op ⊤) m =
      (1 : X.presheaf.obj (op ⊤)) ⊗ₜ[R] m :=
    Stacks.PresheafOfModules.ChangeOfRings.changeOfRingsAdjunction_unit_app_apply θ G (op ⊤) m
  change ((e.hom.app M).val.app (op ⊤)) (tilde.toOpen M ⊤ m) =
    (adjA.unit.app M) m at h'
  have hunitA : (adjA.unit.app M) m =
      tensorUnitSection (X := (Spec R).toRingedSpace)
        (Scheme.ΓSpecIso R).inv.hom M (op ⊤) m := by
    simp only [adjA]
    change ((PresheafOfModules.sheafificationAdjunction
      (R := structureSheafRing X)
      (𝟙 (structureSheafRing X).obj)).unit.app
        ((Stacks.PresheafOfModules.ChangeOfRings.changeOfRings θ).obj G)).app (op ⊤)
        (((adjCR.unit.app G).app (op ⊤)) m) = _
    rw [hCR]
    rfl
  simpa only [hunitA] using h'

add_to_stacks 01I7 "quasi-coherence"
  AlgebraicGeometry.instIsQuasicoherentOpensCarrierCarrierCommRingCatSpecTilde
add_to_sga "6 0 2.5" "partial"
  AlgebraicGeometry.instIsQuasicoherentOpensCarrierCarrierCommRingCatSpecTilde
add_to_ega "I 1.4.1" "a ⇒ c for V = Spec A"
  AlgebraicGeometry.instIsQuasicoherentOpensCarrierCarrierCommRingCatSpecTilde
add_to_ega "I 4.1.1" "affine case"
  AlgebraicGeometry.instIsQuasicoherentOpensCarrierCarrierCommRingCatSpecTilde
add_to_stacks 01I7 "mapping property" AlgebraicGeometry.tilde.adjunction

end AlgebraicGeometry

end
