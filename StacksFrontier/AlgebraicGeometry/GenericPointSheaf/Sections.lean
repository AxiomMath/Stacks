module

public import StacksFrontier.AlgebraicGeometry.GenericPointDecomposition.Defs
public import StacksFrontier.AlgebraicGeometry.GenericPointGluing.GenericPoints

/-!
# Sections of the generic-point contribution

The contribution `genericPointStalkModule X η` of a generic point `η` to the decomposition of
the sheaf of meromorphic functions is a skyscraper: its sections over an open set are the local
ring `𝒪_{X, η}` when `η` lies in that open set, and the zero ring otherwise. This is the
objectwise description of the factors of the product in Stacks Tags 0EMF, 02OW and 0EMH.

## Main results

* `Stacks.AlgebraicGeometry.GenericPointSheaf.subsingleton_genericPointStalkModule_sections`:
  the sections vanish on an open set missing `η`.
* `Stacks.AlgebraicGeometry.GenericPointSheaf.genericPointStalkModuleSectionsIso`: the sections
  over an open set containing `η` are `𝒪_{X, η}`.

## Implementation notes

`AlgebraicGeometry.Scheme.Modules.pushforward_obj_obj` is a `rfl` lemma, so the sections of the
pushforward over `U` are literally the sections of the free rank-one module over
`Spec 𝒪_{X, η}` on the preimage of `U`; the preimage is computed by
`Stacks.AlgebraicGeometry.GenericPointGluing.fromSpecStalk_preimage_eq_top` and
`fromSpecStalk_preimage_eq_bot`, which hold at a generic point with no reducedness hypothesis.
-/

@[expose] public section

open CategoryTheory TopologicalSpace
open AlgebraicGeometry
open scoped AlgebraicGeometry

universe u

namespace Stacks.AlgebraicGeometry.GenericPointSheaf

open Stacks.AlgebraicGeometry.GenericPointDecomposition
open Stacks.AlgebraicGeometry.GenericPointGluing

variable {X : Scheme.{u}}

/-- The sections of the generic-point contribution over an open set are the sections of the
structure sheaf of the local scheme over the preimage of that open set. -/
theorem genericPointStalkModule_sections (η : genericPoints X) (U : X.Opens) :
    (Γ(genericPointStalkModule X η, U) : Type u) =
      (Γ(Spec (X.presheaf.stalk η.1), (X.fromSpecStalk η.1) ⁻¹ᵁ U) : Type u) :=
  rfl

/-- The generic-point contribution has no sections over an open set missing the generic
point. -/
theorem subsingleton_genericPointStalkModule_sections {η : genericPoints X} {U : X.Opens}
    (h : (η : X) ∉ U) : Subsingleton Γ(genericPointStalkModule X η, U) := by
  have he : (X.fromSpecStalk η.1) ⁻¹ᵁ U = ⊥ := fromSpecStalk_preimage_eq_bot η.2 h
  have hsub : Subsingleton
      (Γ(Spec (X.presheaf.stalk η.1), (X.fromSpecStalk η.1) ⁻¹ᵁ U) : Type u) := by
    rw [he]; infer_instance
  exact hsub

/-- Over an open set containing the generic point `η`, the generic-point contribution has the
local ring `𝒪_{X, η}` as its sections. -/
noncomputable def genericPointStalkModuleSectionsIso {η : genericPoints X} {U : X.Opens}
    (hU : (η : X) ∈ U) :
    (Spec (X.presheaf.stalk η.1)).presheaf.obj
        (Opposite.op ((X.fromSpecStalk η.1) ⁻¹ᵁ U)) ≅ X.presheaf.stalk η.1 :=
  eqToIso (congrArg
      (fun V : (Spec (X.presheaf.stalk η.1)).Opens ↦
        (Spec (X.presheaf.stalk η.1)).presheaf.obj (Opposite.op V))
      (fromSpecStalk_preimage_eq_top η.2 hU)) ≪≫
    Scheme.ΓSpecIso (X.presheaf.stalk η.1)

end Stacks.AlgebraicGeometry.GenericPointSheaf
