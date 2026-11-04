module

public import StacksFrontier.AlgebraicGeometry.FormalGeometry.Completion.IdealPowerQuasicoherent
public import StacksFrontier.AlgebraicGeometry.IdealPowerSmul.IdealSmul

/-!
# Lifting a morphism into a submodule, and functoriality of `ℐ ^ n ℱ`

A morphism of modules on a scheme whose values on sections all lie in a submodule of the target
factors through that submodule. Applied to the ideal-power subsheaf `ℐ ^ n ℱ` of
`Stacks.AlgebraicGeometry.IdealPowerSmul.idealPowSmul` this makes `ℱ ↦ ℐ ^ n ℱ` functorial:
a morphism `𝒜 ⟶ ℱ` of quasi-coherent modules carries `ℐ ^ n 𝒜` into `ℐ ^ n ℱ`.

## Main definitions

* `AlgebraicGeometry.liftToSubmodule` — the factorisation through a submodule of the target.
* `AlgebraicGeometry.idealPowSmulMap` — the morphism `ℐ ^ n 𝒜 ⟶ ℐ ^ n ℱ` induced by `𝒜 ⟶ ℱ`.

## Main results

* `AlgebraicGeometry.mem_smul_top_app` — a morphism of modules carries the `I`-multiples among
  the sections over an open to `I`-multiples.
* `AlgebraicGeometry.liftToSubmodule_comp_ι` and `AlgebraicGeometry.idealPowSmulMap_comp_ι` —
  the two factorisations, which is what identifies these morphisms.

## Implementation notes

Membership in `ℐ ^ n ℱ` over an arbitrary open is a local condition; it is read on the affine
opens of a cover, where `Stacks.AlgebraicGeometry.IdealPowerSmul.obj_idealPowSmul` describes it
as `ℐ(V) ^ n Γ(ℱ, V)`, and a morphism of modules is linear on sections, so it preserves that
description. The reduction to affine opens is
`Stacks.Algebraization.mem_submodule_of_affine`.

Linearity is taken in the form `AlgebraicGeometry.Scheme.Modules.Hom.app_smul`, whose scalars
are the functions `Γ(X, V)` of the scheme rather than the sections of the underlying sheaf of
rings; that is the form in which the ideals `ℐ(V)` of an
`AlgebraicGeometry.Scheme.IdealSheafData` are stated.

## References

* [Stacks Project, Tag 01YB](https://stacks.math.columbia.edu/tag/01YB)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits Opposite TopologicalSpace
open Stacks.Algebraization (mem_submodule_of_affine)
open Stacks.AlgebraicGeometry.IdealPowerSmul

universe u

namespace AlgebraicGeometry

attribute [local instance_reducible] AlgebraicGeometry.Scheme.Modules

variable {X : Scheme.{u}}

/-! ### Morphisms of modules preserve ideal multiples of sections -/

/-- A morphism of modules takes the `I`-multiples among the sections over an open to
`I`-multiples, `I` being an ideal of the functions on that open. -/
theorem mem_smul_top_app {F C : X.Modules} (π : F ⟶ C) (V : X.Opens)
    (I : Ideal Γ(X, V)) (x : Γ(F, V))
    (hx : x ∈ I • (⊤ : Submodule Γ(X, V) Γ(F, V))) :
    π.app V x ∈ I • (⊤ : Submodule Γ(X, V) Γ(C, V)) := by
  refine Submodule.smul_induction_on hx (fun a ha z _ => ?_) (fun z w hz hw => ?_)
  · rw [Scheme.Modules.Hom.app_smul]
    exact Submodule.smul_mem_smul ha Submodule.mem_top
  · rw [map_add]
    exact Submodule.add_mem _ hz hw

/-- Naturality of a morphism of modules, read on sections: restricting the image of a section
is the image of its restriction. -/
lemma app_apply_map {A F : X.Modules} (g : A ⟶ F) {U V : X.Opens} (i : V ⟶ U) (s : Γ(A, U)) :
    g.app V (A.val.map i.op s) = F.val.map i.op (g.app U s) :=
  PresheafOfModules.naturality_apply g.val i.op s

/-! ### Lifting a morphism through the inclusion of a submodule -/

/-- **A morphism all of whose values lie in a submodule of the target factors through it.**
The factorisation is the corestriction of the morphism on sections, and its naturality is the
naturality of the original morphism read in the submodule. -/
def liftToSubmodule {A F : X.Modules} (f : A ⟶ F) (N : F.Submodule)
    (h : ∀ (U : X.Opens) (s : Γ(A, U)), f.app U s ∈ N.toSubmodule.obj (op U)) :
    A ⟶ N.toSheafOfModules where
  val :=
    { app U := ModuleCat.ofHom
        ((f.val.app U).hom.codRestrict (N.toSubmodule.obj U) (h U.unop))
      naturality := by
        intro U V g
        ext s
        exact Subtype.ext (PresheafOfModules.naturality_apply f.val g s) }

/-- The factorisation of `AlgebraicGeometry.liftToSubmodule` composed with the inclusion of the
submodule is the original morphism. -/
lemma liftToSubmodule_comp_ι {A F : X.Modules} (f : A ⟶ F) (N : F.Submodule)
    (h : ∀ (U : X.Opens) (s : Γ(A, U)), f.app U s ∈ N.toSubmodule.obj (op U)) :
    liftToSubmodule f N h ≫ N.ι = f := rfl

/-! ### Functoriality of the ideal-power subsheaf -/

/-- **Multiplying by a power of an ideal sheaf is functorial.** A morphism `g : 𝒜 ⟶ ℱ` of
quasi-coherent modules carries `ℐ ^ n 𝒜` into `ℐ ^ n ℱ`. -/
def idealPowSmulMap (J : X.IdealSheafData) (n : ℕ) {A F : X.Modules}
    [A.IsQuasicoherent] [F.IsQuasicoherent] (g : A ⟶ F) :
    (idealPowSmul J n A).toSheafOfModules ⟶ (idealPowSmul J n F).toSheafOfModules :=
  liftToSubmodule ((idealPowSmul J n A).ι ≫ g) (idealPowSmul J n F) (by
    intro U s
    refine mem_submodule_of_affine (idealPowSmul J n F) U _ fun V i => ?_
    have hs : A.val.map i.op s.val ∈ J.ideal V ^ n • (⊤ : Submodule Γ(X, V.1) Γ(A, V.1)) := by
      have h := (idealPowSmul J n A).toSubmodule.map_mem i.op s.property
      rwa [obj_idealPowSmul] at h
    rw [obj_idealPowSmul]
    change F.val.map i.op (g.app U (s.val : Γ(A, U))) ∈ _
    rw [← app_apply_map g i s.val]
    exact mem_smul_top_app g V.1 (J.ideal V ^ n) _ hs)

/-- The morphism induced on ideal powers is compatible with the two inclusions: that is what
identifies it. -/
lemma idealPowSmulMap_comp_ι (J : X.IdealSheafData) (n : ℕ) {A F : X.Modules}
    [A.IsQuasicoherent] [F.IsQuasicoherent] (g : A ⟶ F) :
    idealPowSmulMap J n g ≫ (idealPowSmul J n F).ι = (idealPowSmul J n A).ι ≫ g :=
  liftToSubmodule_comp_ι _ _ _

end AlgebraicGeometry

end
