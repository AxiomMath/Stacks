module

public import Mathlib.CategoryTheory.Abelian.GrothendieckAxioms.SheafOfModules
public import Mathlib.Topology.Sheaves.Sheafify
public import Mathlib.CategoryTheory.Abelian.Basic
public import StacksFrontier.Topology.Sheaves.Cohomology.CechAcyclicity.InjectiveSheavesRestrictOnto

/-!
# Morphisms on an open subset, extended by zero

Let `R` be a sheaf of rings on a topological space `X`, let `W ⊆ X` be open and let
`φ : B|_W ⟶ C|_W` be a morphism of sheaves of `R|_W`-modules. Write `B_W ⊆ B` for the subsheaf
of sections locally zero outside `W`, the realisation of the extension by zero `j_!(B|_W)`
inside `B`. Then `φ` induces a morphism `B_W ⟶ C_W`, which on a section `s` over an open
`V ⊆ W` is `φ(s)`: away from `W` the section is locally zero and is sent to zero, and on `W` it
is sent to `φ(s)`, and these local values glue.

When `C = I` is an injective sheaf of modules this gives the extension property behind the
flasqueness of internal Homs into an injective: every morphism `A|_W ⟶ I|_W` is the restriction
of a morphism `A ⟶ I`.

## Main definitions

* `Stacks.SupportedExtension.supportedMap`: the morphism `B_W ⟶ C_W` induced by `φ`.

## Main results

* `Stacks.SupportedExtension.supportedMap_apply`: its value on a section over an open
  contained in `W`.
* `Stacks.SupportedExtension.exists_extension_of_injective`: a morphism `A|_W ⟶ I|_W` into the
  restriction of an injective sheaf of modules extends to a morphism `A ⟶ I`.

## Implementation notes

The morphism `B_W ⟶ C_W` is produced as a lift through the monomorphism `C_W ⟶ j_*(C|_W)` of
`Stacks.Cohomology.InjectiveRestriction.supportedSubmodule_toDirectImageRestriction_mono`: the
composite `B_W ⟶ j_*(B|_W) ⟶ j_*(C|_W)` vanishes in the cokernel of that monomorphism, because
every section of it is locally in the image, which is checked separately near points of `W` and
near points outside `W`.
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits TopologicalSpace Opposite
open Stacks.Cohomology.InjectiveRestriction

universe u

namespace Stacks.SupportedExtension

variable {X : Type u} [TopologicalSpace X] {R : Sheaf (Opens.grothendieckTopology X) RingCat.{u}}

/-- The monomorphism `M_W ⟶ j_*(M|_W)`. -/
abbrev supportedToDirectImage (M : SheafOfModules.{u} R) (W : Opens X) :
    (supportedSubmodule M W).toSheafOfModules ⟶ directImageRestriction M W :=
  (supportedSubmodule M W).ι ≫ toDirectImageRestriction M W

/-- The morphism `M_W ⟶ j_*(M|_W)` is a monomorphism. -/
instance (M : SheafOfModules.{u} R) (W : Opens X) : Mono (supportedToDirectImage M W) :=
  supportedSubmodule_toDirectImageRestriction_mono M W

/-- The direct image of `φ : B|_W ⟶ C|_W`. -/
abbrev directImageMap {B C : SheafOfModules.{u} R} {W : Opens X} (φ : B.over W ⟶ C.over W) :
    directImageRestriction B W ⟶ directImageRestriction C W :=
  (SheafOfModules.pushforward (SheafOfModules.pushforwardOver W)).map φ

/-- On a section over an open `V ⊆ W`, the unit `M ⟶ j_*(M|_W)` followed by the direct image of
`φ` agrees with `φ` followed by the unit. -/
theorem directImageMap_toDirectImage_apply {B C : SheafOfModules.{u} R} {W : Opens X}
    (φ : B.over W ⟶ C.over W) {V : Opens X} (hV : V ≤ W) (s : B.val.obj (op V)) :
    (directImageMap φ).val.app (op V) ((toDirectImageRestriction B W).val.app (op V) s) =
      (toDirectImageRestriction C W).val.app (op V)
        (φ.val.app (op (Over.mk (homOfLE hV))) s) :=
  PresheafOfModules.naturality_apply φ.val
    (Over.homMk (U := Over.mk (prod.fst : W ⨯ V ⟶ W)) (V := Over.mk (homOfLE hV))
      (prod.snd : W ⨯ V ⟶ V) (Subsingleton.elim _ _)).op s

/-- The unit `M ⟶ j_*(M|_W)` is injective on sections over an open contained in `W`. -/
theorem toDirectImage_injective (M : SheafOfModules.{u} R) {W V : Opens X} (hV : V ≤ W) :
    Function.Injective ((toDirectImageRestriction M W).val.app (op V)) := by
  intro s t h
  change M.val.map (prod.snd : W ⨯ V ⟶ V).op s = M.val.map (prod.snd : W ⨯ V ⟶ V).op t at h
  let l : V ⟶ W ⨯ V := prod.lift (homOfLE hV) (𝟙 V)
  have hl : l ≫ (prod.snd : W ⨯ V ⟶ V) = 𝟙 V := Subsingleton.elim _ _
  have key : ∀ x : M.val.obj (op V), M.val.map l.op (M.val.map (prod.snd : W ⨯ V ⟶ V).op x) = x :=
    fun x => by
      rw [← PresheafOfModules.map_comp_apply, ← op_comp, hl, op_id]
      simp
      rfl
  rw [← key s, ← key t, h]

/-- The composite `B_W ⟶ j_*(B|_W) ⟶ j_*(C|_W)` vanishes in the cokernel of
`C_W ⟶ j_*(C|_W)`. -/
theorem comp_cokernel_π_eq_zero {B C : SheafOfModules.{u} R} {W : Opens X}
    (φ : B.over W ⟶ C.over W) :
    (supportedToDirectImage B W ≫ directImageMap φ) ≫
      cokernel.π (supportedToDirectImage C W) = 0 := by
  let Q := cokernel (supportedToDirectImage C W)
  let π := cokernel.π (supportedToDirectImage C W)
  have hπ : supportedToDirectImage C W ≫ π = 0 := cokernel.condition _
  apply SheafOfModules.hom_ext
  apply PresheafOfModules.hom_ext
  intro V
  apply ModuleCat.hom_ext
  apply LinearMap.ext
  intro s
  let s' : ↥((supportedSubmodule B W).obj V) := s
  show π.val.app V ((directImageMap φ).val.app V
    ((toDirectImageRestriction B W).val.app V s'.val)) = 0
  apply eq_zero_of_locally_zero Q
  intro x hx
  by_cases hxW : x ∈ W
  · refine ⟨V.unop ⊓ W, inf_le_left, ⟨hx, hxW⟩, ?_⟩
    rw [PresheafOfModules.restrictₛₗ_apply, ← PresheafOfModules.naturality_apply,
      ← PresheafOfModules.naturality_apply, ← PresheafOfModules.naturality_apply]
    have e1 := directImageMap_toDirectImage_apply φ (inf_le_right : V.unop ⊓ W ≤ W)
      (B.val.map (homOfLE (inf_le_left : V.unop ⊓ W ≤ V.unop)).op s'.val)
    refine (congrArg (π.val.app (op (V.unop ⊓ W))) e1).trans ?_
    let t : ↥((supportedSubmodule C W).obj (op (V.unop ⊓ W))) :=
      ⟨φ.val.app (op (Over.mk (homOfLE inf_le_right))) (B.val.map (homOfLE inf_le_left).op s'.val),
        (mem_supportedSubmodule_iff C W _).2 fun _ hy hyW => (hyW hy.2).elim⟩
    exact congrArg (fun f => f.val.app (op (V.unop ⊓ W)) t) hπ
  · obtain ⟨W', hW'V, hxW', hs⟩ := (mem_supportedSubmodule_iff B W s'.val).1 s'.property x hx hxW
    refine ⟨W', hW'V, hxW', ?_⟩
    rw [PresheafOfModules.restrictₛₗ_apply] at hs
    rw [PresheafOfModules.restrictₛₗ_apply, ← PresheafOfModules.naturality_apply,
      ← PresheafOfModules.naturality_apply, ← PresheafOfModules.naturality_apply, hs,
      map_zero, map_zero, map_zero]

/-- **The morphism `B_W ⟶ C_W` induced by `φ : B|_W ⟶ C|_W`.** -/
def supportedMap {B C : SheafOfModules.{u} R} {W : Opens X} (φ : B.over W ⟶ C.over W) :
    (supportedSubmodule B W).toSheafOfModules ⟶ (supportedSubmodule C W).toSheafOfModules :=
  Abelian.monoLift (supportedToDirectImage C W) _ (comp_cokernel_π_eq_zero φ)

/-- The morphism `supportedMap φ : B_W ⟶ C_W` followed by `C_W ⟶ j_*(C|_W)` equals
`B_W ⟶ j_*(B|_W)` followed by the direct image of `φ`. -/
theorem supportedMap_comp {B C : SheafOfModules.{u} R} {W : Opens X} (φ : B.over W ⟶ C.over W) :
    supportedMap φ ≫ supportedToDirectImage C W = supportedToDirectImage B W ≫ directImageMap φ :=
  Abelian.monoLift_comp _ _ _

/-- On a section over an open contained in `W`, `supportedMap φ` is `φ`. -/
theorem supportedMap_apply {B C : SheafOfModules.{u} R} {W : Opens X} (φ : B.over W ⟶ C.over W)
    {V : Opens X} (hV : V ≤ W) (s : (supportedSubmodule B W).toSheafOfModules.val.obj (op V)) :
    ((supportedMap φ).val.app (op V) s).val = φ.val.app (op (Over.mk (homOfLE hV))) s.val := by
  apply toDirectImage_injective C hV
  have h := congrArg (fun f => f.val.app (op V) s) (supportedMap_comp φ)
  change (toDirectImageRestriction C W).val.app (op V) ((supportedMap φ).val.app (op V) s).val =
    (directImageMap φ).val.app (op V) ((toDirectImageRestriction B W).val.app (op V) s.val) at h
  rw [h, directImageMap_toDirectImage_apply φ hV]

/-- **Morphisms into the restriction of an injective sheaf of modules extend.** If `I` is an
injective sheaf of `R`-modules and `W` is open, every morphism `A|_W ⟶ I|_W` is the restriction
of a morphism `A ⟶ I`. -/
theorem exists_extension_of_injective (A I : SheafOfModules.{u} R) [Injective I] (W : Opens X)
    (φ : A.over W ⟶ I.over W) :
    ∃ ψ : A ⟶ I, ∀ (V : Opens X) (hV : V ≤ W) (s : A.val.obj (op V)),
      ψ.val.app (op V) s = φ.val.app (op (Over.mk (homOfLE hV))) s := by
  let N := supportedSubmodule A W
  let ψ₀ : N.toSheafOfModules ⟶ I := supportedMap φ ≫ (supportedSubmodule I W).ι
  refine ⟨Injective.factorThru ψ₀ N.ι, fun V hV s => ?_⟩
  let s' : N.toSheafOfModules.val.obj (op V) :=
    ⟨s, (mem_supportedSubmodule_iff A W s).2 fun _ hy hyW => (hyW (hV hy)).elim⟩
  have h := congrArg (fun f => f.val.app (op V) s') (Injective.comp_factorThru ψ₀ N.ι)
  change (Injective.factorThru ψ₀ N.ι).val.app (op V) s = ((supportedMap φ).val.app (op V) s').val
    at h
  rw [h, supportedMap_apply φ hV]

end Stacks.SupportedExtension

end
