module

public import StacksFrontier.AlgebraicGeometry.AmpleH1Vanishing.Basic
public import StacksFrontier.AlgebraicGeometry.PullbackSections.Nonvanishing
public import StacksFrontier.AlgebraicGeometry.QuasiAffineNonvanishing.Basic
public import StacksFrontier.AlgebraicGeometry.NonvanishingTrivialization.Basic
public import Mathlib.Topology.Sheaves.SheafCondition.UniqueGluing

/-!
# Sections of an invertible sheaf: extension by zero, and lifting off a closed subscheme

Three statements about global sections that the criterion for ampleness of [Stacks, Tag 0B5P]
needs, and which are independent of its cohomology.

## Main results

* `Stacks.Cohomology.AmpleH1.exists_sections_eval_eq_of_isClopen`: a section over one half of a
  decomposition of `X` into two disjoint opens extends by zero over the other half.
* `Stacks.Cohomology.AmpleH1.exists_sections_nonvanishingLocus_eq_singleton`: **at a point
  whose singleton is clopen, an invertible sheaf has a global section whose nonvanishing locus
  is exactly that point.**
* `Stacks.Cohomology.AmpleH1.surjective_modulePullbackSection`: surjectivity of
  `Γ(X, L) ⟶ Γ(Z, i^*L)` as a map of modules gives surjectivity of the pullback of global
  sections, which is the form [Stacks, Tag 0H78] is stated at.

## The argument

The germ is supplied by
`Stacks.SheafOfModules.exists_notMem_maximalIdeal_smul_top_of_isInvertible`: an invertible sheaf
has, near every point, a local section whose germ escapes `𝔪ₓLₓ`. When `{x}` is open that
neighbourhood can be taken to be `{x}` itself, and when `{x}` is also closed the complement is
open, so the sheaf condition glues the restricted section to zero and the result is a *global*
section. Its germ at `x` is unchanged, and its germ at every other point is zero, so the
nonvanishing locus is exactly `{x}`. No finiteness and no quasi-coherence is used; in particular
the Nakayama argument of [Stacks, Tag 0B8M] is not needed, because
`Stacks.SheafOfModules.stalkPairing` already exhibits `Lₓ` as an invertible `𝒪_{X,x}`-module.

## Implementation notes

No tag attribute is attached: none of these three statements is a Stacks lemma in its own
right. They are steps inside the proof of Tag 0B5P, whose geometric half — choosing a closed
point in the closure of a given point and an affine open around it — is still missing.

The category of `𝒪_X`-modules is spelled
`SheafOfModules ((Stacks.SheafOfModules.Tensor.ringSheaf (X).sheaf))` throughout, for the reason
given in the implementation notes of
`StacksFrontier/AlgebraicGeometry/AmpleH1Vanishing/Basic.lean`.

## References

* [Stacks Project, Tag 0B5P](https://stacks.math.columbia.edu/tag/0B5P)
* [Stacks Project, Tag 0H78](https://stacks.math.columbia.edu/tag/0H78)
* [Stacks Project, Tag 01CY](https://stacks.math.columbia.edu/tag/01CY)
-/

@[expose] public noncomputable section

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits TopologicalSpace Opposite
open Stacks.SheafOfModules.TensorStalkRingedSpace (grpGerm ringStalk grpStalk)

universe u

namespace Stacks.Cohomology.AmpleH1

/-- A section over one half of a decomposition of `X` into two disjoint opens extends by zero
over the other half. -/
public theorem exists_sections_eval_eq_of_isClopen {X : Scheme.{u}}
    (M : _root_.SheafOfModules.{u} ((Stacks.SheafOfModules.Tensor.ringSheaf (X).sheaf)))
    (U V : X.Opens) (hdisj : U ⊓ V = ⊥) (hcover : U ⊔ V = ⊤)
    (a : M.val.obj (op U)) :
    ∃ s : M.sections, s.eval (op U) = a ∧ s.eval (op V) = 0 := by
  classical
  let F : TopCat.Sheaf AddCommGrpCat.{u} X := ⟨M.val.presheaf, M.isSheaf⟩
  let W : Bool → X.Opens := fun b => if b then U else V
  let t : ∀ b, F.obj.obj (op (W b)) := fun b => by
    cases b
    · exact 0
    · exact a
  have hW : (⊤ : X.Opens) ≤ ⨆ b, W b := by
    rw [iSup_bool_eq]
    simpa [W, sup_comm] using le_of_eq hcover.symm
  have hempty : ∀ A : X.Opens, A = ⊥ → Subsingleton (F.obj.obj (op A)) := by
    rintro A rfl
    exact AddCommGrpCat.subsingleton_of_isZero (F.isTerminalOfEmpty).isZero
  have ht : TopCat.Presheaf.IsCompatible F.obj W t := by
    intro b c
    cases b <;> cases c <;> first
      | rfl
      | exact @Subsingleton.elim _ (hempty _ (by simpa [W, inf_comm] using hdisj)) _ _
  obtain ⟨s, hs, -⟩ := F.existsUnique_gluing' W ⊤ (fun _ => homOfLE le_top) hW t ht
  exact ⟨Stacks.SheafOfModules.sectionsOfTop M s, hs true, hs false⟩

/-- **At a point whose singleton is clopen, an invertible sheaf has a global section whose
nonvanishing locus is exactly that point.** -/
public theorem exists_sections_nonvanishingLocus_eq_singleton {X : Scheme.{u}}
    (L : _root_.SheafOfModules.{u} ((Stacks.SheafOfModules.Tensor.ringSheaf (X).sheaf)))
    [Stacks.SheafOfModules.IsInvertible X.presheaf
      (structureSheafRing X.toRingedSpace).property L]
    (x : X) (hopen : IsOpen ({x} : Set X)) (hclosed : IsClosed ({x} : Set X)) :
    ∃ s : L.sections,
      Stacks.SheafOfModules.nonvanishingLocus (X := X.toRingedSpace) L s = {x} := by
  classical
  obtain ⟨W, hxW, b, hb⟩ :=
    Stacks.SheafOfModules.exists_notMem_maximalIdeal_smul_top_of_isInvertible L x
  let U : X.Opens := ⟨{x}, hopen⟩
  let V : X.Opens := ⟨{x}ᶜ, hclosed.isOpen_compl⟩
  have hxU : x ∈ U := Set.mem_singleton x
  have hUW : U ≤ W := fun y hy => Set.mem_singleton_iff.mp hy ▸ hxW
  obtain ⟨s, hsU, hsV⟩ := exists_sections_eval_eq_of_isClopen L U V
    (by ext y; simp [U, V]) (by ext y; simp [U, V])
    (L.val.map (homOfLE hUW).op b)
  have e : grpGerm X.toRingedSpace L.val x ⊤ (Opens.mem_top x) (s.eval (op ⊤))
      = grpGerm X.toRingedSpace L.val x W hxW b :=
    (Stacks.SheafOfModules.grpGerm_eval s x U hxU).symm.trans
      ((congrArg (grpGerm X.toRingedSpace L.val x U hxU) hsU).trans
        (Stacks.SheafOfModules.grpGerm_res (L := L) W U hUW x hxU b))
  have hkey : x ∈ Stacks.SheafOfModules.nonvanishingLocus (X := X.toRingedSpace) L s := by
    simp only [Stacks.SheafOfModules.nonvanishingLocus, Set.mem_ofPred_eq]
    exact e ▸ hb
  have hout : ∀ y ∈ Stacks.SheafOfModules.nonvanishingLocus (X := X.toRingedSpace) L s,
      y = x := by
    intro y hmem
    by_contra hyx
    simp only [Stacks.SheafOfModules.nonvanishingLocus, Set.mem_ofPred_eq] at hmem
    refine hmem ?_
    rw [← Stacks.SheafOfModules.grpGerm_eval s y V (show y ∈ V from hyx), hsV, map_zero]
    exact zero_mem _
  exact ⟨s, Set.eq_singleton_iff_unique_mem.mpr ⟨hkey, hout⟩⟩

/-- **Lifting a section off a closed subscheme.**  When `Γ(X, L) ⟶ Γ(Z, i^*L)` is
surjective as a map of modules, every global section of `i^*L` is the pullback of a global
section of `L`.  Together with `epi_globalSections_map_unit_app` this is what Tag 0B5P uses
to produce the section of `L` whose nonvanishing locus it then controls. -/
public theorem surjective_modulePullbackSection {Z X : Scheme.{u}} (i : Z ⟶ X)
    (P : _root_.SheafOfModules.{u} ((Stacks.SheafOfModules.Tensor.ringSheaf (X).sheaf)))
    (h : Epi ((moduleGlobalSections X).map
      ((RingedSpaceModuleAdjunction.modulePullbackPushforwardAdjunction
        i.toLRSHom.toShHom).unit.app P))) :
    Function.Surjective (Stacks.SheafOfModules.modulePullbackSection i.toLRSHom P) := by
  intro t
  obtain ⟨a, ha⟩ := (ModuleCat.epi_iff_surjective _).mp h (t.eval (op ⊤))
  refine ⟨Stacks.SheafOfModules.sectionsOfTop P a, ?_⟩
  refine Stacks.SheafOfModules.sections_ext_of_eval_top _
    ((Stacks.SheafOfModules.modulePullbackSection_eval_top i.toLRSHom P
      (Stacks.SheafOfModules.sectionsOfTop P a)).trans ?_)
  rwa [Stacks.SheafOfModules.sectionsOfTop_eval_top P a]

end Stacks.Cohomology.AmpleH1

end
