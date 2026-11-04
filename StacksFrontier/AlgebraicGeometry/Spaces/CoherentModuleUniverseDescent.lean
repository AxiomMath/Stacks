module

public import StacksFrontier.Algebra.Category.ModuleCat.Sheaf.ULiftInjective
public import StacksFrontier.Algebra.Category.ModuleCat.Sheaf.UniverseLift
public import StacksFrontier.AlgebraicGeometry.Spaces.CoherentDevissage
public import StacksFrontier.AlgebraicGeometry.Stacks.Quasicoherent.SectionUniverseLiftDescent
public import StacksFrontier.AlgebraicGeometry.Topologies.CoherentSectionUniverseLift
public import StacksFrontier.AlgebraicGeometry.Topologies.QuasicoherentFromCoherence

/-!
# A coherent module at a large module universe is the lift of one at the universe of the rings

On a site which is essentially small relative to the universe `z` of its structure rings, a
presheaf of modules of finite type (Stacks 03DL(5)) has `z`-small modules of sections, whatever
the universe of its sections: every section is locally a linear combination of finitely many
local generators, and the sections which are such linear combinations on the nose form a
`z`-small subfunctor, which generates the whole sheaf
(`Stacks.SheafOfModules.small_sheafify_obj_of_essentiallySmall`).  So a sheaf of modules of
finite type is the universe lift of the sheaf with the same sections shrunk to universe `z`
(`Stacks.SheafOfModules.moduleULift_essImage_iff`).

On an algebraic space this says that every coherent `𝒪_X`-module, at any module universe, is
isomorphic to the universe lift of a coherent `𝒪_X`-module at the universe `u` of the structure
rings: the small étale site is essentially small at `u` (Stacks 03ED), and quasi-coherence and
coherence descend along the lift.

## Main results

* `Stacks.SheafOfModules.small_val_obj_of_isFiniteType`: a sheaf of modules of finite type on an
  essentially `z`-small site with `z`-valued structure rings has `z`-small sections.
* `AlgebraicGeometry.Space.isCoherent_of_isCoherent_moduleULift`: coherence descends along the
  universe lift of the module sections.
* `AlgebraicGeometry.Space.exists_isCoherent_moduleULift_iso`: **every coherent `𝒪_X`-module is
  the universe lift of a coherent module at the universe of the structure rings.**
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits Opposite
open Stacks.SheafOfModules.Tensor (ringSheaf)

universe u w z m u₁ v₁

namespace Stacks.SheafOfModules

variable {C : Type u₁} [Category.{v₁} C] {J : GrothendieckTopology C} (R : Sheaf J RingCat.{z})
  [EssentiallySmall.{z} C]

/-- **A sheaf of modules of finite type on an essentially `z`-small site with `z`-valued
structure rings has `z`-small modules of sections**, whatever the universe of its sections.

Fix a small model of the site.  Over each of its objects that carries a finite generating family
of `M` choose one; the sections of `M` which are linear combinations of the restrictions of one
of these chosen families form a `z`-small subfunctor.  It generates `M` as a sheaf: a section is
locally over a member of the covering of the finite type condition, every such member is
isomorphic to an object of the small model which then carries a generating family (a restriction
of the given one), and on the members of a covering of that object the section is a linear
combination of the chosen family. -/
theorem small_val_obj_of_isFiniteType (M : _root_.SheafOfModules.{m} R)
    (h : PresheafOfModules.IsFiniteType J M.val) (X : Cᵒᵖ) : Small.{z} (M.val.obj X) := by
  classical
  let e := equivSmallModel.{z} C
  let P : SmallModel.{z} C → Prop := fun W =>
    ∃ (n : ℕ) (s : Fin n → M.val.obj (op (e.inverse.obj W))), PresheafOfModules.Generates J M.val s
  let n : ∀ W : {W // P W}, ℕ := fun W => W.2.choose
  let s : ∀ W : {W // P W}, Fin (n W) → M.val.obj (op (e.inverse.obj W.1)) :=
    fun W => W.2.choose_spec.choose
  have hs : ∀ W : {W // P W}, PresheafOfModules.Generates J M.val (s W) :=
    fun W => W.2.choose_spec.choose_spec
  let ι : Cᵒᵖ → Type _ := fun Y =>
    Σ W : {W // P W}, (Y.unop ⟶ e.inverse.obj W.1) × (Fin (n W) → R.obj.obj Y)
  let φ : ∀ Y : Cᵒᵖ, ι Y → M.val.obj Y := fun Y x =>
    ∑ i, x.2.2 i • M.val.restrictₛₗ x.2.1.op (s x.1 i)
  let G : Subfunctor (M.val.presheaf ⋙ forget _) :=
    { obj := fun Y => Set.range (φ Y)
      map := by
        rintro Y Y' g _ ⟨x, rfl⟩
        refine ⟨⟨x.1, (g.unop ≫ x.2.1, fun i => R.obj.map g (x.2.2 i))⟩, ?_⟩
        change ∑ i, R.obj.map g (x.2.2 i) • M.val.restrictₛₗ (g.unop ≫ x.2.1).op (s x.1 i) =
          M.val.restrictₛₗ g (∑ i, x.2.2 i • M.val.restrictₛₗ x.2.1.op (s x.1 i))
        rw [map_sum]
        refine Finset.sum_congr rfl fun i _ => ?_
        rw [map_smulₛₗ, op_comp, PresheafOfModules.restrictₛₗ_comp_apply]
        rfl }
  have hsmall : ∀ Y : Cᵒᵖ, Small.{z} (G.obj Y) := fun Y => small_range (φ Y)
  have htop : ∀ (Y : Cᵒᵖ) (t : M.val.obj Y), t ∈ (G.sheafify J).obj Y := by
    intro Y t
    obtain ⟨I, U, hU, hg⟩ := h.exists_generators
    refine J.transitive (hU Y.unop) _ fun Z g hg' => ?_
    obtain ⟨i, ⟨p⟩⟩ := hg'
    obtain ⟨k, σ, hσ⟩ := hg i
    let W : SmallModel.{z} C := e.functor.obj Z
    have hW : P W := ⟨k, _, hσ.restrict (e.unitIso.inv.app Z ≫ p)⟩
    obtain ⟨T, hT, hTg⟩ := hs ⟨W, hW⟩ Z (e.unitIso.hom.app Z) (M.val.restrictₛₗ g.op t)
    refine J.superset_covering (fun Z' g' hg'' => ?_) hT
    obtain ⟨a, ha⟩ := hTg Z' g' hg''
    refine ⟨⟨⟨W, hW⟩, (g' ≫ e.unitIso.hom.app Z, a)⟩, ?_⟩
    change ∑ i, a i • M.val.restrictₛₗ (g' ≫ e.unitIso.hom.app Z).op (s ⟨W, hW⟩ i) =
      (M.val.presheaf ⋙ forget _).map (g' ≫ g).op t
    rw [ha]
    change M.val.restrictₛₗ g'.op (M.val.restrictₛₗ g.op t) = M.val.restrictₛₗ (g' ≫ g).op t
    rw [op_comp, PresheafOfModules.restrictₛₗ_comp_apply]
  have := small_sheafify_obj_of_essentiallySmall J G (isSheaf_forgetPresheaf M).isSeparated X
  exact small_of_injective (f := fun t : M.val.obj X => (⟨t, htop X t⟩ : (G.sheafify J).obj X))
    fun _ _ h => congrArg Subtype.val h

end Stacks.SheafOfModules

namespace AlgebraicGeometry.Space

variable (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)
    (F : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u) (hF : IsAlgebraicSpace B S hS F)

/-- **Coherence descends along the universe lift of the module sections**: an `𝒪_X`-module at
the universe of the structure rings whose lift to the module universe `max (u + 1) w` is
coherent is coherent. -/
theorem isCoherent_of_isCoherent_moduleULift (M : Modules.{u, u} B S hS F hF)
    (h : IsCoherent B S hS F hF ((Stacks.SheafOfModules.moduleULift.{max (u + 1) w, u}
      (ringSheaf (smallEtaleRingedSite B S hS F hF).O)).obj M)) :
    IsCoherent B S hS F hF M :=
  { __ := SheafOfModules.IsQuasicoherentOnSite.of_uliftForPresentation'.{u + 1, u, u, u,
      max (u + 1) w} h.toIsQuasicoherentOnSite
    isFiniteType := Stacks.SheafOfModules.isFiniteType_of_sectionwiseEquiv
      (fun _ => RingEquiv.refl _) (fun _ => AddEquiv.ulift) (fun _ _ _ => rfl)
      (fun _ _ => rfl) h.toIsCoherentOnSite.isFiniteType
    kernel_isFiniteType U n s :=
      Stacks.SheafOfModules.CoherentLift.relations_isFiniteType_of_sectionwiseEquiv
        (fun _ => RingEquiv.refl _) (fun _ _ => rfl) (fun _ => AddEquiv.ulift)
        (fun _ _ _ => rfl) (fun _ _ => rfl) s (h.toIsCoherentOnSite.kernel_isFiniteType U n _) }

/-- **Every coherent `𝒪_X`-module is the universe lift of a coherent module at the universe of
the structure rings.**  A coherent module is of finite type, so its sections are `u`-small
(`Stacks.SheafOfModules.small_val_obj_of_isFiniteType`, the small étale site being essentially
small at `u`); shrinking them gives a module whose lift is the given one
(`Stacks.SheafOfModules.moduleULiftShrinkObjIso`), and coherence descends along the lift
(`AlgebraicGeometry.Space.isCoherent_of_isCoherent_moduleULift`). -/
theorem exists_isCoherent_moduleULift_iso (N : Modules.{u, max (u + 1) w} B S hS F hF)
    (hN : IsCoherent B S hS F hF N) :
    ∃ M : Modules.{u, u} B S hS F hF, IsCoherent B S hS F hF M ∧
      Nonempty ((Stacks.SheafOfModules.moduleULift.{max (u + 1) w, u}
        (ringSheaf (smallEtaleRingedSite B S hS F hF).O)).obj M ≅ N) := by
  have hes : EssentiallySmall.{u} (smallEtaleRingedSite B S hS F hF).C := by
    change EssentiallySmall.{u} (SmallEtale B S hS F)
    infer_instance
  have : ∀ U, Small.{u} (N.val.obj U) := fun U =>
    Stacks.SheafOfModules.small_val_obj_of_isFiniteType _ N hN.toIsCoherentOnSite.isFiniteType U
  let e : (Stacks.SheafOfModules.moduleULift.{max (u + 1) w, u}
      (ringSheaf (smallEtaleRingedSite B S hS F hF).O)).obj
        (Stacks.SheafOfModules.shrinkObj (ringSheaf (smallEtaleRingedSite B S hS F hF).O) N) ≅ N :=
    Stacks.SheafOfModules.moduleULiftShrinkObjIso (ringSheaf (smallEtaleRingedSite B S hS F hF).O) N
  exact ⟨_, isCoherent_of_isCoherent_moduleULift B S hS F hF _
    (isCoherent_of_iso B S hS hF e.symm hN), ⟨e⟩⟩

end AlgebraicGeometry.Space

end
