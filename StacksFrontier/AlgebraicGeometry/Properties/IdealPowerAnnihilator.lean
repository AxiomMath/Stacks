module

public import Mathlib.Algebra.Category.ModuleCat.Sheaf.Submodule
public import Mathlib.AlgebraicGeometry.Modules.Tilde
public import Mathlib.CategoryTheory.Functor.OfSequence
public import StacksCore.Tactic.StacksAttribute

/-!
# Sections annihilated by a power of an ideal sheaf

For an ideal subsheaf `I` of the structure sheaf and a sheaf of modules `F`, we define the
subsheaf of sections annihilated by the `n`-th power of `I`.

## Main definitions

* `AlgebraicGeometry.idealPower`: the sheaf-theoretic powers of an ideal subsheaf, decreasing
  with the exponent.
* `AlgebraicGeometry.idealPowerSystem`: these powers as an inverse system of sheaves of
  modules, with the canonical inclusion maps.
* `AlgebraicGeometry.idealPowerAnnihilatorSubmodule`: the presheaf-level submodule of sections
  locally annihilated by a power of an ideal sheaf.
* `AlgebraicGeometry.idealPowerAnnihilator`: the subsheaf of sections locally annihilated by a
  power of an ideal sheaf.

## Main results

* `AlgebraicGeometry.idealPowerAnnihilatorSubmodule_isSheaf`: the defining condition is local,
  so the presheaf-level submodule is already a subsheaf.
* `AlgebraicGeometry.mem_idealPowerAnnihilator` exposes the defining membership condition.

## Implementation notes

The condition on a section over `V` quantifies over every restriction to an open subobject of
`V`.  This expresses that the restricted ideal sheaf, rather than merely its module of sections
over `V`, annihilates the section.  In particular, the condition is stable under restriction and
is local for the open-cover topology.

The power `idealPower I n` is the smallest ideal subsheaf containing `I(V)^n` on every
open `V`; thus it is the sheafification of the sectionwise ideal powers, not the generally
non-sheaf presheaf `V ↦ I(V)^n`. Its order-homomorphism interface gives the inclusions
for increasing exponents, and `idealPowerSystem` packages these as functorial sheaf maps.
The annihilator uses these same powers. Its membership lemma exposes the local annihilation
condition to simplification. None of these constructions requires quasi-coherence or finite
type, so those hypotheses are not imposed on the definitions.

The presheaf-level submodule and its sheaf condition are separate declarations rather than
locals inside `idealPowerAnnihilator`, so that the projection
`(idealPowerAnnihilator I F n).toSubmodule` reduces and `mem_idealPowerAnnihilator` holds by
`Iff.rfl`. For the same reason the module-structure obligations are discharged by explicit
`congrArg`/`smul_add` chains instead of rewriting underneath the scalar action: the scalar ring
appears as `X.ringCatSheaf.obj.obj W`, whose head is a definition that `rw`'s keyed matching
will not unfold, so a rewrite under `•` does not fire there.

## References

* [Stacks Project, Tag 01PQ](https://stacks.math.columbia.edu/tag/01PQ)
-/

@[expose] public section

open CategoryTheory Opposite TopologicalSpace

universe u

namespace AlgebraicGeometry

variable {X : Scheme.{u}}

/-- The powers of an ideal subsheaf, as a decreasing family of ideal subsheaves.
The `n`-th power is the smallest subsheaf containing the sectionwise ideal powers. -/
@[implicit_reducible]
noncomputable def idealPower
    (I : (SheafOfModules.unit.{u} X.ringCatSheaf).Submodule) :
    ℕᵒᵈ →o (SheafOfModules.unit.{u} X.ringCatSheaf).Submodule where
  toFun n := sInf { J | ∀ V : (Opens X)ᵒᵖ,
    (show Ideal _ from I.toSubmodule.obj V) ^ (n : ℕ) ≤ J.toSubmodule.obj V }
  monotone' _ _ h := sInf_le_sInf fun _ hJ V ↦ (Ideal.pow_le_pow_right h).trans (hJ V)

/-- The inverse system of ideal powers, with their canonical inclusions. -/
@[implicit_reducible]
noncomputable def idealPowerSystem
    (I : (SheafOfModules.unit.{u} X.ringCatSheaf).Submodule) : ℕᵒᵖ ⥤ X.Modules :=
  Functor.ofOpSequence (X := fun n ↦ (idealPower I n).toSheafOfModules)
    (fun n ↦ ⟨PresheafOfModules.Submodule.homOfLE
      (SheafOfModules.Submodule.le_iff.mp ((idealPower I).monotone (Nat.le_succ n)))⟩)

/-- The submodule of the underlying presheaf of modules whose sections over an open `V` are
those annihilated, after every restriction, by the `n`-th power of the ideal subsheaf `I`. -/
noncomputable def idealPowerAnnihilatorSubmodule
    (I : (SheafOfModules.unit.{u} X.ringCatSheaf).Submodule) (F : X.Modules) (n : ℕ) :
    F.val.Submodule where
  obj := fun V ↦
    { carrier := {s | ∀ (W : (TopologicalSpace.Opens X)ᵒᵖ) (f : V ⟶ W)
          (a : (X.ringCatSheaf).obj.obj W),
            a ∈ (idealPower I n).toSubmodule.obj W →
            a • F.val.presheaf.map f s = 0}
      zero_mem' := fun W f a _ ↦ (congrArg (fun z => a • z)
        (map_zero (ConcreteCategory.hom (F.val.presheaf.map f)))).trans (smul_zero a)
      add_mem' := fun {x y} hx hy W f a ha ↦ ((congrArg (fun z => a • z)
          (map_add (ConcreteCategory.hom (F.val.presheaf.map f)) x y)).trans
        (smul_add a _ _)).trans
        ((congrArg₂ (· + ·) (hx W f a ha) (hy W f a ha)).trans (add_zero 0))
      smul_mem' := by
        intro r s hs W f a ha
        have h := hs W f a ha
        change a • F.val.map f s = 0 at h
        change a • F.val.map f (r • s) = 0
        rw [F.val.map_smul, smul_smul]
        let _ : CommRing ((X.ringCatSheaf).obj.obj W) :=
          inferInstanceAs (CommRing (X.presheaf.obj W))
        rw [mul_comm a, ← smul_smul, h, smul_zero] }
  map := by
    intro V W f s hs Y g a ha
    change a • F.val.map g (F.val.map f s) = 0
    rw [← F.val.map_comp_apply]
    exact hs Y (f ≫ g) a ha

/-- The local annihilation condition is local for the open-cover topology: a section
annihilated by the ideal power after restriction to each member of a covering sieve is
annihilated already. -/
lemma idealPowerAnnihilatorSubmodule_isSheaf
    (I : (SheafOfModules.unit.{u} X.ringCatSheaf).Submodule) (F : X.Modules) (n : ℕ) :
    ∀ ⦃V : (TopologicalSpace.Opens X)ᵒᵖ⦄ (s : F.val.obj V),
      (idealPowerAnnihilatorSubmodule I F n).toSubfunctor.sieveOfSection s ∈
        (Opens.grothendieckTopology X) V.unop →
      s ∈ (idealPowerAnnihilatorSubmodule I F n).obj V := by
  intro V s hs W f a ha
  show a • F.val.map f s = (0 : F.val.obj W)
  let N := idealPowerAnnihilatorSubmodule I F n
  let S := N.toSubfunctor.sieveOfSection s
  have hF : Presieve.IsSheaf (Opens.grothendieckTopology X)
      (F.val.presheaf ⋙ CategoryTheory.forget AddCommGrpCat) :=
    (isSheaf_iff_isSheaf_of_type _ _).mp
      (Presheaf.isSheaf_comp_of_isSheaf _ _ _ (SheafOfModules.isSheaf F))
  refine (hF (S.pullback f.unop)
    ((Opens.grothendieckTopology X).pullback_stable f.unop hs)).isSeparatedFor.ext ?_
  intro Y g hg
  show F.val.restrictₛₗ g.op (a • F.val.map f s) = F.val.restrictₛₗ g.op 0
  rw [map_zero]
  refine (F.val.restrictₛₗ g.op).map_smulₛₗ a _ |>.trans ?_
  let t : F.val.obj (op Y) := F.val.presheaf.map g.op (F.val.presheaf.map f s)
  show (X.ringCatSheaf.obj.map g.op).hom a • t = 0
  have helem : t = ConcreteCategory.hom (F.val.presheaf.map ((g ≫ f.unop).op)) s := by
    rw [show ((g ≫ f.unop).op : V ⟶ op Y) = f ≫ g.op by simp, Functor.map_comp]
    rfl
  have hmem : t ∈ N.obj (op Y) := by
    rw [helem]
    exact hg
  have hz := hmem (op Y) (𝟙 _) _ ((idealPower I n).toSubmodule.map g.op ha)
  change (X.ringCatSheaf.obj.map g.op).hom a • F.val.presheaf.map (𝟙 _) t = 0 at hz
  have hid : ConcreteCategory.hom (F.val.presheaf.map (𝟙 (op Y))) t = t := by
    rw [CategoryTheory.Functor.map_id]
    rfl
  exact (congrArg (fun z => (X.ringCatSheaf.obj.map g.op).hom a • z) hid).symm.trans hz

/-- The subsheaf of `F` whose local sections are annihilated by the `n`-th power of the
ideal subsheaf `I`. -/
@[stacks 01PQ "ideal_power_annihilator_subsheaf"]
noncomputable def idealPowerAnnihilator
    (I : (SheafOfModules.unit.{u} X.ringCatSheaf).Submodule) (F : X.Modules) (n : ℕ) :
    F.Submodule where
  toSubmodule := idealPowerAnnihilatorSubmodule I F n
  isSheaf := idealPowerAnnihilatorSubmodule_isSheaf I F n

/-- A section lies in the ideal-power annihilator exactly when every restriction of it is
annihilated by the sections of the ideal power there. -/
@[simp]
lemma mem_idealPowerAnnihilator
    (I : (SheafOfModules.unit.{u} X.ringCatSheaf).Submodule) (F : X.Modules) (n : ℕ)
    {V : (TopologicalSpace.Opens X)ᵒᵖ} (s : F.val.obj V) :
    s ∈ (idealPowerAnnihilator I F n).toSubmodule.obj V ↔
      ∀ (W : (TopologicalSpace.Opens X)ᵒᵖ) (f : V ⟶ W)
        (a : (X.ringCatSheaf).obj.obj W),
          a ∈ (idealPower I n).toSubmodule.obj W →
            a • F.val.presheaf.map f s = 0 :=
  Iff.rfl

end AlgebraicGeometry
