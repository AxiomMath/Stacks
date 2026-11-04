module

public import Mathlib.Algebra.Category.ModuleCat.Sheaf.Submodule
public import Mathlib.AlgebraicGeometry.Modules.Sheaf
public import StacksCore.Tactic.StacksAttribute

/-!
# Sections annihilated by an ideal sheaf

An ideal sheaf on a scheme `X` is recorded here as a module `I` on `X` together with a
monomorphism `i : I ⟶ 𝒪_X`. For a module `F` on `X`, this file constructs the subsheaf of `F`
whose sections are annihilated by `I`, and computes its membership relation: a section over `U`
lies in it exactly when, over every open `V` with a map to `U`, every section of `I` over `V`
kills the restriction of the section to `V`. That local form is what `i s = 0` means in Stacks
Tag 01PO, and it is what makes the condition stable under restriction and local for the
open-cover topology.

## Main definitions

* `AlgebraicGeometry.locallyAnnihilatedPresheafSubmodule` is the presheaf-level submodule cut
  out by the local annihilation condition.
* `AlgebraicGeometry.locallyAnnihilatedSubmodule` is the same thing as a subsheaf, the condition
  being local.
* `AlgebraicGeometry.annihilatorSubsheaf` is the annihilator subsheaf, defined as the largest
  submodule of `F` all of whose sections over an open are killed by the sections of `I` there.

## Main results

* `AlgebraicGeometry.mem_annihilatorSubsheaf_iff` identifies `annihilatorSubsheaf` with
  `locallyAnnihilatedSubmodule`, i.e. computes its membership relation. This is the first
  assertion of Tag 01PO.

## Implementation notes

The two descriptions of the annihilator differ in where the ideal is evaluated: the supremum is
taken over submodules whose sections over `U` are killed by `I(U)`, while membership in the
annihilator is tested against `I(V)` for every `V` mapping to `U`. They agree because a
submodule is stable under restriction, which is what the two inequalities of
`mem_annihilatorSubsheaf_iff` use.

No rewriting happens underneath a scalar action in this file. The coefficient of `•` is a
section of `X.ringCatSheaf`, which the presheaf of modules sees through a coercion that `rw`'s
keyed matching will not look through, so each needed identity is stated as a `have` at the
spelling the goal uses and composed with `congrArg` or inside a `calc`.

## References

* [Stacks Project, Tag 01PO](https://stacks.math.columbia.edu/tag/01PO)
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits Opposite TopologicalSpace
open AlgebraicGeometry Scheme.Modules

universe u

namespace AlgebraicGeometry

variable {X : Scheme.{u}} (I F : X.Modules) (i : I ⟶ SheafOfModules.unit X.ringCatSheaf)

/-- The presheaf-level submodule of sections of `F` annihilated, after every restriction, by
the sections of the ideal `I` there. -/
noncomputable def locallyAnnihilatedPresheafSubmodule : F.val.Submodule where
  obj U :=
    { carrier := {s | ∀ (V : X.Opens) (f : V ⟶ unop U) (r : Γ(I, V)),
        (show Γ(X, V) from i.app V r) • F.presheaf.map f.op s = 0}
      zero_mem' := by
        intro V f r
        change (show Γ(X, V) from i.app V r) • F.presheaf.map f.op 0 = 0
        rw [map_zero, smul_zero]
      add_mem' := by
        intro s t hs ht V f r
        change (show Γ(X, V) from i.app V r) • F.presheaf.map f.op (s + t) = 0
        rw [show F.presheaf.map f.op (s + t) =
          F.presheaf.map f.op s + F.presheaf.map f.op t from map_add _ _ _,
          smul_add, hs V f r, ht V f r, add_zero]
      smul_mem' := by
        intro a s hs V f r
        refine Eq.trans (congrArg (fun z => (show Γ(X, V) from i.app V r) • z)
          (Scheme.Modules.map_smul (M := F) f (show Γ(X, unop U) from a) s)) ?_
        rw [smul_comm, hs V f r, smul_zero] }
  map := by
    intro U V f s hs W g r
    change (show Γ(X, W) from i.app W r) •
      F.presheaf.map g.op (F.presheaf.map f s) = 0
    have h := hs W (g ≫ f.unop) r
    rwa [show (g ≫ f.unop).op = f ≫ g.op by simp,
      F.presheaf.map_comp_apply f g.op s] at h

/-- The subsheaf of `F` whose sections are locally annihilated by the ideal `I`. -/
noncomputable def locallyAnnihilatedSubmodule : F.Submodule where
  toSubmodule := locallyAnnihilatedPresheafSubmodule I F i
  isSheaf := by
    intro U s hs V f r
    have hsep := (Presheaf.IsSheaf.isSeparated (Scheme.Modules.isSheaf F)) V
      (((locallyAnnihilatedPresheafSubmodule I F i).toSubfunctor.sieveOfSection s).pullback f)
      ((Opens.grothendieckTopology (X : TopCat)).pullback_stable f (by simpa using hs))
    apply hsep
    intro W g hg
    have hloc : F.presheaf.map (g ≫ f).op s ∈
        (locallyAnnihilatedPresheafSubmodule I F i).obj (op W) := hg
    have hz := hloc W (𝟙 W) (I.presheaf.map g.op r)
    have hid : F.presheaf.map (𝟙 W).op (F.presheaf.map (g ≫ f).op s) =
        F.presheaf.map (g ≫ f).op s := by simp
    have hcomp : F.presheaf.map (g ≫ f).op s =
        F.presheaf.map g.op (F.presheaf.map f.op s) := by
      rw [show (g ≫ f).op = f.op ≫ g.op by simp]
      exact F.presheaf.map_comp_apply f.op g.op s
    have hnat : (show Γ(X, W) from i.app W (I.presheaf.map g.op r)) =
        X.presheaf.map g.op (show Γ(X, V) from i.app V r) :=
      PresheafOfModules.naturality_apply i.val g.op r
    have hz' : (show Γ(X, W) from i.app W (I.presheaf.map g.op r)) •
        F.presheaf.map g.op (F.presheaf.map f.op s) = 0 := by
      rw [← hcomp, ← hid]
      exact hz
    calc F.presheaf.map g.op ((show Γ(X, V) from i.app V r) • F.presheaf.map f.op s)
        = X.presheaf.map g.op (show Γ(X, V) from i.app V r) •
            F.presheaf.map g.op (F.presheaf.map f.op s) :=
          Scheme.Modules.map_smul (M := F) g _ _
      _ = (show Γ(X, W) from i.app W (I.presheaf.map g.op r)) •
            F.presheaf.map g.op (F.presheaf.map f.op s) := by rw [hnat]
      _ = 0 := hz'
      _ = F.presheaf.map g.op 0 := (map_zero _).symm

/-- The subsheaf of `F` whose sections are annihilated by the ideal sheaf `I`: the largest
submodule all of whose sections are killed by the sections of `I` over the same open. -/
@[stacks 01PP "the subsheaf of sections annihilated by I"]
noncomputable def annihilatorSubsheaf [Mono i] : F.Submodule :=
  letI : CompleteLattice F.Submodule := SheafOfModules.Submodule.instCompleteLattice
  sSup { N | ∀ (U : X.Opens) (s : Γ(F, U)),
      s ∈ N.toSubmodule.obj (op U) → ∀ r : Γ(I, U),
        (show Γ(X, U) from i.app U r) • s = 0 }

/-- Membership in the annihilator subsheaf means that, on every smaller open,
every section of the ideal annihilates the restricted section. -/
@[stacks 01PO "the subsheaf"]
lemma mem_annihilatorSubsheaf_iff [Mono i] (U : X.Opens) (s : Γ(F, U)) :
    s ∈ (annihilatorSubsheaf I F i).toSubmodule.obj (op U) ↔
      ∀ (V : X.Opens) (f : V ⟶ U) (r : Γ(I, V)),
        (show Γ(X, V) from i.app V r) • F.presheaf.map f.op s = 0 := by
  classical
  let : CompleteLattice F.Submodule := SheafOfModules.Submodule.instCompleteLattice
  have heq : annihilatorSubsheaf I F i = locallyAnnihilatedSubmodule I F i := by
    show sSup {N : F.Submodule | _} = locallyAnnihilatedSubmodule I F i
    refine le_antisymm (sSup_le fun N hN U t ht V f r => ?_) (le_sSup fun U t ht r => ?_)
    · exact hN V (F.presheaf.map f.op t) (N.toSubmodule.map f.op ht) r
    · simpa using ht U (𝟙 U) r
  rw [heq]
  exact Iff.rfl

end AlgebraicGeometry

end
