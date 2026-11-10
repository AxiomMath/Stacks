module

public import StacksFrontier.AlgebraicGeometry.Modules.IdealPowerMultiple
import StacksCore.Tactic.EgaSgaAttribute

/-!
# Pullback of submodules along a morphism of sheaves of modules

Let `f : M ⟶ N` be a morphism of sheaves of modules on a scheme `X`. This file constructs the
preimage `sheafSubmoduleComap f Q` of a subsheaf `Q ⊆ N`, together with the induced morphism
`sheafSubmoduleMap` between comparable subsheaves, and records the two facts that make such a
morphism usable: it is determined by its composite with the inclusion into the ambient sheaf,
and the inclusion of the top subsheaf is an isomorphism.

## Main definitions

* `AlgebraicGeometry.sheafSubmoduleComap` is the preimage subsheaf `f ⁻¹ Q ⊆ M`.
* `AlgebraicGeometry.sheafSubmoduleMap` is the morphism `P ⟶ Q` induced by `f` when
  `P ≤ f ⁻¹ Q`.
* `AlgebraicGeometry.sheafTopIso` identifies the top subsheaf of `M` with `M`.

## Main results

* `AlgebraicGeometry.sheafSubmoduleMap_comp_ι`: the induced morphism is compatible with the
  inclusions into the ambient sheaves.
* `AlgebraicGeometry.cancel_sheafSubmodule_ι`: a morphism into a subsheaf is determined by its
  composite with the inclusion.
* `AlgebraicGeometry.sheafSubmodule_eq_top_of_affine`: a subsheaf which is everything on every
  affine open is everything.

## Implementation notes

Mathlib's `SheafOfModules.Submodule` carries the lattice structure and the inclusion `ι`, but no
preimage along a morphism; `sheafSubmoduleComap` supplies it. The sheaf condition for the
preimage is checked by refining a covering sieve to the affine opens of `X`, which is where
`sheafSubmodule_eq_top_of_affine` does its work as well: the basis of affine opens is cofinal
in every open, so a section lying in the subsheaf on each affine open lies in it globally.

The complete lattice of submodules of `M` is `AlgebraicGeometry.Scheme.Modules`'s transport of
Mathlib's instance across the `def` `Scheme.Modules`, so `⊤` and `sInf` are available here.
-/

@[expose] public section

universe u

open CategoryTheory Opposite TopologicalSpace

namespace AlgebraicGeometry

/-- The preimage of a subsheaf `Q ⊆ N` along a morphism `f : M ⟶ N` of sheaves of modules: on
every open it is the preimage of `Q`'s sections under the component of `f`. -/
@[sga "6 0 2.11"]
public def sheafSubmoduleComap {X : Scheme.{u}} {M N : X.Modules} (f : M ⟶ N)
    (Q : N.Submodule) : M.Submodule where
  toSubmodule :=
    { obj U := (Q.toSubmodule.obj U).comap (ModuleCat.Hom.hom (f.val.app U))
      map := by
        intro U V k x hx
        change (f.val.app V).hom ((M.val.map k).hom x) ∈ Q.toSubmodule.obj V
        have hx' : (f.val.app U).hom x ∈ Q.toSubmodule.obj U := hx
        have hq := Q.toSubmodule.map k hx'
        change (N.val.map k).hom ((f.val.app U).hom x) ∈ Q.toSubmodule.obj V at hq
        have hh := congrArg (fun g => g x) (PresheafOfModules.Hom.naturality f.val k)
        change (f.val.app V).hom ((M.val.map k).hom x) =
          (N.val.map k).hom ((f.val.app U).hom x) at hh
        rw [hh]
        exact hq }
  isSheaf := by
    intro U s hs
    apply Q.isSheaf
    apply (Opens.grothendieckTopology X).superset_covering ?_ hs
    intro V i hi
    change (f.val.app (op V)).hom ((M.val.map i.op).hom s) ∈ Q.toSubmodule.obj (op V) at hi
    change (N.val.map i.op).hom ((f.val.app U).hom s) ∈ Q.toSubmodule.obj (op V)
    have hh := congrArg (fun g => g s) (PresheafOfModules.Hom.naturality f.val i.op)
    change (f.val.app (op V)).hom ((M.val.map i.op).hom s) =
      (N.val.map i.op).hom ((f.val.app U).hom s) at hh
    rw [← hh]
    exact hi

/-- The morphism `P ⟶ Q` of subsheaves induced by a morphism `f : M ⟶ N` which carries `P`
into `Q`. -/
public def sheafSubmoduleMap {X : Scheme.{u}} {M N : X.Modules} (f : M ⟶ N)
    (P : M.Submodule) (Q : N.Submodule)
    (h : P ≤ sheafSubmoduleComap f Q) : P.toSheafOfModules ⟶ Q.toSheafOfModules := by
  have h' : P.toSubmodule ≤ (sheafSubmoduleComap f Q).toSubmodule :=
    (SheafOfModules.Submodule.le_iff).mp h
  let g : P.toSubmodule.toPresheafOfModules ⟶ Q.toSubmodule.toPresheafOfModules :=
    { app := fun U => ModuleCat.ofHom
        { toFun := fun x => ⟨(f.val.app U).hom x.val, h' U x.property⟩
          map_add' := fun _ _ => Subtype.ext (map_add _ _ _)
          map_smul' := fun _ _ => Subtype.ext (map_smul _ _ _) }
      naturality := by
        intro U V k
        apply ModuleCat.Hom.ext
        ext x
        apply Subtype.ext
        change (f.val.app V).hom ((M.val.map k).hom x.val) =
          (N.val.map k).hom ((f.val.app U).hom x.val)
        exact congrArg (fun g => g x.val) (PresheafOfModules.Hom.naturality f.val k) }
  exact ⟨g⟩

/-- The morphism of subsheaves induced by the zero morphism is zero. -/
public lemma sheafSubmoduleMap_zero {X : Scheme.{u}} {M N : X.Modules}
    (P : M.Submodule) (Q : N.Submodule)
    (h : P ≤ sheafSubmoduleComap (0 : M ⟶ N) Q) :
    sheafSubmoduleMap (0 : M ⟶ N) P Q h = 0 := by
  apply SheafOfModules.hom_ext
  apply PresheafOfModules.Hom.ext
  funext U
  apply ModuleCat.Hom.ext
  ext x
  rfl

/-- The morphism of subsheaves induced by `f` is `f` itself, read inside the ambient sheaves. -/
public lemma sheafSubmoduleMap_comp_ι {X : Scheme.{u}} {M N : X.Modules} (f : M ⟶ N)
    (P : M.Submodule) (Q : N.Submodule) (h : P ≤ sheafSubmoduleComap f Q) :
    sheafSubmoduleMap f P Q h ≫ Q.ι = P.ι ≫ f := by
  apply SheafOfModules.hom_ext
  apply PresheafOfModules.Hom.ext
  funext U
  apply ModuleCat.Hom.ext
  ext x
  rfl

/-- A morphism into a subsheaf is determined by its composite with the inclusion into the
ambient sheaf. -/
public lemma cancel_sheafSubmodule_ι {X : Scheme.{u}} {M : X.Modules}
    (P : M.Submodule) {A : X.Modules} (f g : A ⟶ P.toSheafOfModules)
    (h : f ≫ P.ι = g ≫ P.ι) : f = g := by
  apply SheafOfModules.hom_ext
  apply PresheafOfModules.Hom.ext
  funext U
  apply ModuleCat.Hom.ext
  ext x
  apply Subtype.ext
  exact congrArg (fun k => (k.val.app U).hom x) h

/-- A subsheaf which contains every section over every affine open is the whole sheaf. -/
public lemma sheafSubmodule_eq_top_of_affine {X : Scheme.{u}} {M : X.Modules}
    (P : M.Submodule) (hP : ∀ U : X.affineOpens,
      (⊤ : Submodule Γ(X, U) Γ(M, U)) ≤ P.toSubmodule.obj (op U.1)) : P = ⊤ := by
  apply le_antisymm le_top
  apply SheafOfModules.Submodule.le_iff.mpr
  apply PresheafOfModules.Submodule.le_iff.mpr
  intro U
  have htop : P.toSubmodule.obj U = ⊤ := by
    apply Submodule.eq_top_iff'.2
    intro s
    let R : Presieve U.unop := fun V _ => ∃ A : X.affineOpens,
      V = (A : X.Opens) ∧ (A : X.Opens) ≤ U.unop
    have hcov : Sieve.generate R ∈ Opens.grothendieckTopology X U.unop := by
      intro x hx
      obtain ⟨_, ⟨A, hA, rfl⟩, hxA, hAU⟩ :=
        X.isBasis_affineOpens.exists_subset_of_mem_open hx U.unop.2
      exact ⟨(A : X.Opens), homOfLE hAU,
        ⟨(A : X.Opens), 𝟙 _, homOfLE hAU, ⟨⟨A, hA⟩, rfl, hAU⟩, by simp⟩, hxA⟩
    have hR : R ≤ (P.toSubmodule.toSubfunctor).sieveOfSection s := by
      rintro V i ⟨A, rfl, -⟩
      change M.val.map i.op s ∈ P.toSubmodule.obj (op (A : X.Opens))
      exact (IsConcreteLE.le_iff.mp (hP A)) (x := M.val.map i.op s) Submodule.mem_top
    exact P.isSheaf s ((Opens.grothendieckTopology X).superset_covering
      ((Sieve.generate_le_iff R _).2 hR) hcov)
  simp [htop]

/-- The top subsheaf of `M` is the top submodule of the underlying presheaf of modules. -/
public lemma sheafTop_toSubmodule {X : Scheme.{u}} {M : X.Modules} :
    (⊤ : M.Submodule).toSubmodule = (⊤ : M.val.Submodule) := by
  rw [show (⊤ : M.Submodule) = sInf (∅ : Set M.Submodule) from rfl,
    SheafOfModules.Submodule.toSubmodule_sInf (M := M)]
  apply PresheafOfModules.Submodule.ext
  intro U
  simp

/-- The top subsheaf of `M` has all of `M`'s sections over every open. -/
public lemma sheafTop_obj {X : Scheme.{u}} {M : X.Modules} (U : (Opens X)ᵒᵖ) :
    (⊤ : M.Submodule).toSubmodule.obj U = ⊤ := by
  rw [sheafTop_toSubmodule]
  simp

/-- The inclusion of the top subsheaf of `M` into `M` is an isomorphism. -/
public noncomputable def sheafTopIso {X : Scheme.{u}} (M : X.Modules) :
    (⊤ : M.Submodule).toSheafOfModules ≅ M where
  hom := (⊤ : M.Submodule).ι
  inv := ⟨{
    app := fun U => ModuleCat.ofHom
      { toFun := fun x => ⟨x, by rw [sheafTop_obj]; simp⟩
        map_add' := fun _ _ => rfl
        map_smul' := fun _ _ => rfl }
    naturality := by
      intro U V f
      apply ModuleCat.Hom.ext
      ext x
      rfl }⟩
  hom_inv_id := by
    ext U
    apply Subtype.ext
    rfl
  inv_hom_id := by
    ext U
    rfl

end AlgebraicGeometry
