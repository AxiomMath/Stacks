module

public import Mathlib.AlgebraicGeometry.Modules.Sheaf
public import Mathlib.Algebra.Category.ModuleCat.Sheaf.PullbackFree
public import Mathlib.CategoryTheory.Functor.Flat
public import Mathlib.Topology.Sheaves.SheafCondition.Sites
public import StacksFrontier.AlgebraicGeometry.Descent.PullbackSectionsSheaf.UnitComparison

/-!
# Endomorphisms of the structure sheaf are global functions, compatibly with pullback

For a scheme `T` an endomorphism `θ` of the structure sheaf `𝒪_T`, viewed as an `𝒪_T`-module, is
multiplication by the global function `θ(1)`. This file records the resulting ring-level
dictionary `End(𝒪_T) → Γ(T, 𝒪_T)` — injective, surjective, additive and multiplicative — and its
compatibility with pullback: for `g : T ⟶ S` the pullback of `θ` along `g`, read on `𝒪_T`
through the canonical isomorphism `g^*𝒪_S ≅ 𝒪_T`, is multiplication by `g^♯(θ(1))`.

## Main definitions

* `AlgebraicGeometry.Scheme.Modules.unitScalar`: the global function `θ(1)`.

## Main results

* `AlgebraicGeometry.Scheme.Modules.unitScalar_comp`, `unitScalar_add`, `unitScalar_sub`,
  `unitScalar_injective`, `unitScalar_surjective`.
* `AlgebraicGeometry.Scheme.Modules.unitScalar_pullback`: compatibility with pullback.
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits Opposite TopologicalSpace

universe u

namespace AlgebraicGeometry.Scheme.Modules

/-- The global function `θ(1)` attached to an endomorphism `θ` of the structure sheaf. -/
def unitScalar {T : Scheme.{u}} (θ : Scheme.unitModule T ⟶ Scheme.unitModule T) : Γ(T, ⊤) :=
  θ.val.app (op ⊤) (1 : Γ(T, ⊤))

variable {T : Scheme.{u}}

/-- On global sections `θ` is multiplication by `unitScalar θ`, by linearity over `Γ(T, ⊤)`. -/
lemma unitScalar_val_app_top (θ : Scheme.unitModule T ⟶ Scheme.unitModule T) (a : Γ(T, ⊤)) :
    θ.val.app (op ⊤) a = a * unitScalar θ := by
  have h : θ.val.app (op ⊤) (a * 1) =
      a * (show Γ(T, ⊤) from θ.val.app (op ⊤) (1 : Γ(T, ⊤))) :=
    (θ.val.app (op ⊤)).hom.map_smul a (1 : Γ(T, ⊤))
  exact (congrArg (fun x : Γ(T, ⊤) ↦ θ.val.app (op ⊤) x) (mul_one a).symm).trans h

/-- Composing endomorphisms multiplies the corresponding global functions. -/
lemma unitScalar_comp (θ θ' : Scheme.unitModule T ⟶ Scheme.unitModule T) :
    unitScalar (θ ≫ θ') = unitScalar θ * unitScalar θ' :=
  unitScalar_val_app_top θ' (unitScalar θ)

/-- The dictionary is additive. -/
lemma unitScalar_add (θ θ' : Scheme.unitModule T ⟶ Scheme.unitModule T) :
    unitScalar (θ + θ') = unitScalar θ + unitScalar θ' := rfl

/-- The dictionary respects differences. -/
lemma unitScalar_sub (θ θ' : Scheme.unitModule T ⟶ Scheme.unitModule T) :
    unitScalar (θ - θ') = unitScalar θ - unitScalar θ' := rfl

/-- The identity endomorphism is multiplication by `1`. -/
lemma unitScalar_id : unitScalar (𝟙 (Scheme.unitModule T)) = 1 := rfl

/-- An endomorphism of the structure sheaf is determined by the global function `θ(1)`: every
section is a restriction of a global one, and `θ` commutes with restriction. -/
lemma unitScalar_injective : Function.Injective (unitScalar (T := T)) := by
  intro θ θ' h
  apply (Scheme.unitModule T).unitHomEquiv.injective
  ext U
  have key := fun φ : (Scheme.unitModule T).sections ↦
    φ.property (homOfLE (le_top : U.unop ≤ ⊤)).op
  rw [← key ((Scheme.unitModule T).unitHomEquiv θ), ← key ((Scheme.unitModule T).unitHomEquiv θ')]
  congr 1

/-- Every global function arises: multiplication by it, restricted over each open, is an
endomorphism of the structure sheaf. -/
lemma unitScalar_surjective : Function.Surjective (unitScalar (T := T)) := by
  intro a
  let s : (Scheme.unitModule T).sections := ⟨fun U ↦ T.presheaf.map (homOfLE le_top).op a, by
    intro U V i
    show T.presheaf.map i (T.presheaf.map _ a) = T.presheaf.map _ a
    rw [← ConcreteCategory.comp_apply, ← Functor.map_comp]
    rfl⟩
  refine ⟨(Scheme.unitModule T).unitHomEquiv.symm s, ?_⟩
  have h := (Scheme.unitModule T).unitHomEquiv_apply_coe
    ((Scheme.unitModule T).unitHomEquiv.symm s) (op ⊤)
  rw [Equiv.apply_symm_apply] at h
  refine h.symm.trans ?_
  show T.presheaf.map _ a = a
  rw [show (homOfLE (le_top : (⊤ : T.Opens) ≤ ⊤)).op = 𝟙 _ from Subsingleton.elim _ _,
    T.presheaf.map_id]
  rfl

/-- **The pullback of an endomorphism of the structure sheaf is multiplication by the pulled
back function.** -/
lemma unitScalar_pullback {S : Scheme.{u}} (g : T ⟶ S)
    (θ : Scheme.unitModule S ⟶ Scheme.unitModule S) :
    unitScalar ((pullbackUnitIso g).inv ≫ (pullback g).map θ ≫ (pullbackUnitIso g).hom) =
      g.appTop (unitScalar θ) := by
  set m := (pullbackUnitIso g).inv ≫ (pullback g).map θ ≫ (pullbackUnitIso g).hom
  have hρ : (pullback g).map θ ≫ (pullbackUnitIso g).hom = (pullbackUnitIso g).hom ≫ m := by
    simp [m]
  have hε : (pullbackPushforwardAdjunction g).homEquiv _ _ (pullbackUnitIso g).hom =
      SheafOfModules.unitToPushforwardObjUnit g.toRingCatSheafHom :=
    pullbackUnitIso_homEquiv g
  have h := congrArg ((pullbackPushforwardAdjunction g).homEquiv _ _) hρ
  rw [Adjunction.homEquiv_naturality_left, Adjunction.homEquiv_naturality_right, hε] at h
  have h' := congrArg (fun φ ↦ φ.val.app (op ⊤) (1 : Γ(S, ⊤))) h
  simp only at h'
  change (SheafOfModules.unitToPushforwardObjUnit g.toRingCatSheafHom).val.app (op ⊤)
      (θ.val.app (op ⊤) (1 : Γ(S, ⊤))) = ((pushforward g).map m).val.app (op ⊤)
        ((SheafOfModules.unitToPushforwardObjUnit g.toRingCatSheafHom).val.app (op ⊤)
          (1 : Γ(S, ⊤))) at h'
  exact (congrArg (fun x : Γ(T, ⊤) ↦ m.val.app (op ⊤) x) (map_one g.appTop.hom).symm).trans
    h'.symm

end AlgebraicGeometry.Scheme.Modules

end
