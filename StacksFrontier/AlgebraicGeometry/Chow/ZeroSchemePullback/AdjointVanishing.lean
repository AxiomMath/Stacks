module

public import Mathlib.AlgebraicGeometry.Modules.Sheaf
public import Mathlib.Algebra.Category.ModuleCat.Sheaf.PullbackFree
public import StacksFrontier.Topology.OpensMapFinal

/-!
# Vanishing of a pulled-back adjoint evaluation map

Let `p : Z ⟶ X` be a morphism of schemes, `L` a sheaf of modules on `X`, and
`G : L ⟶ p_* 𝒪_Z` a morphism of `𝒪_X`-modules. Transposing `G` across the adjunction
`p^* ⊣ p_*` gives an *evaluation map* `τ : p^* L ⟶ 𝒪_Z`.

## Main results

* `AlgebraicGeometry.pullback_map_homEquiv_symm_eq_zero_iff` — for a further morphism
  `h : Y ⟶ Z`, the pullback `h^* τ` vanishes if and only if the restriction of `G` along `h`
  does, where the restriction is `G` postcomposed with the canonical comparison
  `p_* 𝒪_Z ⟶ (h ≫ p)_* 𝒪_Y`.

## Implementation notes

The proof is pure adjunction bookkeeping. Write `u` for Mathlib's
`SheafOfModules.pullbackObjUnitToUnit h.toRingCatSheafHom : h^* 𝒪_Z ⟶ 𝒪_Y` and `v` for
`SheafOfModules.unitToPushforwardObjUnit h.toRingCatSheafHom : 𝒪_Z ⟶ h_* 𝒪_Y`. Transposing
`h^* τ ≫ u` across `h^* ⊣ h_*` gives `τ ≫ v`, by naturality in the first variable; transposing
that across `p^* ⊣ p_*` and contracting the iterated pushforward gives the asserted
restriction of `G`, by naturality in the second variable. Both transposes are bijections and
`u` is an isomorphism — the inverse-image functor on opens is final, by
`Stacks.Topology.final_opensMap` — so vanishing travels in both directions.

`Scheme.Modules.pullback` and `Scheme.Modules.pullbackPushforwardAdjunction` are definitional
wrappers around their `SheafOfModules` counterparts, which are the ones `u` and `v` are stated
with. The two spellings are interchangeable only at default transparency, so `rw` builds
ill-typed motives when asked to rewrite under them. The identities are therefore assembled as
`congrArg`/`Eq.trans` *terms*, whose types are elaborated at default transparency — the same
device as in `Chow/ZeroSchemePullback/Factorization.lean` and
`PullbackTensorIso/Sections.lean`.
-/

@[expose] public section

noncomputable section

open CategoryTheory

universe u

namespace AlgebraicGeometry

/-- A morphism whose composition with an isomorphism vanishes is itself zero. Stated with the
isomorphism as an explicit argument, so that no `Mono` instance has to be synthesized. -/
private theorem eq_zero_of_comp_iso {C : Type*} [Category C] [Preadditive C] {M N P : C}
    {f : M ⟶ N} (e : N ≅ P) (hf : f ≫ e.hom = 0) : f = 0 := by
  rw [← Category.comp_id f, ← e.hom_inv_id, ← Category.assoc, hf, Limits.zero_comp]

/-- Let `τ : p^* L ⟶ 𝒪_Z` be the morphism adjoint to `G : L ⟶ p_* 𝒪_Z`. For a morphism
`h : Y ⟶ Z`, the pullback `h^* τ` vanishes exactly when `G` composed with the canonical
comparison `p_* 𝒪_Z ⟶ (h ≫ p)_* 𝒪_Y` vanishes. -/
theorem pullback_map_homEquiv_symm_eq_zero_iff {X Z Y : Scheme.{u}} (p : Z ⟶ X)
    (h : Y ⟶ Z) (L : X.Modules)
    (G : L ⟶ (Scheme.Modules.pushforward p).obj (SheafOfModules.unit Z.ringCatSheaf)) :
    (Scheme.Modules.pullback h).map
        (((Scheme.Modules.pullbackPushforwardAdjunction p).homEquiv L
          (SheafOfModules.unit Z.ringCatSheaf)).symm G) = 0 ↔
      G ≫ (Scheme.Modules.pushforward p).map
          (SheafOfModules.unitToPushforwardObjUnit h.toRingCatSheafHom) ≫
        (Scheme.Modules.pushforwardComp h p).hom.app
          (SheafOfModules.unit Y.ringCatSheaf) = 0 := by
  let A := Scheme.Modules.pullbackPushforwardAdjunction p
  let D := Scheme.Modules.pullbackPushforwardAdjunction h
  let t := (A.homEquiv L (SheafOfModules.unit Z.ringCatSheaf)).symm G
  let : (TopologicalSpace.Opens.map h.base).Final := Stacks.Topology.final_opensMap h.base
  let φ : Z.ringCatSheaf ⟶
      ((TopologicalSpace.Opens.map h.base).sheafPushforwardContinuous RingCat.{u} _ _).obj
        Y.ringCatSheaf := h.toRingCatSheafHom
  let : (SheafOfModules.pushforward φ).IsRightAdjoint := D.isRightAdjoint
  let u : (Scheme.Modules.pullback h).obj (SheafOfModules.unit Z.ringCatSheaf) ⟶
      SheafOfModules.unit Y.ringCatSheaf :=
    SheafOfModules.pullbackObjUnitToUnit φ
  let v : SheafOfModules.unit Z.ringCatSheaf ⟶
      (Scheme.Modules.pushforward h).obj (SheafOfModules.unit Y.ringCatSheaf) :=
    SheafOfModules.unitToPushforwardObjUnit h.toRingCatSheafHom
  show (Scheme.Modules.pullback h).map t = 0 ↔
    G ≫ (Scheme.Modules.pushforward p).map v ≫
      (Scheme.Modules.pushforwardComp h p).hom.app (SheafOfModules.unit Y.ringCatSheaf) = 0
  have hu : IsIso u :=
    SheafOfModules.instIsIsoPullbackObjUnitToUnitOfFinal
      (F := TopologicalSpace.Opens.map h.base) φ
  let e := (Scheme.Modules.pushforwardComp h p).app (SheafOfModules.unit Y.ringCatSheaf)
  have ht : A.homEquiv _ _ t = G := (A.homEquiv _ _).apply_symm_apply _
  have hD : D.homEquiv _ _ ((Scheme.Modules.pullback h).map t ≫ u) = t ≫ v :=
    (D.homEquiv_naturality_left t u).trans
      (congrArg (t ≫ ·) ((D.homEquiv _ _).apply_symm_apply v))
  have hA : A.homEquiv _ _ (t ≫ v) ≫ e.hom =
      G ≫ (Scheme.Modules.pushforward p).map v ≫ e.hom :=
    (congrArg (· ≫ e.hom) (A.homEquiv_naturality_right t v)).trans
      ((congrArg (fun z => (z ≫ (Scheme.Modules.pushforward p).map v) ≫ e.hom) ht).trans
        (Category.assoc G _ e.hom))
  have hA0 : ∀ (M : X.Modules) (N : Z.Modules), A.homEquiv M N 0 = 0 := fun M N => by
    rw [A.homEquiv_unit, Functor.map_zero, Limits.comp_zero]
  have hD0 : ∀ (M : Z.Modules) (N : Y.Modules), D.homEquiv M N 0 = 0 := fun M N => by
    rw [D.homEquiv_unit, Functor.map_zero, Limits.comp_zero]
  refine ⟨fun hz => ?_, fun hz => ?_⟩
  · have h₁ : t ≫ v = 0 :=
      hD.symm.trans ((congrArg (fun z => D.homEquiv _ _ z)
        ((congrArg (· ≫ u) hz).trans Limits.zero_comp)).trans (hD0 _ _))
    exact hA.symm.trans ((congrArg (· ≫ e.hom)
      ((congrArg (fun z => A.homEquiv _ _ z) h₁).trans (hA0 _ _))).trans Limits.zero_comp)
  · have h₁ : t ≫ v = 0 :=
      (A.homEquiv _ _).injective
        ((eq_zero_of_comp_iso e (hA.trans hz)).trans (hA0 _ _).symm)
    exact eq_zero_of_comp_iso (asIso u)
      ((D.homEquiv _ _).injective ((hD.trans h₁).trans (hD0 _ _).symm))

end AlgebraicGeometry

end

end
