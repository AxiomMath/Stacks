module

public import StacksFrontier.AlgebraicGeometry.Chow.BivariantLemmas.VirtualNormalBundleClassConstruction
public import StacksFrontier.AlgebraicGeometry.Chow.BivariantLemmas.VirtualNormalBaseChangeBundle
public import StacksFrontier.AlgebraicGeometry.Chow.InfinityCentreBaseChangeCharts
public import StacksFrontier.AlgebraicGeometry.Chow.FlatPullback.ProperPushforwardBaseChangeUnconditional
public import StacksFrontier.AlgebraicGeometry.Chow.FlatPullback.IsomorphismBaseChange
public import StacksFrontier.AlgebraicGeometry.Chow.BivariantLemmas.VirtualNormalBundleTotalSpaceBaseChange
public import StacksFrontier.AlgebraicGeometry.Chow.BivariantLemmas.VirtualNormalBundleNormalConeBaseChange

/-!
# The virtual normal Gysin class is compatible with base change

This file proves the base-change clause of [Stacks, Tag 0FBK] in the constant-rank case: for a
closed immersion `i : Z ⟶ X`, a virtual normal bundle `𝒩` of constant rank `r` for `i`, and a
cartesian square `Z' = Z ×_X X'` with `f : X' ⟶ X` locally of finite type, the restriction
(Stacks 0F9Z) of `c(Z ⟶ X, 𝒩)` along `f` is `c(Z' ⟶ X', g^*𝒩)`, with `g^*𝒩` the virtual normal
sheaf of Stacks 0FBJ. The proof follows the source. On a test scheme `t : T ⟶ X'` the class `C`
of Stacks 0F9J for the blowup of `𝐏¹_X` restricts to the one for `𝐏¹_{X'}` (Stacks 0GUH and
0FAQ); flat pullback to the open `C_ZX ×_X T` of `W_∞ ×_X T` commutes with proper pushforward
(Stacks 02RG, the normal cone `C_{Z'}X'` being the inverse image of `C_ZX`); and the closed
immersions `ι` are compatible with base change
(`Stacks.Chow.normalConeBaseChangeMap_comp_normalConeEmbedding`). The cap operations of the two
classes are then characterized by Stacks 02TY.

The file also proves that `Stacks.Chow.virtualNormalBundleClass` is invariant under a σ-compatible
isomorphism of virtual normal bundles (`virtualNormalGysinClass_eq_of_dualIso`), which covers
automorphisms such as `-1`.

## Main results

* `Stacks.Chow.bivariantTransport_bivariantRestriction_virtualNormalGysinClass` — the
  base-change clause of Stacks 0FBK at constant rank, for an arbitrary cartesian square, through
  the canonical identification `Z ×_X X' ≅ Z'`.
* `Stacks.Chow.bivariantRestriction_virtualNormalGysinClass` — the same for the chosen fibre
  product.
* `Stacks.Chow.virtualNormalGysinClass_cap_baseChange` — the clause on cap operations.
* `Stacks.Chow.virtualNormalGysinClass_eq_of_dualIso` — invariance under `𝒩'^∨ ≅ 𝒩^∨`
  compatible with the surjections onto the conormal sheaf.

The clause at arbitrary rank, in the completed group, is
`Stacks.Chow.completedBivariantRestriction_completedVirtualNormalGysinClass` of
`StacksFrontier.AlgebraicGeometry.Chow.BivariantLemmas.CompletedVirtualNormalBundleClassBaseChange`.

## References

* [Stacks Project, Tag 0FBK](https://stacks.math.columbia.edu/tag/0FBK)
* [Stacks Project, Tag 0FBJ](https://stacks.math.columbia.edu/tag/0FBJ)
* [Stacks Project, Tag 0F9Z](https://stacks.math.columbia.edu/tag/0F9Z)
* [Stacks Project, Tag 0GUH](https://stacks.math.columbia.edu/tag/0GUH)
* [Stacks Project, Tag 0FAQ](https://stacks.math.columbia.edu/tag/0FAQ)
* [Stacks Project, Tag 02RG](https://stacks.math.columbia.edu/tag/02RG)
* [Stacks Project, Tag 02TY](https://stacks.math.columbia.edu/tag/02TY)
-/

@[expose] public noncomputable section

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits

universe u

namespace Stacks.Chow

/-! ### Base change of an open immersion to a test scheme -/

section OpenBaseChange

variable {C W X T : Scheme.{u}} (j : C ⟶ W) (proj : W ⟶ X) (φ₀ : C ⟶ X)
  (hφ : φ₀ ≫ 𝟙 X = j ≫ proj) (h : T ⟶ X)

/-- The base change `C ×_X T ⟶ W ×_X T` of a morphism `j : C ⟶ W` over `X`, along a test scheme
`h : T ⟶ X`, is the base change of `j` along `W ×_X T ⟶ W`. -/
theorem isPullback_pullbackMap_fst :
    IsPullback (pullback.fst φ₀ h) (pullback.map φ₀ h proj h j (𝟙 T) (𝟙 X) hφ (by simp)) j
      (pullback.fst proj h) := by
  obtain rfl : φ₀ = j ≫ proj := by simpa using hφ
  refine IsPullback.of_bot (h₃₁ := h) (v₂₁ := pullback.snd proj h) (v₂₂ := proj) ?_
    (pullback.lift_fst _ _ _).symm (IsPullback.of_hasPullback proj h)
  rw [pullback.lift_snd, Category.comp_id]
  exact IsPullback.of_hasPullback _ _

/-- The base change `C ×_X T ⟶ W ×_X T` of an open immersion `j : C ⟶ W` over `X` is an open
immersion. -/
instance isOpenImmersion_pullbackMap [IsOpenImmersion j] :
    IsOpenImmersion (pullback.map φ₀ h proj h j (𝟙 T) (𝟙 X) hφ (by simp)) :=
  MorphismProperty.of_isPullback (isPullback_pullbackMap_fst j proj φ₀ hφ h) inferInstance

end OpenBaseChange

/-! ### The class `ι_* ∘ j^* ∘ C` on a test scheme -/

section NormalForm

variable {S Z X : Scheme.{u}} (sZ : Z ⟶ S) (sX : X ⟶ S) (i : Z ⟶ X) [IsClosedImmersion i]
  (hi : i ≫ sX = sZ)

/-- The composite `C_ZX ⟶ V(𝒩) ⟶ Z ⟶ X` equals `C_ZX ⟶ W_∞ ⟶ X`. -/
theorem normalConeEmbedding_comp_eq (𝒩 : VirtualNormalBundle i) :
    (𝒩.normalConeEmbedding ≫ 𝒩.projection ≫ i) ≫ 𝟙 X =
      normalConeToFibreAtInfinity i sX ≫
        modificationProjectionAtInfinity sX (blowupAtInfinityToProjectiveLineProduct i.ker sX) := by
  rw [Category.comp_id, normalConeToFibreAtInfinity_comp_projection,
    𝒩.normalConeEmbedding_projection_assoc]

/-- **The open immersion `j : C_ZX ⟶ W_∞` on a test scheme** `h : T ⟶ X`: the base change
`C_ZX ×_X T ⟶ W_∞ ×_X T`, with `C_ZX ⟶ X` written as `C_ZX ⟶ N ⟶ Z ⟶ X`. -/
abbrev normalConeTestMap (𝒩 : VirtualNormalBundle i) {T : Scheme.{u}} (h : T ⟶ X) :
    pullback (𝒩.normalConeEmbedding ≫ 𝒩.projection ≫ i) h ⟶
      pullback (modificationProjectionAtInfinity sX
        (blowupAtInfinityToProjectiveLineProduct i.ker sX)) h :=
  pullback.map _ h _ h (normalConeToFibreAtInfinity i sX) (𝟙 T) (𝟙 X)
    (normalConeEmbedding_comp_eq sX i 𝒩) (by simp)

include hi in
/-- The base change `C_ZX ×_X T ⟶ W_∞ ×_X T` commutes with the structure morphisms to `S`. -/
theorem normalConeTestMap_comp_structureMorphism (𝒩 : VirtualNormalBundle i) {T : Scheme.{u}}
    (h : T ⟶ X) :
    normalConeTestMap sX i 𝒩 h ≫
        (pullback.fst (modificationProjectionAtInfinity sX
          (blowupAtInfinityToProjectiveLineProduct i.ker sX)) h ≫
          (modificationProjectionAtInfinity sX
            (blowupAtInfinityToProjectiveLineProduct i.ker sX) ≫ sX)) =
      pullback.fst (𝒩.normalConeEmbedding ≫ 𝒩.projection ≫ i) h ≫
        (Stacks.Conormal.normalConeToBase i ≫ sZ) := by
  rw [pullback.lift_fst_assoc, Category.assoc, ← Category.assoc (normalConeToFibreAtInfinity i sX),
    normalConeToFibreAtInfinity_comp_projection, Category.assoc, hi]

end NormalForm

section NormalFormChow

variable (C : ChowSituation.{u}) {Z X : Scheme.{u}} (sZ : Z ⟶ C.S) [LocallyOfFiniteType sZ]
  (sX : X ⟶ C.S) [LocallyOfFiniteType sX] (i : Z ⟶ X) [IsClosedImmersion i]
  (hi : i ≫ sX = sZ)

/-- Flat pullback along the base change `C_ZX ×_X T ⟶ W_∞ ×_X T` of `j` depends on the way
`C_ZX ⟶ X` is written only through the morphism itself. -/
theorem flatPullbackChow_pullbackMap_heq {Cn W T : Scheme.{u}} (sC : Cn ⟶ C.S)
    [LocallyOfFiniteType sC] (j : Cn ⟶ W) [IsOpenImmersion j] (proj : W ⟶ X)
    (sW : W ⟶ C.S) [LocallyOfFiniteType sW] (h : T ⟶ X) [LocallyOfFiniteType h]
    (φ₀ φ₁ : Cn ⟶ X) (e : φ₀ = φ₁) (hφ₀ : φ₀ ≫ 𝟙 X = j ≫ proj) (hφ₁ : φ₁ ≫ 𝟙 X = j ≫ proj)
    [LocallyOfFiniteType (pullback.fst φ₀ h ≫ sC)] [LocallyOfFiniteType (pullback.fst φ₁ h ≫ sC)]
    [LocallyOfFiniteType (pullback.fst proj h ≫ sW)]
    (hb₀ : pullback.map φ₀ h proj h j (𝟙 T) (𝟙 X) hφ₀ (by simp) ≫ (pullback.fst proj h ≫ sW) =
      pullback.fst φ₀ h ≫ sC)
    (hb₁ : pullback.map φ₁ h proj h j (𝟙 T) (𝟙 X) hφ₁ (by simp) ≫ (pullback.fst proj h ≫ sW) =
      pullback.fst φ₁ h ≫ sC) (k : ℤ) (γ : chowGroup C (pullback.fst proj h ≫ sW) k) :
    flatPullbackChow C (pullback.fst φ₀ h ≫ sC) (pullback.fst proj h ≫ sW)
        (pullback.map φ₀ h proj h j (𝟙 T) (𝟙 X) hφ₀ (by simp)) hb₀ 0
        (relativeDimension_of_isOpenImmersion _) k (flatPullbackDescends C _ _ _ _ _ _ _) γ ≍
      flatPullbackChow C (pullback.fst φ₁ h ≫ sC) (pullback.fst proj h ≫ sW)
        (pullback.map φ₁ h proj h j (𝟙 T) (𝟙 X) hφ₁ (by simp)) hb₁ 0
        (relativeDimension_of_isOpenImmersion _) k (flatPullbackDescends C _ _ _ _ _ _ _) γ := by
  subst e
  rfl

omit [LocallyOfFiniteType sZ] in
/-- The bookkeeping behind `Stacks.Chow.virtualNormalConeClass_cap_heq`: the cap of `j^*` on a
test scheme, pushed along the associativity isomorphism, is flat pullback along the base change of
`j`. -/
theorem virtualNormalConeClass_cap_heq_aux {Wi : Scheme.{u}} (J : Stacks.Conormal.normalCone i ⟶ Wi)
    [IsOpenImmersion J] (P : Wi ⟶ X) [LocallyOfFiniteType P]
    (hJ : J ≫ (P ≫ sX) = Stacks.Conormal.normalConeToBase i ≫ sZ)
    (φ₁ : Stacks.Conormal.normalCone i ⟶ X)
    (hJP : J ≫ P = φ₁) {T : Scheme.{u}} (h : T ⟶ X) [LocallyOfFiniteType h] (k : ℤ)
    [LocallyOfFiniteType (Stacks.Conormal.normalConeToBase i ≫ sZ)]
    [LocallyOfFiniteType (pullback.fst φ₁ h ≫ (Stacks.Conormal.normalConeToBase i ≫ sZ))]
    (γ : chowGroup C (pullback.fst P h ≫ (P ≫ sX)) k)
    (hb : pullback.map φ₁ h P h J (𝟙 T) (𝟙 X) (by rw [Category.comp_id, hJP]) (by simp) ≫
      (pullback.fst P h ≫ (P ≫ sX)) =
        pullback.fst φ₁ h ≫ (Stacks.Conormal.normalConeToBase i ≫ sZ)) :
    chowPushforwardOfIso C
        (pullback.fst J (pullback.fst P h) ≫ (Stacks.Conormal.normalConeToBase i ≫ sZ))
        (pullback.fst (J ≫ P) h ≫ (Stacks.Conormal.normalConeToBase i ≫ sZ))
        (pullbackRightPullbackFstIso P h J).hom
        (pullbackRightPullbackFstIso_hom_comp_fst_comp _ J P h) (k - -((0 : ℕ) : ℤ))
        (flatPullbackBivariantCap C (Stacks.Conormal.normalConeToBase i ≫ sZ) (P ≫ sX) J hJ 0
          (relativeDimension_of_isOpenImmersion J) (flatPullbackDescends C)
          (pullback.fst P h) k γ) ≍
      flatPullbackChow C (pullback.fst φ₁ h ≫ (Stacks.Conormal.normalConeToBase i ≫ sZ))
        (pullback.fst P h ≫ (P ≫ sX))
        (pullback.map φ₁ h P h J (𝟙 T) (𝟙 X) (by rw [Category.comp_id, hJP]) (by simp)) hb 0
        (relativeDimension_of_isOpenImmersion _) k (flatPullbackDescends C _ _ _ _ _ _ _) γ := by
  subst hJP
  have hsnd : pullback.snd J (pullback.fst P h) ≫ (pullback.fst P h ≫ (P ≫ sX)) =
      pullback.fst J (pullback.fst P h) ≫ (Stacks.Conormal.normalConeToBase i ≫ sZ) := by
    rw [← Category.assoc, ← pullback.condition, Category.assoc, hJ]
  have hinv : (pullbackRightPullbackFstIso P h J).inv ≫ (pullback.fst J (pullback.fst P h) ≫
      (Stacks.Conormal.normalConeToBase i ≫ sZ)) =
      pullback.fst (J ≫ P) h ≫ (Stacks.Conormal.normalConeToBase i ≫ sZ) := by
    rw [← Category.assoc]
    exact congrArg (· ≫ _) (pullbackRightPullbackFstIso_inv_fst P h J)
  have he0 : AlgebraicGeometry.RelativeDimension (pullbackRightPullbackFstIso P h J).inv 0 :=
    relativeDimension_of_isOpenImmersion _
  have hmap : (pullbackRightPullbackFstIso P h J).inv ≫ pullback.snd J (pullback.fst P h) =
      pullback.map (J ≫ P) h P h J (𝟙 T) (𝟙 X) (by simp) (by simp) := by
    refine pullback.hom_ext ?_ ?_
    · simp
    · simp
  refine (chowPushforwardOfIso_heq_congr C _ _ _ _ (by ring) _ _
    (flatPullbackBivariantCap_heq C _ _ J hJ 0 _ _ (pullback.fst P h) k γ)).trans ?_
  refine HEq.trans (heq_of_eq (chowPushforwardOfIso_congr_apply C _ _ _ _
    (IsIso.Iso.inv_inv (pullbackRightPullbackFstIso P h J)).symm _
    (by rw [IsIso.Iso.inv_inv]; exact pullbackRightPullbackFstIso_hom_comp_fst_comp _ J P h)
    _ _)) ?_
  refine (flatPullbackChow_heq_chowPushforwardOfIso C _ _ (pullbackRightPullbackFstIso P h J).inv
    hinv he0 _ (flatPullbackDescends C _ _ _ _ _ _ _) _).symm.trans ?_
  refine (flatPullbackChow_comp C _ _ _ (pullbackRightPullbackFstIso P h J).inv
    (pullback.snd J (pullback.fst P h)) hinv hsnd 0 0 he0 _ k
    (flatPullbackDescends C _ _ _ _ _ _ _) (flatPullbackDescends C _ _ _ _ _ _ _)
    (flatPullbackDescends C _ _ _ _ _ _ _) γ).trans ?_
  exact flatPullbackChow_heq_congr C _ _ _ _ _ hb hmap (zero_add 0) _ _ rfl _ _ γ γ HEq.rfl

/-- **`ι_* ∘ j^* ∘ C` on a test scheme.** For `h : T ⟶ X` and `α ∈ A_k(T)`, the cap of the class
`ι_* ∘ j^* ∘ C` of the construction preceding Stacks 0FBK is the pushforward along
`C_ZX ×_X T ⟶ N ×_X T` of the restriction to the open `C_ZX ×_X T ⊆ W_∞ ×_X T` of `C ∩ α`. -/
theorem virtualNormalConeClass_cap_heq (𝒩 : VirtualNormalBundle i) {T : Scheme.{u}}
    (h : T ⟶ X) [LocallyOfFiniteType h] (k : ℤ) (α : chowGroup C (h ≫ sX) k) :
    haveI := locallyOfFiniteType_normalConeToBase C sX i
    (virtualNormalConeClass C sZ sX i hi 𝒩).cap h k α ≍
      properChowPushforward C
        (pullback.fst (𝒩.normalConeEmbedding ≫ 𝒩.projection ≫ i) h ≫
          (Stacks.Conormal.normalConeToBase i ≫ sZ))
        (pullback.fst (𝒩.projection ≫ i) h ≫ (𝒩.projection ≫ sZ))
        (bivariantPushforwardBaseChange 𝒩.normalConeEmbedding (𝒩.projection ≫ i) h)
        (bivariantPushforwardBaseChange_comp_structure
          (by rw [𝒩.normalConeEmbedding_projection_assoc]) (𝒩.projection ≫ i) h)
        ((k - 0) + ((0 : ℕ) : ℤ)) (properPushforwardDescends C _ _ _ _ _)
        (flatPullbackChow C _ _ (normalConeTestMap sX i 𝒩 h)
          (normalConeTestMap_comp_structureMorphism sZ sX i hi 𝒩 h) 0
          (relativeDimension_of_isOpenImmersion _) (k - 0) (flatPullbackDescends C _ _ _ _ _ _ _)
          ((gysinAtInfinityClass C sX (blowupAtInfinityToProjectiveLineProduct i.ker sX)
            (isIso_pullback_snd_blowupAtInfinityToProjectiveLineProduct i.ker sX)).cap h k α)) := by
  have := locallyOfFiniteType_normalConeToBase C sX i
  rw [virtualNormalConeClass, bivariantProperPushforwardOfInvertible_cap,
    bivariantProperPushforwardCap_apply]
  refine properChowPushforward_heq_congr C _ _ _ _ (by ring) _
    (properPushforwardDescends C _ _ _ _ _) _ _ ?_
  refine (BivariantClass.copy_cap C (gysinSystemOfInvertible C) _ sX _ _ _ _ _ h k α).trans ?_
  rw [bivariantCompositeOfInvertible, bivariantComposite_cap]
  refine (chowGroupDegreeEquiv_heq C _ _ _).trans ?_
  rw [bivariantCompositeCap_apply, flatPullbackBivariantClassOfIsOpenImmersionOfInvertible,
    flatPullbackBivariantClassOfIsOpenImmersion_cap, properChowPushforward_eq_chowPushforwardOfIso]
  have hJP : normalConeToFibreAtInfinity i sX ≫
      modificationProjectionAtInfinity sX (blowupAtInfinityToProjectiveLineProduct i.ker sX) =
      𝒩.normalConeEmbedding ≫ 𝒩.projection ≫ i := by
    simpa using (normalConeEmbedding_comp_eq sX i 𝒩).symm
  exact virtualNormalConeClass_cap_heq_aux C sZ sX i (normalConeToFibreAtInfinity i sX)
    (modificationProjectionAtInfinity sX (blowupAtInfinityToProjectiveLineProduct i.ker sX))
    (normalConeToFibreAtInfinity_comp_projection_comp C sZ sX i hi) _ hJP h (k - 0)
    ((gysinAtInfinityClass C sX (blowupAtInfinityToProjectiveLineProduct i.ker sX)
      (isIso_pullback_snd_blowupAtInfinityToProjectiveLineProduct i.ker sX)).cap h k α)
    (normalConeTestMap_comp_structureMorphism sZ sX i hi 𝒩 h)

end NormalFormChow

/-! ### Invariance under an isomorphism of virtual normal bundles -/

section DualIsoGeometry

variable {Z X : Scheme.{u}} {i : Z ⟶ X} [IsClosedImmersion i] (𝒩 𝒩' : VirtualNormalBundle i)
  (ψ : Stacks.AlgebraicGeometry.ReflexiveModules.dualSheaf 𝒩'.bundle ≅
    Stacks.AlgebraicGeometry.ReflexiveModules.dualSheaf 𝒩.bundle)

/-- **The isomorphism `𝐕(𝒩^∨) ≅ 𝐕(𝒩'^∨)` of vector bundles over `Z`** induced by an isomorphism
`ψ : 𝒩'^∨ ≅ 𝒩^∨`. -/
def VirtualNormalBundle.totalSpaceIsoOfDualIso : 𝒩.totalSpace ≅ 𝒩'.totalSpace :=
  @asIso _ _ _ _ (Scheme.Modules.vectorBundleMap Z ψ.hom).left
    (@Scheme.Modules.isIso_vectorBundleMap_left _ _ _ inferInstance inferInstance ψ.hom
      ψ.isIso_hom)

/-- The isomorphism `𝐕(𝒩^∨) ≅ 𝐕(𝒩'^∨)` is one over `Z`. -/
@[reassoc (attr := simp)]
theorem VirtualNormalBundle.totalSpaceIsoOfDualIso_hom_projection :
    (𝒩.totalSpaceIsoOfDualIso 𝒩' ψ).hom ≫ 𝒩'.projection = 𝒩.projection :=
  Scheme.Modules.vectorBundleMap_left_comp Z ψ.hom

/-- The inverse of the isomorphism `𝐕(𝒩^∨) ≅ 𝐕(𝒩'^∨)` is one over `Z`. -/
@[reassoc (attr := simp)]
theorem VirtualNormalBundle.totalSpaceIsoOfDualIso_inv_projection :
    (𝒩.totalSpaceIsoOfDualIso 𝒩' ψ).inv ≫ 𝒩.projection = 𝒩'.projection := by
  rw [Iso.inv_comp_eq, VirtualNormalBundle.totalSpaceIsoOfDualIso_hom_projection]

/-- **The closed immersions `ι` correspond under `𝐕(𝒩^∨) ≅ 𝐕(𝒩'^∨)`** when `ψ` is compatible with
the two surjections onto the conormal sheaf. -/
theorem VirtualNormalBundle.normalConeEmbedding_totalSpaceIsoOfDualIso
    (hψ : ψ.hom ≫ 𝒩.surjection = 𝒩'.surjection) :
    𝒩.normalConeEmbedding ≫ (𝒩.totalSpaceIsoOfDualIso 𝒩' ψ).hom = 𝒩'.normalConeEmbedding := by
  have h : ψ.hom ≫ 𝒩.conormalDegreeOneSurjection = 𝒩'.conormalDegreeOneSurjection :=
    (Category.assoc _ _ _).symm.trans
      (congrArg (· ≫ (Stacks.Conormal.conormalDegreeOneIso i).hom) hψ)
  have key : ∀ {F G H : SheafOfModules.{u} Z.ringCatSheaf} [F.IsQuasicoherent]
      [G.IsQuasicoherent] [H.IsQuasicoherent] (a : F ⟶ G) (b : G ⟶ H) (c : F ⟶ H),
      a ≫ b = c → (Scheme.Modules.vectorBundleMap Z b).left ≫
        (Scheme.Modules.vectorBundleMap Z a).left = (Scheme.Modules.vectorBundleMap Z c).left := by
    intro F G H _ _ _ a b c hc
    subst hc
    rw [Scheme.Modules.vectorBundleMap_comp]
    rfl
  exact (Category.assoc _ _ _).trans (congrArg (Stacks.Conormal.normalConeToNormalBundle i ≫ ·)
    (key ψ.hom 𝒩.conormalDegreeOneSurjection 𝒩'.conormalDegreeOneSurjection h))

/-- The inverse of `𝐕(𝒩^∨) ≅ 𝐕(𝒩'^∨)` on a test scheme `g : T ⟶ X`, as the map
`𝐕(𝒩'^∨) ×_X T ⟶ 𝐕(𝒩^∨) ×_X T`. -/
abbrev bundleTestMapOfDualIso {T : Scheme.{u}} (g : T ⟶ X) :
    pullback (𝒩'.projection ≫ i) g ⟶ pullback (𝒩.projection ≫ i) g :=
  pullback.map _ g _ g (𝒩.totalSpaceIsoOfDualIso 𝒩' ψ).inv (𝟙 T) (𝟙 X)
    (by rw [VirtualNormalBundle.totalSpaceIsoOfDualIso_inv_projection_assoc, Category.comp_id])
    (by simp)

/-- The base change of the bundle projection of `𝒩'` is that of `𝒩` after
`𝐕(𝒩'^∨) ×_X T ⟶ 𝐕(𝒩^∨) ×_X T`. -/
theorem bundleTestBaseChange_eq_bundleTestMapOfDualIso_comp {T : Scheme.{u}} (g : T ⟶ X) :
    bundleTestBaseChange i 𝒩'.projection g =
      bundleTestMapOfDualIso 𝒩 𝒩' ψ g ≫ bundleTestBaseChange i 𝒩.projection g := by
  ext <;> simp

/-- The comparison `C_ZX ×_X T ⟶ C_ZX ×_X T` of the two ways of writing `C_ZX ⟶ X` through the
two vector bundles, on a test scheme `g : T ⟶ X`. -/
abbrev normalConeTestMapOfDualIso {T : Scheme.{u}} (g : T ⟶ X) :
    pullback (𝒩'.normalConeEmbedding ≫ 𝒩'.projection ≫ i) g ⟶
      pullback (𝒩.normalConeEmbedding ≫ 𝒩.projection ≫ i) g :=
  pullback.map _ g _ g (𝟙 _) (𝟙 T) (𝟙 X)
    (by rw [Category.id_comp, Category.comp_id, 𝒩.normalConeEmbedding_projection_assoc,
      𝒩'.normalConeEmbedding_projection_assoc])
    (by simp)

/-- The base change of `j : C_ZX ⟶ W_∞` written through `𝒩'` is the one written through `𝒩`
after the comparison of the two fibre products. -/
theorem normalConeTestMap_eq_normalConeTestMapOfDualIso_comp {S : Scheme.{u}} (sX : X ⟶ S)
    {T : Scheme.{u}} (g : T ⟶ X) :
    normalConeTestMap sX i 𝒩' g =
      normalConeTestMapOfDualIso 𝒩 𝒩' g ≫ normalConeTestMap sX i 𝒩 g := by
  ext <;> simp

/-- The base changes of the two closed immersions `ι` correspond on a test scheme. -/
theorem normalConeTestMapOfDualIso_comp_bivariantPushforwardBaseChange
    (hψ : ψ.hom ≫ 𝒩.surjection = 𝒩'.surjection) {T : Scheme.{u}} (g : T ⟶ X) :
    normalConeTestMapOfDualIso 𝒩 𝒩' g ≫
        bivariantPushforwardBaseChange 𝒩.normalConeEmbedding (𝒩.projection ≫ i) g =
      bivariantPushforwardBaseChange 𝒩'.normalConeEmbedding (𝒩'.projection ≫ i) g ≫
        bundleTestMapOfDualIso 𝒩 𝒩' ψ g := by
  have hι : 𝒩.normalConeEmbedding =
      𝒩'.normalConeEmbedding ≫ (𝒩.totalSpaceIsoOfDualIso 𝒩' ψ).inv := by
    rw [Iso.eq_comp_inv, VirtualNormalBundle.normalConeEmbedding_totalSpaceIsoOfDualIso 𝒩 𝒩' ψ hψ]
  refine pullback.hom_ext ?_ ?_
  · simp only [Category.assoc, bivariantPushforwardBaseChange_fst, pullback.lift_fst,
      pullback.lift_fst_assoc, bivariantPushforwardBaseChange_fst_assoc]
    rw [hι, Category.id_comp]
  · simp

end DualIsoGeometry

/-- **Proper pushforward along the two sides of a commutative square whose other two sides are
isomorphisms.** If `u ≫ w = ν ≫ u'` with `ν` and `w` isomorphisms, then pushing forward along `u`
and then `w` is pushing forward along `ν` and then `u'`. -/
theorem chowPushforwardOfIso_properChowPushforward_eq (C : ChowSituation.{u})
    {A A' B B' : Scheme.{u}} (sA : A ⟶ C.S) [LocallyOfFiniteType sA] (sA' : A' ⟶ C.S)
    [LocallyOfFiniteType sA'] (sB : B ⟶ C.S) [LocallyOfFiniteType sB] (sB' : B' ⟶ C.S)
    [LocallyOfFiniteType sB'] (u : A ⟶ B) [IsProper u] (hu : u ≫ sB = sA) (u' : A' ⟶ B')
    [IsProper u'] (hu' : u' ≫ sB' = sA') (ν : A ⟶ A') [IsIso ν] (hν : ν ≫ sA' = sA) (w : B ⟶ B')
    [IsIso w] (hw : w ≫ sB' = sB) (hcomm : u ≫ w = ν ≫ u') (k : ℤ)
    (hfacu : ProperPushforwardFactorsThroughRationalEquivalence C sA sB u hu k)
    (hfacu' : ProperPushforwardFactorsThroughRationalEquivalence C sA' sB' u' hu' k)
    (y : chowGroup C sA k) :
    chowPushforwardOfIso C sB sB' w hw k (properChowPushforward C sA sB u hu k hfacu y) =
      properChowPushforward C sA' sB' u' hu' k hfacu' (chowPushforwardOfIso C sA sA' ν hν k y) := by
  have huw : (u ≫ w) ≫ sB' = sA := by rw [Category.assoc, hw, hu]
  have h1 := properChowPushforward_comp_apply C sA sB sB' u w (u ≫ w) rfl hu hw huw k hfacu
    (properPushforwardDescends C _ _ _ _ _) (properPushforwardDescends C _ _ _ _ _) y
  have h2 := properChowPushforward_comp_apply C sA sA' sB' ν u' (u ≫ w) hcomm.symm hν hu' huw k
    (properPushforwardDescends C _ _ _ _ _) hfacu' (properPushforwardDescends C _ _ _ _ _) y
  exact h1.symm.trans h2

section DualIsoChow

variable (C : ChowSituation.{u}) {Z X : Scheme.{u}} (sZ : Z ⟶ C.S) [LocallyOfFiniteType sZ]
  (sX : X ⟶ C.S) [LocallyOfFiniteType sX] (i : Z ⟶ X) [IsClosedImmersion i]
  (hi : i ≫ sX = sZ) (𝒩 𝒩' : VirtualNormalBundle i)
  (ψ : Stacks.AlgebraicGeometry.ReflexiveModules.dualSheaf 𝒩'.bundle ≅
    Stacks.AlgebraicGeometry.ReflexiveModules.dualSheaf 𝒩.bundle)
  (hψ : ψ.hom ≫ 𝒩.surjection = 𝒩'.surjection) (r : ℕ)
  [SheafOfModules.IsFiniteLocallyFreeOfRank.{u, u, u} 𝒩.bundle r]
  [SheafOfModules.IsFiniteLocallyFreeOfRank.{u, u, u} 𝒩'.bundle r]

include hψ in
/-- **The class `c(Z ⟶ X, 𝒩)` satisfies the relation of Stacks 0FBK for `𝒩'`** when `𝒩'^∨ ≅ 𝒩^∨`
compatibly with the surjections onto the conormal sheaf. -/
theorem isVirtualNormalGysinClass_of_dualIso :
    IsVirtualNormalBundleClass C sZ sX i hi (gysinSystemOfInvertible C) 𝒩' r
      (virtualNormalBundleClass C sZ sX i hi 𝒩 r) := by
  intro T g _ k α
  rw [bundleFlatPullback_apply]
  refine eq_of_heq ((chowGroupDegreeEquiv_heq C _ _ _).trans ?_)
  have := 𝒩.flat_projection_of_rank r
  have := 𝒩'.flat_projection_of_rank r
  have := locallyOfFiniteType_bundleTestBaseChange i 𝒩.projection g
  have := flat_bundleTestBaseChange i 𝒩.projection (𝒩.flat_projection_of_rank r) g
  have := locallyOfFiniteType_bundleTestBaseChange i 𝒩'.projection g
  have := flat_bundleTestBaseChange i 𝒩'.projection (𝒩'.flat_projection_of_rank r) g
  have := locallyOfFiniteType_normalConeToBase C sX i
  have hΦ : bundleTestMapOfDualIso 𝒩 𝒩' ψ g ≫ (pullback.fst (𝒩.projection ≫ i) g ≫
      (𝒩.projection ≫ sZ)) = pullback.fst (𝒩'.projection ≫ i) g ≫ (𝒩'.projection ≫ sZ) := by
    simp
  have h0 : AlgebraicGeometry.RelativeDimension (bundleTestMapOfDualIso 𝒩 𝒩' ψ g) 0 :=
    relativeDimension_of_isOpenImmersion _
  have hcomp := flatPullbackChow_comp C _ _ _ (bundleTestMapOfDualIso 𝒩 𝒩' ψ g)
    (bundleTestBaseChange i 𝒩.projection g) hΦ
    (bundleTestBaseChange_comp_structureMorphism i 𝒩.projection sZ _ rfl g) 0 r h0
    (relativeDimension_bundleTestBaseChange i 𝒩.projection
      (𝒩.relativeDimension_projection_of_rank r) g)
    (k - r) (flatPullbackDescends C _ _ _ _ _ _ _) (flatPullbackDescends C _ _ _ _ _ _ _)
    (flatPullbackDescends C _ _ _ _ _ _ _)
    ((virtualNormalBundleClass C sZ sX i hi 𝒩 r).cap g k α)
  refine (flatPullbackChow_heq_congr C _ _ _ _ _ _
    (bundleTestBaseChange_eq_bundleTestMapOfDualIso_comp 𝒩 𝒩' ψ g) (zero_add r).symm _ _ rfl _ _
    _ _ HEq.rfl).trans (hcomp.symm.trans ?_)
  refine (flatPullbackChow_heq_chowPushforwardOfIso C _ _ _ hΦ h0 _ _ _).trans ?_
  have hc := bundleFlatPullbackChow_virtualNormalBundleClass_cap C sZ sX i hi 𝒩 r g k α
  have hNF := virtualNormalConeClass_cap_heq C sZ sX i hi 𝒩 g k α
  have hNF' := virtualNormalConeClass_cap_heq C sZ sX i hi 𝒩' g k α
  refine (chowPushforwardOfIso_heq_congr C _ _ _ _ (by ring) _ _ (hc.trans hNF)).trans
    (HEq.trans ?_ hNF'.symm)
  have : IsOpenImmersion (normalConeTestMapOfDualIso 𝒩 𝒩' g) :=
    IsOpenImmersion.of_isIso _
  have hμ : normalConeTestMapOfDualIso 𝒩 𝒩' g ≫
      (pullback.fst (𝒩.normalConeEmbedding ≫ 𝒩.projection ≫ i) g ≫
        (Stacks.Conormal.normalConeToBase i ≫ sZ)) =
      pullback.fst (𝒩'.normalConeEmbedding ≫ 𝒩'.projection ≫ i) g ≫
        (Stacks.Conormal.normalConeToBase i ≫ sZ) := by
    simp
  have hμ0 : AlgebraicGeometry.RelativeDimension (normalConeTestMapOfDualIso 𝒩 𝒩' g) 0 :=
    relativeDimension_of_isOpenImmersion _
  have hcomm : bivariantPushforwardBaseChange 𝒩.normalConeEmbedding (𝒩.projection ≫ i) g ≫
      inv (bundleTestMapOfDualIso 𝒩 𝒩' ψ g) =
      inv (normalConeTestMapOfDualIso 𝒩 𝒩' g) ≫
        bivariantPushforwardBaseChange 𝒩'.normalConeEmbedding (𝒩'.projection ≫ i) g := by
    rw [IsIso.comp_inv_eq, Category.assoc, IsIso.eq_inv_comp,
      normalConeTestMapOfDualIso_comp_bivariantPushforwardBaseChange 𝒩 𝒩' ψ hψ g]
  have hu' := bivariantPushforwardBaseChange_comp_structure (sY := 𝒩'.projection ≫ sZ)
    (f := 𝒩'.normalConeEmbedding) (by rw [𝒩'.normalConeEmbedding_projection_assoc])
    (𝒩'.projection ≫ i) g
  refine (heq_of_eq (chowPushforwardOfIso_properChowPushforward_eq C _ _ _ _ _ _ _ hu'
    (inv (normalConeTestMapOfDualIso 𝒩 𝒩' g)) (by rw [IsIso.inv_comp_eq, hμ]) _ _ hcomm _ _
    (properPushforwardDescends C _ _ _ hu' _) _)).trans ?_
  refine properChowPushforward_heq_congr C _ _ _ _ rfl _ _ _ _ ?_
  refine (flatPullbackChow_heq_chowPushforwardOfIso C _ _ _ hμ hμ0 _
    (flatPullbackDescends C _ _ _ _ _ _ _) _).symm.trans ?_
  refine (flatPullbackChow_comp C _ _ _ (normalConeTestMapOfDualIso 𝒩 𝒩' g)
    (normalConeTestMap sX i 𝒩 g) hμ (normalConeTestMap_comp_structureMorphism sZ sX i hi 𝒩 g)
    0 0 hμ0 (relativeDimension_of_isOpenImmersion _) (k - 0)
    (flatPullbackDescends C _ _ _ _ _ _ _) (flatPullbackDescends C _ _ _ _ _ _ _)
    (flatPullbackDescends C _ _ _ _ _ _ _) _).trans ?_
  exact flatPullbackChow_heq_congr C _ _ _ _ _ _
    (normalConeTestMap_eq_normalConeTestMapOfDualIso_comp 𝒩 𝒩' sX g).symm (zero_add 0) _ _ rfl
    _ _ _ _ HEq.rfl

include hψ in
/-- **Stacks 0FBK: `c(Z ⟶ X, 𝒩)` depends on `𝒩` only up to isomorphism.** If `𝒩'^∨ ≅ 𝒩^∨`
compatibly with the surjections onto the conormal sheaf, then `c(Z ⟶ X, 𝒩) = c(Z ⟶ X, 𝒩')`. This
applies for instance to an automorphism of `𝒩`, such as `-1`, with `𝒩'` carrying the surjection
`σ` composed with its dual. -/
theorem virtualNormalGysinClass_eq_of_dualIso :
    virtualNormalBundleClass C sZ sX i hi 𝒩 r = virtualNormalBundleClass C sZ sX i hi 𝒩' r :=
  (isVirtualNormalBundleClass_iff C sZ sX i hi 𝒩' r _).1
    (isVirtualNormalGysinClass_of_dualIso C sZ sX i hi 𝒩 𝒩' ψ hψ r)

end DualIsoChow

/-! ### The class at infinity under base change, on a test scheme -/

section ClassAtInfinityGeometry

variable {S X X' : Scheme.{u}} (sX : X ⟶ S) (f : X' ⟶ X) (ℐ : X.IdealSheafData)
  (ℐ' : X'.IdealSheafData) (h : ℐ' = ℐ.comap f)

/-- The comparison `W' ×_{X'} T ⟶ W ×_X T` of the base changes of the two blowups at infinity
to a test scheme `t : T ⟶ X'`. -/
abbrev blowupAtInfinityTestComap {T : Scheme.{u}} (t : T ⟶ X') :
    modificationBaseChange (f ≫ sX) (blowupAtInfinityToProjectiveLineProduct ℐ' (f ≫ sX)) t ⟶
      modificationBaseChange sX (blowupAtInfinityToProjectiveLineProduct ℐ sX) (t ≫ f) :=
  pullback.map _ t _ (t ≫ f) (blowupAtInfinityComap f ℐ ℐ' h) (𝟙 T) f (by
      rw [modificationProjection_blowupAtInfinityToProjectiveLineProduct,
        modificationProjection_blowupAtInfinityToProjectiveLineProduct,
        blowupAtInfinityComap_toBase]) (by simp)

/-- The comparison `W'_∞ ×_{X'} T ⟶ W_∞ ×_X T` of the base changes of the two fibres at infinity
to a test scheme `t : T ⟶ X'`. -/
abbrev blowupAtInfinityFibreTestComap {T : Scheme.{u}} (t : T ⟶ X') :
    pullback (modificationProjectionAtInfinity (f ≫ sX)
        (blowupAtInfinityToProjectiveLineProduct ℐ' (f ≫ sX))) t ⟶
      pullback (modificationProjectionAtInfinity sX
        (blowupAtInfinityToProjectiveLineProduct ℐ sX)) (t ≫ f) :=
  pullback.map _ t _ (t ≫ f) (blowupAtInfinityFibreComap f sX ℐ ℐ' h) (𝟙 T) f
    (blowupAtInfinityFibreComap_projection f sX ℐ ℐ' h).symm (by simp)

end ClassAtInfinityGeometry

section ClassAtInfinity

variable (C : ChowSituation.{u}) {X X' : Scheme.{u}} (sX : X ⟶ C.S) [LocallyOfFiniteType sX]
  (f : X' ⟶ X) [LocallyOfFiniteType f] (ℐ : X.IdealSheafData) (ℐ' : X'.IdealSheafData)
  (h : ℐ' = ℐ.comap f)

/-- The comparison `W' ×_{X'} T ⟶ W ×_X T` is proper. -/
instance isProper_blowupAtInfinityTestComap {T : Scheme.{u}} (t : T ⟶ X') :
    IsProper (blowupAtInfinityTestComap sX f ℐ ℐ' h t) := by
  have := LocallyOfFiniteType.isLocallyNoetherian sX
  have : LocallyOfFiniteType (f ≫ sX) := inferInstance
  have := LocallyOfFiniteType.isLocallyNoetherian (f ≫ sX)
  have : IsProper (blowupAtInfinityTestComap sX f ℐ ℐ' h t ≫
      pullback.snd (modificationProjection sX (blowupAtInfinityToProjectiveLineProduct ℐ sX))
        (t ≫ f)) := by
    rw [pullback.lift_snd, Category.comp_id]
    infer_instance
  exact IsProper.of_comp _ (pullback.snd _ _)

/-- The comparison `W'_∞ ×_{X'} T ⟶ W_∞ ×_X T` is proper. -/
instance isProper_blowupAtInfinityFibreTestComap {T : Scheme.{u}} (t : T ⟶ X') :
    IsProper (blowupAtInfinityFibreTestComap sX f ℐ ℐ' h t) := by
  have := LocallyOfFiniteType.isLocallyNoetherian sX
  have : LocallyOfFiniteType (f ≫ sX) := inferInstance
  have := LocallyOfFiniteType.isLocallyNoetherian (f ≫ sX)
  have : IsProper (blowupAtInfinityFibreTestComap sX f ℐ ℐ' h t ≫
      pullback.snd (modificationProjectionAtInfinity sX
        (blowupAtInfinityToProjectiveLineProduct ℐ sX)) (t ≫ f)) := by
    rw [pullback.lift_snd, Category.comp_id]
    infer_instance
  exact IsProper.of_comp _ (pullback.snd _ _)

/-- **Stacks 0FAQ and 0GUH on a test scheme.** For `t : T ⟶ X'` and `α ∈ A_k(T)`, the class
`C ∈ A⁰(W_∞ ⟶ X)` caps `α` (viewed over `X`) to the pushforward along
`W'_∞ ×_{X'} T ⟶ W_∞ ×_X T` of `C' ∩ α`, where `C'` is the class of Stacks 0F9J for the blowup
at infinity `W' ⟶ 𝐏¹_{X'}` of the inverse image of the centre. -/
theorem gysinAtInfinityClass_cap_heq_blowupAtInfinityComap {T : Scheme.{u}} (t : T ⟶ X')
    [LocallyOfFiniteType t] (k : ℤ) (α : chowGroup C (t ≫ (f ≫ sX)) k) :
    (gysinAtInfinityClass C sX (blowupAtInfinityToProjectiveLineProduct ℐ sX)
        (isIso_pullback_snd_blowupAtInfinityToProjectiveLineProduct ℐ sX)).cap (t ≫ f) k
        (chowGroupCongr C (Category.assoc t f sX).symm k α) ≍
      properChowPushforward C
        (modificationInfinityBaseChangeOver (f ≫ sX)
          (blowupAtInfinityToProjectiveLineProduct ℐ' (f ≫ sX)) t)
        (modificationInfinityBaseChangeOver sX (blowupAtInfinityToProjectiveLineProduct ℐ sX)
          (t ≫ f))
        (blowupAtInfinityFibreTestComap sX f ℐ ℐ' h t)
        (by simp [modificationInfinityBaseChangeOver, blowupAtInfinityComap_toBase_assoc])
        (k - 0) (properPushforwardDescends C _ _ _ _ _)
        ((gysinAtInfinityClass C (f ≫ sX) (blowupAtInfinityToProjectiveLineProduct ℐ' (f ≫ sX))
          (isIso_pullback_snd_blowupAtInfinityToProjectiveLineProduct ℐ' (f ≫ sX))).cap t k α) := by
  have hφT : blowupAtInfinityTestComap sX f ℐ ℐ' h t ≫
      pullback.snd (modificationProjection sX (blowupAtInfinityToProjectiveLineProduct ℐ sX))
        (t ≫ f) =
      pullback.snd (modificationProjection (f ≫ sX)
        (blowupAtInfinityToProjectiveLineProduct ℐ' (f ≫ sX))) t := by
    rw [pullback.lift_snd, Category.comp_id]
  have hφ : blowupAtInfinityTestComap sX f ℐ ℐ' h t ≫
      modificationBaseChangeToRelativeLine sX (blowupAtInfinityToProjectiveLineProduct ℐ sX)
        (t ≫ f) =
      modificationBaseChangeToRelativeLine (f ≫ sX)
        (blowupAtInfinityToProjectiveLineProduct ℐ' (f ≫ sX)) t := by
    simp only [modificationBaseChangeToRelativeLine, modificationBaseChangeToLine,
      ← Category.assoc, pullback.lift_fst]
    rw [Category.assoc (pullback.fst _ _), blowupAtInfinityComap_comp_toProjectiveLineProduct,
      Category.assoc, Category.assoc, Category.assoc, familyBaseChange_comp_snd]
  have hφInf : blowupAtInfinityFibreTestComap sX f ℐ ℐ' h t ≫
      modificationInfinityBaseChange sX (blowupAtInfinityToProjectiveLineProduct ℐ sX) (t ≫ f) =
      modificationInfinityBaseChange (f ≫ sX)
        (blowupAtInfinityToProjectiveLineProduct ℐ' (f ≫ sX)) t ≫
        blowupAtInfinityTestComap sX f ℐ ℐ' h t := by
    refine pullback.hom_ext ?_ ?_
    · simp only [Category.assoc, modificationInfinityBaseChange_comp_fst, pullback.lift_fst,
        pullback.lift_fst_assoc]
      rw [blowupAtInfinityFibreComap_inclusion, ← Category.assoc,
        ← modificationInfinityBaseChange_comp_fst, Category.assoc]
    · simp [modificationInfinityBaseChange_comp_snd]
  have key := gysinCapOfLift_comparison C (blowupAtInfinityTestComap sX f ℐ ℐ' h t)
    (blowupAtInfinityFibreTestComap sX f ℐ ℐ' h t) (Category.assoc t f sX).symm
    (isIso_pullback_snd_blowupAtInfinityToProjectiveLineProduct ℐ' (f ≫ sX))
    (isIso_pullback_snd_blowupAtInfinityToProjectiveLineProduct ℐ sX) hφT hφ hφInf k α
  rw [gysinAtInfinityClass_cap, gysinAtInfinityClass_cap, key]
  refine (chowGroupDegreeEquiv_heq C _ _ _).trans ?_
  exact properChowPushforward_heq_congr C _ _ _ _ (sub_zero k).symm _ _ _ _
    (chowGroupDegreeEquiv_heq C _ _ _).symm

end ClassAtInfinity

/-! ### The test-level geometry of the base change -/

section TestGeometry

variable {S Z X Z' X' : Scheme.{u}} (sX : X ⟶ S) (i : Z ⟶ X) [IsClosedImmersion i]
  (i' : Z' ⟶ X') [IsClosedImmersion i'] (g : Z' ⟶ Z) (f : X' ⟶ X) (sq : IsPullback i' g f i)
  (𝒩 : VirtualNormalBundle i)

/-- The equation making the comparison of the normal cones a morphism over `X' ⟶ X`. -/
theorem normalConeEmbedding_baseChange_comp_eq :
    ((𝒩.baseChange i i' g f sq).normalConeEmbedding ≫
        (𝒩.baseChange i i' g f sq).projection ≫ i') ≫ f =
      normalConeBaseChangeMap f sX i i' (ker_eq_comap_of_isPullback f sq) ≫
        𝒩.normalConeEmbedding ≫ 𝒩.projection ≫ i := by
  rw [VirtualNormalBundle.normalConeEmbedding_projection_assoc,
    VirtualNormalBundle.normalConeEmbedding_projection_assoc, Category.assoc, sq.w,
    normalConeBaseChangeMap_toBase_assoc f sX i i' _ g sq.w]

/-- **The comparison `C_{Z'}X' ×_{X'} T ⟶ C_ZX ×_X T` of the normal cones on a test scheme**
`t : T ⟶ X'`. -/
abbrev normalConeTestBaseChange {T : Scheme.{u}} (t : T ⟶ X') :
    pullback ((𝒩.baseChange i i' g f sq).normalConeEmbedding ≫
        (𝒩.baseChange i i' g f sq).projection ≫ i') t ⟶
      pullback (𝒩.normalConeEmbedding ≫ 𝒩.projection ≫ i) (t ≫ f) :=
  pullback.map _ t _ (t ≫ f) (normalConeBaseChangeMap f sX i i' (ker_eq_comap_of_isPullback f sq))
    (𝟙 T) f (normalConeEmbedding_baseChange_comp_eq sX i i' g f sq 𝒩) (by simp)

/-- **`C_{Z'}X' ×_{X'} T` is the inverse image of `C_ZX ×_X T` in `W'_∞ ×_{X'} T`.** -/
theorem isPullback_normalConeTestBaseChange {T : Scheme.{u}} (t : T ⟶ X') :
    IsPullback (normalConeTestMap (f ≫ sX) i' (𝒩.baseChange i i' g f sq) t)
      (normalConeTestBaseChange sX i i' g f sq 𝒩 t)
      (blowupAtInfinityFibreTestComap sX f i.ker i'.ker (ker_eq_comap_of_isPullback f sq) t)
      (normalConeTestMap sX i 𝒩 (t ≫ f)) := by
  have hbot := (isPullback_pullbackMap_fst _ _ _ (normalConeEmbedding_comp_eq sX i 𝒩)
    (t ≫ f)).flip
  refine IsPullback.of_bot ?_ ?_ hbot
  · have hκ : normalConeTestBaseChange sX i i' g f sq 𝒩 t ≫
        pullback.fst (𝒩.normalConeEmbedding ≫ 𝒩.projection ≫ i) (t ≫ f) =
        pullback.fst _ t ≫ normalConeBaseChangeMap f sX i i' (ker_eq_comap_of_isPullback f sq) :=
      pullback.lift_fst _ _ _
    have hφ : blowupAtInfinityFibreTestComap sX f i.ker i'.ker
          (ker_eq_comap_of_isPullback f sq) t ≫
        pullback.fst (modificationProjectionAtInfinity sX
          (blowupAtInfinityToProjectiveLineProduct i.ker sX)) (t ≫ f) =
        pullback.fst _ t ≫ blowupAtInfinityFibreComap f sX i.ker i'.ker
          (ker_eq_comap_of_isPullback f sq) := pullback.lift_fst _ _ _
    rw [hκ, hφ]
    exact (isPullback_pullbackMap_fst _ _ _
      (normalConeEmbedding_comp_eq (f ≫ sX) i' (𝒩.baseChange i i' g f sq)) t).flip.paste_vert
      (isPullback_normalConeBaseChangeMap f sX i i' _).flip
  · refine pullback.hom_ext ?_ ?_
    · simp only [Category.assoc, pullback.lift_fst, pullback.lift_fst_assoc]
      rw [normalConeBaseChangeMap_comp]
    · simp

/-- `V(g^*𝒩) = V(𝒩) ×_X X'`, the cartesian square of Stacks 0FBJ pasted with that of
`Z' = Z ×_X X'`. -/
theorem isPullback_baseChangeTotalSpaceMap_comp :
    IsPullback (𝒩.baseChangeTotalSpaceMap i i' g f sq)
      ((𝒩.baseChange i i' g f sq).projection ≫ i') (𝒩.projection ≫ i) f :=
  (𝒩.isPullback_baseChangeTotalSpaceMap i i' g f sq).paste_vert sq.flip

/-- `V(g^*𝒩) ×_{X'} T = V(𝒩) ×_X T` for a test scheme `t : T ⟶ X'`. -/
theorem isPullback_bundleTestBaseChange_comp {T : Scheme.{u}} (t : T ⟶ X') :
    IsPullback (pullback.fst ((𝒩.baseChange i i' g f sq).projection ≫ i') t ≫
        𝒩.baseChangeTotalSpaceMap i i' g f sq)
      (pullback.snd _ t) (𝒩.projection ≫ i) (t ≫ f) :=
  (IsPullback.of_hasPullback _ t).paste_horiz
    (isPullback_baseChangeTotalSpaceMap_comp i i' g f sq 𝒩)

/-- **The identification `V(𝒩) ×_X T ≅ V(g^*𝒩) ×_{X'} T`** on a test scheme `t : T ⟶ X'`. -/
def bundleTestBaseChangeIso {T : Scheme.{u}} (t : T ⟶ X') :
    pullback (𝒩.projection ≫ i) (t ≫ f) ≅
      pullback ((𝒩.baseChange i i' g f sq).projection ≫ i') t :=
  (isPullback_bundleTestBaseChange_comp i i' g f sq 𝒩 t).isoPullback.symm

/-- The identification `V(𝒩) ×_X T ≅ V(g^*𝒩) ×_{X'} T` followed by the projection to `V(g^*𝒩)`
and the map `V(g^*𝒩) ⟶ V(𝒩)` is the first projection of `V(𝒩) ×_X T`. -/
@[reassoc (attr := simp)]
theorem bundleTestBaseChangeIso_hom_fst {T : Scheme.{u}} (t : T ⟶ X') :
    (bundleTestBaseChangeIso i i' g f sq 𝒩 t).hom ≫ pullback.fst _ t ≫
        𝒩.baseChangeTotalSpaceMap i i' g f sq =
      pullback.fst (𝒩.projection ≫ i) (t ≫ f) :=
  (isPullback_bundleTestBaseChange_comp i i' g f sq 𝒩 t).isoPullback_inv_fst

/-- The identification `V(𝒩) ×_X T ≅ V(g^*𝒩) ×_{X'} T` commutes with the projections to `T`. -/
@[reassoc (attr := simp)]
theorem bundleTestBaseChangeIso_hom_snd {T : Scheme.{u}} (t : T ⟶ X') :
    (bundleTestBaseChangeIso i i' g f sq 𝒩 t).hom ≫ pullback.snd _ t =
      pullback.snd (𝒩.projection ≫ i) (t ≫ f) :=
  (isPullback_bundleTestBaseChange_comp i i' g f sq 𝒩 t).isoPullback_inv_snd

/-- Two morphisms into `V(g^*𝒩)` agree as soon as they agree after `V(g^*𝒩) ⟶ V(𝒩)` and after
`V(g^*𝒩) ⟶ X'`. -/
theorem baseChangeTotalSpace_hom_ext {W : Scheme.{u}}
    {a b : W ⟶ (𝒩.baseChange i i' g f sq).totalSpace}
    (h₁ : a ≫ 𝒩.baseChangeTotalSpaceMap i i' g f sq = b ≫ 𝒩.baseChangeTotalSpaceMap i i' g f sq)
    (h₂ : a ≫ (𝒩.baseChange i i' g f sq).projection ≫ i' =
      b ≫ (𝒩.baseChange i i' g f sq).projection ≫ i') : a = b :=
  (isPullback_baseChangeTotalSpaceMap_comp i i' g f sq 𝒩).hom_ext h₁ h₂

include sq in
omit [IsClosedImmersion i] [IsClosedImmersion i'] in
/-- `Z' ×_{X'} T = Z ×_X T` for a test scheme `t : T ⟶ X'`. -/
theorem isPullback_subschemeTestBaseChange {T : Scheme.{u}} (t : T ⟶ X') :
    IsPullback (pullback.fst i' t ≫ g) (pullback.snd i' t) i (t ≫ f) :=
  (IsPullback.of_hasPullback i' t).paste_horiz sq.flip

/-- **The identification `Z ×_X T ≅ Z' ×_{X'} T`** on a test scheme `t : T ⟶ X'`. -/
def subschemeTestBaseChangeIso {T : Scheme.{u}} (t : T ⟶ X') :
    pullback i (t ≫ f) ≅ pullback i' t :=
  (isPullback_subschemeTestBaseChange i i' g f sq t).isoPullback.symm

include sq in
omit [IsClosedImmersion i] [IsClosedImmersion i'] in
/-- The identification `Z ×_X T ≅ Z' ×_{X'} T` followed by the projection to `Z'` and
`g : Z' ⟶ Z` is the first projection of `Z ×_X T`. -/
@[reassoc (attr := simp)]
theorem subschemeTestBaseChangeIso_hom_fst {T : Scheme.{u}} (t : T ⟶ X') :
    (subschemeTestBaseChangeIso i i' g f sq t).hom ≫ pullback.fst i' t ≫ g =
      pullback.fst i (t ≫ f) :=
  (isPullback_subschemeTestBaseChange i i' g f sq t).isoPullback_inv_fst

include sq in
omit [IsClosedImmersion i] [IsClosedImmersion i'] in
/-- The identification `Z ×_X T ≅ Z' ×_{X'} T` commutes with the projections to `T`. -/
@[reassoc (attr := simp)]
theorem subschemeTestBaseChangeIso_hom_snd {T : Scheme.{u}} (t : T ⟶ X') :
    (subschemeTestBaseChangeIso i i' g f sq t).hom ≫ pullback.snd i' t = pullback.snd i (t ≫ f) :=
  (isPullback_subschemeTestBaseChange i i' g f sq t).isoPullback_inv_snd

include sq in
omit [IsClosedImmersion i] [IsClosedImmersion i'] in
/-- The identification `Z ×_X T ≅ Z' ×_{X'} T` is one over the base. -/
theorem subschemeTestBaseChangeIso_hom_comp_structure {T : Scheme.{u}} (t : T ⟶ X') (sX : X ⟶ S) :
    (subschemeTestBaseChangeIso i i' g f sq t).hom ≫ (pullback.fst i' t ≫ (i' ≫ (f ≫ sX))) =
      pullback.fst i (t ≫ f) ≫ (i ≫ sX) := by
  rw [← Category.assoc i' f, sq.w, Category.assoc g, subschemeTestBaseChangeIso_hom_fst_assoc]

/-- The identification `V(𝒩) ×_X T ≅ V(g^*𝒩) ×_{X'} T` carries the base change of the bundle
projection of `𝒩` to that of `g^*𝒩`, through `Z ×_X T ≅ Z' ×_{X'} T`. -/
theorem bundleTestBaseChange_comp_subschemeTestBaseChangeIso {T : Scheme.{u}} (t : T ⟶ X') :
    bundleTestBaseChange i 𝒩.projection (t ≫ f) ≫ (subschemeTestBaseChangeIso i i' g f sq t).hom =
      (bundleTestBaseChangeIso i i' g f sq 𝒩 t).hom ≫
        bundleTestBaseChange i' (𝒩.baseChange i i' g f sq).projection t := by
  have hw := (𝒩.isPullback_baseChangeTotalSpaceMap i i' g f sq).w
  refine (isPullback_subschemeTestBaseChange i i' g f sq t).hom_ext ?_ ?_
  · simp only [Category.assoc, subschemeTestBaseChangeIso_hom_fst, bundleTestBaseChange_fst,
      bundleTestBaseChange_fst_assoc]
    rw [← hw, bundleTestBaseChangeIso_hom_fst_assoc]
  · simp only [Category.assoc, subschemeTestBaseChangeIso_hom_snd, bundleTestBaseChange_snd]
    rw [bundleTestBaseChangeIso_hom_snd]

/-- **The comparison of the normal cones on a test scheme is compatible with the closed
immersions `ι`**: on `t : T ⟶ X'` this is
`Stacks.Chow.normalConeBaseChangeMap_comp_normalConeEmbedding` read through
`V(𝒩) ×_X T ≅ V(g^*𝒩) ×_{X'} T`. -/
theorem normalConeTestBaseChange_comp_bivariantPushforwardBaseChange {T : Scheme.{u}}
    (t : T ⟶ X') :
    normalConeTestBaseChange sX i i' g f sq 𝒩 t ≫
        bivariantPushforwardBaseChange 𝒩.normalConeEmbedding (𝒩.projection ≫ i) (t ≫ f) ≫
          (bundleTestBaseChangeIso i i' g f sq 𝒩 t).hom =
      bivariantPushforwardBaseChange (𝒩.baseChange i i' g f sq).normalConeEmbedding
        ((𝒩.baseChange i i' g f sq).projection ≫ i') t := by
  refine pullback.hom_ext (baseChangeTotalSpace_hom_ext i i' g f sq 𝒩 ?_ ?_) ?_
  · simp only [Category.assoc, bundleTestBaseChangeIso_hom_fst, bivariantPushforwardBaseChange_fst]
    rw [pullback.lift_fst_assoc, Category.assoc,
      normalConeBaseChangeMap_comp_normalConeEmbedding sX i i' g f sq 𝒩]
  · have hc := pullback.condition (f := (𝒩.baseChange i i' g f sq).projection ≫ i') (g := t)
    simp only [Category.assoc]
    rw [hc, bundleTestBaseChangeIso_hom_snd_assoc, bivariantPushforwardBaseChange_snd_assoc]
    simp only [← Category.assoc, pullback.lift_snd]
    simp only [Category.assoc, Category.comp_id]
    rw [bivariantPushforwardBaseChange_snd_assoc]
  · simp

end TestGeometry

/-! ### The base-change clause of Stacks 0FBK -/

section BaseChangeClause

/-- Two proper pushforwards followed by pushforward along an isomorphism are the pushforward
along the composite. -/
theorem chowPushforwardOfIso_properChowPushforward_properChowPushforward (C : ChowSituation.{u})
    {A B D E : Scheme.{u}} (sA : A ⟶ C.S) [LocallyOfFiniteType sA] (sB : B ⟶ C.S)
    [LocallyOfFiniteType sB] (sD : D ⟶ C.S) [LocallyOfFiniteType sD] (sE : E ⟶ C.S)
    [LocallyOfFiniteType sE] (u : A ⟶ B) [IsProper u] (v : B ⟶ D) [IsProper v] (w : D ⟶ E)
    [IsIso w] (m : A ⟶ E) [IsProper m] (hm : u ≫ v ≫ w = m) (hu : u ≫ sB = sA)
    (hv : v ≫ sD = sB) (hw : w ≫ sE = sD) (hm' : m ≫ sE = sA) (k : ℤ)
    (hfacu : ProperPushforwardFactorsThroughRationalEquivalence C sA sB u hu k)
    (hfacv : ProperPushforwardFactorsThroughRationalEquivalence C sB sD v hv k)
    (hfacm : ProperPushforwardFactorsThroughRationalEquivalence C sA sE m hm' k)
    (z : chowGroup C sA k) :
    chowPushforwardOfIso C sD sE w hw k
        (properChowPushforward C sB sD v hv k hfacv
          (properChowPushforward C sA sB u hu k hfacu z)) =
      properChowPushforward C sA sE m hm' k hfacm z := by
  subst hm
  have huv : (u ≫ v) ≫ sD = sA := by rw [Category.assoc, hv, hu]
  rw [← properChowPushforward_comp_apply C sA sB sD u v (u ≫ v) rfl hu hv huv k hfacu hfacv
    (properPushforwardDescends C _ _ _ _ _),
    ← properChowPushforward_eq_chowPushforwardOfIso C sD sE w
    hw k (properPushforwardDescends C _ _ _ _ _), ← properChowPushforward_comp_apply C sA sD sE
    (u ≫ v) w (u ≫ v ≫ w) (Category.assoc _ _ _) huv hw hm' k _ _ hfacm]

variable (C : ChowSituation.{u}) {Z X Z' X' : Scheme.{u}} (sZ : Z ⟶ C.S) [LocallyOfFiniteType sZ]
  (sX : X ⟶ C.S) [LocallyOfFiniteType sX] (i : Z ⟶ X) [IsClosedImmersion i]
  (hi : i ≫ sX = sZ) (i' : Z' ⟶ X') [IsClosedImmersion i'] (g : Z' ⟶ Z)
  (f : X' ⟶ X) [LocallyOfFiniteType f] (sq : IsPullback i' g f i) (𝒩 : VirtualNormalBundle i)
  (r : ℕ) [SheafOfModules.IsFiniteLocallyFreeOfRank.{u, u, u} 𝒩.bundle r]

/-- **The base-change clause of Stacks 0FBK on cap operations.** For a cartesian square
`Z' = Z ×_X X'` and a test scheme `t : T ⟶ X'`, the class `c(Z' ⟶ X', g^*𝒩)` caps as
`c(Z ⟶ X, 𝒩)` does on `t ≫ f`, through `Z ×_X T ≅ Z' ×_{X'} T`. -/
theorem virtualNormalGysinClass_cap_baseChange
    (sZ' : Z' ⟶ C.S) [LocallyOfFiniteType sZ'] (hi' : i' ≫ (f ≫ sX) = sZ')
    {T : Scheme.{u}} (t : T ⟶ X') [LocallyOfFiniteType t] (k : ℤ)
    (α : chowGroup C (t ≫ (f ≫ sX)) k) :
    haveI : SheafOfModules.IsFiniteLocallyFreeOfRank.{u, u, u}
        (𝒩.baseChange i i' g f sq).bundle r :=
      isFiniteLocallyFreeOfRank_modulePullback g 𝒩.bundle r inferInstance
    (virtualNormalBundleClass C sZ' (f ≫ sX) i' hi' (𝒩.baseChange i i' g f sq) r).cap t k α =
      chowPushforwardOfIso C (pullback.fst i (t ≫ f) ≫ sZ) (pullback.fst i' t ≫ sZ')
        (subschemeTestBaseChangeIso i i' g f sq t).hom
        (by rw [← hi', ← hi]; exact subschemeTestBaseChangeIso_hom_comp_structure i i' g f sq t sX)
        (k - r)
        ((virtualNormalBundleClass C sZ sX i hi 𝒩 r).cap (t ≫ f) k
          (chowGroupCongr C (Category.assoc t f sX).symm k α)) := by
  subst hi'
  have : SheafOfModules.IsFiniteLocallyFreeOfRank.{u, u, u} (𝒩.baseChange i i' g f sq).bundle r :=
    isFiniteLocallyFreeOfRank_modulePullback g 𝒩.bundle r inferInstance
  set 𝒩' := 𝒩.baseChange i i' g f sq
  refine (bijective_bundleFlatPullbackChow C (i' ≫ (f ≫ sX)) i' 𝒩' r t (k - r)).1 (eq_of_heq ?_)
  refine (bundleFlatPullbackChow_virtualNormalBundleClass_cap C (i' ≫ (f ≫ sX)) (f ≫ sX) i' rfl 𝒩'
    r t k α).trans (HEq.symm ?_)
  have := 𝒩.flat_projection_of_rank r
  have := 𝒩'.flat_projection_of_rank r
  have := locallyOfFiniteType_bundleTestBaseChange i 𝒩.projection (t ≫ f)
  have := flat_bundleTestBaseChange i 𝒩.projection (𝒩.flat_projection_of_rank r) (t ≫ f)
  have := locallyOfFiniteType_bundleTestBaseChange i' 𝒩'.projection t
  have := flat_bundleTestBaseChange i' 𝒩'.projection (𝒩'.flat_projection_of_rank r) t
  have hE : (bundleTestBaseChangeIso i i' g f sq 𝒩 t).hom ≫
      (pullback.fst (𝒩'.projection ≫ i') t ≫ (𝒩'.projection ≫ i' ≫ (f ≫ sX))) =
      pullback.fst (𝒩.projection ≫ i) (t ≫ f) ≫ (𝒩.projection ≫ sZ) := by
    have hw := (𝒩.isPullback_baseChangeTotalSpaceMap i i' g f sq).w
    rw [← hi, ← Category.assoc i', sq.w, Category.assoc, ← Category.assoc 𝒩'.projection, ← hw]
    simp only [Category.assoc]
    rw [bundleTestBaseChangeIso_hom_fst_assoc]
  have hA := flatPullbackChow_chowPushforwardOfIso C _ _ _ _
    (subschemeTestBaseChangeIso i i' g f sq t).hom
    (by rw [← hi]; exact subschemeTestBaseChangeIso_hom_comp_structure i i' g f sq t sX)
    (bundleTestBaseChangeIso i i' g f sq 𝒩 t).hom hE
    (bundleTestBaseChange i 𝒩.projection (t ≫ f))
    (bundleTestBaseChange_comp_structureMorphism i 𝒩.projection sZ _ rfl (t ≫ f))
    (bundleTestBaseChange i' 𝒩'.projection t)
    (bundleTestBaseChange_comp_structureMorphism i' 𝒩'.projection _ _ rfl t)
    (bundleTestBaseChange_comp_subschemeTestBaseChangeIso i i' g f sq 𝒩 t) r
    (relativeDimension_bundleTestBaseChange i 𝒩.projection
      (𝒩.relativeDimension_projection_of_rank r) (t ≫ f))
    (relativeDimension_bundleTestBaseChange i' 𝒩'.projection
      (𝒩'.relativeDimension_projection_of_rank r) t)
    (k - r) (flatPullbackDescends C _ _ _ _ _ _ _) (flatPullbackDescends C _ _ _ _ _ _ _)
    ((virtualNormalBundleClass C sZ sX i hi 𝒩 r).cap (t ≫ f) k
      (chowGroupCongr C (Category.assoc t f sX).symm k α))
  refine (heq_of_eq hA).trans ?_
  refine (chowPushforwardOfIso_heq_congr C _ _ _ hE (by ring : (k - r) + r = k - 0) _ _
    (bundleFlatPullbackChow_virtualNormalBundleClass_cap C sZ sX i hi 𝒩 r (t ≫ f) k
      (chowGroupCongr C (Category.assoc t f sX).symm k α))).trans ?_
  have := locallyOfFiniteType_normalConeToBase C sX i
  have := locallyOfFiniteType_normalConeToBase C (f ≫ sX) i'
  have hNF := virtualNormalConeClass_cap_heq C sZ sX i hi 𝒩 (t ≫ f) k
    (chowGroupCongr C (Category.assoc t f sX).symm k α)
  have hNF' := virtualNormalConeClass_cap_heq C (i' ≫ (f ≫ sX)) (f ≫ sX) i' rfl 𝒩' t k α
  refine (chowPushforwardOfIso_heq_congr C _ _ _ hE (by ring) _ _ hNF).trans
    (HEq.trans ?_ hNF'.symm)
  apply heq_of_eq
  rw [eq_of_heq (gysinAtInfinityClass_cap_heq_blowupAtInfinityComap C sX f i.ker i'.ker
    (ker_eq_comap_of_isPullback f sq) t k α)]
  have hsq := isPullback_normalConeTestBaseChange sX i i' g f sq 𝒩 t
  have : IsProper (normalConeTestBaseChange sX i i' g f sq 𝒩 t) :=
    MorphismProperty.of_isPullback hsq inferInstance
  rw [flatPullbackChow_properChowPushforward_of_isProper C
    (modificationInfinityBaseChangeOver (f ≫ sX)
      (blowupAtInfinityToProjectiveLineProduct i'.ker (f ≫ sX)) t)
    (modificationInfinityBaseChangeOver sX (blowupAtInfinityToProjectiveLineProduct i.ker sX)
      (t ≫ f))
    (pullback.fst (𝒩'.normalConeEmbedding ≫ 𝒩'.projection ≫ i') t ≫
      (Stacks.Conormal.normalConeToBase i' ≫ i' ≫ (f ≫ sX)))
    (pullback.fst (𝒩.normalConeEmbedding ≫ 𝒩.projection ≫ i) (t ≫ f) ≫
      (Stacks.Conormal.normalConeToBase i ≫ sZ))
    (blowupAtInfinityFibreTestComap sX f i.ker i'.ker (ker_eq_comap_of_isPullback f sq) t)
    (normalConeTestMap sX i 𝒩 (t ≫ f))
    (normalConeTestMap (f ≫ sX) i' 𝒩' t)
    (normalConeTestBaseChange sX i i' g f sq 𝒩 t) hsq
    (by simp [modificationInfinityBaseChangeOver, blowupAtInfinityComap_toBase_assoc])
    (normalConeTestMap_comp_structureMorphism sZ sX i hi 𝒩 (t ≫ f))
    (normalConeTestMap_comp_structureMorphism (i' ≫ (f ≫ sX)) (f ≫ sX) i' rfl 𝒩' t) 0
    (relativeDimension_of_isOpenImmersion _) (k - 0)]
  exact chowPushforwardOfIso_properChowPushforward_properChowPushforward C _ _ _ _ _ _ _ _
    (normalConeTestBaseChange_comp_bivariantPushforwardBaseChange sX i i' g f sq 𝒩 t)
    _ _ _ _ _ _ _ _ _

omit [LocallyOfFiniteType f] [IsClosedImmersion i] [IsClosedImmersion i'] in
/-- The identification `Z ×_X T ≅ Z' ×_{X'} T` is the pasting of `Z ×_X T ≅ (Z ×_X X') ×_{X'} T`
with the identification `Z ×_X X' ≅ Z'` of the cartesian square. -/
theorem pullbackLeftPullbackSndIso_inv_transportPullbackIso_hom {T : Scheme.{u}} (t : T ⟶ X') :
    (pullbackLeftPullbackSndIso i f t).inv ≫
        (transportPullbackIso (pullback.snd i f) i' sq.flip.isoPullback.symm
          (sq.flip.isoPullback_inv_snd) t).hom =
      (subschemeTestBaseChangeIso i i' g f sq t).hom := by
  refine (isPullback_subschemeTestBaseChange i i' g f sq t).hom_ext ?_ ?_
  · simp
  · simp

/-- **The base-change clause of Stacks 0FBK in the constant-rank case**, for an arbitrary
cartesian square `Z' = Z ×_X X'` with `f : X' ⟶ X` locally of finite type: for `𝒩` of constant
rank `r`, the restriction (Stacks 0F9Z) of `c(Z ⟶ X, 𝒩)` along `f`, carried to `Z'` along the
canonical identification `Z ×_X X' ≅ Z'`, is `c(Z' ⟶ X', g^*𝒩)`, with `g^*𝒩` the virtual normal
sheaf of Stacks 0FBJ. The clause at arbitrary rank, in the completed group, is
`Stacks.Chow.completedBivariantRestriction_completedVirtualNormalGysinClass`. -/
theorem bivariantTransport_bivariantRestriction_virtualNormalGysinClass
    (sZ' : Z' ⟶ C.S) [LocallyOfFiniteType sZ'] (hi' : i' ≫ (f ≫ sX) = sZ') :
    haveI : SheafOfModules.IsFiniteLocallyFreeOfRank.{u, u, u}
        (𝒩.baseChange i i' g f sq).bundle r :=
      isFiniteLocallyFreeOfRank_modulePullback g 𝒩.bundle r inferInstance
    bivariantTransport C (gysinSystemOfInvertible C) (pullback.fst i f ≫ sZ) sZ' (f ≫ sX)
        (pullback.snd i f) (pullbackSnd_comp_structureMorphism_eq C sZ sX i hi f) i' hi'
        sq.flip.isoPullback.symm (sq.flip.isoPullback_inv_snd) (r : ℤ)
        (gysinSystemOfInvertible_isNaturalUnderBaseChangeIso C)
        (bivariantRestriction C (gysinSystemOfInvertible C) sZ sX i hi f (r : ℤ)
          (gysinSystemOfInvertible_isNaturalUnderBaseChangeIso C)
          (virtualNormalBundleClass C sZ sX i hi 𝒩 r)) =
      virtualNormalBundleClass C sZ' (f ≫ sX) i' hi' (𝒩.baseChange i i' g f sq) r := by
  have : SheafOfModules.IsFiniteLocallyFreeOfRank.{u, u, u} (𝒩.baseChange i i' g f sq).bundle r :=
    isFiniteLocallyFreeOfRank_modulePullback g 𝒩.bundle r inferInstance
  refine eq_of_isBivariantTransport C _ _ _ _ _ _ _ _ _ _ _
    (isBivariantTransport_bivariantTransport C _ _ _ _ _ _ _ _ _ _ _ _ _) ?_
  intro T t _ k α
  rw [virtualNormalGysinClass_cap_baseChange C sZ sX i hi i' g f sq 𝒩 r sZ' hi',
    bivariantTransportCap_apply, bivariantRestriction_cap, bivariantRestrictionCap_apply,
    chowPushforwardOfIso_comp_eq C _ _ _ _ _ _
      (pullbackLeftPullbackSndIso_inv_transportPullbackIso_hom i i' g f sq t)]

/-- **The base-change clause of Stacks 0FBK in the constant-rank case**, for the chosen fibre
product: for `𝒩` of constant rank `r`, the restriction (Stacks 0F9Z) of `c(Z ⟶ X, 𝒩)` along
`f : X' ⟶ X` locally of finite type is `c(Z ×_X X' ⟶ X', g^*𝒩)`. The clause at arbitrary rank,
in the completed group, is
`Stacks.Chow.completedBivariantRestriction_completedVirtualNormalGysinClass`. -/
theorem bivariantRestriction_virtualNormalGysinClass :
    bivariantRestriction C (gysinSystemOfInvertible C) sZ sX i hi f (r : ℤ)
        (gysinSystemOfInvertible_isNaturalUnderBaseChangeIso C)
        (virtualNormalBundleClass C sZ sX i hi 𝒩 r) =
      virtualNormalBundleClass C (pullback.fst i f ≫ sZ) (f ≫ sX) (pullback.snd i f)
        (pullbackSnd_comp_structureMorphism_eq C sZ sX i hi f)
        (baseChangeVirtualNormalBundle i f 𝒩) r := by
  refine BivariantClass.ext C _ _ _ _ _ _ fun {T} t _ k α => ?_
  rw [virtualNormalGysinClass_cap_baseChange C sZ sX i hi (pullback.snd i f)
      (pullback.fst i f) f (isPullback_pullbackSnd i f) 𝒩 r _
      (pullbackSnd_comp_structureMorphism_eq C sZ sX i hi f),
    bivariantRestriction_cap, bivariantRestrictionCap_apply]
  refine chowPushforwardOfIso_congr_apply C _ _ _ _ ?_ _ _ _ _
  refine (isPullback_subschemeTestBaseChange i (pullback.snd i f) (pullback.fst i f) f
    (isPullback_pullbackSnd i f) t).hom_ext ?_ ?_
  · simp
  · simp

end BaseChangeClause

end Stacks.Chow

end
