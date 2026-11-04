module

public import StacksFrontier.AlgebraicGeometry.Chow.BivariantLemmas.VirtualNormalBaseChangeBundle
public import StacksFrontier.AlgebraicGeometry.Chow.BivariantLemmas.CompletedComponentReduction
public import StacksFrontier.AlgebraicGeometry.Chow.BivariantLemmas.DualBaseChangeCompatibility
public import StacksFrontier.AlgebraicGeometry.Chow.BivariantLemmas.VirtualNormalBundleImmersionCounterparts

/-!
# The base-change clause of Stacks 0FBK, for a virtual normal sheaf of arbitrary rank

Let `(S, δ)` be the base situation of chapter 42 of the Stacks Project, let `i : Z ⟶ X` be a
closed immersion of schemes locally of finite type over `S` with a virtual normal sheaf `𝒩` of
arbitrary rank, and let `f : X' ⟶ X` be locally of finite type, with base change
`Z' = Z ×_X X' ⟶ X'`. **Stacks 0FBK** asserts that the class `c(Z ⟶ X, 𝒩) ∈ A^*(Z ⟶ X)^∧` is
compatible with base change as in Stacks 0FBJ: its restriction along `f` (Stacks 0F9Z) is
`c(Z' ⟶ X', g^*𝒩)`.

## Main results

* `Stacks.Chow.completedBivariantRestriction_completedVirtualNormalGysinClass` — **Stacks 0FBK**,
  the base-change clause at arbitrary rank: `res(c(Z ⟶ X, 𝒩)) = c(Z ×_X X' ⟶ X', g^*𝒩)` in
  `A^*(Z ×_X X' ⟶ X')^∧`.
* `Stacks.Chow.completedVirtualNormalGysinClass_cap_baseChange` — the clause on cap operations,
  degree by degree, for an arbitrary cartesian square `Z' = Z ×_X X'`.
* `Stacks.Chow.VirtualNormalBundle.baseChangeBaseChangeDualIso_hom_comp_surjection` — at any rank,
  base change of `𝒩` along two stacked cartesian squares is identified with the base change along
  the pasted square, compatibly with the surjections onto the conormal sheaf; hence
  `Stacks.Chow.virtualNormalGysinClass_baseChange_baseChange_eq_paste_vert`.
* `Stacks.Chow.virtualNormalGysinClass_baseChange_baseChange` — at constant rank of `𝒩`, base
  change along two stacked cartesian squares gives the class of the base change along the pasted
  square.

## Implementation notes

The proof is the source's, connected component by connected component. For a connected component
`Z'_w` of `Z'`, lying over the component `Z_a` of `Z` on which `𝒩` has rank `r_a`, let `U'_w ⊆ X'`
and `U_a ⊆ X` be the opens of the construction of the completed class
(`Stacks.Chow.completedVirtualNormalGysinClass`) and `V_w = U'_w ∩ f⁻¹(U_a)`, so that
`Z' ×_{X'} V_w = Z'_w = Z_a ×_{U_a} V_w`. On the piece of `Z' ×_{X'} T` over `Z'_w` both sides
vanish away from degree `r_a`, and in degree `r_a` both are the cap product with the class of the
base change of `𝒩` to `Z'_w ⟶ V_w`, read through `Z'_w ⟶ U'_w` or through `Z_a ⟶ U_a`. The two
readings agree because base change along stacked squares is base change along the pasted square
at the level of virtual normal bundles, whatever the rank of `𝒩`; a class on `Z' ×_{X'} T` is
determined by its restrictions to the pieces
(`Stacks.Chow.eq_of_chowGroupRestrict_piece_eq`).

## References

* [Stacks Project, Tag 0FBK](https://stacks.math.columbia.edu/tag/0FBK)
* [Stacks Project, Tag 0FBJ](https://stacks.math.columbia.edu/tag/0FBJ)
* [Stacks Project, Tag 0F9Z](https://stacks.math.columbia.edu/tag/0F9Z)
* [Stacks Project, Tag 0FE0](https://stacks.math.columbia.edu/tag/0FE0)
-/

@[expose] public noncomputable section

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits

universe u

namespace Stacks.Chow

/-- The base change of a virtual normal bundle of rank `r` has rank `r`. -/
private instance isFiniteLocallyFreeOfRank_baseChange_bundle {Z X Z' X' : Scheme.{u}} (i : Z ⟶ X)
    [IsClosedImmersion i] (i' : Z' ⟶ X') [IsClosedImmersion i'] (g : Z' ⟶ Z) (f : X' ⟶ X)
    (sq : IsPullback i' g f i) (𝒩 : VirtualNormalBundle i) (r : ℕ)
    [SheafOfModules.IsFiniteLocallyFreeOfRank.{u, u, u} 𝒩.bundle r] :
    SheafOfModules.IsFiniteLocallyFreeOfRank.{u, u, u} (𝒩.baseChange i i' g f sq).bundle r :=
  isFiniteLocallyFreeOfRank_modulePullback g 𝒩.bundle r inferInstance

/-! ### Stacked base changes at constant rank -/

section Stacked

variable (C : ChowSituation.{u}) {Z X Z₁ X₁ Z₂ X₂ : Scheme.{u}} (sX : X ⟶ C.S)
  [LocallyOfFiniteType sX] (i : Z ⟶ X) [IsClosedImmersion i] [LocallyOfFiniteType (i ≫ sX)]
  (i₁ : Z₁ ⟶ X₁) [IsClosedImmersion i₁] (g₁ : Z₁ ⟶ Z) (f₁ : X₁ ⟶ X) [LocallyOfFiniteType f₁]
  (sq₁ : IsPullback i₁ g₁ f₁ i) (i₂ : Z₂ ⟶ X₂) [IsClosedImmersion i₂] (g₂ : Z₂ ⟶ Z₁)
  (f₂ : X₂ ⟶ X₁) [LocallyOfFiniteType f₂] (sq₂ : IsPullback i₂ g₂ f₂ i₁)
  (𝒩 : VirtualNormalBundle i) (r : ℕ)
  [SheafOfModules.IsFiniteLocallyFreeOfRank.{u, u, u} 𝒩.bundle r]

/-- **Base change along stacked squares, at constant rank** (Stacks 0FBK and Stacks 0FBJ). For
cartesian squares `Z₁ = Z ×_X X₁` and `Z₂ = Z₁ ×_{X₁} X₂` of closed immersions, the class of the
base change of `𝒩` along the second square of its base change along the first is the class of the
base change of `𝒩` along the pasted square `Z₂ = Z ×_X X₂`: both cap as `c(Z ⟶ X, 𝒩)` does on
`t ≫ (X₂ ⟶ X)`, by the base-change clause of Stacks 0FBK
(`Stacks.Chow.virtualNormalGysinClass_cap_baseChange`). -/
theorem virtualNormalGysinClass_baseChange_baseChange (sZ₂ : Z₂ ⟶ C.S) [LocallyOfFiniteType sZ₂]
    (hi₂ : i₂ ≫ ((f₂ ≫ f₁) ≫ sX) = sZ₂) :
    haveI : SheafOfModules.IsFiniteLocallyFreeOfRank.{u, u, u}
        (𝒩.baseChange i i₁ g₁ f₁ sq₁).bundle r :=
      isFiniteLocallyFreeOfRank_modulePullback g₁ 𝒩.bundle r inferInstance
    haveI : SheafOfModules.IsFiniteLocallyFreeOfRank.{u, u, u}
        ((𝒩.baseChange i i₁ g₁ f₁ sq₁).baseChange i₁ i₂ g₂ f₂ sq₂).bundle r :=
      isFiniteLocallyFreeOfRank_modulePullback g₂ _ r inferInstance
    haveI : SheafOfModules.IsFiniteLocallyFreeOfRank.{u, u, u}
        (𝒩.baseChange i i₂ (g₂ ≫ g₁) (f₂ ≫ f₁) (sq₂.paste_vert sq₁)).bundle r :=
      isFiniteLocallyFreeOfRank_modulePullback (g₂ ≫ g₁) 𝒩.bundle r inferInstance
    virtualNormalBundleClass C sZ₂ ((f₂ ≫ f₁) ≫ sX) i₂ hi₂
        ((𝒩.baseChange i i₁ g₁ f₁ sq₁).baseChange i₁ i₂ g₂ f₂ sq₂) r =
      virtualNormalBundleClass C sZ₂ ((f₂ ≫ f₁) ≫ sX) i₂ hi₂
        (𝒩.baseChange i i₂ (g₂ ≫ g₁) (f₂ ≫ f₁) (sq₂.paste_vert sq₁)) r := by
  have : LocallyOfFiniteType (g₁ ≫ (i ≫ sX)) := by
    rw [← Category.assoc, ← sq₁.w, Category.assoc]; infer_instance
  have hi₁ : i₁ ≫ (f₁ ≫ sX) = g₁ ≫ (i ≫ sX) := by rw [← Category.assoc, sq₁.w, Category.assoc]
  have hi₂' : i₂ ≫ (f₂ ≫ (f₁ ≫ sX)) = sZ₂ := by rw [← hi₂, Category.assoc f₂]
  -- the class of a bundle does not depend on how the structure morphism of the target is written
  have hbase : ∀ (s s' : X₂ ⟶ C.S) [LocallyOfFiniteType s] [LocallyOfFiniteType s']
      (_ : s = s') (h₁ : i₂ ≫ s = sZ₂) (h₂ : i₂ ≫ s' = sZ₂) (N : VirtualNormalBundle i₂)
      [SheafOfModules.IsFiniteLocallyFreeOfRank.{u, u, u} N.bundle r] {T : Scheme.{u}}
      (t : T ⟶ X₂) [LocallyOfFiniteType t] (k : ℤ) (a : chowGroup C (t ≫ s) k)
      (a' : chowGroup C (t ≫ s') k), a ≍ a' →
      (virtualNormalBundleClass C sZ₂ s i₂ h₁ N r).cap t k a =
        (virtualNormalBundleClass C sZ₂ s' i₂ h₂ N r).cap t k a' := by
    intro s s' _ _ hs h₁ h₂ N _ T t _ k a a' ha
    subst hs
    cases ha
    rfl
  refine BivariantClass.ext C _ _ _ _ _ _ fun {T} t _ k α ↦ ?_
  refine (hbase _ (f₂ ≫ (f₁ ≫ sX)) (Category.assoc _ _ _) hi₂ hi₂'
    ((𝒩.baseChange i i₁ g₁ f₁ sq₁).baseChange i₁ i₂ g₂ f₂ sq₂) t k α
    (chowGroupCongr C (by rw [Category.assoc f₂]) k α) (chowGroupCongr_heq C _ k α).symm).trans ?_
  rw [virtualNormalGysinClass_cap_baseChange C (g₁ ≫ (i ≫ sX)) (f₁ ≫ sX) i₁ hi₁ i₂ g₂ f₂ sq₂
      (𝒩.baseChange i i₁ g₁ f₁ sq₁) r sZ₂ hi₂' t k,
    virtualNormalGysinClass_cap_baseChange C (i ≫ sX) sX i rfl i₁ g₁ f₁ sq₁ 𝒩 r
      (g₁ ≫ (i ≫ sX)) hi₁ (t ≫ f₂) k,
    virtualNormalGysinClass_cap_baseChange C (i ≫ sX) sX i rfl i₂ (g₂ ≫ g₁) (f₂ ≫ f₁)
      (sq₂.paste_vert sq₁) 𝒩 r sZ₂ hi₂ t k, chowPushforwardOfIso_comp_apply,
    chowGroupCongr_chowGroupCongr]
  rw [chowGroupCongr_chowGroupCongr, ← chowPushforwardOfIso_congrHom_cap C
    (gysinSystemOfInvertible C) (i ≫ sX) sX i rfl (r : ℤ)
    (virtualNormalBundleClass C (i ≫ sX) sX i rfl 𝒩 r) (Category.assoc t f₂ f₁) (by simp) k α
    (by simp) (by simp), chowPushforwardOfIso_comp_apply]
  refine chowPushforwardOfIso_congr_apply C _ _ _ _ ?_ _ _ _ _
  refine pullback.hom_ext ((sq₂.paste_vert sq₁).hom_ext ?_ ?_) ?_
  · simp only [Category.assoc, pullback.condition]
    simp
  · simp
  · simp

end Stacked

section DualIso

open RingedSpaceModuleAdjunction Stacks.AlgebraicGeometry.ReflexiveModules

variable {Z X Z₁ X₁ Z₂ X₂ : Scheme.{u}} (i : Z ⟶ X) [IsClosedImmersion i]
  (i₁ : Z₁ ⟶ X₁) [IsClosedImmersion i₁] (g₁ : Z₁ ⟶ Z) (f₁ : X₁ ⟶ X)
  (sq₁ : IsPullback i₁ g₁ f₁ i) (i₂ : Z₂ ⟶ X₂) [IsClosedImmersion i₂] (g₂ : Z₂ ⟶ Z₁)
  (f₂ : X₂ ⟶ X₁) (sq₂ : IsPullback i₂ g₂ f₂ i₁)
  (𝒩 : VirtualNormalBundle i)

/-- The identification `((g₂ ≫ g₁)^*𝒩)^∨ ≅ (g₂^*g₁^*𝒩)^∨` of the duals of the base change of `𝒩`
along a pasted square and of its iterated base change along the two squares: the dual of the
pullback-composition isomorphism. -/
def VirtualNormalBundle.baseChangeBaseChangeDualIso :
    dualSheaf (𝒩.baseChange i i₂ (g₂ ≫ g₁) (f₂ ≫ f₁) (sq₂.paste_vert sq₁)).bundle ≅
      dualSheaf ((𝒩.baseChange i i₁ g₁ f₁ sq₁).baseChange i₁ i₂ g₂ f₂ sq₂).bundle :=
  (dualFunctor Z₂).mapIso
    ((modulePullbackComp g₂.toLRSHom.toShHom g₁.toLRSHom.toShHom).app 𝒩.bundle).symm.op

/-- The identification of the duals of the two base changes is the dual of the
pullback-composition comparison. -/
theorem VirtualNormalBundle.baseChangeBaseChangeDualIso_hom :
    (𝒩.baseChangeBaseChangeDualIso i i₁ g₁ f₁ sq₁ i₂ g₂ f₂ sq₂).hom =
      dualMap ((modulePullbackComp g₂.toLRSHom.toShHom g₁.toLRSHom.toShHom).inv.app
        𝒩.bundle) := rfl

/-- A diagram chase in a category: the identity behind
`Stacks.Chow.VirtualNormalBundle.baseChangeBaseChangeDualIso_hom_comp_surjection`, with the
dual base-change maps, the pullback-composition isomorphism and the conormal maps as abstract
morphisms. -/
theorem comp_map_comp_of_dualBaseChange {𝒞 𝒟 : Type*} [Category 𝒞] [Category 𝒟] (F : 𝒞 ⥤ 𝒟)
    {X₁ X₂ X₃ X₄ : 𝒞} {Y₀ Y₁ W W₂ Y₅ : 𝒟} (b : X₁ ≅ X₂) (s : X₁ ⟶ X₃) (c : X₃ ⟶ X₄)
    (d : Y₀ ⟶ Y₁) (e : F.obj X₂ ≅ Y₁) (c₂ : F.obj X₄ ⟶ Y₅) (a : W ≅ Y₀) (m : W ≅ F.obj X₁)
    (fs : W ⟶ W₂) (m' : W₂ ⟶ F.obj X₃)
    (hd : m.inv ≫ a.hom ≫ d = F.map b.hom ≫ e.hom) (hn : m.hom ≫ F.map s = fs ≫ m') :
    d ≫ e.inv ≫ F.map (b.inv ≫ s ≫ c) ≫ c₂ = a.inv ≫ fs ≫ m' ≫ F.map c ≫ c₂ := by
  have h1 : d = a.inv ≫ m.hom ≫ F.map b.hom ≫ e.hom := by
    rw [← hd, Iso.hom_inv_id_assoc, Iso.inv_hom_id_assoc]
  rw [h1, Functor.map_comp, Functor.map_comp]
  simp only [Category.assoc, Iso.hom_inv_id_assoc, ← Functor.map_comp_assoc]
  rw [Functor.map_comp, Category.assoc, reassoc_of% hn]

/-- **Base change of a virtual normal bundle along stacked squares, at any rank** (Stacks 0FBJ).
The base change of `𝒩` along the pasted square `Z₂ = Z ×_X X₂` and its iterated base change
along `Z₁ = Z ×_X X₁` and `Z₂ = Z₁ ×_{X₁} X₂` are identified compatibly with the surjections onto
the conormal sheaf of `Z₂ ⟶ X₂`: by the compatibility of the dual base-change map with
composition (`Stacks.Chow.pullbackDualMap_comp`) and the functoriality of the conormal map for
stacked squares (`Stacks.Immersion.immersionConormalSheafMap_comp`). -/
theorem VirtualNormalBundle.baseChangeBaseChangeDualIso_hom_comp_surjection :
    (𝒩.baseChangeBaseChangeDualIso i i₁ g₁ f₁ sq₁ i₂ g₂ f₂ sq₂).hom ≫
        ((𝒩.baseChange i i₁ g₁ f₁ sq₁).baseChange i₁ i₂ g₂ f₂ sq₂).surjection =
      (𝒩.baseChange i i₂ (g₂ ≫ g₁) (f₂ ≫ f₁) (sq₂.paste_vert sq₁)).surjection := by
  rw [VirtualNormalBundle.baseChange_surjection, VirtualNormalBundle.baseChange_surjection,
    VirtualNormalBundle.baseChange_surjection,
    Stacks.Immersion.immersionConormalSheafMap_comp i₂ i₁ i g₂ f₂ sq₂.w g₁ f₁ sq₁.w]
  exact comp_map_comp_of_dualBaseChange (modulePullback g₂.toLRSHom.toShHom)
    (@asIso _ _ _ _ (pullbackDualMap g₁ 𝒩.bundle)
      (pullbackDualMap_isIso _ _ 𝒩.isFiniteLocallyFree)) _ _ _
    (@asIso _ _ _ _ (pullbackDualMap g₂ (𝒩.baseChange i i₁ g₁ f₁ sq₁).bundle)
      (pullbackDualMap_isIso _ _ (𝒩.baseChange i i₁ g₁ f₁ sq₁).isFiniteLocallyFree)) _
    (@asIso _ _ _ _ (pullbackDualMap (g₂ ≫ g₁) 𝒩.bundle)
      (pullbackDualMap_isIso _ _ 𝒩.isFiniteLocallyFree))
    ((modulePullbackComp g₂.toLRSHom.toShHom g₁.toLRSHom.toShHom).app (dualSheaf 𝒩.bundle)) _ _
    (pullbackDualMap_comp g₂ g₁ 𝒩.bundle)
    ((modulePullbackComp g₂.toLRSHom.toShHom g₁.toLRSHom.toShHom).hom.naturality
      𝒩.surjection).symm


/-- The base change of `𝒩` along a pasted square has rank `r` when the iterated base change
does: the two modules are isomorphic. -/
theorem isFiniteLocallyFreeOfRank_baseChange_paste_vert (r : ℕ)
    [h : SheafOfModules.IsFiniteLocallyFreeOfRank.{u, u, u}
      ((𝒩.baseChange i i₁ g₁ f₁ sq₁).baseChange i₁ i₂ g₂ f₂ sq₂).bundle r] :
    SheafOfModules.IsFiniteLocallyFreeOfRank.{u, u, u}
      (𝒩.baseChange i i₂ (g₂ ≫ g₁) (f₂ ≫ f₁) (sq₂.paste_vert sq₁)).bundle r :=
  SheafOfModules.IsFiniteLocallyFreeOfRank.of_iso.{u, u, u}
    ((modulePullbackComp g₂.toLRSHom.toShHom g₁.toLRSHom.toShHom).app 𝒩.bundle).symm h

/-- **Stacked base changes at any rank.** For a virtual normal bundle `𝒩` of arbitrary rank and
stacked cartesian squares of closed immersions on which the base change has constant rank `r`,
the class of the iterated base change is the class of the base change along the pasted square:
the two bundles are identified compatibly with the surjections onto the conormal sheaf
(`Stacks.Chow.virtualNormalGysinClass_eq_of_dualIso`). -/
theorem virtualNormalGysinClass_baseChange_baseChange_eq_paste_vert (C : ChowSituation.{u})
    (sZ₂ : Z₂ ⟶ C.S) [LocallyOfFiniteType sZ₂] (sX₂ : X₂ ⟶ C.S) [LocallyOfFiniteType sX₂]
    (hi₂ : i₂ ≫ sX₂ = sZ₂) (r : ℕ)
    [SheafOfModules.IsFiniteLocallyFreeOfRank.{u, u, u}
      ((𝒩.baseChange i i₁ g₁ f₁ sq₁).baseChange i₁ i₂ g₂ f₂ sq₂).bundle r] :
    haveI := isFiniteLocallyFreeOfRank_baseChange_paste_vert i i₁ g₁ f₁ sq₁ i₂ g₂ f₂ sq₂ 𝒩 r
    virtualNormalBundleClass C sZ₂ sX₂ i₂ hi₂
        ((𝒩.baseChange i i₁ g₁ f₁ sq₁).baseChange i₁ i₂ g₂ f₂ sq₂) r =
      virtualNormalBundleClass C sZ₂ sX₂ i₂ hi₂
        (𝒩.baseChange i i₂ (g₂ ≫ g₁) (f₂ ≫ f₁) (sq₂.paste_vert sq₁)) r :=
  have := isFiniteLocallyFreeOfRank_baseChange_paste_vert i i₁ g₁ f₁ sq₁ i₂ g₂ f₂ sq₂ 𝒩 r
  virtualNormalGysinClass_eq_of_dualIso C sZ₂ sX₂ i₂ hi₂ _ _
    (𝒩.baseChangeBaseChangeDualIso i i₁ g₁ f₁ sq₁ i₂ g₂ f₂ sq₂)
    (𝒩.baseChangeBaseChangeDualIso_hom_comp_surjection i i₁ g₁ f₁ sq₁ i₂ g₂ f₂ sq₂) r


end DualIso

section SideRestriction

variable (C : ChowSituation.{u}) {Z₁ X₁ W V T₁ S : Scheme.{u}} (sZ₁ : Z₁ ⟶ C.S)
  [LocallyOfFiniteType sZ₁] (sX₁ : X₁ ⟶ C.S) [LocallyOfFiniteType sX₁] (i₁ : Z₁ ⟶ X₁)
  [IsClosedImmersion i₁] (hi₁ : i₁ ≫ sX₁ = sZ₁) (N₁ : VirtualNormalBundle i₁) (m : ℕ)
  [SheafOfModules.IsFiniteLocallyFreeOfRank.{u, u, u} N₁.bundle m] (iV : W ⟶ V)
  [IsClosedImmersion iV] (h : W ⟶ Z₁) (ρ : V ⟶ X₁) [LocallyOfFiniteType ρ]
  (sq : IsPullback iV h ρ i₁) (sW : W ⟶ C.S) [LocallyOfFiniteType sW]
  (hiV : iV ≫ (ρ ≫ sX₁) = sW) (t₁ : T₁ ⟶ X₁) [LocallyOfFiniteType t₁] (v : S ⟶ T₁)
  [IsOpenImmersion v] (s : S ⟶ V) [LocallyOfFiniteType s] (hs : v ≫ t₁ = s ≫ ρ)

/-- For a cartesian square `W = Z₁ ×_{X₁} V` and a test scheme `t₁ : T₁ ⟶ X₁` restricted along an
open immersion `v : S ⟶ T₁` with `v ≫ t₁ = s ≫ ρ`, the map `W ×_V S ⟶ Z₁ ×_{X₁} T₁`. -/
abbrev testRestrictionMap : pullback iV s ⟶ pullback i₁ t₁ :=
  pullback.map iV s i₁ t₁ h v ρ sq.w hs.symm

omit [LocallyOfFiniteType ρ] [LocallyOfFiniteType t₁] [IsOpenImmersion v] [LocallyOfFiniteType s] in
/-- The map `W ×_V S ⟶ Z₁ ×_{X₁} T₁` is the identification `W ×_V S ≅ Z₁ ×_{X₁} S` followed by
the base change of `v`. -/
theorem testRestrictionMap_eq :
    testRestrictionMap i₁ iV h ρ sq t₁ v s hs =
      (subschemeTestBaseChangeIso i₁ iV h ρ sq s).inv ≫
        baseChangeMapOfEq i₁ t₁ v (s ≫ ρ) hs := by
  rw [Iso.eq_inv_comp]
  refine pullback.hom_ext ?_ ?_
  · simp
  · simp

/-- The base change of the open immersion `v` along `i₁` is an open immersion. -/
private instance isOpenImmersion_baseChangeMapOfEq_test :
    IsOpenImmersion (baseChangeMapOfEq i₁ t₁ v (s ≫ ρ) hs) :=
  MorphismProperty.of_isPullback (isPullback_baseChangeMapOfEq i₁ t₁ v (s ≫ ρ) hs)
    (P := @IsOpenImmersion) inferInstance

omit [LocallyOfFiniteType ρ] [LocallyOfFiniteType t₁] [LocallyOfFiniteType s] in
/-- The map `W ×_V S ⟶ Z₁ ×_{X₁} T₁` is an open immersion, as a base change of `v` up to
isomorphism. -/
theorem isOpenImmersion_testRestrictionMap :
    IsOpenImmersion (testRestrictionMap i₁ iV h ρ sq t₁ v s hs) := by
  rw [testRestrictionMap_eq]
  infer_instance

omit [LocallyOfFiniteType sZ₁] [LocallyOfFiniteType sX₁] [IsClosedImmersion i₁]
  [IsClosedImmersion iV] [LocallyOfFiniteType ρ] [LocallyOfFiniteType sW] [LocallyOfFiniteType t₁]
  [IsOpenImmersion v] [LocallyOfFiniteType s] in
include hi₁ hiV in
/-- The map `W ×_V S ⟶ Z₁ ×_{X₁} T₁` is a morphism over the base. -/
theorem testRestrictionMap_comp_structureMorphism :
    testRestrictionMap i₁ iV h ρ sq t₁ v s hs ≫ (pullback.fst i₁ t₁ ≫ sZ₁) =
      pullback.fst iV s ≫ sW := by
  rw [← hiV, ← hi₁, pullback.lift_fst_assoc, Category.assoc, ← reassoc_of% sq.w]

/-- **The constant-rank class on a restricted test scheme, through a cartesian square.** For a
cartesian square `W = Z₁ ×_{X₁} V` and an open immersion `v : S ⟶ T₁` of test schemes with
`v ≫ t₁ = s ≫ ρ`, the restriction of `c(Z₁ ⟶ X₁, 𝒩₁) ∩ α` to `W ×_V S` is
`c(W ⟶ V, h^*𝒩₁) ∩ α|_S`: by the base-change clause at constant rank
(`Stacks.Chow.virtualNormalGysinClass_cap_baseChange`) and the compatibility of the cap
operation with restricting the test scheme to an open
(`Stacks.Chow.BivariantClass.cap_chowGroupRestrict`). -/
theorem chowGroupRestrict_testRestrictionMap_virtualNormalGysinClass_cap (k : ℤ)
    (α : chowGroup C (t₁ ≫ sX₁) k) :
    haveI := isOpenImmersion_testRestrictionMap i₁ iV h ρ sq t₁ v s hs
    haveI : SheafOfModules.IsFiniteLocallyFreeOfRank.{u, u, u}
        (N₁.baseChange i₁ iV h ρ sq).bundle m :=
      isFiniteLocallyFreeOfRank_modulePullback h N₁.bundle m inferInstance
    chowGroupRestrict C (pullback.fst i₁ t₁ ≫ sZ₁) (pullback.fst iV s ≫ sW)
        (testRestrictionMap i₁ iV h ρ sq t₁ v s hs)
        (testRestrictionMap_comp_structureMorphism C sZ₁ sX₁ i₁ hi₁ iV h ρ sq sW hiV t₁ v s hs)
        (k - m) ((virtualNormalBundleClass C sZ₁ sX₁ i₁ hi₁ N₁ m).cap t₁ k α) =
      (virtualNormalBundleClass C sW (ρ ≫ sX₁) iV hiV (N₁.baseChange i₁ iV h ρ sq) m).cap s k
        (chowGroupRestrict C (t₁ ≫ sX₁) (s ≫ (ρ ≫ sX₁)) v
          (by rw [← Category.assoc, hs, Category.assoc]) k α) := by
  have := isOpenImmersion_testRestrictionMap i₁ iV h ρ sq t₁ v s hs
  rw [virtualNormalGysinClass_cap_baseChange C sZ₁ sX₁ i₁ hi₁ iV h ρ sq N₁ m sW hiV s k,
    chowGroupCongr_chowGroupRestrict C _ _ _ v _ (by rw [← hs, Category.assoc]),
    ← BivariantClass.cap_chowGroupRestrict C _ sZ₁ sX₁ i₁ hi₁ (m : ℤ) _ t₁ v (s ≫ ρ) hs
      (baseChangeMapOfEq i₁ t₁ v (s ≫ ρ) hs) (isPullback_baseChangeMapOfEq i₁ t₁ v (s ≫ ρ) hs)
      (baseChangeMapOfEq_fst _ _ _ _ _) k _ (baseChangeMapOfEq_comp_structure sZ₁ i₁ t₁ v _ hs)]
  refine Eq.trans ?_ (chowGroupRestrict_eq_chowPushforwardOfIso_inv C _ _
    (subschemeTestBaseChangeIso i₁ iV h ρ sq s).symm ?_ _ _)
  · rw [chowGroupRestrict_comp]
    exact DFunLike.congr_fun (chowGroupRestrict_congr C _ _ _ _ _ _
      (testRestrictionMap_eq i₁ iV h ρ sq t₁ v s hs) _) _
  · rw [Iso.symm_hom, ← testRestrictionMap_comp_structureMorphism C sZ₁ sX₁ i₁ hi₁ iV h ρ sq sW
      hiV t₁ v s hs, testRestrictionMap_eq, Category.assoc, baseChangeMapOfEq_comp_structure]

end SideRestriction


section ComponentGeometry

variable {Z X Z' X' : Scheme.{u}} (i : Z ⟶ X) [IsClosedImmersion i] (i' : Z' ⟶ X')
  [IsClosedImmersion i'] (g : Z' ⟶ Z) (f : X' ⟶ X) (sq : IsPullback i' g f i)
  [LocallyConnectedSpace Z] [LocallyConnectedSpace X] [LocallyConnectedSpace X']
  [LocallyConnectedSpace Z'] (w : _root_.ConnectedComponents Z')

/-- The connected component `Z_a` of `Z` below a connected component `Z'_w` of `Z'`. -/
abbrev componentBelow : _root_.ConnectedComponents Z :=
  g.continuous.connectedComponentsMap w

/-- The open `V_w = U'_w ∩ f⁻¹(U_a)` of `X'`, for the component neighbourhoods `U'_w ⊆ X'` of
`Z'_w` and `U_a ⊆ X` of the component `Z_a` below it: an open with `Z' ×_{X'} V_w = Z'_w` lying
over `U_a`. -/
def baseChangeComponentOpen : X'.Opens :=
  componentNeighbourhood i' w ⊓
    f ⁻¹ᵁ componentNeighbourhood i (componentBelow g w)

/-- `V_w ⊆ U'_w`. -/
theorem baseChangeComponentOpen_le :
    baseChangeComponentOpen i i' g f w ≤ componentNeighbourhood i' w :=
  inf_le_left

/-- `V_w ⊆ f⁻¹(U_a)`. -/
theorem baseChangeComponentOpen_le_preimage :
    baseChangeComponentOpen i i' g f w ≤ f ⁻¹ᵁ componentNeighbourhood i (componentBelow g w) :=
  inf_le_right

include sq in
/-- The component `Z'_w` lies in the preimage of `V_w`. -/
theorem connectedComponentOpens_le_preimage_baseChangeComponentOpen :
    Z'.connectedComponentOpens w ≤
      i' ⁻¹ᵁ baseChangeComponentOpen i i' g f w := by
  intro x hx
  refine ⟨(preimage_componentNeighbourhood i' w).ge hx, ?_⟩
  have h := (preimage_preimage_componentNeighbourhood (sq)
    (componentBelow g w)).ge (g.connectedComponentOpens_le_preimage w hx)
  exact h

/-- The closed immersion `Z'_w ⟶ V_w`, the restriction of `i'`. -/
def baseChangeComponentImmersion :
    (Z'.connectedComponentOpens w : Scheme.{u}) ⟶
      (baseChangeComponentOpen i i' g f w : Scheme.{u}) :=
  i'.resLE _ _ (connectedComponentOpens_le_preimage_baseChangeComponentOpen i i' g f sq w)

/-- `Z'_w ⟶ V_w ⟶ X'` is `Z'_w ⟶ Z' ⟶ X'`. -/
@[reassoc (attr := simp)]
theorem baseChangeComponentImmersion_ι :
    baseChangeComponentImmersion i i' g f sq w ≫ (baseChangeComponentOpen i i' g f w).ι =
      (Z'.connectedComponentOpens w).ι ≫ i' :=
  Scheme.Hom.resLE_comp_ι _ _

/-- `Z'_w ⟶ V_w ⟶ U'_w` is the closed immersion `Z'_w ⟶ U'_w` of the construction of the
completed class. -/
theorem baseChangeComponentImmersion_homOfLE :
    baseChangeComponentImmersion i i' g f sq w ≫
        X'.homOfLE (baseChangeComponentOpen_le i i' g f w) =
      componentRestriction i' w := by
  rw [← cancel_mono (componentNeighbourhood i' w).ι, Category.assoc,
    Scheme.homOfLE_ι, baseChangeComponentImmersion_ι, componentRestriction_ι]

/-- `Z'_w = Z'_w ×_{U'_w} V_w`. -/
theorem isPullback_baseChangeComponentImmersion_homOfLE :
    IsPullback (baseChangeComponentImmersion i i' g f sq w) (𝟙 _)
      (X'.homOfLE (baseChangeComponentOpen_le i i' g f w))
      (componentRestriction i' w) :=
  IsPullback.of_vert_isIso_mono ⟨by rw [baseChangeComponentImmersion_homOfLE, Category.id_comp]⟩

/-- `Z'_w ⟶ V_w` is a closed immersion. -/
instance isClosedImmersion_baseChangeComponentImmersion :
    IsClosedImmersion (baseChangeComponentImmersion i i' g f sq w) :=
  MorphismProperty.of_isPullback (P := @IsClosedImmersion)
    (isPullback_baseChangeComponentImmersion_homOfLE i i' g f sq w).flip inferInstance

/-- The restriction `V_w ⟶ U_a` of `f`. -/
def baseChangeComponentMap :
    (baseChangeComponentOpen i i' g f w : Scheme.{u}) ⟶
      (componentNeighbourhood i (componentBelow g w) : Scheme.{u}) :=
  f.resLE _ _ (baseChangeComponentOpen_le_preimage i i' g f w)

/-- `V_w ⟶ U_a ⟶ X` is `V_w ⟶ X' ⟶ X`. -/
@[reassoc (attr := simp)]
theorem baseChangeComponentMap_ι :
    baseChangeComponentMap i i' g f w ≫ (componentNeighbourhood i (componentBelow g w)).ι =
      (baseChangeComponentOpen i i' g f w).ι ≫ f :=
  Scheme.Hom.resLE_comp_ι _ _

/-- `V_w ⟶ U_a` is locally of finite type. -/
instance locallyOfFiniteType_baseChangeComponentMap [LocallyOfFiniteType f] :
    LocallyOfFiniteType (baseChangeComponentMap i i' g f w) := by
  have : LocallyOfFiniteType (baseChangeComponentMap i i' g f w ≫
      (componentNeighbourhood i (componentBelow g w)).ι) := by
    rw [baseChangeComponentMap_ι]; infer_instance
  exact LocallyOfFiniteType.of_comp this

/-- **`Z'_w = Z_a ×_{U_a} V_w`**: the square of `Z'_w ⟶ V_w` over the closed immersion
`Z_a ⟶ U_a` of the construction of the completed class is cartesian, since the pasted square over
`Z ⟶ X` is. -/
theorem isPullback_baseChangeComponentMap :
    IsPullback (baseChangeComponentImmersion i i' g f sq w)
      (g.resConnectedComponent w) (baseChangeComponentMap i i' g f w)
      (componentRestriction i (componentBelow g w)) := by
  have H := ((isPullback_baseChangeComponentImmersion_homOfLE i i' g f sq w).paste_vert
    (isPullback_componentRestriction i' w)).paste_vert (sq)
  have e₁ : (𝟙 _ ≫ (Z'.connectedComponentOpens w).ι) ≫ g =
      g.resConnectedComponent w ≫
        (Z.connectedComponentOpens (componentBelow g w)).ι := by
    rw [Category.id_comp, Scheme.Hom.resConnectedComponent_comp_ι]
  have e₂ : (X'.homOfLE (baseChangeComponentOpen_le i i' g f w) ≫
      (componentNeighbourhood i' w).ι) ≫ f =
      baseChangeComponentMap i i' g f w ≫ (componentNeighbourhood i (componentBelow g w)).ι := by
    rw [Scheme.homOfLE_ι, baseChangeComponentMap_ι]
  rw [e₁, e₂] at H
  refine H.of_bot ?_ (isPullback_componentRestriction i (componentBelow g w))
  rw [← cancel_mono (componentNeighbourhood i (componentBelow g w)).ι, Category.assoc,
    Category.assoc, baseChangeComponentMap_ι, componentRestriction_ι,
    baseChangeComponentImmersion_ι_assoc, sq.w, Scheme.Hom.resConnectedComponent_comp_ι_assoc]

end ComponentGeometry


section ComponentClass

variable (C : ChowSituation.{u}) {Z X Z' X' : Scheme.{u}} (sZ : Z ⟶ C.S)
  [LocallyOfFiniteType sZ] (sX : X ⟶ C.S) [LocallyOfFiniteType sX] (i : Z ⟶ X)
  [IsClosedImmersion i] (hi : i ≫ sX = sZ) (i' : Z' ⟶ X') [IsClosedImmersion i'] (g : Z' ⟶ Z)
  (f : X' ⟶ X) [LocallyOfFiniteType f] (sq : IsPullback i' g f i) (𝒩 : VirtualNormalBundle i)
  [LocallyConnectedSpace Z] [LocallyConnectedSpace X] [LocallyConnectedSpace X']
  [LocallyConnectedSpace Z'] (w : _root_.ConnectedComponents Z')

/-- The class of Stacks 0FBK at constant rank of equal virtual normal bundles agree, whatever the
rank instances. -/
theorem virtualNormalGysinClass_congr_bundle {Z₀ X₀ : Scheme.{u}} (sZ₀ : Z₀ ⟶ C.S)
    [LocallyOfFiniteType sZ₀] (sX₀ : X₀ ⟶ C.S) [LocallyOfFiniteType sX₀] (i₀ : Z₀ ⟶ X₀)
    [IsClosedImmersion i₀] (hi₀ : i₀ ≫ sX₀ = sZ₀) {N₁ N₂ : VirtualNormalBundle i₀} (h : N₁ = N₂)
    (r : ℕ) [SheafOfModules.IsFiniteLocallyFreeOfRank.{u, u, u} N₁.bundle r]
    [SheafOfModules.IsFiniteLocallyFreeOfRank.{u, u, u} N₂.bundle r] :
    virtualNormalBundleClass C sZ₀ sX₀ i₀ hi₀ N₁ r =
      virtualNormalBundleClass C sZ₀ sX₀ i₀ hi₀ N₂ r := by
  subst h
  rfl

omit [LocallyOfFiniteType f] in
/-- The base changes of `𝒩` to `Z'_w ⟶ V_w` along the two pasted squares, through `Z' ⟶ X'` and
`Z'_w ⟶ U'_w` or through `Z_a ⟶ U_a`, agree. -/
theorem baseChange_paste_baseChangeComponent :
    𝒩.baseChange i (baseChangeComponentImmersion i i' g f sq w)
        ((𝟙 _ ≫ (Z'.connectedComponentOpens w).ι) ≫ g)
        ((X'.homOfLE (baseChangeComponentOpen_le i i' g f w) ≫
          (componentNeighbourhood i' w).ι) ≫ f)
        (((isPullback_baseChangeComponentImmersion_homOfLE i i' g f sq w).paste_vert
          (isPullback_componentRestriction i' w)).paste_vert
            (sq)) =
      𝒩.baseChange i (baseChangeComponentImmersion i i' g f sq w)
        (g.resConnectedComponent w ≫
          (Z.connectedComponentOpens (componentBelow g w)).ι)
        (baseChangeComponentMap i i' g f w ≫
          (componentNeighbourhood i (componentBelow g w)).ι)
        ((isPullback_baseChangeComponentMap i i' g f sq w).paste_vert
          (isPullback_componentRestriction i (componentBelow g w))) :=
  VirtualNormalBundle.baseChange_congr 𝒩
    (by rw [Category.id_comp, Scheme.Hom.resConnectedComponent_comp_ι])
    (by rw [Scheme.homOfLE_ι, baseChangeComponentMap_ι]) _ _

omit [LocallyOfFiniteType f] in
/-- **The rank of `g^*𝒩` on `Z'_w` is the rank of `𝒩` on the component `Z_a` below it.** -/
theorem componentRank_baseChange :
    componentRank (𝒩.baseChange i i' g f sq).bundle w =
      componentRank 𝒩.bundle (componentBelow g w) := by
  have : SheafOfModules.IsFiniteLocallyFreeOfRank.{u, u, u}
      ((((𝒩.baseChange i i' g f (sq)).baseChange
        i' (componentRestriction i' w)
        (Z'.connectedComponentOpens w).ι
        (componentNeighbourhood i' w).ι
        (isPullback_componentRestriction i' w)).baseChange
          (componentRestriction i' w) (baseChangeComponentImmersion i i' g f sq w) (𝟙 _)
          (X'.homOfLE (baseChangeComponentOpen_le i i' g f w))
          (isPullback_baseChangeComponentImmersion_homOfLE i i' g f sq w)).bundle)
      (componentRank (𝒩.baseChange i i' g f sq).bundle w) :=
    isFiniteLocallyFreeOfRank_modulePullback _ _ _
      (isFiniteLocallyFreeOfRank_componentRank (𝒩.baseChange i i' g f sq).bundle w)
  have := isFiniteLocallyFreeOfRank_baseChange_paste_vert i'
    (componentRestriction i' w) _ _
    (isPullback_componentRestriction i' w) _ _ _
    (isPullback_baseChangeComponentImmersion_homOfLE i i' g f sq w)
    (𝒩.baseChange i i' g f sq) (componentRank (𝒩.baseChange i i' g f sq).bundle w)
  have h₁ := isFiniteLocallyFreeOfRank_baseChange_paste_vert i i' _ _
    (sq) _ _ _
    ((isPullback_baseChangeComponentImmersion_homOfLE i i' g f sq w).paste_vert
      (isPullback_componentRestriction i' w)) 𝒩
    (componentRank (𝒩.baseChange i i' g f sq).bundle w)
  have : SheafOfModules.IsFiniteLocallyFreeOfRank.{u, u, u}
      (((𝒩.baseChange i (componentRestriction i (componentBelow g w))
        (Z.connectedComponentOpens (componentBelow g w)).ι
        (componentNeighbourhood i (componentBelow g w)).ι
        (isPullback_componentRestriction i (componentBelow g w))).baseChange
        (componentRestriction i (componentBelow g w)) (baseChangeComponentImmersion i i' g f sq w)
        (g.resConnectedComponent w) (baseChangeComponentMap i i' g f w)
        (isPullback_baseChangeComponentMap i i' g f sq w)).bundle)
      (componentRank 𝒩.bundle (componentBelow g w)) :=
    isFiniteLocallyFreeOfRank_modulePullback _ _ _
      (isFiniteLocallyFreeOfRank_componentRank 𝒩.bundle (componentBelow g w))
  have h₂ := isFiniteLocallyFreeOfRank_baseChange_paste_vert i
    (componentRestriction i (componentBelow g w)) _ _
    (isPullback_componentRestriction i (componentBelow g w)) _ _ _
    (isPullback_baseChangeComponentMap i i' g f sq w) 𝒩
    (componentRank 𝒩.bundle (componentBelow g w))
  rw [baseChange_paste_baseChangeComponent] at h₁
  obtain ⟨x, hx⟩ := _root_.ConnectedComponents.surjective_coe w
  exact Scheme.Modules.isFiniteLocallyFreeOfRank_unique _ h₁ h₂
    ⟨x, (Scheme.mem_connectedComponentOpens Z').2 hx⟩

omit [LocallyOfFiniteType f] in
/-- `(g^*𝒩)|_{Z'_w}` has the rank of `𝒩` on the component `Z_a` below `Z'_w`. -/
theorem isFiniteLocallyFreeOfRank_toComponent_baseChange :
    SheafOfModules.IsFiniteLocallyFreeOfRank.{u, u, u}
      ((𝒩.baseChange i i' g f sq).toComponent i' w).bundle
      (componentRank 𝒩.bundle (componentBelow g w)) := by
  rw [← componentRank_baseChange i i' g f sq 𝒩 w]
  exact isFiniteLocallyFreeOfRank_componentRank _ w

/-- **The two classes on `Z'_w ⟶ V_w`.** The base change to `Z'_w ⟶ V_w` of `(g^*𝒩)|_{Z'_w}` and
that of `𝒩|_{Z_a}` have the same class (Stacks 0FBK at constant rank): both bundles are
identified with the base change of `𝒩` along the pasted square over `Z ⟶ X`, compatibly with the
surjections onto the conormal sheaf
(`Stacks.Chow.virtualNormalGysinClass_baseChange_baseChange_eq_paste_vert`). -/
theorem virtualNormalGysinClass_baseChangeComponent (sW : _ ⟶ C.S) [LocallyOfFiniteType sW]
    (hiV : baseChangeComponentImmersion i i' g f sq w ≫ (baseChangeComponentMap i i' g f w ≫
      ((componentNeighbourhood i (componentBelow g w)).ι ≫ sX)) = sW) :
    haveI := isFiniteLocallyFreeOfRank_toComponent_baseChange i i' g f sq 𝒩 w
    haveI : SheafOfModules.IsFiniteLocallyFreeOfRank.{u, u, u}
        (((𝒩.baseChange i i' g f sq).toComponent i' w).baseChange
          (componentRestriction i' w) (baseChangeComponentImmersion i i' g f sq w) (𝟙 _)
          (X'.homOfLE (baseChangeComponentOpen_le i i' g f w))
          (isPullback_baseChangeComponentImmersion_homOfLE i i' g f sq w)).bundle
        (componentRank 𝒩.bundle (componentBelow g w)) :=
      isFiniteLocallyFreeOfRank_modulePullback _ _ _ inferInstance
    haveI : SheafOfModules.IsFiniteLocallyFreeOfRank.{u, u, u}
        ((𝒩.toComponent i (componentBelow g w)).baseChange
          (componentRestriction i (componentBelow g w)) (baseChangeComponentImmersion i i' g f sq w)
          (g.resConnectedComponent w) (baseChangeComponentMap i i' g f w)
          (isPullback_baseChangeComponentMap i i' g f sq w)).bundle
        (componentRank 𝒩.bundle (componentBelow g w)) :=
      isFiniteLocallyFreeOfRank_modulePullback _ _ _ inferInstance
    virtualNormalBundleClass C sW (baseChangeComponentMap i i' g f w ≫
        ((componentNeighbourhood i (componentBelow g w)).ι ≫ sX))
        (baseChangeComponentImmersion i i' g f sq w) hiV
        (((𝒩.baseChange i i' g f sq).toComponent i' w).baseChange
          (componentRestriction i' w) (baseChangeComponentImmersion i i' g f sq w) (𝟙 _)
          (X'.homOfLE (baseChangeComponentOpen_le i i' g f w))
          (isPullback_baseChangeComponentImmersion_homOfLE i i' g f sq w))
        (componentRank 𝒩.bundle (componentBelow g w)) =
      virtualNormalBundleClass C sW (baseChangeComponentMap i i' g f w ≫
        ((componentNeighbourhood i (componentBelow g w)).ι ≫ sX))
        (baseChangeComponentImmersion i i' g f sq w) hiV
        ((𝒩.toComponent i (componentBelow g w)).baseChange
          (componentRestriction i (componentBelow g w)) (baseChangeComponentImmersion i i' g f sq w)
          (g.resConnectedComponent w) (baseChangeComponentMap i i' g f w)
          (isPullback_baseChangeComponentMap i i' g f sq w))
        (componentRank 𝒩.bundle (componentBelow g w)) := by
  have : SheafOfModules.IsFiniteLocallyFreeOfRank.{u, u, u}
      ((((𝒩.baseChange i i' g f (sq)).baseChange
        i' (componentRestriction i' w)
        (Z'.connectedComponentOpens w).ι
        (componentNeighbourhood i' w).ι
        (isPullback_componentRestriction i' w)).baseChange
          (componentRestriction i' w) (baseChangeComponentImmersion i i' g f sq w) (𝟙 _)
          (X'.homOfLE (baseChangeComponentOpen_le i i' g f w))
          (isPullback_baseChangeComponentImmersion_homOfLE i i' g f sq w)).bundle)
      (componentRank 𝒩.bundle (componentBelow g w)) :=
    isFiniteLocallyFreeOfRank_modulePullback _ _ _
      (isFiniteLocallyFreeOfRank_toComponent_baseChange i i' g f sq 𝒩 w)
  have : SheafOfModules.IsFiniteLocallyFreeOfRank.{u, u, u}
      (((𝒩.baseChange i (componentRestriction i (componentBelow g w))
        (Z.connectedComponentOpens (componentBelow g w)).ι
        (componentNeighbourhood i (componentBelow g w)).ι
        (isPullback_componentRestriction i (componentBelow g w))).baseChange
        (componentRestriction i (componentBelow g w)) (baseChangeComponentImmersion i i' g f sq w)
        (g.resConnectedComponent w) (baseChangeComponentMap i i' g f w)
        (isPullback_baseChangeComponentMap i i' g f sq w)).bundle)
      (componentRank 𝒩.bundle (componentBelow g w)) :=
    isFiniteLocallyFreeOfRank_modulePullback _ _ _
      (isFiniteLocallyFreeOfRank_componentRank 𝒩.bundle (componentBelow g w))
  have := isFiniteLocallyFreeOfRank_baseChange_paste_vert i'
    (componentRestriction i' w) _ _
    (isPullback_componentRestriction i' w) _ _ _
    (isPullback_baseChangeComponentImmersion_homOfLE i i' g f sq w)
    (𝒩.baseChange i i' g f sq) (componentRank 𝒩.bundle (componentBelow g w))
  have := isFiniteLocallyFreeOfRank_baseChange_paste_vert i i' _ _
    (sq) _ _ _
    ((isPullback_baseChangeComponentImmersion_homOfLE i i' g f sq w).paste_vert
      (isPullback_componentRestriction i' w)) 𝒩
    (componentRank 𝒩.bundle (componentBelow g w))
  have := isFiniteLocallyFreeOfRank_baseChange_paste_vert i
    (componentRestriction i (componentBelow g w)) _ _
    (isPullback_componentRestriction i (componentBelow g w)) _ _ _
    (isPullback_baseChangeComponentMap i i' g f sq w) 𝒩
    (componentRank 𝒩.bundle (componentBelow g w))
  exact (virtualNormalGysinClass_baseChange_baseChange_eq_paste_vert i'
    (componentRestriction i' w) _ _
    (isPullback_componentRestriction i' w) _ _ _
    (isPullback_baseChangeComponentImmersion_homOfLE i i' g f sq w)
    (𝒩.baseChange i i' g f sq) C sW _ hiV _).trans
    ((virtualNormalGysinClass_baseChange_baseChange_eq_paste_vert i i' _ _
    (sq) _ _ _
    ((isPullback_baseChangeComponentImmersion_homOfLE i i' g f sq w).paste_vert
      (isPullback_componentRestriction i' w)) 𝒩 C sW _ hiV _).trans
    ((virtualNormalGysinClass_congr_bundle C sW _ _ hiV
      (baseChange_paste_baseChangeComponent i i' g f sq 𝒩 w) _).trans
    (virtualNormalGysinClass_baseChange_baseChange_eq_paste_vert i
    (componentRestriction i (componentBelow g w)) _ _
    (isPullback_componentRestriction i (componentBelow g w)) _ _ _
    (isPullback_baseChangeComponentMap i i' g f sq w) 𝒩 C sW _ hiV _).symm))

end ComponentClass


/-- Two composites of restrictions along open immersions with equal composites agree. -/
theorem chowGroupRestrict_comp_eq_comp (C : ChowSituation.{u}) {A B B' D : Scheme.{u}}
    {sA : A ⟶ C.S} [LocallyOfFiniteType sA] {sB : B ⟶ C.S} [LocallyOfFiniteType sB]
    {sB' : B' ⟶ C.S} [LocallyOfFiniteType sB'] {sD : D ⟶ C.S} [LocallyOfFiniteType sD]
    (u : B ⟶ A) [IsOpenImmersion u] (hu : u ≫ sA = sB) (v : D ⟶ B) [IsOpenImmersion v]
    (hv : v ≫ sB = sD) (u' : B' ⟶ A) [IsOpenImmersion u'] (hu' : u' ≫ sA = sB')
    (v' : D ⟶ B') [IsOpenImmersion v'] (hv' : v' ≫ sB' = sD) (h : v ≫ u = v' ≫ u') {k : ℤ}
    (x : chowGroup C sA k) :
    chowGroupRestrict C sB sD v hv k (chowGroupRestrict C sA sB u hu k x) =
      chowGroupRestrict C sB' sD v' hv' k (chowGroupRestrict C sA sB' u' hu' k x) := by
  rw [chowGroupRestrict_comp, chowGroupRestrict_comp]
  exact DFunLike.congr_fun (chowGroupRestrict_congr C _ _ _ _ _ _ h _) x

/-- Pushforward along an isomorphism over the base is restriction along its inverse. -/
theorem chowPushforwardOfIso_hom_eq_chowGroupRestrict_inv (C : ChowSituation.{u})
    {A B : Scheme.{u}} (sA : A ⟶ C.S) [LocallyOfFiniteType sA] (sB : B ⟶ C.S)
    [LocallyOfFiniteType sB] (e : A ≅ B) (he : e.hom ≫ sB = sA) (he' : e.inv ≫ sA = sB) {k : ℤ}
    (x : chowGroup C sA k) :
    chowPushforwardOfIso C sA sB e.hom he k x = chowGroupRestrict C sA sB e.inv he' k x :=
  (chowGroupRestrict_eq_chowPushforwardOfIso_inv C sA sB e.symm he' k x).symm

/-- The cap operation of a class of Stacks 0FBK at constant rank does not depend on how the
structure morphism of the target is written. -/
theorem virtualNormalGysinClass_cap_congr (C : ChowSituation.{u}) {Z₀ X₀ T : Scheme.{u}}
    (sZ₀ : Z₀ ⟶ C.S) [LocallyOfFiniteType sZ₀] (sX₀ sX₀' : X₀ ⟶ C.S) [LocallyOfFiniteType sX₀]
    [LocallyOfFiniteType sX₀'] (h : sX₀ = sX₀') (i₀ : Z₀ ⟶ X₀) [IsClosedImmersion i₀]
    (hi₀ : i₀ ≫ sX₀ = sZ₀) (hi₀' : i₀ ≫ sX₀' = sZ₀) (N : VirtualNormalBundle i₀) (r : ℕ)
    [SheafOfModules.IsFiniteLocallyFreeOfRank.{u, u, u} N.bundle r] (t : T ⟶ X₀)
    [LocallyOfFiniteType t] (k : ℤ) (a : chowGroup C (t ≫ sX₀) k)
    (a' : chowGroup C (t ≫ sX₀') k) (ha : a ≍ a') :
    (virtualNormalBundleClass C sZ₀ sX₀ i₀ hi₀ N r).cap t k a =
      (virtualNormalBundleClass C sZ₀ sX₀' i₀ hi₀' N r).cap t k a' := by
  subst h
  cases ha
  rfl

section PieceComparison

variable (C : ChowSituation.{u}) {Z X Z' X' : Scheme.{u}} (sZ : Z ⟶ C.S)
  [LocallyOfFiniteType sZ] (sX : X ⟶ C.S) [LocallyOfFiniteType sX] (i : Z ⟶ X)
  [IsClosedImmersion i] (hi : i ≫ sX = sZ) (i' : Z' ⟶ X') [IsClosedImmersion i'] (g : Z' ⟶ Z)
  (f : X' ⟶ X) [LocallyOfFiniteType f] (sq : IsPullback i' g f i) (𝒩 : VirtualNormalBundle i)
  (sZ' : Z' ⟶ C.S) [LocallyOfFiniteType sZ'] (hi' : i' ≫ (f ≫ sX) = sZ')
  [IsLocallyNoetherian Z] [IsLocallyNoetherian X] [IsLocallyNoetherian X']
  [IsLocallyNoetherian Z'] (w : _root_.ConnectedComponents Z')
  {T : Scheme.{u}} (t : T ⟶ X') [LocallyOfFiniteType t]

/-- The comparison `Z' ×_{X'} T ⟶ Z ×_X T`. -/
def basePieceIso : pullback i' t ⟶ pullback i (t ≫ f) :=
  (IsPullback.of_hasPullback i' t).flip.flip.isoPullback.hom ≫
    (subschemeTestBaseChangeIso i i' g f sq t).inv ≫
      (IsPullback.of_hasPullback i (t ≫ f)).flip.flip.isoPullback.inv

/-- The identification `Z' ×_{X'} T ≅ Z ×_X T` is an isomorphism. -/
instance isIso_basePieceIso : IsIso (basePieceIso i i' g f sq t) := by
  rw [basePieceIso]
  infer_instance

omit [LocallyOfFiniteType f] [IsLocallyNoetherian Z] [IsLocallyNoetherian X]
  [IsLocallyNoetherian X'] [IsLocallyNoetherian Z'] [LocallyOfFiniteType t] in
/-- The identification `Z' ×_{X'} T ≅ Z ×_X T` over `Z`. -/
@[reassoc]
theorem basePieceIso_fst :
    basePieceIso i i' g f sq t ≫ pullback.fst i (t ≫ f) =
      pullback.fst i' t ≫ g := by
  rw [basePieceIso, Category.assoc, Category.assoc, IsPullback.isoPullback_inv_fst,
    ← subschemeTestBaseChangeIso_hom_fst i i' g f sq t, Iso.inv_hom_id_assoc,
    IsPullback.isoPullback_hom_fst_assoc]

omit [LocallyOfFiniteType f] [LocallyOfFiniteType t] in
/-- The piece of `Z' ×_{X'} T` over `Z'_w` lies over the piece of `Z ×_X T` over the component
`Z_a` below it. -/
theorem pieceOpen_le_preimage_basePieceIso :
    pullback.snd i' t ⁻¹ᵁ (t ⁻¹ᵁ componentNeighbourhood i' w) ≤
      basePieceIso i i' g f sq t ⁻¹ᵁ (pullback.snd i (t ≫ f) ⁻¹ᵁ ((t ≫ f) ⁻¹ᵁ
        componentNeighbourhood i (componentBelow g w))) := by
  rw [preimage_preimage_componentNeighbourhood (IsPullback.of_hasPullback i' t).flip
      w, preimage_preimage_componentNeighbourhood (IsPullback.of_hasPullback i (t ≫ f)).flip
      (componentBelow g w), ← Scheme.Hom.comp_preimage, basePieceIso_fst,
    Scheme.Hom.comp_preimage]
  exact Scheme.Hom.preimage_mono _ (g.connectedComponentOpens_le_preimage w)

/-- The inclusion of the piece of `Z' ×_{X'} T` over `Z'_w` into the piece of `Z ×_X T` over
`Z_a`. -/
def basePieceMap :
    ((pullback.snd i' t ⁻¹ᵁ (t ⁻¹ᵁ componentNeighbourhood i' w) :
      (pullback i' t).Opens) : Scheme.{u}) ⟶
    ((pullback.snd i (t ≫ f) ⁻¹ᵁ ((t ≫ f) ⁻¹ᵁ
        componentNeighbourhood i (componentBelow g w)) : (pullback i (t ≫ f)).Opens) :
      Scheme.{u}) :=
  (basePieceIso i i' g f sq t).resLE _ _ (pieceOpen_le_preimage_basePieceIso i i' g f sq w t)

/-- The inclusion of the piece over `Z'_w` into the piece over `Z_a` is an open immersion. -/
instance isOpenImmersion_basePieceMap : IsOpenImmersion (basePieceMap i i' g f sq w t) := by
  have : IsOpenImmersion (basePieceMap i i' g f sq w t ≫ (pullback.snd i (t ≫ f) ⁻¹ᵁ ((t ≫ f) ⁻¹ᵁ
      componentNeighbourhood i (componentBelow g w))).ι) := by
    rw [basePieceMap, Scheme.Hom.resLE_comp_ι]; infer_instance
  exact IsOpenImmersion.of_comp _ (pullback.snd i (t ≫ f) ⁻¹ᵁ ((t ≫ f) ⁻¹ᵁ
      componentNeighbourhood i (componentBelow g w))).ι

omit [LocallyOfFiniteType f] [LocallyOfFiniteType t] in
/-- The inclusion of the piece over `Z'_w` into the piece over `Z_a`, followed by the inclusion of
the latter, is the inclusion of the former followed by `Z' ×_{X'} T ≅ Z ×_X T`. -/
theorem basePieceMap_comp :
    basePieceMap i i' g f sq w t ≫ ((pullback.snd i (t ≫ f) ⁻¹ᵁ ((t ≫ f) ⁻¹ᵁ
        componentNeighbourhood i (componentBelow g w))).ι ≫
        (IsPullback.of_hasPullback i (t ≫ f)).flip.flip.isoPullback.hom) =
      ((pullback.snd i' t ⁻¹ᵁ
        (t ⁻¹ᵁ componentNeighbourhood i' w)).ι ≫
        (IsPullback.of_hasPullback i' t).flip.flip.isoPullback.hom) ≫
        (subschemeTestBaseChangeIso i i' g f sq t).inv := by
  rw [basePieceMap, Scheme.Hom.resLE_comp_ι_assoc, basePieceIso]
  simp only [Category.assoc, Iso.inv_hom_id, Category.comp_id]

omit [LocallyOfFiniteType f] [IsLocallyNoetherian Z] [IsLocallyNoetherian X]
  [IsLocallyNoetherian X'] [IsLocallyNoetherian Z'] [LocallyOfFiniteType t] in
/-- The identification `Z' ×_{X'} T ≅ Z ×_X T` over `T`. -/
@[reassoc]
theorem basePieceIso_snd :
    basePieceIso i i' g f sq t ≫ pullback.snd i (t ≫ f) = pullback.snd i' t := by
  rw [basePieceIso, Category.assoc, Category.assoc, IsPullback.isoPullback_inv_snd,
    ← subschemeTestBaseChangeIso_hom_snd i i' g f sq t, Iso.inv_hom_id_assoc,
    IsPullback.isoPullback_hom_snd]

omit [LocallyOfFiniteType f] [LocallyOfFiniteType t] in
include sq in
/-- The piece of `Z' ×_{X'} T` over `Z'_w` lies over `t⁻¹(V_w)`. -/
theorem pieceOpen_le_preimage_testOpen :
    pullback.snd i' t ⁻¹ᵁ (t ⁻¹ᵁ componentNeighbourhood i' w) ≤
      pullback.snd i' t ⁻¹ᵁ (t ⁻¹ᵁ baseChangeComponentOpen i i' g f w) := by
  rw [preimage_preimage_componentNeighbourhood (IsPullback.of_hasPullback i' t).flip
      w, ← Scheme.Hom.comp_preimage, ← pullback.condition, Scheme.Hom.comp_preimage]
  exact Scheme.Hom.preimage_mono _
    (connectedComponentOpens_le_preimage_baseChangeComponentOpen i i' g f sq w)

omit [LocallyOfFiniteType f] [LocallyOfFiniteType t] in
/-- `t⁻¹(V_w) ⊆ t⁻¹(U'_w)`. -/
theorem testOpen_le_componentNeighbourhood :
    t ⁻¹ᵁ baseChangeComponentOpen i i' g f w ≤ t ⁻¹ᵁ componentNeighbourhood i' w :=
  Scheme.Hom.preimage_mono _ (baseChangeComponentOpen_le i i' g f w)

omit [LocallyOfFiniteType f] [LocallyOfFiniteType t] in
/-- `t⁻¹(V_w) ⊆ (t ≫ f)⁻¹(U_a)`. -/
theorem testOpen_le_componentNeighbourhood_base :
    t ⁻¹ᵁ baseChangeComponentOpen i i' g f w ≤
      (t ≫ f) ⁻¹ᵁ componentNeighbourhood i (componentBelow g w) :=
  Scheme.Hom.preimage_mono _ (baseChangeComponentOpen_le_preimage i i' g f w)

omit [LocallyOfFiniteType f] [LocallyOfFiniteType t] in
/-- The restriction of `t` to `t⁻¹(V_w)`, read in `U'_w`. -/
theorem testOpen_homOfLE_morphismRestrict :
    T.homOfLE (testOpen_le_componentNeighbourhood i i' g f w t) ≫
        t ∣_ componentNeighbourhood i' w =
      t ∣_ baseChangeComponentOpen i i' g f w ≫
        X'.homOfLE (baseChangeComponentOpen_le i i' g f w) := by
  rw [← cancel_mono (componentNeighbourhood i' w).ι, Category.assoc,
    morphismRestrict_ι, Scheme.homOfLE_ι_assoc, Category.assoc, Scheme.homOfLE_ι,
    morphismRestrict_ι]

omit [LocallyOfFiniteType f] [LocallyOfFiniteType t] in
/-- The restriction of `t ≫ f` to `t⁻¹(V_w)`, read in `U_a`. -/
theorem testOpen_homOfLE_morphismRestrict_base :
    T.homOfLE (testOpen_le_componentNeighbourhood_base i i' g f w t) ≫
        (t ≫ f) ∣_ componentNeighbourhood i (componentBelow g w) =
      t ∣_ baseChangeComponentOpen i i' g f w ≫ baseChangeComponentMap i i' g f w := by
  rw [← cancel_mono (componentNeighbourhood i (componentBelow g w)).ι, Category.assoc,
    morphismRestrict_ι, Scheme.homOfLE_ι_assoc, Category.assoc, baseChangeComponentMap_ι,
    morphismRestrict_ι_assoc]

/-- The map from the piece of `Z' ×_{X'} T` over `Z'_w` to `Z'_w ×_V t⁻¹(V)`. -/
def pieceTestMap :
    ((pullback.snd i' t ⁻¹ᵁ (t ⁻¹ᵁ componentNeighbourhood i' w) :
      (pullback i' t).Opens) : Scheme.{u}) ⟶
      pullback (baseChangeComponentImmersion i i' g f sq w)
        (t ∣_ baseChangeComponentOpen i i' g f w) :=
  pullback.lift (pieceProjection (IsPullback.of_hasPullback i' t).flip w)
    ((pullback.snd i' t).resLE _ _ (pieceOpen_le_preimage_testOpen i i' g f sq w t)) (by
      rw [← cancel_mono (baseChangeComponentOpen i i' g f w).ι, Category.assoc, Category.assoc,
        baseChangeComponentImmersion_ι, morphismRestrict_ι, Scheme.Hom.resLE_comp_ι_assoc,
        Scheme.Hom.resLE_comp_ι_assoc, pullback.condition])

omit [LocallyOfFiniteType f] [LocallyOfFiniteType t] in
/-- The piece over `Z'_w` is carried to `Z'_w ×_{U'_w} t⁻¹(U'_w)` through
`Z'_w ×_{V_w} t⁻¹(V_w)` as by the identification of the piece with the fibre product. -/
theorem pieceTestMap_comp :
    pieceTestMap i i' g f sq w t ≫ testRestrictionMap (componentRestriction i' w)
        (baseChangeComponentImmersion i i' g f sq w) (𝟙 _)
        (X'.homOfLE (baseChangeComponentOpen_le i i' g f w))
        (isPullback_baseChangeComponentImmersion_homOfLE i i' g f sq w)
        (t ∣_ componentNeighbourhood i' w)
        (T.homOfLE (testOpen_le_componentNeighbourhood i i' g f w t))
        (t ∣_ baseChangeComponentOpen i i' g f w) (testOpen_homOfLE_morphismRestrict i i' g f w t) =
      (isPullback_pieceProjection (IsPullback.of_hasPullback i' t).flip
        w).flip.isoPullback.hom := by
  refine pullback.hom_ext ?_ ?_
  · rw [Category.assoc, pullback.lift_fst, IsPullback.isoPullback_hom_fst, ← Category.assoc,
      pieceTestMap, pullback.lift_fst, Category.comp_id]
  · rw [← cancel_mono (t ⁻¹ᵁ componentNeighbourhood i' w).ι]
    simp only [Category.assoc]
    rw [pullback.lift_snd_assoc, IsPullback.isoPullback_hom_snd_assoc, morphismRestrict_ι]
    simp only [Category.assoc]
    rw [pieceTestMap, pullback.lift_snd_assoc, Scheme.homOfLE_ι, Scheme.Hom.resLE_comp_ι]

/-- The map from the piece over `Z'_w` to `Z'_w ×_{V_w} t⁻¹(V_w)` is an open immersion. -/
instance isOpenImmersion_pieceTestMap : IsOpenImmersion (pieceTestMap i i' g f sq w t) := by
  have := isOpenImmersion_testRestrictionMap (componentRestriction i' w)
    (baseChangeComponentImmersion i i' g f sq w) (𝟙 _)
    (X'.homOfLE (baseChangeComponentOpen_le i i' g f w))
    (isPullback_baseChangeComponentImmersion_homOfLE i i' g f sq w)
    (t ∣_ componentNeighbourhood i' w)
    (T.homOfLE (testOpen_le_componentNeighbourhood i i' g f w t))
    (t ∣_ baseChangeComponentOpen i i' g f w) (testOpen_homOfLE_morphismRestrict i i' g f w t)
  have : IsOpenImmersion (pieceTestMap i i' g f sq w t ≫ testRestrictionMap
      (componentRestriction i' w)
      (baseChangeComponentImmersion i i' g f sq w) (𝟙 _)
    (X'.homOfLE (baseChangeComponentOpen_le i i' g f w))
      (isPullback_baseChangeComponentImmersion_homOfLE i i' g f sq w)
      (t ∣_ componentNeighbourhood i' w)
      (T.homOfLE (testOpen_le_componentNeighbourhood i i' g f w t))
      (t ∣_ baseChangeComponentOpen i i' g f w)
      (testOpen_homOfLE_morphismRestrict i i' g f w t)) := by
    rw [pieceTestMap_comp]; infer_instance
  exact IsOpenImmersion.of_comp _ (testRestrictionMap (componentRestriction i' w)
    (baseChangeComponentImmersion i i' g f sq w) (𝟙 _)
    (X'.homOfLE (baseChangeComponentOpen_le i i' g f w))
    (isPullback_baseChangeComponentImmersion_homOfLE i i' g f sq w)
    (t ∣_ componentNeighbourhood i' w)
    (T.homOfLE (testOpen_le_componentNeighbourhood i i' g f w t))
    (t ∣_ baseChangeComponentOpen i i' g f w) (testOpen_homOfLE_morphismRestrict i i' g f w t))

omit [LocallyOfFiniteType f] [LocallyOfFiniteType t] in
/-- The piece over `Z'_w` is carried to `Z_a ×_{U_a} (t ≫ f)⁻¹(U_a)` through
`Z'_w ×_{V_w} t⁻¹(V_w)` as through the piece of `Z ×_X T` over `Z_a`. -/
theorem pieceTestMap_comp_base :
    pieceTestMap i i' g f sq w t ≫ testRestrictionMap (componentRestriction i (componentBelow g w))
        (baseChangeComponentImmersion i i' g f sq w) (g.resConnectedComponent w)
        (baseChangeComponentMap i i' g f w) (isPullback_baseChangeComponentMap i i' g f sq w)
        ((t ≫ f) ∣_ componentNeighbourhood i (componentBelow g w))
        (T.homOfLE (testOpen_le_componentNeighbourhood_base i i' g f w t))
        (t ∣_ baseChangeComponentOpen i i' g f w)
        (testOpen_homOfLE_morphismRestrict_base i i' g f w t) =
      basePieceMap i i' g f sq w t ≫
        (isPullback_pieceProjection (IsPullback.of_hasPullback i (t ≫ f)).flip
        (componentBelow g w)).flip.isoPullback.hom := by
  refine pullback.hom_ext ?_ ?_
  · rw [← cancel_mono (Z.connectedComponentOpens (componentBelow g w)).ι]
    simp only [Category.assoc]
    rw [pullback.lift_fst_assoc, IsPullback.isoPullback_hom_fst_assoc]
    simp only [Category.assoc]
    rw [Scheme.Hom.resConnectedComponent_comp_ι, Scheme.Hom.resLE_comp_ι, basePieceMap,
      Scheme.Hom.resLE_comp_ι_assoc, basePieceIso_fst, pieceTestMap, pullback.lift_fst_assoc,
      Scheme.Hom.resLE_comp_ι_assoc]
  · rw [← cancel_mono ((t ≫ f) ⁻¹ᵁ componentNeighbourhood i (componentBelow g w)).ι]
    simp only [Category.assoc]
    rw [pullback.lift_snd_assoc, IsPullback.isoPullback_hom_snd_assoc]
    simp only [Category.assoc]
    rw [Scheme.homOfLE_ι, morphismRestrict_ι, basePieceMap, Scheme.Hom.resLE_comp_ι_assoc,
      basePieceIso_snd, pieceTestMap, pullback.lift_snd_assoc, Scheme.Hom.resLE_comp_ι]

omit [LocallyOfFiniteType sZ] [LocallyOfFiniteType sX] [LocallyOfFiniteType f]
  [LocallyOfFiniteType sZ'] [IsLocallyNoetherian Z] [IsLocallyNoetherian X] [IsLocallyNoetherian X']
  [IsLocallyNoetherian Z'] [LocallyOfFiniteType t] in
include hi hi' in
/-- The identification `Z ×_X T ≅ Z' ×_{X'} T` is one over the base, for the structure morphism
`s_{Z'}` of `Z'`. -/
theorem subschemeTestBaseChangeIso_hom_comp_structureMorphism :
    (subschemeTestBaseChangeIso i i' g f sq t).hom ≫ (pullback.fst i' t ≫ sZ') =
      pullback.fst i (t ≫ f) ≫ sZ := by
  rw [← hi', ← hi]
  exact subschemeTestBaseChangeIso_hom_comp_structure i i' g f sq t sX

/-- Restricting a pushed-forward class to the piece of `Z' ×_{X'} T` over `Z'_w` is restricting
its source to the piece of `Z ×_X T` over `Z_a` below it, then to the former piece. -/
private theorem chowGroupRestrict_piece_chowPushforwardOfIso_subschemeTestBaseChangeIso {m : ℤ}
    (x : chowGroup C (pullback.fst i (t ≫ f) ≫ sZ) m) :
    chowGroupRestrict C (pullback.fst i' t ≫ sZ')
        ((pullback.snd i' t ⁻¹ᵁ (t ⁻¹ᵁ componentNeighbourhood i' w)).ι ≫
          (pullback.fst i' t ≫ sZ'))
        ((pullback.snd i' t ⁻¹ᵁ (t ⁻¹ᵁ componentNeighbourhood i' w)).ι ≫
          (IsPullback.of_hasPullback i' t).flip.flip.isoPullback.hom)
        (pieceInclusion_comp_structureMorphism C sZ' (f ≫ sX) i' hi' t _ _
          (IsPullback.of_hasPullback i' t).flip _
          (pullbackSnd_comp_structureMorphism_eq C sZ' (f ≫ sX) i' hi' t) w) m
        (chowPushforwardOfIso C (pullback.fst i (t ≫ f) ≫ sZ) (pullback.fst i' t ≫ sZ')
          (subschemeTestBaseChangeIso i i' g f sq t).hom
          (subschemeTestBaseChangeIso_hom_comp_structureMorphism C sZ sX i hi i' g f sq sZ' hi' t)
          m x) =
      chowGroupRestrict C ((pullback.snd i (t ≫ f) ⁻¹ᵁ ((t ≫ f) ⁻¹ᵁ
          componentNeighbourhood i (componentBelow g w))).ι ≫ (pullback.fst i (t ≫ f) ≫ sZ))
        ((pullback.snd i' t ⁻¹ᵁ (t ⁻¹ᵁ componentNeighbourhood i' w)).ι ≫
          (pullback.fst i' t ≫ sZ'))
        (basePieceMap i i' g f sq w t)
        (by rw [basePieceMap, Scheme.Hom.resLE_comp_ι_assoc, basePieceIso_fst_assoc, ← hi',
          ← Category.assoc i', sq.w, Category.assoc, hi]) m
        (chowGroupRestrict C (pullback.fst i (t ≫ f) ≫ sZ)
          ((pullback.snd i (t ≫ f) ⁻¹ᵁ ((t ≫ f) ⁻¹ᵁ
            componentNeighbourhood i (componentBelow g w))).ι ≫ (pullback.fst i (t ≫ f) ≫ sZ))
          ((pullback.snd i (t ≫ f) ⁻¹ᵁ ((t ≫ f) ⁻¹ᵁ
            componentNeighbourhood i (componentBelow g w))).ι ≫
            (IsPullback.of_hasPullback i (t ≫ f)).flip.flip.isoPullback.hom)
          (pieceInclusion_comp_structureMorphism C sZ sX i hi (t ≫ f) _ _
            (IsPullback.of_hasPullback i (t ≫ f)).flip _
            (pullbackSnd_comp_structureMorphism_eq C sZ sX i hi (t ≫ f)) (componentBelow g w))
          m x) := by
  rw [chowPushforwardOfIso_hom_eq_chowGroupRestrict_inv C _ _ _ _
      (by rw [← subschemeTestBaseChangeIso_hom_comp_structureMorphism C sZ sX i hi i' g f sq sZ'
        hi' t, Iso.inv_hom_id_assoc]),
    chowGroupRestrict_comp_eq_comp C (sB' := (pullback.snd i (t ≫ f) ⁻¹ᵁ ((t ≫ f) ⁻¹ᵁ
        componentNeighbourhood i (componentBelow g w))).ι ≫ (pullback.fst i (t ≫ f) ≫ sZ))
      _ _ _ _ _ (pieceInclusion_comp_structureMorphism C sZ sX i hi (t ≫ f) _ _
        (IsPullback.of_hasPullback i (t ≫ f)).flip _
        (pullbackSnd_comp_structureMorphism_eq C sZ sX i hi (t ≫ f)) (componentBelow g w))
      _ (by rw [basePieceMap, Scheme.Hom.resLE_comp_ι_assoc, basePieceIso_fst_assoc, ← hi',
        ← Category.assoc i', sq.w, Category.assoc, hi])
      (basePieceMap_comp i i' g f sq w t).symm]

/-- **The side of `Z ×_X T` vanishes on a piece in degrees other than the rank.** On the piece of
`Z' ×_{X'} T` over `Z'_w`, the degree-`n` part of `c(Z ⟶ X, 𝒩) ∩ α` read on `Z' ×_{X'} T`
vanishes unless `n` is the rank of `𝒩` on the component `Z_a` below `Z'_w`: the piece lies in
the piece of `Z ×_X T` over `Z_a`. -/
theorem chowGroupRestrict_piece_cap_baseChange_of_ne (n : ℤ)
    (hn : n ≠ componentRank 𝒩.bundle (componentBelow g w)) (k : ℤ)
    (α : chowGroup C (t ≫ (f ≫ sX)) k) :
    chowGroupRestrict C (pullback.fst i' t ≫ sZ')
        ((pullback.snd i' t ⁻¹ᵁ (t ⁻¹ᵁ componentNeighbourhood i' w)).ι ≫
          (pullback.fst i' t ≫ sZ'))
        ((pullback.snd i' t ⁻¹ᵁ (t ⁻¹ᵁ componentNeighbourhood i' w)).ι ≫
          (IsPullback.of_hasPullback i' t).flip.flip.isoPullback.hom)
        (pieceInclusion_comp_structureMorphism C sZ' (f ≫ sX) i' hi' t _ _
          (IsPullback.of_hasPullback i' t).flip _
          (pullbackSnd_comp_structureMorphism_eq C sZ' (f ≫ sX) i' hi' t) w) (k - n)
        (chowPushforwardOfIso C (pullback.fst i (t ≫ f) ≫ sZ) (pullback.fst i' t ≫ sZ')
          (subschemeTestBaseChangeIso i i' g f sq t).hom
          (subschemeTestBaseChangeIso_hom_comp_structureMorphism C sZ sX i hi i' g f sq sZ' hi' t)
          (k - n)
          ((completedBivariantSequenceOfInvertible C sZ sX i hi
            (completedVirtualNormalGysinClass C sZ sX i hi 𝒩) n).cap (t ≫ f) k
            (chowGroupCongr C (Category.assoc t f sX).symm k α))) = 0 := by
  rw [chowGroupRestrict_piece_chowPushforwardOfIso_subschemeTestBaseChangeIso C sZ sX i hi i' g f
      sq sZ' hi' w t,
    chowGroupRestrict_completedVirtualNormalGysinCap_piece_eq_zero C sZ sX i hi 𝒩 (t ≫ f) _ _
      (IsPullback.of_hasPullback i (t ≫ f)).flip _
      (pullbackSnd_comp_structureMorphism_eq C sZ sX i hi (t ≫ f)) (componentBelow g w)
      n hn k,
    map_zero]

omit [LocallyOfFiniteType sX] [LocallyOfFiniteType f] [LocallyOfFiniteType sZ'] in
include hi' in
/-- `Z'_w ⟶ V_w` is a morphism over the base, for the structure morphism of `V_w` through
`U'_w`. -/
theorem baseChangeComponentImmersion_comp_structureMorphism :
    baseChangeComponentImmersion i i' g f sq w ≫
      (X'.homOfLE (baseChangeComponentOpen_le i i' g f w) ≫
      ((componentNeighbourhood i' w).ι ≫ (f ≫ sX))) = (Z'.connectedComponentOpens w).ι ≫ sZ' := by
  rw [Scheme.homOfLE_ι_assoc, baseChangeComponentImmersion_ι_assoc, hi']

omit [LocallyOfFiniteType sX] [LocallyOfFiniteType f] [LocallyOfFiniteType sZ'] in
include hi' in
/-- `Z'_w ⟶ V_w` is a morphism over the base, for the structure morphism of `V_w` through `U_a`. -/
theorem baseChangeComponentImmersion_comp_structureMorphism_base :
    baseChangeComponentImmersion i i' g f sq w ≫ (baseChangeComponentMap i i' g f w ≫
      ((componentNeighbourhood i (componentBelow g w)).ι ≫ sX)) =
      (Z'.connectedComponentOpens w).ι ≫ sZ' := by
  rw [baseChangeComponentMap_ι_assoc, baseChangeComponentImmersion_ι_assoc, hi']

/-- **The side of `Z' ×_{X'} T` on a piece.** On the piece of `Z' ×_{X'} T` over `Z'_w`, the
degree-`r_a` part of `c(Z' ⟶ X', g^*𝒩) ∩ α` is, through `Z'_w ×_{V_w} t⁻¹(V_w)`, the cap
product with the class of the base change of `(g^*𝒩)|_{Z'_w}` to `Z'_w ⟶ V_w`. -/
theorem chowGroupRestrict_piece_completedVirtualNormalGysinClass_baseChange_cap (k : ℤ)
    (α : chowGroup C (t ≫ (f ≫ sX)) k) :
    haveI := isFiniteLocallyFreeOfRank_toComponent_baseChange i i' g f sq 𝒩 w
    haveI : SheafOfModules.IsFiniteLocallyFreeOfRank.{u, u, u}
        (((𝒩.baseChange i i' g f sq).toComponent i' w).baseChange
          (componentRestriction i' w) (baseChangeComponentImmersion i i' g f sq w) (𝟙 _)
          (X'.homOfLE (baseChangeComponentOpen_le i i' g f w))
          (isPullback_baseChangeComponentImmersion_homOfLE i i' g f sq w)).bundle
        (componentRank 𝒩.bundle (componentBelow g w)) :=
      isFiniteLocallyFreeOfRank_modulePullback _ _ _ inferInstance
    chowGroupRestrict C (pullback.fst i' t ≫ sZ')
        ((pullback.snd i' t ⁻¹ᵁ (t ⁻¹ᵁ componentNeighbourhood i' w)).ι ≫
          (pullback.fst i' t ≫ sZ'))
        ((pullback.snd i' t ⁻¹ᵁ (t ⁻¹ᵁ componentNeighbourhood i' w)).ι ≫
          (IsPullback.of_hasPullback i' t).flip.flip.isoPullback.hom)
        (pieceInclusion_comp_structureMorphism C sZ' (f ≫ sX) i' hi' t _ _
          (IsPullback.of_hasPullback i' t).flip _
          (pullbackSnd_comp_structureMorphism_eq C sZ' (f ≫ sX) i' hi' t) w)
        (k - (componentRank 𝒩.bundle (componentBelow g w) : ℕ))
        ((completedBivariantSequenceOfInvertible C sZ' (f ≫ sX) i' hi'
          (completedVirtualNormalGysinClass C sZ' (f ≫ sX) i' hi' (𝒩.baseChange i i' g f sq))
          ((componentRank 𝒩.bundle (componentBelow g w) : ℕ) : ℤ)).cap t k α) =
      chowGroupRestrict C (pullback.fst (baseChangeComponentImmersion i i' g f sq w)
          (t ∣_ baseChangeComponentOpen i i' g f w) ≫ ((Z'.connectedComponentOpens w).ι ≫ sZ'))
        ((pullback.snd i' t ⁻¹ᵁ (t ⁻¹ᵁ componentNeighbourhood i' w)).ι ≫
          (pullback.fst i' t ≫ sZ'))
        (pieceTestMap i i' g f sq w t)
        (by rw [pieceTestMap, pullback.lift_fst_assoc, Scheme.Hom.resLE_comp_ι_assoc])
        (k - (componentRank 𝒩.bundle (componentBelow g w) : ℕ))
        ((virtualNormalBundleClass C ((Z'.connectedComponentOpens w).ι ≫ sZ')
          (X'.homOfLE (baseChangeComponentOpen_le i i' g f w) ≫
            ((componentNeighbourhood i' w).ι ≫ (f ≫ sX)))
          (baseChangeComponentImmersion i i' g f sq w)
          (baseChangeComponentImmersion_comp_structureMorphism C sX i i' g f sq sZ' hi' w)
          (((𝒩.baseChange i i' g f sq).toComponent i' w).baseChange
            (componentRestriction i' w) (baseChangeComponentImmersion i i' g f sq w) (𝟙 _)
            (X'.homOfLE (baseChangeComponentOpen_le i i' g f w))
            (isPullback_baseChangeComponentImmersion_homOfLE i i' g f sq w))
          (componentRank 𝒩.bundle (componentBelow g w))).cap
          (t ∣_ baseChangeComponentOpen i i' g f w) k
          (chowGroupRestrict C ((t ∣_ componentNeighbourhood i' w) ≫
              ((componentNeighbourhood i' w).ι ≫ (f ≫ sX)))
            ((t ∣_ baseChangeComponentOpen i i' g f w) ≫
              (X'.homOfLE (baseChangeComponentOpen_le i i' g f w) ≫
                ((componentNeighbourhood i' w).ι ≫ (f ≫ sX))))
            (T.homOfLE (testOpen_le_componentNeighbourhood i i' g f w t))
            (by rw [← Category.assoc, testOpen_homOfLE_morphismRestrict, Category.assoc]) k
            (chowGroupRestrict C (t ≫ (f ≫ sX))
              ((t ∣_ componentNeighbourhood i' w) ≫ ((componentNeighbourhood i' w).ι ≫ (f ≫ sX)))
              (t ⁻¹ᵁ componentNeighbourhood i' w).ι
              (by rw [← Category.assoc (t ∣_ _), morphismRestrict_ι, Category.assoc]) k α))) := by
  have := isFiniteLocallyFreeOfRank_toComponent_baseChange i i' g f sq 𝒩 w
  rw [chowGroupRestrict_piece_completedVirtualNormalGysinClass_cap C sZ' (f ≫ sX) i' hi'
    (𝒩.baseChange i i' g f sq) t (pullback.snd i' t) (pullback.fst i' t)
    (IsPullback.of_hasPullback i' t).flip (pullback.fst i' t ≫ sZ')
    (pullbackSnd_comp_structureMorphism_eq C sZ' (f ≫ sX) i' hi' t) w _
    (componentRank_baseChange i i' g f sq 𝒩 w) k α]
  rw [← chowGroupRestrict_testRestrictionMap_virtualNormalGysinClass_cap C
    ((Z'.connectedComponentOpens w).ι ≫ sZ') ((componentNeighbourhood i' w).ι ≫ (f ≫ sX))
    (componentRestriction i' w)
    (componentRestriction_comp_structureMorphism C sZ' (f ≫ sX) i' hi' w)
    ((𝒩.baseChange i i' g f sq).toComponent i' w) _
    (baseChangeComponentImmersion i i' g f sq w) (𝟙 _)
    (X'.homOfLE (baseChangeComponentOpen_le i i' g f w))
    (isPullback_baseChangeComponentImmersion_homOfLE i i' g f sq w)
    ((Z'.connectedComponentOpens w).ι ≫ sZ')
    (baseChangeComponentImmersion_comp_structureMorphism C sX i i' g f sq sZ' hi' w)
    (t ∣_ componentNeighbourhood i' w) (T.homOfLE (testOpen_le_componentNeighbourhood i i' g f w t))
    (t ∣_ baseChangeComponentOpen i i' g f w) (testOpen_homOfLE_morphismRestrict i i' g f w t),
    chowGroupRestrict_comp]
  exact DFunLike.congr_fun (chowGroupRestrict_congr C _ _ _ _ _ _
    (pieceTestMap_comp i i' g f sq w t).symm _) _

/-- **The side of `Z ×_X T` on a piece.** On the piece of `Z' ×_{X'} T` over `Z'_w`, the
degree-`r_a` part of `c(Z ⟶ X, 𝒩) ∩ α` read on `Z' ×_{X'} T` is, through
`Z'_w ×_{V_w} t⁻¹(V_w)`, the cap product with the class of the base change of `𝒩|_{Z_a}` to
`Z'_w ⟶ V_w`. -/
theorem chowGroupRestrict_piece_cap_baseChange_eq (k : ℤ) (α : chowGroup C (t ≫ (f ≫ sX)) k) :
    haveI : SheafOfModules.IsFiniteLocallyFreeOfRank.{u, u, u}
        ((𝒩.toComponent i (componentBelow g w)).baseChange
          (componentRestriction i (componentBelow g w)) (baseChangeComponentImmersion i i' g f sq w)
          (g.resConnectedComponent w) (baseChangeComponentMap i i' g f w)
          (isPullback_baseChangeComponentMap i i' g f sq w)).bundle
        (componentRank 𝒩.bundle (componentBelow g w)) :=
      isFiniteLocallyFreeOfRank_modulePullback _ _ _ inferInstance
    chowGroupRestrict C (pullback.fst i' t ≫ sZ')
        ((pullback.snd i' t ⁻¹ᵁ (t ⁻¹ᵁ componentNeighbourhood i' w)).ι ≫
          (pullback.fst i' t ≫ sZ'))
        ((pullback.snd i' t ⁻¹ᵁ (t ⁻¹ᵁ componentNeighbourhood i' w)).ι ≫
          (IsPullback.of_hasPullback i' t).flip.flip.isoPullback.hom)
        (pieceInclusion_comp_structureMorphism C sZ' (f ≫ sX) i' hi' t _ _
          (IsPullback.of_hasPullback i' t).flip _
          (pullbackSnd_comp_structureMorphism_eq C sZ' (f ≫ sX) i' hi' t) w)
        (k - (componentRank 𝒩.bundle (componentBelow g w) : ℕ))
        (chowPushforwardOfIso C (pullback.fst i (t ≫ f) ≫ sZ) (pullback.fst i' t ≫ sZ')
          (subschemeTestBaseChangeIso i i' g f sq t).hom
          (subschemeTestBaseChangeIso_hom_comp_structureMorphism C sZ sX i hi i' g f sq sZ' hi' t)
          (k - (componentRank 𝒩.bundle (componentBelow g w) : ℕ))
          ((completedBivariantSequenceOfInvertible C sZ sX i hi
            (completedVirtualNormalGysinClass C sZ sX i hi 𝒩)
            ((componentRank 𝒩.bundle (componentBelow g w) : ℕ) : ℤ)).cap (t ≫ f) k
            (chowGroupCongr C (Category.assoc t f sX).symm k α))) =
      chowGroupRestrict C (pullback.fst (baseChangeComponentImmersion i i' g f sq w)
          (t ∣_ baseChangeComponentOpen i i' g f w) ≫ ((Z'.connectedComponentOpens w).ι ≫ sZ'))
        ((pullback.snd i' t ⁻¹ᵁ (t ⁻¹ᵁ componentNeighbourhood i' w)).ι ≫
          (pullback.fst i' t ≫ sZ'))
        (pieceTestMap i i' g f sq w t)
        (by rw [pieceTestMap, pullback.lift_fst_assoc, Scheme.Hom.resLE_comp_ι_assoc])
        (k - (componentRank 𝒩.bundle (componentBelow g w) : ℕ))
        ((virtualNormalBundleClass C ((Z'.connectedComponentOpens w).ι ≫ sZ')
          (baseChangeComponentMap i i' g f w ≫
            ((componentNeighbourhood i (componentBelow g w)).ι ≫ sX))
          (baseChangeComponentImmersion i i' g f sq w)
          (baseChangeComponentImmersion_comp_structureMorphism_base C sX i i' g f sq sZ' hi' w)
          ((𝒩.toComponent i (componentBelow g w)).baseChange
            (componentRestriction i (componentBelow g w))
            (baseChangeComponentImmersion i i' g f sq w)
            (g.resConnectedComponent w) (baseChangeComponentMap i i' g f w)
            (isPullback_baseChangeComponentMap i i' g f sq w))
          (componentRank 𝒩.bundle (componentBelow g w))).cap
          (t ∣_ baseChangeComponentOpen i i' g f w) k
          (chowGroupRestrict C (((t ≫ f) ∣_ componentNeighbourhood i (componentBelow g w)) ≫
              ((componentNeighbourhood i (componentBelow g w)).ι ≫ sX))
            ((t ∣_ baseChangeComponentOpen i i' g f w) ≫ (baseChangeComponentMap i i' g f w ≫
              ((componentNeighbourhood i (componentBelow g w)).ι ≫ sX)))
            (T.homOfLE (testOpen_le_componentNeighbourhood_base i i' g f w t))
            (by rw [← Category.assoc, testOpen_homOfLE_morphismRestrict_base, Category.assoc]) k
            (chowGroupRestrict C ((t ≫ f) ≫ sX)
              (((t ≫ f) ∣_ componentNeighbourhood i (componentBelow g w)) ≫
                ((componentNeighbourhood i (componentBelow g w)).ι ≫ sX))
              ((t ≫ f) ⁻¹ᵁ componentNeighbourhood i (componentBelow g w)).ι
              (by
                rw [← Category.assoc ((t ≫ f) ∣_ _), morphismRestrict_ι]
                simp only [Category.assoc])
              k (chowGroupCongr C (Category.assoc t f sX).symm k α)))) := by
  rw [chowGroupRestrict_piece_chowPushforwardOfIso_subschemeTestBaseChangeIso C sZ sX i hi i' g f
      sq sZ' hi' w t,
    chowGroupRestrict_piece_completedVirtualNormalGysinClass_cap C sZ sX i hi 𝒩 (t ≫ f)
      (pullback.snd i (t ≫ f)) (pullback.fst i (t ≫ f)) (IsPullback.of_hasPullback i (t ≫ f)).flip
      (pullback.fst i (t ≫ f) ≫ sZ) (pullbackSnd_comp_structureMorphism_eq C sZ sX i hi (t ≫ f))
      (componentBelow g w) _ rfl k,
    ← chowGroupRestrict_testRestrictionMap_virtualNormalGysinClass_cap C
      ((Z.connectedComponentOpens (componentBelow g w)).ι ≫ sZ)
      ((componentNeighbourhood i (componentBelow g w)).ι ≫ sX)
      (componentRestriction i (componentBelow g w))
      (componentRestriction_comp_structureMorphism C sZ sX i hi (componentBelow g w))
      (𝒩.toComponent i (componentBelow g w)) _
      (baseChangeComponentImmersion i i' g f sq w) (g.resConnectedComponent w)
      (baseChangeComponentMap i i' g f w) (isPullback_baseChangeComponentMap i i' g f sq w)
      ((Z'.connectedComponentOpens w).ι ≫ sZ')
      (baseChangeComponentImmersion_comp_structureMorphism_base C sX i i' g f sq sZ' hi' w)
      ((t ≫ f) ∣_ componentNeighbourhood i (componentBelow g w))
      (T.homOfLE (testOpen_le_componentNeighbourhood_base i i' g f w t))
      (t ∣_ baseChangeComponentOpen i i' g f w)
      (testOpen_homOfLE_morphismRestrict_base i i' g f w t)]
  · have := isOpenImmersion_testRestrictionMap (componentRestriction i (componentBelow g w))
      (baseChangeComponentImmersion i i' g f sq w) (g.resConnectedComponent w)
      (baseChangeComponentMap i i' g f w) (isPullback_baseChangeComponentMap i i' g f sq w)
      ((t ≫ f) ∣_ componentNeighbourhood i (componentBelow g w))
      (T.homOfLE (testOpen_le_componentNeighbourhood_base i i' g f w t))
      (t ∣_ baseChangeComponentOpen i i' g f w)
      (testOpen_homOfLE_morphismRestrict_base i i' g f w t)
    exact chowGroupRestrict_comp_eq_comp C _ _ _ _ _ _ _ _
      (pieceTestMap_comp_base i i' g f sq w t).symm _

/-- The two cap products on `Z'_w ×_{V_w} t⁻¹(V_w)` agree: the classes agree
(`Stacks.Chow.virtualNormalGysinClass_baseChangeComponent`), and so do the restrictions of `α`. -/
theorem baseChangeComponent_cap_eq (k : ℤ) (α : chowGroup C (t ≫ (f ≫ sX)) k) :
    haveI := isFiniteLocallyFreeOfRank_toComponent_baseChange i i' g f sq 𝒩 w
    haveI : SheafOfModules.IsFiniteLocallyFreeOfRank.{u, u, u}
        (((𝒩.baseChange i i' g f sq).toComponent i' w).baseChange
          (componentRestriction i' w) (baseChangeComponentImmersion i i' g f sq w) (𝟙 _)
          (X'.homOfLE (baseChangeComponentOpen_le i i' g f w))
          (isPullback_baseChangeComponentImmersion_homOfLE i i' g f sq w)).bundle
        (componentRank 𝒩.bundle (componentBelow g w)) :=
      isFiniteLocallyFreeOfRank_modulePullback _ _ _ inferInstance
    haveI : SheafOfModules.IsFiniteLocallyFreeOfRank.{u, u, u}
        ((𝒩.toComponent i (componentBelow g w)).baseChange
          (componentRestriction i (componentBelow g w)) (baseChangeComponentImmersion i i' g f sq w)
          (g.resConnectedComponent w) (baseChangeComponentMap i i' g f w)
          (isPullback_baseChangeComponentMap i i' g f sq w)).bundle
        (componentRank 𝒩.bundle (componentBelow g w)) :=
      isFiniteLocallyFreeOfRank_modulePullback _ _ _ inferInstance
    (virtualNormalBundleClass C ((Z'.connectedComponentOpens w).ι ≫ sZ')
          (X'.homOfLE (baseChangeComponentOpen_le i i' g f w) ≫
            ((componentNeighbourhood i' w).ι ≫ (f ≫ sX)))
          (baseChangeComponentImmersion i i' g f sq w)
          (baseChangeComponentImmersion_comp_structureMorphism C sX i i' g f sq sZ' hi' w)
          (((𝒩.baseChange i i' g f sq).toComponent i' w).baseChange
            (componentRestriction i' w) (baseChangeComponentImmersion i i' g f sq w) (𝟙 _)
            (X'.homOfLE (baseChangeComponentOpen_le i i' g f w))
            (isPullback_baseChangeComponentImmersion_homOfLE i i' g f sq w))
          (componentRank 𝒩.bundle (componentBelow g w))).cap
          (t ∣_ baseChangeComponentOpen i i' g f w) k
          (chowGroupRestrict C ((t ∣_ componentNeighbourhood i' w) ≫
              ((componentNeighbourhood i' w).ι ≫ (f ≫ sX)))
            ((t ∣_ baseChangeComponentOpen i i' g f w) ≫
              (X'.homOfLE (baseChangeComponentOpen_le i i' g f w) ≫
                ((componentNeighbourhood i' w).ι ≫ (f ≫ sX))))
            (T.homOfLE (testOpen_le_componentNeighbourhood i i' g f w t))
            (by rw [← Category.assoc, testOpen_homOfLE_morphismRestrict, Category.assoc]) k
            (chowGroupRestrict C (t ≫ (f ≫ sX))
              ((t ∣_ componentNeighbourhood i' w) ≫ ((componentNeighbourhood i' w).ι ≫ (f ≫ sX)))
              (t ⁻¹ᵁ componentNeighbourhood i' w).ι
              (by rw [← Category.assoc (t ∣_ _), morphismRestrict_ι, Category.assoc]) k α)) =
      (virtualNormalBundleClass C ((Z'.connectedComponentOpens w).ι ≫ sZ')
          (baseChangeComponentMap i i' g f w ≫
            ((componentNeighbourhood i (componentBelow g w)).ι ≫ sX))
          (baseChangeComponentImmersion i i' g f sq w)
          (baseChangeComponentImmersion_comp_structureMorphism_base C sX i i' g f sq sZ' hi' w)
          ((𝒩.toComponent i (componentBelow g w)).baseChange
            (componentRestriction i (componentBelow g w))
            (baseChangeComponentImmersion i i' g f sq w)
            (g.resConnectedComponent w) (baseChangeComponentMap i i' g f w)
            (isPullback_baseChangeComponentMap i i' g f sq w))
          (componentRank 𝒩.bundle (componentBelow g w))).cap
          (t ∣_ baseChangeComponentOpen i i' g f w) k
          (chowGroupRestrict C (((t ≫ f) ∣_ componentNeighbourhood i (componentBelow g w)) ≫
              ((componentNeighbourhood i (componentBelow g w)).ι ≫ sX))
            ((t ∣_ baseChangeComponentOpen i i' g f w) ≫ (baseChangeComponentMap i i' g f w ≫
              ((componentNeighbourhood i (componentBelow g w)).ι ≫ sX)))
            (T.homOfLE (testOpen_le_componentNeighbourhood_base i i' g f w t))
            (by rw [← Category.assoc, testOpen_homOfLE_morphismRestrict_base, Category.assoc]) k
            (chowGroupRestrict C ((t ≫ f) ≫ sX)
              (((t ≫ f) ∣_ componentNeighbourhood i (componentBelow g w)) ≫
                ((componentNeighbourhood i (componentBelow g w)).ι ≫ sX))
              ((t ≫ f) ⁻¹ᵁ componentNeighbourhood i (componentBelow g w)).ι
              (by
                rw [← Category.assoc ((t ≫ f) ∣_ _), morphismRestrict_ι]
                simp only [Category.assoc])
              k (chowGroupCongr C (Category.assoc t f sX).symm k α))) := by
  have := isFiniteLocallyFreeOfRank_toComponent_baseChange i i' g f sq 𝒩 w
  have : SheafOfModules.IsFiniteLocallyFreeOfRank.{u, u, u}
      (((𝒩.baseChange i i' g f sq).toComponent i' w).baseChange
        (componentRestriction i' w) (baseChangeComponentImmersion i i' g f sq w) (𝟙 _)
        (X'.homOfLE (baseChangeComponentOpen_le i i' g f w))
        (isPullback_baseChangeComponentImmersion_homOfLE i i' g f sq w)).bundle
      (componentRank 𝒩.bundle (componentBelow g w)) :=
    isFiniteLocallyFreeOfRank_modulePullback _ _ _ inferInstance
  have : SheafOfModules.IsFiniteLocallyFreeOfRank.{u, u, u}
      ((𝒩.toComponent i (componentBelow g w)).baseChange
        (componentRestriction i (componentBelow g w)) (baseChangeComponentImmersion i i' g f sq w)
        (g.resConnectedComponent w) (baseChangeComponentMap i i' g f w)
        (isPullback_baseChangeComponentMap i i' g f sq w)).bundle
      (componentRank 𝒩.bundle (componentBelow g w)) :=
    isFiniteLocallyFreeOfRank_modulePullback _ _ _ inferInstance
  have hV : X'.homOfLE (baseChangeComponentOpen_le i i' g f w) ≫
      ((componentNeighbourhood i' w).ι ≫ (f ≫ sX)) = baseChangeComponentMap i i' g f w ≫
        ((componentNeighbourhood i (componentBelow g w)).ι ≫ sX) := by
    rw [Scheme.homOfLE_ι_assoc, baseChangeComponentMap_ι_assoc]
  refine (virtualNormalGysinClass_cap_congr C _ _ _ hV _ _
    (baseChangeComponentImmersion_comp_structureMorphism_base C sX i i' g f sq sZ' hi' w)
    _ _ _ _ _ _ (chowGroupCongr_heq C
      (congrArg (fun s ↦ (t ∣_ baseChangeComponentOpen i i' g f w) ≫ s) hV)
      k _).symm).trans ?_
  rw [virtualNormalGysinClass_baseChangeComponent C sX i i' g f sq 𝒩 w _
    (baseChangeComponentImmersion_comp_structureMorphism_base C sX i i' g f sq sZ' hi' w)]
  congr 1
  refine eq_of_heq ((chowGroupCongr_heq C _ k _).trans ?_)
  rw [chowGroupRestrict_comp, chowGroupRestrict_comp, chowGroupRestrict_chowGroupCongr]
  · exact chowGroupRestrict_heq_congr C _ _ _ _ _ _ _
      (by rw [Scheme.homOfLE_ι, Scheme.homOfLE_ι]) k α
  · rw [Scheme.homOfLE_ι, baseChangeComponentMap_ι_assoc, ← morphismRestrict_ι_assoc]

end PieceComparison


/-- **Stacks 0FBK, the base-change clause on cap operations, for a virtual normal sheaf of
arbitrary rank.** For a cartesian square `Z' = Z ×_X X'` of closed immersions and a test scheme
`t : T ⟶ X'`, the degree-`n` part of `c(Z' ⟶ X', g^*𝒩) ∈ A^*(Z' ⟶ X')^∧` caps as the degree-`n`
part of `c(Z ⟶ X, 𝒩)` does on `t ≫ f`, through `Z ×_X T ≅ Z' ×_{X'} T`.

The two sides are compared piece by piece on the decomposition of `Z' ×_{X'} T` over the
connected components `Z'_w` of `Z'` (Stacks 0FDZ). On the piece over `Z'_w`, lying over the
component `Z_a` of `Z` on which `𝒩` has rank `r_a`, both sides vanish in degrees other than `r_a`;
in degree `r_a` both are, on `Z'_w ×_{V_w} t⁻¹(V_w)` for the open `V_w = U'_w ∩ f⁻¹(U_a)` of `X'`,
the cap product with the class of the base change of `𝒩` to the closed immersion `Z'_w ⟶ V_w`,
by the base-change clause at constant rank applied to `Z'_w ⟶ U'_w` and to `Z_a ⟶ U_a`. -/
theorem completedVirtualNormalGysinClass_cap_baseChange (C : ChowSituation.{u})
    {Z X Z' X' : Scheme.{u}} (sZ : Z ⟶ C.S) [LocallyOfFiniteType sZ] (sX : X ⟶ C.S)
    [LocallyOfFiniteType sX] (i : Z ⟶ X) [IsClosedImmersion i] (hi : i ≫ sX = sZ)
    (i' : Z' ⟶ X') [IsClosedImmersion i'] (g : Z' ⟶ Z) (f : X' ⟶ X) [LocallyOfFiniteType f]
    (sq : IsPullback i' g f i) (𝒩 : VirtualNormalBundle i) (sZ' : Z' ⟶ C.S)
    [LocallyOfFiniteType sZ'] (hi' : i' ≫ (f ≫ sX) = sZ') (n : ℤ) {T : Scheme.{u}}
    (t : T ⟶ X') [LocallyOfFiniteType t] (k : ℤ) (α : chowGroup C (t ≫ (f ≫ sX)) k) :
    haveI : IsLocallyNoetherian Z := LocallyOfFiniteType.isLocallyNoetherian sZ
    haveI : IsLocallyNoetherian X := LocallyOfFiniteType.isLocallyNoetherian sX
    haveI : IsLocallyNoetherian Z' := LocallyOfFiniteType.isLocallyNoetherian sZ'
    haveI : IsLocallyNoetherian X' := LocallyOfFiniteType.isLocallyNoetherian (f ≫ sX)
    (completedBivariantSequenceOfInvertible C sZ' (f ≫ sX) i' hi'
        (completedVirtualNormalGysinClass C sZ' (f ≫ sX) i' hi' (𝒩.baseChange i i' g f sq)) n).cap
        t k α =
      chowPushforwardOfIso C (pullback.fst i (t ≫ f) ≫ sZ) (pullback.fst i' t ≫ sZ')
        (subschemeTestBaseChangeIso i i' g f sq t).hom
        (subschemeTestBaseChangeIso_hom_comp_structureMorphism C sZ sX i hi i' g f sq sZ' hi' t)
        (k - n)
        ((completedBivariantSequenceOfInvertible C sZ sX i hi
          (completedVirtualNormalGysinClass C sZ sX i hi 𝒩) n).cap (t ≫ f) k
          (chowGroupCongr C (Category.assoc t f sX).symm k α)) := by
  have : IsLocallyNoetherian Z := LocallyOfFiniteType.isLocallyNoetherian sZ
  have : IsLocallyNoetherian X := LocallyOfFiniteType.isLocallyNoetherian sX
  have : IsLocallyNoetherian Z' := LocallyOfFiniteType.isLocallyNoetherian sZ'
  have : IsLocallyNoetherian X' := LocallyOfFiniteType.isLocallyNoetherian (f ≫ sX)
  refine eq_of_chowGroupRestrict_piece_eq C sZ' (f ≫ sX) i' hi' t (pullback.snd i' t)
    (pullback.fst i' t) (IsPullback.of_hasPullback i' t).flip (pullback.fst i' t ≫ sZ')
    (pullbackSnd_comp_structureMorphism_eq C sZ' (f ≫ sX) i' hi' t) fun w ↦ ?_
  by_cases hn : n = (componentRank 𝒩.bundle (componentBelow g w) : ℤ)
  · subst hn
    rw [chowGroupRestrict_piece_cap_baseChange_eq C sZ sX i hi i' g f sq 𝒩 sZ' hi' w t k α,
      chowGroupRestrict_piece_completedVirtualNormalGysinClass_baseChange_cap C sX i i' g f sq 𝒩
        sZ' hi' w t k α]
    rw [baseChangeComponent_cap_eq C sX i i' g f sq 𝒩 sZ' hi' w t k α]
  · rw [chowGroupRestrict_piece_cap_baseChange_of_ne C sZ sX i hi i' g f sq 𝒩 sZ' hi' w t n hn k α,
      chowGroupRestrict_completedVirtualNormalGysinCap_piece_eq_zero C sZ' (f ≫ sX) i' hi'
        (𝒩.baseChange i i' g f sq) t (pullback.snd i' t) (pullback.fst i' t)
        (IsPullback.of_hasPullback i' t).flip (pullback.fst i' t ≫ sZ')
        (pullbackSnd_comp_structureMorphism_eq C sZ' (f ≫ sX) i' hi' t) w n
        (by rwa [componentRank_baseChange i i' g f sq 𝒩 w]) k α]

/-- **Stacks 0FBK, the base-change clause, for a virtual normal sheaf of arbitrary rank.** For
`f : X' ⟶ X` locally of finite type, the restriction (Stacks 0F9Z) of
`c(Z ⟶ X, 𝒩) ∈ A^*(Z ⟶ X)^∧` along `f` is `c(Z ×_X X' ⟶ X', g^*𝒩)`, for the virtual normal sheaf
`g^*𝒩` of Stacks 0FBJ. Both are read degree by degree (Stacks 0FE0), and in each degree the cap
operations agree by `Stacks.Chow.completedVirtualNormalGysinClass_cap_baseChange`. -/
@[stacks 0FBK "base change: the restriction of c(Z → X, 𝒩) ∈ A^*(Z → X)^∧ along X' → X is \
c(Z ×_X X' → X', g^*𝒩), for 𝒩 of arbitrary rank"]
theorem completedBivariantRestriction_completedVirtualNormalGysinClass (C : ChowSituation.{u})
    {Z X X' : Scheme.{u}} (sZ : Z ⟶ C.S) [LocallyOfFiniteType sZ] (sX : X ⟶ C.S)
    [LocallyOfFiniteType sX] (i : Z ⟶ X) [IsClosedImmersion i] (hi : i ≫ sX = sZ)
    (f : X' ⟶ X) [LocallyOfFiniteType f] (𝒩 : VirtualNormalBundle i) :
    haveI : IsLocallyNoetherian Z := LocallyOfFiniteType.isLocallyNoetherian sZ
    haveI : IsLocallyNoetherian X := LocallyOfFiniteType.isLocallyNoetherian sX
    haveI : IsLocallyNoetherian X' := LocallyOfFiniteType.isLocallyNoetherian (f ≫ sX)
    haveI : IsLocallyNoetherian (pullback i f) :=
      LocallyOfFiniteType.isLocallyNoetherian (pullback.fst i f ≫ sZ)
    completedBivariantRestrictionViaSequence C sZ sX i hi f
        (completedVirtualNormalGysinClass C sZ sX i hi 𝒩) =
      completedVirtualNormalGysinClass C (pullback.fst i f ≫ sZ) (f ≫ sX) (pullback.snd i f)
        (pullbackSnd_comp_structureMorphism_eq C sZ sX i hi f)
        (baseChangeVirtualNormalBundle i f 𝒩) := by
  have : IsLocallyNoetherian Z := LocallyOfFiniteType.isLocallyNoetherian sZ
  have : IsLocallyNoetherian X := LocallyOfFiniteType.isLocallyNoetherian sX
  have : IsLocallyNoetherian X' := LocallyOfFiniteType.isLocallyNoetherian (f ≫ sX)
  have : IsLocallyNoetherian (pullback i f) :=
    LocallyOfFiniteType.isLocallyNoetherian (pullback.fst i f ≫ sZ)
  refine completedBivariantSequence_injective C (gysinSystemOfInvertible C) _ _ _ _
    (gysinSystemOfInvertible_isNaturalUnderOpenImmersion C)
    (gysinSystemOfInvertible_isNaturalUnderOpensRestriction C)
    (gysinSystemOfInvertible_isNaturalUnderPullbackComp C) (funext fun n ↦ ?_)
  refine (completedBivariantSequenceOfInvertible_completedBivariantRestriction C sZ sX i hi f
    _ n).trans (BivariantClass.ext C _ _ _ _ _ _ fun {T} t _ k α ↦ ?_)
  refine Eq.trans ?_ (completedVirtualNormalGysinClass_cap_baseChange C sZ sX i hi
    (pullback.snd i f) (pullback.fst i f) f (isPullback_pullbackSnd i f) 𝒩 _
    (pullbackSnd_comp_structureMorphism_eq C sZ sX i hi f) n t k α).symm
  rw [bivariantRestriction_cap, bivariantRestrictionCap_apply]
  refine chowPushforwardOfIso_congr_apply C _ _ _ _ ?_ _ _ _ _
  refine (isPullback_subschemeTestBaseChange i (pullback.snd i f) (pullback.fst i f) f
    (isPullback_pullbackSnd i f) t).hom_ext ?_ ?_
  · simp
  · simp

end Stacks.Chow

end
