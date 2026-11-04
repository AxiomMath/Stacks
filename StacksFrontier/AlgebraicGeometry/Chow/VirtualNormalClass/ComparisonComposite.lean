module

public import StacksFrontier.AlgebraicGeometry.Chow.VirtualNormalClass.BaseChange
public import StacksFrontier.AlgebraicGeometry.Chow.BivariantLemmas.CompletedRestriction

/-!
# Composing comparisons of virtual normal bundles, and the cap in restriction form

A comparison of virtual normal bundles `𝒩 ⟶ 𝒩'` over a cartesian square of closed immersions
(`Stacks.Chow.VirtualNormalBundle.Comparison`) is an isomorphism `g^*(𝒩^∨) ≅ 𝒩'^∨` matching the
surjections onto the conormal sheaves through the canonical map of Stacks 01R4. Since that map is
compatible with stacking squares (Stacks 04G2), comparisons compose along vertically stacked
squares, and a comparison over a stacked square determines one over its upper half once a
comparison over its lower half is given.

The base change clause of Stacks 0FBK, `Comparison.virtualNormalClass_cap`, reads the cap of
`c(Z' ⟶ X', 𝒩')` through the isomorphism `T ×_{X'} Z' ≅ T ×_X Z`. Pushing forward along the inverse
of an isomorphism is restricting along it, so the cap is the restriction of the cap of
`c(Z ⟶ X, 𝒩)` along any morphism `T ×_{X'} Z' ⟶ T ×_X Z` over `T` and `Z`; that is the form in
which it is combined with the restrictions of Stacks 0FDZ.

## Main definitions

* `Stacks.Chow.VirtualNormalBundle.Comparison.trans` — the comparison over a stacked square.
* `Stacks.Chow.VirtualNormalBundle.Comparison.cancel` — the comparison over the upper square.
* `Stacks.Chow.VirtualNormalBundle.Comparison.congr` — transport along equal morphisms.

## Main results

* `Stacks.Chow.VirtualNormalBundle.Comparison.virtualNormalClass_cap_eq_chowGroupRestrict` — the
  cap of `c(Z' ⟶ X', 𝒩')` is a restriction of the cap of `c(Z ⟶ X, 𝒩)`.

## References

* [Stacks Project, Tag 0FBK](https://stacks.math.columbia.edu/tag/0FBK)
* [Stacks Project, Tag 04G2](https://stacks.math.columbia.edu/tag/04G2)
-/

@[expose] public noncomputable section

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits
open RingedSpaceModuleAdjunction Stacks.AlgebraicGeometry.ReflexiveModules

universe u

namespace Stacks.Chow.VirtualNormalBundle

section Paste

variable {Z X Z₁ X₁ Z₂ X₂ : Scheme.{u}} {i : Z ⟶ X} [IsClosedImmersion i]
  {i₁ : Z₁ ⟶ X₁} [IsClosedImmersion i₁] {i₂ : Z₂ ⟶ X₂} [IsClosedImmersion i₂]
  {g₁ : Z₁ ⟶ Z} {h₁ : X₁ ⟶ X} {g₂ : Z₂ ⟶ Z₁} {h₂ : X₂ ⟶ X₁}
  {sq₁ : IsPullback i₁ g₁ h₁ i} {sq₂ : IsPullback i₂ g₂ h₂ i₁}
  {sq₁₂ : IsPullback i₂ (g₂ ≫ g₁) (h₂ ≫ h₁) i}
  {𝒩 : VirtualNormalBundle i} {𝒩₁ : VirtualNormalBundle i₁} {𝒩₂ : VirtualNormalBundle i₂}

/-- The diagram chase behind `Stacks.Chow.VirtualNormalBundle.Comparison.trans`. -/
theorem comm_trans_aux {𝒞 : Type*} [Category 𝒞] {P Q R S T U V W : 𝒞} (a : P ⟶ Q) (x : Q ⟶ R)
    (y : R ⟶ S) (z : S ⟶ T) (uu : R ⟶ U) (v : U ⟶ T) (w : Q ⟶ V) (t : V ⟶ U)
    (gs : P ⟶ W) (b : W ⟶ V) (K : W ⟶ T) (hyz : y ≫ z = uu ≫ v)
    (hxu : x ≫ uu = w ≫ t) (hnat : gs ≫ b = a ≫ w) (hK : K = b ≫ t ≫ v) :
    (a ≫ x ≫ y) ≫ z = gs ≫ K := by
  subst hK
  rw [reassoc_of% hnat]
  simp only [Category.assoc]
  rw [hyz, reassoc_of% hxu]

/-- The diagram chase behind `Stacks.Chow.VirtualNormalBundle.Comparison.cancel`. -/
theorem comm_cancel_aux {𝒞 : Type*} [Category 𝒞] {P Q R S T U V W : 𝒞} (xi : R ⟶ Q)
    (ai : Q ⟶ P) (y : P ⟶ S) (z : S ⟶ T) (s₁' : R ⟶ U) (v : U ⟶ T) (w : Q ⟶ V) (t : V ⟶ U)
    (a : P ⟶ Q) (gs : P ⟶ W) (b : W ⟶ V) (K : W ⟶ T) (hia : ai ≫ a = 𝟙 Q)
    (hΨ : y ≫ z = gs ≫ K) (hK : K = b ≫ t ≫ v) (hnat : gs ≫ b = a ≫ w)
    (hs₁ : s₁' = xi ≫ w ≫ t) : (xi ≫ ai ≫ y) ≫ z = s₁' ≫ v := by
  subst hK hs₁
  simp only [Category.assoc]
  rw [hΨ, reassoc_of% hnat, reassoc_of% hia]

/-- The canonical map of Stacks 01R4 for a stacked square, Stacks 04G2. -/
theorem immersionConormalSheafMap_stack :
    Stacks.Immersion.immersionConormalSheafMap i₂ i (g₂ ≫ g₁) (h₂ ≫ h₁)
        (Stacks.Immersion.toShHom_square sq₁₂.w) =
      (modulePullbackComp g₂.toLRSHom.toShHom g₁.toLRSHom.toShHom).hom.app
          (Stacks.Thickenings.immersionConormalSheaf i) ≫
        (modulePullback g₂.toLRSHom.toShHom).map
          (Stacks.Immersion.immersionConormalSheafMap i₁ i g₁ h₁
            (Stacks.Immersion.toShHom_square sq₁.w)) ≫
        Stacks.Immersion.immersionConormalSheafMap i₂ i₁ g₂ h₂
          (Stacks.Immersion.toShHom_square sq₂.w) :=
  Stacks.Immersion.immersionConormalSheafMap_comp i₂ i₁ i g₂ h₂ sq₂.w g₁ h₁ sq₁.w

/-- **Comparisons compose along stacked squares**: comparisons `𝒩 ⟶ 𝒩₁` and `𝒩₁ ⟶ 𝒩₂` over two
vertically stacked cartesian squares give a comparison `𝒩 ⟶ 𝒩₂` over the composite square. -/
def Comparison.trans (Φ₁ : Comparison sq₁ 𝒩 𝒩₁) (Φ₂ : Comparison sq₂ 𝒩₁ 𝒩₂) :
    Comparison sq₁₂ 𝒩 𝒩₂ where
  map := (Scheme.Modules.pullbackComp g₂ g₁).inv.app (dualSheaf 𝒩.bundle) ≫
    (Scheme.Modules.pullback g₂).map Φ₁.map ≫ Φ₂.map
  isIso := by
    have := Φ₁.isIso
    have := Φ₂.isIso
    infer_instance
  comm := comm_trans_aux _ _ _ _ _ _ _ _ _ _ _ Φ₂.comm
    (((Scheme.Modules.pullback g₂).map_comp _ _).symm.trans
      ((congrArg (Scheme.Modules.pullback g₂).map Φ₁.comm).trans
        ((Scheme.Modules.pullback g₂).map_comp _ _)))
    ((modulePullbackComp g₂.toLRSHom.toShHom g₁.toLRSHom.toShHom).hom.naturality 𝒩.surjection)
    (immersionConormalSheafMap_stack (sq₁ := sq₁) (sq₂ := sq₂) (sq₁₂ := sq₁₂))

/-- **A comparison over a stacked square restricts to the upper square**: given comparisons
`𝒩 ⟶ 𝒩₁` over the lower square and `𝒩 ⟶ 𝒩₂` over the composite square, there is a comparison
`𝒩₁ ⟶ 𝒩₂` over the upper square. -/
def Comparison.cancel (Φ₁ : Comparison sq₁ 𝒩 𝒩₁) (Ψ : Comparison sq₁₂ 𝒩 𝒩₂) :
    Comparison sq₂ 𝒩₁ 𝒩₂ :=
  haveI := Φ₁.isIso
  { map := (Scheme.Modules.pullback g₂).map (inv Φ₁.map) ≫
      (Scheme.Modules.pullbackComp g₂ g₁).hom.app (dualSheaf 𝒩.bundle) ≫ Ψ.map
    isIso := by
      have := Ψ.isIso
      infer_instance
    comm := comm_cancel_aux _ _ _ _ _ _ _ _
      ((Scheme.Modules.pullbackComp g₂ g₁).inv.app (dualSheaf 𝒩.bundle)) _ _ _
      (Iso.hom_inv_id_app _ _) Ψ.comm
      (immersionConormalSheafMap_stack (sq₁ := sq₁) (sq₂ := sq₂) (sq₁₂ := sq₁₂))
      ((modulePullbackComp g₂.toLRSHom.toShHom g₁.toLRSHom.toShHom).hom.naturality
        𝒩.surjection)
      ((congrArg (Scheme.Modules.pullback g₂).map
          ((IsIso.eq_inv_comp Φ₁.map).2 Φ₁.comm)).trans
        (((Scheme.Modules.pullback g₂).map_comp _ _).trans
          (congrArg _ ((Scheme.Modules.pullback g₂).map_comp _ _)))) }

/-- A comparison over a square transports to a square with equal morphisms. -/
def Comparison.congr {Z' X' : Scheme.{u}} {i' : Z' ⟶ X'} [IsClosedImmersion i']
    {g g' : Z' ⟶ Z} {h h' : X' ⟶ X} (hg : g = g') (hh : h = h')
    {sq : IsPullback i' g h i} {sq' : IsPullback i' g' h' i} {𝒩' : VirtualNormalBundle i'}
    (Φ : Comparison sq 𝒩 𝒩') : Comparison sq' 𝒩 𝒩' := by
  subst hg hh
  exact Φ

end Paste

section Restrict

variable {Z X Z' X' : Scheme.{u}} {i : Z ⟶ X} [IsClosedImmersion i] {i' : Z' ⟶ X'}
  [IsClosedImmersion i'] {g : Z' ⟶ Z} {h : X' ⟶ X} {sq : IsPullback i' g h i}
  [LocallyOfFiniteType h] {𝒩 : VirtualNormalBundle i} {𝒩' : VirtualNormalBundle i'}
  (Φ : Comparison sq 𝒩 𝒩')
  (C : ChowSituation.{u}) (sX : X ⟶ C.S) [LocallyOfFiniteType sX] (sZ : Z ⟶ C.S)
  [LocallyOfFiniteType sZ] (hZ : i ≫ sX = sZ)
  (r : ℕ) [SheafOfModules.IsFiniteLocallyFreeOfRank.{u, u, u} 𝒩.bundle r]
  [SheafOfModules.IsFiniteLocallyFreeOfRank.{u, u, u} 𝒩'.bundle r]

include Φ in
/-- **Stacks 0FBK, compatibility with base change, in restriction form**: the cap of
`c(Z' ⟶ X', 𝒩')` at `t : T ⟶ X'` is the cap of `c(Z ⟶ X, 𝒩)` at `t ≫ h`, restricted along any
morphism `T ×_{X'} Z' ⟶ T ×_X Z` over `T` and over `Z` (it is the isomorphism of the cartesian
square). -/
theorem Comparison.virtualNormalClass_cap_eq_chowGroupRestrict {T : Scheme.{u}} (t : T ⟶ X')
    [LocallyOfFiniteType t] (m : T ⟶ X) [LocallyOfFiniteType m] (hm : t ≫ h = m)
    (φ : pullback i' t ⟶ pullback i m) [IsOpenImmersion φ]
    (hφ₁ : φ ≫ pullback.fst i m = pullback.fst i' t ≫ g)
    (hφ₂ : φ ≫ pullback.snd i m = pullback.snd i' t)
    (hbase : φ ≫ (pullback.fst i m ≫ sZ) = pullback.fst i' t ≫ (g ≫ sZ))
    (hmX : t ≫ (h ≫ sX) = m ≫ sX) (k : ℤ) (α : chowGroup C (t ≫ (h ≫ sX)) k) :
    haveI := locallyOfFiniteType_baseChange_fst sq
    (𝒩'.virtualNormalClass C (h ≫ sX) (g ≫ sZ)
        (baseChange_structure sq C sX sZ hZ) r).cap t k α =
      chowGroupRestrict C (pullback.fst i m ≫ sZ) (pullback.fst i' t ≫ (g ≫ sZ)) φ hbase (k - r)
        ((𝒩.virtualNormalClass C sX sZ hZ r).cap m k (chowGroupCongr C hmX k α)) := by
  subst hm
  have := locallyOfFiniteType_baseChange_fst sq
  have hφ : φ = (restrictionTestIso sq t).hom := by
    refine pullback.hom_ext ?_ ?_
    · rw [hφ₁, restrictionTestIso_hom_fst]
    · rw [hφ₂, restrictionTestIso_hom_snd]
  refine (Φ.virtualNormalClass_cap C sX sZ hZ r t k α).trans ?_
  rw [chowPushforwardOfIso_inv_eq_chowGroupRestrict C _ _ (restrictionTestIso sq t) _
    (by rw [restrictionTestIso_hom_fst_assoc])]
  exact DFunLike.congr_fun (chowGroupRestrict_congr C _ _ _ _ _ _ hφ.symm _) _

include Φ in
/-- `Stacks.Chow.VirtualNormalBundle.Comparison.virtualNormalClass_cap_eq_chowGroupRestrict` with
the structure morphisms of `Z'` and `X'` given by any morphisms equal to the composites. -/
theorem Comparison.virtualNormalClass_cap_eq_chowGroupRestrict' (sX' : X' ⟶ C.S)
    [LocallyOfFiniteType sX'] (sZ' : Z' ⟶ C.S) [LocallyOfFiniteType sZ'] (hX' : h ≫ sX = sX')
    (hZg : g ≫ sZ = sZ') (hZ' : i' ≫ sX' = sZ') {T : Scheme.{u}} (t : T ⟶ X')
    [LocallyOfFiniteType t] (m : T ⟶ X) [LocallyOfFiniteType m] (hm : t ≫ h = m)
    (φ : pullback i' t ⟶ pullback i m) [IsOpenImmersion φ]
    (hφ₁ : φ ≫ pullback.fst i m = pullback.fst i' t ≫ g)
    (hφ₂ : φ ≫ pullback.snd i m = pullback.snd i' t)
    (hbase : φ ≫ (pullback.fst i m ≫ sZ) = pullback.fst i' t ≫ sZ')
    (hmX : t ≫ sX' = m ≫ sX) (k : ℤ) (α : chowGroup C (t ≫ sX') k) :
    (𝒩'.virtualNormalClass C sX' sZ' hZ' r).cap t k α =
      chowGroupRestrict C (pullback.fst i m ≫ sZ) (pullback.fst i' t ≫ sZ') φ hbase (k - r)
        ((𝒩.virtualNormalClass C sX sZ hZ r).cap m k (chowGroupCongr C hmX k α)) := by
  subst hX' hZg
  exact Φ.virtualNormalClass_cap_eq_chowGroupRestrict C sX sZ hZ r t m hm φ hφ₁ hφ₂ hbase hmX k α

end Restrict

end Stacks.Chow.VirtualNormalBundle

end
