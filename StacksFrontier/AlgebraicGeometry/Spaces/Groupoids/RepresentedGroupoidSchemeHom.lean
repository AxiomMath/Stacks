module

public import StacksFrontier.AlgebraicGeometry.Spaces.Groupoids.GroupoidSchemeOfRepresented
public import StacksFrontier.AlgebraicGeometry.GroupScheme.Pullback

/-!
# Morphisms of the groupoid schemes of represented groupoids

Let `(U, R, s, t, c)` and `(U', R', s', t', c')` be groupoids of the big fppf site over `S`
presented by objects of the site, their composition laws given on sections. A pair of morphisms
`fU : U' ⟶ U`, `fV : R' ⟶ R` of the site compatible with source and target and with composition
of sections induces a morphism of the groupoid schemes over `S`
(`AlgebraicGeometry.Space.representedGroupoidScheme`). Compatibility with identities is automatic:
the image of an identity is an idempotent arrow, hence an identity.

This is the morphism of groupoid schemes `(U', R', s', t', c') ⟶ (U, R, s, t, c)` of the proof of
Stacks 0DUQ, to which Stacks 0DT9 is applied.

## Main results

* `AlgebraicGeometry.Space.representedGroupoidSchemeHom`: the morphism of groupoid schemes induced
  by `fU` and `fV`.
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits Opposite

universe u

namespace AlgebraicGeometry.Space

variable {B : BigFppfSite.{u}} {S : Scheme.{u}} {hS : B.Contains S}
  {U R U' R' : BigFppfOver B S hS} (s t : R ⟶ U)
  (c : Deformation.composableArrows (yoneda.obj U) (yoneda.obj R)
    (yoneda.map s) (yoneda.map t) ⟶ yoneda.obj R)
  (hG : ∀ T, Nonempty (Deformation.PointwiseGroupoid ((yoneda.map s).app T)
    ((yoneda.map t).app T) fun p => c.app T p))
  (s' t' : R' ⟶ U')
  (c' : Deformation.composableArrows (yoneda.obj U') (yoneda.obj R')
    (yoneda.map s') (yoneda.map t') ⟶ yoneda.obj R')
  (hG' : ∀ T, Nonempty (Deformation.PointwiseGroupoid ((yoneda.map s').app T)
    ((yoneda.map t').app T) fun p => c'.app T p))
  (fU : U' ⟶ U) (fV : R' ⟶ R) (hs : fV ≫ s = s' ≫ fU) (ht : fV ≫ t = t' ≫ fU)

/-- The composition of `representedGroupoidScheme s t c hG` is the image under `siteToOver` of
`representedCompMap s t c`, precomposed with the identification of `representedPairs s t` with
the fibre product. -/
theorem representedGroupoidScheme_comp :
    (representedGroupoidScheme s t c hG).comp =
      (isPullback_map_representedPairs s t).isoPullback.inv ≫
        (siteToOver B hS).map (representedCompMap s t c) := rfl

/-- The identity of `representedGroupoidScheme s t c hG` is the image under `siteToOver` of
`representedIdentity s t c hG`. -/
theorem representedGroupoidScheme_identity :
    (representedGroupoidScheme s t c hG).identity =
      (siteToOver B hS).map (representedIdentity s t c hG) := rfl

include hs ht in
/-- The images of a composable pair of sections of `R'` are composable. -/
theorem comp_fV_composable {X : BigFppfOver B S hS} {a b : X ⟶ R'} (h : a ≫ s' = b ≫ t') :
    (a ≫ fV) ≫ s = (b ≫ fV) ≫ t := by
  rw [Category.assoc, Category.assoc, hs, ht, ← Category.assoc, ← Category.assoc, h]

/-- **The morphism of groupoid schemes induced by a morphism of represented groupoids.** -/
noncomputable def representedGroupoidSchemeHom
    (hc : ∀ (X : BigFppfOver B S hS) (a b : X ⟶ R') (h : a ≫ s' = b ≫ t'),
      representedComp s' t' c' a b h ≫ fV =
        representedComp s t c (a ≫ fV) (b ≫ fV) (comp_fV_composable s t s' t' fU fV hs ht h)) :
    Stacks.Groupoids.GroupoidScheme.Hom (representedGroupoidScheme s' t' c' hG')
      (representedGroupoidScheme s t c hG) where
  mapObjects := (siteToOver B hS).map fU
  mapArrows := (siteToOver B hS).map fV
  map_source := by
    change (siteToOver B hS).map fV ≫ (siteToOver B hS).map s =
      (siteToOver B hS).map s' ≫ (siteToOver B hS).map fU
    rw [← Functor.map_comp, ← Functor.map_comp, hs]
  map_target := by
    change (siteToOver B hS).map fV ≫ (siteToOver B hS).map t =
      (siteToOver B hS).map t' ≫ (siteToOver B hS).map fU
    rw [← Functor.map_comp, ← Functor.map_comp, ht]
  map_identity := by
    suffices hid : fU ≫ representedIdentity s t c hG = representedIdentity s' t' c' hG' ≫ fV by
      have h := congrArg (siteToOver B hS).map hid
      rwa [Functor.map_comp, Functor.map_comp] at h
    let D' := representedSetData s' t' c' hG' (op U')
    let e' := representedIdentity s' t' c' hG'
    have hse' : e' ≫ s' = 𝟙 U' := representedIdentity_source s' t' c' hG'
    have hte' : e' ≫ t' = 𝟙 U' := representedIdentity_target s' t' c' hG'
    have hidem' : representedComp s' t' c' e' e' (hse'.trans hte'.symm) = e' :=
      (D'.comp_congr (congrArg D'.identity hte'.symm) rfl _ (D'.source_identity _)).trans
        (D'.comp_identity_left _)
    have hsa : (e' ≫ fV) ≫ s = fU := by
      rw [Category.assoc, hs, ← Category.assoc, hse', Category.id_comp]
    have hta : (e' ≫ fV) ≫ t = fU := by
      rw [Category.assoc, ht, ← Category.assoc, hte', Category.id_comp]
    have hidem : representedComp s t c (e' ≫ fV) (e' ≫ fV) (hsa.trans hta.symm) = e' ≫ fV :=
      (representedComp_congr s t c rfl rfl _ _).trans
        ((hc U' e' e' (hse'.trans hte'.symm)).symm.trans (congrArg (· ≫ fV) hidem'))
    exact (representedSetData_identity_eq s t c hG fU).symm.trans
      ((representedSetData s t c hG (op U')).eq_identity_of_comp_self_eq fU (e' ≫ fV) hsa hta
        (hsa.trans hta.symm) hidem).symm
  map_comp := by
    intro T f g w w'
    let F := siteToOver B hS
    have hp := isPullback_map_representedPairs s t
    have hp' := isPullback_map_representedPairs s' t'
    have hpS := isPullback_representedPairs s t
    let m := hpS.lift (representedFst s' t' ≫ fV) (representedSnd s' t' ≫ fV)
      (comp_fV_composable s t s' t' fU fV hs ht (representedFst_comp s' t'))
    have hm₁ : m ≫ representedFst s t = representedFst s' t' ≫ fV := hpS.lift_fst _ _ _
    have hm₂ : m ≫ representedSnd s t = representedSnd s' t' ≫ fV := hpS.lift_snd _ _ _
    have hsite : representedCompMap s' t' c' ≫ fV = m ≫ representedCompMap s t c :=
      (hc _ _ _ (representedFst_comp s' t')).trans
        ((representedComp_congr s t c hm₁.symm hm₂.symm _ _).trans
          (comp_representedCompMap s t c m).symm)
    let k' : T ⟶ F.obj (representedPairs s' t') :=
      pullback.lift f g w ≫ hp'.isoPullback.inv
    have hk₁ : k' ≫ F.map (representedFst s' t') = f :=
      (Category.assoc _ _ _).trans ((congrArg (pullback.lift f g w ≫ ·)
        hp'.isoPullback_inv_fst).trans (pullback.lift_fst _ _ _))
    have hk₂ : k' ≫ F.map (representedSnd s' t') = g :=
      (Category.assoc _ _ _).trans ((congrArg (pullback.lift f g w ≫ ·)
        hp'.isoPullback_inv_snd).trans (pullback.lift_snd _ _ _))
    have hk : k' ≫ F.map m = pullback.lift (f ≫ F.map fV) (g ≫ F.map fV) w' ≫
        hp.isoPullback.inv := by
      refine hp.hom_ext ?_ ?_
      · rw [Category.assoc, ← F.map_comp, hm₁, F.map_comp, ← Category.assoc, hk₁]
        exact ((Category.assoc _ _ _).trans ((congrArg (_ ≫ ·) hp.isoPullback_inv_fst).trans
          (pullback.lift_fst _ _ _))).symm
      · rw [Category.assoc, ← F.map_comp, hm₂, F.map_comp, ← Category.assoc, hk₂]
        exact ((Category.assoc _ _ _).trans ((congrArg (_ ≫ ·) hp.isoPullback_inv_snd).trans
          (pullback.lift_snd _ _ _))).symm
    change (pullback.lift f g w ≫ hp'.isoPullback.inv ≫ F.map (representedCompMap s' t' c')) ≫
        F.map fV = pullback.lift (f ≫ F.map fV) (g ≫ F.map fV) w' ≫ hp.isoPullback.inv ≫
          F.map (representedCompMap s t c)
    exact (congrArg (· ≫ F.map fV) (Category.assoc (pullback.lift f g w) hp'.isoPullback.inv
        (F.map (representedCompMap s' t' c'))).symm).trans
      ((Category.assoc k' _ _).trans ((congrArg (k' ≫ ·) ((F.map_comp _ _).symm.trans
        ((congrArg F.map hsite).trans (F.map_comp _ _)))).trans
        ((Category.assoc _ _ _).symm.trans ((congrArg (· ≫ F.map (representedCompMap s t c))
          hk).trans (Category.assoc _ _ _)))))

/-- The morphism of objects of `representedGroupoidSchemeHom` is the image of `fU`. -/
@[simp]
theorem representedGroupoidSchemeHom_mapObjects (hc) :
    (representedGroupoidSchemeHom s t c hG s' t' c' hG' fU fV hs ht hc).mapObjects =
      (siteToOver B hS).map fU := rfl

/-- The morphism of arrows of `representedGroupoidSchemeHom` is the image of `fV`. -/
@[simp]
theorem representedGroupoidSchemeHom_mapArrows (hc) :
    (representedGroupoidSchemeHom s t c hG s' t' c' hG' fU fV hs ht hc).mapArrows =
      (siteToOver B hS).map fV := rfl

end AlgebraicGeometry.Space

end
