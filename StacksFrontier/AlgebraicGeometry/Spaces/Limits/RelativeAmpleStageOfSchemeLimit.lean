module

public import Mathlib.CategoryTheory.Filtered.Final
public import StacksFrontier.AlgebraicGeometry.AmpleBridge.Basic
public import StacksFrontier.AlgebraicGeometry.AmpleLimit.Unconditional
public import StacksFrontier.AlgebraicGeometry.RelativeAmpleAffineBase.Basic
public import StacksFrontier.AlgebraicGeometry.RelativeVeryAmple.TensorPower
public import StacksFrontier.AlgebraicGeometry.Spaces.AffineHigherPushforwardVanishing
public import StacksFrontier.AlgebraicGeometry.Spaces.BaseChangeModuleInvertible
public import StacksFrontier.AlgebraicGeometry.Spaces.ChartSchemeRestrictionBaseChange
public import StacksFrontier.AlgebraicGeometry.Spaces.ChowLemma.Basic
public import StacksFrontier.AlgebraicGeometry.Spaces.LimitSituation
public import StacksFrontier.AlgebraicGeometry.Spaces.Perfect.ResolutionPropertyRelativeAmple
public import StacksFrontier.AlgebraicGeometry.Spaces.ProjectiveCoverTwistVanishing
public import StacksFrontier.AlgebraicGeometry.Spaces.ProperPermanence
public import StacksFrontier.AlgebraicGeometry.Spaces.RelativeAmpleOverScheme
public import StacksFrontier.AlgebraicGeometry.Spaces.SmallEtaleModulePullback

/-!
# Ampleness on the limit of a system of proper algebraic spaces over an affine scheme

Let `E` be a directed inverse system of algebraic spaces over `S` with affine transition
morphisms, each stage proper over a fixed affine scheme `V` of the site, compatibly, and let
`cE` be its limit. Suppose that some stage `E_{i₀}` is a scheme, so that every later stage is a
scheme too (an affine morphism to a scheme has a scheme as source), and that the underlying
scheme functor preserves the limit of the schemes representing the later stages. If an invertible
module `N` on `E_{i₀}` pulls back to a module on `cE.pt` which is ample relative to `cE.pt ⟶ V`,
then the pullback of `N` to some later stage `E_j` is ample relative to `E_j ⟶ V`.

This is the step of the proof of Stacks 0D3D which applies Stacks 09MT to the system of fibres
`X_{i, y_i}`: once those stages are schemes (Stacks 07SR), the ampleness of `L` on the fibre
`X_y = lim X_{i, y_i}` descends to a stage. The stages are read as schemes of the site through
their representing objects, Stacks 09MT is applied to that system of schemes, and Stacks 0D32
turns its conclusion back into relative ampleness of algebraic spaces.

The preservation hypothesis `hpres` is the point where the source's standing convention of
Section 70.2 (tag 07SD) enters: it says that the scheme the site sees as the limit of the stages
is their limit as schemes.

## Main results

* `AlgebraicGeometry.Space.isRepresentable_obj_of_isAffineHom_map`: a stage affine over a stage
  which is a scheme is a scheme.
* `AlgebraicGeometry.Space.exists_le_isRelativelyAmple_of_isRelativelyAmple_limit`: the
  statement above.

## References

* [Stacks Project, Tag 0D3D](https://stacks.math.columbia.edu/tag/0D3D)
* [Stacks Project, Tag 09MT](https://stacks.math.columbia.edu/tag/09MT)
* [Stacks Project, Tag 0D32](https://stacks.math.columbia.edu/tag/0D32)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits Opposite

universe u

namespace AlgebraicGeometry.Space

variable {B : BigFppfSite.{u}} {S : Scheme.{u}} {hS : B.Contains S}
  {I : Type u} [Preorder I] [IsDirected I (· ≤ ·)]
  {E : Iᵒᵖ ⥤ (BigFppfOver B S hS)ᵒᵖ ⥤ Type u}

omit [IsDirected I (· ≤ ·)] in
/-- **A stage affine over a scheme is a scheme.** In a system of algebraic spaces with affine
transition morphisms, every stage mapping to a representable stage is representable: an affine
morphism is representable (Stacks 03WG), and a representable morphism to a representable
presheaf has a representable source (Stacks 03KC). -/
theorem isRepresentable_obj_of_isAffineHom_map
    (hE : ∀ j : I, IsAlgebraicSpace B S hS (E.obj (op j)))
    (hEaff : ∀ {i j : Iᵒᵖ} (g : i ⟶ j), IsAffineHom B S hS (E.map g))
    {i₀ : I} (hrep : (E.obj (op i₀)).IsRepresentable) {j : Iᵒᵖ} (g : j ⟶ op i₀) :
    (E.obj j).IsRepresentable :=
  Functor.isRepresentable_of_relativelyRepresentable_of_target_isRepresentable (E.map g)
    (relativelyRepresentable_of_isAffineHom B S hS
      (X := (⟨E.obj j, hE j.unop⟩ : AlgebraicSpaces B S hS))
      (Y := (⟨E.obj (op i₀), hE i₀⟩ : AlgebraicSpaces B S hS))
      (ObjectProperty.homMk (E.map g)) (hEaff g))

/-- Base change of a module along a morphism of schemes `U' ⟶ U` over a morphism of algebraic
spaces `f`: the pullback of `baseChangeModule N U p` is `baseChangeModule (f^* N) U' pU'`. -/
private theorem nonempty_pullback_baseChangeModule_iso {X X' : AlgebraicSpaces B S hS}
    (f : X' ⟶ X) (N : Modules.{u, u} B S hS X.1 X.2)
    (hN : Stacks.SheafOfModules.IsInvertible (structurePresheaf B S hS X.1)
      ((Stacks.SheafOfModules.Tensor.ringSheaf (smallEtaleRingedSite B S hS X.1 X.2).O)).property N)
    {U U' : BigFppfOver B S hS} (p : yoneda.obj U ⟶ X.1) (r : U' ⟶ U)
    (pU : yoneda.obj U' ⟶ X'.1) (h : yoneda.map r ≫ p = pU ≫ f.hom) :
    Nonempty ((Scheme.Modules.pullback ((BigFppfOver.toScheme B S hS).map r)).obj
      (baseChangeModule B S hS N U p) ≅
        baseChangeModule B S hS ((modulePullback B S hS f).obj N) U' pU) := by
  obtain ⟨e⟩ := nonempty_baseChangeModule_baseChange_of_isInvertible N hN U U' p r
  exact ⟨e.symm ≪≫ eqToIso (congrArg (baseChangeModule B S hS N U') h) ≪≫
    baseChangeModuleCompIso B S hS f N U' pU⟩

/-- **Stacks 09MT along a system of algebraic spaces which become schemes.** Let `E` be a
directed system of algebraic spaces with affine transition morphisms and compatible proper
morphisms `s_j : E_j ⟶ h_V` to an affine scheme `V`, with limit `cE`. Suppose that the stage
`E_{i₀}` is a scheme and that the underlying scheme functor preserves the limit of every lift of
the stages over `i₀` to the site (`hpres`). If an invertible module `N` on `E_{i₀}` pulls back to
a module ample relative to `cE.pt ⟶ h_V`, then its pullback to some stage `E_j`, `j ≥ i₀`, is
ample relative to `s_j`. -/
theorem exists_le_isRelativelyAmple_of_isRelativelyAmple_limit {V : BigFppfOver B S hS}
    (s : E ⟶ (Functor.const Iᵒᵖ).obj (yoneda.obj V))
    (hE : ∀ j : I, IsAlgebraicSpace B S hS (E.obj (op j)))
    (hEaff : ∀ {i j : Iᵒᵖ} (g : i ⟶ j), IsAffineHom B S hS (E.map g))
    (hs : ∀ j : I, IsProper B S hS (s.app (op j)))
    (hV : IsAffine ((BigFppfOver.toScheme B S hS).obj V))
    {cE : Cone E} (hcE : IsLimit cE) (hlim : IsAlgebraicSpace B S hS cE.pt)
    (i₀ : I) (hrep : (E.obj (op i₀)).IsRepresentable)
    (hpres : ∀ W : Over (op i₀) ⥤ BigFppfOver B S hS,
      Nonempty (W ⋙ yoneda ≅ Over.forget (op i₀) ⋙ E) →
        PreservesLimit W (BigFppfOver.toScheme B S hS))
    (N : Modules.{u, u} B S hS (E.obj (op i₀)) (hE i₀))
    (hN : Stacks.SheafOfModules.IsInvertible (structurePresheaf B S hS (E.obj (op i₀)))
      ((Stacks.SheafOfModules.Tensor.ringSheaf
        (smallEtaleRingedSite B S hS (E.obj (op i₀)) (hE i₀)).O)).property N)
    (hamp : IsRelativelyAmple B S hS
      (ObjectProperty.homMk (cE.π.app (op i₀) ≫ s.app (op i₀)) :
        (⟨cE.pt, hlim⟩ : AlgebraicSpaces B S hS) ⟶ representedAlgebraicSpace B S hS V)
      ((modulePullback B S hS (ObjectProperty.homMk (cE.π.app (op i₀)) :
        (⟨cE.pt, hlim⟩ : AlgebraicSpaces B S hS) ⟶ ⟨E.obj (op i₀), hE i₀⟩)).obj N)) :
    ∃ (j : I) (hj : i₀ ≤ j), IsRelativelyAmple B S hS
      (ObjectProperty.homMk (s.app (op j)) :
        (⟨E.obj (op j), hE j⟩ : AlgebraicSpaces B S hS) ⟶ representedAlgebraicSpace B S hS V)
      ((modulePullback B S hS (ObjectProperty.homMk (E.map (homOfLE hj).op) :
        (⟨E.obj (op j), hE j⟩ : AlgebraicSpaces B S hS) ⟶ ⟨E.obj (op i₀), hE i₀⟩)).obj N) := by
  have := hV
  -- the stages over `i₀`, lifted to the site
  let G : Over (op i₀) ⥤ (BigFppfOver B S hS)ᵒᵖ ⥤ Type u := Over.forget (op i₀) ⋙ E
  have hG : ∀ X : Over (op i₀), yoneda.essImage (G.obj X) := fun X =>
    have _ : (G.obj X).IsRepresentable := isRepresentable_obj_of_isAffineHom_map hE hEaff hrep X.hom
    ⟨(G.obj X).reprX, ⟨(G.obj X).reprW⟩⟩
  let W : Over (op i₀) ⥤ BigFppfOver B S hS := Functor.essImage.liftFunctor G yoneda hG
  let eW : W ⋙ yoneda ≅ G := Functor.essImage.liftFunctorCompIso G yoneda hG
  -- the limit is a scheme
  have _ : (((Functor.const Iᵒᵖ).obj (yoneda.obj V)).obj (op i₀)).IsRepresentable :=
    inferInstanceAs (yoneda.obj V).IsRepresentable
  have hlimrep : cE.pt.IsRepresentable :=
    Functor.isRepresentable_of_relativelyRepresentable_of_target_isRepresentable
      (cE.π.app (op i₀) ≫ s.app (op i₀)) hamp.1
  let Z : BigFppfOver B S hS := cE.pt.reprX
  let eZ : yoneda.obj Z ≅ cE.pt := cE.pt.reprW
  -- the cone of schemes of the site
  let cW : Cone W :=
    { pt := Z
      π :=
        { app := fun X => yoneda.preimage (eZ.hom ≫ cE.π.app X.left ≫ eW.inv.app X)
          naturality := fun X Y f => by
            apply yoneda.map_injective
            have h₁ := eW.inv.naturality f
            have h₂ := cE.w f.left
            simp only [Functor.const_obj_obj, Functor.const_obj_map, Category.id_comp,
              Functor.map_comp, Functor.map_preimage, Category.assoc]
            change _ = _ ≫ _ ≫ _ ≫ (W ⋙ yoneda).map f
            rw [← h₁]
            change _ = eZ.hom ≫ cE.π.app X.left ≫ E.map f.left ≫ eW.inv.app Y
            rw [reassoc_of% h₂] } }
  have hπ : ∀ X : Over (op i₀),
      yoneda.map (cW.π.app X) ≫ eW.hom.app X = eZ.hom ≫ cE.π.app X.left := fun X => by
    change yoneda.map (yoneda.preimage _) ≫ _ = _
    rw [Functor.map_preimage, Category.assoc, Category.assoc, Iso.inv_hom_id_app]
    exact congrArg (eZ.hom ≫ ·) (Category.comp_id _)
  have hcW : IsLimit cW := by
    have h₁ : IsLimit (cE.whisker (Over.forget (op i₀))) :=
      (Functor.Initial.isLimitWhiskerEquiv (Over.forget (op i₀)) cE).symm hcE
    have h₂ : IsLimit ((Cone.postcompose eW.hom).obj (yoneda.mapCone cW)) :=
      h₁.ofIsoLimit (Cone.ext eZ fun X => hπ X).symm
    exact isLimitOfReflects yoneda ((IsLimit.postcomposeHomEquiv eW _) h₂)
  have hsch : IsLimit ((BigFppfOver.toScheme B S hS).mapCone cW) :=
    have := hpres W ⟨eW⟩
    isLimitOfPreserves (BigFppfOver.toScheme B S hS) hcW
  -- the stages are quasi-compact, quasi-separated schemes with affine transition morphisms
  let D : Over (op i₀) ⥤ Scheme.{u} := W ⋙ BigFppfOver.toScheme B S hS
  have hDaff : ∀ {X Y : Over (op i₀)} (g : X ⟶ Y),
      _root_.AlgebraicGeometry.IsAffineHom (D.map g) := fun {X Y} g => by
    refine isAffineHom_toScheme_map_of_isAffineHom B S hS (W.map g) ?_
    have hnat : yoneda.map (W.map g) = eW.hom.app X ≫ E.map g.left ≫ eW.inv.app Y := by
      have := eW.hom.naturality g
      change yoneda.map (W.map g) ≫ eW.hom.app Y = eW.hom.app X ≫ E.map g.left at this
      rw [← reassoc_of% this, Iso.hom_inv_id_app]
      exact (Category.comp_id _).symm
    rw [hnat]
    exact isAffineHom_comp B S hS _ _ (isAffineHom_of_isIso _)
      (isAffineHom_comp B S hS _ _ (hEaff g.left) (isAffineHom_of_isIso _))
  have hDproper : ∀ X : Over (op i₀), ∃ σ : W.obj X ⟶ V,
      _root_.AlgebraicGeometry.IsProper ((BigFppfOver.toScheme B S hS).map σ) := fun X => by
    refine ⟨yoneda.preimage (eW.hom.app X ≫ s.app X.left), ?_⟩
    refine isProper_toScheme_map_of_isProper B S hS _ ?_
    rw [Functor.map_preimage]
    exact isProper_comp' B S hS _ _ (hE X.left.unop) (isAlgebraicSpace_yoneda B S hS V)
      (isProper_of_isIso B S hS _) (hs X.left.unop)
  have hDqc : ∀ X : Over (op i₀), CompactSpace (D.obj X) := fun X => by
    obtain ⟨σ, hσ⟩ := hDproper X
    exact QuasiCompact.compactSpace_of_compactSpace ((BigFppfOver.toScheme B S hS).map σ)
  have hDqs : ∀ X : Over (op i₀), QuasiSeparatedSpace (D.obj X) := fun X => by
    obtain ⟨σ, hσ⟩ := hDproper X
    exact quasiSeparatedSpace_of_quasiSeparated ((BigFppfOver.toScheme B S hS).map σ)
  -- the module on the scheme of the stage `i₀`
  let j₀ : Over (op i₀) := Over.mk (𝟙 (op i₀))
  let p₀ : yoneda.obj (W.obj j₀) ⟶ E.obj (op i₀) := eW.hom.app j₀
  let M : (D.obj j₀).Modules :=
    baseChangeModule B S hS (X := ⟨E.obj (op i₀), hE i₀⟩) N (W.obj j₀) p₀
  have hM : Stacks.Ample.IsInvertibleModule ((BigFppfOver.toScheme B S hS).obj (W.obj j₀))
      (baseChangeModule B S hS (X := ⟨E.obj (op i₀), hE i₀⟩) N (W.obj j₀) p₀) :=
    isInvertibleModule_baseChangeModule (X := ⟨E.obj (op i₀), hE i₀⟩) N hN
      (W.obj j₀) p₀
  -- its pullback to the limit is ample
  let q : Z ⟶ V := yoneda.preimage (eZ.hom ≫ cE.π.app (op i₀) ≫ s.app (op i₀))
  have hsq : IsPullback eZ.hom (yoneda.map q)
      (ObjectProperty.homMk (cE.π.app (op i₀) ≫ s.app (op i₀)) :
        (⟨cE.pt, hlim⟩ : AlgebraicSpaces B S hS) ⟶ representedAlgebraicSpace B S hS V).hom
      (𝟙 (yoneda.obj V)) :=
    IsPullback.of_horiz_isIso ⟨by
      rw [Functor.map_preimage, Category.comp_id]
      rfl⟩
  obtain ⟨hinvZ, hampZ⟩ := isAmple_baseChangeModule_of_isRelativelyAmple hamp V Z hV
    (𝟙 _) eZ.hom q hsq
  have hcomp : yoneda.map (cW.π.app j₀) ≫ p₀ = eZ.hom ≫ cE.π.app (op i₀) := hπ j₀
  obtain ⟨e⟩ := nonempty_pullback_baseChangeModule_iso (X := ⟨E.obj (op i₀), hE i₀⟩)
    (X' := ⟨cE.pt, hlim⟩) (U := W.obj j₀) (U' := Z)
    (ObjectProperty.homMk (cE.π.app (op i₀))) N hN p₀ (cW.π.app j₀) eZ.hom hcomp
  have hpullinv : Stacks.Ample.IsInvertibleModule ((BigFppfOver.toScheme B S hS).obj Z)
      ((Scheme.Modules.pullback ((BigFppfOver.toScheme B S hS).map (cW.π.app j₀))).obj M) :=
    Stacks.SheafOfModules.Invertible.isInvertible_of_iso _ _ e.symm
  have : AlgebraicGeometry.SheafOfModules.IsInvertible
      ((BigFppfOver.toScheme B S hS).mapCone cW).pt.toRingedSpace.presheaf
      (structureSheafRing ((BigFppfOver.toScheme B S hS).mapCone cW).pt.toRingedSpace).property
      ((Scheme.Modules.pullback (((BigFppfOver.toScheme B S hS).mapCone cW).π.app j₀)).obj M) :=
    hpullinv
  have : AlgebraicGeometry.SheafOfModules.IsInvertible (D.obj j₀).toRingedSpace.presheaf
      (structureSheafRing (D.obj j₀).toRingedSpace).property M := hM
  have hample : Scheme.Modules.IsAmple ((BigFppfOver.toScheme B S hS).mapCone cW).pt
      ((Scheme.Modules.pullback
        (((BigFppfOver.toScheme B S hS).mapCone cW).π.app j₀)).obj M) :=
    (Stacks.AmpleBridge.isAmple_iff_isAmple _ _).1
      ((Stacks.RelativeVeryAmple.isAmple_congr _ _ e).2 hampZ)
  -- Stacks 09MT
  obtain ⟨j', g, hj'⟩ :=
    Stacks.AlgebraicGeometry.AmpleLimit.exists_isAmple_pullback_map_of_isLimit_of_qcqs D
      ((BigFppfOver.toScheme B S hS).mapCone cW) hsch j₀ M hample
  -- back to the stage
  have hle : i₀ ≤ j'.left.unop := leOfHom j'.hom.unop
  refine ⟨j'.left.unop, hle, ?_⟩
  let N' := (modulePullback B S hS (ObjectProperty.homMk (E.map (homOfLE hle).op) :
    (⟨E.obj (op j'.left.unop), hE j'.left.unop⟩ : AlgebraicSpaces B S hS) ⟶
      ⟨E.obj (op i₀), hE i₀⟩)).obj N
  have hN' : Stacks.SheafOfModules.IsInvertible
      (structurePresheaf B S hS (E.obj (op j'.left.unop)))
      ((Stacks.SheafOfModules.Tensor.ringSheaf
        (smallEtaleRingedSite B S hS (E.obj (op j'.left.unop)) (hE j'.left.unop)).O)).property
      N' :=
    Stacks.SheafOfModules.isInvertible_pullbackModules_obj
      (f := smallEtaleRingedToposModulesHom B S hS
        (ObjectProperty.homMk (E.map (homOfLE hle).op) :
          (⟨E.obj (op j'.left.unop), hE j'.left.unop⟩ : AlgebraicSpaces B S hS) ⟶
            ⟨E.obj (op i₀), hE i₀⟩)) (L := N) (hL := hN)
  have hgl : g.left = (homOfLE hle).op := Subsingleton.elim _ _
  have hnat : yoneda.map (W.map g) ≫ p₀ = (eW.app j').hom ≫ E.map (homOfLE hle).op := by
    have := eW.hom.naturality g
    change yoneda.map (W.map g) ≫ eW.hom.app j₀ = (eW.app j').hom ≫ E.map g.left at this
    rw [← hgl]
    exact this
  obtain ⟨e'⟩ : Nonempty ((Scheme.Modules.pullback (D.map g)).obj M ≅
      baseChangeModule B S hS N' (W.obj j') (eW.app j').hom) :=
    nonempty_pullback_baseChangeModule_iso (X := ⟨E.obj (op i₀), hE i₀⟩)
    (X' := ⟨E.obj (op j'.left.unop), hE j'.left.unop⟩)
    (U := W.obj j₀) (U' := W.obj j')
    (ObjectProperty.homMk (E.map (homOfLE hle).op)) N hN p₀ (W.map g) (eW.app j').hom hnat
  have hinv' : Stacks.Ample.IsInvertibleModule (D.obj j')
      (baseChangeModule B S hS (X := ⟨E.obj (op j'.left.unop), hE j'.left.unop⟩) N' (W.obj j')
        ((eW.app j').hom)) :=
    isInvertibleModule_baseChangeModule
      (X := ⟨E.obj (op j'.left.unop), hE j'.left.unop⟩) N' hN' (W.obj j') ((eW.app j').hom)
  have hpullinv' : Stacks.Ample.IsInvertibleModule (D.obj j')
      ((Scheme.Modules.pullback (D.map g)).obj M) :=
    Stacks.SheafOfModules.Invertible.isInvertible_of_iso _ _ e'.symm
  have hamp' : Stacks.Ample.IsAmple (D.obj j')
      (baseChangeModule B S hS (X := ⟨E.obj (op j'.left.unop), hE j'.left.unop⟩) N' (W.obj j')
        ((eW.app j').hom)) :=
    (Stacks.RelativeVeryAmple.isAmple_congr _ _ e').1
      ((Stacks.AmpleBridge.isAmple_iff_isAmple _ _).2 hj')
  -- Stacks 0D32
  refine isRelativelyAmple_of_exists_scheme _ N' hN' V (Iso.refl _)
    ⟨W.obj j', eW.app j', hinv', ?_⟩
  exact (@Stacks.RelativeAmpleAffineBase.isRelativelyAmple_iff_isAmple _ _ _ _ _ hinv').2 hamp'

end AlgebraicGeometry.Space

end
