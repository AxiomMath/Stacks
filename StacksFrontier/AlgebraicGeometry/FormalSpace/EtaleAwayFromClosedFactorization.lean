module

public import StacksFrontier.AlgebraicGeometry.FormalSpace.Completion
public import StacksFrontier.AlgebraicGeometry.FormalSpace.MorphismUniquenessAlongClosedSubset
public import StacksFrontier.AlgebraicGeometry.Spaces.EtalePushoutAlgebraic
public import StacksFrontier.AlgebraicGeometry.Spaces.ImmersionBaseChange
public import StacksFrontier.AlgebraicGeometry.Spaces.OpenSubspaceCorrespondence
import all StacksFrontier.AlgebraicGeometry.Spaces.ElementaryDistinguishedSquareGluing

/-!
# Modifying a morphism étale away from a closed subset

Let `S` be a scheme contained in a big fppf site `B`, let `X` be an algebraic space over `S` and
let `T ⊆ |X|` be a closed subset, with open complement `U = X ∖ T`. A morphism `f : X' ⟶ X`
which is locally of finite type and étale over `U` factors as `X' ⟶ X'' ⟶ X`, where `X'' ⟶ X` is
locally of finite type and an isomorphism over `U`, and `X' ⟶ X''` induces an isomorphism of
completions `X'_{/T} ⟶ X''_{/T}`. The space `X''` is the pushout `X' ⨿_{U'} U` of the open
immersion `U' ⟶ X'` and the étale morphism `U' ⟶ U`, where `U' = X' ×_X U`.

## Main results

* `AlgebraicGeometry.FormalSpace.exists_factorization_isIso_completionSheafMap`: a morphism of
  algebraic spaces, locally of finite type and étale away from a closed subset `T`, factors
  through a morphism that is an isomorphism away from `T` by a morphism inducing an isomorphism
  of completions along `T`.

## References

* [Stacks Project, Tag 0AR9](https://stacks.math.columbia.edu/tag/0AR9)
* [Stacks Project, Tag 0AMC](https://stacks.math.columbia.edu/tag/0AMC)
* [Stacks Project, Tag 02WR](https://stacks.math.columbia.edu/tag/02WR)
* [Stacks Project, Tag 03BZ](https://stacks.math.columbia.edu/tag/03BZ)
* [Stacks Project, Tag 04S6](https://stacks.math.columbia.edu/tag/04S6)
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits Opposite

universe u

namespace AlgebraicGeometry.FormalSpace

variable (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)

attribute [local instance] Space.pointTopology

/-- A morphism of sheaves whose underlying morphism of presheaves is an isomorphism is an
isomorphism. -/
private theorem isIso_homMk_of_isIso {C : Type*} [Category* C] {J : GrothendieckTopology C}
    {D : Type*} [Category* D] {X Y : Sheaf J D} (φ : X.obj ⟶ Y.obj) (_ : IsIso φ) :
    IsIso (ObjectProperty.homMk φ : X ⟶ Y) :=
  ⟨⟨ObjectProperty.homMk (inv φ), ObjectProperty.hom_ext _ (by simp),
    ObjectProperty.hom_ext _ (by simp)⟩⟩

/-! ### Lifting sections with image in the closed set -/

set_option synthInstance.maxHeartbeats 400000 in
-- instance search for limits of sheaves on the big fppf site is slow
/-- Pullbacks of fppf sheaves of sets, supplied directly (instance search times out). -/
local instance hasPullbacks_sheaf_etaleAwayFromClosedFactorization :
    HasPullbacks (Sheaf (BigFppfOver.topology B S hS) (Type u)) :=
  inferInstance

local instance (priority := high) hasPullback_sheaf_etaleAwayFromClosedFactorization
    {X Y Z : Sheaf (BigFppfOver.topology B S hS) (Type u)} (f : X ⟶ Z) (g : Y ⟶ Z) :
    HasLimit (cospan f g) :=
  HasLimitsOfShape.has_limit _

set_option synthInstance.maxHeartbeats 400000 in
-- instance search for strict initial objects of sheaves on the big fppf site is slow
/-- Strict initial objects of fppf sheaves of sets (instance search times out). -/
local instance (priority := high)
    hasStrictInitialObjects_sheaf_etaleAwayFromClosedFactorization :
    HasStrictInitialObjects (Sheaf (BigFppfOver.topology B S hS) (Type u)) := inferInstance

set_option synthInstance.maxHeartbeats 400000 in
-- instance search for limits of presheaves on the big fppf site is slow
/-- Pullbacks of presheaves on the big fppf site (instance search times out). -/
local instance hasPullbacks_presheaf_etaleAwayFromClosedFactorization :
    HasPullbacks ((BigFppfOver B S hS)ᵒᵖ ⥤ Type u) := inferInstance

local instance (priority := high) hasPullback_presheaf_etaleAwayFromClosedFactorization
    {X Y Z : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u} (f : X ⟶ Z) (g : Y ⟶ Z) :
    HasLimit (cospan f g) :=
  HasLimitsOfShape.has_limit _

/-- Let `Q` be the pushout of a monomorphism `a : A ⟶ F` and a morphism `b : A ⟶ V` of fppf
sheaves of sets, with legs `g` and `i`, where `V` and `Q` are algebraic spaces, and let `T` be
a set of points of `Q` which meets no point coming from `V`. Then a section of `Q` with
point-set image in `T` lifts uniquely along `g`. -/
private theorem existsUnique_app_eq_of_hasImageIn
    {A F V Q : Sheaf (BigFppfOver.topology B S hS) (Type u)} {a : A ⟶ F} {b : A ⟶ V}
    {g : F ⟶ Q} {i : V ⟶ Q} [Mono a] (h : IsPushout a b g i)
    (hV : IsAlgebraicSpace B S hS V.obj) (hQ : IsAlgebraicSpace B S hS Q.obj)
    (T : Set (Space.points B S hS Q.obj))
    (hd : ∀ v, Space.pointsMap B S hS V.obj i.hom v ∉ T)
    (W : BigFppfOver B S hS) (y : Q.obj.obj (op W))
    (hy : Space.HasImageIn B S hS Q.obj T W y) :
    ∃! x : F.obj.obj (op W), g.hom.app (op W) x = y := by
  let Wsh : Sheaf (BigFppfOver.topology B S hS) (Type u) :=
    ⟨yoneda.obj W, BigFppfOver.isSheaf_yoneda_obj B S hS W⟩
  let ys : Wsh ⟶ Q := ObjectProperty.homMk (yonedaEquiv.symm y)
  have hPi : IsPullback (pullback.fst ys i).hom (pullback.snd ys i).hom ys.hom i.hom :=
    (IsPullback.of_hasPullback ys i).map (sheafToPresheaf (BigFppfOver.topology B S hS) (Type u))
  have hPialg : IsAlgebraicSpace B S hS (pullback ys i).obj :=
    isAlgebraicSpace_of_iso B S hS hPi.isoPullback
      (isAlgebraicSpace_pullback B S hS ys.hom i.hom (isAlgebraicSpace_yoneda B S hS W) hV hQ)
  have hempty : IsEmpty (Space.points B S hS (pullback ys i).obj) := by
    refine ⟨fun τ ↦ hd (Space.pointsMap B S hS _ (pullback.snd ys i).hom τ) ?_⟩
    rw [← Space.pointsMap_comp_apply, ← hPi.w, Space.pointsMap_comp_apply]
    exact (Space.hasImageIn_iff_range_subset B S hS T W y).mp hy ⟨_, rfl⟩
  have hinit : IsInitial (pullback ys i) :=
    Space.isInitial_sheaf_of_isEmpty_points B S hS ⟨_, hPialg⟩ hempty
  have : IsIso (pullback.fst ys g) := Space.isIso_pullback_of_initial_other_leg a b g i h ys
    (pullback.fst ys g) (pullback.snd ys g) (pullback.fst ys i) (pullback.snd ys i)
    (IsPullback.of_hasPullback ys g) (IsPullback.of_hasPullback ys i) hinit
  let xs : Wsh ⟶ F := inv (pullback.fst ys g) ≫ pullback.snd ys g
  have hxs : xs ≫ g = ys := by
    rw [Category.assoc, ← pullback.condition, IsIso.inv_hom_id_assoc]
  refine ⟨yonedaEquiv xs.hom, ?_, fun x hx ↦ ?_⟩
  · change g.hom.app (op W) (yonedaEquiv xs.hom) = y
    rw [← yonedaEquiv_comp]
    exact (congrArg (fun k ↦ yonedaEquiv k.hom) hxs).trans (Equiv.apply_symm_apply _ _)
  · let xh : Wsh ⟶ F := ObjectProperty.homMk (yonedaEquiv.symm x)
    have hxh : xh ≫ g = ys := ObjectProperty.hom_ext _ (by
      change yonedaEquiv.symm x ≫ g.hom = yonedaEquiv.symm y
      rw [yonedaEquiv_symm_naturality_right, hx])
    let l : Wsh ⟶ pullback ys g := pullback.lift (𝟙 Wsh) xh (by rw [Category.id_comp, hxh])
    have hl : l = inv (pullback.fst ys g) :=
      IsIso.eq_inv_of_inv_hom_id (pullback.lift_fst _ _ _)
    have hxl : xh = xs := by
      rw [← pullback.lift_snd (𝟙 Wsh) xh (by rw [Category.id_comp, hxh])]
      change l ≫ _ = _
      rw [hl]
    rw [← hxl]
    exact (Equiv.apply_symm_apply _ x).symm

/-- In the situation of `existsUnique_app_eq_of_hasImageIn`, the leg `g` induces an
isomorphism of the subfunctors of sections with point-set image in `T`. -/
private theorem isIso_completionMap_of_isPushout
    {A F V Q : Sheaf (BigFppfOver.topology B S hS) (Type u)} {a : A ⟶ F} {b : A ⟶ V}
    {g : F ⟶ Q} {i : V ⟶ Q} [Mono a] (h : IsPushout a b g i)
    (hV : IsAlgebraicSpace B S hS V.obj) (hQ : IsAlgebraicSpace B S hS Q.obj)
    (T : Set (Space.points B S hS Q.obj))
    (hd : ∀ v, Space.pointsMap B S hS V.obj i.hom v ∉ T) :
    IsIso (Space.completionMap B S hS g.hom T) := by
  have hlift := existsUnique_app_eq_of_hasImageIn B S hS h hV hQ T hd
  have hW : ∀ W, IsIso ((Space.completionMap B S hS g.hom T).app W) := by
    intro W
    rw [isIso_iff_bijective]
    refine ⟨fun x₁ x₂ hx ↦ ?_, fun y ↦ ?_⟩
    · have hx' : g.hom.app W x₁.1.down = g.hom.app W x₂.1.down :=
        congrArg (fun z ↦ z.1.down) hx
      obtain ⟨x, -, huniq⟩ := hlift W.unop (g.hom.app W x₁.1.down)
        ((Space.completionMap B S hS g.hom T).app W x₁).2
      exact Subtype.ext (ULift.ext ((huniq _ rfl).trans (huniq _ hx'.symm).symm))
    · obtain ⟨x, hx, -⟩ := hlift W.unop y.1.down y.2
      have hxg : yonedaEquiv.symm x ≫ g.hom = yonedaEquiv.symm y.1.down :=
        by rw [yonedaEquiv_symm_naturality_right, hx]
      have hmem : Space.HasImageIn B S hS F.obj (Space.pointsMap B S hS F.obj g.hom ⁻¹' T)
          W.unop x := by
        rw [Space.hasImageIn_iff_range_subset]
        rintro _ ⟨w, rfl⟩
        change Space.pointsMap B S hS F.obj g.hom
          (Space.pointsMap B S hS _ (yonedaEquiv.symm x) w) ∈ T
        rw [← Space.pointsMap_comp_apply, hxg]
        exact (Space.hasImageIn_iff_range_subset B S hS T W.unop y.1.down).mp y.2 ⟨w, rfl⟩
      exact ⟨⟨⟨x⟩, hmem⟩, Subtype.ext (ULift.ext hx)⟩
  exact NatIso.isIso_of_isIso_app _

/-! ### The factorization -/

/-- Let `X` be an algebraic space over `S`, let `T ⊆ |X|` be closed with open
complement `U = X ∖ T`, and let `f : X' ⟶ X` be a morphism of algebraic spaces which is locally
of finite type and étale over `U`. Then `f` factors as `X' ⟶ X'' ⟶ X` where `X'' ⟶ X` is locally
of finite type and an isomorphism over `U`, and `X' ⟶ X''` induces an isomorphism
`X'_{/T} ⟶ X''_{/T}` of completions.

Here `U` is the open subspace with point set `Tᶜ`, and "over `U`" is the base change along its
inclusion. -/
@[stacks 0AR9]
theorem exists_factorization_isIso_completionSheafMap
    {X X' : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u}
    (hX : IsAlgebraicSpace B S hS X) (hX' : IsAlgebraicSpace B S hS X')
    (T : Set (Space.points B S hS X)) (hT : IsClosed T)
    (f : X' ⟶ X) (hf : Space.IsLocallyOfFiniteType B S hS f)
    (hfU : Space.IsEtale B S hS (pullback.snd f
      ((Space.openSubspacesOrderIso B S hS X hX).symm ⟨Tᶜ, hT.isOpen_compl⟩).1.ι)) :
    ∃ (X'' : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u) (_ : IsAlgebraicSpace B S hS X'')
      (g : X' ⟶ X'') (p : X'' ⟶ X),
      g ≫ p = f ∧ Space.IsLocallyOfFiniteType B S hS p ∧
        IsIso (pullback.snd p
          ((Space.openSubspacesOrderIso B S hS X hX).symm ⟨Tᶜ, hT.isOpen_compl⟩).1.ι) ∧
        IsIso (Space.completionSheafMap B S hS g (Space.pointsMap B S hS X'' p ⁻¹' T)) := by
  classical
  let J := BigFppfOver.topology B S hS
  set Uo := (Space.openSubspacesOrderIso B S hS X hX).symm ⟨Tᶜ, hT.isOpen_compl⟩ with hUo
  have hUrange : Set.range (Space.pointsMap B S hS Uo.1.toFunctor Uo.1.ι) = Tᶜ := by
    rw [← Space.openSubspacesOrderIso_apply B S hS X hX Uo, hUo]
    simp
  have hUalg : IsAlgebraicSpace B S hS Uo.1.toFunctor := Uo.2.1
  have hAalg : IsAlgebraicSpace B S hS (pullback f Uo.1.ι) :=
    isAlgebraicSpace_pullback B S hS f Uo.1.ι hX' hUalg hX
  let F : Sheaf (BigFppfOver.topology B S hS) (Type u) := ⟨X', hX'.isSheaf⟩
  let H : Sheaf (BigFppfOver.topology B S hS) (Type u) := ⟨X, hX.isSheaf⟩
  let V : Sheaf (BigFppfOver.topology B S hS) (Type u) := ⟨Uo.1.toFunctor, hUalg.isSheaf⟩
  let A : Sheaf (BigFppfOver.topology B S hS) (Type u) := ⟨pullback f Uo.1.ι, hAalg.isSheaf⟩
  let fs : F ⟶ H := ObjectProperty.homMk f
  let iH : V ⟶ H := ObjectProperty.homMk Uo.1.ι
  let a : A ⟶ F := ObjectProperty.homMk (pullback.fst f Uo.1.ι)
  let b : A ⟶ V := ObjectProperty.homMk (pullback.snd f Uo.1.ι)
  have hAP : IsPullback a b fs iH :=
    IsPullback.of_map_of_faithful (sheafToPresheaf (BigFppfOver.topology B S hS) (Type u))
      (IsPullback.of_hasPullback f Uo.1.ι)
  have ha : Space.IsOpenImmersion B S hS a.hom :=
    Space.isOpenImmersion_of_isPullback B S hS
      (F := ⟨Uo.1.toFunctor, hUalg⟩) (G := ⟨X', hX'⟩) (H := ⟨X, hX⟩) (P := ⟨_, hAalg⟩)
      (f := ObjectProperty.homMk Uo.1.ι) (g := ObjectProperty.homMk f)
      (fst := ObjectProperty.homMk (pullback.snd f Uo.1.ι))
      (snd := ObjectProperty.homMk (pullback.fst f Uo.1.ι))
      (IsPullback.of_map_of_faithful (ObjectProperty.ι _)
        (IsPullback.of_hasPullback f Uo.1.ι).flip) Uo.2.2
  have hiHmono : Mono iH :=
    Functor.mono_of_mono_map (sheafToPresheaf (BigFppfOver.topology B S hS) (Type u))
      (show Mono Uo.1.ι from inferInstance)
  have : Mono a := Functor.mono_of_mono_map (sheafToPresheaf (BigFppfOver.topology B S hS) (Type u))
    (Space.mono_of_isOpenImmersion B S hS _ ha)
  have hpo := IsPushout.of_hasPushout a b
  let g : F ⟶ pushout a b := pushout.inl a b
  let i : V ⟶ pushout a b := pushout.inr a b
  obtain ⟨hQ, hqEt, hqSurj⟩ :=
    Space.isAlgebraicSpace_of_isPushout_of_isOpenImmersion_of_isEtale B S hS hpo hAalg hX' hUalg
      ha hfU
  let p : pushout a b ⟶ H := pushout.desc fs iH hAP.w
  have hgp : g ≫ p = fs := pushout.inl_desc _ _ _
  have hip : i ≫ p = iH := pushout.inr_desc _ _ _
  refine ⟨(pushout a b).obj, hQ, g.hom, p.hom, congrArg (fun k ↦ k.hom) hgp, ?_, ?_, ?_⟩
  · have hY : IsAlgebraicSpace B S hS (F ⨿ V).obj :=
      Space.isAlgebraicSpace_binaryCoproduct B S hS hX' hUalg coprod.inl coprod.inr
        (coprodIsCoprod _ _)
    refine Space.isLocallyOfFiniteType_of_comp_of_isEtale_of_isSurjective B S hS hY hQ hX
      hqEt hqSurj ?_
    refine Space.isLocallyOfFiniteType_of_isColimit_binaryCofan B S hS hX' hUalg hY hX
      coprod.inl coprod.inr (coprodIsCoprod _ _) _ ?_ ?_
    · change Space.IsLocallyOfFiniteType B S hS ((coprod.inl ≫ coprod.desc g i ≫ p).hom)
      rw [coprod.inl_desc_assoc, hgp]
      exact hf
    · change Space.IsLocallyOfFiniteType B S hS ((coprod.inr ≫ coprod.desc g i ≫ p).hom)
      rw [coprod.inr_desc_assoc, hip]
      exact Space.isLocallyOfFiniteType_of_isEtale' B S hS _
        (Space.isEtale_of_isOpenImmersion B S hS Uo.2.2)
  · have hsq := (Adhesive.isPullback_inr_of_isPushout hpo hAP p hgp hip).map
      (sheafToPresheaf (BigFppfOver.topology B S hS) (Type u))
    have he : (pullback.snd p.hom Uo.1.ι) = hsq.isoPullback.inv ≫ 𝟙 _ :=
      (Iso.eq_inv_comp _).mpr hsq.isoPullback_hom_snd
    rw [he]
    infer_instance
  · have hd : ∀ v, Space.pointsMap B S hS V.obj i.hom v ∉
        Space.pointsMap B S hS (pushout a b).obj p.hom ⁻¹' T := by
      intro v hv
      rw [Set.mem_preimage, ← Space.pointsMap_comp_apply] at hv
      have hv' : Space.pointsMap B S hS V.obj Uo.1.ι v ∈ Tᶜ := hUrange ▸ ⟨v, rfl⟩
      exact hv' (by rwa [show i.hom ≫ p.hom = Uo.1.ι from congrArg (fun k ↦ k.hom) hip]
        at hv)
    have hmap := isIso_completionMap_of_isPushout B S hS hpo hUalg hQ _ hd
    have hη : IsIso ((J.sheafification (Type (u + 1))).map (Space.completionMap B S hS g.hom
        (Space.pointsMap B S hS (pushout a b).obj p.hom ⁻¹' T))) := inferInstance
    exact isIso_homMk_of_isIso _ hη

end AlgebraicGeometry.FormalSpace

end
