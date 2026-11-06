module

public import StacksFrontier.AlgebraicGeometry.MoreMorphisms.SteinFactorization.ClopenFibreSpreadingIntegral
public import StacksFrontier.AlgebraicGeometry.Spaces.ProperConnectedGeometricFibres

/-!
# Connected fibres of a proper morphism with `f_* 𝒪_X = 𝒪_Y` over an arbitrary base

Let `f : X ⟶ Y` be a proper surjective morphism of algebraic spaces over `S` whose structure map
`𝒪_Y ⟶ f_* 𝒪_X` is an isomorphism.  Then every geometric fibre of `f` is connected.

`StacksFrontier.AlgebraicGeometry.Spaces.ProperConnectedFibresOverAffine` and
`StacksFrontier.AlgebraicGeometry.Spaces.ProperConnectedGeometricFibres` prove this for a locally
Noetherian `Y`.  Local Noetherianity enters their argument at exactly one place: the spreading
of a clopen split of a fibre of the proper morphism of schemes `V ⟶ T` from a Chow cover `V` of
`X` over an affine chart `T` of `Y`,
`Stacks.SteinFactorization.exists_etaleNeighborhood_isClopen_of_isProper`.
Over an affine base that spreading holds with no Noetherian hypothesis,
`Stacks.SteinFactorization.exists_etaleNeighborhood_isClopen_of_isProper_of_isAffine`, and the
three statements below are the ones of those two files with that lemma substituted; the rest
of each argument is unchanged.

## Main results

* `AlgebraicGeometry.Space.isPreconnected_fibre_of_isProper_of_isIso_fSharp_of_isAffine`: the
  fibres over the points of an affine scheme of the site are preconnected.
* `AlgebraicGeometry.Space.isPreconnected_fibre_of_isProper_of_isIso_fSharp_of_scheme`:
  the same over an arbitrary scheme of the site.
* `AlgebraicGeometry.Space.connectedPullback_of_isProper_of_isSurjective_of_isIso_fSharp`: every
  geometric fibre of a proper surjective morphism with `f_* 𝒪_X = 𝒪_Y` is connected.

## References

* [Stacks Project, Tag 0A1C](https://stacks.math.columbia.edu/tag/0A1C)
* [Stacks Project, Tag 0A1A](https://stacks.math.columbia.edu/tag/0A1A)
* [Stacks Project, Tag 089J](https://stacks.math.columbia.edu/tag/089J)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits Opposite

universe u

namespace AlgebraicGeometry.Space

attribute [local instance] pointTopology

variable {B : BigFppfSite.{u}} {S : Scheme.{u}} {hS : B.Contains S}

/-- A point of `X` lying over the image of a point `u` of `T₂` under `ν : T₂ ⟶ T` lifts to a point
of the base change of `f : X ⟶ T` along `ν` lying over `u`. -/
theorem exists_pullback_point_of_pointsToScheme_eq {T T₂ : BigFppfOver B S hS}
    {X : AlgebraicSpaces B S hS} (f : X ⟶ schemeSpace T) (ν : T₂ ⟶ T)
    {x : points B S hS X.obj} {u : (BigFppfOver.toScheme B S hS).obj T₂}
    (hx : pointsToScheme B S hS T (pointsMap B S hS X.obj f.hom x) =
      (BigFppfOver.toScheme B S hS).map ν u) :
    ∃ y : points B S hS (pullback f (schemeSpaceMap ν)).obj,
      pointsMap B S hS _ (pullback.fst f (schemeSpaceMap ν)).hom y = x ∧
      pointsToScheme B S hS T₂
        (pointsMap B S hS _ (pullback.snd f (schemeSpaceMap ν)).hom y) = u := by
  obtain ⟨p, hp⟩ := surjective_pointsToScheme B S hS T₂ u
  have hcomp : pointsMap B S hS X.obj f.hom x =
      pointsMap B S hS (schemeSpace T₂).obj (schemeSpaceMap ν).hom p :=
    injective_pointsToScheme B S hS T (hx.trans ((congrArg _ hp).symm.trans
      (pointsToScheme_pointsMap_yoneda B S hS ν p).symm))
  obtain ⟨y, hy₁, hy₂⟩ := exists_point_of_isPullback B S hS
    (IsPullback.of_hasPullback f (schemeSpaceMap ν)) x p hcomp
  exact ⟨y, hy₁, (congrArg (pointsToScheme B S hS T₂) hy₂).trans hp⟩

/-- If `ρ ≫ f = yoneda.map m`, then the point of `T` below the image in `F` of a scheme point `v`
of `V` is the image of `v` under `m`. -/
theorem pointsToScheme_pointsMap_pointsEquivScheme_symm {V T : BigFppfOver B S hS}
    {F : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u} (ρ : yoneda.obj V ⟶ F) (f : F ⟶ yoneda.obj T)
    (m : V ⟶ T) (hm : ρ ≫ f = yoneda.map m) (v : (BigFppfOver.toScheme B S hS).obj V) :
    pointsToScheme B S hS T (pointsMap B S hS F f
      (pointsMap B S hS (yoneda.obj V) ρ ((pointsEquivScheme B S hS V).symm v))) =
      (BigFppfOver.toScheme B S hS).map m v := by
  have h₁ : pointsMap B S hS F f
      (pointsMap B S hS (yoneda.obj V) ρ ((pointsEquivScheme B S hS V).symm v)) =
      pointsMap B S hS (yoneda.obj V) (yoneda.map m) ((pointsEquivScheme B S hS V).symm v) :=
    (congrFun (pointsMap_comp B S hS _ ρ f) _).symm.trans
      (congrArg (fun k => pointsMap B S hS (yoneda.obj V) k
        ((pointsEquivScheme B S hS V).symm v)) hm)
  refine (congrArg (pointsToScheme B S hS T) h₁).trans ?_
  rw [pointsToScheme_pointsMap_yoneda]
  congr 1
  exact (pointsEquivScheme B S hS V).apply_symm_apply v

/-- The scheme map of the site corresponding to an étale morphism `ν` is flat. -/
private theorem isFlat_schemeSpaceMap_of_etale {T T₂ : BigFppfOver B S hS} (ν : T₂ ⟶ T)
    (hνet : Etale ((BigFppfOver.toScheme B S hS).map ν)) :
    IsFlat B S hS (schemeSpaceMap ν).hom :=
  isFlat_of_presheafEtale B S hS ((presheaf_yoneda_map_iff B S hS
    AlgebraicGeometry.Etale.etale_isStableUnderBaseChange ν).2 hνet)

/-- `f_* 𝒪 = 𝒪` is preserved by the base change of a proper morphism along a flat morphism. -/
private theorem isIso_fSharp_pullback_snd_of_isFlat {X Y Z : AlgebraicSpaces B S hS}
    (f : X ⟶ Y) (hf : IsProper B S hS f.hom) (g : Z ⟶ Y) (hg : IsFlat B S hS g.hom)
    [IsIso (smallEtaleRingedToposHom B S hS f).fSharp] :
    IsIso (smallEtaleRingedToposHom B S hS (pullback.snd f g)).fSharp :=
  isIso_fSharp_of_isPullback_of_isFlat (IsPullback.of_hasPullback f g) hf.2.1.2
    (isQuasiSeparated_of_isSeparated B S hS hf.1) hg

/-- **The fibres of a proper morphism with `f_* 𝒪_X = 𝒪_T` over an affine scheme of the site are
preconnected.**  Let `T` be an object of the big fppf site of `S` with affine scheme, and let
`f : X ⟶ T` be proper with `𝒪_T ⟶ f_* 𝒪_X` an isomorphism.  Then for every point `t` of `T` the
fibre `{x ∈ |X| : f(x) = t}` is preconnected.

This is `AlgebraicGeometry.Space.isPreconnected_fibre_of_isProper_of_isIso_fSharp` without its
locally Noetherian hypothesis on `T`: a split of the fibre pulls back to a Chow cover `V`, is
spread out over an étale neighbourhood of `t` by
`Stacks.SteinFactorization.exists_etaleNeighborhood_isClopen_of_isProper_of_isAffine`, pushed
back down to `X` and contradicted by `f_* 𝒪 = 𝒪`. -/
theorem isPreconnected_fibre_of_isProper_of_isIso_fSharp_of_isAffine
    {T : BigFppfOver B S hS}
    [IsAffine ((BigFppfOver.toScheme B S hS).obj T)]
    {X : AlgebraicSpaces B S hS} (f : X ⟶ schemeSpace T) (hf : IsProper B S hS f.hom)
    [IsIso (smallEtaleRingedToposHom B S hS f).fSharp]
    (t : (BigFppfOver.toScheme B S hS).obj T) :
    IsPreconnected {x : points B S hS X.obj |
      pointsToScheme B S hS T (pointsMap B S hS X.obj f.hom x) = t} := by
  classical
  rw [isPreconnected_iff_subset_of_disjoint_closed]
  intro P₀ Q₀ hP₀ hQ₀ hcov hdisj
  by_contra hcon
  rw [not_or, Set.not_subset, Set.not_subset] at hcon
  obtain ⟨⟨x₁, hx₁F, hx₁P⟩, ⟨x₂, hx₂F, hx₂Q⟩⟩ := hcon
  have hx₂P : x₂ ∈ P₀ := (hcov hx₂F).resolve_right hx₂Q
  let Tsch := (BigFppfOver.toScheme B S hS).obj T
  -- Chow's lemma
  obtain ⟨V, ρ, hρP, hρS⟩ := exists_properSurjective_schemeCover_of_isProper_toAffine B S hS T
    inferInstance X.property f.hom hf
  have hT := isAlgebraicSpace_yoneda B S hS T
  have hVsp := isAlgebraicSpace_yoneda B S hS V
  let m : V ⟶ T := yoneda.preimage (ρ ≫ f.hom)
  have hm : yoneda.map m = ρ ≫ f.hom := yoneda.map_preimage _
  have hcompP : IsProper B S hS (ρ ≫ f.hom) :=
    isProper_comp B S hS hVsp X.property hT ρ f.hom hρP hf
  have hmProper : AlgebraicGeometry.IsProper ((BigFppfOver.toScheme B S hS).map m) := by
    have hpre : (MorphismProperty.inverseImage
        (@_root_.AlgebraicGeometry.IsProper.{u} : MorphismProperty Scheme.{u})
        (BigFppfOver.toScheme B S hS)).presheaf (yoneda.map m) := by
      rw [hm]
      exact (presheaf_isProper_iff B S hS (ρ ≫ f.hom) hVsp hT
        (by rw [← hm]; exact Functor.relativelyRepresentable.map yoneda m)).mp hcompP
    change (MorphismProperty.inverseImage
      (@_root_.AlgebraicGeometry.IsProper.{u} : MorphismProperty Scheme.{u})
      (BigFppfOver.toScheme B S hS)).relative yoneda (yoneda.map m) at hpre
    have hpm := MorphismProperty.of_relative_map hpre
    exact hpm
  -- the scheme points of `V` read in `X`
  let ψ : (BigFppfOver.toScheme B S hS).obj V → points B S hS X.obj := fun v =>
    pointsMap B S hS (yoneda.obj V) ρ ((pointsEquivScheme B S hS V).symm v)
  have hψc : Continuous ψ :=
    (continuous_pointsMap B S hS ρ).comp (continuous_pointsEquivScheme_symm V)
  have hψT : ∀ v, pointsToScheme B S hS T (pointsMap B S hS X.obj f.hom (ψ v)) =
      (BigFppfOver.toScheme B S hS).map m v :=
    pointsToScheme_pointsMap_pointsEquivScheme_symm ρ f.hom m hm.symm
  let P : Set ((BigFppfOver.toScheme B S hS).obj V) := ψ ⁻¹' P₀
  let Q : Set ((BigFppfOver.toScheme B S hS).obj V) := ψ ⁻¹' Q₀
  have hcov' : (BigFppfOver.toScheme B S hS).map m ⁻¹' {t} ⊆ P ∪ Q :=
    fun v hv => hcov ((hψT v).trans hv)
  have hdisj' : (BigFppfOver.toScheme B S hS).map m ⁻¹' {t} ∩ (P ∩ Q) = ∅ := by
    ext v
    simp only [Set.mem_inter_iff, Set.mem_preimage, Set.mem_singleton_iff, Set.mem_empty_iff_false,
      iff_false, not_and]
    intro hv hvP hvQ
    exact hdisj.subset ⟨(hψT v).trans hv, hvP, hvQ⟩
  -- spread the split of the fibre of `V ⟶ T` over an étale neighbourhood
  obtain ⟨U, -, A, hA, hAp⟩ :=
    Stacks.SteinFactorization.exists_etaleNeighborhood_isClopen_of_isProper_of_isAffine
    ((BigFppfOver.toScheme B S hS).map m) t P Q (hP₀.preimage hψc) (hQ₀.preimage hψc) hcov' hdisj'
  obtain ⟨Zu, ν, κ, u', -, hκ, hκν, hνet, hκu, hνu⟩ :=
    exists_affine_siteObject_of_etaleNeighborhood B S hS (inferInstance : IsAffine Tsch) U
  -- the base change of `f` to `Zu`
  have hflat := isFlat_schemeSpaceMap_of_etale ν hνet
  let sq := IsPullback.of_hasPullback f (schemeSpaceMap ν)
  let X' := Limits.pullback f (schemeSpaceMap ν)
  let j := pullback.fst f (schemeSpaceMap ν)
  let g := pullback.snd f (schemeSpaceMap ν)
  have hfqc : IsQuasiCompact B S hS f.hom := hf.2.1.2
  have hfqs : IsQuasiSeparated B S hS f.hom := isQuasiSeparated_of_isSeparated B S hS hf.1
  have : IsIso (smallEtaleRingedToposHom B S hS g).fSharp :=
    isIso_fSharp_pullback_snd_of_isFlat f hf _ hflat
  have sqP : IsPullback j.hom g.hom f.hom (yoneda.map ν) := sq.map (ObjectProperty.ι _)
  have hZu := isAlgebraicSpace_yoneda B S hS Zu
  have hgqc : IsQuasiCompact B S hS g.hom := isQuasiCompact_of_isPullback B S hS sqP hfqc
  have hgqs : IsQuasiSeparated B S hS g.hom := isQuasiSeparated_of_isPullback B S hS sqP hfqs
  have hguc : UniversallyClosed B S hS g.hom :=
    universallyClosed_of_isPullback B S hS X'.property X.property hZu hT f.hom (yoneda.map ν)
      hf.2.2 sqP.flip
  -- the base change of the Chow cover, as a scheme of the site
  let hrep : yoneda.relativelyRepresentable (yoneda.map m) :=
    Functor.relativelyRepresentable.map yoneda m
  let Vp := hrep.pullback (yoneda.map ν)
  let a : Vp ⟶ V := hrep.fst' (yoneda.map ν)
  let b : Vp ⟶ Zu := hrep.snd (yoneda.map ν)
  have hab : a ≫ m = b ≫ ν := hrep.w' ν
  let ρ' : yoneda.obj Vp ⟶ X'.obj := sqP.lift (yoneda.map a ≫ ρ) (yoneda.map b)
    ((Category.assoc _ _ _).trans ((congrArg (yoneda.map a ≫ ·) hm.symm).trans
      ((yoneda.map_comp a m).symm.trans ((congrArg yoneda.map hab).trans
        (yoneda.map_comp b ν)))))
  have hρ'j : ρ' ≫ j.hom = yoneda.map a ≫ ρ := sqP.lift_fst _ _ _
  have hρ'g : ρ' ≫ g.hom = yoneda.map b := sqP.lift_snd _ _ _
  have hsqρ : IsPullback (yoneda.map a) ρ' ρ j.hom := by
    refine IsPullback.of_bot ?_ hρ'j.symm sqP
    rw [hρ'g, ← hm]
    exact hrep.isPullback' (yoneda.map ν)
  have hρ'uc : UniversallyClosed B S hS ρ' :=
    universallyClosed_of_isPullback B S hS (isAlgebraicSpace_yoneda B S hS Vp) hVsp
      X'.property X.property ρ j.hom hρP.2.2 hsqρ.flip
  have hρ'surj : Function.Surjective (pointsMap B S hS (yoneda.obj Vp) ρ') :=
    surjective_pointsMap_of_isPullback B S hS hsqρ hρS
  -- the clopen subset of the base change of the Chow cover
  let lam : (BigFppfOver.toScheme B S hS).obj Vp ⟶
      Limits.pullback ((BigFppfOver.toScheme B S hS).map m) U.toBase :=
    pullback.lift ((BigFppfOver.toScheme B S hS).map a)
      ((BigFppfOver.toScheme B S hS).map b ≫ κ) (by
        rw [Category.assoc, hκν, ← Functor.map_comp, ← Functor.map_comp, hab])
  let A' : Set ((BigFppfOver.toScheme B S hS).obj Vp) := lam ⁻¹' A
  have hA' : IsClopen A' := hA.preimage lam.continuous
  have hA'p : ∀ z, (BigFppfOver.toScheme B S hS).map b z = u' →
      (z ∈ A' ↔ (BigFppfOver.toScheme B S hS).map a z ∈ P) := by
    intro z hz
    have hsnd : pullback.snd ((BigFppfOver.toScheme B S hS).map m) U.toBase (lam z) = U.point := by
      rw [← Scheme.Hom.comp_apply, pullback.lift_snd, Scheme.Hom.comp_apply, hz, hκu]
    have hfst : pullback.fst ((BigFppfOver.toScheme B S hS).map m) U.toBase (lam z) =
        (BigFppfOver.toScheme B S hS).map a z := by
      rw [← Scheme.Hom.comp_apply, pullback.lift_fst]
    change lam z ∈ A ↔ _
    rw [hAp (lam z) hsnd, hfst]
  -- the points of the base change of the Chow cover, read in `X'`
  let ψ' : (BigFppfOver.toScheme B S hS).obj Vp → points B S hS X'.obj := fun z =>
    pointsMap B S hS (yoneda.obj Vp) ρ' ((pointsEquivScheme B S hS Vp).symm z)
  have hψ'j : ∀ z, pointsMap B S hS X'.obj j.hom (ψ' z) =
      ψ ((BigFppfOver.toScheme B S hS).map a z) := by
    intro z
    have h₁ := (congrFun (pointsMap_comp B S hS _ ρ' j.hom)
      ((pointsEquivScheme B S hS Vp).symm z)).symm.trans
      ((congrArg (fun k => pointsMap B S hS (yoneda.obj Vp) k
        ((pointsEquivScheme B S hS Vp).symm z)) hρ'j).trans
      (congrFun (pointsMap_comp B S hS _ (yoneda.map a) ρ) ((pointsEquivScheme B S hS Vp).symm z)))
    refine h₁.trans (congrArg (pointsMap B S hS (yoneda.obj V) ρ) ?_)
    apply injective_pointsToScheme B S hS V
    rw [pointsToScheme_pointsMap_yoneda]
    change (BigFppfOver.toScheme B S hS).map a (pointsEquivScheme B S hS Vp
      ((pointsEquivScheme B S hS Vp).symm z)) = pointsEquivScheme B S hS V
        ((pointsEquivScheme B S hS V).symm _)
    rw [Equiv.apply_symm_apply, Equiv.apply_symm_apply]
  have hψ'g : ∀ z, pointsToScheme B S hS Zu (pointsMap B S hS X'.obj g.hom (ψ' z)) =
      (BigFppfOver.toScheme B S hS).map b z :=
    pointsToScheme_pointsMap_pointsEquivScheme_symm ρ' g.hom b hρ'g
  have hψ'surj : Function.Surjective ψ' :=
    hρ'surj.comp (pointsEquivScheme B S hS Vp).symm.surjective
  have hcl : ∀ K : Set ((BigFppfOver.toScheme B S hS).obj Vp), IsClosed K → IsClosed (ψ' '' K) := by
    intro K hK
    rw [show ψ' '' K = pointsMap B S hS (yoneda.obj Vp) ρ' ''
      ((pointsEquivScheme B S hS Vp).symm '' K) from (Set.image_image _ _ _).symm]
    exact isClosedMap_pointsMap_of_pullback_fst_id B S hS ρ'
      (hρ'uc X'.obj X'.property (𝟙 _)) _ (isClosedMap_pointsEquivScheme_symm Vp _ hK)
  let C₁ := ψ' '' A'
  let C₂ := ψ' '' A'ᶜ
  have hC₁ : IsClosed C₁ := hcl _ hA'.1
  have hC₂ : IsClosed C₂ := hcl _ hA'.2.isClosed_compl
  have hcovC : C₁ ∪ C₂ = Set.univ := by
    rw [← Set.image_union, Set.union_compl_self, Set.image_univ, hψ'surj.range_eq]
  let E : Set ((BigFppfOver.toScheme B S hS).obj Zu) :=
    pointsToScheme B S hS Zu '' (pointsMap B S hS X'.obj g.hom '' (C₁ ∩ C₂))
  have hE : IsClosed E :=
    (isClosed_pointTopology_yoneda_iff_isClosed_image B S hS Zu _).1
      (isClosedMap_pointsMap_of_pullback_fst_id B S hS g.hom
        (hguc (schemeSpace Zu).obj (schemeSpace Zu).property (𝟙 _)) _ (hC₁.inter hC₂))
  have hD : ∀ x ∈ C₁ ∩ C₂,
      pointsToScheme B S hS Zu (pointsMap B S hS X'.obj g.hom x) ∈ E :=
    fun x hx => ⟨_, ⟨x, hx, rfl⟩, rfl⟩
  -- the key property of the pieces over `u'`
  have hkey : ∀ x : points B S hS X'.obj,
      pointsToScheme B S hS Zu (pointsMap B S hS X'.obj g.hom x) = u' →
      ∀ z, ψ' z = x → (z ∈ A' ↔ pointsMap B S hS X'.obj j.hom x ∈ P₀) := by
    intro x hx z hz
    have hbz : (BigFppfOver.toScheme B S hS).map b z = u' := by rw [← hψ'g, hz, hx]
    rw [hA'p z hbz, ← hz, hψ'j]
    exact Iff.rfl
  have hu' : u' ∉ E := by
    rintro ⟨_, ⟨x, ⟨⟨z₁, hz₁, hz₁x⟩, ⟨z₂, hz₂, hz₂x⟩⟩, rfl⟩, hxu⟩
    exact hz₂ ((hkey x hxu z₂ hz₂x).2
      ((hkey x hxu z₁ hz₁x).1 hz₁))
  -- the two points over `u'`
  have hlift : ∀ x : points B S hS X.obj,
      pointsToScheme B S hS T (pointsMap B S hS X.obj f.hom x) = t →
      ∃ x' : points B S hS X'.obj, pointsMap B S hS X'.obj j.hom x' = x ∧
        pointsToScheme B S hS Zu (pointsMap B S hS X'.obj g.hom x') = u' :=
    fun _ hx => exists_pullback_point_of_pointsToScheme_eq f ν (hx.trans hνu.symm)
  obtain ⟨x₁', hx₁j, hx₁g⟩ := hlift x₁ hx₁F
  obtain ⟨x₂', hx₂j, hx₂g⟩ := hlift x₂ hx₂F
  have h₂ : x₂' ∈ C₁ := by
    obtain ⟨z, hz⟩ := hψ'surj x₂'
    exact ⟨z, (hkey x₂' hx₂g z hz).2 (hx₂j ▸ hx₂P), hz⟩
  have h₁ : x₁' ∉ C₁ := by
    intro h
    obtain ⟨z, hz⟩ := hψ'surj x₁'
    have hz₂ : z ∈ A'ᶜ := fun hzA => hx₁P (hx₁j ▸ (hkey x₁' hx₁g z hz).1 hzA)
    exact hu' (hx₁g ▸ hD x₁' ⟨h, z, hz₂, hz⟩)
  exact h₁ ((iff_mem_of_isClosed_cover_of_isIso_fSharp g hgqc hgqs C₁ C₂ hC₁ hC₂ hcovC E hE hD
    u' hu' x₁' x₂' hx₁g hx₂g).2 h₂)

/-- **The fibres of a proper morphism with `f_* 𝒪_X = 𝒪_T` over a scheme of the site are
preconnected.**  The fibre over `t` is the image of the fibre of the base change to an affine
open neighbourhood of `t`, which is preconnected by
`AlgebraicGeometry.Space.isPreconnected_fibre_of_isProper_of_isIso_fSharp_of_isAffine`: the base
change of `f` to the open neighbourhood is proper, with `f_* 𝒪 = 𝒪` by flat base change. -/
theorem isPreconnected_fibre_of_isProper_of_isIso_fSharp_of_scheme
    {T : BigFppfOver B S hS}
    {X : AlgebraicSpaces B S hS} (f : X ⟶ schemeSpace T) (hf : IsProper B S hS f.hom)
    [IsIso (smallEtaleRingedToposHom B S hS f).fSharp]
    (t : (BigFppfOver.toScheme B S hS).obj T) :
    IsPreconnected {x : points B S hS X.obj |
      pointsToScheme B S hS T (pointsMap B S hS X.obj f.hom x) = t} := by
  obtain ⟨_, ⟨O₀, hO₀, rfl⟩, htO, -⟩ :=
    ((BigFppfOver.toScheme B S hS).obj T).isBasis_affineOpens.exists_subset_of_mem_open
      (Set.mem_univ t) isOpen_univ
  let O : ((BigFppfOver.toScheme B S hS).obj T).Opens := O₀
  have hOc : B.Contains O.toScheme := Scheme.size_lt_of_isOpenImmersion O.ι T.left.property
  obtain ⟨T₂, ν, e, hν⟩ := exists_siteObject_toScheme_map_eq B S hS hOc O.ι
  have hνet : Etale ((BigFppfOver.toScheme B S hS).map ν) := by
    rw [hν]
    infer_instance
  have : AlgebraicGeometry.IsOpenImmersion ((BigFppfOver.toScheme B S hS).map ν) := by
    rw [hν]
    infer_instance
  have : IsAffine ((BigFppfOver.toScheme B S hS).obj T₂) := by
    have : IsAffine O.toScheme := hO₀
    exact IsAffine.of_isIso e.hom
  have hflat := isFlat_schemeSpaceMap_of_etale ν hνet
  let sq := IsPullback.of_hasPullback f (schemeSpaceMap ν)
  let j := pullback.fst f (schemeSpaceMap ν)
  let g := pullback.snd f (schemeSpaceMap ν)
  have : IsIso (smallEtaleRingedToposHom B S hS g).fSharp :=
    isIso_fSharp_pullback_snd_of_isFlat f hf _ hflat
  have hg : IsProper B S hS g.hom := (isProper_isStableUnderBaseChange B S hS).of_isPullback sq hf
  let tO : O.toScheme := ⟨t, htO⟩
  let t₂ : (BigFppfOver.toScheme B S hS).obj T₂ := e.inv tO
  have ht₂ : (BigFppfOver.toScheme B S hS).map ν t₂ = t := by
    rw [hν, Scheme.Hom.comp_apply, ← Scheme.Hom.comp_apply e.inv e.hom, Iso.inv_hom_id]
    rfl
  have hpre := isPreconnected_fibre_of_isProper_of_isIso_fSharp_of_isAffine g hg t₂
  have himage : ∀ y : points B S hS (pullback f (schemeSpaceMap ν)).obj,
      pointsToScheme B S hS T (pointsMap B S hS X.obj f.hom (pointsMap B S hS _ j.hom y)) =
        (BigFppfOver.toScheme B S hS).map ν
          (pointsToScheme B S hS T₂ (pointsMap B S hS _ g.hom y)) := by
    intro y
    have hw : j.hom ≫ f.hom = g.hom ≫ yoneda.map ν := congrArg (fun m => m.hom) sq.w
    have e₁ := congrFun (pointsMap_comp B S hS _ j.hom f.hom) y
    have e₂ := congrFun (pointsMap_comp B S hS _ g.hom (yoneda.map ν)) y
    have h₁ : pointsMap B S hS X.obj f.hom (pointsMap B S hS _ j.hom y) =
        pointsMap B S hS (yoneda.obj T₂) (yoneda.map ν) (pointsMap B S hS _ g.hom y) :=
      e₁.symm.trans ((congrArg (fun m => pointsMap B S hS _ m y) hw).trans e₂)
    exact (congrArg (pointsToScheme B S hS T) h₁).trans
      (pointsToScheme_pointsMap_yoneda B S hS ν _)
  have heq : {x : points B S hS X.obj |
      pointsToScheme B S hS T (pointsMap B S hS X.obj f.hom x) = t} =
      pointsMap B S hS _ j.hom '' {y | pointsToScheme B S hS T₂
        (pointsMap B S hS _ g.hom y) = t₂} := by
    ext x
    refine ⟨fun hx => (exists_pullback_point_of_pointsToScheme_eq f ν (hx.trans ht₂.symm)).imp
      fun _ => And.symm, ?_⟩
    rintro ⟨y, hy, rfl⟩
    change pointsToScheme B S hS T (pointsMap B S hS X.obj f.hom (pointsMap B S hS _ j.hom y)) = t
    rw [himage, hy, ht₂]
  rw [heq]
  exact hpre.image _ (continuous_pointsMap B S hS j.hom).continuousOn

/-- **The geometric fibres of a proper surjective morphism with `f_* 𝒪_X = 𝒪_Y` are
connected.**  Let `f : X ⟶ Y` be a proper surjective morphism of algebraic spaces over `S` with
`𝒪_Y ⟶ f_* 𝒪_X` an isomorphism.  For every geometric point `ȳ` of `Y` the fibre `X ×_Y ȳ` has
connected point space.

By Stacks 0A1A
(`AlgebraicGeometry.Space.connectedSpace_geometricFiber_iff_forall_scheme_etaleNeighborhood`) it
suffices that the fibre of the base change `X_W ⟶ W` to every étale neighbourhood of `ȳ` by a
scheme `W` is connected over the point of `W` below `ȳ`; it is nonempty by surjectivity and
preconnected by
`AlgebraicGeometry.Space.isPreconnected_fibre_of_isProper_of_isIso_fSharp_of_scheme`,
`f_* 𝒪 = 𝒪` surviving the flat base change to `W`.  This is
`AlgebraicGeometry.Space.connectedPullback_of_isProper_of_isIso_fSharp` without its locally
Noetherian hypothesis on `Y`. -/
theorem connectedPullback_of_isProper_of_isSurjective_of_isIso_fSharp
    {X Y : AlgebraicSpaces B S hS}
    (f : X ⟶ Y) (hf : IsProper B S hS f.hom) (hfs : IsSurjective B S hS f.hom)
    [IsIso (smallEtaleRingedToposHom B S hS f).fSharp] (y : GeometricPoint B S hS Y.1) :
    ConnectedPullback B S hS f.hom (yonedaEquiv.symm y.val.value) := by
  refine (connectedSpace_geometricFiber_iff_forall_scheme_etaleNeighborhood B S hS X.property
    Y.property f.hom y).2 fun U W e => ?_
  let r := representedResidueFieldPointInNeighborhood B S hS U W e
  -- the étale morphism from the scheme `W` and the point of `W`
  let a : yoneda.obj W ⟶ Y.obj := e.inv ≫ U.toBase
  have ha : IsEtale B S hS a := by
    intro T φ hφ
    exact U.etale_toBase T (φ ≫ e.inv) (MorphismProperty.RespectsIso.postcomp _ e.inv φ hφ)
  let q : FieldValuedPoint B S hS (yoneda.obj W) := FieldValuedPoint.map B S hS U.space e.hom r
  have hq : yonedaEquiv.symm q.value = yonedaEquiv.symm r.value ≫ e.hom :=
    (yonedaEquiv_symm_naturality_right _ e.hom _).symm
  have hka : yonedaEquiv.symm q.value ≫ a = yonedaEquiv.symm r.value ≫ U.toBase := by
    rw [hq]
    exact (Category.assoc _ _ _).trans
      (congrArg (yonedaEquiv.symm r.value ≫ ·) (e.hom_inv_id_assoc U.toBase))
  obtain ⟨hrqc, hrmono⟩ := representedResidueFieldPointInNeighborhood_qc_mono B S hS U W e
  have hqmono : Mono (yonedaEquiv.symm q.value) := by
    rw [hq]
    exact @mono_comp _ _ _ _ _ _ hrmono _ (IsIso.mono_of_iso e.hom)
  have hqqc : IsQuasiCompact B S hS (yonedaEquiv.symm q.value) := by
    rw [hq]
    exact (isQuasiCompact_comp_isIso_iff B S hS _ e.hom).2 hrqc
  -- the base change of `f` to `W`
  let aS : schemeSpace W ⟶ Y := ObjectProperty.homMk a
  let sq := IsPullback.of_hasPullback f aS
  let j := pullback.fst f aS
  let g := pullback.snd f aS
  have sqP : IsPullback j.hom g.hom f.hom a := sq.map (ObjectProperty.ι _)
  have : IsIso (smallEtaleRingedToposHom B S hS g).fSharp :=
    isIso_fSharp_pullback_snd_of_isFlat f hf _ (isFlat_of_isEtale B S hS ha)
  have hg : IsProper B S hS g.hom := (isProper_isStableUnderBaseChange B S hS).of_isPullback sq hf
  have hgs : IsSurjective B S hS g.hom := isSurjective_of_isPullback B S hS sq hfs
  -- the fibre over `q` is connected
  let w := pointsToScheme B S hS W (q.class B S hS (yoneda.obj W))
  have hset : setFibre B S hS g.hom q = {x : points B S hS (pullback f aS).obj |
      pointsToScheme B S hS W (pointsMap B S hS _ g.hom x) = w} := by
    ext x
    exact ⟨fun hx => congrArg (pointsToScheme B S hS W) hx,
      fun hx => injective_pointsToScheme B S hS W hx⟩
  have hpre := isPreconnected_fibre_of_isProper_of_isIso_fSharp_of_scheme g hg w
  rw [← hset] at hpre
  have hconn : ConnectedSpace (setFibre B S hS g.hom q) :=
    isConnected_iff_connectedSpace.mp ⟨hgs _, hpre⟩
  have hfib : ConnectedPullback B S hS g.hom (yonedaEquiv.symm q.value) :=
    let φ := (homeomorphSetFibre B S hS (pullback f aS).property (schemeSpace W).property g.hom q
      hqmono hqqc).symm
    φ.surjective.connectedSpace φ.continuous
  -- transport along the pasting of the two cartesian squares
  have big : IsPullback (pullback.fst g.hom (yonedaEquiv.symm q.value) ≫ j.hom)
      (pullback.snd g.hom (yonedaEquiv.symm q.value)) f.hom
      (yonedaEquiv.symm q.value ≫ a) :=
    (IsPullback.of_hasPullback g.hom (yonedaEquiv.symm q.value)).paste_horiz sqP
  rw [← hka]
  exact connectedSpace_of_presheafIso B S hS big.isoPullback hfib

end AlgebraicGeometry.Space

end
