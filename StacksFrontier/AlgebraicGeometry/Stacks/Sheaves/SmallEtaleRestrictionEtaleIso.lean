module

public import StacksFrontier.AlgebraicGeometry.Stacks.Sheaves.SmallEtaleRestrictionComparison
public import StacksFrontier.CategoryTheory.Sites.Localization.PushforwardAdjunction

/-!
# The comparison along an etale morphism is an isomorphism (Stacks 075D, part (2))

Let `F` be an etale sheaf on a category fibred in groupoids `p : X ⥤ (Sch/S)_{fppf}` and let
`φ : x ⟶ y` be an arrow of `X` lying over an *etale* morphism `a : U ⟶ V` of schemes. Then the
comparison `c_φ : a_{small}^{-1}(F|_{V_et}) ⟶ F|_{U_et}` of Stacks 06W3 is an isomorphism.

## Main results

* `AlgebraicGeometry.Stack.isIso_restrictionInverseImageComparison`: **Stacks 075D**, part (2).

## Implementation notes

For an etale `a`, base change along `a` between small etale sites has a left adjoint on the
sites themselves, namely post-composition with `a`: an etale scheme over `U` is etale over `V`.
That adjunction of sites induces an adjunction on sheaves whose left adjoint is the direct image
along post-composition, so it is canonically isomorphic to the sheaf pullback along base change.
Transported across that isomorphism, the comparison map becomes, on sections over a small etale
object, restriction of `F` along a single arrow of the fibred category whose image in schemes is
an isomorphism; since `p` is fibred in groupoids, the arrow itself is then an isomorphism.

## References

* [Stacks Project, Tag 075D](https://stacks.math.columbia.edu/tag/075D)
-/

@[expose] public section

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits

universe u v w t

namespace AlgebraicGeometry.Stack

variable (B : BigFppfSite.{u}) (E : BigEtaleSite.{u}) (h : E.cutoff = B.cutoff)
  (S : Scheme.{u}) (hS : B.Contains S)

/-- Post-composition with an étale morphism `j : U ⟶ V` of a big étale site, as a functor from
the small étale site of `U` to that of `V`: an étale morphism to `U` composed with `j` is étale
over `V`. -/
private noncomputable def smallEtalePostcompose {U V : E.Scheme} (j : U ⟶ V)
    (hj : Etale (E.inclusion.map j)) :
    SmallEtale E U.1 U.property ⥤ SmallEtale E V.1 V.property :=
  (BigEtaleOver.IsEtaleOver E V.1 V.property).lift
    (SmallEtale.inclusion E U.1 U.property ⋙ Over.map j)
    (by
      intro X
      change Etale (E.inclusion.map (X.obj.hom ≫ j))
      let : Etale (E.inclusion.map X.obj.hom) := X.property
      let : Etale (E.inclusion.map j) := hj
      exact Etale.etale_comp (E.inclusion.map X.obj.hom) (E.inclusion.map j))

/-- Post-composition along an étale morphism is continuous: it carries the standard covering
families of the small étale site of `U` to standard covering families of that of `V`, the two
families having the same image in schemes. -/
private theorem smallEtalePostcompose_isContinuous {U V : E.Scheme} (j : U ⟶ V)
    (hj : Etale (E.inclusion.map j)) :
    (smallEtalePostcompose E j hj).IsContinuous
      (SmallEtale.topology E U.1 U.property) (SmallEtale.topology E V.1 V.property) := by
  let M := smallEtalePostcompose E j hj
  let iU := SmallEtale.inclusion E U.1 U.property
  let iV := SmallEtale.inclusion E V.1 V.property
  have := hasPullbacks_bigEtaleSite E
  have := hasPullbacks_smallEtale E U.1 U.property
  have := hasPullbacks_smallEtale E V.1 V.property
  have : ReflectsLimitsOfShape WalkingCospan E.inclusion :=
    reflectsLimitsOfShape_of_reflectsIsomorphisms
  have hUScheme : PreservesLimitsOfShape WalkingCospan
      (iU ⋙ (Over.forget (E.obj U.1 U.property) ⋙ E.inclusion)) := by
    show PreservesLimitsOfShape WalkingCospan (SmallEtale.toScheme E U.1 U.property)
    exact preservesPullbacks_smallEtaleToScheme E U.1 U.property
  have : PreservesLimitsOfShape WalkingCospan
      ((iU ⋙ Over.forget (E.obj U.1 U.property)) ⋙ E.inclusion) :=
    preservesLimitsOfShape_of_natIso
      (Functor.associator iU (Over.forget (E.obj U.1 U.property)) E.inclusion).symm
  have hUOver : PreservesLimitsOfShape WalkingCospan
      (iU ⋙ Over.forget (E.obj U.1 U.property)) :=
    preservesLimitsOfShape_of_reflects_of_preserves
      (iU ⋙ Over.forget (E.obj U.1 U.property)) E.inclusion
  have : PreservesLimitsOfShape WalkingCospan
      ((iU ⋙ Over.map j) ⋙ Over.forget (E.obj V.1 V.property)) := by
    simp only [Functor.assoc, Over.mapForget_eq]
    infer_instance
  have : PreservesLimitsOfShape WalkingCospan (M ⋙ iV) := by
    show PreservesLimitsOfShape WalkingCospan (iU ⋙ Over.map j)
    exact preservesLimitsOfShape_of_reflects_of_preserves
      (iU ⋙ Over.map j) (Over.forget (E.obj V.1 V.property))
  have : PreservesLimitsOfShape WalkingCospan M :=
    preservesLimitsOfShape_of_reflects_of_preserves M iV
  have hcp : CoverPreserving (SmallEtale.topology E U.1 U.property)
      (SmallEtale.topology E V.1 V.property) M := by
    apply coverPreserving_toGrothendieck_of_generators M
      (SmallEtale.precoverage E U.1 U.property) (SmallEtale.topology E V.1 V.property)
    intro X R hR
    obtain ⟨C, rfl, hC⟩ := (SmallEtale.mem_precoverage_iff E U.1 U.property).1 hR
    rw [← PreZeroHypercover.sieve₀_map]
    exact Precoverage.generate_mem_toGrothendieck
      ((SmallEtale.mem_precoverage_iff E V.1 V.property).2 ⟨C.map M, rfl, hC⟩)
  have : M.PreservesOneHypercovers (SmallEtale.topology E U.1 U.property)
      (SmallEtale.topology E V.1 V.property) :=
    Functor.PreservesOneHypercovers.of_coverPreserving hcp
  infer_instance

/-- Post-composition along an étale morphism is left adjoint to base change along it, the
restriction to étale objects of the slice adjunction `Over.map j ⊣ Over.pullback j`. -/
private noncomputable def smallEtalePostcomposeAdjunction {U V : E.Scheme} (j : U ⟶ V)
    (hj : Etale (E.inclusion.map j)) :
    smallEtalePostcompose E j hj ⊣ smallEtaleBaseChange E j := by
  let := hasPullbacks_bigEtaleSite E
  let iU := SmallEtale.inclusion E U.1 U.property
  let iV := SmallEtale.inclusion E V.1 V.property
  let M := smallEtalePostcompose E j hj
  let N := smallEtaleBaseChange E j
  let : iU.Full := inferInstance
  let : iU.Faithful := inferInstance
  let : iV.Full := inferInstance
  let : iV.Faithful := inferInstance
  let e₁ : iU ⋙ Over.map j ≅ M ⋙ iV := eqToIso (by rfl)
  let e₂ : iV ⋙ Over.pullback j ≅ N ⋙ iU :=
    eqToIso (smallEtaleBaseChange_comp_inclusion E j).symm
  exact (Over.mapPullbackAdj j).restrictFullyFaithful
    (Functor.FullyFaithful.ofFullyFaithful iU) (Functor.FullyFaithful.ofFullyFaithful iV) e₁ e₂

/-- The counit of the post-composition adjunction is the counit of the slice adjunction, after
forgetting the étale condition. -/
private theorem smallEtalePostcomposeAdjunction_counit_map {U V : E.Scheme} (j : U ⟶ V)
    (hj : Etale (E.inclusion.map j)) (W : SmallEtale E V.1 V.property) :
    (SmallEtale.inclusion E V.1 V.property).map
        ((smallEtalePostcomposeAdjunction E j hj).counit.app W) =
      (Over.mapPullbackAdj j).counit.app
        ((SmallEtale.inclusion E V.1 V.property).obj W) := by
  let iU := SmallEtale.inclusion E U.1 U.property
  let iV := SmallEtale.inclusion E V.1 V.property
  let M := smallEtalePostcompose E j hj
  let N := smallEtaleBaseChange E j
  let comm1 : iU ⋙ Over.map j ≅ M ⋙ iV := eqToIso (by rfl)
  let comm2 : iV ⋙ Over.pullback j ≅ N ⋙ iU :=
    eqToIso (smallEtaleBaseChange_comp_inclusion E j).symm
  show iV.map (((Over.mapPullbackAdj j).restrictFullyFaithful
      (Functor.FullyFaithful.ofFullyFaithful iU)
      (Functor.FullyFaithful.ofFullyFaithful iV) comm1 comm2).counit.app W) = _
  rw [Adjunction.map_restrictFullyFaithful_counit_app]
  simp [comm1, comm2, Over.mapPullbackAdj_counit_app]
  rfl

private theorem comp_comp_eq_of_conj {C : Type*} [Category C] {A A' X X' Y : C} {b : A ⟶ X}
    {a : X ⟶ Y} {eT : A ⟶ A'} {eX : X ⟶ X'} {eY : Y ⟶ A'} {u : A' ⟶ X'} {c : X' ⟶ A'}
    (hb : b ≫ eX = eT ≫ u) (ha : a ≫ eY = eX ≫ c) (hu : u ≫ c = 𝟙 A') :
    (b ≫ a) ≫ eY = eT := by
  rw [Category.assoc, ha, reassoc_of% hb, hu, Category.comp_id]

/-- The underlying morphism of an isomorphism in a slice category is an isomorphism. -/
private theorem isIso_left_hom_of_iso {C : Type*} [Category C] {X : C} {A A' : Over X}
    (e : A ≅ A') : IsIso e.hom.left :=
  (Over.forget X).map_isIso e.hom

/-- In a category fibred in groupoids over the big fppf site, an arrow whose underlying morphism
of schemes is an isomorphism is itself an isomorphism. -/
private theorem isIso_of_isIso_map_left {𝒳 : Type v} [Category.{w} 𝒳]
    (p : 𝒳 ⥤ BigFppfOver B S hS) (hp : p.IsFiberedInGroupoids) {x y : 𝒳} (δ : x ⟶ y)
    (hδ : IsIso (p.map δ).left) : IsIso δ := by
  have : IsIso ((Over.forget (B.obj hS)).map (p.map δ)) := hδ
  have := Functor.ReflectsIsomorphisms.reflects (Over.forget (B.obj hS)) (p.map δ)
  have := hp.isStronglyCartesian δ
  exact Functor.IsStronglyCartesian.isIso_of_base_isIso (p := p) (f := p.map δ) δ

/-- **Stacks 075D**, part (2). If an arrow of `𝒳` lies over an étale morphism of schemes, the
comparison of Stacks 06W3 between the inverse image of the restriction at its target and the
restriction at its source is an isomorphism. -/
@[stacks 075D "part (2)"]
theorem isIso_restrictionInverseImageComparison {𝒳 : Type v} [Category.{w} 𝒳]
    (p : 𝒳 ⥤ BigFppfOver B S hS) (hp : p.IsFiberedInGroupoids) {x y : 𝒳} (φ : x ⟶ y)
    (hφ : Etale (B.inclusion.map (p.map φ).left))
    (F : Sheaf (associatedTopology B S hS p (etaleTopology B)) (Type (max (u + 1) t))) :
    IsIso (restrictionInverseImageComparison B E h S hS p hp φ F) := by
  let U := E.obj (p.obj x).left.1 (contains_base B E h S hS p x)
  let V := E.obj (p.obj y).left.1 (contains_base B E h S hS p y)
  let f := smallEtaleBaseMorphism B E h S hS p φ
  have hf : Etale (E.inclusion.map f) := by
    simpa [f, smallEtaleBaseMorphism] using hφ
  let Jx := SmallEtale.topology E U.1 U.property
  let Jy := SmallEtale.topology E V.1 V.property
  let M := smallEtalePostcompose E f hf
  let N := smallEtaleBaseChange E f
  let : M.IsContinuous Jx Jy := smallEtalePostcompose_isContinuous E f hf
  let : N.IsContinuous Jy Jx := inferInstance
  let siteAdj := smallEtalePostcomposeAdjunction E f hf
  let pullAdj := N.sheafAdjunctionContinuous (Type (max (u + 1) t)) Jy Jx
  let postAdj := siteAdj.sheafPushforwardAdjunction (Type (max (u + 1) t)) (J := Jx) (K := Jy)
  let adjIso := pullAdj.leftAdjointUniq postAdj
  let Fy := restrictToSmallEtale B E h S hS p hp y F.obj
  let Fx := restrictToSmallEtale B E h S hS p hp x F.obj
  let Sy := restrictToSmallEtaleSheaf B E h S hS p hp y F
  let Sx := restrictToSmallEtaleSheaf B E h S hS p hp x F
  let etaP := restrictionPushforwardComparison B E h S hS p hp φ F.obj
  let eta : Sy ⟶ (N.sheafPushforwardContinuous (Type (max (u + 1) t)) Jy Jx).obj Sx :=
    Sheaf.homEquiv.symm etaP
  let gamma : (M.sheafPushforwardContinuous (Type (max (u + 1) t)) Jx Jy).obj Sy ⟶ Sx :=
    (postAdj.homEquiv Sy Sx).symm eta
  have hcomparison : restrictionInverseImageComparison B E h S hS p hp φ F =
      (pullAdj.homEquiv Sy Sx).symm eta := by
    dsimp only [restrictionInverseImageComparison, eta, etaP, Sy, Sx, N, f, Jy, Jx]
  have hgamma : IsIso gamma := by
    rw [← isIso_iff_of_reflects_iso _ (sheafToPresheaf Jx (Type (max (u + 1) t))),
      NatTrans.isIso_iff_isIso_app]
    intro T'
    let T := T'.unop
    show IsIso (gamma.hom.app (Opposite.op T))
    have : (Over.post (X := x) (p ⋙ Over.forget (B.obj hS))).IsEquivalence :=
      isEquivalence_overPost B S hS p hp x
    have : (Over.post (X := y) (p ⋙ Over.forget (B.obj hS))).IsEquivalence :=
      isEquivalence_overPost B S hS p hp y
    let Px := Over.post (X := x) (p ⋙ Over.forget (B.obj hS))
    let Py := Over.post (X := y) (p ⋙ Over.forget (B.obj hS))
    let Ix := smallEtaleInclusion B E h U.1 U.property
    let Iy := smallEtaleInclusion B E h V.1 V.property
    let W := M.obj T
    let NW := N.obj W
    let ePx := Px.asEquivalence
    let ePy := Py.asEquivalence
    let xT := ePx.inverse.obj (Ix.obj T)
    let xNW := ePx.inverse.obj (Ix.obj NW)
    let yW := ePy.inverse.obj (Iy.obj W)
    let z : Over y := Over.mk (xNW.hom ≫ φ)
    let jB : (p ⋙ Over.forget (B.obj hS)).obj x ⟶
        (p ⋙ Over.forget (B.obj hS)).obj y := (p.map φ).left
    let e₁ : Ix ⋙ Over.map jB ≅ M ⋙ Iy := Iso.refl _
    let eT : Px.obj xT ≅ Ix.obj T := ePx.counitIso.app (Ix.obj T)
    let eX : Px.obj xNW ≅ Ix.obj NW := ePx.counitIso.app (Ix.obj NW)
    let eY : Py.obj yW ≅ Iy.obj W := ePy.counitIso.app (Iy.obj W)
    have hz : Py.obj z = (Over.map jB).obj (Px.obj xNW) := by
      show Over.mk ((p.map (xNW.hom ≫ φ)).left) =
        (Over.map jB).obj (Over.mk ((p.map xNW.hom).left))
      apply congrArg Over.mk
      simp [jB, Functor.map_comp]
    let a : Py.obj z ⟶ Py.obj yW :=
      (eqToIso hz).hom ≫ (Over.map jB).map eX.hom ≫ (e₁.app NW).hom ≫
        Iy.map (siteAdj.counit.app W) ≫ eY.inv
    let alphaOver : z ⟶ yW := Py.preimage a
    let alpha := alphaOver.left
    have hAlpha : alpha ≫ yW.hom = xNW.hom ≫ φ := alphaOver.w
    let betaOver := Px.inv.map (Ix.map (siteAdj.unit.app T))
    let beta := betaOver.left
    have hGammaApp : gamma.hom.app (Opposite.op T) =
        etaP.app (Opposite.op W) ≫ Fx.map (Opposite.op (siteAdj.unit.app T)) := by
      dsimp [gamma]
      rw [postAdj.homEquiv_counit]
      show etaP.app (Opposite.op W) ≫ (postAdj.counit.app Sx).hom.app (Opposite.op T) =
        etaP.app (Opposite.op W) ≫ Fx.map (Opposite.op (siteAdj.unit.app T))
      congr 1
    have hAlphaBase : (p.map alpha).left ≫ eY.hom.left =
        eX.hom.left ≫ (e₁.app NW).hom.left ≫ (Iy.map (siteAdj.counit.app W)).left := by
      have hmap : Py.map alphaOver = a := by simp [alphaOver]
      let Qy := Over.forget ((p ⋙ Over.forget (B.obj hS)).obj y)
      have hmap' := congrArg Qy.map hmap
      simp only [Qy, Over.forget_map] at hmap'
      have hzleft : (Py.obj z).left = ((Over.map jB).obj (Px.obj xNW)).left := by rfl
      have hmap'' : (p.map alpha).left = a.left := hmap'
      have hEq : Over.Hom.left ((eqToIso hz).hom) = eqToHom hzleft := by
        dsimp only [eqToIso]
        rw [Over.eqToHom_left]
      have hYcancel : Over.Hom.left eY.inv ≫ Over.Hom.left eY.hom = 𝟙 _ :=
        Over.inv_left_hom_left eY
      cases hzleft
      rw [hmap'']
      dsimp only [a]
      simp only [Over.comp_left]
      rw [hEq]
      simp [Over.map_map_left, hYcancel]
    have hCompat : B.inclusion.map (p.map alpha).left ≫ B.inclusion.map eY.hom.left =
        B.inclusion.map eX.hom.left ≫ E.inclusion.map (pullback.fst W.obj.hom f) := by
      calc
        B.inclusion.map ((p.map alpha).left ≫ eY.hom.left) =
            B.inclusion.map (eX.hom.left ≫ (e₁.app NW).hom.left ≫
              (Iy.map (siteAdj.counit.app W)).left) :=
              congrArg (B.inclusion.map) hAlphaBase
        _ = B.inclusion.map eX.hom.left ≫ E.inclusion.map (pullback.fst W.obj.hom f) := by
              rw [Functor.map_comp]
              have := isIso_left_hom_of_iso eX
              have : IsIso (B.inclusion.map eX.hom.left) := Functor.map_isIso _ _
              apply (cancel_epi (B.inclusion.map eX.hom.left)).mpr
              have hR : (e₁.app NW).hom.left ≫ (Iy.map (siteAdj.counit.app W)).left =
                  (Iy.map (siteAdj.counit.app W)).left := Category.id_comp _
              rw [hR]
              have hc := smallEtalePostcomposeAdjunction_counit_map E f hf W
              have hc' := congrArg (fun g => E.inclusion.map (Over.Hom.left g)) hc
              dsimp only at hc'
              simp only [Over.mapPullbackAdj_counit_app, Over.homMk_left] at hc'
              exact hc'
    have hEta : etaP.app (Opposite.op W) = F.obj.map (Opposite.op alpha) :=
      restrictionPushforwardComparison_app B E h S hS p hp φ F.obj W alpha hAlpha hCompat
    have hFx : Fx.map (Opposite.op (siteAdj.unit.app T)) = F.obj.map (Opposite.op beta) := rfl
    let delta := beta ≫ alpha
    rw [hGammaApp, hEta, hFx]
    have hdelta : IsIso delta := by
      apply isIso_of_isIso_map_left B S hS p hp
      have hBeta : (p.map beta).left ≫ eX.hom.left =
          eT.hom.left ≫ (Ix.map (siteAdj.unit.app T)).left :=
        congrArg (Over.forget ((p ⋙ Over.forget (B.obj hS)).obj x)).map
          (ePx.counitIso.hom.naturality (Ix.map (siteAdj.unit.app T)))
      have htriangle : (Ix.map (siteAdj.unit.app T)).left ≫
          (e₁.app NW).hom.left ≫ (Iy.map (siteAdj.counit.app W)).left =
            𝟙 (Iy.obj W).left := by
        have ht := siteAdj.left_triangle_components T
        have htransport :
            (Ix.map (siteAdj.unit.app T)).left ≫ (e₁.app NW).hom.left =
              (Iy.map (M.map (siteAdj.unit.app T))).left := by
          simp only [Functor.id_obj, Functor.comp_obj, Over.forget_obj, Iso.app_hom]
          exact Category.comp_id _
        rw [← Category.assoc, htransport]
        have ht' := congrArg (fun g => (Iy.map g).left) ht
        show (Iy.map (M.map (siteAdj.unit.app T) ≫ siteAdj.counit.app W)).left =
          (Iy.map (𝟙 W)).left
        exact ht'
      have hd : (p.map delta).left = (p.map beta).left ≫ (p.map alpha).left :=
        (congrArg Over.Hom.left (p.map_comp beta alpha)).trans (Over.comp_left _ _ _ _ _)
      have hconj : (p.map delta).left ≫ eY.hom.left = eT.hom.left :=
        (congrArg (· ≫ eY.hom.left) hd).trans (comp_comp_eq_of_conj hBeta hAlphaBase htriangle)
      have := isIso_left_hom_of_iso eY
      have : IsIso ((p.map delta).left ≫ eY.hom.left) := by
        rw [hconj]; exact isIso_left_hom_of_iso eT
      exact IsIso.of_isIso_comp_right _ eY.hom.left
    show IsIso (F.obj.map alpha.op ≫ F.obj.map beta.op)
    have hmap_eq : F.obj.map delta.op = F.obj.map alpha.op ≫ F.obj.map beta.op :=
      F.obj.map_comp alpha.op beta.op
    rw [← hmap_eq]
    exact Functor.map_isIso _ _
  have hfactor : restrictionInverseImageComparison B E h S hS p hp φ F =
      adjIso.hom.app Sy ≫ gamma := by
    apply (pullAdj.homEquiv Sy Sx).injective
    rw [hcomparison, pullAdj.homEquiv_naturality_right,
      pullAdj.homEquiv_leftAdjointUniq_hom_app postAdj Sy, ← postAdj.homEquiv_unit]
    simp [gamma]
  rw [hfactor]
  infer_instance

end AlgebraicGeometry.Stack

end
