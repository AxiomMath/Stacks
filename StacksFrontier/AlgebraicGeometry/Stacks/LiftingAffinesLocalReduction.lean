module

public import StacksFrontier.AlgebraicGeometry.Stacks.LiftingAffinesLocalSetup
public import StacksFrontier.AlgebraicGeometry.Spaces.SectionsOfPullback
public import StacksFrontier.AlgebraicGeometry.Spaces.FibreProduct
public import StacksFrontier.AlgebraicGeometry.Spaces.SmoothLocalProperties
public import StacksFrontier.AlgebraicGeometry.Spaces.EtalePermanence
public import StacksFrontier.AlgebraicGeometry.Spaces.SectionSpaceFinitePart
public import StacksFrontier.AlgebraicGeometry.Spaces.SmoothSourceLocalityTransfer

/-!
# The reduction of a thickened chart along a 2-fibre product, for Stacks 0CJV

Let `ι : 𝒳 ⟶ 𝒳'` be a 1-morphism of algebraic stacks, `b_w : U'_w ⟶ 𝒳'` a 1-morphism out of an
affine scheme of the site, and `U_w = U'_w ×_{𝒳'} 𝒳`, represented by a closed subscheme
`Y_w ⊆ U'_w` with ideal `J ⊆ Γ(U'_w)`. Let `E` be an affine scheme of the site with two
morphisms `s, t : E ⟶ U'_w` whose composites with `b_w` are 2-isomorphic. This file proves:

* `J · Γ(E)` is the same ideal through `s` and through `t`;
* the 2-fibre product `R = U'_w ×_{𝒳'} U'_w` has an affine étale chart through any point of the
  diagonal, with smooth projections;
* for a `Γ(U'_w)`-algebra `X` whose spectrum maps to `𝒳` by a relatively smooth 1-morphism
  lifting its map to `𝒳'`, the ring `X ⊗_{Γ(U'_w)} Γ(E)` is smooth over `Γ(Y_w)` through `t`,
  when `E` is an étale chart of `R` and `s`, `t` are its two projections.

The last statement is the ring-level content of the source's observation that
`Z = 𝒳 ×_{𝒳'} Z'` is smooth over `X = 𝒳 ×_{𝒳'} X'` in the proof of Stacks 0CJV.
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits Bicategory TensorProduct

namespace AlgebraicGeometry.Stack.LiftingAffinesLocal

universe u w

variable {B : BigFppfSite.{u}} {S : Scheme.{u}} {hS : B.Contains S}

/-- The morphism of algebraic spaces represented by a morphism of the site: an abbreviation of
`AlgebraicGeometry.schemeSpaceMap`. -/
noncomputable abbrev repHom {T T' : BigFppfOver B S hS} (φ : T ⟶ T') :
    Space.yonedaSpace _ _ _ T ⟶ Space.yonedaSpace _ _ _ T' :=
  schemeSpaceMap φ

/-- `repHom` sends a composite of morphisms of the site to the composite of their images. -/
theorem repHom_comp {T T' T'' : BigFppfOver B S hS} (φ : T ⟶ T') (ψ : T' ⟶ T'') :
    repHom (φ ≫ ψ) = repHom φ ≫ repHom ψ :=
  ObjectProperty.hom_ext _ (yoneda.map_comp φ ψ)

variable {𝒳 𝒳' : AlgebraicStacks.{u, w} B S hS} {ι : 𝒳 ⟶ 𝒳'}

/-- A 2-isomorphism of composites through a common first factor. -/
noncomputable def whiskerTwoIso {T T' V : AlgebraicSpaces B S hS}
    (k : T ⟶ T') {s t : T' ⟶ V} (bw : (algebraicSpaceStackFunctor.{u, w} B S hS).obj V ⟶ 𝒳')
    (ρ : (algebraicSpaceStackFunctor.{u, w} B S hS).map s ≫ bw ≅
      (algebraicSpaceStackFunctor.{u, w} B S hS).map t ≫ bw) :
    (algebraicSpaceStackFunctor.{u, w} B S hS).map (k ≫ s) ≫ bw ≅
      (algebraicSpaceStackFunctor.{u, w} B S hS).map (k ≫ t) ≫ bw :=
  (α_ ((algebraicSpaceStackFunctor.{u, w} B S hS).map k)
      ((algebraicSpaceStackFunctor.{u, w} B S hS).map s) bw ≪≫
    whiskerLeftIso ((algebraicSpaceStackFunctor.{u, w} B S hS).map k) ρ ≪≫
    (α_ ((algebraicSpaceStackFunctor.{u, w} B S hS).map k)
      ((algebraicSpaceStackFunctor.{u, w} B S hS).map t) bw).symm :)

/-- A map `K ⟶ Yw` obtained by transporting `f : K ⟶ Uw` along `eY` composes with `c` to `g`
whenever `f` lies over `g`. -/
private theorem preimage_comp_eY_inv_comp {V Yw K : BigFppfOver B S hS}
    {Uw : AlgebraicSpaces B S hS} {iUw : Uw ⟶ Space.yonedaSpace _ _ _ V} (c : Yw ⟶ V)
    (eY : yoneda.obj Yw ≅ Uw.obj) (heY : eY.hom ≫ iUw.hom = yoneda.map c)
    (f : yoneda.obj K ⟶ Uw.obj) (g : K ⟶ V) (h : f ≫ iUw.hom = yoneda.map g) :
    (yoneda.preimage (f ≫ eY.inv) : K ⟶ Yw) ≫ c = g := by
  apply yoneda.map_injective
  rw [yoneda.map_comp, Functor.map_preimage, Category.assoc, ← heY, Iso.inv_hom_id_assoc, h]

/-- **`J · Γ(E)` through `t` lies in `J · Γ(E)` through `s`**, for `s, t : E ⟶ U'_w` with
2-isomorphic composites with `b_w`. -/
theorem map_ker_le_map_of_twoIso {V Yw E : BigFppfOver B S hS}
    [IsAffine ((BigFppfOver.toScheme B S hS).obj V)]
    [IsAffine ((BigFppfOver.toScheme B S hS).obj Yw)]
    [IsAffine ((BigFppfOver.toScheme B S hS).obj E)]
    {bw : (algebraicSpaceStackFunctor.{u, w} B S hS).obj (Space.yonedaSpace _ _ _ V) ⟶ 𝒳'}
    {Uw : AlgebraicSpaces B S hS} {iUw : Uw ⟶ Space.yonedaSpace _ _ _ V}
    {aw : (algebraicSpaceStackFunctor.{u, w} B S hS).obj Uw ⟶ 𝒳}
    {γw : (algebraicSpaceStackFunctor.{u, w} B S hS).map iUw ≫ bw ≅ aw ≫ ι}
    (hUw : IsTwoFibreProduct (⟨_, _, _, γw⟩ : TwoCommSq bw ι))
    (c : Yw ⟶ V) (hπ : Function.Surjective ((BigFppfOver.toScheme B S hS).map c).appTop.hom)
    (eY : yoneda.obj Yw ≅ Uw.obj) (heY : eY.hom ≫ iUw.hom = yoneda.map c)
    (s t : E ⟶ V)
    (ρE : (algebraicSpaceStackFunctor.{u, w} B S hS).map (repHom s) ≫ bw ≅
      (algebraicSpaceStackFunctor.{u, w} B S hS).map (repHom t) ≫ bw) :
    (RingHom.ker ((BigFppfOver.toScheme B S hS).map c).appTop.hom).map
        ((BigFppfOver.toScheme B S hS).map t).appTop.hom ≤
      (RingHom.ker ((BigFppfOver.toScheme B S hS).map c).appTop.hom).map
        ((BigFppfOver.toScheme B S hS).map s).appTop.hom := by
  set π := ((BigFppfOver.toScheme B S hS).map c).appTop.hom
  set σ := ((BigFppfOver.toScheme B S hS).map s).appTop.hom
  set τ := ((BigFppfOver.toScheme B S hS).map t).appTop.hom
  set I := (RingHom.ker π).map σ
  let χ : Γ((BigFppfOver.toScheme B S hS).obj Yw, ⊤) →+*
      Γ((BigFppfOver.toScheme B S hS).obj E, ⊤) ⧸ I :=
    (Ideal.Quotient.lift (RingHom.ker π) ((Ideal.Quotient.mk I).comp σ) (fun j hj => by
      rw [RingHom.comp_apply, Ideal.Quotient.eq_zero_iff_mem]
      exact Ideal.mem_map_of_mem _ hj)).comp
      (RingHom.quotientKerEquivOfSurjective hπ).symm.toRingHom
  have hχ : χ.comp π = (algebraMap _ (Γ((BigFppfOver.toScheme B S hS).obj E, ⊤) ⧸ I)).comp σ := by
    ext b
    have h : (RingHom.quotientKerEquivOfSurjective hπ).symm (π b) = Ideal.Quotient.mk _ b := by
      rw [RingEquiv.symm_apply_eq, RingHom.quotientKerEquivOfSurjective_apply_mk]
    simp only [χ, RingHom.comp_apply, RingEquiv.toRingHom_eq_coe, RingEquiv.coe_toRingHom, h,
      Ideal.Quotient.lift_mk, Ideal.Quotient.algebraMap_eq]
  let Zs := BigFppfOver.specObj E (Γ((BigFppfOver.toScheme B S hS).obj E, ⊤) ⧸ I)
  let zE : Zs ⟶ E := BigFppfOver.specObjToBase E _
  let zY : Zs ⟶ Yw := BigFppfOver.specObjHomOver c s χ hχ
  have h1 : zY ≫ c = zE ≫ s := BigFppfOver.hom_ext_of_ringOf (by
    rw [BigFppfOver.ringOf_comp, BigFppfOver.ringOf_comp, BigFppfOver.ringOf_specObjHomOver,
      BigFppfOver.ringOf_specObjToBase]
    exact hχ)
  have η := whiskerTwoIso (repHom zE) bw ρE
  rw [← repHom_comp, ← repHom_comp] at η
  obtain ⟨k₂, hk₂, -⟩ := exists_factor_of_twoIso γw hUw (repHom (zE ≫ s)) (repHom (zE ≫ t)) η
    (repHom zY ≫ ObjectProperty.homMk eY.hom) (by
      apply ObjectProperty.hom_ext
      show yoneda.map zY ≫ eY.hom ≫ iUw.hom = yoneda.map (zE ≫ s)
      rw [heY, ← yoneda.map_comp, h1])
  let κ : Zs ⟶ Yw := yoneda.preimage (k₂.hom ≫ eY.inv)
  have h2 : κ ≫ c = zE ≫ t :=
    preimage_comp_eY_inv_comp c eY heY k₂.hom _ (congrArg (fun f => f.hom) hk₂)
  have h3 := congrArg BigFppfOver.ringOf h2
  rw [BigFppfOver.ringOf_comp, BigFppfOver.ringOf_comp, BigFppfOver.ringOf_specObjToBase] at h3
  rw [Ideal.map_le_iff_le_comap]
  intro j hj
  have h4 := RingHom.congr_fun h3 j
  rw [RingHom.comp_apply, RingHom.comp_apply, Ideal.Quotient.algebraMap_eq] at h4
  have hπj : π j = 0 := RingHom.mem_ker.mp hj
  rw [hπj, map_zero] at h4
  rw [Ideal.mem_comap, ← Ideal.Quotient.eq_zero_iff_mem]
  exact h4.symm

/-- **An affine étale chart of `U'_w ×_{𝒳'} U'_w` through the diagonal.** -/
theorem exists_affine_selfProduct_chart {V : BigFppfOver B S hS}
    (bw : (algebraicSpaceStackFunctor.{u, w} B S hS).obj (Space.yonedaSpace _ _ _ V) ⟶ 𝒳')
    (hbw : AlgebraicStacks.IsSmooth B S hS bw) (u : Space.points B S hS (yoneda.obj V)) :
    ∃ (R : AlgebraicSpaces B S hS) (sR tR : R ⟶ Space.yonedaSpace _ _ _ V)
      (ρ : (algebraicSpaceStackFunctor.{u, w} B S hS).map sR ≫ bw ≅
        (algebraicSpaceStackFunctor.{u, w} B S hS).map tR ≫ bw),
      Nonempty (IsTwoFibreProduct (⟨_, _, _, ρ⟩ : TwoCommSq bw bw)) ∧
      ∃ (E : BigFppfOver B S hS) (eE : Space.yonedaSpace _ _ _ E ⟶ R) (sE tE : E ⟶ V),
        IsAffine ((BigFppfOver.toScheme B S hS).obj E) ∧ Space.IsEtale B S hS eE.hom ∧
        repHom sE = eE ≫ sR ∧ repHom tE = eE ≫ tR ∧
        Space.IsSmooth B S hS (yoneda.map sE) ∧ Space.IsSmooth B S hS (yoneda.map tE) ∧
        u ∈ Set.range (Space.pointsMap B S hS (yoneda.obj E) (yoneda.map sE)) := by
  obtain ⟨R, sR, tR, ρ, ⟨hR⟩⟩ := exists_isTwoFibreProduct_algebraicSpaceStackFunctor bw bw
  have hbrel := isRelativelySmooth_of_isSmooth_space_source bw hbw
  let D : TwoCommSq bw bw :=
    ⟨(algebraicSpaceStackFunctor.{u, w} B S hS).obj (Space.yonedaSpace _ _ _ V),
      𝟙 _, 𝟙 _, Iso.refl _⟩
  let mD := twoFibreProductPreHom hR D
  let δ : Space.yonedaSpace _ _ _ V ⟶ R :=
    ObjectProperty.homMk (representingMap B S hS _ _ (yoneda.obj V)
      R.obj (StacksRepresentableCFG.EquivalenceOver.refl _)
      (StacksRepresentableCFG.EquivalenceOver.refl _) mD.hom.hom)
  have hδ : (algebraicSpaceStackFunctor.{u, w} B S hS).map δ = mD.hom :=
    algebraicSpaceStackFunctor_map_homMk_representingMap _
  have hδs : δ ≫ sR = 𝟙 _ := by
    apply algebraicSpaceStackFunctor_map_injective
    rw [Functor.map_comp, hδ, CategoryTheory.Functor.map_id]
    exact (eq_of_hom₂_algebraicSpaceStackFunctor_obj mD.isoFst.hom).symm
  obtain ⟨E, eE0, hEaff, hEet, e, he⟩ :=
    Space.exists_affine_etale_mem_range R.property (Space.pointsMap B S hS _ δ.hom u)
  let sE : E ⟶ V := yoneda.preimage (eE0 ≫ sR.hom)
  let tE : E ⟶ V := yoneda.preimage (eE0 ≫ tR.hom)
  have hsm : ∀ {r : R ⟶ Space.yonedaSpace _ _ _ V}, Space.IsSmooth B S hS r.hom →
      Space.IsSmooth B S hS (yoneda.map (yoneda.preimage (eE0 ≫ r.hom))) := fun {r} hr => by
    rw [Functor.map_preimage]
    exact Space.isSmooth_comp B S hS (isAlgebraicSpace_yoneda B S hS E) R.property
      (isAlgebraicSpace_yoneda B S hS V) _ _
      (Space.isSmooth_of_isEtale B S hS R.property hEet) hr
  refine ⟨R, sR, tR, ρ, ⟨hR⟩, E, ObjectProperty.homMk eE0, sE, tE, hEaff, hEet,
    ObjectProperty.hom_ext _ (by exact Functor.map_preimage yoneda (eE0 ≫ sR.hom)),
    ObjectProperty.hom_ext _ (by exact Functor.map_preimage yoneda (eE0 ≫ tR.hom)),
    hsm (isSmooth_fst_of_isTwoFibreProduct_of_isRelativelySmooth hR hbrel),
    hsm (isSmooth_fst_of_isTwoFibreProduct_of_isRelativelySmooth (isTwoFibreProduct_swap hR) hbrel),
    e, ?_⟩
  · have hδs' : δ.hom ≫ sR.hom = 𝟙 _ := congrArg (fun f => f.hom) hδs
    rw [Functor.map_preimage, Space.pointsMap_comp, Function.comp_apply, he,
      ← Function.comp_apply (f := Space.pointsMap B S hS _ sR.hom), ← Space.pointsMap_comp,
      hδs', Space.pointsMap_id]
    rfl

/-- **The base change of the chart along an étale chart of `U'_w ×_{𝒳'} U'_w` is smooth over the
reduction.** Let `E` be an affine étale chart of `R = U'_w ×_{𝒳'} U'_w` with projections
`s, t : E ⟶ U'_w`, and let `X` be a finite type `Γ(U'_w)`-algebra whose spectrum `T₁` maps to
`𝒳` by a relatively smooth 1-morphism `x_T` with `x_T ≫ ι ≅ (T₁ ⟶ U'_w) ≫ b_w`. Then the ring
`X ⊗_{Γ(U'_w)} Γ(E)` (base change along `s`) is smooth over `Γ(Y_w)` through `t`. -/
theorem exists_smooth_tensor_of_twoFibreProduct {V Yw E : BigFppfOver B S hS}
    [IsAffine ((BigFppfOver.toScheme B S hS).obj V)]
    [IsAffine ((BigFppfOver.toScheme B S hS).obj Yw)]
    [IsAffine ((BigFppfOver.toScheme B S hS).obj E)]
    {bw : (algebraicSpaceStackFunctor.{u, w} B S hS).obj (Space.yonedaSpace _ _ _ V) ⟶ 𝒳'}
    {Uw : AlgebraicSpaces B S hS} {iUw : Uw ⟶ Space.yonedaSpace _ _ _ V}
    {aw : (algebraicSpaceStackFunctor.{u, w} B S hS).obj Uw ⟶ 𝒳}
    {γw : (algebraicSpaceStackFunctor.{u, w} B S hS).map iUw ≫ bw ≅ aw ≫ ι}
    (hUw : IsTwoFibreProduct (⟨_, _, _, γw⟩ : TwoCommSq bw ι))
    (c : Yw ⟶ V) (eY : yoneda.obj Yw ≅ Uw.obj) (heY : eY.hom ≫ iUw.hom = yoneda.map c)
    {R : AlgebraicSpaces B S hS} {sR tR : R ⟶ Space.yonedaSpace _ _ _ V}
    {ρ : (algebraicSpaceStackFunctor.{u, w} B S hS).map sR ≫ bw ≅
      (algebraicSpaceStackFunctor.{u, w} B S hS).map tR ≫ bw}
    (hR : IsTwoFibreProduct (⟨_, _, _, ρ⟩ : TwoCommSq bw bw))
    (eE : Space.yonedaSpace _ _ _ E ⟶ R) (heE : Space.IsEtale B S hS eE.hom) (sE tE : E ⟶ V)
    (hsE : repHom sE = eE ≫ sR) (htE : repHom tE = eE ≫ tR)
    [Algebra Γ((BigFppfOver.toScheme B S hS).obj V, ⊤) Γ((BigFppfOver.toScheme B S hS).obj E, ⊤)]
    [Algebra.FiniteType Γ((BigFppfOver.toScheme B S hS).obj V, ⊤)
      Γ((BigFppfOver.toScheme B S hS).obj E, ⊤)]
    (hs : algebraMap Γ((BigFppfOver.toScheme B S hS).obj V, ⊤)
      Γ((BigFppfOver.toScheme B S hS).obj E, ⊤) = ((BigFppfOver.toScheme B S hS).map sE).appTop.hom)
    (X : Type u) [CommRing X] [Algebra Γ((BigFppfOver.toScheme B S hS).obj V, ⊤) X]
    [Algebra.FiniteType Γ((BigFppfOver.toScheme B S hS).obj V, ⊤) X]
    (xT : (algebraicSpaceStackFunctor.{u, w} B S hS).obj
      (Space.yonedaSpace _ _ _ (BigFppfOver.specObj V X)) ⟶ 𝒳)
    (hxT : IsRelativelySmooth.{u, u, u + 1} B S hS xT.hom)
    (θ : xT ≫ ι ≅ (algebraicSpaceStackFunctor.{u, w} B S hS).map
      (repHom (BigFppfOver.specObjToBase V X)) ≫ bw) :
    ∃ ψ : Γ((BigFppfOver.toScheme B S hS).obj Yw, ⊤) →+*
        X ⊗[Γ((BigFppfOver.toScheme B S hS).obj V, ⊤)] Γ((BigFppfOver.toScheme B S hS).obj E, ⊤),
      ψ.Smooth ∧ ψ.comp ((BigFppfOver.toScheme B S hS).map c).appTop.hom =
        Algebra.TensorProduct.includeRight.toRingHom.comp
          ((BigFppfOver.toScheme B S hS).map tE).appTop.hom := by
  let F := algebraicSpaceStackFunctor.{u, w} B S hS
  let T₁ := BigFppfOver.specObj V X
  let k' : T₁ ⟶ V := BigFppfOver.specObjToBase V X
  -- the fibre product `K' = R ×_{U'_w} T₁` of presheaves, an algebraic space
  have hKp : IsAlgebraicSpace B S hS (pullback sR.hom (yoneda.map k')) :=
    isAlgebraicSpace_of_isPullback R.property (isAlgebraicSpace_yoneda B S hS T₁)
      (isAlgebraicSpace_yoneda B S hS V).isSheaf
      (isAlgebraicSpace_yoneda B S hS V).diagonal_representable
      (IsPullback.of_hasPullback sR.hom (yoneda.map k'))
  let Kp : AlgebraicSpaces B S hS := ⟨pullback sR.hom (yoneda.map k'), hKp⟩
  let p₁ : Kp ⟶ R := ObjectProperty.homMk (pullback.fst _ _)
  let p₂ : Kp ⟶ Space.yonedaSpace _ _ _ T₁ := ObjectProperty.homMk (pullback.snd _ _)
  have hpb : IsPullback p₂.hom p₁.hom (repHom k').hom sR.hom :=
    (IsPullback.of_hasPullback sR.hom (yoneda.map k')).flip
  -- `K'` is the 2-fibre product `U'_w ×_{𝒳'} T₁`, by pasting with `R`
  let P : TwoCommSq bw bw := ⟨_, _, _, ρ⟩
  have hQ := isTwoFibreProduct_of_isPullback.{u, w} hpb
  have hout := isTwoFibreProduct_pasteFst P hR _ hQ
  have hN := isTwoFibreProduct_swap hout
  obtain ⟨m, hm, hmsm⟩ := exists_smooth_factor_of_isTwoFibreProduct hUw xT hxT θ
    (k₁ := p₁ ≫ tR) (k₂ := p₂) hN
  -- the ring `X ⊗ Γ(E)` and its spectrum `K = T₁ ×_{U'_w} E`
  have : Algebra.FiniteType Γ((BigFppfOver.toScheme B S hS).obj V, ⊤)
      (X ⊗[Γ((BigFppfOver.toScheme B S hS).obj V, ⊤)] Γ((BigFppfOver.toScheme B S hS).obj E, ⊤)) :=
    Algebra.FiniteType.trans (S := X) inferInstance inferInstance
  let K := BigFppfOver.specObj V
    (X ⊗[Γ((BigFppfOver.toScheme B S hS).obj V, ⊤)] Γ((BigFppfOver.toScheme B S hS).obj E, ⊤))
  let kT : K ⟶ T₁ := BigFppfOver.specObjMap (Algebra.TensorProduct.includeLeft
    (S := Γ((BigFppfOver.toScheme B S hS).obj V, ⊤)) (A := X)
    (B := Γ((BigFppfOver.toScheme B S hS).obj E, ⊤)))
  have hkE : (Algebra.TensorProduct.includeRight.toRingHom).comp
      ((BigFppfOver.toScheme B S hS).map sE).appTop.hom =
      algebraMap Γ((BigFppfOver.toScheme B S hS).obj V, ⊤)
        (X ⊗[Γ((BigFppfOver.toScheme B S hS).obj V, ⊤)]
          Γ((BigFppfOver.toScheme B S hS).obj E, ⊤)) := by
    rw [← hs]
    exact Algebra.TensorProduct.includeRight.comp_algebraMap
  let kE : K ⟶ E := BigFppfOver.specObjHom sE _ hkE
  have hpo : IsPushout
      (BigFppfOver.ringHomOf (algebraMap Γ((BigFppfOver.toScheme B S hS).obj V, ⊤) X))
      ((BigFppfOver.toScheme B S hS).map sE).appTop
      (CommRingCat.ofHom (Algebra.TensorProduct.includeLeft
        (S := Γ((BigFppfOver.toScheme B S hS).obj V, ⊤)) (A := X)
        (B := Γ((BigFppfOver.toScheme B S hS).obj E, ⊤))).toRingHom)
      (BigFppfOver.ringHomOf (Algebra.TensorProduct.includeRight
        (R := Γ((BigFppfOver.toScheme B S hS).obj V, ⊤)) (A := X)
        (B := Γ((BigFppfOver.toScheme B S hS).obj E, ⊤))).toRingHom) := by
    have h := CommRingCat.isPushout_tensorProduct Γ((BigFppfOver.toScheme B S hS).obj V, ⊤) X
      Γ((BigFppfOver.toScheme B S hS).obj E, ⊤)
    rw [hs] at h
    exact h
  have hKpb := BigFppfOver.isPullback_yoneda_of_isPushout sE (Algebra.TensorProduct.includeLeft
    (S := Γ((BigFppfOver.toScheme B S hS).obj V, ⊤)) (A := X)
    (B := Γ((BigFppfOver.toScheme B S hS).obj E, ⊤))) _ hkE hpo
  -- the comparison `K ⟶ K'` is étale, a base change of `E ⟶ R`
  have hsE' : eE.hom ≫ sR.hom = yoneda.map sE := (congrArg (fun f => f.hom) hsE).symm
  have htE' : eE.hom ≫ tR.hom = yoneda.map tE := (congrArg (fun f => f.hom) htE).symm
  let l : yoneda.obj K ⟶ pullback sR.hom (yoneda.map k') :=
    pullback.lift (yoneda.map kE ≫ eE.hom) (yoneda.map kT) (by
      rw [Category.assoc, hsE']
      exact hKpb.w.symm)
  have hbig : IsPullback l (yoneda.map kE) (pullback.fst sR.hom (yoneda.map k')) eE.hom := by
    refine IsPullback.of_right (h₁₂ := pullback.snd sR.hom (yoneda.map k'))
      (h₂₂ := sR.hom) (v₁₃ := yoneda.map k') ?_ (pullback.lift_fst _ _ _)
      (IsPullback.of_hasPullback sR.hom (yoneda.map k')).flip
    rw [pullback.lift_snd, hsE']
    exact hKpb.flip.flip
  have hlet : Space.IsEtale B S hS l :=
    Space.isEtale_of_isPullback_of_isAlgebraicSpace B S hS hbig
      (isAlgebraicSpace_yoneda B S hS K) hKp (isAlgebraicSpace_yoneda B S hS E) R.property heE
  have hsm : Space.IsSmooth B S hS (l ≫ m.hom ≫ eY.inv) :=
    Space.isSmooth_comp B S hS (isAlgebraicSpace_yoneda B S hS K) hKp
      (isAlgebraicSpace_yoneda B S hS Yw) _ _ (Space.isSmooth_of_isEtale B S hS hKp hlet)
      (Space.isSmooth_comp B S hS hKp Uw.property (isAlgebraicSpace_yoneda B S hS Yw) _ _ hmsm
        (Space.isSmooth_of_isIso B S hS Uw.property (isAlgebraicSpace_yoneda B S hS Yw) _))
  let θK : K ⟶ Yw := yoneda.preimage (l ≫ m.hom ≫ eY.inv)
  have hθsm : Smooth ((BigFppfOver.toScheme B S hS).map θK) := by
    rw [← Space.isSmooth_yoneda_map_iff, Functor.map_preimage]
    exact hsm
  have hθc : θK ≫ c = kE ≫ tE := by
    refine preimage_comp_eY_inv_comp c eY heY (l ≫ m.hom) _ ?_
    have hm' : m.hom ≫ iUw.hom = p₁.hom ≫ tR.hom := congrArg (fun f => f.hom) hm
    rw [Category.assoc, hm', yoneda.map_comp, ← htE']
    show l ≫ pullback.fst _ _ ≫ tR.hom = _
    rw [← Category.assoc, pullback.lift_fst, Category.assoc]
  refine ⟨BigFppfOver.ringOf θK, (BigFppfOver.prop_iff_ringOf @Smooth θK).mp hθsm, ?_⟩
  have h := congrArg BigFppfOver.ringOf hθc
  rwa [BigFppfOver.ringOf_comp, BigFppfOver.ringOf_comp, BigFppfOver.ringOf_specObjHom] at h

end AlgebraicGeometry.Stack.LiftingAffinesLocal

end
