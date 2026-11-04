module

public import StacksFrontier.AlgebraicGeometry.Stacks.LiftingAffinesLocalLift

/-!
# The local step of Stacks 0CJV, assembled

`AlgebraicGeometry.Stack.LiftingAffinesLocal.exists_local_etaleSmoothLift`: every point of a scheme
`T` of the site, étale over `W` and mapping to the base change `U = U' ×_{𝒳'} 𝒳` of a smooth chart
over `𝒳`, has an open neighbourhood in `T` which is the base of a smooth lift along the thickening
`𝒳 ⟶ 𝒳'`. The steps are those of the source's proof of Stacks 0CJV (its last three paragraphs),
with the Koszul-regular sequence replaced by minimal generators lifted to the thickened chart:

1. shrink `T` and `U'` to affines `T₀ ⊆ T`, `U'_w ⊆ U'`, and represent `U'_w ×_{𝒳'} 𝒳` by a closed
   subscheme `Y_w ⊆ U'_w` (`exists_thickeningChart_square`,
   `exists_closedSubscheme_of_isThickening`);
2. factor `T₀ ⟶ U'_w` through `Y_w` by a morphism locally of finite presentation
   (`exists_reduction_factor`);
3. present `Γ(T₀)` over `Γ(Y_w)` at the point, with minimal generators lifted to `Γ(U'_w)[x]`
   (`Algebra.exists_liftedPresentation`);
4. choose an affine étale chart `E` of `U'_w ×_{𝒳'} U'_w` through the diagonal
   (`exists_affine_selfProduct_chart`); its two projections agree on `J`
   (`map_ker_le_map_of_twoIso`) and the reduction of the lifted chart is smooth over `Y_w` after
   base change to `E` (`exists_smooth_reduced_tensor`);
5. the Jacobian lifting gives a smooth chart of a principal open `T'_w` of the lifted chart
   (`exists_smooth_chart_of_liftedPresentation`), so `T'_w ⟶ 𝒳'` is smooth
   (`isSmooth_specAway_of_chart`);
6. `T'_w ×_{U'_w} Y_w` is an open of `T₀` around the point (`exists_awayQuotient_open`) and is
   `𝒳 ×_{𝒳'} T'_w` (`exists_etaleSmoothLift_of_isPullback`).
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits Bicategory TensorProduct

namespace AlgebraicGeometry.Stack.LiftingAffinesLocal

universe u w

variable {B : BigFppfSite.{u}} {S : Scheme.{u}} {hS : B.Contains S}
variable {𝒳 𝒳' : AlgebraicStacks.{u, w} B S hS} {ι : 𝒳 ⟶ 𝒳'}

/-- The last step of `exists_local_etaleSmoothLift`: given the smooth chart `T'_w` of the lifted
equations, the open `A = T'_w ×_{U'_w} Y_w` of `T₀` around the point is the base of a smooth
lift. -/
theorem exists_local_etaleSmoothLift_of_chart (hι : IsThickening ι)
    (W : AlgebraicSpaces B S hS) (x : (algebraicSpaceStackFunctor.{u, w} B S hS).obj W ⟶ 𝒳)
      (hx : AlgebraicStacks.IsSmooth B S hS x)
    {T : BigFppfOver B S hS} (t : yoneda.obj T ⟶ W.obj) (ht : Space.IsEtale B S hS t)
    {V Yw T₀ : BigFppfOver B S hS} [IsAffine ((BigFppfOver.toScheme B S hS).obj V)]
      [IsAffine ((BigFppfOver.toScheme B S hS).obj Yw)]
    [IsAffine ((BigFppfOver.toScheme B S hS).obj T₀)]
    {bw : (algebraicSpaceStackFunctor.{u, w} B S hS).obj (Space.yonedaSpace _ _ _ V) ⟶ 𝒳'}
      {Uw : AlgebraicSpaces B S hS} {iUw : Uw ⟶ Space.yonedaSpace _ _ _ V}
    {aw : (algebraicSpaceStackFunctor.{u, w} B S hS).obj Uw ⟶ 𝒳}
      {γw : (algebraicSpaceStackFunctor.{u, w} B S hS).map iUw ≫ bw ≅ aw ≫ ι}
    (hUw : IsTwoFibreProduct (⟨_, _, _, γw⟩ : TwoCommSq bw ι))
    (c : Yw ⟶ V) (hπ : Function.Surjective ((BigFppfOver.toScheme B S hS).map c).appTop.hom)
    (eY : yoneda.obj Yw ≅ Uw.obj) (heY : eY.hom ≫ iUw.hom = yoneda.map c)
    (mT₀ : T₀ ⟶ T) [AlgebraicGeometry.IsOpenImmersion ((BigFppfOver.toScheme B S hS).map mT₀)]
      (κ : T₀ ⟶ Yw)
    (θ₀ : (algebraicSpaceStackFunctor.{u, w} B S hS).map
      (repHom mT₀ ≫ (ObjectProperty.homMk t : Space.yonedaSpace _ _ _ T ⟶ W)) ≫ x ≅
      (algebraicSpaceStackFunctor.{u, w} B S hS).map
        (repHom κ ≫ (ObjectProperty.homMk eY.hom : Space.yonedaSpace _ _ _ Yw ⟶ Uw)) ≫ aw)
    (S₁ : Type u) [CommRing S₁] [Algebra Γ((BigFppfOver.toScheme B S hS).obj V, ⊤) S₁]
      [Algebra.FiniteType Γ((BigFppfOver.toScheme B S hS).obj V, ⊤) S₁]
    (lam : Γ((BigFppfOver.toScheme B S hS).obj T₀, ⊤) →+* S₁ ⧸
      (RingHom.ker ((BigFppfOver.toScheme B S hS).map c).appTop.hom).map
      (algebraMap Γ((BigFppfOver.toScheme B S hS).obj V, ⊤) S₁))
    (hlam : lam.comp ((BigFppfOver.toScheme B S hS).map κ).appTop.hom = BigFppfOver.quotientBaseMap
      ((BigFppfOver.toScheme B S hS).map c).appTop hπ S₁)
    (d : Γ((BigFppfOver.toScheme B S hS).obj T₀, ⊤))
      (hloc : @IsLocalization.Away _ _ d (S₁ ⧸ (RingHom.ker
      ((BigFppfOver.toScheme B S hS).map c).appTop.hom).map
        (algebraMap Γ((BigFppfOver.toScheme B S hS).obj V, ⊤) S₁)) _ lam.toAlgebra)
    (y₀ : (BigFppfOver.toScheme B S hS).obj T₀)
      (hd : d ∉ (((BigFppfOver.toScheme B S hS).obj T₀).isoSpec.hom y₀).asIdeal)
    (h' : S₁) (hh' : Ideal.Quotient.mk _ h' ∉
      (((BigFppfOver.toScheme B S hS).obj T₀).isoSpec.hom y₀).asIdeal.map lam)
    (hsm : AlgebraicStacks.IsSmooth B S hS
      ((algebraicSpaceStackFunctor.{u, w} B S hS).map
        (repHom (BigFppfOver.specObjToBase V (Localization.Away h'))) ≫ bw)) :
    ∃ (A : BigFppfOver B S hS) (m : A ⟶ T) (hm : Space.IsEtale B S hS (yoneda.map m ≫ t))
      (ξ : EtaleSmoothLift B S hS ι hι W x hx),
      (BigFppfOver.toScheme B S hS).map mT₀ y₀ ∈ Set.range ((BigFppfOver.toScheme B S hS).map m) ∧
      ξ.base = Space.SpacesEtale.ofRepresentable B S hS W A (yoneda.map m ≫ t) hm := by
  obtain ⟨m', hm'et, ⟨y', hy'⟩, hm'κ⟩ := exists_awayQuotient_open c
    ((BigFppfOver.toScheme B S hS).map c).appTop rfl hπ κ S₁ lam hlam d hloc y₀ hd h' hh'
    (BigFppfOver.awayQuotientBase_comp ((BigFppfOver.toScheme B S hS).map c).appTop hπ S₁ h')
  let m := m' ≫ mT₀
  have hm : Space.IsEtale B S hS (yoneda.map m ≫ t) :=
    Space.isEtale_comp B S hS ((Space.isEtale_iff_presheaf_of_yoneda B S hS _).2
      ((Space.presheaf_yoneda_map_etale_iff B S hS _).2
        (by rw [Functor.map_comp]; infer_instance))) ht
  have e1 : (ObjectProperty.homMk (yoneda.map m ≫ t) :
      Space.yonedaSpace _ _ _ (BigFppfOver.specObj V
        (BigFppfOver.AwayQuotient ((BigFppfOver.toScheme B S hS).map c).appTop S₁ h')) ⟶ W) =
      repHom m' ≫ (repHom mT₀ ≫ (ObjectProperty.homMk t : Space.yonedaSpace _ _ _ T ⟶ W)) :=
    ObjectProperty.hom_ext _
      ((congrArg (· ≫ t) (yoneda.map_comp m' mT₀)).trans (Category.assoc _ _ _))
  have e2 : repHom m' ≫
      (repHom κ ≫ (ObjectProperty.homMk eY.hom : Space.yonedaSpace _ _ _ Yw ⟶ Uw)) =
      repHom (BigFppfOver.specObjHom c
        (BigFppfOver.awayQuotientBase ((BigFppfOver.toScheme B S hS).map c).appTop hπ S₁ h')
        (BigFppfOver.awayQuotientBase_comp ((BigFppfOver.toScheme B S hS).map c).appTop hπ S₁ h')) ≫
        (ObjectProperty.homMk eY.hom : Space.yonedaSpace _ _ _ Yw ⟶ Uw) :=
    (Category.assoc _ _ _).symm.trans
      (congrArg (· ≫ (ObjectProperty.homMk eY.hom : Space.yonedaSpace _ _ _ Yw ⟶ Uw))
        ((repHom_comp m' κ).symm.trans (congrArg repHom hm'κ)))
  let ea := eqToIso (congrArg (fun f => (algebraicSpaceStackFunctor.{u, w} B S hS).map f ≫ x) e1) ≪≫
    whiskerTwoIso' (repHom m') θ₀ ≪≫
    eqToIso (congrArg (fun f => (algebraicSpaceStackFunctor.{u, w} B S hS).map f ≫ aw) e2)
  obtain ⟨ξ, hξ⟩ := exists_etaleSmoothLift_of_isPullback hι W x hx hUw c eY heY _ _ _
    (BigFppfOver.isPullback_yoneda_awayQuotient c hπ S₁ h') hsm (yoneda.map m ≫ t) hm ea
  exact ⟨_, m, hm, ξ, ⟨y', congrArg ((BigFppfOver.toScheme B S hS).map mT₀) hy'⟩, hξ⟩

/-- The fifth step of `exists_local_etaleSmoothLift`: the Jacobian chart of the lifted
presentation, and the smoothness of `T'_w` over `𝒳'`. -/
theorem exists_local_etaleSmoothLift_of_presentation (hι : IsThickening ι)
    (W : AlgebraicSpaces B S hS) (x : (algebraicSpaceStackFunctor.{u, w} B S hS).obj W ⟶ 𝒳)
      (hx : AlgebraicStacks.IsSmooth B S hS x)
    {T : BigFppfOver B S hS} (t : yoneda.obj T ⟶ W.obj) (ht : Space.IsEtale B S hS t)
    {V Yw T₀ E : BigFppfOver B S hS} [IsAffine ((BigFppfOver.toScheme B S hS).obj V)]
      [IsAffine ((BigFppfOver.toScheme B S hS).obj Yw)]
    [IsAffine ((BigFppfOver.toScheme B S hS).obj T₀)]
      [IsAffine ((BigFppfOver.toScheme B S hS).obj E)]
    {bw : (algebraicSpaceStackFunctor.{u, w} B S hS).obj (Space.yonedaSpace _ _ _ V) ⟶ 𝒳'}
      (hbw : AlgebraicStacks.IsSmooth B S hS bw)
    {Uw : AlgebraicSpaces B S hS} {iUw : Uw ⟶ Space.yonedaSpace _ _ _ V}
    {aw : (algebraicSpaceStackFunctor.{u, w} B S hS).obj Uw ⟶ 𝒳}
      {γw : (algebraicSpaceStackFunctor.{u, w} B S hS).map iUw ≫ bw ≅ aw ≫ ι}
    (hUw : IsTwoFibreProduct (⟨_, _, _, γw⟩ : TwoCommSq bw ι))
    (c : Yw ⟶ V) (hπ : Function.Surjective ((BigFppfOver.toScheme B S hS).map c).appTop.hom)
    (hJ : RingHom.ker ((BigFppfOver.toScheme B S hS).map c).appTop.hom ≤ nilradical
      Γ((BigFppfOver.toScheme B S hS).obj V, ⊤))
    (eY : yoneda.obj Yw ≅ Uw.obj) (heY : eY.hom ≫ iUw.hom = yoneda.map c)
    (mT₀ : T₀ ⟶ T) [AlgebraicGeometry.IsOpenImmersion ((BigFppfOver.toScheme B S hS).map mT₀)]
      (κ : T₀ ⟶ Yw)
    (θ₀ : (algebraicSpaceStackFunctor.{u, w} B S hS).map
      (repHom mT₀ ≫ (ObjectProperty.homMk t : Space.yonedaSpace _ _ _ T ⟶ W)) ≫ x ≅
      (algebraicSpaceStackFunctor.{u, w} B S hS).map
        (repHom κ ≫ (ObjectProperty.homMk eY.hom : Space.yonedaSpace _ _ _ Yw ⟶ Uw)) ≫ aw)
    [Algebra Γ((BigFppfOver.toScheme B S hS).obj Yw, ⊤) Γ((BigFppfOver.toScheme B S hS).obj T₀, ⊤)]
    (hκalg : algebraMap Γ((BigFppfOver.toScheme B S hS).obj Yw, ⊤)
      Γ((BigFppfOver.toScheme B S hS).obj T₀, ⊤) = ((BigFppfOver.toScheme B S hS).map κ).appTop.hom)
    (y₀ : (BigFppfOver.toScheme B S hS).obj T₀)
    {n r : ℕ} (g'' : MvPolynomial (Fin n) Γ((BigFppfOver.toScheme B S hS).obj V, ⊤))
    (f'' : Fin r → MvPolynomial (Fin n) Γ((BigFppfOver.toScheme B S hS).obj V, ⊤))
    (lam : Γ((BigFppfOver.toScheme B S hS).obj T₀, ⊤) →+* Algebra.LiftedPresentation.Reduced
      ((BigFppfOver.toScheme B S hS).map c).appTop.hom g'' f'')
    (hlamB : (lam.comp (algebraMap
      Γ((BigFppfOver.toScheme B S hS).obj Yw, ⊤) Γ((BigFppfOver.toScheme B S hS).obj T₀, ⊤))).comp
      ((BigFppfOver.toScheme B S hS).map c).appTop.hom =
      algebraMap Γ((BigFppfOver.toScheme B S hS).obj V, ⊤) (Algebra.LiftedPresentation.Reduced
        ((BigFppfOver.toScheme B S hS).map c).appTop.hom g'' f''))
    (d : Γ((BigFppfOver.toScheme B S hS).obj T₀, ⊤))
    (hloc : @IsLocalization.Away _ _ d
      (Algebra.LiftedPresentation.Reduced ((BigFppfOver.toScheme B S hS).map c).appTop.hom
      g'' f'') _ lam.toAlgebra)
    (hd : d ∉ (((BigFppfOver.toScheme B S hS).obj T₀).isoSpec.hom y₀).asIdeal)
    (hrel : ∀ a : Fin r → Algebra.LiftedPresentation.AmbientReduced
      ((BigFppfOver.toScheme B S hS).map c).appTop.hom g'',
      ∑ i, a i * Ideal.Quotient.mk _ (algebraMap _ (Localization.Away g'') (f'' i)) = 0 →
      ∀ i, a i ∈ ((((((BigFppfOver.toScheme B S hS).obj T₀).isoSpec.hom y₀).asIdeal.map lam).comap
        (Ideal.Quotient.mk _)).comap
        (algebraMap (Localization.Away g'') (Algebra.LiftedPresentation.Chart g'' f''))).map
          (Ideal.Quotient.mk _))
    (sE tE : E ⟶ V) (ρE : (algebraicSpaceStackFunctor.{u, w} B S hS).map (repHom sE) ≫ bw ≅
      (algebraicSpaceStackFunctor.{u, w} B S hS).map (repHom tE) ≫ bw)
    [Algebra Γ((BigFppfOver.toScheme B S hS).obj V, ⊤) Γ((BigFppfOver.toScheme B S hS).obj E, ⊤)]
      [Algebra.Smooth Γ((BigFppfOver.toScheme B S hS).obj V, ⊤)
      Γ((BigFppfOver.toScheme B S hS).obj E, ⊤)]
    (hs : algebraMap Γ((BigFppfOver.toScheme B S hS).obj V, ⊤)
      Γ((BigFppfOver.toScheme B S hS).obj E, ⊤) = ((BigFppfOver.toScheme B S hS).map sE).appTop.hom)
    (hτ : @Algebra.Smooth
      Γ((BigFppfOver.toScheme B S hS).obj V, ⊤) _ Γ((BigFppfOver.toScheme B S hS).obj E, ⊤) _
      ((BigFppfOver.toScheme B S hS).map tE).appTop.hom.toAlgebra)
    (hE0 : (RingHom.ker ((BigFppfOver.toScheme B S hS).map c).appTop.hom).map (algebraMap
      Γ((BigFppfOver.toScheme B S hS).obj V, ⊤) Γ((BigFppfOver.toScheme B S hS).obj E, ⊤)) =
      (RingHom.ker ((BigFppfOver.toScheme B S hS).map c).appTop.hom).map
        ((BigFppfOver.toScheme B S hS).map tE).appTop.hom)
    (ψ : Γ((BigFppfOver.toScheme B S hS).obj Yw, ⊤) →+* Algebra.LiftedPresentation.Reduced
      ((BigFppfOver.toScheme B S hS).map c).appTop.hom g'' f'' ⊗[
      Γ((BigFppfOver.toScheme B S hS).obj V, ⊤)] Γ((BigFppfOver.toScheme B S hS).obj E, ⊤))
        (hψ : ψ.Smooth)
    (hψeq : ψ.comp ((BigFppfOver.toScheme B S hS).map c).appTop.hom =
      Algebra.TensorProduct.includeRight.toRingHom.comp
        ((BigFppfOver.toScheme B S hS).map tE).appTop.hom)
    (𝔢 : Ideal Γ((BigFppfOver.toScheme B S hS).obj E, ⊤)) [𝔢.IsPrime]
    (h𝔢 : 𝔢.comap (algebraMap Γ((BigFppfOver.toScheme B S hS).obj V, ⊤)
      Γ((BigFppfOver.toScheme B S hS).obj E, ⊤)) =
      (((BigFppfOver.toScheme B S hS).obj T₀).isoSpec.hom y₀).asIdeal.comap
        ((algebraMap Γ((BigFppfOver.toScheme B S hS).obj Yw, ⊤)
          Γ((BigFppfOver.toScheme B S hS).obj T₀, ⊤)).comp
          ((BigFppfOver.toScheme B S hS).map c).appTop.hom)) :
    ∃ (A : BigFppfOver B S hS) (m : A ⟶ T) (hm : Space.IsEtale B S hS (yoneda.map m ≫ t))
      (ξ : EtaleSmoothLift B S hS ι hι W x hx),
      (BigFppfOver.toScheme B S hS).map mT₀ y₀ ∈ Set.range ((BigFppfOver.toScheme B S hS).map m) ∧
      ξ.base = Space.SpacesEtale.ofRepresentable B S hS W A (yoneda.map m ≫ t) hm := by
  have hchart := exists_smooth_chart_of_liftedPresentation
    ((BigFppfOver.toScheme B S hS).map c).appTop.hom hπ hJ
    (((BigFppfOver.toScheme B S hS).obj T₀).isoSpec.hom y₀).asIdeal g'' f'' lam hlamB d hloc hd hrel
    ((BigFppfOver.toScheme B S hS).map tE).appTop.hom hτ hE0 ψ hψ hψeq 𝔢 h𝔢
  choose h' hh' Pr _ α β hαβ hαsm hαsurj hβsm using hchart
  have hsm := isSmooth_specAway_of_chart bw hbw sE tE ρE hs
    (Algebra.LiftedPresentation.Chart g'' f'') h' Pr α β hαβ hαsm hαsurj hβsm
  have hlam' : lam.comp ((BigFppfOver.toScheme B S hS).map κ).appTop.hom =
      BigFppfOver.quotientBaseMap ((BigFppfOver.toScheme B S hS).map c).appTop hπ
        (Algebra.LiftedPresentation.Chart g'' f'') :=
    BigFppfOver.eq_quotientBaseMap_of_comp ((BigFppfOver.toScheme B S hS).map c).appTop hπ _ _
      (by rwa [← hκalg])
  exact exists_local_etaleSmoothLift_of_chart hι W x hx t ht hUw c hπ eY heY mT₀ κ θ₀
    (Algebra.LiftedPresentation.Chart g'' f'') lam hlam' d hloc y₀ hd h' hh' hsm

/-- The third and fourth steps of `exists_local_etaleSmoothLift`: the lifted presentation, the
étale chart of `U'_w ×_{𝒳'} U'_w`, and the smoothness of the reduced chart over `Y_w`. -/
theorem exists_local_etaleSmoothLift_of_factor (hι : IsThickening ι)
    (W : AlgebraicSpaces B S hS) (x : (algebraicSpaceStackFunctor.{u, w} B S hS).obj W ⟶ 𝒳)
      (hx : AlgebraicStacks.IsSmooth B S hS x)
    {T : BigFppfOver B S hS} (t : yoneda.obj T ⟶ W.obj) (ht : Space.IsEtale B S hS t)
    {V Yw T₀ : BigFppfOver B S hS} [IsAffine ((BigFppfOver.toScheme B S hS).obj V)]
      [IsAffine ((BigFppfOver.toScheme B S hS).obj Yw)]
    [IsAffine ((BigFppfOver.toScheme B S hS).obj T₀)]
    {bw : (algebraicSpaceStackFunctor.{u, w} B S hS).obj (Space.yonedaSpace _ _ _ V) ⟶ 𝒳'}
      (hbw : AlgebraicStacks.IsSmooth B S hS bw)
    {Uw : AlgebraicSpaces B S hS} {iUw : Uw ⟶ Space.yonedaSpace _ _ _ V}
    {aw : (algebraicSpaceStackFunctor.{u, w} B S hS).obj Uw ⟶ 𝒳}
      {γw : (algebraicSpaceStackFunctor.{u, w} B S hS).map iUw ≫ bw ≅ aw ≫ ι}
    (hUw : IsTwoFibreProduct (⟨_, _, _, γw⟩ : TwoCommSq bw ι))
    (c : Yw ⟶ V) [AlgebraicGeometry.IsClosedImmersion ((BigFppfOver.toScheme B S hS).map c)]
    (hcsurj : Function.Surjective ((BigFppfOver.toScheme B S hS).map c))
    (eY : yoneda.obj Yw ≅ Uw.obj) (heY : eY.hom ≫ iUw.hom = yoneda.map c)
    (mT₀ : T₀ ⟶ T) [AlgebraicGeometry.IsOpenImmersion ((BigFppfOver.toScheme B S hS).map mT₀)]
      (εV : T₀ ⟶ V) (κ : T₀ ⟶ Yw)
    (hκ : κ ≫ c = εV)
      (hκlfp : AlgebraicGeometry.LocallyOfFinitePresentation ((BigFppfOver.toScheme B S hS).map κ))
    (θ₀ : (algebraicSpaceStackFunctor.{u, w} B S hS).map
      (repHom mT₀ ≫ (ObjectProperty.homMk t : Space.yonedaSpace _ _ _ T ⟶ W)) ≫ x ≅
      (algebraicSpaceStackFunctor.{u, w} B S hS).map
        (repHom κ ≫ (ObjectProperty.homMk eY.hom : Space.yonedaSpace _ _ _ Yw ⟶ Uw)) ≫ aw)
    (y₀ : (BigFppfOver.toScheme B S hS).obj T₀) :
    ∃ (A : BigFppfOver B S hS) (m : A ⟶ T) (hm : Space.IsEtale B S hS (yoneda.map m ≫ t))
      (ξ : EtaleSmoothLift B S hS ι hι W x hx),
      (BigFppfOver.toScheme B S hS).map mT₀ y₀ ∈ Set.range ((BigFppfOver.toScheme B S hS).map m) ∧
      ξ.base = Space.SpacesEtale.ofRepresentable B S hS W A (yoneda.map m ≫ t) hm := by
  classical
  have hπ : Function.Surjective ((BigFppfOver.toScheme B S hS).map c).appTop.hom :=
    Scheme.Hom.app_surjective _ ⊤ (isAffineOpen_top _)
  have hJ : RingHom.ker ((BigFppfOver.toScheme B S hS).map c).appTop.hom ≤ nilradical
      Γ((BigFppfOver.toScheme B S hS).obj V, ⊤) :=
    ker_le_nilradical_of_surjective _ hcsurj
  let : Algebra Γ((BigFppfOver.toScheme B S hS).obj Yw, ⊤)
      Γ((BigFppfOver.toScheme B S hS).obj T₀, ⊤) :=
    ((BigFppfOver.toScheme B S hS).map κ).appTop.hom.toAlgebra
  have : Algebra.FinitePresentation Γ((BigFppfOver.toScheme B S hS).obj Yw, ⊤)
      Γ((BigFppfOver.toScheme B S hS).obj T₀, ⊤) :=
    RingHom.finitePresentation_algebraMap.mp
      ((HasRingHomProperty.iff_of_isAffine (P := @AlgebraicGeometry.LocallyOfFinitePresentation)).mp
        hκlfp)
  have hlp := Algebra.exists_liftedPresentation ((BigFppfOver.toScheme B S hS).map c).appTop.hom hπ
    (((BigFppfOver.toScheme B S hS).obj T₀).isoSpec.hom y₀).asIdeal
  choose n r g'' f'' lam hlamB hloc' hrel using hlp
  choose d hd hloc using hloc'
  obtain ⟨y₀p, hy₀p⟩ := (Space.bijective_pointsToScheme B S hS T₀).surjective y₀
  have hchart := exists_affine_selfProduct_chart bw hbw
    (Space.pointsMap B S hS (yoneda.obj T₀) (yoneda.map εV) y₀p)
  choose R sR tR ρ hR' E eE sE tE hEaff heE hsE htE hsEsm htEsm e₀ he₀ using hchart
  have hR := hR'.some
  have := hEaff
  let : Algebra Γ((BigFppfOver.toScheme B S hS).obj V, ⊤)
      Γ((BigFppfOver.toScheme B S hS).obj E, ⊤) :=
    ((BigFppfOver.toScheme B S hS).map sE).appTop.hom.toAlgebra
  have hsm : ∀ f : E ⟶ V, Space.IsSmooth B S hS (yoneda.map f) →
      @Algebra.Smooth Γ((BigFppfOver.toScheme B S hS).obj V, ⊤) _
        Γ((BigFppfOver.toScheme B S hS).obj E, ⊤) _
        ((BigFppfOver.toScheme B S hS).map f).appTop.hom.toAlgebra := fun f hf =>
    (HasRingHomProperty.iff_of_isAffine (P := @AlgebraicGeometry.Smooth)).mp
      ((Space.isSmooth_yoneda_map_iff B S hS f).mp hf)
  have hCsm := hsm sE hsEsm
  have hτsm := hsm tE htEsm
  let ρE : (algebraicSpaceStackFunctor.{u, w} B S hS).map (repHom sE) ≫ bw ≅
      (algebraicSpaceStackFunctor.{u, w} B S hS).map (repHom tE) ≫ bw :=
    eqToIso (by rw [hsE]) ≪≫ whiskerTwoIso eE bw ρ ≪≫ eqToIso (by rw [htE])
  have hE0 : (RingHom.ker ((BigFppfOver.toScheme B S hS).map c).appTop.hom).map
      (algebraMap Γ((BigFppfOver.toScheme B S hS).obj V, ⊤)
        Γ((BigFppfOver.toScheme B S hS).obj E, ⊤)) =
      (RingHom.ker ((BigFppfOver.toScheme B S hS).map c).appTop.hom).map
        ((BigFppfOver.toScheme B S hS).map tE).appTop.hom :=
    le_antisymm (map_ker_le_map_of_twoIso hUw c hπ eY heY tE sE ρE.symm)
      (map_ker_le_map_of_twoIso hUw c hπ eY heY sE tE ρE)
  have hεapp : ((BigFppfOver.toScheme B S hS).map εV).appTop.hom =
      (algebraMap Γ((BigFppfOver.toScheme B S hS).obj Yw, ⊤)
        Γ((BigFppfOver.toScheme B S hS).obj T₀, ⊤)).comp
        ((BigFppfOver.toScheme B S hS).map c).appTop.hom := by
    rw [← hκ, Functor.map_comp, Scheme.Hom.comp_appTop, CommRingCat.hom_comp]
    rfl
  have hlamε : lam.comp ((BigFppfOver.toScheme B S hS).map εV).appTop.hom = algebraMap
      Γ((BigFppfOver.toScheme B S hS).obj V, ⊤)
      (Algebra.LiftedPresentation.Reduced ((BigFppfOver.toScheme B S hS).map c).appTop.hom g''
        f'') :=
    (congrArg lam.comp hεapp).trans hlamB
  have hψ := exists_smooth_reduced_tensor W x hx t ht hUw c eY heY hR eE heE
    sE tE hsE htE rfl mT₀ εV κ hκ θ₀ _ lam hlamε d hloc
  choose ψ hψsm hψeq using hψ
  have hpt : (BigFppfOver.toScheme B S hS).map sE (Space.pointsToScheme B S hS E e₀) =
      (BigFppfOver.toScheme B S hS).map εV y₀ := by
    rw [← Space.pointsToScheme_pointsMap_yoneda, he₀, Space.pointsToScheme_pointsMap_yoneda, hy₀p]
  have h𝔢 : ((((BigFppfOver.toScheme B S hS).obj E).isoSpec.hom
      (Space.pointsToScheme B S hS E e₀)).asIdeal).comap
        (algebraMap Γ((BigFppfOver.toScheme B S hS).obj V, ⊤)
          Γ((BigFppfOver.toScheme B S hS).obj E, ⊤)) =
      (((BigFppfOver.toScheme B S hS).obj T₀).isoSpec.hom y₀).asIdeal.comap
        ((algebraMap Γ((BigFppfOver.toScheme B S hS).obj Yw, ⊤)
          Γ((BigFppfOver.toScheme B S hS).obj T₀, ⊤)).comp
          ((BigFppfOver.toScheme B S hS).map c).appTop.hom) := by
    have h1 := congrArg PrimeSpectrum.asIdeal (isoSpec_hom_apply_eq_comap
      ((BigFppfOver.toScheme B S hS).map sE) (Space.pointsToScheme B S hS E e₀))
    have h2 := congrArg PrimeSpectrum.asIdeal
      (isoSpec_hom_apply_eq_comap ((BigFppfOver.toScheme B S hS).map εV) y₀)
    rw [hpt] at h1
    rw [hεapp] at h2
    exact h1.symm.trans h2
  exact exists_local_etaleSmoothLift_of_presentation hι W x hx t ht hbw hUw c hπ hJ eY heY mT₀ κ
    θ₀ rfl y₀ g'' f'' lam hlamB d hloc hd hrel sE tE ρE rfl hτsm hE0 ψ hψsm hψeq _ h𝔢

/-- **The local step of Stacks 0CJV.** Let `ι : 𝒳 ⟶ 𝒳'` be a thickening, `x : W ⟶ 𝒳` smooth, and
`U = U' ×_{𝒳'} 𝒳` the base change of a smooth `b : U' ⟶ 𝒳'` by a scheme of the site, with
`U ⟶ U'` a monomorphism. Let `T` be a scheme of the site with an étale `t : T ⟶ W` and a morphism
`e : T ⟶ U` locally of finite presentation, with `x ∘ t ≅ a ∘ e`. Then every point of `T` has an
open neighbourhood `A ⊆ T` which is the base of a smooth lift along `ι`. -/
theorem exists_local_etaleSmoothLift (hι : IsThickening ι)
    (W : AlgebraicSpaces B S hS)
    (x : (algebraicSpaceStackFunctor.{u, w} B S hS).obj W ⟶ 𝒳)
    (hx : AlgebraicStacks.IsSmooth B S hS x)
    {U' : BigFppfOver B S hS}
    (b : (algebraicSpaceStackFunctor.{u, w} B S hS).obj (Space.yonedaSpace _ _ _ U') ⟶ 𝒳')
    (hb : AlgebraicStacks.IsSmooth B S hS b)
    {U : AlgebraicSpaces B S hS} (iU : U ⟶ Space.yonedaSpace _ _ _ U') [Mono iU.hom]
    (a : (algebraicSpaceStackFunctor.{u, w} B S hS).obj U ⟶ 𝒳)
    {γ : (algebraicSpaceStackFunctor.{u, w} B S hS).map iU ≫ b ≅ a ≫ ι}
    (hU : IsTwoFibreProduct (⟨_, _, _, γ⟩ : TwoCommSq b ι))
    (T : BigFppfOver B S hS) (t : yoneda.obj T ⟶ W.obj) (ht : Space.IsEtale B S hS t)
    (e : Space.yonedaSpace _ _ _ T ⟶ U) (he : Space.IsLocallyOfFinitePresentation B S hS e.hom)
    (η : (algebraicSpaceStackFunctor.{u, w} B S hS).map
        (ObjectProperty.homMk t : Space.yonedaSpace _ _ _ T ⟶ W) ≫ x ≅
      (algebraicSpaceStackFunctor.{u, w} B S hS).map e ≫ a)
    (y : (BigFppfOver.toScheme B S hS).obj T) :
    ∃ (A : BigFppfOver B S hS) (m : A ⟶ T) (hm : Space.IsEtale B S hS (yoneda.map m ≫ t))
      (ξ : EtaleSmoothLift B S hS ι hι W x hx),
      y ∈ Set.range ((BigFppfOver.toScheme B S hS).map m) ∧
      ξ.base = Space.SpacesEtale.ofRepresentable B S hS W A (yoneda.map m ≫ t) hm := by
  classical
  let εU : T ⟶ U' := yoneda.preimage (e.hom ≫ iU.hom)
  have hεU : yoneda.map εU = e.hom ≫ iU.hom := Functor.map_preimage _ _
  obtain ⟨V, ιV, T₀, mT₀, εV, hVaff, hT₀aff, hιV, hmT₀, hεsq, y₀, hy₀⟩ :=
    BigFppfOver.exists_affine_shrink εU y
  have := hVaff
  have := hT₀aff
  have := hιV
  have := hmT₀
  let bw := (algebraicSpaceStackFunctor.{u, w} B S hS).map (repHom ιV) ≫ b
  have hbw : AlgebraicStacks.IsSmooth B S hS bw :=
    AlgebraicStacks.isSmooth_comp B S hS _ _
      (isSmooth_map_yoneda_of_etale.{u, w} ιV inferInstance) hb
  obtain ⟨Uw, iUw, aw, γw, ⟨hUw⟩, -, hmono, hthick⟩ := exists_thickeningChart_square ι hι bw hbw
  have := hmono
  obtain ⟨Yw, c, eY, heY, hcl, hcsurj⟩ := exists_closedSubscheme_of_isThickening iUw hthick
  have := hcl
  have : IsAffine ((BigFppfOver.toScheme B S hS).obj Yw) :=
    isAffine_of_isAffineHom ((BigFppfOver.toScheme B S hS).map c)
  obtain ⟨κ, hκ, hκlfp, ⟨θ₀⟩⟩ := exists_reduction_factor W x b iU a hU t e he η ιV mT₀ εV εU
    hεU hεsq hUw c eY heY
  have h := exists_local_etaleSmoothLift_of_factor hι W x hx t ht hbw hUw c hcsurj eY heY mT₀ εV
    κ hκ hκlfp θ₀ y₀
  rwa [hy₀] at h

end AlgebraicGeometry.Stack.LiftingAffinesLocal

end
