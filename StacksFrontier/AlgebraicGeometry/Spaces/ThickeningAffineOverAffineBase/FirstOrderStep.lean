module

public import StacksFrontier.AlgebraicGeometry.MoreMorphisms.ThickeningAffineFirstOrder
public import StacksFrontier.AlgebraicGeometry.Spaces.PointsAndCoverings.SpecialCoverings
public import StacksFrontier.AlgebraicGeometry.Spaces.QuasiCompactSurjection
public import StacksFrontier.AlgebraicGeometry.Spaces.Thickenings.FirstOrderGlobalFunctionsAffineBase
public import StacksFrontier.AlgebraicGeometry.Spaces.ThickeningAffineOverAffineBase.ChartValues
public import StacksFrontier.AlgebraicGeometry.Spaces.ThickeningAffineOverAffineBase.PresentationLift
public import StacksFrontier.AlgebraicGeometry.Spaces.ThickeningAffineOverAffineBase.QuotientPushout

/-!
# Affineness over a first-order thickening of an affine base

Let `U` be an algebraic space over an affine object `T` of the site and let `T₀ ⟶ T` be a
first-order thickening.  If `U ×_T T₀` is affine, then `U` is affine.

This is the presentation step `AlgebraicGeometry.Space.exists_iso_yoneda_of_presentationLift`
fed with the two lifts it asks for:

* the coefficients of a submersive presentation of the thin chart are global functions on the
  thin part `U ×_T T₀`, and lift to global functions on `U` because global functions extend over
  a first-order thickening of an affine base change
  (`AlgebraicGeometry.Space.surjective_globalFunctionsMap_pullback_of_isFirstOrderThickening`);
* the generators lift to roots of the lifted relations by formal étaleness of the localized
  quotient, the kernel of `Γ(W) ⟶ Γ(W ×_T T₀)` being of square zero.

Then `U` is represented by a scheme, which is affine by Stacks 06AD.

## Main results

* `AlgebraicGeometry.Space.exists_generic_presentation`: an étale algebra has a submersive
  presentation whose relations are the specializations of polynomials with indeterminate
  coefficients.
* `AlgebraicGeometry.Space.isAffineSpace_of_isFirstOrderThickening_pullback`.
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits MvPolynomial

universe u

namespace AlgebraicGeometry.Space

/-- **A submersive presentation with generic coefficients.**  An étale `C₀`-algebra `D₀` has a
submersive presentation with as many relations as variables, whose relations are the
specializations along `y_c ↦ coef c` of polynomials over `A[y_F]`, for any ring map
`A ⟶ C₀`. -/
theorem exists_generic_presentation {A C₀ D₀ : Type u} [CommRing A] [CommRing C₀] [CommRing D₀]
    [Algebra C₀ D₀] [Algebra.Etale C₀ D₀] (φA : A →+* C₀) :
    ∃ (τ σ : Type) (_ : Finite τ) (_ : Finite σ)
      (P₀ : Algebra.SubmersivePresentation C₀ D₀ τ σ) (F : Type) (_ : Finite F)
      (coef : F → C₀) (g : σ → MvPolynomial τ (MvPolynomial F A)),
      Nat.card τ = Nat.card σ ∧ ∀ j, (g j).map (eval₂Hom φA coef) = P₀.relation j := by
  classical
  obtain ⟨τ, σ, hσ, hτ, P₀, hdim⟩ :=
    (Algebra.Etale.iff_isStandardSmoothOfRelativeDimension_zero (R := C₀) (S := D₀)).mp
      inferInstance |>.out
  have hle := P₀.toPreSubmersivePresentation.card_relations_le_card_vars_of_isFinite
  have hcard : Nat.card τ = Nat.card σ := by
    simp only [Algebra.Presentation.dimension] at hdim
    lia
  let F := Σ j : σ, (P₀.relation j).support
  refine ⟨τ, σ, hτ, hσ, P₀, F, inferInstance, fun c ↦ (P₀.relation c.1).coeff c.2.1,
    fun j ↦ ∑ d ∈ (P₀.relation j).support.attach, monomial d.1 (X ⟨j, d⟩), hcard, fun j ↦ ?_⟩
  rw [map_sum]
  simp only [map_monomial, eval₂Hom_X']
  conv_rhs => rw [(P₀.relation j).as_sum]
  exact Finset.sum_attach _ (fun d ↦ monomial d ((P₀.relation j).coeff d))

variable (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)

/-- The base change of a surjective morphism of the site along a morphism of presheaves into
its target is surjective. -/
theorem isSurjective_pullback_fst_yoneda {U : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u}
    (hU : IsAlgebraicSpace B S hS U) {T₀ T : BigFppfOver B S hS} (k : T₀ ⟶ T)
    (hk : Surjective ((BigFppfOver.toScheme B S hS).map k)) (π : U ⟶ yoneda.obj T) :
    IsSurjective B S hS (pullback.fst π (yoneda.map k)) := by
  have hP := isAlgebraicSpace_pullback B S hS π (yoneda.map k) hU
    (isAlgebraicSpace_yoneda B S hS T₀) (isAlgebraicSpace_yoneda B S hS T)
  let sq : IsPullback (P := (⟨_, hP⟩ : AlgebraicSpaces B S hS))
      (X := (⟨_, isAlgebraicSpace_yoneda B S hS T₀⟩ : AlgebraicSpaces B S hS))
      (Y := (⟨_, hU⟩ : AlgebraicSpaces B S hS))
      (Z := (⟨_, isAlgebraicSpace_yoneda B S hS T⟩ : AlgebraicSpaces B S hS))
      (ObjectProperty.homMk (pullback.snd π (yoneda.map k)))
      (ObjectProperty.homMk (pullback.fst π (yoneda.map k)))
      (ObjectProperty.homMk (yoneda.map k)) (ObjectProperty.homMk π) :=
    IsPullback.of_map_of_faithful (ObjectProperty.ι _) (IsPullback.of_hasPullback _ _).flip
  exact isSurjective_of_isPullback B S hS sq (isSurjective_yoneda_map B S hS k hk)

/-- **An algebraic space over an affine base whose base change to a first-order thickening of
the base is affine is affine.** -/
theorem isAffineSpace_of_isFirstOrderThickening_pullback {U : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u}
    (hU : IsAlgebraicSpace B S hS U) {T₀ T : BigFppfOver B S hS}
    [IsAffine ((BigFppfOver.toScheme B S hS).obj T)] (k : T₀ ⟶ T)
    (hk : Stacks.Thickenings.IsFirstOrderThickening ((BigFppfOver.toScheme B S hS).map k))
    (π : U ⟶ yoneda.obj T) (hU₀ : IsAffineSpace B S hS (pullback π (yoneda.map k))) :
    IsAffineSpace B S hS U := by
  classical
  have hkth := hk.isThickening
  have : _root_.AlgebraicGeometry.IsClosedImmersion ((BigFppfOver.toScheme B S hS).map k) := hk.1
  have : IsAffine ((BigFppfOver.toScheme B S hS).obj T₀) :=
    isAffine_of_isAffineHom ((BigFppfOver.toScheme B S hS).map k)
  have hU₀alg := hU₀.isAlgebraicSpace
  have hfst := isSurjective_pullback_fst_yoneda B S hS hU k ⟨hkth.2⟩ π
  have hqc : IsQuasiCompactSpace B S hS U :=
    IsQuasiCompactSpace.of_isSurjective B S hS hU₀alg hU hfst hU₀.isQuasiCompactSpace
  obtain ⟨W, w, hWaff, hws, hwe'⟩ :=
    (isQuasiCompactSpace_iff_exists_affine_etale_surjective_cover B S hS U hU).mp hqc
  have hwe := (isEtale_iff_presheaf_of_yoneda B S hS w).1 hwe'
  have hR := hws.rep.isPullback' w
  have hU₀' := hU₀
  obtain ⟨O₀, hO₀, ⟨e₀⟩⟩ := hU₀'
  have : IsAffine ((BigFppfOver.toScheme B S hS).obj O₀) := hO₀
  have : IsAffine ((BigFppfOver.toScheme B S hS).obj W) := hWaff
  -- the thin point and the thin chart
  set x₀ : yoneda.obj O₀ ⟶ U := e₀.inv ≫ pullback.fst π (yoneda.map k)
  have hx₀ : IsSurjective B S hS x₀ := by
    intro y
    obtain ⟨z, rfl⟩ := hfst y
    refine ⟨pointsMap B S hS _ e₀.hom z, ?_⟩
    rw [← pointsMap_comp_apply, Iso.hom_inv_id_assoc]
  set W₀ := levelChart π w k
  set ι₀ : W₀ ⟶ W := pullback.fst (levelChartBase π w) k
  set c₀ : W₀ ⟶ O₀ := yoneda.preimage (levelChartMap π w k ≫ e₀.hom)
  have hc₀y : yoneda.map c₀ = levelChartMap π w k ≫ e₀.hom := Functor.map_preimage _ _
  have hsq₀ : IsPullback (yoneda.map ι₀) (yoneda.map c₀) w x₀ := by
    refine (isPullback_levelChart π w k).of_iso (Iso.refl _) (Iso.refl _) e₀ (Iso.refl _)
      (by simp only [Iso.refl_hom, Category.comp_id, Category.id_comp]; rfl)
      (by simp [hc₀y]) (by simp) (by simp [x₀])
  have hpres : PreservesLimitsOfShape WalkingCospan (BigFppfOver.toScheme B S hS) := by
    dsimp [BigFppfOver.toScheme]
    infer_instance
  have hW₀sch := (IsPullback.of_hasPullback (levelChartBase π w) k).map
    (BigFppfOver.toScheme B S hS)
  have : IsAffine ((BigFppfOver.toScheme B S hS).obj W₀) := .of_isPullback hW₀sch
  -- the thin chart is étale over the thin space
  have hc₀et : Etale ((BigFppfOver.toScheme B S hS).map c₀) :=
    hwe.property x₀ (yoneda.map ι₀) c₀ hsq₀
  let : Algebra Γ((BigFppfOver.toScheme B S hS).obj O₀, ⊤)
      Γ((BigFppfOver.toScheme B S hS).obj W₀, ⊤) :=
    ((BigFppfOver.toScheme B S hS).map c₀).appTop.hom.toAlgebra
  have : Algebra.Etale Γ((BigFppfOver.toScheme B S hS).obj O₀, ⊤)
      Γ((BigFppfOver.toScheme B S hS).obj W₀, ⊤) := by
    rw [← RingHom.etale_algebraMap]
    exact (HasRingHomProperty.iff_of_isAffine (P := @Etale)).mp hc₀et
  obtain ⟨τ, σ, hτ, hσ, P₀, F, hF, coef, g, hcard, hrel⟩ := exists_generic_presentation
    (D₀ := Γ((BigFppfOver.toScheme B S hS).obj W₀, ⊤))
    ((BigFppfOver.toScheme B S hS).map (levelChartBase π x₀)).appTop.hom
  -- the coefficients lift to global functions on `U`
  let Usp : AlgebraicSpaces B S hS := ⟨U, hU⟩
  have hlift : ∀ c : F, ∃ a : globalFunctions' B S hS U, ∀ {V : BigFppfOver B S hS}
      (v : yoneda.obj V ⟶ yoneda.obj O₀),
      globalChartValue B S hS (X := Usp) a (v ≫ x₀) =
        ((BigFppfOver.toScheme B S hS).map (yoneda.preimage v)).appTop (coef c) := by
    intro c
    let ā := globalFunctionsMap B S hS
      (V := ⟨pullback π (yoneda.map k), IsAffineSpace.isAlgebraicSpace hU₀⟩)
      (U := ⟨yoneda.obj O₀, isAlgebraicSpace_yoneda B S hS O₀⟩) (ObjectProperty.homMk e₀.hom)
      (representableGlobalFunction B S hS O₀ (coef c))
    obtain ⟨a, ha⟩ := surjective_globalFunctionsMap_pullback_of_isFirstOrderThickening B S hS hU
      k hk π hU₀ ā
    refine ⟨a, fun v ↦ ?_⟩
    have h1 := globalChartValue_globalFunctionsMap B S hS
      (X := Usp) (Y := ⟨pullback π (yoneda.map k), IsAffineSpace.isAlgebraicSpace hU₀⟩)
      (ObjectProperty.homMk (pullback.fst π (yoneda.map k))) a (v ≫ e₀.inv)
    rw [ha] at h1
    have h2 := globalChartValue_globalFunctionsMap B S hS
      (X := ⟨yoneda.obj O₀, isAlgebraicSpace_yoneda B S hS O₀⟩)
      (Y := ⟨pullback π (yoneda.map k), IsAffineSpace.isAlgebraicSpace hU₀⟩)
      (ObjectProperty.homMk e₀.hom) (representableGlobalFunction B S hS O₀ (coef c)) (v ≫ e₀.inv)
    have hv : (v ≫ e₀.inv) ≫ e₀.hom = v := by rw [Category.assoc, Iso.inv_hom_id, Category.comp_id]
    rw [h2, globalChartValue_congr B S hS _ hv, globalChartValue_representableFunction] at h1
    refine Eq.trans ?_ h1.symm
    exact globalChartValue_congr B S hS a (by simp [x₀])
  choose a ha using hlift
  -- the functions `θ`
  set ω := levelChartBase π w
  set θ : MvPolynomial F (affineBaseRing B S hS T) →+* Γ((BigFppfOver.toScheme B S hS).obj W, ⊤) :=
    eval₂Hom ((BigFppfOver.toScheme B S hS).map ω).appTop.hom
      (fun c ↦ globalChartValue B S hS (X := Usp) (a c) w)
  have hθA : θ.comp (algebraMap _ _) = ((BigFppfOver.toScheme B S hS).map ω).appTop.hom := by
    ext x
    simp only [RingHom.comp_apply, MvPolynomial.algebraMap_eq, θ, coe_eval₂Hom, eval₂_C]
  have hθinv : ((BigFppfOver.toScheme B S hS).map (hws.rep.fst' w)).appTop.hom.comp θ =
      ((BigFppfOver.toScheme B S hS).map (hws.rep.snd w)).appTop.hom.comp θ := by
    apply MvPolynomial.ringHom_ext
    · intro r
      simp only [RingHom.comp_apply, θ, eval₂Hom_C, ← CommRingCat.comp_apply,
        ← Scheme.Hom.comp_appTop, ← Functor.map_comp]
      rw [← levelChartBase_comp, ← levelChartBase_comp, hR.w]
    · intro c
      simp only [RingHom.comp_apply, θ, eval₂Hom_X']
      rw [← globalChartValue_comp, ← globalChartValue_comp]
      exact globalChartValue_congr B S hS _ hR.w
  have hbase : ι₀ ≫ ω = c₀ ≫ levelChartBase π x₀ := by
    apply yoneda.map_injective
    rw [Functor.map_comp, Functor.map_comp, yoneda_map_levelChartBase, yoneda_map_levelChartBase,
      ← Category.assoc, hsq₀.w, Category.assoc]
  have hθ₀ : ((BigFppfOver.toScheme B S hS).map ι₀).appTop.hom.comp θ =
      (algebraMap Γ((BigFppfOver.toScheme B S hS).obj O₀, ⊤)
        Γ((BigFppfOver.toScheme B S hS).obj W₀, ⊤)).comp
        (coefSpecialization B S hS π x₀ coef) := by
    apply MvPolynomial.ringHom_ext
    · intro r
      simp only [RingHom.comp_apply, θ, eval₂Hom_C, coefSpecialization,
        RingHom.algebraMap_toAlgebra]
      rw [← CommRingCat.comp_apply, ← Scheme.Hom.comp_appTop, ← Functor.map_comp, hbase,
        Functor.map_comp, Scheme.Hom.comp_appTop, CommRingCat.comp_apply]
    · intro c
      simp only [RingHom.comp_apply, θ, eval₂Hom_X', coefSpecialization,
        RingHom.algebraMap_toAlgebra]
      rw [← globalChartValue_comp, globalChartValue_congr B S hS _ hsq₀.w, ha c (yoneda.map c₀),
        Functor.preimage_map]
  -- the generators lift to roots, by formal étaleness
  have hsurjW : Function.Surjective ((BigFppfOver.toScheme B S hS).map ι₀).appTop.hom :=
    surjective_appTop_of_isPullback_isClosedImmersion hW₀sch
  have hkerW := ker_appTop_of_isPullback_isClosedImmersion hW₀sch
  have hJJ : RingHom.ker ((BigFppfOver.toScheme B S hS).map k).appTop.hom *
      RingHom.ker ((BigFppfOver.toScheme B S hS).map k).appTop.hom = ⊥ := by
    rw [eq_bot_iff, Ideal.mul_le]
    intro x hx y hy
    rw [Ideal.mem_bot]
    exact Stacks.Thickenings.mul_eq_zero_of_app_eq_zero hk ⊤ x y hx hy
  have hnil : IsNilpotent (RingHom.ker ((BigFppfOver.toScheme B S hS).map ι₀).appTop.hom) :=
    ⟨2, by rw [hkerW, ← Ideal.map_pow, pow_two, hJJ, Ideal.map_bot]; rfl⟩
  have := Algebra.LocalizedQuotient.etale g P₀.map P₀.map_inj hcard
  let : Algebra (MvPolynomial F (affineBaseRing B S hS T))
      Γ((BigFppfOver.toScheme B S hS).obj W, ⊤) := θ.toAlgebra
  let : Algebra (MvPolynomial F (affineBaseRing B S hS T))
      Γ((BigFppfOver.toScheme B S hS).obj O₀, ⊤) := (coefSpecialization B S hS π x₀ coef).toAlgebra
  let : Algebra (MvPolynomial F (affineBaseRing B S hS T))
      Γ((BigFppfOver.toScheme B S hS).obj W₀, ⊤) :=
    ((algebraMap Γ((BigFppfOver.toScheme B S hS).obj O₀, ⊤)
      Γ((BigFppfOver.toScheme B S hS).obj W₀, ⊤)).comp
        (coefSpecialization B S hS π x₀ coef)).toAlgebra
  have : IsScalarTower (MvPolynomial F (affineBaseRing B S hS T))
      Γ((BigFppfOver.toScheme B S hS).obj O₀, ⊤) Γ((BigFppfOver.toScheme B S hS).obj W₀, ⊤) :=
    IsScalarTower.of_algebraMap_eq' rfl
  have hrel' : ∀ j, P₀.relation j = (g j).map (algebraMap (MvPolynomial F (affineBaseRing B S hS T))
      Γ((BigFppfOver.toScheme B S hS).obj O₀, ⊤)) := fun j ↦ (hrel j).symm
  let G : Γ((BigFppfOver.toScheme B S hS).obj W, ⊤) →ₐ[MvPolynomial F (affineBaseRing B S hS T)]
      Γ((BigFppfOver.toScheme B S hS).obj W₀, ⊤) :=
    { ((BigFppfOver.toScheme B S hS).map ι₀).appTop.hom with
      commutes' := fun r ↦ congrArg (fun f ↦ f r) hθ₀ }
  let lift := Algebra.FormallySmooth.liftOfSurjective
    (Algebra.LocalizedQuotient.toAlgHom g P₀.map P₀.map_inj P₀ hrel' rfl) G hsurjW hnil
  have hθ' : lift.toRingHom.comp (algebraMap _ _) = θ := lift.comp_algebraMap
  have hθ'₀ : ∀ i, ((BigFppfOver.toScheme B S hS).map ι₀).appTop.hom
      (lift.toRingHom (algebraMap (Algebra.LocalizedQuotient.quot g) _
        (Ideal.Quotient.mk _ (MvPolynomial.X i)))) = P₀.val i := by
    intro i
    have h := Algebra.FormallySmooth.liftOfSurjective_apply
      (Algebra.LocalizedQuotient.toAlgHom g P₀.map P₀.map_inj P₀ hrel' rfl) G hsurjW hnil
      (algebraMap (Algebra.LocalizedQuotient.quot g) _ (Ideal.Quotient.mk _ (MvPolynomial.X i)))
    refine h.trans ?_
    rw [Algebra.LocalizedQuotient.toAlgHom_algebraMap, Algebra.LocalizedQuotient.quotToAlgHom_mk,
      MvPolynomial.aeval_X]
  obtain ⟨Z, ⟨eZ⟩⟩ := exists_iso_yoneda_of_presentationLift B S hS hU π w hws hwe hR x₀ hx₀ ι₀ c₀
    hsq₀ rfl P₀ hcard P₀.map P₀.map_inj rfl coef g hrel θ hθA hθinv hθ₀ lift.toRingHom hθ' hθ'₀
  exact isAffineSpace_of_iso_yoneda_of_isThickening B S hS eZ π k hkth hU₀

end AlgebraicGeometry.Space

end
