module

public import StacksFrontier.AlgebraicGeometry.Stacks.GroupoidLift.LiftDescent

/-!
# Uniqueness of the descended lift at a chart point

In the situation of `AlgebraicGeometry.Stack.GroupoidLift.StackChart.exists_lift_of_chartLift`
(a stack `𝒳` with a chart over the affine `T'`, `A' = Γ(T', ⊤)`, a square-zero ideal `I`, a
faithfully flat finitely presented `A'`-algebra `C'`, and `x̄` over `Spec (A' ⧸ I)` coming from a
chart point over `Spec (C' ⧸ I C')`), two lifts `x'`, `x''` of `x̄` over `A'` whose pullbacks to
`C'` are the same lift `ξ u` are isomorphic as lifts of `x̄`
(`AlgebraicGeometry.Stack.GroupoidLift.StackChart.exists_iso_of_chartLift`).

This is the injectivity half of the sheaf condition of Stacks 0DNS for the covering `A' → C'`.
The descent arrows of the two lifts are exact cocycles lifting the descent arrow of `x̄`, so
they are conjugate by an infinitesimal automorphism `ψ` of `ξ u`
(`AlgebraicGeometry.Stack.GroupoidLift.NerveDatum.exists_infH_eq_conj`); the morphism
`ψ ≫ ζ''` is then compatible with the descent arrow of `x'` and glues to the isomorphism.
-/

@[expose] public section

open scoped TensorProduct
open CategoryTheory Opposite Limits
open AlgebraicGeometry.Space.ChartDescent

namespace AlgebraicGeometry.Stack.GroupoidLift

universe w u

/-- A morphism that is the identity up to `eqToHom`s and commutes with `t` past `ψ` makes
`ψ` invisible after `t`. -/
theorem _root_.CategoryTheory.comp_eq_of_eqToHom_id_comp {𝒞 : Type*} [Category 𝒞]
    {X X' Y W W' : 𝒞} (m : X ⟶ X') (t : X ⟶ W) (t' : X' ⟶ W') (ψ : W ⟶ W')
    (p : X = Y) (q : Y = X') (hm : m = eqToHom p ≫ 𝟙 Y ≫ eqToHom q) (h : m ≫ t' = t ≫ ψ) :
    t ≫ ψ = eqToHom (p.trans q) ≫ t' := by
  subst p q
  simp only [eqToHom_refl, Category.id_comp] at hm ⊢
  subst hm
  exact h.symm.trans (Category.id_comp _)

/-- **Conjugate descent arrows.** If `R'' = M₀⁻¹ ≫ R' ≫ M₁` (up to `eqToHom`s) where `M₀`, `M₁`
are the pullbacks of `ψ` along `t₀`, `t₁`, and `R''` is compatible with `ζ`, then `R'` is
compatible with `ψ ≫ ζ`. -/
theorem _root_.CategoryTheory.comp_conj_fac {𝒞 : Type*} [Category 𝒞] {X₀ X₁ W Z : 𝒞}
    (R'' R' : X₀ ⟶ X₁) (M₀ : X₀ ⟶ X₀) [hM₀ : IsIso M₀] (M₁ : X₁ ⟶ X₁) (p₁ p₂ : X₀ = X₀)
    (p₃ p₄ : X₁ = X₁) (t₀ : X₀ ⟶ W) (t₁ : X₁ ⟶ W) (ψ : W ⟶ W) (ζ : W ⟶ Z)
    (hc : R'' = eqToHom p₁ ≫ (inv M₀ ≫ eqToHom p₂ ≫ (R' ≫ eqToHom p₃ ≫ M₁)) ≫ eqToHom p₄)
    (n₀ : M₀ ≫ t₀ = t₀ ≫ ψ) (n₁ : M₁ ≫ t₁ = t₁ ≫ ψ) (hf : R'' ≫ t₁ ≫ ζ = t₀ ≫ ζ) :
    R' ≫ t₁ ≫ ψ ≫ ζ = t₀ ≫ ψ ≫ ζ := by
  simp only [eqToHom_refl, Category.id_comp, Category.comp_id] at hc
  subst hc
  have e₁ : R' ≫ t₁ ≫ ψ ≫ ζ = R' ≫ M₁ ≫ t₁ ≫ ζ := by
    rw [← Category.assoc t₁, ← n₁, Category.assoc]
  rw [e₁, ← Category.assoc t₀, ← n₀, Category.assoc, ← hf]
  simp

variable {B : BigFppfSite.{u}} {S : Scheme.{u}} {hS : B.Contains S} {T' : BigFppfOver B S hS}
  [IsAffine ((BigFppfOver.toScheme B S hS).obj T')]
  {𝒳 : CatFiberedInGroupoids.{u, u, u + 1, u + 1} (BigFppfOver B S hS)}
  {U₀ : BigFppfOver B S hS} {a : schemeFibredCategory B S hS U₀ ⟶ 𝒳}
  {P : SmallAlg (ringOf B S hS T') B.cutoff} {ι : specOver P ⟶ U₀}

namespace StackChart

variable {hA : Cardinal.mk (ringOf B S hS T') < B.cutoff} {C' : Type u} [CommRing C']
  [Algebra (ringOf B S hS T') C'] {hC : Cardinal.mk C' < B.cutoff} {I : Ideal (ringOf B S hS T')}
  {hI : I ^ 2 = ⊥}

/-- **An infinitesimal automorphism conjugating two descent arrows of lifts.** If the descent
arrows of `ζ'` and `ζ''` are conjugate by the pullbacks of an automorphism `η` of the lifted
point `u` reducing to the identity, then `η`, as an automorphism `ψ` of `ξ u` over the identity,
reduces to the identity and makes `ψ ≫ ζ''` compatible with the descent arrow of `ζ'`. -/
theorem exists_fac_of_conj (u : P.obj →ₐ[ringOf B S hS T'] (descNerve T' hC 0).obj)
    {x' x'' : 𝒳.val.obj} (ζ' : ξ a ι u ⟶ x') (ζ'' : ξ a ι u ⟶ x'')
    [𝒳.val.p.IsHomLift (specOverMap (baseMap B.aleph0_lt_cutoff hC hA)) ζ']
    [𝒳.val.p.IsHomLift (specOverMap (baseMap B.aleph0_lt_cutoff hC hA)) ζ'']
    (η : NerveDatum.ptAt (G := stackGroupoid a ι) (hκ := B.aleph0_lt_cutoff) (hC := hC) u
        (vₗ _ C' 0) ⟶
      NerveDatum.ptAt (G := stackGroupoid a ι) (hκ := B.aleph0_lt_cutoff) (hC := hC) u
        (vₗ _ C' 0))
    {wb : P.obj →ₐ[ringOf B S hS T'] (red I (descNerve T' hC 0)).obj}
    (hred : Arr.map a ι (qC hC I hI) η.1 = Arr.idt wb)
    (heq : (stackGroupoid a ι).toHom
        (x := NerveDatum.ptAt (G := stackGroupoid a ι) (hκ := B.aleph0_lt_cutoff) (hC := hC) u
          (v₀ _ C' 1))
        (y := NerveDatum.ptAt (G := stackGroupoid a ι) (hκ := B.aleph0_lt_cutoff) (hC := hC) u
          (vₗ _ C' 1)) (liftArr (hA := hA) u ζ'') rfl rfl =
      CategoryTheory.Groupoid.inv (NerveDatum.mapPt (I := I) (hI := hI) (face _ C' 0 1)
          NerveDatum.face_zero_one_comp_vₗ NerveDatum.face_zero_one_comp_vₗ η) ≫
        (stackGroupoid a ι).toHom (liftArr (hA := hA) u ζ') rfl rfl ≫
          NerveDatum.mapPt (I := I) (hI := hI) (face _ C' 0 0)
            NerveDatum.face_zero_zero_comp_vₗ NerveDatum.face_zero_zero_comp_vₗ η) :
    ∃ ψ : ξ a ι u ⟶ ξ a ι u, 𝒳.val.p.IsHomLift (𝟙 (specOver (descNerve T' hC 0))) ψ ∧
      trans a ι (qC hC I hI) u ≫ ψ = trans a ι (qC hC I hI) u ∧
      (liftArr (hA := hA) u ζ').hom ≫ trans a ι (descVₗ T' hC) u ≫ ψ ≫ ζ'' =
        trans a ι (descV₀ T' hC) u ≫ ψ ≫ ζ'' := by
  obtain ⟨⟨s, t, φ, l⟩, hs, ht⟩ := η
  change s = (vₗ _ C' 0).comp u at hs
  change t = (vₗ _ C' 0).comp u at ht
  subst hs ht
  refine ⟨φ, l, ?_, ?_⟩
  · exact (comp_eq_of_eqToHom_id_comp _ _ _ φ _ _ (Arr.hom_eq_of_eq hred)
      (Arr.map_hom_fac (qC hC I hI) (⟨_, _, φ, l⟩ : Arr a ι (descNerve T' hC 0)))).trans
      ((congrArg (· ≫ _) (eqToHom_refl _ _)).trans (Category.id_comp _))
  · let η' : Arr a ι (descNerve T' hC 0) := ⟨_, _, φ, l⟩
    let h₀ := (NerveDatum.Th (hκ := B.aleph0_lt_cutoff) (hC := hC) (I := I) (hI := hI)
      (face _ C' 0 1)).top
    let h₁ := (NerveDatum.Th (hκ := B.aleph0_lt_cutoff) (hC := hC) (I := I) (hI := hI)
      (face _ C' 0 0)).top
    have n₀ := Arr.map_hom_fac h₀ η'
    have n₁ := Arr.map_hom_fac h₁ η'
    have hc' : (liftArr (hA := hA) u ζ'').hom = eqToHom _ ≫ (inv (Arr.map a ι h₀ η').hom ≫
        eqToHom _ ≫ ((liftArr (hA := hA) u ζ').hom ≫ eqToHom _ ≫ (Arr.map a ι h₁ η').hom)) ≫
          eqToHom _ := Arr.hom_eq_of_eq (C := descNerve T' hC 1) (congrArg Subtype.val heq)
    have hf : (liftArr (hA := hA) u ζ'').hom ≫ trans a ι h₁ η'.tgt ≫ ζ'' =
        trans a ι h₀ η'.tgt ≫ ζ'' := liftArr_fac (hA := hA) u ζ''
    exact comp_conj_fac (liftArr (hA := hA) u ζ'').hom (liftArr (hA := hA) u ζ').hom
      (Arr.map a ι h₀ η').hom (hM₀ := Arr.isIso_hom (Arr.map a ι h₀ η')) (Arr.map a ι h₁ η').hom
      _ _ _ _ (trans a ι h₀ η'.tgt) (trans a ι h₁ η'.tgt) φ ζ'' hc' n₀ n₁ hf

/-- The defect of the descent arrow of a lift is trivial, since that arrow is a cocycle. -/
private theorem defectH_liftArr_eq_id (u : P.obj →ₐ[ringOf B S hS T'] (descNerve T' hC 0).obj)
    {x : 𝒳.val.obj} (ζ : ξ a ι u ⟶ x)
    [𝒳.val.p.IsHomLift (specOverMap (baseMap B.aleph0_lt_cutoff hC hA)) ζ] :
    NerveDatum.defectH (G := stackGroupoid a ι) (hκ := B.aleph0_lt_cutoff) (hC := hC) (I := I)
      (hI := hI) (liftArr (hA := hA) u ζ) rfl rfl = 𝟙 _ :=
  have ⟨h, hcoc⟩ := liftArr_cocycle (hA := hA) u ζ
  NerveDatum.defectH_eq_id_of_cocycle (G := stackGroupoid a ι) (hκ := B.aleph0_lt_cutoff)
    (hC := hC) (I := I) (hI := hI) (liftArr (hA := hA) u ζ) rfl rfl h hcoc

variable (hA hC I hI) in
/-- **Uniqueness of the descended lift at a chart point.** Two lifts `φ' : x̄ ⟶ x'` and
`φ'' : x̄ ⟶ x''` of `x̄` over `Spec A'` whose pullbacks to `Spec C'` are the same lift `ξ u`
(`c ≫ φ = trans qC u ≫ ζ` for `ζ : ξ u ⟶ x` over `Spec C' ⟶ Spec A'`) are isomorphic as lifts:
there is `θ : x' ⟶ x''` over the identity of `Spec A'` with `φ' ≫ θ = φ''`. -/
theorem exists_iso_of_chartLift
    (h𝒳 : 𝒳.val.p.IsStackInGroupoids.{w} (BigFppfOver.topology B S hS))
    [Module.FaithfullyFlat (ringOf B S hS T') C'] [Algebra.FinitePresentation (ringOf B S hS T') C']
    [Module.FinitePresentation P.obj Ω[P.obj⁄ringOf B S hS T']]
    {Q : Type u} [CommRing Q] [Algebra (ringOf B S hS T') Q]
    [Module.FinitePresentation Q Ω[Q⁄ringOf B S hS T']]
    (b : Chart (stackArr a ι) Q) (hb : b.IsFormallyEtale) (sV tV : P.obj →ₐ[ringOf B S hS T'] Q)
    (hsV : ∀ (D : SmallAlg (ringOf B S hS T') B.cutoff) (v : Q →ₐ[ringOf B S hS T'] D.obj),
      (b.app D v).src = v.comp sV)
    (htV : ∀ (D : SmallAlg (ringOf B S hS T') B.cutoff) (v : Q →ₐ[ringOf B S hS T'] D.obj),
      (b.app D v).tgt = v.comp tV)
    {xb : 𝒳.val.obj} (hxb : 𝒳.val.p.obj xb = specOver (red I (baseAlg (κ := B.cutoff) hA)))
    (u : P.obj →ₐ[ringOf B S hS T'] (descNerve T' hC 0).obj)
    (c : ξ a ι ((qC hC I hI).hom.hom.comp u) ⟶ xb)
    (hc : 𝒳.val.p.IsHomLift (specOverMap (baseThk B.aleph0_lt_cutoff hC hI hA).bot) c)
    (εbar : Q →ₐ[ringOf B S hS T'] (red I (descNerve T' hC 0)).obj)
    (hε : b.app _ εbar = Arr.idt ((qC hC I hI).hom.hom.comp u))
    {x' x'' : 𝒳.val.obj} (ζ' : ξ a ι u ⟶ x') (ζ'' : ξ a ι u ⟶ x'') (φ' : xb ⟶ x')
    (φ'' : xb ⟶ x'')
    (hζ' : 𝒳.val.p.IsHomLift (specOverMap (baseMap B.aleph0_lt_cutoff hC hA)) ζ')
    (hζ'' : 𝒳.val.p.IsHomLift (specOverMap (baseMap B.aleph0_lt_cutoff hC hA)) ζ'')
    (hφ' : 𝒳.val.p.IsHomLift (specOverMap (thk I hI (baseAlg (κ := B.cutoff) hA)).q) φ')
    (hφ'' : 𝒳.val.p.IsHomLift (specOverMap (thk I hI (baseAlg (κ := B.cutoff) hA)).q) φ'')
    (hcφ' : c ≫ φ' = trans a ι (qC hC I hI) u ≫ ζ')
    (hcφ'' : c ≫ φ'' = trans a ι (qC hC I hI) u ≫ ζ'') :
    ∃ θ : x' ⟶ x'', 𝒳.val.p.IsHomLift (𝟙 (specOver (baseAlg (κ := B.cutoff) hA))) θ ∧
      φ' ≫ θ = φ'' := by
  have := hc
  have := hζ'
  have := hζ''
  let D := chartNerveDatumOfLift hA hC I hI _ c u rfl
  obtain ⟨ε₀, ⟨hε₀, -⟩, -⟩ := hb _ _ (thk I hI (descNerve T' hC 0)).q
    (thk I hI (descNerve T' hC 0)).surj (thk I hI (descNerve T' hC 0)).sq εbar (Arr.idt D.u₀)
    ((Arr.map_idt _ _).trans ((congrArg Arr.idt D.u₀_lift).trans hε.symm))
  have hq' := map_liftArr_eq_chartRbar u ζ' c φ' hφ' hcφ'
  have hq'' := map_liftArr_eq_chartRbar u ζ'' c φ'' hφ'' hcφ''
  obtain ⟨E₀, hE₀, heq⟩ := D.exists_infH_eq_conj sV tV εbar hsV htV hε hb rfl rfl rfl hq' rfl rfl
    hq'' ε₀ hε₀ (defectH_liftArr_eq_id u ζ') (defectH_liftArr_eq_id u ζ'')
  have hred : Arr.map a ι (qC hC I hI) (D.infH sV tV εbar hsV htV hε hb rfl (vₗ _ C' 0) hE₀).1 =
      Arr.idt (D.wAt (vₗ _ C' 0)) :=
    map_infOf (G := stackGroupoid a ι) b hb sV tV _ _ hE₀
  obtain ⟨ψ, hψ, hψq, hψζ⟩ := exists_fac_of_conj (I := I) (hI := hI) u ζ' ζ''
    (D.infH sV tV εbar hsV htV hε hb rfl (vₗ _ C' 0) hE₀) hred heq
  have hx' : 𝒳.val.p.obj x' = specOver (baseAlg (κ := B.cutoff) hA) :=
    @IsHomLift.codomain_eq _ _ _ _ 𝒳.val.p _ _ _ _ _ ζ' hζ'
  have hx'' : 𝒳.val.p.obj x'' = specOver (baseAlg (κ := B.cutoff) hA) :=
    @IsHomLift.codomain_eq _ _ _ _ 𝒳.val.p _ _ _ _ _ ζ'' hζ''
  have := hψ
  have hζ₃ : 𝒳.val.p.IsHomLift (specOverMap (baseMap B.aleph0_lt_cutoff hC hA) ≫ 𝟙 _)
      (ψ ≫ ζ'') :=
    isHomLift_of_eq ((Category.id_comp _).trans (Category.comp_id _).symm) inferInstance
  obtain ⟨θ, hθ, hζθ⟩ := exists_hom_of_chart (baseMap B.aleph0_lt_cutoff hC hA) (descV₀ T' hC)
    (descVₗ T' hC) h𝒳 (isPullback_descV hC hA) (ofArrows_baseMap_mem hC hA) (𝟙 _) hx' hx'' u ζ'
    hζ' (ψ ≫ ζ'') hζ₃ (liftArr (hA := hA) u ζ').hom (liftArr (hA := hA) u ζ').lift
    (liftArr_fac u ζ') hψζ
  refine ⟨θ, hθ, ?_⟩
  have := hφ'
  have := hθ
  refine hom_ext_of_chart (baseThk B.aleph0_lt_cutoff hC hI hA).bot (rV₀ hC I) (rVₗ hC I) h𝒳
    (isPullback_specOverMap_of_isPushout _ _ _ _
      (isPushout_red_nerve_one B.aleph0_lt_cutoff C' hC I hI hA)) (ofArrows_red_mem hA hC I hI)
    (specOverMap (thk I hI (baseAlg (κ := B.cutoff) hA)).q) hxb hx'' _ c hc
    (chartRbar hC I _ c).hom (chartRbar hC I _ c).lift (chartRbar_fac hC I _ c) (φ' ≫ θ) φ''
    (isHomLift_of_eq (Category.comp_id _) inferInstance) hφ'' ?_
  rw [← Category.assoc, hcφ', Category.assoc, hζθ, ← Category.assoc, hψq, hcφ'']

end StackChart

end AlgebraicGeometry.Stack.GroupoidLift

end
