module

public import StacksFrontier.AlgebraicGeometry.Stacks.LiftingAffinesLocalReduction
public import StacksFrontier.AlgebraicGeometry.Stacks.LiftingAffinesLocalOpen
public import StacksFrontier.RingTheory.Smooth.NilpotentLiftChart
public import StacksFrontier.RingTheory.Smooth.NilpotentLiftPresentation
public import StacksFrontier.AlgebraicGeometry.Spaces.FinitePresentationCancellation
public import StacksFrontier.AlgebraicGeometry.Spaces.FiniteTypeProperties
public import StacksFrontier.AlgebraicGeometry.Spaces.EtaleChartComposition
public import StacksFrontier.AlgebraicGeometry.Spaces.EtaleChartFppfDescent

/-!
# The local step of Stacks 0CJV

Let `ι : 𝒳 ⟶ 𝒳'` be a thickening of algebraic stacks, `W` an algebraic space with a smooth
1-morphism `x : W ⟶ 𝒳`, and `U = U' ×_{𝒳'} 𝒳` the base change of a smooth chart `b : U' ⟶ 𝒳'` by
a scheme of the site. For a scheme `T` of the site, étale over `W` and mapping to `U` over `𝒳`, and
a point `y` of `T`, this file produces an open neighbourhood `A ⊆ T` of `y` which sits in a
cartesian square
```
A ⟶ T'
↓     ↓
𝒳 ⟶ 𝒳'
```
with `T' ⟶ 𝒳'` smooth: `AlgebraicGeometry.Stack.LiftingAffinesLocal.exists_local_etaleSmoothLift`.

The argument is the source's (Stacks 0CJV, last three paragraphs) with its Koszul-regular
immersion replaced by minimal generators of the ideal of `A` in an affine space over `U`, lifted
to the thickening `U'`: the closed subscheme `T'` they cut out is smooth over `𝒳'` by the smooth
diagram test of Stacks 075U, checked on an affine étale chart of `U' ×_{𝒳'} U'` by the Jacobian
lifting argument of `Algebra.isSmoothAt_tensor_quotient_span`, which is where Stacks 0CER enters
the source.
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits Bicategory TensorProduct

namespace AlgebraicGeometry.Stack.LiftingAffinesLocal

universe u w

variable {B : BigFppfSite.{u}} {S : Scheme.{u}} {hS : B.Contains S}

/-- **A smooth morphism of algebraic spaces gives a smooth 1-morphism of algebraic stacks.** -/
theorem isSmooth_map_of_isSmooth {X Y : AlgebraicSpaces B S hS} (f : X ⟶ Y)
    (hf : Space.IsSmooth B S hS f.hom) :
    AlgebraicStacks.IsSmooth B S hS ((algebraicSpaceStackFunctor.{u, w} B S hS).map f) := by
  refine isSmooth_of_isSmooth_representingMap B S hS X.obj Y.obj X.property Y.property
    (StacksRepresentableCFG.EquivalenceOver.refl _)
    (StacksRepresentableCFG.EquivalenceOver.refl _) _ ?_
  show Space.IsSmooth B S hS (representingMap B S hS (fibredCategory B S hS X.obj)
    (fibredCategory B S hS Y.obj) X.obj Y.obj
    (StacksRepresentableCFG.EquivalenceOver.refl _)
    (StacksRepresentableCFG.EquivalenceOver.refl _) (associatedMap B S hS f.hom).1)
  rw [representingMap_associatedMap]
  exact hf

/-- The prime of a point of an affine scheme, pushed along a morphism of affine schemes. -/
theorem isoSpec_hom_apply_eq_comap {X Y : Scheme.{u}} [IsAffine X] [IsAffine Y] (f : X ⟶ Y)
    (x : X) : Y.isoSpec.hom (f x) = PrimeSpectrum.comap f.appTop.hom (X.isoSpec.hom x) := by
  have h := congrArg (fun g => g x) (Scheme.isoSpec_hom_naturality f)
  simp only [Scheme.Hom.comp_apply] at h
  rw [← h, Spec.map_apply]

/-- **The kernel of the ring map of a surjective morphism of affine schemes is nil.** -/
theorem ker_le_nilradical_of_surjective {X Y : Scheme.{u}} [IsAffine X] [IsAffine Y] (f : X ⟶ Y)
    (hf : Function.Surjective f) : RingHom.ker f.appTop.hom ≤ nilradical Γ(Y, ⊤) := by
  rw [nilradical_eq_sInf]
  refine le_sInf fun p hp => ?_
  have : p.IsPrime := hp
  let z : Spec Γ(Y, ⊤) := (⟨p, hp⟩ : PrimeSpectrum Γ(Y, ⊤))
  obtain ⟨x, hx⟩ := hf (Y.isoSpec.inv z)
  have h := isoSpec_hom_apply_eq_comap f x
  have hz : Y.isoSpec.hom (Y.isoSpec.inv z) = z := by
    rw [← Scheme.Hom.comp_apply, Iso.inv_hom_id]
    rfl
  rw [hx, hz] at h
  intro r hr
  have hr' : r ∈ (PrimeSpectrum.comap f.appTop.hom (X.isoSpec.hom x)).asIdeal := by
    show f.appTop.hom r ∈ (X.isoSpec.hom x).asIdeal
    rw [RingHom.mem_ker.mp hr]
    exact Ideal.zero_mem _
  rwa [← h] at hr'

/-- **A prime of a tensor product over two primes with a common contraction.** -/
theorem exists_isPrime_tensor {R A C : Type u} [CommRing R] [CommRing A] [CommRing C]
    [Algebra R A] [Algebra R C] (p : Ideal A) [p.IsPrime] (q : Ideal C) [q.IsPrime]
    (h : p.comap (algebraMap R A) = q.comap (algebraMap R C)) :
    ∃ z : Ideal (A ⊗[R] C), z.IsPrime ∧
      z.comap Algebra.TensorProduct.includeLeftRingHom = p ∧
      z.comap Algebra.TensorProduct.includeRight.toRingHom = q := by
  have hpb := isPullback_SpecMap_of_isPushout _ _ _ _ (CommRingCat.isPushout_tensorProduct R A C)
  obtain ⟨z, hz1, hz2⟩ := Scheme.exists_preimage_of_isPullback hpb
    (⟨p, inferInstance⟩ : PrimeSpectrum A) (⟨q, inferInstance⟩ : PrimeSpectrum C)
    (PrimeSpectrum.ext h)
  exact ⟨z.asIdeal, z.isPrime, congrArg PrimeSpectrum.asIdeal hz1,
    congrArg PrimeSpectrum.asIdeal hz2⟩

/-- **The Jacobian chart of the lifted presentation.** Let `π : B' → A₀` be surjective with nil
kernel `J`, `D` a finitely presented `A₀`-algebra with a prime `𝔭`, and `(g'', f'', λ)` a lifted
presentation of `D` at `𝔭` (`Algebra.exists_liftedPresentation`). Let `C` be a `B'`-algebra,
smooth through its structure map `s` and through a second map `τ`, with `J C` the same through
both, such that `X ⊗_{B'} C` is smooth over `A₀` through `τ`, and let `𝔢` be a prime of `C` over
the image of `𝔭` in `B'`. Then a principal open `D(h')` of `Spec S₁` around the prime under `𝔭`
has a smooth chart by a ring `Pr`, smooth over `B'` through `τ`. -/
theorem exists_smooth_chart_of_liftedPresentation {B' A₀ D C : Type u} [CommRing B'] [CommRing A₀]
    [CommRing D] [CommRing C] (π : B' →+* A₀) (hπ : Function.Surjective π)
    (hJ : RingHom.ker π ≤ nilradical B') [Algebra A₀ D] (𝔭 : Ideal D) [𝔭.IsPrime]
    {n r : ℕ} (g'' : MvPolynomial (Fin n) B') (f'' : Fin r → MvPolynomial (Fin n) B')
    (lam : D →+* Algebra.LiftedPresentation.Reduced π g'' f'')
    (hlamB : (lam.comp (algebraMap A₀ D)).comp π =
      algebraMap B' (Algebra.LiftedPresentation.Reduced π g'' f''))
    (d : D) (hloc : @IsLocalization.Away D _ d (Algebra.LiftedPresentation.Reduced π g'' f'') _
      lam.toAlgebra) (hd𝔭 : d ∉ 𝔭)
    (hrel : ∀ a : Fin r → Algebra.LiftedPresentation.AmbientReduced π g'',
      ∑ i, a i * Ideal.Quotient.mk _ (algebraMap _ (Localization.Away g'') (f'' i)) = 0 →
      ∀ i, a i ∈ ((((𝔭.map lam).comap (Ideal.Quotient.mk _)).comap
        (algebraMap (Localization.Away g'') (Algebra.LiftedPresentation.Chart g'' f''))).map
          (Ideal.Quotient.mk _)))
    [Algebra B' C] [Algebra.Smooth B' C] (τ : B' →+* C) (hτ : @Algebra.Smooth B' _ C _ τ.toAlgebra)
    (hE0 : (RingHom.ker π).map (algebraMap B' C) = (RingHom.ker π).map τ)
    (ψ : A₀ →+* Algebra.LiftedPresentation.Reduced π g'' f'' ⊗[B'] C) (hψ : ψ.Smooth)
    (hψeq : ψ.comp π = Algebra.TensorProduct.includeRight.toRingHom.comp τ)
    (𝔢 : Ideal C) [𝔢.IsPrime]
    (h𝔢 : 𝔢.comap (algebraMap B' C) = 𝔭.comap ((algebraMap A₀ D).comp π)) :
    ∃ (h' : Algebra.LiftedPresentation.Chart g'' f'')
      (_ : h' ∉ (𝔭.map lam).comap (Ideal.Quotient.mk _)) (Pr : Type u) (_ : CommRing Pr)
      (α : Localization.Away h' →+* Pr) (β : C →+* Pr),
      α.comp (algebraMap B' (Localization.Away h')) = β.comp (algebraMap B' C) ∧
      @Algebra.Smooth (Localization.Away h') _ Pr _ α.toAlgebra ∧
      Function.Surjective (PrimeSpectrum.comap α) ∧
      @Algebra.Smooth B' _ Pr _ (β.comp τ).toAlgebra := by
  let := lam.toAlgebra
  have := hloc
  have hdisj : Disjoint (Submonoid.powers d : Set D) ↑𝔭 :=
    (Ideal.disjoint_powers_iff_notMem_of_isPrime d).mpr hd𝔭
  have h𝔵' : (𝔭.map lam).IsPrime :=
    IsLocalization.isPrime_of_isPrime_disjoint (Submonoid.powers d) _ 𝔭 inferInstance hdisj
  have hcomap : (𝔭.map lam).comap lam = 𝔭 :=
    IsLocalization.under_map_of_isPrime_disjoint (Submonoid.powers d) _ inferInstance hdisj
  have : ((𝔭.map lam).comap (Ideal.Quotient.mk ((RingHom.ker π).map
      (algebraMap B' (Algebra.LiftedPresentation.Chart g'' f''))))).IsPrime :=
    Ideal.comap_isPrime _ _
  have hZ : @Algebra.FormallySmooth (B' ⧸ RingHom.ker π)
      (Algebra.LiftedPresentation.Reduced π g'' f'' ⊗[B'] C) _ _
      (Algebra.tensorQuotientViaT (RingHom.ker π) τ hE0
        (Algebra.LiftedPresentation.Reduced π g'' f'')
        (Algebra.algebraMap_quotient_map_eq_zero (RingHom.ker π)
          (Algebra.LiftedPresentation.Chart g'' f''))).toAlgebra := by
    have hcomp : Algebra.tensorQuotientViaT (RingHom.ker π) τ hE0
        (Algebra.LiftedPresentation.Reduced π g'' f'')
        (Algebra.algebraMap_quotient_map_eq_zero (RingHom.ker π)
          (Algebra.LiftedPresentation.Chart g'' f'')) =
        ψ.comp (RingHom.quotientKerEquivOfSurjective hπ).toRingHom := by
      apply Ideal.Quotient.ringHom_ext
      ext b
      simp only [Algebra.tensorQuotientViaT, RingHom.comp_apply, Ideal.Quotient.lift_mk,
        RingEquiv.toRingHom_eq_coe, RingEquiv.coe_toRingHom,
        RingHom.quotientKerEquivOfSurjective_apply_mk]
      exact (RingHom.congr_fun hψeq b).symm
    rw [hcomp]
    exact (RingHom.FormallySmooth.of_bijective
      (RingHom.quotientKerEquivOfSurjective hπ).bijective).comp hψ.formallySmooth
  have hcontr : ((𝔭.map lam).comap (Ideal.Quotient.mk _)).comap
      (algebraMap B' (Algebra.LiftedPresentation.Chart g'' f'')) =
      𝔢.comap (algebraMap B' C) := by
    rw [h𝔢, Ideal.comap_comap]
    show (𝔭.map lam).comap (algebraMap B' (Algebra.LiftedPresentation.Reduced π g'' f'')) = _
    rw [← hlamB, ← Ideal.comap_comap, ← Ideal.comap_comap, hcomap, Ideal.comap_comap]
  obtain ⟨𝔷, _, h𝔷, -⟩ := exists_isPrime_tensor _ 𝔢 hcontr
  have : Algebra.FinitePresentation B' (Algebra.LiftedPresentation.Chart g'' f'') :=
    Algebra.FinitePresentation.quotient (Submodule.fg_span (Set.finite_range _))
  have hsmAt := Algebra.isSmoothAt_tensor_quotient_span (RingHom.ker π) τ hJ hτ hE0
    (M := Localization.Away g'') (fun i => algebraMap _ (Localization.Away g'') (f'' i))
    (RingHom.id _) (RingHom.Flat.id _)
    (fun i => Ideal.Quotient.mk _ (algebraMap _ (Localization.Away g'') (f'' i))) (fun i => rfl)
    _ hrel hZ 𝔷 (by rw [h𝔷, Ideal.comap_id]; exact le_rfl)
  exact Algebra.exists_smooth_chart_of_isSmoothAt τ hτ _ 𝔷 h𝔷 hsmAt

variable {𝒳 𝒳' : AlgebraicStacks.{u, w} B S hS} {ι : 𝒳 ⟶ 𝒳'}

/-- A 2-isomorphism of composites through a common first factor, with arbitrary second legs. -/
noncomputable def whiskerTwoIso' {T T' V V' : AlgebraicSpaces B S hS}
    {𝒵 : AlgebraicStacks.{u, w} B S hS}
    (k : T ⟶ T') {s : T' ⟶ V} {t : T' ⟶ V'}
    {g : (algebraicSpaceStackFunctor.{u, w} B S hS).obj V ⟶ 𝒵}
    {g' : (algebraicSpaceStackFunctor.{u, w} B S hS).obj V' ⟶ 𝒵}
    (ρ : (algebraicSpaceStackFunctor.{u, w} B S hS).map s ≫ g ≅
      (algebraicSpaceStackFunctor.{u, w} B S hS).map t ≫ g') :
    (algebraicSpaceStackFunctor.{u, w} B S hS).map (k ≫ s) ≫ g ≅
      (algebraicSpaceStackFunctor.{u, w} B S hS).map (k ≫ t) ≫ g' :=
  (α_ ((algebraicSpaceStackFunctor.{u, w} B S hS).map k)
      ((algebraicSpaceStackFunctor.{u, w} B S hS).map s) g ≪≫
    whiskerLeftIso ((algebraicSpaceStackFunctor.{u, w} B S hS).map k) ρ ≪≫
    (α_ ((algebraicSpaceStackFunctor.{u, w} B S hS).map k)
      ((algebraicSpaceStackFunctor.{u, w} B S hS).map t) g').symm :)

/-- A morphism of the site which is étale as a morphism of schemes is étale after `yoneda.map`. -/
private theorem isEtale_yoneda_map_of_etale {U V : BigFppfOver B S hS} (φ : U ⟶ V)
    (h : AlgebraicGeometry.Etale ((BigFppfOver.toScheme B S hS).map φ)) :
    Space.IsEtale B S hS (yoneda.map φ) :=
  (Space.isEtale_iff_presheaf_of_yoneda B S hS _).2
    ((Space.presheaf_yoneda_map_etale_iff B S hS _).2 h)

/-- **An affine member factors through the reduction of the local chart.** With
`U = U' ×_{𝒳'} 𝒳`, `U_w = U'_w ×_{𝒳'} 𝒳` represented by a closed subscheme `Y_w ⊆ U'_w`, and an
affine open `T₀` of `T` mapping into `U'_w`, the morphism `T₀ ⟶ U'_w` factors through `Y_w` by a
morphism locally of finite presentation, compatibly with the 1-morphisms to `𝒳`. -/
theorem exists_reduction_factor
    (W : AlgebraicSpaces B S hS) (x : (algebraicSpaceStackFunctor.{u, w} B S hS).obj W ⟶ 𝒳)
    {U' : BigFppfOver B S hS}
    (b : (algebraicSpaceStackFunctor.{u, w} B S hS).obj (Space.yonedaSpace _ _ _ U') ⟶ 𝒳')
    {U : AlgebraicSpaces B S hS} (iU : U ⟶ Space.yonedaSpace _ _ _ U') [Mono iU.hom]
    (a : (algebraicSpaceStackFunctor.{u, w} B S hS).obj U ⟶ 𝒳)
    {γ : (algebraicSpaceStackFunctor.{u, w} B S hS).map iU ≫ b ≅ a ≫ ι}
    (hU : IsTwoFibreProduct (⟨_, _, _, γ⟩ : TwoCommSq b ι))
    {T : BigFppfOver B S hS} (t : yoneda.obj T ⟶ W.obj)
    (e : Space.yonedaSpace _ _ _ T ⟶ U) (he : Space.IsLocallyOfFinitePresentation B S hS e.hom)
    (η : (algebraicSpaceStackFunctor.{u, w} B S hS).map
        (ObjectProperty.homMk t : Space.yonedaSpace _ _ _ T ⟶ W) ≫ x ≅
      (algebraicSpaceStackFunctor.{u, w} B S hS).map e ≫ a)
    {V : BigFppfOver B S hS} (ιV : V ⟶ U')
    [AlgebraicGeometry.IsOpenImmersion ((BigFppfOver.toScheme B S hS).map ιV)]
    {T₀ : BigFppfOver B S hS} (mT₀ : T₀ ⟶ T)
    [AlgebraicGeometry.IsOpenImmersion ((BigFppfOver.toScheme B S hS).map mT₀)]
    (εV : T₀ ⟶ V) (εU : T ⟶ U') (hεU : yoneda.map εU = e.hom ≫ iU.hom)
    (hεsq : εV ≫ ιV = mT₀ ≫ εU)
    {Uw : AlgebraicSpaces B S hS} {iUw : Uw ⟶ Space.yonedaSpace _ _ _ V}
    {aw : (algebraicSpaceStackFunctor.{u, w} B S hS).obj Uw ⟶ 𝒳}
    {γw : (algebraicSpaceStackFunctor.{u, w} B S hS).map iUw ≫
      ((algebraicSpaceStackFunctor.{u, w} B S hS).map (repHom ιV) ≫ b) ≅ aw ≫ ι}
    (hUw : IsTwoFibreProduct (⟨_, _, _, γw⟩ : TwoCommSq
      ((algebraicSpaceStackFunctor.{u, w} B S hS).map (repHom ιV) ≫ b) ι))
    {Yw : BigFppfOver B S hS} (c : Yw ⟶ V)
    [AlgebraicGeometry.IsClosedImmersion ((BigFppfOver.toScheme B S hS).map c)]
    (eY : yoneda.obj Yw ≅ Uw.obj) (heY : eY.hom ≫ iUw.hom = yoneda.map c) :
    ∃ κ : T₀ ⟶ Yw, κ ≫ c = εV ∧
      AlgebraicGeometry.LocallyOfFinitePresentation ((BigFppfOver.toScheme B S hS).map κ) ∧
      Nonempty ((algebraicSpaceStackFunctor.{u, w} B S hS).map
          (repHom mT₀ ≫ (ObjectProperty.homMk t : Space.yonedaSpace _ _ _ T ⟶ W)) ≫ x ≅
        (algebraicSpaceStackFunctor.{u, w} B S hS).map
          (repHom κ ≫ (ObjectProperty.homMk eY.hom : Space.yonedaSpace _ _ _ Yw ⟶ Uw)) ≫ aw) := by
  let F := algebraicSpaceStackFunctor.{u, w} B S hS
  let bw := F.map (repHom ιV) ≫ b
  let k₁ : Space.yonedaSpace _ _ _ T₀ ⟶ U := repHom mT₀ ≫ e
  have hk₁ : k₁ ≫ iU = repHom (mT₀ ≫ εU) :=
    ObjectProperty.hom_ext _ (by
      show yoneda.map mT₀ ≫ e.hom ≫ iU.hom = yoneda.map (mT₀ ≫ εU)
      rw [yoneda.map_comp, hεU])
  have η₁ : F.map (repHom (mT₀ ≫ εU)) ≫ b ≅ F.map (repHom εV) ≫ bw :=
    eqToIso (by rw [← hεsq, repHom_comp]; rfl) ≪≫ α_ (F.map (repHom εV)) (F.map (repHom ιV)) b
  obtain ⟨k₂, hk₂, ⟨ηk⟩⟩ := exists_factor_of_twoIso γ hUw (repHom (mT₀ ≫ εU)) (repHom εV) η₁
    k₁ hk₁
  let κ : T₀ ⟶ Yw := yoneda.preimage (k₂.hom ≫ eY.inv)
  have hk₂' : k₂.hom ≫ iUw.hom = yoneda.map εV := congrArg (fun f => f.hom) hk₂
  have hκk : yoneda.map κ ≫ eY.hom = k₂.hom := by
    rw [Functor.map_preimage, Category.assoc, Iso.inv_hom_id, Category.comp_id]
  have hκ : κ ≫ c = εV := by
    apply yoneda.map_injective
    rw [yoneda.map_comp, ← heY, ← Category.assoc, hκk, hk₂']
  obtain ⟨j, hj, -⟩ := exists_factor_of_twoIso γw hU iUw (iUw ≫ repHom ιV)
    (α_ (F.map iUw) (F.map (repHom ιV)) b).symm (𝟙 Uw) (Category.id_comp _)
  have hj' : j.hom ≫ iU.hom = iUw.hom ≫ yoneda.map ιV := congrArg (fun f => f.hom) hj
  have hk₂j : k₂.hom ≫ j.hom = k₁.hom := by
    rw [← cancel_mono iU.hom, Category.assoc, hj', ← Category.assoc, hk₂', ← yoneda.map_comp,
      hεsq]
    exact (congrArg (fun f => f.hom) hk₁).symm
  have hk₂κ : repHom κ ≫ (ObjectProperty.homMk eY.hom : Space.yonedaSpace _ _ _ Yw ⟶ Uw) = k₂ :=
    ObjectProperty.hom_ext _ hκk
  refine ⟨κ, hκ, ?_, ⟨α_ (F.map (repHom mT₀))
      (F.map (ObjectProperty.homMk t : Space.yonedaSpace _ _ _ T ⟶ W)) x ≪≫
      whiskerLeftIso (F.map (repHom mT₀)) η ≪≫ (α_ (F.map (repHom mT₀)) (F.map e) a).symm ≪≫
      ηk ≪≫ eqToIso (by rw [hk₂κ])⟩⟩
  have hY := isAlgebraicSpace_yoneda B S hS Yw
  have hT₀ := isAlgebraicSpace_yoneda B S hS T₀
  have hlft : Space.IsLocallyOfFiniteType B S hS (eY.hom ≫ j.hom) := by
    refine Space.isLocallyOfFiniteType_of_comp B S hS hY U.property
      (isAlgebraicSpace_yoneda B S hS U') _ iU.hom ?_
    rw [Category.assoc, hj', ← Category.assoc, heY, ← yoneda.map_comp]
    exact (Space.holdsOnEveryEtaleChart_yoneda_map_iff B S hS
      LocallyOfFiniteType.isEtaleLocalOnSourceAndTarget _).2
      (by rw [Functor.map_comp]; infer_instance)
  have hcomp : Space.IsLocallyOfFinitePresentation B S hS (yoneda.map κ ≫ eY.hom ≫ j.hom) := by
    rw [← Category.assoc, hκk, hk₂j]
    exact Space.isLocallyOfFinitePresentation_comp B S hS hT₀
      (isAlgebraicSpace_yoneda B S hS T) U.property _ _
      (Space.isLocallyOfFinitePresentation_of_isEtale B S hS
        (isEtale_yoneda_map_of_etale _ inferInstance)) he
  exact (Space.holdsOnEveryEtaleChart_yoneda_map_iff B S hS
    LocallyOfFinitePresentation.isEtaleLocalOnSourceAndTarget κ).1
    (Space.isLocallyOfFinitePresentation_of_comp B S hS hT₀ hY U.property _ _ hcomp hlft)

/-- **The reduction of the lifted chart is smooth over `Y_w` after base change to the étale
chart of `U'_w ×_{𝒳'} U'_w`.** For a `Γ(U'_w)`-algebra `X` which is a localization of `Γ(T₀)`
away from one element, compatibly with `U'_w`, the ring `X ⊗_{Γ(U'_w)} Γ(E)` is smooth over
`Γ(Y_w)` through `t`. -/
theorem exists_smooth_reduced_tensor
    (W : AlgebraicSpaces B S hS) (x : (algebraicSpaceStackFunctor.{u, w} B S hS).obj W ⟶ 𝒳)
    (hx : AlgebraicStacks.IsSmooth B S hS x)
    {T : BigFppfOver B S hS} (t : yoneda.obj T ⟶ W.obj) (ht : Space.IsEtale B S hS t)
    {V Yw T₀ E : BigFppfOver B S hS} [IsAffine ((BigFppfOver.toScheme B S hS).obj V)]
    [IsAffine ((BigFppfOver.toScheme B S hS).obj Yw)]
    [IsAffine ((BigFppfOver.toScheme B S hS).obj T₀)]
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
        Γ((BigFppfOver.toScheme B S hS).obj E, ⊤) =
      ((BigFppfOver.toScheme B S hS).map sE).appTop.hom)
    (mT₀ : T₀ ⟶ T) [AlgebraicGeometry.IsOpenImmersion ((BigFppfOver.toScheme B S hS).map mT₀)]
    (εV : T₀ ⟶ V)
    (κ : T₀ ⟶ Yw) (hκ : κ ≫ c = εV)
    (θ₀ : (algebraicSpaceStackFunctor.{u, w} B S hS).map
        (repHom mT₀ ≫ (ObjectProperty.homMk t : Space.yonedaSpace _ _ _ T ⟶ W)) ≫ x ≅
      (algebraicSpaceStackFunctor.{u, w} B S hS).map
        (repHom κ ≫ (ObjectProperty.homMk eY.hom : Space.yonedaSpace _ _ _ Yw ⟶ Uw)) ≫ aw)
    (X : Type u) [CommRing X] [Algebra Γ((BigFppfOver.toScheme B S hS).obj V, ⊤) X]
    [Algebra.FiniteType Γ((BigFppfOver.toScheme B S hS).obj V, ⊤) X]
    (lam : Γ((BigFppfOver.toScheme B S hS).obj T₀, ⊤) →+* X)
    (hlamε : lam.comp ((BigFppfOver.toScheme B S hS).map εV).appTop.hom =
      algebraMap Γ((BigFppfOver.toScheme B S hS).obj V, ⊤) X)
    (d : Γ((BigFppfOver.toScheme B S hS).obj T₀, ⊤))
    (hloc : @IsLocalization.Away _ _ d X _ lam.toAlgebra) :
    ∃ ψ : Γ((BigFppfOver.toScheme B S hS).obj Yw, ⊤) →+*
        X ⊗[Γ((BigFppfOver.toScheme B S hS).obj V, ⊤)] Γ((BigFppfOver.toScheme B S hS).obj E, ⊤),
      ψ.Smooth ∧ ψ.comp ((BigFppfOver.toScheme B S hS).map c).appTop.hom =
        Algebra.TensorProduct.includeRight.toRingHom.comp
          ((BigFppfOver.toScheme B S hS).map tE).appTop.hom := by
  let t' : Space.yonedaSpace _ _ _ T ⟶ W := ObjectProperty.homMk t
  let T₁ := BigFppfOver.specObj V X
  let mT₁ : T₁ ⟶ T₀ := BigFppfOver.specObjHom εV lam hlamε
  have hmT₁ : mT₁ ≫ εV = BigFppfOver.specObjToBase V X := BigFppfOver.hom_ext_of_ringOf (by
    rw [BigFppfOver.ringOf_comp, BigFppfOver.ringOf_specObjHom, BigFppfOver.ringOf_specObjToBase]
    exact hlamε)
  have hmT₁et : AlgebraicGeometry.Etale ((BigFppfOver.toScheme B S hS).map mT₁) := by
    rw [BigFppfOver.prop_iff_ringOf @AlgebraicGeometry.Etale, BigFppfOver.ringOf_specObjHom]
    let := lam.toAlgebra
    exact RingHom.etale_algebraMap.mpr (Algebra.Etale.of_isLocalizationAway d)
  have hk : (repHom κ ≫ (ObjectProperty.homMk eY.hom : Space.yonedaSpace _ _ _ Yw ⟶ Uw)) ≫ iUw =
      repHom εV := ObjectProperty.hom_ext _ (by
    show yoneda.map κ ≫ eY.hom ≫ iUw.hom = yoneda.map εV
    rw [heY, ← yoneda.map_comp, hκ])
  let k₂ := repHom κ ≫ (ObjectProperty.homMk eY.hom : Space.yonedaSpace _ _ _ Yw ⟶ Uw)
  let θ₁ : (algebraicSpaceStackFunctor.{u, w} B S hS).map (repHom mT₀ ≫ t') ≫ (x ≫ ι) ≅
      (algebraicSpaceStackFunctor.{u, w} B S hS).map (repHom εV) ≫ bw :=
    (α_ _ _ _).symm ≪≫ whiskerRightIso θ₀ ι ≪≫
      α_ ((algebraicSpaceStackFunctor.{u, w} B S hS).map k₂) aw ι ≪≫
      whiskerLeftIso ((algebraicSpaceStackFunctor.{u, w} B S hS).map k₂) γw.symm ≪≫
      (α_ ((algebraicSpaceStackFunctor.{u, w} B S hS).map k₂)
        ((algebraicSpaceStackFunctor.{u, w} B S hS).map iUw) bw).symm ≪≫
      eqToIso (by rw [← hk]; rfl)
  let xT : (algebraicSpaceStackFunctor.{u, w} B S hS).obj (Space.yonedaSpace _ _ _ T₁) ⟶ 𝒳 :=
    (algebraicSpaceStackFunctor.{u, w} B S hS).map (repHom mT₁ ≫ repHom mT₀ ≫ t') ≫ x
  have hxTet : Space.IsEtale B S hS (yoneda.map mT₁ ≫ yoneda.map mT₀ ≫ t) := by
    rw [← Category.assoc, ← yoneda.map_comp]
    refine Space.isEtale_comp B S hS (isEtale_yoneda_map_of_etale _ ?_) ht
    rw [Functor.map_comp]
    infer_instance
  have hxT : IsRelativelySmooth.{u, u, u + 1} B S hS xT.hom :=
    isRelativelySmooth_of_isSmooth_space_source xT
      (AlgebraicStacks.isSmooth_comp B S hS _ _
        (isSmooth_map_of_isSmooth.{u, w} (repHom mT₁ ≫ repHom mT₀ ≫ t')
          (Space.isSmooth_of_isEtale B S hS W.property hxTet)) hx)
  let θ : xT ≫ ι ≅
      (algebraicSpaceStackFunctor.{u, w} B S hS).map (repHom (BigFppfOver.specObjToBase V X)) ≫
        bw :=
    α_ _ _ _ ≪≫ whiskerTwoIso' (repHom mT₁) θ₁ ≪≫ eqToIso (by rw [← repHom_comp, hmT₁])
  exact exists_smooth_tensor_of_twoFibreProduct hUw c eY heY hR eE heE sE tE hsE htE hs X xT hxT θ

/-- **Smoothness of the lifted chart over `𝒳'`, by the smooth diagram test (Stacks 075U).** Let
`E` be an affine scheme of the site with `s, t : E ⟶ U'_w` whose composites with `b_w` are
2-isomorphic, and let `α : S₁[1/h'] → Pr`, `β : Γ(E) → Pr` be ring maps agreeing on `Γ(U'_w)`
(through `s`), with `α` smooth and surjective on spectra and `β ∘ t` smooth. Then
`Spec S₁[1/h'] ⟶ U'_w ⟶ 𝒳'` is smooth. -/
theorem isSmooth_specAway_of_chart {V E : BigFppfOver B S hS}
    [IsAffine ((BigFppfOver.toScheme B S hS).obj V)]
    [IsAffine ((BigFppfOver.toScheme B S hS).obj E)]
    (bw : (algebraicSpaceStackFunctor.{u, w} B S hS).obj (Space.yonedaSpace _ _ _ V) ⟶ 𝒳')
    (hbw : AlgebraicStacks.IsSmooth B S hS bw)
    (sE tE : E ⟶ V) (ρE : (algebraicSpaceStackFunctor.{u, w} B S hS).map (repHom sE) ≫ bw ≅
      (algebraicSpaceStackFunctor.{u, w} B S hS).map (repHom tE) ≫ bw)
    [Algebra Γ((BigFppfOver.toScheme B S hS).obj V, ⊤) Γ((BigFppfOver.toScheme B S hS).obj E, ⊤)]
    (hs : algebraMap Γ((BigFppfOver.toScheme B S hS).obj V, ⊤)
        Γ((BigFppfOver.toScheme B S hS).obj E, ⊤) =
      ((BigFppfOver.toScheme B S hS).map sE).appTop.hom)
    (S₁ : Type u) [CommRing S₁] [Algebra Γ((BigFppfOver.toScheme B S hS).obj V, ⊤) S₁]
    [Algebra.FiniteType Γ((BigFppfOver.toScheme B S hS).obj V, ⊤) S₁]
    (h' : S₁) (Pr : Type u) [CommRing Pr] (α : Localization.Away h' →+* Pr)
    (β : Γ((BigFppfOver.toScheme B S hS).obj E, ⊤) →+* Pr)
    (hαβ : α.comp (algebraMap Γ((BigFppfOver.toScheme B S hS).obj V, ⊤) (Localization.Away h')) =
      β.comp (algebraMap Γ((BigFppfOver.toScheme B S hS).obj V, ⊤)
        Γ((BigFppfOver.toScheme B S hS).obj E, ⊤)))
    (hαsm : @Algebra.Smooth (Localization.Away h') _ Pr _ α.toAlgebra)
    (hαsurj : Function.Surjective (PrimeSpectrum.comap α))
    (hβsm : @Algebra.Smooth Γ((BigFppfOver.toScheme B S hS).obj V, ⊤) _ Pr _
      (β.comp ((BigFppfOver.toScheme B S hS).map tE).appTop.hom).toAlgebra) :
    AlgebraicStacks.IsSmooth B S hS
      ((algebraicSpaceStackFunctor.{u, w} B S hS).map
        (repHom (BigFppfOver.specObjToBase V (Localization.Away h'))) ≫ bw) := by
  let : Algebra Γ((BigFppfOver.toScheme B S hS).obj V, ⊤) Pr :=
    (α.comp (algebraMap Γ((BigFppfOver.toScheme B S hS).obj V, ⊤) (Localization.Away h'))).toAlgebra
  have : Algebra.FiniteType Γ((BigFppfOver.toScheme B S hS).obj V, ⊤) Pr := by
    have h1 : α.FiniteType := by
      let := α.toAlgebra
      have := hαsm
      exact RingHom.finiteType_algebraMap.mpr inferInstance
    have h2 :
        (algebraMap Γ((BigFppfOver.toScheme B S hS).obj V, ⊤) (Localization.Away h')).FiniteType :=
      RingHom.finiteType_algebraMap.mpr inferInstance
    exact RingHom.finiteType_algebraMap.mp (h1.comp h2)
  let T'w := BigFppfOver.specObj V (Localization.Away h')
  let P := BigFppfOver.specObj V Pr
  let αA : Localization.Away h' →ₐ[Γ((BigFppfOver.toScheme B S hS).obj V, ⊤)] Pr :=
    { α with commutes' := fun _ => rfl }
  let πP : P ⟶ T'w := BigFppfOver.specObjMap αA
  have hβ : β.comp ((BigFppfOver.toScheme B S hS).map sE).appTop.hom =
      algebraMap Γ((BigFppfOver.toScheme B S hS).obj V, ⊤) Pr := by
    rw [← hs, ← hαβ]
    rfl
  let PE : P ⟶ E := BigFppfOver.specObjHom sE β hβ
  let hP : P ⟶ V := PE ≫ tE
  have hπPsm : AlgebraicGeometry.Smooth ((BigFppfOver.toScheme B S hS).map πP) :=
    (BigFppfOver.prop_specObjMap_iff @AlgebraicGeometry.Smooth αA).mpr hαsm
  have hπPsurj : AlgebraicGeometry.Surjective ((BigFppfOver.toScheme B S hS).map πP) := by
    rw [BigFppfOver.toScheme_map_specObjMap]
    exact ⟨hαsurj⟩
  have hhPsm : AlgebraicGeometry.Smooth ((BigFppfOver.toScheme B S hS).map hP) := by
    rw [BigFppfOver.prop_iff_ringOf @AlgebraicGeometry.Smooth, BigFppfOver.ringOf_comp,
      BigFppfOver.ringOf_specObjHom]
    exact hβsm
  have heq : πP ≫ BigFppfOver.specObjToBase V (Localization.Away h') = PE ≫ sE :=
    BigFppfOver.hom_ext_of_ringOf (by
      rw [BigFppfOver.ringOf_specObjMap_comp, BigFppfOver.ringOf_specObjToBase,
        BigFppfOver.ringOf_comp, BigFppfOver.ringOf_specObjHom, hβ]
      exact αA.comp_algebraMap)
  let τP : (algebraicSpaceStackFunctor.{u, w} B S hS).map (repHom πP) ≫
      ((algebraicSpaceStackFunctor.{u, w} B S hS).map
        (repHom (BigFppfOver.specObjToBase V (Localization.Away h'))) ≫ bw) ≅
      (algebraicSpaceStackFunctor.{u, w} B S hS).map (repHom hP) ≫ bw :=
    (α_ _ _ _).symm ≪≫ eqToIso (by rw [← Functor.map_comp, ← repHom_comp, heq]) ≪≫
      eqToIso (by rw [repHom_comp]) ≪≫ whiskerTwoIso (repHom PE) bw ρE ≪≫
      eqToIso (by rw [← repHom_comp])
  have hF := isAlgebraicSpace_yoneda B S hS P
  have hG := isAlgebraicSpace_yoneda B S hS T'w
  exact ⟨yoneda.obj P, yoneda.obj V, hF, isAlgebraicSpace_yoneda B S hS V,
    ((algebraicSpaceStackFunctor.{u, w} B S hS).map (repHom πP)).hom, bw.hom, yoneda.map hP,
    ⟨(InducedBicategory.isoHom τP).symm⟩,
    isRelativelySmooth_associatedMap B S hS hF hG (yoneda.map πP)
      ((Space.isSmooth_yoneda_map_iff B S hS πP).mpr hπPsm),
    isSurjectiveOnObjects_associatedMap B S hS hF hG (yoneda.map πP)
      ((Space.surjective_pointsMap_yoneda_iff B S hS πP).mpr hπPsurj.surj),
    isRelativelySmooth_of_isSmooth_space_source bw hbw,
    (Space.isSmooth_yoneda_map_iff B S hS hP).mpr hhPsm⟩

/-- **A smooth lift from a cartesian square of schemes over the local chart.** Let
`U_w = U'_w ×_{𝒳'} 𝒳` be represented by `Y_w ⟶ U'_w`, let `A = T'_w ×_{U'_w} Y_w` be a pullback
square of schemes of the site with `T'_w ⟶ U'_w ⟶ 𝒳'` smooth, and let `A ⟶ W` be étale with
1-morphism to `𝒳` 2-isomorphic to `A ⟶ Y_w ⟶ 𝒳`. Then `A ⟶ W` is the base of a smooth lift along
`ι`. -/
theorem exists_etaleSmoothLift_of_isPullback (hι : IsThickening ι)
    (W : AlgebraicSpaces B S hS) (x : (algebraicSpaceStackFunctor.{u, w} B S hS).obj W ⟶ 𝒳)
    (hx : AlgebraicStacks.IsSmooth B S hS x)
    {V Yw A T'w : BigFppfOver B S hS}
    {bw : (algebraicSpaceStackFunctor.{u, w} B S hS).obj (Space.yonedaSpace _ _ _ V) ⟶ 𝒳'}
    {Uw : AlgebraicSpaces B S hS} {iUw : Uw ⟶ Space.yonedaSpace _ _ _ V}
    {aw : (algebraicSpaceStackFunctor.{u, w} B S hS).obj Uw ⟶ 𝒳}
    {γw : (algebraicSpaceStackFunctor.{u, w} B S hS).map iUw ≫ bw ≅ aw ≫ ι}
    (hUw : IsTwoFibreProduct (⟨_, _, _, γw⟩ : TwoCommSq bw ι))
    (c : Yw ⟶ V) (eY : yoneda.obj Yw ≅ Uw.obj) (heY : eY.hom ≫ iUw.hom = yoneda.map c)
    (AT : A ⟶ T'w) (AY : A ⟶ Yw) (Tb : T'w ⟶ V)
    (hApb : IsPullback (yoneda.map AT) (yoneda.map AY) (yoneda.map Tb) (yoneda.map c))
    (hsm : AlgebraicStacks.IsSmooth B S hS
      ((algebraicSpaceStackFunctor.{u, w} B S hS).map (repHom Tb) ≫ bw))
    (m : yoneda.obj A ⟶ W.obj) (hm : Space.IsEtale B S hS m)
    (ea : (algebraicSpaceStackFunctor.{u, w} B S hS).map
        (ObjectProperty.homMk m : Space.yonedaSpace _ _ _ A ⟶ W) ≫ x ≅
      (algebraicSpaceStackFunctor.{u, w} B S hS).map
        (repHom AY ≫ (ObjectProperty.homMk eY.hom : Space.yonedaSpace _ _ _ Yw ⟶ Uw)) ≫ aw) :
    ∃ ξ : EtaleSmoothLift B S hS ι hι W x hx,
      ξ.base = Space.SpacesEtale.ofRepresentable B S hS W A m hm := by
  have hApb' : IsPullback (yoneda.map AT) (yoneda.map AY ≫ eY.hom) (yoneda.map Tb) iUw.hom :=
    hApb.of_iso (Iso.refl _) (Iso.refl _) eY (Iso.refl _) (by simp) (by simp) (by simp)
      (by simp [heY])
  have hApb'' : IsPullback (repHom AT).hom
      (repHom AY ≫ (ObjectProperty.homMk eY.hom : Space.yonedaSpace _ _ _ Yw ⟶ Uw)).hom
      (repHom Tb).hom iUw.hom := hApb'
  let Q : TwoCommSq ((algebraicSpaceStackFunctor.{u, w} B S hS).map (repHom Tb))
      ((algebraicSpaceStackFunctor.{u, w} B S hS).map iUw) :=
    ⟨(algebraicSpaceStackFunctor.{u, w} B S hS).obj (Space.yonedaSpace _ _ _ A),
      (algebraicSpaceStackFunctor.{u, w} B S hS).map (repHom AT),
      (algebraicSpaceStackFunctor.{u, w} B S hS).map
        (repHom AY ≫ (ObjectProperty.homMk eY.hom : Space.yonedaSpace _ _ _ Yw ⟶ Uw)),
      Bicategory.InducedBicategory.isoMk (fibredCategorySquare hApb''.w).iso⟩
  let Pw : TwoCommSq bw ι := ⟨_, _, _, γw⟩
  have hsw := isTwoFibreProduct_swap
    (isTwoFibreProduct_pasteFst Pw hUw Q (isTwoFibreProduct_of_isPullback.{u, w} hApb''))
  let eb : (algebraicSpaceStackFunctor.{u, w} B S hS).map (repHom AT) ≅
      𝟙 _ ≫ (algebraicSpaceStackFunctor.{u, w} B S hS).map (repHom AT) := (λ_ _).symm
  let ea' := ea ≪≫ (λ_ _).symm
  exact ⟨{ base := Space.SpacesEtale.ofRepresentable B S hS W A m hm
           ambient := Space.yonedaSpace _ _ _ T'w
           inclusion := repHom AT
           ambientMap := (algebraicSpaceStackFunctor.{u, w} B S hS).map (repHom Tb) ≫ bw
           isSmooth_ambientMap := hsm
           comm := ((Pw.pasteFst Q).swap.ofComparison (𝟙 _) ea' eb).iso
           isTwoFibreProduct := isTwoFibreProduct_ofComparison_id _ hsw ea' eb }, rfl⟩

end AlgebraicGeometry.Stack.LiftingAffinesLocal

end
