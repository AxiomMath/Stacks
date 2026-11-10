module

public import StacksFrontier.AlgebraicGeometry.Spaces.ThickeningAffineOverAffineBase.FirstOrderStep
public import StacksFrontier.AlgebraicGeometry.Spaces.ThickeningAffineOverAffineBase.QuotientLevels

/-!
# Affineness over a finitely generated part of a thickening of an affine base

Let `U` be an algebraic space over an affine object `T` of the site, with ring of functions `A`,
and let `T₀ ⟶ T` be a thickening, with ideal `I ⊆ A`.  If `U ×_T T₀` is affine, then there is a
finitely generated ideal `K ⊆ I` such that `U ×_T Spec(A/K)` is affine.  As `I` consists of
nilpotent elements, `K` is nilpotent, so `Spec(A/K) ⟶ T` is a finite-order thickening.

This is the first step of the proof of Stacks 07SQ, read along the system of the `Spec(A/K)`:
the coefficients of a submersive presentation of a thin chart, and lifts of its generators, are
chosen on an affine chart `W` of `U`; the finitely many equations they satisfy over `T₀` — the
invariance of the coefficients under the kernel pair of the chart and the vanishing of the
relations at the generators — hold modulo `I`, hence modulo a finitely generated `K ⊆ I`, and
then `AlgebraicGeometry.Space.exists_iso_yoneda_of_presentationLift` applies over `Spec(A/K)`.

## Main results

* `AlgebraicGeometry.Space.exists_fg_le_of_mem_map`: an element of an extended ideal lies in the
  extension of a finitely generated subideal.
* `AlgebraicGeometry.Space.exists_isFiniteOrderThickening_isAffineSpace_pullback`.
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits MvPolynomial

universe u

namespace AlgebraicGeometry.Space

/-- An element of an extended ideal lies in the extension of a finitely generated subideal. -/
theorem exists_fg_le_of_mem_map {R R' : Type*} [CommRing R] [CommRing R'] (f : R →+* R')
    {I : Ideal R} {x : R'} (hx : x ∈ I.map f) : ∃ K : Ideal R, K.FG ∧ K ≤ I ∧ x ∈ K.map f := by
  classical
  rw [Ideal.map, Ideal.span] at hx
  obtain ⟨T, hT, hxT⟩ := Submodule.mem_span_finite_of_mem_span hx
  choose g hg hgf using fun y : T ↦ hT y.2
  refine ⟨Ideal.span (Set.range g), ⟨(Finset.univ.image g), by simp⟩, ?_, ?_⟩
  · rw [Ideal.span_le]
    rintro _ ⟨y, rfl⟩
    exact hg y
  · refine Submodule.span_le.mpr ?_ hxT
    intro y hy
    have h1 : f (g ⟨y, hy⟩) = y := hgf ⟨y, hy⟩
    have h2 := Ideal.mem_map_of_mem f (Ideal.subset_span (s := Set.range g) ⟨⟨y, hy⟩, rfl⟩)
    rw [h1] at h2
    exact h2

/-- An element of the extension of an ideal killed by a ring map along which the extension is
taken is killed. -/
theorem map_eq_zero_of_mem_map {R R' R'' Q : Type*} [CommRing R] [CommRing R'] [CommRing R'']
    [CommRing Q] (f : R →+* R') (g : R' →+* R'') (q : R →+* Q) (h : Q →+* R'') {K : Ideal R}
    (hK : K ≤ RingHom.ker q) (hcomm : g.comp f = h.comp q) {x : R'} (hx : x ∈ K.map f) :
    g x = 0 := by
  have : K.map f ≤ RingHom.ker g := by
    rw [Ideal.map_le_iff_le_comap]
    intro a ha
    simp only [Ideal.mem_comap, RingHom.mem_ker]
    rw [← RingHom.comp_apply, hcomm, RingHom.comp_apply, RingHom.mem_ker.mp (hK ha), map_zero]
  exact this hx

/-- A preimage of a unit along a surjection with nil kernel is a unit. -/
theorem isUnit_of_isUnit_map_of_ker_nil {R R' : Type*} [CommRing R] [CommRing R'] (f : R →+* R')
    (hf : Function.Surjective f) (hnil : ∀ x ∈ RingHom.ker f, IsNilpotent x) {x : R}
    (hx : IsUnit (f x)) : IsUnit x := by
  obtain ⟨y', hy'⟩ := hx.exists_right_inv
  obtain ⟨y, rfl⟩ := hf y'
  have hn : IsNilpotent (x * y - 1) := hnil _ (by simp [RingHom.mem_ker, hy'])
  have : IsUnit (x * y) := by
    have := hn.isUnit_one_add
    rwa [add_sub_cancel] at this
  exact isUnit_of_mul_isUnit_left this

variable (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)

/-- **Roots of the relations over a nil surjection give a lift of the localized quotient.**  If
`v` is a root of the relations `g'` over `E`, and `v` reduces to the generators of a submersive
presentation along a surjection `f : E ⟶ D₀` with nil kernel compatible with the coefficients,
then the localized quotient maps to `E`. -/
theorem exists_liftOfRoots {P C₀ D₀ E : Type u} [CommRing P] [CommRing C₀] [CommRing D₀]
    [CommRing E] [Algebra C₀ D₀] {τ σ : Type} [Finite τ] [Finite σ]
    (P₀ : Algebra.SubmersivePresentation C₀ D₀ τ σ)
    (g' : σ → MvPolynomial τ P) (φ : P →+* C₀) (hrel : ∀ j, (g' j).map φ = P₀.relation j)
    (θ : P →+* E) (f : E →+* D₀) (hf : Function.Surjective f)
    (hnil : ∀ x ∈ RingHom.ker f, IsNilpotent x) (hθ₀ : f.comp θ = (algebraMap C₀ D₀).comp φ)
    (v : τ → E) (hv : ∀ j, eval₂ θ v (g' j) = 0) (hfv : ∀ i, f (v i) = P₀.val i) :
    ∃ θ' : Algebra.LocalizedQuotient.ring g' P₀.map P₀.map_inj →+* E,
      θ'.comp (algebraMap _ _) = θ ∧ ∀ i, f (θ' (algebraMap (Algebra.LocalizedQuotient.quot g') _
        (Ideal.Quotient.mk _ (MvPolynomial.X i)))) = P₀.val i := by
  let : Algebra P E := θ.toAlgebra
  let : Algebra P C₀ := φ.toAlgebra
  let : Algebra P D₀ := ((algebraMap C₀ D₀).comp φ).toAlgebra
  have : IsScalarTower P C₀ D₀ := IsScalarTower.of_algebraMap_eq' rfl
  have hv' : ∀ j, aeval v (g' j) = 0 := hv
  have hrel'' : ∀ j, P₀.relation j = (g' j).map (algebraMap P C₀) := fun j ↦ (hrel j).symm
  have hu : IsUnit (Algebra.LocalizedQuotient.quotLift g' v hv'
      (Algebra.LocalizedQuotient.jac g' P₀.map P₀.map_inj)) := by
    refine isUnit_of_isUnit_map_of_ker_nil f hf hnil ?_
    obtain ⟨y, hy⟩ := Ideal.Quotient.mk_surjective
      (Algebra.LocalizedQuotient.jac g' P₀.map P₀.map_inj)
    have hjac := Algebra.LocalizedQuotient.quotToAlgHom_jac g' P₀.map P₀.map_inj P₀ hrel'' rfl
    rw [← hy, Algebra.LocalizedQuotient.quotToAlgHom_mk] at hjac
    rw [← hy, Algebra.LocalizedQuotient.quotLift_mk, aeval_def, RingHom.algebraMap_toAlgebra,
      MvPolynomial.hom_eval₂, hθ₀, funext hfv]
    have := P₀.jacobian_isUnit
    rwa [← hjac, aeval_def] at this
  refine ⟨(Algebra.LocalizedQuotient.liftOfRoots g' P₀.map P₀.map_inj v hv' hu).toRingHom,
    (Algebra.LocalizedQuotient.liftOfRoots g' P₀.map P₀.map_inj v hv' hu).comp_algebraMap,
    fun i ↦ ?_⟩
  change f (Algebra.LocalizedQuotient.liftOfRoots g' P₀.map P₀.map_inj v hv' hu
    (algebraMap (Algebra.LocalizedQuotient.quot g') _ (Ideal.Quotient.mk _ (MvPolynomial.X i)))) =
      P₀.val i
  rw [Algebra.LocalizedQuotient.liftOfRoots_algebraMap, Algebra.LocalizedQuotient.quotLift_mk,
    aeval_X]
  exact hfv i

/-- A commutative square of the site gives a commutative square of rings of global functions. -/
theorem appTop_comp_appTop_of_comp_eq {X Y Z V : BigFppfOver B S hS} {a : V ⟶ X} {b : V ⟶ Y}
    {c : X ⟶ Z} {d : Y ⟶ Z} (h : a ≫ c = b ≫ d) :
    ((BigFppfOver.toScheme B S hS).map a).appTop.hom.comp
      ((BigFppfOver.toScheme B S hS).map c).appTop.hom =
    ((BigFppfOver.toScheme B S hS).map b).appTop.hom.comp
      ((BigFppfOver.toScheme B S hS).map d).appTop.hom := by
  rw [← CommRingCat.hom_comp, ← CommRingCat.hom_comp, ← Scheme.Hom.comp_appTop,
    ← Scheme.Hom.comp_appTop, ← Functor.map_comp, ← Functor.map_comp, h]

/-- Global sections of a composite, applied to an element. -/
private theorem appTop_map_comp_apply {X Y Z : BigFppfOver B S hS} (a : X ⟶ Y) (b : Y ⟶ Z)
    (x : Γ((BigFppfOver.toScheme B S hS).obj Z, ⊤)) :
    ((BigFppfOver.toScheme B S hS).map (a ≫ b)).appTop x =
      ((BigFppfOver.toScheme B S hS).map a).appTop
        (((BigFppfOver.toScheme B S hS).map b).appTop x) := by
  rw [Functor.map_comp, Scheme.Hom.comp_appTop, CommRingCat.comp_apply]

/-- The first projection of a chart level is compatible with a morphism of charts on global
sections. -/
private theorem appTop_levelKernelMap_fst {U : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u}
    {T R W T' : BigFppfOver B S hS} (π : U ⟶ yoneda.obj T) (w : yoneda.obj W ⟶ U) {s : R ⟶ W}
    (a : R ⟶ W) (ha : yoneda.map a ≫ w = yoneda.map s ≫ w) (j : T' ⟶ T)
    (x : Γ((BigFppfOver.toScheme B S hS).obj W, ⊤)) :
    ((BigFppfOver.toScheme B S hS).map (levelKernelMap π w a ha j)).appTop
        (((BigFppfOver.toScheme B S hS).map (pullback.fst (levelChartBase π w) j)).appTop x) =
      ((BigFppfOver.toScheme B S hS).map
        (pullback.fst (levelChartBase π (yoneda.map s ≫ w)) j)).appTop
        (((BigFppfOver.toScheme B S hS).map a).appTop x) := by
  rw [← appTop_map_comp_apply, ← appTop_map_comp_apply, levelKernelMap_fst]

/-- The base morphisms of two charts related by a pullback square are compatible. -/
private theorem comp_levelChartBase_eq_of_isPullback {U : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u}
    {T X Y V : BigFppfOver B S hS} (π : U ⟶ yoneda.obj T) {v : yoneda.obj V ⟶ U}
    {y : yoneda.obj Y ⟶ U} {a : X ⟶ V} {c : X ⟶ Y}
    (h : IsPullback (yoneda.map a) (yoneda.map c) v y) :
    a ≫ levelChartBase π v = c ≫ levelChartBase π y := by
  apply yoneda.map_injective
  rw [Functor.map_comp, Functor.map_comp, yoneda_map_levelChartBase, yoneda_map_levelChartBase,
    ← Category.assoc, h.w, Category.assoc]

/-- The base change of a thin square along a factorization of the thickening through a closed
subobject of the base. -/
theorem isPullback_thin_level {U : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u}
    {T₀ T T' O₀ : BigFppfOver B S hS}
    {k : T₀ ⟶ T} {j : T₀ ⟶ T'} {ι : T' ⟶ T} (hj : j ≫ ι = k) {π : U ⟶ yoneda.obj T}
    {x₀ : yoneda.obj O₀ ⟶ U} {y₀ : yoneda.obj O₀ ⟶ yoneda.obj T₀}
    (hx₀ : IsPullback x₀ y₀ π (yoneda.map k)) :
    IsPullback (pullback.lift x₀ (y₀ ≫ yoneda.map j) (by rw [hx₀.w, Category.assoc,
        ← Functor.map_comp, hj]) : yoneda.obj O₀ ⟶ pullback π (yoneda.map ι)) y₀
      (pullback.snd π (yoneda.map ι)) (yoneda.map j) := by
  refine IsPullback.of_right ?_ (pullback.lift_snd _ _ _) (IsPullback.of_hasPullback _ _)
  rwa [pullback.lift_fst, ← Functor.map_comp, hj]

/-- **The thin data at a closed level of the base.**  For a factorization `k = j ≫ ι` of the
thickening through a closed subobject `T'` of the base, the base changes to `T'` of the chart and
of the thin point form again a thin square. -/
theorem thin_level {U : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u} {T₀ T T' O₀ W : BigFppfOver B S hS}
    {k : T₀ ⟶ T} {j : T₀ ⟶ T'} {ι : T' ⟶ T} (hj : j ≫ ι = k) {π : U ⟶ yoneda.obj T}
    (e₀ : pullback π (yoneda.map k) ≅ yoneda.obj O₀) (w : yoneda.obj W ⟶ U)
    (c₀ : levelChart π w k ⟶ O₀) (hc₀y : yoneda.map c₀ = levelChartMap π w k ≫ e₀.hom)
    (hsq₀ : IsPullback (yoneda.map (pullback.fst (levelChartBase π w) k)) (yoneda.map c₀) w
      (e₀.inv ≫ pullback.fst π (yoneda.map k))) :
    ∃ (x₀' : yoneda.obj O₀ ⟶ pullback π (yoneda.map ι)) (ι₀ : levelChart π w k ⟶ levelChart π w ι),
      IsPullback x₀' (e₀.inv ≫ pullback.snd π (yoneda.map k)) (pullback.snd π (yoneda.map ι))
        (yoneda.map j) ∧
      IsPullback (yoneda.map ι₀) (yoneda.map c₀) (levelChartMap π w ι) x₀' ∧
      x₀' ≫ pullback.fst π (yoneda.map ι) = e₀.inv ≫ pullback.fst π (yoneda.map k) ∧
      ι₀ ≫ pullback.fst (levelChartBase π w) ι = pullback.fst (levelChartBase π w) k ∧
      ι₀ ≫ pullback.snd (levelChartBase π w) ι = pullback.snd (levelChartBase π w) k ≫ j := by
  have hx₀ : IsPullback (e₀.inv ≫ pullback.fst π (yoneda.map k))
      (e₀.inv ≫ pullback.snd π (yoneda.map k)) π (yoneda.map k) :=
    (IsPullback.of_hasPullback π (yoneda.map k)).of_iso e₀ (Iso.refl _) (Iso.refl _)
      (Iso.refl _) (by simp) (by simp) (by simp) (by simp)
  refine ⟨_, pullback.map _ _ _ _ (𝟙 W) j (𝟙 T) (by simp) (by simp [hj]),
    isPullback_thin_level B S hS hj hx₀, ?_, pullback.lift_fst _ _ _, by simp, by simp⟩
  refine IsPullback.of_right ?_ ?_ (isPullback_levelChart π w ι)
  · rwa [← Functor.map_comp, pullback.lift_fst, pullback.lift_fst, Category.comp_id]
  · apply pullback.hom_ext
    · rw [Category.assoc, Category.assoc, levelChartMap_fst, pullback.lift_fst,
        ← Functor.map_comp_assoc]
      simp only [pullback.lift_fst, Category.comp_id]
      exact hsq₀.w
    · rw [Category.assoc, Category.assoc, levelChartMap_snd, pullback.lift_snd,
        ← Functor.map_comp, pullback.lift_snd, hc₀y, Functor.map_comp]
      simp only [Category.assoc, Iso.hom_inv_id_assoc, levelChartMap_snd_assoc]

/-- The presentation step at a closed level of the base, given the thin data at the level. -/
theorem isAffineSpace_pullback_quotientLevel_of_lifts_aux {U : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u}
    (hU : IsAlgebraicSpace B S hS U) {T₀ T : BigFppfOver B S hS}
    [IsAffine ((BigFppfOver.toScheme B S hS).obj T)] (k : T₀ ⟶ T)
    (hk : Stacks.Thickenings.IsThickening ((BigFppfOver.toScheme B S hS).map k))
    (π : U ⟶ yoneda.obj T) {O₀ : BigFppfOver B S hS}
    [IsAffine ((BigFppfOver.toScheme B S hS).obj O₀)]
    (e₀ : pullback π (yoneda.map k) ≅ yoneda.obj O₀) {W R : BigFppfOver B S hS}
    [IsAffine ((BigFppfOver.toScheme B S hS).obj W)]
    [IsAffine ((BigFppfOver.toScheme B S hS).obj R)] (w : yoneda.obj W ⟶ U)
    (hws : (MorphismProperty.presheaf (MorphismProperty.inverseImage
      (@Surjective.{u} : MorphismProperty Scheme.{u}) (BigFppfOver.toScheme B S hS))) w)
    (hwe : (MorphismProperty.presheaf (MorphismProperty.inverseImage
      (@Etale.{u} : MorphismProperty Scheme.{u}) (BigFppfOver.toScheme B S hS))) w)
    {s t : R ⟶ W} (hR : IsPullback (yoneda.map s) (yoneda.map t) w w)
    (c₀ : levelChart π w k ⟶ O₀)
    [IsAffine ((BigFppfOver.toScheme B S hS).obj (levelChart π w k))]
    {τ σ : Type} [Finite τ] [Finite σ]
    [Algebra Γ((BigFppfOver.toScheme B S hS).obj O₀, ⊤)
      Γ((BigFppfOver.toScheme B S hS).obj (levelChart π w k), ⊤)]
    (hc₀ : algebraMap Γ((BigFppfOver.toScheme B S hS).obj O₀, ⊤)
      Γ((BigFppfOver.toScheme B S hS).obj (levelChart π w k), ⊤) =
      ((BigFppfOver.toScheme B S hS).map c₀).appTop.hom)
    (P₀ : Algebra.SubmersivePresentation Γ((BigFppfOver.toScheme B S hS).obj O₀, ⊤)
      Γ((BigFppfOver.toScheme B S hS).obj (levelChart π w k), ⊤) τ σ)
    (hcard : Nat.card τ = Nat.card σ) {F : Type} [Finite F]
    (coef : F → Γ((BigFppfOver.toScheme B S hS).obj O₀, ⊤))
    (g : σ → MvPolynomial τ (MvPolynomial F (affineBaseRing B S hS T)))
    (hrel : ∀ j, (g j).map (coefSpecialization B S hS π
      (e₀.inv ≫ pullback.fst π (yoneda.map k)) coef) = P₀.relation j)
    (p : F → Γ((BigFppfOver.toScheme B S hS).obj W, ⊤))
    (hp : ∀ c, ((BigFppfOver.toScheme B S hS).map (pullback.fst (levelChartBase π w) k)).appTop
      (p c) = ((BigFppfOver.toScheme B S hS).map c₀).appTop (coef c))
    (q : τ → Γ((BigFppfOver.toScheme B S hS).obj W, ⊤))
    (hq : ∀ i, ((BigFppfOver.toScheme B S hS).map (pullback.fst (levelChartBase π w) k)).appTop
      (q i) = P₀.val i)
    (K : Ideal (affineBaseRing B S hS T)) {T' : BigFppfOver B S hS}
    [IsAffine ((BigFppfOver.toScheme B S hS).obj T')] (ι : T' ⟶ T)
    [_root_.AlgebraicGeometry.IsClosedImmersion ((BigFppfOver.toScheme B S hS).map ι)]
    (hιK : K ≤ RingHom.ker ((BigFppfOver.toScheme B S hS).map ι).appTop.hom)
    (he1 : ∀ c, ((BigFppfOver.toScheme B S hS).map s).appTop (p c) -
      ((BigFppfOver.toScheme B S hS).map t).appTop (p c) ∈
        K.map ((BigFppfOver.toScheme B S hS).map (levelChartBase π (yoneda.map s ≫ w))).appTop.hom)
    (he2 : ∀ j, eval₂ (eval₂Hom ((BigFppfOver.toScheme B S hS).map (levelChartBase π w)).appTop.hom
      p) q (g j) ∈ K.map ((BigFppfOver.toScheme B S hS).map (levelChartBase π w)).appTop.hom)
    {j : T₀ ⟶ T'}
    (hjth : Stacks.Thickenings.IsThickening ((BigFppfOver.toScheme B S hS).map j))
    {x₀' : yoneda.obj O₀ ⟶ pullback π (yoneda.map ι)}
    (hx₀'s : IsSurjective B S hS x₀')
    (hx₀'f : x₀' ≫ pullback.fst π (yoneda.map ι) =
      e₀.inv ≫ pullback.fst π (yoneda.map k))
    {ι₀' : levelChart π w k ⟶ levelChart π w ι}
    (hsq₀' : IsPullback (yoneda.map ι₀') (yoneda.map c₀)
      (levelChartMap π w ι) x₀')
    (hι₀'f : ι₀' ≫ pullback.fst (levelChartBase π w) ι =
      pullback.fst (levelChartBase π w) k)
    (hUK₀ : IsAffineSpace B S hS
      (pullback (pullback.snd π (yoneda.map ι)) (yoneda.map j))) :
    IsAffineSpace B S hS (pullback π (yoneda.map ι)) := by
  classical
  have hUK := isAlgebraicSpace_pullback B S hS π (yoneda.map ι) hU
    (isAlgebraicSpace_yoneda B S hS _) (isAlgebraicSpace_yoneda B S hS T)
  have hwsK := (MorphismProperty.relative_isStableUnderBaseChange _).of_isPullback
    (isPullback_levelChart π w ι) hws
  have hweK := (MorphismProperty.relative_isStableUnderBaseChange _).of_isPullback
    (isPullback_levelChart π w ι) hwe
  have hRK := isPullback_levelKernel π w hR ι
  have hpres := preservesLimitsOfShape_walkingCospan_toScheme B S hS
  have hWKsch := (IsPullback.of_hasPullback (levelChartBase π w)
    ι).map (BigFppfOver.toScheme B S hS)
  have : IsAffine ((BigFppfOver.toScheme B S hS).obj
    (levelChart π w ι)) := .of_isPullback hWKsch
  have : _root_.AlgebraicGeometry.IsClosedImmersion ((BigFppfOver.toScheme B S hS).map k) := hk.1
  have : IsAffine ((BigFppfOver.toScheme B S hS).obj T₀) :=
    isAffine_of_isAffineHom ((BigFppfOver.toScheme B S hS).map k)
  -- the data at the level `T_K`
  obtain ⟨ρ, hρ⟩ : ∃ ρ, ρ = pullback.snd π (yoneda.map ι) := ⟨_, rfl⟩
  obtain ⟨wK, hwK⟩ : ∃ wK, wK = levelChartMap π w ι := ⟨_, rfl⟩
  obtain ⟨qK, hqK⟩ : ∃ qK, qK = ((BigFppfOver.toScheme B S hS).map
    ι).appTop.hom := ⟨_, rfl⟩
  have hqKker : K ≤ RingHom.ker qK := by rwa [hqK]
  obtain ⟨ρK, hρK⟩ : ∃ ρK, ρK = ((BigFppfOver.toScheme B S hS).map
    (pullback.fst (levelChartBase π w) ι)).appTop.hom := ⟨_, rfl⟩
  have hW₀sch := (IsPullback.of_hasPullback (levelChartBase π w) k).map
    (BigFppfOver.toScheme B S hS)
  have hρW : ∀ x, ((BigFppfOver.toScheme B S hS).map ι₀').appTop (ρK x) =
      ((BigFppfOver.toScheme B S hS).map (pullback.fst (levelChartBase π w) k)).appTop x := by
    intro x
    rw [hρK, ← hι₀'f, appTop_map_comp_apply]
  have hωK : levelChartBase ρ wK = pullback.snd (levelChartBase π w) ι :=
    yoneda.map_injective (by rw [yoneda_map_levelChartBase, hρ, hwK, levelChartMap_snd])
  have hcondK : ρK.comp ((BigFppfOver.toScheme B S hS).map (levelChartBase π w)).appTop.hom =
      ((BigFppfOver.toScheme B S hS).map (levelChartBase ρ wK)).appTop.hom.comp qK := by
    rw [hρK, hqK, hωK]
    exact appTop_comp_appTop_of_comp_eq B S hS pullback.condition
  -- the relations at the level
  obtain ⟨g', hg'def⟩ : ∃ g' : σ → MvPolynomial τ
      (MvPolynomial F (affineBaseRing B S hS T')),
      g' = fun j ↦ (g j).map (MvPolynomial.map qK) := ⟨_, rfl⟩
  have hbase₀ : levelChartBase ρ x₀' ≫ ι =
      levelChartBase π (e₀.inv ≫ pullback.fst π (yoneda.map k)) := by
    apply yoneda.map_injective
    rw [Functor.map_comp, yoneda_map_levelChartBase, yoneda_map_levelChartBase, Category.assoc, hρ,
      ← pullback.condition, ← Category.assoc, hx₀'f, Category.assoc]
  have hcoef : (coefSpecialization B S hS ρ x₀' coef).comp (MvPolynomial.map qK) =
      coefSpecialization B S hS π (e₀.inv ≫ pullback.fst π (yoneda.map k)) coef := by
    apply MvPolynomial.ringHom_ext
    · intro r
      simp only [RingHom.comp_apply, MvPolynomial.map_C, coefSpecialization, eval₂Hom_C]
      rw [← hbase₀, Functor.map_comp, Scheme.Hom.comp_appTop, CommRingCat.comp_apply, hqK]
    · intro c
      simp only [RingHom.comp_apply, MvPolynomial.map_X, coefSpecialization, eval₂Hom_X']
  have hrel' : ∀ j, (g' j).map (coefSpecialization B S hS ρ x₀' coef) = P₀.relation j := by
    intro j
    simp only [hg'def, MvPolynomial.map_map, hcoef]
    exact hrel j
  -- the coefficients at the level
  obtain ⟨θ, hθdef⟩ : ∃ θ : MvPolynomial F (affineBaseRing B S hS T') →+*
      Γ((BigFppfOver.toScheme B S hS).obj (levelChart π w ι), ⊤),
      θ = eval₂Hom ((BigFppfOver.toScheme B S hS).map (levelChartBase ρ wK)).appTop.hom
        (fun c ↦ ρK (p c)) := ⟨_, rfl⟩
  have hθA : θ.comp (algebraMap _ _) =
      ((BigFppfOver.toScheme B S hS).map (levelChartBase ρ wK)).appTop.hom := by
    ext x
    simp only [RingHom.comp_apply, MvPolynomial.algebraMap_eq, hθdef, coe_eval₂Hom, eval₂_C]
  obtain ⟨sK, hsK⟩ : ∃ sK, sK = levelKernelMap π w s rfl ι := ⟨_, rfl⟩
  obtain ⟨tK, htK⟩ : ∃ tK, tK = levelKernelMap π w t hR.w.symm ι :=
    ⟨_, rfl⟩
  have hRK' : IsPullback (yoneda.map sK) (yoneda.map tK) wK wK := by
    rwa [hsK, htK, hwK]
  have hst : sK ≫ levelChartBase ρ wK = tK ≫ levelChartBase ρ wK := by
    rw [← levelChartBase_comp, ← levelChartBase_comp, hRK'.w]
  have hfstR := (IsPullback.of_hasPullback (levelChartBase π (yoneda.map s ≫ w))
    ι).w
  have hsfst : ∀ x, ((BigFppfOver.toScheme B S hS).map sK).appTop (ρK x) =
      ((BigFppfOver.toScheme B S hS).map (pullback.fst (levelChartBase π (yoneda.map s ≫ w))
        ι)).appTop (((BigFppfOver.toScheme B S hS).map s).appTop x) := by
    intro x
    rw [hρK, hsK]
    exact appTop_levelKernelMap_fst B S hS π w _ _ ι x
  have htfst : ∀ x, ((BigFppfOver.toScheme B S hS).map tK).appTop (ρK x) =
      ((BigFppfOver.toScheme B S hS).map (pullback.fst (levelChartBase π (yoneda.map s ≫ w))
        ι)).appTop (((BigFppfOver.toScheme B S hS).map t).appTop x) := by
    intro x
    rw [hρK, htK]
    exact appTop_levelKernelMap_fst B S hS π w _ _ ι x
  have hθinv : ((BigFppfOver.toScheme B S hS).map sK).appTop.hom.comp θ =
      ((BigFppfOver.toScheme B S hS).map tK).appTop.hom.comp θ := by
    apply MvPolynomial.ringHom_ext
    · intro r
      simp only [RingHom.comp_apply, hθdef, eval₂Hom_C]
      rw [← appTop_map_comp_apply, ← appTop_map_comp_apply, hst]
    · intro c
      simp only [RingHom.comp_apply, hθdef, eval₂Hom_X']
      rw [hsfst, htfst, ← sub_eq_zero, ← map_sub]
      refine map_eq_zero_of_mem_map _ _ qK ((BigFppfOver.toScheme B S hS).map
        (pullback.snd (levelChartBase π (yoneda.map s ≫ w)) ι)).appTop.hom
        hqKker ?_ (he1 c)
      rw [hqK]
      exact appTop_comp_appTop_of_comp_eq B S hS hfstR
  have hbase' : ι₀' ≫ levelChartBase ρ wK = c₀ ≫ levelChartBase ρ x₀' :=
    comp_levelChartBase_eq_of_isPullback B S hS ρ (hwK ▸ hsq₀')
  have hθ₀ : ((BigFppfOver.toScheme B S hS).map ι₀').appTop.hom.comp θ =
      (algebraMap Γ((BigFppfOver.toScheme B S hS).obj O₀, ⊤)
        Γ((BigFppfOver.toScheme B S hS).obj (levelChart π w k), ⊤)).comp
        (coefSpecialization B S hS ρ x₀' coef) := by
    apply MvPolynomial.ringHom_ext
    · intro r
      simp only [RingHom.comp_apply, hθdef, eval₂Hom_C, coefSpecialization, hc₀]
      rw [← appTop_map_comp_apply, hbase', appTop_map_comp_apply]
    · intro c
      simp only [RingHom.comp_apply, hθdef, eval₂Hom_X', coefSpecialization, hc₀]
      rw [hρW, hp c]
  -- the roots at the level
  have hθt : θ.comp (MvPolynomial.map qK) =
      ρK.comp (eval₂Hom ((BigFppfOver.toScheme B S hS).map (levelChartBase π w)).appTop.hom p) := by
    apply MvPolynomial.ringHom_ext
    · intro r
      simp only [RingHom.comp_apply, MvPolynomial.map_C, hθdef, eval₂Hom_C]
      exact (congrArg (fun f ↦ f r) hcondK).symm
    · intro c
      simp only [RingHom.comp_apply, MvPolynomial.map_X, hθdef, eval₂Hom_X']
  have hv : ∀ j, eval₂ θ (fun i ↦ ρK (q i)) (g' j) = 0 := by
    intro j
    rw [hg'def, MvPolynomial.eval₂_map, hθt, ← MvPolynomial.hom_eval₂]
    exact map_eq_zero_of_mem_map _ _ qK _ hqKker hcondK (he2 j)
  -- the kernel of the restriction to the thin chart is nil
  have hsurjK : Function.Surjective ρK := by
    rw [hρK]
    exact surjective_appTop_of_isPullback_isClosedImmersion hWKsch
  have hsurj₀ : Function.Surjective ((BigFppfOver.toScheme B S hS).map ι₀').appTop.hom := by
    intro y
    obtain ⟨x, hx⟩ := surjective_appTop_of_isPullback_isClosedImmersion hW₀sch y
    exact ⟨ρK x, (hρW x).trans hx⟩
  have hInil : ∀ a ∈ RingHom.ker ((BigFppfOver.toScheme B S hS).map k).appTop.hom,
      IsNilpotent a := fun a ha ↦ hk.isNilpotent_of_mem_ker_appTop_of_compactSpace ha
  have hnil₀ : ∀ x ∈ RingHom.ker ((BigFppfOver.toScheme B S hS).map ι₀').appTop.hom,
      IsNilpotent x := by
    intro x hx
    obtain ⟨y, rfl⟩ := hsurjK x
    have hy : y ∈ RingHom.ker ((BigFppfOver.toScheme B S hS).map
        (pullback.fst (levelChartBase π w) k)).appTop.hom := by
      rw [RingHom.mem_ker, ← hρW]
      exact hx
    rw [ker_appTop_of_isPullback_isClosedImmersion hW₀sch] at hy
    have hle : (RingHom.ker ((BigFppfOver.toScheme B S hS).map k).appTop.hom).map
        ((BigFppfOver.toScheme B S hS).map (levelChartBase π w)).appTop.hom ≤ nilradical _ := by
      rw [Ideal.map_le_iff_le_comap]
      intro a ha
      exact (hInil a ha).map _
    exact (mem_nilradical.mp (hle hy)).map ρK
  obtain ⟨θ', hθ', hθ'₀⟩ := exists_liftOfRoots
    (E := Γ((BigFppfOver.toScheme B S hS).obj (levelChart π w ι), ⊤))
    P₀ g' (coefSpecialization B S hS ρ x₀' coef) hrel' θ
    ((BigFppfOver.toScheme B S hS).map ι₀').appTop.hom hsurj₀ hnil₀ hθ₀ (fun i ↦ ρK (q i)) hv
    (fun i ↦ (hρW (q i)).trans (hq i))
  subst hwK hρ
  obtain ⟨Z, ⟨eZ⟩⟩ := exists_iso_yoneda_of_presentationLift B S hS hUK
    (pullback.snd π (yoneda.map ι)) _ hwsK hweK hRK' x₀' hx₀'s ι₀'
    c₀ hsq₀' hc₀ P₀ hcard P₀.map P₀.map_inj rfl coef g' hrel' θ hθA hθinv hθ₀ θ' hθ' hθ'₀
  exact isAffineSpace_of_iso_yoneda_of_isThickening B S hS eZ _ j hjth hUK₀

/-- **The presentation step at a closed level of the base.**  If the lifts on the chart satisfy
the equations of the thin chart modulo `K`, then the base change of `U` to `T_K` is affine. -/
theorem isAffineSpace_pullback_quotientLevel_of_lifts {U : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u}
    (hU : IsAlgebraicSpace B S hS U) {T₀ T : BigFppfOver B S hS}
    [IsAffine ((BigFppfOver.toScheme B S hS).obj T)] (k : T₀ ⟶ T)
    (hk : Stacks.Thickenings.IsThickening ((BigFppfOver.toScheme B S hS).map k))
    (π : U ⟶ yoneda.obj T) {O₀ : BigFppfOver B S hS}
    [IsAffine ((BigFppfOver.toScheme B S hS).obj O₀)]
    (e₀ : pullback π (yoneda.map k) ≅ yoneda.obj O₀) {W R : BigFppfOver B S hS}
    [IsAffine ((BigFppfOver.toScheme B S hS).obj W)]
    [IsAffine ((BigFppfOver.toScheme B S hS).obj R)] (w : yoneda.obj W ⟶ U)
    (hws : (MorphismProperty.presheaf (MorphismProperty.inverseImage
      (@Surjective.{u} : MorphismProperty Scheme.{u}) (BigFppfOver.toScheme B S hS))) w)
    (hwe : (MorphismProperty.presheaf (MorphismProperty.inverseImage
      (@Etale.{u} : MorphismProperty Scheme.{u}) (BigFppfOver.toScheme B S hS))) w)
    {s t : R ⟶ W} (hR : IsPullback (yoneda.map s) (yoneda.map t) w w)
    (c₀ : levelChart π w k ⟶ O₀) (hc₀y : yoneda.map c₀ = levelChartMap π w k ≫ e₀.hom)
    (hsq₀ : IsPullback (yoneda.map (pullback.fst (levelChartBase π w) k)) (yoneda.map c₀) w
      (e₀.inv ≫ pullback.fst π (yoneda.map k)))
    [IsAffine ((BigFppfOver.toScheme B S hS).obj (levelChart π w k))]
    {τ σ : Type} [Finite τ] [Finite σ]
    [Algebra Γ((BigFppfOver.toScheme B S hS).obj O₀, ⊤)
      Γ((BigFppfOver.toScheme B S hS).obj (levelChart π w k), ⊤)]
    (hc₀ : algebraMap Γ((BigFppfOver.toScheme B S hS).obj O₀, ⊤)
      Γ((BigFppfOver.toScheme B S hS).obj (levelChart π w k), ⊤) =
      ((BigFppfOver.toScheme B S hS).map c₀).appTop.hom)
    (P₀ : Algebra.SubmersivePresentation Γ((BigFppfOver.toScheme B S hS).obj O₀, ⊤)
      Γ((BigFppfOver.toScheme B S hS).obj (levelChart π w k), ⊤) τ σ)
    (hcard : Nat.card τ = Nat.card σ) {F : Type} [Finite F]
    (coef : F → Γ((BigFppfOver.toScheme B S hS).obj O₀, ⊤))
    (g : σ → MvPolynomial τ (MvPolynomial F (affineBaseRing B S hS T)))
    (hrel : ∀ j, (g j).map (coefSpecialization B S hS π
      (e₀.inv ≫ pullback.fst π (yoneda.map k)) coef) = P₀.relation j)
    (p : F → Γ((BigFppfOver.toScheme B S hS).obj W, ⊤))
    (hp : ∀ c, ((BigFppfOver.toScheme B S hS).map (pullback.fst (levelChartBase π w) k)).appTop
      (p c) = ((BigFppfOver.toScheme B S hS).map c₀).appTop (coef c))
    (q : τ → Γ((BigFppfOver.toScheme B S hS).obj W, ⊤))
    (hq : ∀ i, ((BigFppfOver.toScheme B S hS).map (pullback.fst (levelChartBase π w) k)).appTop
      (q i) = P₀.val i)
    (K : Ideal (affineBaseRing B S hS T))
    (hKI : K ≤ RingHom.ker ((BigFppfOver.toScheme B S hS).map k).appTop.hom)
    (he1 : ∀ c, ((BigFppfOver.toScheme B S hS).map s).appTop (p c) -
      ((BigFppfOver.toScheme B S hS).map t).appTop (p c) ∈
        K.map ((BigFppfOver.toScheme B S hS).map (levelChartBase π (yoneda.map s ≫ w))).appTop.hom)
    (he2 : ∀ j, eval₂ (eval₂Hom ((BigFppfOver.toScheme B S hS).map (levelChartBase π w)).appTop.hom
      p) q (g j) ∈ K.map ((BigFppfOver.toScheme B S hS).map (levelChartBase π w)).appTop.hom) :
    IsAffineSpace B S hS (pullback π (yoneda.map (quotientLevelι B S hS T K))) := by
  classical
  obtain ⟨j, hj⟩ := exists_factor_quotientLevelι B S hS T K k hKI
  obtain ⟨x₀', ι₀', hx₀', hsq₀', hx₀'f, hι₀'f, hι₀'s⟩ :=
    thin_level B S hS hj e₀ w c₀ hc₀y hsq₀
  have hUK := isAlgebraicSpace_pullback B S hS π (yoneda.map (quotientLevelι B S hS T K)) hU
    (isAlgebraicSpace_yoneda B S hS _) (isAlgebraicSpace_yoneda B S hS T)
  have hpres := preservesLimitsOfShape_walkingCospan_toScheme B S hS
  have hWKsch := (IsPullback.of_hasPullback (levelChartBase π w)
    (quotientLevelι B S hS T K)).map (BigFppfOver.toScheme B S hS)
  have : IsAffine ((BigFppfOver.toScheme B S hS).obj
    (levelChart π w (quotientLevelι B S hS T K))) := .of_isPullback hWKsch
  -- the factor `j` is a thickening
  have hkci : _root_.AlgebraicGeometry.IsClosedImmersion ((BigFppfOver.toScheme B S hS).map k) :=
    hk.1
  have : IsAffine ((BigFppfOver.toScheme B S hS).obj T₀) :=
    isAffine_of_isAffineHom ((BigFppfOver.toScheme B S hS).map k)
  have hjci : _root_.AlgebraicGeometry.IsClosedImmersion ((BigFppfOver.toScheme B S hS).map j) := by
    have : _root_.AlgebraicGeometry.IsClosedImmersion ((BigFppfOver.toScheme B S hS).map j ≫
        (BigFppfOver.toScheme B S hS).map (quotientLevelι B S hS T K)) := by
      rwa [← Functor.map_comp, hj]
    exact IsClosedImmersion.of_comp_isClosedImmersion _
      ((BigFppfOver.toScheme B S hS).map (quotientLevelι B S hS T K))
  have hjsurj : Function.Surjective ((BigFppfOver.toScheme B S hS).map j) := by
    intro y
    obtain ⟨x, hx⟩ := hk.2 ((BigFppfOver.toScheme B S hS).map (quotientLevelι B S hS T K) y)
    have hinj := ((BigFppfOver.toScheme B S hS).map (quotientLevelι B S hS T K)).isClosedEmbedding
    refine ⟨x, hinj.injective ?_⟩
    rw [← Scheme.Hom.comp_apply, ← Functor.map_comp, hj, hx]
  have hjth : Stacks.Thickenings.IsThickening ((BigFppfOver.toScheme B S hS).map j) :=
    ⟨hjci, hjsurj⟩
  -- the thin point at the level is surjective
  have hx₀'s : IsSurjective B S hS x₀' := by
    have sq : IsPullback (P := (⟨_, isAlgebraicSpace_yoneda B S hS O₀⟩ : AlgebraicSpaces B S hS))
        (X := (⟨_, isAlgebraicSpace_yoneda B S hS T₀⟩ : AlgebraicSpaces B S hS))
        (Y := (⟨_, hUK⟩ : AlgebraicSpaces B S hS))
        (Z := (⟨_, isAlgebraicSpace_yoneda B S hS _⟩ : AlgebraicSpaces B S hS))
        (ObjectProperty.homMk (e₀.inv ≫ pullback.snd π (yoneda.map k)))
        (ObjectProperty.homMk x₀') (ObjectProperty.homMk (yoneda.map j))
        (ObjectProperty.homMk (pullback.snd π (yoneda.map (quotientLevelι B S hS T K)))) :=
      IsPullback.of_map_of_faithful (ObjectProperty.ι _) hx₀'.flip
    exact isSurjective_of_isPullback B S hS sq (isSurjective_yoneda_map B S hS j ⟨hjsurj⟩)
  have hUK₀ : IsAffineSpace B S hS
      (pullback (pullback.snd π (yoneda.map (quotientLevelι B S hS T K))) (yoneda.map j)) :=
    ⟨O₀, inferInstance, ⟨hx₀'.isoPullback.symm⟩⟩
  have : IsAffine ((BigFppfOver.toScheme B S hS).obj (quotientLevel B S hS T K)) :=
    isAffine_of_isAffineHom ((BigFppfOver.toScheme B S hS).map (quotientLevelι B S hS T K))
  exact isAffineSpace_pullback_quotientLevel_of_lifts_aux B S hS hU k hk π e₀ w hws hwe hR c₀
    hc₀ P₀ hcard coef g hrel p hp q hq K (quotientLevelι B S hS T K)
    (ker_appTop_quotientLevelι B S hS T K).ge he1 he2 hjth hx₀'s hx₀'f hsq₀' hι₀'f hUK₀

/-- **Stacks 07SQ along the finitely generated ideals of a thickening of an affine base.**  An
algebraic space over an affine object `T` of the site whose base change to a thickening `T₀` of
`T` is affine has an affine base change to a finite-order thickening of `T` through which
`T₀ ⟶ T` factors. -/
theorem exists_isFiniteOrderThickening_isAffineSpace_pullback
    {U : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u} (hU : IsAlgebraicSpace B S hS U)
    {T₀ T : BigFppfOver B S hS} [IsAffine ((BigFppfOver.toScheme B S hS).obj T)] (k : T₀ ⟶ T)
    (hk : Stacks.Thickenings.IsThickening ((BigFppfOver.toScheme B S hS).map k))
    (π : U ⟶ yoneda.obj T) (hU₀ : IsAffineSpace B S hS (pullback π (yoneda.map k))) :
    ∃ (T' : BigFppfOver B S hS) (ι : T' ⟶ T),
      Stacks.Thickenings.IsFiniteOrderThickening ((BigFppfOver.toScheme B S hS).map ι) ∧
      IsAffineSpace B S hS (pullback π (yoneda.map ι)) := by
  classical
  have : _root_.AlgebraicGeometry.IsClosedImmersion ((BigFppfOver.toScheme B S hS).map k) := hk.1
  have : IsAffine ((BigFppfOver.toScheme B S hS).obj T₀) :=
    isAffine_of_isAffineHom ((BigFppfOver.toScheme B S hS).map k)
  have hpres := preservesLimitsOfShape_walkingCospan_toScheme B S hS
  have hU₀alg := hU₀.isAlgebraicSpace
  have hfst := isSurjective_pullback_fst_yoneda B S hS hU k ⟨hk.2⟩ π
  have hqc : IsQuasiCompactSpace B S hS U :=
    IsQuasiCompactSpace.of_isSurjective B S hS hU₀alg hU hfst hU₀.isQuasiCompactSpace
  obtain ⟨W, w, hWaff, hws, hwe'⟩ :=
    (isQuasiCompactSpace_iff_exists_affine_etale_surjective_cover B S hS U hU).mp hqc
  have hwe := (isEtale_iff_presheaf_of_yoneda B S hS w).1 hwe'
  have hR := hws.rep.isPullback' w
  set s := hws.rep.fst' w
  set t := hws.rep.snd w
  have hU₀' := hU₀
  obtain ⟨O₀, hO₀, ⟨e₀⟩⟩ := hU₀'
  have : IsAffine ((BigFppfOver.toScheme B S hS).obj O₀) := hO₀
  have : IsAffine ((BigFppfOver.toScheme B S hS).obj W) := hWaff
  -- the thin point and the thin chart over `T₀`
  set x₀ : yoneda.obj O₀ ⟶ U := e₀.inv ≫ pullback.fst π (yoneda.map k)
  set W₀ := levelChart π w k
  set ι₀ : W₀ ⟶ W := pullback.fst (levelChartBase π w) k
  set c₀ : W₀ ⟶ O₀ := yoneda.preimage (levelChartMap π w k ≫ e₀.hom)
  have hc₀y : yoneda.map c₀ = levelChartMap π w k ≫ e₀.hom := Functor.map_preimage _ _
  have hsq₀ : IsPullback (yoneda.map ι₀) (yoneda.map c₀) w x₀ := by
    refine (isPullback_levelChart π w k).of_iso (Iso.refl _) (Iso.refl _) e₀ (Iso.refl _)
      (by simp only [Iso.refl_hom, Category.comp_id, Category.id_comp]; rfl)
      (by simp [hc₀y]) (by simp) (by simp [x₀])
  have hW₀sch := (IsPullback.of_hasPullback (levelChartBase π w) k).map
    (BigFppfOver.toScheme B S hS)
  have : IsAffine ((BigFppfOver.toScheme B S hS).obj W₀) := .of_isPullback hW₀sch
  -- the kernel pair of the chart is affine
  set R₀ := levelChart π (yoneda.map s ≫ w) k
  have hR₀y : IsPullback (yoneda.map (levelKernelMap π w s rfl k))
      (yoneda.map (levelKernelMap π w t hR.w.symm k)) (yoneda.map c₀) (yoneda.map c₀) := by
    refine (isPullback_levelKernel π w hR k).of_iso (Iso.refl _) (Iso.refl _) (Iso.refl _) e₀
      (by simp) (by simp) (by simp [hc₀y]) (by simp [hc₀y])
  let : PreservesLimitsOfShape WalkingCospan (BigFppfOver.forget B S hS) := inferInstance
  let : PreservesLimitsOfShape WalkingCospan B.inclusion := inferInstance
  let : PreservesLimitsOfShape WalkingCospan (BigFppfOver.toScheme B S hS) :=
    comp_preservesLimitsOfShape _ _
  have : PreservesLimit (cospan c₀ c₀) (BigFppfOver.toScheme B S hS) :=
    PreservesLimitsOfShape.preservesLimit
  have hR₀sch := (IsPullback.of_map_of_faithful yoneda hR₀y).map (BigFppfOver.toScheme B S hS)
  have : IsAffine ((BigFppfOver.toScheme B S hS).obj R₀) := .of_isPullback hR₀sch
  have hR₀T := (IsPullback.of_hasPullback (levelChartBase π (yoneda.map s ≫ w)) k).map
    (BigFppfOver.toScheme B S hS)
  have hRthick : Stacks.Thickenings.IsThickening ((BigFppfOver.toScheme B S hS).map
      (pullback.fst (levelChartBase π (yoneda.map s ≫ w)) k)) := by
    have hsu : Surjective ((BigFppfOver.toScheme B S hS).map k) := ⟨hk.2⟩
    exact ⟨MorphismProperty.of_isPullback hR₀T.flip inferInstance,
      (MorphismProperty.of_isPullback (P := @Surjective) hR₀T.flip hsu).surj⟩
  have : IsAffine ((BigFppfOver.toScheme B S hS).obj (hws.rep.pullback w)) :=
    Stacks.Thickenings.isAffine_of_isThickening hRthick
  -- the presentation of the thin chart
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
  -- lifts on the chart
  set ω := levelChartBase π w
  set ρW := ((BigFppfOver.toScheme B S hS).map ι₀).appTop.hom
  have hρWsurj : Function.Surjective ρW := surjective_appTop_of_isPullback_isClosedImmersion hW₀sch
  have hρWker := ker_appTop_of_isPullback_isClosedImmersion hW₀sch
  choose p hp using fun c : F ↦ hρWsurj (((BigFppfOver.toScheme B S hS).map c₀).appTop (coef c))
  choose q hq using fun i : τ ↦ hρWsurj (P₀.val i)
  set θt : MvPolynomial F (affineBaseRing B S hS T) →+* Γ((BigFppfOver.toScheme B S hS).obj W, ⊤) :=
    eval₂Hom ((BigFppfOver.toScheme B S hS).map ω).appTop.hom p
  have hbase : ι₀ ≫ ω = c₀ ≫ levelChartBase π x₀ :=
    comp_levelChartBase_eq_of_isPullback B S hS π hsq₀
  have hρθt : ρW.comp θt = (algebraMap Γ((BigFppfOver.toScheme B S hS).obj O₀, ⊤)
        Γ((BigFppfOver.toScheme B S hS).obj W₀, ⊤)).comp (coefSpecialization B S hS π x₀ coef) := by
    apply MvPolynomial.ringHom_ext
    · intro r
      simp only [RingHom.comp_apply, θt, eval₂Hom_C, coefSpecialization,
        RingHom.algebraMap_toAlgebra, ρW]
      rw [← appTop_map_comp_apply, hbase, appTop_map_comp_apply]
    · intro c
      simp only [RingHom.comp_apply, θt, eval₂Hom_X', coefSpecialization,
        RingHom.algebraMap_toAlgebra]
      exact hp c
  -- the equations over `T₀`
  obtain ⟨I, hI⟩ : ∃ I, I = RingHom.ker ((BigFppfOver.toScheme B S hS).map k).appTop.hom :=
    ⟨_, rfl⟩
  obtain ⟨ωR, hωR⟩ : ∃ ωR, ωR = levelChartBase π (yoneda.map s ≫ w) := ⟨_, rfl⟩
  obtain ⟨ρR, hρR⟩ : ∃ ρR, ρR = ((BigFppfOver.toScheme B S hS).map
    (pullback.fst (levelChartBase π (yoneda.map s ≫ w)) k)).appTop.hom := ⟨_, rfl⟩
  have hρRker : RingHom.ker ρR = I.map ((BigFppfOver.toScheme B S hS).map ωR).appTop.hom := by
    rw [hρR, hI, hωR]
    exact ker_appTop_of_isPullback_isClosedImmersion hR₀T
  have hρRs : ∀ x, ρR (((BigFppfOver.toScheme B S hS).map s).appTop x) =
      ((BigFppfOver.toScheme B S hS).map (levelKernelMap π w s rfl k)).appTop (ρW x) := by
    intro x
    rw [hρR]
    exact (appTop_levelKernelMap_fst B S hS π w s rfl k x).symm
  have hρRt : ∀ x, ρR (((BigFppfOver.toScheme B S hS).map t).appTop x) =
      ((BigFppfOver.toScheme B S hS).map (levelKernelMap π w t hR.w.symm k)).appTop (ρW x) := by
    intro x
    rw [hρR]
    exact (appTop_levelKernelMap_fst B S hS π w t hR.w.symm k x).symm
  have hst₀ : levelKernelMap π w s rfl k ≫ c₀ = levelKernelMap π w t hR.w.symm k ≫ c₀ :=
    yoneda.map_injective (by rw [Functor.map_comp, Functor.map_comp, hR₀y.w])
  have he1' : ∀ c, ρR (((BigFppfOver.toScheme B S hS).map s).appTop (p c) -
      ((BigFppfOver.toScheme B S hS).map t).appTop (p c)) = 0 := by
    intro c
    have hs' := hρRs (p c)
    have ht' := hρRt (p c)
    rw [hp c] at hs' ht'
    have hc : ((BigFppfOver.toScheme B S hS).map (levelKernelMap π w s rfl k)).appTop
        (((BigFppfOver.toScheme B S hS).map c₀).appTop (coef c)) =
        ((BigFppfOver.toScheme B S hS).map (levelKernelMap π w t hR.w.symm k)).appTop
        (((BigFppfOver.toScheme B S hS).map c₀).appTop (coef c)) := by
      have h := congrArg (fun f ↦ ((BigFppfOver.toScheme B S hS).map f).appTop (coef c)) hst₀
      simpa only [Functor.map_comp, Scheme.Hom.comp_appTop, CommRingCat.comp_apply] using h
    exact (map_sub ρR _ _).trans (sub_eq_zero.mpr (hs'.trans (hc.trans ht'.symm)))
  have he1 : ∀ c, ((BigFppfOver.toScheme B S hS).map s).appTop (p c) -
      ((BigFppfOver.toScheme B S hS).map t).appTop (p c) ∈ I.map
        ((BigFppfOver.toScheme B S hS).map ωR).appTop.hom := fun c ↦
    hρRker ▸ RingHom.mem_ker.mpr (he1' c)
  have he2 : ∀ j, eval₂ θt q (g j) ∈ I.map ((BigFppfOver.toScheme B S hS).map ω).appTop.hom := by
    intro j
    rw [hI]
    refine hρWker ▸ RingHom.mem_ker.mpr ?_
    change ρW (eval₂ θt q (g j)) = 0
    rw [MvPolynomial.hom_eval₂, hρθt]
    have hq' : (fun i ↦ ρW (q i)) = P₀.val := funext hq
    rw [hq', ← MvPolynomial.eval₂_map, show MvPolynomial.map
      (coefSpecialization B S hS π x₀ coef) (g j) = P₀.relation j from hrel j, ← aeval_def]
    exact P₀.aeval_val_relation j
  -- a finitely generated ideal carrying the equations
  rw [hωR] at he1
  choose K₁ hK₁fg hK₁I hK₁ using fun c ↦ exists_fg_le_of_mem_map _ (he1 c)
  choose K₂ hK₂fg hK₂I hK₂ using fun j ↦ exists_fg_le_of_mem_map _ (he2 j)
  obtain ⟨K, hK⟩ : ∃ K : Ideal (affineBaseRing B S hS T), K = (⨆ c, K₁ c) ⊔ ⨆ j, K₂ j :=
    ⟨_, rfl⟩
  have hKfg : K.FG := hK ▸ (Submodule.fg_iSup _ hK₁fg).sup (Submodule.fg_iSup _ hK₂fg)
  have hKI : K ≤ I := hK ▸ sup_le (iSup_le hK₁I) (iSup_le hK₂I)
  have he1K : ∀ c, ((BigFppfOver.toScheme B S hS).map s).appTop (p c) -
      ((BigFppfOver.toScheme B S hS).map t).appTop (p c) ∈ K.map
        ((BigFppfOver.toScheme B S hS).map (levelChartBase π (yoneda.map s ≫ w))).appTop.hom :=
    fun c ↦ Ideal.map_mono (hK ▸ (le_iSup K₁ c).trans le_sup_left) (hK₁ c)
  have he2K : ∀ j, eval₂ θt q (g j) ∈
      K.map ((BigFppfOver.toScheme B S hS).map (levelChartBase π w)).appTop.hom :=
    fun j ↦ Ideal.map_mono (hK ▸ (le_iSup K₂ j).trans le_sup_right) (hK₂ j)
  -- the ideal is nilpotent
  have hKnil : K ≤ nilradical _ := fun a ha ↦ mem_nilradical.mpr
    (hk.isNilpotent_of_mem_ker_appTop_of_compactSpace (hI ▸ hKI ha))
  obtain ⟨n, hn⟩ := hKfg.isNilpotent_iff_le_nilradical.mpr hKnil
  have hn' : K ^ (n + 1) = ⊥ := by rw [pow_succ, hn, zero_mul]; rfl
  rw [hI] at hKI
  exact ⟨quotientLevel B S hS T K, quotientLevelι B S hS T K,
    isFiniteOrderThickening_quotientLevelι B S hS T K n hn',
    isAffineSpace_pullback_quotientLevel_of_lifts B S hS hU k hk π e₀ w hws hwe hR c₀ hc₀y hsq₀ rfl
      P₀ hcard coef g hrel p hp q hq K hKI he1K he2K⟩

end AlgebraicGeometry.Space

end
