module

public import StacksCore.Tactic.StacksAttribute
public import StacksFrontier.AlgebraicGeometry.Groupoids.FiniteFlatAffine.CoproductDecomposition
public import StacksFrontier.AlgebraicGeometry.Picard.HilbertFunctorDisjointUnion
public import StacksFrontier.AlgebraicGeometry.Spaces.EtaleIdealPullbackSections
public import StacksFrontier.AlgebraicGeometry.Spaces.IdealSmulOfAffineCharts
public import StacksFrontier.AlgebraicGeometry.Spaces.FittingIdealChain
public import StacksFrontier.AlgebraicGeometry.Spaces.FinitePushforwardQuasicoherent
public import StacksFrontier.AlgebraicGeometry.Spaces.FinitePushforwardFiniteType
public import StacksFrontier.AlgebraicGeometry.Spaces.MorphismKernelIdeal
public import StacksFrontier.AlgebraicGeometry.Spaces.KernelIdealAffineChartFiniteType
public import StacksFrontier.AlgebraicGeometry.Spaces.LocallyPrincipalComplement
public import StacksFrontier.AlgebraicGeometry.Spaces.EtaleCharts
public import StacksFrontier.AlgebraicGeometry.Spaces.AffineAtlas
public import StacksFrontier.AlgebraicGeometry.Spaces.PointsBaseChange
public import StacksFrontier.AlgebraicGeometry.Spaces.OpenSubspaceCorrespondence
public import StacksFrontier.RingTheory.Fitting.Basic

/-!
# The Fitting ideal of a direct image along a clopen splitting of an étale base change

Let `φ : W ⟶ X` be an étale representable morphism and `τ : Z ⟶ X` a finite morphism of
algebraic spaces over a scheme `S`, and suppose that the fibre product `P = W ×_X Z` is split
by a set `T` of points which is open and closed into the two complementary open and closed
subspaces `P_T` and `P_{T^c}`.  This file computes the inverse image along `φ` of the zeroth
Fitting ideal of the direct image `τ_* 𝒪_Z`: when `P_T ⟶ W` is a closed immersion with ideal
`𝓘` and `P_{T^c} ⟶ W` is finite,

`φ⁻¹ Fit_0(τ_* 𝒪_Z) · 𝒪_W = 𝓘 · Fit_0((P_{T^c} ⟶ W)_* 𝒪)`.

This is the computation which ends the proof of Stacks 087B.

## Main results

* `fittingIdeal_zero_eq_mul_of_linearEquiv`: for a finite module `M ≅ (C ⧸ I) × N`,
  `Fit_0(M) = I · Fit_0(N)`.
* `AlgebraicGeometry.Space.pullbackIdealSubsheaf_fittingIdeal_eq_idealSmul`: the displayed
  identity.

## Implementation notes

Both sides are sheaves of ideals of `𝒪_W`, so by
`AlgebraicGeometry.Space.eq_idealSmul_of_forall_isAffine` it suffices to compare their sections
over an affine étale chart `V` of `W`.  There the inverse-image ideal has the sections of
`Fit_0(τ_* 𝒪_Z)` over the composite chart `V ⟶ W ⟶ X`
(`AlgebraicGeometry.Space.pullbackIdealSubsheaf_eq_etaleIdealRestrict`), which are the Fitting
ideal of the module `Γ(V ×_X Z)` of sections of `τ_* 𝒪_Z` there.  The two pieces of `P` pull
back to two open subschemes of `V ×_X Z = V ×_W P` with complementary images, so that
`Γ(V ×_X Z) = Γ(V ×_W P_T) × Γ(V ×_W P_{T^c})`, and the first factor is `Γ(V) ⧸ 𝓘(V)` because
`V ×_W P_T ⟶ V` is a closed immersion with ideal `𝓘(V)`.  The product formula and the quotient
formula of Stacks 07ZA finish the computation.

## References

* [Stacks Project, Tag 087B](https://stacks.math.columbia.edu/tag/087B)
* [Stacks Project, Tag 07ZA](https://stacks.math.columbia.edu/tag/07ZA)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits Opposite AlgebraicGeometry

universe u

/-! ### The Fitting ideal of a module split off a quotient of the ring -/

/-- **The zeroth Fitting ideal of a module split off a cyclic module.**  For finite modules
`M ≅ (C ⧸ I) × N` over a commutative ring `C`, `Fit_0(M) = I · Fit_0(N)`, by the product and
quotient formulas of Stacks 07ZA. -/
theorem fittingIdeal_zero_eq_mul_of_linearEquiv {C : Type u} [CommRing C]
    {M N : Type u} [AddCommGroup M] [Module C M] [Module.Finite C M]
    [AddCommGroup N] [Module C N] [Module.Finite C N] (I : Ideal C)
    (e : M ≃ₗ[C] (C ⧸ I) × N) :
    fittingIdeal (R := C) (M := M) 0 = I * fittingIdeal (R := C) (M := N) 0 := by
  have h := fittingIdeal_eq_of_linearEquiv e 0
  simp only [Nat.cast_zero] at h
  rw [h, ((fittingIdeal_basic_properties.{u, u, u, u} (R := C) (M := C ⧸ I)).2.1 N).1,
    (fittingIdeal_basic_properties.{u, u, u, u} (R := C) (M := C ⧸ I)).2.2.2.2.2.2.2 I]

/-! ### The Fitting ideal of global functions on a disjoint union -/

/-- **The zeroth Fitting ideal of the global functions on a disjoint union over an affine
scheme.**  Let `A ⟶ V` be a morphism to an affine scheme and let `A` be the disjoint union of
two open subschemes `A₁` and `A₂`, where `A₁ ⟶ V` is a closed immersion.  Then, as modules over
`Γ(V)`, `Fit_0(Γ(A)) = Ker(Γ(V) ⟶ Γ(A₁)) · Fit_0(Γ(A₂))`. -/
theorem AlgebraicGeometry.fittingIdeal_zero_appTop_eq_ker_mul {V A A₁ A₂ : Scheme.{u}}
    [IsAffine V] (s : A ⟶ V) (s₁ : A₁ ⟶ V) (s₂ : A₂ ⟶ V) (i₁ : A₁ ⟶ A) (i₂ : A₂ ⟶ A)
    [IsOpenImmersion i₁] [IsOpenImmersion i₂] (h : IsCompl i₁.opensRange i₂.opensRange)
    (h₁ : i₁ ≫ s = s₁) (h₂ : i₂ ≫ s = s₂) [IsClosedImmersion s₁] :
    letI := s.appTop.hom.toModule
    letI := s₂.appTop.hom.toModule
    ∀ [Module.Finite Γ(V, ⊤) Γ(A, ⊤)] [Module.Finite Γ(V, ⊤) Γ(A₂, ⊤)],
      fittingIdeal (R := Γ(V, ⊤)) (M := Γ(A, ⊤)) 0 =
        RingHom.ker s₁.appTop.hom * fittingIdeal (R := Γ(V, ⊤)) (M := Γ(A₂, ⊤)) 0 := by
  let := s.appTop.hom.toModule
  let := s₂.appTop.hom.toModule
  intro _ _
  have hsurj : Function.Surjective s₁.appTop :=
    (IsClosedImmersion.isAffine_surjective_of_isAffine s₁).2
  let q : Γ(A₁, ⊤) ≃+* Γ(V, ⊤) ⧸ RingHom.ker s₁.appTop.hom :=
    (RingHom.quotientKerEquivOfSurjective hsurj).symm
  let ψ : Γ(A, ⊤) →ₗ[Γ(V, ⊤)] (Γ(V, ⊤) ⧸ RingHom.ker s₁.appTop.hom) × Γ(A₂, ⊤) :=
    { toFun := fun x => (q (i₁.appTop x), i₂.appTop x)
      map_add' := fun x y => by simp
      map_smul' := fun c x => by
        show (q (i₁.appTop (s.appTop c * x)), i₂.appTop (s.appTop c * x)) =
          (c • q (i₁.appTop x), s₂.appTop c * i₂.appTop x)
        have e : ∀ {A' : Scheme.{u}} (i : A' ⟶ A) (s' : A' ⟶ V), i ≫ s = s' →
            i.appTop (s.appTop c) = s'.appTop c := fun i s' h => by
          rw [← h, Scheme.Hom.comp_appTop]
          rfl
        simp only [map_mul, e i₁ s₁ h₁, e i₂ s₂ h₂]
        refine Prod.ext ?_ rfl
        show q (s₁.appTop c) * q (i₁.appTop x) = _
        rw [Algebra.smul_def]
        congr 1
        exact (RingHom.quotientKerEquivOfSurjective hsurj).symm_apply_apply c }
  have hψ : Function.Bijective ψ := by
    have : (ψ : Γ(A, ⊤) → _) =
        (Prod.map q id) ∘ (RingHom.prod i₁.appTop.hom i₂.appTop.hom) := rfl
    rw [this]
    exact (Function.Bijective.prodMap q.bijective Function.bijective_id).comp
      (Stacks.Hilbert.bijective_prod_appTop_of_isCompl i₁ i₂ h)
  exact fittingIdeal_zero_eq_mul_of_linearEquiv _ (LinearEquiv.ofBijective ψ hψ)

namespace AlgebraicGeometry.Space

attribute [local instance] pointTopology

variable {B : BigFppfSite.{u}} {S : Scheme.{u}} {hS : B.Contains S}

/-- Pullbacks of presheaves on `BigFppfOver B S hS`, given directly: instance search for them
times out under Lean v4.35.0. -/
local instance (priority := high) hasPullbacks_presheaf_FittingIdealEtaleClopenSplitting :
    HasPullbacks ((BigFppfOver B S hS)ᵒᵖ ⥤ Type u) :=
  Limits.functorCategoryHasLimitsOfShape

local instance (priority := high) hasPullback_presheaf_FittingIdealEtaleClopenSplitting
    {X Y Z : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u} (f : X ⟶ Z) (g : Y ⟶ Z) :
    HasLimit (cospan f g) :=
  hasPullbacks_presheaf_FittingIdealEtaleClopenSplitting.has_limit _

/-! ### The pieces of the fibre product -/

section Pieces

variable {X W Z : AlgebraicSpaces B S hS} (φ : W ⟶ X) (τ : Z ⟶ X)

/-- The fibre product `W ×_X Z` of two morphisms of algebraic spaces is an algebraic space. -/
theorem isAlgebraicSpace_pullback_hom :
    IsAlgebraicSpace B S hS (pullback φ.hom τ.hom) :=
  isAlgebraicSpace_pullback B S hS φ.hom τ.hom W.2 Z.2 X.2

/-- The open subspace of `W ×_X Z` cut out by an open set `T` of its points, as an algebraic
space. -/
abbrev fibrePiece (T : Set (points B S hS (pullback φ.hom τ.hom))) (hT : IsOpen T) :
    AlgebraicSpaces B S hS :=
  ⟨(openSubspaceOfPoints B S hS _ T).toFunctor,
    (isOpenSubspace_openSubspaceOfPoints B S hS (isAlgebraicSpace_pullback_hom φ τ) T hT).1⟩

/-- The projection to `W` of the open subspace of `W ×_X Z` cut out by an open set of points. -/
abbrev fibrePieceHom (T : Set (points B S hS (pullback φ.hom τ.hom))) (hT : IsOpen T) :
    fibrePiece φ τ T hT ⟶ W :=
  ObjectProperty.homMk ((openSubspaceOfPoints B S hS _ T).ι ≫ pullback.fst φ.hom τ.hom)

end Pieces

/-! ### The pieces over an étale chart -/

section Chart

variable {X W Z : AlgebraicSpaces B S hS} (φ : W ⟶ X)
  (τ : Z ⟶ X) (hτ : yoneda.relativelyRepresentable τ.hom)
  (V : SmallEtale B S hS W.1)

/-- Over an étale chart `V` of `W`, the canonical morphism from the chart `V ×_X Z` of `Z` to the
fibre product `W ×_X Z`. -/
noncomputable def chartToFibre :
    yoneda.obj (hτ.pullback (V.1.hom ≫ φ.hom)) ⟶ pullback φ.hom τ.hom :=
  pullback.lift (yoneda.map (hτ.snd (V.1.hom ≫ φ.hom)) ≫ V.1.hom)
    (hτ.fst (V.1.hom ≫ φ.hom)) (by rw [hτ.w, Category.assoc])

/-- The composite of `chartToFibre` with the first projection to `W` is the composite of the
projection `V ×_X Z ⟶ V` with `V ⟶ W`. -/
@[reassoc (attr := simp)]
theorem chartToFibre_fst :
    chartToFibre φ τ hτ V ≫ pullback.fst φ.hom τ.hom =
      yoneda.map (hτ.snd (V.1.hom ≫ φ.hom)) ≫ V.1.hom :=
  pullback.lift_fst _ _ _

/-- The composite of `chartToFibre` with the second projection to `Z` is the projection
`V ×_X Z ⟶ Z`. -/
@[reassoc (attr := simp)]
theorem chartToFibre_snd :
    chartToFibre φ τ hτ V ≫ pullback.snd φ.hom τ.hom = hτ.fst (V.1.hom ≫ φ.hom) :=
  pullback.lift_snd _ _ _

/-- The chart `V ×_X Z` is the base change of `W ×_X Z ⟶ W` along `V ⟶ W`. -/
theorem isPullback_chartToFibre :
    IsPullback (chartToFibre φ τ hτ V) (yoneda.map (hτ.snd (V.1.hom ≫ φ.hom)))
      (pullback.fst φ.hom τ.hom) V.1.hom := by
  refine IsPullback.of_right (h₁₂ := pullback.snd φ.hom τ.hom) (v₁₃ := τ.hom)
    (h₂₂ := φ.hom) ?_ (chartToFibre_fst φ τ hτ V) (IsPullback.of_hasPullback φ.hom τ.hom).flip
  rw [chartToFibre_snd]
  exact hτ.isPullback (V.1.hom ≫ φ.hom)

variable (T : Set (points B S hS (pullback φ.hom τ.hom))) (hT : IsOpen T)
  (hk : yoneda.relativelyRepresentable (fibrePieceHom φ τ T hT).hom)

/-- Over an étale chart `V` of `W`, the morphism from the chart `V ×_W P_T` of the piece `P_T` of
`W ×_X Z` cut out by `T` to the chart `V ×_X Z` of `Z`. -/
noncomputable def pieceToChart :
    hk.pullback V.1.hom ⟶ hτ.pullback (V.1.hom ≫ φ.hom) :=
  hτ.lift (hk.fst V.1.hom ≫ (openSubspaceOfPoints B S hS _ T).ι ≫ pullback.snd φ.hom τ.hom)
    (hk.snd V.1.hom) (by
      rw [Category.assoc, Category.assoc, ← pullback.condition, ← Category.assoc,
        ← Category.assoc, ← Category.assoc]
      change (hk.fst V.1.hom ≫ (fibrePieceHom φ τ T hT).hom) ≫ φ.hom = _
      rw [hk.w, Category.assoc])

/-- The composite of `pieceToChart` with the projection `V ×_X Z ⟶ V` is the projection
`V ×_W P_T ⟶ V`. -/
@[reassoc (attr := simp)]
theorem pieceToChart_snd :
    pieceToChart φ τ hτ V T hT hk ≫ hτ.snd (V.1.hom ≫ φ.hom) = hk.snd V.1.hom :=
  hτ.lift_snd _ _ _

/-- The composite of `pieceToChart` with `chartToFibre` is the composite of the projection
`V ×_W P_T ⟶ P_T` with the inclusion of `P_T` into `W ×_X Z`. -/
theorem yoneda_map_pieceToChart_chartToFibre :
    yoneda.map (pieceToChart φ τ hτ V T hT hk) ≫ chartToFibre φ τ hτ V =
      hk.fst V.1.hom ≫ (openSubspaceOfPoints B S hS _ T).ι := by
  refine pullback.hom_ext ?_ ?_
  · rw [Category.assoc, chartToFibre_fst, ← Category.assoc, ← Functor.map_comp,
      pieceToChart_snd, Category.assoc]
    exact (hk.w V.1.hom).symm
  · rw [Category.assoc, chartToFibre_snd, pieceToChart, hτ.lift_fst, Category.assoc]

/-- The chart `V ×_W P_T` is the base change of the open subspace `P_T ⊆ W ×_X Z` along the
chart `V ×_X Z ⟶ W ×_X Z`. -/
theorem isPullback_pieceToChart :
    IsPullback (hk.fst V.1.hom) (yoneda.map (pieceToChart φ τ hτ V T hT hk))
      (openSubspaceOfPoints B S hS _ T).ι (chartToFibre φ τ hτ V) := by
  refine IsPullback.of_bot ?_ (yoneda_map_pieceToChart_chartToFibre φ τ hτ V T hT hk).symm
    (isPullback_chartToFibre φ τ hτ V)
  rw [← Functor.map_comp, pieceToChart_snd]
  exact hk.isPullback V.1.hom

/-- The morphism `V ×_W P_T ⟶ V ×_X Z` is an open immersion of schemes. -/
theorem isOpenImmersion_pieceToChart :
    _root_.AlgebraicGeometry.IsOpenImmersion
      ((BigFppfOver.toScheme B S hS).map (pieceToChart φ τ hτ V T hT hk)) := by
  have hbc := MorphismProperty.relative_isStableUnderBaseChange
    (MorphismProperty.inverseImage
      (@_root_.AlgebraicGeometry.IsOpenImmersion.{u} : MorphismProperty Scheme.{u})
      (BigFppfOver.toScheme B S hS)) (F := yoneda)
  refine (BigFppfOver.presheaf_inverseImage_yoneda_map_iff B S hS _ _).1 ?_
  exact MorphismProperty.IsStableUnderBaseChange.of_isPullback
    (isPullback_pieceToChart φ τ hτ V T hT hk)
    (isOpenSubspace_openSubspaceOfPoints B S hS (isAlgebraicSpace_pullback_hom φ τ) T hT).2

/-- A point of the scheme `V ×_X Z` lies in the image of `V ×_W P_T` exactly when its image in
`W ×_X Z` lies in `T`. -/
theorem mem_range_pieceToChart_iff
    (w : points B S hS (yoneda.obj (hτ.pullback (V.1.hom ≫ φ.hom)))) :
    pointsToScheme B S hS _ w ∈
        Set.range ((BigFppfOver.toScheme B S hS).map (pieceToChart φ τ hτ V T hT hk)) ↔
      pointsMap B S hS _ (chartToFibre φ τ hτ V) w ∈ T := by
  rw [← mem_range_pointsMap_yoneda_map_iff]
  have h := preimage_image_pointsMap_of_isPullback B S hS
    (isPullback_pieceToChart φ τ hτ V T hT hk) Set.univ
  rw [Set.image_univ, Set.preimage_univ, Set.image_univ,
    range_pointsMap_ι_openSubspaceOfPoints] at h
  rw [← h]
  rfl

end Chart

/-! ### The two pieces over an étale chart -/

section Split

variable {X W Z : AlgebraicSpaces B S hS} (φ : W ⟶ X)
  (τ : Z ⟶ X) (hτ : yoneda.relativelyRepresentable τ.hom)
  (V : SmallEtale B S hS W.1)
  (T : Set (points B S hS (pullback φ.hom τ.hom))) (hT : IsClopen T)
  (hk₁ : yoneda.relativelyRepresentable (fibrePieceHom φ τ T hT.isOpen).hom)
  (hk₂ : yoneda.relativelyRepresentable (fibrePieceHom φ τ Tᶜ hT.isClosed.isOpen_compl).hom)

/-- Over an étale chart `V` of `W`, the charts of the two pieces `P_T` and `P_{T^c}` of
`W ×_X Z` are complementary open subschemes of the chart `V ×_X Z` of `Z`. -/
theorem isCompl_opensRange_pieceToChart :
    haveI := isOpenImmersion_pieceToChart φ τ hτ V T hT.isOpen hk₁
    haveI := isOpenImmersion_pieceToChart φ τ hτ V Tᶜ hT.isClosed.isOpen_compl hk₂
    IsCompl ((BigFppfOver.toScheme B S hS).map (pieceToChart φ τ hτ V T hT.isOpen hk₁)).opensRange
      ((BigFppfOver.toScheme B S hS).map
        (pieceToChart φ τ hτ V Tᶜ hT.isClosed.isOpen_compl hk₂)).opensRange := by
  have := isOpenImmersion_pieceToChart φ τ hτ V T hT.isOpen hk₁
  have := isOpenImmersion_pieceToChart φ τ hτ V Tᶜ hT.isClosed.isOpen_compl hk₂
  have key : ∀ a, (a ∈ Set.range ((BigFppfOver.toScheme B S hS).map
      (pieceToChart φ τ hτ V T hT.isOpen hk₁)) ↔
      a ∉ Set.range ((BigFppfOver.toScheme B S hS).map
        (pieceToChart φ τ hτ V Tᶜ hT.isClosed.isOpen_compl hk₂))) := by
    intro a
    obtain ⟨w, rfl⟩ := surjective_pointsToScheme B S hS _ a
    rw [mem_range_pieceToChart_iff, mem_range_pieceToChart_iff, Set.mem_compl_iff, not_not]
  constructor
  · rw [disjoint_iff, eq_bot_iff]
    intro a ha
    exact ((key a).1 ha.1 ha.2).elim
  · rw [codisjoint_iff, eq_top_iff]
    intro a _
    exact (em (a ∈ Set.range ((BigFppfOver.toScheme B S hS).map
      (pieceToChart φ τ hτ V Tᶜ hT.isClosed.isOpen_compl hk₂)))).symm.imp (key a).2 id

end Split

/-! ### The Fitting ideal of the direct image -/

section Fitting

variable {X W Z : AlgebraicSpaces B S hS}

/-- The direct image `f_* 𝒪_Z` of the structure sheaf along a finite morphism `f : Z ⟶ X`, as an
`𝒪_X`-module, taken along base change of étale charts. -/
noncomputable abbrev finiteDirectImageUnit (f : Z ⟶ X) (hf : IsFinite B S hS f.hom) :
    Modules.{u, u} B S hS X.1 X.2 :=
  (smallBaseChangeModulePushforward B S hS f
    (relativelyRepresentable_hom_of_isFinite B S hS f hf)).obj
      (SheafOfModules.unit (smallEtaleRingSheaf B S hS Z.1 Z.2))

/-- The sections of the direct image of the structure sheaf along a finite morphism over an
affine étale chart of the target form a finite module. -/
theorem moduleFinite_sections_finiteDirectImageUnit (f : Z ⟶ X)
    (hf : IsFinite B S hS f.hom) (A : SmallEtale B S hS X.1)
    (hA : IsAffine ((SmallEtale.toOver B S hS X.1 ⋙ BigFppfOver.toScheme B S hS).obj A)) :
    Module.Finite (chartRing B S hS X.1 X.2 A) ((finiteDirectImageUnit f hf).val.obj (op A)) :=
  moduleFinite_sections_smallBaseChangeModulePushforward B S hS f
    (relativelyRepresentable_hom_of_isFinite B S hS f hf) _ hf A hA (Module.Finite.self _)

/-- The sections of the direct image of the structure sheaf along a finite morphism of finite
presentation over an affine étale chart of the target form a finitely presented module: they are
the regular functions on the base-changed chart, a finite algebra of finite presentation over the
regular functions on the chart (Stacks 0564). -/
theorem moduleFinitePresentation_sections_finiteDirectImageUnit (f : Z ⟶ X)
    (hf : IsFinite B S hS f.hom) (hfp : IsFinitePresentation B S hS f.hom)
    (A : SmallEtale B S hS X.1)
    (hA : IsAffine ((SmallEtale.toOver B S hS X.1 ⋙ BigFppfOver.toScheme B S hS).obj A)) :
    Module.FinitePresentation (chartRing B S hS X.1 X.2 A)
      ((finiteDirectImageUnit f hf).val.obj (op A)) := by
  set hr := relativelyRepresentable_hom_of_isFinite B S hS f hf
  have : IsAffine ((BigFppfOver.toScheme B S hS).obj A.1.left) := hA
  have : _root_.AlgebraicGeometry.IsFinite ((BigFppfOver.toScheme B S hS).map (hr.snd A.1.hom)) :=
    isFinite_toScheme_smallBaseChange_snd B S hS f hr hf A
  have : IsAffine ((BigFppfOver.toScheme B S hS).obj (hr.pullback A.1.hom)) :=
    isAffine_of_isAffineHom ((BigFppfOver.toScheme B S hS).map (hr.snd A.1.hom))
  have : _root_.AlgebraicGeometry.LocallyOfFinitePresentation
      ((BigFppfOver.toScheme B S hS).map (hr.snd A.1.hom)) :=
    hfp.1 _ _ (hr.fst A.1.hom) A.1.hom (hr.snd A.1.hom)
      ((smallBaseChange B S hS f hr).obj A).2 A.2 (hr.w A.1.hom).symm
  let := ((BigFppfOver.toScheme B S hS).map (hr.snd A.1.hom)).appTop.hom.toAlgebra
  have : Module.Finite Γ((BigFppfOver.toScheme B S hS).obj A.1.left, ⊤)
      Γ((BigFppfOver.toScheme B S hS).obj (hr.pullback A.1.hom), ⊤) :=
    Scheme.Hom.finite_appTop _
  have : Algebra.FinitePresentation Γ((BigFppfOver.toScheme B S hS).obj A.1.left, ⊤)
      Γ((BigFppfOver.toScheme B S hS).obj (hr.pullback A.1.hom), ⊤) :=
    Scheme.Hom.finitePresentation_appTop _
  exact Module.FinitePresentation.of_finite_of_finitePresentation
    Γ((BigFppfOver.toScheme B S hS).obj A.1.left, ⊤)
    Γ((BigFppfOver.toScheme B S hS).obj (hr.pullback A.1.hom), ⊤)

/-- The direct image of the structure sheaf along a finite morphism is cartesian on the affine
étale charts of the target. -/
theorem isCartesianOnAffineCharts_finiteDirectImageUnit (f : Z ⟶ X)
    (hf : IsFinite B S hS f.hom) :
    IsCartesianOnAffineCharts (finiteDirectImageUnit f hf) :=
  isCartesianOnAffineCharts_of_isQuasicoherentOnSite B S hS X.1 X.2 _
    (isQuasicoherentOnSite_smallBaseChangeModulePushforward B S hS f hf _
      (SheafOfModules.isQuasicoherentOnSite_unit _))

variable (φ : W ⟶ X) (hφ : IsEtale B S hS φ.hom) (hrep : yoneda.relativelyRepresentable φ.hom)
  (τ : Z ⟶ X) (hτ : IsFinite B S hS τ.hom)
  (T : Set (points B S hS (pullback φ.hom τ.hom))) (hT : IsClopen T)
  (he₁ : IsClosedImmersion B S hS (fibrePieceHom φ τ T hT.isOpen).hom)
  (he₂ : IsFinite B S hS (fibrePieceHom φ τ Tᶜ hT.isClosed.isOpen_compl).hom)

include he₁ in
/-- **The inverse image of the zeroth Fitting ideal of a finite direct image along a clopen
splitting, on an affine chart.**  In the situation of
`AlgebraicGeometry.Space.pullbackIdealSubsheaf_fittingIdeal_eq_idealSmul`, over every affine étale
chart `V` of `W` the sections of `Fit_0(τ_* 𝒪_Z)` over `V ⟶ W ⟶ X` are the product of the
sections of `𝓘` and of `Fit_0((P_{T^c} ⟶ W)_* 𝒪)` over `V`. -/
theorem chartSectionsIdeal_etaleIdealRestrict_fittingIdeal_eq_mul (V : SmallEtale B S hS W.1)
    (hV : IsAffine ((SmallEtale.toOver B S hS W.1 ⋙ BigFppfOver.toScheme B S hS).obj V)) :
    chartSectionsIdeal B S hS W
        (etaleIdealRestrict B S hS φ hφ
          (fittingIdeal B S hS X.1 X.2 (finiteDirectImageUnit τ hτ) 0)) V =
      chartSectionsIdeal B S hS W (kernelIdealSheaf B S hS (fibrePieceHom φ τ T hT.isOpen)) V *
        chartSectionsIdeal B S hS W (fittingIdeal B S hS W.1 W.2
          (finiteDirectImageUnit (fibrePieceHom φ τ Tᶜ hT.isClosed.isOpen_compl) he₂) 0) V := by
  set hτr := relativelyRepresentable_hom_of_isFinite B S hS τ hτ
  set hk₂ := relativelyRepresentable_hom_of_isFinite B S hS _ he₂
  set VX := (smallEtalePostcomp B S hS φ hφ).obj V
  have hVX : IsAffine ((SmallEtale.toOver B S hS X.1 ⋙ BigFppfOver.toScheme B S hS).obj VX) := hV
  have hJ := fittingIdeal_obj_eq_fittingIdealOnChart (finiteDirectImageUnit τ hτ)
    (isCartesianOnAffineCharts_finiteDirectImageUnit τ hτ)
    (fun A hA => moduleFinite_sections_finiteDirectImageUnit τ hτ A hA) 0 hVX
  have hI' := fittingIdeal_obj_eq_fittingIdealOnChart (finiteDirectImageUnit _ he₂)
    (isCartesianOnAffineCharts_finiteDirectImageUnit _ he₂)
    (fun A hA => moduleFinite_sections_finiteDirectImageUnit _ he₂ A hA) 0 hV
  have hK := ker_structureSharp_app_eq_ker_appTop B S hS _ he₁.rep V
  have : IsAffine ((BigFppfOver.toScheme B S hS).obj V.1.left) := hV
  have := isOpenImmersion_pieceToChart φ τ hτr V T hT.isOpen he₁.rep
  have := isOpenImmersion_pieceToChart φ τ hτr V Tᶜ hT.isClosed.isOpen_compl hk₂
  have : _root_.AlgebraicGeometry.IsClosedImmersion
      ((BigFppfOver.toScheme B S hS).map (he₁.rep.snd V.1.hom)) := he₁.property_snd V.1.hom
  let := ((BigFppfOver.toScheme B S hS).map (hτr.snd (V.1.hom ≫ φ.hom))).appTop.hom.toModule
  let := ((BigFppfOver.toScheme B S hS).map (hk₂.snd V.1.hom)).appTop.hom.toModule
  have hfA : Module.Finite Γ((BigFppfOver.toScheme B S hS).obj V.1.left, ⊤)
      Γ((BigFppfOver.toScheme B S hS).obj (hτr.pullback (V.1.hom ≫ φ.hom)), ⊤) :=
    moduleFinite_sections_finiteDirectImageUnit τ hτ VX hVX
  have hfA₂ : Module.Finite Γ((BigFppfOver.toScheme B S hS).obj V.1.left, ⊤)
      Γ((BigFppfOver.toScheme B S hS).obj (hk₂.pullback V.1.hom), ⊤) :=
    moduleFinite_sections_finiteDirectImageUnit _ he₂ V hV
  have key := AlgebraicGeometry.fittingIdeal_zero_appTop_eq_ker_mul
    ((BigFppfOver.toScheme B S hS).map (hτr.snd (V.1.hom ≫ φ.hom)))
    ((BigFppfOver.toScheme B S hS).map (he₁.rep.snd V.1.hom))
    ((BigFppfOver.toScheme B S hS).map (hk₂.snd V.1.hom))
    ((BigFppfOver.toScheme B S hS).map (pieceToChart φ τ hτr V T hT.isOpen he₁.rep))
    ((BigFppfOver.toScheme B S hS).map (pieceToChart φ τ hτr V Tᶜ hT.isClosed.isOpen_compl hk₂))
    (isCompl_opensRange_pieceToChart φ τ hτr V T hT he₁.rep hk₂)
    (by rw [← Functor.map_comp, pieceToChart_snd])
    (by rw [← Functor.map_comp, pieceToChart_snd])
  exact ((chartSectionsIdeal_etaleIdealRestrict B S hS φ hφ _ V).trans (hJ.trans key)).trans
    (congrArg₂ (· * ·) hK.symm hI'.symm)


include hφ he₁ in
/-- **The inverse image of the zeroth Fitting ideal of a finite direct image along a clopen
splitting.**  Let `φ : W ⟶ X` be étale and representable and `τ : Z ⟶ X` finite, and let a
clopen set `T` of points of `W ×_X Z` split it into pieces `P_T` and `P_{T^c}` with `P_T ⟶ W` a
closed immersion and `P_{T^c} ⟶ W` finite.  Then

`φ⁻¹ Fit_0(τ_* 𝒪_Z) · 𝒪_W = 𝓘 · Fit_0((P_{T^c} ⟶ W)_* 𝒪)`,

with `𝓘` the ideal of `P_T ⟶ W`. -/
theorem pullbackIdealSubsheaf_fittingIdeal_eq_idealSmul :
    pullbackIdealSubsheaf B S hS φ hrep
        (fittingIdeal B S hS X.1 X.2 (finiteDirectImageUnit τ hτ) 0) =
      Stacks.Sites.idealSmul (O := structureSheaf B S hS W.1 W.2)
        (kernelIdealSheaf B S hS (fibrePieceHom φ τ T hT.isOpen))
        (fittingIdeal B S hS W.1 W.2
          (finiteDirectImageUnit (fibrePieceHom φ τ Tᶜ hT.isClosed.isOpen_compl) he₂) 0) :=
  (pullbackIdealSubsheaf_eq_etaleIdealRestrict B S hS φ hφ hrep
    (fittingIdeal B S hS X.1 X.2 (finiteDirectImageUnit τ hτ) 0)).trans
    (eq_idealSmul_of_forall_isAffine _ _ _ fun V hV =>
      chartSectionsIdeal_etaleIdealRestrict_fittingIdeal_eq_mul φ hφ τ hτ T hT he₁ he₂ V hV)

end Fitting

end AlgebraicGeometry.Space

end
