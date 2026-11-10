module

public import StacksCore.Tactic.StacksAttribute
public import StacksFrontier.AlgebraicGeometry.Spaces.Descent.Properties.Noetherian
public import StacksFrontier.AlgebraicGeometry.Stacks.DecentStackSoberInertia
public import StacksFrontier.AlgebraicGeometry.Stacks.FppfDescentIngredients
public import StacksFrontier.AlgebraicGeometry.Stacks.GerbeReducedFactorization
public import StacksFrontier.AlgebraicGeometry.Stacks.IntegralAlgebraicStackStructure
public import StacksFrontier.AlgebraicGeometry.Stacks.OpenSubstackPoints
public import StacksFrontier.AlgebraicGeometry.Stacks.ReducedUniquePointSubstack
public import StacksFrontier.AlgebraicGeometry.Stacks.ResidualGerbeQuasiCompactInertia
public import StacksFrontier.AlgebraicGeometry.Stacks.SmoothLocalMorphismComp
public import StacksFrontier.AlgebraicGeometry.Stacks.SurjectiveProperties

/-!
# A reduced stack over a point factors through the residual gerbe

Let `f : 𝒴 ⟶ 𝒳` be a 1-morphism of algebraic stacks and let `x ∈ |𝒳|`. Assume
1. `𝒳` is decent or locally Noetherian (or both),
2. `I_𝒳 ⟶ 𝒳` is quasi-compact,
3. `|f|(|𝒴|)` is contained in `{x}`, and
4. `𝒴` is reduced.

Then the residual gerbe `𝒵_x` of `𝒳` at `x` exists and `f` factors through it.

The residual gerbe appears in two forms: its existence, `HasReducedSingletonPointMonomorphism`,
says that some reduced algebraic stack admits a monomorphism to `𝒳` whose space of points is a
single point lying over `x`; and the residual gerbe itself is the strictly full subcategory
`residualGerbe` cut out by an object property meeting the specification `IsResidualGerbeAt`.

## Main results

* `AlgebraicGeometry.Stack.exists_factorization_of_range_pointsMap_subset_singleton`: `f` factors
  through every monomorphism whose image contains `x`.
* `AlgebraicGeometry.Stack.exists_comp_residualGerbeInclusion_eq`: `f` factors strictly through
  the inclusion of the residual gerbe `residualGerbe`.
* `AlgebraicGeometry.Stack.residualGerbe_factorization_of_isReducedStack`: the residual gerbe
  exists, and `f` factors through every monomorphism with a single point over `x` and strictly
  through every residual gerbe at `x`.

## References

* [Stacks Project, Tag 0H25](https://stacks.math.columbia.edu/tag/0H25)
* [Stacks Project, Tag 06RD](https://stacks.math.columbia.edu/tag/06RD)
* [Stacks Project, Tag 06RC](https://stacks.math.columbia.edu/tag/06RC)
* [Stacks Project, Tag 06MQ](https://stacks.math.columbia.edu/tag/06MQ)
* [Stacks Project, Tag 0H1T](https://stacks.math.columbia.edu/tag/0H1T)
* [Stacks Project, Tag 0H1S](https://stacks.math.columbia.edu/tag/0H1S)
-/

@[expose] public section

open CategoryTheory

universe u w

namespace AlgebraicGeometry.Stack

variable (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)

/-- **A 1-morphism whose image on points lies in an open substack factors through it**: every
object of the source is sent into the open substack. -/
theorem OpenSubstack.mem_of_range_pointsMap_subset {𝒳 𝒴 : AlgebraicStacks.{u, w} B S hS}
    (W : OpenSubstack 𝒳) (f : 𝒴 ⟶ 𝒳)
    (hf : Set.range (AlgebraicStacks.pointsMap B S hS f) ⊆
      Set.range (AlgebraicStacks.pointsMap B S hS
        (fullSubcategoryInclusion 𝒳 W.property W.isAlgebraic))) :
    ∀ ξ : 𝒴.val.val.obj, W.property (f.hom.hom.toFunctor.obj ξ) := by
  intro ξ
  obtain ⟨b, ⟨e⟩⟩ := AlgebraicStacks.exists_schemeStack_hom_iso B S hS 𝒴 ξ
  have hrange : Set.range (AlgebraicStacks.pointsMap B S hS (b ≫ f)) ⊆
      Set.range (AlgebraicStacks.pointsMap B S hS
        (fullSubcategoryInclusion 𝒳 W.property W.isAlgebraic)) := by
    rintro _ ⟨q, rfl⟩
    refine hf ⟨AlgebraicStacks.pointsMap B S hS b q, ?_⟩
    rw [AlgebraicStacks.pointsMap_comp]
    rfl
  obtain ⟨z, ⟨e'⟩⟩ := AlgebraicStacks.exists_iso_of_range_pointsMap_subset B S hS
    (fullSubcategoryInclusion 𝒳 W.property W.isAlgebraic) W.isOpenImmersion (b ≫ f) hrange
  have := W.strictlyFull
  exact W.property.prop_of_iso (e' ≪≫ f.hom.hom.toFunctor.mapIso e) z.property

/-- **A locally Noetherian gerbe has locally Noetherian base space.** Let `π : 𝒰 ⟶ 𝒱` make `𝒰` a
gerbe over an algebraic stack represented by an algebraic space `F`. If `𝒰` is locally Noetherian,
so is `F`. -/
theorem hasEtaleLocalProperty_isLocallyNoetherian_of_isGerbeOver
    {𝒰 𝒱 : AlgebraicStacks.{u, w} B S hS} (π : 𝒰 ⟶ 𝒱)
    (hπ : AlgebraicStacks.IsGerbeOver B S hS π)
    (F : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u) (hF : IsAlgebraicSpace B S hS F)
    (eF : StacksRepresentableCFG.EquivalenceOver 𝒱.val.val.p
      (presheafOfCategories (F ⋙ typeToCat)).p)
    (hN : IsLocallyNoetherianStack B S hS 𝒰) :
    Space.HasEtaleLocalProperty B S hS F (fun T : Scheme.{u} => IsLocallyNoetherian T) := by
  obtain ⟨V, b, hbsurj, hbsm, hV⟩ := hN
  obtain ⟨hπflat, hπlfp⟩ :=
    AlgebraicStacks.isFlat_and_isLocallyOfFinitePresentation_of_isGerbeOver B S hS π hπ
  have hV' : Space.HasEtaleLocalProperty B S hS (yoneda.obj V)
      (fun T : Scheme.{u} => IsLocallyNoetherian T) :=
    (Space.exists_atlas_iff_of_representable B S hS (yoneda.obj V)
      (fun T : Scheme.{u} => IsLocallyNoetherian T) V (Iso.refl _)).mpr hV
  have hVsp : IsAlgebraicSpace B S hS (yoneda.obj V) := isAlgebraicSpace_yoneda B S hS V
  let c : schemeStack.{u, w} B S hS V ⟶ 𝒱 := b ≫ π
  have hclfp : AlgebraicStacks.IsLocallyOfFinitePresentation B S hS c :=
    AlgebraicStacks.isLocallyOfFinitePresentation_comp B S hS b π
      (AlgebraicStacks.isLocallyOfFinitePresentation_of_isSmooth B S hS b hbsm) hπlfp
  have hcflat : AlgebraicStacks.IsFlat B S hS c :=
    AlgebraicStacks.isFlat_comp B S hS b π (AlgebraicStacks.isFlat_of_isSmooth B S hS b hbsm)
      hπflat
  have hcsurj : IsSurjective B S hS c :=
    isSurjective_comp B S hS b π hbsurj (isSurjective_of_isGerbeOver B S hS π hπ)
  have h₁ := isLocallyOfFinitePresentation_representingMap_of_isLocallyOfFinitePresentation B S hS
    (yoneda.obj V) F hVsp hF (representedChart B S hS V) eF c hclfp
  have h₂ := isFlat_representingMap_of_isFlat B S hS (yoneda.obj V) F hVsp hF
    (representedChart B S hS V) eF c hcflat
  have h₃ := isSurjective_representingMap_of_isSurjective B S hS (yoneda.obj V) F
    (representedChart B S hS V) eF c hcsurj
  exact Space.isLocallyNoetherian_of_isSurjective_of_isFlat_of_isLocallyOfFinitePresentation
    B S hS hVsp hF _ h₁ h₂ h₃ hV'

/-- A 1-morphism into `𝒞` that lands on the image of `b` under an injective `j : ℬ ⟶ 𝒞` on
points sends `y` to `b`. -/
private theorem pointsMap_eq_of_comp_eq {𝒜 ℬ 𝒞 : AlgebraicStacks.{u, w} B S hS}
    (g : 𝒜 ⟶ ℬ) (j : ℬ ⟶ 𝒞) (hj : Function.Injective (AlgebraicStacks.pointsMap B S hS j))
    (y : AlgebraicStacks.points B S hS 𝒜) (b : AlgebraicStacks.points B S hS ℬ)
    (h : AlgebraicStacks.pointsMap B S hS (g ≫ j) y = AlgebraicStacks.pointsMap B S hS j b) :
    AlgebraicStacks.pointsMap B S hS g y = b :=
  hj (by rwa [AlgebraicStacks.pointsMap_comp] at h)

/-- **A reduced stack over a point of a decent or locally Noetherian stack with quasi-compact
inertia factors through every monomorphism whose image contains the point.** -/
theorem exists_factorization_of_range_pointsMap_subset_singleton
    {𝒳 𝒴 : AlgebraicStacks.{u, w} B S hS} (f : 𝒴 ⟶ 𝒳) (x : AlgebraicStacks.points B S hS 𝒳)
    (h1 : IsDecent B S hS 𝒳.val ∨ IsLocallyNoetherianStack B S hS 𝒳)
    (h2 : IsQuasiCompactMorphism.{u, w} B S hS (inertiaProjectionAlgebraicStacks B S hS 𝒳))
    (h3 : Set.range (AlgebraicStacks.pointsMap B S hS f) ⊆ {x})
    (h4 : IsReducedStack B S hS 𝒴)
    {𝒵 : AlgebraicStacks.{u, w} B S hS} (m : 𝒵 ⟶ 𝒳)
    (hm : AlgebraicStacks.IsMonomorphism B S hS m) (z : AlgebraicStacks.points B S hS 𝒵)
    (hz : AlgebraicStacks.pointsMap B S hS m z = x) :
    ∃ g : 𝒴 ⟶ 𝒵, Nonempty (g ≫ m ≅ f) := by
  classical
  let := pointTopology B S hS 𝒳.val
  obtain ⟨P, hP, hPT⟩ :=
    exists_isClosedSubstack_isReducedStack_range_pointsMap_eq 𝒳 (closure {x}) isClosed_closure
  obtain ⟨hA, -⟩ := id hP.2
  obtain ⟨hrange, hred⟩ := hPT hA
  set 𝒳' := fullSubcategoryAlgebraicStack 𝒳 P hA
  let i := fullSubcategoryInclusion 𝒳 P hA
  have hmemP : ∀ ξ : 𝒴.val.val.obj, P (f.hom.hom.toFunctor.obj ξ) := by
    have := hP.1
    refine (factorsThroughSubstack_iff_forall f).1
      ((factorsThroughSubstack_iff_range_pointsMap_subset B S hS f hP hA h4).2 ?_)
    rw [hrange]
    exact h3.trans (Set.singleton_subset_iff.2 (subset_closure (Set.mem_singleton x)))
  let f' : 𝒴 ⟶ 𝒳' := liftFullSubcategory B S hS f hA hmemP
  have h1' : IsDecent B S hS 𝒳'.val ∨ IsLocallyNoetherianStack B S hS 𝒳' := by
    rcases h1 with hd | hN
    · exact Or.inl (AlgebraicStacks.isDecent_of_isClosedSubstack hd hP hA)
    · exact Or.inr (isLocallyNoetherianStack_of_isClosedSubstack B S hS 𝒳 P hP hA hN)
  have h2' := AlgebraicStacks.isQuasiCompactMorphism_inertia_of_fullyFaithful i
    (Functor.FullyFaithful.ofFullyFaithful _) h2
  obtain ⟨W, hWdense, hWgerbe⟩ := exists_openSubstack_dense_isGerbe B S hS 𝒳' hred h2'
  let := pointTopology B S hS 𝒳'.val
  obtain ⟨x', hx'⟩ : x ∈ Set.range (AlgebraicStacks.pointsMap B S hS i) :=
    hrange ▸ subset_closure (Set.mem_singleton x)
  have hemb := (AlgebraicStacks.isClosedEmbedding_pointsMap_of_isClosedSubstack hP hA).isEmbedding
  have hgen : closure {x'} = Set.univ := by
    rw [hemb.closure_eq_preimage_closure_image, Set.image_singleton]
    change AlgebraicStacks.pointsMap B S hS i ⁻¹'
      closure {AlgebraicStacks.pointsMap B S hS i x'} = _
    rw [hx', ← hrange, Set.preimage_range]
  have hx'W : x' ∈ W.pointSet B S hS := by
    have : Nonempty (AlgebraicStacks.points B S hS 𝒳') := ⟨x'⟩
    obtain ⟨y, hy⟩ := hWdense.nonempty
    exact (specializes_iff_closure_subset.2 (hgen ▸ Set.subset_univ _)).mem_open
      (OpenSubstack.isOpen_pointSet B S hS W) hy
  obtain ⟨u, hu⟩ := hx'W
  have hf' : ∀ y, AlgebraicStacks.pointsMap B S hS f' y = x' := by
    intro y
    exact pointsMap_eq_of_comp_eq B S hS f' i hemb.injective y x' (hx'.symm ▸ h3 ⟨y, rfl⟩)
  have hmemW : ∀ ξ : 𝒴.val.val.obj, W.property (f'.hom.hom.toFunctor.obj ξ) := by
    refine OpenSubstack.mem_of_range_pointsMap_subset B S hS W f' ?_
    rintro _ ⟨y, rfl⟩
    rw [hf' y]
    exact ⟨u, hu⟩
  let f'' : 𝒴 ⟶ fullSubcategoryAlgebraicStack 𝒳' W.property W.isAlgebraic :=
    liftFullSubcategory B S hS f' W.isAlgebraic hmemW
  have e₁ : f'' ≫ OpenSubstack.inclusion B S hS W = f' :=
    liftFullSubcategory_comp B S hS f' W.isAlgebraic hmemW
  have e₂ : f' ≫ i = f := liftFullSubcategory_comp B S hS f hA hmemP
  have : (CatFiberedInGroupoids.homFunctor
      (fullSubcategoryInclusion 𝒳' W.property W.isAlgebraic).hom).Full :=
    full_fullSubcategoryInclusion 𝒳' W.property W.isAlgebraic
  have : (CatFiberedInGroupoids.homFunctor
      (fullSubcategoryInclusion 𝒳' W.property W.isAlgebraic).hom).Faithful :=
    faithful_fullSubcategoryInclusion 𝒳' W.property W.isAlgebraic
  have hjinj : Function.Injective (AlgebraicStacks.pointsMap B S hS
      (fullSubcategoryInclusion 𝒳' W.property W.isAlgebraic)) :=
    pointsMap_injective_of_fullyFaithful B S hS _
  have hf'' : ∀ y, AlgebraicStacks.pointsMap B S hS f'' y = u := by
    intro y
    exact pointsMap_eq_of_comp_eq B S hS f'' _ hjinj y u ((hf' y).trans hu.symm)
  obtain ⟨𝒱, ⟨F, hF, ⟨eF⟩⟩, π, hπ⟩ := hWgerbe
  have hcase : Space.IsDecentSpace B S hS F ∨
      Space.HasEtaleLocalProperty B S hS F (fun T : Scheme.{u} => IsLocallyNoetherian T) := by
    rcases h1' with hd | hN
    · exact Or.inl (isDecentSpace_of_isDecent_representing B S hS 𝒱.val
        (isDecent_of_isGerbeOver B S hS π hπ (OpenSubstack.isDecent B S hS W hd)) F hF eF)
    · refine Or.inr
        (hasEtaleLocalProperty_isLocallyNoetherian_of_isGerbeOver B S hS π hπ F hF eF ?_)
      exact AlgebraicStacks.isLocallyNoetherian_of_isImmersion B S hS
        (OpenSubstack.inclusion B S hS W)
        ⟨W.isOpenImmersion.1, fun U y hy G hG he =>
          Space.isImmersion_of_isOpenImmersion B S hS (W.isOpenImmersion.2 U y hy G hG he)⟩ hN
  obtain ⟨𝒲, h, hcov, ⟨w, hw⟩, a, ⟨ηa⟩⟩ :=
    exists_cover_factorization_of_isGerbeOver B S hS π hπ F hF eF hcase u f'' hf'' h4
  have hwz : AlgebraicStacks.pointsMap B S hS (h ≫ OpenSubstack.inclusion B S hS W ≫ i) w =
      AlgebraicStacks.pointsMap B S hS m z := by
    rw [AlgebraicStacks.pointsMap_comp, AlgebraicStacks.pointsMap_comp, Function.comp_apply,
      Function.comp_apply, hw, hu, hx', hz]
  obtain ⟨k, ⟨ηk⟩⟩ := exists_factorization_of_isMonomorphism_of_fieldSpectrumCover B S hS
    (h ≫ OpenSubstack.inclusion B S hS W ≫ i) m hm hcov w z hwz
  refine ⟨a ≫ k, ⟨?_⟩⟩
  exact Bicategory.associator a k m ≪≫ Bicategory.whiskerLeftIso a ηk ≪≫
    (Bicategory.associator a h (OpenSubstack.inclusion B S hS W ≫ i)).symm ≪≫
    Bicategory.whiskerRightIso ηa (OpenSubstack.inclusion B S hS W ≫ i) ≪≫
    (Bicategory.associator f'' (OpenSubstack.inclusion B S hS W) i).symm ≪≫
    eqToIso (by rw [e₁, e₂])

/-- **A reduced stack over a point factors strictly through the residual gerbe.** Under the
hypotheses of `AlgebraicGeometry.Stack.residualGerbe_factorization_of_isReducedStack`, `f` factors
through the inclusion of every residual gerbe `residualGerbe` of `𝒳` at `x`, by a 1-morphism whose
composite with the inclusion is `f` on the nose. -/
theorem exists_comp_residualGerbeInclusion_eq
    {𝒳 𝒴 : AlgebraicStacks.{u, w} B S hS} (f : 𝒴 ⟶ 𝒳) (x : AlgebraicStacks.points B S hS 𝒳)
    (h1 : IsDecent B S hS 𝒳.val ∨ IsLocallyNoetherianStack B S hS 𝒳)
    (h2 : IsQuasiCompactMorphism.{u, w} B S hS (inertiaProjectionAlgebraicStacks B S hS 𝒳))
    (h3 : Set.range (AlgebraicStacks.pointsMap B S hS f) ⊆ {x})
    (h4 : IsReducedStack B S hS 𝒴)
    (P : ObjectProperty 𝒳.val.val.obj) (hP : IsResidualGerbeAt B S hS 𝒳 x P) :
    ∃ g : 𝒴 ⟶ residualGerbe B S hS 𝒳 x P hP,
      g ≫ residualGerbeInclusion B S hS 𝒳 x P hP = f := by
  obtain ⟨z, -, hz⟩ := hP.2.choose_spec.2.2
  obtain ⟨g, ⟨η⟩⟩ := exists_factorization_of_range_pointsMap_subset_singleton B S hS f x h1 h2 h3
    h4 (fullSubcategoryInclusion 𝒳 P hP.2.choose)
    (AlgebraicStacks.isMonomorphism_fullSubcategoryInclusion B S hS 𝒳 P hP.2.choose) z hz
  have hmem : ∀ ξ : 𝒴.val.val.obj, P (f.hom.hom.toFunctor.obj ξ) := fun ξ => by
    have := hP.1
    exact P.prop_of_iso ((CatFiberedInGroupoids.underlyingIso
      (Bicategory.InducedBicategory.isoHom η)).app ξ)
      (g.hom.hom.toFunctor.obj ξ).property
  exact ⟨liftFullSubcategory B S hS f hP.2.choose hmem, rfl⟩

/-- **A reduced stack over a point factors through the residual gerbe.** Let `f : 𝒴 ⟶ 𝒳` be a
1-morphism of algebraic stacks over `S` and let `x ∈ |𝒳|`. Assume that
1. `𝒳` is decent or locally Noetherian (or both),
2. the inertia projection `I_𝒳 ⟶ 𝒳` is quasi-compact,
3. `|f|(|𝒴|)` is contained in `{x}`, and
4. `𝒴` is reduced.

Then the residual gerbe `𝒵_x` of `𝒳` at `x` exists and `f` factors through it. Precisely:
* the residual gerbe of `𝒳` at `x` exists: some reduced algebraic stack admits a monomorphism to
  `𝒳` whose space of points is a single point lying over `x`;
* `f` factors, up to a 2-isomorphism, through every monomorphism `𝒵 ⟶ 𝒳` from an algebraic stack
  with a single point lying over `x`, in particular through every residual gerbe so presented;
* `f` factors strictly through the inclusion of every residual gerbe of `𝒳` at `x`, the strictly
  full subcategory `residualGerbe`. -/
@[stacks 0H25]
theorem residualGerbe_factorization_of_isReducedStack
    {𝒳 𝒴 : AlgebraicStacks.{u, w} B S hS} (f : 𝒴 ⟶ 𝒳) (x : AlgebraicStacks.points B S hS 𝒳)
    (h1 : IsDecent B S hS 𝒳.val ∨ IsLocallyNoetherianStack B S hS 𝒳)
    (h2 : IsQuasiCompactMorphism.{u, w} B S hS (inertiaProjectionAlgebraicStacks B S hS 𝒳))
    (h3 : Set.range (AlgebraicStacks.pointsMap B S hS f) ⊆ {x})
    (h4 : IsReducedStack B S hS 𝒴) :
    HasReducedSingletonPointMonomorphism B S hS 𝒳 x ∧
      (∀ (𝒵 : AlgebraicStacks.{u, w} B S hS) (m : 𝒵 ⟶ 𝒳),
        AlgebraicStacks.IsMonomorphism B S hS m → HasUniquePointOver B S hS m x →
          ∃ g : 𝒴 ⟶ 𝒵, Nonempty (g ≫ m ≅ f)) ∧
      ∀ (P : ObjectProperty 𝒳.val.val.obj) (hP : IsResidualGerbeAt B S hS 𝒳 x P),
        ∃ g : 𝒴 ⟶ residualGerbe B S hS 𝒳 x P hP,
          g ≫ residualGerbeInclusion B S hS 𝒳 x P hP = f :=
  ⟨hasReducedSingletonPointMonomorphism_of_isQuasiCompact_inertia B S hS 𝒳 h2 x,
    fun _ m hm ⟨z, _, hz⟩ =>
      exists_factorization_of_range_pointsMap_subset_singleton B S hS f x h1 h2 h3 h4 m hm z hz,
    fun P hP => exists_comp_residualGerbeInclusion_eq B S hS f x h1 h2 h3 h4 P hP⟩

end AlgebraicGeometry.Stack

end
