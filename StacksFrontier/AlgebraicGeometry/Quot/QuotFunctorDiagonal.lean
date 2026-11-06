module

public import StacksCore.Tactic.StacksAttribute
public import StacksFrontier.AlgebraicGeometry.Quot.HilbertQuotNaturality
public import StacksFrontier.AlgebraicGeometry.Quot.QuotFunctorPresheaf
public import StacksFrontier.AlgebraicGeometry.Spaces.LargeValuedProper
public import StacksFrontier.AlgebraicGeometry.Spaces.QuasicoherentClausesUnconditional
public import StacksFrontier.AlgebraicGeometry.Spaces.ModuleMapTargetBaseChange
public import StacksFrontier.AlgebraicGeometry.Spaces.ZeroLocusClosedProperSupportUnconditional
public import StacksFrontier.AlgebraicGeometry.Topologies.FiniteTypeOnSiteKernel
public import StacksFrontier.CategoryTheory.Functor.ConjugateQuotientOrder
public import StacksFrontier.CategoryTheory.MorphismProperty.RelativeDiagonalEqualizerLocus

/-!
# The diagonal of the Quot functor (Stacks 0DM2)

Let `f : X ⟶ B` be a morphism of algebraic spaces of finite presentation and `F` a quasi-coherent
`𝒪_X`-module, the standing data `AlgebraicGeometry.Space.QuotSituation` of Stacks 09TR. Stacks
0DM2 asserts that the diagonal of `Quot_{F/X/B} ⟶ B` is a closed immersion, and a closed immersion
of finite presentation when `F` is of finite type.

## The argument

Two `T`-valued points of `Quot_{F/X/B}` over `B` are two quotients `F_T ⟶ Q₁`, `F_T ⟶ Q₂`, recorded
by their kernels `K₁, K₂`. After a base change `T' ⟶ T` they agree exactly when the pullback of
each kernel is contained in the pullback of the other kernel, and by right exactness of pullback
(`CategoryTheory.Functor.conjSubobject_le_conjSubobject_iff`) the pullback of `K₁` is contained in
the pullback of `K₂` exactly when the pullback of the composite `u₁ : K₁ ⟶ F_T ⟶ Q₂` vanishes. By
Stacks 083M
(`AlgebraicGeometry.Space.ModuleMapSituation.zeroLocusRepresentation_of_hasProperSupport`) applied
to `u₁` and to the symmetric map `u₂ : K₂ ⟶ Q₁`, each vanishing locus is a closed subspace of `T`,
of finite presentation when `K₁`, `K₂` are of finite type, which holds when `F` is of finite type
by Stacks 082T. The locus where the two quotients agree is the intersection of the two, a closed
subscheme of `T`.

## Main results

* `AlgebraicGeometry.Space.QuotSituation.exists_quotientPullback_eq_iff_of_presheaf`: the locus
  of a test scheme where two quotients agree is cut out by a morphism with any property stable
  under composition which every zero locus of Stacks 083M has.
* `AlgebraicGeometry.Space.QuotSituation.diagonal_quotSitePresheafToBase`: the diagonal of
  `Quot_{F/X/B} ⟶ B` is a closed immersion, of finite presentation when `F` is of finite type.

## Implementation notes

The Quot presheaf takes values in `Type (u + 1)`, quotients being recorded by subobjects, so the
diagonal is a morphism of presheaves of `Type (u + 1)` and its being a closed immersion is read
through `CategoryTheory.uliftYoneda`, as `AlgebraicGeometry.Space.IsClosedImmersionULift`; that is
`AlgebraicGeometry.Space.IsClosedImmersion` with the scheme-valued points taken one universe up,
and it presupposes no choice of model of the Quot presheaf in `Type u`. A closed immersion of
algebraic spaces is representable, so being of finite presentation is tested on its base changes to
schemes, which are closed immersions locally of finite presentation (a closed immersion being
quasi-compact and separated).

## References

* [Stacks Project, Tag 0DM2](https://stacks.math.columbia.edu/tag/0DM2)
* [Stacks Project, Tag 083M](https://stacks.math.columbia.edu/tag/083M)
* [Stacks Project, Tag 082T](https://stacks.math.columbia.edu/tag/082T)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits Opposite

-- The `𝒪_{X_T}`-modules here have their sections in the universe `u` of the schemes, which this
-- ambient-universe abelian structure cannot describe; left in place it is selected ahead of
-- `SheafOfModules.instAbelian` and leaves the module universe of every subobject and cokernel
-- below unsolved.
attribute [-instance] Stacks.Cohomology.SiteModules.moduleSheavesAbelian

universe u

namespace AlgebraicGeometry.Space

variable {B : BigFppfSite.{u}} {S : Scheme.{u}} {hS : B.Contains S}

/-! ### Closed subspaces of a scheme of the site -/

/-- **A subfunctor of a scheme of the site whose inclusion has a relative property is a locus on
the schemes of the site.** If the inclusion of `W ⊆ yoneda T` has a property `Q` of morphisms of
the site relative to `yoneda`, then there is a morphism `s : V ⟶ T` with property `Q` through which
a morphism `T' ⟶ T` factors exactly when its functor of points factors through `W`. -/
theorem exists_forall_factorsThrough_iff_of_presheaf
    (Q : MorphismProperty (BigFppfOver B S hS)) {T : BigFppfOver B S hS}
    (W : Subfunctor (yoneda.obj T)) (hW : Q.presheaf W.ι) :
    ∃ (V : BigFppfOver B S hS) (s : V ⟶ T), Q s ∧
      ∀ (T' : BigFppfOver B S hS) (h : T' ⟶ T),
        (∃ t : T' ⟶ V, t ≫ s = h) ↔ ∃ r : yoneda.obj T' ⟶ W.toFunctor, r ≫ W.ι = yoneda.map h := by
  have hpb := hW.rep.isPullback (𝟙 (yoneda.obj T))
  have _ : IsIso (hW.rep.fst (𝟙 (yoneda.obj T))) := hpb.isIso_fst_of_isIso
  have he : hW.rep.fst (𝟙 (yoneda.obj T)) ≫ W.ι = yoneda.map (hW.rep.snd (𝟙 (yoneda.obj T))) := by
    exact hpb.w.trans (Category.comp_id _)
  refine ⟨hW.rep.pullback (𝟙 (yoneda.obj T)), hW.rep.snd (𝟙 (yoneda.obj T)),
    hW.property_snd (𝟙 (yoneda.obj T)), fun T' h => ⟨?_, ?_⟩⟩
  · rintro ⟨t, rfl⟩
    exact ⟨yoneda.map t ≫ hW.rep.fst (𝟙 (yoneda.obj T)), by
      rw [Category.assoc, he, ← Functor.map_comp]⟩
  · rintro ⟨r, hr⟩
    refine ⟨yoneda.preimage (r ≫ inv (hW.rep.fst (𝟙 (yoneda.obj T)))), yoneda.map_injective ?_⟩
    rw [Functor.map_comp, Functor.map_preimage, ← he, Category.assoc, IsIso.inv_hom_id_assoc]
    exact hr

/-- **Intersecting a locus with a relatively represented subfunctor.** Given a morphism
`s₁ : V₁ ⟶ T` of the site with property `Q` and a subfunctor `W ⊆ yoneda T` whose inclusion has
`Q` relative to `yoneda`, there is a morphism `s : V ⟶ T` with property `Q`, provided `Q` is
stable under composition, through which a morphism `T' ⟶ T` factors exactly when it factors
through `s₁` and its functor of points factors through `W`. -/
theorem exists_forall_factorsThrough_iff_of_presheaf_inter
    (Q : MorphismProperty (BigFppfOver B S hS)) [Q.IsStableUnderComposition]
    {T V₁ : BigFppfOver B S hS} (s₁ : V₁ ⟶ T) (hs₁ : Q s₁)
    (W : Subfunctor (yoneda.obj T)) (hW : Q.presheaf W.ι) :
    ∃ (V : BigFppfOver B S hS) (s : V ⟶ T), Q s ∧
      ∀ (T' : BigFppfOver B S hS) (h : T' ⟶ T),
        (∃ t : T' ⟶ V, t ≫ s = h) ↔ (∃ t₁ : T' ⟶ V₁, t₁ ≫ s₁ = h) ∧
          ∃ r : yoneda.obj T' ⟶ W.toFunctor, r ≫ W.ι = yoneda.map h := by
  have hpb := hW.rep.isPullback (yoneda.map s₁)
  refine ⟨hW.rep.pullback (yoneda.map s₁), hW.rep.snd (yoneda.map s₁) ≫ s₁,
    Q.comp_mem _ _ (hW.property_snd (yoneda.map s₁)) hs₁, fun T' h => ⟨?_, ?_⟩⟩
  · rintro ⟨t, rfl⟩
    refine ⟨⟨t ≫ hW.rep.snd (yoneda.map s₁), by rw [Category.assoc]⟩,
      yoneda.map t ≫ hW.rep.fst (yoneda.map s₁), ?_⟩
    rw [Category.assoc, hpb.w, ← Functor.map_comp_assoc, ← Functor.map_comp, Category.assoc]
  · rintro ⟨⟨t₁, rfl⟩, r, hr⟩
    refine ⟨yoneda.preimage (hpb.lift r (yoneda.map t₁) (hr.trans (yoneda.map_comp t₁ s₁))), ?_⟩
    rw [← Category.assoc]
    congr 1
    apply yoneda.map_injective
    rw [Functor.map_comp, Functor.map_preimage, hpb.lift_snd]

/-- The closed immersions of schemes of the site which are locally of finite presentation. -/
abbrev closedImmersionFinitePresentation : MorphismProperty (BigFppfOver B S hS) :=
  MorphismProperty.inverseImage
    (@AlgebraicGeometry.IsClosedImmersion.{u} ⊓ @AlgebraicGeometry.LocallyOfFinitePresentation.{u})
    (BigFppfOver.toScheme B S hS)

/-- Closed immersions locally of finite presentation of the site respect isomorphisms. -/
instance : (closedImmersionFinitePresentation (B := B) (S := S) (hS := hS)).RespectsIso :=
  have : (@AlgebraicGeometry.IsClosedImmersion.{u} ⊓
      @AlgebraicGeometry.LocallyOfFinitePresentation.{u} :
        MorphismProperty Scheme.{u}).RespectsIso :=
    have : MorphismProperty.RespectsIso
        (@AlgebraicGeometry.LocallyOfFinitePresentation.{u} : MorphismProperty Scheme.{u}) :=
      MorphismProperty.respectsIso_of_isStableUnderComposition fun _ _ f hf => by
        have : IsIso f := hf
        infer_instance
    MorphismProperty.RespectsIso.inf _ _
  MorphismProperty.RespectsIso.inverseImage _ _

/-- Closed immersions locally of finite presentation of the site are stable under composition. -/
instance : (closedImmersionFinitePresentation (B := B) (S := S) (hS := hS)).IsStableUnderComposition
    where
  comp_mem f g hf hg := by
    change AlgebraicGeometry.IsClosedImmersion ((BigFppfOver.toScheme B S hS).map (f ≫ g)) ∧
      AlgebraicGeometry.LocallyOfFinitePresentation ((BigFppfOver.toScheme B S hS).map (f ≫ g))
    have := hf.1
    have := hf.2
    have := hg.1
    have := hg.2
    rw [Functor.map_comp]
    exact ⟨inferInstance, inferInstance⟩

/-- Closed immersions of schemes of the site are stable under composition. -/
instance : (MorphismProperty.inverseImage (@AlgebraicGeometry.IsClosedImmersion.{u})
    (BigFppfOver.toScheme B S hS)).IsStableUnderComposition where
  comp_mem f g hf hg := by
    change AlgebraicGeometry.IsClosedImmersion ((BigFppfOver.toScheme B S hS).map (f ≫ g))
    have : AlgebraicGeometry.IsClosedImmersion ((BigFppfOver.toScheme B S hS).map f) := hf
    have : AlgebraicGeometry.IsClosedImmersion ((BigFppfOver.toScheme B S hS).map g) := hg
    rw [Functor.map_comp]
    infer_instance

/-- A closed immersion of schemes of the site is a monomorphism of the site. -/
theorem mono_of_isClosedImmersion_toScheme_map {V T : BigFppfOver B S hS} (s : V ⟶ T)
    (hs : AlgebraicGeometry.IsClosedImmersion ((BigFppfOver.toScheme B S hS).map s)) : Mono s :=
  (BigFppfOver.toScheme B S hS).mono_of_mono_map
    (inferInstanceAs (Mono ((BigFppfOver.toScheme B S hS).map s)))

/-- Every zero locus of Stacks 083M over a scheme of the site is a closed immersion relative to
`yoneda`. -/
theorem presheaf_isClosedImmersion_of_isClosedSubspace {T : BigFppfOver B S hS}
    (Z : Subfunctor (yoneda.obj T)) (hZ : IsClosedSubspace B S hS Z) :
    (MorphismProperty.inverseImage (@AlgebraicGeometry.IsClosedImmersion.{u})
      (BigFppfOver.toScheme B S hS)).presheaf Z.ι :=
  hZ.2

/-- A closed subspace of a scheme of the site whose inclusion is of finite presentation is a
closed immersion locally of finite presentation relative to `yoneda`. -/
theorem presheaf_closedImmersionFinitePresentation_of_isClosedSubspace {T : BigFppfOver B S hS}
    (Z : Subfunctor (yoneda.obj T)) (hZ : IsClosedSubspace B S hS Z)
    (hfp : IsFinitePresentation B S hS Z.ι) :
    (closedImmersionFinitePresentation (B := B) (S := S) (hS := hS)).presheaf Z.ι := by
  have hlfp := (isLocallyOfFinitePresentation_iff_presheaf B S hS hZ.1
    (isAlgebraicSpace_yoneda B S hS T) hZ.2.rep).1 hfp.1
  exact ⟨hZ.2.rep, fun _ _ g fst snd h => ⟨hZ.2.2 g fst snd h, hlfp.2 g fst snd h⟩⟩

namespace QuotSituation

variable (D : QuotSituation B S hS)

/-! ### Comparing two quotients after base change -/

/-- **Containment of pulled-back quotients is a vanishing condition.** After a morphism
`h : T' ⟶ T` of test schemes, the pullback of the quotient with kernel `K` has kernel contained in
that of the pullback of the quotient with kernel `K'` exactly when the pullback of the composite
`K ⟶ F_T ⟶ F_T/K'` along `X_{T'} ⟶ X_T` vanishes. -/
theorem quotientPullback_le_quotientPullback_iff {T' T : SchemesOver D.Y} (h : T' ⟶ T)
    (K K' : Subobject (D.baseChangeModule T)) :
    D.quotientPullback h K ≤ D.quotientPullback h K' ↔
      (modulePullback B S hS (D.relativeMap h)).map (K.arrow ≫ D.quotientProjection T K') = 0 :=
  Functor.conjSubobject_le_conjSubobject_iff
    (preservesFiniteColimits_spaceModulePullback (D.relativeMap h)) (D.baseChangeComparison h) K K'

/-- The short exact sequence `0 ⟶ K ⟶ F_T ⟶ F_T/K ⟶ 0` of a submodule of `F_T`. -/
abbrev kernelShortComplex (T : SchemesOver D.Y) (K : Subobject (D.baseChangeModule T)) :
    ShortComplex (Modules.{u, u} B S hS (D.space T).1 (D.space T).2) :=
  ShortComplex.mk K.arrow (D.quotientProjection T K) (cokernel.condition K.arrow)

/-- The sequence `0 ⟶ K ⟶ F_T ⟶ F_T/K ⟶ 0` of a submodule `K` of `F_T` is short exact. -/
theorem shortExact_kernelShortComplex (T : SchemesOver D.Y)
    (K : Subobject (D.baseChangeModule T)) : (D.kernelShortComplex T K).ShortExact := by
  refine ShortComplex.ShortExact.mk' ?_ (by dsimp; infer_instance) (by dsimp; infer_instance)
  exact ShortComplex.exact_of_g_is_cokernel _ (cokernelIsCokernel K.arrow)

/-- The kernel of a member of `Quot_{F/X/B}(T)` is quasi-coherent, being the kernel of a
surjection of quasi-coherent modules (Stacks 03M1). -/
theorem isQuasicoherentOnSite_of_mem {T : SchemesOver D.Y} {K : Subobject (D.baseChangeModule T)}
    (hK : K ∈ D.properlySupportedQuotients T) :
    SheafOfModules.IsQuasicoherentOnSite
      (K : Modules.{u, u} B S hS (D.space T).1 (D.space T).2) := by
  have : (D.kernelShortComplex T K).X₂.IsQuasicoherentOnSite :=
    isQuasicoherentOnSite_modulePullback_of_isQuasicoherentOnSite B S hS _ D.F D.quasicoherent
  have : (D.kernelShortComplex T K).X₃.IsQuasicoherentOnSite := hK.1.1.1
  exact isQuasicoherent_left_of_shortExact' _ (D.shortExact_kernelShortComplex T K)

/-- The kernel of a member of `Quot_{F/X/B}(T)` is of finite type when `F` is: it is the kernel of
a surjection from the finite type module `F_T` onto a module of finite presentation, which is
Stacks 082T. -/
theorem isFiniteTypeOnSite_of_mem (hF : SheafOfModules.IsFiniteTypeOnSite D.F)
    {T : SchemesOver D.Y} {K : Subobject (D.baseChangeModule T)}
    (hK : K ∈ D.properlySupportedQuotients T) :
    SheafOfModules.IsFiniteTypeOnSite (K : Modules.{u, u} B S hS (D.space T).1 (D.space T).2) := by
  have : ∀ (U : (smallEtaleRingedSite B S hS (D.space T).1 (D.space T).2).C)
      (N : _root_.SheafOfModules.{u} ((Stacks.SheafOfModules.Tensor.ringSheaf
        (smallEtaleRingedSite B S hS (D.space T).1 (D.space T).2).O).over U)),
      Small.{u, u + 1} N.sections :=
    fun _ N => _root_.SheafOfModules.small_sections_of_isTerminal Over.mkIdTerminal N
  exact Stacks.SheafOfModules.isFiniteTypeOnSite_X₁_of_shortExact_of_small
    (S := D.kernelShortComplex T K) (D.shortExact_kernelShortComplex T K)
    (isFiniteTypeOnSite_modulePullback B S hS _ D.F hF) hK.1.2

/-- A map `u : N ⟶ F_T/K` from a quasi-coherent `𝒪_{X_T}`-module to the quotient of a member of
`Quot_{F/X/B}(T)`, as the standing datum of Stacks 083F over the test scheme `T`. -/
def testSituation {T : SchemesOver D.Y} {K : Subobject (D.baseChangeModule T)}
    (hK : K ∈ D.properlySupportedQuotients T)
    {N : Modules.{u, u} B S hS (D.space T).1 (D.space T).2} (hN : N.IsQuasicoherentOnSite)
    (v : N ⟶ D.quotientModule T K) : ModuleMapSituation.{u, u} B S hS where
  X := D.space T
  Y := (schemeSpaceFunctor B S hS).obj T.left
  f := D.projection T
  F := N
  G := D.quotientModule T K
  quasicoherent_F := hN
  quasicoherent_G := hK.1.1.1
  u := v

/-- The comparison `X_{T'} ≅ X_T ×_T T'` of the base change of the situation along a morphism
`t : T' ⟶ T` of test schemes with the base change of the datum
`AlgebraicGeometry.Space.QuotSituation.testSituation` along the underlying morphism of schemes. -/
def testSchemeSpaceIso {T : SchemesOver D.Y}
    {K : Subobject (D.baseChangeModule T)} (hK : K ∈ D.properlySupportedQuotients T)
    {N : Modules.{u, u} B S hS (D.space T).1 (D.space T).2} (hN : N.IsQuasicoherentOnSite)
    (v : N ⟶ D.quotientModule T K) {T' : SchemesOver D.Y} (t : T' ⟶ T) :
    D.space T' ≅ (D.testSituation hK hN v).baseChangeSpace
        (CostructuredArrow.mk ((schemeSpaceFunctor B S hS).map t.left)) :=
  IsPullback.isoIsPullback _ _ (isPullback_baseChangeMap D.f t)
    (AlgebraicSpaces.isPullback_fiberProduct B S hS (D.projection T)
      ((schemeSpaceFunctor B S hS).map t.left))

/-- The comparison `X_{T'} ≅ X_T ×_T T'` composed with the projection to `X_T` is the morphism
of base changes `X_{T'} ⟶ X_T`. -/
theorem testSchemeSpaceIso_hom_comp {T : SchemesOver D.Y}
    {K : Subobject (D.baseChangeModule T)} (hK : K ∈ D.properlySupportedQuotients T)
    {N : Modules.{u, u} B S hS (D.space T).1 (D.space T).2} (hN : N.IsQuasicoherentOnSite)
    (v : N ⟶ D.quotientModule T K) {T' : SchemesOver D.Y} (t : T' ⟶ T) :
    (D.testSchemeSpaceIso hK hN v t).hom ≫ (D.testSituation hK hN v).baseChangeProjection
        (CostructuredArrow.mk ((schemeSpaceFunctor B S hS).map t.left)) = D.relativeMap t :=
  IsPullback.isoIsPullback_hom_fst _ _ _ _

/-- **The pullback along `X_{T'} ⟶ X_T` vanishes exactly at the zero locus of Stacks 083F.** For a
morphism `t : T' ⟶ T` of test schemes, the pullback of `v : N ⟶ F_T/K` along the morphism of base
changes `X_{T'} ⟶ X_T` vanishes exactly when `v` vanishes at the test scheme `t`. -/
theorem modulePullback_relativeMap_eq_zero_iff_isZeroAt {T : SchemesOver D.Y}
    {K : Subobject (D.baseChangeModule T)} (hK : K ∈ D.properlySupportedQuotients T)
    {N : Modules.{u, u} B S hS (D.space T).1 (D.space T).2} (hN : N.IsQuasicoherentOnSite)
    (v : N ⟶ D.quotientModule T K) {T' : SchemesOver D.Y} (t : T' ⟶ T) :
    (modulePullback B S hS (D.relativeMap t)).map v = 0 ↔
      (D.testSituation hK hN v).IsZeroAt (modulePullbackSystem B S hS)
        (CostructuredArrow.mk ((schemeSpaceFunctor B S hS).map t.left)) := by
  rw [← D.testSchemeSpaceIso_hom_comp hK hN v t]
  exact (modulePullbackSystem B S hS).map_eq_zero_isIso_comp_iff _ _ v

/-- **The zero locus of a map into a member of `Quot_{F/X/B}(T)`**, by Stacks 083M: for a
quasi-coherent `N` and `v : N ⟶ F_T/K` with `K ∈ Quot_{F/X/B}(T)`, the morphisms `t : T' ⟶ T` of
test schemes along which the pullback of `v` vanishes are those whose underlying morphism of
schemes factors through a closed subspace of `T`, of finite presentation when `N` is of finite
type. -/
theorem exists_isClosedSubspace_modulePullback_eq_zero_iff {T : SchemesOver D.Y}
    {K : Subobject (D.baseChangeModule T)} (hK : K ∈ D.properlySupportedQuotients T)
    {N : Modules.{u, u} B S hS (D.space T).1 (D.space T).2} (hN : N.IsQuasicoherentOnSite)
    (v : N ⟶ D.quotientModule T K) :
    ∃ Z : Subfunctor (yoneda.obj T.left), IsClosedSubspace B S hS Z ∧
      (SheafOfModules.IsFiniteTypeOnSite N → IsFinitePresentation B S hS Z.ι) ∧
      ∀ (T' : SchemesOver D.Y) (t : T' ⟶ T),
        (modulePullback B S hS (D.relativeMap t)).map v = 0 ↔
          ∃ k : yoneda.obj T'.left ⟶ Z.toFunctor, k ≫ Z.ι = yoneda.map t.left := by
  obtain ⟨Z, hZ, hZfp, hZloc⟩ :=
    (D.testSituation hK hN v).zeroLocusRepresentation_of_hasProperSupport
      ((isLocallyOfFinitePresentation_isStableUnderBaseChange B S hS).of_isPullback
        (AlgebraicSpaces.isPullback_fiberProduct B S hS D.f T.hom) D.finitePresentation.1)
      hK.1.2 hK.1.1.2 hK.2
  refine ⟨Z, hZ, hZfp, fun T' t => ?_⟩
  rw [D.modulePullback_relativeMap_eq_zero_iff_isZeroAt hK hN v t, hZloc]
  rfl

/-- **The locus where the pullback of one quotient is contained in that of another is a closed
subspace**: it is the zero locus of `K ⟶ F_T ⟶ F_T/K'`, of finite presentation when `F` is of
finite type. -/
theorem exists_isClosedSubspace_quotientPullback_le_iff {T : SchemesOver D.Y}
    {K K' : Subobject (D.baseChangeModule T)}
    (hK : K ∈ D.properlySupportedQuotients T) (hK' : K' ∈ D.properlySupportedQuotients T) :
    ∃ Z : Subfunctor (yoneda.obj T.left), IsClosedSubspace B S hS Z ∧
      (SheafOfModules.IsFiniteTypeOnSite D.F → IsFinitePresentation B S hS Z.ι) ∧
      ∀ (T' : BigFppfOver B S hS) (t : T' ⟶ T.left),
        D.quotientPullback (CostructuredArrow.homMk t rfl :
            CostructuredArrow.mk ((schemeSpaceFunctor B S hS).map t ≫ T.hom) ⟶ T) K ≤
          D.quotientPullback (CostructuredArrow.homMk t rfl :
            CostructuredArrow.mk ((schemeSpaceFunctor B S hS).map t ≫ T.hom) ⟶ T) K' ↔
          ∃ k : yoneda.obj T' ⟶ Z.toFunctor, k ≫ Z.ι = yoneda.map t := by
  obtain ⟨Z, hZ, hZfp, hZloc⟩ := D.exists_isClosedSubspace_modulePullback_eq_zero_iff hK'
    (D.isQuasicoherentOnSite_of_mem hK) (K.arrow ≫ D.quotientProjection T K')
  refine ⟨Z, hZ, fun hF => hZfp (D.isFiniteTypeOnSite_of_mem hF hK), fun T' t => ?_⟩
  rw [D.quotientPullback_le_quotientPullback_iff]
  exact hZloc (CostructuredArrow.mk ((schemeSpaceFunctor B S hS).map t ≫ T.hom))
    (CostructuredArrow.homMk t rfl)

/-! ### The locus where two quotients agree -/

/-- **The locus of a test scheme where two quotients agree**, for a property `Q` of morphisms of
the site stable under composition which every zero locus of Stacks 083M has relative to `yoneda`:
there is a morphism `s : V ⟶ T` with property `Q` through which a morphism `t : T' ⟶ T` factors
exactly when the two quotients agree after base change along `t`. -/
theorem exists_quotientPullback_eq_iff_of_presheaf (Q : MorphismProperty (BigFppfOver B S hS))
    [Q.IsStableUnderComposition] {T : SchemesOver D.Y}
    {K K' : Subobject (D.baseChangeModule T)}
    (hK : K ∈ D.properlySupportedQuotients T) (hK' : K' ∈ D.properlySupportedQuotients T)
    (hQ : ∀ Z : Subfunctor (yoneda.obj T.left), IsClosedSubspace B S hS Z →
      (SheafOfModules.IsFiniteTypeOnSite D.F → IsFinitePresentation B S hS Z.ι) → Q.presheaf Z.ι) :
    ∃ (V : BigFppfOver B S hS) (s : V ⟶ T.left), Q s ∧
      ∀ (T' : BigFppfOver B S hS) (t : T' ⟶ T.left),
        D.quotientPullback (CostructuredArrow.homMk t rfl :
            CostructuredArrow.mk ((schemeSpaceFunctor B S hS).map t ≫ T.hom) ⟶ T) K =
          D.quotientPullback (CostructuredArrow.homMk t rfl :
            CostructuredArrow.mk ((schemeSpaceFunctor B S hS).map t ≫ T.hom) ⟶ T) K' ↔
          ∃ r : T' ⟶ V, r ≫ s = t := by
  obtain ⟨Z₁, hZ₁, hZ₁fp, hZ₁loc⟩ := D.exists_isClosedSubspace_quotientPullback_le_iff hK hK'
  obtain ⟨Z₂, hZ₂, hZ₂fp, hZ₂loc⟩ := D.exists_isClosedSubspace_quotientPullback_le_iff hK' hK
  obtain ⟨V₁, s₁, hs₁, hV₁⟩ :=
    exists_forall_factorsThrough_iff_of_presheaf Q Z₁ (hQ Z₁ hZ₁ hZ₁fp)
  obtain ⟨V, s, hs, hV⟩ :=
    exists_forall_factorsThrough_iff_of_presheaf_inter Q s₁ hs₁ Z₂ (hQ Z₂ hZ₂ hZ₂fp)
  refine ⟨V, s, hs, fun T' t => ?_⟩
  rw [hV, hV₁, ← hZ₁loc, ← hZ₂loc]
  exact ⟨fun h => ⟨h.le, h.ge⟩, fun h => le_antisymm h.1 h.2⟩

/-! ### The diagonal -/

/-- **The equalizer locus of two points of `Quot_{F/X/B}`**, for a property `Q` of morphisms of
the site, stable under composition and contained in the monomorphisms, which every zero locus of
Stacks 083M over a scheme of the site has relative to `yoneda`: two `a`-valued points of the Quot
presheaf over the same point of `B` agree after restriction along `t : c ⟶ a` exactly when `t`
factors through a fixed monomorphism with property `Q`. -/
theorem exists_equalizerLocus_quotSitePresheaf (Q : MorphismProperty (BigFppfOver B S hS))
    [Q.IsStableUnderComposition]
    (hQmono : ∀ {V T : BigFppfOver B S hS} (s : V ⟶ T), Q s → Mono s)
    (hQ : ∀ (T : BigFppfOver B S hS) (Z : Subfunctor (yoneda.obj T)), IsClosedSubspace B S hS Z →
      (SheafOfModules.IsFiniteTypeOnSite D.F → IsFinitePresentation B S hS Z.ι) → Q.presheaf Z.ι)
    (a : BigFppfOver B S hS) (x y : D.quotSitePresheaf.obj (Opposite.op a))
    (hxy : D.quotSitePresheafToBase.app (Opposite.op a) x =
      D.quotSitePresheafToBase.app (Opposite.op a) y) :
    ∃ (b : BigFppfOver B S hS) (s : b ⟶ a), Mono s ∧ Q s ∧ ∀ (c : BigFppfOver B S hS) (t : c ⟶ a),
      D.quotSitePresheaf.map t.op x = D.quotSitePresheaf.map t.op y ↔ ∃ r : c ⟶ b, r ≫ s = t := by
  have hb : x.toBase = y.toBase :=
    ObjectProperty.hom_ext _ (yonedaEquiv.injective (congrArg ULift.down hxy))
  obtain ⟨xb, xK, xM⟩ := x
  obtain ⟨yb, yK, yM⟩ := y
  dsimp only at hb
  subst hb
  obtain ⟨V, s, hs, hloc⟩ := D.exists_quotientPullback_eq_iff_of_presheaf Q xM yM (hQ a)
  refine ⟨V, s, hQmono s hs, hs, fun c t => ?_⟩
  rw [← hloc c t]
  show QuotFamilyOver.baseChange t ⟨xb, xK, xM⟩ = QuotFamilyOver.baseChange t ⟨xb, yK, yM⟩ ↔ _
  exact ⟨fun h => by injection h, fun h => QuotFamilyOver.ext rfl (heq_of_eq h)⟩

/-- **The diagonal of `Quot_{F/X/B} ⟶ B` through equalizer loci**, for a property `Q` as in
`AlgebraicGeometry.Space.QuotSituation.exists_equalizerLocus_quotSitePresheaf` which respects
isomorphisms: the relative diagonal of the Quot presheaf over `B` has `Q` relative to
`uliftYoneda`. -/
theorem relative_diagonal_quotSitePresheafToBase_of (Q : MorphismProperty (BigFppfOver B S hS))
    [Q.RespectsIso] [Q.IsStableUnderComposition]
    (hQmono : ∀ {V T : BigFppfOver B S hS} (s : V ⟶ T), Q s → Mono s)
    (hQ : ∀ (T : BigFppfOver B S hS) (Z : Subfunctor (yoneda.obj T)), IsClosedSubspace B S hS Z →
      (SheafOfModules.IsFiniteTypeOnSite D.F → IsFinitePresentation B S hS Z.ι) → Q.presheaf Z.ι) :
    Q.relative uliftYoneda.{u + 1} (pullback.diagonal D.quotSitePresheafToBase) :=
  MorphismProperty.relative_pullbackDiagonal_of_equalizerLoci Q _
    (D.exists_equalizerLocus_quotSitePresheaf Q hQmono hQ)

/-- The diagonal of `Quot_{F/X/B} ⟶ B` is a closed immersion. If `F` is of finite type, then the
diagonal is a closed immersion of finite presentation.

The diagonal is that of the Quot presheaf of `Type (u + 1)` over the base, and being a closed
immersion (of finite presentation) is representability by closed immersions of schemes (locally
of finite presentation), read through `CategoryTheory.uliftYoneda`. -/
@[stacks 0DM2]
theorem diagonal_quotSitePresheafToBase :
    IsClosedImmersionULift.{u + 1} B S hS (pullback.diagonal D.quotSitePresheafToBase) ∧
      (SheafOfModules.IsFiniteTypeOnSite D.F →
        (closedImmersionFinitePresentation (B := B) (S := S) (hS := hS)).relative
          uliftYoneda.{u + 1} (pullback.diagonal D.quotSitePresheafToBase)) := by
  have _ : (MorphismProperty.inverseImage (@AlgebraicGeometry.IsClosedImmersion.{u})
      (BigFppfOver.toScheme B S hS)).RespectsIso := MorphismProperty.RespectsIso.inverseImage _ _
  exact ⟨D.relative_diagonal_quotSitePresheafToBase_of _
    (fun s hs => mono_of_isClosedImmersion_toScheme_map s hs)
    (fun _ Z hZ _ => presheaf_isClosedImmersion_of_isClosedSubspace Z hZ),
    fun hF => D.relative_diagonal_quotSitePresheafToBase_of _
      (fun s hs => mono_of_isClosedImmersion_toScheme_map s hs.1)
      (fun _ Z hZ hfp => presheaf_closedImmersionFinitePresentation_of_isClosedSubspace Z hZ
        (hfp hF))⟩

/-- The morphism `Quot_{F/X/B} ⟶ B` is separated: its diagonal is a closed immersion. -/
theorem isSeparatedULift_quotSitePresheafToBase :
    IsSeparatedULift.{u + 1} B S hS D.quotSitePresheafToBase :=
  D.diagonal_quotSitePresheafToBase.1

end QuotSituation

add_to_stacks 0DM3 "the separation clause: the diagonal of Quot over B is a closed immersion"
  AlgebraicGeometry.Space.QuotSituation.isSeparatedULift_quotSitePresheafToBase

end AlgebraicGeometry.Space

end
