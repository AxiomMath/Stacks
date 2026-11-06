module

public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.Trace.TraceFormulaUpToDimZero
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.Trace.FrobeniusTraceQuasiIso
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.Trace.ExactPushforwardTwistTrace
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.ConstructibleComplexes.EtaleModulesCtfDenseOpen
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.ConstructibleComplexes.EtaleModulesLocallyConstantTransport
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.ConstructibleComplexes.ConstructibleFlatShriek
public import StacksFrontier.AlgebraicGeometry.Variety.Curve.Defs
public import StacksFrontier.AlgebraicGeometry.Variety.Smooth.DenseSmoothOpen
public import StacksFrontier.AlgebraicGeometry.Variety.Geometrically.Reduced
public import StacksFrontier.AlgebraicGeometry.Properties.NormalCoproduct
public import StacksFrontier.AlgebraicGeometry.Descent.EtaleLocal.Normal
public import StacksFrontier.AlgebraicGeometry.NormalizationBaseChange.Normal

/-!
# Reduction of the trace formula in dimension at most one to smooth curves

Steps 1–3 of the proof of [Stacks, Tag 03UG], in their geometric form: the trace formula

`Tr(π_X^* | RΓ_c(X_k̄, K)) = ∑_{x ∈ X(k)} Tr(π_x | K_x̄)`

for every separated scheme `X` of finite type over a finite field `k` of dimension at most one,
every compactification and every `K ∈ D_ctf(X, Λ)` follows from the case of a smooth curve `U`
over `k` without rational points and a bounded complex `K` of sheaves which are locally constant
with finite projective values.

The reduction is a sequence of open and closed dévissages
(`Stacks.EtaleCohomology.canonicalTraceFormula_of_openClosed`) whose closed pieces have dimension
at most zero, where the trace formula holds by Step 2
(`Stacks.EtaleCohomology.traceFormulaUpToDim_zero`):
* `X` is replaced by its reduction (the open piece is empty);
* the reduced `X` by its dense open smooth locus, which exists as `k` is perfect (Tag 056V);
* the smooth locus by the complement of its finitely many rational points;
* that complement by a dense open on which a bounded complex of constructible flat sheaves
  representing `K` (Tag 03TT) has locally constant terms with finite projective values.
On the last open `O` the trace formula does not change when `K` is replaced by that complex
(`Stacks.EtaleCohomology.canonicalTraceFormula_iff_of_derivedIso_of_isEmpty`: there is no rational
point, and the left hand side only depends on `K` in the derived category). Finally `O` is smooth,
hence normal, so its irreducible components are open and closed; splitting off one irreducible
component at a time, every component of dimension one is a smooth curve without rational points,
and every other component has dimension zero.

The result is an intermediate lemma for [Stacks, Tag 03UG]: the curve case is an input.

## Main results

* `Stacks.EtaleCohomology.canonicalTraceFormula_iff_of_derivedIso_of_isEmpty`: without rational
  points, the trace formula only depends on the class of `K` in the derived category.
* `Stacks.EtaleCohomology.canonicalTraceFormula_of_isOpenImmersion_of_dimLEZero`: the trace formula
  on `X` from the trace formula on an open whose complement has dimension at most zero.
* `Stacks.EtaleCohomology.traceFormulaUpToDim_one_of_smoothCurve`: the reduction.

## References

* [Stacks Project, Tag 03UG](https://stacks.math.columbia.edu/tag/03UG), Steps 1–3.
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits
open AlgebraicGeometry AlgebraicGeometry.Scheme
open CategoryTheory.FilteredDerived Stacks.Frobenius

universe u

namespace Stacks.EtaleCohomology

attribute [local instance] HasDerivedCategory.standard moduleCat_hasLimitsOfSize
  SmallEtale.hasWeakSheafify_over_moduleCat_ring
  SmallEtale.isRightAdjoint_smallEtalePushforward_moduleCat_ring
  etaleModuleInverseImage_preservesFiniteLimits etaleModuleInverseImage_preservesFiniteColimits

section QuasiIso

variable (Λ : Type) [Ring Λ] [Finite Λ] {k : Type u} [Field k] [Fintype k]
  (kbar : Type u) [Field kbar] [IsAlgClosed kbar] [Algebra k kbar] (p q : ℕ) [Fact p.Prime]
  [CharP k p] [CharP kbar p] (hcard : Fintype.card k = p ^ q)

/-- **Without rational points, the trace formula is invariant under quasi-isomorphism.** The
right hand side is an empty sum, and the left hand side is computed from `j_! K`, which `j_!`
(an exact functor) carries to a quasi-isomorphic complex. -/
theorem canonicalTraceFormula_iff_of_quasiIso_of_isEmpty {X : Scheme.{u}}
    (f : X ⟶ Spec (.of k)) [IsEmpty (rationalPoints f)] (j : CompactificationOf (Over.mk f))
    {K₁ K₂ : CochainComplex.Plus (EtaleModules.{u, 0} Λ X)} (φ : K₁ ⟶ K₂) [QuasiIso φ.hom] :
    CanonicalTraceFormula Λ kbar p q hcard f j K₁ ↔
      CanonicalTraceFormula Λ kbar p q hcard f j K₂ := by
  let Φ := (etaleModuleExtensionByZero.{u, 0} Λ j.immersion).mapCochainComplexPlus.map φ
  have : QuasiIso Φ.hom := inferInstanceAs (QuasiIso
    (((etaleModuleExtensionByZero.{u, 0} Λ j.immersion).mapHomologicalComplex _).map φ.hom))
  have hiff := isPerfect_frobeniusRestriction_iff_of_quasiIso Λ (Over.mk j.toBase) kbar Φ
  have htr := perfectDerivedTrace_frobeniusRestrictionCohomologyEndo_eq_of_quasiIso_of_isPerfect Λ
    (Over.mk j.toBase) kbar p q hcard Φ
  constructor
  · rintro ⟨hX, _, h⟩
    refine ⟨hiff.1 hX, isEmptyElim, ?_⟩
    rw [finsum_of_isEmpty] at h ⊢
    exact (htr hX (hiff.1 hX)).symm.trans h
  · rintro ⟨hX, _, h⟩
    refine ⟨hiff.2 hX, isEmptyElim, ?_⟩
    rw [finsum_of_isEmpty] at h ⊢
    exact (htr (hiff.2 hX) hX).trans h

/-- **Without rational points, the trace formula only depends on the class of `K` in the derived
category.** Both complexes map by quasi-isomorphisms to a bounded below complex of injectives. -/
theorem canonicalTraceFormula_iff_of_derivedIso_of_isEmpty {X : Scheme.{u}}
    (f : X ⟶ Spec (.of k)) [IsEmpty (rationalPoints f)] (j : CompactificationOf (Over.mk f))
    {K₁ K₂ : CochainComplex.Plus (EtaleModules.{u, 0} Λ X)}
    (e : DerivedCategory.Q.obj K₁.obj ≅ DerivedCategory.Q.obj K₂.obj) :
    CanonicalTraceFormula Λ kbar p q hcard f j K₁ ↔
      CanonicalTraceFormula Λ kbar p q hcard f j K₂ := by
  have : EnoughInjectives (EtaleModules.{u, 0} Λ X) := etaleModules_enoughInjectives.{u, 0} Λ X
  obtain ⟨T, ψ, hψ, hT, -, -⟩ := Functor.exists_twist_lift_of_injectiveResolution
    (𝟭 (EtaleModules.{u, 0} Λ X)) K₂ (𝟙 _)
  obtain ⟨b, _⟩ := T.property
  have : ∀ m, Injective (T.obj.X m) := hT
  have : T.obj.IsKInjective := CochainComplex.isKInjective_of_injective T.obj b
  obtain ⟨φ, hφ⟩ := StacksDraft.DerivedHom.exists_eq_Q_map_of_isKInjective _ T.obj
    (e.hom ≫ DerivedCategory.Q.map ψ.hom)
  have : QuasiIso φ := (DerivedCategory.isIso_Q_map_iff_quasiIso _ φ).1 (hφ ▸ inferInstance)
  let Φ : K₁ ⟶ T := ObjectProperty.homMk φ
  have : QuasiIso Φ.hom := ‹QuasiIso φ›
  exact (canonicalTraceFormula_iff_of_quasiIso_of_isEmpty Λ kbar p q hcard f j Φ).trans
    (canonicalTraceFormula_iff_of_quasiIso_of_isEmpty Λ kbar p q hcard f j ψ).symm

end QuasiIso

section LocallyConstant

variable (B : BigEtaleSite.{u}) (Λ : Type) [Ring Λ]

/-- **Local constancy with finite projective values is preserved by inverse image**, for sheaves
on Mathlib's small étale sites of schemes of the big étale site, read on the small étale
sites of Stacks 021B. -/
theorem isFiniteProjectiveLocallyConstant_etaleModulesToSmallEtale_inverseImage {Y Z : B.Scheme}
    (i : Z.obj ⟶ Y.obj) (F : EtaleModules.{u, 0} Λ Y.obj)
    (hF : Stacks.ConstantSheaf.IsFiniteProjectiveLocallyConstant Λ
      (SmallEtale.topology B Y.obj Y.property) ((etaleModulesToSmallEtale B Y Λ).obj F)) :
    Stacks.ConstantSheaf.IsFiniteProjectiveLocallyConstant Λ
      (SmallEtale.topology B Z.obj Z.property)
      ((etaleModulesToSmallEtale B Z Λ).obj ((etaleModuleInverseImage.{u, 0} Λ i).obj F)) :=
  Stacks.ConstantSheaf.isFiniteProjectiveLocallyConstant_congr _ _
    (etaleModulesToSmallEtalePullbackIso B Λ (ObjectProperty.homMk i : Z ⟶ Y) F).symm
    (isFiniteProjectiveLocallyConstant_smallEtaleSheafPullback B Λ _ _ hF)

/-- **Local constancy with finite projective values is preserved by restriction to an open.** -/
theorem isFiniteProjectiveLocallyConstant_etaleModulesToSmallEtale_restriction {Y Z : B.Scheme}
    (i : Z.obj ⟶ Y.obj) [IsOpenImmersion i] (F : EtaleModules.{u, 0} Λ Y.obj)
    (hF : Stacks.ConstantSheaf.IsFiniteProjectiveLocallyConstant Λ
      (SmallEtale.topology B Y.obj Y.property) ((etaleModulesToSmallEtale B Y Λ).obj F)) :
    Stacks.ConstantSheaf.IsFiniteProjectiveLocallyConstant Λ
      (SmallEtale.topology B Z.obj Z.property)
      ((etaleModulesToSmallEtale B Z Λ).obj ((etaleModuleRestriction.{u, 0} Λ i).obj F)) :=
  Stacks.ConstantSheaf.isFiniteProjectiveLocallyConstant_congr _ _
    ((etaleModulesToSmallEtale B Z Λ).mapIso
      ((etaleModuleInverseImageRestrictionIso.{u, 0} Λ i).app F))
    (isFiniteProjectiveLocallyConstant_etaleModulesToSmallEtale_inverseImage B Λ i F hF)

end LocallyConstant

section Dimension

/-- A finite set of closed points has dimension at most zero: as a subspace it is finite and
`T₁`, hence discrete. -/
theorem topologicalKrullDim_le_zero_of_finite_of_isClosed {X : Type*} [TopologicalSpace X]
    {S : Set X} (hS : S.Finite) (hc : ∀ x ∈ S, IsClosed ({x} : Set X)) :
    topologicalKrullDim S ≤ 0 := by
  have : Finite S := hS.to_subtype
  have : T1Space S := ⟨fun x => by
    convert (hc x.1 x.2).preimage (continuous_subtype_val (p := (· ∈ S))) using 1
    ext y
    simp [Subtype.ext_iff]⟩
  exact topologicalKrullDim_zero_of_discreteTopology S

/-- In a Noetherian space of dimension at most one, the complement of a dense open has dimension
at most zero: it is closed and nowhere dense. -/
theorem topologicalKrullDim_compl_le_zero_of_dense {X : Type*} [TopologicalSpace X]
    [TopologicalSpace.NoetherianSpace X] (hX : topologicalKrullDim X ≤ 1) {V : Set X}
    (hV : IsOpen V) (hd : Dense V) : topologicalKrullDim (Vᶜ : Set X) ≤ 0 := by
  have hnd : IsNowhereDense (Vᶜ : Set X) := by
    rw [hV.isClosed_compl.isNowhereDense_iff, interior_compl, Set.compl_empty_iff]
    exact hd.closure_eq
  exact_mod_cast hnd.topologicalKrullDim_le_of_le_natCast_succ hV.isClosed_compl 0
    (by exact_mod_cast hX)

end Dimension

section Devissage

variable (B : BigEtaleSite.{u}) (Λ : Type) [Ring Λ] [Finite Λ] {k : Type u} [Field k] [Fintype k]
  (kbar : Type u) [Field kbar] [IsAlgClosed kbar] [Algebra k kbar] (p q : ℕ) [Fact p.Prime]
  [CharP k p] [CharP kbar p] (hcard : Fintype.card k = p ^ q)

/-- Every closed subset of a scheme of the big étale site is the range of a closed immersion
from a reduced scheme of the site (its reduced closed subscheme). -/
private theorem exists_isClosedImmersion_range_eq (X : B.Scheme)
    (C : TopologicalSpace.Closeds X.obj) :
    ∃ (Z : B.Scheme) (i : Z.obj ⟶ X.obj), IsClosedImmersion i ∧ IsReduced Z.obj ∧
      Set.range i.base = C := by
  let i := (Scheme.IdealSheafData.vanishingIdeal C).subschemeι
  exact ⟨⟨_, Scheme.size_lt_of_isClosedImmersion i X.property⟩, i, inferInstance, inferInstance,
    Scheme.IdealSheafData.range_subschemeι_vanishingIdeal C⟩

/-- **The trace formula from an open with a complement of dimension at most zero.** If the
trace formula holds on an open `U` of `X` whose complement has dimension at most zero, it holds
on `X`: on the reduced closed complement it holds by Step 2 of Tag 03UG
(`Stacks.EtaleCohomology.traceFormulaUpToDim_zero`), and the open and closed dévissage combines
the two. -/
theorem canonicalTraceFormula_of_isOpenImmersion_of_dimLEZero (X : B.Scheme)
    (f : X.obj ⟶ Spec (.of k)) [QuasiCompact f] [LocallyOfFiniteType f] [IsSeparated f]
    (j : CompactificationOf (Over.mk f)) (K : CochainComplex.Plus (EtaleModules.{u, 0} Λ X.obj))
    (hK : IsCtf B X Λ (DerivedCategory.Q.obj K.obj)) {U : Scheme.{u}} (jU : U ⟶ X.obj)
    [IsOpenImmersion jU] (hdim : topologicalKrullDim ((Set.range jU.base)ᶜ : Set X.obj) ≤ 0)
    (hU : CanonicalTraceFormula Λ kbar p q hcard (jU ≫ f) (j.restrictOpen jU)
      ((etaleModuleRestriction.{u, 0} Λ jU).mapCochainComplexPlus.obj K)) :
    CanonicalTraceFormula Λ kbar p q hcard f j K := by
  obtain ⟨Z, i, _, _, hrange⟩ := exists_isClosedImmersion_range_eq B X
    ⟨(Set.range jU.base)ᶜ, jU.isOpenEmbedding.isOpen_range.isClosed_compl⟩
  have : LocallyOfFiniteType i := instLocallyOfFiniteTypeOfIsClosedImmersion i
  have : LocallyOfFiniteType (i ≫ f) := locallyOfFiniteType_comp i f
  have hij : Set.range jU.base = (Set.range i.base)ᶜ := by
    rw [show Set.range i.base = (Set.range jU.base)ᶜ from hrange, compl_compl]
  have hZdim : topologicalKrullDim Z.obj ≤ ((0 : ℕ) : WithBot ℕ∞) :=
    (topologicalKrullDim_le_of_range_subset i _ hrange.le).trans (by exact_mod_cast hdim)
  exact canonicalTraceFormula_of_openClosed Λ kbar p q hcard j jU i hij K hU
    (traceFormulaUpToDim_zero B Λ kbar p q hcard Z (i ≫ f) hZdim (j.restrictClosed i) _
      (isCtf_inverseImage B Λ i Z.property _ _ hK))

end Devissage

/-- A scheme smooth over a field is normal. -/
theorem isNormal_of_smooth_of_field {k : Type u} [Field k] {Y : Scheme.{u}}
    (g : Y ⟶ Spec (.of k)) [Smooth g] : IsNormal Y :=
  have : IsNormal (Spec (.of k)) :=
    isNormal_spec_of_isNormalRing (IsNormalRing.of_isIntegrallyClosed k)
  isNormal_of_smooth g

section Components

/-- A space covered by finitely many irreducible open sets splits off an irreducible component:
there is an irreducible open and closed `W` whose complement is covered by fewer irreducible open
sets, each disjoint from `W`. Every irreducible open set of the cover lies in a single irreducible
component, so the component of a point is the union of the members of the cover meeting it. -/
theorem exists_isClopen_isIrreducible_of_finset_cover {X : Type*} [TopologicalSpace X]
    [Nonempty X] (s : Finset (Set X)) (hs : ∀ V ∈ s, IsOpen V ∧ IsIrreducible V)
    (hcov : ∀ x, ∃ V ∈ s, x ∈ V) :
    ∃ W : Set X, IsClopen W ∧ IsIrreducible W ∧ ∃ s' : Finset (Set X), s'.card < s.card ∧
      (∀ V ∈ s', IsOpen V ∧ IsIrreducible V) ∧ (∀ V ∈ s', V ⊆ Wᶜ) ∧
        ∀ x ∉ W, ∃ V ∈ s', x ∈ V := by
  classical
  obtain ⟨x⟩ := ‹Nonempty X›
  let W := irreducibleComponent x
  have hW : W ∈ irreducibleComponents X := irreducibleComponent_mem_irreducibleComponents x
  have key : ∀ V ∈ s, (V ∩ W).Nonempty → V ⊆ W := by
    intro V hV hVW
    obtain ⟨C, hC, hVC⟩ :=
      exists_mem_irreducibleComponents_subset_of_isIrreducible V (hs V hV).2
    obtain ⟨y, hy⟩ := (hs V hV).2.nonempty
    have hWC : W = C := component_eq_of_open_irreducible_nhd W C hW hC V (hs V hV).1 (hs V hV).2
      (by rwa [Set.inter_comm]) ⟨y, hVC hy, hy⟩
    exact hWC ▸ hVC
  have hWopen : IsOpen W := isOpen_iff_forall_mem_open.2 fun y hy => by
    obtain ⟨V, hV, hyV⟩ := hcov y
    exact ⟨V, key V hV ⟨y, hyV, hy⟩, (hs V hV).1, hyV⟩
  refine ⟨W, ⟨isClosed_of_mem_irreducibleComponents W hW, hWopen⟩, hW.1,
    s.filter (fun V => V ⊆ Wᶜ), ?_, fun V hV => hs V (Finset.mem_filter.1 hV).1,
    fun V hV => (Finset.mem_filter.1 hV).2, fun y hy => ?_⟩
  · obtain ⟨V₀, hV₀, hxV₀⟩ := hcov x
    exact Finset.card_lt_card (Finset.filter_ssubset.2
      ⟨V₀, hV₀, fun h => h hxV₀ mem_irreducibleComponent⟩)
  · obtain ⟨V, hV, hyV⟩ := hcov y
    exact ⟨V, Finset.mem_filter.2 ⟨hV, fun z hz hzW => hy (key V hV ⟨z, hz, hzW⟩ hyV)⟩, hyV⟩

/-- A scheme smooth over a field whose underlying space is Noetherian is covered by finitely
many irreducible open subsets: it is normal, hence a finite disjoint union of integral schemes
(Tag 033M). -/
theorem exists_finset_cover_isOpen_isIrreducible_of_smooth {k : Type u} [Field k]
    {Y : Scheme.{u}} (g : Y ⟶ Spec (.of k)) [Smooth g] [IsNoetherian Y] :
    ∃ s : Finset (Set Y), (∀ V ∈ s, IsOpen V ∧ IsIrreducible V) ∧ ∀ x, ∃ V ∈ s, x ∈ V := by
  classical
  have : IsNormal Y := isNormal_of_smooth_of_field g
  obtain ⟨ι, _, Yi, -, hint, ⟨e⟩⟩ :=
    (isNormal_iff_exists_iso_finite_coproduct_integral_normal Y).1 inferInstance
  let : Fintype ι := Fintype.ofFinite ι
  refine ⟨Finset.univ.image fun i => Set.range (Sigma.ι Yi i ≫ e.inv).base, ?_, fun x => ?_⟩
  · intro V hV
    obtain ⟨i, -, rfl⟩ := Finset.mem_image.1 hV
    have : IsIntegral (Yi i) := hint i
    refine ⟨(Sigma.ι Yi i ≫ e.inv).isOpenEmbedding.isOpen_range, ?_⟩
    rw [← Set.image_univ]
    exact (IrreducibleSpace.isIrreducible_univ (Yi i)).image _
      (Sigma.ι Yi i ≫ e.inv).continuous.continuousOn
  · obtain ⟨⟨i, y⟩, hy⟩ := (sigmaMk Yi).surjective (e.hom x)
    refine ⟨_, Finset.mem_image.2 ⟨i, Finset.mem_univ _, rfl⟩, y, ?_⟩
    rw [sigmaMk_mk] at hy
    rw [Scheme.Hom.comp_apply, hy, ← Scheme.Hom.comp_apply, e.hom_inv_id]
    rfl

/-- An open subscheme whose underlying set is irreducible is an irreducible space. -/
theorem irreducibleSpace_toScheme_of_isIrreducible {X : Scheme.{u}} (U : X.Opens)
    (hU : IsIrreducible (U : Set X)) : IrreducibleSpace U.toScheme := by
  refine (irreducibleSpace_def _).2 ?_
  have h := hU.preimage U.ι.isOpenEmbedding (by
    obtain ⟨y, hy⟩ := hU.nonempty
    exact ⟨y, hy, (Scheme.Opens.range_ι U).symm.subset hy⟩)
  have huniv : U.ι.base ⁻¹' U = Set.univ := by
    rw [← Set.preimage_range U.ι.base, Scheme.Opens.range_ι]
  rwa [huniv] at h

/-- A finite cover of an open `U` by irreducible open sets contained in `U` pulls back to a finite
cover of the open subscheme `U` by irreducible open sets. -/
theorem isOpen_isIrreducible_image_preimage_ι {X : Scheme.{u}} (U : X.Opens)
    [DecidableEq (Set U.toScheme)] (s : Finset (Set X)) (hs : ∀ V ∈ s, IsOpen V ∧ IsIrreducible V)
    (hsU : ∀ V ∈ s, V ⊆ U) (hcov : ∀ x ∈ U, ∃ V ∈ s, x ∈ V) :
    (∀ V ∈ s.image (U.ι.base ⁻¹' ·), IsOpen V ∧ IsIrreducible V) ∧
      ∀ x, ∃ V ∈ s.image (U.ι.base ⁻¹' ·), x ∈ V := by
  refine ⟨fun V hV => ?_, fun z => ?_⟩
  · obtain ⟨V, hV', rfl⟩ := Finset.mem_image.1 hV
    refine ⟨(hs V hV').1.preimage U.ι.continuous, (hs V hV').2.preimage U.ι.isOpenEmbedding ?_⟩
    obtain ⟨y, hy⟩ := (hs V hV').2.nonempty
    exact ⟨y, hy, (Scheme.Opens.range_ι U).symm.subset (hsU V hV' hy)⟩
  · obtain ⟨V, hV, hzV⟩ := hcov _ ((Scheme.Opens.range_ι U).subset (Set.mem_range_self z))
    exact ⟨_, Finset.mem_image.2 ⟨V, hV, rfl⟩, hzV⟩

end Components

section RationalPoints

/-- A scheme of finite type over a field is locally Noetherian and Noetherian. -/
private theorem isLocallyNoetherian_and_isNoetherian_of_finiteType {k : Type u} [Field k]
    {Y : Scheme.{u}} (g : Y ⟶ Spec (.of k)) [QuasiCompact g] [LocallyOfFiniteType g] :
    IsLocallyNoetherian Y ∧ IsNoetherian Y :=
  have : IsLocallyNoetherian Y := LocallyOfFiniteType.isLocallyNoetherian g
  have : CompactSpace Y := QuasiCompact.compactSpace_of_compactSpace g
  ⟨inferInstance, ⟨⟩⟩

/-- Without rational points on `Y`, there are none on a scheme over `Y`. -/
theorem isEmpty_rationalPoints_comp {k : Type u} [Field k] {U Y : Scheme.{u}} (i : U ⟶ Y)
    (g : Y ⟶ Spec (.of k)) [IsEmpty (rationalPoints g)] : IsEmpty (rationalPoints (i ≫ g)) :=
  ⟨fun y => isEmptyElim (α := rationalPoints g) ⟨y.1 ≫ i, (Category.assoc _ _ _).trans y.2⟩⟩

/-- On a separated scheme over a field, the image of a rational point is closed. -/
theorem isClosed_range_of_rationalPoints {k : Type u} [Field k] {Y : Scheme.{u}}
    {g : Y ⟶ Spec (.of k)} [IsSeparated g] (x : rationalPoints g) :
    IsClosed (Set.range x.1.base) := by
  have : IsClosedImmersion (x.1 ≫ g) := by
    rw [x.2]
    infer_instance
  have : IsClosedImmersion x.1 := IsClosedImmersion.of_comp x.1 g
  exact x.1.isClosedEmbedding.isClosed_range

end RationalPoints

section Bounds

variable {C D : Type*} [Category* C] [Category* D] [HasZeroMorphisms C] [HasZeroMorphisms D]

/-- A functor preserving zero morphisms preserves strict lower bounds of cochain complexes. -/
theorem isStrictlyGE_mapHomologicalComplex_of_preservesZeroMorphisms (F : C ⥤ D)
    [F.PreservesZeroMorphisms] (K : CochainComplex C ℤ) (n : ℤ) [K.IsStrictlyGE n] :
    CochainComplex.IsStrictlyGE ((F.mapHomologicalComplex (ComplexShape.up ℤ)).obj K) n := by
  rw [CochainComplex.isStrictlyGE_iff]
  exact fun i hi => F.map_isZero (K.isZero_of_isStrictlyGE n i hi)

/-- A functor preserving zero morphisms preserves strict upper bounds of cochain complexes. -/
theorem isStrictlyLE_mapHomologicalComplex_of_preservesZeroMorphisms (F : C ⥤ D)
    [F.PreservesZeroMorphisms] (K : CochainComplex C ℤ) (n : ℤ) [K.IsStrictlyLE n] :
    CochainComplex.IsStrictlyLE ((F.mapHomologicalComplex (ComplexShape.up ℤ)).obj K) n := by
  rw [CochainComplex.isStrictlyLE_iff]
  exact fun i hi => F.map_isZero (K.isZero_of_isStrictlyLE n i hi)

end Bounds

section SmoothCurve

variable (B : BigEtaleSite.{u}) (Λ : Type) [Ring Λ] [Finite Λ] {k : Type u} [Field k] [Fintype k]
  (kbar : Type u) [Field kbar] [IsAlgClosed kbar] [Algebra k kbar] (p q : ℕ) [Fact p.Prime]
  [CharP k p] [CharP kbar p] (hcard : Fintype.card k = p ^ q)

/-- **The core case of the trace formula in dimension one**: for every smooth curve `U` over `k`
in `B` without rational points, every compactification of `U` and every bounded complex `K` of
sheaves of `Λ`-modules on `U_étale` which are locally constant with finite projective values,
the trace formula holds. This is the input of the reduction of this file. -/
def SmoothCurveTraceFormula : Prop :=
  ∀ (U : B.Scheme) (pU : U.obj ⟶ Spec (.of k)) [IsCurve k pU] [Smooth pU]
    [IsEmpty (rationalPoints pU)] (J : CompactificationOf (Over.mk pU))
    (K : CochainComplex.Plus (EtaleModules.{u, 0} Λ U.obj)) (a b : ℤ) [K.obj.IsStrictlyGE a]
    [K.obj.IsStrictlyLE b],
    (∀ n, Stacks.ConstantSheaf.IsFiniteProjectiveLocallyConstant Λ U.obj.smallEtaleTopology
      (K.obj.X n)) → CanonicalTraceFormula Λ kbar p q hcard pU J K

variable {B Λ kbar p q hcard}

/-- **The trace formula on an irreducible smooth scheme without rational points**, of dimension
at most one, for a bounded complex with locally constant terms with finite projective values: in
dimension zero it is Step 2, in dimension one the scheme is a smooth curve. -/
theorem canonicalTraceFormula_of_irreducibleSpace_of_smooth
    (hcore : SmoothCurveTraceFormula B Λ kbar p q hcard) (Y : B.Scheme)
    (g : Y.obj ⟶ Spec (.of k)) [QuasiCompact g] [LocallyOfFiniteType g] [IsSeparated g]
    [Smooth g] [IsEmpty (rationalPoints g)] [IrreducibleSpace Y.obj]
    (hY : topologicalKrullDim Y.obj ≤ 1) (j : CompactificationOf (Over.mk g))
    (C : CochainComplex.Plus (EtaleModules.{u, 0} Λ Y.obj)) (a b : ℤ) [C.obj.IsStrictlyGE a]
    [C.obj.IsStrictlyLE b]
    (hC : ∀ n, Stacks.ConstantSheaf.IsFiniteProjectiveLocallyConstant Λ
      (SmallEtale.topology B Y.obj Y.property) ((etaleModulesToSmallEtale B Y Λ).obj (C.obj.X n)))
    (hCtf : IsCtf B Y Λ (DerivedCategory.Q.obj C.obj)) :
    CanonicalTraceFormula Λ kbar p q hcard g j C := by
  by_cases h0 : topologicalKrullDim Y.obj ≤ 0
  · exact traceFormulaUpToDim_zero B Λ kbar p q hcard Y g (by exact_mod_cast h0) j C hCtf
  have h1 : topologicalKrullDim Y.obj = 1 := by
    refine le_antisymm hY ?_
    induction h : topologicalKrullDim Y.obj using WithBot.recBotCoe with
    | bot => exact absurd (h ▸ bot_le) h0
    | coe d =>
      rw [h] at h0
      have hd : d ≠ 0 := by
        rintro rfl
        exact h0 le_rfl
      exact_mod_cast Order.one_le_iff_ne_zero.2 hd
  have : IsNormal Y.obj := isNormal_of_smooth_of_field g
  have : IsIntegral Y.obj := isIntegral_of_irreducibleSpace_of_isReduced Y.obj
  have : IsCurve k g := { topologicalKrullDim_eq_one := h1 }
  exact hcore Y g j C a b fun n =>
    (isFiniteProjectiveLocallyConstant_etaleModulesToSmallEtale_iff B Y Λ _).1 (hC n)

/-- **The trace formula on the empty scheme**, which has dimension at most zero. -/
theorem canonicalTraceFormula_of_isEmpty (Y : B.Scheme) (g : Y.obj ⟶ Spec (.of k))
    [QuasiCompact g] [LocallyOfFiniteType g] [IsSeparated g] [IsEmpty Y.obj]
    (j : CompactificationOf (Over.mk g)) (C : CochainComplex.Plus (EtaleModules.{u, 0} Λ Y.obj))
    (hCtf : IsCtf B Y Λ (DerivedCategory.Q.obj C.obj)) :
    CanonicalTraceFormula Λ kbar p q hcard g j C := by
  have : IsEmpty (TopologicalSpace.IrreducibleCloseds Y.obj) :=
    ⟨fun Z => isEmptyElim Z.isIrreducible.nonempty.some⟩
  have h0 : topologicalKrullDim Y.obj ≤ ((0 : ℕ) : WithBot ℕ∞) := by
    rw [topologicalKrullDim, Order.krullDim_eq_bot]
    exact bot_le
  exact traceFormulaUpToDim_zero B Λ kbar p q hcard Y g h0 j C hCtf

/-- **Splitting off the irreducible components.** The trace formula holds on a smooth scheme
without rational points, of dimension at most one and covered by finitely many irreducible open
sets, for a bounded complex with locally constant terms with finite projective values. By
induction on the size of the cover: an irreducible component `W` is open and closed, the trace
formula holds on `W` by `canonicalTraceFormula_of_irreducibleSpace_of_smooth` and on its
complement by induction, and the open and closed dévissage combines the two. -/
theorem canonicalTraceFormula_of_smooth_of_finset_cover
    (hcore : SmoothCurveTraceFormula B Λ kbar p q hcard) (n : ℕ) :
    ∀ (Y : B.Scheme) (g : Y.obj ⟶ Spec (.of k)) [QuasiCompact g] [LocallyOfFiniteType g]
      [IsSeparated g] [Smooth g] [IsEmpty (rationalPoints g)],
      topologicalKrullDim Y.obj ≤ 1 → ∀ s : Finset (Set Y.obj), s.card ≤ n →
      (∀ V ∈ s, IsOpen V ∧ IsIrreducible V) → (∀ x, ∃ V ∈ s, x ∈ V) →
      ∀ (j : CompactificationOf (Over.mk g))
        (C : CochainComplex.Plus (EtaleModules.{u, 0} Λ Y.obj)) (a b : ℤ) [C.obj.IsStrictlyGE a]
        [C.obj.IsStrictlyLE b],
        (∀ n, Stacks.ConstantSheaf.IsFiniteProjectiveLocallyConstant Λ
          (SmallEtale.topology B Y.obj Y.property)
            ((etaleModulesToSmallEtale B Y Λ).obj (C.obj.X n))) →
        IsCtf B Y Λ (DerivedCategory.Q.obj C.obj) →
        CanonicalTraceFormula Λ kbar p q hcard g j C := by
  induction n with
  | zero =>
    intro Y g _ _ _ _ _ _ s hs _ hcov j C _ _ _ _ _ hCtf
    obtain rfl := Finset.card_eq_zero.1 (Nat.le_zero.1 hs)
    have : IsEmpty Y.obj := ⟨fun x => by simpa using hcov x⟩
    exact canonicalTraceFormula_of_isEmpty Y g j C hCtf
  | succ n ih =>
    intro Y g _ _ _ _ _ hY s hs hsV hcov j C a b _ _ hC hCtf
    rcases isEmpty_or_nonempty Y.obj with _ | _
    · exact canonicalTraceFormula_of_isEmpty Y g j C hCtf
    obtain ⟨W, hWc, hWi, s', hcard', hs'V, hs'W, hcov'⟩ :=
      exists_isClopen_isIrreducible_of_finset_cover s hsV hcov
    have : IsLocallyNoetherian Y.obj := LocallyOfFiniteType.isLocallyNoetherian g
    let VW : Y.obj.Opens := ⟨W, hWc.isOpen⟩
    let VZ : Y.obj.Opens := ⟨Wᶜ, hWc.isClosed.isOpen_compl⟩
    have : IsClosedImmersion VZ.ι := .of_isPreimmersion _ (by
      rw [Scheme.Opens.range_ι]
      exact hWc.isOpen.isClosed_compl)
    have hij : Set.range VW.ι.base = (Set.range VZ.ι.base)ᶜ := by
      rw [Scheme.Opens.range_ι, Scheme.Opens.range_ι]
      exact (compl_compl W).symm
    have hUB : B.Contains VW.toScheme := Scheme.size_lt_of_isOpenImmersion VW.ι Y.property
    have hZB : B.Contains VZ.toScheme := Scheme.size_lt_of_isOpenImmersion VZ.ι Y.property
    have := isEmpty_rationalPoints_comp VW.ι g
    have := isEmpty_rationalPoints_comp VZ.ι g
    have := irreducibleSpace_toScheme_of_isIrreducible VW hWi
    let FU := etaleModuleRestriction.{u, 0} Λ VW.ι
    let FZ := etaleModuleInverseImage.{u, 0} Λ VZ.ι
    have : ((FU.mapCochainComplexPlus.obj C).obj).IsStrictlyGE a :=
      isStrictlyGE_mapHomologicalComplex_of_preservesZeroMorphisms FU C.obj a
    have : ((FU.mapCochainComplexPlus.obj C).obj).IsStrictlyLE b :=
      isStrictlyLE_mapHomologicalComplex_of_preservesZeroMorphisms FU C.obj b
    have : ((FZ.mapCochainComplexPlus.obj C).obj).IsStrictlyGE a :=
      isStrictlyGE_mapHomologicalComplex_of_preservesZeroMorphisms FZ C.obj a
    have : ((FZ.mapCochainComplexPlus.obj C).obj).IsStrictlyLE b :=
      isStrictlyLE_mapHomologicalComplex_of_preservesZeroMorphisms FZ C.obj b
    refine canonicalTraceFormula_of_openClosed Λ kbar p q hcard j VW.ι VZ.ι hij C ?_ ?_
    · exact canonicalTraceFormula_of_irreducibleSpace_of_smooth hcore ⟨VW.toScheme, hUB⟩
        (VW.ι ≫ g) (VW.ι.isOpenEmbedding.isInducing.topologicalKrullDim_le.trans hY) _ _ a b
        (fun m => isFiniteProjectiveLocallyConstant_etaleModulesToSmallEtale_restriction B Λ
          (Z := ⟨VW.toScheme, hUB⟩) VW.ι _ (hC m))
        (isCtf_restriction hUB VW.ι hCtf)
    · obtain ⟨hV, hcovV⟩ := isOpen_isIrreducible_image_preimage_ι VZ s' hs'V hs'W hcov'
      exact ih ⟨VZ.toScheme, hZB⟩ (VZ.ι ≫ g)
        (VZ.ι.isOpenEmbedding.isInducing.topologicalKrullDim_le.trans hY) _
        (Nat.lt_succ_iff.1 ((Finset.card_image_le).trans_lt (hcard'.trans_le hs))) hV hcovV _ _ a b
        (fun m => isFiniteProjectiveLocallyConstant_etaleModulesToSmallEtale_inverseImage B Λ
          (Z := ⟨VZ.toScheme, hZB⟩) VZ.ι _ (hC m))
        (isCtf_inverseImage B Λ VZ.ι hZB _ _ hCtf)

/-- **Step 3 of Tag 03UG on a smooth scheme without rational points.** By Tag 03TT, `K` is
represented by a bounded complex `C` of constructible flat sheaves; on a dense open `O` the terms
of `C` are locally constant with finite projective values, and as `O` has no rational point the
trace formula for `K|_O` is that for `C|_O`, which holds by
`canonicalTraceFormula_of_smooth_of_finset_cover`. The complement of `O` has dimension at most
zero. -/
theorem canonicalTraceFormula_of_smooth_of_isEmpty
    (hcore : SmoothCurveTraceFormula B Λ kbar p q hcard) (Y : B.Scheme)
    (g : Y.obj ⟶ Spec (.of k)) [QuasiCompact g] [LocallyOfFiniteType g] [IsSeparated g]
    [Smooth g] [IsEmpty (rationalPoints g)] (hY : topologicalKrullDim Y.obj ≤ 1)
    (j : CompactificationOf (Over.mk g)) (K : CochainComplex.Plus (EtaleModules.{u, 0} Λ Y.obj))
    (hK : IsCtf B Y Λ (DerivedCategory.Q.obj K.obj)) :
    CanonicalTraceFormula Λ kbar p q hcard g j K := by
  obtain ⟨_, _⟩ := isLocallyNoetherian_and_isNoetherian_of_finiteType g
  have : IsNormal Y.obj := isNormal_of_smooth_of_field g
  obtain ⟨C, a, b, ha, hb, hCf, ⟨eC⟩⟩ := (isCtf_iff_of_qcqs B Λ _).1 hK
  obtain ⟨O, o, ho, hdO, hnice⟩ :=
    exists_dense_isOpenImmersion_isFiniteProjectiveLocallyConstant_of_complex B Λ Y C a b ha hb
      hCf
  let jO : O.obj ⟶ Y.obj := B.inclusion.map o
  have : IsOpenImmersion jO := ho
  refine canonicalTraceFormula_of_isOpenImmersion_of_dimLEZero B Λ kbar p q hcard Y g j K hK jO
    (topologicalKrullDim_compl_le_zero_of_dense hY jO.isOpenEmbedding.isOpen_range hdO) ?_
  have := isEmpty_rationalPoints_comp jO g
  let F := etaleModuleInverseImage.{u, 0} Λ jO
  let Cp : CochainComplex.Plus (EtaleModules.{u, 0} Λ Y.obj) := ⟨C, a, ha⟩
  let CO := F.mapCochainComplexPlus.obj Cp
  let e : DerivedCategory.Q.obj CO.obj ≅ DerivedCategory.Q.obj
      ((etaleModuleRestriction.{u, 0} Λ jO).mapCochainComplexPlus.obj K).obj :=
    (F.mapDerivedCategoryFactors.app C).symm ≪≫ F.mapDerivedCategory.mapIso eC ≪≫
      F.mapDerivedCategoryFactors.app K.obj ≪≫
      DerivedCategory.Q.mapIso ((NatIso.mapHomologicalComplex
        (etaleModuleInverseImageRestrictionIso.{u, 0} Λ jO) (ComplexShape.up ℤ)).app K.obj)
  refine (canonicalTraceFormula_iff_of_derivedIso_of_isEmpty Λ kbar p q hcard (jO ≫ g) _ e).1 ?_
  have : CochainComplex.IsStrictlyGE CO.obj a :=
    isStrictlyGE_mapHomologicalComplex_of_preservesZeroMorphisms F C a
  have : CochainComplex.IsStrictlyLE CO.obj b :=
    isStrictlyLE_mapHomologicalComplex_of_preservesZeroMorphisms F C b
  obtain ⟨_, _⟩ := isLocallyNoetherian_and_isNoetherian_of_finiteType (jO ≫ g)
  obtain ⟨s, hs, hcov⟩ := exists_finset_cover_isOpen_isIrreducible_of_smooth (jO ≫ g)
  exact canonicalTraceFormula_of_smooth_of_finset_cover hcore s.card O (jO ≫ g)
    (jO.isOpenEmbedding.isInducing.topologicalKrullDim_le.trans hY) s le_rfl hs hcov _ CO a b
    hnice ((isCtf_restriction O.property jO hK).of_iso B _ Λ e.symm)

/-- **The trace formula on a smooth scheme of dimension at most one.** Its rational points are
finitely many closed points; on their complement the trace formula holds by
`canonicalTraceFormula_of_smooth_of_isEmpty`. -/
theorem canonicalTraceFormula_of_smooth
    (hcore : SmoothCurveTraceFormula B Λ kbar p q hcard) (Y : B.Scheme)
    (g : Y.obj ⟶ Spec (.of k)) [QuasiCompact g] [LocallyOfFiniteType g] [IsSeparated g]
    [Smooth g] (hY : topologicalKrullDim Y.obj ≤ 1)
    (j : CompactificationOf (Over.mk g)) (K : CochainComplex.Plus (EtaleModules.{u, 0} Λ Y.obj))
    (hK : IsCtf B Y Λ (DerivedCategory.Q.obj K.obj)) :
    CanonicalTraceFormula Λ kbar p q hcard g j K := by
  classical
  have : Finite (rationalPoints g) := finite_rationalPoints g
  have : Subsingleton (Spec (.of k)) := inferInstanceAs (Subsingleton (PrimeSpectrum k))
  have : Nonempty (Spec (.of k)) := inferInstanceAs (Nonempty (PrimeSpectrum k))
  have : IsLocallyNoetherian Y.obj := LocallyOfFiniteType.isLocallyNoetherian g
  let R : Set Y.obj := ⋃ x : rationalPoints g, Set.range x.1.base
  have hRc : ∀ y ∈ R, IsClosed ({y} : Set Y.obj) := by
    intro y hy
    obtain ⟨x, z, rfl⟩ := Set.mem_iUnion.1 hy
    convert isClosed_range_of_rationalPoints x using 1
    ext w
    constructor
    · rintro rfl
      exact ⟨z, rfl⟩
    · rintro ⟨z', rfl⟩
      rw [Subsingleton.elim z' z]
      rfl
  let V : Y.obj.Opens :=
    ⟨Rᶜ, (isClosed_iUnion_of_finite isClosed_range_of_rationalPoints).isOpen_compl⟩
  have hVB : B.Contains V.toScheme := Scheme.size_lt_of_isOpenImmersion V.ι Y.property
  refine canonicalTraceFormula_of_isOpenImmersion_of_dimLEZero B Λ kbar p q hcard Y g j K hK V.ι
    ?_ ?_
  · rw [Scheme.Opens.range_ι]
    change topologicalKrullDim ((Rᶜ)ᶜ : Set Y.obj) ≤ 0
    rw [compl_compl]
    exact topologicalKrullDim_le_zero_of_finite_of_isClosed
      (Set.finite_iUnion fun x => Set.finite_range _) hRc
  have : IsEmpty (rationalPoints (V.ι ≫ g)) := ⟨fun y => by
    obtain ⟨z⟩ := ‹Nonempty (Spec (.of k))›
    have h1 : V.ι.base (y.1.base z) ∈ R := Set.mem_iUnion.2
      ⟨⟨y.1 ≫ V.ι, (Category.assoc _ _ _).trans y.2⟩, z, Scheme.Hom.comp_apply y.1 V.ι z⟩
    exact (Scheme.Opens.range_ι V).subset (Set.mem_range_self (y.1.base z)) h1⟩
  exact canonicalTraceFormula_of_smooth_of_isEmpty hcore ⟨V.toScheme, hVB⟩ (V.ι ≫ g)
    (V.ι.isOpenEmbedding.isInducing.topologicalKrullDim_le.trans hY) _ _
    (isCtf_restriction hVB V.ι hK)

/-- **The trace formula on a reduced scheme of dimension at most one.** The field `k` is finite,
hence perfect, so the reduced `X` is geometrically reduced and its smooth locus is a dense open
(Tag 056V), on which the trace formula holds by `canonicalTraceFormula_of_smooth`. -/
theorem canonicalTraceFormula_of_isReduced
    (hcore : SmoothCurveTraceFormula B Λ kbar p q hcard) (X : B.Scheme)
    (f : X.obj ⟶ Spec (.of k)) [QuasiCompact f] [LocallyOfFiniteType f] [IsSeparated f]
    [IsReduced X.obj] (hX : topologicalKrullDim X.obj ≤ 1)
    (j : CompactificationOf (Over.mk f)) (K : CochainComplex.Plus (EtaleModules.{u, 0} Λ X.obj))
    (hK : IsCtf B X Λ (DerivedCategory.Q.obj K.obj)) :
    CanonicalTraceFormula Λ kbar p q hcard f j K := by
  obtain ⟨_, _⟩ := isLocallyNoetherian_and_isNoetherian_of_finiteType f
  obtain ⟨V, hd, hsm⟩ :=
    (geometricallyReduced_iff_exists_dense_open_smooth f).1 (geometricallyReduced_of_isReduced f)
  have hVB : B.Contains V.toScheme := Scheme.size_lt_of_isOpenImmersion V.ι X.property
  refine canonicalTraceFormula_of_isOpenImmersion_of_dimLEZero B Λ kbar p q hcard X f j K hK V.ι
    ?_ (canonicalTraceFormula_of_smooth hcore ⟨V.toScheme, hVB⟩ (V.ι ≫ f)
      (V.ι.isOpenEmbedding.isInducing.topologicalKrullDim_le.trans hX) _ _
      (isCtf_restriction hVB V.ι hK))
  rw [Scheme.Opens.range_ι]
  exact topologicalKrullDim_compl_le_zero_of_dense hX V.isOpen hd

/-- **The trace formula in dimension at most one, from smooth curves without rational points.**
If the trace formula holds for every smooth curve `U` over `k` in `B` without rational points,
every compactification of `U` and every bounded complex of sheaves of `Λ`-modules on `U_étale`
which are locally constant with finite projective values, then it holds for every separated
scheme `X` of finite type over `k` in `B` of dimension at most one, every compactification of
`X` and every `K ∈ D_ctf(X, Λ)` (Steps 1–3 of Tag 03UG). The open and closed dévissage along the
empty open and the reduction `X_red` (with the same underlying space) reduces `X` to `X_red`,
treated by `canonicalTraceFormula_of_isReduced`. -/
theorem traceFormulaUpToDim_one_of_smoothCurve
    (hcore : ∀ (U : B.Scheme) (pU : U.obj ⟶ Spec (.of k)) [IsCurve k pU] [Smooth pU]
      [IsEmpty (rationalPoints pU)] (J : CompactificationOf (Over.mk pU))
      (K : CochainComplex.Plus (EtaleModules.{u, 0} Λ U.obj)) (a b : ℤ) [K.obj.IsStrictlyGE a]
      [K.obj.IsStrictlyLE b],
      (∀ n, Stacks.ConstantSheaf.IsFiniteProjectiveLocallyConstant Λ U.obj.smallEtaleTopology
        (K.obj.X n)) → CanonicalTraceFormula Λ kbar p q hcard pU J K) :
    TraceFormulaUpToDim B Λ kbar p q hcard 1 := by
  intro X f _ _ _ hX j K hK
  obtain ⟨Z, i, _, _, hrange⟩ := exists_isClosedImmersion_range_eq B X ⊤
  have : LocallyOfFiniteType i := instLocallyOfFiniteTypeOfIsClosedImmersion i
  have : LocallyOfFiniteType (i ≫ f) := locallyOfFiniteType_comp i f
  replace hrange : Set.range i.base = Set.univ := hrange
  let jU : (∅ : Scheme.{u}) ⟶ X.obj := Scheme.emptyTo X.obj
  have hij : Set.range jU.base = (Set.range i.base)ᶜ := by
    rw [hrange, Set.compl_univ, Set.range_eq_empty_iff]
    infer_instance
  refine canonicalTraceFormula_of_openClosed Λ kbar p q hcard j jU i hij K ?_ ?_
  · -- the empty open
    have : IsClosedImmersion (jU ≫ f) := .of_isPreimmersion _ (by
      rw [Set.range_eq_empty]
      exact isClosed_empty)
    exact canonicalTraceFormula_of_etale Λ kbar p q hcard (jU ≫ f) _ _ fun s =>
      isEmptyElim (s.hom.base (Nonempty.some inferInstance))
  · -- the reduction
    exact canonicalTraceFormula_of_isReduced hcore Z (i ≫ f)
      ((topologicalKrullDim_le_of_range_subset i _ hrange.le).trans
        ((topologicalKrullDim_subspace_le _ _).trans (by exact_mod_cast hX))) _ _
      (isCtf_inverseImage B Λ i Z.property _ _ hK)

end SmoothCurve

end Stacks.EtaleCohomology

end
