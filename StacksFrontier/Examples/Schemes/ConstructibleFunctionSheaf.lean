module

public import Mathlib.Algebra.Category.Grp.Ulift
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.TopologicalInvariance.DenseSubsite
public import StacksFrontier.AlgebraicGeometry.EventualLimitProperties.Basic
public import StacksFrontier.AlgebraicGeometry.Flatness.Flattening.LimitPreserving
public import StacksFrontier.AlgebraicGeometry.Limits.Descending.UnderlyingSpace
public import StacksFrontier.AlgebraicGeometry.MoreMorphisms.ThickeningMorphism.UniversalHomeomorphism
public import StacksFrontier.AlgebraicGeometry.Morphisms.FinitePresentation.Constructible
public import StacksFrontier.AlgebraicGeometry.Sites.LocallySurjectiveUnivLE
public import StacksFrontier.AlgebraicGeometry.Size.Cutoff
public import StacksFrontier.AlgebraicGeometry.Spaces.FinitePresentation.Sheafify
public import StacksFrontier.AlgebraicGeometry.Topologies.Etale
public import StacksFrontier.AlgebraicGeometry.Topologies.Etale.RepresentableSheaves
public import StacksFrontier.Topology.Spectral.LimitConstructible

/-!
# A nonzero limit-preserving étale sheaf vanishing on fields

On the big étale site of schemes, the constructible `ℤ`-valued functions modulo the locally
constant ones form a separated presheaf of abelian groups whose sheafification `G` vanishes on
spectra of fields, is invariant under thickenings and is limit preserving, yet is not zero.

## Main results

* `exists_nonzero_limitPreserving_sheaf_vanishing_on_fields`: such a sheaf exists.

## Implementation notes

The existential packages one sheaf and all four properties, so that the same sheaf witnesses
them simultaneously. Vanishing is expressed by `IsZero` of the section group; invariance under a
thickening by the canonical restriction map being an isomorphism, rather than by a
non-canonical equality of groups. The bounded big site contains only schemes below its size
cutoff, so the field and thickening clauses quantify over objects of that site. Limit
preservation is that of the underlying set-valued presheaf, with index categories small
relative to the universe of schemes.

Invariance under a thickening `i : X ⟶ X'` needs the small étale sites of `X` and `X'` to agree
far enough to compare sheafifications. What is used is that étale base change along `i`
exhibits one as a *dense subsite* of the other
(`Stacks.EtaleCohomology.isDenseSubsite_of_universalHomeomorphism`), which holds for every
universal homeomorphism; the stronger equivalence of étale sites of
[Stacks, Tag 04DZ](https://stacks.math.columbia.edu/tag/04DZ) is not needed.

## References

* [Stacks Project, Tag 05LH](https://stacks.math.columbia.edu/tag/05LH)
-/

@[expose] public section

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits Topology

/- `CategoryTheory.MorphismProperty C` is the type of families `⦃X Y : C⦄ → (X ⟶ Y) → Prop`, and
the small étale site is `MorphismProperty.Over @Etale ⊤ X`. Recognizing `@Etale` at that type
needs the definition unfolded, so it is made `implicit_reducible` for this file. -/
attribute [local implicit_reducible] CategoryTheory.MorphismProperty
  AddCommGrpCat.uliftFunctor

namespace Stacks.Examples.ConstructibleFunctionSheaf

universe u v w w' z z'

private def LocallyFiniteValued {X : Scheme.{u}} (f : X → ℤ) : Prop :=
  ∀ x, ∃ U ∈ 𝓝 x, IsOpen U ∧ (f '' U).Finite

private lemma finite_image_of_locally_finite_valued {X : Type u} [TopologicalSpace X]
    {f : X → ℤ} {s : Set X} (hs : IsCompact s)
    (h : ∀ x ∈ s, ∃ U ∈ 𝓝 x, IsOpen U ∧ (f '' U).Finite) :
    (f '' s).Finite := by
  classical
  choose U hUm hUo hUf using fun x : s => h x.1 x.2
  obtain ⟨t, ht⟩ := hs.elim_finite_subcover U hUo fun x hx =>
    Set.mem_iUnion.mpr ⟨⟨x, hx⟩, mem_of_mem_nhds (hUm ⟨x, hx⟩)⟩
  refine (t.finite_toSet.biUnion fun x _ => hUf x).subset ?_
  rintro z ⟨x, hx, rfl⟩
  have hxcover := ht hx
  simp only [Set.mem_iUnion] at hxcover
  rcases hxcover with ⟨y, hy, hyU⟩
  exact Set.mem_iUnion.mpr ⟨y, Set.mem_iUnion.mpr ⟨hy, ⟨x, hyU, rfl⟩⟩⟩

private lemma locallyFiniteValued_of_affineFinite {X : Scheme.{u}} {f : X → ℤ}
    (hf : ∀ U : X.affineOpens, (f '' (U : Set X)).Finite) : LocallyFiniteValued f := by
  intro x
  obtain ⟨_, ⟨U, hU, rfl⟩, hxU, _⟩ :=
    X.isBasis_affineOpens.exists_subset_of_mem_open (Set.mem_univ x) isOpen_univ
  exact ⟨U, U.2.mem_nhds hxU, U.2, hf ⟨U, hU⟩⟩

private lemma locallyFiniteValued_comp {X Y : Scheme.{u}}
    (f : X → Y) (hf : Continuous f) {g : Y → ℤ}
    (hg : LocallyFiniteValued g) : LocallyFiniteValued (g ∘ f) := by
  intro x
  obtain ⟨V, hV, hVo, hVr⟩ := hg (f x)
  exact ⟨f ⁻¹' V, hf.continuousAt.preimage_mem_nhds hV,
    hVo.preimage hf, hVr.subset fun _ ⟨y, hy, h⟩ => ⟨f y, hy, h⟩⟩

private lemma finite_image_affine_of_locallyFiniteValued {X : Scheme.{u}} {f : X → ℤ}
    (hf : LocallyFiniteValued f) (U : X.affineOpens) :
    (f '' (U : Set X)).Finite := by
  let fU : ↥(U.1 : Set X) → ℤ := fun x => f x.1
  have : CompactSpace ↥(U.1 : Set X) :=
    isCompact_iff_compactSpace.mp U.property.isCompact
  have hfin : (fU '' Set.univ).Finite :=
    finite_image_of_locally_finite_valued isCompact_univ (fun x _ => by
      obtain ⟨V, hV, hVo, hVr⟩ := hf x.1
      refine ⟨Subtype.val ⁻¹' V,
        continuous_subtype_val.continuousAt.preimage_mem_nhds hV,
        hVo.preimage continuous_subtype_val, hVr.subset fun _ ⟨y, hy, h⟩ => ⟨y.1, hy, h⟩⟩)
  exact hfin.subset fun _ ⟨x, hx, h⟩ => ⟨⟨x, hx⟩, Set.mem_univ _, h⟩

private def IsConstructibleFunction {X : Scheme.{u}} (f : X → ℤ) : Prop :=
  (∀ U : X.affineOpens, (f '' (U : Set X)).Finite) ∧
    ∀ n : ℤ, IsLocallyConstructible (f ⁻¹' {n})

private lemma finite_range_of_isConstructibleFunction_of_affine
    {X : Scheme.{u}} [IsAffine X] {f : X → ℤ}
    (hf : IsConstructibleFunction f) : (Set.range f).Finite := by
  simpa using hf.1 ⟨⊤, isAffineOpen_top X⟩

private lemma constructible_fibers_of_isConstructibleFunction_of_affine
    {X : Scheme.{u}} [IsAffine X] {f : X → ℤ}
    (hf : IsConstructibleFunction f) (n : ℤ) :
    IsConstructible (f ⁻¹' {n}) :=
  (hf.2 n).isConstructible

private lemma isConstructibleFunction_of_affine
    {X : Scheme.{u}} [IsAffine X] {f : X → ℤ}
    (hfin : (Set.range f).Finite)
    (hlevels : ∀ n : ℤ, IsConstructible (f ⁻¹' {n})) :
    IsConstructibleFunction f :=
  ⟨fun _ => hfin.subset (Set.image_subset_range _ _), fun n => (hlevels n).isLocallyConstructible⟩

/-- Precomposition with a continuous map preserves constructible functions, once the pulled-back
levels are locally constructible. -/
private lemma isConstructibleFunction_comp_of_continuous {X Y : Scheme.{u}} (f : X → Y)
    (hf : Continuous f) {g : Y → ℤ} (hg : IsConstructibleFunction g)
    (h : ∀ n : ℤ, IsLocallyConstructible (f ⁻¹' (g ⁻¹' {n}))) :
    IsConstructibleFunction (g ∘ f) :=
  ⟨fun U => finite_image_affine_of_locallyFiniteValued
    (locallyFiniteValued_comp f hf (locallyFiniteValued_of_affineFinite hg.1)) U, h⟩

private lemma isConstructibleFunction_comp {X Y : Scheme.{u}} (f : X ⟶ Y)
    {g : Y → ℤ} (hg : IsConstructibleFunction g) :
    IsConstructibleFunction (g ∘ f) :=
  isConstructibleFunction_comp_of_continuous f f.continuous hg fun n =>
    AlgebraicGeometry.isLocallyConstructible_preimage f (hg.2 n)

private lemma isConstructibleFunction_zero (X : Scheme.{u}) :
    IsConstructibleFunction (fun _ : X => (0 : ℤ)) := by
  refine ⟨fun _ => (Set.finite_singleton (0 : ℤ)).subset fun _ ⟨_, _, h⟩ => h.symm,
    fun n => ?_⟩
  by_cases hn : n = 0
  · subst n
    rw [Set.preimage_const_of_mem (Set.mem_singleton 0)]
    exact IsLocallyConstructible.univ
  · rw [Set.preimage_const_of_notMem (Set.notMem_singleton_iff.mpr (Ne.symm hn))]
    exact IsLocallyConstructible.empty

private lemma isConstructibleFunction_add {X : Scheme.{u}} {f g : X → ℤ}
  (hf : IsConstructibleFunction f) (hg : IsConstructibleFunction g) :
    IsConstructibleFunction (f + g) := by
  refine ⟨fun U => (((hf.1 U).prod (hg.1 U)).image fun p : ℤ × ℤ => p.1 + p.2).subset ?_,
    fun n => (AlgebraicGeometry.isLocallyConstructible_iff_forall_affineOpens _).2 fun U => ?_⟩
  · rintro z ⟨x, hx, rfl⟩
    exact ⟨(f x, g x), ⟨Set.mem_image_of_mem f hx, Set.mem_image_of_mem g hx⟩, rfl⟩
  · let fU : ↥(U : Set X) → ℤ := fun x => f x.1
    let gU : ↥(U : Set X) → ℤ := fun x => g x.1
    let pieces : ℤ → Set ↥(U : Set X) := fun a =>
      (fU ⁻¹' {a}) ∩ (gU ⁻¹' {n - a})
    have hfr : (fU '' Set.univ).Finite :=
      (hf.1 U).subset fun _ ⟨x, _, h⟩ => ⟨x.1, x.2, h⟩
    have hp' : (⋃ a ∈ fU '' Set.univ, pieces a) = (fU + gU) ⁻¹' {n} := by
      ext x
      simp only [Set.mem_iUnion, Set.mem_inter_iff, Set.mem_preimage, Set.mem_singleton_iff,
        Pi.add_apply, pieces, exists_prop]
      exact ⟨fun ⟨a, _, hxa, hgb⟩ => by omega,
        fun hsum => ⟨fU x, ⟨x, Set.mem_univ x, rfl⟩, rfl, by omega⟩⟩
    change IsConstructible ((fU + gU) ⁻¹' {n})
    rw [← hp']
    exact IsConstructible.biUnion hfr fun a _ =>
      ((AlgebraicGeometry.isLocallyConstructible_iff_forall_affineOpens _).mp (hf.2 a) U).inter
        ((AlgebraicGeometry.isLocallyConstructible_iff_forall_affineOpens _).mp
          (hg.2 (n - a)) U)

private lemma isConstructibleFunction_neg {X : Scheme.{u}} {f : X → ℤ}
    (hf : IsConstructibleFunction f) : IsConstructibleFunction (-f) := by
  refine ⟨fun U => ?_, fun n => ?_⟩
  · change ((fun x : X => -f x) '' (U : Set X)).Finite
    rw [← Set.image_image Neg.neg f]
    exact (hf.1 U).image Neg.neg
  · have hEq : (-f) ⁻¹' ({n} : Set ℤ) = f ⁻¹' ({-n} : Set ℤ) := by
      ext x
      change (-f x = n) ↔ (f x = -n)
      omega
    rw [hEq]
    exact hf.2 (-n)

private def constructibleFunctionSubgroup (X : Scheme.{u}) : AddSubgroup (X → ℤ) where
  carrier := {f | IsConstructibleFunction f}
  zero_mem' := isConstructibleFunction_zero X
  add_mem' := isConstructibleFunction_add
  neg_mem' := isConstructibleFunction_neg

private def locallyConstantSubgroup (X : Scheme.{u}) :
    AddSubgroup (constructibleFunctionSubgroup X) where
  carrier := {f | IsLocallyConstant f.1}
  zero_mem' := IsLocallyConstant.const 0
  add_mem' hf hg := hf.comp₂ hg (· + ·)
  neg_mem' hf := hf.comp fun x => -x

private abbrev ConstructibleFunctionQuotient (X : Scheme.{u}) :=
  (constructibleFunctionSubgroup X) ⧸ locallyConstantSubgroup X

private def constructibleFunctionPullback {X Y : Scheme.{u}} (f : X ⟶ Y) :
    constructibleFunctionSubgroup Y →+ constructibleFunctionSubgroup X where
  toFun g := ⟨g.1 ∘ f, isConstructibleFunction_comp f g.2⟩
  map_zero' := rfl
  map_add' _ _ := rfl

private def constructibleFunctionQuotientPullback {X Y : Scheme.{u}} (f : X ⟶ Y) :
    ConstructibleFunctionQuotient Y →+ ConstructibleFunctionQuotient X :=
  QuotientAddGroup.map _ _ (constructibleFunctionPullback f)
    (fun _ hg => hg.comp_continuous f.continuous)

private lemma constructibleFunctionQuotientPullback_mk {X Y : Scheme.{u}} (f : X ⟶ Y)
    (g : constructibleFunctionSubgroup Y) :
    constructibleFunctionQuotientPullback f (QuotientAddGroup.mk g) =
      QuotientAddGroup.mk (constructibleFunctionPullback f g) := rfl

private lemma constructibleFunctionQuotientPullback_id (X : Scheme.{u}) :
    constructibleFunctionQuotientPullback (𝟙 X) = AddMonoidHom.id _ := by
  refine AddMonoidHom.ext fun g => ?_
  induction g using Quotient.inductionOn with | h g => rfl

private lemma constructibleFunctionQuotientPullback_comp {X Y Z : Scheme.{u}}
    (f : X ⟶ Y) (g : Y ⟶ Z) :
    constructibleFunctionQuotientPullback (f ≫ g) =
      (constructibleFunctionQuotientPullback f).comp
        (constructibleFunctionQuotientPullback g) := by
  refine AddMonoidHom.ext fun h => ?_
  induction h using Quotient.inductionOn with | h h => rfl

private def constructibleFunctionQuotientPresheaf : Scheme.{u}ᵒᵖ ⥤ AddCommGrpCat.{u} where
  obj X := AddCommGrpCat.of (ConstructibleFunctionQuotient X.unop)
  map f := AddCommGrpCat.ofHom (constructibleFunctionQuotientPullback f.unop)
  map_id X := congrArg AddCommGrpCat.ofHom (constructibleFunctionQuotientPullback_id X.unop)
  map_comp f g := congrArg AddCommGrpCat.ofHom
    (constructibleFunctionQuotientPullback_comp g.unop f.unop)

private lemma constructibleFunctionQuotient_subsingleton (X : Scheme.{u})
    [DiscreteTopology X] : Subsingleton (ConstructibleFunctionQuotient X) := by
  refine subsingleton_of_forall_eq 0 fun g => ?_
  induction g using Quotient.inductionOn with
  | h g => exact (QuotientAddGroup.eq_zero_iff _).mpr (IsLocallyConstant.of_discrete _)

private lemma isConstructibleFunction_comp_homeomorph {X Y : Scheme.{u}}
    (e : X ≃ₜ Y) {g : Y → ℤ} (hg : IsConstructibleFunction g) :
    IsConstructibleFunction (g ∘ e) :=
  isConstructibleFunction_comp_of_continuous e e.continuous hg fun n =>
    (hg.2 n).preimage_of_isOpenEmbedding e.isOpenEmbedding

private lemma constructibleFunctionQuotientPullback_bijective {X Y : Scheme.{u}}
    (f : X ⟶ Y) (hf : IsHomeomorph f) :
    Function.Bijective (constructibleFunctionQuotientPullback f) := by
  let e : X ≃ₜ Y := hf.homeomorph f
  refine ⟨(injective_iff_map_eq_zero _).mpr fun a ha => ?_, fun a => ?_⟩
  · induction a using Quotient.inductionOn with
    | h a =>
      have h : IsLocallyConstant (a.1 ∘ f) := (QuotientAddGroup.eq_zero_iff _).mp ha
      refine (QuotientAddGroup.eq_zero_iff _).mpr ?_
      change IsLocallyConstant a.1
      convert h.comp_continuous e.symm.continuous using 1
      ext y
      exact (congrArg a.1 (e.apply_symm_apply y)).symm
  · induction a using Quotient.inductionOn with
    | h a =>
      refine ⟨QuotientAddGroup.mk
        ⟨a.1 ∘ e.symm, isConstructibleFunction_comp_homeomorph e.symm a.2⟩, ?_⟩
      rw [constructibleFunctionQuotientPullback_mk]
      congr 1
      exact Subtype.ext (funext fun x => congrArg a.1 (e.symm_apply_apply x))

private lemma constructibleFunctionQuotientPullback_isIso_of_thickening
    {X Y : Scheme.{u}} (f : X ⟶ Y) (hf : Stacks.Thickenings.IsThickening f) :
    IsIso (constructibleFunctionQuotientPresheaf.map f.op) := by
  have : IsClosedImmersion f := hf.1
  exact (ConcreteCategory.isIso_iff_bijective _).mpr
    (constructibleFunctionQuotientPullback_bijective f
      (isHomeomorph_iff_isEmbedding_surjective.mpr
        ⟨(IsClosedImmersion.isClosedEmbedding f).isEmbedding, hf.2⟩))

private lemma constructibleFunctionQuotient_eq_zero_of_cover
    {ι : Type*} {X : Scheme.{u}} {U : ι → Scheme.{u}} (f : ∀ i, U i ⟶ X)
    (hf : ∀ i, IsOpenMap (f i)) (hs : ∀ x, ∃ i y, f i y = x)
    (a : ConstructibleFunctionQuotient X)
    (ha : ∀ i, constructibleFunctionQuotientPullback (f i) a = 0) : a = 0 := by
  induction a using Quotient.inductionOn with
  | h a =>
    apply (QuotientAddGroup.eq_zero_iff _).mpr
    apply IsLocallyConstant.iff_isOpen_fiber.mpr
    intro n
    have heq : a.1 ⁻¹' {n} = ⋃ i, f i '' ((a.1 ∘ f i) ⁻¹' {n}) := by
      ext x
      refine ⟨fun hx => ?_, fun hx => ?_⟩
      · obtain ⟨i, y, rfl⟩ := hs x
        exact Set.mem_iUnion.mpr ⟨i, y, hx, rfl⟩
      · obtain ⟨i, y, hy, rfl⟩ := Set.mem_iUnion.mp hx
        exact hy
    rw [heq]
    exact isOpen_iUnion fun i =>
      hf i _ (((QuotientAddGroup.eq_zero_iff _).mp (ha i)).isOpen_fiber n)

private lemma isConstructibleFunction_indicator {X : Scheme.{u}}
    (s : Set X) (hs : IsLocallyConstructible s) :
    IsConstructibleFunction (s.indicator (fun _ => (1 : ℤ))) := by
  classical
  refine ⟨fun U => ?_, fun n => ?_⟩
  · apply (Set.toFinite ({0, 1} : Set ℤ)).subset
    rintro y ⟨x, hx, rfl⟩
    by_cases hxs : x ∈ s <;> simp [Set.indicator, hxs]
  · by_cases h0 : n = 0
    · subst n
      have heq : (s.indicator (fun _ => (1 : ℤ))) ⁻¹' {0} = sᶜ := by
        ext x
        by_cases hx : x ∈ s <;> simp [Set.indicator, hx]
      rw [heq]
      intro x
      obtain ⟨U, hU, hUo, hUs⟩ := hs x
      exact ⟨U, hU, hUo, by simpa only [Set.preimage_compl] using hUs.compl⟩
    · by_cases h1 : n = 1
      · subst n
        have heq : (s.indicator (fun _ => (1 : ℤ))) ⁻¹' {1} = s := by
          ext x
          by_cases hx : x ∈ s <;> simp [Set.indicator, hx]
        rw [heq]
        exact hs
      · have heq : (s.indicator (fun _ => (1 : ℤ))) ⁻¹' {n} = ∅ := by
          ext x
          by_cases hx : x ∈ s <;> simp [Set.indicator, hx, h0, h1, eq_comm]
        rw [heq]
        exact IsLocallyConstructible.empty

private lemma constructibleFunctionQuotient_nontrivial_of_constructible
    {X : Scheme.{u}} [PreconnectedSpace X] (s : Set X)
    (hs : IsLocallyConstructible s) (hne : s.Nonempty) (hne' : sᶜ.Nonempty) :
    Nontrivial (ConstructibleFunctionQuotient X) := by
  classical
  let a : constructibleFunctionSubgroup X :=
    ⟨s.indicator (fun _ => (1 : ℤ)), isConstructibleFunction_indicator s hs⟩
  refine ⟨⟨QuotientAddGroup.mk a, 0, ?_⟩⟩
  intro h
  have hlc : IsLocallyConstant a.1 := (QuotientAddGroup.eq_zero_iff _).mp h
  obtain ⟨x, hx⟩ := hne
  obtain ⟨y, hy⟩ := hne'
  change y ∉ s at hy
  have heq := hlc.apply_eq_of_preconnectedSpace x y
  simp [a, Set.indicator, hx, hy] at heq

private lemma constructibleFunctionQuotient_nontrivial_spec
    (R : Type u) [CommRing R] [IsDomain R] (f : R) (hf : f ≠ 0)
    (x : PrimeSpectrum R) (hx : f ∈ x.asIdeal) :
    Nontrivial (ConstructibleFunctionQuotient (Spec (.of R))) :=
  constructibleFunctionQuotient_nontrivial_of_constructible (X := Spec (.of R))
    (show Set (PrimeSpectrum R) from PrimeSpectrum.basicOpen f)
    ((PrimeSpectrum.isCompact_basicOpen f).isConstructible
      (PrimeSpectrum.basicOpen f).isOpen).isLocallyConstructible
    ⟨(⊥ : PrimeSpectrum R), hf⟩ ⟨x, not_not_intro hx⟩

private lemma exists_nonzero_constructibleFunctionQuotient
    (B : BigEtaleSite.{u}) :
    ∃ X : B.Scheme, Nontrivial (ConstructibleFunctionQuotient X.obj) := by
  let R := ULift.{u} ℤ
  have : IsDomain R := ULift.ringEquiv.toMulEquiv.isDomain ℤ
  let q : R →+* ZMod 2 := (Int.castRingHom (ZMod 2)).comp ULift.ringEquiv.toRingHom
  let x : PrimeSpectrum R := PrimeSpectrum.comap q ⊥
  have hX : B.Contains (Spec (.of R)) := by
    change (Spec (.of R)).size < B.cutoff
    rw [Scheme.size_Spec]
    simpa [R] using B.aleph0_lt_cutoff
  refine ⟨B.obj (Spec (.of R)) hX,
    constructibleFunctionQuotient_nontrivial_spec R 2 ?_ x ?_⟩
  · intro h
    have := congrArg ULift.down h
    norm_num at this
  · change (2 : ZMod 2) = 0
    rfl

private noncomputable def constructibleFunctionQuotientSheaf :
    Sheaf Scheme.etaleTopology.{u} AddCommGrpCat.{u + 1} :=
  (presheafToSheaf Scheme.etaleTopology AddCommGrpCat.{u + 1}).obj
    (constructibleFunctionQuotientPresheaf ⋙ AddCommGrpCat.uliftFunctor.{u + 1})

private lemma constructibleFunctionQuotient_toSheafify_injective (X : Scheme.{u}) :
    Function.Injective ((toSheafify Scheme.etaleTopology
      (constructibleFunctionQuotientPresheaf ⋙ AddCommGrpCat.uliftFunctor.{u + 1})).app
        (Opposite.op X)) := by
  intro a b hab
  have hS := Presheaf.equalizerSieve_mem Scheme.etaleTopology
    (toSheafify Scheme.etaleTopology
      (constructibleFunctionQuotientPresheaf ⋙ AddCommGrpCat.uliftFunctor.{u + 1})) a b hab
  obtain ⟨𝒰, h𝒰⟩ := Scheme.mem_grothendieckTopology_iff.mp hS
  refine ULift.ext (sub_eq_zero.mp (constructibleFunctionQuotient_eq_zero_of_cover 𝒰.f
    (fun i => (𝒰.f i).isOpenMap) 𝒰.exists_eq _ fun i => ?_))
  exact (map_sub (constructibleFunctionQuotientPullback (𝒰.f i)) a.down b.down).trans
    (sub_eq_zero.mpr (congrArg ULift.down (h𝒰 _ _ ⟨i⟩)))

/-- Sections of the sheafified sheaf agreeing on an étale cover are equal. -/
private lemma constructibleFunctionQuotientSheaf_ext_of_cover {X : Scheme.{u}}
    (𝒰 : X.Cover.{u} (Scheme.precoverage (@Etale)))
    {s t : constructibleFunctionQuotientSheaf.obj.obj (Opposite.op X)}
    (h : ∀ i, constructibleFunctionQuotientSheaf.obj.map (𝒰.f i).op s =
      constructibleFunctionQuotientSheaf.obj.map (𝒰.f i).op t) : s = t := by
  apply constructibleFunctionQuotientSheaf.property.isSeparated X (Sieve.generate 𝒰.presieve₀)
    (Precoverage.generate_mem_toGrothendieck 𝒰.mem₀) s t
  rintro Y f ⟨Z, g, k, ⟨i⟩, rfl⟩
  change constructibleFunctionQuotientSheaf.obj.map ((𝒰.f i).op ≫ g.op) s =
    constructibleFunctionQuotientSheaf.obj.map ((𝒰.f i).op ≫ g.op) t
  simp only [Functor.map_comp, ConcreteCategory.comp_apply, h]

private lemma constructibleFunctionQuotientSheaf_nontrivial (X : Scheme.{u})
    [Nontrivial (ConstructibleFunctionQuotient X)] :
    Nontrivial (constructibleFunctionQuotientSheaf.obj.obj (Opposite.op X)) := by
  have : Nontrivial ((constructibleFunctionQuotientPresheaf ⋙
      AddCommGrpCat.uliftFunctor.{u + 1}).obj (Opposite.op X)) :=
    inferInstanceAs (Nontrivial (ULift.{u + 1} (ConstructibleFunctionQuotient X)))
  exact (constructibleFunctionQuotient_toSheafify_injective X).nontrivial

private lemma discreteTopology_of_etale_over_field (k : Type u) [Field k]
    {X : Scheme.{u}} (f : X ⟶ Spec (.of k)) [Etale f] : DiscreteTopology X := by
  have : LocallyQuasiFinite f := by
    rw [locallyQuasiFinite_iff]
    intro U hU V hV e
    have hφ := f.etale_appLE hU hV e
    algebraize [(f.appLE U V e).hom]
    exact Algebra.IsUnramifiedAt.instQuasiFiniteOfEssFiniteTypeOfFormallyUnramified
  let x : Spec (.of k) := Classical.choice inferInstance
  have h := f.isDiscrete_preimage_singleton x
  rw [show f ⁻¹' {x} = Set.univ from Set.eq_univ_of_forall fun y => Subsingleton.elim (f y) x] at h
  exact isDiscrete_univ_iff.mp h

private lemma constructibleFunctionQuotientSheaf_spec_field_isZero
    (k : Type u) [Field k] :
    IsZero (constructibleFunctionQuotientSheaf.obj.obj (Opposite.op (Spec (.of k)))) := by
  refine AddCommGrpCat.isZero_iff_subsingleton.mpr (subsingleton_of_forall_eq 0 fun s => ?_)
  let F : Scheme.{u}ᵒᵖ ⥤ AddCommGrpCat.{u + 1} :=
    constructibleFunctionQuotientPresheaf ⋙ AddCommGrpCat.uliftFunctor.{u + 1}
  let η := toSheafify Scheme.etaleTopology F
  have hS := Presheaf.imageSieve_mem Scheme.etaleTopology η s
  obtain ⟨𝒰, h𝒰⟩ := Scheme.mem_grothendieckTopology_iff.mp hS
  have hs : ∀ i, constructibleFunctionQuotientSheaf.obj.map (𝒰.f i).op s = 0 := by
    intro i
    obtain ⟨t, ht⟩ := h𝒰 _ _ ⟨i⟩
    have := discreteTopology_of_etale_over_field k (𝒰.f i)
    have := constructibleFunctionQuotient_subsingleton (𝒰.X i)
    have ht0 : t = 0 :=
      @Subsingleton.elim (ULift.{u + 1} (ConstructibleFunctionQuotient (𝒰.X i)))
        inferInstance t 0
    exact ht.symm.trans (ht0 ▸ map_zero (η.app _).hom)
  exact constructibleFunctionQuotientSheaf_ext_of_cover 𝒰 (t := 0) (by simpa using hs)

private lemma small_sections_of_locallySurjective
    {C : Type u} [SmallCategory C] (J : GrothendieckTopology C)
    (F : Cᵒᵖ ⥤ Type v) (G : Cᵒᵖ ⥤ Type v)
    (η : F ⟶ G) [Presheaf.IsLocallySurjective J η]
    (hG : Presieve.IsSeparated J G) [∀ Y, Small.{u} (F.obj Y)] (X : C) :
    Small.{u} (G.obj (Opposite.op X)) := by
  classical
  let R := Σ S : J.Cover X, (a : S.Arrow) → Shrink.{u} (F.obj (Opposite.op a.Y))
  let represents (r : R) (s : G.obj (Opposite.op X)) : Prop :=
    ∀ a : r.1.Arrow,
      η.app _ ((equivShrink _).symm (r.2 a)) = G.map a.f.op s
  have hex (s : G.obj (Opposite.op X)) : ∃ r : R, represents r s := by
    let S : J.Cover X := ⟨Presheaf.imageSieve η s, Presheaf.imageSieve_mem J η s⟩
    have h (a : S.Arrow) : ∃ t, η.app _ t = G.map a.f.op s := a.hf
    exact ⟨⟨S, fun a => equivShrink _ (h a).choose⟩, fun a => by simpa using (h a).choose_spec⟩
  choose r hr using hex
  refine small_of_injective (f := r) fun s t h => ?_
  have ht : represents (r s) t := h ▸ hr t
  exact (hG _ (r s).1.2).ext fun Y f hf => ((hr s) ⟨Y, f, hf⟩).symm.trans (ht ⟨Y, f, hf⟩)

private lemma small_sections_of_essentiallySmall
    {C : Type*} [Category C] [EssentiallySmall.{u} C] (J : GrothendieckTopology C)
    (F G : Cᵒᵖ ⥤ Type v) (η : F ⟶ G) [Presheaf.IsLocallySurjective J η]
    (hG : Presieve.IsSheaf J G) [hF : ∀ Y, Small.{u} (F.obj Y)] (X : C) :
    Small.{u} (G.obj (Opposite.op X)) := by
  let e := equivSmallModel.{u} C
  let K := e.inverse.inducedTopology J
  have : Presheaf.IsLocallySurjective K (Functor.whiskerLeft e.inverse.op η) :=
    Presheaf.isLocallySurjective_whisker K J e.inverse η
  have hG' : Presieve.IsSheaf K (e.inverse.op ⋙ G) :=
    e.inverse.op_comp_isSheaf_of_isSheaf_type K hG
  let : ∀ Y, Small.{u} ((e.inverse.op ⋙ F).obj Y) := fun Y => hF _
  let : Small.{u} (G.obj (Opposite.op ((e.functor ⋙ e.inverse).obj X))) :=
    small_sections_of_locallySurjective K (e.inverse.op ⋙ F) (e.inverse.op ⋙ G)
      (Functor.whiskerLeft e.inverse.op η) hG'.isSeparated (e.functor.obj X)
  exact small_of_injective
    ((ConcreteCategory.bijective_of_isIso (G.map (e.unitIso.app X).inv.op)).1)

private lemma etaleForget_isCocontinuous (X : Scheme.{u}) :
    (Scheme.Etale.forget X ⋙ Over.forget X).IsCocontinuous
      X.smallEtaleTopology Scheme.etaleTopology := by
  have : (Scheme.Etale.forget X).IsCocontinuous
      X.smallEtaleTopology (Scheme.etaleTopology.over X) := by
    change (MorphismProperty.Over.forget (@Etale : MorphismProperty Scheme.{u}) ⊤ X)
      |>.IsCocontinuous _ _
    dsimp [Scheme.smallEtaleTopology]
    infer_instance
  exact isCocontinuous_comp _ _ _ (Scheme.etaleTopology.over X)
private lemma etaleForget_isContinuous (X : Scheme.{u}) :
    (Scheme.Etale.forget X ⋙ Over.forget X).IsContinuous
      X.smallEtaleTopology Scheme.etaleTopology :=
  Functor.isContinuous_comp _ _ _ (Scheme.etaleTopology.over X) _

private lemma constructibleFunctionQuotientSheaf_small_on_affineEtale
    (X : Scheme.{u}) (Y : X.AffineEtale) :
    Small.{u} (constructibleFunctionQuotientSheaf.obj.obj
      (Opposite.op ((Scheme.AffineEtale.Spec X ⋙ Scheme.Etale.forget X ⋙
        Over.forget X).obj Y))) := by
  let K := Scheme.AffineEtale.topology X
  let H := Scheme.AffineEtale.Spec X ⋙ Scheme.Etale.forget X ⋙ Over.forget X
  have := etaleForget_isContinuous X
  have := etaleForget_isCocontinuous X
  have : H.IsContinuous K Scheme.etaleTopology :=
    Functor.isContinuous_comp _ _ _ X.smallEtaleTopology _
  have : H.IsCocontinuous K Scheme.etaleTopology :=
    isCocontinuous_comp _ _ _ X.smallEtaleTopology
  let F : Scheme.{u}ᵒᵖ ⥤ AddCommGrpCat.{u + 1} :=
    constructibleFunctionQuotientPresheaf ⋙ AddCommGrpCat.uliftFunctor.{u + 1}
  let η := Functor.whiskerLeft H.op
    (Functor.whiskerRight (toSheafify Scheme.etaleTopology F)
      (forget AddCommGrpCat.{u + 1}))
  have : Presheaf.IsLocallySurjective K η :=
    Presheaf.isLocallySurjective_whisker K Scheme.etaleTopology H _
  have : ∀ Z, Small.{u} ((H.op ⋙ F ⋙ forget AddCommGrpCat.{u + 1}).obj Z) :=
    fun _ => inferInstanceAs (Small.{u} (ULift.{u + 1} _))
  exact small_sections_of_essentiallySmall K _ _ η (H.op_comp_isSheaf_of_isSheaf_type K
    ((isSheaf_iff_isSheaf_of_type _ _).mp
      (Presheaf.isSheaf_comp_of_isSheaf Scheme.etaleTopology
        constructibleFunctionQuotientSheaf.obj (forget AddCommGrpCat.{u + 1})
        constructibleFunctionQuotientSheaf.property))) Y

private lemma constructibleFunctionQuotientSheaf_small_spec (R : CommRingCat.{u}) :
    Small.{u} (constructibleFunctionQuotientSheaf.obj.obj (Opposite.op (Spec R))) :=
  constructibleFunctionQuotientSheaf_small_on_affineEtale (Spec R)
    (Scheme.AffineEtale.mk (𝟙 (Spec R)))

private lemma constructibleFunctionQuotientSheaf_small_affine
    (X : Scheme.{u}) [IsAffine X] :
    Small.{u} (constructibleFunctionQuotientSheaf.obj.obj (Opposite.op X)) := by
  have := constructibleFunctionQuotientSheaf_small_spec (Γ(X, ⊤))
  exact small_of_injective ((ConcreteCategory.bijective_of_isIso
    (constructibleFunctionQuotientSheaf.obj.map X.isoSpec.inv.op)).1)

private lemma constructibleFunctionQuotientSheaf_small (X : Scheme.{u}) :
    Small.{u} (constructibleFunctionQuotientSheaf.obj.obj (Opposite.op X)) := by
  have : ∀ i, Small.{u} (constructibleFunctionQuotientSheaf.obj.obj
      (Opposite.op (X.affineCover.X i))) :=
    fun i => constructibleFunctionQuotientSheaf_small_affine _
  apply small_of_injective (f := fun s i =>
    constructibleFunctionQuotientSheaf.obj.map (X.affineCover.f i).op s)
  intro s t h
  exact constructibleFunctionQuotientSheaf_ext_of_cover
    (X.affineCover.changeProp (fun _ => inferInstance)) (congrFun h)

private noncomputable def shrinkAddCommGrpFunctor
    {C : Type*} [Category C] (F : C ⥤ AddCommGrpCat.{max u v})
    [∀ X, Small.{u} (F.obj X)] : C ⥤ AddCommGrpCat.{u} where
  obj X := AddCommGrpCat.of (Shrink.{u} (F.obj X))
  map f := AddCommGrpCat.ofHom
    ((Shrink.addEquiv.symm.toAddMonoidHom.comp (F.map f).hom).comp
      Shrink.addEquiv.toAddMonoidHom)
  map_id X := by
    ext x
    simp
  map_comp f g := by
    ext x
    simp

private noncomputable def shrinkAddCommGrpFunctorIso
    {C : Type*} [Category C] (F : C ⥤ AddCommGrpCat.{max u v})
    [∀ X, Small.{u} (F.obj X)] :
    shrinkAddCommGrpFunctor.{u, v} F ⋙ AddCommGrpCat.uliftFunctor.{v} ≅ F :=
  NatIso.ofComponents
    (fun X => (AddEquiv.ulift.trans Shrink.addEquiv).toAddCommGrpIso)
    (by
      intro X Y f
      ext x
      change (equivShrink _).symm (equivShrink _ ((F.map f)
        ((equivShrink _).symm x.down))) = _
      exact (equivShrink _).symm_apply_apply _)

private noncomputable def constructibleFunctionQuotientSmallSheaf :
    Sheaf Scheme.etaleTopology.{u} AddCommGrpCat.{u} := by
  let : ∀ X, Small.{u} (constructibleFunctionQuotientSheaf.obj.obj X) :=
    fun X => constructibleFunctionQuotientSheaf_small X.unop
  exact ⟨shrinkAddCommGrpFunctor.{u, u + 1} constructibleFunctionQuotientSheaf.obj,
    Presheaf.isSheaf_of_isSheaf_comp _ _ AddCommGrpCat.uliftFunctor.{u + 1}
      ((Presheaf.isSheaf_of_iso_iff (shrinkAddCommGrpFunctorIso.{u, u + 1}
        constructibleFunctionQuotientSheaf.{u}.obj)).mpr
          constructibleFunctionQuotientSheaf.property)⟩

private noncomputable def constructibleFunctionQuotientSmallSheafIso :
    constructibleFunctionQuotientSmallSheaf.{u}.obj ⋙ AddCommGrpCat.uliftFunctor.{u + 1} ≅
      constructibleFunctionQuotientSheaf.{u}.obj := by
  let : ∀ X, Small.{u} (constructibleFunctionQuotientSheaf.obj.obj X) :=
    fun X => constructibleFunctionQuotientSheaf_small X.unop
  exact shrinkAddCommGrpFunctorIso.{u, u + 1} constructibleFunctionQuotientSheaf.{u}.obj

private lemma constructibleFunctionQuotientSmallSheaf_spec_field_isZero
    (k : Type u) [Field k] :
    IsZero (constructibleFunctionQuotientSmallSheaf.obj.obj
      (Opposite.op (Spec (.of k)))) := by
  have h' := (constructibleFunctionQuotientSheaf_spec_field_isZero k).of_iso
    ((constructibleFunctionQuotientSmallSheafIso.{u}).app (Opposite.op (Spec (.of k))))
  apply AddCommGrpCat.isZero_iff_subsingleton.mpr
  let : Subsingleton (ULift.{u + 1}
      (constructibleFunctionQuotientSmallSheaf.obj.obj
        (Opposite.op (Spec (.of k))))) := AddCommGrpCat.isZero_iff_subsingleton.mp h'
  exact Function.Injective.subsingleton (f := ULift.up.{u + 1}) ULift.up_injective

private lemma exists_nonzero_constructibleFunctionQuotientSmallSheaf
    (B : BigEtaleSite.{u}) :
    ∃ X : B.Scheme, ¬ IsZero (constructibleFunctionQuotientSmallSheaf.obj.obj
      (Opposite.op X.obj)) := by
  obtain ⟨X, hX⟩ := exists_nonzero_constructibleFunctionQuotient B
  have := constructibleFunctionQuotientSheaf_nontrivial X.obj
  refine ⟨X, fun h => ?_⟩
  have := AddCommGrpCat.isZero_iff_subsingleton.mp h
  let : Subsingleton ((constructibleFunctionQuotientSmallSheaf.obj ⋙
      AddCommGrpCat.uliftFunctor.{u + 1}).obj (Opposite.op X.obj)) :=
    inferInstanceAs (Subsingleton (ULift.{u + 1}
      (constructibleFunctionQuotientSmallSheaf.obj.obj (Opposite.op X.obj))))
  have := (ConcreteCategory.bijective_of_isIso
    ((constructibleFunctionQuotientSmallSheafIso.{u}).app (Opposite.op X.obj)).hom).2.subsingleton
  exact not_subsingleton (constructibleFunctionQuotientSheaf.obj.obj
    (Opposite.op X.obj)) inferInstance

private lemma isSheaf_restrict_bigEtaleSite
    (B : BigEtaleSite.{u}) {A : Type*} [Category A]
    (F : Sheaf Scheme.etaleTopology.{u} A) :
    Presheaf.IsSheaf B.topology (B.inclusion.op ⋙ F.obj) := by
  let : CreatesLimitsOfShape WalkingCospan B.inclusion :=
    { CreatesLimit := fun {D} => by
        let E := D ⋙ B.inclusion
        let t := pullback.cone (E.map WalkingCospan.Hom.inl)
          (E.map WalkingCospan.Hom.inr)
        exact createsLimitFullSubcategoryInclusion' D
          ((IsLimit.postcomposeInvEquiv (diagramIsoCospan E) t).symm (limit.isLimit _))
          (Scheme.size_pullback_lt _ _ (D.obj .left).property (D.obj .right).property) }
  have : HasPullbacks B.Scheme :=
    hasLimitsOfShape_of_hasLimitsOfShape_createsLimitsOfShape B.inclusion
  have : PreservesLimitsOfShape WalkingCospan B.inclusion := inferInstance
  let K := (Scheme.precoverage (@Etale)).comap B.inclusion
  have : B.inclusion.IsContinuous K.toGrothendieck Scheme.etaleTopology :=
    Functor.isContinuous_toGrothendieck_of_pullbacksPreservedBy B.inclusion
      K (Scheme.precoverage (@Etale)) le_rfl
  have hle : B.precoverage ≤ K := by
    intro X R hR
    obtain ⟨𝒰, rfl, h𝒰⟩ := (B.mem_precoverage_iff).mp hR
    have h := BigEtaleSite.IsCovering.etale h𝒰
    change 𝒰.presieve₀.map B.inclusion ∈ Scheme.etalePrecoverage _
    change (𝒰.map B.inclusion).presieve₀ ∈ Scheme.etalePrecoverage _ at h
    simpa only [PreZeroHypercover.presieve₀_map] using h
  exact Presheaf.IsSheaf.of_le (Precoverage.toGrothendieck_mono hle)
    (B.inclusion.op_comp_isSheaf K.toGrothendieck Scheme.etaleTopology F)

private noncomputable def constructibleFunctionQuotientBigEtaleSheaf
    (B : BigEtaleSite.{u}) : Sheaf B.topology AddCommGrpCat.{u} :=
  ⟨B.inclusion.op ⋙ constructibleFunctionQuotientSmallSheaf.obj,
    isSheaf_restrict_bigEtaleSite B constructibleFunctionQuotientSmallSheaf⟩

/-- The structure morphism of a base change `W ×_Y X ⟶ W`, natural in the étale `Y`-scheme
`W`. -/
private noncomputable def etaleBaseChangeToSource {X Y : Scheme.{u}} (f : X ⟶ Y) :
    Stacks.EtaleCohomology.smallEtaleBaseChange f ⋙ Scheme.Etale.forget X ⋙ Over.forget X ⟶
      Scheme.Etale.forget Y ⋙ Over.forget Y where
  app U := pullback.fst U.hom f
  naturality U V g := by
    change pullback.lift _ _ _ ≫ pullback.fst V.hom f =
      pullback.fst U.hom f ≫ g.left
    exact pullback.lift_fst _ _ _

/-- A thickening is a universal homeomorphism, so étale base change along it exhibits the small
étale site of the ambient scheme as a dense subsite of that of the closed subscheme. -/
private lemma smallEtaleBaseChange_isDenseSubsite_of_thickening
    {X Y : Scheme.{u}} {f : X ⟶ Y} (hf : Stacks.Thickenings.IsThickening f) :
    (Stacks.EtaleCohomology.smallEtaleBaseChange f).IsDenseSubsite
      Y.smallEtaleTopology X.smallEtaleTopology :=
  have := hf.universalHomeomorphism
  Stacks.EtaleCohomology.isDenseSubsite_of_universalHomeomorphism f

private lemma constructibleFunctionQuotientSheaf_pullback_fst_isIso
    {X Y : Scheme.{u}} {f : X ⟶ Y} (hf : Stacks.Thickenings.IsThickening f)
    (U : Y.Etale) :
    IsIso (constructibleFunctionQuotientSheaf.obj.map (pullback.fst U.hom f).op) := by
  have := hf.1
  have : Surjective f := ⟨hf.2⟩
  let H := Stacks.EtaleCohomology.smallEtaleBaseChange f
  let HX := Scheme.Etale.forget X ⋙ Over.forget X
  let HY := Scheme.Etale.forget Y ⋙ Over.forget Y
  have := etaleForget_isContinuous X
  have := etaleForget_isContinuous Y
  have := etaleForget_isCocontinuous X
  have := etaleForget_isCocontinuous Y
  have := smallEtaleBaseChange_isDenseSubsite_of_thickening hf
  let F : Scheme.{u}ᵒᵖ ⥤ AddCommGrpCat.{u + 1} :=
    constructibleFunctionQuotientPresheaf ⋙ AddCommGrpCat.uliftFunctor.{u + 1}
  let G : Scheme.{u}ᵒᵖ ⥤ AddCommGrpCat.{u + 1} := constructibleFunctionQuotientSheaf.obj
  let η := toSheafify Scheme.etaleTopology F
  let β : HY.op ⋙ F ⟶ (H ⋙ HX).op ⋙ F :=
    Functor.whiskerRight (NatTrans.op (etaleBaseChangeToSource f)) F
  let δ : HY.op ⋙ G ⟶ (H ⋙ HX).op ⋙ G :=
    Functor.whiskerRight (NatTrans.op (etaleBaseChangeToSource f)) G
  have : ∀ V, IsIso (β.app V) := by
    intro V
    have : IsIso (constructibleFunctionQuotientPresheaf.map
        (pullback.fst V.unop.hom f).op) :=
      constructibleFunctionQuotientPullback_isIso_of_thickening _
        ⟨inferInstance, (inferInstance : Surjective _).1⟩
    change IsIso (AddCommGrpCat.uliftFunctor.map
      (constructibleFunctionQuotientPresheaf.map (pullback.fst V.unop.hom f).op))
    infer_instance
  have : IsIso β := NatIso.isIso_of_isIso_app β
  have : Presheaf.IsLocallyInjective Y.smallEtaleTopology β := inferInstance
  have : Presheaf.IsLocallySurjective Y.smallEtaleTopology β := inferInstance
  let ηY := Functor.whiskerLeft HY.op η
  have : (H ⋙ HX).IsCocontinuous Y.smallEtaleTopology Scheme.etaleTopology :=
    isCocontinuous_comp _ _ _ X.smallEtaleTopology
  have : (H ⋙ HX).IsContinuous Y.smallEtaleTopology Scheme.etaleTopology :=
    Functor.isContinuous_comp _ _ _ X.smallEtaleTopology _
  let ηH := Functor.whiskerLeft (H ⋙ HX).op η
  have : Presheaf.IsLocallyInjective Y.smallEtaleTopology ηY :=
    Presheaf.isLocallyInjective_whisker _ Scheme.etaleTopology HY η
  have : Presheaf.IsLocallySurjective Y.smallEtaleTopology ηY :=
    Presheaf.isLocallySurjective_whisker _ Scheme.etaleTopology HY η
  have : Presheaf.IsLocallyInjective Y.smallEtaleTopology ηH :=
    Presheaf.isLocallyInjective_whisker _ Scheme.etaleTopology (H ⋙ HX) η
  have : Presheaf.IsLocallySurjective Y.smallEtaleTopology ηH :=
    Presheaf.isLocallySurjective_whisker _ Scheme.etaleTopology (H ⋙ HX) η
  have hn : ηY ≫ δ = β ≫ ηH :=
    NatTrans.ext <| funext fun V => (η.naturality ((etaleBaseChangeToSource f).app V.unop).op).symm
  have : Presheaf.IsLocallyInjective Y.smallEtaleTopology (ηY ≫ δ) :=
    hn ▸ Presheaf.isLocallyInjective_comp Y.smallEtaleTopology β ηH
  have : Presheaf.IsLocallySurjective Y.smallEtaleTopology (ηY ≫ δ) :=
    hn ▸ Presheaf.isLocallySurjective_comp Y.smallEtaleTopology β ηH
  have hδi : Presheaf.IsLocallyInjective Y.smallEtaleTopology δ :=
    (Presheaf.comp_isLocallyInjective_iff _ ηY δ).mp inferInstance
  have hδs : Presheaf.IsLocallySurjective Y.smallEtaleTopology δ :=
    Presheaf.isLocallySurjective_of_isLocallySurjective _ ηY δ
  let GY : Sheaf Y.smallEtaleTopology AddCommGrpCat.{u + 1} :=
    ⟨HY.op ⋙ G, HY.op_comp_isSheaf _ _ constructibleFunctionQuotientSheaf⟩
  let GH : Sheaf Y.smallEtaleTopology AddCommGrpCat.{u + 1} :=
    ⟨(H ⋙ HX).op ⋙ G,
      (H ⋙ HX).op_comp_isSheaf _ _ constructibleFunctionQuotientSheaf⟩
  let d : GY ⟶ GH := ObjectProperty.homMk δ
  have : IsIso d := (Sheaf.isLocallyBijective_iff_isIso d).mp ⟨hδi, hδs⟩
  exact inferInstanceAs (IsIso (((sheafToPresheaf _ _).map d).app (Opposite.op U)))

private lemma constructibleFunctionQuotientSheaf_map_isIso_of_thickening
    {X Y : Scheme.{u}} {f : X ⟶ Y} (hf : Stacks.Thickenings.IsThickening f) :
    IsIso (constructibleFunctionQuotientSheaf.obj.map f.op) := by
  have h : IsIso (constructibleFunctionQuotientSheaf.obj.map
      (pullback.fst (𝟙 Y) f).op) :=
    constructibleFunctionQuotientSheaf_pullback_fst_isIso hf (Scheme.Etale.mk (𝟙 Y))
  have heq : pullback.fst (𝟙 Y) f = pullback.snd (𝟙 Y) f ≫ f := by
    simpa using pullback.condition (f := 𝟙 Y) (g := f)
  rw [heq, op_comp, Functor.map_comp] at h
  exact IsIso.of_isIso_comp_right _
    (constructibleFunctionQuotientSheaf.obj.map (pullback.snd (𝟙 Y) f).op)

private lemma constructibleFunctionQuotientSmallSheaf_map_isIso_of_thickening
    {X Y : Scheme.{u}} {f : X ⟶ Y} (hf : Stacks.Thickenings.IsThickening f) :
    IsIso (constructibleFunctionQuotientSmallSheaf.obj.map f.op) := by
  have : IsIso (AddCommGrpCat.uliftFunctor.{u + 1}.map
      (constructibleFunctionQuotientSmallSheaf.obj.map f.op)) :=
    (NatIso.isIso_map_iff constructibleFunctionQuotientSmallSheafIso f.op).mpr
      (constructibleFunctionQuotientSheaf_map_isIso_of_thickening hf)
  exact isIso_of_reflects_iso _ AddCommGrpCat.uliftFunctor.{u + 1}

private lemma exists_finite_affine_etale_refinement
    (X : Scheme.{u}) [CompactSpace X] (R : Scheme.etaleTopology.Cover X) :
    ∃ 𝒱 : X.Cover.{u} (Scheme.precoverage (@Etale)),
      Finite 𝒱.I₀ ∧ (∀ i, IsAffine (𝒱.X i)) ∧ ∀ i, R (𝒱.f i) := by
  classical
  obtain ⟨𝒰, h𝒰⟩ := Scheme.mem_grothendieckTopology_iff.mp R.2
  let ι := Σ i : 𝒰.I₀, (𝒰.X i).affineCover.I₀
  let V : ι → Scheme.{u} := fun i => (𝒰.X i.1).affineCover.X i.2
  let f : ∀ i, V i ⟶ X := fun i => (𝒰.X i.1).affineCover.f i.2 ≫ 𝒰.f i.1
  have hc : Set.univ ⊆ ⋃ i, Set.range (f i) := by
    intro x _
    obtain ⟨i, y, rfl⟩ := 𝒰.exists_eq x
    obtain ⟨j, z, rfl⟩ := (𝒰.X i).affineCover.exists_eq y
    exact Set.mem_iUnion.mpr ⟨⟨i, j⟩, z, rfl⟩
  obtain ⟨t, ht⟩ := isCompact_univ.elim_finite_subcover
    (fun i => Set.range (f i)) (fun i => (f i).isOpenMap.isOpen_range) hc
  have hsurj : ∀ x : X, ∃ i : t, ∃ y, f i y = x := by
    intro x
    obtain ⟨i, hi, y, hy⟩ := Set.mem_iUnion₂.mp (ht (Set.mem_univ x))
    exact ⟨⟨i, hi⟩, y, hy⟩
  let 𝒱 : X.Cover.{u} (Scheme.precoverage (@Etale)) :=
    { I₀ := t
      X i := V i
      f i := f i
      mem₀ := by
        rw [Scheme.presieve₀_mem_precoverage_iff]
        exact ⟨hsurj, fun _ => inferInstance⟩ }
  exact ⟨𝒱, inferInstance,
    fun i => inferInstanceAs (IsAffine ((𝒰.X i.val.1).affineCover.X i.val.2)),
    fun i => R.1.downward_closed (h𝒰 _ _ ⟨i.val.1⟩) ((𝒰.X i.val.1).affineCover.f i.val.2)⟩

attribute [local instance] isLocallySurjective_toSheafify isLocallyInjective_toSheafify

private theorem limitPreserving_sheafify_of_cover_descent
    {C : Type z} [Category.{z'} C] [HasPullbacks C]
    (T : C ⥤ Scheme.{u}) [PreservesLimitsOfShape WalkingCospan T]
    (J : GrothendieckTopology C)
    (hdesc : AffineCoversDescend.{u, w, w'} T J)
    (hfin : FiniteAffineRefinements T J)
    (F : Cᵒᵖ ⥤ Type v) [UnivLE.{max z z', v}]
    (hF : AlgebraicGeometry.LimitPreserving.{u, v, w, w', z} T F) :
    AlgebraicGeometry.LimitPreserving.{u, v, w, w', z} T (J.sheafify F) := by
  let G := J.sheafify F
  let η := J.toSheafify F
  have hG : Presieve.IsSheaf J G :=
    (isSheaf_iff_isSheaf_of_type J G).mp (J.sheafify_isSheaf F)
  have hη : ImagesEventuallyEqual.{u, v, w, w'} T η :=
    images_eventually_equal_of_locally_injective T J hdesc η hG hF
  have hinj : ImagesEventuallyEqual.{u, v, w, w'} T (𝟙 G) :=
    images_eventually_equal_of_locally_surjective T J hfin η hG hη
  intro I _ _ D c hc hD hC
  exact isColimit_mapCocone_of_exists_of_eventually_eq G D c
    (exists_sheaf_section_at_stage T J hdesc η hG hF hinj D c hc hD hC)
    (hinj I D c hc hD hC)

/-- The `ULift`-reindexed presieve of an étale cover generates a covering sieve. -/
private lemma generate_reindex_mem_toGrothendieck {X : Scheme.{u}}
    (𝒱 : X.Cover.{u} (Scheme.precoverage (@Etale))) :
    Sieve.generate (𝒱.toPreZeroHypercover.reindex (Equiv.ulift.{u + 1, u})).presieve₀ ∈
      (Scheme.precoverage (@Etale)).toGrothendieck X := by
  rw [PreZeroHypercover.presieve₀_reindex]
  exact Precoverage.generate_mem_toGrothendieck 𝒱.mem₀

private theorem finiteAffineRefinements_etale :
    FiniteAffineRefinements (𝟭 Scheme.{u}) Scheme.etaleTopology := by
  intro X hX R
  let : IsAffine X := hX
  obtain ⟨𝒱, hfin, haff, hR⟩ := exists_finite_affine_etale_refinement X R
  let := hfin
  let E := 𝒱.toPreZeroHypercover.reindex (Equiv.ulift.{u + 1, u})
  refine ⟨E, ?_, fun k => haff k.down, ?_, fun k => hR k.down⟩
  · change Finite (ULift.{u + 1, u} 𝒱.I₀)
    infer_instance
  · exact generate_reindex_mem_toGrothendieck 𝒱

private theorem affineCoversDescend_etale [UnivLE.{max v w, u}] :
    AffineCoversDescend.{u, v, w} (𝟭 Scheme.{u}) Scheme.etaleTopology := by
  classical
  intro I _ _ D c hc hD hC R
  let : IsAffine c.pt := hC
  let : ∀ i, IsAffine (D.obj i) := hD
  let : UnivLE.{w, max v w} := by simpa only [max_comm] using univLE_max.{w, v}
  let : UnivLE.{w, u} := UnivLE.trans.{w, max v w, u}
  let : LocallySmall.{u} I := ⟨fun _ _ => inferInstance⟩
  let e := equivSmallModel.{u} I
  let : IsCofiltered (SmallModel.{u} I) := IsCofiltered.of_equivalence e
  obtain ⟨V, hfin, haff, hR⟩ := exists_finite_affine_etale_refinement c.pt R
  let := hfin
  let : ∀ k, IsAffine (V.X k) := haff
  let U : c.pt.AffineCover.{u} @Etale :=
    { I₀ := V.I₀
      X k := Scheme.Γ.obj (Opposite.op (V.X k))
      f k := (V.X k).isoSpec.inv ≫ V.f k
      map_prop k :=
        (MorphismProperty.cancel_left_of_respectsIso
          (@Etale : MorphismProperty Scheme.{u}) (V.X k).isoSpec.inv (V.f k)).mpr
          (V.map_prop k)
      idx := V.idx
      covers x := by
        obtain ⟨y, hy⟩ := V.covers x
        refine ⟨(V.X (V.idx x)).isoSpec.hom y, ?_⟩
        exact (congrArg (fun f : V.X (V.idx x) ⟶ c.pt => f y)
          ((V.X (V.idx x)).isoSpec.hom_inv_id_assoc (V.f (V.idx x)))).trans hy }
  let : IsAffine (c.whisker e.inverse).pt := hC
  let : ∀ j, IsAffine ((e.inverse ⋙ D).obj j) := fun j => hD _
  obtain ⟨i, W, hWfin, q, hq⟩ :=
    AlgebraicGeometry.exists_standardEtaleCovering_of_isLimit
      (e.inverse ⋙ D) (c.whisker e.inverse) (hc.whiskerEquivalence e.symm) U
  let := hWfin
  let E := W.cover.toPreZeroHypercover.reindex (Equiv.ulift.{u + 1, u})
  refine ⟨e.inverse.obj i, E, ?_, ?_, ?_, ?_⟩
  · change Finite (ULift.{u + 1, u} W.I₀)
    infer_instance
  · intro k
    change IsAffine (Spec (W.X k.down))
    infer_instance
  · exact generate_reindex_mem_toGrothendieck W.cover
  · rintro ⟨k⟩
    change R (pullback.fst (c.π.app (e.inverse.obj i)) (W.f k))
    obtain ⟨r, rfl⟩ := q.surjective k
    obtain ⟨a⟩ := hq r
    have ha : a.hom.left ≫ U.f r =
        pullback.snd (W.f (q r)) (c.π.app (e.inverse.obj i)) := Over.w a.hom
    have hR' : R (U.f r) := R.1.downward_closed (hR _) (V.X _).isoSpec.inv
    have hRa := R.1.downward_closed hR' a.hom.left
    rw [ha] at hRa
    have hRb := R.1.downward_closed hRa
      (pullbackSymmetry (c.π.app (e.inverse.obj i)) (W.f (q r))).hom
    simpa only [pullbackSymmetry_hom_comp_snd] using hRb

/-! Arbitrary-index compact-open descent for affine inverse limits. -/

attribute [local simp] Scheme.Hom.resLE_comp_resLE Scheme.Hom.resLE_comp_ι
  Scheme.Hom.resLE_id

private lemma jointly_surjective_of_isColimit_commRing
    {J : Type v} [Category.{w} J] [IsFiltered J]
    (F : J ⥤ CommRingCat.{u}) (c : Cocone F) (hc : IsColimit c) (x : c.pt) :
    ∃ (j : J) (y : F.obj j), c.ι.app j y = x := by
  classical
  let s : Set c.pt := ⋃ j, Set.range fun y : F.obj j => (c.ι.app j).hom y
  let C : Subring c.pt := Subring.closure s
  let ι' (j : J) : F.obj j ⟶ CommRingCat.of C :=
    CommRingCat.ofHom ((c.ι.app j).hom.codRestrict C fun y =>
      Subring.subset_closure (Set.mem_iUnion.mpr ⟨j, Set.mem_range.mpr ⟨y, rfl⟩⟩))
  let c' : Cocone F := {
    pt := CommRingCat.of C
    ι := {
      app := ι'
      naturality := by
        intro j k f
        ext y
        apply Subtype.ext
        change (c.ι.app k).hom ((F.map f).hom y) = (c.ι.app j).hom y
        simpa only [CommRingCat.comp_apply] using congrArg (fun q => q y) (c.w f)
    }
  }
  let incl : CommRingCat.of C ⟶ c.pt := CommRingCat.ofHom C.subtype
  let d := hc.desc c'
  have hd : d ≫ incl = 𝟙 c.pt := by
    refine hc.hom_ext fun j => ?_
    calc
      c.ι.app j ≫ (d ≫ incl) = (c.ι.app j ≫ d) ≫ incl := by simp [Category.assoc]
      _ = c'.ι.app j ≫ incl := by rw [hc.fac c' j]
      _ = c.ι.app j := by ext y; rfl
  have hs : x ∈ C := by
    have hz := congrArg (fun g : c.pt ⟶ c.pt => g.hom x) hd
    simp only [CommRingCat.id_apply] at hz
    rw [← hz]
    exact (d.hom x).2
  have hw {j l : J} (f : j ⟶ l) (a : F.obj j) :
      (c.ι.app l).hom ((F.map f).hom a) = (c.ι.app j).hom a := by
    simpa only [← ConcreteCategory.comp_apply] using congrArg (fun q => q.hom a) (c.w f)
  apply Subring.closure_induction (s := s) (p := fun x _ =>
    ∃ (j : J) (y : F.obj j), c.ι.app j y = x)
    (fun y hy => by
      rcases Set.mem_iUnion.mp hy with ⟨j, hy⟩
      rcases Set.mem_range.mp hy with ⟨z, rfl⟩
      exact ⟨j, z, rfl⟩)
    ⟨(IsFiltered.nonempty (C := J)).some, 0, by simp⟩
    ⟨(IsFiltered.nonempty (C := J)).some, 1, by simp⟩
    (by
      intro x y hx hy h₁ h₂
      obtain ⟨j, a, rfl⟩ := h₁
      obtain ⟨k, b, rfl⟩ := h₂
      obtain ⟨l, f, g, -⟩ := IsFilteredOrEmpty.cocone_objs j k
      refine ⟨l, (F.map f).hom a + (F.map g).hom b, ?_⟩
      change (c.ι.app l).hom ((F.map f).hom a + (F.map g).hom b) = _
      rw [map_add, hw, hw])
    (by
      intro x hx h₁
      obtain ⟨j, a, rfl⟩ := h₁
      exact ⟨j, -a, by simp⟩)
    (by
      intro x y hx hy h₁ h₂
      obtain ⟨j, a, rfl⟩ := h₁
      obtain ⟨k, b, rfl⟩ := h₂
      obtain ⟨l, f, g, -⟩ := IsFilteredOrEmpty.cocone_objs j k
      refine ⟨l, (F.map f).hom a * (F.map g).hom b, ?_⟩
      change (c.ι.app l).hom ((F.map f).hom a * (F.map g).hom b) = _
      rw [map_mul, hw, hw])
    hs

/-- `f.appLE U V e` is the map on global sections of the restricted morphism `f.resLE U V e`,
conjugated by the canonical isomorphisms `Γ(U.toScheme, ⊤) ≅ Γ(Y, U)` and
`Γ(V.toScheme, ⊤) ≅ Γ(X, V)`. -/
private lemma appLE_eq_topIso_inv_comp_resLE_appTop {X Y : Scheme.{u}} (f : X ⟶ Y)
    (U : Y.Opens) (V : X.Opens) (e : V ≤ f ⁻¹ᵁ U) :
    f.appLE U V e = U.topIso.inv ≫ (f.resLE U V e).appTop ≫ V.topIso.hom := by
  have hw : U.topIso.hom ≫ f.appLE U V e = (f.resLE U V e).appTop ≫ V.topIso.hom :=
    (arrowResLEAppIso f U V e).hom.w
  rw [← hw, Iso.inv_hom_id_assoc]

open Scheme.Opens in
private lemma isBasis_preimage_isAffineOpenGen {I : Type v} [Category.{w} I]
    {D : I ⥤ Scheme.{u}} {c : Cone D} (hc : IsLimit c) [IsCofiltered I]
    [∀ {i j} (f : i ⟶ j), IsAffineHom (D.map f)] :
    TopologicalSpace.Opens.IsBasis
      { (c.π.app i ⁻¹ᵁ V : c.pt.Opens) | (i : I) (V : (D.obj i).Opens)
        (_ : IsAffineOpen V) } := by
  classical
  refine TopologicalSpace.Opens.isBasis_iff_nbhd.mpr fun {U x} hxU => ?_
  obtain ⟨i⟩ := IsCofiltered.nonempty (C := I)
  have : IsCofiltered (Over i) := inferInstance
  have : IsFiltered (Over i)ᵒᵖ := inferInstance
  obtain ⟨_, ⟨V, hV : IsAffineOpen V, rfl⟩, hxV, -⟩ :=
    (D.obj i).isBasis_affineOpens.exists_subset_of_mem_open
      (Set.mem_univ (c.π.app i x)) isOpen_univ
  have (j : Over i) : IsAffine ((EventualLimit.preimageDiagram D i V).obj j) := hV.preimage _
  have (j : (Over i)ᵒᵖ) : IsAffine ((EventualLimit.preimageDiagram D i V).op.obj j).unop :=
    hV.preimage _
  have : PreservesColimit (EventualLimit.preimageDiagram D i V).op Scheme.Γ :=
    AlgebraicGeometry.preservesColimit_Γ (D := (EventualLimit.preimageDiagram D i V).op)
  have hΓ : IsColimit (Scheme.Γ.mapCocone (EventualLimit.preimageCone D c i V).op) :=
    isColimitOfPreserves Scheme.Γ (EventualLimit.isLimitPreimageCone D c hc i V).op
  obtain ⟨r, hrU, hxr⟩ := IsAffineOpen.exists_basicOpen_le
    (Scheme.isAffine_of_isLimit _ (EventualLimit.isLimitPreimageCone D c hc i V)) (V := U)
    ⟨x, hxU⟩ hxV
  obtain ⟨j, s, hs⟩ := jointly_surjective_of_isColimit_commRing
    ((EventualLimit.preimageDiagram D i V).op ⋙ Scheme.Γ)
    (Scheme.Γ.mapCocone (EventualLimit.preimageCone D c i V).op)
    hΓ ((c.π.app i ⁻¹ᵁ V).topIso.inv r)
  obtain ⟨s, rfl⟩ := (D.map j.unop.hom ⁻¹ᵁ V).topIso.symm.commRingCatIsoToRingEquiv.surjective s
  have h : c.π.app j.unop.left ⁻¹ᵁ D.map j.unop.hom ⁻¹ᵁ V = c.π.app i ⁻¹ᵁ V :=
    congr($(c.w j.unop.hom) ⁻¹ᵁ V)
  have hres : r = (c.π.app j.unop.left).appLE (D.map j.unop.hom ⁻¹ᵁ V)
      (c.π.app i ⁻¹ᵁ V) h.ge s := by
    convert! show r = ((topIso _).inv ≫ ((EventualLimit.preimageCone D c i V).π.app j.unop).appTop ≫
      (topIso _).hom) s from
      (c.π.app i ⁻¹ᵁ V).topIso.commRingCatIsoToRingEquiv.symm_apply_eq.mp hs.symm using 3
    simp only [EventualLimit.preimageCone]
    exact appLE_eq_topIso_inv_comp_resLE_appTop _ _ _ _
  refine ⟨_, ⟨j.unop.left, _, (hV.preimage _).basicOpen s, rfl⟩, ?_⟩
  simp only [Functor.const_obj_obj, Scheme.preimage_basicOpen] at hres ⊢
  rw [← c.pt.basicOpen_res_eq _ (eqToHom h.symm).op, ← CommRingCat.comp_apply,
    Scheme.Hom.app_eq_appLE, Scheme.Hom.appLE_map, ← hres]
  exact ⟨hxr, hrU⟩

private lemma exists_preimage_eq_gen {I : Type v} [Category.{w} I]
    {D : I ⥤ Scheme.{u}} {c : Cone D} (hc : IsLimit c) [IsCofiltered I]
    [∀ {i j} (f : i ⟶ j), IsAffineHom (D.map f)]
    (U : c.pt.Opens) (hU : IsCompact (U : Set c.pt)) :
    ∃ (i : I) (V : (D.obj i).Opens), IsCompact (V : Set (D.obj i)) ∧
      c.π.app i ⁻¹ᵁ V = U := by
  classical
  obtain ⟨s, hs, hsf, rfl⟩ := (isBasis_preimage_isAffineOpenGen hc).exists_finite_of_isCompact hU
  have : Finite s := hsf
  choose i V hV hVi using fun x : s => hs x.2
  obtain ⟨j, fj⟩ := IsCofiltered.inf_objs_exists (hsf.toFinset.attach.image
    fun x => i ⟨x.1, by simpa only [Set.Finite.mem_toFinset] using x.2⟩ :)
  replace fj : ∀ b : s, j ⟶ i b := fun b =>
    (@fj (i b) (by simpa using ⟨b.1, b.2, rfl⟩)).some
  refine ⟨j, ⨆ (k : s), D.map (fj _) ⁻¹ᵁ V k, ?_, ?_⟩
  · simp only [TopologicalSpace.Opens.iSup_mk, TopologicalSpace.Opens.carrier_eq_coe,
      TopologicalSpace.Opens.map_coe, TopologicalSpace.Opens.coe_mk]
    exact isCompact_iUnion fun i => ((hV i).preimage _).isCompact
  · simp [-TopologicalSpace.Opens.iSup_mk, Scheme.Hom.preimage_iSup,
      ← Scheme.Hom.comp_preimage, c.w, hVi, sSup_eq_iSup']

private abbrev ConstructibleFunctionDescent : Prop :=
  ∀ (I : Type (max v w)) [Category.{w} I] [IsCofiltered I]
    (D : I ⥤ Scheme.{u}) (c : Cone D), IsLimit c →
    (∀ i, IsAffine (D.obj i)) → IsAffine c.pt →
    ∀ f : constructibleFunctionSubgroup c.pt,
      ∃ (i : I) (g : constructibleFunctionSubgroup (D.obj i)),
        constructibleFunctionPullback (c.π.app i) g = f

private abbrev ConstructibleSetDescent : Prop :=
  ∀ (I : Type (max v w)) [Category.{w} I] [IsCofiltered I]
    (D : I ⥤ Scheme.{u}) (c : Cone D), IsLimit c →
    (∀ i, IsAffine (D.obj i)) → IsAffine c.pt →
    ∀ s : Set c.pt, IsConstructible s →
      ∃ (i : I) (t : Set (D.obj i)), IsConstructible t ∧
        (c.π.app i) ⁻¹' t = s

private theorem constructibleSetDescent : ConstructibleSetDescent.{u, v, w} := by
  classical
  intro I _ _ D c hc hD hC s hs
  let : ∀ i, IsAffine (D.obj i) := hD
  let : IsAffine c.pt := hC
  have : ∀ {i j : I} (a : i ⟶ j), IsAffineHom (D.map a) := fun _ => inferInstance
  induction hs using IsConstructible.empty_union_induction with
  | open_retrocompact U hUo hUr =>
    obtain ⟨i, V, hVc, hVeq⟩ := exists_preimage_eq_gen hc ⟨U, hUo⟩ hUr.isCompact
    refine ⟨i, (V : Set (D.obj i)), hVc.isConstructible V.isOpen, ?_⟩
    exact congrArg (fun W : c.pt.Opens => (W : Set c.pt)) hVeq
  | union s _ t _ hs ht =>
    obtain ⟨i, A, hA, hAe⟩ := hs
    obtain ⟨j, B, hB, hBe⟩ := ht
    let k := IsCofiltered.min i j
    let a : k ⟶ i := IsCofiltered.minToLeft i j
    let b : k ⟶ j := IsCofiltered.minToRight i j
    refine ⟨k, (D.map a) ⁻¹' A ∪ (D.map b) ⁻¹' B,
      ((D.map a).isConstructible_preimage hA).union
        ((D.map b).isConstructible_preimage hB), ?_⟩
    change (c.π.app k ≫ D.map a) ⁻¹' A ∪ (c.π.app k ≫ D.map b) ⁻¹' B = s ∪ t
    rw [c.w, c.w, hAe, hBe]
  | compl s _ hs =>
    obtain ⟨i, A, hA, hAe⟩ := hs
    refine ⟨i, Aᶜ, hA.compl, ?_⟩
    rw [Set.preimage_compl, hAe]

private lemma constructible_levels_of_membership_pattern
    {X A B : Type*} [TopologicalSpace X] [Finite A]
    (E : A → Set X) (hE : ∀ a, IsConstructible (E a))
    (g : (A → Bool) → B) (b : B) :
    IsConstructible {x | g (fun a => @decide (x ∈ E a) (Classical.propDecidable _)) = b} := by
  classical
  have hp (p : A → Bool) :
      IsConstructible {x | ∀ a, decide (x ∈ E a) = p a} := by
    rw [Set.ofPred_forall]
    refine IsConstructible.iInter fun a => ?_
    cases h : p a with
    | false =>
      convert (hE a).compl using 1
      ext x
      simp
    | true =>
      convert hE a using 1
      ext x
      simp
  have heq : {x | g (fun a => decide (x ∈ E a)) = b} =
      ⋃ p : {p : A → Bool // g p = b}, {x | ∀ a, decide (x ∈ E a) = p.1 a} := by
    ext x
    simp only [Set.mem_ofPred_eq, Set.mem_iUnion]
    refine ⟨fun hx => ⟨⟨fun a => decide (x ∈ E a), hx⟩, fun _ => rfl⟩, ?_⟩
    rintro ⟨p, hp'⟩
    have h : (fun a => decide (x ∈ E a)) = p.1 := funext hp'
    simpa [h] using p.2
  rw [heq]
  exact IsConstructible.iUnion fun p => hp p.1

private theorem constructibleFunctionDescent_of_setDescent
    (hset : ConstructibleSetDescent.{u, v, w}) :
    ConstructibleFunctionDescent.{u, v, w} := by
  classical
  intro I _ _ D c hc hD hC f
  let : IsAffine c.pt := hC
  let t : Finset ℤ := (finite_range_of_isConstructibleFunction_of_affine f.2).toFinset
  choose i E hE hdesc using fun n : ℤ =>
    hset I D c hc hD hC (f.1 ⁻¹' {n})
      (constructible_fibers_of_isConstructibleFunction_of_affine f.2 n)
  obtain ⟨k, hk⟩ := IsCofiltered.inf_objs_exists (t.image i)
  have hik (n : ℤ) (hn : n ∈ t) : Nonempty (k ⟶ i n) :=
    hk (Finset.mem_image.mpr ⟨n, hn, rfl⟩)
  let a (n : ℤ) (hn : n ∈ t) : k ⟶ i n := (hik n hn).some
  let Eₖ : {n : ℤ // n ∈ t} → Set (D.obj k) := fun n =>
    D.map (a n.1 n.2) ⁻¹' E n.1
  have hEₖ (n : {n : ℤ // n ∈ t}) : IsConstructible (Eₖ n) :=
    (D.map (a n.1 n.2)).isConstructible_preimage (hE n.1)
  have hEq (n : {n : ℤ // n ∈ t}) :
      (c.π.app k) ⁻¹' Eₖ n = f.1 ⁻¹' {n.1} := by
    ext x
    have hx := congrArg (fun s : Set c.pt => x ∈ s) (hdesc n.1)
    change D.map (a n.1 n.2) (c.π.app k x) ∈ E n.1 ↔ f.1 x = n.1
    rw [← Scheme.Hom.comp_apply, c.w (a n.1 n.2)]
    simpa only [Set.mem_preimage, Set.mem_singleton_iff] using (eq_iff_iff.mp hx)
  let g : ({n : ℤ // n ∈ t} → Bool) → ℤ := fun p =>
    if hp : ∃ n, p n = true then (Classical.choose hp).1 else 0
  let fₖ : D.obj k → ℤ := fun x => g (fun n => decide (x ∈ Eₖ n))
  let : IsAffine (D.obj k) := hD k
  have hfin : (Set.range fₖ).Finite := (Set.finite_range g).subset fun _ ⟨_, h⟩ => ⟨_, h⟩
  have hlevels (n : ℤ) : IsConstructible (fₖ ⁻¹' {n}) :=
    constructible_levels_of_membership_pattern Eₖ hEₖ g n
  refine ⟨k, ⟨fₖ, isConstructibleFunction_of_affine hfin hlevels⟩, ?_⟩
  apply Subtype.ext
  funext x
  have hmem : ∃ n : {n : ℤ // n ∈ t}, decide (c.π.app k x ∈ Eₖ n) = true :=
    ⟨⟨f.1 x, (finite_range_of_isConstructibleFunction_of_affine f.2).mem_toFinset.mpr
      (Set.mem_range_self x)⟩, decide_eq_true <| (Set.ext_iff.mp (hEq _) x).mpr rfl⟩
  have hn := (Set.ext_iff.mp (hEq (Classical.choose hmem)) x).mp
    (of_decide_eq_true (Classical.choose_spec hmem))
  change g (fun n => decide (c.π.app k x ∈ Eₖ n)) = f.1 x
  dsimp only [g]
  rw [dite_eq_left hmem]
  exact (hn : f.1 x = _).symm

private theorem constructibleFunctionDescent : ConstructibleFunctionDescent.{u, v, w} :=
  constructibleFunctionDescent_of_setDescent constructibleSetDescent

private abbrev LocallyConstantFunctionDescent : Prop :=
  ∀ (I : Type (max v w)) [Category.{w} I] [IsCofiltered I]
    (D : I ⥤ Scheme.{u}) (c : Cone D), IsLimit c →
    (∀ i, IsAffine (D.obj i)) → IsAffine c.pt →
    ∀ (i : I) (g : constructibleFunctionSubgroup (D.obj i)),
      IsLocallyConstant (g.1 ∘ c.π.app i) →
      ∃ (j : I) (a : j ⟶ i), IsLocallyConstant (g.1 ∘ D.map a)

private lemma exists_constructible_preimage_empty_of_affine_limit
    {I : Type u} [Category.{u} I] [IsCofiltered I]
    (D : I ⥤ Scheme.{u}) (c : Cone D) (hc : IsLimit c)
    [∀ i, IsAffine (D.obj i)] (i : I) (S : Set (D.obj i))
    (hS : IsConstructible S) (h : (c.π.app i) ⁻¹' S = ∅) :
    ∃ (j : I) (a : j ⟶ i), (D.map a) ⁻¹' S = ∅ := by
  let hspectral (j : I) : SpectralSpace (D.obj j) := ⟨⟩
  have : ∀ {j k : I} (a : j ⟶ k), IsAffineHom (D.map a) := fun _ => inferInstance
  let F := D ⋙ Scheme.forgetToTop
  let ht := isLimitOfPreserves Scheme.forgetToTop hc
  let e := ht.conePointUniqueUpToIso (limit.isLimit F)
  have he (x : (limit F : TopCat.{u})) : c.π.app i (e.inv x) = limit.π F i x :=
    ConcreteCategory.congr_hom (ht.conePointUniqueUpToIso_inv_comp (limit.isLimit F) i :
      e.inv ≫ Scheme.forgetToTop.map (c.π.app i) = limit.π F i) x
  obtain ⟨j, a, ha⟩ :=
    SpectralLimits.exists_map_preimage_subset_of_preimage_limit_π_subset F
      hspectral (fun a => (D.map a).isSpectralMap) i S ∅
      hS.isClosed_constructibleTopology
      (@isOpen_empty (D.obj i) (constructibleTopology (D.obj i))) fun x hx =>
        h.subset (show e.inv x ∈ (c.π.app i) ⁻¹' S from
          Set.mem_preimage.mpr (by rw [he x]; exact hx))
  exact ⟨j, a, Set.subset_empty_iff.mp ha⟩

private lemma exists_constructible_preimage_eq_of_affine_limit
    {I : Type u} [Category.{u} I] [IsCofiltered I]
    (D : I ⥤ Scheme.{u}) (c : Cone D) (hc : IsLimit c)
    [∀ i, IsAffine (D.obj i)] (i : I) (S T : Set (D.obj i))
    (hS : IsConstructible S) (hT : IsConstructible T)
    (h : (c.π.app i) ⁻¹' S = (c.π.app i) ⁻¹' T) :
    ∃ (j : I) (a : j ⟶ i), (D.map a) ⁻¹' S = (D.map a) ⁻¹' T := by
  have hbad : (c.π.app i) ⁻¹' ((S ∩ Tᶜ) ∪ (T ∩ Sᶜ)) = ∅ := by
    rw [Set.preimage_union, Set.preimage_inter, Set.preimage_inter,
      Set.preimage_compl, Set.preimage_compl, h]
    simp
  obtain ⟨j, a, ha⟩ := exists_constructible_preimage_empty_of_affine_limit D c hc i
    ((S ∩ Tᶜ) ∪ (T ∩ Sᶜ)) ((hS.inter hT.compl).union (hT.inter hS.compl)) hbad
  refine ⟨j, a, Set.ext fun x => ?_⟩
  have hx : D.map a x ∉ (S ∩ Tᶜ) ∪ (T ∩ Sᶜ) := Set.eq_empty_iff_forall_notMem.mp ha x
  simpa only [Set.mem_preimage] using
    (show D.map a x ∈ S ↔ D.map a x ∈ T from
      ⟨fun hs => by_contra fun ht => hx (Or.inl ⟨hs, ht⟩),
       fun ht => by_contra fun hs => hx (Or.inr ⟨ht, hs⟩)⟩)

private lemma exists_isOpen_preimage_of_isClopen_preimage
    {I : Type u} [Category.{u} I] [IsCofiltered I]
    (D : I ⥤ Scheme.{u}) (c : Cone D) (hc : IsLimit c)
    [∀ i, IsAffine (D.obj i)] [IsAffine c.pt]
    (i : I) (S : Set (D.obj i)) (hS : IsConstructible S)
    (h : IsClopen ((c.π.app i) ⁻¹' S)) :
    ∃ (j : I) (a : j ⟶ i), IsOpen ((D.map a) ⁻¹' S) := by
  have hclosed : IsClosed ((c.π.app i) ⁻¹' S : Set c.pt) := h.isClosed
  obtain ⟨j, V, hV, he⟩ := exists_preimage_eq_gen hc
    ⟨(c.π.app i) ⁻¹' S, h.isOpen⟩ hclosed.isCompact
  let k := IsCofiltered.min i j
  let a : k ⟶ i := IsCofiltered.minToLeft i j
  let b : k ⟶ j := IsCofiltered.minToRight i j
  have hpre (l m : I) (f : l ⟶ m) (T : Set (D.obj m)) :
      (c.π.app l) ⁻¹' ((D.map f) ⁻¹' T) = (c.π.app m) ⁻¹' T := by
    change ((c.π.app l) ≫ D.map f) ⁻¹' T = _
    rw [c.w]
  have he' : (c.π.app k) ⁻¹' ((D.map a) ⁻¹' S) =
      (c.π.app k) ⁻¹' ((D.map b) ⁻¹' (V : Set (D.obj j))) := by
    rw [hpre, hpre]
    exact (congrArg (fun W : c.pt.Opens => (W : Set c.pt)) he).symm
  obtain ⟨l, d, hd⟩ := exists_constructible_preimage_eq_of_affine_limit D c hc k
    ((D.map a) ⁻¹' S) ((D.map b) ⁻¹' (V : Set (D.obj j)))
    ((D.map a).isConstructible_preimage hS)
    ((D.map b).isConstructible_preimage (hV.isConstructible V.isOpen)) he'
  refine ⟨l, d ≫ a, ?_⟩
  rw [D.map_comp]
  change IsOpen ((D.map d) ⁻¹' ((D.map a) ⁻¹' S))
  rw [hd]
  exact (V.isOpen.preimage (D.map b).continuous).preimage (D.map d).continuous

private lemma locallyConstantFunctionDescent_small : LocallyConstantFunctionDescent.{u, u, u} := by
  classical
  intro I _ _ D c hc hD hC i g hg
  let : ∀ i, IsAffine (D.obj i) := hD
  let : IsAffine c.pt := hC
  let A := Set.range g.1
  have hA : A.Finite := finite_range_of_isConstructibleFunction_of_affine g.2
  let : Finite A := hA
  have hlev (n : A) : ∃ (j : I) (a : j ⟶ i),
      IsOpen ((D.map a) ⁻¹' (g.1 ⁻¹' {n.1})) :=
    exists_isOpen_preimage_of_isClopen_preimage D c hc i _
      (constructible_fibers_of_isConstructibleFunction_of_affine g.2 n.1)
      (hg.isClopen_fiber n.1)
  choose j a ha using hlev
  let K : A → Over i := fun n => Over.mk (a n)
  obtain ⟨t, ht⟩ := IsCofiltered.inf_objs_exists (Set.range K).toFinite.toFinset
  let b (n : A) : t ⟶ K n := (ht (by simp)).some
  refine ⟨t.left, t.hom, IsLocallyConstant.iff_isOpen_fiber.mpr fun n => ?_⟩
  by_cases hn : n ∈ A
  · let m : A := ⟨n, hn⟩
    have hm : D.map (b m).left ≫ D.map (a m) = D.map t.hom := by
      rw [← D.map_comp]
      exact congrArg D.map (Over.w (b m))
    have hopen := (ha m).preimage (D.map (b m).left).continuous
    change IsOpen (((D.map (b m).left ≫ D.map (a m)) ⁻¹' (g.1 ⁻¹' {n}))) at hopen
    change IsOpen ((D.map t.hom) ⁻¹' (g.1 ⁻¹' {n}))
    rwa [hm] at hopen
  · have hempty : (g.1 ∘ D.map t.hom) ⁻¹' {n} = ∅ :=
      Set.eq_empty_iff_forall_notMem.mpr fun x hx => hn ⟨D.map t.hom x, hx⟩
    rw [hempty]
    exact isOpen_empty

private theorem locallyConstantFunctionDescent [UnivLE.{max v w, u}] :
    LocallyConstantFunctionDescent.{u, v, w} := by
  intro I _ _ D c hc hD hC i g hg
  let : UnivLE.{w, max v w} := by simpa only [max_comm] using univLE_max.{w, v}
  let : UnivLE.{w, u} := UnivLE.trans.{w, max v w, u}
  let : LocallySmall.{u} I := ⟨fun _ _ => inferInstance⟩
  let e := equivSmallModel.{u} I
  let : IsCofiltered (SmallModel.{u} I) := IsCofiltered.of_equivalence e
  let g' := constructibleFunctionPullback (D.map (e.unitIso.inv.app i)) g
  have he : (fun x => g'.1 ((c.whisker e.inverse).π.app (e.functor.obj i) x)) =
      g.1 ∘ c.π.app i := by
    funext x
    change g.1 ((c.π.app _ ≫ D.map (e.unitIso.inv.app i)) x) = _
    rw [c.w]
    rfl
  obtain ⟨j, a, ha⟩ := locallyConstantFunctionDescent_small (SmallModel.{u} I)
    (e.inverse ⋙ D) (c.whisker e.inverse) (hc.whiskerEquivalence e.symm)
    (fun j => hD _) hC (e.functor.obj i) g' (by simpa only [Function.comp_def, he] using hg)
  refine ⟨e.inverse.obj j, e.inverse.map a ≫ e.unitIso.inv.app i, ?_⟩
  rw [D.map_comp]
  exact ha

private theorem limitPreserving_constructibleFunctionQuotientPresheaf
    (hcon : ConstructibleFunctionDescent.{u, v, w})
    (hloc : LocallyConstantFunctionDescent.{u, v, w}) :
    AlgebraicGeometry.LimitPreserving.{u, u, v, w, u + 1, u}
      (𝟭 Scheme.{u})
      (constructibleFunctionQuotientPresheaf ⋙ forget AddCommGrpCat.{u}) := by
  intro I _ _ D c hc hD hC
  apply isColimit_mapCocone_of_exists_of_eventually_eq
  · intro x
    induction x using Quotient.inductionOn with
    | h f =>
      obtain ⟨i, g, hg⟩ := hcon I D c hc hD hC f
      exact ⟨i, QuotientAddGroup.mk g, congrArg QuotientAddGroup.mk hg⟩
  · intro i x y hxy
    induction x using Quotient.inductionOn with
    | h x =>
      induction y using Quotient.inductionOn with
      | h y =>
        have hlocal : IsLocallyConstant ((x - y).1 ∘ c.π.app i) := by
          change QuotientAddGroup.mk (constructibleFunctionPullback (c.π.app i) x) =
            QuotientAddGroup.mk (constructibleFunctionPullback (c.π.app i) y) at hxy
          exact (QuotientAddGroup.eq_zero_iff _).mp (sub_eq_zero.mpr hxy)
        obtain ⟨j, a, ha⟩ := hloc I D c hc hD hC i (x - y) hlocal
        exact ⟨j, a, sub_eq_zero.mp ((QuotientAddGroup.eq_zero_iff _).mpr ha)⟩

private theorem limitPreserving_constructibleFunctionQuotientPresheaf_ulift
    (hcon : ConstructibleFunctionDescent.{u, v, w})
    (hloc : LocallyConstantFunctionDescent.{u, v, w}) :
    AlgebraicGeometry.LimitPreserving.{u, u + 1, v, w, u + 1, u}
      (𝟭 Scheme.{u})
      ((constructibleFunctionQuotientPresheaf ⋙ AddCommGrpCat.uliftFunctor.{u + 1}) ⋙
        forget AddCommGrpCat.{u + 1}) := by
  intro I _ _ D c hc hD hC
  obtain ⟨h⟩ := limitPreserving_constructibleFunctionQuotientPresheaf
    hcon hloc I D c hc hD hC
  apply isColimit_mapCocone_of_exists_of_eventually_eq
  · intro x
    obtain ⟨i, y, hy⟩ := Types.jointly_surjective_of_isColimit h x.down
    exact ⟨i.unop, ULift.up y, congrArg ULift.up hy⟩
  · intro i x y hxy
    obtain ⟨j, f, hf⟩ := (Types.FilteredColimit.isColimit_eq_iff' h x.down y.down).mp
      (congrArg ULift.down hxy)
    exact ⟨j.unop, f.unop, congrArg ULift.up hf⟩

private theorem limitPreserving_constructibleFunctionQuotientSheaf_of_typeSheafification
    (h : AlgebraicGeometry.LimitPreserving.{u, u + 1, v, w, u + 1, u}
      (𝟭 Scheme.{u})
      (sheafify Scheme.etaleTopology
        ((constructibleFunctionQuotientPresheaf ⋙ AddCommGrpCat.uliftFunctor.{u + 1}) ⋙
          forget AddCommGrpCat.{u + 1}))) :
    AlgebraicGeometry.LimitPreserving.{u, u + 1, v, w, u + 1, u}
      (𝟭 Scheme.{u})
      (constructibleFunctionQuotientSheaf.obj ⋙ forget AddCommGrpCat.{u + 1}) := by
  intro I _ _ D c hc hD hC
  obtain ⟨hcol⟩ := h I D c hc hD hC
  let P := constructibleFunctionQuotientPresheaf ⋙ AddCommGrpCat.uliftFunctor.{u + 1}
  let e := sheafifyComposeIso Scheme.etaleTopology
    (forget AddCommGrpCat.{u + 1}) P
  exact ⟨IsColimit.mapCoconeEquiv e hcol⟩

private lemma limitPreserving_bigEtaleSheaf_of_limitPreserving_sheafification
    (B : BigEtaleSite.{u})
    (h : AlgebraicGeometry.LimitPreserving.{u, u + 1, v, w, u + 1, u}
      (𝟭 Scheme.{u}) (constructibleFunctionQuotientSheaf.obj ⋙
        forget AddCommGrpCat.{u + 1})) :
    AlgebraicGeometry.LimitPreserving.{u, u, v, w, u + 1, u}
      B.inclusion ((constructibleFunctionQuotientBigEtaleSheaf B).obj ⋙
        forget AddCommGrpCat.{u}) := by
  intro I _ _ D c hc hD hC
  obtain ⟨hcol⟩ := h I (D ⋙ B.inclusion) (B.inclusion.mapCone c) hc hD hC
  let e := Functor.isoWhiskerRight constructibleFunctionQuotientSmallSheafIso
    (forget AddCommGrpCat.{u + 1})
  exact ⟨isColimitOfReflects uliftFunctor.{u + 1}
    (IsColimit.mapCoconeEquiv e.symm hcol)⟩

private theorem limitPreserving_bigEtaleSheaf_of_descent
    (B : BigEtaleSite.{u})
    (hcon : ConstructibleFunctionDescent.{u, v, w})
    (hloc : LocallyConstantFunctionDescent.{u, v, w})
    (hcover : AffineCoversDescend.{u, v, w}
      (𝟭 Scheme.{u}) Scheme.etaleTopology) :
    AlgebraicGeometry.LimitPreserving.{u, u, v, w, u + 1, u}
      B.inclusion ((constructibleFunctionQuotientBigEtaleSheaf B).obj ⋙
        forget AddCommGrpCat.{u}) := by
  apply limitPreserving_bigEtaleSheaf_of_limitPreserving_sheafification
  apply limitPreserving_constructibleFunctionQuotientSheaf_of_typeSheafification
  let P : Scheme.{u}ᵒᵖ ⥤ Type (u + 1) :=
    (constructibleFunctionQuotientPresheaf ⋙ AddCommGrpCat.uliftFunctor.{u + 1}) ⋙
      forget AddCommGrpCat.{u + 1}
  intro I _ _ D c hc hD hC
  obtain ⟨hcol⟩ := limitPreserving_sheafify_of_cover_descent
    (𝟭 Scheme.{u}) Scheme.etaleTopology hcover finiteAffineRefinements_etale P
    (limitPreserving_constructibleFunctionQuotientPresheaf_ulift hcon hloc) I D c hc hD hC
  exact ⟨IsColimit.mapCoconeEquiv
    (plusPlusIsoSheafify Scheme.etaleTopology (Type (u + 1)) P) hcol⟩

private theorem limitPreserving_constructibleFunctionQuotientBigEtaleSheaf
    (B : BigEtaleSite.{u}) [UnivLE.{max v w, u}] :
    AlgebraicGeometry.LimitPreserving.{u, u, v, w, u + 1, u}
      B.inclusion ((constructibleFunctionQuotientBigEtaleSheaf B).obj ⋙
        forget AddCommGrpCat.{u}) :=
  limitPreserving_bigEtaleSheaf_of_descent B constructibleFunctionDescent
    locallyConstantFunctionDescent affineCoversDescend_etale

/-- A nonzero limit-preserving étale sheaf of abelian groups which vanishes on fields
and whose restriction maps along thickenings are isomorphisms. -/
@[stacks 05LH]
public theorem exists_nonzero_limitPreserving_sheaf_vanishing_on_fields
    (B : BigEtaleSite.{u}) [UnivLE.{max v w, u}] :
    ∃ G : Sheaf B.topology AddCommGrpCat.{u},
      (∀ (k : Type u) [Field k] (hk : B.Contains (Spec (.of k))),
        IsZero (G.obj.obj (Opposite.op (B.obj (Spec (.of k)) hk)))) ∧
      AlgebraicGeometry.LimitPreserving.{u, u, v, w, u + 1, u}
        B.inclusion (G.obj ⋙ forget AddCommGrpCat.{u}) ∧
      (∀ (X X' : Scheme.{u}) (hX : B.Contains X) (hX' : B.Contains X')
        (i : X ⟶ X'), Stacks.Thickenings.IsThickening i →
          IsIso (G.obj.map (ObjectProperty.homMk i :
            B.obj X hX ⟶ B.obj X' hX').op)) ∧
      (∃ X : B.Scheme, ¬ IsZero (G.obj.obj (Opposite.op X))) :=
  ⟨constructibleFunctionQuotientBigEtaleSheaf B,
    fun k _ _ => constructibleFunctionQuotientSmallSheaf_spec_field_isZero k,
    limitPreserving_constructibleFunctionQuotientBigEtaleSheaf B,
    fun _ _ _ _ _ hi => constructibleFunctionQuotientSmallSheaf_map_isIso_of_thickening hi,
    exists_nonzero_constructibleFunctionQuotientSmallSheaf B⟩

end Stacks.Examples.ConstructibleFunctionSheaf
