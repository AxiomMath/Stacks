module

public import Mathlib.AlgebraicGeometry.IdealSheaf.Subscheme
public import Mathlib.CategoryTheory.Comma.Over.Pullback
public import Mathlib.CategoryTheory.Limits.Constructions.Over.Connected
public import Mathlib.CategoryTheory.Limits.Types.Filtered
public import StacksCore.Tactic.StacksAttribute
public import StacksFrontier.AlgebraicGeometry.Flatness.FlatteningFunctor.FlatDimensionFunctor
public import StacksFrontier.AlgebraicGeometry.Flatness.FlatteningFunctor.LimitPreserving
public import StacksFrontier.AlgebraicGeometry.Flatness.FlatteningFunctor.ModuleIsoFlatness
public import StacksFrontier.AlgebraicGeometry.GenericFlatness.ImageBaseChangeGeneric
public import StacksFrontier.AlgebraicGeometry.Limits.DescendingMorphisms.ClosedImmersion
public import StacksFrontier.AlgebraicGeometry.Limits.DescendingMorphisms.Relative
public import StacksFrontier.AlgebraicGeometry.Limits.FibreDimensionEnlargement
public import StacksFrontier.AlgebraicGeometry.Morphisms.CohenMacaulay.FlatLocus
public import StacksFrontier.AlgebraicGeometry.Morphisms.FibreDimension.Basic
public import StacksFrontier.AlgebraicGeometry.Morphisms.FlatMorphisms.EtaleBase
public import StacksFrontier.AlgebraicGeometry.Morphisms.ImmersionsAndAffine.FinitePresentationOpenImmersion
public import StacksFrontier.AlgebraicGeometry.ObjectDescent.Basic
public import StacksFrontier.Topology.Spectral.ConstructibleTopology

/-!
# The functor of flatness in dimensions at least `n` is limit preserving

Let `f : X ⟶ S` be a quasi-compact morphism of schemes which is locally of finite presentation,
let `F` be a quasi-coherent `𝒪_X`-module of finite presentation and let `n` be a natural number.
Then the functor `F_n` of flatness in dimensions `≥ n` of Stacks 05MT is limit preserving: it
carries a cofiltered inverse limit of affine schemes over `S` to a filtered colimit of sets.

Since `F_n` is subterminal the colimit statement reduces to a single assertion: if `F_T` is flat
over `T` in dimensions `≥ n` for `T = lim T_i`, then `F_{T_i}` is already flat over `T_i` in
dimensions `≥ n` for some index `i`.  The source's proof, which is reproduced here, goes as
follows.  Fixing a stage `i₀` and replacing `X ⟶ S` by its base change `X_{i₀} ⟶ T_{i₀}`, the
total space becomes quasi-compact over an affine base, so it is covered by finitely many affine
opens whose disjoint union is a surjective étale cover of finite presentation; flatness in
dimensions `≥ n` may be tested after that cover, so one may assume the morphism is of finite
presentation.  Over the limit, the non-flat locus `Z` of `F_T` is closed and its fibres have
dimension `< n`; Stacks 05M6 enlarges it to a closed subscheme `Z' ⊆ X_T` whose closed immersion
is of finite presentation and whose fibres still have dimension `< n`.  Stacks 01ZM and 01ZP
descend `Z' ⊆ X_T` to a closed immersion `Z'_i ⊆ X_i` of finite presentation at some stage,
Stacks 05M5 keeps all of its fibres of dimension `< n` after a further stage, and — because
`X_T \ Z'` is quasi-compact, `Z' ⟶ X_T` being of finite presentation — Stacks 05LY arranges
flatness of `F_i` away from `Z'_i`.  At that stage the non-flat locus of `F_i` is contained in
`Z'_i`, whose fibres have dimension `< n`, so `F_i` is flat over `T_i` in dimensions `≥ n`.

## Main results

* `AlgebraicGeometry.FlatDimensionSituation.flatDimensionFunctor_limitPreserving`: **Stacks
  05MV**, part (2): the functor `F_n` is limit preserving for a quasi-compact morphism locally
  of finite presentation and a module of finite presentation.  The whole of Stacks 05MV, parts
  (1) and (2) together, is
  `AlgebraicGeometry.FlatDimensionSituation.flatDimensionFunctor_isSheaf_fpqc_and_limitPreserving`
  in
  `StacksFrontier.AlgebraicGeometry.Flatness.FlatteningFunctor.FlatDimensionSheafAndLimitPreserving`.
* `AlgebraicGeometry.isFlatOver_iff_isFlatOverInDimensionsGE_zero`: flatness in dimensions `≥ 0`
  is flatness.

## Implementation notes

The case `n = 0` is separated off: flatness in dimensions `≥ 0` is flatness, so there `F_n` is
the flatness functor of Stacks 05MW and limit preservation is Stacks 05MY.  For `n > 0` the
dimension bound `< n` on fibres is turned into the bound `≤ n - 1` that Stacks 05M5 and 05M6
take, which is where positivity of `n` is used.

The object and morphism universes of the index category of the tested inverse system are
independent of each other and of the universe of the schemes, exactly as for Stacks 05MY; the
scheme universe is the maximum of those two and a third parameter.  That maximum is what makes
the index category essentially small relative to the schemes, which is the hypothesis of Stacks
05M5; the helper `exists_fiber_dimension_le_baseChange` is stated for a general index category
and therefore carries that smallness as an explicit instance argument, applied only to slices
`Over i` of the ambient index category, which inherit it.

## References

* [Stacks Project, Tag 05MV](https://stacks.math.columbia.edu/tag/05MV)
* [Stacks Project, Tag 05MT](https://stacks.math.columbia.edu/tag/05MT)
* [Stacks Project, Tag 05MY](https://stacks.math.columbia.edu/tag/05MY)
* [Stacks Project, Tag 05M5](https://stacks.math.columbia.edu/tag/05M5)
* [Stacks Project, Tag 05M6](https://stacks.math.columbia.edu/tag/05M6)
* [Stacks Project, Tag 05LY](https://stacks.math.columbia.edu/tag/05LY)
* [Stacks Project, Tag 0CWG](https://stacks.math.columbia.edu/tag/0CWG)
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits Topology TopologicalSpace
open RingedSpaceModuleAdjunction
open Stacks.GenericFlatness (finitePresentation_pullback)

universe u v w z t r

namespace AlgebraicGeometry

attribute [local instance] SheafOfModules.modulePullback_isQuasicoherent
  Stacks.SheafOfModules.modulePullback_isFinitePresentation

/-- The base change of a scheme over `S` along `T ⟶ S` is again locally of finite type over
the new base, in the form in which the statements below meet it. -/
private instance overPullbackHom_locallyOfFiniteType {S T : Scheme.{u}} (g : T ⟶ S)
    (X : Over S) [LocallyOfFiniteType X.hom] :
    LocallyOfFiniteType ((Over.pullback g).obj X).hom :=
  inferInstanceAs (LocallyOfFiniteType (pullback.snd X.hom g))

/-- The left component of an isomorphism in an over category is an isomorphism. -/
private instance over_isIso_left {S : Scheme.{u}} {X Y : Over S} (e : X ⟶ Y) [IsIso e] :
    IsIso e.left :=
  inferInstanceAs (IsIso ((Over.forget S).map e))

/-- The structure morphism of `Over.mk f` is `f`, so it is locally of finite type if `f` is. -/
private instance overMk_locallyOfFiniteType {X S : Scheme.{u}} (f : X ⟶ S)
    [LocallyOfFiniteType f] : LocallyOfFiniteType (Over.mk f).hom :=
  ‹_›

/-- The pullback of a quasi-coherent module along a morphism of schemes is quasi-coherent. -/
private instance modules_pullback_isQuasicoherent {X Y : Scheme.{u}} (q : Y ⟶ X) (F : X.Modules)
    [F.IsQuasicoherent] : ((Scheme.Modules.pullback q).obj F).IsQuasicoherent :=
  @SheafOfModules.modulePullback_isQuasicoherent _ _ q.toLRSHom.toShHom F ‹_›

/-- The pullback of a module of finite type along a morphism of schemes is of finite type. -/
private instance modules_pullback_isFiniteType {X Y : Scheme.{u}} (q : Y ⟶ X) (F : X.Modules)
    [F.IsFiniteType] : ((Scheme.Modules.pullback q).obj F).IsFiniteType :=
  SheafOfModules.pullback_isFiniteType q.toLRSHom.toShHom F

/-- Flatness over the base in dimensions `≥ n` only depends on the morphism to the base
through its value, so it transports along an equality of morphisms. -/
private theorem flatInDimensions_congr {X S : Scheme.{u}} {f g : X ⟶ S} (hfg : f = g)
    [LocallyOfFiniteType f] [LocallyOfFiniteType g] (F : X.Modules)
    [F.IsQuasicoherent] [F.IsFiniteType] (n : ℕ)
    (h : IsFlatOverInDimensionsGE f F n) : IsFlatOverInDimensionsGE g F n := by
  subst hfg
  exact h

private theorem topologicalKrullDim_fiber_closed_bad_locus_le
    {X S Z : Scheme.{u}} (f : X ⟶ S) (F : X.Modules) (i : Z ⟶ X)
    [IsClosedImmersion i] (hbad : Set.range i =
      {x : X | ¬ IsFlatOverAt f.toLRSHom.toShHom F x}) (s : S) :
    topologicalKrullDim ((i ≫ f).fiber s) ≤
      topologicalKrullDim {x : f.fiber s // ¬ IsFlatOverAt
        f.toLRSHom.toShHom F (f.fiberι s x)} := by
  let g := i ≫ f
  let A : Set Z := {z | g z = s}
  let B : Set X := f ⁻¹' {s}
  let C := {x : f.fiber s // ¬ IsFlatOverAt
    f.toLRSHom.toShHom F (f.fiberι s x)}
  let k : A → B := fun z => ⟨i z.1, z.2⟩
  have hkcont : Continuous k :=
    (i.continuous.comp continuous_subtype_val).subtype_mk _
  have hkemb : IsEmbedding k := IsEmbedding.of_comp hkcont continuous_subtype_val
    (i.isClosedEmbedding.isEmbedding.comp IsEmbedding.subtypeVal)
  let ψ : A → f.fiber s := fun z => (f.fiberHomeo s).symm (k z)
  have hψemb : IsEmbedding ψ := (f.fiberHomeo s).symm.isEmbedding.comp hkemb
  let φ : A → C := fun z => ⟨ψ z, by
    have hzbad : ¬ IsFlatOverAt f.toLRSHom.toShHom F (i z.1) := by
      have hr : i z.1 ∈ Set.range i := ⟨z.1, rfl⟩
      have hr' : i z.1 ∈ {x : X | ¬ IsFlatOverAt
          f.toLRSHom.toShHom F x} := hbad ▸ hr
      simpa only [Set.mem_setOf_eq] using hr'
    simpa [ψ, k, Scheme.Hom.fiberι_fiberHomeo_symm] using hzbad⟩
  have hφcont : Continuous φ := hψemb.continuous.subtype_mk _
  have hφemb : IsEmbedding φ := IsEmbedding.of_comp hφcont continuous_subtype_val hψemb
  exact ((g.fiberHomeo s).isHomeomorph.topologicalKrullDim_eq).trans_le
    hφemb.isInducing.topologicalKrullDim_le

private theorem closed_bad_locus_subscheme
    {X S : Scheme.{u}} (f : X ⟶ S) (F : X.Modules)
    [F.IsQuasicoherent] [F.IsFinitePresentation]
    [LocallyOfFinitePresentation f] :
    ∃ (Z : Scheme.{u}) (i : Z ⟶ X), IsClosedImmersion i ∧
      Set.range i = {x : X | ¬ IsFlatOverAt f.toLRSHom.toShHom F x} := by
  classical
  let bad : Set X := {x | ¬ IsFlatOverAt f.toLRSHom.toShHom F x}
  have hopen : IsOpen ({x : X | IsFlatOverAt f.toLRSHom.toShHom F x}) :=
    isOpen_setOf_flatOverAt f F
  have hclosed : IsClosed bad := by
    simpa [bad, Set.compl_setOf] using hopen.isClosed_compl
  let I : X.IdealSheafData := Scheme.IdealSheafData.vanishingIdeal ⟨bad, hclosed⟩
  let i := I.subschemeι
  refine ⟨I.subscheme, i, ?_, ?_⟩
  · infer_instance
  · simpa [i, I, bad] using Scheme.IdealSheafData.range_subschemeι I

private theorem withBotENat_lt_nat_le_pred {n : ℕ}
    (a : WithBot ℕ∞) (ha : a < (n : WithBot ℕ∞)) :
    a ≤ ((n - 1 : ℕ) : WithBot ℕ∞) := by
  cases a with
  | bot => simp
  | coe d =>
    have hd : d < (n : ℕ∞) := WithBot.coe_lt_coe.mp ha
    cases d with
    | top => simp at hd
    | coe m =>
      exact WithBot.coe_le_coe.mpr (WithTop.coe_le_coe.mpr
        (Nat.le_pred_of_lt (WithTop.coe_lt_coe.mp hd)))

private theorem trdeg_residueField_eq_of_etale {A B S : Scheme.{u}}
    (q : A ⟶ B) [Etale q] (p : B ⟶ S) (a : A) :
    letI : Algebra (S.residueField (p (q a))) (B.residueField (q a)) :=
      ((S.residueFieldCongr rfl).inv ≫ p.residueFieldMap (q a)).hom.toAlgebra
    letI : Algebra (S.residueField (p (q a))) (A.residueField a) :=
      ((S.residueFieldCongr rfl).inv ≫ (q ≫ p).residueFieldMap a).hom.toAlgebra
    Algebra.trdeg (S.residueField (p (q a))) (B.residueField (q a)) =
      Algebra.trdeg (S.residueField (p (q a))) (A.residueField a) := by
  let K := S.residueField (p (q a))
  let E := B.residueField (q a)
  let L := A.residueField a
  let : Algebra K E :=
    ((S.residueFieldCongr rfl).inv ≫ p.residueFieldMap (q a)).hom.toAlgebra
  let : Algebra E L := (q.residueFieldMap a).hom.toAlgebra
  let : Algebra K L :=
    ((S.residueFieldCongr rfl).inv ≫ (q ≫ p).residueFieldMap a).hom.toAlgebra
  have hcomp : (algebraMap E L).comp (algebraMap K E) = algebraMap K L := by
    ext z
    show (q.residueFieldMap a).hom
        (((S.residueFieldCongr rfl).inv ≫ p.residueFieldMap (q a)).hom z) =
      ((S.residueFieldCongr rfl).inv ≫ (q ≫ p).residueFieldMap a).hom z
    simp [Scheme.residueFieldCongr_refl, Scheme.residueFieldMap_comp,
      CategoryTheory.Iso.refl_inv]
    rfl
  let : IsScalarTower K E L := IsScalarTower.of_algebraMap_eq' hcomp.symm
  have : Algebra.IsAlgebraic E L := by
    have : FormallyUnramified q := inferInstance
    have : LocallyOfFiniteType q := inferInstance
    exact (inferInstance : Algebra.IsSeparable E L).isAlgebraic
  have h := trdeg_add_eq (R := K) (S := E) (A := L)
  rw [trdeg_eq_zero (R := E) (A := L), add_zero] at h
  simpa [K, E, L] using h

private theorem flatInDimensions_comp_etale_iff
    {X X' S : Scheme.{u}} (f : X ⟶ S) [LocallyOfFiniteType f]
    (F : X.Modules) [F.IsQuasicoherent] [F.IsFiniteType]
    (q : X' ⟶ X) [Etale q] (hq : Function.Surjective q)
    [((Scheme.Modules.pullback q).obj F).IsQuasicoherent]
    [((Scheme.Modules.pullback q).obj F).IsFiniteType] (n : ℕ) :
    IsFlatOverInDimensionsGE (q ≫ f) ((Scheme.Modules.pullback q).obj F) n ↔
      IsFlatOverInDimensionsGE f F n := by
  have : Flat q := (Etale.iff_flat_and_formallyUnramified).mp inferInstance |>.1
  rw [isFlatOverInDimensionsGE_iff_forall_toENat_trdeg_lt,
    isFlatOverInDimensionsGE_iff_forall_toENat_trdeg_lt]
  have hflatEq (x' : X') := isFlatOverAt_iff_modulePullback_isFlatOverAt
    q f F x' (Flat.stalkMap q x')
  have htr (x' : X') := congrArg (fun c : Cardinal => (Cardinal.toENat c : WithBot ℕ∞))
    (trdeg_residueField_eq_of_etale q f x')
  refine ⟨fun h x hnonflat => ?_, fun h x' hnonflat' => ?_⟩
  · obtain ⟨x', rfl⟩ := hq x
    exact lt_of_eq_of_lt (htr x') (h x' (mt (hflatEq x').mpr hnonflat))
  · exact lt_of_eq_of_lt (htr x').symm (h (q x') (mt (hflatEq x').mp hnonflat'))

/-- A morphism that is locally of finite presentation, quasi-compact and quasi-separated is of
finite presentation. -/
private theorem finitePresentation_of_instances {X S : Scheme.{u}} (f : X ⟶ S)
    [LocallyOfFinitePresentation f] [QuasiCompact f] [QuasiSeparated f] :
    FinitePresentation f :=
  ⟨inferInstance, inferInstance, inferInstance⟩

private theorem exists_affine_etale_cover_of_finitePresentation
    {X S : Scheme.{u}} (f : X ⟶ S) [IsAffine S]
    [QuasiCompact f] [LocallyOfFinitePresentation f] :
    ∃ (A : Scheme.{u}) (q : A ⟶ X), IsAffine A ∧ Surjective q ∧ Etale q ∧
      FinitePresentation (q ≫ f) := by
  let : CompactSpace S := Scheme.compactSpace_of_isAffine S
  let : CompactSpace X := QuasiCompact.compactSpace_of_compactSpace f
  let Ucover := X.affineCover.finiteSubcover
  let : Finite Ucover.I₀ := inferInstance
  let (k : Ucover.I₀) : IsAffine (Ucover.X k) := by
    dsimp [Ucover]
    infer_instance
  let A := ∐ Ucover.X
  let : IsAffine A := by infer_instance
  let q : A ⟶ X := Sigma.desc Ucover.f
  let : Surjective q := by
    dsimp [q]
    infer_instance
  let (k : Ucover.I₀) : Etale (Ucover.f k) := by infer_instance
  let : Etale q := by
    let : IsZariskiLocalAtSource (@Etale) :=
      HasRingHomProperty.instIsZariskiLocalAtSource
    dsimp [q]
    apply IsZariskiLocalAtSource.sigmaDesc
    intro k
    infer_instance
  let (k : Ucover.I₀) : LocallyOfFinitePresentation (Ucover.f k) := by
    infer_instance
  let : LocallyOfFinitePresentation q := by
    let : IsZariskiLocalAtSource (@LocallyOfFinitePresentation) :=
      HasRingHomProperty.instIsZariskiLocalAtSource
        (P := @LocallyOfFinitePresentation) (Q := RingHom.FinitePresentation)
    dsimp [q]
    apply IsZariskiLocalAtSource.sigmaDesc
    intro k
    infer_instance
  let : QuasiSeparated (q ≫ f) := by infer_instance
  let : QuasiCompact (q ≫ f) := by infer_instance
  let : LocallyOfFinitePresentation (q ≫ f) := by infer_instance
  exact ⟨A, q, inferInstance, inferInstance, inferInstance,
    finitePresentation_of_instances _⟩

private theorem exists_finitePresentation_bad_locus_enlargement
    {X S : Scheme.{u}} (f : X ⟶ S) [LocallyOfFiniteType f] (F : X.Modules) (n : ℕ)
    [F.IsQuasicoherent] [F.IsFiniteType] [F.IsFinitePresentation]
    [CompactSpace S] [QuasiSeparatedSpace S]
    (hfp : FinitePresentation f)
    (hDim : IsFlatOverInDimensionsGE f F n) :
    ∃ (Z : Scheme.{u}) (j : Z ⟶ X), IsClosedImmersion j ∧
      FinitePresentation j ∧
      (∀ s : S, topologicalKrullDim ((j ≫ f).fiber s) ≤
        ((n - 1 : ℕ) : WithBot ℕ∞)) ∧
      (∀ x : X, x ∉ Set.range j →
        IsFlatOverAt f.toLRSHom.toShHom F x) := by
  let : LocallyOfFinitePresentation f := hfp.1
  obtain ⟨Z₀, i, hi, hrange⟩ := closed_bad_locus_subscheme f F
  have hdim₀ : ∀ s : S, topologicalKrullDim ((i ≫ f).fiber s) ≤
      ((n - 1 : ℕ) : WithBot ℕ∞) := by
    intro s
    have hs : topologicalKrullDim
        {x : f.fiber s // ¬ IsFlatOverAt f.toLRSHom.toShHom F
          (f.fiberι s x)} < (n : WithBot ℕ∞) := by
      change IsFlatOverInDimensionsGE f F n at hDim
      exact hDim s
    exact (topologicalKrullDim_fiber_closed_bad_locus_le f F i hrange s).trans
      (withBotENat_lt_nat_le_pred _ hs)
  obtain ⟨Z, j, h, hj, hh, hfactor, hfpj, hdim⟩ :=
    exists_finitePresentation_closedImmersion_of_forall_topologicalKrullDim_fiber_le
      f hfp i (n - 1) hdim₀
  have hsubset : Set.range i ⊆ Set.range j := by
    intro x hx
    obtain ⟨z, rfl⟩ := hx
    refine ⟨h z, ?_⟩
    show j (h z) = i z
    rw [hfactor]
    rfl
  refine ⟨Z, j, hj, hfpj, hdim, ?_⟩
  intro x hx
  by_contra hflat
  have hbad : x ∈ {x : X | ¬ IsFlatOverAt f.toLRSHom.toShHom F x} := by
    simpa only [Set.mem_setOf_eq] using hflat
  have hi' : x ∈ Set.range i := hrange.symm ▸ hbad
  exact hx (hsubset hi')

private lemma topologicalKrullDim_le_of_range_subset
    {A B C : Type*} [TopologicalSpace A] [TopologicalSpace B] [TopologicalSpace C]
    {i : A → C} {j : B → C} (hi : IsEmbedding i) (hj : IsEmbedding j)
    (h : Set.range j ⊆ Set.range i) : topologicalKrullDim B ≤ topologicalKrullDim A := by
  calc
    topologicalKrullDim B = topologicalKrullDim (Set.range j) :=
      hj.toHomeomorph.isHomeomorph.topologicalKrullDim_eq
    _ = topologicalKrullDim (i ⁻¹' Set.range j) :=
      (hi.homeomorphOfSubsetRange h).isHomeomorph.topologicalKrullDim_eq.symm
    _ ≤ topologicalKrullDim A := IsEmbedding.subtypeVal.isInducing.topologicalKrullDim_le

private theorem flatInDimensions_of_closed_bad_locus
    {X S Z : Scheme.{u}} (f : X ⟶ S) [LocallyOfFiniteType f] (F : X.Modules)
    [F.IsQuasicoherent] [F.IsFiniteType] (n : ℕ)
    (i : Z ⟶ X) [IsClosedImmersion i]
    (hdim : ∀ s : S,
      topologicalKrullDim ((i ≫ f).fiber s) < (n : WithBot ℕ∞))
    (hflat : ∀ x : X, x ∉ Set.range i →
      IsFlatOverAt f.toLRSHom.toShHom F x) :
    IsFlatOverInDimensionsGE f F n := by
  intro s
  let A := (i ≫ f) ⁻¹' {s}
  let B := {x : f.fiber s // ¬ IsFlatOverAt
    f.toLRSHom.toShHom F (f.fiberι s x)}
  let k : A → X := fun z => i z.1
  let l : B → X := fun x => f.fiberι s x.1
  have hk : IsEmbedding k := i.isClosedEmbedding.isEmbedding.comp IsEmbedding.subtypeVal
  have hl : IsEmbedding l :=
    (IsPreimmersion.isEmbedding (f.fiberι s)).comp IsEmbedding.subtypeVal
  have hrange : Set.range l ⊆ Set.range k := by
    rintro x ⟨b, rfl⟩
    have hb : l b ∈ Set.range i := by
      by_contra hx
      exact b.2 (hflat _ hx)
    obtain ⟨z, hz⟩ := hb
    have hzs : (i ≫ f) z = s := by
      show f (i z) = s
      rw [hz]
      exact (f.fiberHomeo s b.1).property
    exact ⟨⟨z, hzs⟩, hz⟩
  have hle : topologicalKrullDim B ≤ topologicalKrullDim A :=
    topologicalKrullDim_le_of_range_subset hk hl hrange
  have heq : topologicalKrullDim ((i ≫ f).fiber s) = topologicalKrullDim A :=
    ((i ≫ f).fiberHomeo s).isHomeomorph.topologicalKrullDim_eq
  exact hle.trans_lt (heq ▸ hdim s)

private theorem flatOfFlatInDimensionsGE_zero
    {X S : Scheme.{u}} (f : X ⟶ S) [LocallyOfFiniteType f] (F : X.Modules)
    [F.IsQuasicoherent] [F.IsFiniteType]
    (h : IsFlatOverInDimensionsGE f F 0) :
    IsFlatOver f.toLRSHom.toShHom F := by
  intro x
  by_contra hbad
  let b : ↥{y : f.fiber (f x) |
      ¬ IsFlatOverAt f.toLRSHom.toShHom F (f.fiberι (f x) y)} :=
    ⟨f.asFiber x, by simpa using hbad⟩
  have hdimBot : topologicalKrullDim
      ↥{y : f.fiber (f x) |
        ¬ IsFlatOverAt f.toLRSHom.toShHom F (f.fiberι (f x) y)} = ⊥ := by
    cases hd : topologicalKrullDim
        ↥{y : f.fiber (f x) |
          ¬ IsFlatOverAt f.toLRSHom.toShHom F (f.fiberι (f x) y)} with
    | bot => rfl
    | coe d => simpa [hd] using h (f x)
  exact ((topologicalKrullDim_eq_bot_iff_isEmpty _).mp hdimBot).false b

/-- A module is flat over the base exactly when it is flat over the base in dimensions `≥ 0`: the
non-flat locus of every fibre then has dimension `< 0`, that is, it is empty. -/
theorem isFlatOver_iff_isFlatOverInDimensionsGE_zero
    {X S : Scheme.{u}} (f : X ⟶ S) [LocallyOfFiniteType f] (F : X.Modules)
    [F.IsQuasicoherent] [F.IsFiniteType] :
    IsFlatOver f.toLRSHom.toShHom F ↔
      IsFlatOverInDimensionsGE f F 0 := by
  refine ⟨fun hflat s => ?_, flatOfFlatInDimensionsGE_zero f F⟩
  have hbot : topologicalKrullDim
      ↥{x : f.fiber s |
        ¬ IsFlatOverAt f.toLRSHom.toShHom F (f.fiberι s x)} = ⊥ :=
    (topologicalKrullDim_eq_bot_iff_isEmpty _).2 ⟨fun x => x.2 (hflat (f.fiberι s x))⟩
  rw [hbot]
  exact WithBot.bot_lt_coe (0 : ℕ∞)

private theorem limitPreserving_of_natIso
    {C : Type z} [Category.{t, z} C] {toScheme : C ⥤ Scheme.{u}}
    {P Q : Cᵒᵖ ⥤ Type r} (e : P ≅ Q)
    (hP : LimitPreserving.{u, r, v, w, z, t} toScheme P) :
    LimitPreserving.{u, r, v, w, z, t} toScheme Q := by
  intro I instCat instCof D c hc hAffine hAffineLimit
  obtain ⟨hP⟩ := hP I D c hc hAffine hAffineLimit
  let eD : D.op ⋙ P ≅ D.op ⋙ Q := NatIso.ofComponents
    (fun i => e.app (D.op.obj i)) (by
      intro i j f
      exact e.hom.naturality (D.op.map f))
  let cP := P.mapCocone c.op
  exact ⟨((IsColimit.precomposeInvEquiv eD cP).symm hP).ofIsoColimit
    (by apply Cocone.ext (e.app (Opposite.op c.pt)))⟩

private noncomputable abbrev flatnessSituationOfFlatDimensionSituation
    (D : FlatDimensionSituation.{u}) : FlatnessSituation.{u} :=
  { S := D.S, X := D.X, f := D.f, F := D.F, isQuasicoherent := D.isQuasicoherent }

private noncomputable def flatDimensionFunctor_zero_iso
    (D : FlatDimensionSituation.{u})
    (hn : D.n = 0) :
    D.flatDimensionFunctor ≅
      (flatnessSituationOfFlatDimensionSituation D).flatFunctor := by
  let Dflat := flatnessSituationOfFlatDimensionSituation D
  refine NatIso.ofComponents (fun T => ?_) (by
    intro T T' g
    ext x
    exact Subsingleton.elim _ _)
  let eP : D.IsFlatInDimensionsGEAfterBaseChange T.unop ↔
      Dflat.IsFlatAfterBaseChange T.unop := by
    change IsFlatOverInDimensionsGE
        (D.baseChangeMap T.unop) (D.baseChangeModule T.unop) D.n ↔
      IsFlatOver (D.baseChangeMap T.unop).toLRSHom.toShHom
        (D.baseChangeModule T.unop)
    rw [hn]
    exact (isFlatOver_iff_isFlatOverInDimensionsGE_zero _ _).symm
  let eType : PLift (D.IsFlatInDimensionsGEAfterBaseChange T.unop) ≃
      PLift (Dflat.IsFlatAfterBaseChange T.unop) := {
    toFun := fun x => ⟨eP.mp x.down⟩
    invFun := fun x => ⟨eP.mpr x.down⟩
    left_inv := fun _ => rfl
    right_inv := fun _ => rfl }
  exact eType.toIso

private lemma isCompact_of_isConstructible {A : Type*} [TopologicalSpace A]
    [SpectralSpace A] {s : Set A} (hs : IsConstructible s) : IsCompact s := by
  apply IsClosed.isCompact_of_constructibleTopology
  have ho : @IsOpen A (constructibleTopology A) sᶜ := by
    rw [constructibleTopology_eq_generateFrom_isConstructible]
    exact TopologicalSpace.isOpen_generateFrom_of_mem hs.compl
  simpa only [compl_compl] using @IsOpen.isClosed_compl A (constructibleTopology A) sᶜ ho

private lemma isCompact_compl_range_of_finitePresentation
    {Z X : Scheme.{u}} [CompactSpace X] [QuasiSeparatedSpace X]
    (i : Z ⟶ X) [LocallyOfFinitePresentation i] [QuasiCompact i] :
    IsCompact (Set.range i)ᶜ := by
  let : SpectralSpace X := ⟨⟩
  apply isCompact_of_isConstructible
  apply IsConstructible.compl
  simpa only [Set.image_univ] using i.isConstructible_image IsConstructible.univ

private lemma finitePresentation_open_immersion_of_isCompact
    {X : Scheme.{u}} [QuasiSeparatedSpace X] (U : X.Opens)
    (hU : IsCompact (U : Set X)) : FinitePresentation U.ι :=
  (finitePresentation_iff_quasiCompact_of_isOpenImmersion U.ι).2 <|
    quasiCompact_iff_isSpectralMap.mpr <|
      IsRetrocompact_iff_isSpectralMap_subtypeVal.mp (hU.isRetrocompact U.isOpen)

private noncomputable def pullbackProjection {B X : Scheme.{u}} (f : X ⟶ B) :
    (Over.pullback f ⋙ Over.forget X) ⟶ Over.forget B where
  app A := pullback.fst A.hom f
  naturality {A A'} α := by
    simp only [Functor.comp_map, Over.forget_map, Over.pullback_map_left, pullback.lift_fst]

private theorem pullbackProjection_isPullback {B X : Scheme.{u}} (f : X ⟶ B)
    {A A' : Over B} (α : A ⟶ A') :
    IsPullback ((Over.pullback f).map α).left (pullback.fst A.hom f)
      (pullback.fst A'.hom f) α.left := by
  apply IsPullback.of_right (h₁₂ := pullback.snd A'.hom f) (h₂₂ := A'.hom)
  · simpa only [Over.pullback_map_left, pullback.lift_snd, Over.w] using
      (IsPullback.of_hasPullback A.hom f).flip
  · simp only [Over.pullback_map_left, pullback.lift_fst]
  · exact (IsPullback.of_hasPullback A'.hom f).flip

private theorem range_over_pullback_map
    {S T : Scheme.{u}} (g : T ⟶ S) {X Y : Over S} (f : X ⟶ Y) :
    Set.range ((Over.pullback g).map f).left =
      (pullback.fst Y.hom g) ⁻¹' Set.range f.left := by
  have sq := (pullbackProjection_isPullback g f).flip
  rw [← sq.isoPullback_hom_snd]
  show Set.range (pullback.snd f.left (pullback.fst Y.hom g) ∘
    sq.isoPullback.hom) = _
  rw [Set.range_comp, sq.isoPullback.hom.surjective.range_eq, Set.image_univ]
  exact Scheme.Pullback.range_snd _ _

/-- A slice of a category that is essentially small relative to `u` is again essentially
small relative to `u`: transport along `Over.postEquiv` into the small model. -/
private theorem essentiallySmall_over {I : Type v} [Category.{w} I]
    [EssentiallySmall.{u} I] (j : I) : EssentiallySmall.{u} (Over j) := by
  rw [essentiallySmall_congr (Over.postEquiv (X := j) (equivSmallModel.{u} I))]
  infer_instance

private theorem exists_fiber_dimension_le_baseChange
    {I : Type v} [Category.{w} I] [IsCofiltered I] [EssentiallySmall.{u} I]
    {B X : Scheme.{u}} (E : I ⥤ Over B) (c : Cone E)
    (hc : IsLimit ((Over.forget B).mapCone c))
    [∀ {i j : I} (g : i ⟶ j), IsAffineHom (E.map g).left]
    [∀ i, CompactSpace (E.obj i).left]
    [∀ i, QuasiSeparatedSpace (E.obj i).left]
    (f : X ⟶ B) [LocallyOfFiniteType f] [QuasiCompact f]
    (d : ℕ)
    (hdim : ∀ s : c.pt.left,
      topologicalKrullDim ((pullback.fst c.pt.hom f).fiber s) ≤ (d : WithBot ℕ∞)) :
    ∃ i, ∀ s : (E.obj i).left,
      topologicalKrullDim ((pullback.fst (E.obj i).hom f).fiber s) ≤
        (d : WithBot ℕ∞) := by
  let : IsConnected I := IsCofiltered.isConnected I
  let S := E ⋙ Over.forget B
  let Y := E ⋙ Over.pullback f ⋙ Over.forget X
  let p : Y ⟶ S := Functor.whiskerLeft E (pullbackProjection f)
  let cS : Cone S := (Over.forget B).mapCone c
  let cY : Cone Y := (Over.pullback f ⋙ Over.forget X).mapCone c
  have hcE : IsLimit c := isLimitOfReflects (Over.forget B) hc
  let hcY : IsLimit cY := isLimitOfPreserves (Over.pullback f ⋙ Over.forget X) hcE
  have hclosed {i j : I} (g : i ⟶ j) :
      IsClosedImmersion (pullback.lift (Y.map g) (p.app i) (p.naturality g)) := by
    have h := pullbackProjection_isPullback f (E.map g)
    show IsClosedImmersion h.isoPullback.hom
    infer_instance
  have hp : hc.lift ((Cone.postcompose p).obj cY) = pullback.fst c.pt.hom f := by
    apply hc.hom_ext
    intro i
    rw [hc.fac]
    dsimp [p, cY, pullbackProjection]
    simp only [Over.pullback_map_left, pullback.lift_fst]
  let : ∀ {i j : I} (g : i ⟶ j), IsAffineHom (S.map g) :=
    fun {_ _} g => inferInstanceAs (IsAffineHom (E.map g).left)
  let : ∀ i, CompactSpace (S.obj i) :=
    inferInstanceAs (∀ i, CompactSpace (E.obj i).left)
  let : ∀ i, QuasiSeparatedSpace (S.obj i) :=
    inferInstanceAs (∀ i, QuasiSeparatedSpace (E.obj i).left)
  let : ∀ i, LocallyOfFiniteType (p.app i) :=
    fun i => inferInstanceAs (LocallyOfFiniteType (pullback.fst (E.obj i).hom f))
  let : ∀ i, QuasiCompact (p.app i) :=
    fun i => inferInstanceAs (QuasiCompact (pullback.fst (E.obj i).hom f))
  apply exists_forall_topologicalKrullDim_fiber_le_of_isLimit_of_essentiallySmall
    Y S p cY hcY cS hc d
  show ∀ s : c.pt.left, topologicalKrullDim
    ((hc.lift ((Cone.postcompose p).obj cY)).fiber s) ≤ (d : WithBot ℕ∞)
  rw [hp]
  exact hdim

/-- The iterated base change of a scheme over the stage `S j`, first to the stage `S i` and then
to the vertex of a cone over `S`, identified with its direct base change to the vertex.  This is
`AlgebraicGeometry.overPullbackCompIso` at the cone's own compatibility equation, read from the
vertex inwards. -/
private noncomputable def overPullbackConeIso
    {I : Type v} [Category.{w} I] (S : I ⥤ Scheme.{u}) (c : Cone S)
    {i j : I} (g : i ⟶ j) (Y : Over (S.obj j)) :
    (Over.pullback (c.π.app j)).obj Y ≅
      (Over.pullback (c.π.app i)).obj ((Over.pullback (S.map g)).obj Y) :=
  (overPullbackCompIso (S.map g) (c.π.app i) (c.π.app j) (c.w g) Y).symm

private theorem overPullbackConeIso_naturality
    {I : Type v} [Category.{w} I] (S : I ⥤ Scheme.{u}) (c : Cone S)
    {i j : I} (g : i ⟶ j) {Y Z : Over (S.obj j)} (f : Y ⟶ Z) :
    (overPullbackConeIso S c g Y).hom ≫
        (Over.pullback (c.π.app i)).map ((Over.pullback (S.map g)).map f) =
      (Over.pullback (c.π.app j)).map f ≫
        (overPullbackConeIso S c g Z).hom := by
  have h := overPullbackCompIso_naturality (S.map g) (c.π.app i) (c.π.app j) (c.w g) f
  show (overPullbackCompIso (S.map g) (c.π.app i) (c.π.app j) (c.w g) Y).inv ≫ _ =
    _ ≫ (overPullbackCompIso (S.map g) (c.π.app i) (c.π.app j) (c.w g) Z).inv
  rw [Iso.inv_comp_eq, ← Category.assoc, h, Category.assoc, Iso.hom_inv_id, Category.comp_id]

private theorem overPullbackConeIso_fst
    {I : Type v} [Category.{w} I] (S : I ⥤ Scheme.{u}) (c : Cone S)
    {i j : I} (g : i ⟶ j) (Y : Over (S.obj j)) :
    (overPullbackConeIso S c g Y).hom.left ≫
        pullback.fst ((Over.pullback (S.map g)).obj Y).hom (c.π.app i) ≫
          pullback.fst Y.hom (S.map g) =
      pullback.fst Y.hom (c.π.app j) := by
  have h := overPullbackCompIso_fst (S.map g) (c.π.app i) (c.π.app j) (c.w g) Y
  have hid : (overPullbackConeIso S c g Y).hom.left ≫
      (overPullbackCompIso (S.map g) (c.π.app i) (c.π.app j) (c.w g) Y).hom.left = 𝟙 _ := by
    show ((overPullbackCompIso (S.map g) (c.π.app i) (c.π.app j) (c.w g) Y).inv ≫
      (overPullbackCompIso (S.map g) (c.π.app i) (c.π.app j) (c.w g) Y).hom).left = 𝟙 _
    rw [Iso.inv_hom_id]
    rfl
  rw [← h, ← Category.assoc, hid, Category.id_comp]

private theorem fiber_dimension_eq_of_over_iso
    {S : Scheme.{u}} {X Y : Over S} (e : X ≅ Y) (s : S) :
    topologicalKrullDim (X.hom.fiber s) = topologicalKrullDim (Y.hom.fiber s) := by
  let h : X.left ≃ₜ Y.left := TopCat.homeoOfIso (asIso e.hom.left.base)
  have heq (x : X.left) : X.hom x = Y.hom (h x) := by
    show X.hom x = Y.hom (e.hom.left x)
    rw [← e.hom.w]
    rfl
  let h' : X.hom ⁻¹' {s} ≃ₜ Y.hom ⁻¹' {s} := h.subtype (fun x => by
    simp only [Set.mem_preimage, Set.mem_singleton_iff]
    rw [← heq x])
  calc
    topologicalKrullDim (X.hom.fiber s) = topologicalKrullDim (X.hom ⁻¹' {s}) :=
      (X.hom.fiberHomeo s).isHomeomorph.topologicalKrullDim_eq
    _ = topologicalKrullDim (Y.hom ⁻¹' {s}) := h'.isHomeomorph.topologicalKrullDim_eq
    _ = topologicalKrullDim (Y.hom.fiber s) :=
      (Y.hom.fiberHomeo s).isHomeomorph.topologicalKrullDim_eq.symm

private noncomputable def pullback_symmetry_over
    {A B X : Scheme.{u}} (f : X ⟶ B) (g : A ⟶ B) :
    Over.mk (pullback.snd f g) ≅ Over.mk (pullback.fst g f) :=
  Over.isoMk (pullbackSymmetry f g) (by simp)

private theorem finitePresentation_of_over_morphism
    {B : Scheme.{u}} {X Y : Over B} (f : X ⟶ Y)
    (hX : FinitePresentation X.hom)
    (hY : FinitePresentation Y.hom) :
    FinitePresentation f.left := by
  let : LocallyOfFinitePresentation (f.left ≫ Y.hom) := by
    rw [f.w]
    exact hX.1
  let : QuasiCompact (f.left ≫ Y.hom) := by
    rw [f.w]
    exact hX.2.1
  let : QuasiSeparated (f.left ≫ Y.hom) := by
    rw [f.w]
    exact hX.2.2
  let : LocallyOfFiniteType Y.hom := by
    let : LocallyOfFinitePresentation Y.hom := hY.1
    infer_instance
  let : QuasiSeparated Y.hom := hY.2.2
  refine FinitePresentation.mk ?_ ?_ ?_
  · exact locallyOfFinitePresentation_of_comp f.left Y.hom
  · exact QuasiCompact.of_comp f.left Y.hom
  · exact QuasiSeparated.of_comp f.left Y.hom

private theorem flatInDimensions_of_overIso
    {S : Scheme.{u}} {X Y : Over S} (e : X ≅ Y)
    [LocallyOfFiniteType X.hom] [LocallyOfFiniteType Y.hom] (F : Y.left.Modules)
    [F.IsQuasicoherent] [F.IsFiniteType] (n : ℕ)
    (h : IsFlatOverInDimensionsGE X.hom
      ((Scheme.Modules.pullback e.hom.left).obj F) n) :
    IsFlatOverInDimensionsGE Y.hom F n := by
  refine (flatInDimensions_comp_etale_iff Y.hom F e.hom.left e.hom.left.surjective n).mp ?_
  simpa only [e.hom.w] using h

private noncomputable def modulePullbackCompIsoOfEq
    {X Y Z : Scheme.{u}} (a : X ⟶ Y) (b : Y ⟶ Z) (c : X ⟶ Z)
    (h : a ≫ b = c) (F : Z.Modules) :
    (Scheme.Modules.pullback a).obj ((Scheme.Modules.pullback b).obj F) ≅
      (Scheme.Modules.pullback c).obj F := by
  subst c
  exact (Scheme.Modules.pullbackComp a b).app F

/-- Flatness in dimensions `≥ n` transfers from a pullback square `sq` to the canonical pullback:
if the pullback of `F` along `q` is flat over `T` in dimensions `≥ n` via `p`, then so is the
pullback of `F` to `pullback f g` via `pullback.snd f g`. -/
public theorem flatInDimensions_canonical_of_isPullback
    {X Y S T : Scheme.{u}} {q : Y ⟶ X} {p : Y ⟶ T}
    {f : X ⟶ S} {g : T ⟶ S} (sq : IsPullback q p f g)
    [LocallyOfFiniteType f] [LocallyOfFiniteType p]
    (F : X.Modules) [F.IsQuasicoherent] [F.IsFiniteType]
    (n : ℕ) (h : IsFlatOverInDimensionsGE p
      ((Scheme.Modules.pullback q).obj F) n) :
    IsFlatOverInDimensionsGE (pullback.snd f g)
      ((Scheme.Modules.pullback (pullback.fst f g)).obj F) n := by
  let e : Over.mk p ≅ Over.mk (pullback.snd f g) :=
    Over.isoMk sq.isoPullback sq.isoPullback_hom_snd
  exact flatInDimensions_of_overIso e _ n (IsFlatOverInDimensionsGE.of_moduleIso p
    (modulePullbackCompIsoOfEq sq.isoPullback.hom (pullback.fst f g) q
      sq.isoPullback_hom_fst F).symm h)

/-- Flatness in dimensions `≥ n` transfers from the canonical pullback to any pullback square `sq`:
the converse of `flatInDimensions_canonical_of_isPullback`. -/
public theorem flatInDimensions_of_isPullback_canonical
    {X Y S T : Scheme.{u}} {q : Y ⟶ X} {p : Y ⟶ T}
    {f : X ⟶ S} {g : T ⟶ S} (sq : IsPullback q p f g)
    [LocallyOfFiniteType f] [LocallyOfFiniteType p]
    (F : X.Modules) [F.IsQuasicoherent] [F.IsFiniteType]
    (n : ℕ) (h : IsFlatOverInDimensionsGE (pullback.snd f g)
      ((Scheme.Modules.pullback (pullback.fst f g)).obj F) n) :
    IsFlatOverInDimensionsGE p ((Scheme.Modules.pullback q).obj F) n := by
  let e : Over.mk p ≅ Over.mk (pullback.snd f g) :=
    Over.isoMk sq.isoPullback sq.isoPullback_hom_snd
  exact flatInDimensions_of_overIso e.symm _ n (IsFlatOverInDimensionsGE.of_moduleIso _
    (modulePullbackCompIsoOfEq sq.isoPullback.inv q (pullback.fst f g)
      sq.isoPullback_inv_fst F).symm h)

private theorem eventually_flatInDimensionsGE_of_finitePresentation
    {I : Type v} [Category.{w} I] [IsCofiltered I] [EssentiallySmall.{u} I]
    (S : I ⥤ Scheme.{u}) (c : Cone S) (hc : IsLimit c)
    [∀ {i j : I} (g : i ⟶ j), IsAffineHom (S.map g)]
    [∀ i : I, CompactSpace (S.obj i)]
    [∀ i : I, QuasiSeparatedSpace (S.obj i)]
    [CompactSpace c.pt] [QuasiSeparatedSpace c.pt]
    (i₀ : I) (X₀ : Over (S.obj i₀)) [LocallyOfFiniteType X₀.hom]
    (hX₀ : FinitePresentation X₀.hom)
    (F₀ : X₀.left.Modules) [F₀.IsQuasicoherent]
    [F₀.IsFiniteType] [F₀.IsFinitePresentation]
    (n : ℕ) (hn : 0 < n)
    (hflatDim :
      IsFlatOverInDimensionsGE
        ((Over.pullback (c.π.app i₀)).obj X₀).hom
        ((Scheme.Modules.pullback
          (pullback.fst X₀.hom (c.π.app i₀))).obj F₀) n) :
    ∃ (i : I) (g : i ⟶ i₀),
      IsFlatOverInDimensionsGE
        ((Over.pullback (S.map g)).obj X₀).hom
        ((Scheme.Modules.pullback
          (pullback.fst X₀.hom (S.map g))).obj F₀) n := by
  have ⟨_, _, _⟩ := hX₀
  let Xlim : Over c.pt := (Over.pullback (c.π.app i₀)).obj X₀
  have hXlim : FinitePresentation Xlim.hom :=
    finitePresentation_pullback (c.π.app i₀) X₀ hX₀
  let Mlim : Xlim.left.Modules :=
    (Scheme.Modules.pullback (pullback.fst X₀.hom (c.π.app i₀))).obj F₀
  let : Mlim.IsFinitePresentation :=
    @Stacks.SheafOfModules.modulePullback_isFinitePresentation _ _
      (pullback.fst X₀.hom (c.π.app i₀)).toLRSHom.toShHom F₀
      (show F₀.IsFinitePresentation from by assumption)
  have ⟨_, _, _⟩ := hXlim
  obtain ⟨Z, j, hj, hfpj, hdimj, hflatj⟩ :=
    exists_finitePresentation_bad_locus_enlargement Xlim.hom Mlim n hXlim hflatDim
  let : IsClosedImmersion j := hj
  have ⟨_, _, _⟩ := hfpj
  let Zover : Over c.pt := Over.mk (j ≫ Xlim.hom)
  have hZover : FinitePresentation Zover.hom :=
    finitePresentation_of_instances (j ≫ Xlim.hom)
  obtain ⟨k, Zk, hZk, ⟨α⟩⟩ :=
    LimitFPObjectDescent.exists_model_of_finitePresentation S c hc Zover hZover
  obtain ⟨l, glk, gli₀, _⟩ := IsCofilteredOrEmpty.cone_objs k i₀
  let Zl : Over (S.obj l) := (Over.pullback (S.map glk)).obj Zk
  let Xl : Over (S.obj l) := (Over.pullback (S.map gli₀)).obj X₀
  let βZ := overPullbackConeIso S c glk Zk
  let βX := overPullbackConeIso S c gli₀ X₀
  let jOver : Zover ⟶ Xlim := Over.homMk j (by rfl)
  let jlim : (Over.pullback (c.π.app l)).obj Zl ⟶
      (Over.pullback (c.π.app l)).obj Xl :=
    βZ.inv ≫ α.inv ≫ jOver ≫ βX.hom
  have hZl : FinitePresentation Zl.hom :=
    finitePresentation_pullback (S.map glk) Zk hZk
  have hXl : FinitePresentation Xl.hom :=
    finitePresentation_pullback (S.map gli₀) X₀ hX₀
  have hjlim : IsClosedImmersion jlim.left := by
    show IsClosedImmersion (βZ.inv.left ≫ α.inv.left ≫ j ≫ βX.hom.left)
    infer_instance
  obtain ⟨m, gml, jm, γZ, γX, hγZ, hγX, hγj⟩ :=
    exists_morphism_after_baseChange S c hc l Zl Xl hZl hXl jlim
  have hjpb : IsClosedImmersion ((Over.pullback (c.π.app m)).map jm).left := by
    have h : IsClosedImmersion (γZ.hom.left ≫ jlim.left) := by infer_instance
    have heq : γZ.hom.left ≫ jlim.left =
        ((Over.pullback (c.π.app m)).map jm).left ≫ γX.hom.left :=
      congrArg Over.Hom.left hγj
    rw [heq] at h
    let : IsClosedImmersion
        (((Over.pullback (c.π.app m)).map jm).left ≫ γX.hom.left) := h
    exact IsClosedImmersion.of_comp_isClosedImmersion
      ((Over.pullback (c.π.app m)).map jm).left γX.hom.left
  let Zm : Over (S.obj m) := (Over.pullback (S.map gml)).obj Zl
  let Xm : Over (S.obj m) := (Over.pullback (S.map gml)).obj Xl
  have hZm : FinitePresentation Zm.hom :=
    finitePresentation_pullback (S.map gml) Zl hZl
  have hXm : FinitePresentation Xm.hom :=
    finitePresentation_pullback (S.map gml) Xl hXl
  have ⟨_, _, _⟩ := hZm
  have ⟨_, _, _⟩ := hXm
  let : CompactSpace Zm.left := QuasiCompact.compactSpace_of_compactSpace Zm.hom
  let : QuasiSeparatedSpace Zm.left :=
    quasiSeparatedSpace_of_quasiSeparated Zm.hom
  let : CompactSpace Xm.left := QuasiCompact.compactSpace_of_compactSpace Xm.hom
  let : QuasiSeparatedSpace Xm.left :=
    quasiSeparatedSpace_of_quasiSeparated Xm.hom
  have hjmFiniteType : LocallyOfFiniteType jm.left := by
    have : LocallyOfFiniteType (jm.left ≫ Xm.hom) := by
      rw [jm.w]
      infer_instance
    exact locallyOfFiniteType_of_comp jm.left Xm.hom
  let : LocallyOfFiniteType jm.left := hjmFiniteType
  obtain ⟨r, grm, hjr⟩ :=
    exists_isClosedImmersion_baseChange_of_isLimit S c hc m Zm Xm jm
  let eZm : Zover ≅ (Over.pullback (c.π.app m)).obj Zm :=
    α ≪≫ βZ ≪≫ γZ.symm
  let eXm : Xlim ≅ (Over.pullback (c.π.app m)).obj Xm :=
    βX ≪≫ γX.symm
  have hcomm_m : eZm.hom ≫ (Over.pullback (c.π.app m)).map jm =
      jOver ≫ eXm.hom := by
    have hγ' : γZ.hom ≫ jlim ≫ γX.inv =
        (Over.pullback (c.π.app m)).map jm := by
      rw [← Category.assoc, hγj]
      simp
    have hγ'' : γZ.inv ≫ (Over.pullback (c.π.app m)).map jm =
        jlim ≫ γX.inv := by
      rw [← hγ']
      simp [Category.assoc]
    dsimp [eZm, eXm]
    simp only [Iso.trans_hom, Iso.symm_hom, Category.assoc]
    rw [hγ'']
    simp [jlim, Category.assoc]
  let Zr : Over (S.obj r) := (Over.pullback (S.map grm)).obj Zm
  let Xr : Over (S.obj r) := (Over.pullback (S.map grm)).obj Xm
  let jr : Zr ⟶ Xr := (Over.pullback (S.map grm)).map jm
  let : IsClosedImmersion jr.left := hjr
  let eZr : Zover ≅ (Over.pullback (c.π.app r)).obj Zr :=
    eZm ≪≫ overPullbackConeIso S c grm Zm
  let eXr : Xlim ≅ (Over.pullback (c.π.app r)).obj Xr :=
    eXm ≪≫ overPullbackConeIso S c grm Xm
  have hcomm_r : eZr.hom ≫ (Over.pullback (c.π.app r)).map jr =
      jOver ≫ eXr.hom := by
    dsimp [eZr, eXr, jr]
    rw [Category.assoc, overPullbackConeIso_naturality S c grm jm]
    simp only [← Category.assoc]
    rw [hcomm_m]
  have hdimZr : ∀ s : c.pt,
      topologicalKrullDim (((Over.pullback (c.π.app r)).obj Zr).hom.fiber s) ≤
        ((n - 1 : ℕ) : WithBot ℕ∞) := by
    intro s
    exact (fiber_dimension_eq_of_over_iso eZr s).symm ▸ hdimj s
  have hdimZr' : ∀ s : c.pt,
      topologicalKrullDim ((pullback.fst (c.π.app r) Zr.hom).fiber s) ≤
        ((n - 1 : ℕ) : WithBot ℕ∞) := by
    intro s
    exact (fiber_dimension_eq_of_over_iso
      (pullback_symmetry_over Zr.hom (c.π.app r)) s) ▸ hdimZr s
  let Er : Over r ⥤ Over (S.obj r) := Over.post (X := r) S
  let cr : Cone Er := (Over.conePost S r).obj c
  have hcr : IsLimit ((Over.forget (S.obj r)).mapCone cr) :=
    isLimitOfPreserves (Over.forget (S.obj r)) (Over.isLimitConePost r hc)
  let : ∀ {a b : Over r} (g : a ⟶ b), IsAffineHom (Er.map g).left := by
    intro a b g
    show IsAffineHom (S.map g.left)
    infer_instance
  let : ∀ a : Over r, CompactSpace (Er.obj a).left := fun a => by
    show CompactSpace (S.obj a.left)
    infer_instance
  let : ∀ a : Over r, QuasiSeparatedSpace (Er.obj a).left := fun a => by
    show QuasiSeparatedSpace (S.obj a.left)
    infer_instance
  let : LocallyOfFinitePresentation Zr.hom := by
    show LocallyOfFinitePresentation (pullback.snd Zm.hom (S.map grm))
    infer_instance
  let : QuasiCompact Zr.hom := by
    show QuasiCompact (pullback.snd Zm.hom (S.map grm))
    infer_instance
  let : LocallyOfFiniteType Zr.hom := by
    infer_instance
  have : EssentiallySmall.{u} (Over r) := essentiallySmall_over r
  obtain ⟨t, hdimt⟩ := exists_fiber_dimension_le_baseChange Er cr hcr Zr.hom
    (n - 1) hdimZr'
  let Zt : Over (S.obj t.left) := (Over.pullback (S.map t.hom)).obj Zr
  let Xt : Over (S.obj t.left) := (Over.pullback (S.map t.hom)).obj Xr
  let jt : Zt ⟶ Xt := (Over.pullback (S.map t.hom)).map jr
  let : IsClosedImmersion jt.left := by
    dsimp [jt]
    exact MorphismProperty.overPullbackMap (P := @IsClosedImmersion)
      (S.map t.hom) jr hjr
  let eZt : Zover ≅ (Over.pullback (c.π.app t.left)).obj Zt :=
    eZr ≪≫ overPullbackConeIso S c t.hom Zr
  let eXt : Xlim ≅ (Over.pullback (c.π.app t.left)).obj Xt :=
    eXr ≪≫ overPullbackConeIso S c t.hom Xr
  have hcomm_t : eZt.hom ≫ (Over.pullback (c.π.app t.left)).map jt =
      jOver ≫ eXt.hom := by
    dsimp [eZt, eXt, jt]
    rw [Category.assoc, overPullbackConeIso_naturality S c t.hom jr]
    simp only [← Category.assoc]
    rw [hcomm_r]
  let ql : Xl.left ⟶ X₀.left := pullback.fst X₀.hom (S.map gli₀)
  let qm : Xm.left ⟶ X₀.left := pullback.fst Xl.hom (S.map gml) ≫ ql
  let qr : Xr.left ⟶ X₀.left := pullback.fst Xm.hom (S.map grm) ≫ qm
  let qt : Xt.left ⟶ X₀.left := pullback.fst Xr.hom (S.map t.hom) ≫ qr
  have hβfst : βX.hom.left ≫ pullback.fst Xl.hom (c.π.app l) ≫ ql =
      pullback.fst X₀.hom (c.π.app i₀) :=
    overPullbackConeIso_fst S c gli₀ X₀
  have hγInvfst : γX.inv.left ≫ pullback.fst Xm.hom (c.π.app m) ≫ qm =
      pullback.fst Xl.hom (c.π.app l) ≫ ql := by
    have hγX' : γX.hom.left ≫ pullback.fst Xl.hom (c.π.app l) ≫ ql =
        pullback.fst Xm.hom (c.π.app m) ≫ qm := by
      simpa [Xm, qm, Category.assoc] using
        congrArg (fun k : ((Over.pullback (c.π.app m)).obj Xm).left ⟶
          Xl.left => k ≫ ql) hγX
    have h := congrArg (fun k : ((Over.pullback (c.π.app m)).obj Xm).left ⟶
      X₀.left => γX.inv.left ≫ k) hγX'
    simpa [Category.assoc] using h.symm
  have heXmProj : eXm.hom.left ≫ pullback.fst Xm.hom (c.π.app m) ≫ qm =
      pullback.fst X₀.hom (c.π.app i₀) := by
    calc
      _ = βX.hom.left ≫
          (γX.inv.left ≫ pullback.fst Xm.hom (c.π.app m) ≫ qm) := by
        simp [eXm, Category.assoc]
      _ = βX.hom.left ≫ (pullback.fst Xl.hom (c.π.app l) ≫ ql) := by
        rw [hγInvfst]
      _ = pullback.fst X₀.hom (c.π.app i₀) := by
        simpa [Category.assoc] using hβfst
  have heXrProj : eXr.hom.left ≫ pullback.fst Xr.hom (c.π.app r) ≫ qr =
      pullback.fst X₀.hom (c.π.app i₀) := by
    calc
      _ = eXm.hom.left ≫
          ((overPullbackConeIso S c grm Xm).hom.left ≫
            pullback.fst Xr.hom (c.π.app r) ≫ qr) := by
        simp [eXr, Category.assoc]
      _ = eXm.hom.left ≫ (pullback.fst Xm.hom (c.π.app m) ≫ qm) := by
        have h := congrArg
          (fun k : ((Over.pullback (c.π.app m)).obj Xm).left ⟶ Xm.left =>
            eXm.hom.left ≫ k ≫ qm)
          (overPullbackConeIso_fst S c grm Xm)
        simpa [Xr, qr, Category.assoc] using h
      _ = pullback.fst X₀.hom (c.π.app i₀) := by
        simpa [Category.assoc] using heXmProj
  have heXtProj : eXt.hom.left ≫ pullback.fst Xt.hom (c.π.app t.left) ≫ qt =
      pullback.fst X₀.hom (c.π.app i₀) := by
    calc
      _ = eXr.hom.left ≫
          ((overPullbackConeIso S c t.hom Xr).hom.left ≫
            pullback.fst Xt.hom (c.π.app t.left) ≫ qt) := by
        simp [eXt, Category.assoc]
      _ = eXr.hom.left ≫ (pullback.fst Xr.hom (c.π.app r) ≫ qr) := by
        have h := congrArg
          (fun k : ((Over.pullback (c.π.app r)).obj Xr).left ⟶ Xr.left =>
            eXr.hom.left ≫ k ≫ qr)
          (overPullbackConeIso_fst S c t.hom Xr)
        simpa [Xt, qt, Category.assoc] using h
      _ = pullback.fst X₀.hom (c.π.app i₀) := by
        simpa [Category.assoc] using heXrProj
  have heXtInvProj : pullback.fst Xt.hom (c.π.app t.left) ≫ qt =
      eXt.inv.left ≫ pullback.fst X₀.hom (c.π.app i₀) := by
    have h := congrArg (fun k : Xlim.left ⟶ X₀.left => eXt.inv.left ≫ k)
      heXtProj
    simpa [Category.assoc] using h
  have hdimZt (s : S.obj t.left) :
      topologicalKrullDim (Zt.hom.fiber s) ≤
        ((n - 1 : ℕ) : WithBot ℕ∞) :=
    (fiber_dimension_eq_of_over_iso
      (pullback_symmetry_over Zr.hom (S.map t.hom)) s).symm ▸ hdimt s
  have hZr : FinitePresentation Zr.hom :=
    finitePresentation_pullback (S.map grm) Zm hZm
  have hXr : FinitePresentation Xr.hom :=
    finitePresentation_pullback (S.map grm) Xm hXm
  have hZt : FinitePresentation Zt.hom :=
    finitePresentation_pullback (S.map t.hom) Zr hZr
  have hXt : FinitePresentation Xt.hom :=
    finitePresentation_pullback (S.map t.hom) Xr hXr
  have hfpjt : FinitePresentation jt.left :=
    finitePresentation_of_over_morphism jt hZt hXt
  have ⟨_, _, _⟩ := hXt
  let : CompactSpace Xt.left := QuasiCompact.compactSpace_of_compactSpace Xt.hom
  let : QuasiSeparatedSpace Xt.left := quasiSeparatedSpace_of_quasiSeparated Xt.hom
  let Ut : Xt.left.Opens :=
    ⟨(Set.range jt.left)ᶜ, jt.left.isClosedEmbedding.isClosed_range.isOpen_compl⟩
  have hUtCompact : IsCompact (Ut : Set Xt.left) := by
    show IsCompact (Set.range jt.left)ᶜ
    have ⟨_, _, _⟩ := hfpjt
    exact isCompact_compl_range_of_finitePresentation jt.left
  have hfpUt : FinitePresentation (Ut.ι ≫ Xt.hom) := by
    have ⟨_, _, _⟩ := finitePresentation_open_immersion_of_isCompact Ut hUtCompact
    exact finitePresentation_of_instances _
  have hnotRangeLimit (x : ((Over.pullback (c.π.app t.left)).obj Xt).left)
      (hx : x ∉ Set.range ((Over.pullback (c.π.app t.left)).map jt).left) :
      eXt.inv.left x ∉ Set.range j := by
    intro ⟨z, hz⟩
    have hcomp := congrArg Over.Hom.left hcomm_t
    have heval := congrArg
      (fun k : Z ⟶ ((Over.pullback (c.π.app t.left)).obj Xt).left => k z) hcomp
    change ((Over.pullback (c.π.app t.left)).map jt).left (eZt.hom.left z) =
      eXt.hom.left (j z) at heval
    rw [hz] at heval
    have hinv : eXt.hom.left (eXt.inv.left x) = x := by
      have hid := congrArg Over.Hom.left eXt.inv_hom_id
      have hpt := congrArg
        (fun k : ((Over.pullback (c.π.app t.left)).obj Xt).left ⟶
          ((Over.pullback (c.π.app t.left)).obj Xt).left => k x) hid
      change eXt.hom.left (eXt.inv.left x) = x at hpt
      exact hpt
    exact hx ⟨eZt.hom.left z, heval.trans hinv⟩
  have hflatLimitPoint (x : ((Over.pullback (c.π.app t.left)).obj Xt).left)
      (hx : x ∉ Set.range ((Over.pullback (c.π.app t.left)).map jt).left) :
      IsFlatOverAt
        ((Over.pullback (c.π.app t.left)).obj Xt).hom.toLRSHom.toShHom
        ((Scheme.Modules.pullback eXt.inv.left).obj Mlim) x := by
    let : Flat eXt.inv.left := by infer_instance
    have h := (isFlatOverAt_iff_modulePullback_isFlatOverAt
      eXt.inv.left Xlim.hom Mlim x (Flat.stalkMap eXt.inv.left x)).mp
      (hflatj _ (hnotRangeLimit x hx))
    rwa [eXt.inv.w] at h
  let Uover : Over (S.obj t.left) := Over.mk (Ut.ι ≫ Xt.hom)
  let iu : Uover ⟶ Xt := Over.homMk Ut.ι (by rfl)
  let Ulim : Over c.pt := (Over.pullback (c.π.app t.left)).obj Uover
  let iuLim : Ulim ⟶ (Over.pullback (c.π.app t.left)).obj Xt :=
    (Over.pullback (c.π.app t.left)).map iu
  have hiuProj : iuLim.left ≫ pullback.fst Xt.hom (c.π.app t.left) =
      pullback.fst Uover.hom (c.π.app t.left) ≫ Ut.ι := by
    simp [iuLim, iu, Over.pullback_map_left, pullback.lift_fst]
  have hpaths : pullback.fst Uover.hom (c.π.app t.left) ≫ Ut.ι ≫ qt =
      iuLim.left ≫ eXt.inv.left ≫ pullback.fst X₀.hom (c.π.app i₀) := by
    calc
      _ = iuLim.left ≫ (pullback.fst Xt.hom (c.π.app t.left) ≫ qt) := by
        simpa [Category.assoc] using
          congrArg (fun k : Ulim.left ⟶ Xt.left => k ≫ qt) hiuProj.symm
      _ = iuLim.left ≫ (eXt.inv.left ≫ pullback.fst X₀.hom (c.π.app i₀)) := by
        rw [heXtInvProj]
  have hnotJ (x : Ulim.left) :
      iuLim.left x ∉ Set.range ((Over.pullback (c.π.app t.left)).map jt).left := by
    intro hx
    have hx' : (pullback.fst Xt.hom (c.π.app t.left)) (iuLim.left x) ∈
        Set.range jt.left := by
      rwa [range_over_pullback_map (c.π.app t.left) jt] at hx
    have hq : (pullback.fst Xt.hom (c.π.app t.left)) (iuLim.left x) =
        Ut.ι (pullback.fst Uover.hom (c.π.app t.left) x) := by
      simp only [iuLim, iu, Over.pullback_map_left, ← Scheme.Hom.comp_apply,
        pullback.lift_fst]
      rfl
    rw [hq] at hx'
    exact (pullback.fst Uover.hom (c.π.app t.left) x).property hx'
  have hflatUlimIter : IsFlatOver Ulim.hom.toLRSHom.toShHom
      ((Scheme.Modules.pullback iuLim.left).obj
        ((Scheme.Modules.pullback eXt.inv.left).obj Mlim)) := by
    let : IsOpenImmersion iuLim.left := by
      dsimp [iuLim]
      exact MorphismProperty.overPullbackMap (P := @IsOpenImmersion)
        (c.π.app t.left) iu (inferInstanceAs (IsOpenImmersion Ut.ι))
    let : Flat iuLim.left := by infer_instance
    intro x
    have h := (isFlatOverAt_iff_modulePullback_isFlatOverAt
      iuLim.left ((Over.pullback (c.π.app t.left)).obj Xt).hom
      ((Scheme.Modules.pullback eXt.inv.left).obj Mlim) x
      (Flat.stalkMap iuLim.left x)).mp (hflatLimitPoint _ (hnotJ x))
    rwa [iuLim.w] at h
  let FUt : Uover.left.Modules := (Scheme.Modules.pullback (Ut.ι ≫ qt)).obj F₀
  let hFUtQC : FUt.IsQuasicoherent := modules_pullback_isQuasicoherent (Ut.ι ≫ qt) F₀
  let hFUtFP : FUt.IsFinitePresentation :=
    @Stacks.SheafOfModules.modulePullback_isFinitePresentation _ _
      (Ut.ι ≫ qt).toLRSHom.toShHom F₀
      (show F₀.IsFinitePresentation from by assumption)
  let qU : Ulim.left ⟶ Uover.left := pullback.fst Uover.hom (c.π.app t.left)
  let q₀ : Xlim.left ⟶ X₀.left := pullback.fst X₀.hom (c.π.app i₀)
  have hpaths' : qU ≫ (Ut.ι ≫ qt) =
      iuLim.left ≫ (eXt.inv.left ≫ q₀) := by
    simpa [qU, q₀, Category.assoc] using hpaths
  let eIter : ((Scheme.Modules.pullback iuLim.left).obj
        ((Scheme.Modules.pullback eXt.inv.left).obj Mlim)) ≅
      ((Scheme.Modules.pullback (iuLim.left ≫ (eXt.inv.left ≫ q₀))).obj F₀) :=
    ((Scheme.Modules.pullback iuLim.left).mapIso
      ((Scheme.Modules.pullbackComp eXt.inv.left q₀).app F₀)) ≪≫
    ((Scheme.Modules.pullbackComp iuLim.left (eXt.inv.left ≫ q₀)).app F₀)
  let ePath : ((Scheme.Modules.pullback (iuLim.left ≫ (eXt.inv.left ≫ q₀))).obj F₀) ≅
      ((Scheme.Modules.pullback (qU ≫ (Ut.ι ≫ qt))).obj F₀) := by
    rw [hpaths']
  let eStage := (Scheme.Modules.pullbackComp qU (Ut.ι ≫ qt)).app F₀
  let eModule : ((Scheme.Modules.pullback iuLim.left).obj
        ((Scheme.Modules.pullback eXt.inv.left).obj Mlim)) ≅
      ((Scheme.Modules.pullback qU).obj FUt) :=
    eIter ≪≫ ePath ≪≫ eStage.symm
  have hflatUlim : IsFlatOver Ulim.hom.toLRSHom.toShHom
      ((Scheme.Modules.pullback qU).obj FUt) :=
    isFlatOver_of_moduleIso Ulim.hom.toLRSHom.toShHom eModule hflatUlimIter
  let Yt : Over (S.obj t.left) := Over.mk (𝟙 (S.obj t.left))
  have hYt : FinitePresentation Yt.hom :=
    finitePresentation_of_instances (𝟙 (S.obj t.left))
  let fUt : Uover ⟶ Yt := Over.homMk Uover.hom (by dsimp [Yt]; simp)
  let fLim := ((Over.pullback (c.π.app t.left)).map fUt).left
  let qYlim := ((Over.pullback (c.π.app t.left)).obj Yt).hom
  let : IsIso qYlim := by
    show IsIso (pullback.snd (𝟙 (S.obj t.left)) (c.π.app t.left))
    infer_instance
  let : Etale qYlim := by infer_instance
  have hLimComp : fLim ≫ qYlim = Ulim.hom :=
    ((Over.pullback (c.π.app t.left)).map fUt).w
  have hflatFor05LY : IsFlatOver fLim.toLRSHom.toShHom
      ((Scheme.Modules.pullback qU).obj FUt) := by
    have hflatComp : IsFlatOver (fLim ≫ qYlim).toLRSHom.toShHom
        ((Scheme.Modules.pullback qU).obj FUt) := by
      rw [hLimComp]
      exact hflatUlim
    exact (isFlatOver_comp_iff_of_etale fLim qYlim
      ((Scheme.Modules.pullback qU).obj FUt)).mp hflatComp
  obtain ⟨p, gpt, hflatp⟩ :=
    @eventually_isFlatOver_modulePullback _ _ _ _ S c hc
      (by assumption) (by assumption) (by assumption)
      t.left Uover Yt hfpUt hYt fUt FUt hFUtQC hFUtFP hflatFor05LY
  let Xp : Over (S.obj p) := (Over.pullback (S.map gpt)).obj Xt
  let Zp : Over (S.obj p) := (Over.pullback (S.map gpt)).obj Zt
  let Up : Over (S.obj p) := (Over.pullback (S.map gpt)).obj Uover
  let jp : Zp ⟶ Xp := (Over.pullback (S.map gpt)).map jt
  let iup : Up ⟶ Xp := (Over.pullback (S.map gpt)).map iu
  let qp : Xp.left ⟶ X₀.left := pullback.fst Xt.hom (S.map gpt) ≫ qt
  let Mp : Xp.left.Modules := (Scheme.Modules.pullback qp).obj F₀
  have : IsClosedImmersion jp.left :=
    MorphismProperty.overPullbackMap (P := @IsClosedImmersion) (S.map gpt) jt (by assumption)
  have : IsOpenImmersion iup.left :=
    MorphismProperty.overPullbackMap (P := @IsOpenImmersion) (S.map gpt) iu
      (inferInstanceAs (IsOpenImmersion Ut.ι))
  have hflatUp : IsFlatOver Up.hom.toLRSHom.toShHom
      ((Scheme.Modules.pullback (pullback.fst Uover.hom (S.map gpt))).obj FUt) := by
    let fUp := ((Over.pullback (S.map gpt)).map fUt).left
    let qYp := ((Over.pullback (S.map gpt)).obj Yt).hom
    have : IsIso qYp := by
      show IsIso (pullback.snd (𝟙 (S.obj t.left)) (S.map gpt))
      infer_instance
    have h := (isFlatOver_comp_iff_of_etale fUp qYp
      ((Scheme.Modules.pullback (pullback.fst Uover.hom (S.map gpt))).obj FUt)).mpr hflatp
    simpa only [show fUp ≫ qYp = Up.hom from
      ((Over.pullback (S.map gpt)).map fUt).w] using h
  have hpathp : iup.left ≫ qp =
      pullback.fst Uover.hom (S.map gpt) ≫ (Ut.ι ≫ qt) := by
    simp [iup, iu, qp, Over.pullback_map_left, Category.assoc, pullback.lift_fst_assoc]
  let eMp : (Scheme.Modules.pullback iup.left).obj Mp ≅
      (Scheme.Modules.pullback (pullback.fst Uover.hom (S.map gpt))).obj FUt :=
    (modulePullbackCompIsoOfEq iup.left qp
      (pullback.fst Uover.hom (S.map gpt) ≫ (Ut.ι ≫ qt)) hpathp F₀) ≪≫
      ((Scheme.Modules.pullbackComp (pullback.fst Uover.hom (S.map gpt))
        (Ut.ι ≫ qt)).app F₀).symm
  have hflatUp' : IsFlatOver Up.hom.toLRSHom.toShHom
      ((Scheme.Modules.pullback iup.left).obj Mp) :=
    isFlatOver_of_moduleIso _ eMp.symm hflatUp
  have : LocallyOfFiniteType Xt.hom := inferInstance
  have : LocallyOfFiniteType Xp.hom := by
    dsimp only [Xp]
    infer_instance
  have : Mp.IsQuasicoherent := by
    dsimp only [Mp]
    infer_instance
  have : Mp.IsFiniteType := by
    dsimp only [Mp]
    infer_instance
  have hdimXp : IsFlatOverInDimensionsGE Xp.hom Mp n := by
    apply flatInDimensions_of_closed_bad_locus Xp.hom Mp n jp.left
    · intro s
      rw [jp.w]
      have : LocallyOfFinitePresentation Zt.hom := hZt.1
      have hd := congrFun (Scheme.Hom.fiberDimension_eq_of_isPullback
        (IsPullback.of_hasPullback Zt.hom (S.map gpt))) s
      change topologicalKrullDim (Zp.hom.fiber s) =
        topologicalKrullDim (Zt.hom.fiber (S.map gpt s)) at hd
      rw [hd]
      apply (hdimZt _).trans_lt
      exact_mod_cast Nat.sub_lt hn (by decide : 0 < 1)
    · intro x hx
      have hxU : x ∈ Set.range iup.left := by
        rw [range_over_pullback_map (S.map gpt) iu]
        show (pullback.fst Xt.hom (S.map gpt) x) ∈ Set.range Ut.ι
        rw [Scheme.Opens.range_ι]
        show pullback.fst Xt.hom (S.map gpt) x ∉ Set.range jt.left
        exact fun hmem => hx (by rwa [range_over_pullback_map (S.map gpt) jt])
      obtain ⟨z, rfl⟩ := hxU
      apply (isFlatOverAt_iff_modulePullback_isFlatOverAt
        iup.left Xp.hom Mp z (Flat.stalkMap iup.left z)).mpr
      show IsFlatOverAt (iup.left ≫ Xp.hom).toLRSHom.toShHom
        ((Scheme.Modules.pullback iup.left).obj Mp) z
      rw [iup.w]
      exact hflatUp' z
  let gp₀ : p ⟶ i₀ := gpt ≫ t.hom ≫ grm ≫ gml ≫ gli₀
  have sq : IsPullback qp Xp.hom X₀.hom (S.map gp₀) := by
    have h := (IsPullback.of_hasPullback Xt.hom (S.map gpt)).paste_horiz
      ((IsPullback.of_hasPullback Xr.hom (S.map t.hom)).paste_horiz
        ((IsPullback.of_hasPullback Xm.hom (S.map grm)).paste_horiz
          ((IsPullback.of_hasPullback Xl.hom (S.map gml)).paste_horiz
            (IsPullback.of_hasPullback X₀.hom (S.map gli₀)))))
    simpa only [gp₀, Functor.map_comp, qp, qt, qr, qm, ql, Xp, Over.pullback_obj_hom] using h
  exact ⟨p, gp₀, flatInDimensions_canonical_of_isPullback sq F₀ n hdimXp⟩

private theorem flatInDimensions_iterated_baseChange_iff
    {X S T B : Scheme.{u}} (f : X ⟶ S) [LocallyOfFiniteType f]
    (F : X.Modules) [F.IsQuasicoherent] [F.IsFiniteType]
    (a : T ⟶ B) (b : B ⟶ S) (d : T ⟶ S) (hd : a ≫ b = d) (n : ℕ) :
    IsFlatOverInDimensionsGE (pullback.snd (pullback.snd f b) a)
      ((Scheme.Modules.pullback (pullback.fst (pullback.snd f b) a)).obj
        ((Scheme.Modules.pullback (pullback.fst f b)).obj F)) n ↔
    IsFlatOverInDimensionsGE (pullback.snd f d)
      ((Scheme.Modules.pullback (pullback.fst f d)).obj F) n := by
  have sq : IsPullback
      (pullback.fst (pullback.snd f b) a ≫ pullback.fst f b)
      (pullback.snd (pullback.snd f b) a) f d := by
    rw [← hd]
    exact (IsPullback.of_hasPullback (pullback.snd f b) a).paste_horiz
      (IsPullback.of_hasPullback f b)
  let e : (Scheme.Modules.pullback (pullback.fst (pullback.snd f b) a)).obj
        ((Scheme.Modules.pullback (pullback.fst f b)).obj F) ≅
      (Scheme.Modules.pullback
        (pullback.fst (pullback.snd f b) a ≫ pullback.fst f b)).obj F :=
    modulePullbackCompIsoOfEq (pullback.fst (pullback.snd f b) a) (pullback.fst f b)
      (pullback.fst (pullback.snd f b) a ≫ pullback.fst f b) rfl F
  exact ⟨fun h => flatInDimensions_canonical_of_isPullback sq F n
      (IsFlatOverInDimensionsGE.of_moduleIso _ e h),
    fun h => IsFlatOverInDimensionsGE.of_moduleIso _ e.symm
      (flatInDimensions_of_isPullback_canonical sq F n h)⟩

private theorem flatInDimensions_pullback_etale_iff
    {X A S T : Scheme.{u}} (f : X ⟶ S) [LocallyOfFiniteType f]
    (F : X.Modules) [F.IsQuasicoherent] [F.IsFiniteType]
    (q : A ⟶ X) [Etale q] [Surjective q] (g : T ⟶ S) (n : ℕ) :
    IsFlatOverInDimensionsGE (pullback.snd (q ≫ f) g)
      ((Scheme.Modules.pullback (pullback.fst (q ≫ f) g)).obj
        ((Scheme.Modules.pullback q).obj F)) n ↔
    IsFlatOverInDimensionsGE (pullback.snd f g)
      ((Scheme.Modules.pullback (pullback.fst f g)).obj F) n := by
  let Q : Over.mk (q ≫ f) ⟶ Over.mk f := Over.homMk q rfl
  let Qg := (Over.pullback g).map Q
  have : Etale Qg.left :=
    MorphismProperty.overPullbackMap (P := @Etale) g Q (inferInstanceAs (Etale q))
  have : Surjective Qg.left :=
    MorphismProperty.overPullbackMap (P := @Surjective) g Q
      (inferInstanceAs (Surjective q))
  let M := (Scheme.Modules.pullback (pullback.fst f g)).obj F
  have hw : Qg.left ≫ pullback.snd f g = pullback.snd (q ≫ f) g := Qg.w
  have hpath : Qg.left ≫ pullback.fst f g = pullback.fst (q ≫ f) g ≫ q := by
    simp [Qg, Q, Over.pullback_map_left, pullback.lift_fst]
  let e : (Scheme.Modules.pullback Qg.left).obj M ≅
      (Scheme.Modules.pullback (pullback.fst (q ≫ f) g)).obj
        ((Scheme.Modules.pullback q).obj F) :=
    modulePullbackCompIsoOfEq Qg.left (pullback.fst f g)
      (pullback.fst (q ≫ f) g ≫ q) hpath F ≪≫
        ((Scheme.Modules.pullbackComp (pullback.fst (q ≫ f) g) q).app F).symm
  have hiff := flatInDimensions_comp_etale_iff (pullback.snd f g) M Qg.left Qg.left.surjective n
  exact ⟨fun h => hiff.mp
      (flatInDimensions_congr hw.symm _ n (IsFlatOverInDimensionsGE.of_moduleIso _ e.symm h)),
    fun h => IsFlatOverInDimensionsGE.of_moduleIso _ e
      (flatInDimensions_congr hw _ n (hiff.mpr h))⟩

private theorem flatDimensionFunctor_limitPreserving_of_zero
    (D : FlatDimensionSituation.{max u v w})
    [QuasiCompact D.f] [LocallyOfFinitePresentation D.f]
    [D.F.IsFinitePresentation] (hn : D.n = 0) :
    LimitPreserving.{max u v w, 0, v, w, (max u v w) + 1}
      (Over.forget D.S) D.flatDimensionFunctor := by
  let Dflat := flatnessSituationOfFlatDimensionSituation D
  let : Dflat.F.IsFinitePresentation := (inferInstance : D.F.IsFinitePresentation)
  exact limitPreserving_of_natIso (flatDimensionFunctor_zero_iso D hn).symm
    (FlatnessSituation.flatFunctor_limitPreserving.{u, v, w} Dflat)

namespace FlatDimensionSituation

/-- **Stacks Project, Tag 05MV.** Part (2): if `f : X ⟶ S` is quasi-compact and locally of
finite presentation and `F` is of finite presentation, then the functor `F_n` of flatness in
dimensions `≥ n` is limit preserving: it carries a cofiltered inverse limit of affine schemes
over `S` to a filtered colimit of sets.

This is part (2) of the tag; the whole tag is
`AlgebraicGeometry.FlatDimensionSituation.flatDimensionFunctor_isSheaf_fpqc_and_limitPreserving`,
which carries the tag. -/
public theorem flatDimensionFunctor_limitPreserving
    (D : FlatDimensionSituation.{max u v w})
    [QuasiCompact D.f] [LocallyOfFinitePresentation D.f]
    [D.F.IsFinitePresentation] :
    LimitPreserving.{max u v w, 0, v, w, (max u v w) + 1, max u v w}
      (Over.forget D.S) D.flatDimensionFunctor := by
  intro I instCat instCof E c hc hAffine hAffineLimit
  by_cases hn : D.n = 0
  · exact flatDimensionFunctor_limitPreserving_of_zero.{u, v, w} D hn I E c hc hAffine hAffineLimit
  refine ⟨Types.FilteredColimit.isColimitOf (E.op ⋙ D.flatDimensionFunctor)
    (D.flatDimensionFunctor.mapCocone c.op) (fun y ↦ ?_) fun k l xk xl _ ↦ ?_⟩
  · have hdim : D.IsFlatInDimensionsGEAfterBaseChange c.pt := y.down
    have hnpos : 0 < D.n := Nat.pos_of_ne_zero hn
    let : IsAffine c.pt.left := hAffineLimit
    let : CompactSpace c.pt.left := Scheme.compactSpace_of_isAffine c.pt.left
    let : QuasiSeparatedSpace c.pt.left := by infer_instance
    let S := E ⋙ Over.forget D.S
    let cs := (Over.forget D.S).mapCone c
    have : CompactSpace cs.pt := (inferInstance : CompactSpace c.pt.left)
    have : QuasiSeparatedSpace cs.pt := (inferInstance : QuasiSeparatedSpace c.pt.left)
    let : ∀ i : I, IsAffine (S.obj i) := hAffine
    let : ∀ i : I, CompactSpace (S.obj i) :=
      fun i => Scheme.compactSpace_of_isAffine (S.obj i)
    let : ∀ i : I, QuasiSeparatedSpace (S.obj i) := fun i => inferInstance
    let : ∀ {i j : I} (a : i ⟶ j), IsAffineHom (S.map a) :=
      fun {_ _} _ => inferInstance
    let i₀ : I := Classical.choice (IsCofiltered.nonempty (C := I))
    let f₀ := D.baseChangeMap (E.obj i₀)
    let F₀ := D.baseChangeModule (E.obj i₀)
    have : IsAffine (E.obj i₀).left := hAffine i₀
    have : QuasiCompact f₀ := by
      dsimp [f₀]
      infer_instance
    have : LocallyOfFinitePresentation f₀ := by
      dsimp [f₀]
      infer_instance
    have : F₀.IsQuasicoherent := D.baseChangeModule_isQuasicoherent _
    have : F₀.IsFiniteType := D.baseChangeModule_isFiniteType _
    have : F₀.IsFinitePresentation :=
      @Stacks.SheafOfModules.modulePullback_isFinitePresentation _ _
        (pullback.fst D.f (E.obj i₀).hom).toLRSHom.toShHom D.F (by assumption)
    obtain ⟨A, q, hA, hq, hqe, hfp⟩ :=
      exists_affine_etale_cover_of_finitePresentation f₀
    have : Etale q := hqe
    have : Surjective q := hq
    let F := (Scheme.Modules.pullback q).obj F₀
    have : F.IsFinitePresentation :=
      @Stacks.SheafOfModules.modulePullback_isFinitePresentation _ _
        q.toLRSHom.toShHom F₀ (by assumption)
    have hdim₀ : IsFlatOverInDimensionsGE
        (pullback.snd f₀ (cs.π.app i₀))
        ((Scheme.Modules.pullback (pullback.fst f₀ (cs.π.app i₀))).obj F₀) D.n :=
      (flatInDimensions_iterated_baseChange_iff D.f D.F (c.π.app i₀).left
        (E.obj i₀).hom c.pt.hom (c.π.app i₀).w D.n).mpr hdim
    have hdimA := (flatInDimensions_pullback_etale_iff
      f₀ F₀ q (cs.π.app i₀) D.n).mpr hdim₀
    obtain ⟨i, g, hi⟩ := eventually_flatInDimensionsGE_of_finitePresentation
      S cs hc i₀ (Over.mk (q ≫ f₀)) hfp F D.n hnpos hdimA
    have hdimStage := (flatInDimensions_pullback_etale_iff
      f₀ F₀ q (S.map g) D.n).mp hi
    have hiD : D.IsFlatInDimensionsGEAfterBaseChange (E.obj i) :=
      (flatInDimensions_iterated_baseChange_iff D.f D.F (E.map g).left
        (E.obj i₀).hom (E.obj i).hom (E.map g).w D.n).mp hdimStage
    refine ⟨Opposite.op i, ⟨hiD⟩, ?_⟩
    exact @Subsingleton.elim (D.flatDimensionFunctor.obj (Opposite.op c.pt))
      inferInstance _ _
  · obtain ⟨m, a, b, -⟩ := IsFilteredOrEmpty.cocone_objs k l
    exact ⟨m, a, b, @Subsingleton.elim _ (D.flatDimensionFunctor_obj_subsingleton _) _ _⟩

end FlatDimensionSituation

end AlgebraicGeometry

end
