module

public import Mathlib.AlgebraicGeometry.AffineTransitionLimit
public import Mathlib.CategoryTheory.Comma.LocallySmall
public import Mathlib.FieldTheory.IsAlgClosed.Classification
public import Mathlib.Logic.Small.Basic
public import Mathlib.Topology.Spectral.ConstructibleTopology
public import StacksCore.Tactic.StacksAttribute
public import StacksFrontier.AlgebraicGeometry.Limits.Descending.UnderlyingSpace
public import StacksFrontier.AlgebraicGeometry.MoreMorphisms.FibreConnectedComponents.Constructible
public import StacksFrontier.AlgebraicGeometry.MoreMorphisms.Weighting.BaseChange
public import StacksFrontier.AlgebraicGeometry.MoreMorphisms.Weighting.LevelSetConstructible
public import StacksFrontier.AlgebraicGeometry.Morphisms.Fibres.ConnectedComponents
public import StacksFrontier.AlgebraicGeometry.Morphisms.FinitePresentationPoint
public import StacksFrontier.AlgebraicGeometry.Morphisms.WeaklyEtale.UniversalFiniteOpen
public import StacksFrontier.AlgebraicGeometry.Morphisms.WeaklyEtale.Weighting
public import StacksFrontier.AlgebraicGeometry.Properties.Constructible
public import StacksFrontier.Topology.Spectral.DescentConstructible
public import StacksFrontier.Topology.Spectral.LimitConstructible
public import StacksFrontier.AlgebraicGeometry.MoreMorphisms.Weighting.LimitDescent.ConstructibleFibreSum
public import StacksFrontier.AlgebraicGeometry.MoreMorphisms.Weighting.LimitDescent.UniversalFiniteOpen

/-!
# Descent of a weighting to a finite stage of a limit of affine schemes

Let `Y = lim Y i` be the limit of a directed inverse system of affine schemes, let `f₀ : X₀ ⟶ Y i₀`
be a quasi-finite morphism of finite presentation of affine schemes, and let `f : X ⟶ Y` and
`f i : X i ⟶ Y i` be the base changes of `f₀`. Every weighting of `f` is, at all sufficiently late
stages, the pullback of a weighting of `f i`.

## Main results

* `AlgebraicGeometry.eventually_exists_weighting_baseChange`: a weighting of the limit base change
  comes from a weighting at every sufficiently late stage of the system.

## Implementation notes

The directed inverse system is a functor on the opposite of a directed preorder that is small
relative to the scheme universe, equipped with a limit cone. The finite-stage and limit morphisms
are the second projections from the canonical pullbacks, and the map from the limit base change to
a stage is the unique pullback lift of the canonical maps to the fixed-stage source and the stage
base. Since finite presentation supplies local finite type and quasi-compactness, the remaining
quasi-finiteness hypothesis is `AlgebraicGeometry.LocallyQuasiFinite`.

The proof runs along the source. A weighting has locally constructible level sets ([Stacks, Tag
0F3G]) and hence, the base change being affine and so a spectral space, only finitely many values;
a function with finitely many values and constructible level sets on the limit of a system of
spectral spaces is pulled back from a finite stage, which produces the candidate `w i`. That it is
a weighting is tested on the universal finite open subscheme `U` of a universal base change
`Y i,univ ⟶ Y i` ([Stacks, Tag 0F3N]): a function on the source is a weighting exactly when the
weighted fibre sum of `U` is locally constant, since every finite open piece of every base change
over an affine base is an inverse image of `U`. That fibre sum has finitely many values and
constructible level sets, because for the indicator function of a retrocompact open it counts the
geometric connected components of the fibres ([Stacks, Tag 055I]) and such functions span all
constructible integer-valued functions. Its pullback to the limit is locally constant, by [Stacks,
Tag 0F3B] applied to the given weighting, and openness of a constructible set descends to a finite
stage, which is the stage asked for.

## References

* [Stacks Project, Tag 0F3P](https://stacks.math.columbia.edu/tag/0F3P)
* [Stacks Project, Tag 0F3G](https://stacks.math.columbia.edu/tag/0F3G)
* [Stacks Project, Tag 0F3N](https://stacks.math.columbia.edu/tag/0F3N)
* [Stacks Project, Tag 0F3B](https://stacks.math.columbia.edu/tag/0F3B)
* [Stacks Project, Tag 0F2M](https://stacks.math.columbia.edu/tag/0F2M)
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits Opposite
open AlgebraicGeometry

universe v u

namespace AlgebraicGeometry

private lemma isWeighting_zero {X Y : Scheme.{u}} (f : X ⟶ Y) :
    IsWeighting f 0 := by
  intro U V h π g comm hg hj hπ
  convert (IsLocallyConstant.const (X := V) (0 : ℤ)) using 1
  funext v
  simp [separableDegreeWeightedFiberSum]

private noncomputable def pullbackDiagram
    {J : Type v} [Category.{v} J] {C : Type*} [Category C]
    (D : J ⥤ C) (j₀ : J) {X₀ : C} (f₀ : X₀ ⟶ D.obj j₀)
    [HasPullbacksAlong f₀] : Over j₀ ⥤ C :=
  Over.post D ⋙ Over.pullback f₀ ⋙ Over.forget X₀

private noncomputable def pullbackCone
    {J : Type v} [Category.{v} J] {C : Type*} [Category C]
    (D : J ⥤ C) (j₀ : J) {X₀ : C} (f₀ : X₀ ⟶ D.obj j₀)
    [HasPullbacksAlong f₀] (c : Cone D) :
    Cone (pullbackDiagram D j₀ f₀) :=
  (Over.pullback f₀ ⋙ Over.forget X₀).mapCone ((Over.conePost D j₀).obj c)

private noncomputable def pullbackCone_isLimit
    {J : Type v} [Category.{v} J] [IsCofiltered J]
    {C : Type*} [Category C] (D : J ⥤ C) (j₀ : J)
    {X₀ : C} (f₀ : X₀ ⟶ D.obj j₀) [HasPullbacksAlong f₀]
    (c : Cone D) (hc : IsLimit c) :
    IsLimit (pullbackCone D j₀ f₀ c) := by
  exact isLimitOfPreserves (Over.pullback f₀ ⋙ Over.forget X₀)
    (Over.isLimitConePost j₀ hc)

private lemma spectralSpace_affine {X : Scheme.{u}} [IsAffine X] :
    SpectralSpace X := by
  let : SpectralSpace (Spec (.of Γ(X, ⊤))) := PrimeSpectrum.instSpectralSpace
  exact SpectralSpace.of_homeomorph X.isoSpec.hom.homeomorph

private lemma spectralMap_homeomorph {X Y : Type*} [TopologicalSpace X] [TopologicalSpace Y]
    (e : X ≃ₜ Y) : IsSpectralMap e := by
  refine ⟨e.continuous, fun s _ hs ↦ ?_⟩
  have heq : e ⁻¹' s = e.symm '' s := by
    ext x
    simp only [Set.mem_preimage, Set.mem_image]
    refine ⟨fun hx ↦ ⟨e x, hx, e.symm_apply_apply x⟩, ?_⟩
    rintro ⟨y, hy, rfl⟩
    simpa using hy
  rw [heq]
  exact hs.image e.symm.continuous

/-- The preimage of a constructible set under a spectral map is constructible. -/
private lemma isConstructible_preimage_of_isSpectralMap {X Y : Type*} [TopologicalSpace X]
    [TopologicalSpace Y] [QuasiSeparatedSpace X] [CompactSpace Y] {f : X → Y}
    (hf : IsSpectralMap f) {s : Set Y}
    (hs : Topology.IsConstructible s) : Topology.IsConstructible (f ⁻¹' s) :=
  hs.preimage hf.continuous fun _ hU hUc ↦
    (hf.isCompact_preimage_of_isOpen hU hUc.isCompact).isRetrocompact (hU.preimage hf.continuous)

/-- Pulling back along a transition map and then along a projection is pulling back along the
projection of the target. -/
private lemma preimage_projFun_preimage_map {J : Type v} [SmallCategory J] [IsCofiltered J]
    (D : SpectralDiagram.{v, u} J) {j i : J} (a : j ⟶ i) (S : Set (D.F.obj i)) :
    D.projFun j ⁻¹' (D.F.map a ⁻¹' S) = D.projFun i ⁻¹' S := by
  ext x
  change (D.F.map a).hom (D.projFun j x) ∈ S ↔ D.projFun i x ∈ S
  rw [D.projFun_comp a x]

private lemma factor_finite_range_function
    {J : Type v} [SmallCategory J] [IsCofiltered J]
    (D : SpectralDiagram.{v, u} J) (f : D.invLimit → ℤ)
    (hfinite : (Set.range f).Finite)
    (hlevels : ∀ n, Topology.IsConstructible {x | f x = n}) :
    ∃ (i : J) (fᵢ : D.F.obj i → ℤ),
      (Set.range fᵢ).Finite ∧
      (∀ n, Topology.IsConstructible {x | fᵢ x = n}) ∧
      f = fᵢ ∘ D.projFun i := by
  classical
  let : ∀ j, SpectralSpace (D.F.obj j) := D.isSpectralSpace
  let t : Finset ℤ := hfinite.toFinset
  choose i E hE hdesc using fun n : ℤ => descend_isConstructible D (hlevels n)
  obtain ⟨k, hk⟩ := IsCofiltered.inf_objs_exists (t.image i)
  have hik (n : ℤ) (hn : n ∈ t) : Nonempty (k ⟶ i n) :=
    hk (Finset.mem_image.mpr ⟨n, hn, rfl⟩)
  let a (n : ℤ) (hn : n ∈ t) : k ⟶ i n := Classical.choice (hik n hn)
  let Eₖ : {n : ℤ // n ∈ t} → Set (D.F.obj k) := fun n =>
    (D.F.map (a n.1 n.2)).hom ⁻¹' E n.1
  have hEₖ (n : {n : ℤ // n ∈ t}) : Topology.IsConstructible (Eₖ n) := by
    exact isConstructible_preimage_of_isSpectralMap (D.isSpectralMap (a n.1 n.2)) (hE n.1)
  have hEq (n : {n : ℤ // n ∈ t}) :
      D.projFun k ⁻¹' Eₖ n = {x | f x = n.1} := by
    exact (preimage_projFun_preimage_map D (a n.1 n.2) (E n.1)).trans (hdesc n.1)
  let g : ({n : ℤ // n ∈ t} → Bool) → ℤ := fun p ↦
    if hp : ∃ n, p n = true then (Classical.choose hp).1 else 0
  let fᵢ : D.F.obj k → ℤ := fun x ↦ g (fun n ↦ decide (x ∈ Eₖ n))
  refine ⟨k, fᵢ, ?_, ?_, ?_⟩
  · apply (Set.finite_range g).subset
    rintro n ⟨x, rfl⟩
    exact ⟨_, rfl⟩
  · exact isConstructible_levelSet_membershipFunction Eₖ hEₖ g
  · funext x
    have hmem : ∃ n : {n : ℤ // n ∈ t}, decide (D.projFun k x ∈ Eₖ n) = true := by
      refine ⟨⟨f x, hfinite.mem_toFinset.mpr (Set.mem_range_self x)⟩, ?_⟩
      apply decide_eq_true
      show x ∈ D.projFun k ⁻¹' Eₖ ⟨f x, _⟩
      rw [hEq]
      rfl
    have hn : D.projFun k x ∈ Eₖ (Classical.choose hmem) :=
      of_decide_eq_true (Classical.choose_spec hmem)
    have hnval : f x = (Classical.choose hmem).1 := by
      change x ∈ D.projFun k ⁻¹' Eₖ (Classical.choose hmem) at hn
      rw [hEq] at hn
      exact hn
    show f x = g (fun n ↦ decide (D.projFun k x ∈ Eₖ n))
    dsimp only [g]
    rw [dite_eq_left hmem]
    exact hnval

/-- The spectral diagram of underlying spaces of a diagram of schemes with spectral transition
maps. -/
private noncomputable def schemeSpectralDiagram {J : Type u} [SmallCategory J] [IsCofiltered J]
    (D : J ⥤ Scheme.{u}) (hs : ∀ j, SpectralSpace (D.obj j))
    (hm : ∀ {i j : J} (a : i ⟶ j), IsSpectralMap (D.map a)) : SpectralDiagram.{u, u} J where
  F := D ⋙ Scheme.forgetToTop
  isSpectralSpace := hs
  isSpectralMap a := hm a

/-- The limit of a diagram of schemes is homeomorphic to the limit of its underlying spaces,
compatibly with the projections. -/
private lemma exists_homeomorph_schemeSpectralDiagram {J : Type u} [SmallCategory J]
    [IsCofiltered J] (D : J ⥤ Scheme.{u}) (hs : ∀ j, SpectralSpace (D.obj j))
    (hm : ∀ {i j : J} (a : i ⟶ j), IsSpectralMap (D.map a)) [PreservesLimit D Scheme.forgetToTop]
    (c : Cone D) (hc : IsLimit c) :
    ∃ e : c.pt ≃ₜ (schemeSpectralDiagram D hs hm).invLimit,
      ∀ i x, (schemeSpectralDiagram D hs hm).projFun i (e x) = c.π.app i x := by
  have hc' : IsLimit (Scheme.forgetToTop.mapCone c) := isLimitOfPreserves Scheme.forgetToTop hc
  exact ⟨TopCat.homeoOfIso (hc'.conePointUniqueUpToIso (limit.isLimit _)), fun i x ↦
    ConcreteCategory.congr_hom (hc'.conePointUniqueUpToIso_hom_comp (limit.isLimit _) i) x⟩

private lemma factor_constructible_function_of_affine_limit
    {J : Type u} [SmallCategory J] [IsCofiltered J]
    (D : J ⥤ Scheme.{u}) (c : Cone D) (hc : IsLimit c)
    [∀ j, IsAffine (D.obj j)] (f : c.pt → ℤ)
    (hfinite : (Set.range f).Finite)
    (hlevels : ∀ n, Topology.IsConstructible {x | f x = n}) :
    ∃ (i : J) (fᵢ : D.obj i → ℤ), (Set.range fᵢ).Finite ∧
      (∀ n, Topology.IsConstructible {x | fᵢ x = n}) ∧ f = fᵢ ∘ c.π.app i := by
  have : IsAffine c.pt := Scheme.isAffine_of_isLimit c hc
  have : SpectralSpace c.pt := spectralSpace_affine
  let S := schemeSpectralDiagram D (fun _ ↦ spectralSpace_affine) fun a ↦ (D.map a).isSpectralMap
  obtain ⟨e, he⟩ := exists_homeomorph_schemeSpectralDiagram D (fun _ ↦ spectralSpace_affine)
    (fun a ↦ (D.map a).isSpectralMap) c hc
  have hfinite' : (Set.range (f ∘ e.symm)).Finite :=
    hfinite.subset (Set.range_comp_subset_range _ _)
  have hlevels' (n : ℤ) : Topology.IsConstructible {x | (f ∘ e.symm) x = n} := by
    have : SpectralSpace S.invLimit := spectralDiagram_invLimit_spectralSpace S
    exact isConstructible_preimage_of_isSpectralMap (spectralMap_homeomorph e.symm) (hlevels n)
  obtain ⟨i, fᵢ, hfin, hlev, heq⟩ := factor_finite_range_function S
    (f ∘ e.symm) hfinite' hlevels'
  refine ⟨i, fᵢ, hfin, hlev, ?_⟩
  funext x
  have h := congrFun heq (e x)
  simp only [Function.comp_apply, e.symm_apply_apply] at h
  exact h.trans (congrArg fᵢ (he i x))

private lemma factor_constructible_function_of_small_affine_limit
    {J : Type v} [Small.{u} J] [Category.{v} J] [LocallySmall.{u} J]
    [IsCofiltered J]
    (D : J ⥤ Scheme.{u}) (c : Cone D) (hc : IsLimit c)
    [∀ j, IsAffine (D.obj j)] (f : c.pt → ℤ)
    (hfinite : (Set.range f).Finite)
    (hlevels : ∀ n, Topology.IsConstructible {x | f x = n}) :
    ∃ (i : J) (fᵢ : D.obj i → ℤ), (Set.range fᵢ).Finite ∧
      (∀ n, Topology.IsConstructible {x | fᵢ x = n}) ∧ f = fᵢ ∘ c.π.app i := by
  let : Small.{u} (ShrinkHoms J) := by change Small.{u} J; infer_instance
  let E := (ShrinkHoms.equivalence J).trans
    (Shrink.equivalence.{u} (ShrinkHoms J))
  let D' : Shrink.{u} (ShrinkHoms J) ⥤ Scheme.{u} := E.inverse ⋙ D
  let c' : Cone D' := c.whisker E.inverse
  have hc' : IsLimit c' := hc.whiskerEquivalence E.symm
  let : IsCofiltered (Shrink.{u} (ShrinkHoms J)) :=
    IsCofiltered.of_equivalence E
  let (j : Shrink.{u} (ShrinkHoms J)) : IsAffine (D'.obj j) :=
    inferInstanceAs (IsAffine (D.obj (E.inverse.obj j)))
  obtain ⟨i, fᵢ, hfin, hlev, heq⟩ :=
    factor_constructible_function_of_affine_limit D' c' hc' f hfinite hlevels
  exact ⟨E.inverse.obj i, fᵢ, hfin, hlev, heq⟩

private lemma small_over_op_preorder
    {I : Type v} [Small.{u} I] [Preorder I] (i₀ : I) :
    Small.{u} (Over (op i₀)) := by
  let : Small.{u} (Iᵒᵖ) := Opposite.small
  apply small_of_injective (f := fun j : Over (op i₀) => j.left)
  rintro ⟨x, ⟨⟩, f⟩ ⟨y, ⟨⟩, g⟩ h
  change x = y at h
  subst y
  congr
  exact Subsingleton.elim _ _

private lemma isClopen_constructibleTopology_of_isConstructible
    {X : Type*} [TopologicalSpace X] [SpectralSpace X]
    {E : Set X} (hE : Topology.IsConstructible E) :
    @IsClopen X (constructibleTopology X) E := by
  induction hE using Topology.IsConstructible.empty_union_induction with
  | open_retrocompact U hU hUc => exact hUc.isCompact.isClopen_constructibleTopology hU
  | union s _ t _ hs ht => exact @IsClopen.union X (constructibleTopology X) s t hs ht
  | compl s _ hs => exact @IsClopen.compl X (constructibleTopology X) s hs

private lemma exists_map_preimage_eq_of_limit_preimage_eq
    {J : Type u} [SmallCategory J] [IsCofiltered J]
    (D : SpectralDiagram.{u, u} J) (i : J)
    {E G : Set (D.F.obj i)} (hE : Topology.IsConstructible E)
    (hG : Topology.IsConstructible G)
    (heq : D.projFun i ⁻¹' E = D.projFun i ⁻¹' G) :
    ∃ (j : J) (a : j ⟶ i), D.F.map a ⁻¹' E = D.F.map a ⁻¹' G := by
  let : ∀ j, SpectralSpace (D.F.obj j) := D.isSpectralSpace
  have hEc := isClopen_constructibleTopology_of_isConstructible hE
  have hGc := isClopen_constructibleTopology_of_isConstructible hG
  obtain ⟨j, a, ha⟩ :=
    (SpectralLimits.preimage_limit_π_subset_iff_exists_map_preimage_subset
      D.F D.isSpectralSpace D.isSpectralMap i E G hEc.1 hGc.2).mp heq.le
  obtain ⟨k, b, hb⟩ :=
    (SpectralLimits.preimage_limit_π_subset_iff_exists_map_preimage_subset
      D.F D.isSpectralSpace D.isSpectralMap i G E hGc.1 hEc.2).mp heq.ge
  obtain ⟨l, c, d, hcd⟩ := IsCofiltered.cospan a b
  refine ⟨l, c ≫ a, Set.Subset.antisymm ?_ ?_⟩
  · simpa only [Functor.map_comp, TopCat.coe_comp, Set.preimage_comp] using
      Set.preimage_mono (f := D.F.map c) ha
  · rw [hcd]
    simpa only [Functor.map_comp, TopCat.coe_comp, Set.preimage_comp] using
      Set.preimage_mono (f := D.F.map d) hb

private lemma exists_isOpen_preimage_of_isOpen_limit_preimage
    {J : Type u} [SmallCategory J] [IsCofiltered J]
    (D : SpectralDiagram.{u, u} J) (i : J)
    {E : Set (D.F.obj i)} (hE : Topology.IsConstructible E)
    (ho : IsOpen (D.projFun i ⁻¹' E)) :
    ∃ (j : J) (a : j ⟶ i), IsOpen (D.F.map a ⁻¹' E) := by
  let : ∀ j, SpectralSpace (D.F.obj j) := D.isSpectralSpace
  have hpre : Topology.IsConstructible (D.projFun i ⁻¹' E) :=
    isConstructible_preimage_of_isSpectralMap (spectralDiagram_proj_isSpectralMap D i) hE
  obtain ⟨j, G, hG, hGo, hGpre⟩ := descend_isConstructible_isOpen D hpre ho
  let k := IsCofiltered.min i j
  let a : k ⟶ i := IsCofiltered.minToLeft i j
  let b : k ⟶ j := IsCofiltered.minToRight i j
  obtain ⟨l, c, hc⟩ := exists_map_preimage_eq_of_limit_preimage_eq D k
    (isConstructible_preimage_of_isSpectralMap (D.isSpectralMap a) hE)
    (isConstructible_preimage_of_isSpectralMap (D.isSpectralMap b) hG)
    (by rw [preimage_projFun_preimage_map, preimage_projFun_preimage_map, hGpre])
  refine ⟨l, c ≫ a, ?_⟩
  rw [Functor.map_comp, TopCat.coe_comp, Set.preimage_comp, hc]
  exact (hGo.preimage (D.F.map b).hom.continuous).preimage (D.F.map c).hom.continuous

private lemma exists_isLocallyConstant_comp_of_isLocallyConstant_limit_comp
    {J : Type u} [SmallCategory J] [IsCofiltered J] {A : Type*}
    (D : SpectralDiagram.{u, u} J) (i : J) (f : D.F.obj i → A)
    (hfinite : (Set.range f).Finite)
    (hlevels : ∀ n, Topology.IsConstructible {x | f x = n})
    (hf : IsLocallyConstant (f ∘ D.projFun i)) :
    ∃ (j : J) (a : j ⟶ i), IsLocallyConstant (f ∘ D.F.map a) := by
  classical
  have hopen (n : A) :
      ∃ (j : J) (a : j ⟶ i), IsOpen (D.F.map a ⁻¹' {x | f x = n}) :=
    exists_isOpen_preimage_of_isOpen_limit_preimage D i (hlevels n) (hf.isOpen_fiber n)
  have hfiniteOpen (t : Finset A) : ∃ (j : J) (a : j ⟶ i),
      ∀ n ∈ t, IsOpen (D.F.map a ⁻¹' {x | f x = n}) := by
    induction t using Finset.induction_on with
    | empty => exact ⟨i, 𝟙 i, by simp⟩
    | @insert n t _ ht =>
      obtain ⟨j, a, ha⟩ := hopen n
      obtain ⟨k, b, hb⟩ := ht
      obtain ⟨l, c, d, hcd⟩ := IsCofiltered.cospan a b
      refine ⟨l, c ≫ a, fun m hm ↦ ?_⟩
      rcases Finset.mem_insert.mp hm with rfl | hm
      · simpa only [Functor.map_comp, TopCat.coe_comp, Set.preimage_comp] using
          ha.preimage (D.F.map c).hom.continuous
      · rw [hcd]
        simpa only [Functor.map_comp, TopCat.coe_comp, Set.preimage_comp] using
          (hb m hm).preimage (D.F.map d).hom.continuous
  obtain ⟨j, a, ha⟩ := hfiniteOpen hfinite.toFinset
  refine ⟨j, a, IsLocallyConstant.iff_isOpen_fiber.mpr fun n ↦ ?_⟩
  by_cases hn : n ∈ Set.range f
  · exact ha n (hfinite.mem_toFinset.mpr hn)
  · have hempty : (f ∘ D.F.map a) ⁻¹' {n} = ∅ :=
      Set.eq_empty_iff_forall_notMem.mpr fun x hx ↦ hn ⟨D.F.map a x, hx⟩
    rw [hempty]
    exact isOpen_empty

private lemma exists_isLocallyConstant_comp_of_scheme_limit
    {J : Type u} [SmallCategory J] [IsCofiltered J] {A : Type*}
    (D : J ⥤ Scheme.{u}) (c : Cone D) (hc : IsLimit c)
    [∀ j, CompactSpace (D.obj j)] [∀ j, QuasiSeparatedSpace (D.obj j)]
    [∀ {i j : J} (a : i ⟶ j), IsAffineHom (D.map a)]
    (i : J) (f : D.obj i → A) (hfinite : (Set.range f).Finite)
    (hlevels : ∀ n, Topology.IsConstructible {x | f x = n})
    (hf : IsLocallyConstant (f ∘ c.π.app i)) :
    ∃ (j : J) (a : j ⟶ i), IsLocallyConstant (f ∘ D.map a) := by
  let S := schemeSpectralDiagram D (fun _ ↦ ⟨⟩) fun a ↦ (D.map a).isSpectralMap
  obtain ⟨e, he⟩ := exists_homeomorph_schemeSpectralDiagram D (fun _ ↦ ⟨⟩)
    (fun a ↦ (D.map a).isSpectralMap) c hc
  have hf' : IsLocallyConstant (f ∘ S.projFun i) := by
    have hπ : f ∘ S.projFun i = (f ∘ c.π.app i) ∘ e.symm := by
      funext x
      simp only [Function.comp_apply, ← he i (e.symm x), e.apply_symm_apply]
      rfl
    rw [hπ]
    exact hf.comp_continuous e.symm.continuous
  exact exists_isLocallyConstant_comp_of_isLocallyConstant_limit_comp S i f
    hfinite hlevels hf'

private lemma exists_isLocallyConstant_comp_of_small_scheme_limit
    {J : Type v} [Small.{u} J] [Category.{v} J] [LocallySmall.{u} J]
    [IsCofiltered J] {A : Type*}
    (D : J ⥤ Scheme.{u}) (c : Cone D) (hc : IsLimit c)
    [∀ j, CompactSpace (D.obj j)] [∀ j, QuasiSeparatedSpace (D.obj j)]
    [∀ {i j : J} (a : i ⟶ j), IsAffineHom (D.map a)]
    (i : J) (f : D.obj i → A) (hfinite : (Set.range f).Finite)
    (hlevels : ∀ n, Topology.IsConstructible {x | f x = n})
    (hf : IsLocallyConstant (f ∘ c.π.app i)) :
    ∃ (j : J) (a : j ⟶ i), IsLocallyConstant (f ∘ D.map a) := by
  let : Small.{u} (ShrinkHoms J) := by change Small.{u} J; infer_instance
  let E := (ShrinkHoms.equivalence J).trans
    (Shrink.equivalence.{u} (ShrinkHoms J))
  let D' : Shrink.{u} (ShrinkHoms J) ⥤ Scheme.{u} := E.inverse ⋙ D
  let c' : Cone D' := c.whisker E.inverse
  have hc' : IsLimit c' := hc.whiskerEquivalence E.symm
  let : IsCofiltered (Shrink.{u} (ShrinkHoms J)) :=
    IsCofiltered.of_equivalence E
  let (j : Shrink.{u} (ShrinkHoms J)) : CompactSpace (D'.obj j) :=
    inferInstanceAs (CompactSpace (D.obj (E.inverse.obj j)))
  let (j : Shrink.{u} (ShrinkHoms J)) : QuasiSeparatedSpace (D'.obj j) :=
    inferInstanceAs (QuasiSeparatedSpace (D.obj (E.inverse.obj j)))
  let {j k : Shrink.{u} (ShrinkHoms J)} (a : j ⟶ k) :
      IsAffineHom (D'.map a) :=
    inferInstanceAs (IsAffineHom (D.map (E.inverse.map a)))
  let i' := E.functor.obj i
  let t : E.inverse.obj i' ⟶ i := (E.unitIso.app i).inv
  let f' : D'.obj i' → A := f ∘ D.map t
  have hfinite' : (Set.range f').Finite :=
    hfinite.subset (Set.range_comp_subset_range _ _)
  have hlevels' (n : A) : Topology.IsConstructible {x | f' x = n} :=
    (D.map t).isConstructible_preimage (hlevels n)
  have hπ : c'.π.app i' ≫ D.map t = c.π.app i := by
    simp [c', D', i', t]
  have hf' : IsLocallyConstant (f' ∘ c'.π.app i') := by
    have heq : f' ∘ c'.π.app i' = f ∘ c.π.app i := by
      funext x
      exact congrArg (fun m : c.pt ⟶ D.obj i ↦ f (m x)) hπ
    rwa [heq]
  obtain ⟨j, a, ha⟩ := exists_isLocallyConstant_comp_of_scheme_limit
    D' c' hc' i' f' hfinite' hlevels' hf'
  refine ⟨E.inverse.obj j, E.inverse.map a ≫ t, ?_⟩
  change IsLocallyConstant (f ∘ D.map t ∘ D.map (E.inverse.map a)) at ha
  have heq : f ∘ D.map t ∘ D.map (E.inverse.map a) =
      f ∘ D.map (E.inverse.map a ≫ t) := by
    funext x
    simp only [Function.comp_apply, Functor.map_comp, Scheme.Hom.comp_apply]
  rwa [← heq]

private lemma exists_isLocallyConstant_pullback_snd
    {J : Type v} [Small.{u} J] [Category.{v} J] [LocallySmall.{u} J]
    [IsCofiltered J] {A : Type*}
    (D : J ⥤ Scheme.{u}) (c : Cone D) (hc : IsLimit c)
    [∀ j, IsAffine (D.obj j)] (i : J)
    {V : Scheme.{u}} [CompactSpace V] [QuasiSeparatedSpace V]
    (g : V ⟶ D.obj i) (f : V → A) (hfinite : (Set.range f).Finite)
    (hlevels : ∀ n, Topology.IsConstructible {x | f x = n})
    (hf : IsLocallyConstant (f ∘ pullback.snd (c.π.app i) g)) :
    ∃ (j : J) (a : j ⟶ i), IsLocallyConstant (f ∘ pullback.snd (D.map a) g) := by
  let Q := pullbackDiagram D i g
  let cQ := pullbackCone D i g c
  let : Small.{u} (Over i) := by
    let : ∀ j : J, Small.{u} (j ⟶ i) := fun _ ↦ inferInstance
    apply small_of_injective (f := fun j : Over i => (⟨j.left, j.hom⟩ :
      Σ k : J, k ⟶ i))
    rintro ⟨j, f⟩ ⟨k, h⟩ heq
    cases heq
    have : f = h := Subsingleton.elim _ _
    subst h
    rfl
  let : LocallySmall.{u} (Over i) := inferInstance
  let q (j : Over i) : Q.obj j ⟶ V := pullback.snd (D.map j.hom) g
  let : MorphismProperty.IsStableUnderBaseChangeAlong (@IsAffineHom) g :=
    ⟨fun pb hf ↦ isAffineHom_isStableUnderBaseChange.of_isPullback pb hf⟩
  have hq (j : Over i) : IsAffineHom (q j) := by
    dsimp only [q]
    exact MorphismProperty.pullback_snd (P := @IsAffineHom) (D.map j.hom) g
      (inferInstanceAs (IsAffineHom (D.map j.hom)))
  have hw {j k : Over i} (a : j ⟶ k) : Q.map a ≫ q k = q j :=
    Over.w ((Over.pullback g).map ((Over.post D).map a))
  let (j : Over i) : CompactSpace (Q.obj j) := by
    let := hq j
    exact QuasiCompact.compactSpace_of_compactSpace (q j)
  let (j : Over i) : QuasiSeparatedSpace (Q.obj j) := by
    let := hq j
    exact quasiSeparatedSpace_of_quasiSeparated (q j)
  let {j k : Over i} (a : j ⟶ k) : IsAffineHom (Q.map a) := by
    let := hq k
    have : IsAffineHom (Q.map a ≫ q k) := by rw [hw]; exact hq j
    exact IsAffineHom.of_comp (Q.map a) (q k)
  let i' : Over i := Over.mk (𝟙 i)
  have hπ : cQ.π.app i' ≫ q i' = pullback.snd (c.π.app i) g :=
    Over.w ((Over.pullback g).map (((Over.conePost D i).obj c).π.app i'))
  have hf' : IsLocallyConstant ((f ∘ q i') ∘ cQ.π.app i') := by
    have heq : (f ∘ q i') ∘ cQ.π.app i' = f ∘ pullback.snd (c.π.app i) g := by
      funext x
      exact congrArg (fun a : cQ.pt ⟶ V ↦ f (a x)) hπ
    rwa [heq]
  obtain ⟨j, a, ha⟩ := exists_isLocallyConstant_comp_of_small_scheme_limit Q cQ
    (pullbackCone_isLimit D i g c hc) i' (f ∘ q i')
    (hfinite.subset (Set.range_comp_subset_range _ _))
    (fun n ↦ (q i').isConstructible_preimage (hlevels n)) hf'
  refine ⟨j.left, j.hom, ?_⟩
  have heq : (f ∘ q i') ∘ Q.map a = f ∘ q j := by
    funext x
    exact congrArg (fun b : Q.obj j ⟶ V ↦ f (b x)) (hw a)
  rwa [heq] at ha


/-- A weighting on the limit base change of a quasi-finite finitely presented
morphism of affine schemes comes from a weighting at every sufficiently late
stage of the directed inverse system. -/
@[stacks 0F3P]
theorem eventually_exists_weighting_baseChange
    {I : Type v} [Small.{u} I] [Preorder I] [IsDirected I (· ≤ ·)]
    (D : Iᵒᵖ ⥤ Scheme.{u}) (c : Cone D) (hc : IsLimit c)
    [∀ i : I, IsAffine (D.obj (op i))]
    (i₀ : I) (X₀ : Scheme.{u}) [IsAffine X₀]
    (f₀ : X₀ ⟶ D.obj (op i₀))
    (hfp : FinitePresentation f₀)
    [LocallyQuasiFinite f₀]
    (w : (pullback f₀ (c.π.app (op i₀)) : Scheme.{u}) → ℤ)
    (hw : IsWeighting
      (pullback.snd f₀ (c.π.app (op i₀))) w) :
    ∀ᶠ i in Filter.atTop, ∀ hi : i₀ ≤ i,
      ∃ wᵢ : (pullback f₀ (D.map (homOfLE hi).op) : Scheme.{u}) → ℤ,
        IsWeighting
          (pullback.snd f₀ (D.map (homOfLE hi).op)) wᵢ ∧
        w = wᵢ ∘ pullback.lift
          (pullback.fst f₀ (c.π.app (op i₀)))
          (pullback.snd f₀ (c.π.app (op i₀)) ≫ c.π.app (op i))
          (by
            rw [Category.assoc, c.w (homOfLE hi).op]
            exact pullback.condition) := by
  classical
  by_cases hz : w = 0
  · apply Filter.Eventually.of_forall
    intro i hi
    exact ⟨0, isWeighting_zero _, hz⟩
  let : Nonempty I := ⟨i₀⟩
  let : ∀ i : Iᵒᵖ, IsAffine (D.obj i) := fun i ↦ ‹∀ i : I, IsAffine (D.obj (op i))› i.unop
  have : IsAffine c.pt := Scheme.isAffine_of_isLimit c hc
  have : LocallyOfFinitePresentation f₀ := hfp.1
  have : IsAffine (((Functor.const Iᵒᵖ).obj c.pt).obj (op i₀)) :=
    inferInstanceAs (IsAffine c.pt)
  have : IsAffine (pullback f₀ (c.π.app (op i₀))) :=
    Scheme.Pullback.isAffine_of_isAffine_isAffine_isAffine _ _
  have hfinite : (Set.range w).Finite :=
    finite_range_of_weighting_level_sets (pullback.snd f₀ (c.π.app (op i₀))) w hw
  have hlevels (n : ℤ) : Topology.IsConstructible {x | w x = n} :=
    (isLocallyConstructible_weighting_levelSet hw n).isConstructible
  let p (i : I) (hi : i₀ ≤ i) :
      pullback f₀ (c.π.app (op i₀)) ⟶ pullback f₀ (D.map (homOfLE hi).op) :=
    pullback.lift (pullback.fst f₀ (c.π.app (op i₀)))
      (pullback.snd f₀ (c.π.app (op i₀)) ≫ c.π.app (op i))
      (by rw [Category.assoc, c.w (homOfLE hi).op]; exact pullback.condition)
  suffices hdesc : ∃ (j : I) (hj : i₀ ≤ j)
      (wⱼ : (pullback f₀ (D.map (homOfLE hj).op) : Scheme.{u}) → ℤ),
      IsWeighting (pullback.snd f₀ (D.map (homOfLE hj).op)) wⱼ ∧
      w = wⱼ ∘ p j hj by
    obtain ⟨j, hj, wⱼ, hwⱼ, hpⱼ⟩ := hdesc
    refine Filter.eventually_atTop.mpr ⟨j, fun i hji hi ↦ ?_⟩
    have hh : D.map (homOfLE hji).op ≫ D.map (homOfLE hj).op =
        D.map (homOfLE hi).op := by rw [← D.map_comp]; rfl
    let q : pullback f₀ (D.map (homOfLE hi).op) ⟶
        pullback f₀ (D.map (homOfLE hj).op) :=
      pullback.lift (pullback.fst f₀ (D.map (homOfLE hi).op))
        (pullback.snd f₀ (D.map (homOfLE hi).op) ≫ D.map (homOfLE hji).op)
        (by rw [Category.assoc, hh]; exact pullback.condition)
    have hq : IsPullback q (pullback.snd f₀ (D.map (homOfLE hi).op))
        (pullback.snd f₀ (D.map (homOfLE hj).op)) (D.map (homOfLE hji).op) :=
      isPullback_lift_snd f₀ _ _ _ hh
    have hpp : p i hi ≫ q = p j hj := by
      apply pullback.hom_ext
      · simp only [Category.assoc, p, q, pullback.lift_fst]
      · simp only [Category.assoc, p, q, pullback.lift_snd, pullback.lift_snd_assoc]
        rw [c.w (homOfLE hji).op]
    refine ⟨wⱼ ∘ q, IsWeighting.comp_of_isPullback hwⱼ hq, ?_⟩
    show w = (wⱼ ∘ q) ∘ p i hi
    rw [hpⱼ]
    funext x
    simp only [Function.comp_apply, ← Scheme.Hom.comp_apply, hpp]
  let Q := pullbackDiagram D (op i₀) f₀
  let cQ := pullbackCone D (op i₀) f₀ c
  have hcQ : IsLimit cQ := pullbackCone_isLimit D (op i₀) f₀ c hc
  have hQ (j : Over (op i₀)) : IsAffine (Q.obj j) := by
    show IsAffine (pullback (D.map j.hom) f₀)
    exact Scheme.Pullback.isAffine_of_isAffine_isAffine_isAffine _ _
  let e : cQ.pt ≅ pullback f₀ (c.π.app (op i₀)) :=
    pullbackSymmetry (c.π.app (op i₀)) f₀
  have hfiniteQ : (Set.range (w ∘ e.hom)).Finite :=
    hfinite.subset (Set.range_comp_subset_range _ _)
  have hlevelsQ (n : ℤ) : Topology.IsConstructible {x | (w ∘ e.hom) x = n} :=
    e.hom.isConstructible_preimage (hlevels n)
  let : Small.{u} (Over (op i₀)) := small_over_op_preorder i₀
  let : LocallySmall.{u} (Iᵒᵖ) := ⟨fun _ _ => small_subsingleton _⟩
  let (j : Over (op i₀)) : IsAffine (Q.obj j) := hQ j
  obtain ⟨j, wj, hwjfinite, hwjlevels, hwjdesc⟩ :=
    factor_constructible_function_of_small_affine_limit Q cQ hcQ
      (w ∘ e.hom) hfiniteQ hlevelsQ
  let i : I := j.left.unop
  have hj : i₀ ≤ i := leOfHom j.hom.unop
  let eᵢ : pullback f₀ (D.map (homOfLE hj).op) ≅ Q.obj j :=
    pullbackSymmetry f₀ (D.map (homOfLE hj).op)
  let wᵢ : (pullback f₀ (D.map (homOfLE hj).op) : Scheme.{u}) → ℤ :=
    fun x ↦ wj (eᵢ.hom x)
  have hwᵢfinite : (Set.range wᵢ).Finite :=
    hwjfinite.subset (Set.range_comp_subset_range _ _)
  have hwᵢlevels (n : ℤ) : Topology.IsConstructible {x | wᵢ x = n} :=
    eᵢ.hom.isConstructible_preimage (hwjlevels n)
  have hcomm : p i hj ≫ eᵢ.hom = e.inv ≫ cQ.π.app j := by
    cases (Subsingleton.elim j.hom (homOfLE hj).op)
    show p i hj ≫ eᵢ.hom = e.inv ≫
      pullback.lift
        (pullback.fst (c.π.app (op i₀)) f₀ ≫ c.π.app j.left)
        (pullback.snd (c.π.app (op i₀)) f₀)
        (by
          calc
            (pullback.fst (c.π.app (op i₀)) f₀ ≫ c.π.app j.left) ≫
                D.map j.hom =
                pullback.fst (c.π.app (op i₀)) f₀ ≫
                  (c.π.app j.left ≫ D.map j.hom) := Category.assoc _ _ _
            _ = pullback.fst (c.π.app (op i₀)) f₀ ≫ c.π.app (op i₀) :=
              by rw [c.w j.hom]
            _ = pullback.snd (c.π.app (op i₀)) f₀ ≫ f₀ := pullback.condition)
    have hfst : cQ.π.app j ≫ pullback.fst (D.map j.hom) f₀ =
        pullback.fst (c.π.app (op i₀)) f₀ ≫ c.π.app j.left := by
      have hpt : ((Over.conePost D (op i₀)).obj c).pt.hom =
          c.π.app (op i₀) := rfl
      show pullback.lift
          (pullback.fst (c.π.app (op i₀)) f₀ ≫ c.π.app j.left)
          (pullback.snd (c.π.app (op i₀)) f₀) _ ≫
          pullback.fst (D.map j.hom) f₀ = _
      exact pullback.lift_fst _ _ _
    have hsnd : cQ.π.app j ≫ pullback.snd (D.map j.hom) f₀ =
        pullback.snd (c.π.app (op i₀)) f₀ := by
      have hpt : ((Over.conePost D (op i₀)).obj c).pt.hom =
          c.π.app (op i₀) := rfl
      show pullback.lift
          (pullback.fst (c.π.app (op i₀)) f₀ ≫ c.π.app j.left)
          (pullback.snd (c.π.app (op i₀)) f₀) _ ≫
          pullback.snd (D.map j.hom) f₀ = _
      exact pullback.lift_snd _ _ _
    have hjhom : j.hom = (homOfLE hj).op := Subsingleton.elim _ _
    have heᵢ : eᵢ.hom = (pullbackSymmetry f₀ (D.map j.hom)).hom := by
      cases hjhom
      rfl
    let p' : pullback f₀ (c.π.app (op i₀)) ⟶ pullback f₀ (D.map j.hom) :=
      pullback.lift (pullback.fst f₀ (c.π.app (op i₀)))
        (pullback.snd f₀ (c.π.app (op i₀)) ≫ c.π.app j.left)
        (by rw [Category.assoc, c.w j.hom]; exact pullback.condition)
    have hp : p i hj = p' := by
      cases hjhom
      rfl
    have hefst : e.inv ≫ pullback.fst (c.π.app (op i₀)) f₀ =
        pullback.snd f₀ (c.π.app (op i₀)) := pullbackSymmetry_inv_comp_fst ..
    have hesnd : e.inv ≫ pullback.snd (c.π.app (op i₀)) f₀ =
        pullback.fst f₀ (c.π.app (op i₀)) := pullbackSymmetry_inv_comp_snd ..
    apply pullback.hom_ext
    · show (p i hj ≫ eᵢ.hom) ≫ pullback.fst (D.map j.hom) f₀ =
        (e.inv ≫ cQ.π.app j) ≫ pullback.fst (D.map j.hom) f₀
      calc
        (p i hj ≫ eᵢ.hom) ≫ pullback.fst (D.map j.hom) f₀ =
            p' ≫ (pullbackSymmetry f₀ (D.map j.hom)).hom ≫
              pullback.fst (D.map j.hom) f₀ := by
          rw [hp, heᵢ]
          exact Category.assoc _ _ _
        _ = p' ≫ pullback.snd f₀ (D.map j.hom) := by
          rw [pullbackSymmetry_hom_comp_fst]
        _ = pullback.snd f₀ (c.π.app (op i₀)) ≫ c.π.app j.left :=
          pullback.lift_snd _ _ _
        _ = (e.inv ≫ pullback.fst (c.π.app (op i₀)) f₀) ≫ c.π.app j.left := by
          rw [hefst]
        _ = e.inv ≫ cQ.π.app j ≫ pullback.fst (D.map j.hom) f₀ :=
          (Category.assoc _ _ _).trans (congrArg (fun m ↦ e.inv ≫ m) hfst.symm)
        _ = (e.inv ≫ cQ.π.app j) ≫ pullback.fst (D.map j.hom) f₀ :=
          (Category.assoc _ _ _).symm
    · show (p i hj ≫ eᵢ.hom) ≫ pullback.snd (D.map j.hom) f₀ =
        (e.inv ≫ cQ.π.app j) ≫ pullback.snd (D.map j.hom) f₀
      calc
        (p i hj ≫ eᵢ.hom) ≫ pullback.snd (D.map j.hom) f₀ =
            p' ≫ (pullbackSymmetry f₀ (D.map j.hom)).hom ≫
              pullback.snd (D.map j.hom) f₀ := by
          rw [hp, heᵢ]
          exact Category.assoc _ _ _
        _ = p' ≫ pullback.fst f₀ (D.map j.hom) := by
          rw [pullbackSymmetry_hom_comp_snd]
        _ = pullback.fst f₀ (c.π.app (op i₀)) := pullback.lift_fst _ _ _
        _ = e.inv ≫ pullback.snd (c.π.app (op i₀)) f₀ := hesnd.symm
        _ = (e.inv ≫ cQ.π.app j) ≫ pullback.snd (D.map j.hom) f₀ :=
          ((Category.assoc _ _ _).trans (congrArg (fun m ↦ e.inv ≫ m) hsnd)).symm
  have hwdesc : w = wᵢ ∘ p i hj := by
    funext x
    have hx := congrFun hwjdesc (e.inv x)
    have he : e.hom (e.inv x) = x := by simp
    change w (e.hom (e.inv x)) = wj (cQ.π.app j (e.inv x)) at hx
    rw [he] at hx
    have hc := congrArg
      (fun (m : pullback f₀ (c.π.app (op i₀)) ⟶ Q.obj j) ↦ m x) hcomm
    have hc' := congrArg wj hc
    change wj (eᵢ.hom (p i hj x)) = wj (cQ.π.app j (e.inv x)) at hc'
    exact hx.trans hc'.symm
  let fᵢ : pullback f₀ (D.map (homOfLE hj).op) ⟶ D.obj (op i) :=
    pullback.snd f₀ (D.map (homOfLE hj).op)
  let : IsAffine (pullback f₀ (D.map (homOfLE hj).op)) :=
    Scheme.Pullback.isAffine_of_isAffine_isAffine_isAffine _ _
  let : LocallyOfFinitePresentation fᵢ := inferInstance
  let : LocallyQuasiFinite fᵢ := inferInstance
  have hfpᵢ : FinitePresentation fᵢ :=
    ⟨inferInstance, inferInstance, inferInstance⟩
  obtain ⟨V, g, U, hg, hU, huniv, hτfinite, hτlevels, hcriterion⟩ :=
    exists_universal_constructible_integral fᵢ hfpᵢ wᵢ hwᵢfinite hwᵢlevels
  let f : pullback f₀ (c.π.app (op i₀)) ⟶ c.pt :=
    pullback.snd f₀ (c.π.app (op i₀))
  let : LocallyOfFiniteType f := inferInstance
  let : LocallyQuasiFinite f := inferInstance
  have hbase : c.π.app (op i) ≫ D.map (homOfLE hj).op =
      c.π.app (op i₀) := c.w (homOfLE hj).op
  have sqᵢ : IsPullback (p i hj) f fᵢ (c.π.app (op i)) := by
    simpa only [p, f, fᵢ] using
      (isPullback_lift_snd f₀ (D.map (homOfLE hj).op)
        (c.π.app (op i₀)) (c.π.app (op i)) hbase)
  let τᵢ : V → ℤ :=
    separableDegreeWeightedFiberSum
      (U.ι ≫ pullback.snd fᵢ g) (wᵢ ∘ (U.ι ≫ pullback.fst fᵢ g))
  have hτlimit : IsLocallyConstant
      (τᵢ ∘ pullback.snd (c.π.app (op i)) g) :=
    isLocallyConstant_finiteOpen_integral_of_isPullback sqᵢ g U
      wᵢ w hwdesc hw
  let : CompactSpace (D.obj (op i)) := Scheme.compactSpace_of_isAffine _
  let : QuasiCompact g := hg.2.1
  let : QuasiSeparated g := hg.2.2
  let : CompactSpace V := QuasiCompact.compactSpace_of_compactSpace g
  let : QuasiSeparatedSpace V := quasiSeparatedSpace_of_quasiSeparated g
  obtain ⟨j', a, hτj⟩ := exists_isLocallyConstant_pullback_snd
    D c hc (op i) g τᵢ hτfinite hτlevels hτlimit
  let k : I := j'.unop
  have hik : i ≤ k := leOfHom a.unop
  have h0k : i₀ ≤ k := hj.trans hik
  have hb : D.map a ≫ D.map (homOfLE hj).op =
      D.map (homOfLE h0k).op := by
    rw [← D.map_comp]
    congr 1
  let q : pullback f₀ (D.map (homOfLE h0k).op) ⟶
      pullback f₀ (D.map (homOfLE hj).op) :=
    pullback.lift (pullback.fst f₀ (D.map (homOfLE h0k).op))
      (pullback.snd f₀ (D.map (homOfLE h0k).op) ≫ D.map a)
      (by rw [Category.assoc, hb]; exact pullback.condition)
  let fₖ : pullback f₀ (D.map (homOfLE h0k).op) ⟶ D.obj j' :=
    pullback.snd f₀ (D.map (homOfLE h0k).op)
  have sqₖ : IsPullback q fₖ fᵢ (D.map a) := by
    simpa only [q, fₖ, fᵢ] using
      (isPullback_lift_snd f₀ (D.map (homOfLE hj).op)
        (D.map (homOfLE h0k).op) (D.map a) hb)
  let wₖ : (pullback f₀ (D.map (homOfLE h0k).op) : Scheme.{u}) → ℤ :=
    wᵢ ∘ q
  have hwₖ : IsWeighting fₖ wₖ :=
    isWeighting_of_universal_finiteOpen_baseChange sqₖ g U huniv
      wᵢ wₖ rfl hτj
  have hpq : p k h0k ≫ q = p i hj := by
    apply pullback.hom_ext
    · simp only [Category.assoc, q, pullback.lift_fst, p]
    · simp only [Category.assoc, q, pullback.lift_snd, p, pullback.lift_snd_assoc]
      rw [c.w a]
  refine ⟨k, h0k, wₖ, hwₖ, ?_⟩
  show w = (wᵢ ∘ q) ∘ p k h0k
  rw [hwdesc]
  funext x
  simp only [Function.comp_apply, ← Scheme.Hom.comp_apply, hpq]

end AlgebraicGeometry
