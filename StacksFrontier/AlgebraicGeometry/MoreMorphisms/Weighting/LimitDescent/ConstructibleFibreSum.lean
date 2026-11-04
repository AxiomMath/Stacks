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

/-!
# Constructibility of weighted fibre sums

Identities for the separable-degree weighted fibre sum `separableDegreeWeightedFiberSum` (for the
constant function `1` it counts the geometric connected components of the fibres; it is additive,
commutes with integer multiples, and on the indicator of an open subscheme it is the fibre sum of
the restriction), and the result that for a quasi-finite morphism of finite presentation to a
quasi-compact quasi-separated scheme, the weighted fibre sum of a function with finitely many
values and constructible level sets again has finitely many values and constructible level sets.
These are used to descend a weighting to a finite stage of a limit in
`StacksFrontier.AlgebraicGeometry.MoreMorphisms.Weighting.LimitDescent.FiniteStage`.
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits Opposite
open AlgebraicGeometry

universe v u

namespace AlgebraicGeometry

private lemma finite_residueFieldMap_of_locallyQuasiFinite
    {X Y : Scheme.{u}} (f : X ⟶ Y) [LocallyQuasiFinite f] (x : X) :
    letI := (f.residueFieldMap x).hom.toAlgebra;
      Module.Finite (Y.residueField (f x)) (X.residueField x) := by
  have hres : RingHom.QuasiFinite (X.residue x).hom :=
    .of_finite (.of_surjective _ (X.residue_surjective x))
  have hcomp := hres.comp (f.quasiFiniteAt x)
  have heq := congrArg CommRingCat.Hom.hom (Scheme.residue_residueFieldMap f x)
  change (f.residueFieldMap x).hom.comp (Y.residue (f x)).hom =
    (X.residue x).hom.comp (f.stalkMap x).hom at heq
  rw [← heq] at hcomp
  have hqf : (f.residueFieldMap x).hom.QuasiFinite := .of_comp hcomp
  let := (f.residueFieldMap x).hom.toAlgebra
  have : Algebra.QuasiFinite (Y.residueField (f x)) (X.residueField x) :=
    RingHom.quasiFinite_algebraMap.mp hqf
  exact Module.Finite.of_quasiFinite

private lemma isAlgClosed_residueField_spec
    (K : Type u) [Field K] [IsAlgClosed K] (x : Spec (.of K)) :
    IsAlgClosed ((Spec (.of K)).residueField x) := by
  let : x.asIdeal.IsPrime := x.isPrime
  let e := (Ideal.algEquivResidueFieldOfField x.asIdeal).toRingEquiv
  exact IsAlgClosed.of_ringEquiv K _
    (e.trans (Scheme.Spec.residueFieldIso (.of K) x).commRingCatIsoToRingEquiv.symm)

private lemma separableDegreeWeightedFiberSum_one_spec
    (K : Type u) [Field K] [IsAlgClosed K] {X : Scheme.{u}}
    (f : X ⟶ Spec (.of K)) [LocallyQuasiFinite f] (y : Spec (.of K)) :
    separableDegreeWeightedFiberSum f 1 y = (Nat.card X : ℤ) := by
  classical
  have hdegree (x : X) :
      (let := (f.residueFieldMap x).hom.toAlgebra;
        Field.finSepDegree ((Spec (.of K)).residueField (f x)) (X.residueField x)) = 1 := by
    let := (f.residueFieldMap x).hom.toAlgebra
    let : Module.Finite ((Spec (.of K)).residueField (f x)) (X.residueField x) :=
      finite_residueFieldMap_of_locallyQuasiFinite f x
    let : IsAlgClosed ((Spec (.of K)).residueField (f x)) :=
      isAlgClosed_residueField_spec K (f x)
    let : IsPurelyInseparable ((Spec (.of K)).residueField (f x)) (X.residueField x) :=
      Algebra.IsAlgebraic.isPurelyInseparable_of_isSepClosed
    exact IsPurelyInseparable.finSepDegree_eq_one _ _
  unfold separableDegreeWeightedFiberSum
  simp only [Subsingleton.elim (f _) y, ↓reduceIte, Pi.one_apply, one_mul, hdegree,
    Nat.cast_one]
  cases finite_or_infinite X with
  | inl h =>
    let : Finite X := h
    let : Fintype X := Fintype.ofFinite X
    rw [finsum_eq_sum_of_fintype]
    simp [Nat.card_eq_fintype_card]
  | inr h =>
    let : Infinite X := h
    rw [finsum_of_infinite_support]
    · simp
    · simpa only [Function.support_const (one_ne_zero : (1 : ℤ) ≠ 0)] using
        (Set.infinite_univ : (Set.univ : Set X).Infinite)

private lemma natCard_connectedComponents_eq_of_discrete
    (X : Type*) [TopologicalSpace X] [DiscreteTopology X] :
    Nat.card (ConnectedComponents X) = Nat.card X := by
  apply Nat.card_congr
  apply Equiv.symm
  apply Equiv.ofBijective (ConnectedComponents.mk : X → ConnectedComponents X)
  refine ⟨?_, ConnectedComponents.surjective_coe⟩
  intro x y hxy
  have h := ConnectedComponents.coe_eq_coe.mp hxy
  exact Set.singleton_injective (by simpa only [connectedComponent_eq_singleton] using h)

private lemma separableDegreeWeightedFiberSum_one_eq_components
    {X Y : Scheme.{u}} (f : X ⟶ Y) [LocallyQuasiFinite f] [QuasiCompact f] (y : Y) :
    separableDegreeWeightedFiberSum f 1 y =
      ((numGeometricConnectedComponents f y).toNat : ℤ) := by
  classical
  let K := AlgebraicClosure (Y.residueField y)
  let g : Spec (.of K) ⟶ Spec (Y.residueField y) :=
    Spec.map (CommRingCat.ofHom (algebraMap (Y.residueField y) K))
  let Z := geometricFiber f y K
  let q : Z ⟶ Spec (.of K) := pullback.snd (f.fiberToSpecResidueField y) g
  have : LocallyQuasiFinite q := inferInstanceAs (LocallyQuasiFinite (pullback.snd _ g))
  have : QuasiCompact q := inferInstanceAs (QuasiCompact (pullback.snd _ g))
  have heq₁ := separableDegreeWeightedFiberSum_comp_of_isPullback
    f (f.fiberι y) (f.fiberToSpecResidueField y) (Y.fromSpecResidueField y)
    (IsPullback.of_hasPullback _ _) (fun z ↦ f.finite_preimage_singleton z) 1
  have heq₂ := separableDegreeWeightedFiberSum_comp_of_isPullback
    (f.fiberToSpecResidueField y) (pullback.fst _ g) q g
    (IsPullback.of_hasPullback _ _)
    (fun z ↦ (f.fiberToSpecResidueField y).finite_preimage_singleton z) 1
  let z : Spec (.of K) := IsLocalRing.closedPoint K
  have hvalue : separableDegreeWeightedFiberSum f 1 y = (Nat.card Z : ℤ) := by
    have h₁ := congrFun heq₁ (g z)
    have h₂ := congrFun heq₂ z
    simp only [Function.comp_apply, Scheme.fromSpecResidueField_apply] at h₁ h₂
    exact h₁.trans (h₂.trans (separableDegreeWeightedFiberSum_one_spec K q z))
  have : DiscreteTopology Z := by
    apply isDiscrete_univ_iff.mp
    have h := q.isDiscrete_preimage_singleton z
    have heq : q ⁻¹' {z} = Set.univ := by
      ext x
      simp only [Set.mem_preimage, Set.mem_singleton_iff, Set.mem_univ, iff_true]
      exact Subsingleton.elim _ _
    rwa [heq] at h
  rw [hvalue, ← enatCard_connectedComponents_fiberBaseChange f y K]
  congr 1
  rw [← natCard_connectedComponents_eq_of_discrete Z]
  simp [ENat.card, Nat.card, Z]

private lemma finSepDegree_comp_openImmersion
    {U X Y : Scheme.{u}} (j : U ⟶ X) [IsOpenImmersion j] (f : X ⟶ Y) (x : U) :
    (letI := ((j ≫ f).residueFieldMap x).hom.toAlgebra;
      Field.finSepDegree (Y.residueField ((j ≫ f) x)) (U.residueField x)) =
    (letI := (f.residueFieldMap (j x)).hom.toAlgebra;
      Field.finSepDegree (Y.residueField (f (j x))) (X.residueField (j x))) := by
  let A := Y.residueField (f (j x))
  let B := X.residueField (j x)
  let C := U.residueField x
  let : Algebra A B := (f.residueFieldMap (j x)).hom.toAlgebra
  let : Algebra B C := (j.residueFieldMap x).hom.toAlgebra
  let : Algebra A C := ((j ≫ f).residueFieldMap x).hom.toAlgebra
  let : IsScalarTower A B C := IsScalarTower.of_algebraMap_eq fun a ↦ by
    show ((j ≫ f).residueFieldMap x).hom a =
      (j.residueFieldMap x).hom ((f.residueFieldMap (j x)).hom a)
    rw [Scheme.residueFieldMap_comp]
    rfl
  let e : B ≃ₐ[A] C := AlgEquiv.ofBijective (IsScalarTower.toAlgHom A B C)
    (ConcreteCategory.bijective_of_isIso (j.residueFieldMap x))
  exact (Field.finSepDegree_eq_of_equiv A B C e).symm

private lemma separableDegreeWeightedFiberSum_indicator_open
    {X Y : Scheme.{u}} (f : X ⟶ Y) (U : X.Opens) :
    separableDegreeWeightedFiberSum f ((U : Set X).indicator 1) =
      separableDegreeWeightedFiberSum (U.ι ≫ f) 1 := by
  classical
  funext y
  let d (x : X) : ℤ := by
    let := (f.residueFieldMap x).hom.toAlgebra
    exact (Field.finSepDegree (Y.residueField (f x)) (X.residueField x) : ℤ)
  let (x : U) : Field (U.toScheme.residueField x) :=
    Scheme.instFieldCarrierResidueField U.toScheme x
  have hdegree (x : U) :
      (let := ((U.ι ≫ f).residueFieldMap x).hom.toAlgebra;
        (Field.finSepDegree (Y.residueField ((U.ι ≫ f) x))
          (U.toScheme.residueField x) : ℤ)) = d x.1 :=
    congrArg (fun n : ℕ ↦ (n : ℤ)) (finSepDegree_comp_openImmersion U.ι f x)
  unfold separableDegreeWeightedFiberSum
  simp only [Pi.one_apply, one_mul]
  show (∑ᶠ x : X, if f x = y then (U : Set X).indicator (1 : X → ℤ) x * d x else 0) =
    ∑ᶠ x : U, if (U.ι ≫ f) x = y then
      (let := ((U.ι ≫ f).residueFieldMap x).hom.toAlgebra;
        (Field.finSepDegree (Y.residueField ((U.ι ≫ f) x))
          (U.toScheme.residueField x) : ℤ)) else 0
  simp_rw [hdegree]
  show _ = ∑ᶠ x : U, if f x.1 = y then d x.1 else 0
  rw [finsum_subtype_eq_finsum_cond (f := fun x : X ↦ if f x = y then d x else 0)
    (fun x ↦ x ∈ U)]
  simp only
  apply finsum_congr
  intro x
  by_cases hx : x ∈ U <;> by_cases hxy : f x = y <;>
    simp [Set.indicator, hx, hxy]

private lemma separableDegreeWeightedFiberSum_add
    {X Y : Scheme.{u}} (f : X ⟶ Y)
    (hfinite : ∀ y, (f ⁻¹' {y}).Finite) (w w' : X → ℤ) :
    separableDegreeWeightedFiberSum f (w + w') =
      separableDegreeWeightedFiberSum f w +
        separableDegreeWeightedFiberSum f w' := by
  classical
  funext y
  let d (x : X) : ℤ := by
    let := (f.residueFieldMap x).hom.toAlgebra
    exact (Field.finSepDegree (Y.residueField (f x)) (X.residueField x) : ℤ)
  have hs (v : X → ℤ) :
      Function.HasFiniteSupport (fun x ↦ if f x = y then v x * d x else 0) := by
    apply (hfinite y).subset
    intro x hx
    by_contra hxy
    simp only [Set.mem_preimage, Set.mem_singleton_iff] at hxy
    simp [hxy] at hx
  show (∑ᶠ x, if f x = y then (w x + w' x) * d x else 0) =
    (∑ᶠ x, if f x = y then w x * d x else 0) +
      ∑ᶠ x, if f x = y then w' x * d x else 0
  have heq (x : X) : (if f x = y then (w x + w' x) * d x else 0) =
      (if f x = y then w x * d x else 0) +
        (if f x = y then w' x * d x else 0) := by
    split_ifs <;> simp only [add_mul, add_zero]
  simp_rw [heq]
  exact finsum_add_distrib (hs w) (hs w')

private lemma finite_of_constructible_partition
    {Y J : Type*} [TopologicalSpace Y] [SpectralSpace Y]
    (E : J → Set Y) (hE : ∀ j, Topology.IsConstructible (E j))
    (hcover : ∀ y, ∃ j, y ∈ E j)
    (hdisjoint : ∀ j k y, y ∈ E j → y ∈ E k → j = k) :
    {j | (E j).Nonempty}.Finite := by
  classical
  let O : J → Set (WithConstructibleTopology Y) := fun j ↦
    WithTopology.ofTopology ⁻¹' E j
  have hO : ∀ j, IsOpen (O j) := by
    intro j
    apply WithConstructibleTopology.isOpen_iff.mpr
    show @IsOpen Y (constructibleTopology Y) (E j)
    rw [constructibleTopology_eq_generateFrom_isConstructible]
    exact TopologicalSpace.isOpen_generateFrom_of_mem (hE j)
  obtain ⟨t, ht⟩ := isCompact_univ.elim_finite_subcover O hO (by
    intro y _
    obtain ⟨j, hj⟩ := hcover (WithTopology.ofTopology y)
    exact Set.mem_iUnion.mpr ⟨j, hj⟩)
  refine t.finite_toSet.subset ?_
  rintro j ⟨y, hy⟩
  obtain ⟨k, hkt, hyk⟩ := Set.mem_iUnion₂.mp
    (ht (Set.mem_univ (WithTopology.toTopology (constructibleTopology Y) y)))
  simpa [hdisjoint j k y hy hyk] using hkt

private lemma finite_range_of_locallyConstructible_level_sets
    {X : Scheme.{u}} {A : Type*} [CompactSpace X] (w : X → A)
    (hlevels : ∀ n, Topology.IsLocallyConstructible {x | w x = n}) :
    (Set.range w).Finite := by
  classical
  let U : X.affineOpens → Set X := fun U ↦ U.1
  obtain ⟨s, hs⟩ := isCompact_univ.elim_finite_subcover U
      (fun U : X.affineOpens ↦ U.1.2) (by
    intro x _
    obtain ⟨_, ⟨V, hV, rfl⟩, hxV, -⟩ :=
      X.isBasis_affineOpens.exists_subset_of_mem_open (Set.mem_univ x) isOpen_univ
    exact Set.mem_iUnion.mpr ⟨⟨V, hV⟩, hxV⟩)
  have hfinite (U : X.affineOpens) :
      {n : A | ({x : U.1 | w x.1 = n}).Nonempty}.Finite := by
    let E : A → Set (U.1 : Set X) := fun n ↦ {x | w x.1 = n}
    let : SpectralSpace (U.1 : Set X) := spectralSpace_affineOpen U
    have hE : ∀ n, Topology.IsConstructible (E n) := fun n ↦ by
      simpa [E, Set.inter_comm] using
        (isLocallyConstructible_iff_forall_affineOpens {x : X | w x = n}).mp (hlevels n) U
    exact finite_of_constructible_partition E hE (fun x ↦ ⟨w x.1, rfl⟩)
      fun _ _ _ hn hm ↦ hn.symm.trans hm
  let V : X.affineOpens → Set A := fun U ↦
    {n | ({x : U.1 | w x.1 = n}).Nonempty}
  have hcoverValues : Set.range w ⊆ ⋃ U ∈ s, V U := by
    rintro n ⟨x, rfl⟩
    obtain ⟨U, hUs, hx⟩ := Set.mem_iUnion₂.mp (hs (Set.mem_univ x))
    exact Set.mem_iUnion₂.mpr ⟨U, hUs, ⟨⟨x, hx⟩, rfl⟩⟩
  exact (Set.Finite.biUnion s.finite_toSet fun U _ ↦ hfinite U).subset hcoverValues

lemma finite_range_of_weighting_level_sets
    {X Y : Scheme.{u}} (f : X ⟶ Y) [LocallyOfFiniteType f] [LocallyQuasiFinite f]
    [CompactSpace X] (w : X → ℤ) (hw : IsWeighting f w) :
    (Set.range w).Finite :=
  finite_range_of_locallyConstructible_level_sets w
    (isLocallyConstructible_weighting_levelSet hw)

private lemma finite_range_numGeometricConnectedComponents
    {X Y : Scheme.{u}} [CompactSpace Y] (f : X ⟶ Y)
    (hf : FinitePresentation f) :
    (Set.range (numGeometricConnectedComponents f)).Finite :=
  finite_range_of_locallyConstructible_level_sets _
    (isLocallyConstructible_numGeometricConnectedComponents f hf)

private lemma finite_range_isConstructible_of_finite_family
    {X A B C : Type*} [TopologicalSpace X] [Finite A]
    (f : A → X → B) (hfinite : ∀ a, (Set.range (f a)).Finite)
    (hlevels : ∀ a b, Topology.IsConstructible {x | f a x = b})
    (g : (A → B) → C) :
    (Set.range (fun x ↦ g (fun a ↦ f a x))).Finite ∧
      ∀ c, Topology.IsConstructible {x | g (fun a ↦ f a x) = c} := by
  classical
  let (a : A) : Finite (Set.range (f a)) := (hfinite a).to_subtype
  let P := ∀ a, Set.range (f a)
  let q : P → C := fun p ↦ g (fun a ↦ (p a).1)
  constructor
  · apply (Set.finite_range q).subset
    rintro c ⟨x, rfl⟩
    exact ⟨fun a ↦ ⟨f a x, Set.mem_range_self x⟩, rfl⟩
  · intro c
    have heq : {x | g (fun a ↦ f a x) = c} =
        ⋃ p : {p : P // q p = c}, ⋂ a, {x | f a x = (p.1 a).1} := by
      ext x
      simp only [Set.mem_ofPred_eq, Set.mem_iUnion, Set.mem_iInter]
      constructor
      · intro hx
        exact ⟨⟨fun a ↦ ⟨f a x, Set.mem_range_self x⟩, hx⟩, fun a ↦ rfl⟩
      · rintro ⟨p, hp⟩
        have h : (fun a ↦ f a x) = (fun a ↦ (p.1 a).1) := funext hp
        rw [h]
        exact p.2
    rw [heq]
    exact Topology.IsConstructible.iUnion fun p ↦
      Topology.IsConstructible.iInter fun a ↦ hlevels a (p.1 a).1

lemma isConstructible_levelSet_membershipFunction
    {X A B : Type*} [TopologicalSpace X] [Finite A]
    (E : A → Set X) (hE : ∀ a, Topology.IsConstructible (E a))
    (g : (A → Bool) → B) (b : B) :
    Topology.IsConstructible
      {x | g (fun a ↦ @decide (x ∈ E a) (Classical.propDecidable _)) = b} := by
  classical
  apply (finite_range_isConstructible_of_finite_family
    (fun a x ↦ decide (x ∈ E a)) (fun _ ↦ Set.toFinite _) ?_ g).2
  intro a p
  cases p
  · convert (hE a).compl using 1
    ext x
    simp only [Set.mem_ofPred_eq, Set.mem_compl_iff, decide_eq_false_iff_not]
  · convert hE a using 1
    ext x
    simp only [Set.mem_ofPred_eq, decide_eq_true_eq]

private lemma indicator_mem_span_open_retrocompact
    {X : Type*} [TopologicalSpace X] {E : Set X}
    (hE : Topology.IsConstructible E) :
    E.indicator (1 : X → ℤ) ∈ Submodule.span ℤ
      {f : X → ℤ | ∃ U : Set X, IsOpen U ∧ IsRetrocompact U ∧
        f = U.indicator 1} := by
  classical
  let S : Set (X → ℤ) :=
    {f | ∃ U : Set X, IsOpen U ∧ IsRetrocompact U ∧ f = U.indicator 1}
  let M := Submodule.span ℤ S
  have hmul {f g : X → ℤ} (hf : f ∈ M) (hg : g ∈ M) : f * g ∈ M := by
    induction hf, hg using Submodule.span_induction₂ with
    | mem_mem f g hf hg =>
      obtain ⟨U, hU, hUc, rfl⟩ := hf
      obtain ⟨V, hV, hVc, rfl⟩ := hg
      apply Submodule.subset_span
      refine ⟨U ∩ V, hU.inter hV, hUc.inter_isOpen hVc hV, ?_⟩
      funext x
      by_cases hxU : x ∈ U <;> by_cases hxV : x ∈ V <;>
        simp [Set.indicator, hxU, hxV]
    | zero_left g hg => simp
    | zero_right f hf => simp
    | add_left f g h hf hg hh hfh hgh =>
      simpa only [add_mul] using M.add_mem hfh hgh
    | add_right f g h hf hg hh hfg hfh =>
      simpa only [mul_add] using M.add_mem hfg hfh
    | smul_left a f g hf hg hfg =>
      simpa only [smul_mul_assoc] using M.smul_mem a hfg
    | smul_right a f g hf hg hfg =>
      simpa only [mul_smul_comm] using M.smul_mem a hfg
  have hOne : (1 : X → ℤ) ∈ M := by
    apply Submodule.subset_span
    exact ⟨Set.univ, isOpen_univ, IsRetrocompact.univ, by simp⟩
  show E.indicator 1 ∈ M
  induction hE using Topology.IsConstructible.empty_union_induction with
  | open_retrocompact U hU hUc =>
    exact Submodule.subset_span ⟨U, hU, hUc, rfl⟩
  | union U hU V hV ihU ihV =>
    have heq : (U ∪ V).indicator (1 : X → ℤ) =
        U.indicator 1 + V.indicator 1 - U.indicator 1 * V.indicator 1 := by
      funext x
      by_cases hxU : x ∈ U <;> by_cases hxV : x ∈ V <;>
        simp [Set.indicator, hxU, hxV]
    rw [heq]
    exact M.sub_mem (M.add_mem ihU ihV) (hmul ihU ihV)
  | compl U hU ihU =>
    have heq : Uᶜ.indicator (1 : X → ℤ) = 1 - U.indicator 1 := by
      funext x
      by_cases hx : x ∈ U <;> simp [Set.indicator, hx]
    rw [heq]
    exact M.sub_mem hOne ihU

private lemma mem_span_open_retrocompact_of_constructible_levels
    {X : Type*} [TopologicalSpace X] (f : X → ℤ)
    (hfinite : (Set.range f).Finite)
    (hlevels : ∀ n, Topology.IsConstructible {x | f x = n}) :
    f ∈ Submodule.span ℤ
      {g : X → ℤ | ∃ U : Set X, IsOpen U ∧ IsRetrocompact U ∧
        g = U.indicator 1} := by
  classical
  have heq : f = ∑ n ∈ hfinite.toFinset, n • ({x | f x = n}.indicator (1 : X → ℤ)) := by
    funext x
    simp only [Finset.sum_apply, Pi.smul_apply, smul_eq_mul]
    rw [Finset.sum_eq_single (f x)]
    · simp
    · intro n hn hnx
      simp [Set.indicator, Ne.symm hnx]
    · intro hx
      exact (hx (hfinite.mem_toFinset.mpr (Set.mem_range_self x))).elim
  rw [heq]
  exact Submodule.sum_mem _ fun n hn ↦
    Submodule.smul_mem _ n (indicator_mem_span_open_retrocompact (hlevels n))

private lemma separableDegreeWeightedFiberSum_smul
    {X Y : Scheme.{u}} (f : X ⟶ Y) (a : ℤ) (w : X → ℤ) :
    separableDegreeWeightedFiberSum f (a • w) =
      a • separableDegreeWeightedFiberSum f w := by
  classical
  funext y
  simp only [separableDegreeWeightedFiberSum, Pi.smul_apply, smul_eq_mul,
    mul_finsum]
  apply finsum_congr
  intro x
  split_ifs <;> simp [mul_assoc]

private lemma constructible_integral_of_constructible_levels
    {X Y : Scheme.{u}} [CompactSpace Y] [QuasiSeparatedSpace Y]
    (f : X ⟶ Y) [LocallyQuasiFinite f] (hf : FinitePresentation f)
    (w : X → ℤ) (hfinite : (Set.range w).Finite)
    (hlevels : ∀ n, Topology.IsConstructible {x | w x = n}) :
    (Set.range (separableDegreeWeightedFiberSum f w)).Finite ∧
      ∀ n, Topology.IsConstructible
        {y | separableDegreeWeightedFiberSum f w y = n} := by
  classical
  let : LocallyOfFinitePresentation f := hf.1
  let : QuasiCompact f := hf.2.1
  let : QuasiSeparated f := hf.2.2
  let H (v : Y → ℤ) : Prop := (Set.range v).Finite ∧
    ∀ n, Topology.IsConstructible {y | v y = n}
  have hmap {A : Type} (v : Y → A) (hv : (Set.range v).Finite)
      (hlev : ∀ a, Topology.IsConstructible {y | v y = a}) (g : A → ℤ) :
      H (g ∘ v) :=
    finite_range_isConstructible_of_finite_family (fun _ : Unit ↦ v)
      (fun _ ↦ hv) (fun _ ↦ hlev) (fun p ↦ g (p ()))
  have hadd {v v' : Y → ℤ} (hv : H v) (hv' : H v') : H (v + v') := by
    let F : Bool → Y → ℤ := fun b ↦ if b then v else v'
    have hfin : ∀ b, (Set.range (F b)).Finite
      | false => hv'.1
      | true => hv.1
    have hlev : ∀ b n, Topology.IsConstructible {y | F b y = n}
      | false, n => hv'.2 n
      | true, n => hv.2 n
    exact finite_range_isConstructible_of_finite_family F hfin hlev
      (fun p ↦ p true + p false)
  have hsmul {v : Y → ℤ} (a : ℤ) (hv : H v) : H (a • v) :=
    hmap v hv.1 hv.2 (fun n ↦ a * n)
  have hzero : H 0 := by
    refine ⟨Set.finite_range_const, fun n ↦ ?_⟩
    by_cases hn : (0 : ℤ) = n
    · simp [hn]
    · simp [hn]
  have hopen (U : Set X) (hU : IsOpen U) (hUc : IsRetrocompact U) :
      H (separableDegreeWeightedFiberSum f (U.indicator 1)) := by
    let V : X.Opens := ⟨U, hU⟩
    have : QuasiCompact V.ι := quasiCompact_iff_isSpectralMap.mpr
      (IsRetrocompact_iff_isSpectralMap_subtypeVal.mp hUc)
    have hV : FinitePresentation (V.ι ≫ f) :=
      ⟨inferInstance, inferInstance, inferInstance⟩
    show H (separableDegreeWeightedFiberSum f ((V : Set X).indicator 1))
    rw [separableDegreeWeightedFiberSum_indicator_open f V]
    have h := hmap (numGeometricConnectedComponents (V.ι ≫ f))
      (finite_range_numGeometricConnectedComponents _ hV)
      (fun n ↦ (isLocallyConstructible_numGeometricConnectedComponents
        (V.ι ≫ f) hV n).isConstructible) (fun n ↦ (n.toNat : ℤ))
    convert h using 1
    funext y
    exact separableDegreeWeightedFiberSum_one_eq_components _ y
  have hspan := mem_span_open_retrocompact_of_constructible_levels w hfinite hlevels
  show H (separableDegreeWeightedFiberSum f w)
  clear hfinite hlevels
  induction hspan using Submodule.span_induction with
  | mem v hv =>
    obtain ⟨U, hU, hUc, rfl⟩ := hv
    exact hopen U hU hUc
  | zero =>
    convert hzero using 1
    funext y
    simp [separableDegreeWeightedFiberSum]
  | add v v' hv hv' ih ih' =>
    rw [separableDegreeWeightedFiberSum_add f (fun y ↦ f.finite_preimage_singleton y)]
    exact hadd ih ih'
  | smul a v hv ih =>
    rw [separableDegreeWeightedFiberSum_smul]
    exact hsmul a ih

lemma constructible_finiteOpen_integral
    {X Y V : Scheme.{u}} [CompactSpace V] [QuasiSeparatedSpace V]
    (f : X ⟶ Y) [LocallyOfFinitePresentation f] (g : V ⟶ Y)
    (U : (pullback f g).Opens) [IsFinite (U.ι ≫ pullback.snd f g)]
    (w : X → ℤ) (hfinite : (Set.range w).Finite)
    (hlevels : ∀ n, Topology.IsConstructible {x | w x = n}) :
    (Set.range (separableDegreeWeightedFiberSum
      (U.ι ≫ pullback.snd f g) (w ∘ (U.ι ≫ pullback.fst f g)))).Finite ∧
      ∀ n, Topology.IsConstructible
        {v | separableDegreeWeightedFiberSum
          (U.ι ≫ pullback.snd f g) (w ∘ (U.ι ≫ pullback.fst f g)) v = n} := by
  apply constructible_integral_of_constructible_levels
    (U.ι ≫ pullback.snd f g) ⟨inferInstance, inferInstance, inferInstance⟩
  · exact hfinite.subset (Set.range_comp_subset_range _ _)
  · intro n
    exact (U.ι ≫ pullback.fst f g).isConstructible_preimage (hlevels n)

end AlgebraicGeometry
