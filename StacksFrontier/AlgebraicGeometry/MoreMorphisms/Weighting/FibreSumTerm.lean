module

public import Mathlib.AlgebraicGeometry.Morphisms.QuasiFinite
public import Mathlib.FieldTheory.SeparableClosure
public import StacksFrontier.AlgebraicGeometry.MoreMorphisms.FiniteOverSmooth.ResidueFieldMap
public import StacksFrontier.AlgebraicGeometry.Morphisms.QuasiFinite.SpecializationLift
public import StacksFrontier.AlgebraicGeometry.Morphisms.WeaklyEtale.WeightedFibreSum
public import StacksFrontier.Topology.Separation.IsolatedPoint
public import StacksCore.Tactic.StacksAttribute

/-!
# The individual terms of a separable-degree weighted fibre sum

The separable-degree weighted fibre sum of `w : X → ℤ` along `f : X ⟶ Y` is an unconditional
sum over `X` of terms which vanish away from one fibre. This file isolates that term as a
function of its own, computes it along an open immersion, and derives the consequences that
are used over and over when a weighted fibre sum is split along an open decomposition of the
source or evaluated on a single-point fibre.

## Main definitions

* `AlgebraicGeometry.separableDegreeWeightedFiberTerm` is the summand of
  `AlgebraicGeometry.separableDegreeWeightedFiberSum` at a point of the source.

## Main results

* `AlgebraicGeometry.separableDegreeWeightedFiberTerm_comp_isPreimmersion`: the term is
  unchanged by restricting the source along a preimmersion.
* `AlgebraicGeometry.separableDegreeWeightedFiberSum_eq_sum_opens` and
  `AlgebraicGeometry.separableDegreeWeightedFiberSum_eq_sum_opens_of_hasFiniteSupport`: the
  weighted fibre sum of a morphism is the sum of the weighted fibre sums of its restrictions to
  a finite family of pairwise disjoint opens covering the source.
* `AlgebraicGeometry.separableDegreeWeightedFiberSum_eq_finsum_fiber` and
  `AlgebraicGeometry.separableDegreeWeightedFiberSum_eq_finsum_preimage` describe the weighted
  fibre sum as a sum indexed by the fibre.
* `AlgebraicGeometry.separableDegreeWeightedFiberSum_eq_of_fiber_singleton`: on a fibre reduced
  to one point with purely inseparable residue extension the weighted fibre sum is the weight
  of that point.
* `AlgebraicGeometry.separableDegreeWeightedFiberSum_eq_zero_of_fiber_eq_empty`: the weighted
  fibre sum vanishes over a point with empty fibre.
* `AlgebraicGeometry.separableDegreeWeightedFiberSum_nonneg`,
  `AlgebraicGeometry.le_separableDegreeWeightedFiberSum` and
  `AlgebraicGeometry.separableDegreeWeightedFiberSum_pos` bound the weighted fibre sum of a
  positive weight below.
* `AlgebraicGeometry.module_finite_residueFieldMap` and
  `AlgebraicGeometry.finSepDegree_residueFieldMap_pos`: the residue-field extension at a point of
  a locally quasi-finite morphism is finite, hence has positive separable degree.

## Implementation notes

The weight of a point is multiplied by the separable degree of its residue field over that of
its image, so the algebra structure used throughout is the one induced by the morphism. The
identity along a preimmersion needs the separable degree to be transported along the
induced isomorphism of residue fields; this is done by a pair of auxiliary lemmas comparing
separable degrees along compatible ring equivalences of the base and the top field.

## References

* [Stacks Project, Tag 0F39](https://stacks.math.columbia.edu/tag/0F39)
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits

universe u

namespace AlgebraicGeometry

/-- The separable degree of a field extension is unchanged when the base field is replaced by an
isomorphic one with a compatible structure map. -/
private lemma finSepDegree_eq_of_baseEquiv
    (F G E : Type*) [Field F] [Field G] [Field E]
    [Algebra F E] [Algebra G E] (e : F ≃+* G)
    (h : ∀ a : F, algebraMap F E a = algebraMap G E (e a)) :
    Field.finSepDegree F E = Field.finSepDegree G E := by
  have hcl (a : F) : algebraMap F (AlgebraicClosure E) a =
      algebraMap G (AlgebraicClosure E) (e a) := by
    change algebraMap E (AlgebraicClosure E) (algebraMap F E a) =
      algebraMap E (AlgebraicClosure E) (algebraMap G E (e a))
    exact congrArg (algebraMap E (AlgebraicClosure E)) (h a)
  let forward (φ : Field.Emb F E) : Field.Emb G E :=
    AlgHom.mk φ.toRingHom (by
      intro b
      let a := e.symm b
      calc
        φ (algebraMap G E b) = φ (algebraMap F E a) := by rw [h a, e.apply_symm_apply]
        _ = algebraMap F (AlgebraicClosure E) a := φ.commutes' a
        _ = algebraMap G (AlgebraicClosure E) b := by rw [hcl a, e.apply_symm_apply])
  let backward (ψ : Field.Emb G E) : Field.Emb F E :=
    AlgHom.mk ψ.toRingHom (by
      intro a
      calc
        ψ (algebraMap F E a) = ψ (algebraMap G E (e a)) := by rw [h a]
        _ = algebraMap G (AlgebraicClosure E) (e a) := ψ.commutes' (e a)
        _ = algebraMap F (AlgebraicClosure E) a := by rw [hcl a])
  let equiv : Field.Emb F E ≃ Field.Emb G E :=
    { toFun := forward
      invFun := backward
      left_inv := by intro φ; apply AlgHom.ext; intro x; rfl
      right_inv := by intro ψ; apply AlgHom.ext; intro x; rfl }
  exact Nat.card_congr equiv

/-- Two field extensions related by compatible ring isomorphisms of the base and of the top
field have the same separable degree. -/
private lemma finSepDegree_eq_of_compatible_fieldEquiv
    {F G E K : Type*} [Field F] [Field G] [Field E] [Field K]
    [Algebra F E] [Algebra G K]
    (eF : F ≃+* G) (eE : E ≃+* K)
    (hcompat : ∀ a : F, eE (algebraMap F E a) = algebraMap G K (eF a)) :
    Field.finSepDegree F E = Field.finSepDegree G K := by
  let : Algebra F K := ((algebraMap G K).comp eF.toRingHom).toAlgebra
  have hcompat' : ∀ a : F, eE (algebraMap F E a) = algebraMap F K a := hcompat
  exact (Field.finSepDegree_eq_of_equiv F E K (AlgEquiv.ofRingEquiv (f := eE) hcompat')).trans
    (finSepDegree_eq_of_baseEquiv F G K eF fun _ => rfl)

/-- Precomposing with a preimmersion does not change the separable degree of the
residue-field extension at a point. -/
private lemma finSepDegree_residueFieldMap_comp_isPreimmersion
    {X Y Z : Scheme.{u}} (i : Z ⟶ X) (g : X ⟶ Y) [IsPreimmersion i] (z : Z) :
    letI := ((i ≫ g).residueFieldMap z).hom.toAlgebra
    letI := (g.residueFieldMap (i z)).hom.toAlgebra
    Field.finSepDegree (Y.residueField ((i ≫ g) z)) (Z.residueField z) =
      Field.finSepDegree (Y.residueField (g (i z))) (X.residueField (i z)) := by
  let : Algebra (Y.residueField ((i ≫ g) z)) (Z.residueField z) :=
    ((i ≫ g).residueFieldMap z).hom.toAlgebra
  let : Algebra (Y.residueField (g (i z))) (X.residueField (i z)) :=
    (g.residueFieldMap (i z)).hom.toAlgebra
  let e' : X.residueField (i z) ≃+* Z.residueField z :=
    RingEquiv.ofBijective (i.residueFieldMap z).hom ((ConcreteCategory.isIso_iff_bijective _).mp
      (isIso_residueFieldMap_of_isPreimmersion i z))
  refine finSepDegree_eq_of_compatible_fieldEquiv (RingEquiv.refl _) e'.symm fun a => ?_
  change e'.symm (((i ≫ g).residueFieldMap z).hom a) = (g.residueFieldMap (i z)).hom a
  rw [Scheme.residueFieldMap_comp]
  exact e'.symm_apply_apply _

/-- The summand of `AlgebraicGeometry.separableDegreeWeightedFiberSum` at a point `x` of the
source: the weight at `x` times the separable degree of the residue-field extension at `x`
when `x` lies in the fibre over `y`, and zero otherwise. -/
noncomputable def separableDegreeWeightedFiberTerm
    {X Y : Scheme.{u}} (f : X ⟶ Y) (w : X → ℤ) (y : Y) (x : X) : ℤ := by
  classical
  exact if f x = y then
      letI := (f.residueFieldMap x).hom.toAlgebra
      w x * (Field.finSepDegree (Y.residueField (f x)) (X.residueField x) : ℤ)
    else 0

/-- At a point of the fibre the term of a weighted fibre sum is the weight times the separable
degree of the residue-field extension. -/
lemma separableDegreeWeightedFiberTerm_of_mem_fiber
    {X Y : Scheme.{u}} (f : X ⟶ Y) (w : X → ℤ) {y : Y} {x : X} (hxy : f x = y) :
    separableDegreeWeightedFiberTerm f w y x =
      letI := (f.residueFieldMap x).hom.toAlgebra
      w x * (Field.finSepDegree (Y.residueField (f x)) (X.residueField x) : ℤ) :=
  ite_eq_left hxy

/-- Off the fibre the term of a weighted fibre sum vanishes. -/
lemma separableDegreeWeightedFiberTerm_of_notMem_fiber
    {X Y : Scheme.{u}} (f : X ⟶ Y) (w : X → ℤ) {y : Y} {x : X} (hxy : f x ≠ y) :
    separableDegreeWeightedFiberTerm f w y x = 0 :=
  ite_eq_right hxy

/-- The weighted fibre sum is the unconditional sum of its terms. -/
lemma separableDegreeWeightedFiberSum_eq_finsum_term
    {X Y : Scheme.{u}} (f : X ⟶ Y) (w : X → ℤ) (y : Y) :
    separableDegreeWeightedFiberSum f w y = ∑ᶠ x : X, separableDegreeWeightedFiberTerm f w y x :=
  rfl

/-- The term of a weighted fibre sum is unchanged by restricting the source along a
preimmersion — in particular along an open or a closed immersion. -/
lemma separableDegreeWeightedFiberTerm_comp_isPreimmersion
    {X Y Z : Scheme.{u}} (i : Z ⟶ X) (g : X ⟶ Y) [IsPreimmersion i]
    (w : X → ℤ) (y : Y) (z : Z) :
    separableDegreeWeightedFiberTerm (i ≫ g) (w ∘ i) y z =
      separableDegreeWeightedFiberTerm g w y (i z) := by
  by_cases h : g (i z) = y
  · subst y
    have hp := Scheme.Hom.comp_apply i g z
    cases hp
    simp only [separableDegreeWeightedFiberTerm, Function.comp_apply, Scheme.Hom.comp_apply,
      reduceIte]
    rw [finSepDegree_residueFieldMap_comp_isPreimmersion i g z]
  · rw [separableDegreeWeightedFiberTerm_of_notMem_fiber g w h,
      separableDegreeWeightedFiberTerm_of_notMem_fiber (i ≫ g) (w ∘ i)
        (by simpa only [Scheme.Hom.comp_apply] using h)]

/-- Summing the terms of a weighted fibre sum over an open subscheme gives the weighted fibre
sum of the restriction to that open subscheme. -/
lemma finsum_mem_separableDegreeWeightedFiberTerm
    {P U : Scheme.{u}} (g : P ⟶ U) (D : P.Opens) (w : P → ℤ) (u : U) :
    (∑ᶠ x ∈ (D : Set P), separableDegreeWeightedFiberTerm g w u x) =
      separableDegreeWeightedFiberSum (D.ι ≫ g) (w ∘ D.ι) u := by
  classical
  rw [← finsum_set_coe_eq_finsum_mem (D : Set P)]
  unfold separableDegreeWeightedFiberSum
  exact finsum_congr fun x =>
    (separableDegreeWeightedFiberTerm_comp_isPreimmersion D.ι g w u x).symm

/-- The terms of a weighted fibre sum are supported on the fibre, hence have finite support as
soon as the fibre is finite. -/
lemma separableDegreeWeightedFiberTerm_hasFiniteSupport
    {X Y : Scheme.{u}} (f : X ⟶ Y) (w : X → ℤ) (y : Y) (hfinite : (f ⁻¹' {y}).Finite) :
    Function.HasFiniteSupport (separableDegreeWeightedFiberTerm f w y) := by
  classical
  change (Function.support (separableDegreeWeightedFiberTerm f w y)).Finite
  apply hfinite.subset
  intro x hx
  by_contra hnot
  have hxy : f x ≠ y := fun hxy => hnot (by simp [hxy])
  exact hx (by simp [separableDegreeWeightedFiberTerm, hxy])

/-- A function with finite support is the sum of its restrictions to a finite family of
pairwise disjoint sets covering its support. -/
private lemma finsum_eq_sum_finsum_mem
    {α ι G : Type*} [Fintype ι] [AddCommGroup G]
    (D : ι → Set α) (F : α → G) (hF : Function.HasFiniteSupport F)
    (hdisj : ∀ i j, i ≠ j → Disjoint (D i) (D j))
    (hcover : ∀ x, F x ≠ 0 → ∃ i, x ∈ D i) :
    (∑ i, ∑ᶠ x ∈ D i, F x) = ∑ᶠ x, F x := by
  classical
  change (Function.support F).Finite at hF
  let s := hF.toFinset
  have hsupport (i : ι) : Function.support ((D i).indicator F) ⊆ (s : Set α) :=
    fun x hx => hF.mem_toFinset.mpr fun hz => hx (by simp [Set.indicator, hz])
  have hFsupport : Function.support F ⊆ (s : Set α) :=
    fun x hx => hF.mem_toFinset.mpr hx
  have hpoint (x : α) : (∑ i, (D i).indicator F x) = F x := by
    by_cases hxF : F x = 0
    · simp [hxF, Set.indicator_apply]
    · obtain ⟨i, hi⟩ := hcover x hxF
      have honly : ∀ j, j ≠ i → x ∉ D j := fun j hji =>
        Set.disjoint_left.mp (hdisj i j hji.symm) hi
      rw [Finset.sum_eq_single i]
      · simp [hi]
      · intro j hj hji
        simp [honly j hji]
      · exact fun hi' => (hi' (Finset.mem_univ i)).elim
  calc
    (∑ i, ∑ᶠ x ∈ D i, F x) = ∑ i, ∑ᶠ x, (D i).indicator F x :=
      Finset.sum_congr rfl fun i _ => finsum_mem_def (D i) F
    _ = ∑ i, ∑ x ∈ s, (D i).indicator F x :=
      Finset.sum_congr rfl fun i _ => finsum_eq_sum_of_support_subset _ (hsupport i)
    _ = ∑ x ∈ s, ∑ i, (D i).indicator F x := Finset.sum_comm
    _ = ∑ x ∈ s, F x := by simp_rw [hpoint]
    _ = ∑ᶠ x, F x := (finsum_eq_sum_of_support_subset F hFsupport).symm

/-- The weighted fibre sum of a morphism is the sum of the weighted fibre sums of its
restrictions to a finite family of pairwise disjoint opens covering the source, provided the
terms of the sum have finite support. -/
lemma separableDegreeWeightedFiberSum_eq_sum_opens_of_hasFiniteSupport
    {P U : Scheme.{u}} {ι : Type*} [Fintype ι]
    (π : P ⟶ U) (w : P → ℤ) (D : ι → P.Opens)
    (hdisj : ∀ i j, i ≠ j → Disjoint (D i : Set P) (D j : Set P))
    (hcover : ∀ x : P, ∃ i, x ∈ D i)
    (hsupport : ∀ u, Function.HasFiniteSupport (separableDegreeWeightedFiberTerm π w u)) :
    separableDegreeWeightedFiberSum π w =
      ∑ i, separableDegreeWeightedFiberSum ((D i).ι ≫ π) (w ∘ (D i).ι) := by
  classical
  funext u
  have hpartition := finsum_eq_sum_finsum_mem
    (fun i ↦ (D i : Set P)) (separableDegreeWeightedFiberTerm π w u)
    (hsupport u) hdisj (fun x _ ↦ hcover x)
  rw [Finset.sum_apply, separableDegreeWeightedFiberSum_eq_finsum_term, ← hpartition]
  exact Finset.sum_congr rfl fun i _ => finsum_mem_separableDegreeWeightedFiberTerm π (D i) w u

/-- The weighted fibre sum of a morphism with finite fibres is the sum of the weighted fibre
sums of its restrictions to a finite family of pairwise disjoint opens covering the source. -/
lemma separableDegreeWeightedFiberSum_eq_sum_opens
    {P U : Scheme.{u}} {ι : Type*} [Fintype ι]
    (π : P ⟶ U) (w : P → ℤ) (D : ι → P.Opens)
    (hdisj : ∀ i j, i ≠ j → Disjoint (D i : Set P) (D j : Set P))
    (hcover : ∀ x : P, ∃ i, x ∈ D i)
    (hfinite : ∀ u, (π ⁻¹' {u}).Finite) :
    separableDegreeWeightedFiberSum π w =
      ∑ i, separableDegreeWeightedFiberSum ((D i).ι ≫ π) (w ∘ (D i).ι) :=
  separableDegreeWeightedFiberSum_eq_sum_opens_of_hasFiniteSupport π w D hdisj hcover
    fun u ↦ separableDegreeWeightedFiberTerm_hasFiniteSupport π w u (hfinite u)

/-- A sum over the source with the terms outside a subtype discarded is the sum over that
subtype. -/
private lemma finsum_dite_eq_finsum_subtype {α : Type*} (p : α → Prop) [DecidablePred p]
    (F : Subtype p → ℤ) :
    (∑ᶠ x : α, if h : p x then F ⟨x, h⟩ else 0) = ∑ᶠ y : Subtype p, F y := by
  classical
  let G : α → ℤ := fun x => if h : p x then F ⟨x, h⟩ else 0
  calc
    (∑ᶠ x : α, G x) = ∑ᶠ i : α, ∑ᶠ _ : p i, G i := by
      apply finsum_congr
      intro i
      by_cases h : p i <;> simp [G, h]
    _ = ∑ᶠ y : Subtype p, G y :=
      (finsum_subtype_eq_finsum_cond (p := p) (f := G)).symm
    _ = ∑ᶠ y : Subtype p, F y := by
      apply finsum_congr
      intro y
      simp [G, y.property]

/-- Reindexing a sum over a fibre between its two descriptions. -/
private lemma finsum_preimage_singleton_eq {α β : Type*}
    (f : α → β) (y : β) (F : α → ℤ) :
    (∑ᶠ x : {x : α // x ∈ f ⁻¹' {y}}, F x.1) =
      ∑ᶠ x : {x : α // f x = y}, F x.1 := by
  let e : {x : α // x ∈ f ⁻¹' {y}} ≃ {x : α // f x = y} :=
    { toFun := fun x => ⟨x.1, by
        simpa only [Set.mem_preimage, Set.mem_singleton_iff] using x.2⟩
      invFun := fun x => ⟨x.1, by
        simpa only [Set.mem_preimage, Set.mem_singleton_iff] using x.2⟩
      left_inv := by intro x; cases x; simp
      right_inv := by intro x; cases x; simp }
  simpa [e] using (finsum_comp_equiv e (f := fun x => F x.1))

/-- The weighted fibre sum, written as a sum indexed by the fibre. -/
lemma separableDegreeWeightedFiberSum_eq_finsum_fiber
    {X Y : Scheme.{u}} (f : X ⟶ Y) (w : X → ℤ) (y : Y) :
    separableDegreeWeightedFiberSum f w y =
      ∑ᶠ x : {x : X // f x = y},
        letI := (f.residueFieldMap x.1).hom.toAlgebra
        w x.1 * (Field.finSepDegree (Y.residueField (f x.1)) (X.residueField x.1) : ℤ) := by
  classical
  let F : {x : X // f x = y} → ℤ := fun x => by
    let := (f.residueFieldMap x.1).hom.toAlgebra
    exact w x.1 * (Field.finSepDegree (Y.residueField (f x.1)) (X.residueField x.1) : ℤ)
  unfold separableDegreeWeightedFiberSum
  calc
    (∑ᶠ u : X, if f u = y then
      let := (f.residueFieldMap u).hom.toAlgebra
      w u * (Field.finSepDegree (Y.residueField (f u)) (X.residueField u) : ℤ) else 0) =
        (∑ᶠ u : X, if h : f u = y then F ⟨u, h⟩ else 0) := by
          apply finsum_congr
          intro u
          split_ifs with h <;> rfl
    _ = ∑ᶠ x : {x : X // f x = y}, F x :=
      finsum_dite_eq_finsum_subtype (p := fun x : X => f x = y) F
    _ = _ := rfl

/-- The weighted fibre sum, written as a sum indexed by the preimage of a point. -/
lemma separableDegreeWeightedFiberSum_eq_finsum_preimage
    {X Y : Scheme.{u}} (f : X ⟶ Y) (w : X → ℤ) (y : Y) :
    separableDegreeWeightedFiberSum f w y =
      ∑ᶠ x : {x : X // x ∈ f ⁻¹' {y}},
        letI := (f.residueFieldMap x.1).hom.toAlgebra
        w x.1 * (Field.finSepDegree (Y.residueField (f x.1)) (X.residueField x.1) : ℤ) := by
  calc
    _ = ∑ᶠ x : {x : X // f x = y},
        let := (f.residueFieldMap x.1).hom.toAlgebra
        w x.1 * (Field.finSepDegree (Y.residueField (f x.1)) (X.residueField x.1) : ℤ) :=
      separableDegreeWeightedFiberSum_eq_finsum_fiber f w y
    _ = _ := (finsum_preimage_singleton_eq f y (fun x ↦ by
        let := (f.residueFieldMap x).hom.toAlgebra
        exact w x * (Field.finSepDegree (Y.residueField (f x)) (X.residueField x) : ℤ))).symm

/-- On a fibre consisting of a single point with purely inseparable residue-field extension the
weighted fibre sum is the weight of that point. -/
lemma separableDegreeWeightedFiberSum_eq_of_fiber_singleton
    {X Y : Scheme.{u}} (g : X ⟶ Y) (w : X → ℤ) (y : Y) (x : X)
    (hfiber : g ⁻¹' ({y} : Set Y) = {x}) (hxy : g x = y)
    (hpure : ((Y.residueFieldCongr hxy).inv ≫ g.residueFieldMap x).hom.IsPurelyInseparable) :
    separableDegreeWeightedFiberSum g w y = w x := by
  classical
  rw [separableDegreeWeightedFiberSum_eq_finsum_term,
    finsum_eq_single _ x fun z hzx ↦ separableDegreeWeightedFiberTerm_of_notMem_fiber g w fun hzy ↦
      hzx (by simpa [hfiber] using show z ∈ g ⁻¹' ({y} : Set Y) from hzy),
    separableDegreeWeightedFiberTerm_of_mem_fiber g w hxy]
  let : Algebra (Y.residueField (g x)) (X.residueField x) :=
    (g.residueFieldMap x).hom.toAlgebra
  have hdegree : Field.finSepDegree (Y.residueField (g x)) (X.residueField x) = 1 := by
    subst y
    exact hpure.finSepDegree_eq_one
  simp [hdegree]

/-- The weighted fibre sum over a point with empty fibre vanishes. -/
lemma separableDegreeWeightedFiberSum_eq_zero_of_fiber_eq_empty
    {X Y : Scheme.{u}} (f : X ⟶ Y) (w : X → ℤ) (y : Y) (hempty : f ⁻¹' {y} = ∅) :
    separableDegreeWeightedFiberSum f w y = 0 := by
  rw [separableDegreeWeightedFiberSum_eq_finsum_term]
  exact finsum_eq_zero_of_forall_eq_zero fun x ↦
    separableDegreeWeightedFiberTerm_of_notMem_fiber f w fun hx ↦ by
      have hmem : x ∈ f ⁻¹' {y} := hx
      rw [hempty] at hmem
      cases hmem

/-- The residue-field extension at a point of a locally quasi-finite morphism is finite. -/
alias module_finite_residueFieldMap := residueField_finite_of_locallyQuasiFinite

/-- The residue-field extension at a point of a locally quasi-finite morphism has positive
separable degree. -/
lemma finSepDegree_residueFieldMap_pos
    {X Y : Scheme.{u}} (f : X ⟶ Y) [LocallyQuasiFinite f] (x : X) :
    letI := (f.residueFieldMap x).hom.toAlgebra
    0 < Field.finSepDegree (Y.residueField (f x)) (X.residueField x) := by
  let : Algebra (Y.residueField (f x)) (X.residueField x) :=
    (f.residueFieldMap x).hom.toAlgebra
  have : Module.Finite (Y.residueField (f x)) (X.residueField x) :=
    module_finite_residueFieldMap f x
  exact Nat.pos_of_ne_zero (NeZero.ne _)

/-- Each term of the weighted fibre sum of a nonnegative weight is nonnegative. -/
lemma separableDegreeWeightedFiberTerm_nonneg
    {X Y : Scheme.{u}} (f : X ⟶ Y) (w : X → ℤ) (y : Y) (x : X) (hw : ∀ x, 0 ≤ w x) :
    0 ≤ separableDegreeWeightedFiberTerm f w y x := by
  classical
  by_cases h : f x = y
  · rw [separableDegreeWeightedFiberTerm_of_mem_fiber f w h]
    let : Algebra (Y.residueField (f x)) (X.residueField x) :=
      (f.residueFieldMap x).hom.toAlgebra
    exact mul_nonneg (hw x) (Int.natCast_nonneg _)
  · rw [separableDegreeWeightedFiberTerm_of_notMem_fiber f w h]

/-- The weighted fibre sum of a nonnegative weight is nonnegative. -/
lemma separableDegreeWeightedFiberSum_nonneg
    {X Y : Scheme.{u}} (f : X ⟶ Y) (w : X → ℤ) (hw : ∀ x, 0 ≤ w x) (y : Y) :
    0 ≤ separableDegreeWeightedFiberSum f w y := by
  rw [separableDegreeWeightedFiberSum_eq_finsum_term]
  exact finsum_nonneg fun x ↦ separableDegreeWeightedFiberTerm_nonneg f w y x hw

/-- At a point of the fibre, the term of the weighted fibre sum of a positive weight along a
locally quasi-finite morphism is positive. -/
lemma separableDegreeWeightedFiberTerm_pos
    {X Y : Scheme.{u}} (f : X ⟶ Y) [LocallyQuasiFinite f]
    (w : X → ℤ) (y : Y) (x : X) (hxy : f x = y) (hpos : ∀ x, 0 < w x) :
    0 < separableDegreeWeightedFiberTerm f w y x := by
  classical
  rw [separableDegreeWeightedFiberTerm_of_mem_fiber f w hxy]
  let : Algebra (Y.residueField (f x)) (X.residueField x) :=
    (f.residueFieldMap x).hom.toAlgebra
  exact mul_pos (hpos x) (Int.natCast_pos.mpr (finSepDegree_residueFieldMap_pos f x))

/-- The weighted fibre sum of a positive weight along a locally quasi-finite morphism with
finite fibres is at least the weight of any point of the fibre. -/
lemma le_separableDegreeWeightedFiberSum
    {X Y : Scheme.{u}} (g : X ⟶ Y) [LocallyQuasiFinite g]
    (w : X → ℤ) (y : Y) (x : X) (hx : g x = y)
    (hfinite : (g ⁻¹' ({y} : Set Y)).Finite) (hpos : ∀ x, 0 < w x) :
    w x ≤ separableDegreeWeightedFiberSum g w y := by
  classical
  rw [separableDegreeWeightedFiberSum_eq_finsum_term]
  refine le_trans ?_ (single_le_finsum x
    (separableDegreeWeightedFiberTerm_hasFiniteSupport g w y hfinite)
    fun z ↦ separableDegreeWeightedFiberTerm_nonneg g w y z fun z ↦ (hpos z).le)
  rw [separableDegreeWeightedFiberTerm_of_mem_fiber g w hx]
  let : Algebra (Y.residueField (g x)) (X.residueField x) :=
    (g.residueFieldMap x).hom.toAlgebra
  have hd : 1 ≤ (Field.finSepDegree (Y.residueField (g x)) (X.residueField x) : ℤ) := by
    exact_mod_cast Nat.succ_le_of_lt (finSepDegree_residueFieldMap_pos g x)
  simpa only [mul_one] using Int.mul_le_mul_of_nonneg_left hd (le_of_lt (hpos x))

/-- The weighted fibre sum of a positive weight along a locally quasi-finite morphism with
finite fibres is positive over every point of the image. -/
lemma separableDegreeWeightedFiberSum_pos
    {X Y : Scheme.{u}} (f : X ⟶ Y) [LocallyQuasiFinite f]
    (hfinite : ∀ y, (f ⁻¹' {y}).Finite) (w : X → ℤ)
    (hpos : ∀ x, 0 < w x) (y : Y) (hne : ∃ x, f x = y) :
    0 < separableDegreeWeightedFiberSum f w y := by
  classical
  obtain ⟨x, hxy⟩ := hne
  rw [separableDegreeWeightedFiberSum_eq_finsum_term]
  exact finsum_pos
    (fun z ↦ separableDegreeWeightedFiberTerm_nonneg f w y z fun z ↦ (hpos z).le)
    ⟨x, separableDegreeWeightedFiberTerm_pos f w y x hxy hpos⟩
    (separableDegreeWeightedFiberTerm_hasFiniteSupport f w y (hfinite y))

/-- A finite fibre of a locally quasi-finite morphism locally of finite type is enumerated
bijectively by `Fin n` for some `n`, and all of its points are isolated. -/
lemma exists_fin_bijective_isolated_fiber
    {X Y : Scheme.{u}} (f : X ⟶ Y) [LocallyOfFiniteType f] [LocallyQuasiFinite f]
    (hfinite : ∀ y, (f ⁻¹' {y}).Finite) (y : Y) :
    ∃ n, ∃ x : Fin n → f.fiber y,
      Function.Bijective x ∧ ∀ i, IsIsolatedPoint (x i) := by
  classical
  have : Finite (f.fiber y) := (f.fiberHomeo y).finite_iff.mpr (hfinite y)
  let : Fintype (f.fiber y) := Fintype.ofFinite _
  let : DiscreteTopology (f.fiber y) :=
    (f.fiberHomeo y).discreteTopology_iff.mpr
      ((_root_.isDiscrete_iff_discreteTopology).mp
        ((locallyQuasiFinite_iff_isDiscrete_preimage_singleton.mp inferInstance) y))
  let e := Fintype.equivFin (f.fiber y)
  refine ⟨Fintype.card (f.fiber y), e.symm, e.symm.bijective, ?_⟩
  intro i
  rw [isIsolatedPoint_iff]
  exact isOpen_discrete _

end AlgebraicGeometry
