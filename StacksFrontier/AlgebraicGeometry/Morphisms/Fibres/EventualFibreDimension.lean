module

public import Mathlib.Algebra.Category.Ring.FilteredColimits
public import Mathlib.Algebra.Polynomial.Bivariate
public import Mathlib.AlgebraicGeometry.AffineSpace
public import Mathlib.AlgebraicGeometry.AffineTransitionLimit
public import Mathlib.AlgebraicGeometry.Artinian
public import Mathlib.AlgebraicGeometry.Fiber
public import Mathlib.AlgebraicGeometry.IdealSheaf.IrreducibleComponent
public import Mathlib.AlgebraicGeometry.Morphisms.ClosedImmersion
public import Mathlib.AlgebraicGeometry.Morphisms.FiniteType
public import Mathlib.AlgebraicGeometry.Morphisms.Integral
public import Mathlib.AlgebraicGeometry.Morphisms.QuasiFinite
public import Mathlib.AlgebraicGeometry.Normalization
public import Mathlib.AlgebraicGeometry.PullbackCarrier
public import Mathlib.CategoryTheory.Comma.LocallySmall
public import Mathlib.CategoryTheory.Comma.StructuredArrow.Small
public import Mathlib.CategoryTheory.MorphismProperty.Limits
public import Mathlib.Order.Filter.AtTopBot.Basic
public import Mathlib.Order.Filter.Finite
public import Mathlib.RingTheory.Algebraic.Integral
public import Mathlib.RingTheory.Flat.TorsionFree
public import Mathlib.RingTheory.KrullDimension.Polynomial
public import Mathlib.RingTheory.PolynomialAlgebra
public import Mathlib.RingTheory.Spectrum.Prime.Noetherian
public import Mathlib.Topology.Constructible
public import Mathlib.Topology.NoetherianSpace
public import StacksCore.Tactic.StacksAttribute
public import StacksCore.Topology.NowhereDense.Defs
public import StacksFrontier.AlgebraicGeometry.FibreDimensionBaseChange.Basic
public import StacksFrontier.AlgebraicGeometry.FibreDimensionBaseChange.Composite
public import StacksFrontier.AlgebraicGeometry.Limits.FibreDimensionBound
public import StacksFrontier.AlgebraicGeometry.Morphisms.FibreDimension.Basic
public import StacksFrontier.AlgebraicGeometry.Morphisms.FibreDimension.Openness
public import StacksFrontier.AlgebraicGeometry.Morphisms.FlatMorphisms.GenericFlatness
public import StacksFrontier.AlgebraicGeometry.Morphisms.Integral.Dimension
public import StacksFrontier.AlgebraicGeometry.Morphisms.Normalization.GenericPoints
public import StacksFrontier.AlgebraicGeometry.Properties.Normal
public import StacksFrontier.AlgebraicGeometry.RingedSpace.Flat
public import StacksFrontier.AlgebraicGeometry.Varieties.FunctionFieldEquivalence.Basic
public import StacksFrontier.AlgebraicGeometry.Variety.Defs.Dimension.Components
public import StacksFrontier.AlgebraicGeometry.Variety.Defs.Dimension.Trdeg
public import StacksFrontier.RingTheory.FinitePresentation.ModuleDescent
public import StacksFrontier.RingTheory.GeometricallyIntegral.NowhereDenseGenericFibre
public import StacksFrontier.RingTheory.IntegralClosure.Basic
public import StacksFrontier.RingTheory.KrullDimension.FiniteTypeOverField
public import StacksFrontier.RingTheory.Nagata.Examples
public import StacksFrontier.RingTheory.Spectrum.Prime.Integral
public import StacksFrontier.RingTheory.Spectrum.Prime.LocalDimension
public import StacksFrontier.Topology.Dimension.ClosedSubsetDimension
public import StacksFrontier.Topology.Dimension.Krull
public import StacksFrontier.Topology.Dimension.LocalKrullDim
import StacksFrontier.AlgebraicGeometry.Variety.SmoothOverField.SmoothStratification

/-!
# Eventual fibre dimension of the affine-line morphism attached to `a ^ n + b`

An element `a` of an `R`-algebra `S` determines an `R`-algebra map `R[X] → S`, `X ↦ a`, hence a
morphism `Spec S ⟶ Spec R[X]` to the affine line over `Spec R`. This file shows that a bound on
the dimensions of the fibres of this morphism for `a` propagates to the morphism attached to
`a ^ n + b`, for every element `b` of `S` and every sufficiently large exponent `n`.

## Main definitions

* `AlgebraicGeometry.specMapAeval` is the morphism to the affine line over the base determined
  by an element of the algebra.

## Main results

* `AlgebraicGeometry.eventually_topologicalKrullDim_fiber_specMapAeval_pow_add_le` is the
  eventual bound on the dimensions of all the fibres.
* `AlgebraicGeometry.eventually_fiberDimension_specMapAeval_pow_add_le` is the same bound
  phrased with `AlgebraicGeometry.Scheme.Hom.fiberDimension`.

## Implementation notes

The affine line over the affine base `Spec R` is `Spec R[X]`, by the affine-base compatibility
of `AlgebraicGeometry.AffineSpace`. The bound is asserted for every fibre, including an empty
one, whose topological Krull dimension is `⊥`.

The proof follows the source. Two successive limit arguments reduce to a base ring of finite
type over `ℤ`, hence of finite dimension, and the general case is then settled by induction on
that dimension: passing to the normalization splits the source into normal domains, and for a
normal domain the morphism `Spec S ⟶ 𝐀²_R` determined by the pair `a, b` is either dominant,
where generic flatness supplies the bound over a dense open of the base, or not, where a
nonzero polynomial relation between `a` and `b` does. The induction is closed by applying the
inductive hypothesis to the complement of that open subset.

## References

* [Stacks Project, Tag 0GTF](https://stacks.math.columbia.edu/tag/0GTF)
-/

@[expose] public section

open AlgebraicGeometry CategoryTheory

universe u

namespace AlgebraicGeometry
-- The `⟶` below is the morphism type of `Scheme`, not of the quiver structure that the
-- category-theory imports otherwise put first.
attribute [-instance] CategoryTheory.ReflQuiver.toQuiver in
/-- The map `Spec S → Spec R[X]` sending the polynomial variable to `a`. -/
public noncomputable abbrev specMapAeval {R S : Type u} [CommRing R] [CommRing S]
    [Algebra R S] (a : S) : Spec (.of S) ⟶ Spec (.of (Polynomial R)) :=
  Spec.map (CommRingCat.ofHom (Polynomial.aeval a).toRingHom)

end AlgebraicGeometry

namespace EventualFibreDimension
/-- Evaluation on a finite type algebra is a morphism locally of finite type. -/
private lemma locallyOfFiniteType_specMapAeval
    {R S : Type u} [CommRing R] [CommRing S] [Algebra R S]
    [Algebra.FiniteType R S] (a : S) : LocallyOfFiniteType (specMapAeval (R := R) a) := by
  apply (HasRingHomProperty.Spec_iff (P := @LocallyOfFiniteType)).mpr
  apply RingHom.FiniteType.of_comp_finiteType (f := Polynomial.C)
  have hc : (Polynomial.aeval a).toRingHom.comp Polynomial.C = algebraMap R S := by
    ext r
    simp
  show ((Polynomial.aeval a).toRingHom.comp Polynomial.C).FiniteType
  rw [hc]
  exact RingHom.finiteType_algebraMap.mpr inferInstance

/-- `Spec` of an algebra of finite type is locally of finite type over `Spec` of the base. -/
private lemma locallyOfFiniteType_specMap_algebraMap
    (R S : Type u) [CommRing R] [CommRing S] [Algebra R S] [Algebra.FiniteType R S] :
    LocallyOfFiniteType (Spec.map (CommRingCat.ofHom (algebraMap R S))) :=
  (HasRingHomProperty.Spec_iff (P := @LocallyOfFiniteType)).mpr
    (RingHom.finiteType_algebraMap.mpr inferInstance)

/-- A space has dimension at most `d` as soon as all of its local dimensions are. -/
private lemma topologicalKrullDim_le_of_forall_topologicalKrullDimAt_le
    {X : Type*} [TopologicalSpace X] (d : WithBot ℕ∞)
    (h : ∀ x : X, topologicalKrullDimAt X x ≤ d) : topologicalKrullDim X ≤ d := by
  rw [TopologicalSpace.topologicalKrullDim_eq_iSup_localKrullDim]
  refine iSup_le fun x => ?_
  rw [← TopologicalSpace.topologicalKrullDimAt_eq_localKrullDim]
  exact h x

/-- The dimension of a space is bounded by the dimensions of its irreducible components. -/
private lemma topologicalKrullDim_le_of_irreducibleComponents
    {X : Type*} [TopologicalSpace X] (d : WithBot ℕ∞)
    (h : ∀ Z ∈ irreducibleComponents X, topologicalKrullDim Z ≤ d) :
    topologicalKrullDim X ≤ d := by
  rw [topologicalKrullDim, Order.krullDim_eq_iSup_height]
  refine iSup_le fun Z => ?_
  obtain ⟨W, hW, hZW⟩ :=
    exists_mem_irreducibleComponents_subset_of_isIrreducible
      (Z : Set X) Z.isIrreducible
  let W' : TopologicalSpace.IrreducibleCloseds X :=
    ⟨W, hW.1, isClosed_of_mem_irreducibleComponents W hW⟩
  calc
    (Order.height Z : WithBot ℕ∞) ≤ (Order.height W' : WithBot ℕ∞) := by
      exact_mod_cast Order.height_mono (show Z ≤ W' from hZW)
    _ ≤ topologicalKrullDim W := height_le_topologicalKrullDim W'
    _ ≤ d := h W hW

/-- A finite closed cover bounds the dimension of the whole space. -/
@[ega "0 14.1.4" "(ii)"]
private lemma topologicalKrullDim_le_of_finite_closed_cover
    {X ι : Type*} [TopologicalSpace X] [Fintype ι]
    (Z : ι → Set X) (hclosed : ∀ i, IsClosed (Z i))
    (hcover : ⋃ i, Z i = Set.univ) (d : WithBot ℕ∞)
    (hZ : ∀ i, topologicalKrullDim (Z i) ≤ d) : topologicalKrullDim X ≤ d := by
  classical
  apply topologicalKrullDim_le_of_irreducibleComponents d
  intro W hW
  have hWcover : W ⊆ ⋃₀ ↑(Finset.univ.image Z) := by
    simpa only [Finset.coe_image, Finset.coe_univ, Set.image_univ, Set.sUnion_range]
      using (Set.subset_univ W).trans_eq hcover.symm
  obtain ⟨Z', hZ', hsub⟩ :=
    isIrreducible_iff_sUnion_isClosed.mp hW.1 (Finset.univ.image Z)
      (by
        intro T hT
        have hT' : T ∈ Finset.univ.image Z := hT
        obtain ⟨i, -, rfl⟩ := Finset.mem_image.mp hT'
        exact hclosed i) hWcover
  have hZ'' : Z' ∈ Finset.univ.image Z := hZ'
  obtain ⟨i, -, rfl⟩ := Finset.mem_image.mp hZ''
  exact (Topology.IsEmbedding.inclusion hsub).isInducing.topologicalKrullDim_le.trans (hZ i)

/-- The part of a fibre lying in the range of an embedding has the dimension of the
corresponding fibre upstairs. -/
private lemma topologicalKrullDim_fiber_part_range_eq
    {W X Y : Type*} [TopologicalSpace W] [TopologicalSpace X] [TopologicalSpace Y]
    (g : W → X) (f : X → Y) (hg : Topology.IsEmbedding g) (y : Y) :
    topologicalKrullDim {z : f ⁻¹' {y} | (z : X) ∈ Set.range g} =
      topologicalKrullDim ((f ∘ g) ⁻¹' {y}) := by
  let m : (f ∘ g) ⁻¹' {y} → {z : f ⁻¹' {y} | (z : X) ∈ Set.range g} :=
    fun w => ⟨⟨g w, w.property⟩, ⟨w, rfl⟩⟩
  have hm : Topology.IsEmbedding m := by
    have hp : Topology.IsEmbedding
        ((Subtype.val : f ⁻¹' {y} → X) ∘
          (Subtype.val : {z : f ⁻¹' {y} | (z : X) ∈ Set.range g} → f ⁻¹' {y})) :=
      Topology.IsEmbedding.subtypeVal.comp Topology.IsEmbedding.subtypeVal
    exact hp.of_comp_iff.mp (by
      show Topology.IsEmbedding (g ∘ (Subtype.val : (f ∘ g) ⁻¹' {y} → W))
      exact hg.comp Topology.IsEmbedding.subtypeVal)
  have hsurj : Function.Surjective m := by
    rintro ⟨⟨x, hfx⟩, ⟨w, hw⟩⟩
    have hwf : w ∈ (f ∘ g) ⁻¹' {y} := by simpa [hw] using hfx
    exact ⟨⟨w, hwf⟩, Subtype.ext (Subtype.ext hw)⟩
  exact (hm.toHomeomorphOfSurjective hsurj).isHomeomorph.topologicalKrullDim_eq.symm

/-- Restricting a fibre to a subset of the source cannot have greater dimension
than the same restriction of the fibre of a composite map. -/
private lemma topologicalKrullDim_fiber_restrict_le_comp
    {X Y Z : Type*} [TopologicalSpace X] [TopologicalSpace Y]
    [TopologicalSpace Z] (f : X → Y) (g : Y → Z)
    (T : Set X) (y : Y) :
    topologicalKrullDim {x : f ⁻¹' {y} | (x : X) ∈ T} ≤
      topologicalKrullDim {x : (g ∘ f) ⁻¹' {g y} | (x : X) ∈ T} := by
  let A := {x : f ⁻¹' {y} | (x : X) ∈ T}
  let B := {x : (g ∘ f) ⁻¹' {g y} | (x : X) ∈ T}
  let m : A → B := fun x =>
    ⟨⟨x.1.1, congrArg g x.1.2⟩, x.2⟩
  have hm : Topology.IsEmbedding m := by
    have hp : Topology.IsEmbedding
        ((Subtype.val : (g ∘ f) ⁻¹' {g y} → X) ∘
          (Subtype.val : B → (g ∘ f) ⁻¹' {g y})) :=
      Topology.IsEmbedding.subtypeVal.comp Topology.IsEmbedding.subtypeVal
    exact hp.of_comp_iff.mp (by
      show Topology.IsEmbedding
        ((Subtype.val : f ⁻¹' {y} → X) ∘
          (Subtype.val : A → f ⁻¹' {y}))
      exact Topology.IsEmbedding.subtypeVal.comp Topology.IsEmbedding.subtypeVal)
  exact hm.isInducing.topologicalKrullDim_le

/-- Fibre-dimension bounds can be checked on a finite closed cover of the source by
embedded subschemes. -/
private lemma fiber_dimension_le_of_finite_closed_cover
    {X Y : Scheme.{u}} {ι : Type*} [Finite ι]
    (W : ι → Scheme.{u}) (g : ∀ i, W i ⟶ X) (f : X ⟶ Y)
    (hg : ∀ i, Topology.IsClosedEmbedding (g i))
    (hcover : ⋃ i, Set.range (g i) = Set.univ) (d : WithBot ℕ∞)
    (hbound : ∀ i y, topologicalKrullDim (((g i) ≫ f).fiber y) ≤ d) :
    ∀ y, topologicalKrullDim (f.fiber y) ≤ d := by
  classical
  let : Fintype ι := Fintype.ofFinite ι
  intro y
  rw [(f.fiberHomeo y).isHomeomorph.topologicalKrullDim_eq]
  let Z : ι → Set (f ⁻¹' {y}) :=
    fun i => {z | (z : X) ∈ Set.range (g i)}
  apply topologicalKrullDim_le_of_finite_closed_cover Z
  · intro i
    exact (hg i).isClosed_range.preimage continuous_subtype_val
  · ext z
    constructor
    · intro _
      trivial
    · intro _
      have hz : (z : X) ∈ ⋃ i, Set.range (g i) := by rw [hcover]; trivial
      rcases Set.mem_iUnion.mp hz with ⟨i, hi⟩
      exact Set.mem_iUnion.mpr ⟨i, hi⟩
  · intro i
    show topologicalKrullDim {z : f ⁻¹' {y} | (z : X) ∈ Set.range (g i)} ≤ d
    rw [topologicalKrullDim_fiber_part_range_eq (g i) f (hg i).isEmbedding]
    have heq : ((f ∘ (g i : W i → X)) ⁻¹' {y}) = ((g i ≫ f) ⁻¹' {y}) := by
      ext z
      rfl
    rw [heq]
    exact ((g i ≫ f).fiberHomeo y).isHomeomorph.topologicalKrullDim_eq.symm.le.trans
      (hbound i y)

/-- Local dimension is constant on an irreducible scheme locally of finite type over a
field. -/
private lemma topologicalKrullDimAt_eq_of_irreducible
    {k : Type u} [Field k] {X : Scheme.{u}} [IrreducibleSpace X]
    (f : X ⟶ Spec (.of k)) [LocallyOfFiniteType f] (x : X) :
    topologicalKrullDimAt X x = topologicalKrullDim X := by
  have hu : topologicalKrullDim ↥(Set.univ : Set X) = topologicalKrullDim X :=
    (Homeomorph.Set.univ X).isHomeomorph.topologicalKrullDim_eq
  rw [AlgebraicGeometry.topologicalKrullDimAt_eq_iSup_irreducibleComponents
    k X f x]
  apply le_antisymm
  · refine iSup_le fun Z => iSup_le fun hZ => ?_
    have h := hZ.1
    rw [irreducibleComponents_eq_singleton, Set.mem_singleton_iff] at h
    subst Z
    exact hu.le
  · rw [← hu]
    exact le_iSup_of_le Set.univ (le_iSup_of_le
      ⟨by simp [irreducibleComponents_eq_singleton], Set.mem_univ x⟩ le_rfl)

/-- Every point of the affine line over a field has local dimension one. -/
private lemma topologicalKrullDimAt_polynomialSpec
    (k : Type u) [Field k] (x : Spec (.of (Polynomial k))) :
    topologicalKrullDimAt (Spec (.of (Polynomial k))) x = 1 := by
  have : LocallyOfFiniteType (Spec.map
      (CommRingCat.ofHom (Polynomial.C : k →+* Polynomial k))) :=
    locallyOfFiniteType_specMap_algebraMap k (Polynomial k)
  rw [topologicalKrullDimAt_eq_of_irreducible
    (Spec.map (CommRingCat.ofHom (Polynomial.C : k →+* Polynomial k)))]
  show topologicalKrullDim (PrimeSpectrum (Polynomial k)) = 1
  rw [PrimeSpectrum.topologicalKrullDim_eq_ringKrullDim,
    Polynomial.ringKrullDim_of_isNoetherianRing, ringKrullDim_eq_zero_of_field, zero_add]

/-- The fibres of the affine-line projection have local dimension one. -/
private lemma topologicalKrullDimAt_fiber_polynomialSpec
    (R : Type u) [CommRing R] (p : Spec (.of R))
    (x : (Spec.map (CommRingCat.ofHom (Polynomial.C : R →+* Polynomial R))).fiber p) :
    topologicalKrullDimAt
      ((Spec.map (CommRingCat.ofHom (Polynomial.C : R →+* Polynomial R))).fiber p) x = 1 := by
  obtain ⟨φ, hφ⟩ := Spec.map_surjective ((Spec (.of R)).fromSpecResidueField p)
  let k := (Spec (.of R)).residueField p
  let : Algebra R k := φ.hom.toAlgebra
  let : Algebra (Polynomial R) (Polynomial k) := Polynomial.algebra R k
  have hsq := (isPullback_SpecMap_of_isPushout _ _ _ _
    (CommRingCat.isPushout_of_isPushout R k (Polynomial R) (Polynomial k))).flip
  change IsPullback _ _ _ (Spec.map φ) at hsq
  rw [hφ] at hsq
  let e : Spec (.of (Polynomial k)) ≅
      (Spec.map (CommRingCat.ofHom (Polynomial.C : R →+* Polynomial R))).fiber p :=
    hsq.isoPullback
  rw [topologicalKrullDimAt_eq_of_homeomorph (Scheme.homeoOfIso e).symm x]
  exact topologicalKrullDimAt_polynomialSpec k _

/-- An open subset and its complement detect dimension bounds on schemes of finite type
    over a field. -/
private lemma topologicalKrullDim_le_of_open_compl
    {k : Type u} [Field k] {X : Scheme.{u}} (f : X ⟶ Spec (.of k))
    [LocallyOfFiniteType f] (U : X.Opens) (d : WithBot ℕ∞)
    (hU : topologicalKrullDim U ≤ d) (hZ : topologicalKrullDim ↥(Uᶜ : Set X) ≤ d) :
    topologicalKrullDim X ≤ d := by
  refine topologicalKrullDim_le_of_forall_topologicalKrullDimAt_le d fun x => ?_
  rw [AlgebraicGeometry.topologicalKrullDimAt_eq_iSup_irreducibleComponents k X f x]
  refine iSup_le fun Z => iSup_le fun hZ' => ?_
  by_cases h : ∃ y : X, y ∈ Z ∧ y ∈ U
  · obtain ⟨y, hyZ, hyU⟩ := h
    calc
      topologicalKrullDim Z ≤ topologicalKrullDimAt X y := by
        rw [AlgebraicGeometry.topologicalKrullDimAt_eq_iSup_irreducibleComponents
          k X f y]
        exact le_iSup_of_le Z (le_iSup_of_le ⟨hZ'.1, hyZ⟩ le_rfl)
      _ = topologicalKrullDimAt U ⟨y, hyU⟩ :=
        U.isOpen.isOpenEmbedding_subtypeVal.topologicalKrullDimAt_eq ⟨y, hyU⟩
      _ ≤ topologicalKrullDim U := topologicalKrullDimAt_le_topologicalKrullDim _
      _ ≤ d := hU
  · have hsub : Z ⊆ (Uᶜ : Set X) := by
      intro y hy hyU
      exact h ⟨y, hy, hyU⟩
    exact (Topology.IsEmbedding.inclusion hsub).isInducing.topologicalKrullDim_le.trans hZ

/-- A proper closed subset containing no irreducible component of a Noetherian
space has smaller dimension. Applied to the complement of a dense open in a
fibre, this is the dimension drop used in the generic-locus argument. -/
private alias topologicalKrullDim_compl_lt_of_dense_open :=
  AlgebraicGeometry.topologicalKrullDim_compl_lt_nat

/-- A nowhere dense closed subset of a Noetherian space whose dimension is
bounded by `n` has dimension strictly below `n`. -/
private lemma topologicalKrullDim_lt_of_closed_nowhereDense
    {X : Type u} [TopologicalSpace X] [TopologicalSpace.NoetherianSpace X]
    {Z : Set X} (hclosed : IsClosed Z) (hnd : IsNowhereDense Z)
    {n : ℕ} (hdim : topologicalKrullDim X ≤ n) :
    topologicalKrullDim Z < n := by
  have hdense : Dense Zᶜ :=
    (isClosed_isNowhereDense_iff_compl.mp ⟨hclosed, hnd⟩).2
  have h := topologicalKrullDim_compl_lt_of_dense_open hclosed.isOpen_compl
    hdense hdim
  have hset : (Zᶜ)ᶜ = Z := by ext x; simp
  rw [hset] at h
  exact h

/-- The complement of a nonempty open subset of an irreducible scheme is nowhere
dense in the fibre over the image of the generic point. -/
private lemma nowhereDense_compl_open_generic_fiber
    {X Y : Scheme.{u}} [IrreducibleSpace X] (f : X ⟶ Y)
    (U : X.Opens) (hU : (U : Set X).Nonempty) :
    IsNowhereDense
      ((f.fiberι (f (genericPoint X))) ⁻¹' (Uᶜ : Set X)) := by
  let η : X := genericPoint X
  let F : Scheme.{u} := f.fiber (f η)
  let p : F := f.asFiber η
  have hp : IsGenericPoint p (Set.univ : Set F) := by
    apply isGenericPoint_iff_specializes.mpr
    intro z
    have hs : f.fiberι (f η) p ⤳ f.fiberι (f η) z := by
      rw [show f.fiberι (f η) p = η by simp [p]]
      exact genericPoint_specializes (f.fiberι (f η) z)
    exact iff_of_true ((f.fiberι (f η)).isEmbedding.specializes_iff.mp hs)
      (Set.mem_univ z)
  have hηU : η ∈ U :=
    ((genericPoint_spec X).mem_open_set_iff U.isOpen).mpr (by simpa using hU)
  have hmem : p ∈ (f.fiberι (f η)) ⁻¹' (U : Set X) := by
    simpa [p] using hηU
  have hdense : Dense ((f.fiberι (f η)) ⁻¹' (U : Set X)) := by
    apply Dense.mono (s₁ := ({p} : Set F))
    · simpa using hmem
    · exact dense_iff_closure_eq.mpr hp.def
  have hopen : IsOpen ((f.fiberι (f η)) ⁻¹' (U : Set X)) :=
    U.isOpen.preimage (f.fiberι (f η)).continuous
  exact (isClosed_isNowhereDense_iff_compl.mpr
    ⟨by simpa using hopen, by simpa using hdense⟩).2

/-- The complement of a dense open has nowhere dense fibres over an open part
of an irreducible base. -/
private lemma exists_open_nowhereDense_compl_fibers
    {X Y : Scheme.{u}} [IrreducibleSpace X] [IrreducibleSpace Y]
    (f : X ⟶ Y) [IsDominant f] [LocallyOfFiniteType f] [QuasiCompact f]
    (U : X.Opens) (hU : Dense (U : Set X)) :
    ∃ V : Set Y, IsOpen V ∧ V.Nonempty ∧
      ∀ y ∈ V, IsNowhereDense ((f.fiberι y) ⁻¹' (Uᶜ : Set X)) := by
  have hη : f (genericPoint X) = genericPoint Y := map_genericPoint_of_isDominant f
  have hZ : IsNowhereDense
      ((f.fiberι (genericPoint Y)) ⁻¹' (Uᶜ : Set X)) := by
    rw [← hη]
    exact nowhereDense_compl_open_generic_fiber f U hU.nonempty
  exact exists_open_isNowhereDense_fiber f
    (Uᶜ : Set X) U.isOpen.isClosed_compl
    (genericPoint Y) (genericPoint_spec Y) hZ

/-- Fibres of a morphism from a Noetherian scheme are Noetherian spaces. -/
private lemma noetherianSpace_fiber_of_noetherianSource
    {X Y : Scheme.{u}} [TopologicalSpace.NoetherianSpace X]
    (f : X ⟶ Y) (y : Y) :
    TopologicalSpace.NoetherianSpace (f.fiber y) :=
  (TopologicalSpace.noetherianSpace_iff_of_homeomorph (f.fiberHomeo y)).mpr inferInstance

/-- The part of a fibre outside a dense open has dimension at most `d` when
the whole fibre has dimension at most `d + 1`. -/
private lemma fiber_compl_dimension_le_of_nowhereDense
    {X Y : Scheme.{u}} [TopologicalSpace.NoetherianSpace X]
    (f : X ⟶ Y) (U : X.Opens) (d : ℕ)
    (hdim : ∀ y : Y, topologicalKrullDim (f.fiber y) ≤
      ((d + 1 : ℕ) : WithBot ℕ∞))
    (y : Y) (hnd : IsNowhereDense ((f.fiberι y) ⁻¹' (Uᶜ : Set X))) :
    topologicalKrullDim ((f.fiberι y) ⁻¹' (Uᶜ : Set X)) ≤
      (d : WithBot ℕ∞) := by
  let : TopologicalSpace.NoetherianSpace (f.fiber y) :=
    noetherianSpace_fiber_of_noetherianSource f y
  have hclosed : IsClosed ((f.fiberι y) ⁻¹' (Uᶜ : Set X)) :=
    U.isOpen.isClosed_compl.preimage (f.fiberι y).continuous
  have hlt := topologicalKrullDim_lt_of_closed_nowhereDense hclosed hnd (hdim y)
  exact ENat.WithBot.lt_add_one_iff.mp (by simpa using hlt)

/-- The closed part of a fibre is a subspace of the corresponding closed part
of any composite fibre. -/
private lemma fiber_compl_dimension_le_comp
    {X Y Z : Scheme.{u}} (f : X ⟶ Y) (g : Y ⟶ Z)
    (U : X.Opens) (q : Y) :
    topologicalKrullDim ((f.fiberι q) ⁻¹' (Uᶜ : Set X)) ≤
      topologicalKrullDim (((f ≫ g).fiberι (g q)) ⁻¹' (Uᶜ : Set X)) := by
  let eF := (f.fiberHomeo q).subtype
    (p := fun x : f.fiber q => f.fiberι q x ∈ (Uᶜ : Set X))
    (q := fun x : f ⁻¹' {q} => (x : X) ∈ (Uᶜ : Set X))
    (by intro x; rfl)
  let eG := ((f ≫ g).fiberHomeo (g q)).subtype
    (p := fun x : (f ≫ g).fiber (g q) => (f ≫ g).fiberι (g q) x ∈ (Uᶜ : Set X))
    (q := fun x : (f ≫ g) ⁻¹' {g q} => (x : X) ∈ (Uᶜ : Set X))
    (by intro x; rfl)
  show topologicalKrullDim {x : f.fiber q // f.fiberι q x ∈ (Uᶜ : Set X)} ≤
    topologicalKrullDim
      {x : (f ≫ g).fiber (g q) // (f ≫ g).fiberι (g q) x ∈ (Uᶜ : Set X)}
  rw [eF.isHomeomorph.topologicalKrullDim_eq,
    eG.isHomeomorph.topologicalKrullDim_eq]
  exact topologicalKrullDim_fiber_restrict_le_comp f g (Uᶜ : Set X) q

/-- The open part and its complement control the dimension of an evaluation
fibre. -/
private lemma fiber_dimension_le_of_open_compl
    {X Y : Scheme.{u}} (f : X ⟶ Y) [LocallyOfFiniteType f]
    (U : X.Opens) (q : Y) (d : WithBot ℕ∞)
    (hU : topologicalKrullDim ((U.ι ≫ f).fiber q) ≤ d)
    (hZ : topologicalKrullDim ((f.fiberι q) ⁻¹' (Uᶜ : Set X)) ≤ d) :
    topologicalKrullDim (f.fiber q) ≤ d := by
  let V : (f.fiber q).Opens :=
    ⟨(f.fiberι q) ⁻¹' (U : Set X), U.isOpen.preimage (f.fiberι q).continuous⟩
  have hrange : Set.range U.ι = (U : Set X) := by
    ext x
    constructor
    · rintro ⟨u, rfl⟩
      exact u.2
    · intro hx
      exact ⟨⟨x, hx⟩, rfl⟩
  have hV : topologicalKrullDim V ≤ d := by
    let e := (f.fiberHomeo q).subtype
      (p := fun z : f.fiber q => f.fiberι q z ∈ U)
      (q := fun z : f ⁻¹' {q} => z.1 ∈ U)
      (by intro z; rfl)
    calc
      topologicalKrullDim V =
          topologicalKrullDim {z : f ⁻¹' {q} | z.1 ∈ (U : Set X)} :=
        e.isHomeomorph.topologicalKrullDim_eq
      _ = topologicalKrullDim ((f ∘ U.ι) ⁻¹' {q}) := by
        rw [← hrange]
        exact topologicalKrullDim_fiber_part_range_eq U.ι f
          U.ι.isOpenEmbedding.isEmbedding q
      _ = topologicalKrullDim ((U.ι ≫ f).fiber q) :=
        ((U.ι ≫ f).fiberHomeo q).isHomeomorph.topologicalKrullDim_eq.symm
      _ ≤ d := hU
  have hZ' : topologicalKrullDim ↥(Vᶜ : Set (f.fiber q)) ≤ d := by
    simpa [V] using hZ
  have : LocallyOfFiniteType (f.fiberToSpecResidueField q) :=
    (show LocallyOfFiniteType
      (Limits.pullback.snd f (Y.fromSpecResidueField q)) from inferInstance)
  exact @topologicalKrullDim_le_of_open_compl
    (Y.residueField q) _ (f.fiber q) (f.fiberToSpecResidueField q)
    ‹LocallyOfFiniteType (f.fiberToSpecResidueField q)› V d hV hZ'

/-- A dense open in the source controls an evaluation fibre when the complement
is nowhere dense in the corresponding fibre over the base. -/
private lemma fiber_dimension_le_of_open_nowhereDense
    {X Y Z : Scheme.{u}} [TopologicalSpace.NoetherianSpace X]
    (f : X ⟶ Y) (g : Y ⟶ Z) [LocallyOfFiniteType f]
    (U : X.Opens) (d : ℕ)
    (hstructure : ∀ z : Z, topologicalKrullDim ((f ≫ g).fiber z) ≤
      ((d + 1 : ℕ) : WithBot ℕ∞))
    (q : Y)
    (hU : topologicalKrullDim ((U.ι ≫ f).fiber q) ≤
      (d : WithBot ℕ∞))
    (hnd : IsNowhereDense
      (((f ≫ g).fiberι (g q)) ⁻¹' (Uᶜ : Set X))) :
    topologicalKrullDim (f.fiber q) ≤ (d : WithBot ℕ∞) := by
  exact fiber_dimension_le_of_open_compl f U q (d : WithBot ℕ∞) hU
    ((fiber_compl_dimension_le_comp f g U q).trans
      (fiber_compl_dimension_le_of_nowhereDense (f ≫ g) U d hstructure (g q) hnd))

/-- Every point of a fibre comes from the corresponding point of the source. -/
private lemma exists_eq_asFiber {X Y : Scheme.{u}} (f : X ⟶ Y) (y : Y)
    (z : f.fiber y) : ∃ x : X, ∃ h : f x = y, h ▸ f.asFiber x = z := by
  let x := f.fiberι y z
  have h : f x = y := (f.fiberHomeo y z).property
  refine ⟨x, h, ?_⟩
  have hι : ∀ (y' : Y) (h' : f x = y'), f.fiberι y' (h' ▸ f.asFiber x) = x := by
    intro y' h'
    cases h'
    exact f.fiberι_asFiber x
  exact (f.fiberι y).isEmbedding.injective (hι y h)

/-- A bound on all fibres is equivalent to the corresponding pointwise bounds. -/
private lemma forall_fiber_dimension_le_iff {X Y : Scheme.{u}} (f : X ⟶ Y)
    (d : WithBot ℕ∞) :
    (∀ y : Y, topologicalKrullDim (f.fiber y) ≤ d) ↔
      ∀ x : X, topologicalKrullDimAt (f.fiber (f x)) (f.asFiber x) ≤ d := by
  constructor
  · intro h x
    exact (topologicalKrullDimAt_le_topologicalKrullDim _).trans (h _)
  · intro h y
    refine topologicalKrullDim_le_of_forall_topologicalKrullDimAt_le d fun z => ?_
    obtain ⟨x, hxy, hz⟩ := exists_eq_asFiber f y z
    cases hxy
    cases hz
    exact h x

/-- Over a discrete target, a bound for every fibre is a bound for the source. -/
private lemma topologicalKrullDim_le_of_discrete_target
    {X Y : Scheme.{u}} (f : X ⟶ Y) [DiscreteTopology Y] (d : WithBot ℕ∞)
    (h : ∀ y : Y, topologicalKrullDim (f.fiber y) ≤ d) : topologicalKrullDim X ≤ d := by
  refine topologicalKrullDim_le_of_forall_topologicalKrullDimAt_le d fun x => ?_
  have hU : IsOpen (f ⁻¹' {f x}) := (isOpen_discrete _).preimage f.continuous
  calc
    topologicalKrullDimAt X x =
        topologicalKrullDimAt ↥(f ⁻¹' {f x}) ⟨x, rfl⟩ :=
      hU.isOpenEmbedding_subtypeVal.topologicalKrullDimAt_eq ⟨x, rfl⟩
    _ = topologicalKrullDimAt (f.fiber (f x)) (f.asFiber x) :=
      topologicalKrullDimAt_eq_of_homeomorph (f.fiberHomeo (f x)).symm ⟨x, rfl⟩
    _ ≤ topologicalKrullDim (f.fiber (f x)) :=
      topologicalKrullDimAt_le_topologicalKrullDim _
    _ ≤ d := h _

/-- Fibre-dimension bounds are preserved by arbitrary base change. -/
lemma fiber_dimension_le_of_isPullback
    {X' X S' S : Scheme.{u}} (g' : X' ⟶ X) (f' : X' ⟶ S') (f : X ⟶ S) (g : S' ⟶ S)
    (h : IsPullback g' f' f g) [LocallyOfFiniteType f]
    (d : WithBot ℕ∞) (hf : ∀ s : S, topologicalKrullDim (f.fiber s) ≤ d) :
    ∀ s' : S', topologicalKrullDim (f'.fiber s') ≤ d := by
  apply (forall_fiber_dimension_le_iff f' d).mpr
  intro x'
  rw [AlgebraicGeometry.topologicalKrullDimAt_fiber_eq_of_isPullback h x']
  exact (forall_fiber_dimension_le_iff f d).mp hf (g' x')

/-- Evaluation at an element commutes with extension of scalars. -/
private lemma isPullback_specMapAeval_of_isPushout
    {R A S T : Type u} [CommRing R] [CommRing A] [CommRing S] [CommRing T]
    [Algebra R A] [Algebra R S] [Algebra R T] [Algebra A T] [Algebra S T]
    [IsScalarTower R A T] [IsScalarTower R S T] [Algebra.IsPushout R A S T]
    (a : S) :
    IsPullback (Spec.map (CommRingCat.ofHom (algebraMap S T)))
      (specMapAeval (R := A) (algebraMap S T a)) (specMapAeval (R := R) a)
      (Spec.map (CommRingCat.ofHom (Polynomial.mapRingHom (algebraMap R A)))) := by
  let : Algebra (Polynomial R) (Polynomial A) := Polynomial.algebra R A
  have htop := CommRingCat.isPushout_of_isPushout R A (Polynomial R) (Polynomial A)
  have hcompR : (CommRingCat.ofHom (Polynomial.C : R →+* Polynomial R)) ≫
      CommRingCat.ofHom (Polynomial.aeval (R := R) a).toRingHom =
        CommRingCat.ofHom (algebraMap R S) := by
    apply CommRingCat.hom_ext
    ext r
    simp
  have hcompA : (CommRingCat.ofHom (Polynomial.C : A →+* Polynomial A)) ≫
      CommRingCat.ofHom (Polynomial.aeval (R := A) (algebraMap S T a)).toRingHom =
        CommRingCat.ofHom (algebraMap A T) := by
    apply CommRingCat.hom_ext
    ext r
    simp
  have hcomm : CommRingCat.ofHom (Polynomial.mapRingHom (algebraMap R A)) ≫
      CommRingCat.ofHom (Polynomial.aeval (R := A) (algebraMap S T a)).toRingHom =
        CommRingCat.ofHom (Polynomial.aeval (R := R) a).toRingHom ≫
          CommRingCat.ofHom (algebraMap S T) := by
    apply CommRingCat.hom_ext
    ext r <;> simp [← IsScalarTower.algebraMap_apply R A T,
      ← IsScalarTower.algebraMap_apply R S T]
  have hwhole := CommRingCat.isPushout_of_isPushout R A S T
  rw [← hcompR, ← hcompA] at hwhole
  exact (isPullback_SpecMap_of_isPushout _ _ _ _ (hwhole.of_top hcomm htop)).flip

/-- A bound for evaluation fibres is preserved under extension of scalars. -/
private lemma fiber_dimension_evaluation_le_of_isPushout
    {R A S T : Type u} [CommRing R] [CommRing A] [CommRing S] [CommRing T]
    [Algebra R A] [Algebra R S] [Algebra R T] [Algebra A T] [Algebra S T]
    [IsScalarTower R A T] [IsScalarTower R S T] [Algebra.IsPushout R A S T]
    [Algebra.FiniteType R S] (a : S) (d : WithBot ℕ∞)
    (ha : ∀ q : Spec (.of (Polynomial R)),
      topologicalKrullDim ((specMapAeval a).fiber q) ≤ d) :
    ∀ q : Spec (.of (Polynomial A)),
      topologicalKrullDim ((specMapAeval (algebraMap S T a)).fiber q) ≤ d := by
  have := locallyOfFiniteType_specMapAeval (R := R) a
  exact fiber_dimension_le_of_isPullback _ _ _ _
    (isPullback_specMapAeval_of_isPushout (A := A) (T := T) a) d ha

/-- Extension of scalars preserves a uniform bound for all sufficiently large powers. -/
private lemma eventually_fiber_dimension_le_of_isPushout
    {R A S T : Type u} [CommRing R] [CommRing A] [CommRing S] [CommRing T]
    [Algebra R A] [Algebra R S] [Algebra R T] [Algebra A T] [Algebra S T]
    [IsScalarTower R A T] [IsScalarTower R S T] [Algebra.IsPushout R A S T]
    [Algebra.FiniteType R S] (d : ℕ) (a b : S)
    (h : ∃ n₀ : ℕ, ∀ n ≥ n₀, ∀ q : Spec (.of (Polynomial R)),
      topologicalKrullDim ((specMapAeval (a ^ n + b)).fiber q) ≤ (d : WithBot ℕ∞)) :
    ∃ n₀ : ℕ, ∀ n ≥ n₀, ∀ q : Spec (.of (Polynomial A)),
      topologicalKrullDim ((specMapAeval
        ((algebraMap S T a) ^ n + algebraMap S T b)).fiber q) ≤ (d : WithBot ℕ∞) := by
  obtain ⟨N, hN⟩ := h
  refine ⟨N, fun n hn q => ?_⟩
  rw [← map_pow (algebraMap S T), ← map_add (algebraMap S T)]
  exact fiber_dimension_evaluation_le_of_isPushout (A := A) (T := T) _ _ (hN n hn) q

/-- Integral surjections on the source preserve the dimensions of all fibres. -/
private lemma topologicalKrullDim_comp_fiber_eq_of_integral_surjective
    {W X Y : Scheme.{u}} (g : W ⟶ X) (f : X ⟶ Y)
    [IsIntegralHom g] [Surjective g] (y : Y) :
    topologicalKrullDim ((g ≫ f).fiber y) = topologicalKrullDim (f.fiber y) := by
  let e := Limits.pullbackRightPullbackFstIso f (Y.fromSpecResidueField y) g
  show topologicalKrullDim ↥(Limits.pullback (g ≫ f) (Y.fromSpecResidueField y)) = _
  rw [← (Scheme.homeoOfIso e).isHomeomorph.topologicalKrullDim_eq]
  exact @AlgebraicGeometry.topologicalKrullDim_eq_of_isIntegralHom_of_surjective _ _
    (Limits.pullback.snd g (Limits.pullback.fst f (Y.fromSpecResidueField y)))
    (CategoryTheory.MorphismProperty.IsStableUnderBaseChange.of_isPullback
      (CategoryTheory.IsPullback.of_hasPullback g
        (Limits.pullback.fst f (Y.fromSpecResidueField y))) ‹IsIntegralHom g›)
    (CategoryTheory.MorphismProperty.IsStableUnderBaseChange.of_isPullback
      (CategoryTheory.IsPullback.of_hasPullback g
        (Limits.pullback.fst f (Y.fromSpecResidueField y))) ‹Surjective g›)

/-- Over a morphism with one-dimensional fibres, any flat factorization has fibre
dimension bounded by that of another factorization. -/
private lemma topologicalKrullDimAt_fiber_le_of_flat_factorization
    {X Y S : Scheme.{u}} (f₀ f₁ : X ⟶ Y) (g : Y ⟶ S)
    [LocallyOfFiniteType f₀] [LocallyOfFiniteType f₁] [LocallyOfFiniteType g]
    (hcomp : f₀ ≫ g = f₁ ≫ g)
    (hg : ∀ y : Y, topologicalKrullDimAt (g.fiber (g y)) (g.asFiber y) = 1)
    (d : ℕ) (h₀ : ∀ y : Y, topologicalKrullDim (f₀.fiber y) ≤ (d : WithBot ℕ∞))
    (x : X) (hflat : AlgebraicGeometry.IsFlatAt f₁.toLRSHom.toShHom x) :
    topologicalKrullDimAt (f₁.fiber (f₁ x)) (f₁.asFiber x) ≤ (d : WithBot ℕ∞) := by
  have hle := topologicalKrullDimAt_fiber_comp_le_add f₀ g x
  have heq := AlgebraicGeometry.topologicalKrullDimAt_fiber_comp_eq_add_of_isFlatAt f₁ g x hflat
  rw [hg] at hle
  rw [hg, ← hcomp] at heq
  apply ENat.WithBot.add_le_add_one_right_iff.mp
  calc
    _ = topologicalKrullDimAt ((f₀ ≫ g).fiber ((f₀ ≫ g) x)) ((f₀ ≫ g).asFiber x) :=
      heq.symm
    _ ≤ topologicalKrullDimAt (f₀.fiber (f₀ x)) (f₀.asFiber x) + 1 := hle
    _ ≤ (d : WithBot ℕ∞) + 1 := add_le_add
      ((topologicalKrullDimAt_le_topologicalKrullDim
        (f₀.asFiber x)).trans (h₀ _)) le_rfl

/-- Composition with a quasi-finite morphism does not increase pointwise fibre
dimension. -/
private lemma topologicalKrullDimAt_comp_fiber_le_of_locallyQuasiFinite
    {X Y S : Scheme.{u}} (f : X ⟶ Y) (g : Y ⟶ S)
    [LocallyOfFiniteType f] [LocallyOfFiniteType g] [LocallyQuasiFinite g]
    (x : X) :
    topologicalKrullDimAt ((f ≫ g).fiber ((f ≫ g) x)) ((f ≫ g).asFiber x) ≤
      topologicalKrullDimAt (f.fiber (f x)) (f.asFiber x) := by
  have : IsLocallyArtinian (g.fiber (g (f x))) := inferInstance
  have : DiscreteTopology (g.fiber (g (f x))) := inferInstance
  have hg : topologicalKrullDimAt (g.fiber (g (f x))) (g.asFiber (f x)) ≤
      (0 : WithBot ℕ∞) :=
    (topologicalKrullDimAt_le_topologicalKrullDim _).trans
      (topologicalKrullDim_zero_of_discreteTopology _)
  calc
    _ ≤ topologicalKrullDimAt (f.fiber (f x)) (f.asFiber x) +
        topologicalKrullDimAt (g.fiber (g (f x))) (g.asFiber (f x)) :=
      topologicalKrullDimAt_fiber_comp_le_add f g x
    _ ≤ topologicalKrullDimAt (f.fiber (f x)) (f.asFiber x) + 0 :=
      add_le_add_right hg _
    _ = _ := by simp

/-- A fibre is a subspace of the corresponding fibre of a composite. -/
lemma topologicalKrullDim_fiber_le_comp
    {X Y Z : Scheme.{u}} (f : X ⟶ Y) (g : Y ⟶ Z) (y : Y) :
    topologicalKrullDim (f.fiber y) ≤ topologicalKrullDim ((f ≫ g).fiber (g y)) := by
  rw [(f.fiberHomeo y).isHomeomorph.topologicalKrullDim_eq,
    ((f ≫ g).fiberHomeo (g y)).isHomeomorph.topologicalKrullDim_eq]
  have h : f ⁻¹' {y} ⊆ (f ≫ g) ⁻¹' {g y} := by
    intro x hx
    show g (f x) = g y
    exact congrArg g hx
  exact (Topology.IsEmbedding.inclusion h).isInducing.topologicalKrullDim_le

/-- Restriction along an inducing morphism cannot increase fibre dimension. -/
private lemma topologicalKrullDim_comp_fiber_le_of_isInducing
    {W X Y : Scheme.{u}} (g : W ⟶ X) (f : X ⟶ Y)
    (hg : Topology.IsInducing g) (y : Y) :
    topologicalKrullDim ((g ≫ f).fiber y) ≤ topologicalKrullDim (f.fiber y) := by
  rw [((g ≫ f).fiberHomeo y).isHomeomorph.topologicalKrullDim_eq,
    (f.fiberHomeo y).isHomeomorph.topologicalKrullDim_eq]
  let m : (g ≫ f) ⁻¹' {y} → X := fun x => g x.val
  have hm : Topology.IsInducing m := hg.comp Topology.IsInducing.subtypeVal
  have hmem : ∀ x, m x ∈ f ⁻¹' {y} := fun x => x.property
  exact (hm.codRestrict hmem).topologicalKrullDim_le

/-- The scheme-theoretic fibre of an affine morphism has the dimension of its fibre ring. -/
private lemma topologicalKrullDim_fiber_SpecMap
    {R S : Type u} [CommRing R] [CommRing S] [Algebra R S] (p : PrimeSpectrum R) :
    topologicalKrullDim ((Spec.map (CommRingCat.ofHom (algebraMap R S))).fiber p) =
      topologicalKrullDim (Spec (.of (p.asIdeal.Fiber S))) := by
  rw [(Scheme.Hom.fiberHomeo (Spec.map (CommRingCat.ofHom (algebraMap R S)))
    p).isHomeomorph.topologicalKrullDim_eq]
  exact (PrimeSpectrum.preimageHomeomorphFiber R S p).isHomeomorph.topologicalKrullDim_eq

-- Comparing the two maps unfolds the canonical fibre homeomorphism.
/-- The map from the spectrum of an affine fibre ring to the original spectrum is an
embedding. -/
private lemma isEmbedding_SpecMap_fiber_includeRight
    {R S : Type u} [CommRing R] [CommRing S] [Algebra R S] (p : PrimeSpectrum R) :
    Topology.IsEmbedding (Spec.map (CommRingCat.ofHom
      (Algebra.TensorProduct.includeRight : S →ₐ[R] p.asIdeal.Fiber S).toRingHom)) := by
  show Topology.IsEmbedding (PrimeSpectrum.comap
    (Algebra.TensorProduct.includeRight : S →ₐ[R] p.asIdeal.Fiber S).toRingHom)
  exact Topology.IsEmbedding.subtypeVal.comp
    (PrimeSpectrum.preimageHomeomorphFiber R S p).symm.isEmbedding

/-- Evaluation followed by the affine-line projection is the structure morphism. -/
private lemma specMapAeval_comp_polynomialSpecMap
    {R S : Type u} [CommRing R] [CommRing S] [Algebra R S] (a : S) :
    specMapAeval (R := R) a ≫
      Spec.map (CommRingCat.ofHom (Polynomial.C : R →+* Polynomial R)) =
        Spec.map (CommRingCat.ofHom (algebraMap R S)) := by
  rw [← Spec.map_comp]
  congr 1
  apply CommRingCat.hom_ext
  ext r
  simp

/-- A bound for the fibres of an evaluation map bounds the fibres of the
structure morphism by one more dimension. -/
private lemma fiber_dimension_structure_le_add_one
    {R S : Type u} [CommRing R] [CommRing S] [Algebra R S]
    [Algebra.FiniteType R S] (d : ℕ) (a : S)
    (ha : ∀ q : Spec (.of (Polynomial R)),
      topologicalKrullDim ((specMapAeval a).fiber q) ≤ (d : WithBot ℕ∞))
    (p : Spec (.of R)) :
    topologicalKrullDim
      ((Spec.map (CommRingCat.ofHom (algebraMap R S))).fiber p) ≤
        ((d + 1 : ℕ) : WithBot ℕ∞) := by
  let g := Spec.map (CommRingCat.ofHom (Polynomial.C : R →+* Polynomial R))
  have : LocallyOfFiniteType (specMapAeval (R := R) a) :=
    locallyOfFiniteType_specMapAeval a
  have : LocallyOfFiniteType g := locallyOfFiniteType_specMap_algebraMap R (Polynomial R)
  have h : ∀ p : Spec (.of R),
      topologicalKrullDim ((specMapAeval a ≫ g).fiber p) ≤
        ((d + 1 : ℕ) : WithBot ℕ∞) := by
    apply (forall_fiber_dimension_le_iff _ _).mpr
    intro x
    calc
      topologicalKrullDimAt ((specMapAeval a ≫ g).fiber
        ((specMapAeval a ≫ g) x)) ((specMapAeval a ≫ g).asFiber x) ≤
      topologicalKrullDimAt ((specMapAeval a).fiber
        (specMapAeval a x)) ((specMapAeval a).asFiber x) +
      topologicalKrullDimAt (g.fiber (g (specMapAeval a x)))
        (g.asFiber (specMapAeval a x)) :=
            topologicalKrullDimAt_fiber_comp_le_add _ _ x
      _ ≤ (d : WithBot ℕ∞) + 1 := by
        rw [topologicalKrullDimAt_fiber_polynomialSpec]
        exact add_le_add
          ((topologicalKrullDimAt_le_topologicalKrullDim _).trans
            (ha (specMapAeval a x))) le_rfl
      _ = ((d + 1 : ℕ) : WithBot ℕ∞) := by simp
  rw [← specMapAeval_comp_polynomialSpecMap a]
  exact h p

/-- A flat map to the affine line has no larger fibres than another one with the same
composite to the base. -/
private lemma fiber_dimension_le_of_flat_of_comp_eq
    {R : Type u} [CommRing R] {X : Scheme.{u}} (f₀ f₁ : X ⟶ Spec (.of (Polynomial R)))
    [LocallyOfFiniteType f₀] [LocallyOfFiniteType f₁] [Flat f₁]
    (hcomp : f₀ ≫ Spec.map (CommRingCat.ofHom (Polynomial.C : R →+* Polynomial R)) =
      f₁ ≫ Spec.map (CommRingCat.ofHom (Polynomial.C : R →+* Polynomial R)))
    (d : ℕ) (h₀ : ∀ q, topologicalKrullDim (f₀.fiber q) ≤ (d : WithBot ℕ∞)) :
    ∀ q, topologicalKrullDim (f₁.fiber q) ≤ (d : WithBot ℕ∞) := by
  have : LocallyOfFiniteType
      (Spec.map (CommRingCat.ofHom (Polynomial.C : R →+* Polynomial R))) :=
    locallyOfFiniteType_specMap_algebraMap R (Polynomial R)
  apply (forall_fiber_dimension_le_iff _ _).mpr
  intro x
  exact topologicalKrullDimAt_fiber_le_of_flat_factorization f₀ f₁ _ hcomp
    (fun y => topologicalKrullDimAt_fiber_polynomialSpec R _ _) d h₀ x
    ((Flat.iff_flat_stalkMap _).mp inferInstance x)

/-- A flat evaluation map has no larger fibres than any other evaluation map. -/
private lemma fiber_dimension_evaluation_le_of_flat
    {R S : Type u} [CommRing R] [CommRing S] [Algebra R S]
    [Algebra.FiniteType R S] (d : ℕ) (a c : S)
    (ha : ∀ q : Spec (.of (Polynomial R)),
      topologicalKrullDim ((specMapAeval a).fiber q) ≤ (d : WithBot ℕ∞))
    [Flat (specMapAeval (R := R) c)] :
    ∀ q : Spec (.of (Polynomial R)),
      topologicalKrullDim ((specMapAeval c).fiber q) ≤ (d : WithBot ℕ∞) := by
  have := locallyOfFiniteType_specMapAeval (R := R) a
  have := locallyOfFiniteType_specMapAeval (R := R) c
  exact fiber_dimension_le_of_flat_of_comp_eq (specMapAeval a) (specMapAeval c)
    ((specMapAeval_comp_polynomialSpecMap a).trans
      (specMapAeval_comp_polynomialSpecMap c).symm) d ha

/-- Flatness on an open part of the source gives the original dimension bound on that
open part. -/
private lemma fiber_dimension_restrict_evaluation_le_of_flat
    {R S : Type u} [CommRing R] [CommRing S] [Algebra R S]
    [Algebra.FiniteType R S] (d : ℕ) (a c : S) (U : (Spec (.of S)).Opens)
    (ha : ∀ q : Spec (.of (Polynomial R)),
      topologicalKrullDim ((specMapAeval a).fiber q) ≤ (d : WithBot ℕ∞))
    [Flat (U.ι ≫ specMapAeval (R := R) c)] :
    ∀ q : Spec (.of (Polynomial R)),
      topologicalKrullDim ((U.ι ≫ specMapAeval c).fiber q) ≤ (d : WithBot ℕ∞) := by
  have := locallyOfFiniteType_specMapAeval (R := R) a
  have := locallyOfFiniteType_specMapAeval (R := R) c
  refine fiber_dimension_le_of_flat_of_comp_eq (U.ι ≫ specMapAeval a)
    (U.ι ≫ specMapAeval c) (by simp only [Category.assoc,
      specMapAeval_comp_polynomialSpecMap]) d fun q => ?_
  exact (topologicalKrullDim_comp_fiber_le_of_isInducing U.ι (specMapAeval a)
    U.ι.isOpenEmbedding.isInducing q).trans (ha q)

/-- Evaluation commutes with homomorphisms of algebras. -/
private lemma specMap_comp_specMapAeval
    {R S T : Type u} [CommRing R] [CommRing S] [CommRing T]
    [Algebra R S] [Algebra R T] (φ : S →ₐ[R] T) (a : S) :
    Spec.map (CommRingCat.ofHom φ.toRingHom) ≫ specMapAeval (R := R) a =
      specMapAeval (R := R) (φ a) := by
  rw [← Spec.map_comp]
  congr 1
  apply CommRingCat.hom_ext
  ext <;> simp

/-- An element integral over a field takes values in a zero-dimensional finite scheme;
therefore its evaluation fibres detect the dimension of the source. -/
private lemma topologicalKrullDim_le_of_isIntegral
    {R k S : Type u} [CommRing R] [Field k] [CommRing S]
    [Algebra R k] [Algebra R S] [Algebra k S] [IsScalarTower R k S]
    (a : S) (ha : IsIntegral k a) (d : WithBot ℕ∞)
    (hd : ∀ q : Spec (.of (Polynomial R)),
      topologicalKrullDim ((specMapAeval a).fiber q) ≤ d) :
    topologicalKrullDim (Spec (.of S)) ≤ d := by
  let B := Algebra.adjoin k ({a} : Set S)
  have : Module.Finite k B := Algebra.finite_adjoin_simple_of_isIntegral ha
  have : IsArtinianRing B := isArtinian_of_tower k inferInstance
  let φ : B →ₐ[R] S := (Subalgebra.val B).restrictScalars R
  let aB : B := ⟨a, Algebra.subset_adjoin (Set.mem_singleton a)⟩
  let f := Spec.map (CommRingCat.ofHom φ.toRingHom)
  apply topologicalKrullDim_le_of_discrete_target f d
  intro q
  have hcomp : f ≫ specMapAeval (R := R) aB = specMapAeval (R := R) a :=
    specMap_comp_specMapAeval φ aB
  exact (topologicalKrullDim_fiber_le_comp f (specMapAeval (R := R) aB) q).trans
    (by rw [hcomp]; exact hd _)

/-- Injective integral extensions of algebras preserve evaluation fibre dimensions. -/
private lemma fiber_dimension_evaluation_eq_of_integral_injective
    {R S T : Type u} [CommRing R] [CommRing S] [CommRing T]
    [Algebra R S] [Algebra R T] (φ : S →ₐ[R] T)
    (hint : φ.toRingHom.IsIntegral) (hinj : Function.Injective φ)
    (a : S) (q : Spec (.of (Polynomial R))) :
    topologicalKrullDim ((specMapAeval (φ a)).fiber q) =
      topologicalKrullDim ((specMapAeval a).fiber q) := by
  have : IsIntegralHom (Spec.map (CommRingCat.ofHom φ.toRingHom)) :=
    IsIntegralHom.SpecMap_iff.mpr hint
  have : Surjective (Spec.map (CommRingCat.ofHom φ.toRingHom)) :=
    ⟨integral_overring_surjective φ.toRingHom hint hinj⟩
  rw [← specMap_comp_specMapAeval φ a]
  exact topologicalKrullDim_comp_fiber_eq_of_integral_surjective _ _ q

/-- An eventual bound is unchanged by an injective integral extension of the source algebra. -/
private lemma eventually_fiber_dimension_le_iff_of_integral_injective
    {R S T : Type u} [CommRing R] [CommRing S] [CommRing T]
    [Algebra R S] [Algebra R T] (φ : S →ₐ[R] T)
    (hint : φ.toRingHom.IsIntegral) (hinj : Function.Injective φ)
    (d : ℕ) (a b : S) :
    (∃ n₀ : ℕ, ∀ n ≥ n₀, ∀ q : Spec (.of (Polynomial R)),
      topologicalKrullDim ((specMapAeval (φ a ^ n + φ b)).fiber q) ≤
        (d : WithBot ℕ∞)) ↔
    (∃ n₀ : ℕ, ∀ n ≥ n₀, ∀ q : Spec (.of (Polynomial R)),
      topologicalKrullDim ((specMapAeval (a ^ n + b)).fiber q) ≤
        (d : WithBot ℕ∞)) := by
  have heq (n : ℕ) (q : Spec (.of (Polynomial R))) :
      topologicalKrullDim ((specMapAeval (φ a ^ n + φ b)).fiber q) =
        topologicalKrullDim ((specMapAeval (a ^ n + b)).fiber q) := by
    rw [← map_pow φ, ← map_add φ]
    exact fiber_dimension_evaluation_eq_of_integral_injective φ hint hinj _ q
  simp_rw [heq]

/-- A surjective algebra map preserves every fibre-dimension bound for evaluation. -/
private lemma fiber_dimension_evaluation_le_of_surjective
    {R S T : Type u} [CommRing R] [CommRing S] [CommRing T]
    [Algebra R S] [Algebra R T] (φ : S →ₐ[R] T) (hφ : Function.Surjective φ)
    (a : S) (q : Spec (.of (Polynomial R))) :
    topologicalKrullDim ((specMapAeval (φ a)).fiber q) ≤
      topologicalKrullDim ((specMapAeval a).fiber q) := by
  rw [← specMap_comp_specMapAeval φ a]
  have : IsClosedImmersion (Spec.map (CommRingCat.ofHom φ.toRingHom)) :=
    IsClosedImmersion.spec_of_surjective _ hφ
  exact topologicalKrullDim_comp_fiber_le_of_isInducing _ _
    (Scheme.Hom.isEmbedding _).isInducing _

/-- A quotient by an ideal contained in the nilradical preserves the dimension of
every evaluation fibre. -/
private lemma fiber_dimension_evaluation_eq_of_nilpotent_quotient
    {R S T : Type u} [CommRing R] [CommRing S] [CommRing T]
    [Algebra R S] [Algebra R T] (φ : S →ₐ[R] T)
    (hφ : Function.Surjective φ) (hker : RingHom.ker φ.toRingHom ≤ nilradical S)
    (a : S) (q : Spec (.of (Polynomial R))) :
    topologicalKrullDim ((specMapAeval (φ a)).fiber q) =
      topologicalKrullDim ((specMapAeval a).fiber q) := by
  have hint : IsIntegralHom (Spec.map (CommRingCat.ofHom φ.toRingHom)) :=
    IsIntegralHom.SpecMap_iff.mpr (RingHom.isIntegral_of_surjective _ hφ)
  have hsurj : Surjective (Spec.map (CommRingCat.ofHom φ.toRingHom)) := by
    have hhomeo : IsHomeomorph (PrimeSpectrum.comap φ.toRingHom) :=
      PrimeSpectrum.isHomeomorph_comap φ.toRingHom
        (fun t => ⟨1, by omega, by
          obtain ⟨s, rfl⟩ := hφ t
          exact ⟨s, by simp⟩⟩) hker
    exact ⟨hhomeo.surjective⟩
  rw [← specMap_comp_specMapAeval φ a]
  exact topologicalKrullDim_comp_fiber_eq_of_integral_surjective _ _ q

/-- Passing to a quotient with nilpotent kernel leaves the eventual bound unchanged. -/
private lemma eventually_fiber_dimension_le_iff_of_nilpotent_quotient
    {R S T : Type u} [CommRing R] [CommRing S] [CommRing T]
    [Algebra R S] [Algebra R T] (φ : S →ₐ[R] T)
    (hφ : Function.Surjective φ) (hker : RingHom.ker φ.toRingHom ≤ nilradical S)
    (d : ℕ) (a b : S) :
    (∃ N : ℕ, ∀ n ≥ N, ∀ q : Spec (.of (Polynomial R)),
      topologicalKrullDim ((specMapAeval (φ a ^ n + φ b)).fiber q) ≤
        (d : WithBot ℕ∞)) ↔
    (∃ N : ℕ, ∀ n ≥ N, ∀ q : Spec (.of (Polynomial R)),
      topologicalKrullDim ((specMapAeval (a ^ n + b)).fiber q) ≤
        (d : WithBot ℕ∞)) := by
  have heq (n : ℕ) (q : Spec (.of (Polynomial R))) :
      topologicalKrullDim ((specMapAeval (φ a ^ n + φ b)).fiber q) =
        topologicalKrullDim ((specMapAeval (a ^ n + b)).fiber q) := by
    rw [← map_pow φ, ← map_add φ]
    exact fiber_dimension_evaluation_eq_of_nilpotent_quotient φ hφ hker _ q
  simp_rw [heq]

/-- A common exponent bound descends through a quotient of the source algebra. -/
private lemma eventually_fiber_dimension_le_of_surjective
    {R S T : Type u} [CommRing R] [CommRing S] [CommRing T]
    [Algebra R S] [Algebra R T] (φ : S →ₐ[R] T) (hφ : Function.Surjective φ)
    (d : ℕ) (a b : S)
    (h : ∃ n₀ : ℕ, ∀ n ≥ n₀, ∀ q : Spec (.of (Polynomial R)),
      topologicalKrullDim ((specMapAeval (a ^ n + b)).fiber q) ≤ (d : WithBot ℕ∞)) :
    ∃ n₀ : ℕ, ∀ n ≥ n₀, ∀ q : Spec (.of (Polynomial R)),
      topologicalKrullDim ((specMapAeval (φ a ^ n + φ b)).fiber q) ≤
        (d : WithBot ℕ∞) := by
  obtain ⟨N, hN⟩ := h
  refine ⟨N, fun n hn q => ?_⟩
  rw [← map_pow φ, ← map_add φ]
  exact (fiber_dimension_evaluation_le_of_surjective φ hφ (a ^ n + b) q).trans
    (hN n hn q)

/-- Postcomposition by an injective map leaves each fibre unchanged. -/
private lemma topologicalKrullDim_fiber_eq_comp_of_injective
    {X Y Z : Scheme.{u}} (f : X ⟶ Y) (g : Y ⟶ Z)
    (hg : Function.Injective g) (y : Y) :
    topologicalKrullDim (f.fiber y) =
      topologicalKrullDim ((f ≫ g).fiber (g y)) := by
  rw [(f.fiberHomeo y).isHomeomorph.topologicalKrullDim_eq,
    ((f ≫ g).fiberHomeo (g y)).isHomeomorph.topologicalKrullDim_eq]
  have h : f ⁻¹' {y} = (f ≫ g) ⁻¹' {g y} := by
    ext x
    show f x = y ↔ g (f x) = g y
    exact hg.eq_iff.symm
  rw [h]

/-- Evaluation over `A` followed by the base change `A[X] → R[X]` is evaluation over `R`. -/
private lemma specMapAeval_comp_specMap_mapRingHom
    {R A S : Type u} [CommRing R] [CommRing A] [CommRing S]
    [Algebra R A] [Algebra R S] [Algebra A S] [IsScalarTower R A S] (a : S) :
    specMapAeval (R := A) a ≫
      Spec.map (CommRingCat.ofHom (Polynomial.mapRingHom (algebraMap R A))) =
        specMapAeval (R := R) a := by
  rw [← Spec.map_comp]
  congr 1
  apply CommRingCat.hom_ext
  ext r <;> simp [← IsScalarTower.algebraMap_apply R A S]

/-- Restricting the coefficient ring along a surjection preserves each evaluation fibre. -/
private lemma fiber_dimension_evaluation_eq_of_surjective_base
    {R A S : Type u} [CommRing R] [CommRing A] [CommRing S]
    [Algebra R A] [Algebra R S] [Algebra A S] [IsScalarTower R A S]
    (hRA : Function.Surjective (algebraMap R A)) (a : S)
    (q : Spec (.of (Polynomial A))) :
    topologicalKrullDim ((specMapAeval (R := A) a).fiber q) =
      topologicalKrullDim ((specMapAeval (R := R) a).fiber
        (Spec.map (CommRingCat.ofHom
          (Polynomial.mapRingHom (algebraMap R A))) q)) := by
  let ψ := Polynomial.mapRingHom (algebraMap R A)
  have hψ : Function.Surjective ψ := Polynomial.map_surjective _ hRA
  have hinj : Function.Injective (Spec.map (CommRingCat.ofHom ψ)) :=
    (PrimeSpectrum.isClosedEmbedding_comap_of_surjective (Polynomial A) ψ hψ).injective
  rw [← specMapAeval_comp_specMap_mapRingHom (R := R) (A := A) a]
  exact topologicalKrullDim_fiber_eq_comp_of_injective _ _ hinj q

/-- A fibre bound over a quotient coefficient ring gives the same bound over
the original coefficient ring. -/
private lemma fiber_dimension_evaluation_le_of_surjective_base
    {R A S : Type u} [CommRing R] [CommRing A] [CommRing S]
    [Algebra R A] [Algebra R S] [Algebra A S] [IsScalarTower R A S]
    (hRA : Function.Surjective (algebraMap R A)) (a : S)
    (d : WithBot ℕ∞)
    (hA : ∀ q : Spec (.of (Polynomial A)),
      topologicalKrullDim ((specMapAeval (R := A) a).fiber q) ≤ d) :
    ∀ q : Spec (.of (Polynomial R)),
      topologicalKrullDim ((specMapAeval (R := R) a).fiber q) ≤ d := by
  let ψ := Polynomial.mapRingHom (algebraMap R A)
  let g := Spec.map (CommRingCat.ofHom ψ)
  have hcomp : specMapAeval (R := A) a ≫ g = specMapAeval (R := R) a :=
    specMapAeval_comp_specMap_mapRingHom a
  apply (forall_fiber_dimension_le_iff _ d).mpr
  intro x
  let q : Spec (.of (Polynomial A)) := specMapAeval (R := A) a x
  have hq : specMapAeval (R := R) a x = g q :=
    congrArg (fun f : Spec (.of S) ⟶ Spec (.of (Polynomial R)) => f x) hcomp |>.symm
  have hdim : topologicalKrullDim
      ((specMapAeval (R := R) a).fiber
        (specMapAeval (R := R) a x)) ≤ d := by
    rw [hq]
    exact (fiber_dimension_evaluation_eq_of_surjective_base hRA a q).symm.le.trans
      (hA q)
  exact (topologicalKrullDimAt_le_topologicalKrullDim _).trans hdim

/-- An eventual bound over a quotient coefficient ring descends to the
original coefficient ring. -/
private lemma eventually_fiber_dimension_le_of_surjective_base
    {R A S : Type u} [CommRing R] [CommRing A] [CommRing S]
    [Algebra R A] [Algebra R S] [Algebra A S] [IsScalarTower R A S]
    (hRA : Function.Surjective (algebraMap R A)) (d : ℕ) (a b : S)
    (h : ∃ N : ℕ, ∀ n ≥ N, ∀ q : Spec (.of (Polynomial A)),
      topologicalKrullDim ((specMapAeval (R := A) (a ^ n + b)).fiber q) ≤
        (d : WithBot ℕ∞)) :
    ∃ N : ℕ, ∀ n ≥ N, ∀ q : Spec (.of (Polynomial R)),
      topologicalKrullDim ((specMapAeval (R := R) (a ^ n + b)).fiber q) ≤
        (d : WithBot ℕ∞) := by
  obtain ⟨N, hN⟩ := h
  exact ⟨N, fun n hn => fiber_dimension_evaluation_le_of_surjective_base
    hRA (a ^ n + b) _ (hN n hn)⟩

/-- A surjective change of coefficient ring preserves and reflects an eventual
bound on the dimensions of all evaluation fibres. -/
private lemma eventually_fiber_dimension_le_iff_of_surjective_base
    {R A S : Type u} [CommRing R] [CommRing A] [CommRing S]
    [Algebra R A] [Algebra R S] [Algebra A S] [IsScalarTower R A S]
    (hRA : Function.Surjective (algebraMap R A)) (d : ℕ) (a b : S) :
    (∃ N : ℕ, ∀ n ≥ N, ∀ q : Spec (.of (Polynomial R)),
      topologicalKrullDim ((specMapAeval (R := R) (a ^ n + b)).fiber q) ≤
        (d : WithBot ℕ∞)) ↔
    (∃ N : ℕ, ∀ n ≥ N, ∀ q : Spec (.of (Polynomial A)),
      topologicalKrullDim ((specMapAeval (R := A) (a ^ n + b)).fiber q) ≤
        (d : WithBot ℕ∞)) := by
  constructor
  · rintro ⟨N, hN⟩
    refine ⟨N, fun n hn q => ?_⟩
    rw [fiber_dimension_evaluation_eq_of_surjective_base hRA]
    exact hN n hn _
  · exact eventually_fiber_dimension_le_of_surjective_base hRA d a b

/-- The affine-plane map with coordinates given by `a` and `b`, using nested polynomial rings
to model the two affine coordinates. -/
private noncomputable def planeEvaluationRingMap {R S : Type u} [CommRing R] [CommRing S]
    [Algebra R S] (a b : S) : Polynomial (Polynomial R) →+* S :=
  Polynomial.eval₂RingHom (Polynomial.aeval a).toRingHom b

/-- The polynomial map `(x, y) ↦ x^n + y` on the affine plane over `R`. -/
private noncomputable def powerAddProjectionRingMap {R : Type u} [CommRing R] (n : ℕ) :
    Polynomial R →+* Polynomial (Polynomial R) :=
  (Polynomial.aeval (R := R)
    ((Polynomial.C (Polynomial.X : Polynomial R) : Polynomial (Polynomial R)) ^ n +
      Polynomial.X)).toRingHom

/-- The projection `x^n + y` is a polynomial projection followed by a change of coordinates. -/
private lemma powerAddProjectionRingMap_flat {R : Type u} [CommRing R] (n : ℕ) :
    (powerAddProjectionRingMap (R := R) n).Flat := by
  let : Algebra (Polynomial R) (Polynomial (Polynomial R)) :=
    Polynomial.algebraOfAlgebra
  let e : Polynomial (Polynomial R) ≃ₐ[R] Polynomial (Polynomial R) :=
    Polynomial.Bivariate.swap.trans
      ((Polynomial.algEquivAevalXAddC ((Polynomial.X : Polynomial R) ^ n)).restrictScalars R)
  have he : powerAddProjectionRingMap (R := R) n =
      e.toRingHom.comp Polynomial.C := by
    ext r <;> simp [e, powerAddProjectionRingMap, Polynomial.Bivariate.swap_C,
      Polynomial.algEquivAevalXAddC, add_comm]
  rw [he]
  have hC : (Polynomial.C : Polynomial R →+* Polynomial (Polynomial R)).Flat := by
    show (algebraMap (Polynomial R) (Polynomial (Polynomial R))).Flat
    exact RingHom.flat_algebraMap_iff.mpr inferInstance
  exact hC.comp (RingHom.Flat.of_bijective e.bijective)

/-- The `x^n + y` projection composed with the affine-plane map is evaluation at `a^n + b`.
This identifies the scheme morphism used in the theorem with the composition in the geometric
argument. -/
private theorem planeEvaluationMap_comp_powerAddProjection
    {R S : Type u} [CommRing R] [CommRing S] [Algebra R S] (a b : S) (n : ℕ) :
    Spec.map (CommRingCat.ofHom (planeEvaluationRingMap (R := R) a b)) ≫
        Spec.map (CommRingCat.ofHom (powerAddProjectionRingMap (R := R) n)) =
      specMapAeval (a ^ n + b) := by
  rw [← Spec.map_comp]
  congr 1
  apply CommRingCat.hom_ext
  ext x
  · simp [planeEvaluationRingMap, powerAddProjectionRingMap]
  · show planeEvaluationRingMap (R := R) a b
      (powerAddProjectionRingMap (R := R) n Polynomial.X) =
        (Polynomial.aeval (R := R) (a ^ n + b)) Polynomial.X
    simp [planeEvaluationRingMap, powerAddProjectionRingMap,
      Polynomial.eval₂_add, Polynomial.eval₂_pow, Polynomial.eval₂_C, Polynomial.eval₂_X]

/-- Flatness of the affine-plane map implies flatness of every perturbed evaluation. -/
private lemma flat_specMapAeval_pow_add
    {R S : Type u} [CommRing R] [CommRing S] [Algebra R S] (a b : S)
    (hflat : Flat (Spec.map (CommRingCat.ofHom (planeEvaluationRingMap (R := R) a b))))
    (n : ℕ) : Flat (specMapAeval (R := R) (a ^ n + b)) := by
  have : Flat (Spec.map (CommRingCat.ofHom (powerAddProjectionRingMap (R := R) n))) :=
    Flat.SpecMap_iff.mpr (powerAddProjectionRingMap_flat n)
  rw [← planeEvaluationMap_comp_powerAddProjection]
  exact Flat.comp _ _

/-- On the locus where the affine-plane evaluation is flat, every perturbed evaluation
satisfies the original fibre-dimension bound. -/
private lemma fiber_dimension_pow_add_le_of_plane_flat
    {R S : Type u} [CommRing R] [CommRing S] [Algebra R S]
    [Algebra.FiniteType R S] (d : ℕ) (a b : S)
    (ha : ∀ q : Spec (.of (Polynomial R)),
      topologicalKrullDim ((specMapAeval a).fiber q) ≤ (d : WithBot ℕ∞))
    (hflat : Flat (Spec.map (CommRingCat.ofHom (planeEvaluationRingMap (R := R) a b))))
    (n : ℕ) : ∀ q : Spec (.of (Polynomial R)),
      topologicalKrullDim ((specMapAeval (a ^ n + b)).fiber q) ≤ (d : WithBot ℕ∞) := by
  have := flat_specMapAeval_pow_add a b hflat n
  exact fiber_dimension_evaluation_le_of_flat d a _ ha

-- Elaborating the finite free structure sheaf involves the local generator construction.
/-- A dominant morphism from an irreducible scheme to a reduced scheme is flat on a
dense open of its source. -/
private lemma exists_dense_open_flat_of_isDominant
    {X Y : Scheme.{u}} (f : X ⟶ Y) [IrreducibleSpace X] [IsReduced Y]
    [LocallyOfFiniteType f] [QuasiCompact f] [IsDominant f] :
    ∃ U : X.Opens, Dense (U : Set X) ∧ Flat (U.ι ≫ f) := by
  have : Nonempty Y := Nonempty.map f inferInstance
  have : (SheafOfModules.free (R := X.ringCatSheaf) PUnit.{u + 1}).IsFiniteType := by
    let G := SheafOfModules.free.generatingSections (R := X.ringCatSheaf) PUnit.{u + 1}
    let q := G.localGeneratorsData
    refine { exists_localGeneratorsData := ?_ }
    refine ⟨q, ?_⟩
    constructor
    intro i
    constructor
    show Finite PUnit.{u + 1}
    infer_instance
  obtain ⟨V, hV, hflat, _⟩ :=
    AlgebraicGeometry.exists_dense_open_flat_finitePresentation f
      (SheafOfModules.free (R := X.ringCatSheaf) PUnit.{u + 1})
  have hdense : DenseRange f := IsDominant.denseRange
  have hne : (f ⁻¹' (V : Set Y)).Nonempty := hdense.exists_mem_open V.isOpen hV.nonempty
  refine ⟨f ⁻¹ᵁ V, (f ⁻¹ᵁ V).isOpen.dense hne, ?_⟩
  rw [← f.resLE_comp_ι (U := V) le_rfl]
  exact Flat.comp _ _

/-- The two-coordinate map of an algebra of finite type is locally of finite type. -/
private lemma locallyOfFiniteType_planeEvaluationRingMap
    {R S : Type u} [CommRing R] [CommRing S] [Algebra R S]
    [Algebra.FiniteType R S] (a b : S) :
    LocallyOfFiniteType (Spec.map (CommRingCat.ofHom (planeEvaluationRingMap (R := R) a b))) := by
  apply (HasRingHomProperty.Spec_iff (P := @LocallyOfFiniteType)).mpr
  apply RingHom.FiniteType.of_comp_finiteType (f := Polynomial.C.comp Polynomial.C)
  have h : (planeEvaluationRingMap (R := R) a b).comp (Polynomial.C.comp Polynomial.C) =
      algebraMap R S := by
    ext r
    simp [planeEvaluationRingMap, Polynomial.eval₂_C]
  show ((planeEvaluationRingMap (R := R) a b).comp (Polynomial.C.comp Polynomial.C)).FiniteType
  rw [h]
  exact RingHom.finiteType_algebraMap.mpr inferInstance

/-- `Spec` of an injective ring map is dominant. -/
private lemma isDominant_specMap_of_injective
    {R S : Type u} [CommRing R] [CommRing S] (f : R →+* S)
    (hf : Function.Injective f) : IsDominant (Spec.map (CommRingCat.ofHom f)) := by
  constructor
  show DenseRange (PrimeSpectrum.comap f)
  rw [PrimeSpectrum.denseRange_comap_iff_ker_le_nilRadical,
    (RingHom.injective_iff_ker_eq_bot _).mp hf]
  exact bot_le

/-- A nondominant two-coordinate map from a domain satisfies a nonzero polynomial
relation. -/
private lemma exists_polynomial_relation_of_not_dominant
    {R S : Type u} [CommRing R] [CommRing S] [IsDomain R] [IsDomain S]
    [Algebra R S] (a b : S)
    (h : ¬ IsDominant (Spec.map (CommRingCat.ofHom
      (planeEvaluationRingMap (R := R) a b)))) :
    ∃ g : Polynomial (Polynomial R), g ≠ 0 ∧
      g.eval₂ (Polynomial.aeval a).toRingHom b = 0 := by
  by_contra hrel
  push Not at hrel
  have hinj : Function.Injective (planeEvaluationRingMap (R := R) a b) := by
    refine (RingHom.injective_iff_ker_eq_bot _).mpr (le_antisymm (fun g hg ↦ ?_) bot_le)
    show g = 0
    by_contra hne
    exact hrel g hne hg
  exact h (isDominant_specMap_of_injective _ hinj)

/-- If the two-coordinate map is dominant over a domain, all powers satisfy the bound on
one dense open subset of the source. -/
private lemma exists_dense_open_fiber_dimension_pow_add_le_of_dominant
    {R S : Type u} [CommRing R] [CommRing S] [IsDomain R] [IsDomain S] [Algebra R S]
    [Algebra.FiniteType R S] (d : ℕ) (a b : S)
    (ha : ∀ q : Spec (.of (Polynomial R)),
      topologicalKrullDim ((specMapAeval a).fiber q) ≤ (d : WithBot ℕ∞))
    [IsDominant (Spec.map (CommRingCat.ofHom (planeEvaluationRingMap (R := R) a b)))] :
    ∃ U : (Spec (.of S)).Opens, Dense (U : Set (Spec (.of S))) ∧
      ∀ n : ℕ, ∀ q : Spec (.of (Polynomial R)),
        topologicalKrullDim ((U.ι ≫ specMapAeval (a ^ n + b)).fiber q) ≤
          (d : WithBot ℕ∞) := by
  have := locallyOfFiniteType_planeEvaluationRingMap (R := R) a b
  obtain ⟨U, hU, hflat⟩ := exists_dense_open_flat_of_isDominant
    (Spec.map (CommRingCat.ofHom (planeEvaluationRingMap (R := R) a b)))
  refine ⟨U, hU, fun n => ?_⟩
  have : Flat (Spec.map (CommRingCat.ofHom (powerAddProjectionRingMap (R := R) n))) :=
    Flat.SpecMap_iff.mpr (powerAddProjectionRingMap_flat n)
  have : Flat (U.ι ≫ specMapAeval (R := R) (a ^ n + b)) := by
    rw [← planeEvaluationMap_comp_powerAddProjection, ← Category.assoc]
    exact Flat.comp _ _
  exact fiber_dimension_restrict_evaluation_le_of_flat d a _ U ha

/-- Substitution of a monic polynomial whose degree exceeds the degrees of the lower
coefficients makes the highest power dominate. -/
private lemma leadingCoeff_eval_of_monic_of_coeff_natDegree_lt
    {R : Type*} [CommRing R] (g : Polynomial (Polynomial R)) (q : Polynomial R)
    (hg : g ≠ 0) (hq : q.Monic)
    (hdeg : ∀ i < g.natDegree, (g.coeff i).natDegree < q.natDegree) :
    (g.eval q).leadingCoeff = g.leadingCoeff.leadingCoeff ∧
      (g.eval q).natDegree = g.leadingCoeff.natDegree + g.natDegree * q.natDegree := by
  classical
  have hlc : g.leadingCoeff ≠ 0 := Polynomial.leadingCoeff_ne_zero.mpr hg
  have hlclc : g.leadingCoeff.leadingCoeff ≠ 0 := Polynomial.leadingCoeff_ne_zero.mpr hlc
  have hlastlc : (g.leadingCoeff * q ^ g.natDegree).leadingCoeff =
      g.leadingCoeff.leadingCoeff := Polynomial.leadingCoeff_mul_monic (hq.pow _)
  have hlastne : g.leadingCoeff * q ^ g.natDegree ≠ 0 :=
    Polynomial.leadingCoeff_ne_zero.mp (hlastlc ▸ hlclc)
  have hlastdeg : (g.leadingCoeff * q ^ g.natDegree).natDegree =
      g.leadingCoeff.natDegree + g.natDegree * q.natDegree := by
    rw [Polynomial.natDegree_mul', hq.natDegree_pow]
    simpa [(hq.pow _).leadingCoeff] using hlclc
  have hsum : g.eval q =
      (∑ i ∈ Finset.range g.natDegree, g.coeff i * q ^ i) +
        g.leadingCoeff * q ^ g.natDegree := by
    rw [Polynomial.eval_eq_sum_range, Finset.sum_range_succ, Polynomial.coeff_natDegree]
  have hlt : (∑ i ∈ Finset.range g.natDegree, g.coeff i * q ^ i).degree <
      (g.leadingCoeff * q ^ g.natDegree).degree := by
    refine (Polynomial.degree_sum_le _ _).trans_lt ?_
    apply (Finset.sup_lt_iff (bot_lt_iff_ne_bot.mpr
      (fun h => hlastne (Polynomial.degree_eq_bot.mp h)))).mpr
    intro i hi
    have hi' := Finset.mem_range.mp hi
    have hterm : (g.coeff i * q ^ i).natDegree <
        g.leadingCoeff.natDegree + g.natDegree * q.natDegree := by
      calc
        _ ≤ (g.coeff i).natDegree + i * q.natDegree :=
          Polynomial.natDegree_mul_le.trans
            (Nat.add_le_add_left Polynomial.natDegree_pow_le _)
        _ < q.natDegree + i * q.natDegree := Nat.add_lt_add_right (hdeg i hi') _
        _ = (i + 1) * q.natDegree := by ring
        _ ≤ g.natDegree * q.natDegree := Nat.mul_le_mul_right _ hi'
        _ ≤ g.leadingCoeff.natDegree + g.natDegree * q.natDegree := Nat.le_add_left _ _
    rw [Polynomial.degree_eq_natDegree hlastne, hlastdeg]
    exact Polynomial.degree_le_natDegree.trans_lt (by exact_mod_cast hterm)
  rw [hsum, Polynomial.leadingCoeff_add_of_degree_lt hlt,
    Polynomial.natDegree_add_eq_right_of_degree_lt hlt, hlastlc, hlastdeg]
  exact ⟨rfl, rfl⟩

/-- The leading coefficient after substituting `y = r - x^n` is nonzero and independent
of both `r` and all sufficiently large `n`. -/
private lemma exists_leadingCoeff_map_eval_C_sub_X_pow
    {R : Type*} [CommRing R] (g : Polynomial (Polynomial R)) (hg : g ≠ 0) :
    ∃ c : R, c ≠ 0 ∧ ∃ n₀ : ℕ,
      ∀ {A : Type*} [CommRing A] (φ : R →+* A), φ c ≠ 0 →
        ∀ n ≥ n₀, ∀ r : A,
          ((g.map (Polynomial.mapRingHom φ)).eval
            (Polynomial.C r - Polynomial.X ^ n)).leadingCoeff = φ c := by
  classical
  let h := g.comp (-Polynomial.X)
  have hh : h ≠ 0 := Polynomial.comp_neg_X_eq_zero_iff.not.mpr hg
  have hc : h.leadingCoeff.leadingCoeff ≠ 0 :=
    Polynomial.leadingCoeff_ne_zero.mpr (Polynomial.leadingCoeff_ne_zero.mpr hh)
  let N := (Finset.range h.natDegree).sup fun i => (h.coeff i).natDegree
  refine ⟨h.leadingCoeff.leadingCoeff, hc, N + 1, ?_⟩
  intro A _ φ hφ n hn r
  have hn0 : n ≠ 0 := by omega
  let H := h.map (Polynomial.mapRingHom φ)
  have hlc : h.leadingCoeff.map φ ≠ 0 := by
    intro heq
    have := Polynomial.leadingCoeff_map_of_leadingCoeff_ne_zero φ hφ
    rw [heq, Polynomial.leadingCoeff_zero] at this
    exact hφ this.symm
  have hHlc : H.leadingCoeff = h.leadingCoeff.map φ :=
    Polynomial.leadingCoeff_map_of_leadingCoeff_ne_zero _ hlc
  have hH : H ≠ 0 := Polynomial.leadingCoeff_ne_zero.mp (hHlc ▸ hlc)
  have hHdeg : H.natDegree = h.natDegree :=
    Polynomial.natDegree_map_of_leadingCoeff_ne_zero _ hlc
  have hHllc : H.leadingCoeff.leadingCoeff = φ h.leadingCoeff.leadingCoeff := by
    rw [hHlc, Polynomial.leadingCoeff_map_of_leadingCoeff_ne_zero φ hφ]
  let q : Polynomial A := Polynomial.X ^ n + Polynomial.C (-r)
  have hq : q.Monic := Polynomial.monic_X_pow_add_C _ hn0
  have hnontriv : Nontrivial A := nontrivial_of_ne _ _ hφ
  have hqdeg : q.natDegree = n := Polynomial.natDegree_X_pow_add_C
  have heval : H.eval q = (g.map (Polynomial.mapRingHom φ)).eval
      (Polynomial.C r - Polynomial.X ^ n) := by
    simp [H, h, q, Polynomial.map_comp, Polynomial.eval_comp, sub_eq_add_neg, add_comm]
  rw [← heval, ← hHllc]
  apply (leadingCoeff_eval_of_monic_of_coeff_natDegree_lt H q hH hq ?_).1
  intro i hi
  rw [hHdeg] at hi
  rw [hqdeg]
  have hle : (H.coeff i).natDegree ≤ (h.coeff i).natDegree := by
    simpa [H] using (Polynomial.natDegree_map_le (f := φ) (p := h.coeff i))
  exact lt_of_le_of_lt (hle.trans (Finset.le_sup (f := fun i => (h.coeff i).natDegree)
    (Finset.mem_range.mpr hi))) (by omega)

/-- A polynomial relation with invertible leading coefficient is a monic relation after
rescaling. -/
private lemma isIntegral_of_isUnit_leadingCoeff_of_aeval_eq_zero
    {R S : Type*} [CommRing R] [CommRing S] [Algebra R S]
    (p : Polynomial R) (a : S) (hp : IsUnit p.leadingCoeff)
    (ha : Polynomial.aeval a p = 0) : IsIntegral R a := by
  refine ⟨hp.unit⁻¹ • p, Polynomial.monic_of_isUnit_leadingCoeff_inv_smul hp, ?_⟩
  change p.eval₂ (algebraMap R S) a = 0 at ha
  simp [Units.smul_def, Polynomial.eval₂_smul, ha]

/-- A bivariate relation makes the first coordinate integral over the perturbed coordinate,
uniformly after inverting one nonzero base coefficient. -/
private lemma exists_eventually_isIntegral_of_polynomial_relation
    {R : Type*} [CommRing R] (g : Polynomial (Polynomial R)) (hg : g ≠ 0) :
    ∃ c : R, c ≠ 0 ∧ ∃ n₀ : ℕ,
      ∀ {A S : Type*} [CommRing A] [CommRing S] [Algebra R A] [Algebra R S]
        [Algebra A S] [IsScalarTower R A S],
        IsUnit (algebraMap R A c) → ∀ (a b : S),
          g.eval₂ (Polynomial.aeval a).toRingHom b = 0 →
            ∀ n ≥ n₀, ∀ r : A, algebraMap A S r = a ^ n + b → IsIntegral A a := by
  obtain ⟨c, hc, N, hN⟩ := exists_leadingCoeff_map_eval_C_sub_X_pow g hg
  refine ⟨c, hc, N, ?_⟩
  intro A S _ _ _ _ _ _ hunit a b hab n hn r hr
  by_cases hA : Subsingleton A
  · let := hA
    have hzero : (1 : S) = 0 := by
      simpa using congrArg (algebraMap A S) (Subsingleton.elim (1 : A) 0)
    exact ⟨1, Polynomial.monic_one, by simpa using hzero⟩
  have : Nontrivial A := not_subsingleton_iff_nontrivial.mp hA
  let G := g.map (Polynomial.mapRingHom (algebraMap R A))
  let q : Polynomial A := Polynomial.C r - Polynomial.X ^ n
  let p := G.eval q
  have hplc : p.leadingCoeff = algebraMap R A c :=
    hN (algebraMap R A) hunit.ne_zero n hn r
  have heval : (Polynomial.aeval (R := A) a).toRingHom.comp
      (Polynomial.mapRingHom (algebraMap R A)) =
        (Polynomial.aeval (R := R) a).toRingHom := by
    ext x <;> simp [IsScalarTower.algebraMap_apply R A S]
  have hq : Polynomial.aeval (R := A) a q = b := by
    simp [q, hr]
  have hp : Polynomial.aeval (R := A) a p = 0 := by
    show (Polynomial.aeval (R := A) a).toRingHom (G.eval q) = 0
    rw [Polynomial.eval, Polynomial.hom_eval₂]
    show G.eval₂ (Polynomial.aeval (R := A) a).toRingHom
      ((Polynomial.aeval (R := A) a) q) = 0
    rw [hq, Polynomial.eval₂_map, heval]
    exact hab
  exact isIntegral_of_isUnit_leadingCoeff_of_aeval_eq_zero p a (hplc ▸ hunit) hp

/-- A nonzero relation between the two coordinates yields a uniform bound away from one
base coefficient. -/
private lemma exists_fiber_dimension_pow_add_le_of_polynomial_relation
    {R S : Type u} [CommRing R] [CommRing S] [Algebra R S]
    (d : ℕ) (a b : S) (g : Polynomial (Polynomial R)) (hg : g ≠ 0)
    (hab : g.eval₂ (Polynomial.aeval a).toRingHom b = 0)
    (ha : ∀ q : Spec (.of (Polynomial R)),
      topologicalKrullDim ((specMapAeval a).fiber q) ≤ (d : WithBot ℕ∞)) :
    ∃ c : R, c ≠ 0 ∧ ∃ N : ℕ, ∀ n ≥ N, ∀ q : Spec (.of (Polynomial R)),
      Polynomial.C c ∉ q.asIdeal →
      topologicalKrullDim ((specMapAeval (a ^ n + b)).fiber q) ≤ (d : WithBot ℕ∞) := by
  obtain ⟨c, hc, N, hN⟩ := exists_eventually_isIntegral_of_polynomial_relation g hg
  refine ⟨c, hc, N, ?_⟩
  intro n hn q hcq
  have : q.asIdeal.IsPrime := q.isPrime
  let P := Polynomial R
  let : Algebra P S := (Polynomial.aeval (R := R) (a ^ n + b)).toRingHom.toAlgebra
  have : IsScalarTower R P S := IsScalarTower.of_algebraMap_eq' (by
    ext r
    show algebraMap R S r = Polynomial.aeval (R := R) (a ^ n + b) (Polynomial.C r)
    simp)
  let k := q.asIdeal.ResidueField
  let T := q.asIdeal.Fiber S
  let : Algebra S T := Algebra.TensorProduct.rightAlgebra
  let : Algebra R k := ((algebraMap P k).comp (algebraMap R P)).toAlgebra
  let RT : Algebra R T := ((algebraMap P T).comp (algebraMap R P)).toAlgebra
  let : SMul R T := RT.toSMul
  let : Module R T := RT.toModule
  have : IsScalarTower R P k := IsScalarTower.of_algebraMap_eq' rfl
  have : IsScalarTower R P T := IsScalarTower.of_algebraMap_eq' rfl
  have : IsScalarTower R k T := IsScalarTower.of_algebraMap_eq' (R := R) (S := k) (A := T) (by
    ext r
    exact (IsScalarTower.algebraMap_apply R P T r).trans
      ((IsScalarTower.algebraMap_apply P k T _).trans
        (congrArg (algebraMap k T) (IsScalarTower.algebraMap_apply R P k r).symm)))
  have : IsScalarTower R S T := IsScalarTower.of_algebraMap_eq' (R := R) (S := S) (A := T) (by
    ext r
    exact (IsScalarTower.algebraMap_apply R P T r).trans
      ((IsScalarTower.algebraMap_apply P S T _).trans
        (congrArg (algebraMap S T) (IsScalarTower.algebraMap_apply R P S r).symm)))
  let φ : S →ₐ[R] T := IsScalarTower.toAlgHom R S T
  have hunit : IsUnit (algebraMap R k c) := by
    apply isUnit_iff_ne_zero.mpr
    show algebraMap P k (Polynomial.C c) ≠ 0
    exact (Ideal.algebraMap_residueField_eq_zero (I := q.asIdeal)).not.mpr hcq
  have heval : φ.toRingHom.comp (Polynomial.aeval (R := R) a).toRingHom =
      (Polynomial.aeval (R := R) (φ a)).toRingHom := by
    ext r <;> simp
  have hab' : g.eval₂ (Polynomial.aeval (R := R) (φ a)).toRingHom (φ b) = 0 := by
    have h := congrArg φ hab
    change φ.toRingHom (g.eval₂ (Polynomial.aeval a).toRingHom b) = φ.toRingHom 0 at h
    rw [Polynomial.hom_eval₂, heval, map_zero] at h
    exact h
  have hr : algebraMap k T (algebraMap P k Polynomial.X) = φ a ^ n + φ b := by
    rw [← IsScalarTower.algebraMap_apply P k T,
      IsScalarTower.algebraMap_apply P S T]
    show φ (Polynomial.aeval (R := R) (a ^ n + b) Polynomial.X) = _
    simp
  have hint : IsIntegral k (φ a) := hN hunit (φ a) (φ b) hab' n hn _ hr
  have hd : ∀ p : Spec (.of (Polynomial R)),
      topologicalKrullDim ((specMapAeval (φ a)).fiber p) ≤ (d : WithBot ℕ∞) := by
    intro p
    rw [← specMap_comp_specMapAeval φ a]
    exact (topologicalKrullDim_comp_fiber_le_of_isInducing
      (Spec.map (CommRingCat.ofHom φ.toRingHom)) (specMapAeval (R := R) a)
      (isEmbedding_SpecMap_fiber_includeRight (R := P) (S := S) q).isInducing p).trans (ha p)
  show topologicalKrullDim ((Spec.map (CommRingCat.ofHom (algebraMap P S))).fiber q) ≤ _
  exact (topologicalKrullDim_fiber_SpecMap (R := P) (S := S) q).trans_le
    (topologicalKrullDim_le_of_isIntegral (R := R) (k := k) (φ a) hint _ hd)

/-- On a dense open of an integral source, the perturbation has the required fibre
dimension over one principal open of the base. -/
private lemma exists_dense_open_eventually_fiber_dimension_pow_add_le
    {R S : Type u} [CommRing R] [CommRing S] [IsDomain R] [IsDomain S]
    [Algebra R S] [Algebra.FiniteType R S] (d : ℕ) (a b : S)
    (ha : ∀ q : Spec (.of (Polynomial R)),
      topologicalKrullDim ((specMapAeval a).fiber q) ≤ (d : WithBot ℕ∞)) :
    ∃ U : (Spec (.of S)).Opens, Dense (U : Set (Spec (.of S))) ∧
      ∃ c : R, c ≠ 0 ∧ ∃ N : ℕ, ∀ n ≥ N, ∀ q : Spec (.of (Polynomial R)),
        Polynomial.C c ∉ q.asIdeal →
          topologicalKrullDim ((U.ι ≫ specMapAeval (a ^ n + b)).fiber q) ≤
            (d : WithBot ℕ∞) := by
  let φ := Spec.map (CommRingCat.ofHom (planeEvaluationRingMap (R := R) a b))
  by_cases hdom : IsDominant φ
  · let : IsDominant φ := hdom
    obtain ⟨U, hU, hbound⟩ :=
      exists_dense_open_fiber_dimension_pow_add_le_of_dominant d a b ha
    exact ⟨U, hU, 1, one_ne_zero, 0, fun n _ q _ => hbound n q⟩
  · obtain ⟨g, hg, hab⟩ := exists_polynomial_relation_of_not_dominant a b hdom
    obtain ⟨c, hc, N, hbound⟩ :=
      exists_fiber_dimension_pow_add_le_of_polynomial_relation d a b g hg hab ha
    refine ⟨⊤, ?_, c, hc, N, ?_⟩
    · simp
    · intro n hn q hcq
      exact (topologicalKrullDim_comp_fiber_le_of_isInducing
        (⊤ : (Spec (.of S)).Opens).ι (specMapAeval (a ^ n + b))
        (⊤ : (Spec (.of S)).Opens).ι.isOpenEmbedding.isInducing q).trans
        (hbound n hn q hcq)

/-- For an injective map of domains, the eventual fibre bound holds over a
nonempty open part of the base. -/
private lemma exists_open_eventually_fiber_dimension_le_of_domain
    {R S : Type u} [CommRing R] [CommRing S] [IsDomain R] [IsDomain S]
    [Algebra R S] [Algebra.FiniteType R S] [IsNoetherianRing S]
    (hinj : Function.Injective (algebraMap R S))
    (d : ℕ) (a b : S)
    (ha : ∀ q : Spec (.of (Polynomial R)),
      topologicalKrullDim ((specMapAeval a).fiber q) ≤ (d : WithBot ℕ∞)) :
    ∃ c : R, c ≠ 0 ∧ ∃ N : ℕ, ∃ V : Set (Spec (.of R)),
      IsOpen V ∧ V.Nonempty ∧
      ∀ n ≥ N, ∀ q : Spec (.of (Polynomial R)),
        (Spec.map (CommRingCat.ofHom (Polynomial.C : R →+* Polynomial R))) q ∈ V →
        Polynomial.C c ∉ q.asIdeal →
        topologicalKrullDim ((specMapAeval (a ^ n + b)).fiber q) ≤
          (d : WithBot ℕ∞) := by
  let s : Spec (.of S) ⟶ Spec (.of R) :=
    Spec.map (CommRingCat.ofHom (algebraMap R S))
  let π : Spec (.of (Polynomial R)) ⟶ Spec (.of R) :=
    Spec.map (CommRingCat.ofHom (Polynomial.C : R →+* Polynomial R))
  have : IsDominant s := isDominant_specMap_of_injective _ hinj
  have : LocallyOfFiniteType s := locallyOfFiniteType_specMap_algebraMap R S
  have : QuasiCompact s := inferInstance
  have : TopologicalSpace.NoetherianSpace (Spec (.of S)) := inferInstance
  obtain ⟨U, hUdense, c, hc, N, hN⟩ :=
    exists_dense_open_eventually_fiber_dimension_pow_add_le d a b ha
  obtain ⟨V, hVopen, hVne, hVnd⟩ :=
    exists_open_nowhereDense_compl_fibers s U hUdense
  refine ⟨c, hc, N, V, hVopen, hVne, ?_⟩
  intro n hn q hq hcq
  have : LocallyOfFiniteType (specMapAeval (R := R) (a ^ n + b)) :=
    locallyOfFiniteType_specMapAeval (a ^ n + b)
  have hs_n : specMapAeval (R := R) (a ^ n + b) ≫ π = s :=
    specMapAeval_comp_polynomialSpecMap (a ^ n + b)
  have hstructure : ∀ p : Spec (.of R),
      topologicalKrullDim
        (((specMapAeval (a ^ n + b)) ≫ π).fiber p) ≤
          ((d + 1 : ℕ) : WithBot ℕ∞) := by
    rw [specMapAeval_comp_polynomialSpecMap]
    exact fiber_dimension_structure_le_add_one d a ha
  exact fiber_dimension_le_of_open_nowhereDense
    (specMapAeval (a ^ n + b)) π U d hstructure q (hN n hn q hcq)
    (by rw [hs_n]; exact hVnd (π q) hq)

/-- The generic bound for an injective map of domains holds above one nonempty
principal open of the base. -/
private lemma exists_principal_open_eventually_fiber_dimension_le_of_domain
    {R S : Type u} [CommRing R] [CommRing S] [IsDomain R] [IsDomain S]
    [Algebra R S] [Algebra.FiniteType R S] [IsNoetherianRing S]
    (hinj : Function.Injective (algebraMap R S))
    (d : ℕ) (a b : S)
    (ha : ∀ q : Spec (.of (Polynomial R)),
      topologicalKrullDim ((specMapAeval a).fiber q) ≤ (d : WithBot ℕ∞)) :
    ∃ t : R, t ≠ 0 ∧ ∃ N : ℕ, ∀ n ≥ N,
      ∀ q : Spec (.of (Polynomial R)),
        Polynomial.C t ∉ q.asIdeal →
          topologicalKrullDim ((specMapAeval (a ^ n + b)).fiber q) ≤
            (d : WithBot ℕ∞) := by
  obtain ⟨c, hc, N, V, hVopen, hVne, hN⟩ :=
    exists_open_eventually_fiber_dimension_le_of_domain hinj d a b ha
  obtain ⟨p, hp⟩ := hVne
  obtain ⟨W, ⟨B, ⟨r, rfl⟩, hBW⟩, hpr, hW⟩ :=
    PrimeSpectrum.isBasis_basic_opens.exists_subset_of_mem_open hp hVopen
  rw [← hBW] at hpr hW
  have hr : r ≠ 0 := by
    intro hr0
    rw [hr0] at hpr
    change 0 ∉ p.asIdeal at hpr
    exact hpr (Ideal.zero_mem _)
  refine ⟨c * r, mul_ne_zero hc hr, N, ?_⟩
  intro n hn q htq
  let π : Spec (.of (Polynomial R)) ⟶ Spec (.of R) :=
    Spec.map (CommRingCat.ofHom (Polynomial.C : R →+* Polynomial R))
  have hcr : Polynomial.C c * Polynomial.C r ∉ q.asIdeal := by
    simpa only [map_mul] using htq
  have hcq : Polynomial.C c ∉ q.asIdeal := by
    intro hcq
    exact hcr (Ideal.mul_mem_right _ _ hcq)
  have hrq : Polynomial.C r ∉ q.asIdeal := by
    intro hrq
    exact hcr (Ideal.mul_mem_left _ _ hrq)
  have hπ : π q ∈ PrimeSpectrum.basicOpen r := by
    show r ∉ (π q).asIdeal
    exact hrq
  have hpV : π q ∈ V := hW hπ
  exact hN n hn q hpV hcq

/-- Over a field extension, a transcendental element has at most one exponent for which a
fixed additive perturbation becomes algebraic. This is the field-level bridge used in the
dominant-locus argument. -/
private lemma algebraic_pow_add_at_most_one
    {k K : Type*} [Field k] [CommRing K] [IsDomain K] [Algebra k K] (a b : K)
    (ha : Transcendental k a) :
    ∀ x y : {n : ℕ // IsAlgebraic k (a ^ n + b)}, x = y := by
  intro x y
  apply Subtype.ext
  by_contra hxy
  have hne : x.val ≠ y.val := hxy
  let p : Polynomial k := Polynomial.X ^ x.val - Polynomial.X ^ y.val
  have hpdeg : p.natDegree ≠ 0 := by
    by_cases hnm : x.val < y.val
    · have hdeg : ((Polynomial.X : Polynomial k) ^ x.val).natDegree <
          ((Polynomial.X : Polynomial k) ^ y.val).natDegree := by simp [hnm]
      rw [Polynomial.natDegree_sub_eq_right_of_natDegree_lt hdeg]
      exact Nat.ne_of_gt (by omega)
    · have hmn : y.val < x.val := Nat.lt_of_le_of_ne (Nat.le_of_not_gt hnm) (Ne.symm hne)
      have hdeg : ((Polynomial.X : Polynomial k) ^ y.val).natDegree <
          ((Polynomial.X : Polynomial k) ^ x.val).natDegree := by simp [hmn]
      rw [Polynomial.natDegree_sub_eq_left_of_natDegree_lt hdeg]
      exact Nat.ne_of_gt (by omega)
  have hpne : p ≠ 0 := by
    intro hp0
    apply hpdeg
    simp [hp0]
  have hplc : p.leadingCoeff ∈ nonZeroDivisors k :=
    mem_nonZeroDivisors_iff_ne_zero.mpr (Polynomial.leadingCoeff_ne_zero.mpr hpne)
  have hsub : IsAlgebraic k ((a ^ x.val + b) - (a ^ y.val + b)) :=
    x.property.sub y.property
  have heq : Polynomial.aeval a p = (a ^ x.val + b) - (a ^ y.val + b) := by
    simp [p, map_sub]
  exact (ha.aeval p hpdeg hplc) (heq ▸ hsub)

/-- For a fixed field extension, all sufficiently large perturbations of a transcendental
element remain transcendental. -/
private lemma eventually_transcendental_pow_add
    {k K : Type*} [Field k] [CommRing K] [IsDomain K] [Algebra k K] (a b : K)
    (ha : Transcendental k a) :
    ∃ n₀ : ℕ, ∀ n : ℕ, n₀ ≤ n → Transcendental k (a ^ n + b) := by
  classical
  by_cases hex : ∃ n : ℕ, IsAlgebraic k (a ^ n + b)
  · obtain ⟨m, hm⟩ := hex
    refine ⟨m + 1, ?_⟩
    intro n hn
    show ¬ IsAlgebraic k (a ^ n + b)
    intro h
    have heq := algebraic_pow_add_at_most_one a b ha ⟨n, h⟩ ⟨m, hm⟩
    simp only [Subtype.mk.injEq] at heq
    omega
  · refine ⟨0, ?_⟩
    intro n hn
    show ¬ IsAlgebraic k (a ^ n + b)
    intro h
    exact hex ⟨n, h⟩

/-- Finitely many eventual natural-number bounds admit one common threshold. -/
private lemma eventually_forall_finite {ι : Type*} [Finite ι]
    (P : ι → ℕ → Prop)
    (h : ∀ i, ∃ N : ℕ, ∀ n ≥ N, P i n) :
    ∃ N : ℕ, ∀ n ≥ N, ∀ i, P i n := by
  classical
  let : Fintype ι := Fintype.ofFinite ι
  have hs : ∀ s : Finset ι, ∃ N : ℕ, ∀ n ≥ N, ∀ i ∈ s, P i n := by
    intro s
    induction s using Finset.induction_on with
    | empty => exact ⟨0, by simp⟩
    | @insert i s hi ih =>
      obtain ⟨N, hN⟩ := ih
      obtain ⟨M, hM⟩ := h i
      refine ⟨max N M, ?_⟩
      intro n hn j hj
      rw [Finset.mem_insert] at hj
      rcases hj with rfl | hj
      · exact hM n ((le_max_right N M).trans hn)
      · exact hN n ((le_max_left N M).trans hn) j hj
  obtain ⟨N, hN⟩ := hs Finset.univ
  exact ⟨N, fun n hn i => hN n hn i (Finset.mem_univ i)⟩

/-- A common exponent bound can be chosen for a finite family of field extensions and
transcendental elements. This is the finite-component form of the preceding bridge. -/
private lemma eventually_transcendental_pow_add_finite
    {k K ι : Type*} [Field k] [Field K] [Algebra k K] [Finite ι]
    (a b : ι → K) (ha : ∀ i, Transcendental k (a i)) :
    ∃ n₀ : ℕ, ∀ n : ℕ, n₀ ≤ n → ∀ i, Transcendental k (a i ^ n + b i) :=
  eventually_forall_finite (fun i n => Transcendental k (a i ^ n + b i)) fun i =>
    eventually_transcendental_pow_add (a i) (b i) (ha i)

/-- Evaluation at a transcendental element of a domain is flat over the polynomial ring
in one variable over a field. -/
private lemma flat_specMapAeval_of_transcendental
    {k S : Type u} [Field k] [CommRing S] [IsDomain S] [Algebra k S]
    (a : S) (ha : Transcendental k a) : Flat (specMapAeval (R := k) a) := by
  let : Algebra (Polynomial k) S := (Polynomial.aeval (R := k) a).toRingHom.toAlgebra
  have : Module.IsTorsionFree (Polynomial k) S :=
    Module.isTorsionFree_iff_algebraMap_injective.mpr (transcendental_iff_injective.mp ha)
  apply Flat.SpecMap_iff.mpr
  show (algebraMap (Polynomial k) S).Flat
  exact RingHom.flat_algebraMap_iff.mpr inferInstance

/-- When the first coordinate is algebraic over a field, every perturbation has the
required dimension bound: the dimension of the whole source is already bounded. -/
private lemma fiber_dimension_pow_add_le_of_isAlgebraic
    {k S : Type u} [Field k] [CommRing S] [Algebra k S]
    (d : ℕ) (a b : S) (halg : IsAlgebraic k a)
    (ha : ∀ q : Spec (.of (Polynomial k)),
      topologicalKrullDim ((specMapAeval a).fiber q) ≤ (d : WithBot ℕ∞))
    (n : ℕ) (q : Spec (.of (Polynomial k))) :
    topologicalKrullDim ((specMapAeval (a ^ n + b)).fiber q) ≤
      (d : WithBot ℕ∞) := by
  have hd := topologicalKrullDim_le_of_isIntegral (R := k) (k := k) a
    halg.isIntegral _ ha
  have hle := (Scheme.Hom.isEmbedding
    ((specMapAeval (a ^ n + b)).fiberι q)).isInducing.topologicalKrullDim_le
  exact hle.trans hd

/-- The assertion for a domain of finite type over a field. -/
private lemma eventually_fiber_dimension_le_of_pow_add_of_field_of_isDomain
    {k S : Type u} [Field k] [CommRing S] [IsDomain S] [Algebra k S]
    [Algebra.FiniteType k S] (d : ℕ) (a b : S)
    (ha : ∀ q : Spec (.of (Polynomial k)),
      topologicalKrullDim ((specMapAeval a).fiber q) ≤ (d : WithBot ℕ∞)) :
    ∃ N : ℕ, ∀ n ≥ N, ∀ q : Spec (.of (Polynomial k)),
      topologicalKrullDim ((specMapAeval (a ^ n + b)).fiber q) ≤ (d : WithBot ℕ∞) := by
  by_cases h : IsAlgebraic k a
  · exact ⟨0, fun n _ q => fiber_dimension_pow_add_le_of_isAlgebraic d a b h ha n q⟩
  · obtain ⟨N, hN⟩ := eventually_transcendental_pow_add a b h
    refine ⟨N, fun n hn q => ?_⟩
    have := flat_specMapAeval_of_transcendental (a ^ n + b) (hN n hn)
    exact fiber_dimension_evaluation_le_of_flat d a _ ha q

/-- Eventual bounds on two complementary parts of an index set combine into
one uniform eventual bound. -/
private lemma eventually_forall_of_cover
    {α : Type*} (P : ℕ → α → Prop) (U : Set α)
    (hU : ∃ N : ℕ, ∀ n ≥ N, ∀ x ∈ U, P n x)
    (hZ : ∃ N : ℕ, ∀ n ≥ N, ∀ x ∉ U, P n x) :
    ∃ N : ℕ, ∀ n ≥ N, ∀ x, P n x := by
  obtain ⟨N, hN⟩ := hU
  obtain ⟨M, hM⟩ := hZ
  refine ⟨max N M, fun n hn x => ?_⟩
  by_cases hx : x ∈ U
  · exact hN n ((le_max_left N M).trans hn) x hx
  · exact hM n ((le_max_right N M).trans hn) x hx

/-- A common bound on the finitely many minimal-prime components bounds the fibres
of the whole source. -/
private lemma eventually_fiber_dimension_le_of_minimalPrimes
    {R S : Type u} [CommRing R] [CommRing S] [Algebra R S]
    [IsNoetherianRing S] (d : ℕ) (a b : S)
    (h : ∀ i : minimalPrimes S, ∃ N : ℕ, ∀ n ≥ N,
      ∀ q : Spec (.of (Polynomial R)),
        topologicalKrullDim
          ((Spec.map (CommRingCat.ofHom (Ideal.Quotient.mk i.1)) ≫
            specMapAeval (a ^ n + b)).fiber q) ≤ (d : WithBot ℕ∞)) :
    ∃ N : ℕ, ∀ n ≥ N, ∀ q : Spec (.of (Polynomial R)),
      topologicalKrullDim ((specMapAeval (a ^ n + b)).fiber q) ≤
        (d : WithBot ℕ∞) := by
  classical
  let ι := minimalPrimes S
  let : Finite ι := (minimalPrimes.finite_of_isNoetherianRing S).to_subtype
  let W : ι → Scheme.{u} := fun i => Spec (.of (S ⧸ i.1))
  let g : ∀ i : ι, W i ⟶ Spec (.of S) := fun i =>
    Spec.map (CommRingCat.ofHom (Ideal.Quotient.mk i.1))
  obtain ⟨N, hN⟩ := eventually_forall_finite
    (fun i n => ∀ q : Spec (.of (Polynomial R)),
      topologicalKrullDim (((g i) ≫ specMapAeval (a ^ n + b)).fiber q) ≤
        (d : WithBot ℕ∞)) h
  refine ⟨N, fun n hn => ?_⟩
  apply fiber_dimension_le_of_finite_closed_cover W g (specMapAeval (a ^ n + b))
  · intro i
    have : IsClosedImmersion (g i) := by
      show IsClosedImmersion (Spec.map (CommRingCat.ofHom (Ideal.Quotient.mk i.1)))
      exact IsClosedImmersion.spec_of_surjective _ Ideal.Quotient.mk_surjective
    exact this.isClosedEmbedding
  · ext q
    constructor
    · intro _; trivial
    · intro _
      let : q.asIdeal.IsPrime := q.isPrime
      obtain ⟨p, hp, hpq⟩ := Ideal.exists_minimalPrimes_le (J := q.asIdeal) bot_le
      have hq : q ∈ Set.range (g ⟨p, hp⟩) := by
        show q ∈ Set.range (PrimeSpectrum.comap (Ideal.Quotient.mk p))
        rw [range_comap_of_surjective (S ⧸ p) (Ideal.Quotient.mk p)
          Ideal.Quotient.mk_surjective, Ideal.mk_ker]
        exact (PrimeSpectrum.mem_zeroLocus _ _).mpr hpq
      exact Set.mem_iUnion.mpr ⟨⟨p, hp⟩, hq⟩
  · exact fun i q => hN n hn i q

/-- The field case follows from the domain case on the finitely many irreducible
components of the source. -/
private lemma eventually_fiber_dimension_le_of_pow_add_of_field
    {k S : Type u} [Field k] [CommRing S] [Algebra k S]
    [Algebra.FiniteType k S] (d : ℕ) (a b : S)
    (ha : ∀ q : Spec (.of (Polynomial k)),
      topologicalKrullDim ((specMapAeval a).fiber q) ≤ (d : WithBot ℕ∞)) :
    ∃ N : ℕ, ∀ n ≥ N, ∀ q : Spec (.of (Polynomial k)),
      topologicalKrullDim ((specMapAeval (a ^ n + b)).fiber q) ≤
        (d : WithBot ℕ∞) := by
  classical
  let : IsNoetherianRing S := Algebra.FiniteType.isNoetherianRing k S
  let ι := minimalPrimes S
  let : Finite ι := (minimalPrimes.finite_of_isNoetherianRing S).to_subtype
  let W : ι → Scheme.{u} := fun i => Spec (.of (S ⧸ i.1))
  let g : ∀ i : ι, W i ⟶ Spec (.of S) := fun i =>
    Spec.map (CommRingCat.ofHom (Ideal.Quotient.mk i.1))
  have hN : ∀ i : ι, ∃ N : ℕ, ∀ n ≥ N, ∀ q : Spec (.of (Polynomial k)),
      topologicalKrullDim (((g i) ≫ specMapAeval (a ^ n + b)).fiber q) ≤
        (d : WithBot ℕ∞) := by
    intro i
    have : i.1.IsPrime := i.2.1.1
    have : IsDomain (S ⧸ i.1) := inferInstance
    have : Algebra.FiniteType k (S ⧸ i.1) :=
      Algebra.FiniteType.of_surjective (Ideal.Quotient.mkₐ k i.1)
        (Ideal.Quotient.mkₐ_surjective k i.1)
    let φ : S →ₐ[k] S ⧸ i.1 := Ideal.Quotient.mkₐ k i.1
    have hi : ∀ q : Spec (.of (Polynomial k)),
        topologicalKrullDim ((specMapAeval (φ a)).fiber q) ≤
          (d : WithBot ℕ∞) := by
      intro q
      exact (fiber_dimension_evaluation_le_of_surjective φ
        (Ideal.Quotient.mkₐ_surjective k i.1) a q).trans (ha q)
    obtain ⟨N, hN⟩ :=
      eventually_fiber_dimension_le_of_pow_add_of_field_of_isDomain d (φ a) (φ b) hi
    refine ⟨N, fun n hn q => ?_⟩
    show topologicalKrullDim
      ((Spec.map (CommRingCat.ofHom φ.toRingHom) ≫
        specMapAeval (a ^ n + b)).fiber q) ≤ _
    rw [specMap_comp_specMapAeval φ, map_add, map_pow]
    exact hN n hn q
  exact eventually_fiber_dimension_le_of_minimalPrimes d a b hN

/-- If the source is finite over the base, every evaluation fibre has dimension
at most zero. -/
private lemma fiber_dimension_le_of_finite_algebra
    {R S : Type u} [CommRing R] [CommRing S] [Algebra R S]
    [Module.Finite R S] (a : S)
    (q : Spec (.of (Polynomial R))) :
    topologicalKrullDim ((specMapAeval a).fiber q) ≤ (0 : WithBot ℕ∞) := by
  have hcomp : (Polynomial.aeval (R := R) a).toRingHom.comp Polynomial.C =
      algebraMap R S := by
    ext r
    simp
  have hfinite : ((Polynomial.aeval (R := R) a).toRingHom).Finite := by
    apply RingHom.Finite.of_comp_finite (f := Polynomial.C)
    rw [hcomp]
    exact RingHom.finite_algebraMap.mpr inferInstance
  have : LocallyQuasiFinite (specMapAeval a) :=
    (HasRingHomProperty.Spec_iff (P := @LocallyQuasiFinite)).mpr
      (RingHom.QuasiFinite.of_finite hfinite)
  have : IsLocallyArtinian ((specMapAeval a).fiber q) := inferInstance
  have : DiscreteTopology ((specMapAeval a).fiber q) := inferInstance
  exact topologicalKrullDim_zero_of_discreteTopology _

/-- A finite algebra has a uniform zero-dimensional bound for every perturbation. -/
private lemma eventually_fiber_dimension_le_of_finite_algebra
    {R S : Type u} [CommRing R] [CommRing S] [Algebra R S]
    [Module.Finite R S] (d : ℕ) (a b : S) :
    ∃ N : ℕ, ∀ n ≥ N, ∀ q : Spec (.of (Polynomial R)),
      topologicalKrullDim ((specMapAeval (a ^ n + b)).fiber q) ≤
        (d : WithBot ℕ∞) := by
  refine ⟨0, fun n _ q => ?_⟩
  exact (fiber_dimension_le_of_finite_algebra (a ^ n + b) q).trans (by simp)

/-- An embedding containing a whole fibre preserves its dimension. -/
private lemma topologicalKrullDim_comp_fiber_eq_of_range
    {W X Y : Scheme.{u}} (g : W ⟶ X) (f : X ⟶ Y)
    (hg : Topology.IsEmbedding g) (y : Y)
    (h : f ⁻¹' {y} ⊆ Set.range g) :
    topologicalKrullDim ((g ≫ f).fiber y) = topologicalKrullDim (f.fiber y) := by
  rw [((g ≫ f).fiberHomeo y).isHomeomorph.topologicalKrullDim_eq,
    (f.fiberHomeo y).isHomeomorph.topologicalKrullDim_eq]
  let m : (g ≫ f) ⁻¹' {y} → f ⁻¹' {y} := fun w => ⟨g w, w.property⟩
  have hm : Topology.IsEmbedding m :=
    Topology.IsEmbedding.subtypeVal.of_comp_iff.mp
      (hg.comp Topology.IsEmbedding.subtypeVal)
  have hs : Function.Surjective m := by
    intro x
    obtain ⟨w, hw⟩ := h x.property
    refine ⟨⟨w, ?_⟩, Subtype.ext hw⟩
    show f (g w) = y
    rw [hw]
    exact x.property
  exact (hm.toHomeomorphOfSurjective hs).isHomeomorph.topologicalKrullDim_eq

/-- Over the vanishing locus of a coefficient, quotienting by that coefficient
preserves each evaluation fibre. -/
private lemma fiber_dimension_evaluation_quotient_eq_of_mem
    {R S : Type u} [CommRing R] [CommRing S] [Algebra R S]
    (c : R) (a : S) (q : Spec (.of (Polynomial R)))
    (hc : Polynomial.C c ∈ q.asIdeal) :
    topologicalKrullDim ((specMapAeval (R := R)
      (Ideal.Quotient.mk (Ideal.span {algebraMap R S c}) a)).fiber q) =
      topologicalKrullDim ((specMapAeval (R := R) a).fiber q) := by
  let J : Ideal S := Ideal.span {algebraMap R S c}
  let φ : S →ₐ[R] S ⧸ J := Ideal.Quotient.mkₐ R J
  show topologicalKrullDim ((specMapAeval (R := R) (φ a)).fiber q) = _
  rw [← specMap_comp_specMapAeval φ a]
  apply topologicalKrullDim_comp_fiber_eq_of_range
  · exact (PrimeSpectrum.isClosedEmbedding_comap_of_surjective _ _
      Ideal.Quotient.mk_surjective).isEmbedding
  · intro x hx
    show x ∈ Set.range (PrimeSpectrum.comap (Ideal.Quotient.mk J))
    rw [range_comap_of_surjective (S ⧸ J) _ Ideal.Quotient.mk_surjective, Ideal.mk_ker]
    apply (PrimeSpectrum.mem_zeroLocus _ _).mpr
    apply Ideal.span_le.mpr
    intro s hs
    obtain rfl : s = algebraMap R S c := Set.mem_singleton_iff.mp hs
    have hx' : specMapAeval a x = q := hx
    rw [← hx'] at hc
    change Polynomial.aeval a (Polynomial.C c) ∈ x.asIdeal at hc
    simpa using hc

/-- A surjection strictly enlarges its kernel after quotienting by a nonzero ideal. -/
private lemma ker_lt_ker_quotient_comp
    {S T : Type*} [CommRing S] [CommRing T]
    (φ : S →+* T) (hφ : Function.Surjective φ) (J : Ideal T) (hJ : J ≠ ⊥) :
    RingHom.ker φ < RingHom.ker ((Ideal.Quotient.mk J).comp φ) := by
  apply lt_of_le_of_ne
  · intro s hs
    show Ideal.Quotient.mk J (φ s) = 0
    rw [show φ s = 0 from hs, map_zero]
  · intro heq
    apply hJ
    apply le_bot_iff.mp
    intro t ht
    obtain ⟨s, rfl⟩ := hφ t
    have hs : s ∈ RingHom.ker ((Ideal.Quotient.mk J).comp φ) :=
      Ideal.Quotient.eq_zero_iff_mem.mpr ht
    rw [← heq] at hs
    exact hs

/-- Over a Noetherian base, a domain source is controlled by its proper closed
subschemes and the generic principal-open bound. -/
private lemma eventually_fiber_dimension_le_of_domain_of_quotients
    {R S : Type u} [CommRing R] [CommRing S] [Algebra R S]
    [IsNoetherianRing R] [Algebra.FiniteType R S] [IsDomain S]
    (d : ℕ) (a b : S)
    (ha : ∀ q : Spec (.of (Polynomial R)),
      topologicalKrullDim ((specMapAeval a).fiber q) ≤ (d : WithBot ℕ∞))
    (hquot : ∀ J : Ideal S, J ≠ ⊥ →
      ∃ N : ℕ, ∀ n ≥ N, ∀ q : Spec (.of (Polynomial R)),
        topologicalKrullDim ((specMapAeval (R := R)
          ((Ideal.Quotient.mk J a) ^ n + Ideal.Quotient.mk J b)).fiber q) ≤
            (d : WithBot ℕ∞)) :
    ∃ N : ℕ, ∀ n ≥ N, ∀ q : Spec (.of (Polynomial R)),
      topologicalKrullDim ((specMapAeval (a ^ n + b)).fiber q) ≤
        (d : WithBot ℕ∞) := by
  let A := (algebraMap R S).range
  let : Algebra R A := (algebraMap R S).rangeRestrict.toAlgebra
  let : Algebra A S := (algebraMap R S).range.subtype.toAlgebra
  have : IsScalarTower R A S := IsScalarTower.of_algebraMap_eq fun _ => rfl
  have hRA : Function.Surjective (algebraMap R A) :=
    (algebraMap R S).rangeRestrict_surjective
  have hAS : Function.Injective (algebraMap A S) := Subtype.val_injective
  have : Algebra.FiniteType A S := Algebra.FiniteType.of_restrictScalars_finiteType R A S
  have : IsNoetherianRing S := Algebra.FiniteType.isNoetherianRing R S
  have haA : ∀ q : Spec (.of (Polynomial A)),
      topologicalKrullDim ((specMapAeval (R := A) a).fiber q) ≤
        (d : WithBot ℕ∞) := by
    intro q
    rw [fiber_dimension_evaluation_eq_of_surjective_base hRA]
    exact ha _
  obtain ⟨t, ht, N, hN⟩ :=
    exists_principal_open_eventually_fiber_dimension_le_of_domain hAS d a b haA
  let J : Ideal S := Ideal.span {algebraMap A S t}
  have hJ : J ≠ ⊥ := by
    intro h
    have hz : algebraMap A S t = 0 := by
      have hm := Ideal.subset_span (Set.mem_singleton (algebraMap A S t))
      change algebraMap A S t ∈ J at hm
      simpa [h] using hm
    exact ht (hAS (hz.trans (map_zero _).symm))
  obtain ⟨M, hM⟩ := hquot J hJ
  apply eventually_fiber_dimension_le_of_surjective_base hRA d a b
  refine ⟨max N M, fun n hn q => ?_⟩
  by_cases hq : Polynomial.C t ∈ q.asIdeal
  · rw [← fiber_dimension_evaluation_quotient_eq_of_mem t (a ^ n + b) q hq]
    have hbound := hM n ((le_max_right N M).trans hn)
    have hdim := hbound (Spec.map (CommRingCat.ofHom
      (Polynomial.mapRingHom (algebraMap R A))) q)
    rw [← fiber_dimension_evaluation_eq_of_surjective_base (S := S ⧸ J) hRA] at hdim
    show topologicalKrullDim ((specMapAeval (R := A)
      (Ideal.Quotient.mk J (a ^ n + b))).fiber q) ≤ _
    rw [map_add, map_pow]
    exact hdim
  · exact hN n ((le_max_left N M).trans hn) q hq

/-- Noetherian induction on the closed subsets of the source makes the
principal-open eventual bounds uniform. -/
private lemma eventually_fiber_dimension_le_of_pow_add_of_noetherian
    {R S : Type u} [CommRing R] [CommRing S] [Algebra R S]
    [IsNoetherianRing R] [Algebra.FiniteType R S]
    (d : ℕ) (a b : S)
    (ha : ∀ q : Spec (.of (Polynomial R)),
      topologicalKrullDim ((specMapAeval a).fiber q) ≤ (d : WithBot ℕ∞)) :
    ∃ N : ℕ, ∀ n ≥ N, ∀ q : Spec (.of (Polynomial R)),
      topologicalKrullDim ((specMapAeval (a ^ n + b)).fiber q) ≤
        (d : WithBot ℕ∞) := by
  have : IsNoetherianRing S := Algebra.FiniteType.isNoetherianRing R S
  have H : ∀ I : Ideal S, ∀ (T : Type u) [CommRing T] [Algebra R T]
      (φ : S →ₐ[R] T), Function.Surjective φ → RingHom.ker φ.toRingHom = I →
      ∀ a b : T,
      (∀ q : Spec (.of (Polynomial R)),
        topologicalKrullDim ((specMapAeval a).fiber q) ≤ (d : WithBot ℕ∞)) →
      ∃ N : ℕ, ∀ n ≥ N, ∀ q : Spec (.of (Polynomial R)),
        topologicalKrullDim ((specMapAeval (a ^ n + b)).fiber q) ≤
          (d : WithBot ℕ∞) := by
    intro I
    induction I using
      (wellFounded_gt : WellFounded ((· > ·) : Ideal S → Ideal S → Prop)).induction with
    | h I ih =>
      intro T _ _ φ hφ hker a b ha
      have : Algebra.FiniteType R T := Algebra.FiniteType.of_surjective φ hφ
      have : IsNoetherianRing T := Algebra.FiniteType.isNoetherianRing R T
      apply eventually_fiber_dimension_le_of_minimalPrimes d a b
      intro p
      have : p.1.IsPrime := p.2.1.1
      let ψ : T →ₐ[R] T ⧸ p.1 := Ideal.Quotient.mkₐ R p.1
      have hψ : Function.Surjective ψ := Ideal.Quotient.mk_surjective
      have : Algebra.FiniteType R (T ⧸ p.1) := Algebra.FiniteType.of_surjective ψ hψ
      have hpa : ∀ q : Spec (.of (Polynomial R)),
          topologicalKrullDim ((specMapAeval (ψ a)).fiber q) ≤
            (d : WithBot ℕ∞) := fun q =>
        (fiber_dimension_evaluation_le_of_surjective ψ hψ a q).trans (ha q)
      obtain ⟨N, hN⟩ := eventually_fiber_dimension_le_of_domain_of_quotients d
        (ψ a) (ψ b) hpa (fun J hJ => by
          let χ : (T ⧸ p.1) →ₐ[R] (T ⧸ p.1) ⧸ J := Ideal.Quotient.mkₐ R J
          have hχ : Function.Surjective χ := Ideal.Quotient.mk_surjective
          have hle : RingHom.ker φ.toRingHom ≤ RingHom.ker (ψ.comp φ).toRingHom := by
            intro s hs
            show ψ (φ s) = 0
            rw [show φ s = 0 from hs, map_zero]
          have hlt : I < RingHom.ker (χ.comp (ψ.comp φ)).toRingHom := by
            rw [← hker]
            exact hle.trans_lt (ker_lt_ker_quotient_comp (ψ.comp φ).toRingHom
              (hψ.comp hφ) J hJ)
          have hqa : ∀ q : Spec (.of (Polynomial R)),
              topologicalKrullDim ((specMapAeval (χ (ψ a))).fiber q) ≤
                (d : WithBot ℕ∞) := fun q =>
            (fiber_dimension_evaluation_le_of_surjective χ hχ (ψ a) q).trans (hpa q)
          exact ih _ hlt _ (χ.comp (ψ.comp φ)) (hχ.comp (hψ.comp hφ)) rfl
            (χ (ψ a)) (χ (ψ b)) hqa)
      refine ⟨N, fun n hn q => ?_⟩
      show topologicalKrullDim ((Spec.map (CommRingCat.ofHom ψ.toRingHom) ≫
        specMapAeval (a ^ n + b)).fiber q) ≤ _
      rw [specMap_comp_specMapAeval ψ, map_add, map_pow]
      exact hN n hn q
  exact H _ S (AlgHom.id R S) Function.surjective_id rfl a b ha

open CategoryTheory.Limits

/-- The diagram of commutative rings `i ↦ A i` given by a monotone family of subrings of `R`,
with the inclusions as transition maps. -/
def subringDiagram {I : Type u} [Preorder I] {R : Type u} [CommRing R]
    (A : I → Subring R) (hA : Monotone A) : I ⥤ CommRingCat.{u} where
  obj i := .of (A i)
  map f := CommRingCat.ofHom (Subring.inclusion (hA f.le))

/-- The cocone over `subringDiagram A hA` with vertex `R`, given by the inclusions of the
subrings `A i`. -/
def subringCocone {I : Type u} [Preorder I] {R : Type u} [CommRing R]
    (A : I → Subring R) (hA : Monotone A) : CategoryTheory.Limits.Cocone (subringDiagram A hA) where
  pt := .of R
  ι := { app := fun i ↦ CommRingCat.ofHom (A i).subtype }

open CategoryTheory.Limits in
/-- A directed family of subrings of `R` whose union is `R` exhibits `R` as the colimit of
the subrings. -/
noncomputable def subringCoconeIsColimit {I : Type u} [Preorder I]
    [IsDirectedOrder I] [Nonempty I] {R : Type u} [CommRing R]
    (A : I → Subring R) (hA : Monotone A) (h : ∀ r : R, ∃ i, r ∈ A i) :
    IsColimit (subringCocone A hA) := by
  let := reflectsColimit_of_reflectsIsomorphisms (subringDiagram A hA) (forget CommRingCat)
  apply isColimitOfReflects (forget CommRingCat)
  apply Types.FilteredColimit.isColimitOf'
  · intro r
    obtain ⟨i, hi⟩ := h r
    exact ⟨i, ⟨r, hi⟩, rfl⟩
  · intro i x y hxy
    exact ⟨i, 𝟙 i, Subtype.ext hxy⟩

open CategoryTheory.Limits in
/-- For a directed family of subrings of `R` whose union is `R`, `Spec R` is the limit of the
schemes `Spec (A i)`. -/
noncomputable def subringSpecIsLimit {I : Type u} [Preorder I]
    [IsDirectedOrder I] [Nonempty I] {R : Type u} [CommRing R]
    (A : I → Subring R) (hA : Monotone A) (h : ∀ r : R, ∃ i, r ∈ A i) :
    IsLimit (Scheme.Spec.mapCone (subringCocone A hA).op) :=
  isLimitOfPreserves Scheme.Spec (subringCoconeIsColimit A hA h).op

/-- The subring of `S` generated by `f '' i ∪ s`, for a finite set `i` of elements of `R`. -/
noncomputable abbrev coefficientSubalgebra {R S : Type*} [CommRing R] [CommRing S]
    (f : R →+* S) (s : Set S) (i : Finset R) : Subalgebra ℤ S :=
  Algebra.adjoin ℤ (f '' (i : Set R) ∪ s)

/-- `coefficientSubalgebra f s i` is monotone in the finite set `i`. -/
theorem coefficientSubalgebra_mono {R S : Type*} [CommRing R] [CommRing S]
    (f : R →+* S) (s : Set S) : Monotone (coefficientSubalgebra f s) :=
  fun _ _ hij ↦ Algebra.adjoin_mono (Set.union_subset_union (Set.image_mono hij) le_rfl)

/-- If `s` is finite, then `coefficientSubalgebra f s i` is a finitely generated
`ℤ`-algebra. -/
theorem coefficientSubalgebra_fg {R S : Type*} [CommRing R] [CommRing S]
    (f : R →+* S) {s : Set S} (hs : s.Finite) (i : Finset R) :
    (coefficientSubalgebra f s i).FG :=
  Subalgebra.fg_def.mpr ⟨f '' (i : Set R) ∪ s, (i.finite_toSet.image f).union hs, rfl⟩

/-- The restriction of `f` to a map from the subring of `R` generated by `i` to
`coefficientSubalgebra f s i`. -/
noncomputable def coefficientMap {R S : Type*} [CommRing R] [CommRing S]
    (f : R →+* S) (s : Set S) (i : Finset R) :
    coefficientSubalgebra (RingHom.id R) ∅ i →ₐ[ℤ] coefficientSubalgebra f s i := by
  let A := coefficientSubalgebra (RingHom.id R) ∅ i
  let B := coefficientSubalgebra f s i
  have h : A ≤ B.comap f.toIntAlgHom := by
    apply Algebra.adjoin_le
    rintro x (⟨r, hr, rfl⟩ | hx)
    · exact Algebra.subset_adjoin (Or.inl ⟨r, hr, rfl⟩)
    · exact hx.elim
  exact (f.toIntAlgHom.comp A.val).codRestrict B (fun x ↦ h x.2)

/-- The natural transformation between the diagrams of coefficient subrings of `R` and of `S`
whose components are the maps `coefficientMap f s i`. -/
noncomputable def coefficientDiagramMap {R S : Type u} [CommRing R] [CommRing S]
    (f : R →+* S) (s : Set S) :
    subringDiagram (fun i ↦ (coefficientSubalgebra (RingHom.id R) ∅ i).toSubring)
        (fun _ _ h ↦ coefficientSubalgebra_mono _ _ h) ⟶
      subringDiagram (fun i ↦ (coefficientSubalgebra f s i).toSubring)
        (fun _ _ h ↦ coefficientSubalgebra_mono _ _ h) where
  app i := CommRingCat.ofHom (coefficientMap f s i).toRingHom

/-- If `s` is finite, then `coefficientMap f s i` is of finite type. -/
theorem coefficientMap_finiteType {R S : Type*} [CommRing R] [CommRing S]
    (f : R →+* S) {s : Set S} (hs : s.Finite) (i : Finset R) :
    (coefficientMap f s i).toRingHom.FiniteType := by
  let A := coefficientSubalgebra (RingHom.id R) ∅ i
  let B := coefficientSubalgebra f s i
  have : Algebra.FiniteType ℤ B := ⟨(Subalgebra.fg_top B).mpr
    (coefficientSubalgebra_fg f hs i)⟩
  apply RingHom.FiniteType.of_comp_finiteType (f := algebraMap ℤ A)
  have h : (coefficientMap f s i).toRingHom.comp (algebraMap ℤ A) =
      algebraMap ℤ B := RingHom.ext (coefficientMap f s i).commutes
  rw [h, RingHom.finiteType_algebraMap]
  infer_instance

/-- Every element of `R` lies in the subring generated by some finite subset of `R`. -/
theorem exists_mem_base_coefficientSubalgebra {R : Type*} [CommRing R] (r : R) :
    ∃ i : Finset R, r ∈ coefficientSubalgebra (RingHom.id R) ∅ i := by
  classical exact ⟨{r}, Algebra.subset_adjoin (Or.inl ⟨r, by simp, rfl⟩)⟩

/-- The subring `coefficientSubalgebra (algebraMap R S) s i` of `S`, as a subalgebra over the
subring of `R` generated by `i`. -/
noncomputable def coefficientAlgebra {R S : Type*} [CommRing R] [CommRing S]
    [Algebra R S] (s : Set S) (i : Finset R) :
    Subalgebra (coefficientSubalgebra (RingHom.id R) ∅ i) S where
  __ := (coefficientSubalgebra (algebraMap R S) s i).toSubsemiring
  algebraMap_mem' a := (coefficientMap (algebraMap R S) s i a).2

/-- Membership in a coefficient stage's subalgebra of `S`, read in the algebra structure over
the stage of the base. -/
private lemma mem_coefficientAlgebra {R S : Type*} [CommRing R] [CommRing S] [Algebra R S]
    (s : Set S) (i : Finset R) {x : S}
    (hx : x ∈ coefficientSubalgebra (algebraMap R S) s i) :
    x ∈ coefficientAlgebra (R := R) s i := hx

/-- If `s` is finite, then `coefficientAlgebra s i` is finitely generated over the subring of
`R` generated by `i`. -/
theorem coefficientAlgebra_fg {R S : Type*} [CommRing R] [CommRing S]
    [Algebra R S] {s : Set S} (hs : s.Finite) (i : Finset R) :
    (coefficientAlgebra (R := R) s i).FG := by
  have h : Algebra.FiniteType (coefficientSubalgebra (RingHom.id R) ∅ i)
      (coefficientAlgebra (R := R) s i) :=
    (RingHom.finiteType_algebraMap).mp (coefficientMap_finiteType (algebraMap R S) hs i)
  exact (Subalgebra.fg_top _).mp h.out

/-- If `s` generates `S` as an `R`-algebra, then so does `coefficientAlgebra s i`. -/
theorem coefficientAlgebra_adjoin_eq_top {R S : Type*} [CommRing R] [CommRing S]
    [Algebra R S] {s : Set S} (hs : Algebra.adjoin R s = ⊤) (i : Finset R) :
    Algebra.adjoin R (coefficientAlgebra (R := R) s i : Set S) = ⊤ := by
  have h : s ⊆ (coefficientAlgebra (R := R) s i : Set S) := by
    intro x hx
    show x ∈ coefficientSubalgebra (algebraMap R S) s i
    exact Algebra.subset_adjoin (Or.inr hx)
  exact top_unique (hs ▸ Algebra.adjoin_mono h)

/-- If `s` generates `S` as an `R`-algebra, then every element of `S` lies in
`coefficientSubalgebra (algebraMap R S) s i` for some finite `i ⊆ R`. -/
theorem exists_mem_coefficientSubalgebra {R S : Type*} [CommRing R] [CommRing S]
    [Algebra R S] {s : Set S} (hs : Algebra.adjoin R s = ⊤) (x : S) :
    ∃ i : Finset R, x ∈ coefficientSubalgebra (algebraMap R S) s i := by
  classical
  have hx : x ∈ Algebra.adjoin R s := hs ▸ Algebra.mem_top
  induction hx using Algebra.adjoin_induction with
  | mem x hx => exact ⟨∅, Algebra.subset_adjoin (Or.inr hx)⟩
  | algebraMap r =>
    exact ⟨{r}, Algebra.subset_adjoin (Or.inl ⟨r, by simp, rfl⟩)⟩
  | add x y _ _ hx hy =>
    obtain ⟨i, hi⟩ := hx
    obtain ⟨j, hj⟩ := hy
    exact ⟨i ∪ j, Subalgebra.add_mem _
      (coefficientSubalgebra_mono _ _ Finset.subset_union_left hi)
      (coefficientSubalgebra_mono _ _ Finset.subset_union_right hj)⟩
  | mul x y _ _ hx hy =>
    obtain ⟨i, hi⟩ := hx
    obtain ⟨j, hj⟩ := hy
    exact ⟨i ∪ j, Subalgebra.mul_mem _
      (coefficientSubalgebra_mono _ _ Finset.subset_union_left hi)
      (coefficientSubalgebra_mono _ _ Finset.subset_union_right hj)⟩

/-- Given a commutative square of ring maps `a : A → B`, `b : A → C`, `c : B → D`,
`d : C → D` such that the images of `c` and `d` generate `D` as a ring, the induced morphism
`Spec D ⟶ Spec B ×_{Spec A} Spec C` is a closed immersion. -/
theorem isClosedImmersion_pullback_lift_of_closure_eq_top
    {A B C D : Type u} [CommRing A] [CommRing B] [CommRing C] [CommRing D]
    (a : A →+* B) (b : A →+* C) (c : B →+* D) (d : C →+* D)
    (hgen : Subring.closure (Set.range c ∪ Set.range d) = ⊤)
    (hcomm : Spec.map (CommRingCat.ofHom c) ≫ Spec.map (CommRingCat.ofHom a) =
      Spec.map (CommRingCat.ofHom d) ≫ Spec.map (CommRingCat.ofHom b)) :
    IsClosedImmersion (pullback.lift
      (f := Spec.map (CommRingCat.ofHom a))
      (g := Spec.map (CommRingCat.ofHom b))
      (Spec.map (CommRingCat.ofHom c)) (Spec.map (CommRingCat.ofHom d)) hcomm) := by
  let f := Spec.map (CommRingCat.ofHom c)
  let g := Spec.map (CommRingCat.ofHom d)
  let k := pullback.lift (f := Spec.map (CommRingCat.ofHom a))
    (g := Spec.map (CommRingCat.ofHom b)) f g hcomm
  show IsClosedImmersion k
  have hsurj : Function.Surjective k.appTop.hom := by
    let T : Subring D := k.appTop.hom.range.comap (Scheme.ΓSpecIso (.of D)).inv.hom
    have hc : Set.range c ⊆ T := by
      rintro _ ⟨x, rfl⟩
      show (Scheme.ΓSpecIso (.of D)).inv (c x) ∈ k.appTop.hom.range
      refine ⟨(pullback.fst (Spec.map (CommRingCat.ofHom a))
        (Spec.map (CommRingCat.ofHom b))).appTop ((Scheme.ΓSpecIso (.of B)).inv x), ?_⟩
      rw [← CommRingCat.comp_apply, ← Scheme.Hom.comp_appTop, pullback.lift_fst]
      have hn := congrArg (fun e ↦ e x)
        (Scheme.ΓSpecIso_inv_naturality (CommRingCat.ofHom c)).symm
      rw [CommRingCat.comp_apply, CommRingCat.comp_apply] at hn
      exact hn
    have hd : Set.range d ⊆ T := by
      rintro _ ⟨x, rfl⟩
      show (Scheme.ΓSpecIso (.of D)).inv (d x) ∈ k.appTop.hom.range
      refine ⟨(pullback.snd (Spec.map (CommRingCat.ofHom a))
        (Spec.map (CommRingCat.ofHom b))).appTop ((Scheme.ΓSpecIso (.of C)).inv x), ?_⟩
      rw [← CommRingCat.comp_apply, ← Scheme.Hom.comp_appTop, pullback.lift_snd]
      have hn := congrArg (fun e ↦ e x)
        (Scheme.ΓSpecIso_inv_naturality (CommRingCat.ofHom d)).symm
      rw [CommRingCat.comp_apply, CommRingCat.comp_apply] at hn
      exact hn
    have hT : T = ⊤ := top_le_iff.mp
      (hgen ▸ Subring.closure_le.mpr (Set.union_subset hc hd))
    intro x
    have hx : (Scheme.ΓSpecIso (.of D)).hom x ∈ T := by rw [hT]; trivial
    obtain ⟨y, hy⟩ := hx
    refine ⟨y, ?_⟩
    simpa using hy
  exact IsClosedImmersion.of_surjective_of_isAffine k hsurj

/-- For `j ⊆ i`, the ring `coefficientSubalgebra f s i` is generated by the image of
`coefficientSubalgebra f s j` together with the image of `coefficientMap f s i`. -/
theorem coefficientSubalgebra_closure_eq_top
    {R S : Type*} [CommRing R] [CommRing S] (f : R →+* S) (s : Set S)
    {i j : Finset R} (hij : j ⊆ i) :
    (Subring.closure
      (Set.range (Subring.inclusion (S := (coefficientSubalgebra f s j).toSubring)
        (T := (coefficientSubalgebra f s i).toSubring)
        (coefficientSubalgebra_mono f s hij)) ∪
        Set.range ((coefficientMap f s i).toRingHom)) :
          Subring (coefficientSubalgebra f s i)) = ⊤ := by
  let A := coefficientSubalgebra (RingHom.id R) ∅ i
  let Bi := coefficientSubalgebra f s i
  let Bj := coefficientSubalgebra f s j
  let T : Subring Bi := Subring.closure
    (Set.range (Subring.inclusion (S := Bj.toSubring) (T := Bi.toSubring)
      (coefficientSubalgebra_mono f s hij)) ∪
      Set.range ((coefficientMap f s i).toRingHom))
  show T = ⊤
  apply top_le_iff.mp
  intro x _
  have hmem : ∀ (y : S) (hy : y ∈ Bi), (⟨y, hy⟩ : Bi) ∈ T := by
    intro y hy
    induction hy using Algebra.adjoin_induction with
    | mem y hy =>
      rcases hy with ⟨r, hr, rfl⟩ | hs
      · have hrA : r ∈ A := Algebra.subset_adjoin (Or.inl ⟨r, hr, rfl⟩)
        apply Subring.subset_closure
        apply Or.inr
        refine ⟨⟨r, hrA⟩, ?_⟩
        apply Subtype.ext
        rfl
      · have hyj : y ∈ Bj := Algebra.subset_adjoin (Or.inr hs)
        apply Subring.subset_closure
        apply Or.inl
        refine ⟨⟨y, hyj⟩, ?_⟩
        rfl
    | algebraMap z =>
      show (z : Bi) ∈ T
      exact intCast_mem T z
    | add x y _ _ hx hy => exact T.add_mem hx hy
    | mul x y _ _ hx hy => exact T.mul_mem hx hy
  exact hmem x x.property

/-- For `j ⊆ i`, the morphism from the spectrum of the `i`-th coefficient subring of `S` to the
fibre product of the `j`-th one with the `i`-th coefficient subring of `R` over the `j`-th one
is a closed immersion. -/
theorem coefficientSpec_transition_closedImmersion
    {R S : Type u} [CommRing R] [CommRing S]
    (r : R →+* S) (s : Set S) {i j : Finset R} (hij : j ⊆ i) :
    let a := (coefficientMap r s j).toRingHom
    let b := Subring.inclusion
      (S := (coefficientSubalgebra (RingHom.id R) ∅ j).toSubring)
      (T := (coefficientSubalgebra (RingHom.id R) ∅ i).toSubring)
      (coefficientSubalgebra_mono (RingHom.id R) ∅ hij)
    let c := Subring.inclusion
      (S := (coefficientSubalgebra r s j).toSubring)
      (T := (coefficientSubalgebra r s i).toSubring)
      (coefficientSubalgebra_mono r s hij)
    let d := (coefficientMap r s i).toRingHom
    ∀ hcomm : Spec.map (CommRingCat.ofHom c) ≫ Spec.map (CommRingCat.ofHom a) =
        Spec.map (CommRingCat.ofHom d) ≫ Spec.map (CommRingCat.ofHom b),
    IsClosedImmersion (pullback.lift
      (f := Spec.map (CommRingCat.ofHom a))
      (g := Spec.map (CommRingCat.ofHom b))
      (Spec.map (CommRingCat.ofHom c))
      (Spec.map (CommRingCat.ofHom d))
      hcomm) := by
  intro a b c d hcomm
  exact isClosedImmersion_pullback_lift_of_closure_eq_top
    _ _ _ _ (coefficientSubalgebra_closure_eq_top r s hij) hcomm

/-- The cofiltered diagram of schemes `i ↦ Spec` of the subring of `R` generated by `i`, over
finite subsets `i` of `R`. -/
noncomputable def baseCoefficientSpecDiagram (R : Type u) [CommRing R] :
    (Finset R)ᵒᵖ ⥤ Scheme.{u} :=
  (subringDiagram
    (fun i ↦ (coefficientSubalgebra (RingHom.id R) ∅ i).toSubring)
    (coefficientSubalgebra_mono (RingHom.id R) ∅)).op ⋙ Scheme.Spec

/-- The cofiltered diagram of schemes `i ↦ Spec (coefficientSubalgebra r s i)`, over finite
subsets `i` of `R`. -/
noncomputable def coefficientSpecDiagram {R S : Type u}
    [CommRing R] [CommRing S] (r : R →+* S) (s : Set S) :
    (Finset R)ᵒᵖ ⥤ Scheme.{u} :=
  (subringDiagram
    (fun i ↦ (coefficientSubalgebra r s i).toSubring)
    (coefficientSubalgebra_mono r s)).op ⋙ Scheme.Spec

/-- The morphism of diagrams `coefficientSpecDiagram r s ⟶ baseCoefficientSpecDiagram R`
whose components are `Spec` of the maps `coefficientMap r s i`. -/
noncomputable def coefficientSpecDiagramMap {R S : Type u}
    [CommRing R] [CommRing S] (r : R →+* S) (s : Set S) :
    coefficientSpecDiagram r s ⟶ baseCoefficientSpecDiagram R :=
  Functor.whiskerRight (NatTrans.op (coefficientDiagramMap r s)) Scheme.Spec

/-- The cone over `baseCoefficientSpecDiagram R` with vertex `Spec R`. -/
noncomputable def baseCoefficientSpecCone (R : Type u) [CommRing R] :
    Cone (baseCoefficientSpecDiagram R) :=
  Scheme.Spec.mapCone (subringCocone
    (fun i ↦ (coefficientSubalgebra (RingHom.id R) ∅ i).toSubring)
    (coefficientSubalgebra_mono (RingHom.id R) ∅)).op

/-- The cone over `coefficientSpecDiagram r s` with vertex `Spec S`. -/
noncomputable def coefficientSpecCone {R S : Type u}
    [CommRing R] [CommRing S] (r : R →+* S) (s : Set S) :
    Cone (coefficientSpecDiagram r s) :=
  Scheme.Spec.mapCone (subringCocone
    (fun i ↦ (coefficientSubalgebra r s i).toSubring)
    (coefficientSubalgebra_mono r s)).op

/-- `Spec R` is the limit of `baseCoefficientSpecDiagram R`. -/
noncomputable def baseCoefficientSpecCone_isLimit (R : Type u) [CommRing R] :
    IsLimit (baseCoefficientSpecCone R) :=
  subringSpecIsLimit
    (fun i ↦ (coefficientSubalgebra (RingHom.id R) ∅ i).toSubring)
    (coefficientSubalgebra_mono (RingHom.id R) ∅)
    exists_mem_base_coefficientSubalgebra

/-- If the finite set `s` generates `S` as an `R`-algebra, then `Spec S` is the limit of
`coefficientSpecDiagram (algebraMap R S) s`. -/
noncomputable def coefficientSpecCone_isLimit {R S : Type u}
    [CommRing R] [CommRing S] [Algebra R S]
    (s : Finset S) (hs : Algebra.adjoin R (s : Set S) = ⊤) :
    IsLimit (coefficientSpecCone (algebraMap R S) (s : Set S)) :=
  subringSpecIsLimit
    (fun i ↦ (coefficientSubalgebra (algebraMap R S) (s : Set S) i).toSubring)
    (coefficientSubalgebra_mono (algebraMap R S) (s : Set S))
    (exists_mem_coefficientSubalgebra hs)

/-- The limit of the morphisms `Spec` of `coefficientMap (algebraMap R S) s i` is
`Spec (algebraMap R S)`. -/
theorem coefficientSpec_limitMap_eq
    {R S : Type u} [CommRing R] [CommRing S] [Algebra R S]
    (s : Set S) :
    (baseCoefficientSpecCone_isLimit R).lift
      ((Cone.postcompose (coefficientSpecDiagramMap (algebraMap R S) s)).obj
        (coefficientSpecCone (algebraMap R S) s)) =
      Spec.map (CommRingCat.ofHom (algebraMap R S)) := by
  let A : Finset R → Subring R := fun i ↦
    (coefficientSubalgebra (RingHom.id R) ∅ i).toSubring
  let B : Finset R → Subring S := fun i ↦
    (coefficientSubalgebra (algebraMap R S) s i).toSubring
  let hcA := baseCoefficientSpecCone_isLimit R
  apply hcA.hom_ext
  intro i
  rw [hcA.fac]
  simp only [Cone.postcompose_obj_π]
  show Spec.map (CommRingCat.ofHom (B i.unop).subtype) ≫
      Spec.map (CommRingCat.ofHom (coefficientMap (algebraMap R S) s i.unop).toRingHom) =
    Spec.map (CommRingCat.ofHom (algebraMap R S)) ≫
      Spec.map (CommRingCat.ofHom (A i.unop).subtype)
  rw [← Spec.map_comp, ← Spec.map_comp]
  congr 1

/-- For each transition `g : i ⟶ j`, the morphism from `(coefficientSpecDiagram r s).obj i` to
the fibre product of `(coefficientSpecDiagram r s).obj j` and
`(baseCoefficientSpecDiagram R).obj i` over `(baseCoefficientSpecDiagram R).obj j` is a closed
immersion. -/
theorem coefficientSpecDiagramMap_transition_closedImmersion
    {R S : Type u} [CommRing R] [CommRing S]
    (r : R →+* S) (s : Set S)
    {i j : (Finset R)ᵒᵖ} (g : i ⟶ j) :
    IsClosedImmersion (pullback.lift
      ((coefficientSpecDiagram r s).map g)
      ((coefficientSpecDiagramMap r s).app i)
      ((coefficientSpecDiagramMap r s).naturality g)) := by
  have hij : j.unop ⊆ i.unop := g.unop.le
  exact coefficientSpec_transition_closedImmersion r s hij
    ((coefficientSpecDiagramMap r s).naturality g)

/-- If the finite set `s` generates `S` as an `R`-algebra and every fibre of
`Spec S → Spec R` has dimension at most `d`, then for some finite `i ⊆ R` every fibre of
`Spec` of `coefficientMap (algebraMap R S) s i` has dimension at most `d`. -/
theorem exists_coefficient_stage_fiberDimension_le
    {R S : Type u} [CommRing R] [CommRing S] [Algebra R S]
    (s : Finset S) (hs : Algebra.adjoin R (s : Set S) = ⊤) (d : ℕ)
    (hdim : ∀ p : Spec (.of R),
      topologicalKrullDim ((Spec.map (CommRingCat.ofHom (algebraMap R S))).fiber p) ≤
        (d : WithBot ℕ∞)) :
    ∃ i : Finset R,
      ∀ p : Spec (.of (coefficientSubalgebra (RingHom.id R) ∅ i)),
        topologicalKrullDim ((Spec.map (CommRingCat.ofHom
          (coefficientMap (algebraMap R S) (s : Set S) i).toRingHom)).fiber p) ≤
            (d : WithBot ℕ∞) := by
  let A : Finset R → Subring R := fun i ↦
    (coefficientSubalgebra (RingHom.id R) ∅ i).toSubring
  have hA : Monotone A := fun _ _ h ↦ coefficientSubalgebra_mono _ _ h
  let F := baseCoefficientSpecDiagram R
  let G := coefficientSpecDiagram (algebraMap R S) (s : Set S)
  let f : G ⟶ F := coefficientSpecDiagramMap (algebraMap R S) (s : Set S)
  let cA : CategoryTheory.Limits.Cone F := baseCoefficientSpecCone R
  let cB : CategoryTheory.Limits.Cone G :=
    coefficientSpecCone (algebraMap R S) (s : Set S)
  let hcA : CategoryTheory.Limits.IsLimit cA := baseCoefficientSpecCone_isLimit R
  let hcB : CategoryTheory.Limits.IsLimit cB := coefficientSpecCone_isLimit s hs
  have instAffine : ∀ {i j : (Finset R)ᵒᵖ} (g : i ⟶ j), IsAffineHom (F.map g) := by
    intro i j g
    show IsAffineHom (Spec.map (CommRingCat.ofHom
      (Subring.inclusion (hA g.unop.le))))
    infer_instance
  have instCompact : ∀ i : (Finset R)ᵒᵖ, CompactSpace (F.obj i) := by
    intro i
    show CompactSpace (Spec (.of (A i.unop)))
    infer_instance
  have instQuasiSeparated : ∀ i : (Finset R)ᵒᵖ, QuasiSeparatedSpace (F.obj i) := by
    intro i
    show QuasiSeparatedSpace (Spec (.of (A i.unop)))
    infer_instance
  have instFiniteType : ∀ i : (Finset R)ᵒᵖ, LocallyOfFiniteType (f.app i) := by
    intro i
    show LocallyOfFiniteType (Spec.map (CommRingCat.ofHom
      (coefficientMap (algebraMap R S) (s : Set S) i.unop).toRingHom))
    exact (HasRingHomProperty.Spec_iff (P := @LocallyOfFiniteType)).mpr
      (coefficientMap_finiteType (algebraMap R S) s.finite_toSet i.unop)
  have instQuasiCompact : ∀ i : (Finset R)ᵒᵖ, QuasiCompact (f.app i) := by
    intro i
    show QuasiCompact (Spec.map (CommRingCat.ofHom
      (coefficientMap (algebraMap R S) (s : Set S) i.unop).toRingHom))
    infer_instance
  have instTransition : ∀ {i j : (Finset R)ᵒᵖ} (g : i ⟶ j),
      IsClosedImmersion (pullback.lift (G.map g) (f.app i) (f.naturality g)) := by
    intro i j g
    exact coefficientSpecDiagramMap_transition_closedImmersion
      (algebraMap R S) (s : Set S) g
  have hdimLimit : ∀ p : cA.pt,
      topologicalKrullDim ((hcA.lift ((CategoryTheory.Limits.Cone.postcompose f).obj cB)).fiber p) ≤
        (d : WithBot ℕ∞) := by
    show ∀ p : (baseCoefficientSpecCone R).pt,
      topologicalKrullDim (((baseCoefficientSpecCone_isLimit R).lift
        ((Cone.postcompose (coefficientSpecDiagramMap (algebraMap R S) (s : Set S))).obj
          (coefficientSpecCone (algebraMap R S) (s : Set S)))).fiber p) ≤
        (d : WithBot ℕ∞)
    rw [coefficientSpec_limitMap_eq (s : Set S)]
    exact hdim
  obtain ⟨i, hi⟩ :=
    @exists_forall_topologicalKrullDim_fiber_le_of_isLimit_of_essentiallySmall.{u, u, u}
    (Finset R)ᵒᵖ
    (inferInstance) (inferInstance) (inferInstance) G F f instAffine instCompact
    instQuasiSeparated instFiniteType instQuasiCompact instTransition cB hcB cA hcA d hdimLimit
  exact ⟨i.unop, hi⟩

/-- A closed subscheme of a base change inherits its fibre-dimension bound. -/
private lemma fiber_dimension_le_of_closed_square
    {A B C D : Type u} [CommRing A] [CommRing B] [CommRing C] [CommRing D]
    (a : A →+* B) (b : A →+* C) (c : B →+* D) (e : C →+* D)
    (htype : a.FiniteType)
    (hgen : Subring.closure (Set.range c ∪ Set.range e) = ⊤)
    (hcomm : Spec.map (CommRingCat.ofHom c) ≫ Spec.map (CommRingCat.ofHom a) =
      Spec.map (CommRingCat.ofHom e) ≫ Spec.map (CommRingCat.ofHom b))
    (d : WithBot ℕ∞)
    (ha : ∀ q : Spec (.of A),
      topologicalKrullDim ((Spec.map (CommRingCat.ofHom a)).fiber q) ≤ d) :
    ∀ q : Spec (.of C),
      topologicalKrullDim ((Spec.map (CommRingCat.ofHom e)).fiber q) ≤ d := by
  let f := Spec.map (CommRingCat.ofHom a)
  let g := Spec.map (CommRingCat.ofHom b)
  let k := pullback.lift (f := f) (g := g)
    (Spec.map (CommRingCat.ofHom c)) (Spec.map (CommRingCat.ofHom e)) hcomm
  have : LocallyOfFiniteType f :=
    (HasRingHomProperty.Spec_iff (P := @LocallyOfFiniteType)).mpr htype
  have : IsClosedImmersion k :=
    isClosedImmersion_pullback_lift_of_closure_eq_top a b c e hgen hcomm
  have h := fiber_dimension_le_of_isPullback _ _ _ _
    (IsPullback.of_hasPullback f g) d ha
  intro q
  rw [← pullback.lift_snd (Spec.map (CommRingCat.ofHom c))
    (Spec.map (CommRingCat.ofHom e)) hcomm]
  exact (topologicalKrullDim_comp_fiber_le_of_isInducing k (pullback.snd f g)
    k.isClosedEmbedding.isInducing q).trans (h q)

private noncomputable def polynomialSubringDiagram {I : Type u} [Preorder I]
    {R : Type u} [CommRing R] (A : I → Subring R) (hA : Monotone A) :
    I ⥤ CommRingCat.{u} where
  obj i := .of (Polynomial (A i))
  map f := CommRingCat.ofHom (Polynomial.mapRingHom (Subring.inclusion (hA f.le)))
  map_id i := by
    apply CommRingCat.hom_ext
    apply Polynomial.ringHom_ext
    · intro r; simp only [CommRingCat.hom_ofHom, Polynomial.coe_mapRingHom,
        Polynomial.map_C, CommRingCat.hom_id, RingHom.id_apply]; rfl
    · simp
  map_comp f g := by
    apply CommRingCat.hom_ext
    apply Polynomial.ringHom_ext
    · intro r; simp only [CommRingCat.hom_ofHom, CommRingCat.hom_comp,
        RingHom.comp_apply, Polynomial.coe_mapRingHom, Polynomial.map_C]; rfl
    · simp

private noncomputable def polynomialSubringCocone {I : Type u} [Preorder I]
    {R : Type u} [CommRing R] (A : I → Subring R) (hA : Monotone A) :
    Cocone (polynomialSubringDiagram A hA) where
  pt := .of (Polynomial R)
  ι := { app := fun i ↦ CommRingCat.ofHom (Polynomial.mapRingHom (A i).subtype)
         naturality := by
           intro i j f
           apply CommRingCat.hom_ext
           apply Polynomial.ringHom_ext
           · intro r; simp [polynomialSubringDiagram, Subring.inclusion]
           · simp [polynomialSubringDiagram] }

private noncomputable def polynomialCoefficientCoconeIsColimit
    (R : Type u) [CommRing R] :
    IsColimit (polynomialSubringCocone
      (fun i ↦ (coefficientSubalgebra (RingHom.id R) ∅ i).toSubring)
      (fun _ _ h => coefficientSubalgebra_mono _ _ h)) := by
  classical
  let A : Finset R → Subring R := fun i ↦
    (coefficientSubalgebra (RingHom.id R) ∅ i).toSubring
  let hA : Monotone A := fun _ _ h => coefficientSubalgebra_mono _ _ h
  let := reflectsColimit_of_reflectsIsomorphisms
    (polynomialSubringDiagram A hA) (forget CommRingCat)
  apply isColimitOfReflects (forget CommRingCat)
  apply Types.FilteredColimit.isColimitOf'
  · intro p
    change Polynomial R at p
    have hp : p ∈ (Polynomial.mapRingHom (A p.coeffs).subtype).range := by
      rw [Polynomial.mem_map_range]
      intro n
      refine ⟨⟨p.coeff n, ?_⟩, rfl⟩
      by_cases h : p.coeff n = 0
      · rw [h]; exact (A p.coeffs).zero_mem
      · exact Algebra.subset_adjoin
          (Or.inl ⟨p.coeff n, Polynomial.coeff_mem_coeffs h, rfl⟩)
    obtain ⟨q, hq⟩ := hp
    exact ⟨p.coeffs, q, hq.symm⟩
  · intro i x y hxy
    refine ⟨i, 𝟙 i, ?_⟩
    change Polynomial.map (A i).subtype x = Polynomial.map (A i).subtype y at hxy
    have h : x = y := Polynomial.map_injective (A i).subtype Subtype.val_injective hxy
    rw [h]

private noncomputable abbrev polynomialCoefficientSpecDiagram
    (R : Type u) [CommRing R] : (Finset R)ᵒᵖ ⥤ Scheme.{u} :=
  (polynomialSubringDiagram
    (fun i ↦ (coefficientSubalgebra (RingHom.id R) ∅ i).toSubring)
    (fun _ _ h => coefficientSubalgebra_mono _ _ h)).op ⋙ Scheme.Spec

private noncomputable abbrev polynomialCoefficientSpecCone
    (R : Type u) [CommRing R] : Cone (polynomialCoefficientSpecDiagram R) :=
  Scheme.Spec.mapCone (polynomialSubringCocone
    (fun i ↦ (coefficientSubalgebra (RingHom.id R) ∅ i).toSubring)
    (fun _ _ h => coefficientSubalgebra_mono _ _ h)).op

private noncomputable def polynomialCoefficientSpecConeIsLimit
    (R : Type u) [CommRing R] : IsLimit (polynomialCoefficientSpecCone R) :=
  isLimitOfPreserves Scheme.Spec (polynomialCoefficientCoconeIsColimit R).op

private noncomputable def coefficientEvaluationMap
    {R S : Type u} [CommRing R] [CommRing S] [Algebra R S]
    (s : Set S) (a : S) (ha : a ∈ s) (i : Finset R) :
    Polynomial (coefficientSubalgebra (RingHom.id R) ∅ i) →+*
      coefficientSubalgebra (algebraMap R S) s i :=
  Polynomial.eval₂RingHom (coefficientMap (algebraMap R S) s i).toRingHom
    ⟨a, Algebra.subset_adjoin (Or.inr ha)⟩

private lemma coefficientEvaluationMap_C
    {R S : Type u} [CommRing R] [CommRing S] [Algebra R S]
    (s : Set S) (a : S) (ha : a ∈ s) (i : Finset R)
    (r : coefficientSubalgebra (RingHom.id R) ∅ i) :
    coefficientEvaluationMap s a ha i (Polynomial.C r) =
      coefficientMap (algebraMap R S) s i r :=
  Polynomial.eval₂_C _ _

private lemma coefficientEvaluationMap_X
    {R S : Type u} [CommRing R] [CommRing S] [Algebra R S]
    (s : Set S) (a : S) (ha : a ∈ s) (i : Finset R) :
    coefficientEvaluationMap s a ha i Polynomial.X =
      ⟨a, Algebra.subset_adjoin (Or.inr ha)⟩ :=
  Polynomial.eval₂_X _ _

/-- Evaluation commutes with a compatible square of coefficient maps. -/
private lemma eval₂RingHom_naturality
    {A B C D : Type*} [Semiring A] [CommSemiring B] [Semiring C] [CommSemiring D]
    (f : A →+* B) (g : C →+* D) (i : A →+* C) (j : B →+* D)
    (b : B) (d : D) (h : g.comp i = j.comp f) (hb : j b = d) :
    (Polynomial.eval₂RingHom g d).comp (Polynomial.mapRingHom i) =
      j.comp (Polynomial.eval₂RingHom f b) := by
  apply Polynomial.ringHom_ext
  · intro a
    simpa using DFunLike.congr_fun h a
  · simpa using hb.symm

private noncomputable def coefficientEvaluationDiagramMap
    {R S : Type u} [CommRing R] [CommRing S] [Algebra R S]
    (s : Set S) (a : S) (ha : a ∈ s) :
    polynomialSubringDiagram
      (fun i ↦ (coefficientSubalgebra (RingHom.id R) ∅ i).toSubring)
      (fun _ _ h => coefficientSubalgebra_mono _ _ h) ⟶
    subringDiagram
      (fun i ↦ (coefficientSubalgebra (algebraMap R S) s i).toSubring)
      (fun _ _ h => coefficientSubalgebra_mono _ _ h) where
  app i := CommRingCat.ofHom (coefficientEvaluationMap s a ha i)
  naturality := by
    intro i j f
    apply CommRingCat.hom_ext
    exact eval₂RingHom_naturality _ _ _ _ _ _
      (congrArg CommRingCat.Hom.hom
        ((coefficientDiagramMap (algebraMap R S) s).naturality f)) rfl

private noncomputable abbrev coefficientEvaluationSpecMap
    {R S : Type u} [CommRing R] [CommRing S] [Algebra R S]
    (s : Set S) (a : S) (ha : a ∈ s) :
    coefficientSpecDiagram (algebraMap R S) s ⟶ polynomialCoefficientSpecDiagram R :=
  Functor.whiskerRight (NatTrans.op (coefficientEvaluationDiagramMap s a ha)) Scheme.Spec

private lemma coefficientEvaluationMap_finiteType
    {R S : Type u} [CommRing R] [CommRing S] [Algebra R S]
    (s : Set S) (hs : s.Finite) (a : S) (ha : a ∈ s) (i : Finset R) :
    (coefficientEvaluationMap (R := R) s a ha i).FiniteType := by
  apply RingHom.FiniteType.of_comp_finiteType
    (f := Polynomial.C)
  convert coefficientMap_finiteType (algebraMap R S) hs i using 1
  ext r
  simp [coefficientEvaluationMap]

private lemma coefficientEvaluationSpec_transition_closedImmersion
    {R S : Type u} [CommRing R] [CommRing S] [Algebra R S]
    (s : Set S) (a : S) (ha : a ∈ s) {i j : (Finset R)ᵒᵖ} (g : i ⟶ j) :
    IsClosedImmersion (pullback.lift
      ((coefficientSpecDiagram (algebraMap R S) s).map g)
      ((coefficientEvaluationSpecMap s a ha).app i)
      ((coefficientEvaluationSpecMap s a ha).naturality g)) := by
  refine isClosedImmersion_pullback_lift_of_closure_eq_top
    (coefficientEvaluationMap s a ha j.unop)
    (Polynomial.mapRingHom (Subring.inclusion
      (S := (coefficientSubalgebra (RingHom.id R) ∅ j.unop).toSubring)
      (T := (coefficientSubalgebra (RingHom.id R) ∅ i.unop).toSubring)
      (coefficientSubalgebra_mono (RingHom.id R) ∅ g.unop.le)))
    (Subring.inclusion
      (S := (coefficientSubalgebra (algebraMap R S) s j.unop).toSubring)
      (T := (coefficientSubalgebra (algebraMap R S) s i.unop).toSubring)
      (coefficientSubalgebra_mono (algebraMap R S) s g.unop.le))
    (coefficientEvaluationMap s a ha i.unop) ?_
    ((coefficientEvaluationSpecMap s a ha).naturality g)
  apply top_unique
  rw [← coefficientSubalgebra_closure_eq_top (algebraMap R S) s g.unop.le]
  apply Subring.closure_mono
  apply Set.union_subset_union_right
  rintro _ ⟨r, rfl⟩
  exact ⟨Polynomial.C r, coefficientEvaluationMap_C (R := R) s a ha i.unop r⟩

private lemma coefficientEvaluationSpec_limitMap_eq
    {R S : Type u} [CommRing R] [CommRing S] [Algebra R S]
    (s : Set S) (a : S) (ha : a ∈ s) :
    (polynomialCoefficientSpecConeIsLimit R).lift
      ((Cone.postcompose (coefficientEvaluationSpecMap s a ha)).obj
        (coefficientSpecCone (algebraMap R S) s)) = specMapAeval (R := R) a := by
  apply (polynomialCoefficientSpecConeIsLimit R).hom_ext
  intro i
  rw [IsLimit.fac]
  simp only [Cone.postcompose_obj_π]
  show Spec.map (CommRingCat.ofHom
      (coefficientSubalgebra (algebraMap R S) s i.unop).toSubring.subtype) ≫
      Spec.map (CommRingCat.ofHom (coefficientEvaluationMap s a ha i.unop)) =
    specMapAeval (R := R) a ≫ Spec.map (CommRingCat.ofHom
      (Polynomial.mapRingHom
        (coefficientSubalgebra (RingHom.id R) ∅ i.unop).toSubring.subtype))
  rw [← Spec.map_comp, ← Spec.map_comp]
  congr 1
  apply CommRingCat.hom_ext
  apply Polynomial.ringHom_ext
  · intro r
    show ((coefficientEvaluationMap s a ha i.unop (Polynomial.C r) :
      coefficientSubalgebra (algebraMap R S) s i.unop) : S) =
        Polynomial.aeval a (Polynomial.map _ (Polynomial.C r))
    rw [coefficientEvaluationMap_C, Polynomial.map_C, Polynomial.aeval_C]
    rfl
  · show ((coefficientEvaluationMap s a ha i.unop Polynomial.X :
      coefficientSubalgebra (algebraMap R S) s i.unop) : S) =
        Polynomial.aeval a (Polynomial.map _ Polynomial.X)
    rw [coefficientEvaluationMap_X, Polynomial.map_X, Polynomial.aeval_X]

/-- The fibre bound for an evaluation map descends to a finite coefficient ring. -/
private lemma exists_coefficient_stage_evaluation_fiber_dimension_le
    {R S : Type u} [CommRing R] [CommRing S] [Algebra R S]
    (s : Finset S) (hs : Algebra.adjoin R (s : Set S) = ⊤)
    (a : S) (has : a ∈ s) (d : ℕ)
    (ha : ∀ q : Spec (.of (Polynomial R)),
      topologicalKrullDim ((specMapAeval a).fiber q) ≤ (d : WithBot ℕ∞)) :
    ∃ i : Finset R,
      ∀ q : Spec (.of (Polynomial (coefficientSubalgebra (RingHom.id R) ∅ i))),
        topologicalKrullDim ((Spec.map (CommRingCat.ofHom
          (coefficientEvaluationMap (s : Set S) a has i))).fiber q) ≤
            (d : WithBot ℕ∞) := by
  let F := polynomialCoefficientSpecDiagram R
  let G := coefficientSpecDiagram (algebraMap R S) (s : Set S)
  let f : G ⟶ F := coefficientEvaluationSpecMap (s : Set S) a has
  let cA : Cone F := polynomialCoefficientSpecCone R
  let cB : Cone G := coefficientSpecCone (algebraMap R S) (s : Set S)
  let hcA : IsLimit cA := polynomialCoefficientSpecConeIsLimit R
  let hcB : IsLimit cB := coefficientSpecCone_isLimit s hs
  have instAffine : ∀ {i j : (Finset R)ᵒᵖ} (g : i ⟶ j), IsAffineHom (F.map g) := by
    intro i j g
    show IsAffineHom (Spec.map (CommRingCat.ofHom (Polynomial.mapRingHom
      (Subring.inclusion
        (S := (coefficientSubalgebra (RingHom.id R) ∅ j.unop).toSubring)
        (T := (coefficientSubalgebra (RingHom.id R) ∅ i.unop).toSubring)
        (coefficientSubalgebra_mono (RingHom.id R) ∅ g.unop.le)))))
    infer_instance
  have instCompact : ∀ i : (Finset R)ᵒᵖ, CompactSpace (F.obj i) := by
    intro i
    show CompactSpace (Spec (.of
      (Polynomial (coefficientSubalgebra (RingHom.id R) ∅ i.unop))))
    infer_instance
  have instQuasiSeparated : ∀ i : (Finset R)ᵒᵖ, QuasiSeparatedSpace (F.obj i) := by
    intro i
    show QuasiSeparatedSpace (Spec (.of
      (Polynomial (coefficientSubalgebra (RingHom.id R) ∅ i.unop))))
    infer_instance
  have instFiniteType : ∀ i : (Finset R)ᵒᵖ, LocallyOfFiniteType (f.app i) := by
    intro i
    show LocallyOfFiniteType (Spec.map (CommRingCat.ofHom
      (coefficientEvaluationMap (s : Set S) a has i.unop)))
    exact (HasRingHomProperty.Spec_iff (P := @LocallyOfFiniteType)).mpr
      (coefficientEvaluationMap_finiteType (s : Set S) s.finite_toSet a has i.unop)
  have instQuasiCompact : ∀ i : (Finset R)ᵒᵖ, QuasiCompact (f.app i) := by
    intro i
    show QuasiCompact (Spec.map (CommRingCat.ofHom
      (coefficientEvaluationMap (s : Set S) a has i.unop)))
    infer_instance
  have instTransition : ∀ {i j : (Finset R)ᵒᵖ} (g : i ⟶ j),
      IsClosedImmersion (pullback.lift (G.map g) (f.app i) (f.naturality g)) := by
    intro i j g
    exact coefficientEvaluationSpec_transition_closedImmersion (s : Set S) a has g
  have hdimLimit : ∀ q : cA.pt,
      topologicalKrullDim ((hcA.lift ((Cone.postcompose f).obj cB)).fiber q) ≤
        (d : WithBot ℕ∞) := by
    show ∀ q, topologicalKrullDim (((polynomialCoefficientSpecConeIsLimit R).lift
      ((Cone.postcompose (coefficientEvaluationSpecMap (s : Set S) a has)).obj
        (coefficientSpecCone (algebraMap R S) (s : Set S)))).fiber q) ≤ _
    rw [coefficientEvaluationSpec_limitMap_eq]
    exact ha
  obtain ⟨i, hi⟩ :=
    @exists_forall_topologicalKrullDim_fiber_le_of_isLimit_of_essentiallySmall.{u, u, u}
    (Finset R)ᵒᵖ
    (inferInstance) (inferInstance) (inferInstance) G F f instAffine instCompact
    instQuasiSeparated instFiniteType instQuasiCompact instTransition cB hcB cA hcA d hdimLimit
  exact ⟨i.unop, hi⟩

/-- A generating subalgebra transfers evaluation-fibre bounds to the original algebra. -/
private lemma fiber_dimension_evaluation_le_of_adjoin_eq_top
    {A R S : Type u} [CommRing A] [CommRing R] [CommRing S]
    [Algebra A R] [Algebra A S] [Algebra R S] [IsScalarTower A R S]
    (B : Subalgebra A S) [Algebra.FiniteType A B]
    (hB : Algebra.adjoin R (B : Set S) = ⊤) (a : B) (d : WithBot ℕ∞)
    (ha : ∀ q : Spec (.of (Polynomial A)),
      topologicalKrullDim ((specMapAeval a).fiber q) ≤ d) :
    ∀ q : Spec (.of (Polynomial R)),
      topologicalKrullDim ((specMapAeval (R := R) (a : S)).fiber q) ≤ d := by
  let e := (Polynomial.aeval (R := R) (a : S)).toRingHom
  have hgen : Subring.closure (Set.range B.val.toRingHom ∪ Set.range e) = ⊤ := by
    let T : Subring S := Subring.closure (Set.range B.val.toRingHom ∪ Set.range e)
    have hR (r : R) : algebraMap R S r ∈ T := by
      apply Subring.subset_closure
      exact Or.inr ⟨Polynomial.C r, by simp [e]⟩
    let T' : Subalgebra R S := { __ := T.toSubsemiring, algebraMap_mem' := hR }
    have hBT : (B : Set S) ⊆ T' := by
      intro x hx
      exact Subring.subset_closure (Or.inl ⟨⟨x, hx⟩, rfl⟩)
    have htop : T' = ⊤ := top_le_iff.mp (hB ▸ Algebra.adjoin_le hBT)
    apply top_le_iff.mp
    intro x hx
    show x ∈ T'
    rw [htop]
    trivial
  let φ : Polynomial A →+* B := (Polynomial.aeval (R := A) a).toRingHom
  let ψ : Polynomial A →+* Polynomial R := Polynomial.mapRingHom (algebraMap A R)
  have hcomm : Spec.map (CommRingCat.ofHom B.val.toRingHom) ≫
      Spec.map (CommRingCat.ofHom φ) =
      Spec.map (CommRingCat.ofHom e) ≫ Spec.map (CommRingCat.ofHom ψ) := by
    rw [← Spec.map_comp, ← Spec.map_comp]
    congr 1
    apply CommRingCat.hom_ext
    apply Polynomial.ringHom_ext
    · intro r
      show B.val (Polynomial.aeval a (Polynomial.C r)) =
        Polynomial.aeval (R := R) (a : S) (Polynomial.map (algebraMap A R) (Polynomial.C r))
      rw [Polynomial.map_C, Polynomial.aeval_C, Polynomial.aeval_C, B.val.commutes]
      exact IsScalarTower.algebraMap_apply A R S r
    · show B.val (Polynomial.aeval a Polynomial.X) =
        Polynomial.aeval (R := R) (a : S) (Polynomial.map (algebraMap A R) Polynomial.X)
      rw [Polynomial.map_X, Polynomial.aeval_X, Polynomial.aeval_X]
      rfl
  have htype : φ.FiniteType := by
    apply RingHom.FiniteType.of_comp_finiteType (f := Polynomial.C)
    have hφ : φ.comp Polynomial.C = algebraMap A B := by ext r; simp [φ]
    rw [hφ, RingHom.finiteType_algebraMap]
    infer_instance
  exact fiber_dimension_le_of_closed_square φ ψ B.val.toRingHom e htype hgen hcomm d ha

/-- Evaluation at an element of the generated subalgebra over a coefficient stage is the
evaluation map of that stage. -/
private lemma specMapAeval_coefficientAlgebra_eq
    {R S : Type u} [CommRing R] [CommRing S] [Algebra R S]
    (t : Set S) (a : S) (hat : a ∈ t) (i : Finset R) :
    specMapAeval (⟨a, mem_coefficientAlgebra _ _ (Algebra.subset_adjoin (Or.inr hat))⟩ :
        coefficientAlgebra (R := R) t i) =
      Spec.map (CommRingCat.ofHom (coefficientEvaluationMap t a hat i)) := by
  have hring : (Polynomial.aeval
      (⟨a, mem_coefficientAlgebra _ _ (Algebra.subset_adjoin (Or.inr hat))⟩ :
        coefficientAlgebra (R := R) t i)).toRingHom = coefficientEvaluationMap t a hat i :=
    Polynomial.ringHom_ext (fun r ↦ Subtype.ext rfl) (Subtype.ext rfl)
  exact congrArg (fun φ ↦ Spec.map (CommRingCat.ofHom φ)) hring

/-- The fibre-dimension bound at a coefficient stage, read through that identification. -/
private lemma fiber_dimension_specMapAeval_coefficientAlgebra
    {R S : Type u} [CommRing R] [CommRing S] [Algebra R S]
    (t : Set S) (a : S) (hat : a ∈ t) (i : Finset R) (d : ℕ)
    (hi : ∀ q : Spec (.of (Polynomial (coefficientSubalgebra (RingHom.id R) ∅ i))),
      topologicalKrullDim ((Spec.map (CommRingCat.ofHom
        (coefficientEvaluationMap t a hat i))).fiber q) ≤ (d : WithBot ℕ∞)) :
    ∀ q : Spec (.of (Polynomial (coefficientSubalgebra (RingHom.id R) ∅ i))),
      topologicalKrullDim ((specMapAeval
          (⟨a, mem_coefficientAlgebra _ _ (Algebra.subset_adjoin (Or.inr hat))⟩ :
            coefficientAlgebra (R := R) t i)).fiber q) ≤ (d : WithBot ℕ∞) := by
  intro q
  rw [specMapAeval_coefficientAlgebra_eq t a hat i]
  exact hi q

/-- The conclusion for a finite generating set, once a coefficient stage carrying the
dimension bound has been found: the stage is of finite type over `ℤ`, hence Noetherian, so the
Noetherian case applies there and the bound descends along the faithfully flat-free surjection
onto the generated subalgebra. -/
private lemma eventually_fiber_dimension_le_of_pow_add_of_stage
    {R S : Type u} [CommRing R] [CommRing S] [Algebra R S]
    (d : ℕ) (a b : S) (t : Finset S) (ht : Algebra.adjoin R (t : Set S) = ⊤)
    (hat : a ∈ (t : Set S)) (hbt : b ∈ (t : Set S)) (i : Finset R)
    (hi : ∀ q : Spec (.of (Polynomial (coefficientSubalgebra (RingHom.id R) ∅ i))),
      topologicalKrullDim ((Spec.map (CommRingCat.ofHom
        (coefficientEvaluationMap (t : Set S) a hat i))).fiber q) ≤ (d : WithBot ℕ∞)) :
    ∃ n₀ : ℕ, ∀ n : ℕ, n₀ ≤ n →
      ∀ q : Spec (.of (Polynomial R)),
        topologicalKrullDim ((specMapAeval (a ^ n + b)).fiber q) ≤
          (d : WithBot ℕ∞) := by
  classical
  let A := coefficientSubalgebra (RingHom.id R) ∅ i
  let B := coefficientAlgebra (R := R) (t : Set S) i
  have : Algebra.FiniteType ℤ A := ⟨(Subalgebra.fg_top A).mpr
    (coefficientSubalgebra_fg _ Set.finite_empty i)⟩
  have : IsNoetherianRing A := Algebra.FiniteType.isNoetherianRing ℤ A
  have : Algebra.FiniteType A B := ⟨(Subalgebra.fg_top B).mpr
    (coefficientAlgebra_fg t.finite_toSet i)⟩
  let a₀ : B := ⟨a, mem_coefficientAlgebra _ _ (Algebra.subset_adjoin (Or.inr hat))⟩
  let b₀ : B := ⟨b, mem_coefficientAlgebra _ _ (Algebra.subset_adjoin (Or.inr hbt))⟩
  have ha₀ : ∀ q : Spec (.of (Polynomial A)),
      topologicalKrullDim ((specMapAeval a₀).fiber q) ≤ (d : WithBot ℕ∞) :=
    fiber_dimension_specMapAeval_coefficientAlgebra (t : Set S) a hat i d hi
  obtain ⟨N, hN⟩ := eventually_fiber_dimension_le_of_pow_add_of_noetherian d a₀ b₀ ha₀
  refine ⟨N, fun n hn => ?_⟩
  exact fiber_dimension_evaluation_le_of_adjoin_eq_top B
    (coefficientAlgebra_adjoin_eq_top ht i) (a₀ ^ n + b₀) _ (hN n hn)

end EventualFibreDimension

namespace AlgebraicGeometry

open EventualFibreDimension

/-- **Stacks Project, Tag 0GTF.** If the morphism to the affine line determined by `a` has
fibres of dimension at most `d`, then so does the morphism determined by `a ^ n + b`, for every
sufficiently large exponent `n`. -/
@[stacks 0GTF]
public theorem eventually_topologicalKrullDim_fiber_specMapAeval_pow_add_le
    {R S : Type u} [CommRing R] [CommRing S] [Algebra R S]
    [Algebra.FiniteType R S] (d : ℕ) (a b : S)
    (ha : ∀ q : Spec (.of (Polynomial R)),
      topologicalKrullDim ((specMapAeval a).fiber q) ≤ (d : WithBot ℕ∞)) :
    ∃ n₀ : ℕ, ∀ n : ℕ, n₀ ≤ n →
      ∀ q : Spec (.of (Polynomial R)),
        topologicalKrullDim ((specMapAeval (a ^ n + b)).fiber q) ≤
          (d : WithBot ℕ∞) := by
  classical
  obtain ⟨s, hs⟩ := (Algebra.FiniteType.out : (⊤ : Subalgebra R S).FG)
  let t : Finset S := insert a (insert b s)
  have ht : Algebra.adjoin R (t : Set S) = ⊤ := by
    apply top_unique
    rw [← hs]
    exact Algebra.adjoin_mono (by intro x hx; simp [t, hx])
  obtain ⟨i, hi⟩ := exists_coefficient_stage_evaluation_fiber_dimension_le
    t ht a (by simp [t]) d ha
  exact eventually_fiber_dimension_le_of_pow_add_of_stage d a b t ht
    (by simp [t]) (by simp [t]) i hi

/-- Tag 0GTF stated with the dimension-of-fibres function of the morphism: a bound on the
dimensions of the fibres of the morphism to the affine line determined by `a` propagates to the
morphism determined by `a ^ n + b` for all large `n`. -/
public theorem eventually_fiberDimension_specMapAeval_pow_add_le
    {R S : Type u} [CommRing R] [CommRing S] [Algebra R S]
    [Algebra.FiniteType R S] (d : ℕ) (a b : S)
    (ha : ∀ q : Spec (.of (Polynomial R)),
      (specMapAeval a).fiberDimension q ≤ (d : WithBot ℕ∞)) :
    ∃ n₀ : ℕ, ∀ n : ℕ, n₀ ≤ n →
      ∀ q : Spec (.of (Polynomial R)),
        (specMapAeval (a ^ n + b)).fiberDimension q ≤ (d : WithBot ℕ∞) :=
  eventually_topologicalKrullDim_fiber_specMapAeval_pow_add_le d a b ha

end AlgebraicGeometry

end
