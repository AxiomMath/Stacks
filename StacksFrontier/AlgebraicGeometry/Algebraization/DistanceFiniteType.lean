module

public import StacksFrontier.AlgebraicGeometry.ResidueFieldClosedImmersion
public import StacksFrontier.AlgebraicGeometry.Algebraization.DistanceFunction
public import StacksFrontier.AlgebraicGeometry.F6Rank128.FiberDimension
import StacksFrontier.AlgebraicGeometry.Limits.NoetherianValuativeCriterion.Separatedness
public import StacksFrontier.AlgebraicGeometry.Morphisms.Dominant.IntegralSchemes
public import StacksFrontier.AlgebraicGeometry.Morphisms.FiniteType.DimensionFormula
public import StacksFrontier.AlgebraicGeometry.Morphisms.FiniteType.UniversallyCatenary
public import StacksFrontier.AlgebraicGeometry.Properties.ReducedClosedSubscheme
public import StacksFrontier.Topology.Dimension.SpecializingSurjection
public import Mathlib.AlgebraicGeometry.Fiber
public import Mathlib.AlgebraicGeometry.IdealSheaf.Functorial
public import Mathlib.AlgebraicGeometry.Morphisms.Separated
public import Mathlib.FieldTheory.FinTrdeg
public import StacksCore.Tactic.StacksAttribute

/-!
# Change of the distance function under a finite type morphism

Let `f : X ⟶ Y` be a finite type morphism of Noetherian schemes with `Y` universally catenary,
let `Z ⊆ Y` be a closed subscheme and let `x` be a point of `X`. The distance from `Z` at the
image `f x` is bounded by the distance from `f⁻¹ Z` at `x`, corrected by the transcendence degree
of the residue field extension and by a bound `e` on the fibre dimension.

A zigzag of integral closed subschemes from `f⁻¹ Z` to the closure of `x` is pushed forward to a
zigzag from `Z` to the closure of `f x` by taking closures of images; the dimension formula for a
dominant morphism of integral schemes of finite type over a universally catenary base controls
how each codimension changes, and that is what bounds the weight of the image zigzag.

## Main results

* `Stacks.Algebraization.distanceFunction_add_trdeg_le` — the bound on the distance at the image
  point.

## Implementation notes

The distance depends only on the underlying closed subset of a closed subscheme, so it is taken
at the support of an ideal sheaf. The inequality is written without subtraction as
`δ_Z(y) + trdeg(κ(x)/κ(y)) ≤ δ_{f⁻¹Z}(x) + e`; the fibre-dimension bound makes the transcendence
degree finite, and this form also covers the case of infinite distance. Finite type is locally
of finite type together with quasi-compactness.

A closed subscheme is realized as the subscheme of the vanishing ideal sheaf of an irreducible
closed subset, which is integral, and a point of such a subscheme is produced from its generic
point; `stratumIdeal`, `stratumMap` and `stratumInclusion` package that construction and its
functoriality.

## References

* [Stacks Project, Tag 0EIZ](https://stacks.math.columbia.edu/tag/0EIZ)
-/

public section

open AlgebraicGeometry CategoryTheory TopologicalSpace

universe u

namespace Stacks.Algebraization

private noncomputable def stratumIdeal {X : Scheme.{u}} (C : IrreducibleCloseds X) :
    X.IdealSheafData :=
  Scheme.IdealSheafData.vanishingIdeal ⟨(C : Set X), C.isClosed⟩

private theorem vanishingSubscheme_isIntegral {X : Scheme.{u}}
    (V : IrreducibleCloseds X) :
    IsIntegral (Scheme.IdealSheafData.vanishingIdeal
      (⟨(V : Set X), V.isClosed⟩ : Closeds X)).subscheme := by
  let I := Scheme.IdealSheafData.vanishingIdeal
    (⟨(V : Set X), V.isClosed⟩ : Closeds X)
  have hRange : Set.range I.subschemeι.base = (V : Set X) := by
    rw [I.range_subschemeι, Scheme.IdealSheafData.coe_support_vanishingIdeal]
    simp
  have hred : IsReduced I.subscheme :=
    Scheme.IdealSheafData.isReduced_subscheme_vanishingIdeal
      (⟨(V : Set X), V.isClosed⟩ : Closeds X)
  have hemb : Topology.IsEmbedding (I.subschemeι.base) :=
    IsPreimmersion.isEmbedding I.subschemeι
  let homeo : I.subscheme ≃ₜ Set.range (I.subschemeι.base) := hemb.toHomeomorph
  have hirr : IrreducibleSpace I.subscheme := by
    have hsub : IsIrreducible (Set.range (I.subschemeι.base)) := by
      rw [hRange]
      exact V.isIrreducible
    exact (homeo.irreducibleSpace_iff).2 (Subtype.irreducibleSpace hsub)
  exact isIntegral_of_irreducibleSpace_of_isReduced I.subscheme

/-- The subscheme of a stratum is integral. -/
private instance isIntegral_stratumIdeal_subscheme {X : Scheme.{u}} (A : IrreducibleCloseds X) :
    IsIntegral (stratumIdeal A).subscheme :=
  vanishingSubscheme_isIntegral A

private theorem universallyCatenary_of_locallyFiniteType {X Y : Scheme.{u}}
    [IsLocallyNoetherian Y] [IsLocallyNoetherian X]
    (hY : Scheme.IsUniversallyCatenary Y)
    (f : X ⟶ Y) [LocallyOfFiniteType f] : Scheme.IsUniversallyCatenary X := by
  show ∀ (T : Scheme.{u}) (g : T ⟶ X) [LocallyOfFiniteType g],
    IrreducibleClosedsCodim.IsCatenarySpace T
  intro T g hg
  let : LocallyOfFiniteType (g ≫ f) := locallyOfFiniteType_comp g f
  exact hY T (g ≫ f)

private def mapDistanceSystem {X Y : Scheme.{u}} (f : X ⟶ Y)
    [IsNoetherian X] [IsNoetherian Y] (I : Y.IdealSheafData) (x : X)
    (s : DistanceSystem X (I.comap f).support x) :
    DistanceSystem Y I.support (f x) := by
  classical
  refine ⟨s.k, (fun i => IrreducibleCloseds.map f.base f.continuous (s.V i)),
    (fun i => IrreducibleCloseds.map f.base f.continuous (s.W i)),
    fun i => IrreducibleCloseds.map_mono f.continuous (s.V_le_W i),
    fun i => IrreducibleCloseds.map_mono f.continuous (s.V_next_le_W i), ?_, ?_⟩
  · rw [IrreducibleCloseds.coe_map]
    apply closure_minimal
    · rintro _ ⟨z, hz, rfl⟩
      have hz' : z ∈ (I.comap f).support := s.V_zero_subset hz
      rw [Scheme.IdealSheafData.support_comap] at hz'
      change z ∈ f.base ⁻¹' (I.support : Set Y) at hz'
      exact hz'
    · exact I.support.isClosed
  · rw [IrreducibleCloseds.coe_map, s.W_last_eq_closure,
      closure_image_closure f.continuous]
    simp

private theorem coe_support_stratumIdeal {X : Scheme.{u}} (A : IrreducibleCloseds X) :
    ((stratumIdeal A).support : Set X) = (A : Set X) :=
  Scheme.IdealSheafData.coe_support_vanishingIdeal _

private theorem stratumIdeal_range {X : Scheme.{u}} (A : IrreducibleCloseds X) :
    Set.range (stratumIdeal A).subschemeι.base = (A : Set X) := by
  rw [(stratumIdeal A).range_subschemeι, coe_support_stratumIdeal]

private theorem stratumMap_exists {X Y : Scheme.{u}} (f : X ⟶ Y)
    (A : IrreducibleCloseds X) (B : IrreducibleCloseds Y)
    (hAB : IrreducibleCloseds.map f.base f.continuous A = B) :
    ∃ g : (stratumIdeal A).subscheme ⟶ (stratumIdeal B).subscheme,
      g ≫ (stratumIdeal B).subschemeι = (stratumIdeal A).subschemeι ≫ f := by
  have hset : closure (f.base '' (A : Set X)) = (B : Set Y) := by
    simpa only [IrreducibleCloseds.coe_map] using
      congrArg (fun C : IrreducibleCloseds Y => (C : Set Y)) hAB
  refine (Scheme.IdealSheafData.exists_lift_subschemeι_iff_range_subset_support _ _).2 ?_
  rintro y ⟨x, rfl⟩
  rw [coe_support_stratumIdeal, ← hset]
  exact subset_closure ⟨_, (stratumIdeal_range A).subset ⟨x, rfl⟩, rfl⟩

private noncomputable def stratumMap {X Y : Scheme.{u}} (f : X ⟶ Y)
    (A : IrreducibleCloseds X) (B : IrreducibleCloseds Y)
    (hAB : IrreducibleCloseds.map f.base f.continuous A = B) :
    (stratumIdeal A).subscheme ⟶ (stratumIdeal B).subscheme :=
  (stratumMap_exists f A B hAB).choose

private theorem stratumMap_fac {X Y : Scheme.{u}} (f : X ⟶ Y)
    (A : IrreducibleCloseds X) (B : IrreducibleCloseds Y)
    (hAB : IrreducibleCloseds.map f.base f.continuous A = B) :
    stratumMap f A B hAB ≫ (stratumIdeal B).subschemeι =
      (stratumIdeal A).subschemeι ≫ f :=
  (stratumMap_exists f A B hAB).choose_spec

private noncomputable def irreducibleTop {X : Scheme.{u}} [IrreducibleSpace X] :
    IrreducibleCloseds X :=
  ⟨Set.univ, IrreducibleSpace.isIrreducible_univ X, isClosed_univ⟩

private noncomputable def liftPointToStratum {X : Scheme.{u}}
    (A : IrreducibleCloseds X) (x : X) (hx : x ∈ (A : Set X)) :
    (stratumIdeal A).subscheme :=
  Classical.choose (Set.mem_range.mp (by rwa [stratumIdeal_range]))

private theorem liftPointToStratum_spec {X : Scheme.{u}}
    (A : IrreducibleCloseds X) (x : X) (hx : x ∈ (A : Set X)) :
    (stratumIdeal A).subschemeι (liftPointToStratum A x hx) = x :=
  Classical.choose_spec (Set.mem_range.mp (by rwa [stratumIdeal_range]))

private theorem irreducibleClosed_genericPoint_mem {X : Type u}
    [TopologicalSpace X] [QuasiSober X]
    (A : IrreducibleCloseds X) : A.isIrreducible.genericPoint ∈ (A : Set X) :=
  (A.isIrreducible.isGenericPoint_genericPoint A.isClosed).mem

private theorem stratum_subscheme_genericPoint {X : Scheme.{u}}
    (A : IrreducibleCloseds X) :
    (stratumIdeal A).subschemeι
        (genericPoint (stratumIdeal A).subscheme) = A.isIrreducible.genericPoint := by
  let I := stratumIdeal A
  have hrange : Set.range I.subschemeι.base = (A : Set X) := stratumIdeal_range A
  have hgen : IsGenericPoint (I.subschemeι.base (genericPoint I.subscheme))
      (A : Set X) := by
    have h := (genericPoint_spec I.subscheme).image I.subschemeι.continuous
    simpa [Set.image_univ, hrange, A.isClosed.closure_eq] using h
  exact hgen.eq (A.isIrreducible.isGenericPoint_genericPoint A.isClosed)

private theorem image_genericPoint {X Y : Type u}
    [TopologicalSpace X] [TopologicalSpace Y] [QuasiSober X] [QuasiSober Y]
    [T0Space Y] (f : X → Y) (hf : Continuous f)
    (A : IrreducibleCloseds X) (B : IrreducibleCloseds Y)
    (hAB : IrreducibleCloseds.map f hf A = B) :
    f (A.isIrreducible.genericPoint) = B.isIrreducible.genericPoint := by
  have hgen := (A.isIrreducible.isGenericPoint_genericPoint A.isClosed).image hf
  change IsGenericPoint (f A.isIrreducible.genericPoint)
    (IrreducibleCloseds.map f hf A : Set Y) at hgen
  rw [hAB] at hgen
  exact hgen.eq (B.isIrreducible.isGenericPoint_genericPoint B.isClosed)

private theorem residue_trdeg_le_fiber_bound {X Y : Scheme.{u}}
    (f : X ⟶ Y) [LocallyOfFiniteType f] (e : ℕ)
    (he : ∀ y : Y, topologicalKrullDim (f.fiber y) ≤ (e : WithBot ℕ∞)) (x : X) :
    let := (f.residueFieldMap x).hom.toAlgebra
    (Cardinal.toENat (Algebra.trdeg (Y.residueField (f x)) (X.residueField x)) : ℕ∞) ≤ e := by
  let := (f.residueFieldMap x).hom.toAlgebra
  have hdim := topologicalKrullDimAt_fiber_eq_krullDimOfRing_stalk_add_trdeg f x
  have htr : (Cardinal.toENat
      (Algebra.trdeg (Y.residueField (f x)) (X.residueField x)) : WithBot ℕ∞) ≤
      topologicalKrullDimAt (f.fiber (f x)) (f.asFiber x) := by
    rw [hdim]
    exact le_add_of_nonneg_left ringKrullDim_nonneg_of_nontrivial
  have htop : topologicalKrullDimAt (f.fiber (f x)) (f.asFiber x) ≤
      topologicalKrullDim (f.fiber (f x)) := by
    rw [topologicalKrullDimAt]
    exact iInf_le_of_le ⟨Set.univ, Set.mem_univ (f.asFiber x), isOpen_univ⟩
      (IsHomeomorph.topologicalKrullDim_eq _
        (Homeomorph.Set.univ (f.fiber (f x))).isHomeomorph).le
  exact_mod_cast htr.trans (htop.trans (he (f x)))

private theorem stratumMap_genericPoint {X Y : Scheme.{u}} (f : X ⟶ Y)
    (A : IrreducibleCloseds X) (B : IrreducibleCloseds Y)
    (hAB : IrreducibleCloseds.map f.base f.continuous A = B) :
    stratumMap f A B hAB (genericPoint (stratumIdeal A).subscheme) =
      genericPoint (stratumIdeal B).subscheme := by
  apply (IsPreimmersion.isEmbedding (stratumIdeal B).subschemeι).injective
  calc
    (stratumIdeal B).subschemeι
        (stratumMap f A B hAB (genericPoint (stratumIdeal A).subscheme)) =
      f ((stratumIdeal A).subschemeι (genericPoint (stratumIdeal A).subscheme)) := by
        have hh := congrArg (fun k : (stratumIdeal A).subscheme ⟶ Y => k.base
          (genericPoint (stratumIdeal A).subscheme)) (stratumMap_fac f A B hAB)
        simpa only [Scheme.Hom.comp_apply] using hh
    _ = (stratumIdeal B).subschemeι (genericPoint (stratumIdeal B).subscheme) := by
        rw [stratum_subscheme_genericPoint, stratum_subscheme_genericPoint]
        exact image_genericPoint f.base f.continuous A B hAB

private theorem stratumMap_locallyOfFiniteType {X Y : Scheme.{u}} (f : X ⟶ Y)
    [LocallyOfFiniteType f] (A : IrreducibleCloseds X) (B : IrreducibleCloseds Y)
    (hAB : IrreducibleCloseds.map f.base f.continuous A = B) :
    LocallyOfFiniteType (stratumMap f A B hAB) := by
  have : LocallyOfFiniteType (stratumMap f A B hAB ≫ (stratumIdeal B).subschemeι) := by
    rw [stratumMap_fac]
    exact locallyOfFiniteType_comp _ f
  exact locallyOfFiniteType_of_comp _ (stratumIdeal B).subschemeι

private theorem stratumMap_dominant {X Y : Scheme.{u}} (f : X ⟶ Y)
    (A : IrreducibleCloseds X) (B : IrreducibleCloseds Y)
    (hAB : IrreducibleCloseds.map f.base f.continuous A = B) :
    IsDominant (stratumMap f A B hAB) := by
  let IA := stratumIdeal A
  let IB := stratumIdeal B
  let : IsIntegral IB.subscheme := vanishingSubscheme_isIntegral B
  rw [isDominant_iff, denseRange_iff_closure_range]
  apply Set.Subset.antisymm (Set.subset_univ _)
  rw [← (genericPoint_spec IB.subscheme).def,
    ← stratumMap_genericPoint f A B hAB]
  exact closure_mono
    (Set.singleton_subset_iff.mpr ⟨genericPoint IA.subscheme, rfl⟩)

private theorem topCodim_closedEmbedding {S Y : Type u}
    [TopologicalSpace S] [TopologicalSpace Y] (j : S → Y)
    (hj : Topology.IsClosedEmbedding j) (W : IrreducibleCloseds Y)
    (hRange : Set.range j = (W : Set Y))
    (topS : IrreducibleCloseds S) (hTopS : (topS : Set S) = Set.univ) :
    ∀ A : IrreducibleCloseds S,
      IrreducibleClosedsCodim.topCodim
          (IrreducibleCloseds.map j hj.continuous A) W =
        IrreducibleClosedsCodim.topCodim A topS := by
  intro A
  let e := IrreducibleCloseds.map j hj.continuous
  have hle : ∀ A B : IrreducibleCloseds S, e A ≤ e B ↔ A ≤ B := by
    intro A B
    refine ⟨fun hab => ?_, fun hab => IrreducibleCloseds.map_mono hj.continuous hab⟩
    have hpre : ∀ C : IrreducibleCloseds S, j ⁻¹' closure (j '' (C : Set S)) = C := fun C => by
      rw [← hj.isInducing.closure_eq_preimage_closure_image C, C.isClosed.closure_eq]
    simpa only [SetLike.coe_subset_coe, e, IrreducibleCloseds.coe_map, hpre] using
      Set.preimage_mono (f := j) hab
  have htop : (e topS : Set Y) = (W : Set Y) := by
    show closure (j '' (topS : Set S)) = (W : Set Y)
    rw [hTopS, Set.image_univ, hRange, W.isClosed.closure_eq]
  have htopIC : e topS = W := IrreducibleCloseds.ext htop
  have hsurj : ∀ Z : IrreducibleCloseds Y, Z ≤ e topS →
      ∃ A, e A = Z := by
    intro Z hZ
    have hZW : (Z : Set Y) ⊆ (W : Set Y) := by
      simpa only [SetLike.coe_subset_coe, ← htop] using hZ
    let T : Set S := j ⁻¹' (Z : Set Y)
    have himage : j '' T = (Z : Set Y) :=
      Set.image_preimage_eq_of_subset (by rwa [hRange])
    let E : (↥T) ≃ₜ (↥(Z : Set Y)) :=
      (hj.isEmbedding.homeomorphImage T).trans
        (Homeomorph.setCongr himage)
    have hTirr : IsIrreducible T := by
      rw [isIrreducible_iff_irreducibleSpace]
      exact E.irreducibleSpace_iff.mpr (Subtype.irreducibleSpace Z.isIrreducible)
    let A : IrreducibleCloseds S := ⟨T, hTirr, Z.isClosed.preimage hj.continuous⟩
    have hA : e A = Z := by
      apply IrreducibleCloseds.ext
      simp [e, A, IrreducibleCloseds.coe_map, himage, Z.isClosed.closure_eq]
    exact ⟨A, hA⟩
  rw [← htopIC]
  exact IrreducibleClosedsCodim.topCodim_eq_of_le_iff e hle A topS hsurj

private theorem stratum_localDimension_eq_topCodim {Y : Scheme.{u}}
    (W V : IrreducibleCloseds Y) (hVW : V ≤ W) :
    ringKrullDim (((stratumIdeal W).subscheme).presheaf.stalk
      (liftPointToStratum W V.isIrreducible.genericPoint
        (hVW (irreducibleClosed_genericPoint_mem V)))) =
      (IrreducibleClosedsCodim.topCodim V W : WithBot ℕ∞) := by
  let I := stratumIdeal W
  let j := I.subschemeι
  let p := liftPointToStratum W V.isIrreducible.genericPoint
    (hVW (irreducibleClosed_genericPoint_mem V))
  have hpoint : IrreducibleCloseds.map j.base j.continuous
      (IrreducibleCloseds.closureSingleton p) =
        IrreducibleCloseds.closureSingleton V.isIrreducible.genericPoint := by
    apply IrreducibleCloseds.ext
    rw [IrreducibleCloseds.coe_map]
    calc
      closure (j.base '' closure ({p} : Set I.subscheme)) =
          closure (j.base '' ({p} : Set I.subscheme)) := closure_image_closure j.continuous
      _ = closure ({V.isIrreducible.genericPoint} : Set Y) := by
        have hp : j.base p = V.isIrreducible.genericPoint := by
          simpa [p] using liftPointToStratum_spec W V.isIrreducible.genericPoint
            (hVW (irreducibleClosed_genericPoint_mem V))
        rw [Set.image_singleton, hp]
  let topS := irreducibleTop (X := I.subscheme)
  have hmax : ∀ A : IrreducibleCloseds I.subscheme, A ≤ topS := by
    intro A
    show (A : Set I.subscheme) ⊆ Set.univ
    exact Set.subset_univ _
  have hcod := topCodim_closedEmbedding j.base j.isClosedEmbedding W
    (stratumIdeal_range W) topS rfl
    (IrreducibleCloseds.closureSingleton p)
  rw [hpoint] at hcod
  rw [AlgebraicGeometry.ringKrullDim_stalk_eq_coheight,
    ← (Order.coheight_orderIso ((irreducibleSetEquivPoints (α := I.subscheme)).symm) p)]
  have hco : Order.coheight ((irreducibleSetEquivPoints (α := I.subscheme)).symm p) =
      IrreducibleClosedsCodim.topCodim V W := by
    calc
      Order.coheight ((irreducibleSetEquivPoints (α := I.subscheme)).symm p) =
          IrreducibleClosedsCodim.topCodim
            (IrreducibleCloseds.closureSingleton p) topS :=
        (topCodim_eq_coheight_of_isMax (IrreducibleCloseds.closureSingleton p) topS hmax).symm
      _ = IrreducibleClosedsCodim.topCodim
          (IrreducibleCloseds.closureSingleton V.isIrreducible.genericPoint) W := hcod.symm
      _ = IrreducibleClosedsCodim.topCodim V W := by
        have hV : IrreducibleCloseds.closureSingleton V.isIrreducible.genericPoint = V := by
          apply IrreducibleCloseds.ext
          simp [V.isClosed.closure_eq]
        rw [hV]
  exact_mod_cast hco

private noncomputable def stratumInclusion {X : Scheme.{u}}
    (A B : IrreducibleCloseds X) (h : A ≤ B) :
    (stratumIdeal A).subscheme ⟶ (stratumIdeal B).subscheme :=
  (stratumIdeal B).inclusion (Scheme.IdealSheafData.vanishingIdeal_antimono h)

private theorem stratumInclusion_fac {X : Scheme.{u}}
    (A B : IrreducibleCloseds X) (h : A ≤ B) :
    stratumInclusion A B h ≫ (stratumIdeal B).subschemeι =
      (stratumIdeal A).subschemeι :=
  Scheme.IdealSheafData.inclusion_subschemeι _

private theorem stratumInclusion_genericPoint_eq_lift {X : Scheme.{u}}
    (A B : IrreducibleCloseds X) (h : A ≤ B) :
    stratumInclusion A B h (genericPoint (stratumIdeal A).subscheme) =
      liftPointToStratum B A.isIrreducible.genericPoint
        (h (irreducibleClosed_genericPoint_mem A)) := by
  apply (IsPreimmersion.isEmbedding (stratumIdeal B).subschemeι).injective
  calc
    (stratumIdeal B).subschemeι
        (stratumInclusion A B h (genericPoint (stratumIdeal A).subscheme)) =
      (stratumIdeal A).subschemeι (genericPoint (stratumIdeal A).subscheme) := by
        have hh := congrArg (fun q : (stratumIdeal A).subscheme ⟶ X =>
          q (genericPoint (stratumIdeal A).subscheme)) (stratumInclusion_fac A B h)
        simpa only [Scheme.Hom.comp_apply] using hh
    _ = A.isIrreducible.genericPoint := stratum_subscheme_genericPoint A
    _ = (stratumIdeal B).subschemeι
        (liftPointToStratum B A.isIrreducible.genericPoint
          (h (irreducibleClosed_genericPoint_mem A))) := by
        rw [liftPointToStratum_spec]

private theorem stratumInclusion_localDimension_eq_topCodim {X : Scheme.{u}}
    (V W : IrreducibleCloseds X) (hVW : V ≤ W) :
    ringKrullDim (((stratumIdeal W).subscheme).presheaf.stalk
      (stratumInclusion V W hVW (genericPoint (stratumIdeal V).subscheme))) =
      (IrreducibleClosedsCodim.topCodim V W : WithBot ℕ∞) := by
  rw [stratumInclusion_genericPoint_eq_lift]
  exact stratum_localDimension_eq_topCodim W V hVW

private theorem stratumMap_inclusion_square {X Y : Scheme.{u}} (f : X ⟶ Y)
    (V' W' : IrreducibleCloseds X) (V W : IrreducibleCloseds Y)
    (hV'W' : V' ≤ W') (hVW : V ≤ W)
    (hW : IrreducibleCloseds.map f.base f.continuous W' = W)
    (hV : IrreducibleCloseds.map f.base f.continuous V' = V) :
    stratumInclusion V' W' hV'W' ≫ stratumMap f W' W hW =
      stratumMap f V' V hV ≫ stratumInclusion V W hVW := by
  apply (cancel_mono (stratumIdeal W).subschemeι).1
  calc
    (stratumInclusion V' W' hV'W' ≫ stratumMap f W' W hW) ≫
        (stratumIdeal W).subschemeι =
      (stratumIdeal V').subschemeι ≫ f := by
        rw [Category.assoc, stratumMap_fac, ← Category.assoc,
          stratumInclusion_fac]
    _ = (stratumMap f V' V hV ≫ stratumInclusion V W hVW) ≫
        (stratumIdeal W).subschemeι := by
        rw [Category.assoc, stratumInclusion_fac, stratumMap_fac]

private noncomputable def residueFieldEquivFunctionField {T : Scheme.{u}}
    [IsIntegral T] : T.residueField (genericPoint T) ≃+* T.functionField := by
  let φ := (T.residue (genericPoint T)).hom
  have hφ : Function.Bijective φ := by
    constructor
    · rw [RingHom.injective_iff_ker_eq_bot]
      change RingHom.ker (IsLocalRing.residue _) = ⊥
      rw [IsLocalRing.ker_residue, IsLocalRing.maximalIdeal_eq_bot]
    · exact T.residue_surjective (genericPoint T)
  exact (RingEquiv.ofBijective φ hφ).symm

private lemma stalkCongr_eqToHom_cancel {T : TopCat.{u}} (F : T.Presheaf CommRingCat)
    {x y : T} (h : x = y) :
    eqToHom (congrArg F.stalk h) ≫ (F.stalkCongr (.of_eq h.symm)).hom = 𝟙 _ := by
  cases h
  simp

private lemma stalkMap_cast_eq {X Y : Scheme.{u}} (f : X ⟶ Y) (x : X) (y : Y)
    (h : f x = y) :
    (eqToHom (congrArg Y.presheaf.stalk h.symm) ≫ f.stalkMap x) = h ▸ f.stalkMap x := by
  cases h
  rfl

private theorem residueTrdeg_eq_functionFieldTrdeg {X Y : Scheme.{u}}
    (f : X ⟶ Y) [IsIntegral X] [IsIntegral Y] [IsDominant f] :
    let η := genericPoint X
    let := (f.residueFieldMap η).hom.toAlgebra
    let := (dominantFunctionFieldMap f).toAlgebra
    Algebra.trdeg (Y.residueField (f η)) (X.residueField η) =
      Algebra.trdeg Y.functionField X.functionField := by
  let η := genericPoint X
  let : Algebra (Y.residueField (f η)) (X.residueField η) :=
    (f.residueFieldMap η).hom.toAlgebra
  let : Algebra Y.functionField X.functionField :=
    (dominantFunctionFieldMap f).toAlgebra
  have hgen : f η = genericPoint Y := ((tfae_isDominant_of_isIntegral f).out 1 2).mp ‹_›
  let eY₀ := residueFieldEquivFunctionField (T := Y)
  let eK : Y.residueField (f η) ≃+* Y.functionField :=
    (Y.residueFieldCongr hgen).commRingCatIsoToRingEquiv.trans eY₀
  let eX := residueFieldEquivFunctionField (T := X)
  have hcompat (z : Y.residueField (f η)) :
      eX ((f.residueFieldMap η).hom z) =
        (dominantFunctionFieldMap f) (eK z) := by
    have h : (f.residueFieldMap η).hom z =
        eX.symm ((dominantFunctionFieldMap f) (eK z)) := by
      let a : Y.presheaf.stalk (f η) :=
        (eqToHom (congrArg Y.presheaf.stalk hgen.symm)).hom (eK z)
      have ha : Y.residue (f η) a = z := by
        apply (Y.residueFieldCongr hgen).commRingCatIsoToRingEquiv.injective
        show (CommRingCat.Hom.hom (Y.residueFieldCongr hgen).hom)
            ((Y.residue (f η)).hom a) =
          (CommRingCat.Hom.hom (Y.residueFieldCongr hgen).hom) z
        have hc := congrArg (fun m : CommRingCat.Hom _ _ => m.hom a)
          (Scheme.residue_residueFieldCongr Y hgen)
        simp only [CommRingCat.hom_comp, RingHom.coe_comp, Function.comp_apply] at hc
        rw [hc]
        have hcan := stalkCongr_eqToHom_cancel Y.presheaf hgen.symm
        have hcanEval :
            (Y.presheaf.stalkCongr (.of_eq hgen)).hom
                ((eqToHom (congrArg Y.presheaf.stalk hgen.symm)).hom (eK z)) = eK z := by
          have hh := congrArg (fun m : CommRingCat.Hom _ _ => m.hom (eK z)) hcan
          simpa only [CommRingCat.hom_comp, RingHom.coe_comp, Function.comp_apply,
            CommRingCat.hom_id, RingHom.id_apply] using hh
        rw [hcanEval]
        show eY₀.symm (eY₀ ((Y.residueFieldCongr hgen).commRingCatIsoToRingEquiv z)) = _
        exact eY₀.symm_apply_apply _
      have hn := congrArg (fun m : CommRingCat.Hom _ _ => m.hom a)
        (Scheme.residue_residueFieldMap f η)
      simp only [CommRingCat.hom_comp, RingHom.coe_comp, Function.comp_apply] at hn
      rw [ha] at hn
      have hcast := congrArg
        (fun m : CommRingCat.Hom _ _ => (X.residue η).hom (m.hom (eK z)))
        (stalkMap_cast_eq f η (genericPoint Y) hgen)
      simp only [CommRingCat.hom_comp, RingHom.coe_comp, Function.comp_apply] at hcast
      show (f.residueFieldMap η).hom z =
        (X.residue η).hom ((hgen ▸ f.stalkMap η).hom (eK z))
      exact hn.trans hcast
    rw [h]
    exact eX.apply_symm_apply _
  exact Algebra.trdeg_eq_of_ringEquiv eK eX hcompat

private theorem residue_trdeg_eq_of_closed_immersion_factor
    {X X' Y Y' : Scheme.{u}} (i : X' ⟶ X) [IsClosedImmersion i]
    (j : Y' ⟶ Y) [IsClosedImmersion j] (f : X ⟶ Y) (g : X' ⟶ Y')
    (h : g ≫ j = i ≫ f) (x : X') :
    let := (f.residueFieldMap (i x)).hom.toAlgebra
    let := (g.residueFieldMap x).hom.toAlgebra
    Algebra.trdeg (Y.residueField (f (i x))) (X.residueField (i x)) =
      Algebra.trdeg (Y'.residueField (g x)) (X'.residueField x) := by
  have hpoint : f (i x) = j (g x) := by
    have hh := congrArg (fun (k : X' ⟶ Y) => k.base x) h
    simpa only [Scheme.Hom.comp_apply] using hh.symm
  have : IsIso (i.residueFieldMap x) := isIso_residueFieldMap_of_isClosedImmersion i x
  have : IsIso (j.residueFieldMap (g x)) :=
    isIso_residueFieldMap_of_isClosedImmersion j (g x)
  let ei : X.residueField (i x) ≃+* X'.residueField x :=
    (asIso (i.residueFieldMap x)).commRingCatIsoToRingEquiv
  let ej : Y.residueField (f (i x)) ≃+* Y'.residueField (g x) :=
    ((Y.residueFieldCongr hpoint).commRingCatIsoToRingEquiv).trans
      (asIso (j.residueFieldMap (g x))).commRingCatIsoToRingEquiv
  have hmaps : (i.residueFieldMap x).hom.comp (f.residueFieldMap (i x)).hom =
      (g.residueFieldMap x).hom.comp
        ((j.residueFieldMap (g x)).hom.comp
          (Y.residueFieldCongr hpoint).hom.hom) := by
    have hh := congrArg CommRingCat.Hom.hom (Scheme.Hom.residueFieldMap_congr h x)
    rw [Scheme.residueFieldMap_comp, Scheme.residueFieldMap_comp] at hh
    have hinv {a b : Y} (hab : a = b) : (Y.residueFieldCongr hab).hom.hom.comp
        ((Y.residueFieldCongr hab.symm).hom.hom) = RingHom.id _ := by
      have hh := Scheme.residueFieldCongr_trans_hom Y hab.symm hab
      rw [show hab.symm.trans hab = rfl from Subsingleton.elim _ _] at hh
      exact congrArg CommRingCat.Hom.hom hh
    have := congrArg (fun q : Y.residueField (j (g x)) →+* X'.residueField x =>
      q.comp (Y.residueFieldCongr hpoint).hom.hom) hh
    simpa [RingHom.comp_assoc, hinv hpoint, hinv hpoint.symm] using this.symm
  let := (f.residueFieldMap (i x)).hom.toAlgebra
  let := (g.residueFieldMap x).hom.toAlgebra
  have hcompat (z : Y.residueField (f (i x))) :
      ei ((f.residueFieldMap (i x)).hom z) =
        (g.residueFieldMap x).hom (ej z) := by
    have hv := congrArg (fun k : Y.residueField (f (i x)) →+* _ => k z) hmaps
    show (i.residueFieldMap x).hom ((f.residueFieldMap (i x)).hom z) =
      (g.residueFieldMap x).hom
        ((j.residueFieldMap (g x)).hom ((Y.residueFieldCongr hpoint).hom.hom z))
    simpa [ei, ej] using hv
  exact Algebra.trdeg_eq_of_ringEquiv ej ei hcompat

private theorem stratum_residue_trdeg_eq_of_nested {X Y : Scheme.{u}}
    (f : X ⟶ Y) (V' W' : IrreducibleCloseds X) (V W : IrreducibleCloseds Y)
    (hV'W' : V' ≤ W') (hVW : V ≤ W)
    (hW : IrreducibleCloseds.map f.base f.continuous W' = W)
    (hV : IrreducibleCloseds.map f.base f.continuous V' = V) :
    let i := stratumInclusion V' W' hV'W'
    let η' := genericPoint (stratumIdeal V').subscheme
    let := ((stratumMap f W' W hW).residueFieldMap (i η')).hom.toAlgebra
    let := ((stratumMap f V' V hV).residueFieldMap
      η').hom.toAlgebra
    Algebra.trdeg
        (((stratumIdeal W).subscheme).residueField (stratumMap f W' W hW (i η')))
        (((stratumIdeal W').subscheme).residueField (i η')) =
    Algebra.trdeg
        (((stratumIdeal V).subscheme).residueField
          (stratumMap f V' V hV (genericPoint (stratumIdeal V').subscheme)))
        (((stratumIdeal V').subscheme).residueField
          (genericPoint (stratumIdeal V').subscheme)) := by
  let i := stratumInclusion V' W' hV'W'
  let j := stratumInclusion V W hVW
  let gW := stratumMap f W' W hW
  let gV := stratumMap f V' V hV
  let η' := genericPoint (stratumIdeal V').subscheme
  have hsq := stratumMap_inclusion_square f V' W' V W hV'W' hVW hW hV
  have hiComp : IsClosedImmersion (i ≫ (stratumIdeal W').subschemeι) := by
    rw [stratumInclusion_fac]
    infer_instance
  have hjComp : IsClosedImmersion (j ≫ (stratumIdeal W).subschemeι) := by
    rw [stratumInclusion_fac]
    infer_instance
  have hiClosed : IsClosedImmersion i :=
    IsClosedImmersion.of_comp i (stratumIdeal W').subschemeι
  have hjClosed : IsClosedImmersion j :=
    IsClosedImmersion.of_comp j (stratumIdeal W).subschemeι
  have htr := residue_trdeg_eq_of_closed_immersion_factor i j gW gV hsq.symm η'
  simpa [i, j, gW, gV, η'] using htr

private theorem stratum_residue_trdeg_eq_ambient {X Y : Scheme.{u}}
    (f : X ⟶ Y) (A : IrreducibleCloseds X) (B : IrreducibleCloseds Y)
    (hAB : IrreducibleCloseds.map f.base f.continuous A = B) :
    let := (f.residueFieldMap ((stratumIdeal A).subschemeι
      (genericPoint (stratumIdeal A).subscheme))).hom.toAlgebra
    let := (stratumMap f A B hAB).residueFieldMap
      (genericPoint (stratumIdeal A).subscheme) |>.hom.toAlgebra
    Algebra.trdeg (Y.residueField
      (f ((stratumIdeal A).subschemeι (genericPoint (stratumIdeal A).subscheme))))
        (X.residueField ((stratumIdeal A).subschemeι
          (genericPoint (stratumIdeal A).subscheme))) =
      Algebra.trdeg
        (((stratumIdeal B).subscheme).residueField
          (stratumMap f A B hAB (genericPoint (stratumIdeal A).subscheme)))
        (((stratumIdeal A).subscheme).residueField
          (genericPoint (stratumIdeal A).subscheme)) := by
  let IA := stratumIdeal A
  let IB := stratumIdeal B
  let i := IA.subschemeι
  let j := IB.subschemeι
  let g := stratumMap f A B hAB
  let : IsIntegral IB.subscheme := vanishingSubscheme_isIntegral B
  have hsq : g ≫ j = i ≫ f := stratumMap_fac f A B hAB
  let η := genericPoint IA.subscheme
  have : IsClosedImmersion i := inferInstanceAs (IsClosedImmersion (stratumIdeal A).subschemeι)
  have : IsClosedImmersion j := inferInstanceAs (IsClosedImmersion (stratumIdeal B).subschemeι)
  have h := residue_trdeg_eq_of_closed_immersion_factor i j f g hsq η
  simpa [IA, IB, i, j, g, η] using h

private theorem stratum_functionField_trdeg_le_fiber_bound {X Y : Scheme.{u}}
    (f : X ⟶ Y) [LocallyOfFiniteType f] (e : ℕ)
    (he : ∀ y : Y, topologicalKrullDim (f.fiber y) ≤ (e : WithBot ℕ∞))
    (A : IrreducibleCloseds X) (B : IrreducibleCloseds Y)
    (hAB : IrreducibleCloseds.map f.base f.continuous A = B) :
    let : IsDominant (stratumMap f A B hAB) := stratumMap_dominant f A B hAB
    let := (dominantFunctionFieldMap (stratumMap f A B hAB)).toAlgebra
    Cardinal.toENat (Algebra.trdeg ((stratumIdeal B).subscheme).functionField
      ((stratumIdeal A).subscheme).functionField) ≤ e := by
  let IA := stratumIdeal A
  let IB := stratumIdeal B
  let g := stratumMap f A B hAB
  let : IsIntegral IB.subscheme := vanishingSubscheme_isIntegral B
  let : IsDominant g := stratumMap_dominant f A B hAB
  let η := genericPoint IA.subscheme
  let : Algebra IB.subscheme.functionField IA.subscheme.functionField :=
    (dominantFunctionFieldMap g).toAlgebra
  let : Algebra (Y.residueField (f (IA.subschemeι η)))
      (X.residueField (IA.subschemeι η)) :=
    (f.residueFieldMap (IA.subschemeι η)).hom.toAlgebra
  have hres := stratum_residue_trdeg_eq_ambient f A B hAB
  have hfun := residueTrdeg_eq_functionFieldTrdeg g
  have hbound := residue_trdeg_le_fiber_bound f e he (IA.subschemeι η)
  have htr : Cardinal.toENat (Algebra.trdeg IB.subscheme.functionField
      IA.subscheme.functionField) ≤ e := by
    rw [← hfun, ← hres]
    exact hbound
  simpa [IA, IB, g] using htr

private noncomputable def stratumTrdegNat {X Y : Scheme.{u}} (f : X ⟶ Y)
    (A : IrreducibleCloseds X) (B : IrreducibleCloseds Y)
    (hAB : IrreducibleCloseds.map f.base f.continuous A = B) : ℕ := by
  let : IsDominant (stratumMap f A B hAB) := stratumMap_dominant f A B hAB
  let : Algebra ((stratumIdeal B).subscheme).functionField
      ((stratumIdeal A).subscheme).functionField :=
    (dominantFunctionFieldMap (stratumMap f A B hAB)).toAlgebra
  exact (Cardinal.toENat (Algebra.trdeg ((stratumIdeal B).subscheme).functionField
    ((stratumIdeal A).subscheme).functionField)).toNat

private theorem stratumTrdegNat_le_fiber_bound {X Y : Scheme.{u}}
    (f : X ⟶ Y) [LocallyOfFiniteType f] (e : ℕ)
    (he : ∀ y : Y, topologicalKrullDim (f.fiber y) ≤ (e : WithBot ℕ∞))
    (A : IrreducibleCloseds X) (B : IrreducibleCloseds Y)
    (hAB : IrreducibleCloseds.map f.base f.continuous A = B) :
    stratumTrdegNat f A B hAB ≤ e := by
  simpa only [stratumTrdegNat, Cardinal.toNat_toENat] using
    ENat.toNat_le_of_le_natCast
      (stratum_functionField_trdeg_le_fiber_bound f e he A B hAB)

private theorem stratum_functionField_trdeg_eq_ambient_of_generic_support {X Y : Scheme.{u}}
    (f : X ⟶ Y) (A : IrreducibleCloseds X) (B : IrreducibleCloseds Y)
    (hAB : IrreducibleCloseds.map f.base f.continuous A = B) (x : X)
    (hA : (A : Set X) = closure ({x} : Set X)) :
    let : IsDominant (stratumMap f A B hAB) := stratumMap_dominant f A B hAB
    let := (dominantFunctionFieldMap (stratumMap f A B hAB)).toAlgebra
    let := (f.residueFieldMap x).hom.toAlgebra
    Cardinal.toENat (Algebra.trdeg ((stratumIdeal B).subscheme).functionField
      ((stratumIdeal A).subscheme).functionField) =
    Cardinal.toENat (Algebra.trdeg (Y.residueField (f x)) (X.residueField x)) := by
  let : IsDominant (stratumMap f A B hAB) := stratumMap_dominant f A B hAB
  let : Algebra ((stratumIdeal B).subscheme).functionField
      ((stratumIdeal A).subscheme).functionField :=
    (dominantFunctionFieldMap (stratumMap f A B hAB)).toAlgebra
  let η := genericPoint (stratumIdeal A).subscheme
  let : Algebra (Y.residueField (f ((stratumIdeal A).subschemeι η)))
      (X.residueField ((stratumIdeal A).subschemeι η)) :=
    (f.residueFieldMap ((stratumIdeal A).subschemeι η)).hom.toAlgebra
  let : Algebra (Y.residueField (f x)) (X.residueField x) :=
    (f.residueFieldMap x).hom.toAlgebra
  have hη : (stratumIdeal A).subschemeι η = x := by
    have hgenEq : (stratumIdeal A).subschemeι η = A.isIrreducible.genericPoint := by
      simpa [η] using stratum_subscheme_genericPoint A
    have hx : IsGenericPoint x (A : Set X) := by
      rw [hA]
      exact isGenericPoint_closure
    exact hgenEq.trans ((A.isIrreducible.isGenericPoint_genericPoint A.isClosed).eq hx)
  cases hη
  have hres := stratum_residue_trdeg_eq_ambient f A B hAB
  have hfun := residueTrdeg_eq_functionFieldTrdeg (stratumMap f A B hAB)
  exact congrArg Cardinal.toENat (hfun.symm.trans hres.symm)

private theorem stratum_dimension_formula {X Y : Scheme.{u}}
    [IsLocallyNoetherian X] [IsLocallyNoetherian Y]
    (hY : Scheme.IsUniversallyCatenary Y)
    (f : X ⟶ Y) [LocallyOfFiniteType f]
    (V' W' : IrreducibleCloseds X) (W : IrreducibleCloseds Y)
    (hV'W' : V' ≤ W')
    (hW : IrreducibleCloseds.map f.base f.continuous W' = W) :
    let g := stratumMap f W' W hW
    let p' := stratumInclusion V' W' hV'W'
      (genericPoint (stratumIdeal V').subscheme)
    let : LocallyOfFiniteType (stratumIdeal W').subschemeι :=
      inferInstance
    let : LocallyOfFiniteType (stratumIdeal W).subschemeι :=
      inferInstance
    let : IsLocallyNoetherian (stratumIdeal W').subscheme :=
      LocallyOfFiniteType.isLocallyNoetherian (stratumIdeal W').subschemeι
    let : IsLocallyNoetherian (stratumIdeal W).subscheme :=
      LocallyOfFiniteType.isLocallyNoetherian (stratumIdeal W).subschemeι
    let : LocallyOfFiniteType g := stratumMap_locallyOfFiniteType f W' W hW
    let : IsDominant g := stratumMap_dominant f W' W hW
    let := (g.residueFieldMap p').hom.toAlgebra
    let := (dominantFunctionFieldMap g).toAlgebra
    ringKrullDim (((stratumIdeal W').subscheme).presheaf.stalk p') +
        (Cardinal.toENat (Algebra.trdeg
          (((stratumIdeal W).subscheme).residueField (g p'))
          (((stratumIdeal W').subscheme).residueField p')) : WithBot ℕ∞) =
      ringKrullDim (((stratumIdeal W).subscheme).presheaf.stalk (g p')) +
        (Cardinal.toENat (Algebra.trdeg
          ((stratumIdeal W).subscheme).functionField
          ((stratumIdeal W').subscheme).functionField) : WithBot ℕ∞) := by
  let g := stratumMap f W' W hW
  let p' := stratumInclusion V' W' hV'W'
    (genericPoint (stratumIdeal V').subscheme)
  let : LocallyOfFiniteType (stratumIdeal W').subschemeι :=
    inferInstance
  let : LocallyOfFiniteType (stratumIdeal W).subschemeι :=
    inferInstance
  let : IsLocallyNoetherian (stratumIdeal W').subscheme :=
    LocallyOfFiniteType.isLocallyNoetherian (stratumIdeal W').subschemeι
  let : IsLocallyNoetherian (stratumIdeal W).subscheme :=
    LocallyOfFiniteType.isLocallyNoetherian (stratumIdeal W).subschemeι
  let : LocallyOfFiniteType g := stratumMap_locallyOfFiniteType f W' W hW
  let : IsDominant g := stratumMap_dominant f W' W hW
  let := (g.residueFieldMap p').hom.toAlgebra
  let := (dominantFunctionFieldMap g).toAlgebra
  have hcat : Scheme.IsUniversallyCatenary (stratumIdeal W).subscheme :=
    universallyCatenary_of_locallyFiniteType hY (stratumIdeal W).subschemeι
  have hdim := localDimension_add_trdeg_eq g hcat p'
  simpa [g] using hdim

private theorem stratum_topCodim_formula {X Y : Scheme.{u}}
    [IsLocallyNoetherian X] [IsLocallyNoetherian Y]
    (hY : Scheme.IsUniversallyCatenary Y)
    (f : X ⟶ Y) [LocallyOfFiniteType f]
    (V' W' : IrreducibleCloseds X) (V W : IrreducibleCloseds Y)
    (hV'W' : V' ≤ W') (hVW : V ≤ W)
    (hW : IrreducibleCloseds.map f.base f.continuous W' = W)
    (hV : IrreducibleCloseds.map f.base f.continuous V' = V) :
    let p' := stratumInclusion V' W' hV'W'
      (genericPoint (stratumIdeal V').subscheme)
    let g := stratumMap f W' W hW
    let : IsDominant g := stratumMap_dominant f W' W hW
    let := (g.residueFieldMap p').hom.toAlgebra
    let := (dominantFunctionFieldMap g).toAlgebra
    (IrreducibleClosedsCodim.topCodim V' W' : WithBot ℕ∞) +
        (Cardinal.toENat (Algebra.trdeg
          (((stratumIdeal W).subscheme).residueField (g p'))
          (((stratumIdeal W').subscheme).residueField p')) : WithBot ℕ∞) =
      (IrreducibleClosedsCodim.topCodim V W : WithBot ℕ∞) +
        (Cardinal.toENat (Algebra.trdeg
          ((stratumIdeal W).subscheme).functionField
          ((stratumIdeal W').subscheme).functionField) : WithBot ℕ∞) := by
  let η' := genericPoint (stratumIdeal V').subscheme
  let η := genericPoint (stratumIdeal V).subscheme
  let p' := stratumInclusion V' W' hV'W' η'
  let p := stratumInclusion V W hVW η
  let g := stratumMap f W' W hW
  let : IsDominant g := stratumMap_dominant f W' W hW
  let : Algebra ((stratumIdeal W).subscheme).functionField
      ((stratumIdeal W').subscheme).functionField :=
    (dominantFunctionFieldMap g).toAlgebra
  have hsq := stratumMap_inclusion_square f V' W' V W hV'W' hVW hW hV
  have hpoint : g p' = p := by
    have hh := congrArg (fun q : (stratumIdeal V').subscheme ⟶
        (stratumIdeal W).subscheme => q η') hsq
    have hgen := stratumMap_genericPoint f V' V hV
    simpa [p', p, g, η', η, Scheme.Hom.comp_apply, hgen] using hh
  have hdim := stratum_dimension_formula hY f V' W' W hV'W' hW
  have hlocal' := stratumInclusion_localDimension_eq_topCodim V' W' hV'W'
  have hlocal : ringKrullDim
      (((stratumIdeal W).subscheme).presheaf.stalk (g p')) =
      (IrreducibleClosedsCodim.topCodim V W : WithBot ℕ∞) := by
    rw [hpoint]
    exact stratumInclusion_localDimension_eq_topCodim V W hVW
  dsimp only at hdim
  rw [hlocal', hlocal] at hdim
  simpa [p', g] using hdim

private theorem enat_add_toNat {a b c d : ℕ∞}
    (ha : a ≠ ⊤) (hb : b ≠ ⊤) (hc : c ≠ ⊤) (hd : d ≠ ⊤)
    (h : (a : WithBot ℕ∞) + b = c + d) :
    a.toNat + b.toNat = c.toNat + d.toNat := by
  have h' : a + b = c + d := by exact_mod_cast h
  have h'' := congrArg ENat.toNat h'
  simpa only [ENat.toNat_add ha hb, ENat.toNat_add hc hd] using h''

private theorem nested_point_trdeg_eq_functionField_trdeg {X Y : Scheme.{u}}
    (f : X ⟶ Y) (V' W' : IrreducibleCloseds X) (V W : IrreducibleCloseds Y)
    (hV'W' : V' ≤ W') (hVW : V ≤ W)
    (hW : IrreducibleCloseds.map f.base f.continuous W' = W)
    (hV : IrreducibleCloseds.map f.base f.continuous V' = V) :
    let i := stratumInclusion V' W' hV'W'
    let gW := stratumMap f W' W hW
    let gV := stratumMap f V' V hV
    let : IsDominant gV := stratumMap_dominant f V' V hV
    let η' := genericPoint (stratumIdeal V').subscheme
    let := (gW.residueFieldMap (i η')).hom.toAlgebra
    let := (gV.residueFieldMap η').hom.toAlgebra
    let := (dominantFunctionFieldMap gV).toAlgebra
    Cardinal.toENat (Algebra.trdeg
      (((stratumIdeal W).subscheme).residueField (gW (i η')))
      (((stratumIdeal W').subscheme).residueField (i η'))) =
      Cardinal.toENat (Algebra.trdeg
        ((stratumIdeal V).subscheme).functionField
        ((stratumIdeal V').subscheme).functionField) := by
  let i := stratumInclusion V' W' hV'W'
  let gW := stratumMap f W' W hW
  let gV := stratumMap f V' V hV
  let : IsDominant gV := stratumMap_dominant f V' V hV
  let η' := genericPoint (stratumIdeal V').subscheme
  let := (gV.residueFieldMap η').hom.toAlgebra
  let := (dominantFunctionFieldMap gV).toAlgebra
  have hn := stratum_residue_trdeg_eq_of_nested f V' W' V W hV'W' hVW hW hV
  have hf := residueTrdeg_eq_functionFieldTrdeg gV
  have h := congrArg Cardinal.toENat (hn.trans hf)
  simpa [i, η', gW, gV] using h

private theorem stratum_codim_nat_add_trdeg {X Y : Scheme.{u}}
    [IsNoetherian X] [IsNoetherian Y]
    (hY : Scheme.IsUniversallyCatenary Y)
    (f : X ⟶ Y) [LocallyOfFiniteType f] (e : ℕ)
    (he : ∀ y : Y, topologicalKrullDim (f.fiber y) ≤ (e : WithBot ℕ∞))
    (V' W' : IrreducibleCloseds X) (V W : IrreducibleCloseds Y)
    (hV'W' : V' ≤ W') (hVW : V ≤ W)
    (hW : IrreducibleCloseds.map f.base f.continuous W' = W)
    (hV : IrreducibleCloseds.map f.base f.continuous V' = V) :
    let : IsDominant (stratumMap f V' V hV) := stratumMap_dominant f V' V hV
    let : IsDominant (stratumMap f W' W hW) := stratumMap_dominant f W' W hW
    let := (dominantFunctionFieldMap (stratumMap f V' V hV)).toAlgebra
    let := (dominantFunctionFieldMap (stratumMap f W' W hW)).toAlgebra
    (IrreducibleClosedsCodim.topCodim V W).toNat +
        (Cardinal.toENat (Algebra.trdeg ((stratumIdeal W).subscheme).functionField
          ((stratumIdeal W').subscheme).functionField)).toNat =
      (IrreducibleClosedsCodim.topCodim V' W').toNat +
        (Cardinal.toENat (Algebra.trdeg ((stratumIdeal V).subscheme).functionField
          ((stratumIdeal V').subscheme).functionField)).toNat := by
  let gV := stratumMap f V' V hV
  let gW := stratumMap f W' W hW
  let : IsDominant gV := stratumMap_dominant f V' V hV
  let : IsDominant gW := stratumMap_dominant f W' W hW
  let : Algebra ((stratumIdeal V).subscheme).functionField
      ((stratumIdeal V').subscheme).functionField :=
    (dominantFunctionFieldMap gV).toAlgebra
  let : Algebra ((stratumIdeal W).subscheme).functionField
      ((stratumIdeal W').subscheme).functionField :=
    (dominantFunctionFieldMap gW).toAlgebra
  have hpoint := nested_point_trdeg_eq_functionField_trdeg f V' W' V W
    hV'W' hVW hW hV
  have hformula := stratum_topCodim_formula hY f V' W' V W hV'W' hVW hW hV
  dsimp only at hpoint hformula
  rw [hpoint] at hformula
  have hn := stratum_functionField_trdeg_le_fiber_bound f e he V' V hV
  have hm := stratum_functionField_trdeg_le_fiber_bound f e he W' W hW
  have hmNe : Cardinal.toENat (Algebra.trdeg ((stratumIdeal W).subscheme).functionField
      ((stratumIdeal W').subscheme).functionField) ≠ ⊤ :=
    ne_top_of_le_ne_top (by simp) hm
  have hnat := enat_add_toNat (topCodim_ne_top X _ _)
    (ne_top_of_le_ne_top (by simp) hn) (topCodim_ne_top Y _ _) hmNe hformula
  simpa [Nat.add_comm] using hnat.symm

private theorem suffix_nat_sum_split {k : ℕ} {M : Type*} [AddCommMonoid M]
    (q : Fin k → M) (i : Fin k) :
    (∑ j : Fin k, if i.val ≤ j.val then q j else 0) =
      q i + ∑ j : Fin k, if i.val < j.val then q j else 0 := by
  classical
  let s := Finset.univ.filter (fun j : Fin k => i.val ≤ j.val)
  have hi : i ∈ s := by simp [s]
  have hs : s.erase i = Finset.univ.filter (fun j : Fin k => i.val < j.val) := by
    ext j
    simp only [s, Finset.mem_erase, Finset.mem_filter, Finset.mem_univ, true_and, ne_eq,
      Fin.ext_iff]
    constructor <;> intro h <;> omega
  have hsum := Finset.add_sum_erase s q hi
  rw [hs] at hsum
  simpa [s, Finset.sum_filter] using hsum.symm

private theorem shifted_suffix_nat_sum {k : ℕ} {M : Type*} [AddCommMonoid M]
    (q : Fin (k + 1) → M)
    (i : Fin (k + 1)) :
    (∑ j : Fin (k + 1), if i.val ≤ j.val then q j else 0) =
      q i + ∑ j : Fin k, if i.val ≤ j.val then q (Fin.succ j) else 0 := by
  classical
  refine Fin.cases ?_ ?_ i
  · simp [Fin.sum_univ_succ]
  · intro i
    rw [Fin.sum_univ_succ]
    simp only [Fin.val_zero, Fin.val_succ]
    have h := suffix_nat_sum_split (fun j : Fin k => q (Fin.succ j)) i
    simpa [Nat.succ_le_succ_iff, Nat.succ_lt_succ_iff] using h

private theorem suffix_nat_sum_last {k : ℕ} {M : Type*} [AddCommMonoid M]
    (q : Fin (k + 1) → M)
    (i : Fin (k + 1)) :
    (∑ j : Fin (k + 1), if i.val ≤ j.val then q j else 0) =
      q (Fin.last k) + ∑ j : Fin k,
        if i.val ≤ j.val then q (Fin.castSucc j) else 0 := by
  classical
  rw [Fin.sum_univ_castSucc]
  have hi : i.val ≤ k := by omega
  simp [Fin.val_castSucc, Fin.val_last, hi, add_comm]

private theorem filtered_add_eq_int {ι : Type*} [Fintype ι]
    (P : ι → Prop) [DecidablePred P] (a b c d : ι → ℕ)
    (h : ∀ i, P i → a i + b i = c i + d i) :
    (∑ i, if P i then (a i : ℤ) else 0) +
        (∑ i, if P i then (b i : ℤ) else 0) =
      (∑ i, if P i then (c i : ℤ) else 0) +
        (∑ i, if P i then (d i : ℤ) else 0) := by
  classical
  rw [← Finset.sum_add_distrib, ← Finset.sum_add_distrib]
  apply Finset.sum_congr rfl
  intro i _
  by_cases hp : P i
  · simpa [hp] using congrArg (fun z : ℕ => (z : ℤ)) (h i hp)
  · simp [hp]

private theorem nat_sub_suffix_bound {u v u' v' n m e : ℕ}
    (h : (u : ℤ) - v = (u' : ℤ) - v' + n - m)
    (hn : n ≤ e) (hm : m ≤ e) :
    u - v + m ≤ u' - v' + e := by
  omega

private theorem sequence_weight_bound {k : ℕ}
    (upT upS : Fin (k + 1) → ℕ) (downT downS : Fin k → ℕ)
    (n m : Fin (k + 1) → ℕ) (e : ℕ)
    (hu : ∀ j, upT j + m j = upS j + n j)
    (hd : ∀ j : Fin k,
      downT j + m (Fin.castSucc j) = downS j + n (Fin.succ j))
    (hn : ∀ j, n j ≤ e) (hm : m (Fin.last k) ≤ e) :
    (k + (Finset.univ.sup fun i : Fin (k + 1) =>
      (∑ j : Fin (k + 1), if i.val ≤ j.val then upT j else 0) -
      (∑ j : Fin k, if i.val ≤ j.val then downT j else 0)) : ℕ) +
        m (Fin.last k) ≤
      (k + (Finset.univ.sup fun i : Fin (k + 1) =>
      (∑ j : Fin (k + 1), if i.val ≤ j.val then upS j else 0) -
      (∑ j : Fin k, if i.val ≤ j.val then downS j else 0)) : ℕ) + e := by
  classical
  let UT (i : Fin (k + 1)) : ℤ :=
    ∑ j : Fin (k + 1), if i.val ≤ j.val then (upT j : ℤ) else 0
  let DT (i : Fin (k + 1)) : ℤ :=
    ∑ j : Fin k, if i.val ≤ j.val then (downT j : ℤ) else 0
  let US (i : Fin (k + 1)) : ℤ :=
    ∑ j : Fin (k + 1), if i.val ≤ j.val then (upS j : ℤ) else 0
  let DS (i : Fin (k + 1)) : ℤ :=
    ∑ j : Fin k, if i.val ≤ j.val then (downS j : ℤ) else 0
  let MT (i : Fin (k + 1)) : ℤ :=
    ∑ j : Fin (k + 1), if i.val ≤ j.val then (m j : ℤ) else 0
  let NT (i : Fin (k + 1)) : ℤ :=
    ∑ j : Fin (k + 1), if i.val ≤ j.val then (n j : ℤ) else 0
  let MD (i : Fin (k + 1)) : ℤ :=
    ∑ j : Fin k, if i.val ≤ j.val then (m (Fin.castSucc j) : ℤ) else 0
  let ND (i : Fin (k + 1)) : ℤ :=
    ∑ j : Fin k, if i.val ≤ j.val then (n (Fin.succ j) : ℤ) else 0
  have hU (i : Fin (k + 1)) : UT i + MT i = US i + NT i := by
    simpa [UT, MT, US, NT] using
      filtered_add_eq_int (fun j : Fin (k + 1) => i.val ≤ j.val)
        upT m upS n (fun j _ => hu j)
  have hD (i : Fin (k + 1)) : DT i + MD i = DS i + ND i := by
    simpa [DT, MD, DS, ND] using
      filtered_add_eq_int (fun j : Fin k => i.val ≤ j.val)
        downT (fun j => m (Fin.castSucc j)) downS (fun j => n (Fin.succ j))
        (fun j _ => hd j)
  have hN (i : Fin (k + 1)) : NT i = n i + ND i := by
    simpa [NT, ND] using shifted_suffix_nat_sum (fun j => (n j : ℤ)) i
  have hM (i : Fin (k + 1)) : MT i = m (Fin.last k) + MD i := by
    simpa [MT, MD] using suffix_nat_sum_last (fun j => (m j : ℤ)) i
  have hSigned (i : Fin (k + 1)) :
      UT i - DT i = US i - DS i + n i - m (Fin.last k) := by
    have hUi := hU i
    have hDi := hD i
    have hNi := hN i
    have hMi := hM i
    omega
  let ut (i : Fin (k + 1)) :=
    ∑ j : Fin (k + 1), if i.val ≤ j.val then upT j else 0
  let dt (i : Fin (k + 1)) :=
    ∑ j : Fin k, if i.val ≤ j.val then downT j else 0
  let us (i : Fin (k + 1)) :=
    ∑ j : Fin (k + 1), if i.val ≤ j.val then upS j else 0
  let ds (i : Fin (k + 1)) :=
    ∑ j : Fin k, if i.val ≤ j.val then downS j else 0
  have hSeg (i : Fin (k + 1)) : ut i - dt i + m (Fin.last k) ≤
      us i - ds i + e := by
    have hs : (ut i : ℤ) - dt i = (us i : ℤ) - ds i + n i - m (Fin.last k) := by
      simpa [ut, dt, us, ds, UT, DT, US, DS] using hSigned i
    exact nat_sub_suffix_bound hs (hn i) hm
  let qT (i : Fin (k + 1)) := ut i - dt i
  let qS (i : Fin (k + 1)) := us i - ds i
  have hterm (i : Fin (k + 1)) :
      qT i ≤ (Finset.univ.sup qS) + e - m (Fin.last k) := by
    have hle : qS i ≤ Finset.univ.sup qS := Finset.le_sup (Finset.mem_univ i)
    have hs := hSeg i
    dsimp [qT, qS] at hs ⊢
    have hsum : (ut i - dt i) + m (Fin.last k) ≤
        Finset.univ.sup qS + e :=
      (hs.trans (Nat.add_le_add_right hle e))
    exact le_tsub_of_add_le_right hsum
  have hsup : Finset.univ.sup qT ≤ Finset.univ.sup qS + e - m (Fin.last k) :=
    Finset.sup_le fun i _ => hterm i
  show k + Finset.univ.sup qT + m (Fin.last k) ≤ k + Finset.univ.sup qS + e
  omega

private theorem mapDistanceSystem_weight_bound {X Y : Scheme.{u}}
    [IsNoetherian X] [IsNoetherian Y]
    (hY : Scheme.IsUniversallyCatenary Y)
    (f : X ⟶ Y) [LocallyOfFiniteType f] (e : ℕ)
    (he : ∀ y : Y, topologicalKrullDim (f.fiber y) ≤ (e : WithBot ℕ∞))
    (I : Y.IdealSheafData) (x : X)
    (s : DistanceSystem X (I.comap f).support x) :
    let := (f.residueFieldMap x).hom.toAlgebra
    let t := mapDistanceSystem f I x s
    (t.weight : ℕ∞) + Cardinal.toENat
        (Algebra.trdeg (Y.residueField (f x)) (X.residueField x)) ≤
      (s.weight : ℕ∞) + e := by
  let := (f.residueFieldMap x).hom.toAlgebra
  let t := mapDistanceSystem f I x s
  let hV (i : Fin (s.k + 1)) :
      IrreducibleCloseds.map f.base f.continuous (s.V i) = t.V i := rfl
  let hW (i : Fin (s.k + 1)) :
      IrreducibleCloseds.map f.base f.continuous (s.W i) = t.W i := rfl
  let n : Fin (s.k + 1) → ℕ := fun i => stratumTrdegNat f (s.V i) (t.V i) (hV i)
  let m : Fin (s.k + 1) → ℕ := fun i => stratumTrdegNat f (s.W i) (t.W i) (hW i)
  have hn (i : Fin (s.k + 1)) : n i ≤ e :=
    stratumTrdegNat_le_fiber_bound f e he (s.V i) (t.V i) (hV i)
  have hm (i : Fin (s.k + 1)) : m i ≤ e :=
    stratumTrdegNat_le_fiber_bound f e he (s.W i) (t.W i) (hW i)
  have hu (j : Fin (s.k + 1)) :
      t.upCodimension j + m j = s.upCodimension j + n j := by
    have hcod := stratum_codim_nat_add_trdeg hY f e he
      (s.V j) (s.W j) (t.V j) (t.W j) (s.V_le_W j) (t.V_le_W j)
      (hW j) (hV j)
    simpa [n, m, stratumTrdegNat, DistanceSystem.upCodimension] using hcod
  have hd (j : Fin s.k) :
      t.downCodimension j + m (Fin.castSucc j) =
        s.downCodimension j + n (Fin.succ j) := by
    have hcod := stratum_codim_nat_add_trdeg hY f e he
      (s.V (Fin.succ j)) (s.W (Fin.castSucc j))
      (t.V (Fin.succ j)) (t.W (Fin.castSucc j))
      (s.V_next_le_W j) (t.V_next_le_W j)
      (hW (Fin.castSucc j)) (hV (Fin.succ j))
    convert hcod using 1 <;>
      simp [n, m, stratumTrdegNat, Cardinal.toNat_toENat,
        DistanceSystem.downCodimension] <;> rfl
  let last := Fin.last s.k
  have hmEq : m last = (Cardinal.toENat
      (Algebra.trdeg (Y.residueField (f x)) (X.residueField x))).toNat := by
    have h := congrArg ENat.toNat
      (stratum_functionField_trdeg_eq_ambient_of_generic_support f (s.W last) (t.W last)
        (hW last) x s.W_last_eq_closure)
    simpa only [m, stratumTrdegNat, Cardinal.toNat_toENat] using h
  have hweight := sequence_weight_bound t.upCodimension s.upCodimension
    t.downCodimension s.downCodimension n m e hu hd hn (hm last)
  have hglobal := residue_trdeg_le_fiber_bound f e he x
  have hne : Cardinal.toENat
      (Algebra.trdeg (Y.residueField (f x)) (X.residueField x)) ≠ ⊤ :=
    ne_top_of_le_ne_top (by simp) hglobal
  have hweightN : t.weight + m (Fin.last t.k) ≤ s.weight + e := by
    convert hweight using 1 <;> rfl
  have hweight' : (t.weight : ℕ∞) +
      Cardinal.toENat (Algebra.trdeg (Y.residueField (f x)) (X.residueField x)) ≤
      (s.weight : ℕ∞) + e := by
    rw [← ENat.natCast_toNat hne]
    exact_mod_cast (by simpa only [show Fin.last t.k = last from rfl, hmEq] using hweightN :
      t.weight + (Cardinal.toENat
        (Algebra.trdeg (Y.residueField (f x)) (X.residueField x))).toNat ≤ s.weight + e)
  simpa [t, DistanceSystem.weight] using hweight'

/-- **Stacks Project, Tag 0EIZ.** For a finite type morphism with fibres of dimension at
most `e`, the distance at the image point is at most the distance at the source point
plus `e` minus the residue-field transcendence degree. -/
@[stacks 0EIZ]
public theorem distanceFunction_add_trdeg_le
    {X Y : Scheme.{u}} (f : X ⟶ Y) [IsNoetherian Y]
    [LocallyOfFiniteType f] [QuasiCompact f]
    (hY : Scheme.IsUniversallyCatenary Y)
    (I : Y.IdealSheafData) (e : ℕ)
    (he : ∀ y : Y, topologicalKrullDim (f.fiber y) ≤ (e : WithBot ℕ∞))
    (x : X) :
    let : IsNoetherian X :=
      { toIsLocallyNoetherian := LocallyOfFiniteType.isLocallyNoetherian f
        toCompactSpace := QuasiCompact.compactSpace_of_compactSpace f }
    let := (f.residueFieldMap x).hom.toAlgebra
    distanceFunction Y I.support (f x) +
        Cardinal.toENat (Algebra.trdeg (Y.residueField (f x)) (X.residueField x)) ≤
      distanceFunction X (I.comap f).support x + (e : ℕ∞) := by
    let : IsNoetherian X :=
      { toIsLocallyNoetherian := LocallyOfFiniteType.isLocallyNoetherian f
        toCompactSpace := QuasiCompact.compactSpace_of_compactSpace f }
    let := (f.residueFieldMap x).hom.toAlgebra
    show distanceFunction Y I.support (f x) +
        Cardinal.toENat (Algebra.trdeg (Y.residueField (f x)) (X.residueField x)) ≤
      distanceFunction X (I.comap f).support x + (e : ℕ∞)
    by_cases hsource :
        (connectedComponent x ∩ ((I.comap f).support : Set X)).Nonempty
    · have htarget :
          (connectedComponent (f x) ∩ (I.support : Set Y)).Nonempty := by
        obtain ⟨z, hzcomp, hzsupport⟩ := hsource
        rw [Scheme.IdealSheafData.support_comap] at hzsupport
        exact ⟨f z, f.continuous.image_connectedComponent_subset x ⟨z, hzcomp, rfl⟩,
          hzsupport⟩
      have : Nonempty (DistanceSystem X (I.comap f).support x) :=
        nonempty_distanceSystem_of_connectedComponent_inter X
          (I.comap f).support x hsource
      obtain ⟨s, hs⟩ := ENat.exists_eq_iInf
        (fun s : DistanceSystem X (I.comap f).support x =>
          (s.weight : ℕ∞))
      have hbound :
          distanceFunction Y I.support (f x) +
            Cardinal.toENat (Algebra.trdeg (Y.residueField (f x)) (X.residueField x)) ≤
            (s.weight : ℕ∞) + (e : ℕ∞) := by
        rw [distanceFunction_eq_iInf_of_nonempty Y I.support (f x) htarget]
        exact (add_le_add (iInf_le _ (mapDistanceSystem f I x s)) le_rfl).trans
          (mapDistanceSystem_weight_bound hY f e he I x s)
      rwa [distanceFunction_eq_iInf_of_nonempty X (I.comap f).support x hsource, ← hs]
    · rw [distanceFunction_eq_top_of_disjoint X (I.comap f).support x hsource]
      simp

end Stacks.Algebraization

end
