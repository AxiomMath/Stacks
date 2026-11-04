module

public import Mathlib.AlgebraicGeometry.IdealSheaf.Subscheme
public import Mathlib.AlgebraicGeometry.Morphisms.Immersion
public import Mathlib.AlgebraicGeometry.Properties
public import Mathlib.RingTheory.AlgebraicIndependent.TranscendenceBasis
public import StacksCore.Tactic.StacksAttribute
public import StacksFrontier.AlgebraicGeometry.Variety.Defs.Dimension.Formula
public import StacksFrontier.AlgebraicGeometry.NormalizationBaseChange.Basic
public import StacksFrontier.AlgebraicGeometry.Variety.Defs.Dimension.NonemptyOpen
public import StacksFrontier.Topology.Irreducible.GenericPoints
public import StacksFrontier.Topology.Dimension.ClosedSubsetDimension

/-!
# Dimension and the function fields of a scheme over a field

The dimension of an irreducible scheme locally of finite type over a field is the transcendence
degree of the residue field at its generic point, and for a general such scheme it is the
supremum of those transcendence degrees over the generic points of the irreducible components.

## Main results

* `AlgebraicGeometry.topologicalKrullDim_eq_trdeg_residueField` identifies the dimension of an
  irreducible locally algebraic scheme with the transcendence degree of its function field.
* `AlgebraicGeometry.topologicalKrullDim_eq_iSup_trdeg_residueField` computes the dimension of a
  locally algebraic scheme from its generic points.
* `AlgebraicGeometry.ringKrullDim_stalk_eq_zero_of_mem_genericPoints` shows that the local ring
  at a generic point of an irreducible component is zero-dimensional.
* `AlgebraicGeometry.topologicalKrullDim_eq_zero_of_subsingleton` computes the dimension of a
  nonempty space with at most one point.

## Implementation notes

The dimension is represented by `topologicalKrullDim X : WithBot ℕ∞`. Since a residue field of a
scheme locally of finite type over a field has finite transcendence degree, its cardinal-valued
transcendence degree is converted with `Cardinal.toENat` and then included in `WithBot ℕ∞`. The
canonical algebra structure on the residue field is induced by the structure morphism through
global sections and evaluation at the point. Mathlib's `genericPoints X` is the set of generic
points of the irreducible components; the closure of such a point is given the reduced induced
subscheme structure, so that the irreducible case applies to it.

## References

* [Stacks Project, Tag 0A21](https://stacks.math.columbia.edu/tag/0A21)
-/

@[expose] public section

open CategoryTheory TopologicalSpace
open CommRingCat

universe u

namespace AlgebraicGeometry

private instance nonempty_irreducibleCloseds {Y : Type*} [TopologicalSpace Y] [Nonempty Y] :
    Nonempty (IrreducibleCloseds Y) :=
  ⟨closure {Classical.arbitrary Y}, isIrreducible_singleton.closure, isClosed_closure⟩

/-- A nonempty space with at most one point has Krull dimension zero. -/
theorem topologicalKrullDim_eq_zero_of_subsingleton
    {Y : Type*} [TopologicalSpace Y] [Nonempty Y] [Subsingleton Y] :
    topologicalKrullDim Y = 0 :=
  have : Subsingleton (IrreducibleCloseds Y) := ⟨fun T T' ↦ IrreducibleCloseds.ext <| by
    have h : ∀ s : Set Y, s.Nonempty → s = Set.univ := fun s ⟨y, hy⟩ ↦
      Set.eq_univ_of_forall fun z ↦ Subsingleton.elim y z ▸ hy
    rw [h _ T.isIrreducible.nonempty, h _ T'.isIrreducible.nonempty]⟩
  Order.krullDim_eq_zero

/-- The local ring at a generic point of an irreducible component is zero-dimensional: the
image in `X` of the spectrum of the local ring is the set of generalizations of the point, and
a generic point of an irreducible component has no generalization but itself, so that spectrum
has a single point. -/
@[ega "I 2.4.3" "partial"]
theorem ringKrullDim_stalk_eq_zero_of_mem_genericPoints
    (X : Scheme.{u}) (x : X) (hx : x ∈ genericPoints X) :
    ringKrullDim (X.presheaf.stalk x) = 0 := by
  rw [← PrimeSpectrum.topologicalKrullDim_eq_ringKrullDim]
  have hi : Function.Injective (X.fromSpecStalk x) :=
    (inferInstance : IsPreimmersion (X.fromSpecStalk x)).isEmbedding.injective
  have hgen : ∀ y, X.fromSpecStalk x y = x := fun y ↦ by
    have hy : X.fromSpecStalk x y ∈ Set.range (X.fromSpecStalk x) := ⟨y, rfl⟩
    rw [Scheme.range_fromSpecStalk] at hy
    exact (mem_genericPoints_iff_forall_specializes_eq x).1 hx _ hy
  have : Subsingleton (PrimeSpectrum (X.presheaf.stalk x)) :=
    ⟨fun y z ↦ hi ((hgen y).trans (hgen z).symm)⟩
  exact topologicalKrullDim_eq_zero_of_subsingleton

/-- **The generic point of an irreducible space is a generic point of an irreducible component**,
namely of the whole space. Stated for a topological space, which is where the proof lives; the
scheme case is the instance at `X.carrier`. -/
theorem mem_genericPoints_of_isGenericPoint_univ {Y : Type*} [TopologicalSpace Y]
    [IrreducibleSpace Y] {y : Y} (hy : IsGenericPoint y Set.univ) : y ∈ genericPoints Y := by
  rw [genericPoints, Set.mem_ofPred_eq, hy, irreducibleComponents_eq_singleton]
  rfl

/-- **Stacks Project, Tag 0A21.** The dimension of an irreducible scheme locally of finite type
over a field equals the transcendence degree of its residue field at a generic point. -/
@[stacks 0A21 "irreducible_dimension_trdeg", ega "IV 4.1.1" "special case", ega "IV 5.2.1"]
theorem topologicalKrullDim_eq_trdeg_residueField
    (k : Type u) [Field k] (X : Scheme.{u}) (f : X ⟶ Spec (.of k))
    [IrreducibleSpace X] [LocallyOfFiniteType f] (x : X)
    (hx : IsGenericPoint x Set.univ) :
    letI : Algebra k (X.residueField x) :=
      ((Scheme.ΓSpecIso (.of k)).inv ≫ f.appTop ≫ X.Γevaluation x).hom.toAlgebra
    topologicalKrullDim X =
      (Cardinal.toENat (Algebra.trdeg k (X.residueField x)) : WithBot ℕ∞) := by
  let : Algebra k (X.residueField x) :=
    ((Scheme.ΓSpecIso (.of k)).inv ≫ f.appTop ≫ X.Γevaluation x).hom.toAlgebra
  rw [topologicalKrullDim_eq_topologicalKrullDimAt_of_irreducible k X f x,
    topologicalKrullDimAt_eq_trdeg_add_krullDim_stalk k X f x,
    ringKrullDim_stalk_eq_zero_of_mem_genericPoints X x
      (mem_genericPoints_of_isGenericPoint_univ hx), add_zero]

/-- The height of an irreducible closed subset is at most the dimension of that subset. -/
lemma height_le_topologicalKrullDim {T : Type*} [TopologicalSpace T]
    (Z : IrreducibleCloseds T) :
    (Order.height Z : WithBot ℕ∞) ≤ topologicalKrullDim (Z : Set T) := by
  let e : Set.Iic Z ↪o IrreducibleCloseds (Z : Set T) :=
    OrderEmbedding.ofMapLEIff
      (fun W ↦ ⟨Subtype.val ⁻¹' (W.1 : Set T),
        isIrreducible_preimage_subtypeVal W.1.isIrreducible W.2,
        W.1.isClosed.preimage continuous_subtype_val⟩)
      fun A B ↦ ⟨fun h x hx ↦ h (show (⟨x, A.2 hx⟩ : (Z : Set T)) ∈ _ from hx),
        fun h _ hx ↦ h hx⟩
  rw [Order.height_eq_krullDim_Iic]
  exact Order.krullDim_le_of_strictMono e e.strictMono

/-- Every irreducible closed subset lies in an irreducible component whose dimension is at least
its height. -/
private lemma exists_mem_irreducibleComponents_height_le {T : Type*} [TopologicalSpace T]
    (Z : IrreducibleCloseds T) :
    ∃ C ∈ irreducibleComponents T, (Order.height Z : WithBot ℕ∞) ≤ topologicalKrullDim C := by
  obtain ⟨C, hC, hZC⟩ :=
    exists_mem_irreducibleComponents_subset_of_isIrreducible (Z : Set T) Z.isIrreducible
  let C' : IrreducibleCloseds T := ⟨C, hC.1, isClosed_of_mem_irreducibleComponents C hC⟩
  exact ⟨C, hC, (WithBot.coe_le_coe.mpr (Order.height_mono (show Z ≤ C' from hZC))).trans
    (height_le_topologicalKrullDim C')⟩

/-- **The dimension of a space is the supremum of the dimensions of its irreducible
components.** -/
@[ega "0 14.1.4" "(ii), special case", ega "IV 14.2.4" "more general"]
lemma topologicalKrullDim_eq_iSup_irreducibleComponents (X : Type*) [TopologicalSpace X] :
    topologicalKrullDim X =
      ⨆ W : Set X, ⨆ (_ : W ∈ irreducibleComponents X), topologicalKrullDim W := by
  apply le_antisymm
  · rw [topologicalKrullDim, Order.krullDim_eq_iSup_height]
    refine iSup_le fun Z ↦ ?_
    obtain ⟨W, hW, h⟩ := exists_mem_irreducibleComponents_height_le Z
    exact le_iSup_of_le W (le_iSup_of_le hW h)
  · exact iSup_le fun W ↦ iSup_le fun _ ↦ topologicalKrullDim_subspace_le X W

/-- In a quasi-sober space the dimension is the supremum of the dimensions of the closures of
the generic points. -/
@[ega "0 14.1.4" "(ii), special case"]
private lemma topologicalKrullDim_eq_iSup_genericPoints
    (T : Type*) [TopologicalSpace T] [QuasiSober T] :
    topologicalKrullDim T =
      ⨆ x : genericPoints T, topologicalKrullDim (closure ({x.1} : Set T)) := by
  apply le_antisymm
  · rw [topologicalKrullDim, Order.krullDim_eq_iSup_height]
    refine iSup_le fun Z ↦ ?_
    obtain ⟨C, hC, h⟩ := exists_mem_irreducibleComponents_height_le Z
    refine le_iSup_of_le (genericPoints.ofComponent ⟨C, hC⟩) ?_
    rwa [genericPoints.isGenericPoint_ofComponent ⟨C, hC⟩]
  · exact iSup_le fun x ↦ topologicalKrullDim_subspace_le T _

/-- The dimension of the closure of a point of a locally algebraic scheme is the transcendence
degree of the residue field at that point.

The closure of `{x}`, with its reduced induced structure, is an irreducible scheme locally of
finite type over `k` whose generic point is `x`, so its dimension is the transcendence degree of
its residue field there; the closed immersion is surjective on stalks, so that residue field is
the residue field of `X` at `x`. -/
@[ega "IV 4.1.1" "special case",
  ega "IV 5.2.1" "more general",
  ega "IV 5.2.2" "irreducible case",
  sga "3 VIB 1.5" "more general",
  sga "4 XIV 2.3" "special case"]
lemma topologicalKrullDim_closure_singleton_eq_trdeg
    (k : Type u) [Field k] (X : Scheme.{u}) (f : X ⟶ Spec (.of k))
    [LocallyOfFiniteType f] (x : X) :
    letI : Algebra k (X.residueField x) :=
      ((Scheme.ΓSpecIso (.of k)).inv ≫ f.appTop ≫ X.Γevaluation x).hom.toAlgebra
    topologicalKrullDim (closure ({x} : Set X)) =
      (Cardinal.toENat (Algebra.trdeg k (X.residueField x)) : WithBot ℕ∞) := by
  let I := Scheme.IdealSheafData.vanishingIdeal (Closeds.closure ({x} : Set X))
  let y : I.subscheme := ⟨x, subset_closure (Set.mem_singleton x)⟩
  have : IrreducibleSpace I.subscheme :=
    Subtype.irreducibleSpace (isIrreducible_singleton (x := x)).closure
  have hy : IsGenericPoint y (Set.univ : Set I.subscheme) :=
    isGenericPoint_iff_specializes.mpr fun z ↦ iff_of_true
      (Topology.IsInducing.subtypeVal.specializes_iff.mp
        (show x ⤳ z.1 from specializes_iff_mem_closure.mpr z.2)) (Set.mem_univ z)
  have h := topologicalKrullDim_eq_trdeg_residueField k I.subscheme (I.subschemeι ≫ f) y hy
  rwa [← trdeg_residueField_of_surjectiveOnStalks k f I.subschemeι y] at h

/-- **Stacks Project, Tag 0A21.** The dimension of a scheme locally of finite type over a field
is the supremum of the transcendence degrees of the residue fields at the generic points of its
irreducible components. -/
@[stacks 0A21 "dimension_sup_trdeg", ega "IV 4.1.1", ega "IV 5.2.1" "more general", ega "IV 5.2.2"]
theorem topologicalKrullDim_eq_iSup_trdeg_residueField
    (k : Type u) [Field k] (X : Scheme.{u}) (f : X ⟶ Spec (.of k))
    [LocallyOfFiniteType f] :
    topologicalKrullDim X =
      ⨆ x : genericPoints X,
        letI : Algebra k (X.residueField x.1) :=
          ((Scheme.ΓSpecIso (.of k)).inv ≫ f.appTop ≫ X.Γevaluation x.1).hom.toAlgebra
        (Cardinal.toENat (Algebra.trdeg k (X.residueField x.1)) : WithBot ℕ∞) :=
  (topologicalKrullDim_eq_iSup_genericPoints X).trans
    (iSup_congr fun x ↦ topologicalKrullDim_closure_singleton_eq_trdeg k X f x.1)

end AlgebraicGeometry

end
