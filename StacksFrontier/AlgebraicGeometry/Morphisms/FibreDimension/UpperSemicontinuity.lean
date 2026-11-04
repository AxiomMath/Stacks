module

public import Mathlib.AlgebraicGeometry.Morphisms.UniversallyClosed
public import Mathlib.Topology.Semicontinuity.Basic
public import StacksCore.Tactic.StacksAttribute
public import StacksFrontier.AlgebraicGeometry.Morphisms.FibreDimension.Basic
public import StacksFrontier.AlgebraicGeometry.Morphisms.FibreDimension.Openness

/-!
# Upper semicontinuity of the dimension of the fibres of a universally closed morphism

For a universally closed morphism locally of finite type the dimension of the fibres is an upper
semicontinuous function on the base: the locus where it is at most a given bound is open.

The proof is the source's. The locus in the source where the fibre has local dimension more than
`n` is closed (Tag 02FZ); a point of the base lies in its image exactly when the fibre over that
point has dimension more than `n`, and the image of a closed set is closed because the morphism is
closed. The remaining levels of the codomain are the level `⊥`, whose complement is the image of
the whole source, and the level `⊤`, below which the locus is the union of the loci for the
natural numbers.

## Main results

* `AlgebraicGeometry.upperSemicontinuous_fiberDimension` is **Stacks Tag 0D4I**.

## Implementation notes

The hypothesis is weaker than the source's properness: only universal closedness and local finite
type are used, so the separatedness and the quasi-compactness in properness are dropped. The
source's statement follows, since a proper morphism has both of these properties.

## References

* [Stacks Project, Tag 0D4I](https://stacks.math.columbia.edu/tag/0D4I)
* [Stacks Project, Tag 02FZ](https://stacks.math.columbia.edu/tag/02FZ)
-/

@[expose] public section

open CategoryTheory TopologicalSpace

universe u

namespace AlgebraicGeometry

/-- For a universally closed morphism locally of finite type, the locus in the base where the
fibre has dimension at most `n` is open: its complement is the image of the closed locus in the
source where the fibre has local dimension more than `n`. -/
@[ega "IV 13.1.5" "closedness of {y"]
private lemma isOpen_setOf_fiberDimension_le {X Y : Scheme.{u}} (f : X ⟶ Y)
    [UniversallyClosed f] [LocallyOfFiniteType f] (n : ℕ) :
    IsOpen {y : Y | f.fiberDimension y ≤ (n : WithBot ℕ∞)} := by
  let s : Set X :=
    {x | ¬ topologicalKrullDimAt (f.fiber (f x)) (f.asFiber x) ≤ (n : WithBot ℕ∞)}
  have hs : IsClosed s := (isOpen_setOf_fiberDimensionAt_le f n).isClosed_compl
  have heq : {y : Y | ¬ f.fiberDimension y ≤ (n : WithBot ℕ∞)} = f '' s := by
    ext y
    simp only [Set.mem_ofPred_eq, Set.mem_image, s, Scheme.Hom.fiberDimension_le_iff, not_forall]
    aesop
  simpa only [← heq, Set.compl_ofPred, not_not] using (f.isClosedMap s hs).isOpen_compl

/-- The locus where the fibre dimension is finite is the union of the loci where it is at most
`n`, hence open. -/
private lemma isOpen_setOf_fiberDimension_lt_top {X Y : Scheme.{u}} (f : X ⟶ Y)
    [UniversallyClosed f] [LocallyOfFiniteType f] :
    IsOpen (f.fiberDimension ⁻¹' Set.Iio (⊤ : WithBot ℕ∞)) := by
  have heq : f.fiberDimension ⁻¹' Set.Iio (⊤ : WithBot ℕ∞) =
      ⋃ n : ℕ, {y : Y | f.fiberDimension y ≤ (n : WithBot ℕ∞)} := by
    ext y
    simp only [Set.mem_preimage, Set.mem_Iio, Set.mem_iUnion, Set.mem_ofPred_eq]
    refine ⟨fun hy ↦ ?_, fun ⟨n, hn⟩ ↦ hn.trans_lt (WithBot.coe_lt_coe.mpr (ENat.natCast_lt_top n))⟩
    cases hd : f.fiberDimension y with
    | bot => exact ⟨0, by simp⟩
    | coe d =>
      cases d with
      | top => simp_all
      | coe n => exact ⟨n, by simp⟩
  rw [heq]
  exact isOpen_iUnion fun n ↦ isOpen_setOf_fiberDimension_le f n

/-- The locus where the fibre is empty is the complement of the image, hence open. -/
private lemma isOpen_setOf_fiberDimension_lt_zero {X Y : Scheme.{u}} (f : X ⟶ Y)
    [UniversallyClosed f] :
    IsOpen (f.fiberDimension ⁻¹' Set.Iio (((0 : ℕ) : ℕ∞) : WithBot ℕ∞)) := by
  have hne (y : Y) : Nonempty (f.fiber y) ↔ y ∈ Set.range f := by
    rw [(f.fiberHomeo y).nonempty_congr]
    simp only [Set.nonempty_coe_sort, Set.nonempty_def, Set.mem_preimage,
      Set.mem_singleton_iff, Set.mem_range]
  have heq : f.fiberDimension ⁻¹' Set.Iio (((0 : ℕ) : ℕ∞) : WithBot ℕ∞) = (Set.range f)ᶜ := by
    ext y
    simp only [Set.mem_preimage, Set.mem_Iio, Set.mem_compl_iff]
    rw [ENat.natCast_zero, ← bot_eq_zero, WithBot.lt_coe_bot,
      f.fiberDimension_eq_bot_iff_isEmpty]
    exact not_nonempty_iff.symm.trans (not_congr (hne y))
  rw [heq]
  exact f.isClosedMap.isClosed_range.isOpen_compl

/-- **Stacks Project, Tag 0D4I.** The dimension-of-fibres function of a universally closed
morphism of schemes locally of finite type is upper semicontinuous. In particular this holds for
a proper morphism, which is the source's statement. -/
@[stacks 0D4I, ega "IV 13.1.5" "universally closed"]
public lemma upperSemicontinuous_fiberDimension {X Y : Scheme.{u}} (f : X ⟶ Y)
    [UniversallyClosed f] [LocallyOfFiniteType f] :
    UpperSemicontinuous f.fiberDimension := by
  rw [upperSemicontinuous_iff_isOpen_preimage]
  intro b
  cases b with
  | bot => simp
  | coe b =>
    cases b with
    | top =>
      rw [WithBot.coe_top]
      exact isOpen_setOf_fiberDimension_lt_top f
    | coe n =>
      cases n with
      | zero => exact isOpen_setOf_fiberDimension_lt_zero f
      | succ n =>
        have heq : f.fiberDimension ⁻¹' Set.Iio ((((n + 1 : ℕ) : ℕ∞)) : WithBot ℕ∞) =
            {y : Y | f.fiberDimension y ≤ (n : WithBot ℕ∞)} := by
          ext y
          simp only [Set.mem_preimage, Set.mem_Iio, Set.mem_ofPred_eq]
          rw [show (((n + 1 : ℕ) : ℕ∞) : WithBot ℕ∞) = (n : WithBot ℕ∞) + 1 by norm_cast]
          exact ENat.WithBot.lt_add_one_iff
        rw [heq]
        exact isOpen_setOf_fiberDimension_le f n

end AlgebraicGeometry

end
