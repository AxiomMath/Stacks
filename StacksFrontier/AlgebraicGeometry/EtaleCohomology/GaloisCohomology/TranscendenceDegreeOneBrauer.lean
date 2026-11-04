module

public import Mathlib.FieldTheory.FinTrdeg
public import Mathlib.FieldTheory.RatFunc.AsPolynomial
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.GaloisCohomology.Tsen
import StacksCore.Tactic.EgaSgaAttribute

/-!
# Brauer groups of fields of transcendence degree one

A field extension `K/k` which is finitely generated of transcendence degree one is finite over a
rational function field `k(x)` sitting inside `K`: any transcendental `x ∈ K` generates such a
subfield, and `K` is algebraic over it while remaining finitely generated, hence finite over it.
Over an algebraically closed `k` this makes `K` a `C₁` field by Tsen's theorem, so its Brauer
group is trivial; the same conclusion holds for every finite extension of `K`, because such an
extension is again finitely generated of transcendence degree one over `k`.

## Main results

* `isCField_one_of_essFiniteType_trdeg_eq_one`: a finitely generated field extension of
  transcendence degree one of an algebraically closed field is a `C₁` field.
* `brauerGroup_eq_one_of_essFiniteType_trdeg_eq_one`: its Brauer group is trivial.
* `brauerGroup_eq_one_of_module_finite_of_essFiniteType_trdeg_eq_one`: the Brauer group of every
  finite extension of such a field is trivial.

## Implementation notes

"Finitely generated as a field extension" is spelled `Algebra.EssFiniteType k K`; for a field
extension this is equivalent to `(⊤ : IntermediateField k K).FG` by
`IntermediateField.fg_top_iff`. The transcendence degree is the cardinal `Algebra.trdeg`, so the
hypothesis of transcendence degree one reads `Algebra.trdeg k K = 1`.

The subfield `k(x)` is `IntermediateField.adjoin k {x}`, written `k⟮x⟯`, and
`RatFunc.algEquivOfTranscendental` identifies it with `RatFunc k` for transcendental `x`. Tsen's
theorem is consumed through `IsCField` rather than through
`brauerGroup_eq_one_of_module_finite_tower_ratFunc`: `IsCField` is universe-polymorphic in both
fields and is stable under `IsCField.of_ringEquiv`, so no `Algebra (RatFunc k) K` instance has to
be manufactured on `K` itself.

The transcendence degree hypothesis is used twice: once to produce a transcendental element, and
once — through `AlgebraicIndependent.isTranscendenceBasis_of_trdeg_le_of_finite` — to know that a
single such element already spans, so that `K` is algebraic over `k⟮x⟯`. The index type of the
transcendence basis must live in the same universe as `K`, since `Algebra.trdeg k K ≤ #ι`
compares two cardinals; `PUnit` in the right universe is used for this.

## References

* [Stacks Project, Tag 03RF](https://stacks.math.columbia.edu/tag/03RF): this is the
  field-theoretic half of that tag, which asserts the vanishing of the Brauer group of the
  function field of a curve over an algebraically closed field.
* [Stacks Project, Tag 03RG](https://stacks.math.columbia.edu/tag/03RG): the vanishing of
  `H^q(Spec K, 𝐆_m)` for `q ≥ 1`, whose proof reduces to the statements here by writing a
  transcendence-degree-one extension as a colimit of finitely generated ones.
-/

@[expose] public noncomputable section

universe u v

/-- A finitely generated field extension of transcendence degree one contains a transcendental
element over which the whole extension is algebraic. -/
theorem exists_transcendental_isAlgebraic_adjoin_of_trdeg_eq_one
    (k : Type u) [Field k] (K : Type v) [Field K] [Algebra k K]
    (h : Algebra.trdeg k K = 1) :
    ∃ x : K, Transcendental k x ∧ Algebra.IsAlgebraic (IntermediateField.adjoin k {x}) K := by
  have hne : Algebra.trdeg k K ≠ 0 := by rw [h]; exact one_ne_zero
  have htr : Algebra.Transcendental k K := trdeg_ne_zero_iff.mp hne
  obtain ⟨x, hx⟩ := Algebra.Transcendental.transcendental (R := k) (A := K)
  refine ⟨x, hx, ?_⟩
  have hind : AlgebraicIndependent k (fun _ : PUnit.{v + 1} => x) :=
    algebraicIndependent_unique_type_iff.mpr hx
  have hb : IsTranscendenceBasis k (fun _ : PUnit.{v + 1} => x) :=
    hind.isTranscendenceBasis_of_trdeg_le_of_finite (by simp [h])
  have he : IntermediateField.adjoin k (Set.range (fun _ : PUnit.{v + 1} => x)) =
      IntermediateField.adjoin k {x} := by
    rw [Set.range_const]
  exact he ▸ hb.isAlgebraic_field

/-- A finitely generated field extension of transcendence degree one of an algebraically closed
field is a `C₁` field: it is finite over a rational function field, which is `C₁` by Tsen's
theorem, and the `C₁` property passes to finite extensions. -/
@[sga "4½ Arcata 3.2.3" "special case"]
theorem isCField_one_of_essFiniteType_trdeg_eq_one (k : Type u) [Field k] [IsAlgClosed k]
    (K : Type v) [Field K] [Algebra k K] [Algebra.EssFiniteType k K]
    (h : Algebra.trdeg k K = 1) : IsCField K 1 := by
  obtain ⟨x, hx, halg⟩ := exists_transcendental_isAlgebraic_adjoin_of_trdeg_eq_one k K h
  have halg' : Algebra.IsAlgebraic (IntermediateField.adjoin k {x}) K := halg
  have hess : Algebra.EssFiniteType (IntermediateField.adjoin k {x}) K :=
    Algebra.EssFiniteType.of_comp k (IntermediateField.adjoin k {x}) K
  have hfin : Module.Finite (IntermediateField.adjoin k {x}) K :=
    Algebra.finite_of_essFiniteType_of_isAlgebraic
  exact isCField_one_of_module_finite (IntermediateField.adjoin k {x}) K
    (IsCField.of_ringEquiv (isCField_one_ratFunc k)
      (RatFunc.algEquivOfTranscendental x hx).toRingEquiv)

/-- The Brauer group of a finitely generated field extension of transcendence degree one of an
algebraically closed field is trivial. -/
@[sga "4½ Arcata 3.2.2" "special case"]
theorem brauerGroup_eq_one_of_essFiniteType_trdeg_eq_one (k : Type u) [Field k] [IsAlgClosed k]
    (K : Type v) [Field K] [Algebra k K] [Algebra.EssFiniteType k K]
    (h : Algebra.trdeg k K = 1) (y : BrauerGroup K) : y = 1 :=
  brauerGroup_eq_one_of_isCField K (isCField_one_of_essFiniteType_trdeg_eq_one k K h) y

/-- A finite extension of a finitely generated field extension of transcendence degree one is
again finitely generated of transcendence degree one. -/
theorem essFiniteType_and_trdeg_eq_one_of_module_finite (k : Type u) [Field k]
    (K : Type v) [Field K] [Algebra k K] [Algebra.EssFiniteType k K]
    (h : Algebra.trdeg k K = 1) (K' : Type v) [Field K'] [Algebra K K'] [Module.Finite K K']
    [Algebra k K'] [IsScalarTower k K K'] :
    Algebra.EssFiniteType k K' ∧ Algebra.trdeg k K' = 1 := by
  have hess : Algebra.EssFiniteType k K' := Algebra.EssFiniteType.comp k K K'
  refine ⟨hess, ?_⟩
  have hzero : Algebra.trdeg K K' = 0 := trdeg_eq_zero
  have := trdeg_add_eq k K (A := K')
  rw [hzero, add_zero, h] at this
  exact this.symm

/-- The Brauer group of every finite extension of a finitely generated field extension of
transcendence degree one of an algebraically closed field is trivial.

This is the shape in which the higher vanishing of Stacks 03RG consumes Tsen's theorem: the
vanishing criterion of Stacks 03R8 asks for the Brauer group of every finite extension, not just
of the field itself. -/
@[sga "4½ Arcata 3.2.2" "special case"]
theorem brauerGroup_eq_one_of_module_finite_of_essFiniteType_trdeg_eq_one
    (k : Type u) [Field k] [IsAlgClosed k]
    (K : Type v) [Field K] [Algebra k K] [Algebra.EssFiniteType k K]
    (h : Algebra.trdeg k K = 1) (K' : Type v) [Field K'] [Algebra K K'] [Module.Finite K K']
    [Algebra k K'] [IsScalarTower k K K'] (y : BrauerGroup K') : y = 1 := by
  obtain ⟨hess, htr⟩ := essFiniteType_and_trdeg_eq_one_of_module_finite k K h K'
  exact brauerGroup_eq_one_of_essFiniteType_trdeg_eq_one k K' htr y

end
