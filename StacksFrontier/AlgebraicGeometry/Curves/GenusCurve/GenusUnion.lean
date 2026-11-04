module

public import Mathlib.Algebra.Exact.Sequence
public import StacksFrontier.AlgebraicGeometry.ClosedImmersionCohomology.OverField
public import StacksFrontier.AlgebraicGeometry.CohomologyFinitenessResolution.Basic
public import StacksFrontier.AlgebraicGeometry.CurveEulerBridge.Basic
public import StacksFrontier.AlgebraicGeometry.EulerCharDirectSum.Basic
public import StacksFrontier.AlgebraicGeometry.ProperCohomologyFinite.OverFieldProper
public import StacksFrontier.AlgebraicGeometry.Curves.GenusCurve.CohomologyComparison
public import StacksFrontier.AlgebraicGeometry.Scheme.QuasiCoherent.ClosedUnionExactSequence
public import StacksFrontier.AlgebraicGeometry.Variety.Curve.SectionDegree
import StacksCore.Tactic.EgaSgaAttribute

/-!
# The genus of a union of two closed subschemes

For two closed subschemes `Z₁`, `Z₂` of a scheme `X` over a field `k`, with `W = Z₁ ∪ Z₂` proper
over `k` and `D = Z₁ ∩ Z₂` having no higher cohomology — which is the case whenever `D` is
affine, so in particular whenever the two pieces meet in finitely many points —

`h⁰(W) + deg D + genus Z₁ + genus Z₂ = h⁰(Z₁) + h⁰(Z₂) + genus W`,

where `h⁰` is the dimension over `k` of the ring of global functions and `deg D = h⁰(D)` is the
degree, that is the `k`-length, of the intersection.  This is
`AlgebraicGeometry.genus_union`.  When all three of `W`, `Z₁` and `Z₂` have only the constants
as global functions, so `h⁰ = 1` for each, it reads

`genus W + 1 = genus Z₁ + genus Z₂ + deg D`,

which is `AlgebraicGeometry.genus_union_add_one`, and its integer form
`AlgebraicGeometry.genus_union_cast` is the usual `g(Z₁ ∪ Z₂) = g(Z₁) + g(Z₂) + m - 1`.

## The ideal-sheaf convention, and where the input comes from

Closed subschemes are `AlgebraicGeometry.Scheme.IdealSheafData`, and the order on ideal
sheaves is the order on ideals, so for `I J : X.IdealSheafData` the scheme-theoretic **union**
`Z₁ ∪ Z₂` is cut out by `I ⊓ J` and the scheme-theoretic **intersection** `Z₁ ∩ Z₂` by `I ⊔ J`;
`StacksFrontier/AlgebraicGeometry/Scheme/QuasiCoherent/ClosedUnionExactSequence.lean` fixes that
convention and this file inherits it.  The one geometric input is the short exact sequence of
[Stacks, Tag 0C4J] proved there,

`0 ⟶ 𝒪_{Z₁ ∪ Z₂} ⟶ 𝒪_{Z₁} ⊞ 𝒪_{Z₂} ⟶ 𝒪_{Z₁ ∩ Z₂} ⟶ 0`,

as a sequence of modules on the ambient `X`
(`AlgebraicGeometry.Scheme.IdealSheafData.unionIntersection_shortExact`).  Everything else here
is the cohomological bookkeeping attached to it.

## Why the statement is an equality of natural numbers with no subtraction

`AlgebraicGeometry.genus` is `ℕ`-valued, being a `Module.finrank`.  Writing the classical
formula as `genus W = genus Z₁ + genus Z₂ + m - 1` in `ℕ` would use truncated subtraction, and
at `m = 0` it would be false: for two *disjoint* pieces with `genus Z₁ = 1` and `genus Z₂ = 0`
the right-hand side truncates to `0`, while `AlgebraicGeometry.genus_sigma` gives
`genus W = 1`.  Three formulations avoid the problem and all three are stated here.  The main
theorem carries the `h⁰` terms explicitly and needs no subtraction at all;
`AlgebraicGeometry.genus_union_add_one` moves the `-1` to the other side of the equality; and
`AlgebraicGeometry.genus_union_cast` casts to `ℤ`, where the subtraction is the honest one.
Carrying `0 < m` instead would also repair the `ℕ` form; it is not assumed here because the
`h⁰(W) = 1` hypothesis that the classical form needs anyway already forces `0 < m`, which is
`AlgebraicGeometry.zero_lt_finrank_structureSheafCohomology_zero_sup`.

## Consistency with two known special cases

**The disjoint case.** At `m = 0` the naive reading `genus W = genus Z₁ + genus Z₂ - 1`
*contradicts* `AlgebraicGeometry.genus_sigma`, which gives `genus W = genus Z₁ + genus Z₂` for a
disjoint union.  The main theorem has no such clash, and it is `h⁰` that absorbs the
discrepancy: a disjoint union has `h⁰(W) = h⁰(Z₁) + h⁰(Z₂)`, not `h⁰(W) = 1`, so the identity
reduces to `genus W = genus Z₁ + genus Z₂` — this is
`AlgebraicGeometry.genus_union_eq_add_of_finrank_sections_add`.  The hypothesis `h⁰ = 1` of
`AlgebraicGeometry.genus_union_add_one` is therefore not a convenience: it is what fails in the
disjoint case, and it is why the `+ m - 1` form is a statement about pieces that actually meet.

**The rational tail.** `Stacks.Curves.genus_complementaryCurve` is the case `m = 1` with
`genus Z₂ = 0`: `AlgebraicGeometry.genus_union_add_one` then reads
`genus W + 1 = genus Z₁ + 0 + 1`, that is `genus W = genus Z₁`, which is that theorem's
conclusion that contracting a rational tail does not change the genus.

## Main results

* `AlgebraicGeometry.finrank_cohomologyOverField_add_eq_of_shortExact_of_isZero`: the five-term
  dimension count attached to a short exact sequence of modules whose quotient has vanishing
  `H¹`.  No properness and no coherence; this is where the long exact sequence is used.
* `AlgebraicGeometry.genus_union`: **`h⁰(Z₁ ∪ Z₂) + deg(Z₁ ∩ Z₂) + genus Z₁ + genus Z₂ =
  h⁰(Z₁) + h⁰(Z₂) + genus(Z₁ ∪ Z₂)`.**
* `AlgebraicGeometry.genus_union_add_one`: `genus(Z₁ ∪ Z₂) + 1 = genus Z₁ + genus Z₂ +
  deg(Z₁ ∩ Z₂)` when all three pieces have only constant global functions.
* `AlgebraicGeometry.genus_union_cast`: the same in `ℤ`, as `g = g₁ + g₂ + m - 1`.
* `AlgebraicGeometry.genus_union_eq_add_of_finrank_sections_add`: the disjoint case, agreeing
  with `AlgebraicGeometry.genus_sigma`.
* `AlgebraicGeometry.finrank_structureSheafCohomology_zero_add_le_union`:
  `h⁰(Z₁) + h⁰(Z₂) ≤ h⁰(Z₁ ∪ Z₂) + h⁰(Z₁ ∩ Z₂)`, the left-exact end of the sequence, with no
  hypothesis on the cohomology of the intersection.
* `AlgebraicGeometry.genus_add_le_genus_union`: **`genus Z₁ + genus Z₂ ≤ genus (Z₁ ∪ Z₂)`**, with
  no `h⁰` and no connectedness hypothesis.  At `genus (Z₁ ∪ Z₂) = 0` it forces both pieces to
  have genus zero, which is the genus clause of `AlgebraicGeometry.IsRationalBridge` for the
  pieces of a decomposition of a genus-zero curve.
* `AlgebraicGeometry.zero_lt_finrank_structureSheafCohomology_zero_sup`: pieces whose union has
  only the constants as global functions meet, that is `0 < m`.

## Implementation notes

**Why a five-term count and not the Euler characteristic.** Additivity of the Euler
characteristic along a short exact sequence is available and unconditional
(`AlgebraicGeometry.eulerCharacteristic_add_of_shortExact`, [Stacks, Tag 08AA]), but reading
`χ = h⁰ - h¹` off it needs `Hⁿ(W, 𝒪_W) = 0` for all `n ≥ 2`, which is a dimension hypothesis on
`W`.  The truncated long exact sequence needs no such thing: the six-term piece

`0 ⟶ H⁰(W) ⟶ H⁰(Z₁) ⊕ H⁰(Z₂) ⟶ H⁰(D) ⟶ H¹(W) ⟶ H¹(Z₁) ⊕ H¹(Z₂) ⟶ H¹(D) = 0`

is exact as it stands, and its alternating sum of dimensions is
`Module.sum_neg_one_pow_finrank_eq_zero_of_exact_six`.  So the theorems below hold for closed
subschemes of any dimension, not only for curves.

**Where the hypotheses come from.** Properness is assumed for the union alone, and the pieces
inherit it: `Z₁`, `Z₂` and `D` are closed subschemes of `W`, the inclusion being
`AlgebraicGeometry.Scheme.IdealSheafData.inclusion`, which is a closed immersion and hence
finite, so `AlgebraicGeometry.isProper_subschemeι_comp_of_le` transports properness along `≤`.
Properness is used only for finite dimensionality of the cohomology modules that occur
([Stacks, Tag 02O6], `AlgebraicGeometry.finiteDimensional_cohomologyOverField_of_isProper`).
The vanishing of `H¹(D, 𝒪_D)` is a hypothesis of the main theorem rather than a consequence of
properness, and `AlgebraicGeometry.isZero_structureSheafCohomology_of_isAffine` discharges it
from `D` affine — Serre vanishing, [Stacks, Tag 01XB]; a `D` that is finite over `k`, the case
of two pieces meeting in finitely many points, is affine.

**Moving between `X` and the pieces.** The sequence lives on the ambient `X`, while the genus is
an invariant of a piece, so each term is carried across the closed immersion by
`AlgebraicGeometry.cohomologyOverFieldPushforwardIsoOfIsClosedImmersion` and then between the
two spellings of the cohomology of the structure sheaf by
`AlgebraicGeometry.structureSheafCohomologyIsoCohomologyOverField`; the composite is
`AlgebraicGeometry.cohomologyOverFieldClosedSubschemeStructureSheafIso`.  The middle term is a
biproduct, whose cohomology splits by
`AlgebraicGeometry.nonempty_cohomologyOverField_biprod_linearEquiv` — the splitting coming from
the long exact sequence of the split sequence `0 ⟶ 𝒜 ⟶ 𝒜 ⊞ ℬ ⟶ ℬ ⟶ 0`, Mathlib having no
instance making a right derived functor additive.

## References

* [Stacks Project, Tag 0C4J](https://stacks.math.columbia.edu/tag/0C4J)
* [Stacks Project, Tag 0BY7](https://stacks.math.columbia.edu/tag/0BY7)
* [Stacks Project, Tag 01XB](https://stacks.math.columbia.edu/tag/01XB)
* [Stacks Project, Tag 02O6](https://stacks.math.columbia.edu/tag/02O6)
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits Opposite
open AlgebraicGeometry.Scheme.IdealSheafData
open Stacks.AlgebraicGeometry.CurveEulerBridge

universe u

namespace AlgebraicGeometry

attribute [local instance] HasDerivedCategory.standard

variable (k : Type u) [Field k] {X : Scheme.{u}} (f : X ⟶ Spec (.of k))

/-! ### Transporting the hypotheses between a closed subscheme and a smaller one -/

/-- **Properness of a closed subscheme passes to its closed subschemes.**  For `I ≤ J` the
subscheme cut out by `J` is a closed subscheme of the one cut out by `I`, the inclusion being
`AlgebraicGeometry.Scheme.IdealSheafData.inclusion`; a closed immersion is finite, hence proper,
so the structure morphism of the smaller subscheme is proper as soon as that of the larger one
is. -/
theorem isProper_subschemeι_comp_of_le {I J : X.IdealSheafData} (h : I ≤ J)
    [IsProper (I.subschemeι ≫ f)] : IsProper (J.subschemeι ≫ f) := by
  have hfac : J.subschemeι ≫ f = Scheme.IdealSheafData.inclusion h ≫ (I.subschemeι ≫ f) := by
    rw [← Category.assoc, Scheme.IdealSheafData.inclusion_subschemeι]
  rw [hfac]
  infer_instance

/-- **The cohomology on the ambient scheme of the pushed-forward structure sheaf of a closed
subscheme is the cohomology of the structure sheaf of that subscheme.**  The first factor is the
closed-immersion comparison
`AlgebraicGeometry.cohomologyOverFieldPushforwardIsoOfIsClosedImmersion`, the second the
identification of the two spellings of the cohomology of a structure sheaf,
`AlgebraicGeometry.structureSheafCohomologyIsoCohomologyOverField`. -/
@[ega "III 4.1.3" "special case"]
noncomputable def cohomologyOverFieldClosedSubschemeStructureSheafIso (I : X.IdealSheafData)
    (n : ℕ) :
    cohomologyOverField k f (closedSubschemeStructureSheaf I) n ≅
      structureSheafCohomology (I.subschemeι ≫ f) n :=
  (cohomologyOverFieldPushforwardIsoOfIsClosedImmersion k I.subschemeι f
      (SheafOfModules.unit I.subscheme.ringCatSheaf) n).symm ≪≫
    (structureSheafCohomologyIsoCohomologyOverField k (I.subschemeι ≫ f) n).symm

/-- The dimension of the cohomology on the ambient scheme of the pushed-forward structure sheaf
of a closed subscheme is the dimension of the cohomology of the structure sheaf of that
subscheme. -/
theorem finrank_cohomologyOverField_closedSubschemeStructureSheaf (I : X.IdealSheafData)
    (n : ℕ) :
    Module.finrank k (cohomologyOverField k f (closedSubschemeStructureSheaf I) n) =
      Module.finrank k (structureSheafCohomology (I.subschemeι ≫ f) n) :=
  (cohomologyOverFieldClosedSubschemeStructureSheafIso k f I n).toLinearEquiv.finrank_eq

/-- The cohomology on the ambient scheme of the pushed-forward structure sheaf of a closed
subscheme proper over the base field is finite-dimensional.  This is [Stacks, Tag 02O6] on the
subscheme, carried across the closed immersion. -/
theorem finiteDimensional_cohomologyOverField_closedSubschemeStructureSheaf
    (I : X.IdealSheafData) [IsProper (I.subschemeι ≫ f)] (n : ℕ) :
    FiniteDimensional k (cohomologyOverField k f (closedSubschemeStructureSheaf I) n) :=
  have := isCoherent_unit k (I.subschemeι ≫ f)
  finiteDimensional_cohomologyOverField_pushforward_of_isClosedImmersion k I.subschemeι f _ n
    (finiteDimensional_cohomologyOverField_of_isProper k (I.subschemeι ≫ f) _ n)

/-- **The positive-degree cohomology of the structure sheaf of an affine scheme over a field
vanishes.**  This is Serre vanishing, [Stacks, Tag 01XB], in the spelling
`AlgebraicGeometry.structureSheafCohomology` that the genus is defined from. -/
@[sga "1 XI 6.9" "partial", sga "3 XXII 5.9.6" "special case"]
theorem isZero_structureSheafCohomology_of_isAffine {Z : Scheme.{u}} (g : Z ⟶ Spec (.of k))
    [IsAffine Z] (n : ℕ) (hn : 0 < n) : IsZero (structureSheafCohomology g n) :=
  (isZero_cohomologyOverField_pos_of_isAffine k g (SheafOfModules.unit Z.ringCatSheaf) n
    hn).of_iso (structureSheafCohomologyIsoCohomologyOverField k g n)

/-! ### Cohomology of a biproduct -/

/-- **The dimension of the cohomology of a biproduct of two modules is the sum of the
dimensions.**  This is
`AlgebraicGeometry.nonempty_cohomologyOverField_biprod_linearEquiv` read as an equality of
dimensions; finite dimensionality of the two summands is needed, `Module.finrank` not being
additive on a product of infinite-dimensional spaces. -/
theorem finrank_cohomologyOverField_biprod (A B : X.Modules) (n : ℕ)
    (hA : FiniteDimensional k (cohomologyOverField k f A n))
    (hB : FiniteDimensional k (cohomologyOverField k f B n)) :
    Module.finrank k (cohomologyOverField k f (A ⊞ B) n) =
      Module.finrank k (cohomologyOverField k f A n) +
        Module.finrank k (cohomologyOverField k f B n) := by
  obtain ⟨e⟩ := nonempty_cohomologyOverField_biprod_linearEquiv k f A B n
  have := hA
  have := hB
  rw [e.finrank_eq, Module.finrank_prod]

/-! ### The five-term dimension count -/

/-- **The dimension count attached to a short exact sequence whose quotient has no `H¹`.**  For
a short exact sequence `0 ⟶ 𝒜 ⟶ ℬ ⟶ 𝒞 ⟶ 0` of modules on a scheme over `k` with
`H¹(X, 𝒞) = 0` and with the cohomology of the terms finite-dimensional in the degrees that
occur,

`h⁰(𝒜) + h⁰(𝒞) + h¹(ℬ) = h⁰(ℬ) + h¹(𝒜)`.

There is no properness and no coherence hypothesis: the input is the long exact sequence
`AlgebraicGeometry.exists_cohomologyOverField_longExactSequence`, which has none, truncated at
`H¹(X, 𝒞)`, together with
`Module.sum_neg_one_pow_finrank_eq_zero_of_exact_six`.  Exactness at the last term is free:
the sixth term being zero, the fifth map is surjective. -/
theorem finrank_cohomologyOverField_add_eq_of_shortExact_of_isZero {A B C : X.Modules}
    (u : A ⟶ B) (v : B ⟶ C) (w : u ≫ v = 0) (hSE : (ShortComplex.mk u v w).ShortExact)
    (hA₀ : FiniteDimensional k (cohomologyOverField k f A 0))
    (hA₁ : FiniteDimensional k (cohomologyOverField k f A 1))
    (hB₀ : FiniteDimensional k (cohomologyOverField k f B 0))
    (hB₁ : FiniteDimensional k (cohomologyOverField k f B 1))
    (hC₀ : FiniteDimensional k (cohomologyOverField k f C 0))
    (hC₁ : IsZero (cohomologyOverField k f C 1)) :
    Module.finrank k (cohomologyOverField k f A 0)
        + Module.finrank k (cohomologyOverField k f C 0)
        + Module.finrank k (cohomologyOverField k f B 1)
      = Module.finrank k (cohomologyOverField k f B 0)
        + Module.finrank k (cohomologyOverField k f A 1) := by
  -- The long exact sequence, read at the three modules rather than at the projections of the
  -- short complex, which are only definitionally equal to them.
  obtain ⟨d, hinj, hab, hbc, hca⟩ := exists_cohomologyOverField_longExactSequence k f hSE
  have hsub : Subsingleton (cohomologyOverField k f C 1) :=
    ModuleCat.subsingleton_of_isZero hC₁
  have hsurj : Function.Surjective (cohomologyOverFieldMap k f v 1).hom :=
    fun y => ⟨0, Subsingleton.elim _ _⟩
  have hC₁fin : FiniteDimensional k (cohomologyOverField k f C 1) :=
    have : Finite (cohomologyOverField k f C 1) := Finite.of_subsingleton
    Module.Finite.of_finite
  have hC₁rank : Module.finrank k (cohomologyOverField k f C 1) = 0 :=
    Module.finrank_zero_of_subsingleton
  have := hA₀
  have := hA₁
  have := hB₀
  have := hB₁
  have := hC₀
  have := hC₁fin
  -- The degree-one term of the connecting map is indexed as `0 + 1` by the long exact sequence;
  -- the ascription of the conclusion is what puts it back at `1`.
  have key : (Module.finrank k (cohomologyOverField k f A 0) : ℤ)
        - Module.finrank k (cohomologyOverField k f B 0)
        + Module.finrank k (cohomologyOverField k f C 0)
        - Module.finrank k (cohomologyOverField k f A 1)
        + Module.finrank k (cohomologyOverField k f B 1)
        - Module.finrank k (cohomologyOverField k f C 1) = 0 :=
    Module.sum_neg_one_pow_finrank_eq_zero_of_exact_six
      (cohomologyOverFieldMap k f u 0).hom (cohomologyOverFieldMap k f v 0).hom (d 0).hom
      (cohomologyOverFieldMap k f u 1).hom (cohomologyOverFieldMap k f v 1).hom
      hinj (hab 0) (hbc 0) (hca 0) (hab 1) hsurj
  omega

/-- **The global sections of the middle term of a short exact sequence are at most those of the
two outer terms together.**  For `0 ⟶ 𝒜 ⟶ ℬ ⟶ 𝒞 ⟶ 0` on a scheme over `k`,
`h⁰(ℬ) ≤ h⁰(𝒜) + h⁰(𝒞)`.

Only the left-exact end of the long exact sequence is used — `H⁰(X, 𝒜) ⟶ H⁰(X, ℬ)` is injective
with image the kernel of `H⁰(X, ℬ) ⟶ H⁰(X, 𝒞)` — so there is no hypothesis on `f` beyond finite
dimensionality of the two terms whose dimensions bound the middle one.  Together with
`AlgebraicGeometry.finrank_cohomologyOverField_add_eq_of_shortExact_of_isZero` this is what turns
the dimension count into the inequality
`AlgebraicGeometry.genus_add_le_genus_union`. -/
theorem finrank_cohomologyOverField_zero_le_of_shortExact {A B C : X.Modules}
    (u : A ⟶ B) (v : B ⟶ C) (w : u ≫ v = 0) (hSE : (ShortComplex.mk u v w).ShortExact)
    (hB₀ : FiniteDimensional k (cohomologyOverField k f B 0))
    (hC₀ : FiniteDimensional k (cohomologyOverField k f C 0)) :
    Module.finrank k (cohomologyOverField k f B 0)
      ≤ Module.finrank k (cohomologyOverField k f A 0)
        + Module.finrank k (cohomologyOverField k f C 0) := by
  obtain ⟨d, hinj, hab, hbc, hca⟩ := exists_cohomologyOverField_longExactSequence k f hSE
  have := hB₀
  have := hC₀
  have hrn := (cohomologyOverFieldMap k f v 0).hom.finrank_range_add_finrank_ker
  have hker : Module.finrank k
      (LinearMap.ker (cohomologyOverFieldMap k f v 0).hom) =
        Module.finrank k (cohomologyOverField k f A 0) := by
    rw [(hab 0).linearMap_ker_eq]
    exact LinearMap.finrank_range_of_inj hinj
  have hrange : Module.finrank k
      (LinearMap.range (cohomologyOverFieldMap k f v 0).hom)
        ≤ Module.finrank k (cohomologyOverField k f C 0) := Submodule.finrank_le _
  omega

/-! ### The genus of a union -/

/-- A union of closed subschemes proper over `k` has proper pieces and proper intersection. -/
private theorem isProper_pieces_of_isProper_inf (I J : X.IdealSheafData)
    [IsProper ((I ⊓ J).subschemeι ≫ f)] :
    IsProper (I.subschemeι ≫ f) ∧ IsProper (J.subschemeι ≫ f) ∧
      IsProper ((I ⊔ J).subschemeι ≫ f) :=
  ⟨isProper_subschemeι_comp_of_le k f (inf_le_left : I ⊓ J ≤ I),
    isProper_subschemeι_comp_of_le k f (inf_le_right : I ⊓ J ≤ J),
    isProper_subschemeι_comp_of_le k f (inf_le_left.trans le_sup_left : I ⊓ J ≤ I ⊔ J)⟩

/-- The cohomology of the biproduct of the structure sheaves of two proper closed subschemes is
finite-dimensional, of dimension the sum of the dimensions of their cohomologies. -/
private theorem finiteDimensional_and_finrank_cohomologyOverField_biprod (I J : X.IdealSheafData)
    [IsProper (I.subschemeι ≫ f)] [IsProper (J.subschemeι ≫ f)] (n : ℕ) :
    FiniteDimensional k (cohomologyOverField k f
      (closedSubschemeStructureSheaf I ⊞ closedSubschemeStructureSheaf J) n) ∧
    Module.finrank k (cohomologyOverField k f
      (closedSubschemeStructureSheaf I ⊞ closedSubschemeStructureSheaf J) n) =
      Module.finrank k (structureSheafCohomology (I.subschemeι ≫ f) n) +
        Module.finrank k (structureSheafCohomology (J.subschemeι ≫ f) n) := by
  have hI := finiteDimensional_cohomologyOverField_closedSubschemeStructureSheaf k f I n
  have hJ := finiteDimensional_cohomologyOverField_closedSubschemeStructureSheaf k f J n
  exact ⟨finiteDimensional_cohomologyOverField_biprod k f _ _ n hI hJ, by
    rw [finrank_cohomologyOverField_biprod k f _ _ n hI hJ,
      finrank_cohomologyOverField_closedSubschemeStructureSheaf,
      finrank_cohomologyOverField_closedSubschemeStructureSheaf]⟩

/-- **The genus of a union of two closed subschemes.**  Let `k` be a field, `X` a scheme over
`k` and `I J : X.IdealSheafData`, so that `W = Z₁ ∪ Z₂` is the closed subscheme cut out by
`I ⊓ J`, the pieces `Z₁`, `Z₂` are those cut out by `I`, `J`, and `D = Z₁ ∩ Z₂` is the one cut
out by `I ⊔ J`.  If `W` is proper over `k` and `H¹(D, 𝒪_D) = 0`, then

`h⁰(W) + h⁰(D) + genus Z₁ + genus Z₂ = h⁰(Z₁) + h⁰(Z₂) + genus W`,

where `h⁰` abbreviates `Module.finrank k (structureSheafCohomology · 0)`, the dimension over `k`
of the ring of global functions, and `h⁰(D)` is the degree of the intersection.

The hypotheses are the source's and nothing more.  Properness is required of the union only, the
pieces inheriting it by `AlgebraicGeometry.isProper_subschemeι_comp_of_le`, and it is used only
for finite dimensionality.  The vanishing of `H¹(D, 𝒪_D)` is exactly what "the two pieces meet
in finitely many points" provides, through
`AlgebraicGeometry.isZero_structureSheafCohomology_of_isAffine`; nothing else is assumed, in
particular nothing about the dimension of `W` and nothing about its connectedness.

The classical form `genus W = genus Z₁ + genus Z₂ + m - 1` is the case
`h⁰(W) = h⁰(Z₁) = h⁰(Z₂) = 1`; see `AlgebraicGeometry.genus_union_add_one` and
`AlgebraicGeometry.genus_union_cast`.  It is stated here with the `h⁰` terms present and no
subtraction because `AlgebraicGeometry.genus` is `ℕ`-valued: in `ℕ` the subtraction is truncated
and the formula would be false at `m = 0`, which is exactly the disjoint case, where `h⁰(W)` is
`2` rather than `1`. -/
theorem genus_union (I J : X.IdealSheafData) [IsProper ((I ⊓ J).subschemeι ≫ f)]
    (hint : IsZero (structureSheafCohomology ((I ⊔ J).subschemeι ≫ f) 1)) :
    Module.finrank k (structureSheafCohomology ((I ⊓ J).subschemeι ≫ f) 0)
        + Module.finrank k (structureSheafCohomology ((I ⊔ J).subschemeι ≫ f) 0)
        + genus (I.subschemeι ≫ f) + genus (J.subschemeι ≫ f)
      = Module.finrank k (structureSheafCohomology (I.subschemeι ≫ f) 0)
        + Module.finrank k (structureSheafCohomology (J.subschemeι ≫ f) 0)
        + genus ((I ⊓ J).subschemeι ≫ f) := by
  obtain ⟨_, _, _⟩ := isProper_pieces_of_isProper_inf k f I J
  obtain ⟨hw, hSE⟩ := unionIntersection_shortExact I J
  obtain ⟨hfin₀, hrank₀⟩ := finiteDimensional_and_finrank_cohomologyOverField_biprod k f I J 0
  obtain ⟨hfin₁, hrank₁⟩ := finiteDimensional_and_finrank_cohomologyOverField_biprod k f I J 1
  have hzeroC : IsZero (cohomologyOverField k f (closedSubschemeStructureSheaf (I ⊔ J)) 1) :=
    hint.of_iso (cohomologyOverFieldClosedSubschemeStructureSheafIso k f (I ⊔ J) 1)
  have key := finrank_cohomologyOverField_add_eq_of_shortExact_of_isZero k f
    (unionToBiprod I J) (biprodToIntersection I J) hw hSE
    (finiteDimensional_cohomologyOverField_closedSubschemeStructureSheaf k f (I ⊓ J) 0)
    (finiteDimensional_cohomologyOverField_closedSubschemeStructureSheaf k f (I ⊓ J) 1)
    hfin₀ hfin₁
    (finiteDimensional_cohomologyOverField_closedSubschemeStructureSheaf k f (I ⊔ J) 0) hzeroC
  simp only [hrank₀, hrank₁, finrank_cohomologyOverField_closedSubschemeStructureSheaf] at key
  simp only [genus_eq_finrank_structureSheafCohomology]
  omega

/-- **The genus of a union of two closed subschemes meeting in a finite scheme of degree `m`,
when each of the three pieces has only the constants as global functions.**  Under
`h⁰(Z₁ ∪ Z₂) = h⁰(Z₁) = h⁰(Z₂) = 1`,

`genus (Z₁ ∪ Z₂) + 1 = genus Z₁ + genus Z₂ + m`, where `m = h⁰(Z₁ ∩ Z₂)`.

This is the classical `g = g₁ + g₂ + m - 1` with the `-1` moved across the equality, which is
how the formula is stated in `ℕ` without truncated subtraction;
`AlgebraicGeometry.genus_union_cast` is the integer form.

The intersection is assumed affine rather than its `H¹` assumed to vanish, which is the
geometric reading "the two pieces meet in finitely many points": a `Z₁ ∩ Z₂` finite over `k` is
affine, and then `m` is its degree, that is its `k`-length.  The vanishing is supplied by
`AlgebraicGeometry.isZero_structureSheafCohomology_of_isAffine`.

Two known special cases are the specialisations `m = 1`, `genus Z₂ = 0`, giving
`genus (Z₁ ∪ Z₂) = genus Z₁` — the genus clause of [Stacks, Tag 0E3H], which is
`Stacks.Curves.genus_complementaryCurve` — and `genus Z₁ = genus Z₂ = 0` with `m = 1`, giving
`genus (Z₁ ∪ Z₂) = 0`.  The hypothesis `h⁰ = 1` is what excludes the disjoint case: see
`AlgebraicGeometry.genus_union_eq_add_of_finrank_sections_add`. -/
theorem genus_union_add_one (I J : X.IdealSheafData) [IsProper ((I ⊓ J).subschemeι ≫ f)]
    [IsAffine (I ⊔ J).subscheme]
    (hW : Module.finrank k (structureSheafCohomology ((I ⊓ J).subschemeι ≫ f) 0) = 1)
    (hI : Module.finrank k (structureSheafCohomology (I.subschemeι ≫ f) 0) = 1)
    (hJ : Module.finrank k (structureSheafCohomology (J.subschemeι ≫ f) 0) = 1) :
    genus ((I ⊓ J).subschemeι ≫ f) + 1 =
      genus (I.subschemeι ≫ f) + genus (J.subschemeι ≫ f) +
        Module.finrank k (structureSheafCohomology ((I ⊔ J).subschemeι ≫ f) 0) := by
  have key := genus_union k f I J
    (isZero_structureSheafCohomology_of_isAffine k ((I ⊔ J).subschemeι ≫ f) 1 Nat.one_pos)
  rw [hW, hI, hJ] at key
  omega

/-- **The genus of a union, in the integer form `g = g₁ + g₂ + m - 1`.**  This is
`AlgebraicGeometry.genus_union_add_one` cast to `ℤ`, where the subtraction is the honest one;
in `ℕ` it would be truncated and the statement false at `m = 0`, which is why the hypothesis
`h⁰ = 1` on the union — failing exactly in the disjoint case — is what makes the formula
true. -/
theorem genus_union_cast (I J : X.IdealSheafData) [IsProper ((I ⊓ J).subschemeι ≫ f)]
    [IsAffine (I ⊔ J).subscheme]
    (hW : Module.finrank k (structureSheafCohomology ((I ⊓ J).subschemeι ≫ f) 0) = 1)
    (hI : Module.finrank k (structureSheafCohomology (I.subschemeι ≫ f) 0) = 1)
    (hJ : Module.finrank k (structureSheafCohomology (J.subschemeι ≫ f) 0) = 1) :
    (genus ((I ⊓ J).subschemeι ≫ f) : ℤ) =
      genus (I.subschemeι ≫ f) + genus (J.subschemeι ≫ f) +
        Module.finrank k (structureSheafCohomology ((I ⊔ J).subschemeι ≫ f) 0) - 1 := by
  have key := genus_union_add_one k f I J hW hI hJ
  omega

/-- **The disjoint case, consistent with `AlgebraicGeometry.genus_sigma`.**  If the intersection
contributes nothing — `h⁰(Z₁ ∩ Z₂) = 0`, which is the case when the two pieces are disjoint —
and the global functions on the union are the global functions on the two pieces together,
`h⁰(Z₁ ∪ Z₂) = h⁰(Z₁) + h⁰(Z₂)`, then `genus (Z₁ ∪ Z₂) = genus Z₁ + genus Z₂`.

This is the same conclusion as `AlgebraicGeometry.genus_sigma`, and it is what shows that the
`+ m - 1` correction of `AlgebraicGeometry.genus_union_add_one` does not contradict it: the two
differ only in the value of `h⁰` on the union, which is `1` for pieces that meet and
`h⁰(Z₁) + h⁰(Z₂)` for pieces that do not. -/
theorem genus_union_eq_add_of_finrank_sections_add (I J : X.IdealSheafData)
    [IsProper ((I ⊓ J).subschemeι ≫ f)]
    (hint : IsZero (structureSheafCohomology ((I ⊔ J).subschemeι ≫ f) 1))
    (hdeg : Module.finrank k (structureSheafCohomology ((I ⊔ J).subschemeι ≫ f) 0) = 0)
    (hsplit : Module.finrank k (structureSheafCohomology ((I ⊓ J).subschemeι ≫ f) 0) =
      Module.finrank k (structureSheafCohomology (I.subschemeι ≫ f) 0) +
        Module.finrank k (structureSheafCohomology (J.subschemeι ≫ f) 0)) :
    genus ((I ⊓ J).subschemeι ≫ f) = genus (I.subschemeι ≫ f) + genus (J.subschemeι ≫ f) := by
  have key := genus_union k f I J hint
  rw [hdeg, hsplit] at key
  omega

/-- **The global functions on a union of two closed subschemes are at most those on the two
pieces together, corrected by the intersection.**  For `W = Z₁ ∪ Z₂` proper over `k`,

`h⁰(Z₁) + h⁰(Z₂) ≤ h⁰(W) + h⁰(Z₁ ∩ Z₂)`.

This is the left-exact end of the sequence of [Stacks, Tag 0C4J]: a global function on `W`
restricts to a pair of global functions on the pieces agreeing on the intersection, and that is
all the sequence says in degree zero.  Unlike
`AlgebraicGeometry.genus_union` it needs no hypothesis on the cohomology of the intersection. -/
theorem finrank_structureSheafCohomology_zero_add_le_union (I J : X.IdealSheafData)
    [IsProper ((I ⊓ J).subschemeι ≫ f)] :
    Module.finrank k (structureSheafCohomology (I.subschemeι ≫ f) 0)
        + Module.finrank k (structureSheafCohomology (J.subschemeι ≫ f) 0)
      ≤ Module.finrank k (structureSheafCohomology ((I ⊓ J).subschemeι ≫ f) 0)
        + Module.finrank k (structureSheafCohomology ((I ⊔ J).subschemeι ≫ f) 0) := by
  obtain ⟨_, _, _⟩ := isProper_pieces_of_isProper_inf k f I J
  obtain ⟨hw, hSE⟩ := unionIntersection_shortExact I J
  obtain ⟨hfin, hrank⟩ := finiteDimensional_and_finrank_cohomologyOverField_biprod k f I J 0
  have key := finrank_cohomologyOverField_zero_le_of_shortExact k f
    (unionToBiprod I J) (biprodToIntersection I J) hw hSE hfin
    (finiteDimensional_cohomologyOverField_closedSubschemeStructureSheaf k f (I ⊔ J) 0)
  simp only [hrank, finrank_cohomologyOverField_closedSubschemeStructureSheaf] at key
  omega

/-- **The genus of a union of two closed subschemes is at least the sum of their genera.**  For
`W = Z₁ ∪ Z₂` proper over `k` whose intersection has vanishing `H¹`,

`genus Z₁ + genus Z₂ ≤ genus (Z₁ ∪ Z₂)`.

No connectedness and no `h⁰` hypothesis: the `h⁰` terms of `AlgebraicGeometry.genus_union` are
eliminated against `AlgebraicGeometry.finrank_structureSheafCohomology_zero_add_le_union`, which
bounds them in exactly the direction needed.

The consequence this is wanted for is that **every closed subcurve of a union of genus zero has
genus zero**: at `genus (Z₁ ∪ Z₂) = 0` the inequality forces `genus Z₁ = genus Z₂ = 0`.  That is
the genus clause of `AlgebraicGeometry.IsRationalBridge` for the pieces of a decomposition of a
genus-zero curve, which is how [Stacks, Tag 0E65] uses it. -/
theorem genus_add_le_genus_union (I J : X.IdealSheafData)
    [IsProper ((I ⊓ J).subschemeι ≫ f)]
    (hint : IsZero (structureSheafCohomology ((I ⊔ J).subschemeι ≫ f) 1)) :
    genus (I.subschemeι ≫ f) + genus (J.subschemeι ≫ f)
      ≤ genus ((I ⊓ J).subschemeι ≫ f) := by
  have key := genus_union k f I J hint
  have hle := finrank_structureSheafCohomology_zero_add_le_union k f I J
  omega

/-- **Pieces whose union has only the constants as global functions must meet.**  If
`h⁰(Z₁ ∪ Z₂) = h⁰(Z₁) = h⁰(Z₂) = 1` then the degree `h⁰(Z₁ ∩ Z₂)` of the intersection is
positive.

This is what makes the classical form of the genus formula a statement with an honest `- 1`:
the `h⁰ = 1` hypothesis of `AlgebraicGeometry.genus_union_add_one` already excludes `m = 0`, so
no separate `0 < m` has to be carried, and `AlgebraicGeometry.genus_union_cast` is the formula
`g = g₁ + g₂ + m - 1` in a range where the subtraction does not truncate. -/
theorem zero_lt_finrank_structureSheafCohomology_zero_sup (I J : X.IdealSheafData)
    [IsProper ((I ⊓ J).subschemeι ≫ f)]
    (hW : Module.finrank k (structureSheafCohomology ((I ⊓ J).subschemeι ≫ f) 0) = 1)
    (hI : Module.finrank k (structureSheafCohomology (I.subschemeι ≫ f) 0) = 1)
    (hJ : Module.finrank k (structureSheafCohomology (J.subschemeι ≫ f) 0) = 1) :
    0 < Module.finrank k (structureSheafCohomology ((I ⊔ J).subschemeι ≫ f) 0) := by
  have hle := finrank_structureSheafCohomology_zero_add_le_union k f I J
  omega

end AlgebraicGeometry

end
