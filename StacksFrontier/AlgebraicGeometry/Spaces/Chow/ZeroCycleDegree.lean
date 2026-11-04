module

public import Mathlib.Algebra.BigOperators.Finprod
public import StacksCore.Tactic.StacksAttribute
public import StacksFrontier.AlgebraicGeometry.Spaces.Chow.ProperPushforwardCoherentCycle
public import StacksFrontier.AlgebraicGeometry.Spaces.Decent.IntegralClosedSubspaces
public import StacksFrontier.AlgebraicGeometry.Spaces.UniversallyClosed

/-!
# The degree of a zero cycle on a proper algebraic space over a field

In Situation 0EDT let `p : X ⟶ Y` be a proper morphism of good algebraic spaces over the base,
with `Y` playing the role of `Spec(k)`: its space of points is a single point and the dimension
function it inherits from the base vanishes. Then `Y` carries exactly one integral closed
subspace, so a zero cycle on `Y` is just an integer — its coefficient there — and the *degree*
of a zero cycle `α` on `X` is the coefficient at that subspace of the proper pushforward of `α`,
`AlgebraicGeometry.Space.cycleDegree`.

**Stacks 0ESH** computes it: writing `α = ∑ n_i [Z_i]` over the integral closed subspaces of `X`
of δ-dimension zero,

    deg(α) = ∑ n_i deg(Z_i),

where `deg(Z_i)` is the degree of `Z_i → Spec(k)`. The source's proof is one line — "this is the
definition of proper pushforward", Definition 82.8.1 — and that is what the proof below is, once
two things are checked, neither of which is formal: that the integral closed image of *every*
integral closed subspace of `X` is the one integral closed subspace of `Y`, so that the sum
defining the pushforward coefficient runs over all of them rather than over a proper subset; and
that the weight of Stacks 0EP0 at each `Z_i` is the degree itself rather than zero, which is the
case exactly because the δ-dimension of `Z_i` and the δ-dimension of its image are both zero.

## Main definitions

* `AlgebraicGeometry.Space.cycleDegree`: the degree of a zero cycle on an algebraic space proper
  over the base, read at a chosen integral closed subspace of the target — the construction
  underlying Stacks 0ESG at the level of cycles.

## Main results

* `AlgebraicGeometry.Space.IntegralClosedSubspace.eq_of_subsingleton_points`: an algebraic space
  whose space of points is a single point has at most one integral closed subspace.
* `AlgebraicGeometry.Space.cycleImageSubspace_eq_of_subsingleton_points`: over such a target the
  integral closed image of every integral closed subspace of the source is that subspace.
* `AlgebraicGeometry.Space.cycleDegree_eq_finsum`: **Stacks 0ESH**, in the shape in which this
  library presents a cycle — as the coefficient family `Z ↦ n_Z` on the integral closed
  subspaces — so that the asserted identity is a sum over all of them.
* `AlgebraicGeometry.Space.cycleDegree_eq_sum`: **Stacks 0ESH** in the source's shape, for a
  cycle presented as a finite sum `∑ n_i [Z_i]` over pairwise distinct `Z_i`.

## Implementation notes

**What `deg(Z_i)` is here.** The source writes the degree of `Z_i → Spec(k)` as
`dim_k Γ(Z_i, 𝒪_{Z_i})`, which for an integral `Z_i` of dimension zero is the degree of the
function field `R(Z_i)` over `k`; that is the content of the scheme-level
`Stacks.Chow.residueDegree_eq_finrank_globalSections` of
`StacksFrontier.AlgebraicGeometry.Chow.Degrees.ZeroCycleDegreeFormula`, where Stacks 0AZ2 — the
counterpart of this tag for schemes — is proved in the `Γ` form. For algebraic spaces the ring
of global functions is available, `AlgebraicGeometry.Space.globalFunctions'`, and so is its
pullback along a morphism, `AlgebraicGeometry.Space.globalFunctionsMap`, so the number
`dim_{Γ(Y, 𝒪_Y)} Γ(Z_i, 𝒪_{Z_i})` can be written down. What cannot be proved is that it is the
degree: the scheme-level identification runs through
`Stacks.Chow.isIso_Γevaluation_of_isIntegral_of_subsingleton`, that on an integral scheme with
one point evaluating a global section in the residue field at that point is an isomorphism, and
for algebraic spaces there is no evaluation map from the global functions to the residue field at
a point at all, nor any statement that the global functions of an integral algebraic space form
a field. The nearest thing is Stacks 0DMY,
`AlgebraicGeometry.Space.finiteDimensional_globalFunctions_of_isProper` of
`StacksFrontier.AlgebraicGeometry.Spaces.ProperGlobalFunctions`, which bounds the dimension of
`Γ(X, 𝒪_X)` for `X` proper over a field; it is available only when the base *scheme* of the site
is `Spec(k)`, which is not the shape used here, and only conditionally on Stacks 08AS.
So `deg(Z_i)` is taken here in its other, equivalent, reading: the degree
`[R(Z_i) : R(Z_i')] = [R(Z_i) : k]` of the extension of function fields, which is
`AlgebraicGeometry.Space.cycleResidueDegree` at the generic point of `Z_i`. This is exactly the
degree with which Definition 82.8.1 — Stacks 0EP1, and
`AlgebraicGeometry.Space.properPushforwardWeight` here — weights `Z_i`, and it is the degree of
Spaces over Fields, Definition 72.5.2 that 0EP1 cites. The restriction is recorded on the
`@[stacks 0ESH]` attributes.

**How `Spec(k)` is modelled.** The target is kept general, as a good algebraic space `Y/B`
subject to the two conditions that `Spec(k)` satisfies and that the proof uses: its space of
points is a subsingleton, and the dimension function induced on it by the base vanishes. This is
the shape of the scheme-level `StacksFrontier.AlgebraicGeometry.Chow.Degrees.ZeroCycleDegree`, whose
base situation carries `Subsingleton C.S` and `∀ s, C.dimensionFunction s = 0` rather than
`Spec(k)` itself. Nothing below needs `Y` to be the base of the situation, or a scheme.

**Where properness is used.** Properness enters through quasi-compactness, which is what
`AlgebraicGeometry.Space.properPushforward` asks for: without it the pushforward of a zero cycle
is not known to have locally finite support and so is not a zero cycle on `Y`, and the degree
cannot be formed at all. That is also the only use the source makes of it here, Definition
82.32.1 being stated for a proper `p`. The separatedness and universal-closedness clauses of
properness are not used, and neither is the quasi-separatedness clause of goodness of `X`.

**The degree is not descended to rational equivalence.** Stacks 0ESG defines `deg` on `CH_0(X)`,
through the identification of `CH_0(Spec(k))` with `ℤ`. The descent needs proper pushforward to
respect rational equivalence, Stacks 0EQC, which this library does not have for algebraic
spaces; the cycle-level degree below is what Stacks 0ESH is an identity between, and the
scheme-level file above is organized the same way for the same reason.

## References

* [Stacks Project, Tag 0ESH](https://stacks.math.columbia.edu/tag/0ESH)
* [Stacks Project, Tag 0ESG](https://stacks.math.columbia.edu/tag/0ESG)
* [Stacks Project, Tag 0EP1](https://stacks.math.columbia.edu/tag/0EP1)
* [Stacks Project, Tag 0EP0](https://stacks.math.columbia.edu/tag/0EP0)
* [Stacks Project, Tag 0EDT](https://stacks.math.columbia.edu/tag/0EDT)
* [Stacks Project, Tag 0EDZ](https://stacks.math.columbia.edu/tag/0EDZ)
* [Stacks Project, Tag 0ENF](https://stacks.math.columbia.edu/tag/0ENF)
* [Stacks Project, Tag 0ENZ](https://stacks.math.columbia.edu/tag/0ENZ)
* [Stacks Project, Tag 03ZM](https://stacks.math.columbia.edu/tag/03ZM)
* [Stacks Project, Tag 0AZ2](https://stacks.math.columbia.edu/tag/0AZ2)
-/

@[expose] public noncomputable section

open CategoryTheory TopologicalSpace

universe v u

namespace AlgebraicGeometry.Space

attribute [local instance] pointTopology

/-! ### An algebraic space with one point has one integral closed subspace -/

/-- An algebraic space over `S` whose space of points is a single point has at most one integral
closed subspace.

The set of points of an integral closed subspace is an irreducible closed subset of the space,
in particular nonempty, so in a subsingleton space it is everything; and an integral closed
subspace is determined by its set of points, which is the injectivity clause of Stacks 0ENF. -/
theorem IntegralClosedSubspace.eq_of_subsingleton_points (B : BigFppfSite.{u}) (S : Scheme.{u})
    (hS : B.Contains S) {Y : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u}
    (hY : IsAlgebraicSpace B S hS Y) (hpt : Subsingleton (points B S hS Y))
    (W W' : IntegralClosedSubspace B S hS Y) : W = W' := by
  have h (V : IntegralClosedSubspace B S hS Y) :
      (integralClosedSubspaceSupport B S hS hY V : Set (points B S hS Y)) = Set.univ := by
    obtain ⟨q, hq⟩ := (integralClosedSubspaceSupport B S hS hY V).isIrreducible.nonempty
    exact Set.eq_univ_of_forall fun r => by rw [Subsingleton.elim r q]; exact hq
  exact injective_integralClosedSubspaceSupport B S hS hY
    (IrreducibleCloseds.ext ((h W).trans (h W').symm))

section Degree

variable (D : BaseSpaceDimensionSituation.{u})
    {X Y : (BigFppfOver D.site D.base D.base_mem)ᵒᵖ ⥤ Type u}

/-- When the target has a single point, the integral closed image of Stacks 0EEG of an integral
closed subspace of the source is the unique integral closed subspace of the target. -/
theorem cycleImageSubspace_eq_of_subsingleton_points (sY : Y ⟶ D.space) (hY : D.IsGood sY)
    (hpt : Subsingleton (points D.site D.base D.base_mem Y)) (f : X ⟶ Y)
    (Z : IntegralClosedSubspace D.site D.base D.base_mem X)
    (W : IntegralClosedSubspace D.site D.base D.base_mem Y) :
    cycleImageSubspace D sY hY f Z = W :=
  IntegralClosedSubspace.eq_of_subsingleton_points D.site D.base D.base_mem hY.1 hpt _ _

/-! ### The degree of a zero cycle -/

/-- **The degree of a zero cycle, at the level of cycles.** For `p : X ⟶ Y` proper, the degree of
a zero cycle on `X` read at an integral closed subspace `W` of `Y`: the coefficient at `W` of the
proper pushforward of the cycle.

When `|Y|` is a single point — the case `Y = Spec(k)` of Stacks 0ESG — the subspace `W` is unique
by `AlgebraicGeometry.Space.IntegralClosedSubspace.eq_of_subsingleton_points`, and reading the
coefficient there is the identification of the zero cycles on `Y` with `ℤ` which sends the
fundamental cycle `[Y]` to `1`. -/
def cycleDegree (sX : X ⟶ D.space) (hX : D.IsGood sX) (sY : Y ⟶ D.space) (hY : D.IsGood sY)
    {p : X ⟶ Y} (hbase : p ≫ sY = sX) (hp : IsProper D.site D.base D.base_mem p)
    (W : IntegralClosedSubspace D.site D.base D.base_mem Y) (α : CycleGroup D sX 0) : ℤ :=
  (properPushforward D sX hX sY hY hbase hp.2.1.2 0 α).1 W

/-- **Stacks 0ESH, in the shape in which this library presents a cycle.** Let `p : X ⟶ Y` be a
proper morphism of good algebraic spaces over the base with `|Y|` a single point and with the
dimension function induced on `Y` vanishing — the situation of `Y = Spec(k)`. A zero cycle `α` on
`X` is the coefficient family `Z ↦ n_Z` on the integral closed subspaces of `X`, so the formal
sum `α = ∑ n_Z [Z]` of the source is `α` itself, and the degree of `α` is

    deg(α) = ∑ n_Z deg(Z),

the sum running over every integral closed subspace of `X` and `deg(Z)` being the degree
`[R(Z) : k]` of `Z → Spec(k)`.

This is the definition of proper pushforward, Stacks 0EP1, after two identifications. The sum
defining the pushforward coefficient at `W` runs over the integral closed subspaces of `X` whose
integral closed image is `W`, and that is all of them, by
`AlgebraicGeometry.Space.cycleImageSubspace_eq_of_subsingleton_points`. And at a subspace `Z`
with a nonzero coefficient the weight of Stacks 0EP0 is the degree rather than zero: the
δ-dimension of `Z` is zero because `α` is a zero cycle, and the δ-dimension of its image is zero
because the dimension function of `Y` vanishes. -/
@[stacks 0ESH "deg(Z) read as the degree [R(Z) : k] of the extension of function fields, which \
is the weight of Stacks 0EP0, rather than as dim_k Γ(Z, 𝒪_Z): the two are identified on a \
scheme by Stacks.Chow.isIso_Γevaluation_of_isIntegral_of_subsingleton, and for an algebraic \
space there is no evaluation of a global function in a residue field. Spec(k) is modelled as a \
good algebraic space over the base with one point and vanishing dimension function. The degree \
is the cycle-level degree, not the one on CH_0 of Stacks 0ESG, which needs Stacks 0EQC"]
theorem cycleDegree_eq_finsum (sX : X ⟶ D.space) (hX : D.IsGood sX) (sY : Y ⟶ D.space)
    (hY : D.IsGood sY) {p : X ⟶ Y} (hbase : p ≫ sY = sX)
    (hp : IsProper D.site D.base D.base_mem p)
    (hpt : Subsingleton (points D.site D.base D.base_mem Y))
    (hδ : ∀ y : points D.site D.base D.base_mem Y, D.deltaValue sY y = 0)
    (W : IntegralClosedSubspace D.site D.base D.base_mem Y) (α : CycleGroup D sX 0) :
    cycleDegree D sX hX sY hY hbase hp W α =
      ∑ᶠ Z : IntegralClosedSubspace D.site D.base D.base_mem X, α.1 Z *
        (cycleResidueDegree D sX hX sY hY p
          (Z.ambientGenericPoint D.site D.base D.base_mem) : ℤ) := by
  have huniv : {Z : IntegralClosedSubspace D.site D.base D.base_mem X |
      cycleImageSubspace D sY hY p Z = W} = Set.univ :=
    Set.eq_univ_of_forall fun Z =>
      cycleImageSubspace_eq_of_subsingleton_points D sY hY hpt p Z W
  rw [cycleDegree, properPushforward_coe, properPushforwardCoeff, huniv, finsum_mem_univ]
  refine finsum_congr fun Z => ?_
  by_cases hZ : α.1 Z = 0
  · rw [hZ, zero_mul, zero_mul]
  · have hd : deltaDimension D sY (cycleImageSubspace D sY hY p Z) = deltaDimension D sX Z := by
      rw [cycleImageSubspace_eq_of_subsingleton_points D sY hY hpt p Z W, α.2.2 Z hZ]
      exact hδ _
    rw [properPushforwardWeight_eq_cycleResidueDegree D sX hX sY hY p hd]

/-- **Stacks 0ESH, in the source's shape.** In the situation of
`AlgebraicGeometry.Space.cycleDegree_eq_finsum`, let the zero cycle `α` be presented as a finite
sum `α = ∑ n_i [Z_i]` over pairwise distinct integral closed subspaces `Z_i ⊆ X` — that is, the
coefficient of `α` at `Z_i` is `n_i` and its coefficient at a subspace which is no `Z_i`
vanishes. Then

    deg(α) = ∑ n_i deg(Z_i),

with `deg(Z_i)` the degree `[R(Z_i) : k]` of `Z_i → Spec(k)`.

The sum over all integral closed subspaces of `AlgebraicGeometry.Space.cycleDegree_eq_finsum` is
supported on the `Z_i`, and the `Z_i` are distinct, so it is the finite sum over the index
type. -/
@[stacks 0ESH "the same restriction on deg(Z_i) as on \
AlgebraicGeometry.Space.cycleDegree_eq_finsum; this is its restatement for a cycle given as a \
finite sum over pairwise distinct integral closed subspaces"]
theorem cycleDegree_eq_sum (sX : X ⟶ D.space) (hX : D.IsGood sX) (sY : Y ⟶ D.space)
    (hY : D.IsGood sY) {p : X ⟶ Y} (hbase : p ≫ sY = sX)
    (hp : IsProper D.site D.base D.base_mem p)
    (hpt : Subsingleton (points D.site D.base D.base_mem Y))
    (hδ : ∀ y : points D.site D.base D.base_mem Y, D.deltaValue sY y = 0)
    (W : IntegralClosedSubspace D.site D.base D.base_mem Y) (α : CycleGroup D sX 0)
    {J : Type v} [Fintype J] (Z : J → IntegralClosedSubspace D.site D.base D.base_mem X)
    (hZ : Function.Injective Z) (n : J → ℤ) (hn : ∀ i, α.1 (Z i) = n i)
    (hsupp : ∀ T : IntegralClosedSubspace D.site D.base D.base_mem X,
      (∀ i, Z i ≠ T) → α.1 T = 0) :
    cycleDegree D sX hX sY hY hbase hp W α =
      ∑ i : J, n i * (cycleResidueDegree D sX hX sY hY p
        ((Z i).ambientGenericPoint D.site D.base D.base_mem) : ℤ) := by
  have hrange : ∀ T ∈ Function.support (fun T : IntegralClosedSubspace D.site D.base D.base_mem X
      => α.1 T * (cycleResidueDegree D sX hX sY hY p
        (T.ambientGenericPoint D.site D.base D.base_mem) : ℤ)),
      T ∈ (Set.univ : Set (IntegralClosedSubspace D.site D.base D.base_mem X)) ↔
        T ∈ Set.range Z := by
    intro T hT
    refine ⟨fun _ => ?_, fun _ => Set.mem_univ T⟩
    by_contra hT'
    exact hT (by simp only [hsupp T fun i hi => hT' ⟨i, hi⟩, zero_mul])
  rw [cycleDegree_eq_finsum D sX hX sY hY hbase hp hpt hδ W α, ← finsum_mem_univ,
    finsum_mem_inter_support_eq' _ Set.univ (Set.range Z) hrange, finsum_mem_range hZ,
    finsum_eq_sum_of_fintype]
  exact Finset.sum_congr rfl fun i _ => by simp only [hn i]

end Degree

end AlgebraicGeometry.Space

end
