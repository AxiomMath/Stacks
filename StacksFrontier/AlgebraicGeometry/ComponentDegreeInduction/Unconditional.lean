module

public import StacksFrontier.AlgebraicGeometry.ComponentDegreeInduction.Basic
public import StacksFrontier.AlgebraicGeometry.CurveTensorEulerUnit.Unconditional
public import StacksFrontier.AlgebraicGeometry.ProperCohomologyFinite.OverFieldProper
public import StacksCore.Tactic.StacksAttribute

/-!
# The inductive step of [Stacks, Tag 0AYW] with its two assumed inputs discharged

**The prefix `AlgebraicGeometry.` is elided from every declaration name below.**

`curveDegree_eq_add_of_shortExact_pushforward` and
`curveDegree_eq_mul_of_shortExact_pushforward`
(`StacksFrontier/AlgebraicGeometry/ComponentDegreeInduction/Basic.lean`) prove the arithmetic of the
second paragraph of [Stacks, Tag 0AYW] — for a short exact sequence

`0 ⟶ j_*ℱ ⟶ 𝒪_X ⟶ i_*𝒪_W ⟶ 0`

with `j : C ⟶ X` and `i : W ⟶ X` closed immersions, `deg(ℰ) = r·deg(ℰ|_C) + deg(ℰ|_W)` — from
two inputs carried as hypotheses: `h02O6`, the finite dimensionality of [Stacks, Tag 02O6] on
`X`, and `h0AYV`, [Stacks, Tag 0AYV] on `C` with its coefficient `r`. Both are now theorems, and
this file supplies them, leaving the short exact sequence and the length identity as the only
remaining inputs of the step.

The price is one instance: `h0AYV` is [Stacks, Tag 0AYV], which is a statement about a proper
*curve*, so `C` must be one. In the use the source makes of the step `C` is the reduction of an
irreducible `X` of dimension one, which is a proper curve by
`Stacks.AlgebraicGeometry.ComponentDegrees.isCurve_reducedComponentι_comp`; so this is the
hypothesis under which the step is applied rather than a restriction of it. With `C` a curve the
coefficient `r` is no longer free either: [Stacks, Tag 0AYV] computes it, and it is the fibre
rank of `ℱ` at the generic point of `C`.

## Main results

* `curveDegree_eq_add_of_shortExact_pushforward_of_isCurve`:
  `deg(ℰ) = r·deg(ℰ|_C) + deg(ℰ|_W)` with `r = dim_{κ(ξ)} ℱ_ξ`, with no hypothesis beyond the
  short exact sequence.
* `curveDegree_eq_mul_of_shortExact_pushforward_of_isCurve`: the same with the source's length
  identity `m = r + m'` and the inductive hypothesis `deg(ℰ|_W) = m'·deg(ℰ|_C)` substituted,
  giving `deg(ℰ) = m·deg(ℰ|_C)`.

## Implementation notes

**The two degree arguments agree by proof irrelevance.** [Stacks, Tag 0AYV] states its degree
with the dimension bound `le_of_eq IsCurve.topologicalKrullDim_eq_one`, while the step states it
with the bound `hC` it is given. `AlgebraicGeometry.curveDegree` takes that bound as a `Prop`
argument, so the two readings are definitionally equal and `h0AYV` is supplied with no rewriting;
the same holds of the coherence witness of the tensor product, which [Stacks, Tag 0AYV] produces
existentially and the step names explicitly.

**No [Stacks, Tag 0AYW] attribute is attached.** These statements still carry the short exact
sequence and, in the second, the length identity and the inductive hypothesis; none of the three
is the tag, whose conclusion is a sum over the one-dimensional components of an arbitrary `X`.

## What this leaves open in [Stacks, Tag 0AYW]

Two steps, both above this one and unchanged by it:

1. the short exact sequence itself — the ideal sheaf `ℐ` of the reduction, its powers, the
   closed subschemes they cut out, and the nilpotence `ℐ^{e+1} = 0` of [Stacks, Tag 01Y9] —
   together with the length computation `m = r + m'` at the generic point;
2. the first paragraph of the proof, which reduces an arbitrary `X` to an irreducible one.

## References

* [Stacks Project, Tag 0AYW](https://stacks.math.columbia.edu/tag/0AYW)
* [Stacks Project, Tag 0AYV](https://stacks.math.columbia.edu/tag/0AYV)
* [Stacks Project, Tag 02O6](https://stacks.math.columbia.edu/tag/02O6)
-/

@[expose] public noncomputable section

open CategoryTheory TopologicalSpace

universe u

namespace AlgebraicGeometry

variable (k : Type u) [Field k] {X C W : Scheme.{u}} (f : X ⟶ Spec (.of k))

/-- **The inductive step of [Stacks, Tag 0AYW], with [Stacks, Tag 02O6] and [Stacks, Tag 0AYV]
discharged.** For `j : C ⟶ X` and `i : W ⟶ X` closed immersions with `C` a proper curve over
`k`, `ℱ` coherent on `C`, `ℰ` finite locally free of rank `n` on `X`, and a short exact sequence
`0 ⟶ j_*ℱ ⟶ 𝒪_X ⟶ i_*𝒪_W ⟶ 0`,

`deg(ℰ) = r·deg(ℰ|_C) + deg(ℰ|_W)`, `r = dim_{κ(ξ)} ℱ_ξ` the fibre rank of `ℱ` at the generic
point of `C`.

This is `curveDegree_eq_add_of_shortExact_pushforward` with `h02O6` supplied by
`forall_finiteDimensional_cohomologyOverField_of_isProper` and `h0AYV` by
`exists_eulerCharacteristic_tensorSheaf_eq_fiberRank_mul_curveDegree_add_of_isCurve`. -/
theorem curveDegree_eq_add_of_shortExact_pushforward_of_isCurve [IsProper f]
    [IsLocallyNoetherian X]
    (j : C ⟶ X) [IsClosedImmersion j] (i : W ⟶ X) [IsClosedImmersion i]
    [IsCurve k (j ≫ f)]
    (hX : topologicalKrullDim X ≤ 1) (hC : topologicalKrullDim C ≤ 1)
    (hW : topologicalKrullDim W ≤ 1)
    (E : X.Modules) (n : ℕ) [SheafOfModules.IsFiniteLocallyFreeOfRank.{u, u, u} E n]
    (F : C.Modules) (hF : SheafOfModules.IsCoherent F)
    (hE : SheafOfModules.IsCoherent E)
    (hOX : SheafOfModules.IsCoherent (SheafOfModules.unit X.ringCatSheaf))
    (hOW : SheafOfModules.IsCoherent (SheafOfModules.unit W.ringCatSheaf))
    (hEC : SheafOfModules.IsCoherent ((Scheme.Modules.pullback j).obj E))
    (hEW : SheafOfModules.IsCoherent ((Scheme.Modules.pullback i).obj E))
    (α : (Scheme.Modules.pushforward j).obj F ⟶ SheafOfModules.unit X.ringCatSheaf)
    (β : SheafOfModules.unit X.ringCatSheaf ⟶
      (Scheme.Modules.pushforward i).obj (SheafOfModules.unit W.ringCatSheaf))
    (w : α ≫ β = 0) (hS : (ShortComplex.mk α β w).ShortExact) :
    curveDegree k f hX E n =
      (Scheme.Modules.fiberRank F (genericPoint C) : ℤ) *
          @curveDegree k _ C (j ≫ f) _ hC ((Scheme.Modules.pullback j).obj E) n
            (isFiniteLocallyFreeOfRank_pullback j E n) +
        @curveDegree k _ W (i ≫ f) _ hW ((Scheme.Modules.pullback i).obj E) n
          (isFiniteLocallyFreeOfRank_pullback i E n) := by
  have hEC' := hEC
  have hF' := hF
  obtain ⟨_, h0AYV⟩ :=
    @exists_eulerCharacteristic_tensorSheaf_eq_fiberRank_mul_curveDegree_add_of_isCurve
      k _ C (j ≫ f) _ _ ((Scheme.Modules.pullback j).obj E) n
      (isFiniteLocallyFreeOfRank_pullback j E n) F hF'
  exact curveDegree_eq_add_of_shortExact_pushforward k f j i hX hC hW E n F hF hE hOX hOW hEC hEW
    α β w hS (forall_finiteDimensional_cohomologyOverField_of_isProper k f)
    (Scheme.Modules.fiberRank F (genericPoint C)) h0AYV

/-- **The inductive step of [Stacks, Tag 0AYW], with [Stacks, Tag 02O6] and [Stacks, Tag 0AYV]
discharged and the inductive hypothesis substituted.** Under the hypotheses of
`curveDegree_eq_add_of_shortExact_pushforward_of_isCurve`, together with the source's length
identity `m = r + m'` and the inductive hypothesis `deg(ℰ|_W) = m'·deg(ℰ|_C)`,

`deg(ℰ) = m·deg(ℰ|_C)`.

This is the conclusion of [Stacks, Tag 0AYW] for an irreducible `X` with reduction `C` of
multiplicity `m`, modulo the two steps the module docstring lists as still open. -/
theorem curveDegree_eq_mul_of_shortExact_pushforward_of_isCurve [IsProper f]
    [IsLocallyNoetherian X]
    (j : C ⟶ X) [IsClosedImmersion j] (i : W ⟶ X) [IsClosedImmersion i]
    [IsCurve k (j ≫ f)]
    (hX : topologicalKrullDim X ≤ 1) (hC : topologicalKrullDim C ≤ 1)
    (hW : topologicalKrullDim W ≤ 1)
    (E : X.Modules) (n : ℕ) [SheafOfModules.IsFiniteLocallyFreeOfRank.{u, u, u} E n]
    (F : C.Modules) (hF : SheafOfModules.IsCoherent F)
    (hE : SheafOfModules.IsCoherent E)
    (hOX : SheafOfModules.IsCoherent (SheafOfModules.unit X.ringCatSheaf))
    (hOW : SheafOfModules.IsCoherent (SheafOfModules.unit W.ringCatSheaf))
    (hEC : SheafOfModules.IsCoherent ((Scheme.Modules.pullback j).obj E))
    (hEW : SheafOfModules.IsCoherent ((Scheme.Modules.pullback i).obj E))
    (α : (Scheme.Modules.pushforward j).obj F ⟶ SheafOfModules.unit X.ringCatSheaf)
    (β : SheafOfModules.unit X.ringCatSheaf ⟶
      (Scheme.Modules.pushforward i).obj (SheafOfModules.unit W.ringCatSheaf))
    (w : α ≫ β = 0) (hS : (ShortComplex.mk α β w).ShortExact)
    (m m' : ℕ) (hm : m = Scheme.Modules.fiberRank F (genericPoint C) + m')
    (hind : @curveDegree k _ W (i ≫ f) _ hW ((Scheme.Modules.pullback i).obj E) n
        (isFiniteLocallyFreeOfRank_pullback i E n) =
      (m' : ℤ) * @curveDegree k _ C (j ≫ f) _ hC ((Scheme.Modules.pullback j).obj E) n
        (isFiniteLocallyFreeOfRank_pullback j E n)) :
    curveDegree k f hX E n =
      (m : ℤ) * @curveDegree k _ C (j ≫ f) _ hC ((Scheme.Modules.pullback j).obj E) n
        (isFiniteLocallyFreeOfRank_pullback j E n) := by
  rw [curveDegree_eq_add_of_shortExact_pushforward_of_isCurve k f j i hX hC hW E n F hF hE hOX
      hOW hEC hEW α β w hS, hind, hm]
  push_cast
  ring

end AlgebraicGeometry

end
