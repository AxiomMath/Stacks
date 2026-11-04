module

public import StacksFrontier.AlgebraicGeometry.Spaces.CoherentEtaleChart
public import StacksFrontier.AlgebraicGeometry.Spaces.CoherentQuasicoherence
public import StacksFrontier.AlgebraicGeometry.Spaces.QuasicoherentEtaleMorphism
import StacksFrontier.AlgebraicGeometry.Spaces.CoherentQuasicoherence

/-!
# Coherence on an algebraic space is tested on its étale charts, in both directions

Stacks 07UB characterizes the coherent `𝒪_X`-modules on a locally Noetherian algebraic space
`X` by five equivalent conditions.  Its conditions (4) and (5) test coherence on étale scheme
charts: (4) asks that the pullback to *every* étale chart be coherent, and (5) that the
pullback to *one* surjective étale chart be coherent.  This file proves the three equivalences
among conditions (1), (4) and (5), with the restriction to a chart read as restriction to the
slice of the small étale site at that chart.

The local-to-global halves — (4) ⇒ (1) and (5) ⇒ (1) — are
`StacksFrontier.AlgebraicGeometry.Spaces.CoherentEtaleChart`.  What is added here is the
global-to-local half, `Stacks.SheafOfModules.isCoherentOnSite_over`, the coherence counterpart
of `Stacks.SheafOfModules.isQuasicoherent_over`, together with the observation that an
algebraic space always *has* an étale chart surjective on points
(`AlgebraicGeometry.Space.exists_surjective_smallEtale_chart`), which is what makes condition
(5) follow from condition (4) rather than only the other way round.

Note that no locally Noetherian hypothesis appears anywhere below.  Stacks 07UB carries one
because its conditions (2) and (3) need it; the mutual equivalence of (1), (4) and (5) is the
local-on-a-covering clause of Stacks 03DN and holds for every module on every algebraic space.

## Main results

* `AlgebraicGeometry.Space.isCoherentOnSite_iff_over_of_isSurjective`,
  `AlgebraicGeometry.Space.isCoherentOnSite_iff_forall_over` and
  `AlgebraicGeometry.Space.isCoherentOnSite_iff_forall_affine_over`: coherence on the small
  étale ringed site is equivalent to coherence of the restriction to one surjective étale
  chart, to every étale chart, and to every affine étale chart.  These are at a free module
  universe.
* `AlgebraicGeometry.Space.isCoherent_iff_forall_over`: **Stacks 07UB, conditions (1) and
  (4)**.
* `AlgebraicGeometry.Space.isCoherent_iff_exists_surjective_over`: **Stacks 07UB, conditions
  (1) and (5)**.
* `AlgebraicGeometry.Space.forall_over_iff_exists_surjective_over`: **Stacks 07UB, conditions
  (4) and (5)**, the adjacent equivalence at the bottom of the chain, stated without reference
  to condition (1).

## Implementation notes

Coherence of a module on an algebraic space, `AlgebraicGeometry.Space.IsCoherent`, is
quasi-coherence on the small étale site together with coherence on that site; but the first
clause is a consequence of the second on any site at all, by Stacks 03DL(8) ⟹ 03DL(6), so
`AlgebraicGeometry.Space.isCoherent_iff_isCoherentOnSite` strips it and the conditions (4) and
(5) below say exactly that the slice restriction is coherent, with nothing adjoined.  The
quasi-coherence of the restriction is then a consequence rather than a hypothesis, and
`Stacks.SheafOfModules.isQuasicoherent_over` and
`AlgebraicGeometry.Space.isQuasicoherentOnSite_iff_forall_over` are no longer needed here.

**The restriction is restriction to the slice, not the pullback `φ^*` that Stacks 07UB names.**
The slice of `X_étale` at a chart `φ : U → X` is the small étale site of `U`, which is Stacks
04M0, formalized as `AlgebraicGeometry.Space.smallEtaleEquivalenceOverChart`; identifying a
module on the slice with `φ^*` of a module on `X` is the abuse of notation of Stacks Equation
03LW, and transporting a module across that equivalence of *sites* additionally requires
matching the two structure sheaves, which this development does not do.  This is the same
reading under which `AlgebraicGeometry.Space.isQuasicoherentOnSite_iff_over_of_isSurjective`
and `AlgebraicGeometry.Space.isQuasicoherentOnSite_iff_forall_affine_over` carry
`@[stacks 03M0]`, and the conditions compared below are in that one reading on both sides of
each equivalence.  `AlgebraicGeometry.Space.modulePullback` is not a substitute: it is the
tensor inverse image of Stacks 03D6, part (2), and no comparison of it with the étale
restriction `AlgebraicGeometry.Space.etaleModulePullback` is proved anywhere here.

The three site-level equivalences are at a **free module universe**, since neither
`SheafOfModules.IsCoherentOnSite` nor `PresheafOfModules.IsFiniteType` pins it and nothing
below synthesizes a sheafification, a cokernel or an abelian structure, and so is
`AlgebraicGeometry.Space.forall_over_iff_exists_surjective_over`.  The three statements about
`AlgebraicGeometry.Space.IsCoherent` are confined to module universe `u`, and the binding
constraint is exactly one declaration:
`SheafOfModules.isQuasicoherentOnSite_of_isCoherentOnSite` takes the module sections in the
universe of the coefficient rings.

## References

* [Stacks Project, Tag 07UB](https://stacks.math.columbia.edu/tag/07UB)
* [Stacks Project, Tag 07UA](https://stacks.math.columbia.edu/tag/07UA)
* [Stacks Project, Tag 03DN](https://stacks.math.columbia.edu/tag/03DN)
* [Stacks Project, Tag 03M0](https://stacks.math.columbia.edu/tag/03M0)
* [Stacks Project, Tag 04M0](https://stacks.math.columbia.edu/tag/04M0)
-/

@[expose] public section

open CategoryTheory Opposite

universe u m

namespace AlgebraicGeometry.Space

variable (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)
    (F : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u) (hF : IsAlgebraicSpace B S hS F)

/-- **Coherence on the small étale site is tested on one surjective étale chart.**  A module on
the small étale site of an algebraic space is coherent on that site if and only if its
restriction to the slice at one étale chart whose structure morphism is surjective on points is
coherent.

The reverse implication is `AlgebraicGeometry.Space.isCoherentOnSite_of_over_of_isSurjective`;
the forward one is `Stacks.SheafOfModules.isCoherentOnSite_over` and needs no surjectivity.
The module universe is free. -/
theorem isCoherentOnSite_iff_over_of_isSurjective (M : Modules.{u, m} B S hS F hF)
    (U : (smallEtaleRingedSite B S hS F hF).C) (hsurj : IsSurjective B S hS U.1.hom) :
    SheafOfModules.IsCoherentOnSite M ↔
      SheafOfModules.IsCoherentOnSite
        (R := (Stacks.SheafOfModules.Tensor.ringSheaf
          ((smallEtaleRingedSite B S hS F hF).over U).O)) (M.over U) :=
  ⟨fun h => Stacks.SheafOfModules.isCoherentOnSite_over M h U,
    isCoherentOnSite_of_over_of_isSurjective B S hS F hF M U hsurj⟩

/-- **Coherence on the small étale site is tested on every étale chart.**  A module on the
small étale site of an algebraic space is coherent on that site if and only if its restriction
to the slice at every étale chart is coherent.  The module universe is free. -/
theorem isCoherentOnSite_iff_forall_over (M : Modules.{u, m} B S hS F hF) :
    SheafOfModules.IsCoherentOnSite M ↔
      ∀ U : (smallEtaleRingedSite B S hS F hF).C,
        SheafOfModules.IsCoherentOnSite
          (R := (Stacks.SheafOfModules.Tensor.ringSheaf
            ((smallEtaleRingedSite B S hS F hF).over U).O)) (M.over U) :=
  ⟨fun h U => Stacks.SheafOfModules.isCoherentOnSite_over M h U,
    isCoherentOnSite_of_forall_over B S hS F hF M⟩

/-- **Coherence on the small étale site is tested on every affine étale chart.**  A module on
the small étale site of an algebraic space is coherent on that site if and only if its
restriction to the slice at every étale chart with affine underlying scheme is coherent.  The
module universe is free. -/
theorem isCoherentOnSite_iff_forall_affine_over (M : Modules.{u, m} B S hS F hF) :
    SheafOfModules.IsCoherentOnSite M ↔
      ∀ U : (smallEtaleRingedSite B S hS F hF).C,
        IsAffine ((BigFppfOver.toScheme B S hS).obj ((SmallEtale.toOver B S hS F).obj U)) →
        SheafOfModules.IsCoherentOnSite
          (R := (Stacks.SheafOfModules.Tensor.ringSheaf
            ((smallEtaleRingedSite B S hS F hF).over U).O)) (M.over U) :=
  ⟨fun h U _ => Stacks.SheafOfModules.isCoherentOnSite_over M h U,
    isCoherentOnSite_of_forall_affine_over B S hS F hF M⟩

/-- **Stacks 07UB, conditions (1) and (4).**  A module on an algebraic space is coherent if and
only if its restriction to the slice at every étale chart is coherent there.

The restriction is restriction to the slice of the small étale site at the chart; see the
implementation notes.  The module universe is the universe of the structure rings, which
`AlgebraicGeometry.Space.isCoherent_iff_isCoherentOnSite` pins. -/
@[stacks 07UB "conditions (1) and (4)"]
theorem isCoherent_iff_forall_over (M : Modules.{u, u} B S hS F hF) :
    IsCoherent B S hS F hF M ↔
      ∀ U : (smallEtaleRingedSite B S hS F hF).C,
        SheafOfModules.IsCoherentOnSite
          (R := (Stacks.SheafOfModules.Tensor.ringSheaf
            ((smallEtaleRingedSite B S hS F hF).over U).O)) (M.over U) :=
  (isCoherent_iff_isCoherentOnSite B S hS F hF M).trans
    (isCoherentOnSite_iff_forall_over B S hS F hF M)

/-- **Stacks 07UB, conditions (1) and (5).**  A module on an algebraic space is coherent if and
only if there is an étale chart whose structure morphism is surjective on points and whose
slice restriction is coherent.

The forward implication uses that an algebraic space has such a chart at all, namely its
atlas: `AlgebraicGeometry.Space.exists_surjective_smallEtale_chart`.  The restriction is
restriction to the slice of the small étale site at the chart; see the implementation notes.
The module universe is the universe of the structure rings, which
`AlgebraicGeometry.Space.isCoherent_iff_isCoherentOnSite` pins. -/
@[stacks 07UB "conditions (1) and (5)"]
theorem isCoherent_iff_exists_surjective_over (M : Modules.{u, u} B S hS F hF) :
    IsCoherent B S hS F hF M ↔
      ∃ U : (smallEtaleRingedSite B S hS F hF).C, IsSurjective B S hS U.1.hom ∧
        SheafOfModules.IsCoherentOnSite
          (R := (Stacks.SheafOfModules.Tensor.ringSheaf
            ((smallEtaleRingedSite B S hS F hF).over U).O)) (M.over U) :=
  (isCoherent_iff_isCoherentOnSite B S hS F hF M).trans
    ⟨fun h => let ⟨U, hU⟩ := exists_surjective_smallEtale_chart B S hS F hF
      ⟨U, hU, Stacks.SheafOfModules.isCoherentOnSite_over M h U⟩,
    fun ⟨U, hU, hcoh⟩ => (isCoherentOnSite_iff_over_of_isSurjective B S hS F hF M U hU).2 hcoh⟩

/-- **Stacks 07UB, conditions (4) and (5).**  The slice restriction of a module on an algebraic
space is coherent at *every* étale chart if and only if it is coherent at *one* étale chart
whose structure morphism is surjective on points.

This is the adjacent equivalence at the bottom of the chain of Stacks 07UB, stated without
reference to its condition (1).  Unlike the two equivalences with condition (1) it is at a free
module universe: both implications pass through coherence of the module on the whole small
étale ringed site, and only the identification of that with condition (1) needs the universe
fixed.  The restriction is restriction to the slice of the small étale site at the chart; see
the implementation notes. -/
@[stacks 07UB "conditions (4) and (5)"]
theorem forall_over_iff_exists_surjective_over (M : Modules.{u, m} B S hS F hF) :
    (∀ U : (smallEtaleRingedSite B S hS F hF).C,
        SheafOfModules.IsCoherentOnSite
          (R := (Stacks.SheafOfModules.Tensor.ringSheaf
            ((smallEtaleRingedSite B S hS F hF).over U).O)) (M.over U)) ↔
      ∃ U : (smallEtaleRingedSite B S hS F hF).C, IsSurjective B S hS U.1.hom ∧
        SheafOfModules.IsCoherentOnSite
          (R := (Stacks.SheafOfModules.Tensor.ringSheaf
            ((smallEtaleRingedSite B S hS F hF).over U).O)) (M.over U) :=
  ⟨fun h => let ⟨U, hU⟩ := exists_surjective_smallEtale_chart B S hS F hF; ⟨U, hU, h U⟩,
    fun ⟨U, hU, hcoh⟩ => (isCoherentOnSite_iff_forall_over B S hS F hF M).1
      ((isCoherentOnSite_iff_over_of_isSurjective B S hS F hF M U hU).2 hcoh)⟩

end AlgebraicGeometry.Space

end
