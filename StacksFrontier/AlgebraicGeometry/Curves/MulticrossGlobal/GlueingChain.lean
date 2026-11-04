module

public import StacksFrontier.AlgebraicGeometry.Curves.GlueingSquishing.NormalizationIsoRegularLocus
public import StacksFrontier.AlgebraicGeometry.Curves.MulticrossGlueingResolution
import all StacksFrontier.AlgebraicGeometry.Curves.MulticrossGlueingResolution

/-!
# Multicross singularities and glueing chains of the normalization

Let `k` be an algebraically closed field and `X` a reduced scheme of dimension at most one,
locally of finite type and quasi-compact over `k`. This file proves that every singular point of
`X` is a multicross singularity if and only if the normalization `ν : X^ν ⟶ X` factors as a
chain of glueings of two rational points, with no squishing of a tangent vector.

This is the global form of clause (3) of [Stacks, Tag 0C1X], which the proof of
[Stacks, Tag 0C20] uses: there the source writes "just glue the local sequences for each point to
find one that works for all singular points of `X`; some details omitted". The local statement
is `Stacks.Curves.isMulticrossSingularity_tfae`. Rather than glueing the local towers, the
argument here reruns the two halves of that proof on the whole of `X`, which is possible because
the singular locus is finite.

* If `ν` is a chain of glueings, its source is nonsingular, so `X` carries a tower of glueings in
  the sense of clause (3) of Tag 0C1X; along such a tower the completed local ring at every closed
  point is a multicross ring or a field, and at a singular point it is a multicross ring with at
  least two branches.
* Conversely, if every singular point is multicross, then the completed local ring at every closed
  point of `X` is seminormal: at a nonsingular point it is a power series ring in at most one
  variable, at a singular point a multicross ring. [Stacks, Tag 0C1L] factors `ν` into glueings
  and squishings, and no step of that factorization is a squishing, since a squishing produces a
  non-seminormal completion while seminormality of the completions propagates up the chain
  through every glueing.

A singular point of a reduced scheme of dimension at most one is automatically closed, since the
singular locus is closed and contains no irreducible component; this is what lets both sides
quantify over all points rather than closed ones.

## Main definitions

* `Stacks.GlueSquishFactor.IsGlueingChain`: a chain of glueings of two rational points, with no
  squishing of a tangent vector.
* `AlgebraicGeometry.normalizationOver`: the normalization morphism as a morphism over `Spec k`.

## Main results

* `Stacks.Curves.isClosed_singleton_of_not_isRegularLocalRing`: singular points are closed.
* `Stacks.Curves.forall_isMulticrossSingularity_of_isGlueingChain`: a glueing chain gives
  multicross singularities.
* `Stacks.Curves.isGlueingChain_normalizationOver_of_forall_isMulticrossSingularity`: multicross
  singularities give a glueing chain.
* `Stacks.Curves.isGlueingChain_normalizationOver_iff_forall_isMulticrossSingularity`: the
  equivalence.

## References

* [Stacks Project, Tag 0C1X](https://stacks.math.columbia.edu/tag/0C1X)
* [Stacks Project, Tag 0C1L](https://stacks.math.columbia.edu/tag/0C1L)
* [Stacks Project, Tag 0C20](https://stacks.math.columbia.edu/tag/0C20)
-/

@[expose] public noncomputable section

open CategoryTheory AlgebraicGeometry TopologicalSpace

universe u

namespace Stacks.GlueSquishFactor

/-- **A chain of glueings of two rational points.** This is
`Stacks.GlueSquishFactor.IsElementaryChain` with the squishings of tangent vectors removed: the
factorization of [Stacks, Tag 0C1L] in which no step is of the source's type (3). Equality in
[Stacks, Tag 0C20] holds exactly when the normalization admits such a factorization. -/
inductive IsGlueingChain (k : Type u) [Field k] [IsAlgClosed k] :
    {Y' Y : Over (Spec (.of k))} → (Y' ⟶ Y) → Prop
  /-- An isomorphism is the empty chain. -/
  | of_isIso {Y' Y : Over (Spec (.of k))} (f : Y' ⟶ Y) (hf : IsIso f) : IsGlueingChain k f
  /-- A single glueing of two rational points is a chain of length one. -/
  | of_glueing {Y' Y : Over (Spec (.of k))} (f : Y' ⟶ Y) (a b : Spec (.of k) ⟶ Y'.left)
      (h : AlgebraicGeometry.IsGlueingTwoPoints f.left a b) : IsGlueingChain k f
  /-- Chains compose. -/
  | comp {Z Y' Y : Over (Spec (.of k))} {g : Z ⟶ Y'} {f : Y' ⟶ Y} :
      IsGlueingChain k g → IsGlueingChain k f → IsGlueingChain k (g ≫ f)

/-- A chain of glueings is a chain of elementary modifications: a glueing of two points is one
of the two kinds of elementary modification. -/
theorem IsGlueingChain.isElementaryChain {k : Type u} [Field k] [IsAlgClosed k]
    {Y' Y : Over (Spec (.of k))} {f : Y' ⟶ Y} (hf : IsGlueingChain k f) :
    IsElementaryChain k f := by
  induction hf with
  | of_isIso g hg => exact .of_isIso g hg
  | of_glueing g a b h => exact .of_step g (Or.inl ⟨a, b, h⟩)
  | comp _ _ ihg ihf => exact .comp ihg ihf

end Stacks.GlueSquishFactor

namespace AlgebraicGeometry

/-- **The normalization of a reduced algebraic scheme, as a morphism of objects over `Spec k`.**
This is the morphism [Stacks, Tag 0C1L] factors, in the form
`AlgebraicGeometry.isElementaryChain_normalizationOverField` states it. -/
abbrev normalizationOver (k : Type u) [Field k] (X : Scheme.{u}) [X.Over (Spec (.of k))]
    [LocallyOfFiniteType (X ↘ Spec (.of k))] :
    Over.mk (normalizationOverField k (X ↘ Spec (.of k)) ≫ (X ↘ Spec (.of k))) ⟶
      Over.mk (X ↘ Spec (.of k)) :=
  Over.homMk (normalizationOverField k (X ↘ Spec (.of k))) rfl

end AlgebraicGeometry

namespace Stacks.Curves

open Stacks.GlueSquishFactor

/-- **A singular point of a reduced Nagata scheme of dimension at most one is closed.** The
singular locus is closed, being the complement of the regular locus, which is open for a Nagata
scheme of dimension at most one; and it contains no irreducible component, since the generic
point of a component of a reduced scheme is regular. In a space of dimension at most one every
point of such a closed set is closed. -/
theorem isClosed_singleton_of_not_isRegularLocalRing {X : Scheme.{u}} [IsReduced X]
    (hNagata : IsNagataScheme X) (hdim : topologicalKrullDim X ≤ 1) {x : X}
    (hsing : ¬ IsRegularLocalRing (X.presheaf.stalk x)) : IsClosed ({x} : Set X) :=
  Stacks.Topology.Dimension.isClosed_singleton_of_not_irreducibleComponent_subset hdim
    (isOpen_regularLocus_of_isNagataScheme X hNagata hdim).isClosed_compl
    (fun _ hC ↦ not_subset_singularLocus_of_mem_irreducibleComponents X hC) hsing

/-- A chain of glueings `f : Y' ⟶ Y` is a tower of glueings joining `Y` to a scheme isomorphic to
`Y'`. -/
private theorem IsGlueingChain.hasGlueingTowerTo {k : Type u} [Field k] [IsAlgClosed k]
    {Y' Y : Over (Spec (.of k))} {f : Y' ⟶ Y} (h : IsGlueingChain k f) :
    HasGlueingTowerTo k Y Y' := by
  induction h with
  | of_isIso g hg =>
    have := hg
    exact hasGlueingTowerTo_of_iso (asIso g).symm
  | of_glueing g a b hg => exact ⟨1, _, g, a, b, hg, ⟨Iso.refl _⟩⟩
  | comp _ _ ihg ihf => exact ihf.trans ihg

/-- **No step of a chain of elementary modifications over a scheme with seminormal completed
local rings is a squishing of a tangent vector**, so such a chain is a chain of glueings of two
points; and the completed local rings at the source of the chain are seminormal too.

This is the step of the proof of [Stacks, Tag 0C1X] that rules out a squishing of a tangent
vector, kept here at the level of the chain itself rather than of the tower it produces: a
squishing produces a non-seminormal completion, while seminormality of the completed local rings
travels up the chain through every glueing. -/
private theorem isGlueingChain_of_isElementaryChain {k : Type u} [Field k] [IsAlgClosed k]
    {X' X : Over (Spec (.of k))} {f : X' ⟶ X} (hchain : IsElementaryChain k f)
    (hft : LocallyOfFiniteType X.hom) (hred : IsReduced X'.left)
    (hsemi : ∀ z : X.left, IsClosed ({z} : Set X.left) →
      IsSeminormalRing (Scheme.completedLocalRing X.left z)) :
    IsGlueingChain k f ∧
      ∀ z : X'.left, IsClosed ({z} : Set X'.left) →
        IsSeminormalRing (Scheme.completedLocalRing X'.left z) := by
  induction hchain with
  | @of_isIso Y' Y g hg =>
    have := hg
    have : IsIso g.left := inferInstanceAs (IsIso ((Over.forget (Spec (.of k))).map g))
    let : LocallyOfFiniteType Y.hom := hft
    let : IsLocallyNoetherian Y.left := LocallyOfFiniteType.isLocallyNoetherian Y.hom
    let : LocallyOfFiniteType Y'.hom := by rw [← Over.w g]; infer_instance
    let : IsLocallyNoetherian Y'.left := LocallyOfFiniteType.isLocallyNoetherian Y'.hom
    refine ⟨.of_isIso g hg, fun z hz ↦ ?_⟩
    have hzc : IsClosed ({g.left z} : Set Y.left) := by
      simpa using g.left.isClosedMap _ hz
    exact Stacks.RingTheory.Seminormal.IsSeminormalRing.of_ringEquiv
      (completedLocalRing_ringEquiv_of_isIso_stalkMap g.left z).symm (hsemi _ hzc)
  | @of_step Y' Y g hg =>
    let : LocallyOfFiniteType Y.hom := hft
    let : IsLocallyNoetherian Y.left := LocallyOfFiniteType.isLocallyNoetherian Y.hom
    let := hred
    rcases hg with ⟨a, b, hh⟩ | ⟨θ, hh⟩
    · let : LocallyOfFiniteType Y'.hom := hh.2.2.2.2.1
      let : IsLocallyNoetherian Y'.left := LocallyOfFiniteType.isLocallyNoetherian Y'.hom
      exact ⟨.of_glueing g a b hh,
        isSeminormalRing_completedLocalRing_of_isGlueingTwoPoints g.left a b hh hsemi⟩
    · exact (not_isSquishingTangentVector_of_seminormal_completions g.left θ hsemi hh).elim
  | @comp Z Y' Y g gf hg hf ihg ihf =>
    have hftMid := locallyOfFiniteType_of_isElementaryChain hf hft
    have hredMid := isReduced_of_isElementaryChain hg hred
    obtain ⟨h₁, hsemiMid⟩ := ihf hft hredMid hsemi
    obtain ⟨h₂, hsemiTop⟩ := ihg hftMid hred hsemiMid
    exact ⟨.comp h₂ h₁, hsemiTop⟩

/-- **If the normalization is a chain of glueings, every singular point is multicross.** The
source of the chain, the normalization, is nonsingular, so the chain is a tower of glueings in
the sense of clause (3) of [Stacks, Tag 0C1X] over the whole of `X`; along such a tower the
completed local ring at every closed point is a multicross ring or a field, and at a singular
point, which is closed, it is therefore a multicross ring with at least two branches. -/
theorem forall_isMulticrossSingularity_of_isGlueingChain (k : Type u) [Field k] [IsAlgClosed k]
    (X : Scheme.{u}) [X.Over (Spec (.of k))] [LocallyOfFiniteType (X ↘ Spec (.of k))]
    [IsReduced X] (hdim : topologicalKrullDim X ≤ 1)
    (h : IsGlueingChain k (normalizationOver k X)) :
    ∀ x : X, ¬ IsRegularLocalRing (X.presheaf.stalk x) → IsMulticrossSingularity k X x := by
  let : IsLocallyNoetherian X := LocallyOfFiniteType.isLocallyNoetherian (X ↘ Spec (.of k))
  have hNagata := isNagataScheme_of_locallyOfFiniteType_over_field k (X ↘ Spec (.of k))
  have hreg : IsRegular (normalizationSchemeOverField k (X ↘ Spec (.of k))) :=
    normalizationScheme_isRegular hNagata _ hdim
  obtain ⟨n, htower⟩ :=
    exists_isGlueingTower_of_hasGlueingTowerTo (IsGlueingChain.hasGlueingTowerTo h) hreg
  intro x hsing
  have hx := isClosed_singleton_of_not_isRegularLocalRing hNagata hdim hsing
  exact isMulticrossSingularity_of_hasMulticrossOrFieldCompletion k x hx hsing
    (hasMulticrossOrFieldCompletion_of_isGlueingTower n _ htower
      ‹_› hdim x hx)

/-- **If every singular point is multicross, the normalization is a chain of glueings.** The
completed local ring at every closed point of `X` is seminormal: at a nonsingular point it is a
field or a power series ring in one variable, and at a singular point a multicross ring.
[Stacks, Tag 0C1L] factors the normalization into glueings of two points and squishings of
tangent vectors, and no step of it is a squishing, because seminormality of the completions
propagates up the chain through the glueings while a squishing destroys it. -/
theorem isGlueingChain_normalizationOver_of_forall_isMulticrossSingularity (k : Type u) [Field k]
    [IsAlgClosed k] (X : Scheme.{u}) [X.Over (Spec (.of k))]
    [LocallyOfFiniteType (X ↘ Spec (.of k))] [QuasiCompact (X ↘ Spec (.of k))] [IsReduced X]
    (hdim : topologicalKrullDim X ≤ 1)
    (h : ∀ x : X, ¬ IsRegularLocalRing (X.presheaf.stalk x) → IsMulticrossSingularity k X x) :
    IsGlueingChain k (normalizationOver k X) := by
  let : IsLocallyNoetherian X := LocallyOfFiniteType.isLocallyNoetherian (X ↘ Spec (.of k))
  have hsemi : ∀ z : X, IsClosed ({z} : Set X) →
      IsSeminormalRing (Scheme.completedLocalRing X z) := by
    intro z hz
    by_cases hr : IsRegularLocalRing (X.presheaf.stalk z)
    · exact isSeminormalRing_completedLocalRing_of_hasMulticrossOrFieldCompletion
        (hasMulticrossOrFieldCompletion_of_regular k X z hz hr
          ((AlgebraicGeometry.ringKrullDim_stalk_le_topologicalKrullDim z).trans hdim))
    · obtain ⟨m, hm, hc⟩ := (h z hr).exists_hasMulticrossCompletion
      exact isSeminormalRing_completedLocalRing_of_hasMulticrossOrFieldCompletion
        (Or.inr ⟨m, by omega, hc⟩)
  have hredν : IsReduced (normalizationSchemeOverField k (X ↘ Spec (.of k))) :=
    Scheme.isReduced_normalizationScheme X
      (finite_irreducibleComponents_of_locallyOfFiniteType k (X ↘ Spec (.of k)))
  exact (isGlueingChain_of_isElementaryChain
    (isElementaryChain_normalizationOverField k (X ↘ Spec (.of k)) hdim)
    ‹_› hredν hsemi).1

/-- **Every singular point of `X` is multicross if and only if the normalization of `X` is a chain
of glueings of two rational points with no squishing.** Here `k` is algebraically closed and `X`
is reduced, of dimension at most one, locally of finite type and quasi-compact over `k`.

This is clause (3) of [Stacks, Tag 0C1X] made global over the finitely many singular points, the
step the proof of [Stacks, Tag 0C20] leaves out ("just glue the local sequences for each point to
find one that works for all singular points"). -/
theorem isGlueingChain_normalizationOver_iff_forall_isMulticrossSingularity (k : Type u)
    [Field k] [IsAlgClosed k] (X : Scheme.{u}) [X.Over (Spec (.of k))]
    [LocallyOfFiniteType (X ↘ Spec (.of k))] [QuasiCompact (X ↘ Spec (.of k))] [IsReduced X]
    (hdim : topologicalKrullDim X ≤ 1) :
    IsGlueingChain k (normalizationOver k X) ↔
      ∀ x : X, ¬ IsRegularLocalRing (X.presheaf.stalk x) → IsMulticrossSingularity k X x :=
  ⟨forall_isMulticrossSingularity_of_isGlueingChain k X hdim,
    isGlueingChain_normalizationOver_of_forall_isMulticrossSingularity k X hdim⟩

end Stacks.Curves

end
