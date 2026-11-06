module

public import StacksCore.Tactic.StacksAttribute
public import StacksFrontier.AlgebraicGeometry.Spaces.Groupoids.More.InvariantSourceLocus
public import StacksFrontier.AlgebraicGeometry.Spaces.Groupoids.Stabilizer.Composition
public import StacksFrontier.AlgebraicGeometry.Spaces.Groupoids.Stabilizer.RestrictionArrows

/-!
# Invariance of the locus where the stabilizer of a groupoid has a target-local property

Let `(U, R, s, t, c)` be a groupoid in algebraic spaces over an algebraic space `B` over a
scheme `S`, with stabilizer `G → U`, let `τ` be one of the fppf, syntomic, smooth and étale
topologies of **Stacks 03YH**, and let `P` be a property of morphisms of algebraic spaces
local on the target for `τ`. If both `s` and `t` are `τ`-coverings, then the largest open
subspace `W ⊆ U` over which the restriction of the stabilizer has `P` is invariant under the
groupoid.

The reason is that the two base changes of the stabilizer along `s` and along `t` are
isomorphic over `R`: a generalized point of `G ×_{U,s} R` is a loop `u` at the source of an
arrow `a`, a generalized point of `G ×_{U,t} R` is a loop at its target, and conjugation
`u ↦ a ∘ u ∘ a⁻¹` carries the first to the second, with inverse `w ↦ a⁻¹ ∘ w ∘ a`, without
moving `a`. Since `s` and `t` are coverings, part (3) of **Stacks 06R2** identifies the largest
open locus of each base change with the inverse image of `W`, so `s⁻¹(W) = t⁻¹(W)`.

## Main definitions

* `AlgebraicGeometry.GroupoidInAlgebraicSpaces.stabilizerToObjects`: the stabilizer of
  **Stacks 0447** read as an algebraic space over the object space.
* `AlgebraicGeometry.GroupoidInAlgebraicSpaces.stabilizerProjectionOverOpen`: **Stacks 06R4**,
  the stabilizer after base change to an open subspace of the object space.

## Main results

* `AlgebraicGeometry.GroupoidInAlgebraicSpaces.isInvariantOpen_of_isGreatest_stabilizer`:
  **Stacks 06R4**, invariance of the maximal open stabilizer-property locus.

## Implementation notes

The four permitted topologies are the non-fpqc constructors of
`AlgebraicGeometry.Space.Topology`, the hypothesis `τ ≠ Topology.fpqc` being the one under
which **Stacks 06R2** is available. A covering morphism is expressed as a singleton
`τ`-covering family, indexed by `Unit`. Maximality of the locus is stated as `IsGreatest`
among the open subspaces of the object space on which the base changed stabilizer has `P`,
rather than by naming the open subspace of **Stacks 06R2**: the two agree, the open subspace
of **Stacks 06R2** being such a greatest element and a greatest element being unique, and that
is how the proof proceeds.

Conjugation is built out of the composition and the inverse of generalized arrows,
`AlgebraicGeometry.GroupoidInAlgebraicSpaces.groupoidCompose` and
`AlgebraicGeometry.GroupoidInAlgebraicSpaces.groupoidInverse`, so that both the construction
and the verification that the two conjugations are mutually inverse are computations with
morphisms of presheaves: associativity, the two inverse laws and the two unit laws for
composition of generalized arrows. Nothing is read at a test object. The resulting
isomorphism of the two base changes over the arrow space is `conjugationIso` below, which is
an auxiliary step rather than an assertion of the source and is therefore private.

A generalized point of the stabilizer is determined by its underlying arrow, since the point of
the object space it lies over is the source of that arrow; this is
`stabilizerOverBase_hom_ext` below, and it is what reduces the two round trips to the identity
of the conjugated loops.

## References

* [Stacks Project, Tag 0447](https://stacks.math.columbia.edu/tag/0447)
* [Stacks Project, Tag 043W](https://stacks.math.columbia.edu/tag/043W)
* [Stacks Project, Tag 044F](https://stacks.math.columbia.edu/tag/044F)
* [Stacks Project, Tag 06R2](https://stacks.math.columbia.edu/tag/06R2)
* [Stacks Project, Tag 06R4](https://stacks.math.columbia.edu/tag/06R4)
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits

universe u

namespace AlgebraicGeometry.GroupoidInAlgebraicSpaces

variable {C : BigFppfSite.{u}} {S : Scheme.{u}} {hS : C.Contains S}
  {B : AlgebraicSpaces C S hS}

set_option synthInstance.maxHeartbeats 400000 in
/-- Pullbacks of presheaves on the big fppf site (instance search times out without this
shortcut). -/
private instance hasPullbacks_presheaf_InvariantStabilizerLocus :
    HasPullbacks ((BigFppfOver C S hS)ᵒᵖ ⥤ Type u) := inferInstance

private instance (priority := high) hasPullback_presheaf_InvariantStabilizerLocus
    {X Y Z : (BigFppfOver C S hS)ᵒᵖ ⥤ Type u} (f : X ⟶ Z) (g : Y ⟶ Z) :
    HasLimit (cospan f g) :=
  HasLimitsOfShape.has_limit _

/-! ### Units, inverses and precomposition for composition of generalized arrows -/

section Composition

variable (G : GroupoidInAlgebraicSpaces C S hS B)
  {T T' : (BigFppfOver C S hS)ᵒᵖ ⥤ Type u}

/-- The inverse of a generalized arrow has the target of that arrow as its source. -/
private theorem comp_groupoidInverse_source (a : T ⟶ G.arrows.obj) :
    (a ≫ groupoidInverse G) ≫ G.source.hom = a ≫ G.target.hom := by
  rw [Category.assoc, groupoidInverse_source]

/-- The inverse of a generalized arrow has the source of that arrow as its target. -/
private theorem comp_groupoidInverse_target (a : T ⟶ G.arrows.obj) :
    (a ≫ groupoidInverse G) ≫ G.target.hom = a ≫ G.source.hom := by
  rw [Category.assoc, groupoidInverse_target]

/-- Composing a generalized arrow on the right with any morphism equal to the identity at its
source returns the arrow. -/
private theorem groupoidCompose_eq_self_right (x y : T ⟶ G.arrows.obj)
    (w : x ≫ G.source.hom = y ≫ G.target.hom) (hy : y = identityAfterSource G x) :
    groupoidCompose G x y w = x :=
  (groupoidCompose_congr G w (identityAfterSource_composable G x) rfl hy).trans
    (groupoidCompose_rightIdentity G x)

/-- Composing a generalized arrow on the left with any morphism equal to the identity at its
target returns the arrow. -/
private theorem groupoidCompose_eq_self_left (x y : T ⟶ G.arrows.obj)
    (w : y ≫ G.source.hom = x ≫ G.target.hom) (hy : y = identityAfterTarget G x) :
    groupoidCompose G y x w = x :=
  (groupoidCompose_congr G w (identityAfterTarget_composable G x) hy rfl).trans
    (groupoidCompose_leftIdentity G x)

/-- Precomposition distributes over composition of generalized arrows, for any pair of arrows
equal to the precomposites. -/
private theorem groupoidCompose_pre_eq (k : T' ⟶ T) (f g : T ⟶ G.arrows.obj)
    (w : f ≫ G.source.hom = g ≫ G.target.hom) (f' g' : T' ⟶ G.arrows.obj)
    (w' : f' ≫ G.source.hom = g' ≫ G.target.hom) (hf : f' = k ≫ f) (hg : g' = k ≫ g) :
    k ≫ groupoidCompose G f g w = groupoidCompose G f' g' w' :=
  (groupoidCompose_pre G k f g w).trans (groupoidCompose_congr G _ w' hf.symm hg.symm)

end Composition

/-! ### Conjugating a loop by an arrow -/

section Conjugation

variable (G : GroupoidInAlgebraicSpaces C S hS B)
  {T T' : (BigFppfOver C S hS)ᵒᵖ ⥤ Type u}

/-- The conjugate `a ∘ u ∘ a⁻¹` of a loop `u` at the source of `a`; it is a loop at the target
of `a`. -/
private noncomputable def conjugateLoop (u a : T ⟶ G.arrows.obj)
    (hu : u ≫ G.source.hom = a ≫ G.source.hom)
    (hu' : u ≫ G.target.hom = a ≫ G.source.hom) : T ⟶ G.arrows.obj :=
  groupoidCompose G a
    (groupoidCompose G u (a ≫ groupoidInverse G) (by
      rw [comp_groupoidInverse_target, hu]))
    (by rw [groupoidCompose_target]; exact hu'.symm)

/-- The conjugate `a⁻¹ ∘ u ∘ a` of a loop `u` at the target of `a`; it is a loop at the source
of `a`. -/
private noncomputable def conjugateLoopInv (u a : T ⟶ G.arrows.obj)
    (hu : u ≫ G.source.hom = a ≫ G.target.hom)
    (hu' : u ≫ G.target.hom = a ≫ G.target.hom) : T ⟶ G.arrows.obj :=
  groupoidCompose G (a ≫ groupoidInverse G) (groupoidCompose G u a hu) (by
    rw [comp_groupoidInverse_source, groupoidCompose_target, hu'])

variable (u a : T ⟶ G.arrows.obj)

/-- The conjugate of a loop at the source of `a` has the target of `a` as its source. -/
private theorem conjugateLoop_source (hu : u ≫ G.source.hom = a ≫ G.source.hom)
    (hu' : u ≫ G.target.hom = a ≫ G.source.hom) :
    conjugateLoop G u a hu hu' ≫ G.source.hom = a ≫ G.target.hom := by
  unfold conjugateLoop
  rw [groupoidCompose_source, groupoidCompose_source, comp_groupoidInverse_source]

/-- The conjugate of a loop at the source of `a` has the target of `a` as its target. -/
private theorem conjugateLoop_target (hu : u ≫ G.source.hom = a ≫ G.source.hom)
    (hu' : u ≫ G.target.hom = a ≫ G.source.hom) :
    conjugateLoop G u a hu hu' ≫ G.target.hom = a ≫ G.target.hom := by
  unfold conjugateLoop
  rw [groupoidCompose_target]

/-- The conjugate of a loop at the target of `a` has the source of `a` as its source. -/
private theorem conjugateLoopInv_source (hu : u ≫ G.source.hom = a ≫ G.target.hom)
    (hu' : u ≫ G.target.hom = a ≫ G.target.hom) :
    conjugateLoopInv G u a hu hu' ≫ G.source.hom = a ≫ G.source.hom := by
  unfold conjugateLoopInv
  rw [groupoidCompose_source, groupoidCompose_source]

/-- The conjugate of a loop at the target of `a` has the source of `a` as its target. -/
private theorem conjugateLoopInv_target (hu : u ≫ G.source.hom = a ≫ G.target.hom)
    (hu' : u ≫ G.target.hom = a ≫ G.target.hom) :
    conjugateLoopInv G u a hu hu' ≫ G.target.hom = a ≫ G.source.hom := by
  unfold conjugateLoopInv
  rw [groupoidCompose_target, comp_groupoidInverse_target]

/-- Conjugation depends only on the loop and the arrow, not on the witnesses that they fit
together. -/
private theorem conjugateLoop_congr (u' a' : T ⟶ G.arrows.obj)
    (hu : u ≫ G.source.hom = a ≫ G.source.hom)
    (hu' : u ≫ G.target.hom = a ≫ G.source.hom)
    (hv : u' ≫ G.source.hom = a' ≫ G.source.hom)
    (hv' : u' ≫ G.target.hom = a' ≫ G.source.hom)
    (hU : u = u') (hA : a = a') :
    conjugateLoop G u a hu hu' = conjugateLoop G u' a' hv hv' := by
  cases hU; cases hA; rfl

/-- Conjugation by the inverse depends only on the loop and the arrow. -/
private theorem conjugateLoopInv_congr (u' a' : T ⟶ G.arrows.obj)
    (hu : u ≫ G.source.hom = a ≫ G.target.hom)
    (hu' : u ≫ G.target.hom = a ≫ G.target.hom)
    (hv : u' ≫ G.source.hom = a' ≫ G.target.hom)
    (hv' : u' ≫ G.target.hom = a' ≫ G.target.hom)
    (hU : u = u') (hA : a = a') :
    conjugateLoopInv G u a hu hu' = conjugateLoopInv G u' a' hv hv' := by
  cases hU; cases hA; rfl

/-- Conjugation commutes with precomposition. -/
private theorem comp_conjugateLoop (k : T' ⟶ T)
    (hu : u ≫ G.source.hom = a ≫ G.source.hom)
    (hu' : u ≫ G.target.hom = a ≫ G.source.hom)
    (hv : (k ≫ u) ≫ G.source.hom = (k ≫ a) ≫ G.source.hom)
    (hv' : (k ≫ u) ≫ G.target.hom = (k ≫ a) ≫ G.source.hom) :
    k ≫ conjugateLoop G u a hu hu' = conjugateLoop G (k ≫ u) (k ≫ a) hv hv' := by
  unfold conjugateLoop
  refine groupoidCompose_pre_eq G k a _ _ _ _ _ rfl ?_
  exact (groupoidCompose_pre_eq G k u (a ≫ groupoidInverse G) _ (k ≫ u)
    ((k ≫ a) ≫ groupoidInverse G) _ rfl (Category.assoc _ _ _)).symm

/-- Conjugation by the inverse commutes with precomposition. -/
private theorem comp_conjugateLoopInv (k : T' ⟶ T)
    (hu : u ≫ G.source.hom = a ≫ G.target.hom)
    (hu' : u ≫ G.target.hom = a ≫ G.target.hom)
    (hv : (k ≫ u) ≫ G.source.hom = (k ≫ a) ≫ G.target.hom)
    (hv' : (k ≫ u) ≫ G.target.hom = (k ≫ a) ≫ G.target.hom) :
    k ≫ conjugateLoopInv G u a hu hu' = conjugateLoopInv G (k ≫ u) (k ≫ a) hv hv' := by
  unfold conjugateLoopInv
  refine groupoidCompose_pre_eq G k (a ≫ groupoidInverse G) _ _ _ _ _
    (Category.assoc _ _ _) ?_
  exact (groupoidCompose_pre_eq G k u a hu (k ≫ u) (k ≫ a) hv rfl rfl).symm

/-- Conjugating a loop at the source of `a` by `a` and then conjugating back by `a` returns
the loop: associativity, the inverse law `a⁻¹ ∘ a = 1` and the two unit laws. -/
private theorem conjugateLoopInv_conjugateLoop
    (hu : u ≫ G.source.hom = a ≫ G.source.hom)
    (hu' : u ≫ G.target.hom = a ≫ G.source.hom) :
    conjugateLoopInv G (conjugateLoop G u a hu hu') a
        (conjugateLoop_source G u a hu hu') (conjugateLoop_target G u a hu hu') = u := by
  have hias : (a ≫ groupoidInverse G) ≫ G.source.hom = a ≫ G.target.hom :=
    comp_groupoidInverse_source G a
  have hiat : (a ≫ groupoidInverse G) ≫ G.target.hom = a ≫ G.source.hom :=
    comp_groupoidInverse_target G a
  have wX : u ≫ G.source.hom = (a ≫ groupoidInverse G) ≫ G.target.hom := by rw [hiat, hu]
  have hXs : groupoidCompose G u (a ≫ groupoidInverse G) wX ≫ G.source.hom =
      a ≫ G.target.hom := by rw [groupoidCompose_source, hias]
  have hXt : groupoidCompose G u (a ≫ groupoidInverse G) wX ≫ G.target.hom =
      a ≫ G.source.hom := by rw [groupoidCompose_target]; exact hu'
  have wIA : u ≫ G.source.hom =
      groupoidCompose G (a ≫ groupoidInverse G) a hias ≫ G.target.hom := by
    rw [groupoidCompose_target, hiat]; exact hu
  -- `(u ∘ a⁻¹) ∘ a = u`
  have hXa : groupoidCompose G (groupoidCompose G u (a ≫ groupoidInverse G) wX) a hXs = u :=
    (groupoidCompose_assoc G u (a ≫ groupoidInverse G) a wX hias hXs wIA).trans
      (groupoidCompose_eq_self_right G u _ wIA
        ((groupoidCompose_inverseRight G a).trans (by
          simp only [identityAfterSource, ← Category.assoc, hu])))
  have wAu : a ≫ G.source.hom = u ≫ G.target.hom := hu'.symm
  have hYt : groupoidCompose G a (groupoidCompose G u (a ≫ groupoidInverse G) wX) hXt.symm ≫
      G.target.hom = a ≫ G.target.hom := by rw [groupoidCompose_target]
  have wZ : groupoidCompose G a (groupoidCompose G u (a ≫ groupoidInverse G) wX) hXt.symm ≫
      G.source.hom = a ≫ G.target.hom := by rw [groupoidCompose_source]; exact hXs
  have wXa : a ≫ G.source.hom =
      groupoidCompose G (groupoidCompose G u (a ≫ groupoidInverse G) wX) a hXs ≫
        G.target.hom := by rw [hXa]; exact wAu
  -- `(a ∘ (u ∘ a⁻¹)) ∘ a = a ∘ u`
  have hZ : groupoidCompose G
      (groupoidCompose G a (groupoidCompose G u (a ≫ groupoidInverse G) wX) hXt.symm) a wZ =
      groupoidCompose G a u wAu :=
    (groupoidCompose_assoc G a (groupoidCompose G u (a ≫ groupoidInverse G) wX) a
        hXt.symm hXs wZ wXa).trans
      (groupoidCompose_congr G wXa wAu rfl hXa)
  have hAu : groupoidCompose G a u wAu ≫ G.target.hom = a ≫ G.target.hom := by
    rw [groupoidCompose_target]
  have wFinal : (a ≫ groupoidInverse G) ≫ G.source.hom =
      groupoidCompose G a u wAu ≫ G.target.hom := by rw [hias, hAu]
  have wIAu : groupoidCompose G (a ≫ groupoidInverse G) a hias ≫ G.source.hom =
      u ≫ G.target.hom := by rw [groupoidCompose_source]; exact wAu
  have wR : (a ≫ groupoidInverse G) ≫ G.source.hom =
      groupoidCompose G (groupoidCompose G a
        (groupoidCompose G u (a ≫ groupoidInverse G) wX) hXt.symm) a wZ ≫ G.target.hom := by
    rw [hias, groupoidCompose_target, hYt]
  -- `a⁻¹ ∘ (a ∘ u) = u`
  show groupoidCompose G (a ≫ groupoidInverse G)
    (groupoidCompose G (groupoidCompose G a
      (groupoidCompose G u (a ≫ groupoidInverse G) wX) hXt.symm) a wZ) wR = u
  refine (groupoidCompose_congr G wR wFinal rfl hZ).trans ?_
  refine (groupoidCompose_assoc G (a ≫ groupoidInverse G) a u hias wAu wIAu
    wFinal).symm.trans ?_
  exact groupoidCompose_eq_self_left G u _ wIAu
    ((groupoidCompose_inverseRight G a).trans (by
      simp only [identityAfterSource, identityAfterTarget, ← Category.assoc, hu']))

/-- Conjugating a loop at the target of `a` back by `a` and then conjugating by `a` returns
the loop. -/
private theorem conjugateLoop_conjugateLoopInv
    (hu : u ≫ G.source.hom = a ≫ G.target.hom)
    (hu' : u ≫ G.target.hom = a ≫ G.target.hom) :
    conjugateLoop G (conjugateLoopInv G u a hu hu') a
        (conjugateLoopInv_source G u a hu hu') (conjugateLoopInv_target G u a hu hu') = u := by
  have hias : (a ≫ groupoidInverse G) ≫ G.source.hom = a ≫ G.target.hom :=
    comp_groupoidInverse_source G a
  have hiat : (a ≫ groupoidInverse G) ≫ G.target.hom = a ≫ G.source.hom :=
    comp_groupoidInverse_target G a
  have hXs : groupoidCompose G u a hu ≫ G.source.hom = a ≫ G.source.hom := by
    rw [groupoidCompose_source]
  have hXt : groupoidCompose G u a hu ≫ G.target.hom = a ≫ G.target.hom := by
    rw [groupoidCompose_target]; exact hu'
  have wXi : groupoidCompose G u a hu ≫ G.source.hom =
      (a ≫ groupoidInverse G) ≫ G.target.hom := by rw [hXs, hiat]
  have wAI : u ≫ G.source.hom =
      groupoidCompose G a (a ≫ groupoidInverse G) hiat.symm ≫ G.target.hom := by
    rw [groupoidCompose_target]; exact hu
  -- `(u ∘ a) ∘ a⁻¹ = u`
  have hXi : groupoidCompose G (groupoidCompose G u a hu) (a ≫ groupoidInverse G) wXi = u :=
    (groupoidCompose_assoc G u a (a ≫ groupoidInverse G) hu hiat.symm wXi wAI).trans
      (groupoidCompose_eq_self_right G u _ wAI
        ((groupoidCompose_inverseLeft G a).trans (by
          simp only [identityAfterSource, identityAfterTarget, ← Category.assoc, hu])))
  have wIu : (a ≫ groupoidInverse G) ≫ G.source.hom = u ≫ G.target.hom := by rw [hias, hu']
  have wY : (a ≫ groupoidInverse G) ≫ G.source.hom =
      groupoidCompose G u a hu ≫ G.target.hom := by rw [hias, hXt]
  have hYt : groupoidCompose G (a ≫ groupoidInverse G) (groupoidCompose G u a hu) wY ≫
      G.target.hom = a ≫ G.source.hom := by rw [groupoidCompose_target, hiat]
  have hYs : groupoidCompose G (a ≫ groupoidInverse G) (groupoidCompose G u a hu) wY ≫
      G.source.hom = a ≫ G.source.hom := by rw [groupoidCompose_source]; exact hXs
  have wZ : groupoidCompose G (a ≫ groupoidInverse G) (groupoidCompose G u a hu) wY ≫
      G.source.hom = (a ≫ groupoidInverse G) ≫ G.target.hom := by rw [hYs, hiat]
  have wIX : (a ≫ groupoidInverse G) ≫ G.source.hom =
      groupoidCompose G (groupoidCompose G u a hu) (a ≫ groupoidInverse G) wXi ≫
        G.target.hom := by rw [hXi, hias, hu']
  -- `(a⁻¹ ∘ (u ∘ a)) ∘ a⁻¹ = a⁻¹ ∘ u`
  have hZ : groupoidCompose G
      (groupoidCompose G (a ≫ groupoidInverse G) (groupoidCompose G u a hu) wY)
        (a ≫ groupoidInverse G) wZ =
      groupoidCompose G (a ≫ groupoidInverse G) u wIu :=
    (groupoidCompose_assoc G (a ≫ groupoidInverse G) (groupoidCompose G u a hu)
        (a ≫ groupoidInverse G) wY wXi wZ wIX).trans
      (groupoidCompose_congr G wIX wIu rfl hXi)
  have hIu : groupoidCompose G (a ≫ groupoidInverse G) u wIu ≫ G.target.hom =
      a ≫ G.source.hom := by rw [groupoidCompose_target, hiat]
  have wFinal : a ≫ G.source.hom =
      groupoidCompose G (a ≫ groupoidInverse G) u wIu ≫ G.target.hom := by rw [hIu]
  have wAIu : groupoidCompose G a (a ≫ groupoidInverse G) hiat.symm ≫ G.source.hom =
      u ≫ G.target.hom := by rw [groupoidCompose_source, hias, hu']
  have wR : a ≫ G.source.hom =
      groupoidCompose G (groupoidCompose G (a ≫ groupoidInverse G)
        (groupoidCompose G u a hu) wY) (a ≫ groupoidInverse G) wZ ≫ G.target.hom := by
    rw [groupoidCompose_target, hYt]
  -- `a ∘ (a⁻¹ ∘ u) = u`
  show groupoidCompose G a
    (groupoidCompose G (groupoidCompose G (a ≫ groupoidInverse G)
      (groupoidCompose G u a hu) wY) (a ≫ groupoidInverse G) wZ) wR = u
  refine (groupoidCompose_congr G wR wFinal rfl hZ).trans ?_
  refine (groupoidCompose_assoc G a (a ≫ groupoidInverse G) u hiat.symm wIu wAIu
    wFinal).symm.trans ?_
  exact groupoidCompose_eq_self_left G u _ wAIu
    ((groupoidCompose_inverseLeft G a).trans (by
      simp only [identityAfterTarget, ← Category.assoc, hu']))

end Conjugation

/-! ### The stabilizer over the object space -/

section Stabilizer

variable (G : GroupoidInAlgebraicSpaces C S hS B)

/-- The stabilizer of a groupoid in algebraic spaces, read as an algebraic space over the
object space: the structure morphism is the second projection out of the fibre product of
`(t, s)` with the diagonal of the object space. -/
noncomputable def stabilizerToObjects : stabilizerOverBase G ⟶ G.objects :=
  ObjectProperty.homMk (stabilizer G).hom

/-- The arrow of the groupoid underlying a generalized point of the stabilizer, read on the
stabilizer as an algebraic space over the object space. -/
private noncomputable def stabilizerLoop :
    (stabilizerOverBase G).obj ⟶ G.arrows.obj :=
  stabilizerArrow G

/-- The arrow underlying a generalized point of the stabilizer has as source the point of the
object space that point lies over. -/
private theorem stabilizerLoop_source :
    stabilizerLoop G ≫ G.source.hom = (stabilizerToObjects G).hom :=
  stabilizerArrow_source G

/-- The arrow underlying a generalized point of the stabilizer has as target the point of the
object space that point lies over. -/
private theorem stabilizerLoop_target :
    stabilizerLoop G ≫ G.target.hom = (stabilizerToObjects G).hom :=
  stabilizerArrow_target G

/-- A generalized point of the stabilizer is determined by its underlying arrow: the point of
the object space it lies over is the source of that arrow. -/
private theorem stabilizerOverBase_hom_ext
    {T : (BigFppfOver C S hS)ᵒᵖ ⥤ Type u} (p q : T ⟶ (stabilizerOverBase G).obj)
    (h : p ≫ stabilizerLoop G = q ≫ stabilizerLoop G) : p = q := by
  have hb : p ≫ (stabilizerToObjects G).hom = q ≫ (stabilizerToObjects G).hom := by
    rw [← stabilizerLoop_source, ← Category.assoc, ← Category.assoc, h]
  exact pullback.hom_ext h hb

/-- A generalized arrow whose source and target both equal a given point of the object space
is a generalized point of the stabilizer. -/
private noncomputable def stabilizerLift
    {T : (BigFppfOver C S hS)ᵒᵖ ⥤ Type u} (c : T ⟶ G.arrows.obj) (v : T ⟶ G.objects.obj)
    (hs : c ≫ G.source.hom = v) (ht : c ≫ G.target.hom = v) :
    T ⟶ (stabilizerOverBase G).obj :=
  pullback.lift c v (stabilizerArrow_condition G c v hs ht)

/-- The arrow underlying the generalized point of the stabilizer built from a loop is that
loop. -/
private theorem stabilizerLift_arrow
    {T : (BigFppfOver C S hS)ᵒᵖ ⥤ Type u} (c : T ⟶ G.arrows.obj) (v : T ⟶ G.objects.obj)
    (hs : c ≫ G.source.hom = v) (ht : c ≫ G.target.hom = v) :
    stabilizerLift G c v hs ht ≫ stabilizerLoop G = c :=
  pullback.lift_fst _ _ _

/-- The generalized point of the stabilizer built from a loop lies over the base point of that
loop. -/
private theorem stabilizerLift_base
    {T : (BigFppfOver C S hS)ᵒᵖ ⥤ Type u} (c : T ⟶ G.arrows.obj) (v : T ⟶ G.objects.obj)
    (hs : c ≫ G.source.hom = v) (ht : c ≫ G.target.hom = v) :
    stabilizerLift G c v hs ht ≫ (stabilizerToObjects G).hom = v :=
  pullback.lift_snd _ _ _

/-! ### The two base changes of the stabilizer and the conjugation between them -/

/-- The stabilizer component of a generalized point of the base change along the source. -/
private noncomputable def sourceStabilizerPart :
    (AlgebraicSpaces.fiberProduct C S hS (stabilizerToObjects G) G.source).obj ⟶
      (stabilizerOverBase G).obj :=
  pullback.fst (stabilizerToObjects G).hom G.source.hom

/-- The arrow component of a generalized point of the base change along the source. -/
private noncomputable def sourceArrowPart :
    (AlgebraicSpaces.fiberProduct C S hS (stabilizerToObjects G) G.source).obj ⟶
      G.arrows.obj :=
  pullback.snd (stabilizerToObjects G).hom G.source.hom

/-- The stabilizer component of a generalized point of the base change along the target. -/
private noncomputable def targetStabilizerPart :
    (AlgebraicSpaces.fiberProduct C S hS (stabilizerToObjects G) G.target).obj ⟶
      (stabilizerOverBase G).obj :=
  pullback.fst (stabilizerToObjects G).hom G.target.hom

/-- The arrow component of a generalized point of the base change along the target. -/
private noncomputable def targetArrowPart :
    (AlgebraicSpaces.fiberProduct C S hS (stabilizerToObjects G) G.target).obj ⟶
      G.arrows.obj :=
  pullback.snd (stabilizerToObjects G).hom G.target.hom

/-- A generalized point of the base change along the source is determined by its two
components. -/
private theorem sourceBaseChange_hom_ext
    {T : (BigFppfOver C S hS)ᵒᵖ ⥤ Type u}
    (k l : T ⟶ (AlgebraicSpaces.fiberProduct C S hS (stabilizerToObjects G) G.source).obj)
    (h₀ : k ≫ sourceStabilizerPart G = l ≫ sourceStabilizerPart G)
    (h₁ : k ≫ sourceArrowPart G = l ≫ sourceArrowPart G) : k = l :=
  pullback.hom_ext h₀ h₁

/-- A generalized point of the base change along the target is determined by its two
components. -/
private theorem targetBaseChange_hom_ext
    {T : (BigFppfOver C S hS)ᵒᵖ ⥤ Type u}
    (k l : T ⟶ (AlgebraicSpaces.fiberProduct C S hS (stabilizerToObjects G) G.target).obj)
    (h₀ : k ≫ targetStabilizerPart G = l ≫ targetStabilizerPart G)
    (h₁ : k ≫ targetArrowPart G = l ≫ targetArrowPart G) : k = l :=
  pullback.hom_ext h₀ h₁

private theorem sourceLoop_source :
    (sourceStabilizerPart G ≫ stabilizerLoop G) ≫ G.source.hom =
      sourceArrowPart G ≫ G.source.hom := by
  rw [Category.assoc, stabilizerLoop_source]
  exact pullback.condition

private theorem sourceLoop_target :
    (sourceStabilizerPart G ≫ stabilizerLoop G) ≫ G.target.hom =
      sourceArrowPart G ≫ G.source.hom := by
  rw [Category.assoc, stabilizerLoop_target]
  exact pullback.condition

private theorem targetLoop_source :
    (targetStabilizerPart G ≫ stabilizerLoop G) ≫ G.source.hom =
      targetArrowPart G ≫ G.target.hom := by
  rw [Category.assoc, stabilizerLoop_source]
  exact pullback.condition

private theorem targetLoop_target :
    (targetStabilizerPart G ≫ stabilizerLoop G) ≫ G.target.hom =
      targetArrowPart G ≫ G.target.hom := by
  rw [Category.assoc, stabilizerLoop_target]
  exact pullback.condition

/-- The loop of a generalized point of the base change along the source, conjugated by its
arrow. -/
private noncomputable def sourceConjugate :
    (AlgebraicSpaces.fiberProduct C S hS (stabilizerToObjects G) G.source).obj ⟶
      G.arrows.obj :=
  conjugateLoop G (sourceStabilizerPart G ≫ stabilizerLoop G) (sourceArrowPart G)
    (sourceLoop_source G) (sourceLoop_target G)

/-- The loop of a generalized point of the base change along the target, conjugated by the
inverse of its arrow. -/
private noncomputable def targetConjugate :
    (AlgebraicSpaces.fiberProduct C S hS (stabilizerToObjects G) G.target).obj ⟶
      G.arrows.obj :=
  conjugateLoopInv G (targetStabilizerPart G ≫ stabilizerLoop G) (targetArrowPart G)
    (targetLoop_source G) (targetLoop_target G)

private theorem sourceConjugate_eq :
    sourceConjugate G =
      conjugateLoop G (sourceStabilizerPart G ≫ stabilizerLoop G) (sourceArrowPart G)
        (sourceLoop_source G) (sourceLoop_target G) := rfl

private theorem targetConjugate_eq :
    targetConjugate G =
      conjugateLoopInv G (targetStabilizerPart G ≫ stabilizerLoop G) (targetArrowPart G)
        (targetLoop_source G) (targetLoop_target G) := rfl

private theorem sourceConjugate_source :
    sourceConjugate G ≫ G.source.hom = sourceArrowPart G ≫ G.target.hom :=
  conjugateLoop_source G _ _ (sourceLoop_source G) (sourceLoop_target G)

private theorem sourceConjugate_target :
    sourceConjugate G ≫ G.target.hom = sourceArrowPart G ≫ G.target.hom :=
  conjugateLoop_target G _ _ (sourceLoop_source G) (sourceLoop_target G)

private theorem targetConjugate_source :
    targetConjugate G ≫ G.source.hom = targetArrowPart G ≫ G.source.hom :=
  conjugateLoopInv_source G _ _ (targetLoop_source G) (targetLoop_target G)

private theorem targetConjugate_target :
    targetConjugate G ≫ G.target.hom = targetArrowPart G ≫ G.source.hom :=
  conjugateLoopInv_target G _ _ (targetLoop_source G) (targetLoop_target G)

/-- Conjugation of the loop by the arrow, from the base change of the stabilizer along the
source to the base change along the target. -/
private noncomputable def conjugationSourceToTarget :
    AlgebraicSpaces.fiberProduct C S hS (stabilizerToObjects G) G.source ⟶
      AlgebraicSpaces.fiberProduct C S hS (stabilizerToObjects G) G.target :=
  ObjectProperty.homMk (pullback.lift
    (stabilizerLift G (sourceConjugate G) (sourceArrowPart G ≫ G.target.hom)
      (sourceConjugate_source G) (sourceConjugate_target G))
    (sourceArrowPart G)
    (stabilizerLift_base G (sourceConjugate G) (sourceArrowPart G ≫ G.target.hom)
      (sourceConjugate_source G) (sourceConjugate_target G)))

/-- Conjugation of the loop by the inverse of the arrow, from the base change of the stabilizer
along the target to the base change along the source. -/
private noncomputable def conjugationTargetToSource :
    AlgebraicSpaces.fiberProduct C S hS (stabilizerToObjects G) G.target ⟶
      AlgebraicSpaces.fiberProduct C S hS (stabilizerToObjects G) G.source :=
  ObjectProperty.homMk (pullback.lift
    (stabilizerLift G (targetConjugate G) (targetArrowPart G ≫ G.source.hom)
      (targetConjugate_source G) (targetConjugate_target G))
    (targetArrowPart G)
    (stabilizerLift_base G (targetConjugate G) (targetArrowPart G ≫ G.source.hom)
      (targetConjugate_source G) (targetConjugate_target G)))

private theorem conjugationSourceToTarget_arrow :
    (conjugationSourceToTarget G).hom ≫ targetArrowPart G = sourceArrowPart G :=
  pullback.lift_snd _ _ _

private theorem conjugationTargetToSource_arrow :
    (conjugationTargetToSource G).hom ≫ sourceArrowPart G = targetArrowPart G :=
  pullback.lift_snd _ _ _

private theorem conjugationSourceToTarget_stabilizer :
    (conjugationSourceToTarget G).hom ≫ targetStabilizerPart G =
      stabilizerLift G (sourceConjugate G) (sourceArrowPart G ≫ G.target.hom)
        (sourceConjugate_source G) (sourceConjugate_target G) :=
  pullback.lift_fst _ _ _

private theorem conjugationTargetToSource_stabilizer :
    (conjugationTargetToSource G).hom ≫ sourceStabilizerPart G =
      stabilizerLift G (targetConjugate G) (targetArrowPart G ≫ G.source.hom)
        (targetConjugate_source G) (targetConjugate_target G) :=
  pullback.lift_fst _ _ _

private theorem conjugationSourceToTarget_loop :
    (conjugationSourceToTarget G).hom ≫ (targetStabilizerPart G ≫ stabilizerLoop G) =
      sourceConjugate G := by
  rw [← Category.assoc, conjugationSourceToTarget_stabilizer]
  exact stabilizerLift_arrow G _ _ _ _

private theorem conjugationTargetToSource_loop :
    (conjugationTargetToSource G).hom ≫ (sourceStabilizerPart G ≫ stabilizerLoop G) =
      targetConjugate G := by
  rw [← Category.assoc, conjugationTargetToSource_stabilizer]
  exact stabilizerLift_arrow G _ _ _ _

private theorem conjugation_hom_inv_id :
    conjugationSourceToTarget G ≫ conjugationTargetToSource G =
      𝟙 (AlgebraicSpaces.fiberProduct C S hS (stabilizerToObjects G) G.source) := by
  have hloop := conjugationSourceToTarget_loop G
  have harrow := conjugationSourceToTarget_arrow G
  have hv : ((conjugationSourceToTarget G).hom ≫
        (targetStabilizerPart G ≫ stabilizerLoop G)) ≫ G.source.hom =
      ((conjugationSourceToTarget G).hom ≫ targetArrowPart G) ≫ G.target.hom := by
    rw [hloop, harrow, sourceConjugate_source]
  have hv' : ((conjugationSourceToTarget G).hom ≫
        (targetStabilizerPart G ≫ stabilizerLoop G)) ≫ G.target.hom =
      ((conjugationSourceToTarget G).hom ≫ targetArrowPart G) ≫ G.target.hom := by
    rw [hloop, harrow, sourceConjugate_target]
  refine ObjectProperty.hom_ext _ ?_
  show (conjugationSourceToTarget G).hom ≫ (conjugationTargetToSource G).hom =
    𝟙 (AlgebraicSpaces.fiberProduct C S hS (stabilizerToObjects G) G.source).obj
  refine sourceBaseChange_hom_ext G _ _ ?_ ?_
  · refine stabilizerOverBase_hom_ext G _ _ ?_
    simp only [Category.assoc, Category.id_comp]
    rw [conjugationTargetToSource_loop, targetConjugate_eq,
      comp_conjugateLoopInv G _ _ (conjugationSourceToTarget G).hom
        (targetLoop_source G) (targetLoop_target G) hv hv',
      conjugateLoopInv_congr G _ _
        (conjugateLoop G (sourceStabilizerPart G ≫ stabilizerLoop G) (sourceArrowPart G)
          (sourceLoop_source G) (sourceLoop_target G))
        (sourceArrowPart G) _ _
        (conjugateLoop_source G _ _ (sourceLoop_source G) (sourceLoop_target G))
        (conjugateLoop_target G _ _ (sourceLoop_source G) (sourceLoop_target G))
        (hloop.trans (sourceConjugate_eq G)) harrow]
    exact conjugateLoopInv_conjugateLoop G _ _ (sourceLoop_source G) (sourceLoop_target G)
  · simp only [Category.assoc, Category.id_comp]
    rw [conjugationTargetToSource_arrow, harrow]

private theorem conjugation_inv_hom_id :
    conjugationTargetToSource G ≫ conjugationSourceToTarget G =
      𝟙 (AlgebraicSpaces.fiberProduct C S hS (stabilizerToObjects G) G.target) := by
  have hloop := conjugationTargetToSource_loop G
  have harrow := conjugationTargetToSource_arrow G
  have hv : ((conjugationTargetToSource G).hom ≫
        (sourceStabilizerPart G ≫ stabilizerLoop G)) ≫ G.source.hom =
      ((conjugationTargetToSource G).hom ≫ sourceArrowPart G) ≫ G.source.hom := by
    rw [hloop, harrow, targetConjugate_source]
  have hv' : ((conjugationTargetToSource G).hom ≫
        (sourceStabilizerPart G ≫ stabilizerLoop G)) ≫ G.target.hom =
      ((conjugationTargetToSource G).hom ≫ sourceArrowPart G) ≫ G.source.hom := by
    rw [hloop, harrow, targetConjugate_target]
  refine ObjectProperty.hom_ext _ ?_
  show (conjugationTargetToSource G).hom ≫ (conjugationSourceToTarget G).hom =
    𝟙 (AlgebraicSpaces.fiberProduct C S hS (stabilizerToObjects G) G.target).obj
  refine targetBaseChange_hom_ext G _ _ ?_ ?_
  · refine stabilizerOverBase_hom_ext G _ _ ?_
    simp only [Category.assoc, Category.id_comp]
    rw [conjugationSourceToTarget_loop, sourceConjugate_eq,
      comp_conjugateLoop G _ _ (conjugationTargetToSource G).hom
        (sourceLoop_source G) (sourceLoop_target G) hv hv',
      conjugateLoop_congr G _ _
        (conjugateLoopInv G (targetStabilizerPart G ≫ stabilizerLoop G) (targetArrowPart G)
          (targetLoop_source G) (targetLoop_target G))
        (targetArrowPart G) _ _
        (conjugateLoopInv_source G _ _ (targetLoop_source G) (targetLoop_target G))
        (conjugateLoopInv_target G _ _ (targetLoop_source G) (targetLoop_target G))
        (hloop.trans (targetConjugate_eq G)) harrow]
    exact conjugateLoop_conjugateLoopInv G _ _ (targetLoop_source G) (targetLoop_target G)
  · simp only [Category.assoc, Category.id_comp]
    rw [conjugationSourceToTarget_arrow, harrow]

/-- Conjugation is an isomorphism between the base change of the stabilizer along the source
and its base change along the target. -/
private noncomputable def conjugationIso :
    AlgebraicSpaces.fiberProduct C S hS (stabilizerToObjects G) G.source ≅
      AlgebraicSpaces.fiberProduct C S hS (stabilizerToObjects G) G.target where
  hom := conjugationSourceToTarget G
  inv := conjugationTargetToSource G
  hom_inv_id := conjugation_hom_inv_id G
  inv_hom_id := conjugation_inv_hom_id G

/-- The conjugation isomorphism does not move the arrow component, so it is an isomorphism over
the arrow space. -/
private theorem conjugationIso_inv_fiberProductSnd :
    (conjugationIso G).inv ≫ fiberProductSnd (stabilizerToObjects G) G.source =
      fiberProductSnd (stabilizerToObjects G) G.target := by
  refine ObjectProperty.hom_ext _ ?_
  show (conjugationTargetToSource G).hom ≫ sourceArrowPart G = targetArrowPart G
  exact conjugationTargetToSource_arrow G

end Stabilizer

/-! ### Stacks 06R4 -/

section Invariance

variable (G : GroupoidInAlgebraicSpaces C S hS B)

/-- **Stacks 06R4.** The restriction of the stabilizer of a groupoid in algebraic spaces over
an open subspace of the object space. -/
@[stacks 06R4 "the stabilizer restricted over an open subspace of the object space"]
noncomputable def stabilizerProjectionOverOpen
    (W : {W : Subfunctor G.objects.obj // Space.IsOpenSubspace C S hS W}) :
    AlgebraicSpaces.fiberProduct C S hS (stabilizerToObjects G)
        (Space.openInclusion C S hS W) ⟶ Space.openObject C S hS W :=
  fiberProductSnd (stabilizerToObjects G) (Space.openInclusion C S hS W)

/-- A property respecting isomorphisms holds for the second leg of a cartesian square exactly
when it holds for the second projection of the chosen fibre product. -/
private theorem property_iff_of_isPullback (P : MorphismProperty (AlgebraicSpaces C S hS))
    [P.RespectsIso] {A X Y Z : AlgebraicSpaces C S hS} {p : A ⟶ X} {q : A ⟶ Y}
    {f : X ⟶ Z} {g : Y ⟶ Z} (sq : IsPullback p q f g) : P q ↔ P (pullback.snd f g) := by
  rw [← sq.isoPullback_hom_snd]
  exact P.cancel_left_of_respectsIso _ _

/-- The restriction of the stabilizer over an open subspace has `P` exactly when the open
subspace belongs to the locus considered in **Stacks 06R2** for the stabilizer. -/
private theorem hasPropertyOnOpen_iff_stabilizerProjectionOverOpen
    (P : MorphismProperty (AlgebraicSpaces C S hS)) [P.RespectsIso]
    (W : {W : Subfunctor G.objects.obj // Space.IsOpenSubspace C S hS W}) :
    Space.HasPropertyOnOpen C S hS P (stabilizerToObjects G) W ↔
      P (stabilizerProjectionOverOpen G W) :=
  (property_iff_of_isPullback P (AlgebraicSpaces.isPullback_fiberProduct C S hS
    (stabilizerToObjects G) (Space.openInclusion C S hS W))).symm

/-- **Stacks 06R4.** Let `G` be a groupoid in algebraic spaces whose source and target
morphisms are both coverings for a topology `τ` other than the fpqc topology, and let `P` be a
property of morphisms of algebraic spaces local on the target for `τ`. A greatest open
subspace of the object space over which the restriction of the stabilizer has `P` is invariant
under `G`. -/
@[stacks 06R4 "invariance of the maximal open stabilizer-property locus"]
theorem isInvariantOpen_of_isGreatest_stabilizer (τ : Space.Topology) (hτ : τ ≠ .fpqc)
    (P : MorphismProperty (AlgebraicSpaces C S hS))
    [P.IsLocalAtTarget (Space.Topology.precoverage.{u, u + 1} τ C S hS)]
    (hs : τ.IsCovering C S hS (fun _ : Unit => G.arrows.obj) (fun _ => G.source.hom))
    (ht : τ.IsCovering C S hS (fun _ : Unit => G.arrows.obj) (fun _ => G.target.hom))
    (W : {W : Subfunctor G.objects.obj // Space.IsOpenSubspace C S hS W})
    (hW : IsGreatest {V : {V : Subfunctor G.objects.obj // Space.IsOpenSubspace C S hS V} |
      P (stabilizerProjectionOverOpen G V)} W) :
    IsInvariantOpen G W.1 := by
  -- `W` is the largest open locus of Stacks 06R2 for the stabilizer.
  have hWeq : W.1 =
      (Space.largestOpenSubspace C S hS τ hτ P (stabilizerToObjects G)).1.1 :=
    le_antisymm
      ((Space.largestOpenSubspace C S hS τ hτ P (stabilizerToObjects G)).2.2 W
        ((hasPropertyOnOpen_iff_stabilizerProjectionOverOpen G P W).mpr hW.1))
      (hW.2 ((hasPropertyOnOpen_iff_stabilizerProjectionOverOpen G P
        (Space.largestOpenSubspace C S hS τ hτ P (stabilizerToObjects G)).1).mp
          (Space.largestOpenSubspace C S hS τ hτ P (stabilizerToObjects G)).2.1))
  -- The two base changes of the stabilizer are isomorphic over the arrow space, so the two
  -- inverse images of the locus agree.
  have hpre :
      (Space.largestOpenSubspace C S hS τ hτ P (stabilizerToObjects G)).1.1.preimage
          G.target.hom =
        (Space.largestOpenSubspace C S hS τ hτ P (stabilizerToObjects G)).1.1.preimage
          G.source.hom := by
    rw [← Space.largestOpenSubspace_covering C S hS τ hτ P (stabilizerToObjects G)
        (fun _ : Unit => G.arrows) (fun _ => G.target) ht (),
      ← Space.largestOpenSubspace_covering C S hS τ hτ P (stabilizerToObjects G)
        (fun _ : Unit => G.arrows) (fun _ => G.source) hs ()]
    have key : ∀ {Y : AlgebraicSpaces C S hS} (g : Y ⟶ G.objects),
        (Space.largestOpenSubspace C S hS τ hτ P
          (fiberProductSnd (stabilizerToObjects G) g)).1.1 =
        (Space.largestOpenSubspace C S hS τ hτ P
          (pullback.snd (stabilizerToObjects G) g)).1.1 := fun g =>
      largestOpenSubspace_eq_of_isoOver τ hτ P _ _
        (AlgebraicSpaces.isPullback_fiberProduct C S hS (stabilizerToObjects G) g).isoPullback
        (AlgebraicSpaces.isPullback_fiberProduct C S hS
          (stabilizerToObjects G) g).isoPullback_hom_snd
    exact ((key G.target).symm.trans
      (largestOpenSubspace_eq_of_isoOver τ hτ P _ _ (conjugationIso G).symm
        (conjugationIso_inv_fiberProductSnd G))).trans (key G.source)
  exact ⟨W.2, by rw [hWeq]; exact le_of_eq hpre.symm⟩

end Invariance

end AlgebraicGeometry.GroupoidInAlgebraicSpaces

end
