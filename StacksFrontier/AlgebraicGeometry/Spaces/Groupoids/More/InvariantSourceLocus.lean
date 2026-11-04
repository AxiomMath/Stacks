module

public import StacksCore.Tactic.StacksAttribute
public import StacksFrontier.AlgebraicGeometry.Spaces.Groupoids.GroupoidInSpacesOfComposable
public import StacksFrontier.AlgebraicGeometry.Spaces.Groupoids.Stabilizer.InvariantSubspace
public import StacksFrontier.AlgebraicGeometry.Spaces.LargestOpenLocus

/-!
# Invariance of the locus where the source of a groupoid has a target-local property

Let `(U, R, s, t, c)` be a groupoid in algebraic spaces over an algebraic space `B` over a
scheme `S`, let `τ` be one of the fppf, syntomic, smooth and étale topologies of
**Stacks 03YH**, and let `P` be a property of morphisms of algebraic spaces which is local on
the target for `τ`. If both `s` and `t` are `τ`-coverings, then the largest open subspace
`W ⊆ U` over which the restriction of `s` has `P`, the open subspace of **Stacks 06R2**, is
invariant under the groupoid.

The reason is that the two base changes of `s` along `s` and along `t` are the same morphism
up to an isomorphism of its source. Indeed `R ×_{s,U,t} R` is cartesian over `s` both along
`t`, by the defining square of the fibre product, and along `s`, by the lower right square of
**Stacks 043Z**, whose other leg is the composition law. Since `s` and `t` are coverings, part
(3) of **Stacks 06R2** identifies the largest open locus of each base change with the inverse
image of `W`, so `t⁻¹(W) = s⁻¹(W)` and in particular `s⁻¹(W) ≤ t⁻¹(W)`.

## Main results

* `AlgebraicGeometry.Space.pullback_snd_iff_of_isoOver`: restricting over a fixed morphism is
  insensitive to replacing a morphism by an isomorphic one over the common target.
* `AlgebraicGeometry.GroupoidInAlgebraicSpaces.largestOpenSubspace_eq_of_isoOver`: hence the
  largest open locus of **Stacks 06R2** is insensitive to the same replacement.
* `AlgebraicGeometry.GroupoidInAlgebraicSpaces.isInvariantOpen_largestOpenSubspace_source`:
  **Stacks 044Z**, invariance of the largest open locus of the source morphism.

## Implementation notes

The four permitted topologies are the non-fpqc constructors of
`AlgebraicGeometry.Space.Topology`, the hypothesis `τ ≠ Topology.fpqc` being the one under
which **Stacks 06R2** is available: a flat morphism need not be open. A covering morphism is
expressed as a singleton `τ`-covering family, indexed by `Unit`.

The invariance condition of **Stacks 044F** asks only for the inclusion
`s⁻¹(W) ≤ t⁻¹(W)`, and what is proved here is the equality of the two inverse images; the
inclusion is extracted from it.

## References

* [Stacks Project, Tag 03YH](https://stacks.math.columbia.edu/tag/03YH)
* [Stacks Project, Tag 043Z](https://stacks.math.columbia.edu/tag/043Z)
* [Stacks Project, Tag 044F](https://stacks.math.columbia.edu/tag/044F)
* [Stacks Project, Tag 044Z](https://stacks.math.columbia.edu/tag/044Z)
* [Stacks Project, Tag 06R2](https://stacks.math.columbia.edu/tag/06R2)
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits

universe u

namespace AlgebraicGeometry.Space

variable (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)

/-- Restricting two morphisms with a common target along a third morphism into that target
gives the same property, provided the two differ by an isomorphism of their sources: the
induced morphism of fibre products is then an isomorphism over the restriction. -/
theorem pullback_snd_iff_of_isoOver (P : MorphismProperty (AlgebraicSpaces B S hS))
    [P.RespectsIso] {X X' Y A : AlgebraicSpaces B S hS} (f : X ⟶ Y) (f' : X' ⟶ Y) (e : X ≅ X')
    (he : e.hom ≫ f' = f) (i : A ⟶ Y) :
    P (pullback.snd f i) ↔ P (pullback.snd f' i) := by
  let m := pullback.map f i f' i e.hom (𝟙 A) (𝟙 Y) (by simpa using he.symm) (by simp)
  have hm : m ≫ pullback.snd f' i = pullback.snd f i := by simp [m]
  rw [← hm]
  exact P.cancel_left_of_respectsIso m _

end AlgebraicGeometry.Space

namespace AlgebraicGeometry.GroupoidInAlgebraicSpaces

variable {C : BigFppfSite.{u}} {S : Scheme.{u}} {hS : C.Contains S}
  {B : AlgebraicSpaces C S hS}

/-- The largest open locus of a target-local property depends on the morphism only up to an
isomorphism of its source over the target: the two loci are open subspaces over which both
restrictions have the property, so each is contained in the other. -/
theorem largestOpenSubspace_eq_of_isoOver (τ : Space.Topology) (hτ : τ ≠ .fpqc)
    (P : MorphismProperty (AlgebraicSpaces C S hS))
    [P.IsLocalAtTarget (Space.Topology.precoverage.{u, u + 1} τ C S hS)]
    {X X' Y : AlgebraicSpaces C S hS} (f : X ⟶ Y) (f' : X' ⟶ Y) (e : X ≅ X')
    (he : e.hom ≫ f' = f) :
    (Space.largestOpenSubspace C S hS τ hτ P f).1.1 =
      (Space.largestOpenSubspace C S hS τ hτ P f').1.1 := by
  have hprop (V : {V : Subfunctor Y.obj // Space.IsOpenSubspace C S hS V}) :
      Space.HasPropertyOnOpen C S hS P f V ↔ Space.HasPropertyOnOpen C S hS P f' V :=
    Space.pullback_snd_iff_of_isoOver C S hS P f f' e he (Space.openInclusion C S hS V)
  exact le_antisymm
    ((Space.largestOpenSubspace C S hS τ hτ P f').2.2 _
      ((hprop _).mp (Space.largestOpenSubspace C S hS τ hτ P f).2.1))
    ((Space.largestOpenSubspace C S hS τ hτ P f).2.2 _
      ((hprop _).mpr (Space.largestOpenSubspace C S hS τ hτ P f').2.1))

/-- **Stacks 044Z.** Let `G` be a groupoid in algebraic spaces whose source and target
morphisms are both coverings for a topology `τ` other than the fpqc topology, and let `P` be a
property of morphisms of algebraic spaces local on the target for `τ`. The largest open
subspace of the object space over which the restriction of the source morphism has `P` is
invariant under `G`. -/
@[stacks 044Z]
theorem isInvariantOpen_largestOpenSubspace_source (G : GroupoidInAlgebraicSpaces C S hS B)
    (τ : Space.Topology) (hτ : τ ≠ .fpqc) (P : MorphismProperty (AlgebraicSpaces C S hS))
    [P.IsLocalAtTarget (Space.Topology.precoverage.{u, u + 1} τ C S hS)]
    (hs : τ.IsCovering C S hS (fun _ : Unit => G.arrows.obj) (fun _ => G.source.hom))
    (ht : τ.IsCovering C S hS (fun _ : Unit => G.arrows.obj) (fun _ => G.target.hom)) :
    IsInvariantOpen G (Space.largestOpenSubspace C S hS τ hτ P G.source).1.1 := by
  have hpre :
      (Space.largestOpenSubspace C S hS τ hτ P G.source).1.1.preimage G.target.hom =
        (Space.largestOpenSubspace C S hS τ hτ P G.source).1.1.preimage G.source.hom := by
    rw [← Space.largestOpenSubspace_covering C S hS τ hτ P G.source
        (fun _ : Unit => G.arrows) (fun _ => G.target) ht (),
      ← Space.largestOpenSubspace_covering C S hS τ hτ P G.source
        (fun _ : Unit => G.arrows) (fun _ => G.source) hs ()]
    exact (largestOpenSubspace_eq_of_isoOver τ hτ P _ _
          (AlgebraicSpaces.isPullback_fiberProduct C S hS G.source G.target).isoPullback.symm
          (AlgebraicSpaces.isPullback_fiberProduct C S hS
            G.source G.target).isoPullback_inv_snd).trans
      (largestOpenSubspace_eq_of_isoOver τ hτ P _ _
        (Space.isPullback_comp_source G).isoPullback.symm
        (Space.isPullback_comp_source G).isoPullback_inv_snd).symm
  exact ⟨(Space.largestOpenSubspace C S hS τ hτ P G.source).1.2, hpre.ge⟩

end AlgebraicGeometry.GroupoidInAlgebraicSpaces

end
