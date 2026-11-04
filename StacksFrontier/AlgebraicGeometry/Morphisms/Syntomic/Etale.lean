module

public import Mathlib.AlgebraicGeometry.Sites.Etale
public import StacksFrontier.AlgebraicGeometry.Morphisms.Etale.Defs
public import StacksFrontier.AlgebraicGeometry.Morphisms.Syntomic.Defs
public import StacksFrontier.AlgebraicGeometry.Morphisms.Syntomic.Properties
public import StacksFrontier.RingTheory.Smooth.Syntomic

/-!
# Étale morphisms are syntomic

Every étale morphism of schemes is syntomic, and therefore flat and locally of finite
presentation.

## Main results

* `AlgebraicGeometry.syntomicAt_of_etaleAt` states that a morphism of schemes which is étale at
  a point is syntomic at that point.
* `AlgebraicGeometry.syntomic_of_etale` states that an étale morphism of schemes is syntomic.
* `AlgebraicGeometry.locallyOfFinitePresentation_of_etale` states that an étale morphism of
  schemes is locally of finite presentation.
* `AlgebraicGeometry.flat_of_etale` states that an étale morphism of schemes is flat.
* `AlgebraicGeometry.Scheme.etalePrecoverage_le_syntomicPrecoverage` states that every étale
  covering family is a syntomic covering family.

## Implementation notes

Both notions are affine-local on the source and the target, so the proof reduces to the
ring-theoretic statement that an étale algebra is syntomic. That in turn follows because an
étale algebra is smooth and a smooth algebra is syntomic. Flatness and local finite
presentation are then inherited from the corresponding properties of syntomic morphisms.

## References

* [Stacks Project, Tag 02GQ](https://stacks.math.columbia.edu/tag/02GQ)
* [Stacks Project, Tag 02GR](https://stacks.math.columbia.edu/tag/02GR)
* [Stacks Project, Tag 02GS](https://stacks.math.columbia.edu/tag/02GS)
-/

@[expose] public section

open CategoryTheory

universe u

namespace AlgebraicGeometry

/-- A morphism of schemes which is étale at a point is syntomic at that point. -/
lemma syntomicAt_of_etaleAt {X S : Scheme.{u}} (f : X ⟶ S) (x : X) (h : EtaleAt f x) :
    SyntomicAt f x := by
  obtain ⟨U, hU, hx, V, hV, hUV, hEtale⟩ := h
  refine ⟨⟨U, hU⟩, hx, ⟨V, hV⟩, hUV, ?_⟩
  let : Algebra Γ(S, V) Γ(X, U) := (f.appLE V U hUV).hom.toAlgebra
  have : Algebra.Etale Γ(S, V) Γ(X, U) := hEtale
  exact Algebra.Smooth.syntomic _ _

/-- An étale morphism of schemes is syntomic. -/
@[stacks 02GQ]
lemma syntomic_of_etale {X S : Scheme.{u}} (f : X ⟶ S) [Etale f] : Syntomic f := fun x =>
  syntomicAt_of_etaleAt f x ((etale_iff_forall_etaleAt f).mp inferInstance x)

/-- An étale morphism of schemes is locally of finite presentation. -/
@[stacks 02GR]
lemma locallyOfFinitePresentation_of_etale {X S : Scheme.{u}} (f : X ⟶ S) [Etale f] :
    LocallyOfFinitePresentation f :=
  locallyOfFinitePresentation (syntomic_of_etale f)

/-- An étale morphism of schemes is flat. -/
@[stacks 02GS]
lemma flat_of_etale {X S : Scheme.{u}} (f : X ⟶ S) [Etale f] : Flat f :=
  flat (syntomic_of_etale f)

/-- Every étale covering family is a syntomic covering family, an étale morphism of schemes being
syntomic. -/
theorem Scheme.etalePrecoverage_le_syntomicPrecoverage :
    Scheme.etalePrecoverage.{u} ≤
      Scheme.precoverage (@Syntomic.{u} : MorphismProperty Scheme.{u}) :=
  Scheme.precoverage_mono fun _ _ f hf ↦
    have : Etale f := hf
    syntomic_of_etale f

end AlgebraicGeometry
