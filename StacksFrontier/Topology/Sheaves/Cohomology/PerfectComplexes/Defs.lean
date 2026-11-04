module

public import StacksFrontier.Topology.Sheaves.Cohomology.PseudoCoherence.Defs
public import Mathlib.Algebra.Category.ModuleCat.Sheaf.Abelian
public import Mathlib.Algebra.Homology.DerivedCategory.Basic

/-!
# Perfect complexes on a ringed space

A complex of `O_X`-modules on a ringed space is *perfect* if it is locally quasi-isomorphic to a
strictly perfect complex; an object of the derived category is perfect if it is represented by a
perfect complex.

## Main definitions

* `Stacks.Cohomology.PerfectComplexes.IsPerfectComplex`: perfect complexes of modules on a ringed
  space.
* `Stacks.Cohomology.PerfectComplexes.IsPerfect`: perfect objects of its derived category.

## Main results

* `Stacks.Cohomology.PerfectComplexes.isPerfectComplex_iff` and
  `Stacks.Cohomology.PerfectComplexes.isPerfect_iff` expose the open-cover and
  representative data directly to downstream statements and proofs.

## Implementation notes

Restriction to an open is `AlgebraicGeometry.RingedSpace.PseudoCoherence.restrictModules`, the
  sheaf-of-modules pushforward along
the functor on opens induced by the open embedding; no second restriction functor is introduced
here. The local quasi-isomorphism points from a strictly perfect complex to the restriction of
the given complex, as in the source. The open family covers when its supremum is the top open.
An isomorphism with the image of a representative under the localization functor expresses
representation in the derived category.

The universe of module sections is the universe of the space, independently of the universe of
the structure sheaf's rings; this is why
  `AlgebraicGeometry.RingedSpace.PseudoCoherence.restrictModules` is stated at independent
module and ring universes. The derived-category predicate uses the chosen localization universe
rather than fixing the standard one.

## References

* [Stacks Project, Tag 08CM](https://stacks.math.columbia.edu/tag/08CM)
-/

@[expose] public noncomputable section

open AlgebraicGeometry CategoryTheory TopologicalSpace StrictlyPerfect
  AlgebraicGeometry.RingedSpace.PseudoCoherence

namespace Stacks.Cohomology.PerfectComplexes

universe u v d

/-- A complex is perfect if an open cover admits strictly perfect complexes mapping to its
restrictions by quasi-isomorphisms. -/
@[stacks 08CM "perfect complexes"]
def IsPerfectComplex {X : RingedSpace.{u, v}}
    (E : CochainComplex (OXMod.{u, v} X) ℤ) : Prop :=
  ∃ (I : Type v) (U : I → Opens X), iSup U = ⊤ ∧
    ∀ i : I, ∃ P : CochainComplex (OXMod.{u, v} (X.restrict (U i).isOpenEmbedding)) ℤ,
      IsStrictlyPerfect P ∧
        ∃ f : P ⟶ ((restrictModules X (U i)).mapHomologicalComplex
          (ComplexShape.up ℤ)).obj E, QuasiIso f

/-- A complex is perfect exactly when a cover has strictly perfect complexes
quasi-isomorphic to its restrictions. -/
theorem isPerfectComplex_iff {X : RingedSpace.{u, v}}
    (E : CochainComplex (OXMod.{u, v} X) ℤ) :
    IsPerfectComplex E ↔
      ∃ (I : Type v) (U : I → Opens X), iSup U = ⊤ ∧
        ∀ i : I,
          ∃ P : CochainComplex (OXMod.{u, v} (X.restrict (U i).isOpenEmbedding)) ℤ,
            IsStrictlyPerfect P ∧
              ∃ f : P ⟶ ((restrictModules X (U i)).mapHomologicalComplex
                (ComplexShape.up ℤ)).obj E, QuasiIso f :=
  Iff.rfl

/-- An object of the derived category is perfect if represented by a perfect complex. -/
@[stacks 08CM "perfect derived-category objects"]
def IsPerfect {X : RingedSpace.{u, v}}
    [HasDerivedCategory.{d} (OXMod.{u, v} X)]
    (K : DerivedCategory (OXMod.{u, v} X)) : Prop :=
  ∃ E : CochainComplex (OXMod.{u, v} X) ℤ,
    IsPerfectComplex E ∧ Nonempty (DerivedCategory.Q.obj E ≅ K)

/-- Perfectness of a derived object is existence of a perfect complex representative. -/
theorem isPerfect_iff {X : RingedSpace.{u, v}}
    [HasDerivedCategory.{d} (OXMod.{u, v} X)]
    (K : DerivedCategory (OXMod.{u, v} X)) :
    IsPerfect K ↔
      ∃ E : CochainComplex (OXMod.{u, v} X) ℤ,
        IsPerfectComplex E ∧ Nonempty (DerivedCategory.Q.obj E ≅ K) :=
  Iff.rfl

/-- Perfectness of a derived object only depends on its isomorphism class: a representative of
one object is, composed with the isomorphism, a representative of the other. -/
instance isClosedUnderIsomorphisms_isPerfect {X : RingedSpace.{u, v}}
    [HasDerivedCategory.{d} (OXMod.{u, v} X)] :
    ObjectProperty.IsClosedUnderIsomorphisms
      (fun K : DerivedCategory (OXMod.{u, v} X) => IsPerfect K) where
  of_iso {K L} e hK := by
    obtain ⟨E, hE, ⟨f⟩⟩ := hK
    exact ⟨E, hE, ⟨f.trans e⟩⟩

end Stacks.Cohomology.PerfectComplexes

end
