module

public import StacksFrontier.AlgebraicGeometry.Chow.AffineBundle.Basic
public import StacksFrontier.AlgebraicGeometry.Chow.AffineBundle.LocalModelRelativeDimension

/-!
# Morphisms that are locally the local model of an affine bundle

The local model `B[z₁, z₂]/(z₁z₂ - f)` of
`StacksFrontier.AlgebraicGeometry.Chow.AffineBundle.LocalModel` is the affine bundle over `Spec B`
degenerating along the vanishing locus of `f`. This file introduces the morphisms that look like
it Zariski-locally on the target — the shape the structure morphism of the scheme of [Stacks,
Tag 0F97] has, over an affine open of the base trivializing both invertible modules — and
transfers to them every property of morphisms that is Zariski-local on the target.

The pattern is the one `Stacks.Chow.IsAffineSpaceBundle` and
`Stacks.Chow.morphismProperty_of_isAffineSpaceBundle` already follow for affine-space bundles;
only the local model is different.

## Main definitions

* `Stacks.AffineBundle.IsLocalModelBundle` — a morphism `f : X ⟶ Y` is a **local-model bundle**
  if every point of `Y` has an open neighbourhood `V`, isomorphic to the spectrum of a ring `B`,
  over which `f` restricts to the structure morphism of the local model of some `b : B`.

## Main results

* `Stacks.AffineBundle.morphismProperty_of_isLocalModelBundle` — a property of morphisms that is
  Zariski-local on the target and holds for the structure morphism of every local model holds
  for every local-model bundle.
* `Stacks.AffineBundle.locallyOfFiniteType_of_isLocalModelBundle`,
  `Stacks.AffineBundle.flat_of_isLocalModelBundle` and
  `Stacks.AffineBundle.relativeDimension_of_isLocalModelBundle` — **a local-model bundle is
  locally of finite type, flat, and of relative dimension one.**

## Implementation notes

The witness is stated as `e.hom ≫ localModelSpecMap B b ≫ eV.hom = f ∣_ V`, with `eV` running
from `Spec B` to the open subscheme rather than the other way round, so that the transfer is two
applications of `MorphismProperty.cancel_left_of_respectsIso` and
`MorphismProperty.cancel_right_of_respectsIso` and no inverse has to be moved across the
equation.

Relative dimension is carried through in the bundled form
`AlgebraicGeometry.locallyOfFiniteTypeRelativeDimension`, which is a `MorphismProperty` and hence
has the Zariski-locality instance; `AlgebraicGeometry.RelativeDimension` itself takes a
`LocallyOfFiniteType` instance as an argument of the definition and so is not one. The relative
dimension of the local model itself is
`Stacks.AffineBundle.relativeDimension_localModelSpecMap`, which is a computation of the Krull
dimension of the fibres and not a consequence of flatness and finite type.

## References

* [Stacks Project, Tag 0F97](https://stacks.math.columbia.edu/tag/0F97)
* [Stacks Project, Tag 02TT](https://stacks.math.columbia.edu/tag/02TT)
-/

@[expose] public noncomputable section

open AlgebraicGeometry CategoryTheory

universe u

namespace Stacks.AffineBundle

/-- A morphism `f : X ⟶ Y` is a **local-model bundle** if every point of `Y` has an open
neighbourhood `V`, isomorphic to the spectrum of a ring `B`, over which `f` restricts to the
structure morphism `Spec(B[z₁, z₂]/(z₁z₂ - b)) ⟶ Spec B` of the local model of some `b : B`. -/
def IsLocalModelBundle {X Y : Scheme.{u}} (f : X ⟶ Y) : Prop :=
  ∀ y : Y, ∃ (V : Y.Opens) (_ : y ∈ V) (B : Type u) (_ : CommRing B) (b : B)
    (e : (f ⁻¹ᵁ V).toScheme ≅ Spec (CommRingCat.of (LocalModel B b)))
    (eV : Spec (CommRingCat.of B) ≅ V.toScheme),
      e.hom ≫ localModelSpecMap B b ≫ eV.hom = f ∣_ V

/-- A property of morphisms that is Zariski-local on the target and holds for the structure
morphism of the local model over every ring holds for every local-model bundle. -/
theorem morphismProperty_of_isLocalModelBundle (P : MorphismProperty Scheme.{u})
    [IsZariskiLocalAtTarget P] {X Y : Scheme.{u}} (f : X ⟶ Y)
    (hP : ∀ (B : Type u) (_ : CommRing B) (b : B), P (localModelSpecMap B b))
    (h : IsLocalModelBundle f) : P f := by
  refine IsZariskiLocalAtTarget.of_forall_exists_morphismRestrict fun y ↦ ?_
  obtain ⟨V, hyV, B, hB, b, e, eV, he⟩ := h y
  refine ⟨V, hyV, ?_⟩
  rw [← he, P.cancel_left_of_respectsIso, P.cancel_right_of_respectsIso]
  exact hP B hB b

/-- **A local-model bundle is locally of finite type**: the local model is a quotient of a
polynomial ring in two variables over the base. -/
theorem locallyOfFiniteType_of_isLocalModelBundle {X Y : Scheme.{u}} (f : X ⟶ Y)
    (h : IsLocalModelBundle f) : LocallyOfFiniteType f := by
  have := HasRingHomProperty.instIsZariskiLocalAtTarget (@LocallyOfFiniteType.{u})
  exact morphismProperty_of_isLocalModelBundle (@LocallyOfFiniteType) f
    (fun B hB b ↦ locallyOfFiniteType_localModelSpecMap B b) h

/-- **A local-model bundle is flat**: the local model is free over the base, on the monomials
`z₁^a` for `a ≥ 0` together with `z₂^b` for `b ≥ 1`. -/
theorem flat_of_isLocalModelBundle {X Y : Scheme.{u}} (f : X ⟶ Y)
    (h : IsLocalModelBundle f) : AlgebraicGeometry.Flat f := by
  have := HasRingHomProperty.instIsZariskiLocalAtTarget
    (P := @AlgebraicGeometry.Flat) (Q := RingHom.Flat)
  exact morphismProperty_of_isLocalModelBundle (@AlgebraicGeometry.Flat) f
    (fun B hB b ↦ flat_localModelSpecMap B b) h

/-- **A local-model bundle has relative dimension one**: the fibres of the local model are
hypersurfaces in the affine plane over a residue field, and being locally of finite type of
relative dimension one is Zariski-local on the target. -/
theorem relativeDimension_of_isLocalModelBundle {X Y : Scheme.{u}} (f : X ⟶ Y)
    (h : IsLocalModelBundle f) [LocallyOfFiniteType f] :
    AlgebraicGeometry.RelativeDimension f 1 := by
  have _ : IsZariskiLocalAtTarget (locallyOfFiniteTypeRelativeDimension.{u} 1) :=
    MorphismProperty.IsLocalAtTarget.of_le Scheme.zariskiPrecoverage_le_fpqcPrecoverage
  have hP : locallyOfFiniteTypeRelativeDimension.{u} 1 f :=
    morphismProperty_of_isLocalModelBundle (locallyOfFiniteTypeRelativeDimension.{u} 1) f
      (fun B hB b ↦ ⟨locallyOfFiniteType_localModelSpecMap B b,
        relativeDimension_localModelSpecMap B b⟩) h
  exact hP.choose_spec

end Stacks.AffineBundle

end
