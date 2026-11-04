module

public import StacksFrontier.AlgebraicGeometry.Chow.BivariantDisjoint.PieceRestriction
public import StacksFrontier.AlgebraicGeometry.Morphisms.FibreDimension.BaseChange
import StacksCore.Tactic.EgaSgaAttribute

/-!
# The restriction of a morphism to the preimage of a closed subscheme is a base change

For a morphism `u : A ⟶ B` and quasi-coherent ideal sheaf data `J` on `B`, the morphism

  `Stacks.Chow.comapSubschemeMap J u : (J.comap u).subscheme ⟶ J.subscheme`

is the restriction of `u` over the closed subscheme cut out by `J`. This file records that the
square it forms with the two closed immersions is cartesian, and reads off the three properties
that the flat pullback of chapter 42 of the Stacks Project asks of a morphism: being locally of
finite type, being flat, and having relative dimension `d`.

The square is cartesian by construction — `Stacks.Chow.comapSubschemeMap` is the second
projection of `A ×_B J.subscheme` precomposed with
`AlgebraicGeometry.Scheme.IdealSheafData.comapIso` — so the content here is only that the three
properties descend along it. Flatness and local finiteness of presentation are morphism
properties stable under base change, and relative dimension is
[Stacks, Tag 02NK](https://stacks.math.columbia.edu/tag/02NK).

## Why this is wanted

The flat pullback of a cycle supported on an integral closed subscheme `W ⊆ X` is computed on
the preimage `f^{-1}(W)`, and every statement about it needs `f` restricted to that preimage to
be flat of the same relative dimension. The derivation is three lines once the square is
available, but the square was previously reachable only in the
`AlgebraicGeometry.Scheme.IdealSheafData.subschemeMap` spelling, which does not match the
`Stacks.Chow.comapSubschemeMap` that the Chow development uses.

## Main results

* `Stacks.Chow.isPullback_comapSubschemeMap` — the square is cartesian.
* `Stacks.Chow.flat_comapSubschemeMap` and
  `Stacks.Chow.locallyOfFiniteType_comapSubschemeMap` — the two instances.
* `Stacks.Chow.relativeDimension_comapSubschemeMap` — **Stacks 02NK** for this square.

## References

* [Stacks Project, Tag 02NK](https://stacks.math.columbia.edu/tag/02NK)
* [Stacks Project, Tag 02RB](https://stacks.math.columbia.edu/tag/02RB)
-/

@[expose] public noncomputable section

open AlgebraicGeometry CategoryTheory

universe u

namespace Stacks.Chow

/-- **The restriction of `u` to the preimage of a closed subscheme is a base change of `u`.**
The square formed by `Stacks.Chow.comapSubschemeMap J u` with the closed immersions of `J.comap u`
into `A` and of `J` into `B` is cartesian.

This holds by construction: `Stacks.Chow.comapSubschemeMap J u` is the second projection of
`A ×_B J.subscheme` read through
`AlgebraicGeometry.Scheme.IdealSheafData.comapIso`, which identifies `(J.comap u).subscheme` with
that fibre product compatibly with the first projection. -/
theorem isPullback_comapSubschemeMap {A B : Scheme.{u}} (J : B.IdealSheafData) (u : A ⟶ B) :
    IsPullback (J.comap u).subschemeι (comapSubschemeMap J u) u J.subschemeι :=
  IsPullback.of_iso_pullback ⟨(comapSubschemeMap_comp_subschemeι J u).symm⟩ (J.comapIso u)
    (Scheme.IdealSheafData.comapIso_hom_fst J u) rfl

/-- The restriction of a morphism locally of finite type to the preimage of a closed subscheme is
locally of finite type, that property being stable under base change. -/
@[ega "IV 1.3.4" "(iii)"]
instance locallyOfFiniteType_comapSubschemeMap {A B : Scheme.{u}} (J : B.IdealSheafData)
    (u : A ⟶ B) [LocallyOfFiniteType u] : LocallyOfFiniteType (comapSubschemeMap J u) :=
  MorphismProperty.of_isPullback (isPullback_comapSubschemeMap J u)
    (P := @LocallyOfFiniteType) inferInstance

/-- The restriction of a flat morphism to the preimage of a closed subscheme is flat, flatness
being stable under base change. -/
instance flat_comapSubschemeMap {A B : Scheme.{u}} (J : B.IdealSheafData) (u : A ⟶ B)
    [Flat u] : Flat (comapSubschemeMap J u) :=
  MorphismProperty.of_isPullback (isPullback_comapSubschemeMap J u) (P := @Flat) inferInstance

/-- **Stacks 02NK for the preimage of a closed subscheme.** The restriction of a morphism of
relative dimension `d` to the preimage of a closed subscheme again has relative dimension `d`.

This is `AlgebraicGeometry.RelativeDimension.of_isPullback` at the cartesian square of
`Stacks.Chow.isPullback_comapSubschemeMap`. No Stacks attribute is attached: the tag's statement
is the invariance of relative dimension under an arbitrary base change, which
`AlgebraicGeometry.RelativeDimension.of_isPullback` already carries, and this is one instance of
it. -/
theorem relativeDimension_comapSubschemeMap {A B : Scheme.{u}} (J : B.IdealSheafData) (u : A ⟶ B)
    [LocallyOfFiniteType u] {d : ℕ} (hu : AlgebraicGeometry.RelativeDimension u d) :
    AlgebraicGeometry.RelativeDimension (comapSubschemeMap J u) d :=
  AlgebraicGeometry.RelativeDimension.of_isPullback (isPullback_comapSubschemeMap J u) hu

end Stacks.Chow

end
