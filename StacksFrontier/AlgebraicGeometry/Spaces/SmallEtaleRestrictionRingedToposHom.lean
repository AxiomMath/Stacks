module

public import StacksFrontier.Algebra.Category.ModuleCat.Sheaf.RingedToposTwoIsoInverseImage
public import StacksFrontier.AlgebraicGeometry.Spaces.EtaleInverseImageStructureSheaf
public import StacksFrontier.AlgebraicGeometry.Spaces.SmallEtaleRestrictionAdjunction

/-!
# The morphism of small étale ringed topoi of an étale morphism, presented by restriction

For an étale morphism `h : U ⟶ V` of algebraic spaces over `S`, Stacks 03LQ identifies the
inverse image of `AlgebraicGeometry.Space.smallEtaleRingedToposHom h` with restriction of sheaves
along small étale postcomposition with `h` — but only *up to* the comparison
`AlgebraicGeometry.Space.smallToposMorphismTypeU_inverseImageIso` of two left adjoints of one
functor, which is a `CategoryTheory.Adjunction.leftAdjointUniq` and so has no description on
sections.

This file replaces that comparison by a *second presentation* of the same morphism of ringed
topoi, whose inverse image **is** restriction on the nose: the direct image of
`AlgebraicGeometry.Space.smallEtaleRingedToposHom h` is already
`AlgebraicGeometry.Space.smallEtaleDirectImage h` by `Eq.refl`, and
`AlgebraicGeometry.Space.smallEtaleSetRestrictionAdjunction` exhibits restriction as another left
adjoint of it, so the two presentations have the same direct image and the same structure map and
are therefore 2-isomorphic *by the identity*.  Nothing is computed and no choice is made; what
changes is which of the two left adjoints appears in the type.

Three facts about the restriction presentation are then available that the original presentation
does not have:

* its inverse image is `AlgebraicGeometry.Space.smallEtaleSetRestriction h hh`, so its sections
  over a chart `W` of `U` are the sections of the original sheaf over the chart `W ≫ h` of `V`,
  by `Eq.refl`;
* the inverse-image form of its structure map is the **identity**, because the structure map of an
  étale morphism on underlying sheaves of sets is the unit of the restriction adjunction
  (`AlgebraicGeometry.Space.structureSharpSet_eq_unit`) and the adjunct of a unit is an identity;
* consequently the inverse-image form of the structure map of a composite `χ ∘ h` is just the
  restriction of that of `χ`.

## Main definitions

* `AlgebraicGeometry.Space.smallEtaleRestrictionToposHom` — the morphism of small étale topoi of
  an étale morphism, with restriction as its inverse image.
* `AlgebraicGeometry.Space.smallEtaleRestrictionRingedToposHom` — the same as a morphism of
  ringed topoi, carrying the structure map of Stacks 03G8.

## Main results

* `AlgebraicGeometry.Space.forgetRing_map_structureSharpCommRing` — forgetting the ring
  operations in the `CommRingCat`-valued structure map gives
  `AlgebraicGeometry.Space.structureSharpSet`.
* `AlgebraicGeometry.Space.twoIsoSmallEtaleRestrictionRingedToposHom` — **the two presentations
  are 2-isomorphic by the identity.**
* `AlgebraicGeometry.Space.forgetRing_map_smallEtaleRestriction_fSharpInverseImage` — the
  inverse-image form of the structure map of the restriction presentation is the identity.
* `AlgebraicGeometry.Space.forgetRing_map_comp_smallEtaleRestriction_fSharpInverseImage` — hence
  the inverse-image form of the structure map of `χ ∘ h` is the restriction of that of `χ`.

## Implementation notes

Both `AlgebraicGeometry.Space.smallEtaleRestrictionToposHom` and
`AlgebraicGeometry.Space.smallEtaleRestrictionRingedToposHom` are `abbrev`s rather than `def`s.
As semireducible definitions their projections do not reduce at `implicit` transparency, and a
statement about `(smallEtaleRestrictionRingedToposHom h hh).fSharp` then fails to be type-correct
there even though it elaborates.

`AlgebraicGeometry.Space.forgetRing_map_structureSharpCommRing` is not `Eq.refl`: forgetting the
ring operations of a sheaf of commutative rings in one step,
`CategoryTheory.sheafCompose _ (CategoryTheory.forget CommRingCat)`, and in two steps through
`CategoryTheory.forget₂ CommRingCat RingCat`, agree definitionally but not syntactically, so the
statement is proved by a `show` into the two-step spelling followed by
`AlgebraicGeometry.Space.map_structureSharpCommRing`.

## References

* [Stacks Project, Tag 03LQ](https://stacks.math.columbia.edu/tag/03LQ)
* [Stacks Project, Tag 03LP](https://stacks.math.columbia.edu/tag/03LP)
* [Stacks Project, Tag 03LV](https://stacks.math.columbia.edu/tag/03LV)
* [Stacks Project, Tag 03G8](https://stacks.math.columbia.edu/tag/03G8)
* [Stacks Project, Tag 01D3](https://stacks.math.columbia.edu/tag/01D3)
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits Opposite

universe u

namespace AlgebraicGeometry.Space

variable (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)
    {U V : AlgebraicSpaces B S hS}

/-- **Forgetting the ring operations in the structure map of Stacks 03G8 gives its set-level
form.**  The `CommRingCat`-valued structure map
`AlgebraicGeometry.Space.structureSharpCommRing` of a morphism of algebraic spaces has
`AlgebraicGeometry.Space.structureSharpSet` as its underlying map of sheaves of sets. -/
theorem forgetRing_map_structureSharpCommRing (f : U ⟶ V) :
    (smallEtaleRingedTopos B S hS V).forgetRing.map (structureSharpCommRing B S hS f) =
      structureSharpSet B S hS f := by
  change (sheafCompose (SmallEtale.topology B S hS V.1) (forget RingCat.{u})).map
      ((sheafCompose (SmallEtale.topology B S hS V.1)
        (forget₂ CommRingCat.{u} RingCat.{u})).map (structureSharpCommRing B S hS f)) = _
  rw [map_structureSharpCommRing]
  rfl

/-- **The morphism of small étale topoi of an étale morphism of algebraic spaces, presented with
restriction as its inverse image.**  Its direct image is
`AlgebraicGeometry.Space.smallEtaleDirectImage`, exactly as for
`AlgebraicGeometry.Space.smallToposMorphismTypeU`; what is different is that its inverse image is
`AlgebraicGeometry.Space.smallEtaleSetRestriction` on the nose rather than only up to the
comparison of Stacks 03LQ. -/
noncomputable abbrev smallEtaleRestrictionToposHom (h : U ⟶ V) (hh : IsEtale B S hS h.hom) :
    MorphismOfTopoi (smallEtaleRingedTopos B S hS U).Topos
      (smallEtaleRingedTopos B S hS V).Topos where
  pushforward := smallEtaleDirectImage B S hS h
  inverseImage := smallEtaleSetRestriction B S hS h hh
  adj := smallEtaleSetRestrictionAdjunction B S hS h hh
  preservesFiniteLimits := inferInstance

/-- **The morphism of small étale ringed topoi of an étale morphism of algebraic spaces,
presented with restriction as its inverse image.**  It carries the structure map of Stacks 03G8,
so it differs from `AlgebraicGeometry.Space.smallEtaleRingedToposHom` only in the presentation of
the inverse image. -/
noncomputable abbrev smallEtaleRestrictionRingedToposHom (h : U ⟶ V)
    (hh : IsEtale B S hS h.hom) :
    RingedToposHom (smallEtaleRingedTopos B S hS U) (smallEtaleRingedTopos B S hS V) where
  toToposHom := smallEtaleRestrictionToposHom B S hS h hh
  fSharp := structureSharpCommRing B S hS h

/-- **The two presentations are 2-isomorphic by the identity.**  They have the same direct image
and the same structure map, so the identity isomorphism of direct images is a 2-isomorphism
between them. -/
noncomputable def twoIsoSmallEtaleRestrictionRingedToposHom (h : U ⟶ V)
    (hh : IsEtale B S hS h.hom) :
    RingedToposHom.TwoIso.{u, u + 1, u, u, u + 1, u}
      (smallEtaleRingedToposHom B S hS h) (smallEtaleRestrictionRingedToposHom B S hS h hh) where
  e := Iso.refl _
  commutes := Category.comp_id _

/-- **The inverse-image form of the structure map of the restriction presentation is the
identity.**  Restriction carries the structure sheaf of `V` to the structure sheaf of `U` on the
nose, the set-level structure map of an étale morphism is the unit of the restriction adjunction
(`AlgebraicGeometry.Space.structureSharpSet_eq_unit`), and the adjunct of a unit is an
identity. -/
theorem forgetRing_map_smallEtaleRestriction_fSharpInverseImage (h : U ⟶ V)
    (hh : IsEtale B S hS h.hom) :
    (smallEtaleRingedTopos B S hS U).forgetRing.map
        (smallEtaleRestrictionRingedToposHom B S hS h hh).fSharpInverseImage = 𝟙 _ := by
  refine (RingedToposHom.fSharpInverseImage_forget_homEquiv
    (smallEtaleRestrictionRingedToposHom B S hS h hh)).trans ?_
  refine ((smallEtaleSetRestrictionAdjunction B S hS h hh).homEquiv
    (structureSetSheaf B S hS V) (structureSetSheaf B S hS U)).injective ?_
  refine (Equiv.apply_symm_apply _ _).trans ?_
  refine Eq.trans ?_ (Adjunction.homEquiv_unit _ _ _ _).symm
  refine Eq.trans ((forgetRing_map_structureSharpCommRing B S hS h).trans
    (structureSharpSet_eq_unit B S hS h hh)) ?_
  refine Eq.trans ?_ (congrArg
    (fun z => (smallEtaleSetRestrictionAdjunction B S hS h hh).unit.app
      (structureSetSheaf B S hS V) ≫ z)
    ((smallEtaleDirectImage B S hS h).map_id (structureSetSheaf B S hS U)).symm)
  exact (Category.comp_id _).symm

/-- **The inverse-image form of the structure map of a composite with the restriction
presentation of an étale morphism is the restriction of the structure map.**  This is the
composition law `AlgebraicGeometry.RingedToposHom.comp_fSharpInverseImage_forget` with its second
factor the identity. -/
theorem forgetRing_map_comp_smallEtaleRestriction_fSharpInverseImage
    {X Y : AlgebraicSpaces B S hS}
    (χ : RingedToposHom (smallEtaleRingedTopos B S hS X) (smallEtaleRingedTopos B S hS Y))
    (h : U ⟶ X) (hh : IsEtale B S hS h.hom) :
    (smallEtaleRingedTopos B S hS U).forgetRing.map
        (χ.comp (smallEtaleRestrictionRingedToposHom B S hS h hh)).fSharpInverseImage =
      (smallEtaleSetRestriction B S hS h hh).map
        ((smallEtaleRingedTopos B S hS X).forgetRing.map χ.fSharpInverseImage) :=
  (RingedToposHom.comp_fSharpInverseImage_forget χ
      (smallEtaleRestrictionRingedToposHom B S hS h hh)).trans
    ((congrArg
      (fun z => (smallEtaleSetRestriction B S hS h hh).map
        ((smallEtaleRingedTopos B S hS X).forgetRing.map χ.fSharpInverseImage) ≫ z)
      (forgetRing_map_smallEtaleRestriction_fSharpInverseImage B S hS h hh)).trans
        (Category.comp_id _))

end AlgebraicGeometry.Space

end
