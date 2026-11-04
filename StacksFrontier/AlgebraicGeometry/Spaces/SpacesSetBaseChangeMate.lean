module

public import StacksFrontier.AlgebraicGeometry.Spaces.ModulePushforwardEtaleBaseChange
public import StacksFrontier.AlgebraicGeometry.Spaces.SmallEtaleRingedToposHom
public import StacksFrontier.AlgebraicGeometry.Spaces.Topologies.SmallEtaleBaseChangeMate

/-!
# The spaces-étale base-change isomorphism is a mate, at the universe of the structure rings

Let

```
X' --i--> X
|f'       |f
Y' --g--> Y
```

be a cartesian square of algebraic spaces over a scheme `S` contained in a big fppf site `B`,
with `g` étale.  `AlgebraicGeometry.Space.spacesSetPushforwardBaseChangeIso` is Stacks 03LR,
part (1) on the spaces-étale sites with coefficients in `Type u`, the universe of the structure
rings — the instance of the square that the module development consumes, because the direct
image of modules applies the direct image of sheaves of *sets* to the sheaf underlying a module
and that direct image exists only at `Type u`.

This file proves that this isomorphism **is** the adjunction mate of the comparison of the two
composite direct images, with respect to the two adjunctions of Stacks 03LP between restriction
along étale postcomposition and restriction along base change; and records the unit square that
the mate relation is equivalent to.

Nothing here is new mathematics.
`AlgebraicGeometry.Space.mateEquiv_spacesPushforwardBaseChangeIso`
(`StacksFrontier/AlgebraicGeometry/Spaces/Topologies/SmallEtaleBaseChangeMate.lean`) is the same
statement with coefficients in `Type (u + 1)`, and the coefficient category plays no role in its
proof: the two inputs are
`AlgebraicGeometry.Space.mateEquiv_spacesEtaleBaseChangeSquare`, a statement about the *sites*
with no coefficients at all, and
`CategoryTheory.mateEquiv_sheafPushforwardContinuousNatTrans`, which is stated for an arbitrary
coefficient category.  So the port is the two assemblies of the comparison of composites,
repeated at `Type u`, and one `exact`.

## Main definitions

* `AlgebraicGeometry.Space.spacesSetPushforwardCompSquare`: the comparison of the two composite
  direct images around the square on the spaces-étale sites, with coefficients in `Type u`.

## Main results

* `AlgebraicGeometry.Space.mateEquiv_spacesSetPushforwardBaseChangeIso`: **the mate
  characterization.**  The mate of the inverse of
  `AlgebraicGeometry.Space.spacesSetPushforwardBaseChangeIso` is
  `AlgebraicGeometry.Space.spacesSetPushforwardCompSquare`.
* `AlgebraicGeometry.Space.spacesSetPushforwardBaseChangeIso_unitSquare`: the equivalent unit
  square — the square made by the *units* of the two adjunctions of Stacks 03LP with the
  base-change isomorphism and the comparison of the two composite direct images commutes.
* `AlgebraicGeometry.Space.spacesSetPushforwardCompSquare_eq` and
  `AlgebraicGeometry.Space.spacesSetPushforwardBaseChangeIso_inv`: both sides of the mate
  relation are the restriction to sheaves of the corresponding statement about the sites.

## Implementation notes

The claim recorded in the implementation notes of
`StacksFrontier/AlgebraicGeometry/Spaces/ModuleHigherPushforwardBaseChangeCanonical.lean` that the
`Type u` copies of Stacks 03LR, part (1) have *no* mate characterization is therefore false of
the spaces-étale copy: the characterization is the port below.  What is genuinely absent is the
corresponding statement for
`AlgebraicGeometry.Space.smallEtaleSetPushforwardBaseChangeIso`, where the four functors are
conjugates by the comparison equivalences of Stacks 03G1 and the comparison of the two
assemblies is a separate computation.

No `@[stacks]` attribute appears here.  Stacks 03LR, part (1) is already carried by
`AlgebraicGeometry.Space.smallEtalePushforwardBaseChangeIso`, and identifying an isomorphism
with its mate is not a separate numbered assertion.

## References

* [Stacks Project, Tag 03LR](https://stacks.math.columbia.edu/tag/03LR)
* [Stacks Project, Tag 03LP](https://stacks.math.columbia.edu/tag/03LP)
* [Stacks Project, Tag 03G2](https://stacks.math.columbia.edu/tag/03G2)
-/

@[expose] public section

open CategoryTheory

universe u

namespace AlgebraicGeometry.Space

variable (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)
  {X Y X' Y' : AlgebraicSpaces B S hS}
  (i : X' ⟶ X) (f' : X' ⟶ Y') (f : X ⟶ Y) (g : Y' ⟶ Y)

/-- The comparison of the two composite direct images of a commuting square of algebraic spaces
on the spaces-étale sites, with coefficients in `Type u`: both composites are restriction along
base change along the common composite `X' ⟶ Y` of the square, by the composition isomorphism of
Stacks 03G2, part (2).

This is `AlgebraicGeometry.Space.spacesPushforwardCompSquare` one universe down. -/
noncomputable def spacesSetPushforwardCompSquare (w : i ≫ f = f' ≫ g) :
    spacesSetBaseChange B S hS i ⋙ spacesSetBaseChange B S hS f ⟶
      spacesSetBaseChange B S hS f' ⋙ spacesSetBaseChange B S hS g :=
  (spacesBaseChange_pushforward_compTypeU B S hS i f).hom ≫
    eqToHom (congrArg (fun k : X' ⟶ Y =>
      (spacesBaseChange B S hS k).functor.sheafPushforwardContinuous (Type u)
        (SpacesEtale.topology B S hS Y) (SpacesEtale.topology B S hS X')) w) ≫
    (spacesBaseChange_pushforward_compTypeU B S hS f' g).inv

/-- The comparison of the two composite direct images is the restriction to sheaves of the
comparison `AlgebraicGeometry.Space.spacesBaseChangeCompSquare` of the two composites of base
change on the sites. -/
theorem spacesSetPushforwardCompSquare_eq (w : i ≫ f = f' ≫ g) :
    letI := Functor.isContinuous_comp (spacesBaseChange B S hS g).functor
      (spacesBaseChange B S hS f').functor
      (SpacesEtale.topology B S hS Y) (SpacesEtale.topology B S hS Y')
      (SpacesEtale.topology B S hS X')
    letI := Functor.isContinuous_comp (spacesBaseChange B S hS f).functor
      (spacesBaseChange B S hS i).functor
      (SpacesEtale.topology B S hS Y) (SpacesEtale.topology B S hS X)
      (SpacesEtale.topology B S hS X')
    spacesSetPushforwardCompSquare B S hS i f' f g w =
      Functor.sheafPushforwardContinuousNatTrans
        (spacesBaseChangeCompSquare B S hS i f' f g w) (Type u)
        (SpacesEtale.topology B S hS Y) (SpacesEtale.topology B S hS X') := by
  rw [spacesSetPushforwardCompSquare, spacesBaseChangeCompSquare,
    Functor.sheafPushforwardContinuousNatTrans_comp,
    Functor.sheafPushforwardContinuousNatTrans_comp,
    Functor.sheafPushforwardContinuousNatTrans_eqToHom, Category.assoc]
  rfl

/-- The spaces-étale base-change isomorphism of Stacks 03LR, part (1) at the universe of the
structure rings is the restriction to sheaves of the Beck–Chevalley isomorphism of the sites. -/
theorem spacesSetPushforwardBaseChangeIso_inv (sq : IsPullback i f' f g)
    (hg : IsEtale B S hS g.hom)
    [((spacesBaseChange B S hS f').functor ⋙
        spacesEtalePostcomp B S hS i
          (isEtale_of_isPullback B S hS f' i g f sq.flip hg)).IsContinuous
      (SpacesEtale.topology B S hS Y') (SpacesEtale.topology B S hS X)]
    [(spacesEtalePostcomp B S hS g hg ⋙
        (spacesBaseChange B S hS f).functor).IsContinuous
      (SpacesEtale.topology B S hS Y') (SpacesEtale.topology B S hS X)] :
    (spacesSetPushforwardBaseChangeIso B S hS i f' f g sq hg).inv =
      Functor.sheafPushforwardContinuousNatTrans
        (spacesEtaleBaseChangeSquare B S hS i f' f g sq hg).hom (Type u)
        (SpacesEtale.topology B S hS Y') (SpacesEtale.topology B S hS X) :=
  rfl

/-- **Beck–Chevalley on the spaces-étale sites at the universe of the structure rings, as a
mate.**  The mate of the inverse of the base-change isomorphism of Stacks 03LR, part (1), with
respect to the two adjunctions of Stacks 03LP between restriction along étale postcomposition
and restriction along base change, is the comparison of the two composite direct images.

This is `AlgebraicGeometry.Space.mateEquiv_spacesPushforwardBaseChangeIso` at `Type u`; the
coefficient category plays no part in the proof. -/
theorem mateEquiv_spacesSetPushforwardBaseChangeIso (sq : IsPullback i f' f g)
    (hg : IsEtale B S hS g.hom) :
    mateEquiv (spacesEtalePostcompSheafAdjunction B S hS (Type u) i
          (isEtale_of_isPullback B S hS f' i g f sq.flip hg))
        (spacesEtalePostcompSheafAdjunction B S hS (Type u) g hg)
        (TwoSquare.mk _ _ _ _
          (spacesSetPushforwardBaseChangeIso B S hS i f' f g sq hg).inv) =
      TwoSquare.mk _ _ _ _ (spacesSetPushforwardCompSquare B S hS i f' f g sq.w) := by
  have key := mateEquiv_sheafPushforwardContinuousNatTrans
    (adj₁ := spacesEtalePostcompBaseChangeAdjunction B S hS g hg)
    (adj₂ := spacesEtalePostcompBaseChangeAdjunction B S hS i
      (isEtale_of_isPullback B S hS f' i g f sq.flip hg))
    (A := Type u)
    (SpacesEtale.topology B S hS Y') (SpacesEtale.topology B S hS Y)
    (SpacesEtale.topology B S hS X') (SpacesEtale.topology B S hS X)
    (TwoSquare.mk _ _ _ _ (spacesEtaleBaseChangeSquare B S hS i f' f g sq hg).hom)
  rw [mateEquiv_spacesEtaleBaseChangeSquare] at key
  have := Functor.isContinuous_comp (spacesBaseChange B S hS f').functor
    (spacesEtalePostcomp B S hS i (isEtale_of_isPullback B S hS f' i g f sq.flip hg))
    (SpacesEtale.topology B S hS Y') (SpacesEtale.topology B S hS X')
    (SpacesEtale.topology B S hS X)
  have := Functor.isContinuous_comp
    (spacesEtalePostcomp B S hS g hg) (spacesBaseChange B S hS f).functor
    (SpacesEtale.topology B S hS Y') (SpacesEtale.topology B S hS Y)
    (SpacesEtale.topology B S hS X)
  rw [spacesSetPushforwardBaseChangeIso_inv, spacesSetPushforwardCompSquare_eq]
  exact key

/-- The inverse mate of the comparison of the two composite direct images is the inverse of the
base-change isomorphism. -/
private theorem mateEquiv_symm_spacesSetPushforwardCompSquare (sq : IsPullback i f' f g)
    (hg : IsEtale B S hS g.hom) :
    (mateEquiv (spacesEtalePostcompSheafAdjunction B S hS (Type u) i
          (isEtale_of_isPullback B S hS f' i g f sq.flip hg))
        (spacesEtalePostcompSheafAdjunction B S hS (Type u) g hg)).symm
        (TwoSquare.mk _ _ _ _ (spacesSetPushforwardCompSquare B S hS i f' f g sq.w)) =
      TwoSquare.mk _ _ _ _
        (spacesSetPushforwardBaseChangeIso B S hS i f' f g sq hg).inv := by
  rw [← mateEquiv_spacesSetPushforwardBaseChangeIso B S hS i f' f g sq hg,
    Equiv.symm_apply_apply]

/-- **The unit square of the spaces-étale base change at the universe of the structure rings.**
For every sheaf of sets `Z` on the spaces-étale site of `X`, the unit of the adjunction of
Stacks 03LP along `g` at `f_*Z`, followed by the direct image along `g` of the base-change
isomorphism of Stacks 03LR, part (1), agrees with the direct image along `f` of the unit along
`i` at `Z`, followed by the comparison of the two composite direct images.

This is the mate relation
`AlgebraicGeometry.Space.mateEquiv_spacesSetPushforwardBaseChangeIso` read through
`CategoryTheory.unit_mateEquiv_symm`. -/
theorem spacesSetPushforwardBaseChangeIso_unitSquare (sq : IsPullback i f' f g)
    (hg : IsEtale B S hS g.hom)
    (Z : Sheaf (SpacesEtale.topology B S hS X) (Type u)) :
    (spacesEtalePostcompSheafAdjunction B S hS (Type u) g hg).unit.app
          ((spacesSetBaseChange B S hS f).obj Z) ≫
        (spacesSetBaseChange B S hS g).map
          ((spacesSetPushforwardBaseChangeIso B S hS i f' f g sq hg).inv.app Z) =
      (spacesSetBaseChange B S hS f).map
          ((spacesEtalePostcompSheafAdjunction B S hS (Type u) i
            (isEtale_of_isPullback B S hS f' i g f sq.flip hg)).unit.app Z) ≫
        (spacesSetPushforwardCompSquare B S hS i f' f g sq.w).app
          ((spacesEtaleSetRestriction B S hS i
            (isEtale_of_isPullback B S hS f' i g f sq.flip hg)).obj Z) := by
  have hu := unit_mateEquiv_symm
    (spacesEtalePostcompSheafAdjunction B S hS (Type u) i
      (isEtale_of_isPullback B S hS f' i g f sq.flip hg))
    (spacesEtalePostcompSheafAdjunction B S hS (Type u) g hg)
    (TwoSquare.mk _ _ _ _ (spacesSetPushforwardCompSquare B S hS i f' f g sq.w)) Z
  rw [mateEquiv_symm_spacesSetPushforwardCompSquare B S hS i f' f g sq hg] at hu
  exact hu.symm

/-- **The mate of the comparison of composite direct images is invertible, on the spaces-étale
sites at the universe of the structure rings.**  By
`AlgebraicGeometry.Space.mateEquiv_spacesSetPushforwardBaseChangeIso` that mate *is* the inverse
of the base-change isomorphism of Stacks 03LR, part (1).

This is the back face of the cube along which
`Stacks.CategoryTheory.isIso_mateEquiv_symm_of_reflectsIsomorphisms` transports invertibility to
the module statement of Stacks 03LX. -/
theorem isIso_mateEquiv_symm_spacesSetPushforwardCompSquare (sq : IsPullback i f' f g)
    (hg : IsEtale B S hS g.hom) :
    IsIso ((mateEquiv (spacesEtalePostcompSheafAdjunction B S hS (Type u) i
          (isEtale_of_isPullback B S hS f' i g f sq.flip hg))
        (spacesEtalePostcompSheafAdjunction B S hS (Type u) g hg)).symm
      (TwoSquare.mk _ _ _ _
        (spacesSetPushforwardCompSquare B S hS i f' f g sq.w))).natTrans := by
  rw [mateEquiv_symm_spacesSetPushforwardCompSquare B S hS i f' f g sq hg]
  exact inferInstanceAs
    (IsIso (spacesSetPushforwardBaseChangeIso B S hS i f' f g sq hg).inv)

end AlgebraicGeometry.Space

end
