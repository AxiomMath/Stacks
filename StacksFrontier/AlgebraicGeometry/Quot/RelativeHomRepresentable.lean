module

public import StacksCore.Tactic.StacksAttribute
public import StacksFrontier.AlgebraicGeometry.Quot.RelativeHom
public import StacksFrontier.AlgebraicGeometry.Spaces.FinitePresentation
public import StacksFrontier.AlgebraicGeometry.Spaces.Morphisms.Affine

/-!
# Being an algebraic space affine over a base, read on the test schemes

The representability statements of the `Quot` chapter — Stacks 08JY, 08K6, 08K9 — all have
the shape

> the functor `Hom(F, G) : (Sch/B)ᵒᵖ ⥤ Sets` of Stacks 08JT *is an algebraic space affine
> (and of finite presentation) over `B`*.

The functor of Stacks 08JT lives on the test schemes over `B`,
`AlgebraicGeometry.Space.SchemesOver`, and is built in
`StacksFrontier/AlgebraicGeometry/Quot/RelativeHom.lean`.  An algebraic space affine over `B`,
on the other hand, is an object `H` of `AlgebraicGeometry.AlgebraicSpaces` together with a
morphism `p : H ⟶ B` satisfying `AlgebraicGeometry.Space.IsAffineHom`.  This file supplies
the bridge: the functor on the test schemes over `B` that such a `p` determines, and the two
predicates on a functor on the test schemes that the three statements assert.

The bridge is the *functor of points over the base*: for a test scheme `T` over `B` the set
of morphisms `T ⟶ H` over `B`, which by the Yoneda lemma is the set of sections of `H` over
the scheme `T` lying over the section of `B` that the structure morphism of `T` is.  This is
`AlgebraicGeometry.Space.spacePointsOver`.

## Main definitions

* `AlgebraicGeometry.Space.testPoint`: the section of `Y` over the underlying scheme of a
  test scheme over `Y` that the structure morphism of the test scheme is.
* `AlgebraicGeometry.Space.spacePointsOver`: **the points of an algebraic space over `Y` on
  the test schemes over `Y`**, as a functor `(SchemesOver Y)ᵒᵖ ⥤ Type u`.
* `AlgebraicGeometry.Space.IsAffineAlgebraicSpaceOver`: a functor on the test schemes over
  `Y` *is an algebraic space affine over `Y`*.
* `AlgebraicGeometry.Space.IsAffineFinitePresentationAlgebraicSpaceOver`: a functor on the
  test schemes over `Y` *is an algebraic space affine and of finite presentation over `Y`*.
* `AlgebraicGeometry.Space.HomSituation.IsAffineAlgebraicSpaceOverBase` and
  `AlgebraicGeometry.Space.HomSituation.IsAffineFinitePresentationAlgebraicSpaceOverBase`:
  the two conclusions, at the relative Hom functor of Stacks 08JT.

## Main results

* `AlgebraicGeometry.Space.testPoint_naturality`: the section of `Y` that a test scheme is
  is natural in the test scheme.  This is what makes `spacePointsOver` a functor.
* `AlgebraicGeometry.Space.spacePointsOver_obj` and
  `AlgebraicGeometry.Space.spacePointsOver_map_coe`: the value of the functor of points over
  the base and its action, as sections of `H`.
* `AlgebraicGeometry.Space.IsAffineAlgebraicSpaceOver.of_iso` and
  `AlgebraicGeometry.Space.IsAffineFinitePresentationAlgebraicSpaceOver.of_iso`: both
  predicates transport along an isomorphism of functors on the test schemes.  This is what
  lets a representability statement be proved after replacing the functor by any functor
  isomorphic to it, which is how every proof in the chapter proceeds.
* `Space.IsAffineFinitePresentationAlgebraicSpaceOver.isAffineAlgebraicSpaceOver`: being an
  algebraic space affine and of finite presentation over `Y` is in particular being one affine
  over `Y`.

## Implementation notes

**Why the points over the base, and not the absolute functor.**  The source reads
`Hom(F, G)` as a functor `(Sch/S)ᵒᵖ ⥤ Sets` endowed with a morphism to `B`, whose value at a
scheme `T` over `S` is the set of pairs `(h, u)` with `h : T ⟶ B` and `u : F_T ⟶ G_T` (see
the discussion after Stacks 08JT).  That functor-with-a-morphism-to-`B` and the functor on
the test schemes over `B` are equivalent data: the fibre of the absolute functor over a
section `h` of `B` is the value of the relative functor at the test scheme `(T, h)`, and the
absolute functor is recovered as the total space of those fibres.  Working on the test
schemes over `B` is what the development already has — it is the index category of
`AlgebraicGeometry.Space.HomSituation.homFunctor` — so the comparison is made there, with
`spacePointsOver` playing the part of the right-hand side.  Nothing is weakened: `H` is a
genuine object of `AlgebraicGeometry.AlgebraicSpaces`, so it carries the full
algebraic-space condition of Stacks 025Y, and `p` is a genuine morphism of algebraic spaces,
so `AlgebraicGeometry.Space.IsAffineHom` and
`AlgebraicGeometry.Space.IsFinitePresentation` are the conditions of Stacks 03WF and
Stacks 03XP on it.

**The universe lift.**  An algebraic space is a presheaf valued in `Type u`, the universe of
the schemes of the site, whereas the relative Hom functor is valued in `Type (u + 1)`: a
homomorphism of sheaves of modules on an algebraic space is a datum one universe up, as
recorded in the implementation notes of
`StacksFrontier/AlgebraicGeometry/Quot/RelativeHom.lean`.  The comparison is therefore stated
between `CategoryTheory.uliftFunctor.{u + 1, u}` applied to the functor of points and the
Hom functor itself, exactly as in `StacksFrontier/AlgebraicGeometry/Spaces/LargeValued.lean`,
where the algebraic-space notions are carried into a larger value universe.  A universe lift
is an equivalence onto its image, so this is a comparison of the two functors and not a
weakening of either.

**The comparison is `Nonempty` of an isomorphism**, so that the two predicates are
propositions; the data of the isomorphism is never used downstream, only its existence.

## References

* [Stacks Project, Tag 08JT](https://stacks.math.columbia.edu/tag/08JT)
* [Stacks Project, Tag 03WF](https://stacks.math.columbia.edu/tag/03WF)
* [Stacks Project, Tag 03XP](https://stacks.math.columbia.edu/tag/03XP)
* [Stacks Project, Tag 025Y](https://stacks.math.columbia.edu/tag/025Y)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits

namespace AlgebraicGeometry.Space

universe u

variable {B : BigFppfSite.{u}} {S : Scheme.{u}} {hS : B.Contains S}

section PointsOver

variable {Y : AlgebraicSpaces B S hS}

/-- The section of `Y` over the underlying scheme of a test scheme over `Y` that the
structure morphism of the test scheme is, through the Yoneda lemma. -/
def testPoint (T : SchemesOver Y) : Y.1.obj (Opposite.op T.left) :=
  yonedaEquiv T.hom.hom

/-- The underlying morphism of presheaves of the structure morphism of a test scheme is the
one the Yoneda lemma attaches to its section of `Y`. -/
theorem yonedaEquiv_symm_testPoint (T : SchemesOver Y) :
    yonedaEquiv.symm (testPoint T) = T.hom.hom :=
  yonedaEquiv.symm_apply_apply _

/-- **The section of `Y` that a test scheme is, is natural in the test scheme.**  This is
the content of the commuting triangle defining a morphism of test schemes, read through the
Yoneda lemma, and it is what makes the functor of points over `Y` a functor. -/
theorem testPoint_naturality {U T : SchemesOver Y} (g : U ⟶ T) :
    Y.1.map (Opposite.op g.left) (testPoint T) = testPoint U := by
  have hw : yoneda.map g.left ≫ T.hom.hom = U.hom.hom :=
    congrArg InducedCategory.Hom.hom (CostructuredArrow.w g)
  exact (yonedaEquiv_naturality T.hom.hom g.left).trans (congrArg yonedaEquiv hw)

variable {H : AlgebraicSpaces B S hS}

/-- The points of `H` over `Y` at a test scheme `T` over `Y`: the sections of `H` over the
underlying scheme of `T` that lie over the section of `Y` that `T` is.  By the Yoneda lemma
these are the morphisms `T ⟶ H` over `Y`. -/
abbrev spacePointsOverObj (p : H ⟶ Y) (T : SchemesOver Y) : Type u :=
  {x : H.1.obj (Opposite.op T.left) // p.hom.app (Opposite.op T.left) x = testPoint T}

/-- A section of `H` lying over the section of `Y` that a test scheme is, restricted along a
morphism of test schemes, still lies over the section that the smaller test scheme is. -/
theorem spacePointsOver_restrict {p : H ⟶ Y} {U T : SchemesOver Y} (g : U ⟶ T)
    (x : spacePointsOverObj p T) :
    p.hom.app (Opposite.op U.left) (H.1.map g.left.op x.1) = testPoint U := by
  rw [NatTrans.naturality_apply, x.2]
  exact testPoint_naturality g

/-- **The points of an algebraic space over `Y` on the test schemes over `Y`.**  For a test
scheme `T` over `Y` this is the set of sections of `H` over the underlying scheme of `T`
lying over the section of `Y` that `T` is; by the Yoneda lemma, the set of morphisms
`T ⟶ H` over `Y`.  A morphism of test schemes acts by restriction of sections.

This is the right-hand side of every representability statement of the `Quot` chapter: a
functor on the test schemes over `Y` *is an algebraic space over `Y`* when it is isomorphic
to one of these. -/
def spacePointsOver (p : H ⟶ Y) : (SchemesOver Y)ᵒᵖ ⥤ Type u where
  obj T := spacePointsOverObj p T.unop
  map {T T'} g := ↾fun x ↦ ⟨H.1.map g.unop.left.op x.1, spacePointsOver_restrict g.unop x⟩
  map_id T := by
    refine ConcreteCategory.hom_ext _ _ fun x ↦ Subtype.ext ?_
    exact H.1.map_id_apply _ x.1
  map_comp g h := by
    refine ConcreteCategory.hom_ext _ _ fun x ↦ Subtype.ext ?_
    exact H.1.map_comp_apply g.unop.left.op h.unop.left.op x.1

/-- The value of the functor of points over `Y` is the sections of `H` lying over the
section of `Y` that the test scheme is. -/
theorem spacePointsOver_obj (p : H ⟶ Y) (T : SchemesOver Y) :
    (spacePointsOver p).obj (Opposite.op T) = spacePointsOverObj p T :=
  rfl

/-- The functor of points over `Y` acts by restriction of sections of `H`. -/
theorem spacePointsOver_map_coe (p : H ⟶ Y) {U T : SchemesOver Y} (g : U ⟶ T)
    (x : spacePointsOverObj p T) :
    (((spacePointsOver p).map (Opposite.op g)) x).1 = H.1.map g.left.op x.1 :=
  rfl

end PointsOver

section Predicates

variable (Y : AlgebraicSpaces B S hS) (R R' : (SchemesOver Y)ᵒᵖ ⥤ Type (u + 1))

/-- **A functor on the test schemes over `Y` is an algebraic space affine over `Y`**: it is
isomorphic to the universe lift of the functor of points over `Y` of an algebraic space `H`
whose morphism `H ⟶ Y` is affine in the sense of Stacks 03WF. -/
def IsAffineAlgebraicSpaceOver : Prop :=
  ∃ (H : AlgebraicSpaces B S hS) (p : H ⟶ Y), IsAffineHom B S hS p.hom ∧
    Nonempty (spacePointsOver p ⋙ uliftFunctor.{u + 1, u} ≅ R)

/-- **A functor on the test schemes over `Y` is an algebraic space affine and of finite
presentation over `Y`**: it is isomorphic to the universe lift of the functor of points over
`Y` of an algebraic space `H` whose morphism `H ⟶ Y` is affine in the sense of Stacks 03WF
and of finite presentation in the sense of Stacks 03XP, part (3). -/
def IsAffineFinitePresentationAlgebraicSpaceOver : Prop :=
  ∃ (H : AlgebraicSpaces B S hS) (p : H ⟶ Y), IsAffineHom B S hS p.hom ∧
    IsFinitePresentation B S hS p.hom ∧
      Nonempty (spacePointsOver p ⋙ uliftFunctor.{u + 1, u} ≅ R)

variable {Y R R'}

/-- Being an algebraic space affine over `Y` transports along an isomorphism of functors on
the test schemes over `Y`. -/
theorem IsAffineAlgebraicSpaceOver.of_iso (e : R ≅ R') (h : IsAffineAlgebraicSpaceOver Y R) :
    IsAffineAlgebraicSpaceOver Y R' := by
  obtain ⟨H, p, hp, ⟨c⟩⟩ := h
  exact ⟨H, p, hp, ⟨c ≪≫ e⟩⟩

/-- Being an algebraic space affine and of finite presentation over `Y` transports along an
isomorphism of functors on the test schemes over `Y`. -/
theorem IsAffineFinitePresentationAlgebraicSpaceOver.of_iso (e : R ≅ R')
    (h : IsAffineFinitePresentationAlgebraicSpaceOver Y R) :
    IsAffineFinitePresentationAlgebraicSpaceOver Y R' := by
  obtain ⟨H, p, hp, hfp, ⟨c⟩⟩ := h
  exact ⟨H, p, hp, hfp, ⟨c ≪≫ e⟩⟩

/-- An algebraic space affine and of finite presentation over `Y` is in particular an
algebraic space affine over `Y`. -/
theorem IsAffineFinitePresentationAlgebraicSpaceOver.isAffineAlgebraicSpaceOver
    (h : IsAffineFinitePresentationAlgebraicSpaceOver Y R) : IsAffineAlgebraicSpaceOver Y R := by
  obtain ⟨H, p, hp, _, hc⟩ := h
  exact ⟨H, p, hp, hc⟩

/-- An algebraic space affine over `Y` whose morphism to `Y` is of finite presentation is an
algebraic space affine and of finite presentation over `Y`. -/
theorem IsAffineAlgebraicSpaceOver.isAffineFinitePresentationAlgebraicSpaceOver
    {H : AlgebraicSpaces B S hS} (p : H ⟶ Y) (hp : IsAffineHom B S hS p.hom)
    (hfp : IsFinitePresentation B S hS p.hom)
    (c : spacePointsOver p ⋙ uliftFunctor.{u + 1, u} ≅ R) :
    IsAffineFinitePresentationAlgebraicSpaceOver Y R :=
  ⟨H, p, hp, hfp, ⟨c⟩⟩

end Predicates

namespace HomSituation

variable (s : HomSituation B S hS) (hc : ModulePushforwardCoherence B S hS)

/-- **The relative Hom functor of Stacks 08JT is an algebraic space affine over the base.**
This is the first conclusion of Stacks 08K6; it is conditional on the pseudofunctoriality of
the direct images of Stacks 03LU, as the relative Hom functor itself is. -/
abbrev IsAffineAlgebraicSpaceOverBase : Prop :=
  IsAffineAlgebraicSpaceOver s.base (s.homFunctor hc)

/-- **The relative Hom functor of Stacks 08JT is an algebraic space affine and of finite
presentation over the base.**  This is the conclusion of Stacks 08JY, the second conclusion
of Stacks 08K6, and the conclusion of Stacks 08K9 at the Isom functor; it is conditional on
the pseudofunctoriality of the direct images of Stacks 03LU, as the relative Hom functor
itself is. -/
abbrev IsAffineFinitePresentationAlgebraicSpaceOverBase : Prop :=
  IsAffineFinitePresentationAlgebraicSpaceOver s.base (s.homFunctor hc)

end HomSituation

end AlgebraicGeometry.Space

end
