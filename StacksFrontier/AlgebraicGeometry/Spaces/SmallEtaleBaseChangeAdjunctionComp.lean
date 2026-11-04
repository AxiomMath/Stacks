module

public import StacksFrontier.AlgebraicGeometry.Spaces.SmallEtaleBaseChangeAdjunction
public import StacksFrontier.AlgebraicGeometry.Spaces.SmallEtaleModulePullbackCompIsoEtaleRestriction
public import StacksFrontier.CategoryTheory.Adjunction.ConjugateCompTransfer

/-!
# Base change of charts along a composite, against the comparison of direct images

Along an étale *representable* morphism `f : X ⟶ Y` of algebraic spaces, restriction of modules
`AlgebraicGeometry.Space.etaleModulePullback` has a second adjunction beside the one of
Stacks 03LU: `AlgebraicGeometry.Space.etaleModulePullbackSmallBaseChangeAdjunction`, whose right
adjoint is restriction of sections along base change of étale scheme charts.  That adjunction is
built from the site-level universal property of the fibre product and mentions neither the
comparison of inverse images of Stacks 03LU nor the identification of Stacks 03LW, which is why
it is the one candidate in this development for proving the coherence of those two that the
quasi-coherent module-descent files — and through them Stacks 03LY — are parameterized by,
namely `AlgebraicGeometry.Space.QuasiCoherentDescent.ModulePullbackCompIsoEtaleRestriction`.

This file carries that candidate out, and the result is a **negative** one, which is the point of
recording it: the coherence is equivalent to the identification of the resulting comparison of
right adjoints with `AlgebraicGeometry.Space.modulePushforwardCompIso`, so that route does not
discharge it.  See "What this settles" below for the two statements that do remain open, and for
why one of them is not of the same kind.

## Main definitions

* `AlgebraicGeometry.Space.etaleModulePullbackSmallBaseChangeCompAdjunction` is the composite of
  the two base-change adjunctions, with its left adjoint read as restriction along the composite.
* `AlgebraicGeometry.Space.smallBaseChangeModulePushforwardCompIso` is **the composition
  comparison of the base-change direct images**, `(- ×_C A) ×_A D ≅ - ×_C D` on sections: the
  comparison of the two right adjoints of restriction along the composite that uniqueness of a
  right adjoint supplies.
* `AlgebraicGeometry.Space.SmallBaseChangeModulePushforwardCompSquare` is the square relating it
  to `AlgebraicGeometry.Space.modulePushforwardCompIso` through
  `AlgebraicGeometry.Space.smallBaseChangeModulePushforwardIso` at the three morphisms.

## Main results

* `AlgebraicGeometry.Space.etaleModulePullbackSmallBaseChangeAdjunction_comp`: **the composition
  law for the base-change adjunction** — the adjunction at a composite *is* the composite of the
  two adjunctions, read through
  `AlgebraicGeometry.Space.smallBaseChangeModulePushforwardCompIso`.
* `AlgebraicGeometry.Space.etaleModulePullbackCompAdjunction_eq_iff`: **the equivalence.**  The
  two adjunctions of étale restriction along a composite agree — which is the hypothesis `hu` of
  `AlgebraicGeometry.Space.modulePullbackCompIso_hom_comp_etaleRestriction` — if and only if the
  square commutes.
* `AlgebraicGeometry.Space.modulePullbackCompIso_hom_comp_etaleRestriction_of_square` and
  `AlgebraicGeometry.Space.modulePullbackCompIsoEtaleRestriction_of_square`: the coherence of
  Stacks 03LU against Stacks 03LW, and the predicate the descent files carry, from the square.
* `AlgebraicGeometry.Space.smallBaseChangeModulePushforwardCompSquare_of_unit`: the converse —
  the square follows from that same hypothesis.

## What this settles

The route this file was written to carry out is: prove the composition law for the base-change
adjunction, then identify the comparison of right adjoints it produces with
`AlgebraicGeometry.Space.modulePushforwardCompIso` through
`AlgebraicGeometry.Space.smallBaseChangeModulePushforwardIso`.  The first half is
`AlgebraicGeometry.Space.etaleModulePullbackSmallBaseChangeAdjunction_comp`, and it is *formal*:
the comparison is `CategoryTheory.Adjunction.rightAdjointUniq` of the composite adjunction
against the adjunction at the composite, and an adjunction is its own transport along that
comparison.  Nothing about charts or fibre products is used, and nothing is gained — the content
of a composition law for this adjunction is a *concrete* description of that comparison on
sections, as restriction along the canonical comparison of `(V ×_C A) ×_A D` with `V ×_C D`, and
that is a statement about charts which this file does not need and does not prove.

The second half is the obstruction, and
`AlgebraicGeometry.Space.etaleModulePullbackCompAdjunction_eq_iff` measures it exactly: the
square is **equivalent** to the coherence it was meant to prove.  The reason is visible in the
general form of the equivalence,
`Stacks.CategoryTheory.eq_comp_ofNatIsoRight_ofNatIsoLeft_iff_rightAdjointUniq`: both
`AlgebraicGeometry.Space.smallBaseChangeModulePushforwardIso` and
`AlgebraicGeometry.Space.smallBaseChangeModulePushforwardCompIso` are
`CategoryTheory.Adjunction.rightAdjointUniq`, so the square is an identity between mates of
mates, and the conjugate calculus collapses it to the coherence.  A route through the
base-change adjunction must therefore identify the comparison
`smallBaseChangeModulePushforward f ≅ modulePushforward f` by some means *other* than uniqueness
of a right adjoint.

**And one such means is in the development.**
`AlgebraicGeometry.Space.modulePushforwardChartIso` of
`StacksFrontier/AlgebraicGeometry/Spaces/ModulePushforwardChartComparison.lean` identifies
`AlgebraicGeometry.Space.modulePushforward` along a representable morphism with
`AlgebraicGeometry.Space.smallBaseChangeModulePushforward` by hand — through the right Kan
extension form of the direct image of sheaves of sets, whose index category has the
base-changed chart as an initial object — and so independently of both adjunctions.  With it the
route becomes: prove

* **(†)** `smallBaseChangeModulePushforwardIso f hf hrep = (modulePushforwardChartIso f hrep).symm`
  — that the hand-built comparison is the adjoint-canonical one, equivalently that the unit of
  the adjunction of Stacks 03LU at a representable étale `f`, read through Stacks 03LW and
  through the chart comparison, is restriction of sections along the cartesian projection
  `V ×_Y X ⟶ V`; this is a statement at a **single** morphism, and
  `AlgebraicGeometry.Space.etaleModulePullbackSmallBaseChangeAdjunction_unit_app_val_app` already
  says that the other unit is that restriction, by `rfl`;
* and then the square, whose three comparisons are by then all hand-built and all computable on
  sections — the two chart comparisons and
  `AlgebraicGeometry.Space.moduleSheafFunctor_map_compIsoCongr_hom_app`, which identifies
  `modulePushforwardCompIso` with the geometric comparison of Stacks 03G2, part (3), on
  underlying sheaves of sets.

Neither is proved here.  (†) is the one new statement the repaired route needs, and it is not of
the same kind as the coherence: it is about one morphism rather than a composable pair, and both
of the things it compares have a description on sections.

(†) is moreover of the same kind as the `restrict` field of
`AlgebraicGeometry.Space.ModulePullbackEtaleSourceCoherence` in
`StacksFrontier/AlgebraicGeometry/Spaces/EtaleSourceModulePullbackComparison.lean` — that the
identification of Stacks 03LW carries the chart section at the identity-vertical diagram back to
the section it came from.  Both ask for the unit of a pullback of modules at an étale morphism,
read on the sections over a chart, so a pass that settles one is likely to settle the other.

Two corrections to what this paragraph used to add.  The chart bijectivity of Stacks 083K no
longer waits on that pair: it is
`AlgebraicGeometry.Space.bijective_modulePullbackChartBaseChange_of_isQuasicoherentOnSite` in
`StacksFrontier/AlgebraicGeometry/Spaces/EtaleSourceModuleFMapCompDischarge.lean`, with no
coherence hypothesis.  And the second bullet above is not owed either — that the comparison of
direct images of modules of Stacks 03LU is the geometric comparison of Stacks 03G2, part (3), on
underlying sheaves of sets is
`AlgebraicGeometry.Space.moduleSheafFunctor_map_modulePushforwardCompIso_hom_app` in
`StacksFrontier/AlgebraicGeometry/Spaces/ModulePushforwardCompIsoSheafTransfer.lean`.  So (†) is the
one statement this file's route still needs.

A representability hypothesis is no obstacle to Stacks 03LY — the two chart families it uses are
representable, `AlgebraicGeometry.Space.chartMap` being a morphism of representables and
`AlgebraicGeometry.Space.chartToSpace` representable by
`AlgebraicGeometry.Space.relativelyRepresentable_of_isAlgebraicSpace` — but it does mean that a
consumer of the coherence in the form of the predicate
`AlgebraicGeometry.Space.QuasiCoherentDescent.ModulePullbackCompIsoEtaleRestriction`, which
quantifies over all étale pairs, needs the representable form to be fed through the chart
morphisms rather than the predicate.  That is why
`AlgebraicGeometry.Space.modulePullbackCompIsoEtaleRestriction_of_square` asks for the square at
every representable triple.

## References

* [Stacks Project, Tag 03LP](https://stacks.math.columbia.edu/tag/03LP)
* [Stacks Project, Tag 03G2](https://stacks.math.columbia.edu/tag/03G2)
* [Stacks Project, Tag 03LU](https://stacks.math.columbia.edu/tag/03LU)
* [Stacks Project, Tag 03LW](https://stacks.math.columbia.edu/tag/03LW)
* [Stacks Project, Tag 03LY](https://stacks.math.columbia.edu/tag/03LY)
-/

@[expose] public noncomputable section

open CategoryTheory

universe u

namespace AlgebraicGeometry.Space

variable (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)
variable {A C D : AlgebraicSpaces B S hS} (h : D ⟶ A) (g : A ⟶ C)
    (hh : IsEtale B S hS h.hom) (hg : IsEtale B S hS g.hom)
    (hhg : IsEtale B S hS (h ≫ g).hom)
    (hreph : yoneda.relativelyRepresentable h.hom)
    (hrepg : yoneda.relativelyRepresentable g.hom)
    (hrephg : yoneda.relativelyRepresentable (h ≫ g).hom)

/-- The comparison of the base-change direct image with the direct image of Stacks 03LU is the
comparison of two right adjoints of étale restriction that uniqueness of a right adjoint
supplies, the second adjunction being the one of Stacks 03LU read through Stacks 03LW. -/
theorem smallBaseChangeModulePushforwardIso_eq (f : D ⟶ C) (hf : IsEtale B S hS f.hom)
    (hrep : yoneda.relativelyRepresentable f.hom) :
    smallBaseChangeModulePushforwardIso B S hS f hf hrep =
      Adjunction.rightAdjointUniq
        (etaleModulePullbackSmallBaseChangeAdjunction B S hS f hf hrep)
        (etaleModulePullbackAdjunction B S hS f hf) := rfl

/-- The composite of the two base-change adjunctions, with its left adjoint read as restriction
along the composite: restriction along `h ≫ g` is left adjoint to base change of charts along
`g` followed by base change along `h`. -/
def etaleModulePullbackSmallBaseChangeCompAdjunction :
    etaleModulePullback.{u, u} B S hS (h ≫ g) hhg ⊣
      smallBaseChangeModulePushforward.{u, u} B S hS h hreph ⋙
        smallBaseChangeModulePushforward.{u, u} B S hS g hrepg :=
  ((etaleModulePullbackSmallBaseChangeAdjunction B S hS g hg hrepg).comp
      (etaleModulePullbackSmallBaseChangeAdjunction B S hS h hh hreph)).ofNatIsoLeft
    (etaleModulePullbackComp B S hS h g hh hg hhg)

/-- **The composition comparison of the base-change direct images.**  Base change of charts along
`g` followed by base change along `h` and base change along the composite are two right adjoints
of restriction of modules along `h ≫ g`, so they are compared by uniqueness of a right
adjoint. -/
def smallBaseChangeModulePushforwardCompIso :
    smallBaseChangeModulePushforward.{u, u} B S hS h hreph ⋙
        smallBaseChangeModulePushforward.{u, u} B S hS g hrepg ≅
      smallBaseChangeModulePushforward.{u, u} B S hS (h ≫ g) hrephg :=
  Adjunction.rightAdjointUniq
    (etaleModulePullbackSmallBaseChangeCompAdjunction B S hS h g hh hg hhg hreph hrepg)
    (etaleModulePullbackSmallBaseChangeAdjunction B S hS (h ≫ g) hhg hrephg)

/-- **The composition law for the base-change adjunction.**  The adjunction between restriction
of modules along `h ≫ g` and base change of charts along `h ≫ g` is the composite of the two
adjunctions of the factors, read through
`AlgebraicGeometry.Space.smallBaseChangeModulePushforwardCompIso` on the right and through the
strict composition of étale restrictions on the left.

This is formal — the comparison is uniqueness of a right adjoint, and an adjunction is its own
transport along it; see the module documentation for what a composition law with content would
have to say. -/
theorem etaleModulePullbackSmallBaseChangeAdjunction_comp :
    etaleModulePullbackSmallBaseChangeAdjunction B S hS (h ≫ g) hhg hrephg =
      (((etaleModulePullbackSmallBaseChangeAdjunction B S hS g hg hrepg).comp
                (etaleModulePullbackSmallBaseChangeAdjunction B S hS h hh hreph)).ofNatIsoRight
            (smallBaseChangeModulePushforwardCompIso B S hS h g hh hg hhg hreph hrepg
              hrephg)).ofNatIsoLeft
        (etaleModulePullbackComp B S hS h g hh hg hhg) :=
  (Stacks.CategoryTheory.eq_ofNatIsoRight_rightAdjointUniq
        (etaleModulePullbackSmallBaseChangeCompAdjunction B S hS h g hh hg hhg hreph hrepg)
        (etaleModulePullbackSmallBaseChangeAdjunction B S hS (h ≫ g) hhg hrephg)).trans
    (Stacks.CategoryTheory.ofNatIsoLeft_ofNatIsoRight
      ((etaleModulePullbackSmallBaseChangeAdjunction B S hS g hg hrepg).comp
        (etaleModulePullbackSmallBaseChangeAdjunction B S hS h hh hreph))
      (etaleModulePullbackComp B S hS h g hh hg hhg) _)

/-- **The square**: the composition comparison of the base-change direct images, followed by the
identification of the base-change direct image along the composite with the direct image of
Stacks 03LU, is the two identifications at the factors followed by the composition comparison
`AlgebraicGeometry.Space.modulePushforwardCompIso` of Stacks 03LU. -/
def SmallBaseChangeModulePushforwardCompSquare : Prop :=
  (smallBaseChangeModulePushforwardCompIso B S hS h g hh hg hhg hreph hrepg hrephg).hom ≫
      (smallBaseChangeModulePushforwardIso B S hS (h ≫ g) hhg hrephg).hom =
    (Functor.whiskerLeft (smallBaseChangeModulePushforward.{u, u} B S hS h hreph)
          (smallBaseChangeModulePushforwardIso B S hS g hg hrepg).hom ≫
        Functor.whiskerRight (smallBaseChangeModulePushforwardIso B S hS h hh hreph).hom
          (modulePushforward B S hS g)) ≫
      (modulePushforwardCompIso B S hS h g).hom

/-- **The two adjunctions of étale restriction along a composite agree if and only if the square
commutes.**  The left-hand side is the hypothesis `hu` of
`AlgebraicGeometry.Space.modulePullbackCompIso_hom_comp_etaleRestriction`, in its adjunction
form; the right-hand side is the identification of
`AlgebraicGeometry.Space.smallBaseChangeModulePushforwardCompIso` with
`AlgebraicGeometry.Space.modulePushforwardCompIso`.

Read forwards this is what the base-change route was for; read backwards it says the route is
circular, both comparisons of right adjoints occurring in the square being themselves
`CategoryTheory.Adjunction.rightAdjointUniq`.  See the module documentation. -/
theorem etaleModulePullbackCompAdjunction_eq_iff :
    etaleModulePullbackAdjunction B S hS (h ≫ g) hhg =
        etaleModulePullbackCompAdjunction B S hS h g hh hg hhg ↔
      SmallBaseChangeModulePushforwardCompSquare B S hS h g hh hg hhg hreph hrepg hrephg :=
  Stacks.CategoryTheory.eq_comp_ofNatIsoRight_ofNatIsoLeft_iff_rightAdjointUniq
    (etaleModulePullbackSmallBaseChangeAdjunction B S hS g hg hrepg)
    (etaleModulePullbackSmallBaseChangeAdjunction B S hS h hh hreph)
    (etaleModulePullbackSmallBaseChangeAdjunction B S hS (h ≫ g) hhg hrephg)
    (etaleModulePullbackAdjunction B S hS g hg) (etaleModulePullbackAdjunction B S hS h hh)
    (etaleModulePullbackAdjunction B S hS (h ≫ g) hhg)
    (etaleModulePullbackComp B S hS h g hh hg hhg) (modulePushforwardCompIso B S hS h g)

/-- The hypothesis `hu` of
`AlgebraicGeometry.Space.modulePullbackCompIso_hom_comp_etaleRestriction`, from the square. -/
theorem etaleModulePullbackCompAdjunction_unit_of_square
    (hsq : SmallBaseChangeModulePushforwardCompSquare B S hS h g hh hg hhg hreph hrepg hrephg) :
    (etaleModulePullbackCompAdjunction B S hS h g hh hg hhg).unit =
      (etaleModulePullbackAdjunction B S hS (h ≫ g) hhg).unit :=
  congrArg Adjunction.unit
    (((etaleModulePullbackCompAdjunction_eq_iff B S hS h g hh hg hhg hreph hrepg
      hrephg).2 hsq).symm)

/-- **The coherence of Stacks 03LU against Stacks 03LW for a representable pair, from the
square.**  The comparison of inverse images of Stacks 03LU followed by the identification of
Stacks 03LW is the identification of Stacks 03LW in each factor followed by the strict
composition of étale restrictions. -/
theorem modulePullbackCompIso_hom_comp_etaleRestriction_of_square
    (hsq : SmallBaseChangeModulePushforwardCompSquare B S hS h g hh hg hhg hreph hrepg hrephg) :
    (modulePullbackCompIso B S hS h g).hom ≫
        (modulePullbackIsoEtaleModulePullback B S hS (h ≫ g) hhg).hom =
      Functor.whiskerLeft (modulePullback B S hS g)
          (modulePullbackIsoEtaleModulePullback B S hS h hh).hom ≫
        Functor.whiskerRight (modulePullbackIsoEtaleModulePullback B S hS g hg).hom
            (etaleModulePullback.{u, u} B S hS h hh) ≫
          (etaleModulePullbackComp B S hS h g hh hg hhg).hom :=
  modulePullbackCompIso_hom_comp_etaleRestriction B S hS h g hh hg hhg
    (etaleModulePullbackCompAdjunction_unit_of_square B S hS h g hh hg hhg hreph hrepg hrephg
      hsq)

/-- **The converse: the square follows from the coherence.**  Together with
`AlgebraicGeometry.Space.modulePullbackCompIso_hom_comp_etaleRestriction_of_square` this says
that the square is the coherence, rewritten. -/
theorem smallBaseChangeModulePushforwardCompSquare_of_unit
    (hu : (etaleModulePullbackCompAdjunction B S hS h g hh hg hhg).unit =
      (etaleModulePullbackAdjunction B S hS (h ≫ g) hhg).unit) :
    SmallBaseChangeModulePushforwardCompSquare B S hS h g hh hg hhg hreph hrepg hrephg :=
  (etaleModulePullbackCompAdjunction_eq_iff B S hS h g hh hg hhg hreph hrepg hrephg).1
    (Adjunction.ext hu.symm)

/-- **The predicate the quasi-coherent descent files carry, from the square at every
representable triple.**

The second hypothesis, that *every* morphism of algebraic spaces is relatively representable, is
**not** available in this development and is not expected to be: it is here only to say what the
square at representable triples does and does not give.  The predicate quantifies over all étale
pairs, whereas the base-change adjunction exists only at representable ones, so a consumer that
has the square for representable morphisms — which is every morphism Stacks 03LY uses — has to
take the coherence from
`AlgebraicGeometry.Space.modulePullbackCompIso_hom_comp_etaleRestriction_of_square` at its own
chart morphisms, not from this predicate. -/
theorem modulePullbackCompIsoEtaleRestriction_of_square
    (hsq : ∀ {C' A' D' : AlgebraicSpaces B S hS} (h' : D' ⟶ A') (g' : A' ⟶ C')
      (hh' : IsEtale B S hS h'.hom) (hg' : IsEtale B S hS g'.hom)
      (hhg' : IsEtale B S hS (h' ≫ g').hom)
      (hreph' : yoneda.relativelyRepresentable h'.hom)
      (hrepg' : yoneda.relativelyRepresentable g'.hom)
      (hrephg' : yoneda.relativelyRepresentable (h' ≫ g').hom),
      SmallBaseChangeModulePushforwardCompSquare B S hS h' g' hh' hg' hhg' hreph' hrepg'
        hrephg')
    (hrep : ∀ {X' Y' : AlgebraicSpaces B S hS} (f : X' ⟶ Y'),
      yoneda.relativelyRepresentable f.hom) :
    QuasiCoherentDescent.ModulePullbackCompIsoEtaleRestriction B S hS :=
  modulePullbackCompIsoEtaleRestriction_of_unit B S hS fun h' g' hh' hg' hhg' ↦
    etaleModulePullbackCompAdjunction_unit_of_square B S hS h' g' hh' hg' hhg' (hrep h')
      (hrep g') (hrep (h' ≫ g'))
      (hsq h' g' hh' hg' hhg' (hrep h') (hrep g') (hrep (h' ≫ g')))

end AlgebraicGeometry.Space

end
