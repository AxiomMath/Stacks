module

public import StacksFrontier.AlgebraicGeometry.Spaces.BoundedDirectImageAlgebraFactorization

/-!
# The universal property of Stacks 081V at the structure sheaf

By `AlgebraicGeometry.Space.isEquivalence_boundedPushforwardAlgebraFunctor_iff_bijective` the
anti-equivalence clause of Stacks 081V, on the target cut down to the quasi-coherent algebras
satisfying `AlgebraicGeometry.Space.AlgebraSheaf.SectionsBelowCutoff`, is the assertion that for
all `Y`, `Z` affine over an algebraic space `X` the direct image
`f ↦ f_*` is a bijection from the morphisms `Y ⟶ Z` over `X` onto the morphisms
`Z_* 𝒪_Z ⟶ Y_* 𝒪_Y` of `𝒪_X`-algebras — the universal property of the relative spectrum.  That
assertion is proved here in the one case the development can reach unconditionally, `Z = X` over
itself, where the algebra in question is the structure sheaf: `\underline{Spec}_X(𝒪_X) = X`.

Nothing here is a step towards the general case, and the general case is not a formal consequence
of it; see the implementation notes for what the general case is missing and where the
corresponding scheme-level statement is proved.

## Main results

* `AlgebraicGeometry.Space.isInitialPushforwardAlgebraMkId`: `(𝟙_X)_* 𝒪_X` is the initial sheaf
  of commutative `𝒪_X`-algebras.
* `AlgebraicGeometry.Space.bijective_pushforwardAlgebraMap_mkId`: **the universal property of
  Stacks 081V at the structure sheaf.**  For an arbitrary algebraic space `Y` over `X` the direct
  image is a bijection from the morphisms `Y ⟶ X` over `X` onto the morphisms
  `(𝟙_X)_* 𝒪_X ⟶ Y_* 𝒪_Y` of `𝒪_X`-algebras.  No affineness is required of `Y`, matching the
  scheme-level `Stacks.AffineAlgebraEquivalence.overHomEquivAlgebraHom`, whose only hypothesis is
  affineness of the *target*.

## Implementation notes

**Both sides are singletons, and that is the whole proof.**  `X` over itself is the terminal
object of `CategoryTheory.Over X` (`CategoryTheory.Over.mkIdTerminal`), so the source of the map
has exactly one element.  The target has exactly one element because `(𝟙_X)_* 𝒪_X` is initial:
the identity clause of Stacks 03G8 at the level of algebras,
`AlgebraicGeometry.Space.pushforwardAlgebraIdAlgebraIso`, identifies it with
`AlgebraicGeometry.Space.unitAlgebra X`, and a morphism of algebra sheaves out of
`AlgebraicGeometry.Space.unitAlgebra X` is its target's own structure-algebra map, by
`AlgebraicGeometry.Space.unitAlgebra_hom_right`.  So the bijection carries no information beyond
those two facts; what it is worth is that it is a case of the clause that is *not* vacuous and
*not* excluded by the size obstruction, and that it is the case the rest of the clause has to
agree with.

`AlgebraicGeometry.Space.isInitialUnitQuasicoherentAlgebra` is the same initiality for
`AlgebraicGeometry.Space.unitQuasicoherentAlgebra` in
`AlgebraicGeometry.Space.QuasicoherentAlgebra X`; the statement below is in
`AlgebraicGeometry.Space.AlgebraSheaf` and about the direct image rather than about
`AlgebraicGeometry.Space.unitAlgebra`, which is what the bijection needs, since
`AlgebraicGeometry.Space.pushforwardAlgebraMap` lands in `AlgebraicGeometry.Space.AlgebraSheaf`.

**What the general case needs.**  The general clause is *not* missing for want of a
formal argument, and it is not blocked on the size obstruction either — the obstruction is about
essential surjectivity alone, and
`AlgebraicGeometry.Space.full_boundedPushforwardAlgebraFunctor_iff` together with
`AlgebraicGeometry.Space.faithful_boundedPushforwardAlgebraFunctor_iff` says cutting the target
down affects full faithfulness not at all.  **Exactly one input is absent** from the
library: the sections at an étale chart `V` of `X` of
`AlgebraicGeometry.Space.pushforwardRingMap` for a morphism `f : Y ⟶ Z` over `X` are nowhere
identified with the ring map which the base-changed morphism `Y ×_X V ⟶ Z ×_X V` of schemes
induces on regular functions.  Everything around that identification *is* proved: the object
half `AlgebraicGeometry.Space.pushforwardAlgebraSectionsIso`, which is Stacks 03G8 in the shape
`AlgebraicGeometry.Space.smallEtaleRingedToposHom_representableRing` evaluated at `V`; the bottom
edge `AlgebraicGeometry.Space.fSharp_app_comp_pushforwardAlgebraSectionsIso`, which reads the
structure map at `V` as pullback of regular functions along the cartesian projection
`Y ×_X V ⟶ V`; the triangle those two give for a morphism over `X`,
`AlgebraicGeometry.Space.cartesianProjectionAppTop_comp_pushforwardRingMap_app`, which says the
chart value of `AlgebraicGeometry.Space.pushforwardRingMap f` is a map of `Γ(V)`-algebras; and
the end of the argument, `AlgebraicGeometry.Space.isAffine_smallBaseChange_obj` with
`AlgebraicGeometry.Space.SmallEtale.coversTop_affineCharts` feeding
`AlgebraicGeometry.ext_of_isAffine`.  Being a map of `Γ(V)`-algebras is strictly weaker than
being `(f ×_X V)^*`, however, and only the latter forces the restricted morphisms equal.  The
chart value of the two factors of `AlgebraicGeometry.Space.pushforwardRingMap` that carry the
composition, read against `AlgebraicGeometry.Space.smallBaseChangeComp`, is proved as
`AlgebraicGeometry.Space.smallBaseChangeComp_smallEtaleRingedToposHom_compRingIso`; what the
identification still needs is the other two factors and, before them, a name for the base-changed
morphism of schemes `Y ×_X V ⟶ Z ×_X V`, which is not a declaration of this development.  See the
implementation notes of
`StacksFrontier.AlgebraicGeometry.Spaces.DirectImageAlgebraChartSectionsMorphism` and of
`StacksFrontier.AlgebraicGeometry.Spaces.BoundedAffineAlgebraAntiEquivalence` for the route.

The rest of the scheme-level argument has counterparts here:

* a surjective étale atlas `b : h_U ⟶ X` exists by
  `AlgebraicGeometry.IsAlgebraicSpace.exists_atlas`, and since `b` is étale, `U` is an object of
  `AlgebraicGeometry.Space.SmallEtale B S hS X.1`, so it is a chart at which these sheaves may be
  evaluated.  Two morphisms of algebraic spaces agreeing after precomposition with such an atlas
  are equal, by `AlgebraicGeometry.Space.hom_ext_of_etale_atlas` — which requires only that
  source and target be sheaves, and representability of neither.
  (`AlgebraicGeometry.Space.hom_ext_of_familyImage_cover` needs no representable base either:
  its covering hypothesis is arbitrary, and
  it is only the helper `AlgebraicGeometry.Space.familyImage_cover` which builds that hypothesis
  from a morphism to a representable.)
* a chart is itself an algebraic space, by
  `AlgebraicGeometry.isAlgebraicSpace_yoneda`, and `AlgebraicGeometry.Space.chartOver` packages
  it as an object of `CategoryTheory.Over X` already, so
  `AlgebraicGeometry.Space.affineOverBaseChange` restricts an object of
  `AlgebraicGeometry.Space.AffineOver X` to it, with
  `AlgebraicGeometry.Space.affineOverBaseChange_isPullback` the cartesian square; the restriction
  is a scheme affine over the chart because an affine morphism is relatively representable,
  `AlgebraicGeometry.Space.relativelyRepresentable_of_isAffineHom`.  (What
  `AlgebraicGeometry.Space.AffineOver B S hS X` does
  lack is an action on *morphisms*: `AlgebraicGeometry.Space.affineOverBaseChange` is defined on
  objects only.  That is routine from
  `AlgebraicGeometry.Space.affineOverBaseChange_isPullback` and is not what blocks the argument,
  since the missing naturality statement above is phrased through
  `AlgebraicGeometry.Space.smallBaseChange` and does not pass through it.)

**The scheme-level statement is proved, in full.**
`Stacks.AffineAlgebraEquivalence.overHomEquivAlgebraHom`
is the universal property of the relative spectrum for schemes, with
`Stacks.AffineAlgebraEquivalence.faithful_affinePushforwardAlgebraFunctor` and
`Stacks.AffineAlgebraEquivalence.full_affinePushforwardAlgebraFunctor` the two halves it is built
from, and `Stacks.AffineAlgebraEquivalence.affineAlgebraAntiEquivalence` the resulting
anti-equivalence of Stacks 01SA with its base change.  So the gap is the passage from a scheme
base to an algebraic-space base, and it is the single naturality statement named above and not
the mathematics of the tag.
Nothing here carries Stacks 081V: one object of the source category is not the tag's assertion.

## References

* [Stacks Project, Tag 081V](https://stacks.math.columbia.edu/tag/081V)
* [Stacks Project, Tag 081W](https://stacks.math.columbia.edu/tag/081W)
* [Stacks Project, Tag 03G8](https://stacks.math.columbia.edu/tag/03G8)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits Opposite

universe u

namespace AlgebraicGeometry.Space

variable (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)

/-- **`(𝟙_X)_* 𝒪_X` is the initial sheaf of commutative `𝒪_X`-algebras.**  The identity clause of
Stacks 03G8 at the level of algebras, `AlgebraicGeometry.Space.pushforwardAlgebraIdAlgebraIso`,
identifies it with `AlgebraicGeometry.Space.unitAlgebra X`, and a morphism of algebra sheaves out
of the latter is its target's own structure-algebra map by
`AlgebraicGeometry.Space.unitAlgebra_hom_right`, so there is exactly one of them. -/
def isInitialPushforwardAlgebraMkId (X : AlgebraicSpaces B S hS) :
    IsInitial (pushforwardAlgebra B S hS (Over.mk (𝟙 X))) :=
  IsInitial.ofUniqueHom
    (fun A => (pushforwardAlgebraIdAlgebraIso B S hS X).hom ≫ ⟨A.hom, fun _ _ => rfl⟩)
    fun A m => by
      have h : (pushforwardAlgebraIdAlgebraIso B S hS X).inv ≫ m =
          (⟨A.hom, fun _ _ => rfl⟩ : unitAlgebra B S hS X ⟶ A) :=
        AlgebraSheaf.Hom.ext (unitAlgebra_hom_right B S hS _)
      rw [← h, Iso.hom_inv_id_assoc]

/-- **The universal property of the anti-equivalence of Stacks 081V at the structure sheaf.**  For
an arbitrary algebraic space `Y` over `X`, the direct image `f ↦ f_*` is a bijection from the
morphisms `Y ⟶ X` over `X` onto the morphisms `(𝟙_X)_* 𝒪_X ⟶ Y_* 𝒪_Y` of sheaves of commutative
`𝒪_X`-algebras.

Taking `Y` affine over `X`, this is the case `Z = X` over itself of the first clause of
`AlgebraicGeometry.Space.isEquivalence_boundedPushforwardAlgebraFunctor_iff_bijective`, which is
the whole anti-equivalence clause of the tag on the bounded target.  The clause for a general `Z`
is not proved in this development and does not follow from this; see the implementation notes of
this file for the one input it is missing and for the scheme-level statement,
`Stacks.AffineAlgebraEquivalence.overHomEquivAlgebraHom`, which is proved in full. -/
theorem bijective_pushforwardAlgebraMap_mkId (X : AlgebraicSpaces B S hS) (Y : Over X) :
    Function.Bijective
      (fun f : Y ⟶ Over.mk (𝟙 X) => pushforwardAlgebraMap B S hS f) :=
  ⟨fun f g _ => Over.mkIdTerminal.hom_ext f g,
    fun φ => ⟨Over.mkIdTerminal.from Y,
      (isInitialPushforwardAlgebraMkId B S hS X).hom_ext _ φ⟩⟩

end AlgebraicGeometry.Space

end
