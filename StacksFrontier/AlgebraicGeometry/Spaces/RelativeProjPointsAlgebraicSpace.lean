module

public import StacksCore.Tactic.StacksAttribute
public import StacksFrontier.AlgebraicGeometry.Spaces.PointsAndCoverings.Retrofit
public import StacksFrontier.AlgebraicGeometry.Spaces.RelativeProj
public import StacksFrontier.AlgebraicGeometry.Spaces.Representable

/-!
# The relative Proj of an algebraic space is an algebraic space

In Situation 0849 let `X` be an algebraic space over a scheme `S` and `𝒜` a quasi-coherent
graded `𝒪_X`-algebra.  Stacks 084B asserts that the functor `F` of quadruples of Stacks 084A is
an algebraic space, and that for every morphism `g : Z ⟶ X` with `Z` a scheme there is a
canonical isomorphism `Proj_Z(g^*𝒜) = Z ×_X F`, compatibly with further base change.

The source proves the first assertion *from* the second: "it suffices to prove the second
assertion", because the second says that the structure morphism `π : F ⟶ X` becomes a scheme
after every base change to a scheme, that is that `π` is representable, and Stacks 02WY then
makes `F` an algebraic space.  This file carries out exactly that step, and proves the
base-change compatibility of the third clause.

The second assertion is `AlgebraicGeometry.Space.RelativeProjPoints`, stated in
`StacksFrontier/AlgebraicGeometry/Spaces/RelativeProj.lean`: for every object `T` of the site and
every `T`-point `f` of `X`, an object of the site whose scheme is the relative Proj of
Stacks 01NQ of the restricted algebra, together with a cartesian square identifying it with
`T ×_X F`.  Nothing in this file assumes anything about `F` beyond those squares.

Every result below takes an `AlgebraicGeometry.Space.RelativeProjPoints` as a hypothesis, and
its `isPullback` fields are the cartesian squares the second assertion of Stacks 084B asserts to
exist.  So these results are the implications `084B(2) ⟹ 084B(1)` and `084B(2) ⟹ 084B(3)`.

## Main results

* `AlgebraicGeometry.Space.RelativeProjPoints.relativelyRepresentable`: the structure morphism
  of the relative Proj is a representable transformation of functors.  This is the second
  assertion of Stacks 084B read as a representability statement; it is the hypothesis of
  Stacks 02WY.
* `AlgebraicGeometry.Space.RelativeProjPoints.isAlgebraicSpace`: the relative Proj is an
  algebraic space over `S`, as soon as its base is.  This is the first assertion of
  Stacks 084B *given its second*, which is the hypothesis.
* `AlgebraicGeometry.Space.RelativeProjPoints.fibreComparison` is the comparison morphism
  `T' ×_X F ⟶ T ×_X F` over a morphism `h : T' ⟶ T` of test objects, and
  `…isPullback_fibreComparison` exhibits `T' ×_X F` as `T' ×_T (T ×_X F)`.  This is the
  compatibility clause of Stacks 084B for the squares the hypothesis supplies.
* `AlgebraicGeometry.Space.RelativeProjPoints.isPullback_fibreComparison_site` and
  `…isPullback_map_fibreComparison` are the same cartesian square in the big fppf category
  over `S` and in schemes.

## Implementation notes

**Why the first assertion needs the second.**  `AlgebraicGeometry.IsAlgebraicSpace` asks for a
sheaf with representable diagonal carrying a surjective étale scheme atlas, and the only route
to those three from the data of the relative Proj is through the base changes: a representable
transformation to an algebraic space has an algebraic space as its source, which is
`AlgebraicGeometry.isAlgebraicSpace_of_relativelyRepresentable` (Stacks 02WY).  The shape
of `CategoryTheory.Functor.relativelyRepresentable` — for every object `a` of the site and every
`g : yoneda.obj a ⟶ X` an object `b`, a morphism `b ⟶ a` and a cartesian square — is the shape
of the fields of `AlgebraicGeometry.Space.RelativeProjPoints` on the nose, so
`relativelyRepresentable` is those fields repackaged, and it is the whole of the reduction the
source performs.

**The base-change compatibility is a consequence, not a datum.**  The source states the
compatibility of the isomorphism of its second assertion with further base change and omits the
verification.  Here it is proved: `T' ×_X F` and `T ×_X F` are base changes of `π` along
`yoneda.map h ≫ f` and along `f`, so the comparison morphism between them is the one the
cartesian square over `f` produces, and pullback pasting
(`CategoryTheory.IsPullback.paste_horiz_iff`) turns the two outer squares into the inner square
`T' ×_X F = T' ×_T (T ×_X F)`.  No further hypothesis enters.

**The squares are stated for the fibres.**  Reading the inner square as the isomorphism
`Proj_{T'}((h ∘ g)^*𝒜) = T' ×_T Proj_T(g^*𝒜)` of graded algebras needs the comparison
`h^*(g^*𝒜) = (h ∘ g)^*𝒜` between the restrictions of `𝒜` to two scheme points of `X`, which is
itself a clause of Stacks 084B.  So the squares below are stated for the objects
`AlgebraicGeometry.Space.RelativeProjPoints.fibre` and their structure morphisms, where they are
hypothesis-free, and the field `AlgebraicGeometry.Space.RelativeProjPoints.fibreIso` identifies
those objects with the relative Projs of Stacks 01NQ.

## References

* [Stacks Project, Tag 084B](https://stacks.math.columbia.edu/tag/084B)
* [Stacks Project, Tag 084A](https://stacks.math.columbia.edu/tag/084A)
* [Stacks Project, Tag 0849](https://stacks.math.columbia.edu/tag/0849)
* [Stacks Project, Tag 02WY](https://stacks.math.columbia.edu/tag/02WY)
* [Stacks Project, Tag 01NQ](https://stacks.math.columbia.edu/tag/01NQ)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits

universe u

namespace AlgebraicGeometry.Space

namespace RelativeProjPoints

variable {B : BigFppfSite.{u}} {S : Scheme.{u}} {hS : B.Contains S}
    {X P : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u} {π : P ⟶ X}
    (d : RelativeProjPoints B S hS π)

/-! ### The structure morphism is representable -/

include d in
/-- **The structure morphism of the relative Proj is a representable transformation.**

For every object `T` of the site and every `T`-point `f` of `X`, the base change `T ×_X P` is
the object `AlgebraicGeometry.Space.RelativeProjPoints.fibre T f` of the site, by the cartesian
square the data carry.  That is exactly the shape of
`CategoryTheory.Functor.relativelyRepresentable`. -/
theorem relativelyRepresentable : yoneda.relativelyRepresentable π := by
  intro T f
  exact ⟨d.fibre T f, d.fibreHom T f, d.fibreToSpace T f, d.isPullback T f⟩

include d in
/-- **The first assertion of Stacks 084B.** The relative Proj is an algebraic space over `S`.

This is the source's own proof: the second assertion makes the structure morphism `π`
representable, and a representable transformation to an algebraic space has an algebraic space
as its source, which is Stacks 02WY. -/
theorem isAlgebraicSpace (hX : IsAlgebraicSpace B S hS X) : IsAlgebraicSpace B S hS P :=
  isAlgebraicSpace_of_relativelyRepresentable B S hS π d.relativelyRepresentable hX

/-! ### Compatibility with further base change -/

/-- **The comparison morphism of the base-change compatibility.**

For a morphism `h : T' ⟶ T` of test objects and a `T`-point `f` of `X`, the morphism
`T' ×_X P ⟶ T ×_X P` the cartesian square over `f` produces from the structure morphism of
`T' ×_X P` and from `h`. -/
def fibreComparison (T : BigFppfOver B S hS) (f : yoneda.obj T ⟶ X)
    {T' : BigFppfOver B S hS} (h : T' ⟶ T) :
    d.fibre T' (yoneda.map h ≫ f) ⟶ d.fibre T f :=
  Yoneda.fullyFaithful.preimage
    ((d.isPullback T f).lift (d.fibreToSpace T' (yoneda.map h ≫ f))
      (yoneda.map (d.fibreHom T' (yoneda.map h ≫ f)) ≫ yoneda.map h)
      (by rw [(d.isPullback T' (yoneda.map h ≫ f)).w, Category.assoc]))

/-- The comparison morphism lies over the morphism to `P`. -/
@[simp] theorem map_fibreComparison_comp_fibreToSpace (T : BigFppfOver B S hS)
    (f : yoneda.obj T ⟶ X) {T' : BigFppfOver B S hS} (h : T' ⟶ T) :
    yoneda.map (d.fibreComparison T f h) ≫ d.fibreToSpace T f =
      d.fibreToSpace T' (yoneda.map h ≫ f) := by
  rw [fibreComparison, Yoneda.fullyFaithful.map_preimage]
  exact (d.isPullback T f).lift_fst _ _ _

/-- The comparison morphism lies over `h`. -/
theorem fibreComparison_comp_fibreHom (T : BigFppfOver B S hS) (f : yoneda.obj T ⟶ X)
    {T' : BigFppfOver B S hS} (h : T' ⟶ T) :
    d.fibreComparison T f h ≫ d.fibreHom T f =
      d.fibreHom T' (yoneda.map h ≫ f) ≫ h := by
  apply Yoneda.fullyFaithful.map_injective
  rw [Functor.map_comp, Functor.map_comp, fibreComparison, Yoneda.fullyFaithful.map_preimage]
  exact (d.isPullback T f).lift_snd _ _ _

/-- **The base-change compatibility of Stacks 084B.**

The base change of the relative Proj along a `T'`-point of `X` factoring through a `T`-point `f`
is the base change along `h : T' ⟶ T` of the base change along `f`:
`T' ×_X P = T' ×_T (T ×_X P)`.

The source states this compatibility and omits the verification.  Here it is pullback pasting:
the two outer squares are the cartesian squares of the data over `yoneda.map h ≫ f` and over
`f`, and the comparison morphism was defined to make the triangle on the `P` side commute. -/
theorem isPullback_fibreComparison (T : BigFppfOver B S hS) (f : yoneda.obj T ⟶ X)
    {T' : BigFppfOver B S hS} (h : T' ⟶ T) :
    IsPullback (yoneda.map (d.fibreComparison T f h))
      (yoneda.map (d.fibreHom T' (yoneda.map h ≫ f)))
      (yoneda.map (d.fibreHom T f)) (yoneda.map h) := by
  refine ((d.isPullback T f).paste_horiz_iff ?_).mp ?_
  · rw [← Functor.map_comp, fibreComparison_comp_fibreHom, Functor.map_comp]
  · rw [map_fibreComparison_comp_fibreToSpace]
    exact d.isPullback T' (yoneda.map h ≫ f)

/-- The base-change compatibility, in the big fppf category over `S`.  The square of the
previous result consists of represented presheaves and of morphisms in the image of the Yoneda
embedding, which is fully faithful, so it comes from a cartesian square of the site. -/
theorem isPullback_fibreComparison_site (T : BigFppfOver B S hS) (f : yoneda.obj T ⟶ X)
    {T' : BigFppfOver B S hS} (h : T' ⟶ T) :
    IsPullback (d.fibreComparison T f h) (d.fibreHom T' (yoneda.map h ≫ f))
      (d.fibreHom T f) h :=
  IsPullback.of_map_of_faithful yoneda (d.isPullback_fibreComparison T f h)

/-- The base-change compatibility, read on the underlying schemes: the scheme of `T' ×_X P` is
the fibre product of the scheme of `T ×_X P` with the scheme of `T'` over the scheme of `T`. -/
theorem isPullback_map_fibreComparison (T : BigFppfOver B S hS) (f : yoneda.obj T ⟶ X)
    {T' : BigFppfOver B S hS} (h : T' ⟶ T) :
    IsPullback ((BigFppfOver.toScheme B S hS).map (d.fibreComparison T f h))
      ((BigFppfOver.toScheme B S hS).map (d.fibreHom T' (yoneda.map h ≫ f)))
      ((BigFppfOver.toScheme B S hS).map (d.fibreHom T f))
      ((BigFppfOver.toScheme B S hS).map h) :=
  (BigFppfOver.toScheme B S hS).map_isPullback (d.isPullback_fibreComparison_site T f h)

end RelativeProjPoints

end AlgebraicGeometry.Space

end
