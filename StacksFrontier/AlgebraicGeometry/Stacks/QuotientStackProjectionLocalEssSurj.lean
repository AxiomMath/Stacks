module

public import StacksFrontier.AlgebraicGeometry.Spaces.Groupoids.QuotientStackProjection
public import StacksFrontier.AlgebraicGeometry.Stacks.LocalEssentialSurjectivity
public import StacksFrontier.AlgebraicGeometry.Stacks.RelativePropertyDescent
public import StacksFrontier.AlgebraicGeometry.Stacks.RepresentabilityInvariance
public import StacksFrontier.CategoryTheory.TwoFibreProduct.CatFiberedInGroupoids

/-!
# The quotient-stack projection is locally essentially surjective

Let `G = (U, R, s, t, c)` be a groupoid in algebraic spaces over an algebraic space `B` over a
scheme `S` of a big fppf site, let `[U/R]` be its quotient stack (Stacks 044Q) and let
`π : S_U ⟶ [U/R]` be the canonical projection (Stacks 044R). This module records that `π` is
*locally essentially surjective*: every object of a fibre `[U/R]_T` becomes, after restriction to
a covering sieve of `T`, isomorphic to the image under `π` of an object of `S_U`.

That is the hypothesis `AlgebraicGeometry.Stack.hasRelativeProperty_of_baseChange`
(**Stacks 045D**) and
`AlgebraicGeometry.Stack.hasRelativeProperty_of_prop_representingMap_of_localEssSurj` consume, and
it is the only one of their hypotheses which is about `π` as a *stackification* map rather than
about a single base change of it. For `π` it is not new mathematics: it is clause (2)
of Stacks 02ZN for the quotient, that is part (1) of Stacks 044X, proved as
`AlgebraicGeometry.Stack.essImage_toQuotientStack`. What this module does is move that clause from
`AlgebraicGeometry.Stack.toQuotientStack`, where it is stated, to `π`, where it is used, and then
convert the essential-image form in which both the stackification and Stacks 046N state it into
the lifting form in which Stacks 045D consumes it.

## Main definitions

* `AlgebraicGeometry.Stack.liftedObjectSpace`: the fibred category of the object space with its
  morphism universe raised to the one the quotient stack lives at.
* `AlgebraicGeometry.Stack.objectSpaceLiftDown`: the canonical 1-morphism down to the object space
  itself.
* `AlgebraicGeometry.Stack.quotientStackProjectionHom`: the projection of Stacks 044R as a
  1-morphism of categories fibred in groupoids, which is what the relative-property API takes.
* `AlgebraicGeometry.Stack.prestackObjectLift`: the object of the lifted object space which the
  projection carries to a prescribed object of the pointwise groupoid fibration.

## Main results

* `CategoryTheory.Functor.exists_isHomLift_of_essImage`: the generic conversion, for a functor
  strictly over a base with prefibered target, from "the chosen pullback of `y` along `k` is in the
  essential image on fibres" to "some object of the source maps to `y` by a morphism lying over
  `k`".
* `AlgebraicGeometry.Stack.localEssSurj_of_essImage`: the same conversion for a 1-morphism of
  categories fibred in groupoids over the big fppf site, at the covering-sieve level, taking the
  essential-image form of local essential surjectivity to the form Stacks 045D consumes.
* `AlgebraicGeometry.Stack.essImage_quotientStackProjectionHom`: part (1) of Stacks 044X carried
  from `toQuotientStack` to the projection.
* `AlgebraicGeometry.Stack.localEssSurj_quotientStackProjectionHom`: the projection is locally
  essentially surjective, in the form Stacks 045D consumes.
* `AlgebraicGeometry.Stack.isRepresentableByAlgebraicSpaces_quotientStackProjectionHom`:
  representability of the projection passes to its universe-lifted form, by Stacks 0457.
* `AlgebraicGeometry.Stack.hasRelativeProperty_quotientStackProjectionHom_of_baseChange`:
  Stacks 045D for this morphism with that hypothesis discharged — one base change of the
  projection along itself decides every relative property of it.
* `AlgebraicGeometry.Stack.quotientStackProjectionSelfSquare` and
  `AlgebraicGeometry.Stack.isTwoFibreProduct_quotientStackProjectionSelfSquare`: the canonical
  2-fibre product square of the projection with itself, and its universal property.
* `AlgebraicGeometry.Stack.hasRelativeProperty_quotientStackProjectionHom_of_selfSquare`: the
  same with that square supplied too, so that **exactly two** arguments remain — representability
  (Stacks 04WZ) and the relative property of the one base change (Stacks 04M9).

## Implementation notes

**Why the morphism universe has to be raised.** `AlgebraicGeometry.Stack.quotientStackProjection`
is a `CategoryTheory.BasedFunctor`, which permits its source and target to have morphisms in
different universes, and they do: the object space `AlgebraicGeometry.Stack.fibredCategory` has
morphisms in `Type u` while the quotient stack, being built by stackification, has them in
`Type (u + 1)`. Both `CategoryTheory.Functor.fiberFunctorOfCompEq` — in which the stackification
clause is stated — and `CatFiberedInGroupoids`, in which the relative-property API is stated,
require one common morphism universe. `liftedObjectSpace` supplies it by `CategoryTheory.ULiftHom`,
which is an equivalence commuting *strictly* with the projection to the site, so
`objectSpaceLiftDown` has `rfl` for its structural equation and the base category, the fppf
topology and the `Type u` algebraic-space witnesses are all unchanged.

**Why the lift of a prestack object is strict.** `prestackObjectLift` is not merely an essential
preimage. The fibres of `AlgebraicGeometry.Stack.fibredCategory` are *discrete*, the fibres of the
pointwise groupoid fibration have the same objects, and `ULiftHom` changes no objects at all; so
`AlgebraicGeometry.Stack.pointwiseObjectInclusion` followed by the universe lift is a *bijection*
on the objects of each fibre, with `prestackObjectLift` as its inverse. Hence
`CatFiberedInGroupoids.homFunctor (quotientStackProjectionHom G)` and
`AlgebraicGeometry.Stack.toQuotientStack` agree on the nose there, and
`essImage_quotientStackProjectionHom` transports the isomorphism supplied by
`essImage_toQuotientStack` without a comparison.

**The composition of the two hom lifts.** A morphism of a fibre lies over the identity, and the
chosen pullback map of a prefibered functor lies over the morphism it is chosen along; so the
composite of the essential-image isomorphism with the chosen pullback map lies over that morphism,
by `CategoryTheory.Functor.isHomLift_comp_of_isHomLift_id`. That is the whole of
`exists_isHomLift_of_essImage`, and it is why no cartesian-lift uniqueness argument appears.

## References

* [Stacks Project, Tag 02ZN](https://stacks.math.columbia.edu/tag/02ZN)
* [Stacks Project, Tag 044Q](https://stacks.math.columbia.edu/tag/044Q)
* [Stacks Project, Tag 044R](https://stacks.math.columbia.edu/tag/044R)
* [Stacks Project, Tag 044X](https://stacks.math.columbia.edu/tag/044X)
* [Stacks Project, Tag 045D](https://stacks.math.columbia.edu/tag/045D)
* [Stacks Project, Tag 0457](https://stacks.math.columbia.edu/tag/0457)
* [Stacks Project, Tag 046N](https://stacks.math.columbia.edu/tag/046N)
* [Stacks Project, Tag 04M9](https://stacks.math.columbia.edu/tag/04M9)
* [Stacks Project, Tag 04WZ](https://stacks.math.columbia.edu/tag/04WZ)
* [Stacks Project, Tag 06FH](https://stacks.math.columbia.edu/tag/06FH)
-/

@[expose] public section

open CategoryTheory

namespace CategoryTheory.Functor

universe v₁ v₂ u₁ u₂ u₃

variable {𝒞 : Type u₁} [Category.{v₁} 𝒞] {𝒳 : Type u₂} [Category.{v₂} 𝒳]
  {𝒴 : Type u₃} [Category.{v₂} 𝒴]

/-- **The essential-image form of a local lift gives a lift.** Let `F : 𝒳 ⥤ 𝒴` be a functor
strictly over a base `𝒞`, with `q : 𝒴 ⥤ 𝒞` prefibered, let `y` be an object of the fibre of `𝒴`
over `U` and let `k : V ⟶ U`. If the chosen pullback of `y` along `k` is in the essential image of
the functor `F` induces on the fibres over `V`, then there is an object `z` of `𝒳` and a morphism
`F z ⟶ y` lying over `k`.

The morphism is the essential-image isomorphism, which lies over `𝟙 V` because it is a morphism of
the fibre over `V`, followed by the chosen pullback map of `q` at `y` along `k`, which lies over
`k`. -/
theorem exists_isHomLift_of_essImage {p : 𝒳 ⥤ 𝒞} {q : 𝒴 ⥤ 𝒞} [q.IsPreFibered]
    {F : 𝒳 ⥤ 𝒴} (hF : F ⋙ q = p) {U V : 𝒞} (y : q.Fiber U) (k : V ⟶ U)
    (h : (fiberFunctorOfCompEq hF V).essImage (pullbackFiber q y k)) :
    ∃ (z : 𝒳) (φ : F.obj z ⟶ y.1), q.IsHomLift k φ := by
  obtain ⟨z, ⟨e⟩⟩ := h
  exact ⟨z.1, Fiber.fiberInclusion.map e.hom ≫ IsPreFibered.pullbackMap y.2 k,
    isHomLift_comp_of_isHomLift_id q _ _ k e.hom.2
      (by infer_instance : q.IsHomLift k (IsPreFibered.pullbackMap y.2 k))⟩

end CategoryTheory.Functor

namespace AlgebraicGeometry.Stack

universe u v w t

section Generic

variable (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)

/-- **Local essential surjectivity, from the essential-image form to the lifting form.** A
1-morphism `g : 𝒲 ⟶ 𝒴` of categories fibred in groupoids over the big fppf site of `S` along
which every chosen pullback of an object of a fibre of `𝒴`, over the members of some covering
sieve, is in the essential image of `g` on fibres, is locally essentially surjective in the sense
of Stacks 045D: every object of a fibre of `𝒴` receives, over the members of some covering sieve,
a morphism from the image of an object of `𝒲`.

The two are the same hypothesis in two spellings: the stackification clause of Stacks 02ZN and
the criterion of Stacks 046N produce the first, and
`AlgebraicGeometry.Stack.hasRelativeProperty_of_baseChange` consumes the second. -/
theorem localEssSurj_of_essImage
    {𝒲 𝒴 : CatFiberedInGroupoids.{u, v, u + 1, w} (BigFppfOver B S hS)}
    [𝒴.val.p.IsPreFibered] (g : 𝒲 ⟶ 𝒴)
    (H : ∀ (U : BigFppfOver B S hS) (x : 𝒴.val.p.Fiber U),
      ∃ R ∈ BigFppfOver.topology B S hS U,
        ∀ ⦃V : BigFppfOver B S hS⦄ ⦃k : V ⟶ U⦄, R.arrows k →
          (Functor.fiberFunctorOfCompEq
            (CatFiberedInGroupoids.homFunctor_comp_p g) V).essImage
            (Functor.pullbackFiber 𝒴.val.p x k))
    (U : BigFppfOver B S hS) (y : 𝒴.val.p.Fiber U) :
    ∃ R ∈ BigFppfOver.topology B S hS U,
      ∀ ⦃V : BigFppfOver B S hS⦄ ⦃k : V ⟶ U⦄, R.arrows k →
        ∃ (z : 𝒲.val.obj) (φ : (CatFiberedInGroupoids.homFunctor g).obj z ⟶ y.1),
          𝒴.val.p.IsHomLift k φ := by
  obtain ⟨R, hR, hess⟩ := H U y
  refine ⟨R, hR, ?_⟩
  intro V k hk
  exact Functor.exists_isHomLift_of_essImage
    (CatFiberedInGroupoids.homFunctor_comp_p g) y k (hess hk)

end Generic

section Projection

variable {C : BigFppfSite.{u}} {S : Scheme.{u}} {hS : C.Contains S}
  {B : AlgebraicSpaces C S hS}

/-- The fibred category of an algebraic space, with only its morphism universe raised to the one
the quotient stack lives at, and read as a category fibred in groupoids. The objects, the base
category and the fppf topology are unchanged.

This is the general form; `AlgebraicGeometry.Stack.liftedObjectSpace` is its value at the object
space of a groupoid, and `AlgebraicGeometry.Stack.liftedFibredCategory` is the underlying
category over the site. Nothing in the body mentions a groupoid, which is why the arrow space of
a groupoid — needed to base change the relation of a presentation along a representable
1-morphism, Stacks 04Y6 — is served by the same declaration rather than by a copy. -/
def liftedSpace (X : AlgebraicSpaces C S hS) :
    CatFiberedInGroupoids.{u, u + 1, u + 1, u + 1} (BigFppfOver C S hS) :=
  .mk (BasedCategory.ofFunctor
    ((ULiftHom.down : ULiftHom.{u + 1}
      (fibredCategory C S hS X.obj).val.obj ⥤ _) ⋙
      (fibredCategory C S hS X.obj).val.p))
    (isFiberedInGroupoids_uliftHom _ (fibredCategory C S hS X.obj).property)

/-- The fibred category of the object space of a groupoid in algebraic spaces, with only its
morphism universe raised to the one the quotient stack lives at. The objects, the base category and
the fppf topology are unchanged.

A definitional specialisation of `AlgebraicGeometry.Stack.liftedSpace`: it unfolds to it by `rfl`,
so a consumer may use either. -/
def liftedObjectSpace (G : GroupoidInAlgebraicSpaces C S hS B) :
    CatFiberedInGroupoids.{u, u + 1, u + 1, u + 1} (BigFppfOver C S hS) :=
  liftedSpace G.objects

/-- The canonical 1-morphism from the universe lift of an algebraic space's fibred category down
to that fibred category. It commutes strictly with the projection to the site, which is why its
structural equation is `rfl`. -/
def liftedSpaceDown (X : AlgebraicSpaces C S hS) :
    (liftedSpace X).val ⥤ᵇ (fibredCategory C S hS X.obj).val :=
  ⟨(ULiftHom.down : ULiftHom.{u + 1}
      (fibredCategory C S hS X.obj).val.obj ⥤ _), rfl⟩

/-- The canonical 1-morphism from the universe lift of the object space down to the object space
itself. A definitional specialisation of `AlgebraicGeometry.Stack.liftedSpaceDown`. -/
def objectSpaceLiftDown (G : GroupoidInAlgebraicSpaces C S hS B) :
    (liftedObjectSpace G).val ⥤ᵇ (fibredCategory C S hS G.objects.obj).val :=
  liftedSpaceDown G.objects

/-- The canonical projection `S_U ⟶ [U/R]` of Stacks 044R, as a 1-morphism of categories fibred in
groupoids: the universe lift of the object space followed by
`AlgebraicGeometry.Stack.quotientStackProjection`. -/
noncomputable def quotientStackProjectionHom (G : GroupoidInAlgebraicSpaces C S hS B) :
    liftedObjectSpace G ⟶
      CatFiberedInGroupoids.mk (quotientStack G) (isFiberedInGroupoids_quotientStack G) :=
  Bicategory.InducedBicategory.mkHom
    (BasedFunctor.comp (objectSpaceLiftDown G) (quotientStackProjection G))

/-- The object of the lifted object space which the projection carries to a prescribed object of
the pointwise groupoid fibration: the same base object, and the same point of the object space read
as an object of a discrete fibre. -/
noncomputable def prestackObjectLift (G : GroupoidInAlgebraicSpaces C S hS B)
    (w : (quotientPrestack G).obj) : (liftedObjectSpace G).val.obj :=
  ULiftHom.objUp.{u + 1, u + 1}
    ⟨(ULiftHom.objDown.{u + 1, u + 1} w).base,
      Discrete.mk (ULiftHom.objDown.{u + 1, u + 1} w).fiber⟩

/-- The projection carries `AlgebraicGeometry.Stack.prestackObjectLift` to the prescribed object,
on the nose: the universe lift changes no objects, and the inclusion of the discrete object space
into the pointwise groupoid is a bijection on the objects of each fibre. -/
theorem homFunctor_quotientStackProjectionHom_prestackObjectLift
    (G : GroupoidInAlgebraicSpaces C S hS B) (w : (quotientPrestack G).obj) :
    (CatFiberedInGroupoids.homFunctor (quotientStackProjectionHom G)).obj
        (prestackObjectLift G w) =
      (toQuotientStack G).obj w := rfl

/-- **Part (1) of Stacks 044X along the projection.** Every object of a fibre `[U/R]_T` of the
quotient stack is, over the members of some fppf covering sieve of `T`, in the essential image on
fibres of the canonical projection `S_U ⟶ [U/R]`.

This is `AlgebraicGeometry.Stack.essImage_toQuotientStack` carried from
`AlgebraicGeometry.Stack.toQuotientStack` to the projection, which is possible with no comparison
because the two agree on the objects of each fibre by
`AlgebraicGeometry.Stack.homFunctor_quotientStackProjectionHom_prestackObjectLift`. -/
theorem essImage_quotientStackProjectionHom (G : GroupoidInAlgebraicSpaces C S hS B)
    (U : BigFppfOver C S hS) (x : (quotientStack G).p.Fiber U) :
    ∃ R ∈ BigFppfOver.topology C S hS U,
      ∀ ⦃V : BigFppfOver C S hS⦄ ⦃f : V ⟶ U⦄, R.arrows f →
        (Functor.fiberFunctorOfCompEq
          (CatFiberedInGroupoids.homFunctor_comp_p (quotientStackProjectionHom G)) V).essImage
          (Functor.pullbackFiber (quotientStack G).p x f) := by
  obtain ⟨R, hR, hess⟩ := essImage_toQuotientStack G U x
  refine ⟨R, hR, ?_⟩
  intro V f hf
  obtain ⟨w, ⟨e⟩⟩ := hess hf
  exact ⟨⟨prestackObjectLift G w.1, w.2⟩, ⟨e⟩⟩

/-- **The quotient-stack projection is locally essentially surjective.** Every object of a fibre
`[U/R]_T` of the quotient stack of a groupoid in algebraic spaces receives, over the members of
some fppf covering sieve of `T`, a morphism from the image under the canonical projection
`S_U ⟶ [U/R]` of an object of the object space.

This is the local essential surjectivity hypothesis of **Stacks 045D**
(`AlgebraicGeometry.Stack.hasRelativeProperty_of_baseChange`) and of
`AlgebraicGeometry.Stack.hasRelativeProperty_of_prop_representingMap_of_localEssSurj`, discharged
for this morphism. It needs no hypothesis on the groupoid: it is part (1) of Stacks 044X, which
holds because `[U/R]` is by construction the stackification of the pointwise groupoid
fibration. -/
theorem localEssSurj_quotientStackProjectionHom (G : GroupoidInAlgebraicSpaces C S hS B)
    (U : BigFppfOver C S hS)
    (y : (CatFiberedInGroupoids.mk (quotientStack G)
      (isFiberedInGroupoids_quotientStack G)).val.p.Fiber U) :
    ∃ R ∈ BigFppfOver.topology C S hS U,
      ∀ ⦃V : BigFppfOver C S hS⦄ ⦃k : V ⟶ U⦄, R.arrows k →
        ∃ (z : (liftedObjectSpace G).val.obj)
          (φ : (CatFiberedInGroupoids.homFunctor (quotientStackProjectionHom G)).obj z ⟶ y.1),
          (CatFiberedInGroupoids.mk (quotientStack G)
            (isFiberedInGroupoids_quotientStack G)).val.p.IsHomLift k φ :=
  localEssSurj_of_essImage C S hS (quotientStackProjectionHom G)
    (essImage_quotientStackProjectionHom G) U y

/-- Representability by algebraic spaces passes from the projection of Stacks 044R to its
universe-lifted form, by Stacks 0457: the universe lift is an equivalence of the source commuting
strictly with the projection to the site, and the target is unchanged.

This is what carries a representability result about the projection of Stacks 044R over to the
relative-property results about `AlgebraicGeometry.Stack.quotientStackProjectionHom`, which is the
form those results take their 1-morphism in. -/
theorem isRepresentableByAlgebraicSpaces_quotientStackProjectionHom
    (G : GroupoidInAlgebraicSpaces C S hS B)
    (h : IsRepresentableByAlgebraicSpaces C S hS (quotientStackProjection G)) :
    IsRepresentableByAlgebraicSpaces C S hS (quotientStackProjectionHom G).hom := by
  let : (objectSpaceLiftDown G).toFunctor.IsEquivalence :=
    (ULiftHom.equiv.{u, u + 1, u + 1}
      (C := (fibredCategory C S hS G.objects.obj).val.obj)).isEquivalence_inverse
  let : (BasedFunctor.id (quotientStack G)).toFunctor.IsEquivalence := by
    change (𝟭 (quotientStack G).obj).IsEquivalence
    infer_instance
  exact (isRepresentableByAlgebraicSpaces_iff_of_equivalences C S hS
    (𝒳' := liftedObjectSpace G)
    (𝒳 := fibredCategory C S hS G.objects.obj)
    (𝒴' := .mk (quotientStack G) (isFiberedInGroupoids_quotientStack G))
    (𝒴 := .mk (quotientStack G) (isFiberedInGroupoids_quotientStack G))
    (quotientStackProjectionHom G).hom (quotientStackProjection G)
    (objectSpaceLiftDown G) (BasedFunctor.id _)
    (Iso.refl _)).mp h

/-- **Stacks 045D for the quotient-stack projection, with no representability witness in scope.**
Let `P` be a property of morphisms of algebraic spaces over `S` stable under base change and local
on the target for the fppf precoverage. If in a 2-fibre product square of the canonical projection
`S_U ⟶ [U/R]` with *itself* the projection to the second factor satisfies the condition of
Stacks 03YK at `P`, then so does the canonical projection.

This is `AlgebraicGeometry.Stack.relativeProperty_of_baseChange` with the local essential
surjectivity Stacks 045D asks of the 1-morphism being descended along supplied by
`AlgebraicGeometry.Stack.localEssSurj_quotientStackProjectionHom`, so the only input left is the
one about the base change;
`AlgebraicGeometry.Stack.hasRelativeProperty_quotientStackProjectionHom_of_baseChange` is this
with the representability of the projection assumed as the source assumes it. -/
theorem relativeProperty_quotientStackProjectionHom_of_baseChange
    (G : GroupoidInAlgebraicSpaces C S hS B)
    (P : MorphismProperty (AlgebraicSpaces C S hS))
    [P.IsStableUnderBaseChange]
    [P.IsLocalAtTarget (Space.Topology.fppf.precoverage.{u, max u t} C S hS)]
    (D : Bicategory.TwoCommSq (quotientStackProjectionHom G) (quotientStackProjectionHom G))
    (hD : Bicategory.IsTwoFibreProduct D)
    (hP : RelativeProperty C S hS P D.fst) :
    RelativeProperty C S hS P (quotientStackProjectionHom G) :=
  relativeProperty_of_baseChange.{u, u + 1, u + 1, t} C S hS _ _ _ P
    (quotientStackProjectionHom G) (quotientStackProjectionHom G) D hD
    (localEssSurj_quotientStackProjectionHom G) hP

/-- **Stacks 045D for the quotient-stack projection: one base change of it along itself decides
every relative property of it.** Let `P` be a property of morphisms of algebraic spaces over `S`
stable under base change and local on the target for the fppf precoverage. If the canonical
projection `S_U ⟶ [U/R]` is representable by algebraic spaces, and in a 2-fibre product square of
it with *itself* the projection to the second factor has the relative property `P` of
Stacks 03YK, then the canonical projection has `P` relatively.

The local essential surjectivity which Stacks 045D asks of the 1-morphism being descended along
is `AlgebraicGeometry.Stack.localEssSurj_quotientStackProjectionHom`, so no hypothesis on the
groupoid is needed here; everything left to supply is about the one base change. The property is
left general on purpose: read at `AlgebraicGeometry.Space.smoothMorphismProperty` this is what
Stacks 04X0 asks for, and read at flatness, local finite presentation or surjectivity it is what
Stacks 06FH asks for. -/
theorem hasRelativeProperty_quotientStackProjectionHom_of_baseChange
    (G : GroupoidInAlgebraicSpaces C S hS B)
    (P : MorphismProperty (AlgebraicSpaces C S hS))
    [P.IsStableUnderBaseChange]
    [P.IsLocalAtTarget (Space.Topology.fppf.precoverage.{u, max u t} C S hS)]
    (hf : IsRepresentableByAlgebraicSpaces C S hS (quotientStackProjectionHom G).hom)
    (D : Bicategory.TwoCommSq (quotientStackProjectionHom G) (quotientStackProjectionHom G))
    (hD : Bicategory.IsTwoFibreProduct D)
    (hP : HasRelativeProperty C S hS P D.fst
      (isRepresentableByAlgebraicSpaces_baseChange.{u, u + 1, u + 1} C S hS _ _ _
        (quotientStackProjectionHom G) (quotientStackProjectionHom G) D hD hf)) :
    HasRelativeProperty C S hS P (quotientStackProjectionHom G) hf :=
  relativeProperty_quotientStackProjectionHom_of_baseChange.{u, t} G P D hD hP

/-- The canonical 2-fibre product square of the quotient-stack projection with **itself**, taken
in the 2-category of categories fibred in groupoids over the big fppf site. Its apex is the
2-fibre product `S_U ×_{[U/R]} S_U`, which Stacks 04M9 identifies with the arrow space `R`. -/
noncomputable def quotientStackProjectionSelfSquare
    (G : GroupoidInAlgebraicSpaces C S hS B) :
    Bicategory.TwoCommSq (quotientStackProjectionHom G) (quotientStackProjectionHom G) :=
  CatFiberedInGroupoids.twoFibreProductSquare.{u, u + 1, u + 1, u + 1}
    (quotientStackProjectionHom G) (quotientStackProjectionHom G)

/-- The canonical self-square of the quotient-stack projection is a 2-fibre product. -/
noncomputable def isTwoFibreProduct_quotientStackProjectionSelfSquare
    (G : GroupoidInAlgebraicSpaces C S hS B) :
    Bicategory.IsTwoFibreProduct (quotientStackProjectionSelfSquare G) :=
  CatFiberedInGroupoids.isTwoFibreProduct_twoFibreProductSquare.{u, u + 1, u + 1, u + 1} _ _

/-- **The relative property of the quotient-stack projection reduced to two inputs.** Let `P` be a
property of morphisms of algebraic spaces over `S` stable under base change and local on the
target for the fppf precoverage. If the canonical projection `S_U ⟶ [U/R]` is representable by
algebraic spaces, and the first leg of its canonical 2-fibre product square *with itself* has the
relative property `P` of Stacks 03YK, then the projection has `P` relatively.

This is `AlgebraicGeometry.Stack.hasRelativeProperty_quotientStackProjectionHom_of_baseChange`
with the square and its universal property supplied rather than demanded, so that **exactly two**
arguments remain: `hf`, which is Stacks 04WZ through
`AlgebraicGeometry.Stack.isRepresentableByAlgebraicSpaces_quotientStackProjectionHom`, and `hP`,
which is Stacks 04M9 together with whatever `P` asks of the groupoid's source map. Read at
`AlgebraicGeometry.Space.smoothMorphismProperty` that is the content of Stacks 04X0; read at
flatness, local finite presentation or surjectivity it is the content of Stacks 06FH. -/
theorem hasRelativeProperty_quotientStackProjectionHom_of_selfSquare
    (G : GroupoidInAlgebraicSpaces C S hS B)
    (P : MorphismProperty (AlgebraicSpaces C S hS))
    [P.IsStableUnderBaseChange]
    [P.IsLocalAtTarget (Space.Topology.fppf.precoverage.{u, max u t} C S hS)]
    (hf : IsRepresentableByAlgebraicSpaces C S hS (quotientStackProjectionHom G).hom)
    (hP : HasRelativeProperty C S hS P (quotientStackProjectionSelfSquare G).fst
      (isRepresentableByAlgebraicSpaces_baseChange.{u, u + 1, u + 1} C S hS _ _ _
        (quotientStackProjectionHom G) (quotientStackProjectionHom G)
        (quotientStackProjectionSelfSquare G)
        (isTwoFibreProduct_quotientStackProjectionSelfSquare G) hf)) :
    HasRelativeProperty C S hS P (quotientStackProjectionHom G) hf :=
  hasRelativeProperty_quotientStackProjectionHom_of_baseChange.{u, t} G P hf
    (quotientStackProjectionSelfSquare G)
    (isTwoFibreProduct_quotientStackProjectionSelfSquare G) hP

end Projection

end AlgebraicGeometry.Stack

end
