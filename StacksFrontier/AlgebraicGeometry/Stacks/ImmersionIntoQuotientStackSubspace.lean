module

public import StacksFrontier.AlgebraicGeometry.Spaces.Groupoids.InvariantClosedSubspace
public import StacksFrontier.AlgebraicGeometry.Spaces.Groupoids.Quotient.ProjectionTwoArrow
public import StacksFrontier.AlgebraicGeometry.Spaces.Morphisms.Immersions
public import StacksFrontier.AlgebraicGeometry.Spaces.Morphisms.Monomorphisms
public import StacksFrontier.AlgebraicGeometry.Spaces.OpenSubspaceGeneralizations
public import StacksFrontier.AlgebraicGeometry.Stacks.QuotientStackProjectionLocalEssSurj
public import StacksFrontier.CategoryTheory.TwoFibreProduct.CatFiberedInGroupoids
public import Mathlib.CategoryTheory.EssentialImage
public import Mathlib.CategoryTheory.Subfunctor.Image

/-!
# Stacks 0505: the invariant subspace cut out by an immersion into a quotient stack

Let `G = (U, R, s, t, c)` be a groupoid in algebraic spaces over an algebraic space `B` over a
scheme `S` of a big fppf site, and let `i : 𝒵 ⟶ [U/R]` be an immersion. Stacks 0505 asserts
that there is an `R`-invariant locally closed subspace `Z ⊆ U` and a presentation
`[Z/R_Z] ⟶ 𝒵` making the triangle over `[U/R]` 2-commutative, and that `Z` is closed —
respectively open — when `i` is a closed — respectively open — immersion.

The subspace the source produces is `U' = 𝒵 ×_{[U/R]} U`, read as a subspace of `U` through the
immersion `U' ⟶ U`. This module proves the two assertions about that subspace: that it **is** a
locally closed — respectively closed, respectively open — subspace of `U`, and that it is
**`R`-invariant**.

## Main results

* `AlgebraicGeometry.Space.isAlgebraicSpace_range_of_mono` and
  `AlgebraicGeometry.Space.prop_range_ι_of_mono`: the range of a monomorphism of presheaves on
  the big fppf site of `S` with algebraic-space source is an algebraic space, and its inclusion
  into the target inherits every relative property of scheme morphisms the monomorphism has.
* `AlgebraicGeometry.Space.isLocallyClosedSubspace_range_of_isImmersion` and
  `AlgebraicGeometry.Space.isOpenSubspace_range_of_isOpenImmersion_of_isAlgebraicSpace`: two
  instances of Stacks 02YU — the step of Stacks 0505 which, from the immersion `U' ⟶ U`,
  produces the locally closed subspace `Z ⊆ U` with `U' ≅ Z`.
* `AlgebraicGeometry.Stack.exists_iso_quotientStackProjection_source_target`: the images in
  `[U/R]` of the two ends of an arrow of `G` are isomorphic. This is the 2-morphism of
  Stacks 044S, which lies over an identity of the site and is therefore invertible.
* `AlgebraicGeometry.Stack.preimage_target_eq_preimage_source_of_mem_iff`: a subspace of `U`
  cut out by an isomorphism-invariant property of the image in `[U/R]` is `R`-invariant.
* `AlgebraicGeometry.Stack.isInvariantLocallyClosed_range_of_isImmersion_essImage`,
  `AlgebraicGeometry.Stack.isInvariantOpen_range_of_isOpenImmersion_essImage` and
  `AlgebraicGeometry.Stack.isInvariantClosed_range_of_isClosedImmersion_essImage`: **the
  subspace assertions of Stacks 0505** — `Z` is an invariant locally closed, respectively
  invariant open, respectively invariant closed subspace of `U`.
* `CategoryTheory.TwoFibreProductOver.essImage_obj_iff_exists_x_eq`: for a cospan
  `𝒰 ⟶ 𝒳 ⟵ 𝒴` of categories over a base with `𝒴` and `𝒳` fibred in groupoids, an object of
  `𝒰` lies under an object of the 2-fibre product `𝒰 ×_𝒳 𝒴` exactly when its image in `𝒳` is
  in the essential image of `𝒴 ⟶ 𝒳`. The content is that an isomorphism of `𝒳` between two
  objects over one and the same base object may be replaced by a *vertical* one, which is what
  `CategoryTheory.TwoFibreProductOver` carries.
* `AlgebraicGeometry.Stack.essImage_quotientStackProjection_iff_exists_twoFibreProductOver`
  and `…_iff_exists_twoFibreProductSquare`: that statement at the cospan of Stacks 0505 — the
  canonical atlas `U ⟶ [U/R]` of Stacks 044R against `i : 𝒵 ⟶ [U/R]` — for the 2-fibre product
  over the site and for the apex of the canonical 2-fibre product square of the 2-category of
  categories fibred in groupoids. **This discharges the essential-image half of the carried
  hypothesis `hmem` below**: a point of `U` is in the locus `hmem` describes exactly when it is
  carried by an object of `𝒵 ×_{[U/R]} U`.

## What is proved, and what is not

Stacks 0505's proof has one citation, **Stacks 04Y6**, which produces the 2-fibre product
`U' = 𝒵 ×_{[U/R]} U` together with the presentation of `𝒵` by the restriction of `G` to it. The
2-fibre product itself is available: it is
`CategoryTheory.CatFiberedInGroupoids.twoFibreProductSquare` at the canonical atlas
`AlgebraicGeometry.Stack.quotientStackProjectionHom` and at `i`, and the two statements below
identify, with no hypothesis, the locus of `U` its projection covers. What is *not* available is
the step that reads that 2-fibre product as an algebraic space over `U`: it is a category fibred
in groupoids, and exhibiting it as an algebraic space needs `i` to be representable by algebraic
spaces (Stacks 0300,
`AlgebraicGeometry.Stack.isRepresentableByAlgebraicSpace_twoFibreProduct`). So the *space* `U'`
is still carried, in the two pieces the argument uses:

* an algebraic space `U'` with a morphism `m : U' ⟶ U`, together with the hypothesis that `m`
  is an immersion (respectively a closed, respectively an open immersion) of algebraic spaces.
  In the source this is read off from `i` being one, by Stacks 04XD; that descent is not
  available for a 1-morphism out of a quotient stack, whose morphisms live one universe up
  (see the module documentation of
  `StacksFrontier.AlgebraicGeometry.Stacks.QuotientStackRestrictionImmersion`), so it is carried;
* the hypothesis that the range of `m` is, pointwise, the locus of `U` the projection of
  `𝒵 ×_{[U/R]} U` covers. In the three statements this is spelled out with essential images,
  as `hmem`; given that `𝒵` is fibred in groupoids it is equivalent to the 2-fibre product
  condition itself, which is what Stacks 04Y6 asserts, and that equivalence is proved rather
  than assumed.

The comparison of a vertical isomorphism with an arbitrary one, which that equivalence needs, is
the new content, and it is
`CategoryTheory.TwoFibreProductOver.essImage_obj_iff_exists_x_eq`, which carries nothing.

Both carried hypotheses are used; neither is the conclusion. From them the two subspace
assertions of Stacks 0505 are proved outright: local closedness (respectively closedness,
openness) by the range lemmas below, and `R`-invariance by the 2-morphism of Stacks 044S. No
smoothness of `G` is used anywhere — Stacks 044S holds for any groupoid in algebraic spaces —
so the smoothness hypothesis of Stacks 0505 is **not** carried.

The remaining assertion of Stacks 0505 — that `[Z/R_Z] ⟶ 𝒵` is a *presentation* and that the
triangle over `[U/R]` is 2-commutative — is **not** proved and nothing here is tagged for it.
It is precisely what Stacks 04Y6 supplies, and assuming the equivalence
`[Z/R_Z] ≃ 𝒵` would be assuming all but the smoothness clause of
`AlgebraicGeometry.Stack.GroupoidPresentation`, so no statement of that shape is given.

## Implementation notes

The subspace is `CategoryTheory.Subfunctor.range` of the underlying morphism of presheaves of
`m`, and the isomorphism `U' ≅ Z` of the source's proof is
`CategoryTheory.Subfunctor.toRange`, which is invertible because an immersion of algebraic
spaces is a monomorphism (**Stacks 042R**,
`AlgebraicGeometry.Space.mono_of_isImmersion`). The range lemmas factor through a single
statement for an arbitrary property of scheme morphisms,
`AlgebraicGeometry.Space.prop_range_ι_of_mono`. Its closed instance is **not** given a name
here: it is already
`AlgebraicGeometry.Space.isClosedSubspace_range_of_isClosedImmersion` of
`StacksFrontier.AlgebraicGeometry.Spaces.Limits.DescendingFiniteTypeLimitImage`, with the same
statement, so naming it again would duplicate that declaration; the closed case below uses the
general statement inline instead, and that module is not imported.

Invariance is stated for an arbitrary property of the objects of `[U/R]` closed under
isomorphism, and then instantiated at `CategoryTheory.Functor.essImage` of `i`, which carries
that instance in Mathlib. The argument is the one Stacks 0505 runs: the 2-morphism of
Stacks 044S at a point of the arrow space lies over an identity of the site, a morphism of a
category fibred in groupoids lying over an isomorphism is strongly cartesian, and a strongly
cartesian morphism over an isomorphism is an isomorphism.

`CategoryTheory.TwoFibreProductOver.essImage_obj_iff_exists_x_eq` belongs in
`StacksFrontier.CategoryTheory.TwoFibreProductOver`, which owns that namespace; it is stated here
instead so that this file adds no declaration to a module another file already owns. Its proof
runs the same three steps as
`AlgebraicGeometry.Stack.exists_iso_quotientStackProjection_source_target` above, in the
opposite direction: a lift of the base isomorphism produces an object of `𝒴` over the right
base object, the fill-in property of the target produces the comparison morphism over the
identity, and that morphism is an isomorphism because it lies over one.

The two statements about the cospan of Stacks 0505 are given for the 2-fibre product over the
site and, separately, for the apex of
`CategoryTheory.CatFiberedInGroupoids.twoFibreProductSquare`, the canonical 2-fibre product
square of the 2-category. The second is the square Stacks 04Y6's
`…RepresentablePresentation.atlasBaseChangeSquare` names, but that abbreviation cannot be used:
it is stated for `CategoryTheory.CatFiberedInGroupoids.{u, u, u + 1, u + 1}`, whose morphisms
lie in `Type u`, whereas a quotient stack is a
`CategoryTheory.BasedCategory.{u + 1, u + 1}` — the same universe pin that keeps Stacks 04XD
off a 1-morphism of quotient stacks. The underlying construction is unpinned, so the square is
formed directly, with `AlgebraicGeometry.Stack.quotientStackProjectionHom` as the atlas.

## References

* [Stacks Project, Tag 02YU](https://stacks.math.columbia.edu/tag/02YU)
* [Stacks Project, Tag 0300](https://stacks.math.columbia.edu/tag/0300)
* [Stacks Project, Tag 042R](https://stacks.math.columbia.edu/tag/042R)
* [Stacks Project, Tag 044F](https://stacks.math.columbia.edu/tag/044F)
* [Stacks Project, Tag 044R](https://stacks.math.columbia.edu/tag/044R)
* [Stacks Project, Tag 044S](https://stacks.math.columbia.edu/tag/044S)
* [Stacks Project, Tag 04XD](https://stacks.math.columbia.edu/tag/04XD)
* [Stacks Project, Tag 04Y6](https://stacks.math.columbia.edu/tag/04Y6)
* [Stacks Project, Tag 0505](https://stacks.math.columbia.edu/tag/0505)
-/

@[expose] public section

open CategoryTheory

universe u

namespace CategoryTheory.TwoFibreProductOver

/-- **An object of `𝒰` is covered by the 2-fibre product `𝒰 ×_𝒳 𝒴` exactly when its image is
in the essential image of `𝒴 ⟶ 𝒳`.** Let `f : 𝒰 ⟶ 𝒳` and `g : 𝒴 ⟶ 𝒳` be 1-morphisms of
categories over a base, with `𝒴` and `𝒳` fibred in groupoids. Then `a : 𝒰` is the first
component of an object of `CategoryTheory.TwoFibreProductOver` of that cospan if and only if
`f a` is isomorphic to `g y` for some `y : 𝒴`.

The two conditions are not the same on their face: an object of the 2-fibre product over a base
object `T` carries an isomorphism `f a ≅ g y` which is *vertical* over `T`, whereas the
essential image is taken with respect to arbitrary isomorphisms of `𝒳`. They agree because `𝒴`
is fibred in groupoids: an arbitrary isomorphism `g y ≅ f a` lies over some isomorphism of the
base, `y` can be moved along a lift of it to an object `y'` lying over the same base object as
`a`, and the fill-in property of `𝒳` then produces a morphism `f a ⟶ g y'` over the identity,
which is invertible because it lies over an isomorphism. -/
theorem essImage_obj_iff_exists_x_eq {𝒮 : Type*} [Category 𝒮]
    {𝒰 : BasedCategory 𝒮} {𝒴 : BasedCategory 𝒮} {𝒳 : BasedCategory 𝒮}
    (f : 𝒰 ⥤ᵇ 𝒳) (g : 𝒴 ⥤ᵇ 𝒳)
    (h𝒴 : 𝒴.p.IsFiberedInGroupoids) (h𝒳 : 𝒳.p.IsFiberedInGroupoids) (a : 𝒰.obj) :
    g.toFunctor.essImage (f.obj a) ↔
      ∃ P : TwoFibreProductOver 𝒰.p 𝒴.p 𝒳.p f.toFunctor g.toFunctor, P.x = a := by
  constructor
  · rintro ⟨y, ⟨e⟩⟩
    have ha : 𝒳.p.obj (f.obj a) = 𝒰.p.obj a := BasedFunctor.w_obj f a
    have hy : 𝒳.p.obj (g.obj y) = 𝒴.p.obj y := BasedFunctor.w_obj g y
    set θ : 𝒰.p.obj a ⟶ 𝒴.p.obj y :=
      eqToHom ha.symm ≫ 𝒳.p.map e.inv ≫ eqToHom hy with hθ
    have : 𝒳.p.IsHomLift θ e.inv := IsHomLift.of_fac' _ θ e.inv ha hy (by rw [hθ]; simp)
    obtain ⟨y', ψ, hψ⟩ := h𝒴.exists_lift θ y rfl
    have hy' : 𝒴.p.obj y' = 𝒰.p.obj a := IsHomLift.domain_eq 𝒴.p θ ψ
    have hgy' : 𝒳.p.obj (g.obj y') = 𝒰.p.obj a := (BasedFunctor.w_obj g y').trans hy'
    obtain ⟨χ, ⟨hχmap, _⟩, -⟩ :=
      h𝒳.unique_lift (g.map ψ) e.inv (eqToHom (ha.trans hgy'.symm)) (by
        rw [IsHomLift.fac' 𝒳.p θ (g.map ψ), IsHomLift.fac' 𝒳.p θ e.inv]; simp)
    have hχ : 𝒳.p.IsHomLift (𝟙 (𝒰.p.obj a)) χ :=
      IsHomLift.of_fac' _ _ χ ha hgy' (by rw [hχmap]; simp)
    have := h𝒳.isStronglyCartesian_homLift (𝟙 (𝒰.p.obj a)) χ
    have : IsIso χ :=
      Functor.IsStronglyCartesian.isIso_of_base_isIso 𝒳.p (𝟙 (𝒰.p.obj a)) χ
    exact ⟨{ base := 𝒰.p.obj a, x := a, y := y', hx := rfl, hy := hy'
             iso := asIso χ, vertical := hχ }, rfl⟩
  · rintro ⟨P, hP⟩
    exact ⟨P.y, ⟨P.iso.symm ≪≫ eqToIso (congrArg f.toFunctor.obj hP)⟩⟩

end CategoryTheory.TwoFibreProductOver

namespace AlgebraicGeometry.Space

variable (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)
  {F G : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u}

/-- The range of a monomorphism of presheaves on the big fppf site of `S` whose source is an
algebraic space over `S` is again an algebraic space: the canonical map to the range is
invertible. -/
theorem isAlgebraicSpace_range_of_mono (p : F ⟶ G) [Mono p]
    (hF : IsAlgebraicSpace B S hS F) :
    IsAlgebraicSpace B S hS (Subfunctor.range p).toFunctor :=
  isAlgebraicSpace_of_iso B S hS (asIso (Subfunctor.toRange p)) hF

/-- For a monomorphism `p` of presheaves on the big fppf site of `S`, the inclusion of the range
of `p` has every relative property of scheme morphisms that `p` has: the two differ by
precomposition with the inverse of `CategoryTheory.Subfunctor.toRange`. -/
theorem prop_range_ι_of_mono (Pr : MorphismProperty Scheme.{u}) (p : F ⟶ G) [Mono p]
    (hp : (MorphismProperty.presheaf (MorphismProperty.inverseImage Pr
      (BigFppfOver.toScheme B S hS))) p) :
    (MorphismProperty.presheaf (MorphismProperty.inverseImage Pr
      (BigFppfOver.toScheme B S hS))) (Subfunctor.range p).ι := by
  have heq : (asIso (Subfunctor.toRange p)).inv ≫ p = (Subfunctor.range p).ι :=
    calc (asIso (Subfunctor.toRange p)).inv ≫ p
        = (asIso (Subfunctor.toRange p)).inv ≫
            ((asIso (Subfunctor.toRange p)).hom ≫ (Subfunctor.range p).ι) := by
          rw [asIso_hom, Subfunctor.toRange_ι]
      _ = (Subfunctor.range p).ι :=
          (asIso (Subfunctor.toRange p)).inv_hom_id_assoc (Subfunctor.range p).ι
  exact heq ▸ MorphismProperty.RespectsIso.precomp
    (MorphismProperty.presheaf (MorphismProperty.inverseImage Pr
      (BigFppfOver.toScheme B S hS)))
    (asIso (Subfunctor.toRange p)).inv p hp

/-- **Stacks 02YU, part (6) for the range of an immersion.** The range of an immersion of
algebraic spaces over `S` whose source is an algebraic space is a locally closed subspace of the
target, and the source is isomorphic to it.

This is the step of Stacks 0505 that reads the base change `U' = 𝒵 ×_{[U/R]} U` as a locally
closed subspace `Z ⊆ U`. -/
theorem isLocallyClosedSubspace_range_of_isImmersion (p : F ⟶ G)
    (hF : IsAlgebraicSpace B S hS F) (hp : IsImmersion B S hS p) :
    IsLocallyClosedSubspace B S hS (Subfunctor.range p) :=
  have : Mono p := mono_of_isImmersion B S hS hp
  ⟨isAlgebraicSpace_range_of_mono B S hS p hF,
    prop_range_ι_of_mono B S hS _ p hp⟩

/-- **Stacks 02YU, part (2) for the range of an open immersion.** The range of an open immersion
of algebraic spaces over `S` whose source is an algebraic space is an open subspace of the
target.

`AlgebraicGeometry.Space.isOpenSubspace_range_of_isOpenImmersion` is the same statement for a
*representable* source; this is the form Stacks 0505 needs, where the source is an arbitrary
algebraic space. -/
theorem isOpenSubspace_range_of_isOpenImmersion_of_isAlgebraicSpace (p : F ⟶ G)
    (hF : IsAlgebraicSpace B S hS F) (hp : IsOpenImmersion B S hS p) :
    IsOpenSubspace B S hS (Subfunctor.range p) :=
  have : Mono p := mono_of_isImmersion B S hS (isImmersion_of_isOpenImmersion B S hS hp)
  ⟨isAlgebraicSpace_range_of_mono B S hS p hF,
    prop_range_ι_of_mono B S hS _ p hp⟩

end AlgebraicGeometry.Space

namespace AlgebraicGeometry.Stack

open GroupoidInAlgebraicSpaces

variable {C : BigFppfSite.{u}} {S : Scheme.{u}} {hS : C.Contains S}
  {B : AlgebraicSpaces C S hS}

/-- **The two ends of an arrow of a groupoid have isomorphic images in the quotient stack.** At a
point of the arrow space the 2-morphism of Stacks 044S is a morphism of `[U/R]` lying over an
identity of the big fppf site from the image of the source of that point to the image of its
target; a morphism of a category fibred in groupoids lying over an identity is strongly
cartesian over an isomorphism, hence an isomorphism.

No hypothesis on the groupoid is used. -/
theorem exists_iso_quotientStackProjection_source_target
    (G : GroupoidInAlgebraicSpaces C S hS B)
    (x : (fibredCategory C S hS G.arrows.obj).val.obj) :
    Nonempty
      ((quotientStackProjection G).obj
          ⟨x.base, Discrete.mk (G.source.hom.app (Opposite.op x.base) x.fiber.as)⟩ ≅
        (quotientStackProjection G).obj
          ⟨x.base, Discrete.mk (G.target.hom.app (Opposite.op x.base) x.fiber.as)⟩) := by
  have hs := associatedMap_obj C S hS G.source.hom x
  have ht := associatedMap_obj C S hS G.target.hom x
  have hlift := (quotientStackTwoArrow G).isHomLift' x
  have hcart : (quotientStack G).p.IsStronglyCartesian
      (𝟙 ((fibredCategory C S hS G.arrows.obj).val.p.obj x))
      ((quotientStackTwoArrow G).app x) := by
    have := hlift
    exact (isFiberedInGroupoids_quotientStack G).isStronglyCartesian_homLift _ _
  have := hcart
  have hiso : IsIso ((quotientStackTwoArrow G).app x) :=
    Functor.IsStronglyCartesian.isIso_of_base_isIso (quotientStack G).p
      (𝟙 ((fibredCategory C S hS G.arrows.obj).val.p.obj x))
      ((quotientStackTwoArrow G).app x)
  exact ⟨eqToIso (congrArg (fun z => (quotientStackProjection G).obj z) hs).symm ≪≫
    (@asIso _ _ _ _ _ hiso) ≪≫
      eqToIso (congrArg (fun z => (quotientStackProjection G).obj z) ht)⟩

/-- **A subspace of the object space cut out by an isomorphism-invariant condition on the
quotient stack is `R`-invariant**, in the sense of Stacks 044F: its inverse images along the
target and along the source map of the groupoid agree as subfunctors of the arrow space.

At a point of the arrow space the images in `[U/R]` of its source and of its target are
isomorphic by `AlgebraicGeometry.Stack.exists_iso_quotientStackProjection_source_target`, and
the condition is invariant under isomorphism. -/
theorem preimage_target_eq_preimage_source_of_mem_iff
    (G : GroupoidInAlgebraicSpaces C S hS B)
    (P : ObjectProperty (quotientStack G).obj) [P.IsClosedUnderIsomorphisms]
    (Z : Subfunctor G.objects.obj)
    (hZ : ∀ (W : (BigFppfOver C S hS)ᵒᵖ) (u : G.objects.obj.obj W),
      u ∈ Z.obj W ↔ P ((quotientStackProjection G).obj ⟨W.unop, Discrete.mk u⟩)) :
    Z.preimage G.target.hom = Z.preimage G.source.hom := by
  refine Subfunctor.ext (funext fun W => ?_)
  ext a
  obtain ⟨e⟩ := exists_iso_quotientStackProjection_source_target G
    (⟨W.unop, Discrete.mk a⟩ : (fibredCategory C S hS G.arrows.obj).val.obj)
  show G.target.hom.app W a ∈ Z.obj W ↔ G.source.hom.app W a ∈ Z.obj W
  rw [hZ W (G.target.hom.app W a), hZ W (G.source.hom.app W a)]
  exact ⟨fun h => P.prop_of_iso e.symm h, fun h => P.prop_of_iso e h⟩

section Subspace

variable {G : GroupoidInAlgebraicSpaces C S hS B}
  {𝒵 : BasedCategory.{u + 1, u + 1} (BigFppfOver C S hS)}
  (i : 𝒵 ⥤ᵇ quotientStack G) {U' : AlgebraicSpaces C S hS} (m : U' ⟶ G.objects)

/-- **Stacks 0505, the invariant locally closed subspace.** Let `G = (U, R, s, t, c)` be a
groupoid in algebraic spaces, let `i : 𝒵 ⟶ [U/R]` be a 1-morphism over the big fppf site, and
let `m : U' ⟶ U` be an immersion of algebraic spaces whose range is, pointwise, the inverse
image along `U ⟶ [U/R]` of the essential image of `i` — which is what it is for `U'` to be the
2-fibre product `𝒵 ×_{[U/R]} U` of Stacks 04Y6. Then the range of `m` is an `R`-invariant
locally closed subspace `Z ⊆ U` in the sense of Stacks 044F, part (2), and `U' ≅ Z`.

Smoothness of `G` is not used. -/
@[stacks 0505 "the R-invariant locally closed subspace Z = U' of U cut out by an immersion \
into [U/R]; the 2-fibre product U' = 𝒵 ×_{[U/R]} U of Stacks 04Y6 is carried as the morphism m \
together with hmem, and the immersion property of m (Stacks 04XD applied to i) as hm; the \
presentation [Z/R_Z] ⟶ 𝒵 and the 2-commutative triangle are not proved"]
theorem isInvariantLocallyClosed_range_of_isImmersion_essImage
    (hm : Space.IsImmersion C S hS m.hom)
    (hmem : ∀ (W : (BigFppfOver C S hS)ᵒᵖ) (u : G.objects.obj.obj W),
      u ∈ (Subfunctor.range m.hom).obj W ↔
        i.toFunctor.essImage ((quotientStackProjection G).obj ⟨W.unop, Discrete.mk u⟩)) :
    IsInvariantLocallyClosed G (Subfunctor.range m.hom) :=
  ⟨Space.isLocallyClosedSubspace_range_of_isImmersion C S hS m.hom U'.property hm,
    preimage_target_eq_preimage_source_of_mem_iff G i.toFunctor.essImage _ hmem⟩

/-- **Stacks 0505, the invariant closed subspace.** In the situation of
`AlgebraicGeometry.Stack.isInvariantLocallyClosed_range_of_isImmersion_essImage`, if `m` is a
closed immersion — which is what the source gets from `i` being a closed immersion — then the
range of `m` is an invariant *closed* subspace of `U`. -/
@[stacks 0505 "the R-invariant closed subspace, for a closed immersion into [U/R]; the 2-fibre \
product of Stacks 04Y6 is carried as m together with hmem, and the closed immersion property of \
m (Stacks 04XD applied to i) as hm"]
theorem isInvariantClosed_range_of_isClosedImmersion_essImage
    (hm : Space.IsClosedImmersion C S hS m.hom)
    (hmem : ∀ (W : (BigFppfOver C S hS)ᵒᵖ) (u : G.objects.obj.obj W),
      u ∈ (Subfunctor.range m.hom).obj W ↔
        i.toFunctor.essImage ((quotientStackProjection G).obj ⟨W.unop, Discrete.mk u⟩)) :
    IsInvariantClosed G (Subfunctor.range m.hom) :=
  have : Mono m.hom :=
    Space.mono_of_isImmersion C S hS (Space.isImmersion_of_isClosedImmersion C S hS hm)
  ⟨⟨Space.isAlgebraicSpace_range_of_mono C S hS m.hom U'.property,
      Space.prop_range_ι_of_mono C S hS _ m.hom hm⟩,
    preimage_target_eq_preimage_source_of_mem_iff G i.toFunctor.essImage _ hmem⟩

/-- **Stacks 0505, the invariant open subspace.** In the situation of
`AlgebraicGeometry.Stack.isInvariantLocallyClosed_range_of_isImmersion_essImage`, if `m` is an
open immersion — which is what the source gets from `i` being an open immersion — then the range
of `m` is an invariant *open* subspace of `U` in the sense of Stacks 044F, part (1). -/
@[stacks 0505 "the R-invariant open subspace, for an open immersion into [U/R]; the 2-fibre \
product of Stacks 04Y6 is carried as m together with hmem, and the open immersion property of m \
(Stacks 04XD applied to i) as hm"]
theorem isInvariantOpen_range_of_isOpenImmersion_essImage
    (hm : Space.IsOpenImmersion C S hS m.hom)
    (hmem : ∀ (W : (BigFppfOver C S hS)ᵒᵖ) (u : G.objects.obj.obj W),
      u ∈ (Subfunctor.range m.hom).obj W ↔
        i.toFunctor.essImage ((quotientStackProjection G).obj ⟨W.unop, Discrete.mk u⟩)) :
    IsInvariantOpen G (Subfunctor.range m.hom) :=
  ⟨Space.isOpenSubspace_range_of_isOpenImmersion_of_isAlgebraicSpace C S hS m.hom
      U'.property hm,
    le_of_eq (preimage_target_eq_preimage_source_of_mem_iff G i.toFunctor.essImage _ hmem).symm⟩

/-- **Stacks 0505: the locus the 2-fibre product of Stacks 04Y6 covers is the essential-image
locus.** Let `G = (U, R, s, t, c)` be a groupoid in algebraic spaces and let `i : 𝒵 ⟶ [U/R]` be
a 1-morphism over the big fppf site whose source is fibred in groupoids. A point `x` of `U`
over an object `W` of the site is carried by an object of the 2-fibre product
`U ×_{[U/R]} 𝒵` — the `U'` Stacks 04Y6 forms, for the canonical atlas `U ⟶ [U/R]` of
Stacks 044R — exactly when the image of `x` in `[U/R]` lies in the essential image of `i`.

Nothing is carried: this is the hypothesis `hmem` of
`AlgebraicGeometry.Stack.isInvariantLocallyClosed_range_of_isImmersion_essImage`, in the shape
Stacks 04Y6 states it, proved rather than assumed. -/
@[stacks 0505 "the points of U covered by the 2-fibre product U' = 𝒵 ×_{[U/R]} U of Stacks 04Y6 \
are exactly those whose image in [U/R] is in the essential image of i; nothing carried"]
theorem essImage_quotientStackProjection_iff_exists_twoFibreProductOver
    (h𝒵 : 𝒵.p.IsFiberedInGroupoids) (W : (BigFppfOver C S hS)ᵒᵖ)
    (x : G.objects.obj.obj W) :
    i.toFunctor.essImage ((quotientStackProjection G).obj ⟨W.unop, Discrete.mk x⟩) ↔
      ∃ P : TwoFibreProductOver (fibredCategory C S hS G.objects.obj).val.p 𝒵.p
          (quotientStack G).p (quotientStackProjection G).toFunctor i.toFunctor,
        P.x = ⟨W.unop, Discrete.mk x⟩ :=
  TwoFibreProductOver.essImage_obj_iff_exists_x_eq _ i h𝒵
    (isFiberedInGroupoids_quotientStack G) _

end Subspace

section Square

variable {G : GroupoidInAlgebraicSpaces C S hS B}

/-- **Stacks 0505 for the canonical 2-fibre product square of Stacks 04Y6.** The same statement
as `AlgebraicGeometry.Stack.essImage_quotientStackProjection_iff_exists_twoFibreProductOver`,
read on the apex of `CategoryTheory.CatFiberedInGroupoids.twoFibreProductSquare` at the
canonical atlas `AlgebraicGeometry.Stack.quotientStackProjectionHom` of Stacks 044R and at a
1-morphism `j : 𝒴 ⟶ [U/R]` of categories fibred in groupoids. That square is the
`U' = 𝒰 ×_𝒳 𝒳'` of Stacks 04Y6, formed at the universes a quotient stack lives at.

Nothing is carried. -/
@[stacks 0505 "the points of U covered by the apex of the canonical 2-fibre product square of \
Stacks 04Y6 at the atlas U ⟶ [U/R] are exactly those whose image in [U/R] is in the essential \
image of the other leg; nothing carried"]
theorem essImage_quotientStackProjection_iff_exists_twoFibreProductSquare
    (𝒴 : CatFiberedInGroupoids.{u, u + 1, u + 1, u + 1} (BigFppfOver C S hS))
    (j : 𝒴 ⟶ CatFiberedInGroupoids.mk (quotientStack G)
      (isFiberedInGroupoids_quotientStack G))
    (W : (BigFppfOver C S hS)ᵒᵖ) (x : G.objects.obj.obj W) :
    j.hom.toFunctor.essImage
        ((quotientStackProjection G).obj ⟨W.unop, Discrete.mk x⟩) ↔
      ∃ P : (CatFiberedInGroupoids.twoFibreProductSquare.{u, u + 1, u + 1, u + 1}
          (quotientStackProjectionHom G) j).pt.val.obj,
        P.x = ULiftHom.objUp ⟨W.unop, Discrete.mk x⟩ :=
  TwoFibreProductOver.essImage_obj_iff_exists_x_eq
    (𝒰 := (liftedObjectSpace G).val) (quotientStackProjectionHom G).hom j.hom
    𝒴.property (isFiberedInGroupoids_quotientStack G) _

end Square

end AlgebraicGeometry.Stack

end
