module

public import StacksCore.Tactic.StacksAttribute
public import StacksFrontier.AlgebraicGeometry.Quot.CoherentStackFiberedUnconditional
public import StacksFrontier.AlgebraicGeometry.Quot.CoherentStackMorSheaf
public import StacksFrontier.AlgebraicGeometry.Quot.RelativeIsom
public import StacksFrontier.AlgebraicGeometry.Spaces.FinitePresentationBaseChange
public import StacksFrontier.AlgebraicGeometry.Stacks.CoherentStackDiagonal

/-!
# The equalizer reduction in the proof of Stacks 08W6

Let `f : X ⟶ Y` be a finitely presented morphism of algebraic spaces over a scheme `S` of a big
fppf site, the standing data of Stacks 08KB, and write `𝒳 = Coh_{X/Y}` for the category of
coherent sheaves with proper support of that tag.  Stacks 08W6 asserts that the diagonal
`Δ : 𝒳 ⟶ 𝒳 × 𝒳` is representable by algebraic spaces.  Its proof has four steps:

1. by Lemma 045G it suffices that for every scheme `T` of the site and every pair of objects
   `x = (T, g, ℱ)`, `y = (T, h, 𝒢)` of the fibre over `T` the isomorphism sheaf
   `Isom_𝒳(x, y)` is an algebraic space over `T`;
2. an isomorphism of the restrictions `x|_{T'} ≅ y|_{T'}` forces `g ∘ a = h ∘ a` for
   `a : T' ⟶ T`, so there is a transformation of presheaves
   `Isom_𝒳(x, y) ⟶ Equalizer(g, h)`;
3. the diagonal of `Y` is representable, so that equalizer is a scheme of the site; replacing
   `T` by it and `ℱ`, `𝒢` by their pullbacks one may assume `g = h`;
4. in that case `Isom_𝒳(x, y) = Isom(ℱ, 𝒢)` and the conclusion is Proposition 08K9.

**Steps 2 and 3 are what this file carries, unconditionally.**  Step 1 is already in the
library, as `AlgebraicGeometry.Stack.hasRepresentableDiagonal_iff_isAlgebraicSpaceIsomPresheaf`
of `StacksFrontier/AlgebraicGeometry/Stacks/DiagonalCriteria.lean`, together with the two
bridges of `StacksFrontier/AlgebraicGeometry/Stacks/CoherentStackDiagonal.lean`.  Step 4 is not
available;
see the implementation notes for the measurement, and **no declaration here claims Stacks
08W6**.

## Main definitions

* `AlgebraicGeometry.Space.pointEqualizer` and
  `AlgebraicGeometry.Space.pointEqualizerMap`: the equalizer of two sections of an algebraic
  space over a scheme of the site, as a scheme of the site, with its monomorphism to that
  scheme.  This is step 3 in its general form.
* `AlgebraicGeometry.Space.coherentObjectPoint`: the morphism `U ⟶ Y` carried by an object of
  `Coh_{X/Y}` whose test scheme has `U` as its underlying scheme.
* `AlgebraicGeometry.Space.coherentEqualizer` and
  `AlgebraicGeometry.Space.coherentEqualizerMap`: the equalizer `Equalizer(g, h)` of the
  source's display, for two objects whose test schemes lie over one and the same scheme `U`.
* `AlgebraicGeometry.Space.coherentEqualizerTestScheme`,
  `AlgebraicGeometry.Space.coherentEqualizerToFst` and
  `AlgebraicGeometry.Space.coherentEqualizerToSnd`: the single test scheme over `Y` carried by
  the equalizer and its two comparisons with the given test schemes — the source's "we may
  assume `g = h`".
* `AlgebraicGeometry.Space.coherentEqualizerObjectFst`,
  `AlgebraicGeometry.Space.coherentEqualizerObjectSnd` and
  `AlgebraicGeometry.Space.coherentEqualizerHomSituation`: the two pullbacks of the given
  objects to that test scheme, and the standing datum of Stacks 08JT they form — the standing
  datum whose relative Isom functor step 4 is about.

## Main results

* `AlgebraicGeometry.Space.pointEqualizerMap_comp_eq`,
  `AlgebraicGeometry.Space.mono_pointEqualizerMap` and
  `AlgebraicGeometry.Space.exists_factor_pointEqualizer`: the equalizer does equalize, its
  morphism to `U` is a monomorphism, and it has the universal property of an equalizer.
* `AlgebraicGeometry.Space.coherentObjectPoint_naturality`: the morphism to `Y` carried by an
  object is natural along the morphisms of `Coh_{X/Y}`.
* `AlgebraicGeometry.Space.coherentIsom_point_comp_eq`: **step 2** — a section of
  `Isom_𝒳(x, y)` over `a` equalizes the two morphisms to `Y`.
* `AlgebraicGeometry.Space.existsUnique_factor_coherentEqualizer`: **step 2**, in the form of
  the source's display — a section of `Isom_𝒳(x, y)` over `a` makes `a` factor through
  `Equalizer(g, h)`, and in exactly one way.
* `AlgebraicGeometry.Space.coherentEqualizerMap_point_eq`: **step 3** — the two morphisms to `Y`
  agree over the equalizer, which is what lets the single test scheme above be formed.
* `AlgebraicGeometry.Space.isFinitePresentation_coherentEqualizerHomSituation`: hypothesis (1)
  of Proposition 08K9 holds for that standing datum.

## Implementation notes

**Why Stacks 08W6 is not claimed here: step 4 has no carrier, and its own input has none
either.**  Step 4 is Proposition 08K9, that the relative Isom functor of two finitely presented
modules, flat over the base with support proper over it, is an algebraic space affine and of
finite presentation over the base.  The relative Isom functor itself is in the library
(`AlgebraicGeometry.Space.HomSituation.isomFunctor`, Stacks 08K7, in
`StacksFrontier/AlgebraicGeometry/Quot/RelativeIsom.lean`), and so is the identification of it
with the fibre product the source's proof of 08K9 uses
(`AlgebraicGeometry.Space.HomSituation.mutualInverseFunctorIsoIsom`,
`StacksFrontier/AlgebraicGeometry/Quot/RelativeIsomMutualInverse.lean`).  What is missing is
the algebraicity of the four relative *Hom* functors that identification is fed, Stacks 08K6.
The predicate is
`AlgebraicGeometry.Space.HomSituation.IsAffineAlgebraicSpaceOverBase` and
`AlgebraicGeometry.Space.HomSituation.IsAffineFinitePresentationAlgebraicSpaceOverBase`
(`StacksFrontier/AlgebraicGeometry/Quot/RelativeHomRepresentable.lean`), and it has
**no producer anywhere in the library**: every result about it transports an instance of it
along a comparison —
`AlgebraicGeometry.Space.HomSituation.isAffineAlgebraicSpaceOverBase_of_isColimit`
assumes it at each
stage of a colimit, and
`AlgebraicGeometry.Space.IsAffineAlgebraicSpaceOver.of_iso`
(`StacksFrontier/AlgebraicGeometry/Quot/RelativeHomRepresentable.lean`) transports it along an isomorphism of functors — and the
base case, Lemma 08JY, rests on Lemma 08JX, whose conclusion is likewise unproved: the file
`StacksFrontier/AlgebraicGeometry/Quot/DerivedPullbackSectionFunctor.lean` builds the functor of
08JX, states its two hypotheses and names its conclusion as a
predicate, but nothing produces that predicate.  Nothing below the present file can
therefore close step 4, and a theorem carrying 08K9's conclusion as a hypothesis would not be
Stacks 08W6.

**What a consumer still owes once step 4 lands.**  The identification of step 4 is between the
abstract isomorphism presheaf `Isom_𝒳(x, y)` of the fibre of `Coh_{X/Y}` over the equalizer and
the concrete relative Isom functor of
`AlgebraicGeometry.Space.coherentEqualizerHomSituation`.  The two sides have the same sections:
a morphism of the fibre out of a cartesian lift of `a` is a pair of a morphism of test schemes
and an invertible comparison of modules, by
`AlgebraicGeometry.Space.CoherentHom` and
`AlgebraicGeometry.Space.CoherentSituation.eq_fillIn`
(`StacksFrontier/AlgebraicGeometry/Quot/CoherentStackFibered.lean`), and over the equalizer
the morphism of test schemes is the unique factorization that
`AlgebraicGeometry.Space.existsUnique_factor_coherentEqualizer` provides.  Writing that
comparison out is a substantial piece of work whose only consumer would be step 4, so it is not
done here.

**The two objects are compared through their underlying schemes, not through their test
schemes.**  Two objects of the fibre of `Coh_{X/Y}` over `U` have test schemes `(T, g)` and
`(T', h)` with `T = T' = U` as schemes of the site but with no relation between `g` and `h`;
that is exactly what the equalizer measures.  So `AlgebraicGeometry.Space.coherentObjectPoint`
takes the identification of the underlying scheme with `U` as an argument, and every statement
below is stated for two objects with two such identifications rather than for two objects of
one fibre.  This keeps the whole of steps 2 and 3 free of the category structure on
`AlgebraicGeometry.Space.CoherentObject`, which is a `letI`-bound instance and not an
instance in scope.

**Finite presentation of the projection** is read off Stacks 03XR, through
the stability of finite presentation under base change
(`AlgebraicGeometry.Space.isFinitePresentation_isStableUnderBaseChange`); the remaining
hypotheses of
Proposition 08K9 — finite presentation, flatness over the base and properness of the support of
the two modules — are *defining conditions* of
`AlgebraicGeometry.Space.CoherentObject`, so for the two pullbacks they are the fields
`finitePresentation`, `flat` and `properSupport` of
`AlgebraicGeometry.Space.coherentEqualizerObjectFst` and
`AlgebraicGeometry.Space.coherentEqualizerObjectSnd`, and the two `rfl` lemmas
`AlgebraicGeometry.Space.coherentEqualizerHomSituation_F` and `_G` are what identifies the
modules of the standing datum with theirs.

## References

* [Stacks Project, Tag 08W6](https://stacks.math.columbia.edu/tag/08W6)
* [Stacks Project, Tag 08KB](https://stacks.math.columbia.edu/tag/08KB)
* [Stacks Project, Tag 08W5](https://stacks.math.columbia.edu/tag/08W5)
* [Stacks Project, Tag 045G](https://stacks.math.columbia.edu/tag/045G)
* [Stacks Project, Tag 08JT](https://stacks.math.columbia.edu/tag/08JT)
* [Stacks Project, Tag 08K7](https://stacks.math.columbia.edu/tag/08K7)
* [Stacks Project, Tag 08K9](https://stacks.math.columbia.edu/tag/08K9)
* [Stacks Project, Tag 03XR](https://stacks.math.columbia.edu/tag/03XR)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits Opposite

namespace AlgebraicGeometry.Space

universe u

attribute [local instance] pointTopology

variable {B : BigFppfSite.{u}} {S : Scheme.{u}} {hS : B.Contains S}

/-! ### The equalizer of two scheme-valued points of an algebraic space -/

section PointEqualizer

variable (Y : AlgebraicSpaces B S hS) {U : BigFppfOver B S hS}
  (g h : yoneda.obj U ⟶ Y.1)

/-- The equalizer of two sections `g`, `h` of an algebraic space `Y` over a scheme `U` of the
site: the base change of the diagonal of `Y` along `(g, h) : U ⟶ Y × Y`, which is a scheme of
the site because the diagonal of an algebraic space is representable. -/
def pointEqualizer : BigFppfOver B S hS :=
  Y.property.diagonal_representable.pullback (prod.lift g h)

/-- The morphism `Equalizer(g, h) ⟶ U`. -/
def pointEqualizerMap : pointEqualizer Y g h ⟶ U :=
  Y.property.diagonal_representable.snd (prod.lift g h)

/-- The equalizer sits in the cartesian square defining it. -/
theorem isPullback_pointEqualizer :
    IsPullback (Y.property.diagonal_representable.fst (prod.lift g h))
      (yoneda.map (pointEqualizerMap Y g h)) (diag Y.1) (prod.lift g h) :=
  Y.property.diagonal_representable.isPullback _

/-- The two sections agree after restriction to the equalizer. -/
theorem pointEqualizerMap_comp_eq :
    yoneda.map (pointEqualizerMap Y g h) ≫ g = yoneda.map (pointEqualizerMap Y g h) ≫ h := by
  have hw := (isPullback_pointEqualizer Y g h).w
  have h₁ := congrArg (fun q => q ≫ (prod.fst : Y.1 ⨯ Y.1 ⟶ Y.1)) hw
  have h₂ := congrArg (fun q => q ≫ (prod.snd : Y.1 ⨯ Y.1 ⟶ Y.1)) hw
  simp only [Category.assoc, diag, prod.lift_fst, prod.lift_snd, Category.comp_id] at h₁ h₂
  exact h₁.symm.trans h₂

/-- The morphism from the equalizer to `U` is a monomorphism, the diagonal of `Y` being one. -/
instance mono_pointEqualizerMap : Mono (pointEqualizerMap Y g h) :=
  yoneda.mono_of_mono_map (isPullback_pointEqualizer Y g h).mono_snd_of_mono

/-- **The universal property of the equalizer.**  A morphism of schemes of the site over which
the two sections agree factors through the equalizer, and by the monomorphism above it does so
in only one way. -/
theorem exists_factor_pointEqualizer {V : BigFppfOver B S hS} (a : V ⟶ U)
    (ha : yoneda.map a ≫ g = yoneda.map a ≫ h) :
    ∃ b : V ⟶ pointEqualizer Y g h, b ≫ pointEqualizerMap Y g h = a := by
  refine ⟨Y.property.diagonal_representable.lift (yoneda.map a ≫ g) a ?_, ?_⟩
  · refine prod.hom_ext ?_ ?_
    · simp [diag]
    · simpa [diag] using ha
  · exact Y.property.diagonal_representable.lift_snd _ _ _

end PointEqualizer

/-! ### The base map of an object of `Coh_{X/Y}`, read over a scheme of the site -/

section ObjectPoint

variable {D : CoherentSituation B S hS}

/-- The morphism `U ⟶ Y` of algebraic spaces that an object of `Coh_{X/Y}` whose test scheme has
`U` as its underlying scheme carries: the structure morphism `T ⟶ Y` of the test scheme, read
through the identification of `T` with `U`. -/
def coherentObjectPoint (A : CoherentObject D) {U : BigFppfOver B S hS} (hA : A.T.left = U) :
    (schemeSpaceFunctor B S hS).obj U ⟶ D.Y :=
  (schemeSpaceFunctor B S hS).map (eqToHom hA.symm) ≫ A.T.hom

/-- **The base map is natural.**  A morphism of `Coh_{X/Y}` whose base map underlies `a` carries
the morphism to `Y` of its target to the one of its source. -/
theorem coherentObjectPoint_naturality {A A' : CoherentObject D} (m : CoherentHom A A')
    {U V : BigFppfOver B S hS} (hA : A.T.left = U) (hA' : A'.T.left = V) (a : U ⟶ V)
    (ha : m.base.left = eqToHom hA ≫ a ≫ eqToHom hA'.symm) :
    (schemeSpaceFunctor B S hS).map a ≫ coherentObjectPoint A' hA' =
      coherentObjectPoint A hA := by
  have hw := CostructuredArrow.w m.base
  have key : (schemeSpaceFunctor B S hS).map (eqToHom hA.symm) ≫
      (schemeSpaceFunctor B S hS).map m.base.left =
      (schemeSpaceFunctor B S hS).map a ≫
        (schemeSpaceFunctor B S hS).map (eqToHom hA'.symm) := by
    rw [← CategoryTheory.Functor.map_comp, ← CategoryTheory.Functor.map_comp, ha]
    congr 1
    simp
  rw [coherentObjectPoint, coherentObjectPoint, ← hw, ← Category.assoc, ← Category.assoc, key]

end ObjectPoint

/-! ### The equalizer of the two base maps of Stacks 08W6 -/

section CoherentEqualizer

variable (D : CoherentSituation B S hS) {U : BigFppfOver B S hS}
  (A A' : CoherentObject D) (hA : A.T.left = U) (hA' : A'.T.left = U)

/-- **The equalizer of the two base maps of Stacks 08W6.**  For two objects of `Coh_{X/Y}` whose
test schemes have one and the same underlying scheme `U` of the site, this is the equalizer of
their two morphisms `U ⟶ Y`.  It is a scheme of the site because the diagonal of `Y` is
representable. -/
def coherentEqualizer : BigFppfOver B S hS :=
  pointEqualizer D.Y (coherentObjectPoint A hA).hom (coherentObjectPoint A' hA').hom

/-- The morphism `Equalizer(g, h) ⟶ U` of the source's display. -/
def coherentEqualizerMap : coherentEqualizer D A A' hA hA' ⟶ U :=
  pointEqualizerMap D.Y (coherentObjectPoint A hA).hom (coherentObjectPoint A' hA').hom

/-- The morphism from the equalizer to `U` is a monomorphism. -/
instance mono_coherentEqualizerMap : Mono (coherentEqualizerMap D A A' hA hA') :=
  mono_pointEqualizerMap D.Y _ _

/-- **The two base maps agree over the equalizer.**  This is the source's "thus we may replace
`T` by this equalizer […]; thus we may assume `g = h`". -/
theorem coherentEqualizerMap_point_eq :
    (schemeSpaceFunctor B S hS).map (coherentEqualizerMap D A A' hA hA') ≫
        coherentObjectPoint A hA =
      (schemeSpaceFunctor B S hS).map (coherentEqualizerMap D A A' hA hA') ≫
        coherentObjectPoint A' hA' :=
  ObjectProperty.hom_ext _ <| pointEqualizerMap_comp_eq D.Y (coherentObjectPoint A hA).hom
    (coherentObjectPoint A' hA').hom

/-- The structure morphism to `Y` that the equalizer of the two base maps carries. -/
def coherentEqualizerTestSchemeMap :
    (schemeSpaceFunctor B S hS).obj (coherentEqualizer D A A' hA hA') ⟶ D.Y :=
  (schemeSpaceFunctor B S hS).map (coherentEqualizerMap D A A' hA hA') ≫
    coherentObjectPoint A hA

/-- **The common test scheme over the equalizer.**  Over the equalizer the two base maps agree,
so the equalizer carries a single structure morphism to `Y`; this is the test scheme the
source's reduction to the case `g = h` replaces `T` by. -/
def coherentEqualizerTestScheme : SchemesOver D.Y :=
  CostructuredArrow.mk (coherentEqualizerTestSchemeMap D A A' hA hA')

/-- The underlying scheme of the common test scheme is the equalizer. -/
@[simp]
theorem coherentEqualizerTestScheme_left :
    (coherentEqualizerTestScheme D A A' hA hA').left = coherentEqualizer D A A' hA hA' :=
  rfl

/-- The structure morphism of the common test scheme. -/
@[simp]
theorem coherentEqualizerTestScheme_hom :
    (coherentEqualizerTestScheme D A A' hA hA').hom =
      coherentEqualizerTestSchemeMap D A A' hA hA' :=
  rfl

/-- The structure morphism of the common test scheme, factored through the test scheme of the
first object. -/
theorem coherentEqualizerTestSchemeMap_eq_fst :
    (schemeSpaceFunctor B S hS).map (coherentEqualizerMap D A A' hA hA' ≫ eqToHom hA.symm) ≫
        A.T.hom = coherentEqualizerTestSchemeMap D A A' hA hA' := by
  rw [coherentEqualizerTestSchemeMap, coherentObjectPoint, CategoryTheory.Functor.map_comp,
    Category.assoc]

/-- The structure morphism of the common test scheme, factored through the test scheme of the
second object.  This factorization exists exactly because the two base maps agree over the
equalizer. -/
theorem coherentEqualizerTestSchemeMap_eq_snd :
    (schemeSpaceFunctor B S hS).map (coherentEqualizerMap D A A' hA hA' ≫ eqToHom hA'.symm) ≫
        A'.T.hom = coherentEqualizerTestSchemeMap D A A' hA hA' := by
  rw [coherentEqualizerTestSchemeMap, coherentEqualizerMap_point_eq, coherentObjectPoint,
    CategoryTheory.Functor.map_comp, Category.assoc]

/-- The morphism of test schemes over `Y` from the common test scheme over the equalizer to the
test scheme of the first object. -/
def coherentEqualizerToFst : coherentEqualizerTestScheme D A A' hA hA' ⟶ A.T :=
  CostructuredArrow.homMk (coherentEqualizerMap D A A' hA hA' ≫ eqToHom hA.symm)
    (coherentEqualizerTestSchemeMap_eq_fst D A A' hA hA')

/-- The morphism of test schemes over `Y` from the common test scheme over the equalizer to the
test scheme of the second object.  It exists exactly because the two base maps agree over the
equalizer. -/
def coherentEqualizerToSnd : coherentEqualizerTestScheme D A A' hA hA' ⟶ A'.T :=
  CostructuredArrow.homMk (coherentEqualizerMap D A A' hA hA' ≫ eqToHom hA'.symm)
    (coherentEqualizerTestSchemeMap_eq_snd D A A' hA hA')

/-- The underlying morphism of schemes of the comparison with the first object. -/
@[simp]
theorem coherentEqualizerToFst_left :
    (coherentEqualizerToFst D A A' hA hA').left =
      coherentEqualizerMap D A A' hA hA' ≫ eqToHom hA.symm :=
  rfl

/-- The underlying morphism of schemes of the comparison with the second object. -/
@[simp]
theorem coherentEqualizerToSnd_left :
    (coherentEqualizerToSnd D A A' hA hA').left =
      coherentEqualizerMap D A A' hA hA' ≫ eqToHom hA'.symm :=
  rfl

end CoherentEqualizer

/-! ### The transformation of presheaves into the equalizer -/

section IsomToEqualizer

variable (D : CoherentSituation B S hS)

/-- The morphism `U ⟶ Y` carried by an object of the fibre of `Coh_{X/Y}` over a scheme `U` of
the site. -/
def coherentFiberPoint {U : BigFppfOver B S hS}
    (x : letI : Category.{u + 1} (CoherentObject D) := D.categoryData.category
      (coherentSiteProjection D.categoryData).Fiber U) :
    (schemeSpaceFunctor B S hS).obj U ⟶ D.Y :=
  coherentObjectPoint x.1 x.2

/-- **A morphism of `Coh_{X/Y}` lying over `a` carries the morphism to `Y` carried by its target
to the one carried by its source.** -/
theorem coherentFiberPoint_naturality {U V : BigFppfOver B S hS}
    (x : letI : Category.{u + 1} (CoherentObject D) := D.categoryData.category
      (coherentSiteProjection D.categoryData).Fiber U)
    (y : letI : Category.{u + 1} (CoherentObject D) := D.categoryData.category
      (coherentSiteProjection D.categoryData).Fiber V)
    (a : U ⟶ V)
    (f : letI : Category.{u + 1} (CoherentObject D) := D.categoryData.category
      x.1 ⟶ y.1)
    (hf : letI : Category.{u + 1} (CoherentObject D) := D.categoryData.category
      (coherentSiteProjection D.categoryData).IsHomLift a f) :
    (schemeSpaceFunctor B S hS).map a ≫ coherentFiberPoint D y = coherentFiberPoint D x := by
  let : Category.{u + 1} (CoherentObject D) := D.categoryData.category
  have := hf
  exact coherentObjectPoint_naturality (show CoherentHom x.1 y.1 from f) x.2 y.2 a
    (IsHomLift.fac' (coherentSiteProjection D.categoryData) a f)

/-- **A section of `Isom(x, y)` over `a` equalizes the two morphisms to `Y`.**  This is the step
of the source's proof of Stacks 08W6 that produces the transformation of presheaves
`Isom_𝒳(x, y) ⟶ Equalizer(g, h)`: if the restrictions of `x` and `y` along `a` become isomorphic
in the fibre over `a.left`, then `g ∘ a = h ∘ a`. -/
theorem coherentIsom_point_comp_eq {U : BigFppfOver B S hS}
    (x y : letI : Category.{u + 1} (CoherentObject D) := D.categoryData.category
      (coherentSiteProjection D.categoryData).Fiber U) (a : Over U)
    (i : letI : Category.{u + 1} (CoherentObject D) := D.categoryData.category
      letI : (coherentSiteProjection D.categoryData).IsFibered :=
        D.isFiberedInGroupoids_siteProjection.isFibered
      ((coherentSiteProjection D.categoryData).isomPresheaf x y).obj (op a)) :
    (schemeSpaceFunctor B S hS).map a.hom ≫ coherentFiberPoint D x =
      (schemeSpaceFunctor B S hS).map a.hom ≫ coherentFiberPoint D y := by
  let : Category.{u + 1} (CoherentObject D) := D.categoryData.category
  let : (coherentSiteProjection D.categoryData).IsFibered :=
    D.isFiberedInGroupoids_siteProjection.isFibered
  have key := fun z : (coherentSiteProjection D.categoryData).Fiber U =>
    coherentFiberPoint_naturality D ((coherentSiteProjection D.categoryData).pullbackFiber z a.hom)
      z a.hom (Functor.IsPreFibered.pullbackMap z.2 a.hom) inferInstance
  have hm : (coherentSiteProjection D.categoryData).pullbackFiber x a.hom ⟶
      (coherentSiteProjection D.categoryData).pullbackFiber y a.hom := i.1
  have hi := coherentFiberPoint_naturality D
    ((coherentSiteProjection D.categoryData).pullbackFiber x a.hom)
    ((coherentSiteProjection D.categoryData).pullbackFiber y a.hom) (𝟙 a.left)
    (Functor.Fiber.fiberInclusion.map hm) hm.2
  rw [CategoryTheory.Functor.map_id, Category.id_comp] at hi
  rw [key x, key y]
  exact hi.symm

/-- **The factorization through the equalizer.**  A section of `Isom(x, y)` over `a` makes `a`
factor through the equalizer of the two morphisms `U ⟶ Y` carried by `x` and `y`, and it does so
in exactly one way, the equalizer mapping to `U` by a monomorphism.

This is the transformation of presheaves `Isom_𝒳(x, y) ⟶ Equalizer(g, h)` the source displays,
read on sections. -/
theorem existsUnique_factor_coherentEqualizer {U : BigFppfOver B S hS}
    (x y : letI : Category.{u + 1} (CoherentObject D) := D.categoryData.category
      (coherentSiteProjection D.categoryData).Fiber U) (a : Over U)
    (i : letI : Category.{u + 1} (CoherentObject D) := D.categoryData.category
      letI : (coherentSiteProjection D.categoryData).IsFibered :=
        D.isFiberedInGroupoids_siteProjection.isFibered
      ((coherentSiteProjection D.categoryData).isomPresheaf x y).obj (op a)) :
    ∃! b : a.left ⟶ coherentEqualizer D x.1 y.1 x.2 y.2,
      b ≫ coherentEqualizerMap D x.1 y.1 x.2 y.2 = a.hom := by
  have : Mono (coherentEqualizerMap D x.1 y.1 x.2 y.2) := mono_pointEqualizerMap D.Y _ _
  obtain ⟨b, hb⟩ := exists_factor_pointEqualizer D.Y
    (coherentObjectPoint x.1 x.2).hom (coherentObjectPoint y.1 y.2).hom a.hom
    (congrArg InducedCategory.Hom.hom (coherentIsom_point_comp_eq D x y a i))
  exact ⟨b, hb, fun c hc => (cancel_mono (coherentEqualizerMap D x.1 y.1 x.2 y.2)).1
    (hc.trans hb.symm)⟩

end IsomToEqualizer

/-! ### The standing data of Stacks 08JT that the proof reduces to -/

section EqualizerHomSituation

variable (D : CoherentSituation B S hS) {U : BigFppfOver B S hS}
  (A A' : CoherentObject D) (hA : A.T.left = U) (hA' : A'.T.left = U)
  (hst : ModulePullbackStabilityOfFinitePresentation B S hS)

/-- The pullback of the first object of `Coh_{X/Y}` to the common test scheme over the
equalizer. -/
def coherentEqualizerObjectFst : CoherentObject D :=
  CoherentSituation.pullbackObject' hst A (coherentEqualizerToFst D A A' hA hA')

/-- The pullback of the second object of `Coh_{X/Y}` to the common test scheme over the
equalizer. -/
def coherentEqualizerObjectSnd : CoherentObject D :=
  CoherentSituation.pullbackObject' hst A' (coherentEqualizerToSnd D A A' hA hA')

/-- The first pullback has the common test scheme over the equalizer as its test scheme. -/
@[simp]
theorem coherentEqualizerObjectFst_T :
    (coherentEqualizerObjectFst D A A' hA hA' hst).T =
      coherentEqualizerTestScheme D A A' hA hA' :=
  rfl

/-- The second pullback has the common test scheme over the equalizer as its test scheme. -/
@[simp]
theorem coherentEqualizerObjectSnd_T :
    (coherentEqualizerObjectSnd D A A' hA hA' hst).T =
      coherentEqualizerTestScheme D A A' hA hA' :=
  rfl

/-- **The standing data of Stacks 08JT that the proof of Stacks 08W6 reduces to.**  Its source is
the base change `X_T` of `X` to the common test scheme `T` over the equalizer of the two base
maps, its base is the equalizer itself, and its two modules are the pullbacks to `X_T` of the
modules of the two given objects of `Coh_{X/Y}`.

The relative Isom functor `Isom(ℱ, 𝒢)` of Stacks 08K7 of this standing datum,
`AlgebraicGeometry.Space.HomSituation.isomFunctor`, is the one whose algebraicity
Proposition 08K9 asserts and which the source's proof of Stacks 08W6 appeals to after its
reduction to the case `g = h`. -/
def coherentEqualizerHomSituation : HomSituation B S hS where
  X := D.space (coherentEqualizerTestScheme D A A' hA hA')
  base := (schemeSpaceFunctor B S hS).obj (coherentEqualizer D A A' hA hA')
  f := D.projection (coherentEqualizerTestScheme D A A' hA hA')
  F := (coherentEqualizerObjectFst D A A' hA hA' hst).F
  G := (coherentEqualizerObjectSnd D A A' hA hA' hst).F
  quasicoherent_F := (coherentEqualizerObjectFst D A A' hA hA' hst).quasicoherent
  quasicoherent_G := (coherentEqualizerObjectSnd D A A' hA hA' hst).quasicoherent

/-- The source module of the standing datum is the module of the pullback of the first object. -/
theorem coherentEqualizerHomSituation_F :
    (coherentEqualizerHomSituation D A A' hA hA' hst).F =
      (coherentEqualizerObjectFst D A A' hA hA' hst).F :=
  rfl

/-- The target module of the standing datum is the module of the pullback of the second
object. -/
theorem coherentEqualizerHomSituation_G :
    (coherentEqualizerHomSituation D A A' hA hA' hst).G =
      (coherentEqualizerObjectSnd D A A' hA hA' hst).F :=
  rfl

/-- The morphism of the standing datum is the projection of the base change to the common test
scheme over the equalizer. -/
theorem coherentEqualizerHomSituation_f :
    (coherentEqualizerHomSituation D A A' hA hA' hst).f =
      D.projection (coherentEqualizerTestScheme D A A' hA hA') :=
  rfl

/-- **The morphism of the standing datum is of finite presentation**, which is hypothesis (1) of
Proposition 08K9.  It is the base change of `f : X ⟶ Y` along the common test scheme over the
equalizer, and finite presentation is stable under base change (Stacks 03XR). -/
theorem isFinitePresentation_coherentEqualizerHomSituation :
    IsFinitePresentation B S hS (coherentEqualizerHomSituation D A A' hA hA' hst).f.hom :=
  MorphismProperty.IsStableUnderBaseChange.of_isPullback
    (P := fun ⦃F G : AlgebraicSpaces B S hS⦄ (k : F ⟶ G) => IsFinitePresentation B S hS k.hom)
    (AlgebraicSpaces.isPullback_fiberProduct B S hS D.f
      ((schemesOverToOver D.Y).obj (coherentEqualizerTestScheme D A A' hA hA')).hom)
    D.finitePresentation

end EqualizerHomSituation

end AlgebraicGeometry.Space

end
