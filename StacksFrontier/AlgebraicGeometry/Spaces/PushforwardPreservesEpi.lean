module

public import StacksFrontier.AlgebraicGeometry.Spaces.AbelianPushforwardExact
public import StacksFrontier.AlgebraicGeometry.Spaces.IntegralFinite
public import StacksFrontier.AlgebraicGeometry.Spaces.Representable
public import StacksFrontier.AlgebraicGeometry.Spaces.SmallEtalePushforwardBaseChange
public import StacksFrontier.AlgebraicGeometry.Spaces.SurjectiveOnPoints
public import StacksFrontier.CategoryTheory.Sites.Topos.PushforwardEquality
public import StacksFrontier.AlgebraicGeometry.Spaces.SchemeAsSpace

/-!
# Reducing Stacks 04C2, part (1), for algebraic spaces to the case of schemes

Let `f : X ⟶ Y` be a morphism of algebraic spaces over a scheme `S` contained in a big fppf
site `B`.  Stacks 04C2, part (1) — Étale Cohomology Lemma 59.43.5 — says that for `f` integral
the small étale direct image `f_{small,*}` transforms surjections into surjections.  Its proof
for schemes goes through Stacks 04DR and 04DO and lives in Chapter 59.  Its transport to
algebraic spaces is the reduction, along an étale covering of `Y` by a scheme, carried out
here.

The reduction is unconditional and is in three steps:

* postcomposition along a *surjective* étale morphism `g : Y' ⟶ Y` exhibits the spaces-étale
  site of `Y'` as a cover-dense subsite of that of `Y`, so restriction along it is faithful and
  therefore **reflects** epimorphisms, by Stacks 04D9;
* therefore the restriction functor `(f ≫ ·)⁻¹` of Stacks 03LQ reflects epimorphisms on the
  small étale topoi, that being the conjugate of the former by the comparison equivalences of
  Stacks 03G1;
* Stacks 03LR, part (1) identifies `g⁻¹ ∘ f_{small,*}` with `f'_{small,*} ∘ i⁻¹` for the
  cartesian square of `f` and `g`, and `i⁻¹` preserves epimorphisms because it is a left
  adjoint.  So `f_{small,*}` preserves epimorphisms as soon as `f'_{small,*}` does.

Taking for `g` a scheme atlas of `Y` leaves exactly one input owed: part (1) of Stacks 04C2
for an integral morphism whose *target is a scheme*.  That is carried as the explicit named
hypothesis `hscheme`; it is Chapter 59 mathematics and is not available here.  Note that the
source of such a morphism is then a scheme as well, by Stacks 03ZQ, so the hypothesis asks
nothing about the source.

## Main definitions

There are no new definitions.

## Main results

* `AlgebraicGeometry.Space.isCoverDense_spacesEtalePostcomp`: for `g : Y' ⟶ Y` étale and
  surjective, spaces-étale postcomposition along `g` is cover dense for the spaces-étale
  topology of `Y`.
* `AlgebraicGeometry.Space.reflectsEpimorphisms_smallToposMorphism_inverseImage`: restriction
  along such a `g` reflects epimorphisms of sheaves of sets on the small étale topoi.
* `AlgebraicGeometry.Space.smallEtalePushforward_preservesEpimorphisms_of_etaleCover` is the
  reduction itself, with no hypothesis on `f` at all.
* `AlgebraicGeometry.Space.smallEtalePushforward_preservesEpimorphisms` is **Stacks 04C2, part
  (1), for algebraic spaces**, under the hypothesis `hscheme` that it holds when the target is
  a scheme.
* `AlgebraicGeometry.Space.smallEtaleAbelianPushforward_exact_of_scheme_case` and
  `AlgebraicGeometry.Space.smallEtaleAbelianPushforward_rightDerivedPlus_isZero_of_scheme_case`
  are the two conclusions of Stacks 0A4K with the `hepi` hypothesis of
  `StacksFrontier.AlgebraicGeometry.Spaces.AbelianPushforwardExact` discharged by that reduction,
  so that the only input they still carry is the scheme-level statement.

## Implementation notes

Cover density is produced from a *one-element* covering by
`CategoryTheory.Functor.isCoverDense_of_generate_singleton_functor_π_mem`: for an object `U` of
the spaces-étale site of `Y`, the fibre product `U ×_Y Y'` is étale over `Y'` by Stacks 03FU and
its first projection is surjective on points by Stacks 03MH, so the one-element family
`{U ×_Y Y' → U}` is a covering of `U` in the sense of Stacks 03G0, part (3).  The fibre product
is taken in the category of algebraic spaces, where `AlgebraicGeometry.AlgebraicSpaces.hasPullback`
makes `CategoryTheory.Limits.pullback` available, so no explicit presheaf-level fibre product
appears in any statement.

Cover density is the *only* new input needed for the reflection of epimorphisms: restriction
along a continuous cover-dense functor of sites is faithful, and a faithful functor reflects
epimorphisms.  That is Stacks 04D9 and it is already in the library, for arbitrary coefficients,
as `sheafPushforwardContinuous_reflectsEpimorphisms_of_isCoverDense`.  Nothing here goes through
local surjectivity, so neither `HasSheafify` nor a concrete-category structure on the
coefficients is used, and the universe `Type (u + 1)` of the sheaves of sets is the only one in
play — it is the universe of the objects of both étale sites of an algebraic space over a scheme
of universe `u`.

The passage from the spaces-étale to the small étale topoi costs nothing: the inverse image of
`AlgebraicGeometry.Space.smallToposMorphism` of an étale morphism *is* the conjugate of
spaces-étale restriction by the comparison equivalences of Stacks 03G1, which is
`AlgebraicGeometry.Space.smallToposMorphism_inverseImage_conjIso`, and an equivalence both
preserves and reflects epimorphisms.

No declaration here carries a `@[stacks]` attribute.  Everything unconditional is a step of the
reduction rather than an assertion of the source, and the two statements that *are* assertions of
the source carry `hscheme`.

## References

* [Stacks Project, Tag 04C2](https://stacks.math.columbia.edu/tag/04C2)
* [Stacks Project, Tag 0A4K](https://stacks.math.columbia.edu/tag/0A4K)
* [Stacks Project, Tag 03LR](https://stacks.math.columbia.edu/tag/03LR)
* [Stacks Project, Tag 03LQ](https://stacks.math.columbia.edu/tag/03LQ)
* [Stacks Project, Tag 03G1](https://stacks.math.columbia.edu/tag/03G1)
* [Stacks Project, Tag 03G0](https://stacks.math.columbia.edu/tag/03G0)
* [Stacks Project, Tag 03ZQ](https://stacks.math.columbia.edu/tag/03ZQ)
* [Stacks Project, Tag 03FU](https://stacks.math.columbia.edu/tag/03FU)
* [Stacks Project, Tag 03MH](https://stacks.math.columbia.edu/tag/03MH)
* [Stacks Project, Tag 04D9](https://stacks.math.columbia.edu/tag/04D9)
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits

attribute [local instance] HasDerivedCategory.standard

universe u

namespace AlgebraicGeometry.Space

variable (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)

/-! ### Cover density of postcomposition along a surjective étale morphism -/

/-- For a surjective étale morphism `g : Y' ⟶ Y` of algebraic spaces, spaces-étale
postcomposition along `g` is cover dense for the spaces-étale topology of `Y`: every object `U`
étale over `Y` is covered by an object in the image, namely by `U ×_Y Y'`.

The fibre product `U ×_Y Y'` is étale over `Y'` because `U` is étale over `Y` and étaleness is
stable under base change (Stacks 03FU), so it is an object of the spaces-étale site of `Y'`
whose postcomposition with `g` is `U ×_Y Y'` seen over `Y` through either projection.  Its first
projection to `U` is surjective on points because `g` is (Stacks 03MH), so the one-element
family it forms is a covering in the sense of Stacks 03G0, part (3). -/
theorem isCoverDense_spacesEtalePostcomp {Y' Y : AlgebraicSpaces B S hS} (g : Y' ⟶ Y)
    (hg : IsEtale B S hS g.hom) (hgs : IsSurjective B S hS g.hom) :
    (spacesEtalePostcomp B S hS g hg).IsCoverDense (SpacesEtale.topology B S hS Y) := by
  refine Functor.isCoverDense_of_generate_singleton_functor_π_mem _ _ fun U => ?_
  have sq : IsPullback (pullback.fst U.1.hom g) (pullback.snd U.1.hom g) U.1.hom g :=
    IsPullback.of_hasPullback U.1.hom g
  have hsnd : IsEtale B S hS (pullback.snd U.1.hom g).hom :=
    isEtale_of_isPullback B S hS (pullback.fst U.1.hom g) (pullback.snd U.1.hom g)
      U.1.hom g sq U.2
  refine ⟨⟨Over.mk (pullback.snd U.1.hom g), hsnd⟩,
    ObjectProperty.homMk (Over.homMk (pullback.fst U.1.hom g) sq.w), ?_⟩
  have hfst : Function.Surjective
      (pointsMap B S hS (Limits.pullback U.1.hom g).1 (pullback.fst U.1.hom g).hom) :=
    surjective_pointsMap_of_isPullback B S hS
      (AlgebraicSpaces.isPullback_hom B S hS sq).flip hgs
  rw [← PreZeroHypercover.presieve₀_singleton.{u + 1}]
  exact Precoverage.generate_mem_toGrothendieck
    ⟨_, rfl, fun x => ⟨default, (hfst x).choose, (hfst x).choose_spec⟩⟩

/-! ### Restriction along a surjective étale morphism reflects epimorphisms -/

/-- The inverse image of the morphism of small étale topoi of a surjective étale morphism
`g : Y' ⟶ Y` reflects epimorphisms of sheaves of sets.

By Stacks 03LQ that inverse image is the conjugate, by the comparison equivalences of Stacks
03G1, of spaces-étale restriction along postcomposition with `g`.  That restriction is faithful
and hence reflects epimorphisms by Stacks 04D9, already available as
`sheafPushforwardContinuous_reflectsEpimorphisms_of_isCoverDense`, its cover-density hypothesis
being `AlgebraicGeometry.Space.isCoverDense_spacesEtalePostcomp` — which is where surjectivity
of `g` enters.  An equivalence both preserves and reflects epimorphisms, so the conjugation
costs nothing. -/
theorem reflectsEpimorphisms_smallToposMorphism_inverseImage
    {Y' Y : AlgebraicSpaces B S hS} (g : Y' ⟶ Y) (hg : IsEtale B S hS g.hom)
    (hgs : IsSurjective B S hS g.hom) :
    (smallToposMorphism B S hS g).inverseImage.ReflectsEpimorphisms := by
  have hdense := isCoverDense_spacesEtalePostcomp B S hS g hg hgs
  have hr := sheafPushforwardContinuous_reflectsEpimorphisms_of_isCoverDense
    (spacesEtalePostcomp B S hS g hg) (SpacesEtale.topology B S hS Y')
    (SpacesEtale.topology B S hS Y) (Type (u + 1))
  have h : ((smallEtaleToposEquiv B S hS Y).inverse ⋙
      ((spacesEtalePostcomp B S hS g hg).sheafPushforwardContinuous (Type (u + 1))
        (SpacesEtale.topology B S hS Y') (SpacesEtale.topology B S hS Y) ⋙
      (smallEtaleToposEquiv B S hS Y').functor)).ReflectsEpimorphisms := inferInstance
  exact Functor.ReflectsEpimorphisms.of_iso
    (smallToposMorphism_inverseImage_conjIso B S hS g hg).symm

/-! ### The reduction along an étale covering of the target -/

/-- **The reduction of Stacks 04C2, part (1) to a smaller target.** Let

```
X' --i--> X
|f'       |f
Y' --g--> Y
```

be a cartesian square of algebraic spaces over `S` with `g` étale and surjective.  If the small
étale direct image along `f'` transforms surjections of sheaves of sets into surjections, then
so does the small étale direct image along `f`.

No hypothesis on `f` is needed.  By Stacks 03LR, part (1) the composite
`f_{small,*}` followed by restriction to `Y'` is restriction to `X'` followed by `f'_{small,*}`.
Restriction to `X'` is the inverse image of a morphism of topoi, hence a left adjoint, hence
preserves epimorphisms; so the right-hand composite preserves epimorphisms, and therefore so
does the left-hand one.  Restriction to `Y'` reflects epimorphisms because `g` is surjective
étale, which cancels it. -/
theorem smallEtalePushforward_preservesEpimorphisms_of_etaleCover
    {X X' Y Y' : AlgebraicSpaces B S hS} (i : X' ⟶ X) (f' : X' ⟶ Y') (f : X ⟶ Y) (g : Y' ⟶ Y)
    (sq : IsPullback i f' f g) (hg : IsEtale B S hS g.hom) (hgs : IsSurjective B S hS g.hom)
    (hf' : (smallToposMorphism B S hS f').pushforward.PreservesEpimorphisms) :
    (smallToposMorphism B S hS f).pushforward.PreservesEpimorphisms := by
  have hri := reflectsEpimorphisms_smallToposMorphism_inverseImage B S hS g hg hgs
  have hi : (smallToposMorphism B S hS i).inverseImage.PreservesEpimorphisms :=
    Functor.preservesEpimorphisms_of_adjunction (smallToposMorphism B S hS i).adj
  have hcomp : ((smallToposMorphism B S hS i).inverseImage ⋙
      (smallToposMorphism B S hS f').pushforward).PreservesEpimorphisms := inferInstance
  have hrhs : ((smallToposMorphism B S hS f).pushforward ⋙
      (smallToposMorphism B S hS g).inverseImage).PreservesEpimorphisms :=
    Functor.PreservesEpimorphisms.of_iso
      (smallEtalePushforwardBaseChangeIso B S hS i f' f g sq hg)
  exact Functor.preservesEpimorphisms_of_preserves_of_reflects
    (smallToposMorphism B S hS f).pushforward (smallToposMorphism B S hS g).inverseImage

/-- **Stacks 04C2, part (1), for algebraic spaces**, with the case of a scheme target carried as
the explicit named hypothesis `hscheme`.

For an integral morphism `f : X ⟶ Y` of algebraic spaces over `S` the small étale direct image
transforms surjections of sheaves of sets into surjections, *given* that it does so for every
integral morphism whose target is (the algebraic space attached to) a scheme of the site.

The proof is the reduction
`AlgebraicGeometry.Space.smallEtalePushforward_preservesEpimorphisms_of_etaleCover` applied to a
scheme atlas `g : Y' ⟶ Y` of the target, which is surjective and étale by the definition of an
algebraic space; the base change of `f` along it is integral because integrality of a morphism of
algebraic spaces is an affine-base-change pattern, which is stable under arbitrary base change.

The hypothesis asks nothing about the *source* of the morphism: by Stacks 03ZQ an integral
morphism of algebraic spaces is relatively representable, so a source over a scheme target is a
scheme too, and `hscheme` is Stacks 04C2, part (1) for schemes. -/
theorem smallEtalePushforward_preservesEpimorphisms {X Y : AlgebraicSpaces B S hS} (f : X ⟶ Y)
    (hf : IsIntegralHom B S hS f.hom)
    (hscheme : ∀ (T : BigFppfOver B S hS) (X' : AlgebraicSpaces B S hS)
      (f' : X' ⟶ (schemeSpace T : AlgebraicSpaces B S hS)),
      IsIntegralHom B S hS f'.hom →
      (smallToposMorphism B S hS f').pushforward.PreservesEpimorphisms) :
    (smallToposMorphism B S hS f).pushforward.PreservesEpimorphisms := by
  obtain ⟨T, a, hasurj, haetale⟩ := Y.property.exists_atlas
  let Y' : AlgebraicSpaces B S hS := ⟨yoneda.obj T, isAlgebraicSpace_yoneda B S hS T⟩
  let g : Y' ⟶ Y := ObjectProperty.homMk a
  have hg : IsEtale B S hS g.hom := isEtale_of_presheaf_etale B S hS haetale
  have hgs : IsSurjective B S hS g.hom :=
    (presheafSurjective_iff_isSurjective_yoneda B S hS Y.1 Y.property T a).mp hasurj
  have sq : IsPullback (pullback.fst f g) (pullback.snd f g) f g := IsPullback.of_hasPullback f g
  have hf' : IsIntegralHom B S hS (pullback.snd f g).hom :=
    HoldsOnAffineBaseChange.of_isPullback (AlgebraicSpaces.isPullback_hom B S hS sq) hf
  exact smallEtalePushforward_preservesEpimorphisms_of_etaleCover B S hS
    (pullback.fst f g) (pullback.snd f g) f g sq hg hgs (hscheme T _ (pullback.snd f g) hf')

/-! ### The two conclusions of Stacks 0A4K with `hepi` discharged -/

/-- **Stacks 0A4K, exactness**, with the hypothesis `hepi` of
`AlgebraicGeometry.Space.smallEtaleAbelianPushforward_exact` discharged.

For an integral morphism `f : X ⟶ Y` of algebraic spaces the direct image on the abelian sheaves
of the small étale sites is exact, given Stacks 04C2, part (1) for integral morphisms with a
scheme target.  The reduction from spaces to schemes is
`AlgebraicGeometry.Space.smallEtalePushforward_preservesEpimorphisms`; the step from surjections
of sheaves of sets to exactness on abelian sheaves is Stacks 04DB, already available as
`Stacks.Topos.AbelianPushforward.abelianPushforward_exact`. -/
theorem smallEtaleAbelianPushforward_exact_of_scheme_case {X Y : AlgebraicSpaces B S hS}
    (f : X ⟶ Y) (hf : IsIntegralHom B S hS f.hom)
    (hscheme : ∀ (T : BigFppfOver B S hS) (X' : AlgebraicSpaces B S hS)
      (f' : X' ⟶ (schemeSpace T : AlgebraicSpaces B S hS)),
      IsIntegralHom B S hS f'.hom →
      (smallToposMorphism B S hS f').pushforward.PreservesEpimorphisms) :
    exactFunctor (Sheaf (SmallEtale.topology B S hS X.obj) AddCommGrpCat.{u + 1})
      (Sheaf (SmallEtale.topology B S hS Y.obj) AddCommGrpCat.{u + 1})
      (Stacks.Topos.AbelianPushforward.abelianPushforward (SmallEtale.topology B S hS X.obj)
        (smallToposMorphism B S hS f)) :=
  smallEtaleAbelianPushforward_exact B S hS f hf
    fun hf' => smallEtalePushforward_preservesEpimorphisms B S hS f hf' hscheme

/-- **Stacks 0A4K, vanishing of the positive-degree higher direct images**, with the hypothesis
`hepi` of `AlgebraicGeometry.Space.smallEtaleAbelianPushforward_rightDerivedPlus_isZero`
discharged, by the same reduction to the case of a scheme target. -/
theorem smallEtaleAbelianPushforward_rightDerivedPlus_isZero_of_scheme_case
    {X Y : AlgebraicSpaces B S hS} (f : X ⟶ Y) (hf : IsIntegralHom B S hS f.hom)
    (hscheme : ∀ (T : BigFppfOver B S hS) (X' : AlgebraicSpaces B S hS)
      (f' : X' ⟶ (schemeSpace T : AlgebraicSpaces B S hS)),
      IsIntegralHom B S hS f'.hom →
      (smallToposMorphism B S hS f').pushforward.PreservesEpimorphisms)
    (F : Sheaf (SmallEtale.topology B S hS X.obj) AddCommGrpCat.{u + 1})
    (p : ℤ) (hp : 0 < p) :
    IsZero (((Stacks.Topos.AbelianPushforward.abelianPushforward (SmallEtale.topology B S hS X.obj)
      (smallToposMorphism B S hS f)).rightDerivedPlus p).obj F) :=
  smallEtaleAbelianPushforward_rightDerivedPlus_isZero B S hS f hf
    (fun hf' => smallEtalePushforward_preservesEpimorphisms B S hS f hf' hscheme) F p hp

end AlgebraicGeometry.Space

end
