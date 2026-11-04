module

public import StacksCore.Tactic.StacksAttribute
public import StacksFrontier.AlgebraicGeometry.MoreMorphisms.ThickeningMorphism.EtaleLocalProperties
public import StacksFrontier.AlgebraicGeometry.MoreMorphisms.ThickeningMorphism.UnramifiedPointTest
public import StacksFrontier.AlgebraicGeometry.Spaces.ClosedImmersionCriteria
public import StacksFrontier.AlgebraicGeometry.Spaces.ImmersionBaseChange
public import StacksFrontier.AlgebraicGeometry.Spaces.MapDescSeparated
public import StacksFrontier.AlgebraicGeometry.Spaces.Thickenings.FiniteOrderMorphismImmersions
public import StacksFrontier.AlgebraicGeometry.Spaces.Thickenings.FpqcLocal
public import StacksFrontier.AlgebraicGeometry.Spaces.Thickenings.SeparatedAndClosed

/-!
# Closed immersions, monomorphisms and immersions across a cartesian morphism of thickenings

Let

```
X --f--→ Y
|        |
i        j
↓        ↓
X' -f'-→ Y'
```

be a morphism of thickenings of algebraic spaces over `S` with `f` and `f'` locally of finite
type and `X = Y ×_{Y'} X'`. Then `f` is a closed immersion, a monomorphism or an immersion
exactly when `f'` is: parts (3), (6) and (7) of Stacks 0BPJ.

In each case the direction from `f'` to `f` is base change along the cartesian square. The three
converse directions are chained: (3) is the characterisation of **Stacks 05W8**, (6) applies (3)
to a derived square, and (7) applies (3) to a restricted square.

**Part (3).** Stacks 05W8 characterises a closed immersion of algebraic spaces as a universally
closed, unramified, universally injective morphism, and each of the three conditions transfers:
universal closedness by part (4) of **Stacks 09ZY**, which needs nothing of the square beyond
the two thickenings; unramifiedness by part (5) of Stacks 0BPJ, which is where the cartesian
square and the two local-finite-type hypotheses are used; and universal injectivity because
`X ⟶ Y ⟶ Y'` equals `X ⟶ X' ⟶ Y'`, the inclusion of a thickening is a universally injective
closed immersion, and `i` is surjective.

**Part (6).** `f'` is a monomorphism as soon as the first projection of `X' ×_{Y'} X'` is an
isomorphism. Pulling the thickening `i` back along that projection gives a new cartesian
morphism of thickenings whose two horizontal maps are locally of finite type and whose upper map
is an isomorphism, so part (3) makes the projection a closed immersion, hence a monomorphism; it
is split by the diagonal of `f'`, and a monomorphism which is a split epimorphism is an
isomorphism.

**Part (7).** **Stacks 04CE** factors the immersion `f` as a closed immersion into an open
subspace `V ⊆ Y`; `V` is the inverse image of a unique open subspace `V' ⊆ Y'` by **Stacks
05ZP**, `f'` factors through `V'`, and part (3) at the square restricted to `V'` makes
`X' ⟶ V'` a closed immersion.

## Main results

* `AlgebraicGeometry.Space.closedImmersionProperty_iff_of_cartesianSquareOfThickeningHoms`:
  **Stacks 0BPJ**, part (3), at the point test of Section 04XB.
* `AlgebraicGeometry.Space.mono_iff_of_cartesianSquareOfThickeningHoms`: **Stacks 0BPJ**,
  part (6), at that point test.
* `AlgebraicGeometry.Space.immersionProperty_iff_of_cartesianSquareOfThickeningHoms`:
  **Stacks 0BPJ**, part (7), at that point test.
* `AlgebraicGeometry.Space.isClosedImmersion_iff_of_cartesianMorphismOfThickenings` and
  `AlgebraicGeometry.Space.isImmersion_iff_of_cartesianMorphismOfThickenings`: parts (3) and (7)
  read at the subfunctor presentation of the square, which is what part (7) applies part (3)
  through.

## Implementation notes

Each registered statement gives the square by four objects and four morphisms of the category of
algebraic spaces over `S`, its two vertical maps thickenings in the sense of
`AlgebraicGeometry.Space.IsThickeningHom`, and the property by a morphism property of that
category; this is the shape in which the point test of **Stacks 03YK** reads a property of
morphisms of algebraic spaces (`AlgebraicGeometry.Stack.HasRelativeProperty`). The two bridges
between that shape and the subfunctor presentation of
`AlgebraicGeometry.Space.CartesianLocallyFiniteTypeMorphismOfThickenings` are in
`StacksFrontier.AlgebraicGeometry.MoreMorphisms.ThickeningMorphism.CartesianHom`.

**The relation to Stacks 09ZZ.** Parts (1), (9) and (10) of Stacks 09ZZ are the same three
assertions under a different hypothesis — finite order on the target thickening instead of local
finite type on the two horizontal maps — and are proved in
`StacksFrontier.AlgebraicGeometry.Spaces.Thickenings.FiniteOrderMorphismImmersions` and
`…Thickenings.FiniteOrderMorphismMonomorphism` by the same three arguments. Neither hypothesis
implies the other, so neither tag subsumes the other; but the three arguments are shared, and
the versions there would be the instances of a common core taking the closed-immersion transfer
as a parameter. That refactoring is not done here: those two files were not in scope for this
change.

In particular the entry of Stacks 05W8 used for part (3) is the third, the universally closed
unramified universally injective one, and not the entry characterising a closed immersion as a
universally closed monomorphism locally of finite type — which would be circular with part (6),
proved from part (3).

The universal injectivity of the inclusion of a thickening and the cancellation of universal
injectivity against a surjection are reused from
`StacksFrontier.AlgebraicGeometry.Spaces.Thickenings.FiniteOrderMorphismImmersions`
(`AlgebraicGeometry.Space.universallyInjective_of_isSurjective_comp`); neither uses the
finite-order hypothesis of the file they live in.

## References

* [Stacks Project, Tag 03YK](https://stacks.math.columbia.edu/tag/03YK)
* [Stacks Project, Tag 04CE](https://stacks.math.columbia.edu/tag/04CE)
* [Stacks Project, Tag 05W8](https://stacks.math.columbia.edu/tag/05W8)
* [Stacks Project, Tag 05ZP](https://stacks.math.columbia.edu/tag/05ZP)
* [Stacks Project, Tag 09ZY](https://stacks.math.columbia.edu/tag/09ZY)
* [Stacks Project, Tag 09ZZ](https://stacks.math.columbia.edu/tag/09ZZ)
* [Stacks Project, Tag 0BPJ](https://stacks.math.columbia.edu/tag/0BPJ)
-/

@[expose] public section

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits

universe u

namespace AlgebraicGeometry.Space

variable (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)
  {X X' Y Y' : AlgebraicSpaces B S hS} {i : X ⟶ X'} {j : Y ⟶ Y'} {f : X ⟶ Y} {f' : X' ⟶ Y'}

/-- **Stacks 05W8**: a closed immersion is a universally closed, unramified, universally
injective morphism. -/
private theorem isClosedImmersion_hom_iff_conditions (g : X ⟶ Y) :
    IsClosedImmersion B S hS g.hom ↔ UniversallyClosed B S hS g.hom ∧
      (IsUnramified B S hS g.hom ∧ UniversallyInjective B S hS g.hom) :=
  (closedImmersion_conditions_tfae B S hS X.property Y.property g.hom).out 1 3

/-- The inclusion of a thickening of algebraic spaces is universally injective: it is a closed
immersion, and by **Stacks 05W8** a closed immersion is a universally closed, unramified,
universally injective morphism. -/
theorem IsThickeningHom.universallyInjective (hj : IsThickeningHom B S hS j) :
    UniversallyInjective B S hS j.hom :=
  ((isClosedImmersion_hom_iff_conditions B S hS j).mp
    hj.isClosedImmersion).2.2

/-- **Stacks 0BPJ, part (3), at the point test of Section 04XB.** Let
`(f, f') : (X ⊂ X') → (Y ⊂ Y')` be a morphism of thickenings of algebraic spaces over `S` with
`f` and `f'` locally of finite type and `X = Y ×_{Y'} X'`. Then `f` is a closed immersion if and
only if `f'` is a closed immersion. -/
@[stacks 0BPJ "part (3): closed immersion, at the Section 04XB point test"]
theorem closedImmersionProperty_iff_of_cartesianSquareOfThickeningHoms
    (hi : IsThickeningHom B S hS i) (hj : IsThickeningHom B S hS j) (hsq : IsPullback f i j f')
    (hft : locallyOfFiniteTypeProperty B S hS f)
    (hft' : locallyOfFiniteTypeProperty B S hS f') :
    closedImmersionProperty B S hS f ↔ closedImmersionProperty B S hS f' := by
  refine ⟨fun hf => ?_, fun hf' => isClosedImmersion_of_isPullback B S hS hsq.flip hf'⟩
  obtain ⟨hici, hisurj⟩ := (isThickeningHom_iff_isClosedImmersion_and_isSurjective B S hS i).mp hi
  have hw : f.hom ≫ j.hom = i.hom ≫ f'.hom := congrArg (fun k => k.hom) hsq.w
  obtain ⟨huc, hunram, huinj⟩ := (isClosedImmersion_hom_iff_conditions B S hS f).mp hf
  refine (isClosedImmersion_hom_iff_conditions B S hS f').mpr ⟨?_, ?_, ?_⟩
  · exact (universallyClosed_iff_universallyClosed_of_isClosedImmersion_square B S hS X.property
      X'.property Y.property Y'.property f.hom f'.hom hici hisurj hj.isClosedImmersion hw).mp huc
  · exact (unramifiedMorphismProperty_iff_of_cartesianSquareOfThickeningHoms B S hS hi hj hsq
      hft hft').mp hunram
  · have hcomp : UniversallyInjective B S hS (f.hom ≫ j.hom) :=
      universallyInjective_comp B S hS Y.property Y'.property f.hom j.hom huinj
        (IsThickeningHom.universallyInjective B S hS hj)
    rw [hw] at hcomp
    exact universallyInjective_of_isSurjective_comp B S hS X.property X'.property Y'.property
      i.hom f'.hom hcomp hisurj

/-- **Stacks 0BPJ, part (3)**, read at the subfunctor presentation of a cartesian morphism of
thickenings of algebraic spaces, as parts (1), (4) and (5) of the tag are stated elsewhere. The
registration of the part sits on the point-test form above, of which this is the image under
the reverse bridge of
`StacksFrontier.AlgebraicGeometry.MoreMorphisms.ThickeningMorphism.CartesianHom`. -/
theorem isClosedImmersion_iff_of_cartesianMorphismOfThickenings
    (T : CartesianLocallyFiniteTypeMorphismOfThickenings B S hS) :
    IsClosedImmersion B S hS T.f ↔ IsClosedImmersion B S hS T.f' :=
  closedImmersionProperty_iff_of_cartesianSquareOfThickeningHoms B S hS
    T.isThickeningHom_sourceι T.isThickeningHom_targetι T.isPullback_spaces.flip
    T.locallyOfFiniteType_left T.locallyOfFiniteType_right

/-! ### Immersions -/

/-- The step of part (7) of **Stacks 0BPJ** which the closed-then-open factorisation of
**Stacks 04CE** feeds: if the map `f` between the smaller spaces factors as a closed immersion
into an open subspace `V ⊆ Y`, then the map `f'` between the ambient spaces is an immersion.

The open subspace `V` of the smaller target is the inverse image of a unique open subspace
`V' ⊆ Y'`, by **Stacks 05ZP**, and `f'` factors through `V'` because the two thickenings are
bijective on points. Restricting the cartesian square to `V'` gives a new cartesian morphism of
thickenings, whose target thickening is the inverse image of `Y ⊆ Y'` and whose map between the
smaller spaces is `f` read into `V'`; its two horizontal maps are locally of finite type,
because the ambient one is `f'` with an open immersion cancelled off and the other is its base
change. Part (3) makes its ambient map `X' ⟶ V'` a closed immersion, and `f'` is that followed
by the open immersion of `V'`. -/
theorem isImmersion_right_of_isClosedImmersion_into_openSubspace
    (T : CartesianLocallyFiniteTypeMorphismOfThickenings B S hS)
    (V : Subfunctor T.Y.toFunctor) (hV : IsOpenSubspace B S hS V)
    (c : T.X.toFunctor ⟶ V.toFunctor) (hc : IsClosedImmersion B S hS c)
    (hcι : c ≫ V.ι = T.f) : IsImmersion B S hS T.f' := by
  obtain ⟨V', ⟨hV'open, hV'pre⟩, -⟩ :=
    existsUnique_isOpenSubspace_preimage_eq_of_isThickening B S hS T.targetThickening V hV
  subst hV'pre
  let V'sp : AlgebraicSpaces B S hS := ⟨V'.toFunctor, hV'open.1⟩
  let W : Subfunctor V'sp.1 := T.Y.preimage V'.ι
  have hWthick : IsThickening B S hS V'sp W :=
    isThickening_preimage B S hS T.Y (ObjectProperty.homMk V'.ι : V'sp ⟶ T.Y') T.targetThickening
  have hA : IsPullback (V'.fromPreimage T.Y.ι) (V'.preimage T.Y.ι).ι V'.ι T.Y.ι :=
    Subfunctor.isPullback_preimage T.Y.ι V'
  have hB : IsPullback (T.Y.fromPreimage V'.ι) W.ι T.Y.ι V'.ι :=
    Subfunctor.isPullback_preimage V'.ι T.Y
  -- The two descriptions of `V ∩ V'` as a fibre product agree.
  let e : (V'.preimage T.Y.ι).toFunctor ≅ W.toFunctor := hA.flip.isoIsPullback _ _ hB
  have he_fst : e.hom ≫ T.Y.fromPreimage V'.ι = (V'.preimage T.Y.ι).ι :=
    hA.flip.isoIsPullback_hom_fst _ _ hB
  have he_snd : e.hom ≫ W.ι = V'.fromPreimage T.Y.ι :=
    hA.flip.isoIsPullback_hom_snd _ _ hB
  have hleft : IsClosedImmersion B S hS (c ≫ e.hom) :=
    MorphismProperty.RespectsIso.postcomp _ e.hom c hc
  have hmaps : (c ≫ V'.fromPreimage T.Y.ι) ≫ V'.ι = T.X.ι ≫ T.f' := by
    rw [Category.assoc, hA.w, ← Category.assoc, hcι]
    exact T.morphism.w
  -- The ambient map factors through `V'`, the two thickenings being bijective on points.
  have hrange : Set.range (pointsMap B S hS T.X'.1 T.f') ⊆
      Set.range (pointsMap B S hS V'.toFunctor V'.ι) := by
    rintro y' ⟨x', rfl⟩
    obtain ⟨x, rfl⟩ := T.sourceThickening.2 x'
    refine ⟨pointsMap B S hS T.X.toFunctor (c ≫ V'.fromPreimage T.Y.ι) x, ?_⟩
    have h := congrFun
      (pointsMap_comp B S hS T.X.toFunctor (c ≫ V'.fromPreimage T.Y.ι) V'.ι) x
    rw [hmaps] at h
    exact h.symm.trans (congrFun (pointsMap_comp B S hS T.X.toFunctor T.X.ι T.f') x)
  obtain ⟨g', hg'⟩ :=
    (factorsThrough_openSubspace_iff_points B S hS T.Y'.2 T.X'.2 V' hV'open T.f').2 hrange
  have hw : (c ≫ e.hom) ≫ W.ι = T.X.ι ≫ g' := by
    refine (cancel_mono V'.ι).mp ?_
    rw [Category.assoc c, he_snd, hmaps, Category.assoc, hg']
  have hs : IsPullback ((c ≫ e.hom) ≫ T.Y.fromPreimage V'.ι) T.X.ι T.Y.ι (g' ≫ V'.ι) := by
    rw [show (c ≫ e.hom) ≫ T.Y.fromPreimage V'.ι = T.f from by
      rw [Category.assoc, he_fst, hcι], hg']
    exact T.cartesian
  have hNcart : IsPullback (c ≫ e.hom) T.X.ι W.ι g' := IsPullback.of_right hs hw hB
  -- The two horizontal maps of the restricted square are locally of finite type.
  have hftg' : IsLocallyOfFiniteType B S hS g' :=
    holdsOnEveryEtaleChart_of_comp_etale g' V'.ι
      (presheaf_etale_of_isOpenImmersion B S hS hV'open.2)
      (by rw [hg']; exact T.locallyOfFiniteType_right)
  have hNcartSp : IsPullback
      (ObjectProperty.homMk (c ≫ e.hom) :
        (⟨T.X.toFunctor, T.sourceThickening.1.1⟩ : AlgebraicSpaces B S hS) ⟶
          (⟨W.toFunctor, hWthick.1.1⟩ : AlgebraicSpaces B S hS))
      (ObjectProperty.homMk T.X.ι) (ObjectProperty.homMk W.ι) (ObjectProperty.homMk g') :=
    IsPullback.of_map (ObjectProperty.ι (IsAlgebraicSpace B S hS))
      (ObjectProperty.hom_ext _ hNcart.w) hNcart
  have hftleft : IsLocallyOfFiniteType B S hS (c ≫ e.hom) :=
    (isLocallyOfFiniteType_isStableUnderBaseChange B S hS).of_isPullback hNcartSp.flip hftg'
  let N : CartesianLocallyFiniteTypeMorphismOfThickenings B S hS :=
    { X' := T.X'
      Y' := V'sp
      X := T.X
      Y := W
      sourceThickening := T.sourceThickening
      targetThickening := hWthick
      morphism := Arrow.homMk (c ≫ e.hom) g' hw
      locallyOfFiniteType_left := hftleft
      locallyOfFiniteType_right := hftg'
      cartesian := hNcart }
  have hiff : IsClosedImmersion B S hS (c ≫ e.hom) ↔ IsClosedImmersion B S hS g' :=
    isClosedImmersion_iff_of_cartesianMorphismOfThickenings B S hS N
  rw [← hg']
  have _ := isImmersion_isStableUnderComposition B S hS
  exact MorphismProperty.comp_mem _ _ _
    (isImmersion_of_isClosedImmersion B S hS (hiff.mp hleft))
    (isImmersion_of_isOpenImmersion B S hS hV'open.2)

/-- **Stacks 0BPJ, part (7)**, read at the subfunctor presentation of a cartesian morphism of
thickenings of algebraic spaces. The registration of the part sits on the point-test form
below. -/
theorem isImmersion_iff_of_cartesianMorphismOfThickenings
    (T : CartesianLocallyFiniteTypeMorphismOfThickenings B S hS) :
    IsImmersion B S hS T.f ↔ IsImmersion B S hS T.f' := by
  refine ⟨fun hf => ?_, fun hf' => T.isImmersion hf'⟩
  obtain ⟨c, hc, hcι⟩ := exists_isClosedImmersion_comp_ι_boundaryComplement B S hS
    T.targetThickening.1.1 T.sourceThickening.1.1 T.f hf
  exact isImmersion_right_of_isClosedImmersion_into_openSubspace B S hS T _
    (isOpenSubspace_boundaryComplement B S hS T.targetThickening.1.1
      (isLocallyClosed_range_pointsMap_of_isImmersion B S hS T.targetThickening.1.1 T.f hf))
    c hc hcι

/-- **Stacks 0BPJ, part (7), at the point test of Section 04XB.** Let
`(f, f') : (X ⊂ X') → (Y ⊂ Y')` be a morphism of thickenings of algebraic spaces over `S` with
`f` and `f'` locally of finite type and `X = Y ×_{Y'} X'`. Then `f` is an immersion if and only
if `f'` is an immersion. -/
@[stacks 0BPJ "part (7): immersion, at the Section 04XB point test"]
theorem immersionProperty_iff_of_cartesianSquareOfThickeningHoms
    (hi : IsThickeningHom B S hS i) (hj : IsThickeningHom B S hS j) (hsq : IsPullback f i j f')
    (hft : locallyOfFiniteTypeProperty B S hS f)
    (hft' : locallyOfFiniteTypeProperty B S hS f') :
    immersionProperty B S hS f ↔ immersionProperty B S hS f' :=
  (rangeMap_iff (MorphismProperty.relative_isStableUnderBaseChange
      (MorphismProperty.inverseImage
        (@_root_.AlgebraicGeometry.IsImmersion.{u} : MorphismProperty Scheme.{u})
        (BigFppfOver.toScheme B S hS))).respectsIso hi hj f).trans
    (isImmersion_iff_of_cartesianMorphismOfThickenings B S hS
      (CartesianLocallyFiniteTypeMorphismOfThickenings.ofIsThickeningHom hi hj hsq hft hft'))


/-! ### Monomorphisms -/

/-- The base change of a thickening of algebraic spaces is a thickening: a closed immersion and
a surjection are each stable under base change. -/
theorem IsThickeningHom.of_isPullback {Z W : AlgebraicSpaces B S hS} {g : Z ⟶ X'} {k : W ⟶ Z}
    {l : W ⟶ X} (hsq : IsPullback l k i g) (hi : IsThickeningHom B S hS i) :
    IsThickeningHom B S hS k := by
  obtain ⟨hici, hisurj⟩ := (isThickeningHom_iff_isClosedImmersion_and_isSurjective B S hS i).mp hi
  exact (isThickeningHom_iff_isClosedImmersion_and_isSurjective B S hS k).mpr
    ⟨isClosedImmersion_of_isPullback B S hS hsq hici,
      (surjectiveMorphismProperty_isStableUnderBaseChange B S hS).of_isPullback hsq hisurj⟩

/-- **Stacks 0BPJ, part (6), at the point test of Section 04XB.** Let
`(f, f') : (X ⊂ X') → (Y ⊂ Y')` be a morphism of thickenings of algebraic spaces over `S` with
`f` and `f'` locally of finite type and `X = Y ×_{Y'} X'`. Then `f` is a monomorphism if and
only if `f'` is a monomorphism.

The direction from `f'` to `f` is base change. In the other direction, `f'` is a monomorphism as
soon as the first projection of `X' ×_{Y'} X'` is an isomorphism, and that projection is
obtained as follows. Pull the thickening `i : X ⟶ X'` back along the first projection; the
resulting square

```
X ×_{X'} (X' ×_{Y'} X') --→ X
|                           |
↓                           ↓
X' ×_{Y'} X' ------fst-----→ X'
```

is again a cartesian morphism of thickenings with both horizontal maps locally of finite type,
and its upper map is an *isomorphism*: a section of the upper left corner is a pair `(a, b)` of
sections of `X'` with `f'(a) = f'(b)` and `a` a section of `X`, the cartesian square of the
given morphism of thickenings exhibits `b` as a second factorisation of that pair through `X`
with the same image under `f`, and monomorphy of `f` identifies the two. An isomorphism is a
closed immersion, so part (3) above makes `fst` a closed immersion, hence a monomorphism; it is
also split by the diagonal of `f'`, and a monomorphism which is a split epimorphism is an
isomorphism.

This is the argument of
`AlgebraicGeometry.Space.CartesianFiniteOrderMorphismOfThickenings.mono_iff` for part (9) of
**Stacks 09ZZ**, with part (3) above in place of part (1) of that tag; the source's own proof of
this case instead compares the conormal sheaf of the diagonal of `f` with that of `f'`, which
needs the algebraic-space form of **Stacks 08S2** and so is not available here. -/
@[stacks 0BPJ "part (6): monomorphism, at the Section 04XB point test"]
theorem mono_iff_of_cartesianSquareOfThickeningHoms
    (hi : IsThickeningHom B S hS i) (_hj : IsThickeningHom B S hS j) (hsq : IsPullback f i j f')
    (_hft : locallyOfFiniteTypeProperty B S hS f)
    (hft' : locallyOfFiniteTypeProperty B S hS f') :
    Mono f ↔ Mono f' := by
  refine ⟨fun hf => ?_, fun hf' => hsq.mono_fst_of_mono⟩
  have hP : IsPullback (pullback.fst f' f') (pullback.snd f' f') f' f' :=
    IsPullback.of_hasPullback f' f'
  have hZ : IsPullback (pullback.fst i (pullback.fst f' f'))
      (pullback.snd i (pullback.fst f' f')) i (pullback.fst f' f') :=
    IsPullback.of_hasPullback i (pullback.fst f' f')
  -- The two projections of `X' ×_{Y'} X'` agree on `X ×_{X'} (X' ×_{Y'} X')`.
  have hagree : pullback.snd i (pullback.fst f' f') ≫ pullback.fst f' f' =
      pullback.snd i (pullback.fst f' f') ≫ pullback.snd f' f' := by
    have hcond : (pullback.fst i (pullback.fst f' f') ≫ f) ≫ j =
        (pullback.snd i (pullback.fst f' f') ≫ pullback.snd f' f') ≫ f' := by
      rw [Category.assoc, hsq.w, ← Category.assoc, hZ.w, Category.assoc, Category.assoc,
        ← pullback.condition]
    have hfst := hsq.lift_fst (pullback.fst i (pullback.fst f' f') ≫ f)
      (pullback.snd i (pullback.fst f' f') ≫ pullback.snd f' f') hcond
    have hsnd := hsq.lift_snd (pullback.fst i (pullback.fst f' f') ≫ f)
      (pullback.snd i (pullback.fst f' f') ≫ pullback.snd f' f') hcond
    rw [← hsnd, (cancel_mono f).mp hfst, hZ.w]
  -- The projection to `X` is an isomorphism, the inverse being the diagonal of `f'`.
  have hw : (𝟙 X) ≫ i = (i ≫ pullback.diagonal f') ≫ pullback.fst f' f' := by
    simp
  have hs₁ : hZ.lift (𝟙 X) (i ≫ pullback.diagonal f') hw ≫
      pullback.fst i (pullback.fst f' f') = 𝟙 X := hZ.lift_fst _ _ hw
  have hs₂ : hZ.lift (𝟙 X) (i ≫ pullback.diagonal f') hw ≫
      pullback.snd i (pullback.fst f' f') = i ≫ pullback.diagonal f' := hZ.lift_snd _ _ hw
  have hdiag : pullback.snd i (pullback.fst f' f') ≫ pullback.fst f' f' ≫
      pullback.diagonal f' = pullback.snd i (pullback.fst f' f') := by
    refine hP.hom_ext ?_ ?_
    · simp
    · rw [Category.assoc, Category.assoc, pullback.diagonal_snd, Category.comp_id]
      exact hagree
  have hs₀ : pullback.fst i (pullback.fst f' f') ≫
      hZ.lift (𝟙 X) (i ≫ pullback.diagonal f') hw = 𝟙 _ := by
    refine hZ.hom_ext ?_ ?_
    · rw [Category.assoc, hs₁, Category.comp_id, Category.id_comp]
    · rw [Category.assoc, hs₂, ← Category.assoc, hZ.w, Category.assoc, hdiag, Category.id_comp]
  have hiso : IsIso (pullback.fst i (pullback.fst f' f')) := ⟨_, hs₀, hs₁⟩
  have hisoHom : IsIso (pullback.fst i (pullback.fst f' f')).hom :=
    ⟨(hZ.lift (𝟙 X) (i ≫ pullback.diagonal f') hw).hom,
      congrArg (fun k => k.hom) hs₀, congrArg (fun k => k.hom) hs₁⟩
  -- Part (3) at the derived square makes the first projection a closed immersion.
  have hftP : locallyOfFiniteTypeProperty B S hS (pullback.fst f' f') :=
    (isLocallyOfFiniteType_isStableUnderBaseChange B S hS).of_isPullback hP.flip hft'
  have hftZ : locallyOfFiniteTypeProperty B S hS (pullback.fst i (pullback.fst f' f')) :=
    (isLocallyOfFiniteType_isStableUnderBaseChange B S hS).of_isPullback hZ.flip hftP
  have hci : closedImmersionProperty B S hS (pullback.fst f' f') :=
    (closedImmersionProperty_iff_of_cartesianSquareOfThickeningHoms B S hS
      (IsThickeningHom.of_isPullback B S hS hZ hi) hi hZ hftZ hftP).mp
      (isClosedImmersion_of_isIso B S hS _)
  have _ : Mono (pullback.fst f' f') :=
    (mono_hom_iff_mono B S hS _).mp (mono_of_isClosedImmersion B S hS _ hci)
  have _ : IsSplitEpi (pullback.fst f' f') :=
    IsSplitEpi.mk' ⟨pullback.diagonal f', pullback.diagonal_fst f'⟩
  have _ : IsIso (pullback.fst f' f') := isIso_of_mono_of_isSplitEpi _
  exact IsKernelPair.mono_of_isIso_fst hP

end AlgebraicGeometry.Space

end
