module

public import StacksFrontier.AlgebraicGeometry.Spaces.FlatModuleUniversallyOpen
public import StacksFrontier.AlgebraicGeometry.Spaces.SchemeOfSchemeReduction
public import StacksFrontier.AlgebraicGeometry.Spaces.Thickenings.FiniteOrderMorphismImmersions
public import StacksFrontier.AlgebraicGeometry.Spaces.Thickenings.QuasiSeparatedTransfer

/-!
# Affine, integral, quasi-separated, universally injective, universally open and representable
# morphisms of thickenings of algebraic spaces

A morphism of thickenings of algebraic spaces over a scheme `S` is a commutative square

```
X --a--→ Y
|        |
i        j
↓        ↓
X' --b-→ Y'
```

whose vertical arrows are the inclusions of thickenings, that is a morphism in the arrow
category between the inclusions `G.ι` and `H.ι` of closed subspaces that are surjective on
points. This file proves that `a` is affine, integral, quasi-separated, universally injective,
universally open, respectively representable exactly when `b` is: parts (1), (5), (6), (7),
(8) and (9) of Stacks 09ZY. Parts (2), (3) and (4) and the separated half of part (6) are in
`StacksFrontier/AlgebraicGeometry/Spaces/Thickenings/Morphisms.lean` and
`StacksFrontier/AlgebraicGeometry/Spaces/Thickenings/SeparatedAndClosed.lean`; the declaration
for part (6) here states both of its halves.

Each comparison is proved, as in `SeparatedAndClosed.lean`, for a commutative square
`a ≫ j = i ≫ b` whose vertical arrows are closed immersions, the left one surjective (and for
universal openness the right one surjective too). The direction from `b` to `a` is always the
same: `i ≫ b = a ≫ j` inherits the property from `b` and `i`, and `a` is the base change of
`a ≫ j` along the monomorphism `j`. The direction from `a` to `b` is where the thickening
enters.

* **Affine, part (1).** Following the source, which cites Stacks 07VT: for an affine scheme
  `Z ⟶ Y'` the base change `Z ×_{Y'} X'` contains `Z ×_{Y'} X = (Z ×_{Y'} Y) ×_Y X`, which is
  affine because `Z ×_{Y'} Y` is a closed subscheme of `Z` and `a` is affine, as a closed
  subspace with the same points; so `Z ×_{Y'} X'` is affine by the thickening case of Stacks
  07VT, `AlgebraicGeometry.Space.isAffineSpace_of_isClosedImmersion_of_isSurjective`.
* **Integral, part (5).** Stacks 0415 (integral is affine and universally closed) together
  with part (1) and part (4).
* **Quasi-separated, part (6).** The quasi-compact comparison of part (3) applied to the square
  of relative diagonals `Δₐ ≫ c = i ≫ Δ_b`, whose comparison arrow
  `c : X ×[Y] X ⟶ X' ×[Y'] X'` is a closed immersion
  (`AlgebraicGeometry.Space.isClosedImmersion_pullbackMap`).
* **Universally injective and universally open, parts (7) and (8).** `a ≫ j = i ≫ b` inherits
  the property from `a`, because `j` is a monomorphism, respectively a surjective closed
  immersion and hence universally open; and it may be cancelled along `i`, which is surjective
  on points.
* **Representable, part (9).** Following the source, which cites Stacks 05ZR: for a scheme
  `T ⟶ Y'` the base change `T ×_{Y'} X'` contains `T ×_{Y'} X`, a scheme because `a` is
  representable, as a closed subspace with the same points; so it is a scheme by
  `AlgebraicGeometry.Space.isRepresentable_of_isClosedImmersion_of_bijective` (the implication
  from the source of Stacks 07VV for a closed immersion).

Representability of a morphism of algebraic spaces is
`CategoryTheory.Functor.relativelyRepresentable` along the Yoneda embedding of the big fppf
site, as everywhere in this library.

## Main results

* `AlgebraicGeometry.Space.isAffineHom_iff_isAffineHom_of_isThickening_unconditional`:
  **Stacks 09ZY**, part (1).
* `AlgebraicGeometry.Space.isIntegralHom_iff_isIntegralHom_of_isThickening_unconditional`:
  **Stacks 09ZY**, part (5).
* `AlgebraicGeometry.Space.isSeparated_iff_and_isQuasiSeparated_iff_of_isThickening`:
  **Stacks 09ZY**, part (6), both halves.
* `AlgebraicGeometry.Space.universallyInjective_iff_universallyInjective_of_isThickening`:
  **Stacks 09ZY**, part (7).
* `AlgebraicGeometry.Space.universallyOpen_iff_universallyOpen_of_isThickening`:
  **Stacks 09ZY**, part (8).
* `relativelyRepresentable_iff_relativelyRepresentable_of_isThickening_unconditional`:
  **Stacks 09ZY**, part (9).

## References

* [Stacks Project, Tag 09ZY](https://stacks.math.columbia.edu/tag/09ZY)
* [Stacks Project, Tag 07VT](https://stacks.math.columbia.edu/tag/07VT)
* [Stacks Project, Tag 05ZR](https://stacks.math.columbia.edu/tag/05ZR)
* [Stacks Project, Tag 0415](https://stacks.math.columbia.edu/tag/0415)
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits

universe u

namespace AlgebraicGeometry.Space

attribute [local instance] pointTopology

variable (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)

set_option synthInstance.maxHeartbeats 400000 in
/-- Pullbacks of presheaves on the big fppf site over `S` (instance search times out without
this shortcut). -/
local instance hasPullbacks_presheaf_ThickeningsMorphismProperties :
    HasPullbacks ((BigFppfOver B S hS)ᵒᵖ ⥤ Type u) := inferInstance

local instance (priority := high) hasPullback_presheaf_ThickeningsMorphismProperties
    {X Y Z : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u} (f : X ⟶ Z) (g : Y ⟶ Z) :
    HasLimit (cospan f g) :=
  HasLimitsOfShape.has_limit _

/-! ### Universal openness of a base change and of a surjective closed immersion -/

section Permanence

/-- **Stacks 03Z3** for an arbitrary cartesian square: if `IsPullback k f₀ f g` and `f` is
universally open, then so is `f₀`. A base change of `f₀` along `w` is, by pasting, a base
change of `f` along `w ≫ g`. -/
theorem universallyOpen_of_isPullback {X Y X₀ Y₀ : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u}
    {f : X ⟶ Y} {g : Y₀ ⟶ Y} {k : X₀ ⟶ X} {f₀ : X₀ ⟶ Y₀} (sq : IsPullback k f₀ f g)
    (hf : UniversallyOpen B S hS f) : UniversallyOpen B S hS f₀ := by
  intro W hW w
  have h : IsPullback (pullback.fst w f₀) (pullback.snd w f₀ ≫ k) (w ≫ g) f :=
    (IsPullback.of_hasPullback w f₀).paste_vert sq.flip
  exact isOpenMap_pointsMap_of_comp_isIso B S hS h.isoPullback.hom h.isoPullback_hom_fst
    (hf W hW (w ≫ g))

/-- The base change `pullback.fst g i` of a closed immersion `i` along `g` is a closed
immersion. -/
private theorem isClosedImmersion_pullback_fst {X Y Z : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u}
    (g : Z ⟶ Y) {i : X ⟶ Y} (hi : IsClosedImmersion B S hS i) :
    IsClosedImmersion B S hS (pullback.fst g i) :=
  (isClosedImmersion_isStableUnderBaseChange B S hS).of_isPullback
    (IsPullback.of_hasPullback g i).flip hi

/-- A surjective closed immersion of algebraic spaces over `S` is universally open: each of its
base changes is a closed immersion, hence an embedding on points, and is surjective on points,
so it is a homeomorphism on points. -/
theorem universallyOpen_of_isClosedImmersion_of_isSurjective_of_presheaves
    {X Y : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u} (i : X ⟶ Y) (hi : IsClosedImmersion B S hS i)
    (hisurj : IsSurjective B S hS i) : UniversallyOpen B S hS i := by
  intro Z hZ g
  have hc := isClosedImmersion_pullback_fst B S hS g hi
  exact (isHomeomorph_iff_isEmbedding_surjective.mpr
    ⟨isEmbedding_pointsMap_of_isImmersion B S hS hZ _ (isImmersion_of_isClosedImmersion B S hS hc),
      surjective_pointsMap_of_isPullback B S hS (IsPullback.of_hasPullback g i).flip
        hisurj⟩).isOpenMap

end Permanence

/-! ### A square whose vertical arrows are closed immersions -/

section Square

variable {X X' Y Y' : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u}

/-- **Stacks 09ZY, part (1), in the form it is proved.** In a commutative square
`a ≫ j = i ≫ b` of morphisms of algebraic spaces over `S` whose vertical arrows are closed
immersions, the left one surjective, `a` is affine if and only if `b` is. -/
theorem isAffineHom_iff_isAffineHom_of_isClosedImmersion_square_unconditional
    (hX : IsAlgebraicSpace B S hS X) (hX' : IsAlgebraicSpace B S hS X')
    (hY' : IsAlgebraicSpace B S hS Y')
    {i : X ⟶ X'} {j : Y ⟶ Y'} (a : X ⟶ Y) (b : X' ⟶ Y')
    (hi : IsClosedImmersion B S hS i) (hisurj : IsSurjective B S hS i)
    (hj : IsClosedImmersion B S hS j) (hw : a ≫ j = i ≫ b) :
    IsAffineHom B S hS a ↔ IsAffineHom B S hS b := by
  have : Mono j := mono_of_isClosedImmersion B S hS j hj
  refine ⟨fun ha Z g => ?_, fun hb => IsAffineHom.of_isPullback
    (isPullback_id_of_comp_mono a j hw)
    (isAffineHom_comp B S hS i b (isAffineHom_of_isClosedImmersion B S hS i hi) hb)⟩
  let T := BigFppfOver.toScheme B S hS
  have : IsAffine (T.obj ((BigAffineFppf.inclusion B S hS).obj Z)) := Z.property
  have hsq₀ : IsPullback (hj.rep.fst g) (yoneda.map (hj.rep.snd g)) j g := hj.rep.isPullback g
  have : AlgebraicGeometry.IsClosedImmersion (T.map (hj.rep.snd g)) :=
    hj.property g _ _ hsq₀
  have hZ₀ : IsAffine (T.obj (hj.rep.pullback g)) :=
    isAffine_of_isAffineHom (T.map (hj.rep.snd g))
  obtain ⟨W₀, p₀, q₀, hsq₁⟩ := ha ⟨hj.rep.pullback g, hZ₀⟩ (hj.rep.fst g)
  have hsq₂ : IsPullback p₀ (yoneda.map q₀ ≫ yoneda.map (hj.rep.snd g)) (i ≫ b) g :=
    hw ▸ hsq₁.paste_vert hsq₀
  have hP : IsAlgebraicSpace B S hS (pullback b g) :=
    isAlgebraicSpace_pullback B S hS b g hX' (isAlgebraicSpace_yoneda B S hS _) hY'
  obtain ⟨ℓ, hℓ₁, hℓ₂⟩ : ∃ ℓ : yoneda.obj ((BigAffineFppf.inclusion B S hS).obj W₀) ⟶
      pullback b g, ℓ ≫ pullback.fst b g = p₀ ≫ i ∧
        ℓ ≫ pullback.snd b g = yoneda.map q₀ ≫ yoneda.map (hj.rep.snd g) :=
    ⟨pullback.lift _ _ (by rw [Category.assoc, hsq₂.w]), pullback.lift_fst _ _ _,
      pullback.lift_snd _ _ _⟩
  have hℓ : IsPullback p₀ ℓ i (pullback.fst b g) :=
    IsPullback.of_bot (by rwa [hℓ₂]) hℓ₁.symm (IsPullback.of_hasPullback b g)
  have hℓc : IsClosedImmersion B S hS ℓ :=
    (isClosedImmersion_isStableUnderBaseChange B S hS).of_isPullback hℓ hi
  have hW₀ : IsAffine (T.obj ((BigAffineFppf.inclusion B S hS).obj W₀)) := W₀.property
  obtain ⟨T₁, hT₁, ⟨e⟩⟩ := isAffineSpace_of_isClosedImmersion_of_isSurjective B S hS ℓ
    (isAlgebraicSpace_yoneda B S hS _) hP hℓc
    (surjective_pointsMap_of_isPullback B S hS hℓ hisurj)
    (isAffineSpace_yoneda B S hS _ hW₀)
  refine ⟨⟨T₁, hT₁⟩, e.inv ≫ pullback.fst b g, yoneda.preimage (e.inv ≫ pullback.snd b g), ?_⟩
  exact IsPullback.of_iso_pullback ⟨by simp [pullback.condition]⟩ e.symm rfl (by simp)

/-- **Stacks 09ZY, part (5), in the form it is proved.** In a commutative square
`a ≫ j = i ≫ b` of morphisms of algebraic spaces over `S` whose vertical arrows are closed
immersions, the left one surjective, `a` is integral if and only if `b` is: by Stacks 0415
integrality is affineness together with universal closedness, and each of the two transfers
across the square. -/
theorem isIntegralHom_iff_isIntegralHom_of_isClosedImmersion_square_unconditional
    (hX : IsAlgebraicSpace B S hS X) (hX' : IsAlgebraicSpace B S hS X')
    (hY : IsAlgebraicSpace B S hS Y) (hY' : IsAlgebraicSpace B S hS Y')
    {i : X ⟶ X'} {j : Y ⟶ Y'} (a : X ⟶ Y) (b : X' ⟶ Y')
    (hi : IsClosedImmersion B S hS i) (hisurj : IsSurjective B S hS i)
    (hj : IsClosedImmersion B S hS j) (hw : a ≫ j = i ≫ b) :
    IsIntegralHom B S hS a ↔ IsIntegralHom B S hS b := by
  rw [isIntegralHom_iff_isAffineHom_and_universallyClosed B S hS hX hY,
    isIntegralHom_iff_isAffineHom_and_universallyClosed B S hS hX' hY',
    isAffineHom_iff_isAffineHom_of_isClosedImmersion_square_unconditional B S hS hX hX' hY' a b
      hi hisurj hj hw,
    universallyClosed_iff_universallyClosed_of_isClosedImmersion_square B S hS hX hX' hY hY' a b
      hi hisurj hj hw]

/-- **Stacks 09ZY, part (7), in the form it is proved.** In a commutative square
`a ≫ j = i ≫ b` of morphisms of algebraic spaces over `S` whose vertical arrows are closed
immersions, the left one surjective, `a` is universally injective if and only if `b` is. -/
theorem universallyInjective_iff_universallyInjective_of_isClosedImmersion_square
    (hX : IsAlgebraicSpace B S hS X) (hX' : IsAlgebraicSpace B S hS X')
    (hY : IsAlgebraicSpace B S hS Y) (hY' : IsAlgebraicSpace B S hS Y')
    {i : X ⟶ X'} {j : Y ⟶ Y'} (a : X ⟶ Y) (b : X' ⟶ Y')
    (hi : IsClosedImmersion B S hS i) (hisurj : IsSurjective B S hS i)
    (hj : IsClosedImmersion B S hS j) (hw : a ≫ j = i ≫ b) :
    UniversallyInjective B S hS a ↔ UniversallyInjective B S hS b := by
  have : Mono j := mono_of_isClosedImmersion B S hS j hj
  refine ⟨fun ha => universallyInjective_of_isSurjective_comp B S hS hX hX' hY' i b
    (hw ▸ universallyInjective_comp B S hS hY hY' a j ha
      (universallyInjective_of_mono B S hS j this)) hisurj, fun hb => ?_⟩
  exact universallyInjective_of_isPullback B S hS hX hY hY' (i ≫ b) j
    (universallyInjective_comp B S hS hX' hY' i b
      (universallyInjective_of_mono B S hS i (mono_of_isClosedImmersion B S hS i hi)) hb)
    (isPullback_id_of_comp_mono a j hw).flip

/-- **Stacks 09ZY, part (8), in the form it is proved.** In a commutative square
`a ≫ j = i ≫ b` of morphisms of algebraic spaces over `S` whose vertical arrows are surjective
closed immersions, `a` is universally open if and only if `b` is. -/
theorem universallyOpen_iff_universallyOpen_of_isClosedImmersion_square
    (hX : IsAlgebraicSpace B S hS X) (hX' : IsAlgebraicSpace B S hS X')
    (hY : IsAlgebraicSpace B S hS Y) (hY' : IsAlgebraicSpace B S hS Y')
    {i : X ⟶ X'} {j : Y ⟶ Y'} (a : X ⟶ Y) (b : X' ⟶ Y')
    (hi : IsClosedImmersion B S hS i) (hisurj : IsSurjective B S hS i)
    (hj : IsClosedImmersion B S hS j) (hjsurj : IsSurjective B S hS j) (hw : a ≫ j = i ≫ b) :
    UniversallyOpen B S hS a ↔ UniversallyOpen B S hS b := by
  have : Mono j := mono_of_isClosedImmersion B S hS j hj
  exact ⟨fun ha => universallyOpen_of_universallyOpen_comp B S hS i b hw.symm hisurj
      (universallyOpen_comp B S hS hX hY hY' a j ha
        (universallyOpen_of_isClosedImmersion_of_isSurjective_of_presheaves B S hS j hj hjsurj)),
    fun hb => universallyOpen_of_isPullback B S hS (isPullback_id_of_comp_mono a j hw)
      (universallyOpen_comp B S hS hX hX' hY' i b
        (universallyOpen_of_isClosedImmersion_of_isSurjective_of_presheaves B S hS i hi
          hisurj) hb)⟩

/-- **Stacks 09ZY, part (9), in the form it is proved.** In a commutative square
`a ≫ j = i ≫ b` of morphisms of algebraic spaces over `S` whose vertical arrows are closed
immersions, the left one bijective on points, `a` is representable if and only if `b` is.

If `b` is representable, so is `i ≫ b = a ≫ j`, and `a` is its base change along the
monomorphism `j`. Conversely let `T ⟶ Y'` be a morphism from a scheme. Then `T ×_{Y'} Y` is a
scheme, as `j` is a closed immersion, so `T ×_{Y'} X = (T ×_{Y'} Y) ×_Y X` is a scheme, as `a`
is representable; and `T ×_{Y'} X ⟶ T ×_{Y'} X'` is a base change of `i`, hence a closed
immersion bijective on points, so `T ×_{Y'} X'` is a scheme (Stacks 07VV in the direction from
the source, for a closed immersion). -/
theorem
    relativelyRepresentable_iff_relativelyRepresentable_of_isClosedImmersion_square_unconditional
    (hX : IsAlgebraicSpace B S hS X) (hX' : IsAlgebraicSpace B S hS X')
    (hY' : IsAlgebraicSpace B S hS Y')
    {i : X ⟶ X'} {j : Y ⟶ Y'} (a : X ⟶ Y) (b : X' ⟶ Y')
    (hi : IsClosedImmersion B S hS i) (hisurj : IsSurjective B S hS i)
    (hj : IsClosedImmersion B S hS j) (hw : a ≫ j = i ≫ b) :
    yoneda.relativelyRepresentable a ↔ yoneda.relativelyRepresentable b := by
  have : Mono j := mono_of_isClosedImmersion B S hS j hj
  refine ⟨fun ha => ?_, fun hb => MorphismProperty.of_isPullback
    (isPullback_id_of_comp_mono a j hw) (MorphismProperty.comp_mem _ _ _ hi.rep hb)⟩
  refine (yoneda_relativelyRepresentable_iff_pullback_representable b).2 fun U ξ => ?_
  set g : yoneda.obj U ⟶ Y' := yonedaEquiv.symm ξ
  have hP : IsAlgebraicSpace B S hS (pullback g b) :=
    isAlgebraicSpace_pullback B S hS g b (isAlgebraicSpace_yoneda B S hS U) hX' hY'
  have hQ : IsAlgebraicSpace B S hS (pullback (pullback.snd g b) i) :=
    isAlgebraicSpace_pullback B S hS (pullback.snd g b) i hP hX hX'
  have hc := isClosedImmersion_pullback_fst B S hS (pullback.snd g b) hi
  have : Mono (pullback.fst (pullback.snd g b) i) := mono_of_isClosedImmersion B S hS _ hc
  have : (pullback g j).IsRepresentable :=
    (yoneda_relativelyRepresentable_iff_pullback_representable j).1 hj.rep U ξ
  have : (pullback (pullback.snd g j) a).IsRepresentable :=
    Functor.isRepresentable_of_relativelyRepresentable_of_target_isRepresentable
      (pullback.fst (pullback.snd g j) a)
      (MorphismProperty.of_isPullback (IsPullback.of_hasPullback (pullback.snd g j) a).flip ha)
  have hQrep : (pullback (pullback.snd g b) i).IsRepresentable :=
    isRepresentable_of_natIso _ ((pullbackLeftPullbackSndIso g j a).trans
      ((pullback.congrHom rfl hw).trans (pullbackLeftPullbackSndIso g b i).symm))
  exact isRepresentable_of_isClosedImmersion_of_bijective B S hS hQ hP _ hc
    ⟨pointsMap_injective_of_mono B S hS _,
      surjective_pointsMap_of_isPullback B S hS
        (IsPullback.of_hasPullback (pullback.snd g b) i).flip hisurj⟩ hQrep

end Square

/-! ### Morphisms of thickenings -/

section Thickening

variable {X Y : AlgebraicSpaces B S hS} {G : Subfunctor X.1} {H : Subfunctor Y.1}

/-- **Stacks 09ZY, part (1).** In a morphism of thickenings of algebraic spaces over `S` the
morphism on the closed subspaces is affine if and only if the morphism on the ambient spaces
is. -/
@[stacks 09ZY "part (1): affine"]
theorem isAffineHom_iff_isAffineHom_of_isThickening_unconditional
    (hG : IsThickening B S hS X G) (hH : IsThickening B S hS Y H)
    (f : Arrow.mk G.ι ⟶ Arrow.mk H.ι) :
    IsAffineHom B S hS f.left ↔ IsAffineHom B S hS f.right :=
  isAffineHom_iff_isAffineHom_of_isClosedImmersion_square_unconditional B S hS hG.1.1 X.2 Y.2
    f.left f.right hG.1.2 hG.2 hH.1.2 (Arrow.w f)

/-- **Stacks 09ZY, part (5).** In a morphism of thickenings of algebraic spaces over `S` the
morphism on the closed subspaces is integral if and only if the morphism on the ambient spaces
is. -/
@[stacks 09ZY "part (5): integral"]
theorem isIntegralHom_iff_isIntegralHom_of_isThickening_unconditional
    (hG : IsThickening B S hS X G) (hH : IsThickening B S hS Y H)
    (f : Arrow.mk G.ι ⟶ Arrow.mk H.ι) :
    IsIntegralHom B S hS f.left ↔ IsIntegralHom B S hS f.right :=
  isIntegralHom_iff_isIntegralHom_of_isClosedImmersion_square_unconditional B S hS hG.1.1 X.2
    hH.1.1 Y.2 f.left f.right hG.1.2 hG.2 hH.1.2 (Arrow.w f)

/-- **Stacks 09ZY, part (6).** In a morphism of thickenings of algebraic spaces over `S` the
morphism on the closed subspaces is separated if and only if the morphism on the ambient spaces
is, and it is quasi-separated if and only if the morphism on the ambient spaces is. -/
@[stacks 09ZY "part (6): separated, and quasi-separated"]
theorem isSeparated_iff_and_isQuasiSeparated_iff_of_isThickening
    (hG : IsThickening B S hS X G) (hH : IsThickening B S hS Y H)
    (f : Arrow.mk G.ι ⟶ Arrow.mk H.ι) :
    (IsSeparated B S hS f.left ↔ IsSeparated B S hS f.right) ∧
      (IsQuasiSeparated B S hS f.left ↔ IsQuasiSeparated B S hS f.right) :=
  ⟨isSeparated_iff_isSeparated_of_isThickening B S hS hG hH f,
    isQuasiSeparated_iff_isQuasiSeparated_of_isClosedImmersion_square B S hS hG.1.1 X.2 hH.1.1
      Y.2 f.left f.right hG.1.2 hG.2 hH.1.2 (Arrow.w f)⟩

/-- **Stacks 09ZY, part (7).** In a morphism of thickenings of algebraic spaces over `S` the
morphism on the closed subspaces is universally injective if and only if the morphism on the
ambient spaces is. -/
@[stacks 09ZY "part (7): universally injective"]
theorem universallyInjective_iff_universallyInjective_of_isThickening
    (hG : IsThickening B S hS X G) (hH : IsThickening B S hS Y H)
    (f : Arrow.mk G.ι ⟶ Arrow.mk H.ι) :
    UniversallyInjective B S hS f.left ↔ UniversallyInjective B S hS f.right :=
  universallyInjective_iff_universallyInjective_of_isClosedImmersion_square B S hS hG.1.1 X.2
    hH.1.1 Y.2 f.left f.right hG.1.2 hG.2 hH.1.2 (Arrow.w f)

/-- **Stacks 09ZY, part (8).** In a morphism of thickenings of algebraic spaces over `S` the
morphism on the closed subspaces is universally open if and only if the morphism on the ambient
spaces is. -/
@[stacks 09ZY "part (8): universally open"]
theorem universallyOpen_iff_universallyOpen_of_isThickening
    (hG : IsThickening B S hS X G) (hH : IsThickening B S hS Y H)
    (f : Arrow.mk G.ι ⟶ Arrow.mk H.ι) :
    UniversallyOpen B S hS f.left ↔ UniversallyOpen B S hS f.right :=
  universallyOpen_iff_universallyOpen_of_isClosedImmersion_square B S hS hG.1.1 X.2 hH.1.1 Y.2
    f.left f.right hG.1.2 hG.2 hH.1.2 hH.2 (Arrow.w f)

/-- **Stacks 09ZY, part (9).** In a morphism of thickenings of algebraic spaces over `S` the
morphism on the closed subspaces is representable if and only if the morphism on the ambient
spaces is. -/
@[stacks 09ZY "part (9): representable"]
theorem relativelyRepresentable_iff_relativelyRepresentable_of_isThickening_unconditional
    (hG : IsThickening B S hS X G) (hH : IsThickening B S hS Y H)
    (f : Arrow.mk G.ι ⟶ Arrow.mk H.ι) :
    yoneda.relativelyRepresentable f.left ↔ yoneda.relativelyRepresentable f.right :=
  relativelyRepresentable_iff_relativelyRepresentable_of_isClosedImmersion_square_unconditional
    B S hS hG.1.1 X.2 Y.2 f.left f.right hG.1.2 hG.2 hH.1.2 (Arrow.w f)

end Thickening

end AlgebraicGeometry.Space

end
