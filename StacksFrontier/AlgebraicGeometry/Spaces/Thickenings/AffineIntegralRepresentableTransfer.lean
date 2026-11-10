module

public import StacksCore.Tactic.StacksAttribute
public import StacksFrontier.AlgebraicGeometry.Spaces.AffineOfUniversallyClosedSurjection
public import StacksFrontier.AlgebraicGeometry.Spaces.ClosedImmersionProper
public import StacksFrontier.AlgebraicGeometry.Spaces.IntegralUniversallyClosed
public import StacksFrontier.AlgebraicGeometry.Spaces.Morphisms.AffineDiagonal
public import StacksFrontier.AlgebraicGeometry.Spaces.ProperClosedImmersion
public import StacksFrontier.AlgebraicGeometry.Spaces.SchemeOfIntegralBijection
public import StacksFrontier.AlgebraicGeometry.Spaces.Thickenings.Scheme
public import StacksFrontier.AlgebraicGeometry.Spaces.Thickenings.SeparatedAndClosed
public import StacksFrontier.CategoryTheory.PullbackCancelMono

/-!
# Affineness, integrality and representability across a morphism of thickenings of spaces

A morphism of thickenings of algebraic spaces over a scheme `S` is a commutative square

```
X --a--→ Y
|        |
i        j
↓        ↓
X' --b-→ Y'
```

whose vertical arrows are the inclusions of thickenings. This file proves that `a` is affine,
integral, respectively representable by schemes exactly when `b` is: parts (1), (5) and (9) of
Stacks 09ZY.

As in `StacksFrontier.AlgebraicGeometry.Spaces.Thickenings.SeparatedAndClosed`, the only properties
of the square that the argument uses are that `i` and `j` are closed immersions and that `i` is
surjective; in particular the square need not be cartesian.

## The one geometric input, and where it is granted

Each of the three implications *from the thin side* — from `a` to `b` — comes down to one fibre
product. Fix a test object `T` of the site over `Y'`. The base change `Y ×_{Y'} T` is a closed
subspace of `T`, the base change `X ×_Y (Y ×_{Y'} T)` is a base change of `a`, and the comparison

```
X ×_Y (Y ×_{Y'} T) ⟶ X' ×_{Y'} T
```

is a base change of `i`, hence a surjective closed immersion. So the left-hand object, whose shape
is controlled by `a`, is a thickening of the right-hand object, whose shape is what affineness
respectively representability of `b` asks about — and transferring either shape *up* a thickening
of algebraic spaces is Stacks 07VT, that an algebraic space receiving a surjective universally
closed morphism from an affine scheme is affine. The library form of Stacks 07VT,
`AlgebraicGeometry.Space.isAffineSpace_of_isSurjective_of_universallyClosed`, carries three
hypotheses, and so does Stacks 05ZR through
`AlgebraicGeometry.Space.isRepresentable_of_isIntegralHom_of_bijective`; they are passed through
here unchanged and used for nothing else, so the three implications from the thin side are exactly
as conditional as Stacks 07VT and no more. The three implications *to* the thin side — from `b` to
`a` — are unconditional, and are a cancellation along the square: `a ≫ j = i ≫ b` has the property
because `i` and `j` do, and then `j` separated (parts (1) and (5)) respectively `j` a monomorphism
(part (9)) cancels it off the back.

Part (5) is not proved from the fibre product directly. By Stacks 0415 integrality of a morphism
of algebraic spaces is affineness together with universal closedness, so part (5) is the
conjunction of part (1) with part (4), and part (4) is already proved, unconditionally, as
`AlgebraicGeometry.Space.universallyClosed_iff_universallyClosed_of_isThickening`.

## Main results

**None of the three thickening statements below is registered.** Each carries the three
hypotheses of the library's Stacks 07VT, and one of them, `h07SQ`, is Stacks 07SQ with no bound
on the index set, which is false in this development (an index as large as the site's size
cutoff can have the empty space as limit with no affine stage). They are therefore
stated as conditional lemmas without a `@[stacks 09ZY …]` attribute.

* `AlgebraicGeometry.Space.isAffineHom_iff_isAffineHom_of_isThickening`: **Stacks 09ZY**,
  part (1).
* `AlgebraicGeometry.Space.isIntegralHom_iff_isIntegralHom_of_isThickening`: **Stacks 09ZY**,
  part (5).
* `AlgebraicGeometry.Space.relativelyRepresentable_iff_relativelyRepresentable_of_isThickening`:
  **Stacks 09ZY**, part (9).

Each of the three is also proved in the form it is used, for a commutative square whose vertical
arrows are closed immersions, the left one surjective:
`AlgebraicGeometry.Space.isAffineHom_iff_isAffineHom_of_isClosedImmersion_square` and its two
companions. Taking the right-hand inclusion to be the identity turns each of those into the
cancellation of a surjective closed immersion off the front of a composite, which is the shape the
diagonal clauses of Stacks 0BPV consume.

The shared geometry is the comparison morphism of
`AlgebraicGeometry.Space.exists_isClosedImmersion_isSurjective_of_isClosedImmersion_square`,
and the passage from an isomorphism with a representable presheaf back to the cartesian square
the definitions ask for is `AlgebraicGeometry.Space.isPullback_of_pullback_iso_yoneda`.

## Implementation notes

The hypotheses are the predicates of this directory, stated for arbitrary morphisms of presheaves
on the big fppf site of `S` with algebraicity supplied separately, exactly as in
`StacksFrontier/AlgebraicGeometry/Spaces/Thickenings/Morphisms.lean`. Representability by schemes is
`CategoryTheory.Functor.relativelyRepresentable` for the Yoneda embedding of the site, which is the
notion of a representable morphism that Stacks 02YU uses to define closed immersions here.

Surjectivity of the *right-hand* inclusion `j` is never used, and neither is anything infinitesimal
nor any universal homeomorphism.

## References

* [Stacks Project, Tag 0415](https://stacks.math.columbia.edu/tag/0415)
* [Stacks Project, Tag 05ZR](https://stacks.math.columbia.edu/tag/05ZR)
* [Stacks Project, Tag 07VT](https://stacks.math.columbia.edu/tag/07VT)
* [Stacks Project, Tag 07VV](https://stacks.math.columbia.edu/tag/07VV)
* [Stacks Project, Tag 09ZY](https://stacks.math.columbia.edu/tag/09ZY)
-/

@[expose] public section

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits
open Stacks.Thickenings

universe u

namespace AlgebraicGeometry.Space

variable (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)

set_option synthInstance.maxHeartbeats 400000 in
-- instance search for pullbacks of presheaves on the big fppf site is expensive
/-- Pullbacks of presheaves on the big fppf site over `S` (instance search times out without
this shortcut). -/
local instance hasPullbacks_presheaf_AffineIntegralRepresentableTransfer :
    HasPullbacks ((BigFppfOver B S hS)ᵒᵖ ⥤ Type u) := inferInstance

/-- The limit of a cospan of presheaves on the big fppf site over `S`, found directly. -/
local instance (priority := high) hasPullback_presheaf_AffineIntegralRepresentableTransfer
    {X Y Z : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u} (f : X ⟶ Z) (g : Y ⟶ Z) :
    HasLimit (cospan f g) :=
  HasLimitsOfShape.has_limit _

/-! ### From an isomorphism with a representable presheaf to a cartesian square -/

/-- An isomorphism of the fibre product of `f : F ⟶ G` and `g : yoneda.obj T ⟶ G` with the
presheaf represented by an object `V` of the site turns the fibre product square into a square
over `f` and `g` whose other two sides are a morphism out of `yoneda.obj V` and the image under
Yoneda of a morphism `V ⟶ T` of the site.

This is the data that `AlgebraicGeometry.Space.IsAffineHom` and
`CategoryTheory.Functor.relativelyRepresentable` ask for, assembled from the isomorphism that
affineness respectively representability of the fibre product supplies. -/
theorem isPullback_of_pullback_iso_yoneda {F G : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u} (f : F ⟶ G)
    {T V : BigFppfOver B S hS} (g : yoneda.obj T ⟶ G) (e : pullback f g ≅ yoneda.obj V) :
    IsPullback (e.inv ≫ pullback.fst f g)
      (yoneda.map (yoneda.preimage (e.inv ≫ pullback.snd f g))) f g := by
  refine IsPullback.of_iso_pullback ⟨?_⟩ e.symm rfl (yoneda.map_preimage _).symm
  rw [yoneda.map_preimage, Category.assoc, Category.assoc, pullback.condition]

/-! ### The comparison morphism of a square whose vertical arrows are closed immersions -/

section Square

variable {X X' Y Y' : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u}

/-- **The comparison morphism of two base changes along a square whose left vertical arrow is a
surjective closed immersion.** Let `a ≫ j = i ≫ b` be a commutative square of morphisms of
presheaves on the big fppf site of `S` whose left vertical arrow `i` is a surjective closed
immersion of algebraic spaces. Let `g : T ⟶ Y'` be a morphism, let `(u, v)` exhibit `Q` as the
fibre product of `a ≫ j` and `g`, and let `(p, q)` exhibit `P` as the fibre product of `b` and
`g`. Then the comparison `c : Q ⟶ P` over `T` is a base change of `i`, hence again a surjective
closed immersion.

The comparison is the morphism the universal property of `P` gives to `u ≫ i` and `v`; that the
square it forms with `u`, `i` and `p` is cartesian is the cancellation of the cartesian square
`(p, q)` off the bottom of the cartesian square `(u, v)`. -/
theorem exists_isClosedImmersion_isSurjective_of_isClosedImmersion_square
    (hX : IsAlgebraicSpace B S hS X) (hX' : IsAlgebraicSpace B S hS X')
    {i : X ⟶ X'} {j : Y ⟶ Y'} (a : X ⟶ Y) (b : X' ⟶ Y')
    (hi : IsClosedImmersion B S hS i) (hisurj : IsSurjective B S hS i) (hw : a ≫ j = i ≫ b)
    {Q T P : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u} (hQ : IsAlgebraicSpace B S hS Q)
    (hP : IsAlgebraicSpace B S hS P) {u : Q ⟶ X} {v : Q ⟶ T} {g : T ⟶ Y'} {p : P ⟶ X'}
    {q : P ⟶ T} (sq : IsPullback u v (a ≫ j) g) (sq' : IsPullback p q b g) :
    ∃ c : Q ⟶ P, c ≫ p = u ≫ i ∧ c ≫ q = v ∧
      IsClosedImmersion B S hS c ∧ IsSurjective B S hS c := by
  have hcomm : (u ≫ i) ≫ b = v ≫ g := by
    rw [Category.assoc, ← hw, sq.w]
  have hcp : sq'.lift (u ≫ i) v hcomm ≫ p = u ≫ i := sq'.lift_fst _ _ _
  have hcq : sq'.lift (u ≫ i) v hcomm ≫ q = v := sq'.lift_snd _ _ _
  have sqc : IsPullback u (sq'.lift (u ≫ i) v hcomm) i p := by
    refine IsPullback.of_bot ?_ hcp.symm sq'
    rwa [hcq, ← hw]
  refine ⟨_, hcp, hcq,
    (isClosedImmersion_isStableUnderBaseChange B S hS).of_isPullback sqc hi, ?_⟩
  have hA : IsPullback
      (ObjectProperty.homMk u : (⟨Q, hQ⟩ : AlgebraicSpaces B S hS) ⟶ ⟨X, hX⟩)
      (ObjectProperty.homMk (sq'.lift (u ≫ i) v hcomm) :
        (⟨Q, hQ⟩ : AlgebraicSpaces B S hS) ⟶ ⟨P, hP⟩)
      (ObjectProperty.homMk i : (⟨X, hX⟩ : AlgebraicSpaces B S hS) ⟶ ⟨X', hX'⟩)
      (ObjectProperty.homMk p : (⟨P, hP⟩ : AlgebraicSpaces B S hS) ⟶ ⟨X', hX'⟩) :=
    IsPullback.of_map (ObjectProperty.ι _) (ObjectProperty.hom_ext _ sqc.w) sqc
  exact isSurjective_of_isPullback B S hS hA hisurj

/-- In a square `a ≫ j = i ≫ b` as above, a cartesian square exhibiting the pullback of `a` along
`e.inv ≫ pullback.fst j g` through an isomorphism `e : pullback j g ≅ yoneda.obj V` gives a
surjective closed immersion from its source to `pullback b g`. -/
private theorem exists_isClosedImmersion_isSurjective_of_pullback_iso_yoneda
    (hX : IsAlgebraicSpace B S hS X) (hX' : IsAlgebraicSpace B S hS X')
    {i : X ⟶ X'} {j : Y ⟶ Y'} (a : X ⟶ Y) (b : X' ⟶ Y')
    (hi : IsClosedImmersion B S hS i) (hisurj : IsSurjective B S hS i) (hw : a ≫ j = i ≫ b)
    {T V W : BigFppfOver B S hS} (g : yoneda.obj T ⟶ Y') (e : pullback j g ≅ yoneda.obj V)
    (hPalg : IsAlgebraicSpace B S hS (pullback b g)) {p : yoneda.obj W ⟶ X} {q₁ : W ⟶ V}
    (sq1 : IsPullback p (yoneda.map q₁) a (e.inv ≫ pullback.fst j g)) :
    ∃ c : yoneda.obj W ⟶ pullback b g, IsClosedImmersion B S hS c ∧ IsSurjective B S hS c := by
  have sqBig : IsPullback p
      (yoneda.map (q₁ ≫ yoneda.preimage (e.inv ≫ pullback.snd j g))) (a ≫ j) g := by
    simpa using sq1.paste_vert (isPullback_of_pullback_iso_yoneda B S hS j g e)
  obtain ⟨c, -, -, hcci, hcsurj⟩ :=
    exists_isClosedImmersion_isSurjective_of_isClosedImmersion_square B S hS hX hX'
      a b hi hisurj hw (isAlgebraicSpace_yoneda B S hS _) hPalg sqBig
      (IsPullback.of_hasPullback b g)
  exact ⟨c, hcci, hcsurj⟩

/-! ### Part (1): affineness -/

/-- In a commutative square `a ≫ j = i ≫ b` whose vertical arrows are closed immersions, `a` is
affine if `b` is. -/
theorem isAffineHom_of_isClosedImmersion_square_of_isAffineHom
    {i : X ⟶ X'} {j : Y ⟶ Y'} (a : X ⟶ Y) (b : X' ⟶ Y')
    (hi : IsClosedImmersion B S hS i) (hj : IsClosedImmersion B S hS j) (hw : a ≫ j = i ≫ b)
    (hb : IsAffineHom B S hS b) : IsAffineHom B S hS a := by
  refine isAffineHom_of_isAffineHom_comp_of_isSeparated B S hS a j ?_
    (isSeparated_of_isClosedImmersion B S hS j hj)
  rw [hw]
  exact isAffineHom_comp B S hS i b (isAffineHom_of_isClosedImmersion B S hS i hi) hb

/-- **Stacks 09ZY, part (1), in the form it is proved.** In a commutative square `a ≫ j = i ≫ b`
of morphisms of algebraic spaces over `S` whose vertical arrows are closed immersions, the left
one surjective, `a` is affine if and only if `b` is.

The implication from `b` is a cancellation: `i` is affine by Stacks 07U2, so `i ≫ b = a ≫ j` is
affine by Stacks 03WH, and `j` is separated by Stacks 042R, so Stacks 08GB part (2) makes `a`
affine. The implication from `a` runs over a test object `Z` of the big affine fppf site over
`Y'`: the fibre product `Y ×_{Y'} Z` is affine because the projection to `Z` is a closed
immersion, its fibre product with `X` over `Y` is then affine because `a` is, and that fibre
product maps onto `X' ×_{Y'} Z` by a surjective closed immersion, so Stacks 07VT makes
`X' ×_{Y'} Z` affine. -/
theorem isAffineHom_iff_isAffineHom_of_isClosedImmersion_square
    (hX : IsAlgebraicSpace B S hS X) (hX' : IsAlgebraicSpace B S hS X')
    (hY' : IsAlgebraicSpace B S hS Y')
    {i : X ⟶ X'} {j : Y ⟶ Y'} (a : X ⟶ Y) (b : X' ⟶ Y')
    (hi : IsClosedImmersion B S hS i) (hisurj : IsSurjective B S hS i)
    (hj : IsClosedImmersion B S hS j) (hw : a ≫ j = i ≫ b)
    (h09YA : ∀ {X₀ Y₀ : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u} (g : X₀ ⟶ Y₀),
      IsAlgebraicSpace B S hS X₀ → IsAlgebraicSpace B S hS Y₀ → IsIntegralHom B S hS g →
      IsQuasiCompactSpace B S hS Y₀ →
      IsAbsolutelyQuasiSeparated B S hS B.contains_terminal Y₀ →
      IntegralFiniteSystem B S hS g)
    (h07SQ : ∀ {I : Type u} [Preorder I] [IsDirected I (· ≤ ·)]
      (D : DescentSituation B S hS B.contains_terminal I),
      IsAffineSpace B S hS D.limitCone.pt →
      ∃ k : I, D.base ≤ k ∧ IsAffineSpace B S hS (D.system.obj (Opposite.op k)))
    (hFinitePresentation : ∀ {X₀ Y₀ : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u} (g : X₀ ⟶ Y₀),
      IsAlgebraicSpace B S hS X₀ → IsAlgebraicSpace B S hS Y₀ → IsFinite B S hS g →
      IsFinitePresentation B S hS g → IsSurjective B S hS g → IsAffineSpace B S hS X₀ →
      IsAffineSpace B S hS Y₀) :
    IsAffineHom B S hS a ↔ IsAffineHom B S hS b := by
  refine ⟨fun ha ↦ ?_,
    isAffineHom_of_isClosedImmersion_square_of_isAffineHom B S hS a b hi hj hw⟩
  intro Z g
  obtain ⟨T₁, hT₁, ⟨e⟩⟩ : IsAffineSpace B S hS (pullback j g) :=
    (isAffineHom_of_isClosedImmersion B S hS _
      ((isClosedImmersion_isStableUnderBaseChange B S hS).of_isPullback
        (IsPullback.of_hasPullback j g) hj)).isAffineSpace_source
      (isAffineSpace_yoneda B S hS _ Z.property)
  obtain ⟨W, p, q₁, sq1⟩ := ha ⟨T₁, hT₁⟩ (e.inv ≫ pullback.fst j g)
  have hWaff : IsAffineSpace B S hS
      (yoneda.obj ((BigAffineFppf.inclusion B S hS).obj W)) :=
    isAffineSpace_yoneda B S hS _ W.property
  have hPalg : IsAlgebraicSpace B S hS (pullback b g) :=
    isAlgebraicSpace_pullback B S hS b g hX' (isAlgebraicSpace_yoneda B S hS _) hY'
  obtain ⟨c, hcci, hcsurj⟩ :=
    exists_isClosedImmersion_isSurjective_of_pullback_iso_yoneda B S hS hX hX' a b hi hisurj
      hw g e hPalg sq1
  obtain ⟨V, hV, ⟨eV⟩⟩ := isAffineSpace_of_isSurjective_of_universallyClosed B S hS c
    hWaff.isAlgebraicSpace hPalg hcsurj
    (universallyClosed_of_isClosedImmersion B S hS hWaff.isAlgebraicSpace hPalg c hcci)
    hWaff h09YA h07SQ hFinitePresentation
  exact ⟨⟨V, hV⟩, _, _, isPullback_of_pullback_iso_yoneda B S hS b g eV⟩

/-! ### Part (5): integrality -/

/-- **Stacks 09ZY, part (5), in the form it is proved.** In a commutative square `a ≫ j = i ≫ b`
of morphisms of algebraic spaces over `S` whose vertical arrows are closed immersions, the left
one surjective, `a` is integral if and only if `b` is.

By Stacks 0415 an integral morphism of algebraic spaces is an affine universally closed one, so
this is part (1) conjoined with part (4),
`AlgebraicGeometry.Space.universallyClosed_iff_universallyClosed_of_isClosedImmersion_square`. -/
theorem isIntegralHom_iff_isIntegralHom_of_isClosedImmersion_square
    (hX : IsAlgebraicSpace B S hS X) (hX' : IsAlgebraicSpace B S hS X')
    (hY : IsAlgebraicSpace B S hS Y) (hY' : IsAlgebraicSpace B S hS Y')
    {i : X ⟶ X'} {j : Y ⟶ Y'} (a : X ⟶ Y) (b : X' ⟶ Y')
    (hi : IsClosedImmersion B S hS i) (hisurj : IsSurjective B S hS i)
    (hj : IsClosedImmersion B S hS j) (hw : a ≫ j = i ≫ b)
    (h09YA : ∀ {X₀ Y₀ : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u} (g : X₀ ⟶ Y₀),
      IsAlgebraicSpace B S hS X₀ → IsAlgebraicSpace B S hS Y₀ → IsIntegralHom B S hS g →
      IsQuasiCompactSpace B S hS Y₀ →
      IsAbsolutelyQuasiSeparated B S hS B.contains_terminal Y₀ →
      IntegralFiniteSystem B S hS g)
    (h07SQ : ∀ {I : Type u} [Preorder I] [IsDirected I (· ≤ ·)]
      (D : DescentSituation B S hS B.contains_terminal I),
      IsAffineSpace B S hS D.limitCone.pt →
      ∃ k : I, D.base ≤ k ∧ IsAffineSpace B S hS (D.system.obj (Opposite.op k)))
    (hFinitePresentation : ∀ {X₀ Y₀ : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u} (g : X₀ ⟶ Y₀),
      IsAlgebraicSpace B S hS X₀ → IsAlgebraicSpace B S hS Y₀ → IsFinite B S hS g →
      IsFinitePresentation B S hS g → IsSurjective B S hS g → IsAffineSpace B S hS X₀ →
      IsAffineSpace B S hS Y₀) :
    IsIntegralHom B S hS a ↔ IsIntegralHom B S hS b := by
  rw [isIntegralHom_iff_isAffineHom_and_universallyClosed B S hS hX hY a,
    isIntegralHom_iff_isAffineHom_and_universallyClosed B S hS hX' hY' b]
  exact and_congr
    (isAffineHom_iff_isAffineHom_of_isClosedImmersion_square B S hS hX hX' hY' a b hi hisurj
      hj hw h09YA h07SQ hFinitePresentation)
    (universallyClosed_iff_universallyClosed_of_isClosedImmersion_square B S hS hX hX' hY hY'
      a b hi hisurj hj hw)

/-! ### Part (9): representability by schemes -/

/-- In a commutative square `a ≫ j = i ≫ b` whose vertical arrows are closed immersions, `a` is
representable by schemes if `b` is. -/
theorem relativelyRepresentable_of_isClosedImmersion_square_of_relativelyRepresentable
    {i : X ⟶ X'} {j : Y ⟶ Y'} (a : X ⟶ Y) (b : X' ⟶ Y')
    (hi : IsClosedImmersion B S hS i) (hj : IsClosedImmersion B S hS j) (hw : a ≫ j = i ≫ b)
    (hb : yoneda.relativelyRepresentable b) : yoneda.relativelyRepresentable a := by
  intro T g
  have : Mono j := mono_of_isClosedImmersion B S hS j hj
  have hcomp : yoneda.relativelyRepresentable (a ≫ j) := by
    rw [hw]
    exact MorphismProperty.comp_mem _ _ _ hi.rep hb
  obtain ⟨W, q₁, p, sq1⟩ := hcomp (g ≫ j)
  exact ⟨W, q₁, p, isPullback_of_comp_mono j sq1⟩

/-- **Stacks 09ZY, part (9), in the form it is proved.** In a commutative square `a ≫ j = i ≫ b`
of morphisms of algebraic spaces over `S` whose vertical arrows are closed immersions, the left
one surjective, `a` is representable by schemes if and only if `b` is.

The implication from `b` is formal: `i` and `b` are representable, so `a ≫ j = i ≫ b` is, and
cancelling the monomorphism `j` off a cartesian square over `a ≫ j` and `g ≫ j` leaves a
cartesian square over `a` and `g`. The implication from `a` runs over a test object `T` of the
site over `Y'`: the fibre product `Y ×_{Y'} T` is a scheme because the projection to `T` is a
closed immersion, its fibre product with `X` over `Y` is then a scheme because `a` is
representable, and that fibre product maps onto `X' ×_{Y'} T` by a surjective closed immersion,
so Stacks 07VV in the direction that goes from the source — which is how Stacks 05ZR is proved
here — makes `X' ×_{Y'} T` a scheme. -/
theorem relativelyRepresentable_iff_relativelyRepresentable_of_isClosedImmersion_square
    (hX : IsAlgebraicSpace B S hS X) (hX' : IsAlgebraicSpace B S hS X')
    (hY' : IsAlgebraicSpace B S hS Y')
    {i : X ⟶ X'} {j : Y ⟶ Y'} (a : X ⟶ Y) (b : X' ⟶ Y')
    (hi : IsClosedImmersion B S hS i) (hisurj : IsSurjective B S hS i)
    (hj : IsClosedImmersion B S hS j) (hw : a ≫ j = i ≫ b)
    (h09YA : ∀ {X₀ Y₀ : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u} (g : X₀ ⟶ Y₀),
      IsAlgebraicSpace B S hS X₀ → IsAlgebraicSpace B S hS Y₀ → IsIntegralHom B S hS g →
      IsQuasiCompactSpace B S hS Y₀ →
      IsAbsolutelyQuasiSeparated B S hS B.contains_terminal Y₀ →
      IntegralFiniteSystem B S hS g)
    (h07SQ : ∀ {I : Type u} [Preorder I] [IsDirected I (· ≤ ·)]
      (D : DescentSituation B S hS B.contains_terminal I),
      IsAffineSpace B S hS D.limitCone.pt →
      ∃ k : I, D.base ≤ k ∧ IsAffineSpace B S hS (D.system.obj (Opposite.op k)))
    (hFinitePresentation : ∀ {X₀ Y₀ : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u} (g : X₀ ⟶ Y₀),
      IsAlgebraicSpace B S hS X₀ → IsAlgebraicSpace B S hS Y₀ → IsFinite B S hS g →
      IsFinitePresentation B S hS g → IsSurjective B S hS g → IsAffineSpace B S hS X₀ →
      IsAffineSpace B S hS Y₀) :
    yoneda.relativelyRepresentable a ↔ yoneda.relativelyRepresentable b := by
  refine ⟨fun ha ↦ ?_,
    relativelyRepresentable_of_isClosedImmersion_square_of_relativelyRepresentable B S hS
      a b hi hj hw⟩
  intro T g
  have : (pullback j g).IsRepresentable :=
    isRepresentable_of_isClosedImmersion B S hS (pullback.snd j g)
      ((isClosedImmersion_isStableUnderBaseChange B S hS).of_isPullback
        (IsPullback.of_hasPullback j g) hj)
      inferInstance
  obtain ⟨W, q₁, p, sq1⟩ := ha ((Functor.reprW (pullback j g)).hom ≫ pullback.fst j g)
  have hPalg : IsAlgebraicSpace B S hS (pullback b g) :=
    isAlgebraicSpace_pullback B S hS b g hX' (isAlgebraicSpace_yoneda B S hS T) hY'
  obtain ⟨c, hcci, hcsurj⟩ :=
    exists_isClosedImmersion_isSurjective_of_pullback_iso_yoneda B S hS hX hX' a b hi hisurj
      hw g (Functor.reprW (pullback j g)).symm hPalg sq1
  have : Mono c := mono_of_isClosedImmersion B S hS c hcci
  have : (pullback b g).IsRepresentable :=
    isRepresentable_of_isIntegralHom_of_bijective B S hS
      (isAlgebraicSpace_yoneda B S hS _) hPalg c
      (isIntegralHom_of_isClosedImmersion B S hS c hcci)
      ⟨pointsMap_injective_of_mono B S hS c, hcsurj⟩
      inferInstance h09YA h07SQ hFinitePresentation
  exact ⟨_, _, _, isPullback_of_pullback_iso_yoneda B S hS b g
    (Functor.reprW (pullback b g)).symm⟩

end Square

/-! ### Morphisms of thickenings -/

section Thickening

variable {X Y : AlgebraicSpaces B S hS} {G : Subfunctor X.1} {H : Subfunctor Y.1}

/-- **Stacks 09ZY, part (1).** In a morphism of thickenings of algebraic spaces over `S` the
morphism on the closed subspaces is affine if and only if the morphism on the ambient spaces
is. -/
theorem isAffineHom_iff_isAffineHom_of_isThickening
    (hG : IsThickening B S hS X G) (hH : IsThickening B S hS Y H)
    (f : Arrow.mk G.ι ⟶ Arrow.mk H.ι)
    (h09YA : ∀ {X₀ Y₀ : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u} (g : X₀ ⟶ Y₀),
      IsAlgebraicSpace B S hS X₀ → IsAlgebraicSpace B S hS Y₀ → IsIntegralHom B S hS g →
      IsQuasiCompactSpace B S hS Y₀ →
      IsAbsolutelyQuasiSeparated B S hS B.contains_terminal Y₀ →
      IntegralFiniteSystem B S hS g)
    (h07SQ : ∀ {I : Type u} [Preorder I] [IsDirected I (· ≤ ·)]
      (D : DescentSituation B S hS B.contains_terminal I),
      IsAffineSpace B S hS D.limitCone.pt →
      ∃ k : I, D.base ≤ k ∧ IsAffineSpace B S hS (D.system.obj (Opposite.op k)))
    (hFinitePresentation : ∀ {X₀ Y₀ : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u} (g : X₀ ⟶ Y₀),
      IsAlgebraicSpace B S hS X₀ → IsAlgebraicSpace B S hS Y₀ → IsFinite B S hS g →
      IsFinitePresentation B S hS g → IsSurjective B S hS g → IsAffineSpace B S hS X₀ →
      IsAffineSpace B S hS Y₀) :
    IsAffineHom B S hS f.left ↔ IsAffineHom B S hS f.right :=
  isAffineHom_iff_isAffineHom_of_isClosedImmersion_square B S hS hG.1.1 X.2 Y.2
    f.left f.right hG.1.2 hG.2 hH.1.2 (Arrow.w f) h09YA h07SQ hFinitePresentation

/-- **Stacks 09ZY, part (5).** In a morphism of thickenings of algebraic spaces over `S` the
morphism on the closed subspaces is integral if and only if the morphism on the ambient spaces
is. -/
theorem isIntegralHom_iff_isIntegralHom_of_isThickening
    (hG : IsThickening B S hS X G) (hH : IsThickening B S hS Y H)
    (f : Arrow.mk G.ι ⟶ Arrow.mk H.ι)
    (h09YA : ∀ {X₀ Y₀ : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u} (g : X₀ ⟶ Y₀),
      IsAlgebraicSpace B S hS X₀ → IsAlgebraicSpace B S hS Y₀ → IsIntegralHom B S hS g →
      IsQuasiCompactSpace B S hS Y₀ →
      IsAbsolutelyQuasiSeparated B S hS B.contains_terminal Y₀ →
      IntegralFiniteSystem B S hS g)
    (h07SQ : ∀ {I : Type u} [Preorder I] [IsDirected I (· ≤ ·)]
      (D : DescentSituation B S hS B.contains_terminal I),
      IsAffineSpace B S hS D.limitCone.pt →
      ∃ k : I, D.base ≤ k ∧ IsAffineSpace B S hS (D.system.obj (Opposite.op k)))
    (hFinitePresentation : ∀ {X₀ Y₀ : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u} (g : X₀ ⟶ Y₀),
      IsAlgebraicSpace B S hS X₀ → IsAlgebraicSpace B S hS Y₀ → IsFinite B S hS g →
      IsFinitePresentation B S hS g → IsSurjective B S hS g → IsAffineSpace B S hS X₀ →
      IsAffineSpace B S hS Y₀) :
    IsIntegralHom B S hS f.left ↔ IsIntegralHom B S hS f.right :=
  isIntegralHom_iff_isIntegralHom_of_isClosedImmersion_square B S hS hG.1.1 X.2 hH.1.1 Y.2
    f.left f.right hG.1.2 hG.2 hH.1.2 (Arrow.w f) h09YA h07SQ hFinitePresentation

/-- **Stacks 09ZY, part (9).** In a morphism of thickenings of algebraic spaces over `S` the
morphism on the closed subspaces is representable by schemes if and only if the morphism on the
ambient spaces is. -/
theorem relativelyRepresentable_iff_relativelyRepresentable_of_isThickening
    (hG : IsThickening B S hS X G) (hH : IsThickening B S hS Y H)
    (f : Arrow.mk G.ι ⟶ Arrow.mk H.ι)
    (h09YA : ∀ {X₀ Y₀ : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u} (g : X₀ ⟶ Y₀),
      IsAlgebraicSpace B S hS X₀ → IsAlgebraicSpace B S hS Y₀ → IsIntegralHom B S hS g →
      IsQuasiCompactSpace B S hS Y₀ →
      IsAbsolutelyQuasiSeparated B S hS B.contains_terminal Y₀ →
      IntegralFiniteSystem B S hS g)
    (h07SQ : ∀ {I : Type u} [Preorder I] [IsDirected I (· ≤ ·)]
      (D : DescentSituation B S hS B.contains_terminal I),
      IsAffineSpace B S hS D.limitCone.pt →
      ∃ k : I, D.base ≤ k ∧ IsAffineSpace B S hS (D.system.obj (Opposite.op k)))
    (hFinitePresentation : ∀ {X₀ Y₀ : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u} (g : X₀ ⟶ Y₀),
      IsAlgebraicSpace B S hS X₀ → IsAlgebraicSpace B S hS Y₀ → IsFinite B S hS g →
      IsFinitePresentation B S hS g → IsSurjective B S hS g → IsAffineSpace B S hS X₀ →
      IsAffineSpace B S hS Y₀) :
    yoneda.relativelyRepresentable f.left ↔ yoneda.relativelyRepresentable f.right :=
  relativelyRepresentable_iff_relativelyRepresentable_of_isClosedImmersion_square B S hS
    hG.1.1 X.2 Y.2 f.left f.right hG.1.2 hG.2 hH.1.2 (Arrow.w f) h09YA h07SQ hFinitePresentation

end Thickening

end AlgebraicGeometry.Space

end
