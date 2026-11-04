module

public import StacksCore.Tactic.StacksAttribute
public import StacksFrontier.AlgebraicGeometry.Spaces.FiniteProperQuasiFiniteTfae
public import StacksFrontier.AlgebraicGeometry.Spaces.ImmersionBaseChange
public import StacksFrontier.AlgebraicGeometry.Spaces.Morphisms.UniversallyInjective
public import StacksFrontier.AlgebraicGeometry.Spaces.ProperComposition
public import StacksFrontier.AlgebraicGeometry.Spaces.Thickenings.FiniteOrderMorphismEtaleLocal
public import StacksFrontier.AlgebraicGeometry.Spaces.Thickenings.OpenSubspaces
public import StacksFrontier.AlgebraicGeometry.Spaces.Thickenings.SeparatedAndClosed

/-!
# Immersions, properness and finiteness across a cartesian morphism of finite-order thickenings

Let

```
X --f--→ Y
|        |
↓        ↓
X' -f'-→ Y'
```

be a commutative square of algebraic spaces over a scheme `S` in which `X ⊂ X'` and `Y ⊂ Y'`
are thickenings, the thickening `Y ⊂ Y'` is of finite order, and the square identifies `X` with
`Y ×_{Y'} X'`; that is, let it be a
`AlgebraicGeometry.Space.CartesianFiniteOrderMorphismOfThickenings`. This file proves the four
clauses of Stacks 09ZZ about immersion-like and finiteness-like properties: `f` is a closed
immersion, proper, finite, respectively an immersion exactly when `f'` is. These are parts (1),
(7), (8) and (10) of the tag.

None of the four properties is étale local on the source, so the engine
`AlgebraicGeometry.Space.holdsOnEveryEtaleChart_iff_of_cartesianFiniteOrderMorphismOfThickenings`
of the frame file does not apply to any of them, and each is assembled from clauses already
proved for this situation together with permanence properties of morphisms of algebraic spaces.

**Properness** is the conjunction of separatedness, local finite type, quasi-compactness and
universal closedness. Three of the four are invariant under an *arbitrary* morphism of
thickenings — parts (6), (3) and (4) of Stacks 09ZY, proved in
`StacksFrontier/AlgebraicGeometry/Spaces/Thickenings/SeparatedAndClosed.lean` — and the remaining
one is part (2) of this tag, proved in the frame file.

**Finiteness** is properness together with local quasi-finiteness, by Stacks 0A4X; properness
is the clause just proved and local quasi-finiteness is part (3) of this tag.

**Closed immersions** are not a chart condition but a representability condition, so neither the
étale-chart engine nor properness gives them. The route is Stacks 05W8: a morphism of algebraic
spaces is a closed immersion exactly when it is universally closed, unramified and universally
injective. Universal closedness is part (4) of Stacks 09ZY and unramifiedness is part (6) of
this tag; universal injectivity is new, and is obtained without any monomorphism clause. The
composite `X ⟶ Y ⟶ Y'` equals `X ⟶ X' ⟶ Y'`; a closed immersion is universally injective, by
Stacks 05W8 again, so both `f` and the inclusion `Y ⊂ Y'` are, hence so is the composite, hence
so is `X ⟶ X' ⟶ Y'`; and the inclusion `X ⊂ X'` is surjective, so `f'` is universally injective
by the cancellation `universallyInjective_of_isSurjective_comp` proved below. The converse
direction is base change along the cartesian square.

**Immersions** reduce to closed immersions by the closed-then-open factorisation of Stacks 04CE,
which is unconditional for algebraic spaces: `f` factors as a closed immersion into the open
subspace `V ⊆ Y` complementary to the boundary of the image of `f`. By Stacks 05ZP that open
subspace is the inverse image of a unique open subspace `V' ⊆ Y'`, and `f'` factors through `V'`
because the inclusions of the two thickenings are bijective on points. The square restricted to
`V'` is again a cartesian morphism of finite-order thickenings — its target thickening is the
inverse image of `Y ⊆ Y'`, of finite order by Stacks 09ZX — so part (1) makes `X' ⟶ V'` a closed
immersion and `f'` is that followed by the open immersion of `V'`.

## What is carried

Nothing is assumed without proof, and no clause is proved from a clause not proved here or in
the two files this one builds on. In particular the monomorphism clause, part (9) of the tag, is
*not* used: deriving part (1) from parts (8) and (9) and part (9) from part (1) would be
circular, and the route through Stacks 05W8 taken here avoids it.
Part (1) does not use parts (7) or (8) either.

## Main results

* `AlgebraicGeometry.Space.universallyInjective_of_isSurjective_comp`: if `X` is universally
  injective over `T` and `X ⟶ Y` is surjective, then `Y` is universally injective over `T`.
* `AlgebraicGeometry.Space.CartesianFiniteOrderMorphismOfThickenings.isProper_iff`: part (7) of
  Stacks 09ZZ.
* `AlgebraicGeometry.Space.CartesianFiniteOrderMorphismOfThickenings.isFinite_iff`: part (8) of
  Stacks 09ZZ.
* `AlgebraicGeometry.Space.CartesianFiniteOrderMorphismOfThickenings.isClosedImmersion_iff`:
  part (1) of Stacks 09ZZ.
* `AlgebraicGeometry.Space.CartesianFiniteOrderMorphismOfThickenings.isImmersion_iff`: part (10)
  of Stacks 09ZZ.

## Implementation notes

**The finite-order hypothesis is on the target thickening `Y ⊂ Y'`, not on the source
`X ⊂ X'`.** This is the convention of the frame file
`StacksFrontier/AlgebraicGeometry/Spaces/Thickenings/CartesianFiniteOrderMorphism.lean`, whose
implementation notes explain it: the tag's text puts finite order on the source, but the lemma
it reduces to, Stacks 09ZW, puts it on the target, and the tag's own proof argues by induction
on the order of the thickening `Y ⊂ Y'`. In the presence of the cartesian square target finite
order implies source finite order, by Stacks 09ZX, but not conversely, so the statements below
are weaker than the tag's text announces. The clause strings of the four theorems say so.

The two routes this file does *not* take are worth recording. Part (1) could be proved from
part (8) by identifying a finite morphism with its affine charts and testing the closed-immersion
condition there, but a finite morphism of affine schemes is a closed immersion exactly when it is
a monomorphism, so that route needs part (9). It could also be proved from Stacks 05ZR, that the
ambient space of a thickening whose thin side is a scheme is a scheme; that statement is not
available in this library — see the implementation notes of
`StacksFrontier/AlgebraicGeometry/Spaces/Thickenings/Scheme.lean`, which records that the affine
case of its proof is missing.

The restriction of the cartesian square to the open subspace `V'` needs the two descriptions of
`V ∩ V'` inside `Y'` — as the inverse image of `V'` in `Y` and as the inverse image of `Y` in
`V'` — to be identified. Both are fibre products of the same cospan, by Stacks 083Q, so
`CategoryTheory.IsPullback.isoIsPullback` identifies them, and the comparison is an isomorphism
rather than an equality, which is why the restricted morphism of smaller spaces is the
factorisation of `f` composed with that isomorphism.

## References

* [Stacks Project, Tag 09ZZ](https://stacks.math.columbia.edu/tag/09ZZ)
* [Stacks Project, Tag 09ZY](https://stacks.math.columbia.edu/tag/09ZY)
* [Stacks Project, Tag 09ZX](https://stacks.math.columbia.edu/tag/09ZX)
* [Stacks Project, Tag 05W8](https://stacks.math.columbia.edu/tag/05W8)
* [Stacks Project, Tag 05ZP](https://stacks.math.columbia.edu/tag/05ZP)
* [Stacks Project, Tag 04CE](https://stacks.math.columbia.edu/tag/04CE)
* [Stacks Project, Tag 0A4X](https://stacks.math.columbia.edu/tag/0A4X)
* [Stacks Project, Tag 083Q](https://stacks.math.columbia.edu/tag/083Q)
-/

@[expose] public section

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits
open Stacks.Thickenings

universe u

namespace AlgebraicGeometry.Space

/-! ### Universal injectivity of the image of a surjection -/

section UniversallyInjective

variable (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)
    {X Y T : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u}

/-- Let `X ⟶ Y ⟶ T` be morphisms of algebraic spaces over `S`. If `X` is universally injective
over `T` and `X ⟶ Y` is surjective, then `Y` is universally injective over `T`.

This is the universally injective counterpart of
`AlgebraicGeometry.Space.universallyClosed_of_isSurjective_comp` and has the same proof: a base
change of the composite maps onto the corresponding base change of the second factor by a
morphism which is again surjective, and an injective map which factors through a surjection has
injective second factor. -/
theorem universallyInjective_of_isSurjective_comp
    (hX : IsAlgebraicSpace B S hS X) (hY : IsAlgebraicSpace B S hS Y)
    (hT : IsAlgebraicSpace B S hS T) (f : X ⟶ Y) (q : Y ⟶ T)
    (hfq : UniversallyInjective B S hS (f ≫ q)) (hf : IsSurjective B S hS f) :
    UniversallyInjective B S hS q := by
  intro W hW k
  have hR : IsAlgebraicSpace B S hS (pullback k (f ≫ q)) :=
    isAlgebraicSpace_pullback B S hS k (f ≫ q) hW hX hT
  have hP : IsAlgebraicSpace B S hS (pullback k q) :=
    isAlgebraicSpace_pullback B S hS k q hW hY hT
  have hcomm : pullback.fst k (f ≫ q) ≫ k = (pullback.snd k (f ≫ q) ≫ f) ≫ q := by
    rw [Category.assoc]
    exact pullback.condition
  set r : pullback k (f ≫ q) ⟶ pullback k q :=
    pullback.lift (pullback.fst k (f ≫ q)) (pullback.snd k (f ≫ q) ≫ f) hcomm
  have hrfst : r ≫ pullback.fst k q = pullback.fst k (f ≫ q) := pullback.lift_fst _ _ _
  have hrsnd : r ≫ pullback.snd k q = pullback.snd k (f ≫ q) ≫ f := pullback.lift_snd _ _ _
  have hsquare : IsPullback r (pullback.snd k (f ≫ q)) (pullback.snd k q) f :=
    IsPullback.of_right (by rw [hrfst]; exact IsPullback.of_hasPullback k (f ≫ q)) hrsnd
      (IsPullback.of_hasPullback k q)
  have hsurj : IsSurjective B S hS r := by
    let Rₐ : AlgebraicSpaces B S hS := ⟨pullback k (f ≫ q), hR⟩
    let Pₐ : AlgebraicSpaces B S hS := ⟨pullback k q, hP⟩
    let Xₐ : AlgebraicSpaces B S hS := ⟨X, hX⟩
    let Yₐ : AlgebraicSpaces B S hS := ⟨Y, hY⟩
    have hA : IsPullback
        (ObjectProperty.homMk (pullback.snd k (f ≫ q)) : Rₐ ⟶ Xₐ)
        (ObjectProperty.homMk r : Rₐ ⟶ Pₐ)
        (ObjectProperty.homMk f : Xₐ ⟶ Yₐ)
        (ObjectProperty.homMk (pullback.snd k q) : Pₐ ⟶ Yₐ) :=
      IsPullback.of_map (ObjectProperty.ι _)
        (ObjectProperty.hom_ext _ hsquare.flip.w) hsquare.flip
    exact isSurjective_of_isPullback B S hS hA hf
  have hgoal : Function.Injective
      (pointsMap B S hS (pullback k (f ≫ q)) (r ≫ pullback.fst k q)) := by
    rw [hrfst]
    exact hfq W hW k
  rw [pointsMap_comp] at hgoal
  exact hgoal.of_comp_right hsurj

end UniversallyInjective

namespace CartesianFiniteOrderMorphismOfThickenings

variable {B : BigFppfSite.{u}} {S : Scheme.{u}} {hS : B.Contains S}
    (M : CartesianFiniteOrderMorphismOfThickenings B S hS)

/-! ### The cartesian square in the category of algebraic spaces -/

/-- The smaller source of a cartesian morphism of finite-order thickenings, as an algebraic
space over `S`. -/
abbrev sourceSpace : AlgebraicSpaces B S hS := ⟨M.X.toFunctor, M.sourceThickening.1.1⟩

/-- The smaller target of a cartesian morphism of finite-order thickenings, as an algebraic
space over `S`. -/
abbrev targetSpace : AlgebraicSpaces B S hS := ⟨M.Y.toFunctor, M.targetThickening.1.1⟩

/-- The cartesian square of a cartesian morphism of finite-order thickenings, read in the
category of algebraic spaces over `S`. -/
theorem isPullback_spaces :
    IsPullback (ObjectProperty.homMk M.X.ι : M.sourceSpace ⟶ M.X')
      (ObjectProperty.homMk M.f : M.sourceSpace ⟶ M.targetSpace)
      (ObjectProperty.homMk M.f' : M.X' ⟶ M.Y')
      (ObjectProperty.homMk M.Y.ι : M.targetSpace ⟶ M.Y') :=
  IsPullback.of_map_of_faithful
    (F := ObjectProperty.ι
      (fun F : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u => IsAlgebraicSpace B S hS F))
    M.cartesian.flip

/-! ### Properness and finiteness -/

/-- **Stacks 09ZZ, part (7).** Properness is invariant under a cartesian morphism of thickenings
of algebraic spaces whose target thickening is of finite order.

Properness is the conjunction of separatedness, local finite type, quasi-compactness and
universal closedness. The first, third and fourth are invariant under an arbitrary morphism of
thickenings, by parts (6), (3) and (4) of Stacks 09ZY, and the second is part (2) of this
tag. -/
@[stacks 09ZZ "part (7), proper; the finite-order hypothesis is on the TARGET thickening \
Y ⊆ Y', which is strictly stronger than the source hypothesis X ⊆ X' in the tag's text, so \
this is a weaker theorem than the tag announces. It is the hypothesis the tag's own proof \
uses: it reduces to Tag 09ZW, which puts finite order on the target, and says 'by induction \
on the order of the thickening we may assume that Y ⊆ Y' is a first order thickening'. \
Cartesianness plus target finite order gives source finite order by Tag 09ZX, but not \
conversely"]
theorem isProper_iff : IsProper B S hS M.f ↔ IsProper B S hS M.f' :=
  and_congr
    (isSeparated_iff_isSeparated_of_isThickening B S hS M.sourceThickening M.targetThickening
      M.morphism)
    (and_congr
      (and_congr M.isLocallyOfFiniteType_iff
        (isQuasiCompact_iff_isQuasiCompact_of_isThickening B S hS M.sourceThickening
          M.targetThickening M.morphism))
      (universallyClosed_iff_universallyClosed_of_isThickening B S hS M.sourceThickening
        M.targetThickening M.morphism))

/-- **Stacks 09ZZ, part (8).** Finiteness is invariant under a cartesian morphism of thickenings
of algebraic spaces whose target thickening is of finite order.

By Stacks 0A4X a morphism of algebraic spaces is finite exactly when it is proper and locally
quasi-finite, and both of those are invariant: properness by part (7) of this tag and local
quasi-finiteness by part (3). -/
@[stacks 09ZZ "part (8), finite; the finite-order hypothesis is on the TARGET thickening \
Y ⊆ Y', which is strictly stronger than the source hypothesis X ⊆ X' in the tag's text, so \
this is a weaker theorem than the tag announces. It is the hypothesis the tag's own proof \
uses: it reduces to Tag 09ZW, which puts finite order on the target, and says 'by induction \
on the order of the thickening we may assume that Y ⊆ Y' is a first order thickening'. \
Cartesianness plus target finite order gives source finite order by Tag 09ZX, but not \
conversely"]
theorem isFinite_iff : IsFinite B S hS M.f ↔ IsFinite B S hS M.f' :=
  ((isFinite_tfae B S hS M.sourceThickening.1.1 M.targetThickening.1.1 M.f).out 1 2).trans
    ((and_congr M.isProper_iff M.isLocallyQuasiFinite_iff).trans
      ((isFinite_tfae B S hS M.X'.2 M.Y'.2 M.f').out 1 2).symm)

/-! ### Closed immersions -/

/-- Stacks 05W8: a closed immersion of algebraic spaces is a universally closed, unramified,
universally injective morphism, and conversely. -/
private theorem isClosedImmersion_iff_and
    {X Y : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u} (hX : IsAlgebraicSpace B S hS X)
    (hY : IsAlgebraicSpace B S hS Y) (f : X ⟶ Y) :
    IsClosedImmersion B S hS f ↔ UniversallyClosed B S hS f ∧
      (IsUnramified B S hS f ∧ UniversallyInjective B S hS f) :=
  (closedImmersion_conditions_tfae B S hS hX hY f).out 1 3

/-- The inclusion of the smaller target of a cartesian morphism of finite-order thickenings is
universally injective: it is a closed immersion, and by Stacks 05W8 a closed immersion is a
universally closed, unramified, universally injective morphism. -/
theorem universallyInjective_targetThickening_ι :
    UniversallyInjective B S hS M.Y.ι :=
  ((isClosedImmersion_iff_and M.targetThickening.1.1 M.Y'.2 M.Y.ι).mp
    M.targetThickening.1.2).2.2

/-- **Stacks 09ZZ, part (1).** Being a closed immersion is invariant under a cartesian morphism
of thickenings of algebraic spaces whose target thickening is of finite order.

The implication from the ambient morphism to the morphism of smaller spaces is base change
along the cartesian square. In the other direction, Stacks 05W8 characterises closed immersions
of algebraic spaces as the universally closed, unramified, universally injective morphisms, and
each of those three conditions is invariant: universal closedness by part (4) of Stacks 09ZY,
unramifiedness by part (6) of this tag, and universal injectivity because
`X ⟶ Y ⟶ Y'` equals `X ⟶ X' ⟶ Y'`, the inclusions of the two thickenings are universally
injective closed immersions and the source inclusion is surjective. -/
@[stacks 09ZZ "part (1), closed immersion; the finite-order hypothesis is on the TARGET \
thickening Y ⊆ Y', which is strictly stronger than the source hypothesis X ⊆ X' in the tag's \
text, so this is a weaker theorem than the tag announces. It is the hypothesis the tag's own \
proof uses: it reduces to Tag 09ZW, which puts finite order on the target, and says 'by \
induction on the order of the thickening we may assume that Y ⊆ Y' is a first order \
thickening'. Cartesianness plus target finite order gives source finite order by Tag 09ZX, \
but not conversely"]
theorem isClosedImmersion_iff :
    IsClosedImmersion B S hS M.f ↔ IsClosedImmersion B S hS M.f' := by
  refine ⟨fun hf => ?_, fun hf' => isClosedImmersion_of_isPullback B S hS M.isPullback_spaces hf'⟩
  obtain ⟨huc, hunram, huinj⟩ :=
    (isClosedImmersion_iff_and M.sourceThickening.1.1 M.targetThickening.1.1 M.f).mp hf
  refine (isClosedImmersion_iff_and
    M.X'.2 M.Y'.2 M.f').mpr ⟨?_, M.isUnramified_iff.mp hunram, ?_⟩
  · exact (universallyClosed_iff_universallyClosed_of_isThickening B S hS M.sourceThickening
      M.targetThickening M.morphism).mp huc
  · have hcomp : UniversallyInjective B S hS (M.f ≫ M.Y.ι) :=
      universallyInjective_comp B S hS M.targetThickening.1.1 M.Y'.2 M.f M.Y.ι huinj
        M.universallyInjective_targetThickening_ι
    rw [show M.f ≫ M.Y.ι = M.X.ι ≫ M.f' from M.morphism.w] at hcomp
    exact universallyInjective_of_isSurjective_comp B S hS M.sourceThickening.1.1 M.X'.2 M.Y'.2
      M.X.ι M.f' hcomp M.sourceThickening.2

/-! ### Immersions -/

/-- The step of part (10) of Stacks 09ZZ which the closed-then-open factorisation of Stacks
04CE feeds: if the morphism `f` of smaller spaces factors as a closed immersion into an open
subspace `V ⊆ Y`, then the ambient morphism `f'` is an immersion.

The open subspace `V` of the thin side of the target thickening is the inverse image of a
unique open subspace `V' ⊆ Y'`, by Stacks 05ZP, and `f'` factors through `V'` because the two
thickenings are bijective on points. Restricting the cartesian square to `V'` gives a new
cartesian morphism of finite-order thickenings, whose target thickening is the inverse image of
`Y ⊆ Y'` and so of finite order by Stacks 09ZX, and whose morphism of smaller spaces is `f`
read into `V'`; part (1) makes its ambient morphism `X' ⟶ V'` a closed immersion, and `f'` is
that followed by the open immersion of `V'`. -/
theorem isImmersion_right_of_isClosedImmersion_into_openSubspace
    (V : Subfunctor M.Y.toFunctor) (hV : IsOpenSubspace B S hS V)
    (c : M.X.toFunctor ⟶ V.toFunctor) (hc : IsClosedImmersion B S hS c)
    (hcι : c ≫ V.ι = M.f) : IsImmersion B S hS M.f' := by
  obtain ⟨V', ⟨hV'open, rfl⟩, -⟩ :=
    existsUnique_isOpenSubspace_preimage_eq_of_isThickening B S hS M.targetThickening V hV
  let V'sp : AlgebraicSpaces B S hS := ⟨V'.toFunctor, hV'open.1⟩
  let W : Subfunctor V'sp.1 := M.Y.preimage V'.ι
  have hWorder : IsFiniteOrderThickening B S hS V'sp W :=
    isFiniteOrderThickening_preimage B S hS M.Y (ObjectProperty.homMk V'.ι : V'sp ⟶ M.Y')
      M.targetFiniteOrder
  have hA : IsPullback (V'.fromPreimage M.Y.ι) (V'.preimage M.Y.ι).ι V'.ι M.Y.ι :=
    Subfunctor.isPullback_preimage M.Y.ι V'
  have hB : IsPullback (M.Y.fromPreimage V'.ι) W.ι M.Y.ι V'.ι :=
    Subfunctor.isPullback_preimage V'.ι M.Y
  let e : (V'.preimage M.Y.ι).toFunctor ≅ W.toFunctor := hA.flip.isoIsPullback _ _ hB
  have he_fst : e.hom ≫ M.Y.fromPreimage V'.ι = (V'.preimage M.Y.ι).ι :=
    hA.flip.isoIsPullback_hom_fst _ _ hB
  have he_snd : e.hom ≫ W.ι = V'.fromPreimage M.Y.ι :=
    hA.flip.isoIsPullback_hom_snd _ _ hB
  have hmaps : (c ≫ V'.fromPreimage M.Y.ι) ≫ V'.ι = M.X.ι ≫ M.f' := by
    rw [Category.assoc, hA.w, ← Category.assoc, hcι]
    exact M.morphism.w
  -- The ambient morphism factors through `V'`, because the two thickenings are bijective
  -- on points.
  have hrange : Set.range (pointsMap B S hS M.X'.1 M.f') ⊆
      Set.range (pointsMap B S hS V'.toFunctor V'.ι) := by
    rintro y' ⟨x', rfl⟩
    obtain ⟨x, hx⟩ := M.sourceThickening.2 x'
    subst hx
    refine ⟨pointsMap B S hS M.X.toFunctor (c ≫ V'.fromPreimage M.Y.ι) x, ?_⟩
    have h := congrFun
      (pointsMap_comp B S hS M.X.toFunctor (c ≫ V'.fromPreimage M.Y.ι) V'.ι) x
    rw [hmaps] at h
    exact h.symm.trans (congrFun (pointsMap_comp B S hS M.X.toFunctor M.X.ι M.f') x)
  obtain ⟨g', hg'⟩ :=
    (factorsThrough_openSubspace_iff_points B S hS M.Y'.2 M.X'.2 V' hV'open M.f').2 hrange
  have hw : (c ≫ e.hom) ≫ W.ι = M.X.ι ≫ g' := by
    rw [Category.assoc, he_snd]
    exact (cancel_mono V'.ι).mp (by rw [hmaps, Category.assoc, hg'])
  have hs : IsPullback ((c ≫ e.hom) ≫ M.Y.fromPreimage V'.ι) M.X.ι M.Y.ι (g' ≫ V'.ι) := by
    rw [show (c ≫ e.hom) ≫ M.Y.fromPreimage V'.ι = M.f by
      rw [Category.assoc, he_fst, hcι], hg']
    exact M.cartesian
  let N : CartesianFiniteOrderMorphismOfThickenings B S hS :=
    { X' := M.X'
      Y' := V'sp
      X := M.X
      Y := W
      sourceThickening := M.sourceThickening
      targetFiniteOrder := hWorder
      morphism := Arrow.homMk (c ≫ e.hom) g' hw
      cartesian := IsPullback.of_right hs hw hB }
  have hiff : IsClosedImmersion B S hS (c ≫ e.hom) ↔ IsClosedImmersion B S hS g' :=
    N.isClosedImmersion_iff
  rw [← hg']
  have _ := isImmersion_isStableUnderComposition B S hS
  exact MorphismProperty.comp_mem _ _ _
    (isImmersion_of_isClosedImmersion B S hS
      (hiff.mp (MorphismProperty.RespectsIso.postcomp _ e.hom c hc)))
    (isImmersion_of_isOpenImmersion B S hS hV'open.2)

/-- **Stacks 09ZZ, part (10).** Being an immersion is invariant under a cartesian morphism of
thickenings of algebraic spaces whose target thickening is of finite order.

The implication from the ambient morphism to the morphism of smaller spaces is base change
along the cartesian square. In the other direction, Stacks 04CE factors the immersion `f` as a
closed immersion into the open subspace of `Y` complementary to the boundary of the image of
`f`, and `isImmersion_right_of_isClosedImmersion_into_openSubspace` above turns that
factorisation into an immersion factorisation of `f'` using part (1). -/
@[stacks 09ZZ "part (10), immersion; the finite-order hypothesis is on the TARGET thickening \
Y ⊆ Y', which is strictly stronger than the source hypothesis X ⊆ X' in the tag's text, so \
this is a weaker theorem than the tag announces. It is the hypothesis the tag's own proof \
uses: it reduces to Tag 09ZW, which puts finite order on the target, and says 'by induction \
on the order of the thickening we may assume that Y ⊆ Y' is a first order thickening'. \
Cartesianness plus target finite order gives source finite order by Tag 09ZX, but not \
conversely"]
theorem isImmersion_iff : IsImmersion B S hS M.f ↔ IsImmersion B S hS M.f' := by
  refine ⟨fun hf => ?_, fun hf' => isImmersion_of_isPullback B S hS M.isPullback_spaces hf'⟩
  obtain ⟨c, hc, hcι⟩ := exists_isClosedImmersion_comp_ι_boundaryComplement B S hS
    M.targetThickening.1.1 M.sourceThickening.1.1 M.f hf
  exact M.isImmersion_right_of_isClosedImmersion_into_openSubspace _
    (isOpenSubspace_boundaryComplement B S hS M.targetThickening.1.1
      (isLocallyClosed_range_pointsMap_of_isImmersion B S hS M.targetThickening.1.1 M.f hf))
    c hc hcι

end CartesianFiniteOrderMorphismOfThickenings

end AlgebraicGeometry.Space

end
