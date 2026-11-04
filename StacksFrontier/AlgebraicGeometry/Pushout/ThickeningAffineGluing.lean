module

public import Mathlib.AlgebraicGeometry.Morphisms.Etale
public import Mathlib.AlgebraicGeometry.Morphisms.FinitePresentation
public import Mathlib.AlgebraicGeometry.Morphisms.FiniteType
public import Mathlib.AlgebraicGeometry.Morphisms.Smooth
public import StacksCore.Tactic.StacksAttribute
public import StacksFrontier.AlgebraicGeometry.Pushout.SquareSections
public import StacksFrontier.RingTheory.MilnorPatching.Algebras

/-!
# Properties of a scheme glued along a thickening and an affine morphism

Let `i : X ⟶ X'` be a thickening and `f : X ⟶ Y` an affine morphism, and let
`Y' = Y ⨿_X X'` be their pushout.  A triple `(V, U', φ)` consists of a scheme `V` over `Y`, a
scheme `U'` over `X'` and an identification `φ` of `V ×_Y X` with `U' ×_{X'} X`; the two
identified fibre products are a single scheme `U`, which maps to `U'` by a thickening and to `V`
by an affine morphism, and the pushout `V' = V ⨿_U U'` maps to `Y'`.  This file proves that
`V' ⟶ Y'` is locally of finite type, flat, flat and locally of finite presentation, smooth, or
étale exactly when both `V ⟶ Y` and `U' ⟶ X'` are.

## Main definitions

* `AlgebraicGeometry.ThickeningAffinePushoutSituation` is a pushout square along a closed
  immersion and an affine morphism whose sections are a fibre product.
* `AlgebraicGeometry.ThickeningAffinePushoutSituation.Triple` is a triple `(V, U', φ)` over such
  a square, presented as a second such square together with two cartesian squares.
* `AlgebraicGeometry.ThickeningAffinePushoutSituation.Triple.induced` is the morphism
  `V' ⟶ Y'`.

## Main results

* `AlgebraicGeometry.ThickeningAffinePushoutSituation.Triple.locallyOfFiniteType_induced_iff`,
  `flat_induced_iff`, `flat_and_locallyOfFinitePresentation_induced_iff`, `smooth_induced_iff`
  and `etale_induced_iff` are the five clauses of [Stacks Project, Tag 07RX].

The two further assertions of [Stacks Project, Tag 07RX] — that the counit `G(F(W')) ⟶ W'` is
an isomorphism for `W'` flat over `Y'`, and that `F` and `G` are quasi-inverse equivalences
between the schemes flat over `Y'` and the triples with `V ⟶ Y` and `U' ⟶ X'` flat — are *not*
proved here.  They are statements about the adjunction `G ⊣ F`, which lives one layer up, in
`StacksFrontier.AlgebraicGeometry.MoreMorphisms.ThickeningPushoutGluing`, rather than over the
abstract square of this file.
* `AlgebraicGeometry.ThickeningAffinePushoutSituation.ofIsIntegralHom` builds the situation when
  the affine morphism is integral, with no further hypothesis.

## Implementation notes

**What is assumed, and why.**  `ThickeningAffinePushoutSituation` carries the pushout square,
the affineness of its two legs and the identification of its sections as *hypotheses*: the field
`ThickeningAffinePushoutSituation.sections_isPullback` is exactly the last conclusion of
[Stacks Project, Tag 07RT].  Nothing else about Tag 07RT is used, and the surjectivity needed
for Milnor patching comes from `i` being a closed immersion, not from it being a thickening; so
the thickening hypothesis of the source is weakened here to a closed immersion, and the five
clauses hold for squares that Tag 07RT says nothing about.

Carrying those as hypotheses is a generalization, not a gap.  For a thickening and an affine
morphism they are supplied by Tag 07RT, globally and with nothing assumed:
`Stacks.Pushout.thickeningAffinePushoutSituation` assembles the situation out of
`Stacks.Pushout.pushout_structureSheaf_isPullback`, whose own hypothesis
[Stacks Project, Tag 06AD] — a thickening of an affine scheme is affine — is the theorem
`Stacks.Thickenings.forall_isAffine_of_isThickening`.  The five clauses in that form are in
`StacksFrontier.AlgebraicGeometry.MoreMorphisms.ThickeningPushoutEtale` and
`StacksFrontier.AlgebraicGeometry.MoreMorphisms.ThickeningPushoutGluingUnconditional`, and that is
where Tag 07RX is recorded: the statements below are the general form they are deduced from, not
the tag itself.

For a pushout along a closed immersion and an *integral* morphism the sections hypothesis is a
theorem, [Stacks Project, Tag 0E25]; `ThickeningAffinePushoutSituation.ofIsIntegralHom` records
that case.  The situation of [Stacks Project, Tag 07RV] is the remaining one, where `f` is only
affine.

**The reduction.**  All five properties are local on the source and detected on sections over
affine opens.  Over an affine open `U` of `Y'` and an affine open of `V'` above it, the two rings
of sections are fibre products by the sections hypothesis, and the sections on `V` and on `U'`
are the base changes of those on `Y` and on `X'`, because the two squares of the triple are
cartesian and all the opens in sight are affine
(`AlgebraicGeometry.isIso_pushoutSection_of_isAffineOpen`).  The map on sections is therefore
the canonical map produced by Milnor patching, and [Stacks Project, Tag 08KQ] detects all five
properties on the two factors.  The preimage of an affine open of `Y'` in `X` is affine because
`f` is affine; this is the only place affineness of `f` is used.

## References

* [Stacks Project, Tag 07RX](https://stacks.math.columbia.edu/tag/07RX)
* [Stacks Project, Tag 07RV](https://stacks.math.columbia.edu/tag/07RV)
* [Stacks Project, Tag 07RT](https://stacks.math.columbia.edu/tag/07RT)
* [Stacks Project, Tag 08KQ](https://stacks.math.columbia.edu/tag/08KQ)
* [Stacks Project, Tag 0E25](https://stacks.math.columbia.edu/tag/0E25)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits

universe u

namespace AlgebraicGeometry

/-! ### The ring-theoretic input -/

/-- The five properties of [Stacks Project, Tag 08KQ] for a map `h` between the vertices of two
cartesian squares of rings whose upper square is obtained from the lower one by two pushouts,
the lower right-hand map being surjective.  This is
`MilnorPatching.ringHom_properties_pullback_iff_and_reconstruction` transported along the
identification of the two vertices with the standard fibre products. -/
private lemma ringHom_properties_iff_of_isPullback
    {R A B C R' A' B' C' : CommRingCat.{u}}
    {a : R ⟶ A} {b : R ⟶ B} {i : A ⟶ C} {j : B ⟶ C}
    {a' : R' ⟶ A'} {b' : R' ⟶ B'} {i' : A' ⟶ C'} {j' : B' ⟶ C'}
    (h : R ⟶ R') (f : A ⟶ A') (g : B ⟶ B') (k : C ⟶ C')
    (H : IsPullback a b i j) (H' : IsPullback a' b' i' j')
    (Hf : IsPushout f i i' k) (Hg : IsPushout g j j' k)
    (hj : Function.Surjective j)
    (ha : a ≫ f = h ≫ a') (hb : b ≫ g = h ≫ b') :
    (h.hom.FiniteType ↔ f.hom.FiniteType ∧ g.hom.FiniteType) ∧
      (h.hom.Flat ↔ f.hom.Flat ∧ g.hom.Flat) ∧
      ((h.hom.Flat ∧ h.hom.FinitePresentation) ↔
        (f.hom.Flat ∧ f.hom.FinitePresentation) ∧
          (g.hom.Flat ∧ g.hom.FinitePresentation)) ∧
      (h.hom.Smooth ↔ f.hom.Smooth ∧ g.hom.Smooth) ∧
      (h.hom.Etale ↔ f.hom.Etale ∧ g.hom.Etale) := by
  let base : RingFibreProduct.Situation i.hom j.hom (RingHom.ker j.hom) := ⟨hj, rfl⟩
  have H₁ := IsPullback.of_isLimit (CommRingCat.pullbackConeIsLimit i' j')
  let e := H.isoIsPullback A B (IsPullback.of_isLimit (CommRingCat.pullbackConeIsLimit i j))
  let e' := H'.isoIsPullback A' B' H₁
  have criterion := MilnorPatching.ringHom_properties_pullback_iff_and_reconstruction
    i.hom j.hom (RingHom.ker j.hom) base f.hom g.hom k.hom i'.hom j'.hom
    (MilnorPatching.ringPushout_of_isPushout f.hom i.hom i'.hom k.hom Hf)
    (MilnorPatching.ringPushout_of_isPushout g.hom j.hom j'.hom k.hom Hg)
  dsimp only at criterion
  let t := RingHom.codRestrict
    ((f.hom.comp base.pullbackCone.fst.hom).prod
      (g.hom.comp base.pullbackCone.snd.hom)) (RingHom.pullback i'.hom j'.hom)
    (fun x => by
      show i'.hom (f.hom x.1.1) = j'.hom (g.hom x.1.2)
      exact (congrArg (fun q : A ⟶ C' => q.hom x.1.1) Hf.w).trans
        ((congrArg k.hom x.2).trans (congrArg (fun q : B ⟶ C' => q.hom x.1.2) Hg.w).symm))
  have ht : h ≫ e'.hom = e.hom ≫ CommRingCat.ofHom t := by
    apply H₁.hom_ext
    · have ht₁ : CommRingCat.ofHom t ≫ (CommRingCat.pullbackCone i' j').fst =
          (CommRingCat.pullbackCone i j).fst ≫ f := rfl
      calc
        _ = h ≫ a' := by simp [e']
        _ = a ≫ f := ha.symm
        _ = e.hom ≫ ((CommRingCat.pullbackCone i j).fst ≫ f) := by simp [e]
        _ = _ := (congrArg (fun q => e.hom ≫ q) ht₁.symm).trans (Category.assoc _ _ _).symm
    · have ht₂ : CommRingCat.ofHom t ≫ (CommRingCat.pullbackCone i' j').snd =
          (CommRingCat.pullbackCone i j).snd ≫ g := rfl
      calc
        _ = h ≫ b' := by simp [e']
        _ = b ≫ g := hb.symm
        _ = e.hom ≫ ((CommRingCat.pullbackCone i j).snd ≫ g) := by simp [e]
        _ = _ := (congrArg (fun q => e.hom ≫ q) ht₂.symm).trans (Category.assoc _ _ _).symm
  let ea : Arrow.mk h ≅ Arrow.mk (CommRingCat.ofHom t) := Arrow.isoMk e e' ht.symm
  exact ⟨(RingHom.finiteType_respectsIso.arrow_mk_iso_iff ea).trans criterion.1,
    (RingHom.Flat.respectsIso.arrow_mk_iso_iff ea).trans criterion.2.1,
    ((RingHom.Flat.respectsIso.and RingHom.finitePresentation_respectsIso).arrow_mk_iso_iff
      ea).trans criterion.2.2.1,
    (RingHom.Smooth.propertyIsLocal.respectsIso.arrow_mk_iso_iff ea).trans criterion.2.2.2.1,
    (RingHom.Etale.respectsIso.arrow_mk_iso_iff ea).trans criterion.2.2.2.2.1⟩

/-- A pushout square `Y' = Y ⨿_X X'` along a closed immersion `i : X ⟶ X'` and an affine
morphism `f : X ⟶ Y`, whose two other legs are affine and whose sections over every open form a
fibre product.

The last two requirements are conclusions of [Stacks Project, Tag 07RT] for a thickening `i`,
which is not available in this development; see the implementation notes. -/
structure ThickeningAffinePushoutSituation where
  /-- The closed subscheme which is thickened. -/
  X : Scheme.{u}
  /-- The thickening of `X`. -/
  X' : Scheme.{u}
  /-- The target of the affine morphism out of `X`. -/
  Y : Scheme.{u}
  /-- The pushout `Y ⨿_X X'`. -/
  Y' : Scheme.{u}
  /-- The closed immersion `X ⟶ X'`, a thickening in [Stacks Project, Tag 07RT]. -/
  i : X ⟶ X'
  /-- The affine morphism `X ⟶ Y`. -/
  f : X ⟶ Y
  /-- The canonical morphism `X' ⟶ Y'`. -/
  inX' : X' ⟶ Y'
  /-- The canonical morphism `Y ⟶ Y'`. -/
  inY : Y ⟶ Y'
  /-- The morphism `i` is a closed immersion. -/
  [isClosedImmersion_i : IsClosedImmersion i]
  /-- The morphism `f` is affine. -/
  [isAffineHom_f : IsAffineHom f]
  /-- The morphism `X' ⟶ Y'` is affine, as in [Stacks Project, Tag 07RT]. -/
  [isAffineHom_inX' : IsAffineHom inX']
  /-- The morphism `Y ⟶ Y'` is affine, as in [Stacks Project, Tag 07RT]. -/
  [isAffineHom_inY : IsAffineHom inY]
  /-- The square is cocartesian. -/
  isPushout : IsPushout i f inX' inY
  /-- The sections of `Y'` over an open form the fibre product of the sections of `Y` and of
  `X'` over those of `X`.  This is the last conclusion of [Stacks Project, Tag 07RT]. -/
  sections_isPullback : ∀ U : Y'.Opens,
    IsPullback (inY.app U) (inX'.app U) (f.app (inY ⁻¹ᵁ U))
      (i.app (inX' ⁻¹ᵁ U) ≫ eqToHom (congrArg (fun W ↦ Γ(X, W))
        (congrArg (fun k : X ⟶ Y' ↦ k ⁻¹ᵁ U) isPushout.w)))

attribute [instance] ThickeningAffinePushoutSituation.isClosedImmersion_i
  ThickeningAffinePushoutSituation.isAffineHom_f
  ThickeningAffinePushoutSituation.isAffineHom_inX'
  ThickeningAffinePushoutSituation.isAffineHom_inY

namespace ThickeningAffinePushoutSituation

/-- A pushout square along a closed immersion and an *integral* morphism, with the two other legs
affine, is a situation: the sections hypothesis is then [Stacks Project, Tag 0E25]. -/
def ofIsIntegralHom {X X' Y Y' : Scheme.{u}} (i : X ⟶ X') (f : X ⟶ Y) (inX' : X' ⟶ Y')
    (inY : Y ⟶ Y') [IsClosedImmersion i] [IsIntegralHom f] [IsAffineHom inX'] [IsAffineHom inY]
    (h : IsPushout i f inX' inY) : ThickeningAffinePushoutSituation.{u} where
  X := X
  X' := X'
  Y := Y
  Y' := Y'
  i := i
  f := f
  inX' := inX'
  inY := inY
  isAffineHom_f := inferInstance
  isPushout := h
  sections_isPullback U := structureSheaf_isPullback_of_isPushout_of_isAffineHom h U

variable (S : ThickeningAffinePushoutSituation.{u})

/-- The two legs of the pushout square cut out the same open of `X`. -/
private theorem i_preimage_eq (U : S.Y'.Opens) :
    S.i ⁻¹ᵁ (S.inX' ⁻¹ᵁ U) = S.f ⁻¹ᵁ (S.inY ⁻¹ᵁ U) :=
  congrArg (fun k : S.X ⟶ S.Y' ↦ k ⁻¹ᵁ U) S.isPushout.w

/-- The sections hypothesis of a situation, with both maps into the sections on `X` written as
restriction maps to the single open `S.f ⁻¹ᵁ (S.inY ⁻¹ᵁ U)`. -/
private theorem sections_isPullback_appLE (U : S.Y'.Opens) :
    IsPullback (S.inY.app U) (S.inX'.app U)
      (S.f.appLE (S.inY ⁻¹ᵁ U) (S.f ⁻¹ᵁ (S.inY ⁻¹ᵁ U)) le_rfl)
      (S.i.appLE (S.inX' ⁻¹ᵁ U) (S.f ⁻¹ᵁ (S.inY ⁻¹ᵁ U)) (S.i_preimage_eq U).ge) := by
  rw [← app_comp_eqToHom_eq_appLE S.i (S.i_preimage_eq U) (S.i_preimage_eq U).ge]
  simpa only [Scheme.Hom.app_eq_appLE] using S.sections_isPullback U

/-- A triple `(V, U', φ)` over a situation, as in [Stacks Project, Tag 07RV]: a scheme `V` over
`Y`, a scheme `U'` over `X'`, and an identification of `V ×_Y X` with `U' ×_{X'} X`.  The
identified fibre products appear as the single scheme `T.X`, and `T.Y'` is the pushout
`V' = V ⨿_U U'`. -/
structure Triple (S : ThickeningAffinePushoutSituation.{u}) where
  /-- The pushout situation upstairs: `U ⟶ U'`, `U ⟶ V` and `V' = V ⨿_U U'`. -/
  T : ThickeningAffinePushoutSituation.{u}
  /-- The morphism `U' ⟶ X'`. -/
  toX' : T.X' ⟶ S.X'
  /-- The morphism `V ⟶ Y`. -/
  toY : T.Y ⟶ S.Y
  /-- The morphism `U ⟶ X`. -/
  toX : T.X ⟶ S.X
  /-- `U` is the fibre product `U' ×_{X'} X`. -/
  isPullback_i : IsPullback T.i toX toX' S.i
  /-- `U` is the fibre product `V ×_Y X`; composed with the previous square this is the
  identification `φ`. -/
  isPullback_f : IsPullback T.f toX toY S.f

namespace Triple

variable {S : ThickeningAffinePushoutSituation.{u}} (P : S.Triple)

/-- The morphism `V' ⟶ Y'` of [Stacks Project, Tag 07RX], induced by the universal property of
the pushout `V' = V ⨿_U U'`. -/
def induced : P.T.Y' ⟶ S.Y' :=
  P.T.isPushout.desc (P.toX' ≫ S.inX') (P.toY ≫ S.inY) (by
    rw [← Category.assoc, ← Category.assoc, P.isPullback_i.w, P.isPullback_f.w,
      Category.assoc, Category.assoc, S.isPushout.w])

/-- The composite `U' ⟶ V' ⟶ Y'` of the map `V' ⟶ Y'` with `U' ⟶ V'` is `U' ⟶ X' ⟶ Y'`. -/
@[reassoc]
lemma inX'_comp_induced : P.T.inX' ≫ P.induced = P.toX' ≫ S.inX' :=
  P.T.isPushout.inl_desc _ _ _

/-- The composite `V ⟶ V' ⟶ Y'` of the map `V' ⟶ Y'` with `V ⟶ V'` is `V ⟶ Y ⟶ Y'`. -/
@[reassoc]
lemma inY_comp_induced : P.T.inY ≫ P.induced = P.toY ≫ S.inY :=
  P.T.isPushout.inr_desc _ _ _

/-- An open of `V'` lying over an open of `Y'` cuts out an open of `V` lying over the
corresponding open of `Y`. -/
private theorem leY {U : S.Y'.Opens} {V : P.T.Y'.Opens} (e : V ≤ P.induced ⁻¹ᵁ U) :
    P.T.inY ⁻¹ᵁ V ≤ P.toY ⁻¹ᵁ (S.inY ⁻¹ᵁ U) :=
  preimage_le_preimage_of_comm P.inY_comp_induced e

/-- An open of `V'` lying over an open of `Y'` cuts out an open of `U'` lying over the
corresponding open of `X'`. -/
private theorem leX' {U : S.Y'.Opens} {V : P.T.Y'.Opens} (e : V ≤ P.induced ⁻¹ᵁ U) :
    P.T.inX' ⁻¹ᵁ V ≤ P.toX' ⁻¹ᵁ (S.inX' ⁻¹ᵁ U) :=
  preimage_le_preimage_of_comm P.inX'_comp_induced e

/-- If `u ≫ w = x ≫ z`, the sections of `z` on `U` followed by those of `x` agree with the sections
of `w` followed by those of `u`. -/
private theorem app_comp_appLE_eq_appLE_comp_app {A B C D : Scheme.{u}} {u : A ⟶ B} {w : B ⟶ D}
    {x : A ⟶ C} {z : C ⟶ D} (h : u ≫ w = x ≫ z) (U : D.Opens) (V : B.Opens) (e : V ≤ w ⁻¹ᵁ U) :
    z.app U ≫ x.appLE (z ⁻¹ᵁ U) (u ⁻¹ᵁ V) (preimage_le_preimage_of_comm h e) =
      w.appLE U V e ≫ u.app V := by
  rw [Scheme.Hom.app_eq_appLE, Scheme.Hom.app_eq_appLE, Scheme.Hom.appLE_comp_appLE,
    Scheme.Hom.appLE_comp_appLE]
  exact appLE_eq_appLE_of_eq h.symm U (u ⁻¹ᵁ V) _ _

/-- The local form of [Stacks Project, Tag 07RX]: over an affine open `U` of `Y'` and an affine
open `V` of `V'` above it, the map `V' ⟶ Y'` induces on sections the canonical map of Milnor
patching attached to the maps induced by `V ⟶ Y` and `U' ⟶ X'`, so [Stacks Project, Tag 08KQ]
detects all five properties on the latter two. -/
private theorem appLE_induced_iff {U : S.Y'.Opens} {V : P.T.Y'.Opens}
    (hU : IsAffineOpen U) (hV : IsAffineOpen V) (e : V ≤ P.induced ⁻¹ᵁ U) :
    ((P.induced.appLE U V e).hom.FiniteType ↔
        (P.toY.appLE (S.inY ⁻¹ᵁ U) (P.T.inY ⁻¹ᵁ V) (P.leY e)).hom.FiniteType ∧
          (P.toX'.appLE (S.inX' ⁻¹ᵁ U) (P.T.inX' ⁻¹ᵁ V) (P.leX' e)).hom.FiniteType) ∧
      ((P.induced.appLE U V e).hom.Flat ↔
        (P.toY.appLE (S.inY ⁻¹ᵁ U) (P.T.inY ⁻¹ᵁ V) (P.leY e)).hom.Flat ∧
          (P.toX'.appLE (S.inX' ⁻¹ᵁ U) (P.T.inX' ⁻¹ᵁ V) (P.leX' e)).hom.Flat) ∧
      (((P.induced.appLE U V e).hom.Flat ∧
          (P.induced.appLE U V e).hom.FinitePresentation) ↔
        ((P.toY.appLE (S.inY ⁻¹ᵁ U) (P.T.inY ⁻¹ᵁ V) (P.leY e)).hom.Flat ∧
            (P.toY.appLE (S.inY ⁻¹ᵁ U) (P.T.inY ⁻¹ᵁ V)
              (P.leY e)).hom.FinitePresentation) ∧
          ((P.toX'.appLE (S.inX' ⁻¹ᵁ U) (P.T.inX' ⁻¹ᵁ V) (P.leX' e)).hom.Flat ∧
            (P.toX'.appLE (S.inX' ⁻¹ᵁ U) (P.T.inX' ⁻¹ᵁ V)
              (P.leX' e)).hom.FinitePresentation)) ∧
      ((P.induced.appLE U V e).hom.Smooth ↔
        (P.toY.appLE (S.inY ⁻¹ᵁ U) (P.T.inY ⁻¹ᵁ V) (P.leY e)).hom.Smooth ∧
          (P.toX'.appLE (S.inX' ⁻¹ᵁ U) (P.T.inX' ⁻¹ᵁ V) (P.leX' e)).hom.Smooth) ∧
      ((P.induced.appLE U V e).hom.Etale ↔
        (P.toY.appLE (S.inY ⁻¹ᵁ U) (P.T.inY ⁻¹ᵁ V) (P.leY e)).hom.Etale ∧
          (P.toX'.appLE (S.inX' ⁻¹ᵁ U) (P.T.inX' ⁻¹ᵁ V) (P.leX' e)).hom.Etale) := by
  have hUY : IsAffineOpen (S.inY ⁻¹ᵁ U) := hU.preimage S.inY
  have hUX' : IsAffineOpen (S.inX' ⁻¹ᵁ U) := hU.preimage S.inX'
  have hUX : IsAffineOpen (S.f ⁻¹ᵁ (S.inY ⁻¹ᵁ U)) := hUY.preimage S.f
  have hinfY : P.T.f ⁻¹ᵁ (P.T.inY ⁻¹ᵁ V) =
      P.T.f ⁻¹ᵁ (P.T.inY ⁻¹ᵁ V) ⊓ P.toX ⁻¹ᵁ (S.f ⁻¹ᵁ (S.inY ⁻¹ᵁ U)) :=
    (inf_eq_left.mpr (preimage_le_preimage_of_comm P.isPullback_f.w (P.leY e))).symm
  have hinfX : P.T.f ⁻¹ᵁ (P.T.inY ⁻¹ᵁ V) =
      P.T.i ⁻¹ᵁ (P.T.inX' ⁻¹ᵁ V) ⊓ P.toX ⁻¹ᵁ (S.f ⁻¹ᵁ (S.inY ⁻¹ᵁ U)) := by
    rwa [P.T.i_preimage_eq V]
  have Hf := (isIso_pushoutSection_iff P.isPullback_f (hUST := le_rfl)
      (hUSX := P.leY e) (hUY := hinfY)).mp
    (isIso_pushoutSection_of_isAffineOpen P.isPullback_f (hUST := le_rfl)
      (hUSX := P.leY e) (hUY := hinfY) hUY hUX (hV.preimage P.T.inY))
  have Hg := (isIso_pushoutSection_iff P.isPullback_i (hUST := (S.i_preimage_eq U).ge)
      (hUSX := P.leX' e) (hUY := hinfX)).mp
    (isIso_pushoutSection_of_isAffineOpen P.isPullback_i (hUST := (S.i_preimage_eq U).ge)
      (hUSX := P.leX' e) (hUY := hinfX) hUX' hUX (hV.preimage P.T.inX'))
  exact ringHom_properties_iff_of_isPullback (P.induced.appLE U V e)
    (P.toY.appLE (S.inY ⁻¹ᵁ U) (P.T.inY ⁻¹ᵁ V) (P.leY e))
    (P.toX'.appLE (S.inX' ⁻¹ᵁ U) (P.T.inX' ⁻¹ᵁ V) (P.leX' e)) _
    (S.sections_isPullback_appLE U) (P.T.sections_isPullback_appLE V) Hf Hg
    (appLE_surjective_of_isClosedImmersion S.i hUX' (S.i_preimage_eq U) (S.i_preimage_eq U).ge)
    (app_comp_appLE_eq_appLE_comp_app P.inY_comp_induced _ _ _)
    (app_comp_appLE_eq_appLE_comp_app P.inX'_comp_induced _ _ _)

/-- A property of morphisms of schemes coming from a property of ring maps that is detected on
the two factors of a Milnor patching square holds for `V' ⟶ Y'` exactly when it holds for both
`V ⟶ Y` and `U' ⟶ X'`. -/
private theorem iff_of_hasRingHomProperty (Pr : MorphismProperty Scheme.{u})
    {Q : ∀ {R S : Type u} [CommRing R] [CommRing S], (R →+* S) → Prop}
    [HasRingHomProperty Pr Q]
    (hQ : RingHom.StableUnderCompositionWithLocalizationAwaySource Q)
    (key : ∀ (U : S.Y'.Opens) (V : P.T.Y'.Opens), IsAffineOpen U → IsAffineOpen V →
      ∀ e : V ≤ P.induced ⁻¹ᵁ U, (Q (P.induced.appLE U V e).hom ↔
        Q (P.toY.appLE (S.inY ⁻¹ᵁ U) (P.T.inY ⁻¹ᵁ V) (P.leY e)).hom ∧
          Q (P.toX'.appLE (S.inX' ⁻¹ᵁ U) (P.T.inX' ⁻¹ᵁ V) (P.leX' e)).hom)) :
    Pr P.induced ↔ Pr P.toY ∧ Pr P.toX' := by
  constructor
  · intro h
    have h' := (HasRingHomProperty.iff_appLE (P := Pr)).mp h
    exact ⟨of_forall_appLE_preimage hQ P.toY P.induced S.inY P.T.inY P.inY_comp_induced
        fun U V hU hV e => ((key U V hU hV e).mp (h' ⟨U, hU⟩ ⟨V, hV⟩ e)).1,
      of_forall_appLE_preimage hQ P.toX' P.induced S.inX' P.T.inX' P.inX'_comp_induced
        fun U V hU hV e => ((key U V hU hV e).mp (h' ⟨U, hU⟩ ⟨V, hV⟩ e)).2⟩
  · rintro ⟨hY, hX'⟩
    rw [HasRingHomProperty.iff_appLE (P := Pr)]
    rintro ⟨U, hU⟩ ⟨V, hV⟩ e
    exact (key U V hU hV e).mpr
      ⟨(HasRingHomProperty.iff_appLE (P := Pr)).mp hY ⟨_, hU.preimage _⟩ ⟨_, hV.preimage _⟩ _,
        (HasRingHomProperty.iff_appLE (P := Pr)).mp hX' ⟨_, hU.preimage _⟩ ⟨_, hV.preimage _⟩ _⟩

/-- The same transfer for a conjunction of two properties of morphisms of schemes, needed because
[Stacks Project, Tag 08KQ] detects flatness together with finite presentation, and not finite
presentation on its own. -/
private theorem and_iff_of_hasRingHomProperty (Pr₁ Pr₂ : MorphismProperty Scheme.{u})
    {Q₁ Q₂ : ∀ {R S : Type u} [CommRing R] [CommRing S], (R →+* S) → Prop}
    [HasRingHomProperty Pr₁ Q₁] [HasRingHomProperty Pr₂ Q₂]
    (hQ₁ : RingHom.StableUnderCompositionWithLocalizationAwaySource Q₁)
    (hQ₂ : RingHom.StableUnderCompositionWithLocalizationAwaySource Q₂)
    (key : ∀ (U : S.Y'.Opens) (V : P.T.Y'.Opens), IsAffineOpen U → IsAffineOpen V →
      ∀ e : V ≤ P.induced ⁻¹ᵁ U,
        ((Q₁ (P.induced.appLE U V e).hom ∧ Q₂ (P.induced.appLE U V e).hom) ↔
          ((Q₁ (P.toY.appLE (S.inY ⁻¹ᵁ U) (P.T.inY ⁻¹ᵁ V) (P.leY e)).hom ∧
              Q₂ (P.toY.appLE (S.inY ⁻¹ᵁ U) (P.T.inY ⁻¹ᵁ V) (P.leY e)).hom) ∧
            (Q₁ (P.toX'.appLE (S.inX' ⁻¹ᵁ U) (P.T.inX' ⁻¹ᵁ V) (P.leX' e)).hom ∧
              Q₂ (P.toX'.appLE (S.inX' ⁻¹ᵁ U) (P.T.inX' ⁻¹ᵁ V) (P.leX' e)).hom)))) :
    (Pr₁ P.induced ∧ Pr₂ P.induced) ↔
      ((Pr₁ P.toY ∧ Pr₂ P.toY) ∧ (Pr₁ P.toX' ∧ Pr₂ P.toX')) := by
  constructor
  · rintro ⟨h₁, h₂⟩
    have key' (U : S.Y'.Opens) (V : P.T.Y'.Opens) (hU : IsAffineOpen U) (hV : IsAffineOpen V)
        (e : V ≤ P.induced ⁻¹ᵁ U) := (key U V hU hV e).mp
      ⟨(HasRingHomProperty.iff_appLE (P := Pr₁)).mp h₁ ⟨U, hU⟩ ⟨V, hV⟩ e,
        (HasRingHomProperty.iff_appLE (P := Pr₂)).mp h₂ ⟨U, hU⟩ ⟨V, hV⟩ e⟩
    exact ⟨⟨of_forall_appLE_preimage hQ₁ P.toY P.induced S.inY P.T.inY P.inY_comp_induced
          fun U V hU hV e => (key' U V hU hV e).1.1,
        of_forall_appLE_preimage hQ₂ P.toY P.induced S.inY P.T.inY P.inY_comp_induced
          fun U V hU hV e => (key' U V hU hV e).1.2⟩,
      of_forall_appLE_preimage hQ₁ P.toX' P.induced S.inX' P.T.inX' P.inX'_comp_induced
          fun U V hU hV e => (key' U V hU hV e).2.1,
        of_forall_appLE_preimage hQ₂ P.toX' P.induced S.inX' P.T.inX' P.inX'_comp_induced
          fun U V hU hV e => (key' U V hU hV e).2.2⟩
  · rintro ⟨⟨hY₁, hY₂⟩, hX'₁, hX'₂⟩
    rw [HasRingHomProperty.iff_appLE (P := Pr₁)] at hY₁ hX'₁
    rw [HasRingHomProperty.iff_appLE (P := Pr₂)] at hY₂ hX'₂
    have key' (U : S.Y'.Opens) (V : P.T.Y'.Opens) (hU : IsAffineOpen U) (hV : IsAffineOpen V)
        (e : V ≤ P.induced ⁻¹ᵁ U) := (key U V hU hV e).mpr
      ⟨⟨hY₁ ⟨_, hU.preimage _⟩ ⟨_, hV.preimage _⟩ _, hY₂ ⟨_, hU.preimage _⟩ ⟨_, hV.preimage _⟩ _⟩,
        hX'₁ ⟨_, hU.preimage _⟩ ⟨_, hV.preimage _⟩ _, hX'₂ ⟨_, hU.preimage _⟩ ⟨_, hV.preimage _⟩ _⟩
    rw [HasRingHomProperty.iff_appLE (P := Pr₁), HasRingHomProperty.iff_appLE (P := Pr₂)]
    exact ⟨fun ⟨U, hU⟩ ⟨V, hV⟩ e => (key' U V hU hV e).1,
      fun ⟨U, hU⟩ ⟨V, hV⟩ e => (key' U V hU hV e).2⟩

/-! ### The five clauses -/

/-- **[Stacks, Tag 07RX], clause (1).**  In the situation of [Stacks Project, Tag 07RV], the
morphism `V' ⟶ Y'` out of `V' = G(V, U', φ)` is locally of finite type if and only if both
`V ⟶ Y` and `U' ⟶ X'` are locally of finite type. -/
theorem locallyOfFiniteType_induced_iff :
    LocallyOfFiniteType P.induced ↔
      LocallyOfFiniteType P.toY ∧ LocallyOfFiniteType P.toX' :=
  P.iff_of_hasRingHomProperty @LocallyOfFiniteType
    (RingHom.finiteType_stableUnderComposition.stableUnderCompositionWithLocalizationAway
      RingHom.finiteType_holdsForLocalizationAway).left
    fun _ _ hU hV e => (P.appLE_induced_iff hU hV e).1

/-- **[Stacks, Tag 07RX], clause (2).**  In the situation of [Stacks Project, Tag 07RV], the
morphism `V' ⟶ Y'` out of `V' = G(V, U', φ)` is flat if and only if both `V ⟶ Y` and
`U' ⟶ X'` are flat. -/
theorem flat_induced_iff : Flat P.induced ↔ Flat P.toY ∧ Flat P.toX' :=
  P.iff_of_hasRingHomProperty @Flat
    (RingHom.Flat.stableUnderComposition.stableUnderCompositionWithLocalizationAway
      RingHom.Flat.holdsForLocalizationAway).left
    fun _ _ hU hV e => (P.appLE_induced_iff hU hV e).2.1

/-- **[Stacks, Tag 07RX], clause (3).**  In the situation of [Stacks Project, Tag 07RV], the
morphism `V' ⟶ Y'` out of `V' = G(V, U', φ)` is flat and locally of finite presentation if and
only if both `V ⟶ Y` and `U' ⟶ X'` are flat and locally of finite presentation. -/
theorem flat_and_locallyOfFinitePresentation_induced_iff :
    (Flat P.induced ∧ LocallyOfFinitePresentation P.induced) ↔
      ((Flat P.toY ∧ LocallyOfFinitePresentation P.toY) ∧
        (Flat P.toX' ∧ LocallyOfFinitePresentation P.toX')) :=
  P.and_iff_of_hasRingHomProperty @Flat @LocallyOfFinitePresentation
    (RingHom.Flat.stableUnderComposition.stableUnderCompositionWithLocalizationAway
      RingHom.Flat.holdsForLocalizationAway).left
    (RingHom.finitePresentation_stableUnderComposition.stableUnderCompositionWithLocalizationAway
      RingHom.finitePresentation_holdsForLocalizationAway).left
    fun _ _ hU hV e => (P.appLE_induced_iff hU hV e).2.2.1

/-- **[Stacks, Tag 07RX], clause (4).**  In the situation of [Stacks Project, Tag 07RV], the
morphism `V' ⟶ Y'` out of `V' = G(V, U', φ)` is smooth if and only if both `V ⟶ Y` and
`U' ⟶ X'` are smooth. -/
theorem smooth_induced_iff : Smooth P.induced ↔ Smooth P.toY ∧ Smooth P.toX' :=
  P.iff_of_hasRingHomProperty @Smooth
    (RingHom.Smooth.stableUnderComposition.stableUnderCompositionWithLocalizationAway
      RingHom.Smooth.holdsForLocalizationAway).left
    fun _ _ hU hV e => (P.appLE_induced_iff hU hV e).2.2.2.1

/-- **[Stacks, Tag 07RX], clause (5).**  In the situation of [Stacks Project, Tag 07RV], the
morphism `V' ⟶ Y'` out of `V' = G(V, U', φ)` is étale if and only if both `V ⟶ Y` and
`U' ⟶ X'` are étale. -/
theorem etale_induced_iff : Etale P.induced ↔ Etale P.toY ∧ Etale P.toX' :=
  P.iff_of_hasRingHomProperty @Etale
    (RingHom.Etale.stableUnderComposition.stableUnderCompositionWithLocalizationAway
      (RingHom.Etale.propertyIsLocal.HoldsForLocalizationAway
        RingHom.Etale.containsIdentities)).left
    fun _ _ hU hV e => (P.appLE_induced_iff hU hV e).2.2.2.2

end Triple

end ThickeningAffinePushoutSituation

end AlgebraicGeometry

end
