module

public import StacksFrontier.AlgebraicGeometry.Spaces.Morphisms.ClosedImmersions
public import StacksFrontier.AlgebraicGeometry.Spaces.Pushouts.ThickeningAffinePushoutTheorem

/-!
# The legs of a thickening-and-affine square are affine

Let `i : X ⟶ X'` and `b : Y ⟶ Y'` be thickenings and `f : X ⟶ Y` an affine morphism of algebraic
spaces over `S`, and let `a : X' ⟶ Y'` close the square, `i ≫ a = f ≫ b`.  Then `a` is affine.
Over an affine scheme `T ⟶ Y'` the base change `X' ×_{Y'} T` receives the base change of `i`,
which is a thickening, from `X ×_{Y'} T`; the latter is affine because `f ≫ b = i ≫ a` is affine,
and a thickening of an affine algebraic space is affine (Stacks 05ZR in its affine form).

Applied to the pushout `Y' = Y ⨿_X X'` of Stacks 07VX, whose second leg `Y ⟶ Y'` is a thickening,
this says that both legs of the pushout square are affine, which is used in the proof of
Stacks 08KV: the three base changes of a morphism `V' ⟶ Y'` to `Y`, `X'` and `X` are affine,
hence representable, and their sections over an affine chart are computed on affine schemes.

## Main results

* `AlgebraicGeometry.Space.isAffineHom_of_comp_eq_of_isThickeningHom`: the leg `a` of a
  commutative square as above is affine.
* `AlgebraicGeometry.Space.isAffineHom_pushout_inl` and
  `AlgebraicGeometry.Space.isAffineHom_pushout_inr`: both legs of the pushout of Stacks 07VX
  are affine.

## References

* [Stacks Project, Tag 07VX](https://stacks.math.columbia.edu/tag/07VX)
* [Stacks Project, Tag 05ZR](https://stacks.math.columbia.edu/tag/05ZR)
* [Stacks Project, Tag 08KV](https://stacks.math.columbia.edu/tag/08KV)
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits

universe u

namespace AlgebraicGeometry.Space

/-- Pullbacks of presheaves on `BigFppfOver B S hS`, given directly: instance search for them
times out under Lean v4.35.0. -/
local instance (priority := high) hasPullback_presheaf_ThickeningAffineLegs
    {B : BigFppfSite.{u}} {S : Scheme.{u}} {hS : B.Contains S}
    {X Y Z : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u} (f : X ⟶ Z) (g : Y ⟶ Z) :
    HasLimit (cospan f g) :=
  (Limits.functorCategoryHasLimitsOfShape :
    HasPullbacks ((BigFppfOver B S hS)ᵒᵖ ⥤ Type u)).has_limit _

/-- Pullbacks in presheaves on `BigFppfOver B S hS`, given directly (see above). -/
local instance (priority := high) hasPullbacks_presheaf_ThickeningAffineLegs
    {B : BigFppfSite.{u}} {S : Scheme.{u}} {hS : B.Contains S} :
    HasPullbacks ((BigFppfOver B S hS)ᵒᵖ ⥤ Type u) :=
  Limits.functorCategoryHasLimitsOfShape

variable (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)

/-- A thickening of algebraic spaces is affine: it is a closed immersion (Stacks 07U2). -/
theorem isAffineHom_of_isThickeningHom {X Y : AlgebraicSpaces B S hS} (b : X ⟶ Y)
    (hb : IsThickeningHom B S hS b) : IsAffineHom B S hS b.hom :=
  isAffineHom_of_isClosedImmersion B S hS b.hom
    ((isThickeningHom_iff_isClosedImmersion_and_isSurjective B S hS b).1 hb).1

/-- **The leg of a thickening-and-affine square is affine.**  If `i : X ⟶ X'` and `b : Y ⟶ Y'`
are thickenings, `f : X ⟶ Y` is affine and `i ≫ a = f ≫ b`, then `a : X' ⟶ Y'` is affine. -/
theorem isAffineHom_of_comp_eq_of_isThickeningHom {X X' Y Y' : AlgebraicSpaces B S hS}
    (i : X ⟶ X') (a : X' ⟶ Y') (f : X ⟶ Y) (b : Y ⟶ Y') (comm : i ≫ a = f ≫ b)
    (hi : IsThickeningHom B S hS i) (hf : IsAffineHom B S hS f.hom)
    (hb : IsThickeningHom B S hS b) : IsAffineHom B S hS a.hom := by
  intro Z g
  let T : BigFppfOver B S hS := (BigAffineFppf.inclusion B S hS).obj Z
  let Tsp : AlgebraicSpaces B S hS := representedAlgebraicSpace B S hS T
  let gs : Tsp ⟶ Y' := ObjectProperty.homMk g
  let Q := AlgebraicSpaces.fiberProduct B S hS a gs
  have hQ := AlgebraicSpaces.isPullback_fiberProduct B S hS a gs
  let qa : Q ⟶ X' := ObjectProperty.homMk (pullback.fst a.hom gs.hom)
  let qT : Q ⟶ Tsp := ObjectProperty.homMk (pullback.snd a.hom gs.hom)
  let P := AlgebraicSpaces.fiberProduct B S hS i qa
  have hP := AlgebraicSpaces.isPullback_fiberProduct B S hS i qa
  let pX : P ⟶ X := ObjectProperty.homMk (pullback.fst i.hom qa.hom)
  let pQ : P ⟶ Q := ObjectProperty.homMk (pullback.snd i.hom qa.hom)
  -- the base change of `i` is a thickening
  have hpQ : IsThickeningHom B S hS pQ := C1573.isThickeningHom_fst_of_isPullback B S hS hP.flip hi
  -- `P` is the base change of `i ≫ a = f ≫ b` along `g`, hence affine
  have hcomp : IsAffineHom B S hS (i ≫ a).hom := by
    rw [comm]
    exact isAffineHom_comp B S hS f.hom b.hom hf (isAffineHom_of_isThickeningHom B S hS b hb)
  obtain ⟨W, p, q, hpq⟩ := hcomp Z g
  have hPpb : IsPullback pX.hom (pQ.hom ≫ qT.hom) (i ≫ a).hom g :=
    (AlgebraicSpaces.isPullback_hom B S hS hP).paste_vert (AlgebraicSpaces.isPullback_hom B S hS hQ)
  have hPaff : IsAffineSpace B S hS P.1 :=
    (isAffineSpace_yoneda B S hS _ W.property).of_iso (hpq.isoIsPullback _ _ hPpb)
  -- a thickening of an affine algebraic space is affine
  obtain ⟨T', hT', ⟨e⟩⟩ := isAffineSpace_of_isThickeningHom B S hS pQ hpQ hPaff
  refine ⟨⟨T', hT'⟩, e.inv ≫ qa.hom, Yoneda.fullyFaithful.preimage (e.inv ≫ qT.hom), ?_⟩
  rw [Functor.FullyFaithful.map_preimage]
  exact IsPullback.of_iso (AlgebraicSpaces.isPullback_hom B S hS hQ) e (Iso.refl _) (Iso.refl _)
    (Iso.refl _) (by simp [qa]) (by simp [qT]) (by simp) (by simp [gs])

variable {B S hS}

/-- **The second leg `Y ⟶ Y'` of the pushout of Stacks 07VX is affine**: it is a thickening. -/
theorem isAffineHom_pushout_inr {X X' Y : AlgebraicSpaces B S hS} (i : X ⟶ X') (f : X ⟶ Y)
    (hi : IsThickeningHom B S hS i) (hf : IsAffineHom B S hS f.hom) [HasPushout i f] :
    IsAffineHom B S hS (pushout.inr i f).hom :=
  isAffineHom_of_isThickeningHom B S hS _ (pushout_inr_isThickeningHom B S hS i f hi hf)

/-- **The first leg `X' ⟶ Y'` of the pushout of Stacks 07VX is affine.** -/
theorem isAffineHom_pushout_inl {X X' Y : AlgebraicSpaces B S hS} (i : X ⟶ X') (f : X ⟶ Y)
    (hi : IsThickeningHom B S hS i) (hf : IsAffineHom B S hS f.hom) [HasPushout i f] :
    IsAffineHom B S hS (pushout.inl i f).hom :=
  isAffineHom_of_comp_eq_of_isThickeningHom B S hS i (pushout.inl i f) f (pushout.inr i f)
    pushout.condition hi hf (pushout_inr_isThickeningHom B S hS i f hi hf)

end AlgebraicGeometry.Space

end
