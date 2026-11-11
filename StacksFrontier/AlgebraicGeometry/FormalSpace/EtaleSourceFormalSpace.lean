module

public import StacksCore.Tactic.StacksAttribute
public import StacksFrontier.AlgebraicGeometry.FormalSpace.FibreProduct
public import StacksFrontier.AlgebraicGeometry.FormalSpace.GeneralReduction
public import StacksFrontier.AlgebraicGeometry.FormalSpace.LiftAlongAffineBase
public import StacksFrontier.AlgebraicGeometry.FormalSpace.DependentProduct.Basic
public import StacksFrontier.AlgebraicGeometry.FormalSpace.DependentProduct.BaseChange
public import StacksFrontier.AlgebraicGeometry.FormalSpace.DependentProduct.Universal

/-!
# A sheaf representable étale over a formal algebraic space is a formal algebraic space

Let `S` be a scheme contained in a big fppf site `B`, let `Y` be a formal algebraic space over
`S` and let `q : T ⟶ Y` be a morphism of fppf sheaves on the big fppf site of `S` which is
representable by algebraic spaces and étale. Then `T` is a formal algebraic space over `S`.

## Main results

* `AlgebraicGeometry.FormalSpace.isFormalAlgebraicSpace_of_isRepresentableEtale`: the
  statement above, with nothing assumed.
* `AlgebraicGeometry.FormalSpace.isFormalAlgebraicSpace_pullback_of_isRepresentableEtale`: the
  étale case of **Stacks 0AJ3**, with nothing assumed: a fibre product of a formal algebraic
  space with a representable étale morphism is a formal algebraic space.

## Implementation notes

This is the étale case of Stacks 0AJI, and it is proved here for the étale case alone because
étaleness makes it a corollary of **Stacks 0DEG** and so avoids Stacks 0AIU. The library's
Stacks 0AJI, `AlgebraicGeometry.FormalSpace.isFormalAlgebraicSpace_of_representable_over_formal`,
is stated for a morphism merely representable by algebraic spaces and carries the hypothesis
`h0AIU` — a directed colimit of algebraic spaces along thickenings is a formal algebraic space.
The corrected Stacks 0AIU,
`AlgebraicGeometry.FormalSpace.isFormalAlgebraicSpace_of_colimit_isRepresentableThickeningULift`,
proves that argument, but this file does not import it, and nothing below specialises the
general statement.

Instead `T` is identified with the dependent product `U_{V, ψ}` of Stacks 0DEG, which
`AlgebraicGeometry.FormalSpace.isFormalAlgebraicSpace_liftAlong` shows unconditionally to be a
formal algebraic space. Write `i : Y_red ⟶ Y` for the inclusion of a reduction, which Stacks
0AIN provides and which is a representable thickening, and let `V = T ×_Y Y_red` with
`ψ : V ⟶ Y_red` its projection, a base change of `q` and so again representable étale. The
dependent product `U = U_{V, ψ}` comes with its structure morphism `U ⟶ Y`, representable étale
by `AlgebraicGeometry.FormalSpace.isRepresentableEtale_liftAlongBase`, and with the comparison
`V ⟶ U` exhibiting `V` as `U ×_Y Y_red`, hence a representable thickening of `U`.

The two morphisms between `T` and `U` over `Y` are then both instances of the étale lifting
property `AlgebraicGeometry.FormalSpace.existsUnique_hom_of_isRepresentableThickening` — the
sheaf-level general-thickening case of Stacks 05ZH — applied to the two representable
thickenings `V ⟶ T` and `V ⟶ U` of the two sheaves and to the two representable étale
structure morphisms `q` and `U ⟶ Y`: each extends the identification of the common thickening
`V`. Both composites restrict to the identity of `V` and lie over `Y`, so the uniqueness half
of the same lifting property identifies them with the identities, and `T ≅ U` over `Y`.

The set-theoretic condition of Stacks 0AIS on `T` is not a hypothesis: it is carried by the
isomorphism from the one `U` has as a formal algebraic space.

## References

* [Stacks Project, Tag 0AIM](https://stacks.math.columbia.edu/tag/0AIM)
* [Stacks Project, Tag 0AIN](https://stacks.math.columbia.edu/tag/0AIN)
* [Stacks Project, Tag 0AIS](https://stacks.math.columbia.edu/tag/0AIS)
* [Stacks Project, Tag 0AIU](https://stacks.math.columbia.edu/tag/0AIU)
* [Stacks Project, Tag 0AJ3](https://stacks.math.columbia.edu/tag/0AJ3)
* [Stacks Project, Tag 0AJI](https://stacks.math.columbia.edu/tag/0AJI)
* [Stacks Project, Tag 05ZH](https://stacks.math.columbia.edu/tag/05ZH)
* [Stacks Project, Tag 0DEG](https://stacks.math.columbia.edu/tag/0DEG)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits

namespace AlgebraicGeometry.FormalSpace

open AlgebraicGeometry.FormalSpace.DependentProduct

universe u

variable (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)

/-- The base change of a representable thickening of fppf sheaves is a representable thickening. -/
private theorem isRepresentableThickeningULift_of_isPullback {P Q R Z : FppfSheaf B S hS}
    {a : P ⟶ Q} {b : P ⟶ R} {c : Q ⟶ Z} {d : R ⟶ Z} (h : IsPullback a b c d)
    (hd : Space.IsRepresentableThickeningULift.{u + 1} B S hS d.hom) :
    Space.IsRepresentableThickeningULift.{u + 1} B S hS a.hom :=
  (MorphismProperty.relative_isStableUnderBaseChange _).of_isPullback
    (h.flip.map (sheafToPresheaf (BigFppfOver.topology B S hS) (Type (u + 1)))) hd

/-- **A sheaf representable étale over a formal algebraic space is a formal algebraic space.**
Let `Y` be a formal algebraic space over `S` and let `q : T ⟶ Y` be a morphism of fppf sheaves
which is representable by algebraic spaces and étale. Then `T` is a formal algebraic space
over `S`.

This is the étale case of Stacks 0AJI, proved from **Stacks 0DEG** and so without the
hypothesis `h0AIU` that the library's general form of Stacks 0AJI carries: `T` is identified
with the dependent product of `T ×_Y Y_red ⟶ Y_red` along the inclusion of a reduction of `Y`,
the two morphisms between them and the two identities being the four lifts that the étale
lifting property of Stacks 05ZH produces from their common thickening. -/
theorem isFormalAlgebraicSpace_of_isRepresentableEtale {T Y : FppfSheaf B S hS} (q : T ⟶ Y)
    (hY : IsFormalAlgebraicSpace B S hS Y) (hq : IsRepresentableEtale B S hS q) :
    IsFormalAlgebraicSpace B S hS T := by
  obtain ⟨Yred, i, hi⟩ := exists_isReduction_of_isFormalAlgebraicSpace B S hS Y hY
  have hithick : Space.IsRepresentableThickeningULift.{u + 1} B S hS i.hom :=
    hi.isRepresentableThickening
  have hinj : ∀ A : BigFppfOver B S hS, Function.Injective (i.hom.app (Opposite.op A)) :=
    fun A ↦ (mono_iff_injective _).1 ((NatTrans.mono_iff_mono_app _).1
      (mono_of_isRepresentableThickeningULift B S hS hithick) (Opposite.op A))
  -- the base change `V = T ×_Y Y_red` of `q` along the reduction
  have hsq : IsPullback (pullback.fst q i) (pullback.snd q i) q i :=
    IsPullback.of_hasPullback q i
  have hpet : IsRepresentableEtale B S hS (pullback.snd q i) :=
    isRepresentableEtale_pullback_snd B S hS q i hq
  have hfstthick : Space.IsRepresentableThickeningULift.{u + 1} B S hS
      (pullback.fst q i).hom :=
    isRepresentableThickeningULift_of_isPullback B S hS hsq hithick
  -- the dependent product of Stacks 0DEG, a formal algebraic space
  have hU : IsFormalAlgebraicSpace B S hS (liftAlong B S hS i (pullback.snd q i)) :=
    isFormalAlgebraicSpace_liftAlong hY hithick hpet
  have hUet : IsRepresentableEtale B S hS (liftAlongBase B S hS i (pullback.snd q i)) :=
    isRepresentableEtale_liftAlongBase B S hS hithick hpet
  have hsectsq : IsPullback (liftAlongSection B S hS hinj (p := pullback.snd q i))
      (pullback.snd q i) (liftAlongBase B S hS i (pullback.snd q i)) i :=
    isPullback_liftAlongSection B S hS hinj
  have hsectthick : Space.IsRepresentableThickeningULift.{u + 1} B S hS
      (liftAlongSection B S hS hinj (p := pullback.snd q i)).hom :=
    isRepresentableThickeningULift_of_isPullback B S hS hsectsq hithick
  have hcomm : liftAlongSection B S hS hinj (p := pullback.snd q i) ≫
      liftAlongBase B S hS i (pullback.snd q i) = pullback.fst q i ≫ q := by
    rw [liftAlongSection_comp_liftAlongBase, ← hsq.w]
  -- the morphism `U ⟶ T` extending the identification of the common thickening
  obtain ⟨h, ⟨hh₁, hh₂⟩, -⟩ := existsUnique_hom_of_isRepresentableThickening hsectthick hq
    (liftAlongBase B S hS i (pullback.snd q i)) hcomm.symm
  -- and the morphism `T ⟶ U` in the other direction
  obtain ⟨k, ⟨hk₁, hk₂⟩, -⟩ := existsUnique_hom_of_isRepresentableThickening hfstthick hUet q
    hcomm
  -- the two composites are the identities, by the uniqueness of the lifts
  have hkh : k ≫ h = 𝟙 T :=
    (existsUnique_hom_of_isRepresentableThickening hfstthick hq q
        (rfl : pullback.fst q i ≫ q = pullback.fst q i ≫ q)).unique
      ⟨by rw [Category.assoc, hh₁, hk₁], by rw [← Category.assoc, hk₂, hh₂]⟩
      ⟨Category.id_comp q, Category.comp_id _⟩
  have hhk : h ≫ k = 𝟙 (liftAlong B S hS i (pullback.snd q i)) :=
    (existsUnique_hom_of_isRepresentableThickening hsectthick hUet
        (liftAlongBase B S hS i (pullback.snd q i))
        (rfl : liftAlongSection B S hS hinj (p := pullback.snd q i) ≫
            liftAlongBase B S hS i (pullback.snd q i)
          = liftAlongSection B S hS hinj (p := pullback.snd q i) ≫
            liftAlongBase B S hS i (pullback.snd q i))).unique
      ⟨by rw [Category.assoc, hk₁, hh₁], by rw [← Category.assoc, hh₂, hk₂]⟩
      ⟨Category.id_comp _, Category.comp_id _⟩
  exact isFormalAlgebraicSpace_of_iso B S hS ⟨k, h, hkh, hhk⟩ hU

/-- **The étale case of Stacks 0AJ3**, with nothing assumed. The fibre product `V ×_Y X` of a
formal algebraic space `X` over `Y` with a morphism `v : V ⟶ Y` which is representable by
algebraic spaces and étale is a formal algebraic space over `S`: the projection to `X` is a
base change of `v`, so it is again representable étale, and
`AlgebraicGeometry.FormalSpace.isFormalAlgebraicSpace_of_isRepresentableEtale` applies to it.

The library's general Stacks 0AJ3,
`AlgebraicGeometry.FormalSpace.isFormalAlgebraicSpace_pullback_of_representable`, asks only
that `v` be representable by algebraic spaces, and pays for that with the hypothesis `h0AIU`
and the set-theoretic condition of Stacks 0AIS on the fibre product. Neither is needed once `v`
is étale, so this is stated separately rather than obtained from that one. -/
theorem isFormalAlgebraicSpace_pullback_of_isRepresentableEtale {X Y V : FppfSheaf B S hS}
    (v : V ⟶ Y) (f : X ⟶ Y) (hX : IsFormalAlgebraicSpace B S hS X)
    (hv : IsRepresentableEtale B S hS v) :
    IsFormalAlgebraicSpace B S hS (pullback v f) :=
  isFormalAlgebraicSpace_of_isRepresentableEtale B S hS (pullback.snd v f) hX
    (isRepresentableEtale_pullback_snd B S hS v f hv)

end AlgebraicGeometry.FormalSpace

end
