module

public import Mathlib.Data.List.TFAE
public import StacksCore.Tactic.StacksAttribute
public import StacksFrontier.AlgebraicGeometry.Descent.EtaleLocal.EtaleLocalAtSource
public import StacksFrontier.AlgebraicGeometry.Spaces.EtaleChartCriteria
public import StacksFrontier.AlgebraicGeometry.Spaces.EtaleChartSquares
public import StacksFrontier.AlgebraicGeometry.Spaces.Morphisms.EtaleAtPoint

/-!
# The nine local criteria for étaleness of a morphism of algebraic spaces (Stacks 03XT)

Let `S` be a scheme contained in a big fppf site `B` and let `f : X ⟶ Y` be a morphism of
algebraic spaces over `S`. Étaleness of `f`, in the sense of Tag 03FR, can be read off in
nine equivalent ways: pointwise on the source, after base change to every scheme or to every
affine scheme, after base change to one surjective étale chart of the target, after
composition with one surjective étale chart of the source, in every — or in one surjective —
commuting square of étale scheme charts, or over a pair of Zariski coverings.

## Main definitions

No new definitions are introduced.

## Main results

* `AlgebraicGeometry.Space.isEtale_local_tfae`: **Stacks 03XT**, the equivalence of all nine
  conditions.
* `AlgebraicGeometry.Space.isEtale_iff_forall_isEtaleAt`: **Stacks 03XT**, condition (2).
* `AlgebraicGeometry.Space.isEtale_iff_forall_scheme_baseChange`: **Stacks 03XT**,
  condition (3).
* `AlgebraicGeometry.Space.isEtale_iff_forall_affine_baseChange`: **Stacks 03XT**,
  condition (4).
* `AlgebraicGeometry.Space.isEtale_iff_exists_zariski_coverings`: **Stacks 03XT**,
  condition (9).

## Implementation notes

Tag 03XT is the instance at `P = AlgebraicGeometry.Etale` of the nine criteria of Tag 03MM
for the chart condition of Tag 03MJ. Those criteria are already available for an arbitrary
property of morphisms of schemes, as
`AlgebraicGeometry.Space.holdsOnEveryEtaleChart_tfae` — which supplies the pointwise
criterion and the pair of Zariski coverings — and
`AlgebraicGeometry.Space.holdsOnEveryEtaleChart_tfae_of_isLocalAtTarget` — which supplies the
base-change criteria over all schemes and over all affine schemes. Étaleness of morphisms of
schemes satisfies the hypotheses of both: it is étale local on the source and target
(Tag 04R3, `AlgebraicGeometry.etale_isEtaleLocalOnSourceAndTarget`), stable under composition
(Tag 02GN) and under base change (Tag 02GO), Zariski local at the target, and trivially
implied by étaleness.

What this file adds is the translation of those criteria from the chart condition back to
étaleness of a morphism of algebraic spaces. The translation is condition (7) of this very
tag, `AlgebraicGeometry.Space.isEtale_iff_holdsOnEveryEtaleChart`, applied at each of the
morphisms occurring in the conditions; it is available at each of them because the open
subspaces and the fibre products involved are again algebraic spaces over `S`. Conditions (7)
and (8) need no translation at all: the generic criteria already state them with the scheme
morphism between the two charts, which is the form Tag 03XT uses.

The implication from condition (2) to condition (1) is also available on its own as
`AlgebraicGeometry.Space.isEtale_of_forall_isEtaleAt`, proved there directly from the étale
source-locality of étaleness (Tag 06F4) over the covering of the source by the chosen
neighbourhoods; it is kept because it is what
`StacksFrontier.AlgebraicGeometry.FormalSpace.CompletionFactorization` consumes.

Conditions (5), (6) and (8) are also conditions (3), (2) and (4) of Tag 03FS, and carry that
tag's selectors on `AlgebraicGeometry.Space.isEtale_iff_exists_target_chart`,
`AlgebraicGeometry.Space.isEtale_iff_exists_source_chart` and
`AlgebraicGeometry.Space.isEtale_iff_exists_etale_chart_square`; they are not restated here,
only spelled with `AlgebraicGeometry.Space.IsSurjective` and
`AlgebraicGeometry.Space.IsEtale` for the charts rather than with the relative properties, as
the generic criteria do.

## References

* [Stacks Project, Tag 03FR](https://stacks.math.columbia.edu/tag/03FR)
* [Stacks Project, Tag 03FS](https://stacks.math.columbia.edu/tag/03FS)
* [Stacks Project, Tag 03MJ](https://stacks.math.columbia.edu/tag/03MJ)
* [Stacks Project, Tag 03MM](https://stacks.math.columbia.edu/tag/03MM)
* [Stacks Project, Tag 03XT](https://stacks.math.columbia.edu/tag/03XT)
* [Stacks Project, Tag 04RH](https://stacks.math.columbia.edu/tag/04RH)
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits

universe u

namespace AlgebraicGeometry.Space

variable (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)
variable {X Y : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u}

/-- Étaleness of a base change of `f : X ⟶ Y` to a representable presheaf agrees with the
chart condition of Tag 03MJ at étaleness of morphisms of schemes: the fibre product of two
algebraic spaces over an algebraic space is an algebraic space, so condition (7) of Tag 03XT
applies to the projection. -/
private theorem isEtale_pullback_snd_iff_chart
    (hX : IsAlgebraicSpace B S hS X) (hY : IsAlgebraicSpace B S hS Y) (f : X ⟶ Y)
    (Z : BigFppfOver B S hS) (g : yoneda.obj Z ⟶ Y) :
    IsEtale B S hS (pullback.snd f g) ↔
      HoldsOnEveryEtaleChart B S hS
        (@AlgebraicGeometry.Etale.{u} : MorphismProperty Scheme.{u}) (pullback.snd f g) :=
  isEtale_iff_holdsOnEveryEtaleChart B S hS
    (isAlgebraicSpace_pullback B S hS f g hX (isAlgebraicSpace_yoneda B S hS Z) hY)
    (isAlgebraicSpace_yoneda B S hS Z) _

/-- **Stacks 03XT.** Nine equivalent criteria for a morphism `f : X ⟶ Y` of algebraic spaces
over `S` to be étale: `f` is étale; `f` is étale at every point of `|X|`; the base change of
`f` to every scheme is étale; the base change of `f` to every affine scheme is étale; the base
change of `f` to one surjective étale scheme chart of `Y` is étale; the composite of `f` with
one surjective étale scheme chart of `X` is étale; in every commuting square of étale scheme
charts of `f` the morphism of schemes between the charts is étale; there is one such square
with surjective chart of the source; and there are Zariski coverings `Y = ⋃ Yᵢ` and
`f⁻¹(Yᵢ) = ⋃ Xᵢⱼ` with every `Xᵢⱼ ⟶ Yᵢ` étale. -/
@[stacks 03XT]
theorem isEtale_local_tfae
    (hX : IsAlgebraicSpace B S hS X) (hY : IsAlgebraicSpace B S hS Y) (f : X ⟶ Y) :
    List.TFAE [
      IsEtale B S hS f,
      ∀ x : points B S hS X, IsEtaleAt B S hS f x,
      ∀ (Z : BigFppfOver B S hS) (g : yoneda.obj Z ⟶ Y),
        IsEtale B S hS (pullback.snd f g),
      ∀ (Z : BigFppfOver B S hS) (g : yoneda.obj Z ⟶ Y),
        IsAffine ((BigFppfOver.toScheme B S hS).obj Z) →
          IsEtale B S hS (pullback.snd f g),
      ∃ (V : BigFppfOver B S hS) (g : yoneda.obj V ⟶ Y),
        IsSurjective B S hS g ∧ IsEtale B S hS g ∧ IsEtale B S hS (pullback.snd f g),
      ∃ (U : BigFppfOver B S hS) (p : yoneda.obj U ⟶ X),
        IsSurjective B S hS p ∧ IsEtale B S hS p ∧ IsEtale B S hS (p ≫ f),
      ∀ (U V : BigFppfOver B S hS) (p : yoneda.obj U ⟶ X) (q : yoneda.obj V ⟶ Y) (a : U ⟶ V),
        IsEtale B S hS p → IsEtale B S hS q → p ≫ f = yoneda.map a ≫ q →
          AlgebraicGeometry.Etale ((BigFppfOver.toScheme B S hS).map a),
      ∃ (U V : BigFppfOver B S hS) (p : yoneda.obj U ⟶ X) (q : yoneda.obj V ⟶ Y) (a : U ⟶ V),
        IsEtale B S hS p ∧ IsEtale B S hS q ∧ IsSurjective B S hS p ∧
          p ≫ f = yoneda.map a ≫ q ∧
            AlgebraicGeometry.Etale ((BigFppfOver.toScheme B S hS).map a),
      ∃ (I : Type u) (Yopen : I → Subfunctor Y) (J : I → Type u)
        (Xopen : ∀ i, J i → Subfunctor (pullback f (Yopen i).ι)),
        IsZariskiCover B S hS I Yopen ∧ (∀ i, IsZariskiCover B S hS (J i) (Xopen i)) ∧
          ∀ i j, IsEtale B S hS ((Xopen i j).ι ≫ pullback.snd f (Yopen i).ι)
    ] := by
  have hPcomp : MorphismProperty.IsStableUnderComposition
      (@AlgebraicGeometry.Etale.{u} : MorphismProperty Scheme.{u}) :=
    MorphismProperty.IsMultiplicative.toIsStableUnderComposition
  have : MorphismProperty.IsLocalAtTarget
      (@AlgebraicGeometry.Etale.{u} : MorphismProperty Scheme.{u})
      Scheme.zariskiPrecoverage :=
    MorphismProperty.IsLocalAtTarget.of_le Scheme.zariskiPrecoverage_le_fpqcPrecoverage
  have H8 := holdsOnEveryEtaleChart_tfae_of_isLocalAtTarget B S hS
    (@AlgebraicGeometry.Etale.{u} : MorphismProperty Scheme.{u})
    AlgebraicGeometry.etale_isEtaleLocalOnSourceAndTarget hX hY f
  have H9 := holdsOnEveryEtaleChart_tfae B S hS
    (@AlgebraicGeometry.Etale.{u} : MorphismProperty Scheme.{u})
    AlgebraicGeometry.etale_isEtaleLocalOnSourceAndTarget hPcomp
    AlgebraicGeometry.Etale.etale_isStableUnderBaseChange (fun _ hg => hg) hX hY f
  have e1 := isEtale_iff_holdsOnEveryEtaleChart B S hS hX hY f
  have ebc := isEtale_pullback_snd_iff_chart B S hS hX hY f
  tfae_have 1 ↔ 2 :=
    e1.trans ((H9.out 1 2).trans (forall_congr' fun _ => exists_congr fun U =>
      and_congr_right fun hU => exists_congr fun y => and_congr_right fun _ =>
        (isEtale_iff_holdsOnEveryEtaleChart B S hS hU.1 hY _).symm))
  tfae_have 1 ↔ 3 :=
    e1.trans ((H8.out 1 2).trans
      (forall_congr' fun Z => forall_congr' fun g => (ebc Z g).symm))
  tfae_have 1 ↔ 4 :=
    e1.trans ((H8.out 1 3).trans
      (forall_congr' fun Z => forall_congr' fun g => imp_congr_right fun _ => (ebc Z g).symm))
  tfae_have 1 ↔ 5 :=
    e1.trans ((H8.out 1 4).trans (exists_congr fun V => exists_congr fun g =>
      and_congr_right fun _ => and_congr_right fun _ => (ebc V g).symm))
  tfae_have 1 ↔ 6 :=
    e1.trans ((H8.out 1 5).trans (exists_congr fun U => exists_congr fun p =>
      and_congr_right fun _ => and_congr_right fun _ =>
        (isEtale_iff_holdsOnEveryEtaleChart B S hS
          (isAlgebraicSpace_yoneda B S hS U) hY (p ≫ f)).symm))
  tfae_have 1 ↔ 7 := e1.trans (H8.out 1 6)
  tfae_have 1 ↔ 8 := e1.trans (H8.out 1 7)
  tfae_have 1 ↔ 9 :=
    e1.trans ((H8.out 1 8).trans (exists_congr fun I => exists_congr fun Yopen =>
      exists_congr fun J => exists_congr fun Xopen => and_congr_right fun hYcov =>
        and_congr_right fun hXcov => forall_congr' fun i => forall_congr' fun j =>
          (isEtale_iff_holdsOnEveryEtaleChart B S hS ((hXcov i).1 j).1 (hYcov.1 i).1 _).symm))
  tfae_finish

/-- **Stacks 03XT, condition (2).** A morphism of algebraic spaces over `S` is étale if and
only if it is étale, in the sense of Tag 04RH, at every point of its source. -/
theorem isEtale_iff_forall_isEtaleAt
    (hX : IsAlgebraicSpace B S hS X) (hY : IsAlgebraicSpace B S hS Y) (f : X ⟶ Y) :
    IsEtale B S hS f ↔ ∀ x : points B S hS X, IsEtaleAt B S hS f x :=
  (isEtale_local_tfae B S hS hX hY f).out 1 2

/-- **Stacks 03XT, condition (3).** A morphism of algebraic spaces over `S` is étale if and
only if for every object `Z` of the big fppf site of `S` and every morphism
`yoneda.obj Z ⟶ Y` the base change `Z ×_Y X ⟶ Z` is étale. -/
theorem isEtale_iff_forall_scheme_baseChange
    (hX : IsAlgebraicSpace B S hS X) (hY : IsAlgebraicSpace B S hS Y) (f : X ⟶ Y) :
    IsEtale B S hS f ↔
      ∀ (Z : BigFppfOver B S hS) (g : yoneda.obj Z ⟶ Y),
        IsEtale B S hS (pullback.snd f g) :=
  (isEtale_local_tfae B S hS hX hY f).out 1 3

/-- **Stacks 03XT, condition (4).** A morphism of algebraic spaces over `S` is étale if and
only if for every object `Z` of the big fppf site of `S` with affine underlying scheme and
every morphism `yoneda.obj Z ⟶ Y` the base change `Z ×_Y X ⟶ Z` is étale. -/
theorem isEtale_iff_forall_affine_baseChange
    (hX : IsAlgebraicSpace B S hS X) (hY : IsAlgebraicSpace B S hS Y) (f : X ⟶ Y) :
    IsEtale B S hS f ↔
      ∀ (Z : BigFppfOver B S hS) (g : yoneda.obj Z ⟶ Y),
        IsAffine ((BigFppfOver.toScheme B S hS).obj Z) →
          IsEtale B S hS (pullback.snd f g) :=
  (isEtale_local_tfae B S hS hX hY f).out 1 4

/-- **Stacks 03XT, condition (9).** A morphism `f : X ⟶ Y` of algebraic spaces over `S` is
étale if and only if there are Zariski coverings `Y = ⋃ Yᵢ` by open subspaces and, for each
`i`, a Zariski covering `f⁻¹(Yᵢ) = ⋃ Xᵢⱼ` by open subspaces, such that every induced morphism
`Xᵢⱼ ⟶ Yᵢ` is étale. -/
theorem isEtale_iff_exists_zariski_coverings
    (hX : IsAlgebraicSpace B S hS X) (hY : IsAlgebraicSpace B S hS Y) (f : X ⟶ Y) :
    IsEtale B S hS f ↔
      ∃ (I : Type u) (Yopen : I → Subfunctor Y) (J : I → Type u)
        (Xopen : ∀ i, J i → Subfunctor (pullback f (Yopen i).ι)),
        IsZariskiCover B S hS I Yopen ∧ (∀ i, IsZariskiCover B S hS (J i) (Xopen i)) ∧
          ∀ i j, IsEtale B S hS ((Xopen i j).ι ≫ pullback.snd f (Yopen i).ι) :=
  (isEtale_local_tfae B S hS hX hY f).out 1 9

end AlgebraicGeometry.Space

end
