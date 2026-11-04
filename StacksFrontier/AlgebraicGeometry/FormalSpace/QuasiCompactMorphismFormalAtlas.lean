module

public import StacksCore.Tactic.StacksAttribute
public import StacksFrontier.AlgebraicGeometry.FormalSpace.ColimitOfAlgebraicSpaces
public import StacksFrontier.AlgebraicGeometry.FormalSpace.EtaleSourceFormalSpace
public import StacksFrontier.AlgebraicGeometry.FormalSpace.QuasiCompactMorphismReductions
public import StacksFrontier.AlgebraicGeometry.FormalSpace.QuasiCompactSpaceCriteria
public import StacksFrontier.AlgebraicGeometry.FormalSpace.ReductionSiteChart
public import StacksFrontier.AlgebraicGeometry.FormalSpace.QuasiCompactSpaceCriteriaReduction
public import StacksFrontier.AlgebraicGeometry.FormalSpace.QuasiCompactSpaceCriteriaSupplement
import all StacksFrontier.AlgebraicGeometry.FormalSpace.SpacesEtaleIdentification
public import StacksFrontier.AlgebraicGeometry.FormalSpace.FormalAlgebraicSpaceSanityChecks

/-!
# Condition (4) of Stacks 0AJB, the covering form

Let `S` be a scheme contained in a big fppf site `B` and let `f : X ⟶ Y` be a morphism of
formal algebraic spaces over `S`. **Stacks 0AJB** lists four equivalent conditions on `f`, of
which condition (4) is that there be *some* covering `{Yⱼ ⟶ Y}` as in Definition 0AIM all of
whose fibre products `X ×_Y Yⱼ` are quasi-compact formal algebraic spaces. This file relates
condition (4) to the other three: it proves the implications into condition (4), from condition
(1) and hence from conditions (2) and (3), and it reduces the implications *out of* condition
(4) to one statement about morphisms of algebraic spaces which this library does not have.

Condition (4) asks for a covering of `Y` as in Definition 0AIM, so it has content only when `Y`
has one. The source's hypothesis is exactly that: Stacks 0AJB is stated for a morphism of
*formal algebraic spaces* over `S`, so `Y` carries such a covering by Definition 0AIM, and the
covering produced below is the atlas that the hypothesis `IsFormalAlgebraicSpace B S hS Y`
supplies. The conditions themselves are stated in
`StacksFrontier.AlgebraicGeometry.FormalSpace.QuasiCompactMorphism` for an arbitrary morphism of
fppf sheaves, since none of them uses those witnesses; the statements here are the first among
the conditions of Stacks 0AJB that do use them, and they use no more than the source assumes.

Everything rests on one computation, which is
`AlgebraicGeometry.FormalSpace.exists_isReduction_pullback_iso_of_isRepresentableEtale`. A
member `v : V ⟶ Y` of a covering as in Definition 0AIM is representable by algebraic spaces and
étale, so for a fibre product `W` of `f` with `v`, with projections `p : W ⟶ V` and
`q : W ⟶ X`:

* `q` is a base change of `v`, hence again representable étale, so `W` is a formal algebraic
  space over `S` by the étale case of Stacks 0AJ3,
  `AlgebraicGeometry.FormalSpace.isFormalAlgebraicSpace_of_isRepresentableEtale`, which carries
  no hypothesis;
* `W ×_X X_red` is a reduction of `W` by **Stacks 0GB7**, applied to that same projection `q`,
  an étale morphism being smooth; and `V ×_Y Y_red` is a reduction of `V` by Stacks 0GB7 applied
  to `v`. So both reductions are *computed*, and Stacks 0CB9 is not needed;
* pasting the cartesian square of `W ×_X X_red` with the given one presents `W ×_X X_red` as a
  fibre product of `v` with `X_red ⟶ Y`, and pasting the cartesian square of
  `V_red ×_{Y_red} X_red` with that of `V ×_Y Y_red` presents the latter as a fibre product of
  `v` with the same morphism, the morphism of reductions being compatible with `f`. Hence

    `W_red = V ×_Y X_red = V_red ×_{Y_red} X_red`.

Read left to right this gives the implications into condition (4): condition (1) makes
`V_red ×_{Y_red} X_red` a quasi-compact algebraic space whenever `V_red` is one, and Stacks
0AJ9 — the implication (1) ⇒ (3), through
`AlgebraicGeometry.FormalSpace.hasFiniteFormalAtlas_of_isQuasiCompactSpaceULift_of_isReduction`
and `AlgebraicGeometry.FormalSpace.HasFiniteFormalAtlas.isQuasiCompactSpace` — turns that into
quasi-compactness of `W`. Read right to left it gives what condition (4) yields: an affine étale
covering of `Y_red`, each member represented by a reduced affine object of the site, over which
the base change of the morphism of reductions has quasi-compact source.

## Main results

* `AlgebraicGeometry.FormalSpace.isQuasiCompactSpace_of_isAffineFormalAlgebraicSpace`: an affine
  formal algebraic space over `S` is a quasi-compact formal algebraic space over `S`.
* `AlgebraicGeometry.FormalSpace.exists_isReduction_pullback_iso_of_isRepresentableEtale`: the
  computation above — the reductions of `W` and of `V` as fibre products, and the identification
  `W_red = V_red ×_{Y_red} X_red`.
* `FormalSpace.IsQuasiCompactOnReductions.isQuasiCompactSpace_of_isRepresentableEtale`:
  a fibre product of a morphism satisfying condition (1) of Stacks 0AJB with a morphism which is
  representable by algebraic spaces and étale and whose source is a quasi-compact formal
  algebraic space is a quasi-compact formal algebraic space.
* `AlgebraicGeometry.FormalSpace.IsQuasiCompactOnReductions.hasQuasiCompactFormalAtlas`:
  **Stacks 0AJB**, the implication (1) ⇒ (4).
* `AlgebraicGeometry.FormalSpace.IsQuasiCompact.hasQuasiCompactFormalAtlas`: **Stacks 0AJB**,
  the implication (3) ⇒ (4).
* `AlgebraicGeometry.FormalSpace.IsQuasiCompactOnSchemeBaseChanges.hasQuasiCompactFormalAtlas`:
  **Stacks 0AJB**, the implication (2) ⇒ (4).
* `AlgebraicGeometry.FormalSpace.HasQuasiCompactFormalAtlas.exists_affine_etale_cover_reduction`:
  what condition (4) gives at the reductions.

## What is assumed

Nothing beyond the source's own hypothesis that `X` and `Y` be formal algebraic spaces over `S`.
In particular Stacks 0AIU is not assumed, the general Stacks 0AJ3 is not used, and Stacks 0CB9 is
not used.

The implications not proved here are proved, with the four conditions assembled into one
`List.TFAE`, in `StacksFrontier.AlgebraicGeometry.FormalSpace.QuasiCompactMorphismTFAE`: condition
(4) implies condition (3) by refining the covering, along a point `T ⟶ Y` with `T` affine, to
finitely many *affine* objects of the site étale over `T` (Stacks 0AIG makes the base changes of
the members objects of the site), over each of which the fibre product has a single affine formal
chart by Stacks 0AN3 clause (1). No form of Stacks 0AJ3 or Stacks 0AIU is used: the fibre product
`X ×_Y T` is shown to be a formal algebraic space by exhibiting that chart, not by a colimit
argument. With (1) ⇒ (4) this gives (1) ⇒ (3), and (3) ⇒ (1) closes the cycle.

## Implementation notes

The per-chart statements are proved for an arbitrary cartesian square rather than for the chosen
`CategoryTheory.Limits.pullback`, as conditions (2), (3) and (4) are stated, so that they apply
to whatever fibre product condition (4) is tested at. The hypothesis on the source of the chart
in the implication into condition (4) is quasi-compactness as a formal algebraic space rather
than affineness, which is what the argument uses and is strictly more general; Definition 0AIM
supplies the affine case through
`AlgebraicGeometry.FormalSpace.isQuasiCompactSpace_of_isAffineFormalAlgebraicSpace`.

The reductions appearing in the shared computation are the chosen pullbacks `pullback q iX` and
`pullback v iY`, since that is the shape in which Stacks 0GB7 identifies them and no choice of
reduction is thereby made: any reduction is canonically isomorphic to these by
`AlgebraicGeometry.FormalSpace.IsReduction.isIso_of_comp_eq`. The fibre product
`V_red ×_{Y_red} X_red` is likewise the chosen pullback of sheaves, because condition (1) is
quasi-compactness of the morphism of reductions in the sense of Stacks 03HE, whose conclusion is
about the chosen pullback of *presheaves*; the two are identified along the inclusion of sheaves
into presheaves, which preserves limits.

## References

* [Stacks Project, Tag 0AIM](https://stacks.math.columbia.edu/tag/0AIM)
* [Stacks Project, Tag 0AIP](https://stacks.math.columbia.edu/tag/0AIP)
* [Stacks Project, Tag 0AIS](https://stacks.math.columbia.edu/tag/0AIS)
* [Stacks Project, Tag 0AIU](https://stacks.math.columbia.edu/tag/0AIU)
* [Stacks Project, Tag 0AJ3](https://stacks.math.columbia.edu/tag/0AJ3)
* [Stacks Project, Tag 0AJ9](https://stacks.math.columbia.edu/tag/0AJ9)
* [Stacks Project, Tag 0AJB](https://stacks.math.columbia.edu/tag/0AJB)
* [Stacks Project, Tag 0AJC](https://stacks.math.columbia.edu/tag/0AJC)
* [Stacks Project, Tag 03HE](https://stacks.math.columbia.edu/tag/03HE)
* [Stacks Project, Tag 0GB7](https://stacks.math.columbia.edu/tag/0GB7)
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits

namespace AlgebraicGeometry.FormalSpace

universe u

variable (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)

/-! ### Affine formal algebraic spaces are quasi-compact -/

/-! ### The reduction of a fibre product along a chart of the target -/

/-- **The reduction of a fibre product along a representable étale chart of the target.** Let
`f : X ⟶ Y` be a morphism of formal algebraic spaces over `S`, let `iX : Xred ⟶ X` and
`iY : Yred ⟶ Y` be reductions and let `fred : Xred ⟶ Yred` be compatible with `f`. Let
`v : V ⟶ Y` be representable by algebraic spaces and étale with `V` a formal algebraic space
over `S`, and let `W` with projections `p : W ⟶ V` and `q : W ⟶ X` be a fibre product `V ×_Y X`.
Then `W` is a formal algebraic space over `S`, `W ×_X Xred` is a reduction of `W`,
`V ×_Y Yred` is a reduction of `V`, and

  `W ×_X Xred ≅ (V ×_Y Yred) ×_{Yred} Xred`,

which is the identity `W_red = V_red ×_{Y_red} X_red`. The identification is delivered as the
morphism `W_red ⟶ V_red` compatible with `p`, together with the cartesian square exhibiting it
as the base change of `fred`; that is what makes a property of `fred` stable under base change
pass to the morphism of reductions, and the isomorphism displayed above is its `isoPullback`.

The projection `q` is a base change of `v`, hence again representable étale, so `W` is a formal
algebraic space by the étale case of Stacks 0AJ3 and both reductions are given by Stacks 0GB7,
an étale morphism being smooth. The identification is two applications of pasting of cartesian
squares: `W ×_X Xred` and `(V ×_Y Yred) ×_{Yred} Xred` are both fibre products of `v` with the
composite `Xred ⟶ X ⟶ Y`, which is also `Xred ⟶ Yred ⟶ Y`. -/
theorem exists_isReduction_pullback_iso_of_isRepresentableEtale
    {X Y V W Xred Yred : FppfSheaf B S hS} {f : X ⟶ Y} {v : V ⟶ Y} {p : W ⟶ V} {q : W ⟶ X}
    {iX : Xred ⟶ X} {iY : Yred ⟶ Y} {fred : Xred ⟶ Yred}
    (hX : IsFormalAlgebraicSpace B S hS X) (hY : IsFormalAlgebraicSpace B S hS Y)
    (hV : IsFormalAlgebraicSpace B S hS V) (hiX : IsReduction B S hS X Xred iX)
    (hiY : IsReduction B S hS Y Yred iY) (hfred : fred ≫ iY = iX ≫ f)
    (hv : IsRepresentableEtale B S hS v) (hsq : IsPullback p q v f) :
    IsFormalAlgebraicSpace B S hS W ∧
      IsReduction B S hS W (pullback q iX) (pullback.fst q iX) ∧
      IsReduction B S hS V (pullback v iY) (pullback.fst v iY) ∧
      ∃ pred : pullback q iX ⟶ pullback v iY,
        pred ≫ pullback.fst v iY = pullback.fst q iX ≫ p ∧
          IsPullback pred (pullback.snd q iX) (pullback.snd v iY) fred := by
  -- the projection to `X` is a base change of `v`, hence representable étale
  have hq : IsRepresentableEtale B S hS q := by
    rw [← hsq.isoPullback_hom_snd]
    exact IsRepresentableEtale.comp B S hS
      (isRepresentableEtale_of_isIso B S hS hsq.isoPullback.hom)
      (isRepresentableEtale_pullback_snd B S hS v f hv)
  -- so `W` is a formal algebraic space, by the étale case of Stacks 0AJ3
  have hW : IsFormalAlgebraicSpace B S hS W :=
    isFormalAlgebraicSpace_of_isRepresentableEtale B S hS q hX hq
  -- the two reductions, by Stacks 0GB7
  have sqV : IsPullback (pullback.fst v iY) (pullback.snd v iY) v iY :=
    IsPullback.of_hasPullback v iY
  have hiV : IsReduction B S hS V (pullback v iY) (pullback.fst v iY) :=
    isReduction_pullback_reduction_of_smooth B S hS hV hY hv.1
      (hasPropertyULift_smooth_of_isRepresentableEtale B S hS hv) hiY sqV
  have sqW : IsPullback (pullback.fst q iX) (pullback.snd q iX) q iX :=
    IsPullback.of_hasPullback q iX
  have hiW : IsReduction B S hS W (pullback q iX) (pullback.fst q iX) :=
    isReduction_pullback_reduction_of_smooth B S hS hW hX hq.1
      (hasPropertyULift_smooth_of_isRepresentableEtale B S hS hq) hiX sqW
  -- the morphism of reductions over `p`, and the square exhibiting it over `fred`
  have hWpaste : IsPullback (pullback.fst q iX ≫ p) (pullback.snd q iX) v (iX ≫ f) :=
    sqW.paste_horiz hsq
  have hcomm : (pullback.fst q iX ≫ p) ≫ v = (pullback.snd q iX ≫ fred) ≫ iY := by
    rw [hWpaste.w, Category.assoc, hfred]
  refine ⟨hW, hiW, hiV,
    pullback.lift (pullback.fst q iX ≫ p) (pullback.snd q iX ≫ fred) hcomm,
    pullback.lift_fst _ _ _, ?_⟩
  refine IsPullback.of_right ?_ (pullback.lift_snd _ _ _) sqV
  rw [pullback.lift_fst, hfred]
  exact hWpaste

/-! ### Quasi-compactness of a fibre product along a chart of the target -/

/-- Let `f : X ⟶ Y` be a morphism of formal algebraic spaces over `S` satisfying condition (1)
of **Stacks 0AJB**: every morphism between reductions of `X` and of `Y` compatible with `f` is a
quasi-compact morphism of algebraic spaces. Let `v : V ⟶ Y` be representable by algebraic spaces
and étale with `V` a quasi-compact formal algebraic space over `S`, and let `W` with projections
`p : W ⟶ V` and `q : W ⟶ X` be a fibre product `V ×_Y X`. Then `W` is a quasi-compact formal
algebraic space over `S`.

The reduction of `W` is `V_red ×_{Y_red} X_red` by
`AlgebraicGeometry.FormalSpace.exists_isReduction_pullback_iso_of_isRepresentableEtale`, and that
is a quasi-compact algebraic space by condition (1), `V_red` being one because `V` is a
quasi-compact formal algebraic space. Stacks 0AJ9, the implication (1) ⇒ (3), concludes. -/
theorem IsQuasiCompactOnReductions.isQuasiCompactSpace_of_isRepresentableEtale
    {X Y V W : FppfSheaf B S hS} {f : X ⟶ Y} {v : V ⟶ Y} {p : W ⟶ V} {q : W ⟶ X}
    (h : IsQuasiCompactOnReductions B S hS f) (hX : IsFormalAlgebraicSpace B S hS X)
    (hY : IsFormalAlgebraicSpace B S hS Y) (hV : IsQuasiCompactSpace B S hS V)
    (hv : IsRepresentableEtale B S hS v) (hsq : IsPullback p q v f) :
    IsQuasiCompactSpace B S hS W := by
  -- reductions of `X` and of `Y`, and the morphism between them that `f` induces
  obtain ⟨Xred, iX, hiX⟩ := exists_isReduction_of_isFormalAlgebraicSpace B S hS X hX
  obtain ⟨Yred, iY, hiY⟩ := exists_isReduction_of_isFormalAlgebraicSpace B S hS Y hY
  obtain ⟨fred, hfred, -⟩ := hiY.universal Xred hiX.algebraic hiX.reduced (iX ≫ f)
  obtain ⟨hW, hiW, hiV, pred, -, hpredsq⟩ :=
    exists_isReduction_pullback_iso_of_isRepresentableEtale B S hS
      hX hY (IsQuasiCompactSpace.isFormalAlgebraicSpace B S hS hV) hiX hiY hfred hv hsq
  -- condition (1), read at those reductions, against the quasi-compact reduction of `V`
  have hQqc : Space.IsQuasiCompactSpaceULift.{u + 1} B S hS
      (pullback (pullback.snd v iY) fred).obj :=
    Space.isQuasiCompactSpaceULift_of_iso B S hS
      (((IsPullback.of_hasPullback (pullback.snd v iY) fred).map
        (sheafToPresheaf (BigFppfOver.topology B S hS) (Type (u + 1)))).isoPullback).symm
      (h Xred Yred iX iY hiX hiY fred hfred (pullback v iY).obj hiV.algebraic
        (IsQuasiCompactSpace.isQuasiCompactSpaceULift_of_isReduction B S hS hiV hV)
        (pullback.snd v iY).hom)
  -- so the reduction of `W` is a quasi-compact algebraic space, and Stacks 0AJ9 concludes
  exact HasFiniteFormalAtlas.isQuasiCompactSpace' B S hS
    (hasFiniteFormalAtlas_of_isQuasiCompactSpaceULift_of_isReduction B S hS hW hiW
      (Space.isQuasiCompactSpaceULift_of_iso B S hS
        ((sheafToPresheaf (BigFppfOver.topology B S hS) (Type (u + 1))).mapIso
          hpredsq.isoPullback.symm) hQqc))

/-! ### The implication (1) implies (4) -/

/-- **Stacks 0AJB, condition (1) implies condition (4).** Let `f : X ⟶ Y` be a morphism of
formal algebraic spaces over `S` such that every morphism between reductions of `X` and of `Y`
compatible with `f` is a quasi-compact morphism of algebraic spaces. Then there is a covering
`{Yⱼ ⟶ Y}` as in Definition 0AIM all of whose fibre products with `f` are quasi-compact formal
algebraic spaces over `S`.

The covering is the atlas of `Y` that the hypothesis `IsFormalAlgebraicSpace B S hS Y` supplies,
which is the covering Definition 0AIM provides and the one the source's hypothesis on `Y` names.
Its members are affine formal algebraic spaces, hence quasi-compact formal algebraic spaces, and
representable by algebraic spaces and étale, so
`IsQuasiCompactOnReductions.isQuasiCompactSpace_of_isRepresentableEtale` applies to each fibre
product. -/
@[stacks 0AJB "condition (1) implies condition (4), with the reductions quantified over in \
place of Stacks 0AIN and with the source's own hypothesis that X and Y be formal algebraic \
spaces, which is what supplies the covering of Y that condition (4) asks for"]
theorem IsQuasiCompactOnReductions.hasQuasiCompactFormalAtlas {X Y : FppfSheaf B S hS}
    {f : X ⟶ Y} (h : IsQuasiCompactOnReductions B S hS f)
    (hX : IsFormalAlgebraicSpace B S hS X) (hY : IsFormalAlgebraicSpace B S hS Y) :
    HasQuasiCompactFormalAtlas B S hS f := by
  let : HasColimitsOfSize.{u + 1, u + 1} (FppfSheaf B S hS) := Sheaf.instHasColimitsOfSize
  obtain ⟨I, Yi, c, haffine, hetale, hsurjective⟩ := hY.2
  exact ⟨I, Yi, c, haffine, hetale, hsurjective, fun i _ _ _ sq ↦
    IsQuasiCompactOnReductions.isQuasiCompactSpace_of_isRepresentableEtale B S hS h hX hY
      (isQuasiCompactSpace_of_isAffineFormalAlgebraicSpace B S hS (haffine i)) (hetale i) sq⟩

/-! ### The implications (3) implies (4) and (2) implies (4) -/

/-- **Stacks 0AJB, condition (3) implies condition (4).** A morphism of formal algebraic spaces
over `S` which is quasi-compact in the sense of Stacks 0AJC — every fibre product of it with an
affine scheme over `S` in the site mapping to its target is a quasi-compact formal algebraic
space — admits a covering of its target as in Definition 0AIM all of whose fibre products with
it are quasi-compact formal algebraic spaces.

Condition (3) implies condition (1) by
`AlgebraicGeometry.FormalSpace.IsQuasiCompact.isQuasiCompactOnReductions`, and condition (1)
implies condition (4). -/
@[stacks 0AJB "condition (3) implies condition (4), with the source's own hypothesis that X and \
Y be formal algebraic spaces"]
theorem IsQuasiCompact.hasQuasiCompactFormalAtlas {X Y : FppfSheaf B S hS} {f : X ⟶ Y}
    (h : IsQuasiCompact B S hS f) (hX : IsFormalAlgebraicSpace B S hS X)
    (hY : IsFormalAlgebraicSpace B S hS Y) : HasQuasiCompactFormalAtlas B S hS f :=
  IsQuasiCompactOnReductions.hasQuasiCompactFormalAtlas B S hS
    (IsQuasiCompact.isQuasiCompactOnReductions B S hS h) hX hY

/-- **Stacks 0AJB, condition (2) implies condition (4).** A morphism of formal algebraic spaces
over `S` every one of whose fibre products with a quasi-compact scheme over `S` in the site
mapping to its target is a quasi-compact formal algebraic space admits a covering of its target
as in Definition 0AIM all of whose fibre products with it are quasi-compact formal algebraic
spaces: condition (2) restricts to the affine schemes, which is condition (3). -/
@[stacks 0AJB "condition (2) implies condition (4), with the source's own hypothesis that X and \
Y be formal algebraic spaces"]
theorem IsQuasiCompactOnSchemeBaseChanges.hasQuasiCompactFormalAtlas {X Y : FppfSheaf B S hS}
    {f : X ⟶ Y} (h : IsQuasiCompactOnSchemeBaseChanges B S hS f)
    (hX : IsFormalAlgebraicSpace B S hS X) (hY : IsFormalAlgebraicSpace B S hS Y) :
    HasQuasiCompactFormalAtlas B S hS f :=
  IsQuasiCompact.hasQuasiCompactFormalAtlas B S hS
    (IsQuasiCompactOnSchemeBaseChanges.isQuasiCompact B S hS h) hX hY

/-! ### What condition (4) gives at the reductions -/

/-- **Condition (4) of Stacks 0AJB, carried to the reductions.** Let `f : X ⟶ Y` be a morphism
of formal algebraic spaces over `S` admitting a covering `{Yⱼ ⟶ Y}` as in Definition 0AIM all of
whose fibre products with `f` are quasi-compact formal algebraic spaces, let `iX : Xred ⟶ X` and
`iY : Yred ⟶ Y` be reductions and let `fred : Xred ⟶ Yred` be compatible with `f`. Then there is
a family `{Vᵢ ⟶ Yred}` of morphisms representable by algebraic spaces and étale, jointly
surjective as a map of sheaves, each `Vᵢ` isomorphic to the sheaf of a *reduced affine* object of
the site, such that every fibre product `Vᵢ ×_{Yred} Xred` is a quasi-compact algebraic space.

Each member `Yⱼ ⟶ Y` is representable étale, so the reduction of the fibre product `Yⱼ ×_Y X` is
`(Yⱼ)_red ×_{Yred} Xred` by
`AlgebraicGeometry.FormalSpace.exists_isReduction_pullback_iso_of_isRepresentableEtale`; the
fibre product is a quasi-compact formal algebraic space by hypothesis, so its reduction is a
quasi-compact algebraic space by Stacks 0AJ9, the implication (3) ⇒ (1). The reduction
`(Yⱼ)_red = Yⱼ ×_Y Yred` of the affine formal algebraic space `Yⱼ` is isomorphic to the sheaf of a
reduced affine object of the site, two reductions of one sheaf being canonically isomorphic, and
`(Yⱼ)_red ⟶ Yred` is a base change of `Yⱼ ⟶ Y`, hence representable étale and jointly surjective.

The implication (4) ⇒ (1) is proved through condition (3), in
`StacksFrontier.AlgebraicGeometry.FormalSpace.QuasiCompactMorphismTFAE`. -/
theorem HasQuasiCompactFormalAtlas.exists_affine_etale_cover_reduction
    {X Y Xred Yred : FppfSheaf B S hS} {f : X ⟶ Y} {iX : Xred ⟶ X} {iY : Yred ⟶ Y}
    {fred : Xred ⟶ Yred} (h : HasQuasiCompactFormalAtlas B S hS f)
    (hX : IsFormalAlgebraicSpace B S hS X) (hY : IsFormalAlgebraicSpace B S hS Y)
    (hiX : IsReduction B S hS X Xred iX) (hiY : IsReduction B S hS Y Yred iY)
    (hfred : fred ≫ iY = iX ≫ f) :
    letI : HasColimitsOfSize.{u + 1, u + 1} (FppfSheaf B S hS) := Sheaf.instHasColimitsOfSize
    ∃ (I : Type (u + 1)) (Vi : I → FppfSheaf B S hS) (t : ∀ i, Vi i ⟶ Yred)
      (T : I → BigFppfOver B S hS),
      (∀ i, IsAffine ((BigFppfOver.toScheme B S hS).obj (T i))) ∧
      (∀ i, IsReduced ((BigFppfOver.toScheme B S hS).obj (T i))) ∧
      (∀ i, Nonempty (yonedaSheaf B S hS (T i) ≅ Vi i)) ∧
      (∀ i, IsRepresentableEtale B S hS (t i)) ∧
      Sheaf.IsLocallySurjective (Sigma.desc t) ∧
      ∀ (i : I) (P : FppfSheaf B S hS) (a : P ⟶ Vi i) (b : P ⟶ Xred),
        IsPullback a b (t i) fred → Space.IsQuasiCompactSpaceULift.{u + 1} B S hS P.obj := by
  let : HasColimitsOfSize.{u + 1, u + 1} (FppfSheaf B S hS) := Sheaf.instHasColimitsOfSize
  obtain ⟨I, Yi, c, haffine, hetale, hsurjective, hqc⟩ := h
  refine ⟨I, fun i ↦ pullback (c i) iY, fun i ↦ pullback.snd (c i) iY, ?_⟩
  -- each member of the covering is a formal algebraic space, being affine formal
  have hYi : ∀ i, IsFormalAlgebraicSpace B S hS (Yi i) := fun i ↦
    isFormalAlgebraicSpace_of_isAffineFormalAlgebraicSpace B S hS (haffine i)
  -- the shared computation at each member, applied to the chosen fibre product
  have hdata : ∀ i, IsReduction B S hS (pullback (c i) f)
      (pullback (pullback.snd (c i) f) iX) (pullback.fst (pullback.snd (c i) f) iX) ∧
      IsReduction B S hS (Yi i) (pullback (c i) iY) (pullback.fst (c i) iY) ∧
      Nonempty (pullback (pullback.snd (c i) f) iX ≅
        pullback (pullback.snd (c i) iY) fred) := fun i ↦ by
    obtain ⟨-, hiW, hiV, _pred, -, hpredsq⟩ :=
      exists_isReduction_pullback_iso_of_isRepresentableEtale B S hS
        hX hY (hYi i) hiX hiY hfred (hetale i) (IsPullback.of_hasPullback (c i) f)
    exact ⟨hiW, hiV, ⟨hpredsq.isoPullback⟩⟩
  -- the reduction of each member is the sheaf of a reduced affine object of the site
  have hsite : ∀ i, ∃ T : BigFppfOver B S hS,
      IsAffine ((BigFppfOver.toScheme B S hS).obj T) ∧
      IsReduced ((BigFppfOver.toScheme B S hS).obj T) ∧
      Nonempty (yonedaSheaf B S hS T ≅ pullback (c i) iY) := fun i ↦ by
    obtain ⟨T, g, hred, haff, -, hiT⟩ :=
      exists_isReduction_reduced_affine_siteObject_of_isAffineFormal B S hS (Yi i) (haffine i)
    obtain ⟨k, hk, -⟩ := (hdata i).2.1.universal (yonedaSheaf B S hS T) hiT.algebraic
      hiT.reduced g
    have _ : IsIso k := IsReduction.isIso_of_comp_eq B S hS hiT (hdata i).2.1 hk
    exact ⟨T, haff, hred, ⟨asIso k⟩⟩
  choose T haff hred hiso using hsite
  refine ⟨T, haff, hred, hiso, fun i ↦ isRepresentableEtale_pullback_snd B S hS (c i) iY
    (hetale i), Sheaf.isLocallySurjective_sigmaDesc_pullback_snd iY c hsurjective,
    fun i P a b hsqP ↦ ?_⟩
  -- the reduction of the fibre product is quasi-compact, by Stacks 0AJ9's implication (3) ⇒ (1)
  have hWqc : IsQuasiCompactSpace B S hS (pullback (c i) f) :=
    hqc i _ (pullback.fst (c i) f) (pullback.snd (c i) f) (IsPullback.of_hasPullback (c i) f)
  obtain ⟨e⟩ := (hdata i).2.2
  have hQqc : Space.IsQuasiCompactSpaceULift.{u + 1} B S hS
      (pullback (pullback.snd (c i) iY) fred).obj :=
    Space.isQuasiCompactSpaceULift_of_iso B S hS
      ((sheafToPresheaf (BigFppfOver.topology B S hS) (Type (u + 1))).mapIso e)
      (IsQuasiCompactSpace.isQuasiCompactSpaceULift_of_isReduction B S hS (hdata i).1 hWqc)
  -- and it is the fibre product tested at, up to isomorphism
  exact Space.isQuasiCompactSpaceULift_of_iso B S hS
    ((hsqP.map (sheafToPresheaf (BigFppfOver.topology B S hS) (Type (u + 1)))).isoPullback.trans
      (((IsPullback.of_hasPullback (pullback.snd (c i) iY) fred).map
        (sheafToPresheaf (BigFppfOver.topology B S hS) (Type (u + 1)))).isoPullback).symm).symm
    hQqc

end AlgebraicGeometry.FormalSpace

end
