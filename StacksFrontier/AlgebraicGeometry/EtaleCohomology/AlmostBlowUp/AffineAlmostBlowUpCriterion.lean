module

public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.AlmostBlowUp.DerivedHDescent
public import StacksFrontier.CategoryTheory.Sites.Cohomology.MayerVietoris.DescentForAFamilyOfSquares
import StacksCore.Tactic.StacksAttribute

/-!
# The essential image of `Rε_*` tested on affine almost blowup squares

Let `B` be a big h site containing a scheme `S`, so that the big h category over `S` carries the
h topology `J`, and let `J' ≤ J` be a coarser topology on the same category — the fppf topology
in the source. A sheaf of rings `𝒪` for `J` is also a sheaf of rings for `J'`, and the identity
functor is a comparison of ringed sites `ε : (C_J, 𝒪_J) ⟶ (C_{J'}, 𝒪_{J'})` with derived direct
image `Rε_*`. Stacks 0EWQ says that an object `K` of `D⁺(𝒪_{J'})` is in the essential image of
`Rε_*` if and only if the canonical Mayer–Vietoris comparison `c^K_{X,X',Z,E}` of Stacks 0F16 is
a quasi-isomorphism for every almost blowup square of the site whose base `X` is affine.

## Main definitions

* `AlgebraicGeometry.AffineAlmostBlowUpSquare`: an almost blowup square of the big h category
  over `S` with affine base, bundled so that these squares form a family indexed by a type.
* `AlgebraicGeometry.BigHOver.IsAffineAlmostBlowUpDetecting`: the property of a topology `J'`
  that affine almost blowup squares detect h sheaves among `J'`-sheaves of sets.
* `AlgebraicGeometry.EssImageIffAffineAlmostBlowUpBigH`: the assertion of Stacks 0EWQ for a
  topology `J' ≤ J` and a sheaf of rings `𝒪` for the h topology.

## Main results

* `AlgebraicGeometry.isCSquareIso_of_essImage_affineAlmostBlowUp_bigH`: **Stacks 0EWQ, the
  direction "only if"** — an object in the essential image of `Rε_*` has all its comparison maps
  at affine almost blowup squares invertible.
* `AlgebraicGeometry.essImageIffAffineAlmostBlowUpBigH_of_isAffineAlmostBlowUpDetecting`: the
  assertion of Stacks 0EWQ for every topology `J' ≤ J` whose sheaves of sets affine almost blowup
  squares detect h sheaves among.
* `AlgebraicGeometry.essImage_iff_forall_isCSquareIso_affineAlmostBlowUp_bigH`: the same
  characterization with the derived functor, its unit and the object spelled out as binders.
* `AlgebraicGeometry.BigHOver.isAffineAlmostBlowUpDetecting_self`: affine almost blowup squares
  detect h sheaves among h sheaves.

**Stacks 0EWQ itself** is
`AlgebraicGeometry.essImage_iff_forall_isCSquareIso_affineAlmostBlowUp_fppf_bigH` in
`StacksFrontier.AlgebraicGeometry.EtaleCohomology.AlmostBlowUp.AffineAlmostBlowUpFppfCriterion`: the
assertion above at the fppf topology, which is the source's setting, with the detection supplied
by the sufficiency direction of Stacks 0EVF.

## Implementation notes

The direction "only if" is Stacks 0EWN,
`AlgebraicGeometry.isCSquareIso_of_essImage_almostBlowUpSquare_bigH`, which holds for every
almost blowup square of the site and every object of `D(𝒪_{J'})`; neither affineness of the base
nor boundedness below of `K` is used.

The converse is Stacks 0F18,
`Stacks.Cohomology.MayerVietoris.essImage_iff_forall_isCSquareIso`, applied to the family of all
affine almost blowup squares. That lemma has two hypotheses: that the comparison maps are
invertible on the essential image, which is again Stacks 0EWN, and that the family *detects* `J`
sheaves among `J'`-sheaves of sets, which is
`AlgebraicGeometry.BigHOver.IsAffineAlmostBlowUpDetecting`. Detection is a property of `J'` and
fails for a `J'` too coarse to see the other two conditions of Stacks 0EVF, so the assertion is
stated for an arbitrary `J'` with detection as an explicit assumption, and then proved at the
fppf topology, where detection holds: an fppf sheaf is a Zariski sheaf and satisfies the sheaf
condition for a flat proper surjective morphism of finite presentation with affine target,
because such a morphism is an fppf covering, so the sufficiency direction of Stacks 0EVF applies.
That is
`AlgebraicGeometry.BigHOver.isAffineAlmostBlowUpDetecting_fppfTopology`, and the fppf topology on
this category is `AlgebraicGeometry.BigHOver.fppfTopology`, both in
`StacksFrontier.AlgebraicGeometry.EtaleCohomology.AlmostBlowUp.AffineAlmostBlowUpFppfCriterion`.

The detection condition is phrased on the square-indexed family rather than through
`AlgebraicGeometry.BigHOver.IsAffineAlmostBlowUpSheaf`, the form condition (3) of Stacks 0EVF
takes there; the two differ by `CategoryTheory.IsPullback.flip` on the image square, because
`CategoryTheory.Square.op` exchanges the two outer vertices.

A square of the site is bundled with its centre and the hypotheses on it, as in Stacks 0EWN, so
that the affine almost blowup squares form a family indexed by a type; the vertices are, in
order, the exceptional subscheme, the modification, the centre and the base.

`Rε_*` is an arbitrary right derived functor of `ε_*` with its unit `η`, as in Stacks 0EWN and
Stacks 0F18, so that the statement is about the essential image of any of them.

The coarser sheaf of rings is written `AlgebraicGeometry.RingedSite.ringSheaf` of the coarser
ringed site, as in Stacks 0EWN and Stacks 0F19, whereas Stacks 0F18 writes it
`Stacks.Sites.CoarserTopology.ringSheafOfLe`. The two are the same sheaf of rings, and the
identification is definitional, but typeclass inference does not see through it: the hypothesis
that `Rε_*` is a right derived functor, stated for one spelling, is not found for the other. The
proof of the characterization therefore retypes `Rε_*` and `η` once, and the hypothesis is
transported across the identification by hand.

## References

* [Stacks Project, Tag 0EWQ](https://stacks.math.columbia.edu/tag/0EWQ)
* [Stacks Project, Tag 0EWN](https://stacks.math.columbia.edu/tag/0EWN)
* [Stacks Project, Tag 0F18](https://stacks.math.columbia.edu/tag/0F18)
* [Stacks Project, Tag 0F16](https://stacks.math.columbia.edu/tag/0F16)
* [Stacks Project, Tag 0EVF](https://stacks.math.columbia.edu/tag/0EVF)
* [Stacks Project, Tag 0EWM](https://stacks.math.columbia.edu/tag/0EWM)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits
open Stacks.Sites.CoarserTopology Stacks.Cohomology.MayerVietoris

universe u v r

namespace AlgebraicGeometry

attribute [local instance] HasDerivedCategory.standard

/-- An almost blowup square of the big h category over `S` whose base is affine, bundled with
its centre. The vertices are, in order, the exceptional subscheme, the modification, the centre
and the base. -/
structure AffineAlmostBlowUpSquare (B : BigHSite.{u}) (S : Scheme.{u}) (hS : B.Contains S) where
  /-- The square of the site. -/
  square : Square (BigHOver B S hS)
  /-- The centre, a quasi-coherent ideal sheaf on the underlying scheme of the base. -/
  center : ((BigHOver.toScheme B S hS).obj square.X₄).IdealSheafData
  /-- The underlying scheme of the base is affine. -/
  isAffine_base : IsAffine ((BigHOver.toScheme B S hS).obj square.X₄)
  /-- The centre and the modification form an almost blowup square. -/
  isAlmostBlowUpSquare :
    IsAlmostBlowUpSquare center ((BigHOver.toScheme B S hS).map square.f₂₄)
  /-- The lower-left vertex is the closed subscheme cut out by the centre, over the base. -/
  centerIso : Nonempty (Over.mk ((BigHOver.toScheme B S hS).map square.f₃₄) ≅
    Over.mk center.subschemeι)
  /-- The square of underlying schemes is cartesian, so the upper-left vertex is the exceptional
  subscheme. -/
  isPullback : (square.map (BigHOver.toScheme B S hS)).IsPullback

namespace BigHOver

/-- **Affine almost blowup squares detect h sheaves.** The property of a topology `J'` on the big
h category over `S` that a `J'`-sheaf of sets whose restriction maps along every affine almost
blowup square form a cartesian square is a sheaf for the h topology.

For the fppf topology this is the converse direction of Stacks 0EVF. -/
def IsAffineAlmostBlowUpDetecting (B : BigHSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)
    (J' : GrothendieckTopology (BigHOver B S hS)) : Prop :=
  ∀ F : Sheaf J' (Type (u + 1)),
    (∀ sq : AffineAlmostBlowUpSquare B S hS, (sq.square.op.map F.obj).IsPullback) →
      Presheaf.IsSheaf (BigHOver.topology B S hS) F.obj

/-- The h topology detects h sheaves: a sheaf for the h topology is one, whatever its
restriction maps along affine almost blowup squares do. -/
theorem isAffineAlmostBlowUpDetecting_self (B : BigHSite.{u}) (S : Scheme.{u})
    (hS : B.Contains S) :
    IsAffineAlmostBlowUpDetecting B S hS (BigHOver.topology B S hS) :=
  fun F _ ↦ F.property

end BigHOver

section

variable (B : BigHSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)
  (O : Sheaf (BigHOver.topology B S hS) CommRingCat.{r})
  {J' : GrothendieckTopology (BigHOver B S hS)} (hJ : J' ≤ BigHOver.topology B S hS)
  [HasSheafify (BigHOver.topology B S hS) AddCommGrpCat.{v}]
  [(BigHOver.topology B S hS).WEqualsLocallyBijective AddCommGrpCat.{v}]
  [HasSheafify J' AddCommGrpCat.{v}] [J'.WEqualsLocallyBijective AddCommGrpCat.{v}]
  [UnivLE.{u + 1, v}] [UnivLE.{u, v}] [UnivLE.{r, v}]

/-- **Stacks 0EWQ, the direction "only if".** Let `J' ≤ J` be a topology coarser than the h
topology on the big h category over `S` and let `𝒪` be a sheaf of rings for the h topology, so
that the identity functor is a comparison of ringed sites
`ε : (C_J, 𝒪_J) ⟶ (C_{J'}, 𝒪_{J'})`. Then for every object `K` of `D(𝒪_{J'})` in the essential
image of the derived direct image `Rε_*` and every almost blowup square of the site with affine
base, the canonical Mayer–Vietoris comparison `c^K_{X,X',Z,E}` of Stacks 0F16 is an isomorphism.

This is Stacks 0EWN; affineness of the base is not used, and `K` need not be bounded below. -/
@[stacks 0EWQ "only if"]
theorem isCSquareIso_of_essImage_affineAlmostBlowUp_bigH
    (Rε : DerivedCategory (SheafOfModules.{v}
        (Stacks.SheafOfModules.Tensor.ringSheaf (bigHRingedSite B S hS O).O)) ⥤
      DerivedCategory (SheafOfModules.{v}
        (Stacks.SheafOfModules.Tensor.ringSheaf ((bigHRingedSite B S hS O).ofLe hJ).O)))
    (η : (modulePushforward.{u + 1, v, u, r} hJ
          (Stacks.SheafOfModules.Tensor.ringSheaf (bigHRingedSite B S hS O).O)).mapHomotopyCategory
            (ComplexShape.up ℤ) ⋙
        DerivedCategory.Qh ⟶ DerivedCategory.Qh ⋙ Rε)
    [Rε.IsRightDerivedFunctor η (HomotopyCategory.quasiIso
      (SheafOfModules.{v} (Stacks.SheafOfModules.Tensor.ringSheaf (bigHRingedSite B S hS O).O))
        (ComplexShape.up ℤ))]
    (K : DerivedCategory (SheafOfModules.{v}
        (Stacks.SheafOfModules.Tensor.ringSheaf ((bigHRingedSite B S hS O).ofLe hJ).O)))
    (hK : Rε.essImage K) (sq : AffineAlmostBlowUpSquare B S hS) :
    (Stacks.MayerVietoris.CanonicalMapOfComplexes.derivedCSquareData.{u + 1, v}
      (R := (Stacks.SheafOfModules.Tensor.ringSheaf ((bigHRingedSite B S hS O).ofLe hJ).O))
        sq.square).IsCSquareIso K :=
  isCSquareIso_of_essImage_almostBlowUpSquare_bigH B S hS O hJ Rε η K hK sq.square sq.center
    sq.isAlmostBlowUpSquare sq.centerIso sq.isPullback

/-- **The assertion of Stacks 0EWQ.** Let `J' ≤ J` be a topology coarser than the h topology on
the big h category over `S` and let `𝒪` be a sheaf of rings for the h topology, so that the
identity functor is a comparison of ringed sites `ε : (C_J, 𝒪_J) ⟶ (C_{J'}, 𝒪_{J'})`. The
assertion is that an object `K` of `D⁺(𝒪_{J'})` lies in the essential image of the derived direct
image `Rε_*` if and only if the canonical Mayer–Vietoris comparison `c^K_{X,X',Z,E}` of Stacks
0F16 is an isomorphism for every almost blowup square of the site whose base is affine.

`Rε_*` is an arbitrary right derived functor of `ε_*` together with its unit `η`, as in Stacks
0EWN and Stacks 0F18, so the assertion is about the essential image of any of them.

The assertion is named so that it can also be stated where the sufficiency direction of Stacks
0EVF is available. That import closure carries a global `Abelian (SheafOfModules ...)` instance
whose module universe is a `max`, which no longer unifies with the universe of the sheaves of
modules here, so the derived categories below do not elaborate afresh there; a saturated
assertion costs no elaboration. -/
def EssImageIffAffineAlmostBlowUpBigH : Prop :=
  ∀ (Rε : DerivedCategory (SheafOfModules.{v}
        (Stacks.SheafOfModules.Tensor.ringSheaf (bigHRingedSite B S hS O).O)) ⥤
      DerivedCategory (SheafOfModules.{v}
        (Stacks.SheafOfModules.Tensor.ringSheaf ((bigHRingedSite B S hS O).ofLe hJ).O)))
    (η : (modulePushforward.{u + 1, v, u, r} hJ
          (Stacks.SheafOfModules.Tensor.ringSheaf (bigHRingedSite B S hS O).O)).mapHomotopyCategory
            (ComplexShape.up ℤ) ⋙
        DerivedCategory.Qh ⟶ DerivedCategory.Qh ⋙ Rε)
    [Rε.IsRightDerivedFunctor η (HomotopyCategory.quasiIso
      (SheafOfModules.{v} (Stacks.SheafOfModules.Tensor.ringSheaf (bigHRingedSite B S hS O).O))
        (ComplexShape.up ℤ))]
    (K : DerivedCategory (SheafOfModules.{v}
        (Stacks.SheafOfModules.Tensor.ringSheaf ((bigHRingedSite B S hS O).ofLe hJ).O))),
    (DerivedCategory.TStructure.t (C := SheafOfModules.{v}
        (Stacks.SheafOfModules.Tensor.ringSheaf ((bigHRingedSite B S hS O).ofLe hJ).O))).plus K →
      (Rε.essImage K ↔ ∀ sq : AffineAlmostBlowUpSquare B S hS,
        (Stacks.MayerVietoris.CanonicalMapOfComplexes.derivedCSquareData.{u + 1, v}
        (R := (Stacks.SheafOfModules.Tensor.ringSheaf ((bigHRingedSite B S hS O).ofLe hJ).O))
          sq.square).IsCSquareIso K)

/-- **The assertion of Stacks 0EWQ for a topology whose sheaves affine almost blowup squares
detect h sheaves among.** Let `J' ≤ J` be a topology coarser than the h topology on the big h
category over `S` and let `𝒪` be a sheaf of rings for the h topology, so that the identity functor
is a comparison of ringed sites `ε : (C_J, 𝒪_J) ⟶ (C_{J'}, 𝒪_{J'})`, and let affine almost blowup
squares detect h sheaves among `J'`-sheaves of sets. Then an object `K` of `D⁺(𝒪_{J'})` lies in
the essential image of the derived direct image `Rε_*` if and only if the canonical Mayer–Vietoris
comparison `c^K_{X,X',Z,E}` of Stacks 0F16 is an isomorphism for every almost blowup square of the
site whose base is affine.

This is Stacks 0F18 for the family of affine almost blowup squares, whose comparison hypothesis
is Stacks 0EWN. Detection is a property of `J'`; it holds at the fppf topology, the setting of
Stacks 0EWQ, by `AlgebraicGeometry.BigHOver.isAffineAlmostBlowUpDetecting_fppfTopology`, and the
tag is registered on
`AlgebraicGeometry.essImage_iff_forall_isCSquareIso_affineAlmostBlowUp_fppf_bigH` there. -/
theorem essImageIffAffineAlmostBlowUpBigH_of_isAffineAlmostBlowUpDetecting
    (hdetect : BigHOver.IsAffineAlmostBlowUpDetecting B S hS J') :
    EssImageIffAffineAlmostBlowUpBigH.{u, v, r} B S hS O hJ := by
  intro Rε η hRD K hK
  let Rε' : DerivedCategory (SheafOfModules.{v}
        (Stacks.SheafOfModules.Tensor.ringSheaf (bigHRingedSite B S hS O).O)) ⥤
      DerivedCategory (SheafOfModules.{v}
        (ringSheafOfLe hJ
          (Stacks.SheafOfModules.Tensor.ringSheaf (bigHRingedSite B S hS O).O))) := Rε
  let η' : (modulePushforward.{u + 1, v, u, r} hJ
        (Stacks.SheafOfModules.Tensor.ringSheaf (bigHRingedSite B S hS O).O)).mapHomotopyCategory
          (ComplexShape.up ℤ) ⋙
      DerivedCategory.Qh ⟶ DerivedCategory.Qh ⋙ Rε' := η
  have : Rε'.IsRightDerivedFunctor η' (HomotopyCategory.quasiIso
    (SheafOfModules.{v} (Stacks.SheafOfModules.Tensor.ringSheaf (bigHRingedSite B S hS O).O))
      (ComplexShape.up ℤ)) := hRD
  exact essImage_iff_forall_isCSquareIso.{u + 1, v, u, r}
    (S := bigHRingedSite B S hS O) (J' := J') hJ
    (fun sq : AffineAlmostBlowUpSquare B S hS ↦ sq.square) hdetect Rε' η'
    (fun K' hK' sq ↦ isCSquareIso_of_essImage_affineAlmostBlowUp_bigH B S hS O hJ Rε η K' hK' sq)
    K hK

/-- **Stacks 0EWQ.** Let `J' ≤ J` be a topology coarser than the h topology on the big h category
over `S` and let `𝒪` be a sheaf of rings for the h topology, so that the identity functor is a
comparison of ringed sites `ε : (C_J, 𝒪_J) ⟶ (C_{J'}, 𝒪_{J'})`, and assume that affine almost
blowup squares detect h sheaves among `J'`-sheaves of sets. Then an object `K` of `D⁺(𝒪_{J'})`
lies in the essential image of the derived direct image `Rε_*` if and only if the canonical
Mayer–Vietoris comparison `c^K_{X,X',Z,E}` of Stacks 0F16 is an isomorphism for every almost
blowup square of the site whose base is affine.

This is the derived functor, its unit and the object spelled out as binders, which is
`AlgebraicGeometry.essImageIffAffineAlmostBlowUpBigH_of_isAffineAlmostBlowUpDetecting` with its
conclusion unfolded; the bundled form is the one a downstream file can state, because there the
binders no longer elaborate. The tag is registered here with the detection hypothesis named, and
again unconditionally on
`AlgebraicGeometry.essImage_iff_forall_isCSquareIso_affineAlmostBlowUp_fppf_bigH`, the assertion
at the fppf topology, where detection holds. -/
@[stacks 0EWQ "the iff, given the detection hypothesis"]
theorem essImage_iff_forall_isCSquareIso_affineAlmostBlowUp_bigH
    (hdetect : BigHOver.IsAffineAlmostBlowUpDetecting B S hS J')
    (Rε : DerivedCategory (SheafOfModules.{v}
        (Stacks.SheafOfModules.Tensor.ringSheaf (bigHRingedSite B S hS O).O)) ⥤
      DerivedCategory (SheafOfModules.{v}
        (Stacks.SheafOfModules.Tensor.ringSheaf ((bigHRingedSite B S hS O).ofLe hJ).O)))
    (η : (modulePushforward.{u + 1, v, u, r} hJ
          (Stacks.SheafOfModules.Tensor.ringSheaf (bigHRingedSite B S hS O).O)).mapHomotopyCategory
            (ComplexShape.up ℤ) ⋙
        DerivedCategory.Qh ⟶ DerivedCategory.Qh ⋙ Rε)
    [hRD : Rε.IsRightDerivedFunctor η (HomotopyCategory.quasiIso
      (SheafOfModules.{v} (Stacks.SheafOfModules.Tensor.ringSheaf (bigHRingedSite B S hS O).O))
        (ComplexShape.up ℤ))]
    (K : DerivedCategory (SheafOfModules.{v}
        (Stacks.SheafOfModules.Tensor.ringSheaf ((bigHRingedSite B S hS O).ofLe hJ).O)))
    (hK : (DerivedCategory.TStructure.t (C := SheafOfModules.{v}
      (Stacks.SheafOfModules.Tensor.ringSheaf ((bigHRingedSite B S hS O).ofLe hJ).O))).plus K) :
    Rε.essImage K ↔ ∀ sq : AffineAlmostBlowUpSquare B S hS,
      (Stacks.MayerVietoris.CanonicalMapOfComplexes.derivedCSquareData.{u + 1, v}
      (R := (Stacks.SheafOfModules.Tensor.ringSheaf ((bigHRingedSite B S hS O).ofLe hJ).O))
        sq.square).IsCSquareIso K :=
  essImageIffAffineAlmostBlowUpBigH_of_isAffineAlmostBlowUpDetecting B S hS O hJ hdetect Rε η K hK

end

end AlgebraicGeometry

end
