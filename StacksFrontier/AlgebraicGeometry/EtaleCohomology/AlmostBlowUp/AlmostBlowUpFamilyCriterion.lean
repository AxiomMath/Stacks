module

public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.AlmostBlowUp.AffineAlmostBlowUpCriterion

/-!
# The essential image of `Rε_*` tested on a family of affine almost blowup squares

Let `B` be a big h site containing a scheme `S`, so that the big h category over `S` carries the
h topology `J`, and let `J' ≤ J` be a coarser topology on the same category. A sheaf of rings
`𝒪` for `J` is also a sheaf of rings for `J'`, and the identity functor is a comparison of ringed
sites `ε : (C_J, 𝒪_J) ⟶ (C_{J'}, 𝒪_{J'})` with derived direct image `Rε_*`.

Stacks 0EWQ and Stacks 0EWR both say that an object `K` of `D⁺(𝒪_{J'})` lies in the essential
image of `Rε_*` exactly when the canonical Mayer–Vietoris comparison `c^K_{X,X',Z,E}` of Stacks
0F16 is a quasi-isomorphism for every square of some family of almost blowup squares with affine
base: all of them for Stacks 0EWQ, those of More on Flatness, Examples 0EVG and 0EVH for Stacks
0EWR. Both are Stacks 0F18 applied to the family, and this file proves that application once,
for an arbitrary family of affine almost blowup squares which detects h sheaves among
`J'`-sheaves of sets.

## Main definitions

* `AlgebraicGeometry.BigHOver.IsAffineAlmostBlowUpFamilyDetecting`: the property of a family of
  affine almost blowup squares and a topology `J'` that the squares of the family detect h
  sheaves among `J'`-sheaves of sets.
* `AlgebraicGeometry.EssImageIffAffineAlmostBlowUpFamilyBigH`: the assertion that the essential
  image of `Rε_*` on `D⁺(𝒪_{J'})` is cut out by the comparison maps at the squares of a family.

## Main results

* `AlgebraicGeometry.essImageIffAffineAlmostBlowUpFamilyBigH_of_isDetecting`: the assertion holds
  for every family which detects h sheaves among `J'`-sheaves of sets.

## Implementation notes

The direction "only if" is Stacks 0EWN, which holds for every almost blowup square; the converse
is Stacks 0F18, `Stacks.Cohomology.MayerVietoris.essImage_iff_forall_isCSquareIso`, whose two
hypotheses are that the comparison maps are invertible on the essential image (again Stacks
0EWN) and that the family detects `J` sheaves among `J'`-sheaves of sets.

The assertion is a named `Prop`, in the style of
`AlgebraicGeometry.EssImageIffAffineAlmostBlowUpBigH`, so that it can be stated in modules whose
import closure contains the sufficiency direction of Stacks 0EVF: that closure carries a global
`Abelian (SheafOfModules ...)` instance whose module universe is a `max`, against which the
derived categories below do not elaborate afresh.

## References

* [Stacks Project, Tag 0EWQ](https://stacks.math.columbia.edu/tag/0EWQ)
* [Stacks Project, Tag 0EWR](https://stacks.math.columbia.edu/tag/0EWR)
* [Stacks Project, Tag 0EWN](https://stacks.math.columbia.edu/tag/0EWN)
* [Stacks Project, Tag 0F18](https://stacks.math.columbia.edu/tag/0F18)
* [Stacks Project, Tag 0F16](https://stacks.math.columbia.edu/tag/0F16)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits
open Stacks.Sites.CoarserTopology Stacks.Cohomology.MayerVietoris

universe w u v r

namespace AlgebraicGeometry

attribute [local instance] HasDerivedCategory.standard

namespace BigHOver

/-- **A family of affine almost blowup squares detects h sheaves.** The property of a family of
affine almost blowup squares of the big h category over `S` and of a topology `J'` on that
category that a `J'`-sheaf of sets whose restriction maps along every square of the family form a
cartesian square is a sheaf for the h topology. -/
def IsAffineAlmostBlowUpFamilyDetecting {B : BigHSite.{u}} {S : Scheme.{u}} {hS : B.Contains S}
    {ι : Type w} (sq : ι → AffineAlmostBlowUpSquare B S hS)
    (J' : GrothendieckTopology (BigHOver B S hS)) : Prop :=
  ∀ F : Sheaf J' (Type (u + 1)),
    (∀ i, ((sq i).square.op.map F.obj).IsPullback) →
      Presheaf.IsSheaf (BigHOver.topology B S hS) F.obj

end BigHOver

section

variable (B : BigHSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)
  (O : Sheaf (BigHOver.topology B S hS) CommRingCat.{r})
  {J' : GrothendieckTopology (BigHOver B S hS)} (hJ : J' ≤ BigHOver.topology B S hS)
  [HasSheafify (BigHOver.topology B S hS) AddCommGrpCat.{v}]
  [(BigHOver.topology B S hS).WEqualsLocallyBijective AddCommGrpCat.{v}]
  [HasSheafify J' AddCommGrpCat.{v}] [J'.WEqualsLocallyBijective AddCommGrpCat.{v}]
  [UnivLE.{u + 1, v}] [UnivLE.{u, v}] [UnivLE.{r, v}]

/-- **The essential image of `Rε_*`, cut out by a family of affine almost blowup squares.** Let
`J' ≤ J` be a topology coarser than the h topology on the big h category over `S`, let `𝒪` be a
sheaf of rings for the h topology, so that the identity functor is a comparison of ringed sites
`ε : (C_J, 𝒪_J) ⟶ (C_{J'}, 𝒪_{J'})`, and let `sq` be a family of affine almost blowup squares of
the site. The assertion is that an object `K` of `D⁺(𝒪_{J'})` lies in the essential image of the
derived direct image `Rε_*` if and only if the canonical Mayer–Vietoris comparison
`c^K_{X,X',Z,E}` of Stacks 0F16 is an isomorphism at every square of the family.

`Rε_*` is an arbitrary right derived functor of `ε_*` together with its unit `η`, as in Stacks
0EWN and Stacks 0F18, so the assertion is about the essential image of any of them. -/
def EssImageIffAffineAlmostBlowUpFamilyBigH {ι : Type w}
    (sq : ι → AffineAlmostBlowUpSquare B S hS) : Prop :=
  ∀ (Rε : DerivedCategory (SheafOfModules.{v} (Stacks.SheafOfModules.Tensor.ringSheaf
        (bigHRingedSite B S hS O).O)) ⥤
      DerivedCategory (SheafOfModules.{v} (Stacks.SheafOfModules.Tensor.ringSheaf
        ((bigHRingedSite B S hS O).ofLe hJ).O)))
    (η : (modulePushforward.{u + 1, v, u, r} hJ
          (Stacks.SheafOfModules.Tensor.ringSheaf (bigHRingedSite B S hS O).O)).mapHomotopyCategory
          (ComplexShape.up ℤ) ⋙
        DerivedCategory.Qh ⟶ DerivedCategory.Qh ⋙ Rε)
    [Rε.IsRightDerivedFunctor η (HomotopyCategory.quasiIso
      (SheafOfModules.{v} (Stacks.SheafOfModules.Tensor.ringSheaf (bigHRingedSite B S hS O).O))
        (ComplexShape.up ℤ))]
    (K : DerivedCategory (SheafOfModules.{v} (Stacks.SheafOfModules.Tensor.ringSheaf
      ((bigHRingedSite B S hS O).ofLe hJ).O))),
    (DerivedCategory.TStructure.t (C := SheafOfModules.{v}
        (Stacks.SheafOfModules.Tensor.ringSheaf ((bigHRingedSite B S hS O).ofLe hJ).O))).plus K →
      (Rε.essImage K ↔ ∀ i,
        (Stacks.MayerVietoris.CanonicalMapOfComplexes.derivedCSquareData.{u + 1, v}
        (R := (Stacks.SheafOfModules.Tensor.ringSheaf ((bigHRingedSite B S hS O).ofLe hJ).O))
          (sq i).square).IsCSquareIso K)

/-- **The essential image of `Rε_*` is cut out by any detecting family of affine almost blowup
squares.** Let `J' ≤ J` be a topology coarser than the h topology on the big h category over
`S`, let `𝒪` be a sheaf of rings for the h topology, and let `sq` be a family of affine almost
blowup squares of the site which detects h sheaves among `J'`-sheaves of sets. Then an object `K`
of `D⁺(𝒪_{J'})` lies in the essential image of the derived direct image `Rε_*` if and only if the
canonical Mayer–Vietoris comparison `c^K_{X,X',Z,E}` of Stacks 0F16 is an isomorphism at every
square of the family.

This is Stacks 0F18 for the family, whose comparison hypothesis is Stacks 0EWN. -/
theorem essImageIffAffineAlmostBlowUpFamilyBigH_of_isDetecting {ι : Type w}
    (sq : ι → AffineAlmostBlowUpSquare B S hS)
    (hdetect : BigHOver.IsAffineAlmostBlowUpFamilyDetecting sq J') :
    EssImageIffAffineAlmostBlowUpFamilyBigH.{w, u, v, r} B S hS O hJ sq := by
  intro Rε η hRD K hK
  let Rε' : DerivedCategory (SheafOfModules.{v} (Stacks.SheafOfModules.Tensor.ringSheaf
        (bigHRingedSite B S hS O).O)) ⥤
      DerivedCategory (SheafOfModules.{v}
        (ringSheafOfLe hJ (Stacks.SheafOfModules.Tensor.ringSheaf (bigHRingedSite B S hS O).O))) :=
    Rε
  let η' : (modulePushforward.{u + 1, v, u, r} hJ
        (Stacks.SheafOfModules.Tensor.ringSheaf (bigHRingedSite B S hS O).O)).mapHomotopyCategory
        (ComplexShape.up ℤ) ⋙
      DerivedCategory.Qh ⟶ DerivedCategory.Qh ⋙ Rε' := η
  have : Rε'.IsRightDerivedFunctor η' (HomotopyCategory.quasiIso
    (SheafOfModules.{v} (Stacks.SheafOfModules.Tensor.ringSheaf (bigHRingedSite B S hS O).O))
      (ComplexShape.up ℤ)) := hRD
  exact essImage_iff_forall_isCSquareIso.{u + 1, v, u, r}
    (S := bigHRingedSite B S hS O) (J' := J') hJ
    (fun i ↦ (sq i).square) hdetect Rε' η'
    (fun K' hK' i ↦ isCSquareIso_of_essImage_affineAlmostBlowUp_bigH B S hS O hJ Rε η K' hK'
      (sq i))
    K hK

end

end AlgebraicGeometry

end
