module

public import StacksFrontier.AlgebraicGeometry.Spaces.EtaleChartBaseChange
public import StacksFrontier.AlgebraicGeometry.Spaces.FiniteTypePermanence
public import StacksFrontier.AlgebraicGeometry.Spaces.FiniteTypeQuasicoherentSubobjectExtensionAffine
public import StacksFrontier.AlgebraicGeometry.Spaces.MapDescent
public import StacksFrontier.AlgebraicGeometry.Spaces.NoetherianSpaces
public import StacksFrontier.AlgebraicGeometry.Spaces.QuasiCompactFpqcLocalAtTarget
public import StacksFrontier.AlgebraicGeometry.Spaces.SeparatedQuasiFiniteEtaleDescent
public import StacksFrontier.AlgebraicGeometry.Spaces.SeparatedVariants
public import StacksFrontier.AlgebraicGeometry.Spaces.Morphisms.SeparationAxioms
public import StacksFrontier.AlgebraicGeometry.Spaces.Perfect.AffineEtaleDerivedPushforwardSquare
public import StacksFrontier.AlgebraicGeometry.Spaces.DerivedModulePushforward
public import StacksFrontier.AlgebraicGeometry.Spaces.PseudoCoherentCohomologyUnconditional

/-!
# The hypothesis of Stacks 09TG on a Noetherian algebraic space

[Stacks, Tag 09TN] — the comparison functor `i_X : D(QCoh(𝒪_X)) ⥤ D_QCoh(𝒪_X)` of
[Stacks, Tag 08F1] is an equivalence with quasi-inverse `RQ_X` on a Noetherian algebraic space —
is proved in the source from "Lemmas 09TM and 09TG": the hypothesis of [Stacks, Tag 09TG] asks,
for an étale `j : V ⟶ W` with `V` affine and `W ⊆ X` a quasi-compact open, that the derived
functor of `j_*` on quasi-coherent modules be compatible with `Rj_*`; `V` and `W` are then
Noetherian, and [Stacks, Tag 09TM] gives the compatibility.  This file supplies the geometric
half of that deduction; Stacks 09TN itself is
`StacksFrontier/AlgebraicGeometry/Spaces/Perfect/NoetherianDerivedCoheratorEquivalence.lean`.

## Main results

All names are in the namespace `AlgebraicGeometry`.

* `Space.isNoetherian_of_isOpenImmersion_of_isQuasiCompactSpace`: a quasi-compact open subspace
  of a Noetherian algebraic space is Noetherian.
* `Space.isNoetherian_of_isEtale_of_isAffineSpace`: an affine algebraic space étale over a
  locally Noetherian one is Noetherian.
* `Space.affineEtaleDerivedPushforwardSquareCommutes_of_isNoetherian_of_computedOnKInjectives`:
  the hypothesis of Stacks 09TG holds on a Noetherian space as soon as derived direct images
  between Noetherian spaces are computed on K-injective complexes of quasi-coherent modules.

## References

* [Stacks Project, Tag 09TN](https://stacks.math.columbia.edu/tag/09TN)
* [Stacks Project, Tag 09TG](https://stacks.math.columbia.edu/tag/09TG)
* [Stacks Project, Tag 03EA](https://stacks.math.columbia.edu/tag/03EA)
* [Stacks Project, Tag 04ZK](https://stacks.math.columbia.edu/tag/04ZK)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits

universe u

namespace AlgebraicGeometry.Space

variable (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)
  (hZ : B.Contains (⊤_ Scheme.{u}))

/-- **A quasi-compact open subspace of a Noetherian algebraic space is Noetherian.**
Quasi-compactness is given; quasi-separatedness descends along the open immersion, which is a
monomorphism and hence separated (Stacks 042N, 03KK, 04ZH); local Noetherianity descends along
it, an open immersion being étale and so locally of finite type (Stacks 04ZK). -/
theorem isNoetherian_of_isOpenImmersion_of_isQuasiCompactSpace
    {W X : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u} (hW : IsAlgebraicSpace B S hS W)
    (hX : IsAlgebraicSpace B S hS X) (j : W ⟶ X) (hj : IsOpenImmersion B S hS j)
    (hWqc : IsQuasiCompactSpace B S hS W) (hN : IsNoetherian B S hS hZ X) :
    IsNoetherian B S hS hZ W :=
  ⟨hWqc,
    isAbsolutelyQuasiSeparated_of_isQuasiSeparated B S hS hZ hW hN.2.1
      (isQuasiSeparated_of_isSeparated B S hS
        (isSeparated_of_mono (B := B) (S := S) (hS := hS) j (mono_of_presheaf_isOpenImmersion hj))),
    isLocallyNoetherian_of_isLocallyOfFiniteType B S hS hW hX j
      (isLocallyOfFiniteType_of_isEtale' B S hS j (isEtale_of_isOpenImmersion B S hS hj)) hN.2.2⟩

/-- **An affine algebraic space étale over a locally Noetherian algebraic space is
Noetherian.**  An affine space is quasi-compact and quasi-separated, and local Noetherianity
descends along the étale, hence locally of finite type, morphism (Stacks 04ZK). -/
theorem isNoetherian_of_isEtale_of_isAffineSpace
    {V W : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u} (hV : IsAlgebraicSpace B S hS V)
    (hW : IsAlgebraicSpace B S hS W) (j : V ⟶ W) (hj : IsEtale B S hS j)
    (hVa : IsAffineSpace B S hS V)
    (hN : HasEtaleLocalProperty B S hS W (fun T : Scheme.{u} => IsLocallyNoetherian T)) :
    IsNoetherian B S hS hZ V :=
  ⟨(by
      obtain ⟨T, hT, ⟨e⟩⟩ := hVa
      exact isQuasiCompactSpace_of_iso B S hS e.symm
        (isQuasiCompactSpace_yoneda_of_isAffine B S hS T hT)),
    isAbsolutelyQuasiSeparated_of_isAffineSpace B S hS hZ hVa,
    isLocallyNoetherian_of_isLocallyOfFiniteType B S hS hV hW j
      (isLocallyOfFiniteType_of_isEtale' B S hS j hj) hN⟩


/-! ### The hypothesis of Stacks 09TG on a Noetherian algebraic space -/

section Hypothesis

attribute [local instance] HasDerivedCategory.standard

/-- **The hypothesis of [Stacks, Tag 09TG] holds on a Noetherian algebraic space, as soon as
derived direct images between Noetherian spaces are computed on K-injective complexes of
quasi-coherent modules.**  For `j : V ⟶ W` étale with `V` affine and `W ⊆ X` a quasi-compact
open, both `V` and `W` are Noetherian
(`AlgebraicGeometry.Space.isNoetherian_of_isOpenImmersion_of_isQuasiCompactSpace`,
`AlgebraicGeometry.Space.isNoetherian_of_isEtale_of_isAffineSpace`), so `hcomp` applies to the
chosen total right derived functor of the direct image of all modules along `j`, and
`AlgebraicGeometry.Space.affineEtaleDerivedPushforwardSquareCommutes_of_kInjectives` turns that
into the commuting square. -/
theorem affineEtaleDerivedPushforwardSquareCommutes_of_isNoetherian_of_computedOnKInjectives
    (X : AlgebraicSpaces B S hS) (hN : IsNoetherian B S hS hZ X.1)
    (hcomp : ∀ (V W : AlgebraicSpaces B S hS), IsNoetherian B S hS hZ V.1 →
      IsNoetherian B S hS hZ W.1 → ∀ (j : V ⟶ W)
      (Rj : DerivedCategory (Modules.{u, u} B S hS V.1 V.2) ⥤
        DerivedCategory (Modules.{u, u} B S hS W.1 W.2))
      (βj : (modulePushforward B S hS j).mapHomotopyCategory (ComplexShape.up ℤ) ⋙
        DerivedCategory.Qh ⟶ DerivedCategory.Qh ⋙ Rj),
      Rj.IsRightDerivedFunctor βj
          (HomotopyCategory.quasiIso (Modules.{u, u} B S hS V.1 V.2) (ComplexShape.up ℤ)) →
        DerivedPushforwardComputedOnKInjectives B S hS j Rj βj) :
    ExistsAffineEtaleDerivedPushforwardSquare B S hS X.1 X.2 := by
  refine affineEtaleDerivedPushforwardSquareCommutes_of_kInjectives B S hS X.1 X.2 ?_
  intro W jW hjW hWqc V j hj hV _
  have hW : IsNoetherian B S hS hZ W.1 :=
    isNoetherian_of_isOpenImmersion_of_isQuasiCompactSpace B S hS hZ W.2 X.2 jW.hom hjW hWqc hN
  have hV' : IsNoetherian B S hS hZ V.1 :=
    isNoetherian_of_isEtale_of_isAffineSpace B S hS hZ V.2 W.2 j.hom hj hV hW.2.2
  have := hasRightDerivedFunctor_modulePushforward B S hS j
  let F := (modulePushforward B S hS j).mapHomotopyCategory (ComplexShape.up ℤ) ⋙
    DerivedCategory.Qh
  exact ⟨_, _, inferInstance, hcomp V W hV' hW j
    (F.totalRightDerived DerivedCategory.Qh (HomotopyCategory.quasiIso _ (ComplexShape.up ℤ)))
    (F.totalRightDerivedUnit DerivedCategory.Qh (HomotopyCategory.quasiIso _ (ComplexShape.up ℤ)))
    inferInstance⟩

end Hypothesis

end AlgebraicGeometry.Space

end
