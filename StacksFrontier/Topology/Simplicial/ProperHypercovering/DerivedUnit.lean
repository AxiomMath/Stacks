module

public import StacksFrontier.CategoryTheory.Sites.Simplicial.HypercoveringObjectPushforwardAcyclic
public import StacksFrontier.Topology.Simplicial.ProperHypercovering.BoundedBelowDescent
public import StacksFrontier.Topology.Simplicial.ProperHypercovering.ComparisonUnit
public import StacksFrontier.Topology.Simplicial.ProperHypercovering.QcSmallAcyclic
public import StacksFrontier.Topology.Simplicial.ProperHypercovering.SpectralSequence
public import StacksFrontier.Topology.Simplicial.ProperHypercoveringFullyFaithful
import StacksCore.Tactic.StacksAttribute

/-!
# Cohomological descent for proper hypercoverings of locally quasi-compact spaces

Let `U` be a simplicial object of the category `LC` of Hausdorff, locally quasi-compact spaces and
let `a : U → X` be an augmentation which is a proper hypercovering of `X` (Stacks Section 09XA).
Stacks 09XS asserts that for `K` in `D⁺(X)` the canonical map

`K ⟶ Ra_*(a^{-1}K)`

is an isomorphism, where `a : Sh(U_Zar) → Sh(X)` is the morphism of topoi of Stacks 09W4.

## The proof

Choose a quasi-compact site `LC_qc` of Stacks 09X2 containing `X` and every `U_n`, read through
its small model; by Stacks 09X5 the augmentation is a hypercovering of `X` in `LC_qc`. Consider
the commutative diagram of topoi of Stacks 0DAF
```
Sh((LC_qc/U)_total) --h--> Sh(U_Zar)
        | a_qc                 | a
Sh(LC_qc/X)       --h₋₁--> Sh(X)
```
By Leray's acyclicity lemma (Stacks 015E) it suffices to show, for an abelian sheaf `F` on `X`,
that `F ⟶ a_* a^{-1} F` is an isomorphism, which is Stacks 0DAG, and that `a^{-1}F` is right
acyclic for `a_*`. For the latter put `M = h^{-1}a^{-1}F = a_qc^{-1}h₋₁^{-1}F`. Then:

* `a^{-1}F = h_* M`, as `h^{-1}` is fully faithful (`isIso_qcSmallComparisonMorphism_adj_unit`,
  Stacks 09X3 degreewise and Stacks 0D96);
* `M` is right acyclic for `h_*`: in simplicial degree `n` the higher direct images of `h` are
  those of the comparison `h_n : Sh(LC_qc/U_n) → Sh(U_n)` at `h_n^{-1}F_n`, which vanish by
  Stacks 0D91 (`isZero_rightDerived_qcSmallOpensPushforward`);
* so `R^q a_*(a^{-1}F) = R^q(a_* h_*)(M) = R^q(h₋₁,* a_qc,*)(M)` by Stacks 0DAF, `h_*` preserving
  injectives;
* `M = a_qc^{-1}N` with `N = h₋₁^{-1}F` is right acyclic for `a_qc,*` with `a_qc,* M = N`, by
  Stacks 0D8N and Stacks 0DA8 for the hypercovering of `X` in `LC_qc`;
* so `R^q(h₋₁,* a_qc,*)(M) = R^q h₋₁,*(N) = 0` for `q > 0`, by Stacks 0D91.

This is the source's proof, read on a single sheaf:

`Ra_*a^{-1} = Ra_* Rh_* h^{-1} a^{-1} = Rh₋₁,* Ra_qc,* a_qc^{-1} h₋₁^{-1} = Rh₋₁,* h₋₁^{-1} = id`.

## Main results

* `Stacks.Topology.Simplicial.isZero_rightDerived_qcZariskiAbelianDirectImage`: the higher direct
  images of `a^{-1}F` along `a : Sh(U_Zar) → Sh(X)` vanish, for a hypercovering of `X` in `LC_qc`.
* `ProperHypercovering.isZero_rightDerived_abelianDirectImage_of_isHypercovering`: the same
  vanishing for a proper hypercovering of `LC`, for the augmentation of Stacks 09W4.
* `ProperHypercovering.isIso_derivedAdjunction_unit_app_of_isHypercovering`: **Stacks 09XS**, the
  unit `K ⟶ Ra_*(a^{-1}K)` of the adjunction `a^{-1} ⊣ Ra_*` on `D⁺` of
  `ProperHypercovering.derivedAdjunction`.

## References

* [Stacks Project, Tag 09XS](https://stacks.math.columbia.edu/tag/09XS)
* [Stacks Project, Tag 0DAF](https://stacks.math.columbia.edu/tag/0DAF)
* [Stacks Project, Tag 0D91](https://stacks.math.columbia.edu/tag/0D91)
* [Stacks Project, Tag 0D8N](https://stacks.math.columbia.edu/tag/0D8N)
* [Stacks Project, Tag 09X5](https://stacks.math.columbia.edu/tag/09X5)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits Opposite TopologicalSpace
open Stacks.Topos.AbelianPushforward

universe u w

namespace Stacks.Topology.Simplicial

open Stacks.Topology Stacks.Topology.Simplicial.ProperHypercovering
open Stacks.CategoryTheory.Hypercovering CategoryTheory.SimplicialSemiRepresentable
open Stacks.Topology.LocallyQuasiCompactZariskiSituation

variable {S₀ : Set LocallyQuasiCompactHausdorff.{u}} {Bound : Cardinal.{u} → Cardinal.{u}}
  (S : LocallyQuasiCompactZariskiSituation.{u, w} S₀ Bound)
  (X : S.category) (U : SimplicialObject S.category)
  (a : U ⟶ (SimplicialObject.const S.category).obj X)

/-! ### The four abelian adjunctions of the diagram of Stacks 0DAF -/

section Adjunctions

/-- The inverse image `a^{-1} : Ab(X) ⥤ Ab(U_Zar)` of the augmentation of Stacks 09W4. -/
abbrev qcZariskiAbelianInverseImage :=
  Sites.abelianInverseImage (qcZariskiAugmentation S X U a)

/-- The direct image `a_* : Ab(U_Zar) ⥤ Ab(X)` of the augmentation of Stacks 09W4. -/
abbrev qcZariskiAbelianDirectImage :=
  abelianPushforward (SimplicialOpen.grothendieckTopology (qcSimplicialSpace S U))
    (qcZariskiAugmentation S X U a)

/-- The adjunction `a^{-1} ⊣ a_*` on abelian sheaves. -/
abbrev qcZariskiAbelianAdjunction :
    qcZariskiAbelianInverseImage S X U a ⊣ qcZariskiAbelianDirectImage S X U a :=
  abelianInverseImageAdjPushforward _ _

/-- The direct image of sheaves of sets along the comparison `h` is a right adjoint. -/
instance isRightAdjoint_qcSmallComparisonFunctor_sheafPushforwardContinuous :
    ((qcSmallComparisonFunctor S X U a).sheafPushforwardContinuous (Type u)
      (SimplicialOpen.grothendieckTopology (qcSimplicialSpace S U))
      (qcSmallTotalTopology S X U a)).IsRightAdjoint :=
  ⟨_, ⟨(qcSmallComparisonMorphism S X U a).adj⟩⟩

/-- The direct image `h_*` of the comparison `h : Sh((LC_qc/U)_total) → Sh(U_Zar)`, on abelian
sheaves: restriction along `V ↦ V/U_n`. -/
abbrev qcSmallComparisonAbelianDirectImage :=
  (qcSmallComparisonFunctor S X U a).sheafPushforwardContinuous AddCommGrpCat.{u}
    (SimplicialOpen.grothendieckTopology (qcSimplicialSpace S U)) (qcSmallTotalTopology S X U a)

/-- The adjunction `h^{-1} ⊣ h_*` on abelian sheaves. -/
abbrev qcSmallComparisonAbelianAdjunction :
    Sites.abelianInverseImage (qcSmallComparisonMorphism S X U a) ⊣
      qcSmallComparisonAbelianDirectImage S X U a :=
  abelianInverseImageAdjRestriction (qcSmallComparisonFunctor S X U a)
    (SimplicialOpen.grothendieckTopology (qcSimplicialSpace S U)) (qcSmallTotalTopology S X U a)
    (qcSmallComparisonMorphism S X U a) (Iso.refl _)

/-- **`h^{-1}` is fully faithful on abelian sheaves**: the unit `G ⟶ h_* h^{-1} G` is an
isomorphism for every abelian sheaf `G` on `U_Zar`. -/
instance isIso_qcSmallComparisonAbelianAdjunction_unit :
    IsIso (qcSmallComparisonAbelianAdjunction S X U a).unit := by
  have : ∀ G, IsIso ((qcSmallComparisonAbelianAdjunction S X U a).unit.app G) := fun G =>
    isIso_abelianInverseImageAdjRestriction_unit_app (qcSmallComparisonFunctor S X U a)
      (SimplicialOpen.grothendieckTopology (qcSimplicialSpace S U)) (qcSmallTotalTopology S X U a)
      (qcSmallComparisonMorphism S X U a) (Iso.refl _) inferInstance G
  exact NatIso.isIso_of_isIso_app _

/-- The direct image `h₋₁,*` of the comparison `h₋₁ : Sh(LC_qc/X) → Sh(X)`, on abelian sheaves:
restriction along `W ↦ W/X`. -/
abbrev qcSmallBottomAbelianDirectImage :=
  (qcSmallOpensFunctor S X).sheafPushforwardContinuous AddCommGrpCat.{u}
    (Opens.grothendieckTopology X.obj.obj) (S.qcSite.smallOverTopology X)

/-- The adjunction `h₋₁^{-1} ⊣ h₋₁,*` on abelian sheaves. -/
abbrev qcSmallBottomAbelianAdjunction :
    Sites.abelianInverseImage (qcSmallBottomMorphism S X) ⊣ qcSmallBottomAbelianDirectImage S X :=
  haveI := isRightAdjoint_qcSmallOpensFunctor_sheafPushforwardContinuous.{u, w, u} S X
  abelianInverseImageAdjRestriction (qcSmallOpensFunctor S X)
    (Opens.grothendieckTopology X.obj.obj) (S.qcSite.smallOverTopology X)
    (qcSmallBottomMorphism S X) (qcSmallBottomPushforwardIso S X)

/-- The simplicial semi-representable object `n ↦ {U_n → X}` of the small model. -/
abbrev qcSmallHypercover := qcSmallSemiRep S X U a

/-- The inverse image `a_qc^{-1}` of the augmentation of Section 09X8, on abelian sheaves:
restriction along `V/U_n ↦ V/X`. -/
abbrev qcAugmentationAbelianInverseImage :=
  abelianTotalInverseImageOver S.qcSite.smallPretopology.toGrothendieck
    (S.qcSite.smallEquivalence.functor.obj X) (qcSmallHypercover S X U a)

/-- The direct image `a_qc,*` of the augmentation of Section 09X8, on abelian sheaves. -/
abbrev qcAugmentationAbelianDirectImage :=
  abelianTotalPushforwardOver S.qcSite.smallPretopology.toGrothendieck
    (S.qcSite.smallEquivalence.functor.obj X) (qcSmallHypercover S X U a)

/-- The adjunction `a_qc^{-1} ⊣ a_qc,*` on abelian sheaves. -/
abbrev qcAugmentationAbelianAdjunction :
    qcAugmentationAbelianInverseImage S X U a ⊣ qcAugmentationAbelianDirectImage S X U a :=
  abelianTotalAdjunctionOver _ _ _

/-- Restriction of sheaves of sets along the forgetful functor `(LC_qc/U)_total ⥤ LC_qc/X` is a
right adjoint. -/
instance isRightAdjoint_totalForget_sheafPushforwardContinuous :
    ((totalForget (qcSmallHypercover S X U a)).sheafPushforwardContinuous (Type u)
      (qcSmallTotalTopology S X U a) (S.qcSite.smallOverTopology X)).IsRightAdjoint :=
  ⟨_, ⟨(totalForget (qcSmallHypercover S X U a)).sheafAdjunctionContinuous (Type u)
    (qcSmallTotalTopology S X U a) (S.qcSite.smallOverTopology X)⟩⟩

/-- **Stacks 0DAF on abelian sheaves, inverse images**: `h^{-1} a^{-1} ≅ a_qc^{-1} h₋₁^{-1}`. -/
def qcComparisonSquareAbelianInverseImageIso :
    qcZariskiAbelianInverseImage S X U a ⋙ Sites.abelianInverseImage
        (qcSmallComparisonMorphism S X U a) ≅
      Sites.abelianInverseImage (qcSmallBottomMorphism S X) ⋙
        qcAugmentationAbelianInverseImage S X U a :=
  StacksTag03LR.abelianInverseImageSquareIso _ _ _ _ (qcComparisonSquareInverseImageIso S X U a) ≪≫
    Functor.isoWhiskerLeft _ (Sites.abelianInverseImageIsoSheafPushforwardContinuous
      (totalForget (qcSmallHypercover S X U a)) (qcSmallTotalTopology S X U a)
      (S.qcSite.smallOverTopology X) (qcAugmentationMorphism S X U a) (Iso.refl _))

/-- **Stacks 0DAF on abelian sheaves, direct images**: `h₋₁,* a_qc,* ≅ a_* h_*`, the conjugate of
`qcComparisonSquareAbelianInverseImageIso`. -/
def qcComparisonSquareAbelianDirectImageIso :
    qcAugmentationAbelianDirectImage S X U a ⋙ qcSmallBottomAbelianDirectImage S X ≅
      qcSmallComparisonAbelianDirectImage S X U a ⋙ qcZariskiAbelianDirectImage S X U a :=
  conjugateIsoEquiv ((qcSmallBottomAbelianAdjunction S X).comp
      (qcAugmentationAbelianAdjunction S X U a))
    ((qcZariskiAbelianAdjunction S X U a).comp (qcSmallComparisonAbelianAdjunction S X U a))
    (qcComparisonSquareAbelianInverseImageIso S X U a)

end Adjunctions

/-! ### The higher direct images of `h` at `a_qc^{-1}N`, degree by degree -/

section Components

variable (n : SimplexCategoryᵒᵖ)

/-- Restriction of abelian sheaves on `U_Zar` to simplicial degree `n`. -/
abbrev qcLevelAbelianRestriction :=
  (levelFunctor (qcSimplicialSpace S U) n).sheafPushforwardContinuous AddCommGrpCat.{u}
    (Opens.grothendieckTopology ((qcSimplicialSpace S U).obj n))
    (SimplicialOpen.grothendieckTopology (qcSimplicialSpace S U))

/-- Restriction of abelian sheaves on `(LC_qc/U)_total` to simplicial degree `n`. -/
abbrev qcDegreeAbelianRestriction :=
  (qcSmallTotalIota S X U a n).sheafPushforwardContinuous AddCommGrpCat.{u}
    (qcSmallDegreeTopology S X U a n) (qcSmallTotalTopology S X U a)

/-- The direct image of the comparison of degree `n`, on abelian sheaves. -/
abbrev qcSmallComparisonDegreeAbelianDirectImage :=
  (qcSmallComparisonDegree S X U a n).sheafPushforwardContinuous AddCommGrpCat.{u}
    (Opens.grothendieckTopology ((qcSimplicialSpace S U).obj n)) (qcSmallDegreeTopology S X U a n)

/-- Restriction of abelian sheaves on `U_Zar` to degree `n` preserves finite limits. -/
instance qcLevelAbelianRestriction_preservesFiniteLimits :
    PreservesFiniteLimits (qcLevelAbelianRestriction S U n) :=
  haveI : PreservesLimitsOfSize.{0, 0} (qcLevelAbelianRestriction S U n) :=
    ((levelFunctor (qcSimplicialSpace S U) n).sheafAdjunctionContinuous AddCommGrpCat.{u}
      (Opens.grothendieckTopology ((qcSimplicialSpace S U).obj n))
      (SimplicialOpen.grothendieckTopology (qcSimplicialSpace S U))).rightAdjoint_preservesLimits
  PreservesLimitsOfSize.preservesFiniteLimits _

/-- Restriction of abelian sheaves on `U_Zar` to degree `n` preserves finite colimits. -/
instance qcLevelAbelianRestriction_preservesFiniteColimits :
    PreservesFiniteColimits (qcLevelAbelianRestriction S U n) :=
  haveI : PreservesColimitsOfSize.{0, 0} (qcLevelAbelianRestriction S U n) :=
    ((levelFunctor (qcSimplicialSpace S U) n).sheafAdjunctionCocontinuous AddCommGrpCat.{u}
      (Opens.grothendieckTopology ((qcSimplicialSpace S U).obj n))
      (SimplicialOpen.grothendieckTopology (qcSimplicialSpace S U))).leftAdjoint_preservesColimits
  PreservesColimitsOfSize.preservesFiniteColimits _

/-- Restriction of abelian sheaves on `U_Zar` to degree `n` is additive. -/
instance qcLevelAbelianRestriction_additive : (qcLevelAbelianRestriction S U n).Additive :=
  Functor.additive_of_preserves_binary_products _

/-- Restriction of abelian sheaves on `U_Zar` to degree `n` preserves homology. -/
instance qcLevelAbelianRestriction_preservesHomology :
    (qcLevelAbelianRestriction S U n).PreservesHomology :=
  Functor.preservesHomologyOfExact _

/-- Restriction of abelian sheaves on `(LC_qc/U)_total` to degree `n` preserves finite limits. -/
instance qcDegreeAbelianRestriction_preservesFiniteLimits :
    PreservesFiniteLimits (qcDegreeAbelianRestriction S X U a n) :=
  haveI : PreservesLimitsOfSize.{0, 0} (qcDegreeAbelianRestriction S X U a n) :=
    ((qcSmallTotalIota S X U a n).sheafAdjunctionContinuous AddCommGrpCat.{u}
      (qcSmallDegreeTopology S X U a n) (qcSmallTotalTopology S X U a)).rightAdjoint_preservesLimits
  PreservesLimitsOfSize.preservesFiniteLimits _

/-- Restriction of abelian sheaves on `(LC_qc/U)_total` to degree `n` preserves finite colimits. -/
instance qcDegreeAbelianRestriction_preservesFiniteColimits :
    PreservesFiniteColimits (qcDegreeAbelianRestriction S X U a n) :=
  haveI : PreservesColimitsOfSize.{0, 0} (qcDegreeAbelianRestriction S X U a n) :=
    ((qcSmallTotalIota S X U a n).sheafAdjunctionCocontinuous AddCommGrpCat.{u}
      (qcSmallDegreeTopology S X U a n)
      (qcSmallTotalTopology S X U a)).leftAdjoint_preservesColimits
  PreservesColimitsOfSize.preservesFiniteColimits _

/-- Restriction of abelian sheaves on `(LC_qc/U)_total` to degree `n` is additive. -/
instance qcDegreeAbelianRestriction_additive : (qcDegreeAbelianRestriction S X U a n).Additive :=
  Functor.additive_of_preserves_binary_products _

/-- **Stacks 09WH for `(LC_qc/U)_total`**: restriction to simplicial degree `n` preserves injective
abelian sheaves. -/
instance qcDegreeAbelianRestriction_preservesInjectiveObjects :
    (qcDegreeAbelianRestriction S X U a n).PreservesInjectiveObjects := by
  have key : ∀ (K' : GrothendieckTopology (qcSmallDegree S X U a n))
      (_ : (qcTotalSituation S X U a).componentTopology n.unop = K')
      [(qcSmallTotalIota S X U a n).IsContinuous K' (qcSmallTotalTopology S X U a)],
      ((qcSmallTotalIota S X U a n).sheafPushforwardContinuous AddCommGrpCat.{u} K'
        (qcSmallTotalTopology S X U a)).PreservesInjectiveObjects := by
    intro K' hK _
    subst hK
    exact SimplicialSiteSituation.preservesInjectiveObjects_componentRestrictionAb
      (qcTotalSituation S X U a) n.unop
  exact key _ (componentTopology_eq (S.qcSite.smallOverTopology X) (qcSmallHypercover S X U a)
    n.unop)

/-- Restricting the direct image along `h` to degree `n` is the direct image along the comparison
of degree `n` of the restriction to degree `n`: both are restriction along the two composites of
the square of component inclusions. -/
def qcLevelAbelianSquareIso :
    qcSmallComparisonAbelianDirectImage S X U a ⋙ qcLevelAbelianRestriction S U n ≅
      qcDegreeAbelianRestriction S X U a n ⋙ qcSmallComparisonDegreeAbelianDirectImage S X U a n :=
  haveI := Functor.isContinuous_comp (levelFunctor (qcSimplicialSpace S U) n)
    (qcSmallComparisonFunctor S X U a)
    (Opens.grothendieckTopology ((qcSimplicialSpace S U).obj n))
    (SimplicialOpen.grothendieckTopology (qcSimplicialSpace S U)) (qcSmallTotalTopology S X U a)
  haveI := Functor.isContinuous_comp (qcSmallComparisonDegree S X U a n)
    (qcSmallTotalIota S X U a n) (Opens.grothendieckTopology ((qcSimplicialSpace S U).obj n))
    (qcSmallDegreeTopology S X U a n) (qcSmallTotalTopology S X U a)
  Functor.sheafPushforwardContinuousComp' (Iso.refl _) _ _ _ _ ≪≫
    Functor.sheafPushforwardContinuousIso (qcSmallLevelSquareIso S X U a n).symm _ _ _ ≪≫
    (Functor.sheafPushforwardContinuousComp' (Iso.refl _) _ _ _ _).symm

/-- The localization functor `j_n : (LC_qc/X)/(U_n/X) ⥤ LC_qc/X` of the degree-`n` site. -/
def qcSmallDegreeForget :
    qcSmallDegree S X U a n ⥤ Over (S.qcSite.smallEquivalence.functor.obj X) :=
  sliceForget (qcSmallHypercover S X U a) n

/-- The localization functor `j_n` is continuous. -/
instance qcSmallDegreeForget_isContinuous :
    (qcSmallDegreeForget S X U a n).IsContinuous (qcSmallDegreeTopology S X U a n)
      (S.qcSite.smallOverTopology X) :=
  sliceForget_isContinuous_componentwise (S.qcSite.smallOverTopology X) _ n

/-- The topos of abelian sheaves of the degree-`n` site of `(LC_qc/U)_total` is that of
`LC_qc/U_n`. -/
abbrev qcSmallDegreeAbelianSheafEquivalence :
    Sheaf (qcSmallDegreeTopology S X U a n) AddCommGrpCat.{u} ≌
      Sheaf (S.qcSite.smallOverTopology (U.obj n)) AddCommGrpCat.{u} :=
  SimplicialOver.componentSheafEquivalence (qcSmallSimplicialObject S U)
    (qcSmallAugmentation S X U a) S.qcSite.smallPretopology.toGrothendieck n

/-- The direct image of the comparison of degree `n` is the identification of the degree-`n` topos
with that of `LC_qc/U_n` followed by the direct image of the comparison of `U_n`. -/
def qcSmallComparisonDegreeAbelianPushforwardIso :
    (qcSmallDegreeAbelianSheafEquivalence S X U a n).functor ⋙
        qcSmallBottomAbelianDirectImage S (U.obj n) ≅
      qcSmallComparisonDegreeAbelianDirectImage S X U a n :=
  NatIso.ofComponents (fun _ => (fullyFaithfulSheafToPresheaf _ _).preimageIso (Iso.refl _))
    (fun _ => by
      apply Sheaf.hom_ext
      rfl)

/-- **The higher direct images of the comparison of degree `n` at the restriction of
`a_qc^{-1}h₋₁^{-1}F` vanish**: that restriction is the pullback to `LC_qc/U_n` of
`h₋₁^{-1}F`, which is `h_{U_n}^{-1}` of the pullback `F_n` of `F` to `U_n` (Stacks 0D92), and
`R^p h_{U_n,*} h_{U_n}^{-1} F_n = 0` for `p > 0` (Stacks 0D91). -/
theorem isZero_rightDerived_qcSmallComparisonDegreeAbelianDirectImage
    (F : Sheaf (Opens.grothendieckTopology X.obj.obj) AddCommGrpCat.{u}) (p : ℕ) (hp : 0 < p) :
    IsZero (((qcSmallComparisonDegreeAbelianDirectImage S X U a n).rightDerived p).obj
      ((qcDegreeAbelianRestriction S X U a n).obj ((qcAugmentationAbelianInverseImage S X U a).obj
        ((Sites.abelianInverseImage (qcSmallBottomMorphism S X)).obj F)))) := by
  let E := qcSmallDegreeAbelianSheafEquivalence S X U a n
  let N := (Sites.abelianInverseImage (qcSmallBottomMorphism S X)).obj F
  have : E.functor.Additive := Functor.additive_of_preserves_binary_products _
  have e₁ := Functor.rightDerivedIsoOfSquare E.functor
    (qcSmallComparisonDegreeAbelianDirectImage S X U a n)
    (qcSmallBottomAbelianDirectImage S (U.obj n)) (𝟭 _)
    (Functor.rightUnitor _ ≪≫ (qcSmallComparisonDegreeAbelianPushforwardIso S X U a n).symm) p
  have e₂ := (Functor.sheafPushforwardContinuousComp'
    (eqToIso (ι_comp_totalForget (qcSmallHypercover S X U a) n) :
      qcSmallTotalIota S X U a n ⋙ totalForget (qcSmallHypercover S X U a) ≅
        qcSmallDegreeForget S X U a n) AddCommGrpCat.{u}
    (qcSmallDegreeTopology S X U a n) (qcSmallTotalTopology S X U a)
    (S.qcSite.smallOverTopology X)).app N
  have e₃ := (SimplicialOver.sliceForgetCompComponentSheafEquivalenceIso
    (qcSmallSimplicialObject S U) (qcSmallAugmentation S X U a)
    S.qcSite.smallPretopology.toGrothendieck n).app N
  have e₄ := ((qcSmallComparisonSquareAbIso S (a.app n)).app F).symm
  have hz := isZero_rightDerived_qcSmallOpensPushforward S (U.obj n)
    ((TopCat.Sheaf.pullback AddCommGrpCat.{u}
      ((S.qcSite.inclusion ⋙ locallyQuasiCompactHausdorffToTop).map (a.app n))).obj F) p hp
  exact hz.of_iso (e₁.app _ ≪≫ ((qcSmallBottomAbelianDirectImage S (U.obj n)).rightDerived p).mapIso
    (E.functor.mapIso e₂ ≪≫ e₃ ≪≫ e₄))

/-- **`a_qc^{-1}h₋₁^{-1}F` is right acyclic for `h_*`**: the higher direct images of
`h : Sh((LC_qc/U)_total) → Sh(U_Zar)` at it vanish. Restricted to simplicial degree `n` they are
the higher direct images of the comparison of degree `n` at the restriction, restriction to a
degree being exact and preserving injectives (Stacks 0D97), and those vanish. -/
theorem isZero_rightDerived_qcSmallComparisonAbelianDirectImage
    (F : Sheaf (Opens.grothendieckTopology X.obj.obj) AddCommGrpCat.{u}) (p : ℕ) (hp : 0 < p) :
    IsZero (((qcSmallComparisonAbelianDirectImage S X U a).rightDerived p).obj
      ((qcAugmentationAbelianInverseImage S X U a).obj
        ((Sites.abelianInverseImage (qcSmallBottomMorphism S X)).obj F))) := by
  apply isZero_of_isZero_levelFunctor_sheafPushforwardContinuous_obj
  intro n
  exact (isZero_rightDerived_qcSmallComparisonDegreeAbelianDirectImage S X U a n F p hp).of_iso
    ((Functor.rightDerivedIsoOfSquare (qcDegreeAbelianRestriction S X U a n)
      (qcSmallComparisonAbelianDirectImage S X U a)
      (qcSmallComparisonDegreeAbelianDirectImage S X U a n) (qcLevelAbelianRestriction S U n)
      (qcLevelAbelianSquareIso S X U a n) p).app _)

end Components

/-! ### The higher direct images of `a^{-1}F` along `a : Sh(U_Zar) → Sh(X)` -/

section Acyclicity

/-- The direct image `a_*` on abelian sheaves preserves finite limits. -/
instance qcZariskiAbelianDirectImage_preservesFiniteLimits :
    PreservesFiniteLimits (qcZariskiAbelianDirectImage S X U a) :=
  haveI : PreservesLimitsOfSize.{0, 0} (qcZariskiAbelianDirectImage S X U a) :=
    (qcZariskiAbelianAdjunction S X U a).rightAdjoint_preservesLimits
  PreservesLimitsOfSize.preservesFiniteLimits _

/-- The direct image `a_*` on abelian sheaves is additive. -/
instance qcZariskiAbelianDirectImage_additive :
    (qcZariskiAbelianDirectImage S X U a).Additive :=
  Functor.additive_of_preserves_binary_products _

/-- The direct image `h₋₁,*` on abelian sheaves preserves finite limits. -/
instance qcSmallBottomAbelianDirectImage_preservesFiniteLimits :
    PreservesFiniteLimits (qcSmallBottomAbelianDirectImage S X) :=
  haveI : PreservesLimitsOfSize.{0, 0} (qcSmallBottomAbelianDirectImage S X) :=
    (qcSmallBottomAbelianAdjunction S X).rightAdjoint_preservesLimits
  PreservesLimitsOfSize.preservesFiniteLimits _

/-- The direct image `h₋₁,*` on abelian sheaves is additive. -/
instance qcSmallBottomAbelianDirectImage_additive :
    (qcSmallBottomAbelianDirectImage S X).Additive :=
  Functor.additive_of_preserves_binary_products _

/-- The direct image `h_*` on abelian sheaves preserves finite limits. -/
instance qcSmallComparisonAbelianDirectImage_preservesFiniteLimits :
    PreservesFiniteLimits (qcSmallComparisonAbelianDirectImage S X U a) :=
  haveI : PreservesLimitsOfSize.{0, 0} (qcSmallComparisonAbelianDirectImage S X U a) :=
    (qcSmallComparisonAbelianAdjunction S X U a).rightAdjoint_preservesLimits
  PreservesLimitsOfSize.preservesFiniteLimits _

/-- The direct image `h_*` on abelian sheaves is additive. -/
instance qcSmallComparisonAbelianDirectImage_additive :
    (qcSmallComparisonAbelianDirectImage S X U a).Additive :=
  Functor.additive_of_preserves_binary_products _

/-- The direct image `h_*` on abelian sheaves preserves injective objects. -/
instance qcSmallComparisonAbelianDirectImage_preservesInjectiveObjects :
    (qcSmallComparisonAbelianDirectImage S X U a).PreservesInjectiveObjects :=
  haveI := (Sites.abelianInverseImage_exact (qcSmallComparisonMorphism S X U a)).1
  Functor.preservesInjectiveObjects_of_adjunction_of_preservesMonomorphisms
    (qcSmallComparisonAbelianAdjunction S X U a)

/-- The direct image `a_qc,*` on abelian sheaves preserves finite limits. -/
instance qcAugmentationAbelianDirectImage_preservesFiniteLimits :
    PreservesFiniteLimits (qcAugmentationAbelianDirectImage S X U a) :=
  haveI : PreservesLimitsOfSize.{0, 0} (qcAugmentationAbelianDirectImage S X U a) :=
    (qcAugmentationAbelianAdjunction S X U a).rightAdjoint_preservesLimits
  PreservesLimitsOfSize.preservesFiniteLimits _

/-- The direct image `a_qc,*` on abelian sheaves is additive. -/
instance qcAugmentationAbelianDirectImage_additive :
    (qcAugmentationAbelianDirectImage S X U a).Additive :=
  Functor.additive_of_preserves_binary_products _

/-- The direct image `a_qc,*` on abelian sheaves preserves injective objects. -/
instance qcAugmentationAbelianDirectImage_preservesInjectiveObjects :
    (qcAugmentationAbelianDirectImage S X U a).PreservesInjectiveObjects :=
  haveI : PreservesFiniteLimits (qcAugmentationAbelianInverseImage S X U a) :=
    Functor.preservesFiniteLimits_sheafPushforwardContinuous _ _
      (totalForget (qcSmallHypercover S X U a)) AddCommGrpCat.{u}
  Functor.preservesInjectiveObjects_of_adjunction_of_preservesMonomorphisms
    (qcAugmentationAbelianAdjunction S X U a)

variable {S X U a} in
/-- **The higher direct images of `a^{-1}F` along `a : Sh(U_Zar) → Sh(X)` vanish** when the
augmentation `a : U → X` is a hypercovering of `X` in the quasi-compact site `LC_qc`: for an
abelian sheaf `F` on `X` and `q > 0`, `R^q a_* a^{-1} F = 0`. See the module documentation. -/
theorem isZero_rightDerived_qcZariskiAbelianDirectImage
    (h : IsHypercoveringAugmentation S.qcSite.pretopology U a)
    (F : Sheaf (Opens.grothendieckTopology X.obj.obj) AddCommGrpCat.{u}) (q : ℕ) (hq : 0 < q) :
    IsZero (((qcZariskiAbelianDirectImage S X U a).rightDerived q).obj
      ((qcZariskiAbelianInverseImage S X U a).obj F)) := by
  have hK : IsHypercoveringAugmentation S.qcSite.smallPretopology (qcSmallSimplicialObject S U)
      (qcSmallAugmentation S X U a) :=
    S.qcSite.isHypercoveringAugmentation_smallAugmentation U a h
  have : IsIso (qcAugmentationAbelianAdjunction S X U a).unit :=
    isIso_abelianUnit_augmented' _ _ _ hK
  let N := (Sites.abelianInverseImage (qcSmallBottomMorphism S X)).obj F
  let M := (qcAugmentationAbelianInverseImage S X U a).obj N
  have eG : (qcZariskiAbelianInverseImage S X U a).obj F ≅
      (qcSmallComparisonAbelianDirectImage S X U a).obj M :=
    asIso ((qcSmallComparisonAbelianAdjunction S X U a).unit.app
      ((qcZariskiAbelianInverseImage S X U a).obj F)) ≪≫
      (qcSmallComparisonAbelianDirectImage S X U a).mapIso
        ((qcComparisonSquareAbelianInverseImageIso S X U a).app F)
  have e₃ := Stacks.RightDerivedComp.objIso (qcSmallComparisonAbelianDirectImage S X U a)
    (injectiveResolution M)
    (isZero_rightDerived_qcSmallComparisonAbelianDirectImage S X U a F)
    (qcZariskiAbelianDirectImage S X U a) q
  have hA₁ : (qcSmallComparisonAbelianDirectImage S X U a ⋙
      qcZariskiAbelianDirectImage S X U a).Additive := inferInstance
  have hA₂ : (qcAugmentationAbelianDirectImage S X U a ⋙
      qcSmallBottomAbelianDirectImage S X).Additive := inferInstance
  have e₄ := (@Functor.rightDerivedIsoOfNatIso _ _ _ _ _ _ _ _ _ hA₁ hA₂
    (qcComparisonSquareAbelianDirectImageIso S X U a).symm q).app M
  have e₅ := Stacks.RightDerivedComp.objIso (qcAugmentationAbelianDirectImage S X U a)
    (injectiveResolution M)
    (isZero_rightDerived_abelianTotalPushforwardOver_of_isHypercovering
      S.qcSite.smallPretopology _ _ hK N)
    (qcSmallBottomAbelianDirectImage S X) q
  have e₆ : (qcAugmentationAbelianDirectImage S X U a).obj M ≅ N :=
    (asIso ((qcAugmentationAbelianAdjunction S X U a).unit.app N)).symm
  exact (isZero_rightDerived_qcSmallOpensPushforward S X F q hq).of_iso
    (((qcZariskiAbelianDirectImage S X U a).rightDerived q).mapIso eG ≪≫ e₃.symm ≪≫ e₄ ≪≫ e₅ ≪≫
      ((qcSmallBottomAbelianDirectImage S X).rightDerived q).mapIso e₆)

end Acyclicity


end Stacks.Topology.Simplicial

/-! ### Stacks 09XS -/

namespace Stacks.Topology.Simplicial.ProperHypercovering

open Stacks.Topology Stacks.Topology.Simplicial
open Stacks.CategoryTheory.Hypercovering

attribute [local instance 2000] HomotopyCategory.Plus.instHasPointwiseRightDerivedFunctorQuasiIso

section DerivedUnit

variable (Y : SimplicialObject LocallyQuasiCompactHausdorff.{u})
  (X : LocallyQuasiCompactHausdorff.{u})
  (a : Y ⟶ (SimplicialObject.const LocallyQuasiCompactHausdorff).obj X)

/-- **`a^{-1}F` is right acyclic for `a_*` along a proper hypercovering**: for `U` a simplicial
object of `LC` with an augmentation `a : U → X` which is a proper hypercovering, `F` an abelian
sheaf on `X` and `q > 0`, `R^q a_*(a^{-1}F) = 0`, where `a : Sh(U_Zar) → Sh(X)` is the morphism of
topoi of Stacks 09W4. -/
theorem isZero_rightDerived_abelianDirectImage_of_isHypercovering
    (hyp : MorphismProperty.IsHypercovering properSurjective ⟨Y, X, a⟩)
    (F : Sheaf (Opens.grothendieckTopology (locallyQuasiCompactHausdorffToTop.obj X))
      AddCommGrpCat.{u}) (q : ℕ) (hq : 0 < q) :
    IsZero (((abelianDirectImage Y X a).rightDerived q).obj ((abelianInverseImage Y X a).obj F)) :=
  have hY : ∀ n, (chosenQcSite Y X).qcSite.Contains (Y.obj n) := fun n =>
    chosenQcSite_contains Y X _ (Or.inl ⟨n, rfl⟩)
  have hX : (chosenQcSite Y X).qcSite.Contains X := chosenQcSite_contains Y X _ (Or.inr rfl)
  isZero_rightDerived_qcZariskiAbelianDirectImage
    (isHypercoveringAugmentation_qcLift (chosenQcSite Y X) a hyp hY hX) F q hq

variable [HasDerivedCategory (Sheaf (Opens.grothendieckTopology
    (locallyQuasiCompactHausdorffToTop.obj X)) AddCommGrpCat.{u})]
  [HasDerivedCategory (Sheaf (SimplicialOpen.grothendieckTopology (U Y)) AddCommGrpCat.{u})]

variable {Y X a} in
/-- Let `U` be a simplicial object of the category `LC` of Hausdorff, locally quasi-compact spaces
and let `a : U → X` be an augmentation. If `a : U → X` gives a proper hypercovering of `X`, then
for `K` in `D⁺(X)` the canonical map

`K ⟶ Ra_*(a^{-1}K)`

is an isomorphism, where `a : Sh(U_Zar) → Sh(X)` is the morphism of topoi of Stacks 09W4.

Here `U = Y`; the proper hypercovering condition of Stacks Section 09XA is
`MorphismProperty.IsHypercovering properSurjective`; `D⁺(X)` is the bounded below derived category
of abelian sheaves on `X`, for any model of the derived categories involved; `a^{-1}` is the exact
inverse image of abelian sheaves of the morphism of topoi of Stacks 09W4 applied degreewise, and
`Ra_*` is the right derived functor on bounded below derived categories of its direct image. The
canonical map is the unit at `K` of the adjunction `a^{-1} ⊣ Ra_*` (`derivedAdjunction`).

By Leray's acyclicity lemma (Stacks 015E) the statement reduces to the underived unit
`F ⟶ a_* a^{-1} F` being an isomorphism, which is Stacks 0DAG, and to `R^q a_*(a^{-1}F) = 0` for
`q > 0`, `isZero_rightDerived_abelianDirectImage_of_isHypercovering`, which is the computation of
the source through the diagram of Stacks 0DAF; see the module documentation. -/
@[stacks 09XS]
theorem isIso_derivedAdjunction_unit_app_of_isHypercovering
    (hyp : MorphismProperty.IsHypercovering properSurjective ⟨Y, X, a⟩)
    (K : DerivedCategory.Plus (Sheaf (Opens.grothendieckTopology
      (locallyQuasiCompactHausdorffToTop.obj X)) AddCommGrpCat.{u})) :
    IsIso ((derivedAdjunction Y X a).unit.app K) :=
  isIso_derivedAdjunction_unit_app_of_isZero_rightDerived Y X a hyp
    (isZero_rightDerived_abelianDirectImage_of_isHypercovering Y X a hyp) K

end DerivedUnit

end Stacks.Topology.Simplicial.ProperHypercovering

end
