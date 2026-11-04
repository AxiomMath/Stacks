module

public import StacksFrontier.CategoryTheory.Sites.Simplicial.AugmentationComponentInverseImageAb
public import StacksFrontier.CategoryTheory.Sites.Simplicial.CohomologySpectralSequenceTagSheaf
public import StacksFrontier.CategoryTheory.Sites.Simplicial.HypercoveringBySimplicialObjectDerivedDescent
public import StacksFrontier.CategoryTheory.Sites.Simplicial.HypercoveringBySimplicialObjectTotalSite
public import StacksFrontier.CategoryTheory.Sites.Simplicial.HypercoveringSituationDescentAb
public import StacksFrontier.CategoryTheory.Sites.UniverseLiftDerived

/-!
# The components of the total site of a simplicial object over an object

Let `C` be a site, `X` an object of `C`, `U` a simplicial object of `C` and `a : U → X` an
augmentation. The total site `(C/K)_total` of the simplicial semi-representable object
`K_n = {U_n → X}` of Stacks 09X8 has as component in simplicial degree `n` the site `C/K_n`,
which is the iterated slice `(C/X)/(U_n/X)`, that is the slice `C/U_n`. This file makes that
identification on cohomology: for an abelian sheaf `E` on `C/X`, the restriction to the component
of degree `p` of `a⁻¹E` has the cohomology of the restriction of `E` along `Over.map a_p`:

`H^q(C/K_p, (a⁻¹E)_p) ≅ H^q(C/U_p, E|_{U_p})`,

naturally in `E`. This is what the first page of the spectral sequence of Stacks 09WJ of the
total site computes, written on the slices `C/U_p` of the source.

## Main definitions

* `CategoryTheory.SimplicialOver.componentOverEquivalence`: the component `C/K_n` is the slice
  `C/U_n`, as an equivalence of categories whose inverse is `toComponentOver`.
* `CategoryTheory.SimplicialOver.componentRightDerivedIso`: cohomology on the component is
  cohomology on the slice, along that equivalence.
* `CategoryTheory.SimplicialSemiRepresentable.componentCohomologyInverseImageIso`: the first-page
  term of Stacks 09WJ for `a⁻¹E` is the cohomology of `E|_{U_p}`.
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits Opposite Simplicial SemiRepresentable
open Stacks.CategoryTheory.Hypercovering

universe w u

namespace CategoryTheory.SimplicialOver

variable {C : Type u} [SmallCategory C] [HasPullbacks C] {X : C} (U : SimplicialObject C)
  (a : U ⟶ (SimplicialObject.const C).obj X)

/-- The unit of the comparison of the component `C/K_n` with the slice `C/U_n`. -/
def componentOverUnitIso (n : SimplexCategoryᵒᵖ) :
    𝟭 (ComponentOver ((associatedSimplicialObject.{u} U a).obj n)) ≅
      fromComponentOver U a n ⋙ toComponentOver U a n :=
  Sigma.natIso fun ⟨⟩ =>
    Functor.rightUnitor _ ≪≫ (Functor.leftUnitor _).symm ≪≫
      Functor.isoWhiskerRight (Over.iteratedSliceEquiv ((Over.lift U a).obj n)).unitIso
        (Sigma.incl (C := fun _ : PUnit.{u + 1} ↦ Over ((Over.lift U a).obj n)) PUnit.unit) ≪≫
      Functor.isoWhiskerRight (Sigma.inclDesc
        (fun _ ↦ Over.iteratedSliceForward ((Over.lift U a).obj n)) PUnit.unit).symm
        (toComponentOver U a n)

/-- **The component `C/K_n` of the total site is the slice `C/U_n`**: it is the single slice
`(C/X)/(U_n/X)`, which is `C/U_n` by the iterated slice equivalence. -/
def componentOverEquivalence (n : SimplexCategoryᵒᵖ) :
    ComponentOver ((associatedSimplicialObject.{u} U a).obj n) ≌ Over (U.obj n) :=
  Equivalence.mk (fromComponentOver U a n) (toComponentOver U a n)
    (componentOverUnitIso U a n) (eqToIso (toComponentOver_comp_fromComponentOver U a n))

section Site

variable (J : GrothendieckTopology C)

/-- The inverse `C/U_n ⥤ C/K_n` of `componentOverEquivalence` is a dense subsite. -/
instance componentOverEquivalence_inverse_isDenseSubsite (n : SimplexCategoryᵒᵖ) :
    (componentOverEquivalence U a n).inverse.IsDenseSubsite (J.over (U.obj n))
      (componentwiseTopology (J.over X) ((associatedSimplicialObject.{u} U a).obj n)) := by
  have : (componentOverEquivalence U a n).inverse.IsCocontinuous (J.over (U.obj n))
      (componentwiseTopology (J.over X) ((associatedSimplicialObject.{u} U a).obj n)) :=
    toComponentOver_isCocontinuous U a J n
  have : (componentOverEquivalence U a n).functor.IsCocontinuous
      (componentwiseTopology (J.over X) ((associatedSimplicialObject.{u} U a).obj n))
      (J.over (U.obj n)) :=
    fromComponentOver_isCocontinuous U a J n
  exact Equivalence.isDenseSubsite_inverse_of_isCocontinuous _ _ _

/-- The equivalence of the topoi of `C/K_n` and `C/U_n`, abelian sheaves. -/
abbrev componentSheafEquivalence (n : SimplexCategoryᵒᵖ) :
    Sheaf (componentwiseTopology (J.over X) ((associatedSimplicialObject.{u} U a).obj n))
        AddCommGrpCat.{u} ≌ Sheaf (J.over (U.obj n)) AddCommGrpCat.{u} :=
  (componentOverEquivalence U a n).sheafCongr _ _ _

/-- Global sections of abelian sheaves on the component `C/K_n` form an additive functor. -/
instance additive_componentGlobalSections (n : SimplexCategoryᵒᵖ) :
    (Sheaf.Γ (componentwiseTopology (J.over X) ((associatedSimplicialObject.{u} U a).obj n))
      AddCommGrpCat.{u}).Additive :=
  Functor.additive_of_preserves_binary_products _

/-- Global sections of abelian sheaves on the slice `C/Y` form an additive functor. -/
instance additive_overGlobalSections (Y : C) :
    (Sheaf.Γ (J.over Y) AddCommGrpCat.{u}).Additive :=
  Functor.additive_of_preserves_binary_products _

/-- Global sections on the component `C/K_n` are global sections on the slice `C/U_n`. -/
def componentGlobalSectionsIso (n : SimplexCategoryᵒᵖ) :
    Sheaf.Γ (componentwiseTopology (J.over X) ((associatedSimplicialObject.{u} U a).obj n))
        AddCommGrpCat.{u} ≅
      (componentSheafEquivalence U a J n).functor ⋙
        Sheaf.Γ (J.over (U.obj n)) AddCommGrpCat.{u} :=
  have hT := (Over.mkIdTerminal (X := U.obj n)).isTerminalObj
    (componentOverEquivalence U a n).inverse
  haveI := hT.hasTerminal
  Sheaf.ΓNatIsoSheafSections _ _ hT ≪≫
    (NatIso.ofComponents (fun _ => Iso.refl _) (fun _ => rfl) :
      (sheafSections (componentwiseTopology (J.over X) ((associatedSimplicialObject.{u} U a).obj n))
          AddCommGrpCat.{u}).obj
          (op ((componentOverEquivalence U a n).inverse.obj (Over.mk (𝟙 (U.obj n))))) ≅
        (componentSheafEquivalence U a J n).functor ⋙
          (sheafSections (J.over (U.obj n)) AddCommGrpCat.{u}).obj (op (Over.mk (𝟙 (U.obj n))))) ≪≫
    Functor.isoWhiskerLeft (componentSheafEquivalence U a J n).functor
      (Sheaf.ΓNatIsoSheafSections (J.over (U.obj n)) AddCommGrpCat.{u}
        (Over.mkIdTerminal (X := U.obj n))).symm

/-- **Cohomology on the component `C/K_n` is cohomology on the slice `C/U_n`.** -/
def componentRightDerivedIso (n : SimplexCategoryᵒᵖ) (q : ℕ) :
    (Sheaf.Γ (componentwiseTopology (J.over X) ((associatedSimplicialObject.{u} U a).obj n))
        AddCommGrpCat.{u}).rightDerived q ≅
      (componentSheafEquivalence U a J n).functor ⋙
        (Sheaf.Γ (J.over (U.obj n)) AddCommGrpCat.{u}).rightDerived q :=
  have : (componentSheafEquivalence U a J n).functor.Additive :=
    Functor.additive_of_preserves_binary_products _
  (Functor.rightUnitor _).symm ≪≫
    Functor.rightDerivedIsoOfSquare (componentSheafEquivalence U a J n).functor _ _ (𝟭 _)
      (Functor.rightUnitor _ ≪≫ componentGlobalSectionsIso U a J n) q

/-- The localization functor `j_n : C/K_n ⥤ C/X` is continuous for the componentwise topology. -/
instance sliceForget_associated_isContinuous (n : SimplexCategoryᵒᵖ) :
    (SimplicialSemiRepresentable.sliceForget (associatedSimplicialObject.{u} U a) n).IsContinuous
      (componentwiseTopology (J.over X) ((associatedSimplicialObject.{u} U a).obj n)) (J.over X) :=
  SimplicialSemiRepresentable.sliceForget_isContinuous_componentwise (J.over X) _ n

/-- Restricting along the localization functor of the component `C/K_n` and then reading the
result on `C/U_n` is restricting along `Over.map a_n`. -/
def sliceForgetCompComponentSheafEquivalenceIso (n : SimplexCategoryᵒᵖ) :
    (SimplicialSemiRepresentable.sliceForget (associatedSimplicialObject.{u} U a)
          n).sheafPushforwardContinuous AddCommGrpCat.{u}
        (componentwiseTopology (J.over X) ((associatedSimplicialObject.{u} U a).obj n))
        (J.over X) ⋙ (componentSheafEquivalence U a J n).functor ≅
      (Over.map (augmentationApp U a n)).sheafPushforwardContinuous AddCommGrpCat.{u}
        (J.over (U.obj n)) (J.over X) :=
  NatIso.ofComponents (fun _ => (fullyFaithfulSheafToPresheaf _ _).preimageIso (Iso.refl _))
    (fun _ => rfl)

end Site

end CategoryTheory.SimplicialOver

namespace CategoryTheory.SimplicialSemiRepresentable

variable {C : Type u} [SmallCategory C] [HasPullbacks C] (P : Pretopology C) {X : C}
  (U : SimplicialObject C) (a : U ⟶ (SimplicialObject.const C).obj X)

/-- Cohomology of the restriction along the localization functor `j_n : C/K_n ⥤ C/X`, for any
topology on `C/K_n` equal to the componentwise one, is cohomology on the slice `C/U_n` of the
restriction along `Over.map a_n`. -/
def sliceForgetRightDerivedIsoOfEq (n : SimplexCategoryᵒᵖ)
    (K' : GrothendieckTopology (ComponentOver ((associatedSimplicialObject.{u} U a).obj n)))
    (hK' : K' = componentwiseTopology (P.toGrothendieck.over X)
      ((associatedSimplicialObject.{u} U a).obj n))
    [(sliceForget (associatedSimplicialObject.{u} U a) n).IsContinuous K'
      (P.toGrothendieck.over X)]
    (hΓ : (Sheaf.Γ K' AddCommGrpCat.{u}).Additive) (q : ℕ) :
    (sliceForget (associatedSimplicialObject.{u} U a) n).sheafPushforwardContinuous
        AddCommGrpCat.{u} K' (P.toGrothendieck.over X) ⋙
        (Sheaf.Γ K' AddCommGrpCat.{u}).rightDerived q ≅
      (Over.map (SimplicialOver.augmentationApp U a n)).sheafPushforwardContinuous
          AddCommGrpCat.{u} (P.toGrothendieck.over (U.obj n)) (P.toGrothendieck.over X) ⋙
        (Sheaf.Γ (P.toGrothendieck.over (U.obj n)) AddCommGrpCat.{u}).rightDerived q := by
  subst hK'
  exact Functor.isoWhiskerLeft _
      (SimplicialOver.componentRightDerivedIso U a P.toGrothendieck n q) ≪≫
    (Functor.associator _ _ _).symm ≪≫
    Functor.isoWhiskerRight
      (SimplicialOver.sliceForgetCompComponentSheafEquivalenceIso U a P.toGrothendieck n) _

/-- Global sections of abelian sheaves on the component of degree `n` of the total site form an
additive functor. -/
instance additive_totalSituationComponentGlobalSections (n : SimplexCategory) :
    (Sheaf.Γ ((totalSituation P U a).componentTopology n) AddCommGrpCat.{u}).Additive :=
  Functor.additive_of_preserves_binary_products _

/-- The localization functor `j_n : C/K_n ⥤ C/X` is continuous for the component topology of the
total site. -/
instance sliceForget_totalSituation_isContinuous (n : SimplexCategory) :
    (sliceForget (associatedSimplicialObject.{u} U a) (op n)).IsContinuous
      ((totalSituation P U a).componentTopology n) (P.toGrothendieck.over X) :=
  sliceForget_isContinuous (P.toGrothendieck.over X) (associatedSimplicialObject.{u} U a) n

/-- The abelian inverse image along the component augmentation of degree `n` of the total site
of `K_n = {U_n → X}` is restriction along the localization functor `j_n` (Stacks 0D8B). -/
def componentInverseImageAbIso (n : SimplexCategory) :
    SimplicialSiteSituation.Augmentation.componentInverseImageAb (totalSituation P U a)
        (Cat.of (Over X)) (P.toGrothendieck.over X) (augmentationAugmented P U a) n ≅
      (sliceForget (associatedSimplicialObject.{u} U a) (op n)).sheafPushforwardContinuous
        AddCommGrpCat.{u} ((totalSituation P U a).componentTopology n)
        (P.toGrothendieck.over X) :=
  letI : ((sliceForget (associatedSimplicialObject.{u} U a) (op n)).sheafPushforwardContinuous
      (Type u) ((totalSituation P U a).componentTopology n)
        (P.toGrothendieck.over X)).IsRightAdjoint :=
    (Functor.sheafPullbackConstruction.sheafAdjunctionContinuous
      (sliceForget (associatedSimplicialObject.{u} U a) (op n)) (Type u)
      ((totalSituation P U a).componentTopology n) (P.toGrothendieck.over X)).isRightAdjoint
  Sites.abelianInverseImageIsoSheafPushforwardContinuous
    (sliceForget (associatedSimplicialObject.{u} U a) (op n))
    ((totalSituation P U a).componentTopology n) (P.toGrothendieck.over X) _
    (componentInverseImageIso (P.toGrothendieck.over X) (associatedSimplicialObject.{u} U a) n)

/-- **The first page of the spectral sequence of the total site, for an inverse image.** For an
abelian sheaf `E` on `C/X`, the term `E_1^{p,q} = H^q(C_p, (a⁻¹E)_p)` of the spectral sequence of
Stacks 09WJ of the total site of `K_n = {U_n → X}` is the cohomology `H^q(C/U_p, E|_{U_p})` of the
restriction of `E` along `Over.map a_p`, naturally in `E`. -/
def componentCohomologyInverseImageIso (p q : ℕ) :
    SimplicialSiteSituation.Augmentation.totalInverseImageAb (totalSituation P U a)
        (Cat.of (Over X)) (P.toGrothendieck.over X) (augmentationAugmented P U a) ⋙
        (totalSituation P U a).componentCohomologyFunctor ⦋p⦌ q ≅
      (Over.map (SimplicialOver.augmentationApp U a (op ⦋p⦌))).sheafPushforwardContinuous
          AddCommGrpCat.{u} (P.toGrothendieck.over (U.obj (op ⦋p⦌))) (P.toGrothendieck.over X) ⋙
        (Sheaf.Γ (P.toGrothendieck.over (U.obj (op ⦋p⦌))) AddCommGrpCat.{u}).rightDerived q :=
  (Functor.associator _ _ _).symm ≪≫
    Functor.isoWhiskerRight
      (SimplicialSiteSituation.componentRestrictionAbInverseImageNatIso' (totalSituation P U a)
        (Cat.of (Over X)) (P.toGrothendieck.over X) (augmentationAugmented P U a) ⦋p⦌) _ ≪≫
    Functor.isoWhiskerRight (componentInverseImageAbIso P U a ⦋p⦌) _ ≪≫
    sliceForgetRightDerivedIsoOfEq P U a (op ⦋p⦌) ((totalSituation P U a).componentTopology ⦋p⦌)
      (componentTopology_eq (P.toGrothendieck.over X) (associatedSimplicialObject.{u} U a) ⦋p⦌)
      (additive_totalSituationComponentGlobalSections P U a ⦋p⦌) q

end CategoryTheory.SimplicialSemiRepresentable

end
