module

public import StacksFrontier.AlgebraicGeometry.Quot.ProperFlatChartConormalTensor
public import StacksFrontier.AlgebraicGeometry.Spaces.ConormalModulePreimageSections
public import StacksFrontier.AlgebraicGeometry.Quot.ProperFlatDeformationIdealSections
public import StacksFrontier.AlgebraicGeometry.Quot.SpacesDefoThickeningTower

/-!
# The sections `1 ⊗ n` of the prescribed module of the extension problem at a chart

Let `x = (X → Spec A)` be an object of `Spaces'_{fp, flat, proper}` over an affine chart and
`i : Spec A ⟶ T'` a square-zero closed immersion with `T'` affine. The prescribed module
`f^*𝒞_{Spec A/T'}` of the extension problem of [Stacks, Section 08V3] is `𝒪_X ⊗_A N`
(`AlgebraicGeometry.Space.ProperFlatLift.chartPulledBackConormalIso`, for an `A`-module `N`
identified with the ideal `I` of `Spec A ⊆ T'` through `e`). This file computes that
identification on global sections: the section `1 ⊗ n` of `𝒪_X ⊗_A N` is the pullback to `X` of
the class in the conormal module of the function `e(n) ∈ I`. This is the computation on
generators showing that the prescribed module is natural in the thickening (Remark 0D1P).

## Main results

In the namespace `AlgebraicGeometry.Space.ProperFlatLift`:

* `baseRingTensorSection_comp_chartPulledBackConormalIso_inv`: the inverse of
  `chartPulledBackConormalIso` carries the section `1 ⊗ n` to the pulled-back conormal class of
  `e(n)`.
* `modulePullbackGlobalSection_comp_chartPulledBackConormalIso_hom`: `chartPulledBackConormalIso`
  carries the pulled-back conormal class of `e(n)` to the section `1 ⊗ n`.

## References

* [Stacks Project, Tag 04CN](https://stacks.math.columbia.edu/tag/04CN)
* [Stacks Project, Tag 0D3F](https://stacks.math.columbia.edu/tag/0D3F)
* [Stacks Project, Remark 0D1P](https://stacks.math.columbia.edu/tag/0D1P)
-/

@[expose] public noncomputable section

open CategoryTheory

universe u

/- The global instance `Abelian (SheafOfModules.{max u v r w} O)` leaves a stuck universe
constraint against the `𝒪_X`-modules at the universe of the schemes. -/
attribute [-instance] Stacks.Cohomology.SiteModules.moduleSheavesAbelian
  Stacks.Cohomology.SiteModules.moduleSheavesGrothendieck

namespace AlgebraicGeometry.Space

variable (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S) in
/-- Pulling back twice, read on the pullback along a morphism equal to the composite. -/
theorem modulePullbackGlobalSection_comp_modulePullbackCompIsoOfEq_app_hom
    {X Y W : AlgebraicSpaces B S hS} (f : X ⟶ Y) (g : Y ⟶ W) {h : X ⟶ W} (w : f ≫ g = h)
    {M : Modules.{u, u} B S hS W.1 W.2}
    (s : SheafOfModules.unit (structureRingSheaf B S hS W) ⟶ M) :
    modulePullbackGlobalSection B S hS f (modulePullbackGlobalSection B S hS g s) ≫
        ((modulePullbackCompIsoOfEq B S hS f g w).app M).hom =
      modulePullbackGlobalSection B S hS h s := by
  subst w
  simp only [modulePullbackCompIsoOfEq, eqToIso_refl, Iso.trans_refl]
  exact modulePullbackGlobalSection_comp_modulePullbackCompIso_app_hom B S hS f g s


section RangePullback

variable (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)
  {X : AlgebraicSpaces B S hS} {T T' : BigFppfOver B S hS} (f : X ⟶ schemeSpace T) (j : T ⟶ T')
  (hj : AlgebraicGeometry.IsClosedImmersion ((BigFppfOver.toScheme B S hS).map j))
  (hT' : IsAffine ((BigFppfOver.toScheme B S hS).obj T'))
  {h : X ⟶ closedSubspaceRangeSpace B S hS j hj} (w : f ≫ (rangeSchemeSpaceIso B S hS j hj).hom = h)

/-- **The sections `1 ⊗ c` of `𝒪_X ⊗_{Γ(T')} I` are the pulled-back conormal classes**: for
`f : X ⟶ T` and the closed immersion `j : T ⟶ T'`, through any isomorphism `E` equal to the
composite of `(f ≫ (T ≅ Z))^*𝒞 ≅ f^*(T ≅ Z)^*𝒞`, `f^*` of
`AlgebraicGeometry.Space.conormalModuleRangeSchemeIso` and
`AlgebraicGeometry.Space.baseRingTensorModulePullbackCompIso`, the section `1 ⊗ c` is the pullback
to `X` of the class of `c`. The space `X` and the isomorphism `E` are variables, so that a concrete
instance is checked through `hE` rather than by unfolding; all spaces are spelled as
`AlgebraicGeometry.Space.rangeSchemeSpaceIso` spells them. -/
theorem baseRingTensorSection_comp_pullbackRangeConormalIso_inv
    (c : closedSubspaceBaseIdeal B S hS (rangeSubspace B S hS j hj))
    (E : (modulePullback B S hS h).obj (rangeConormalModule B S hS j hj) ≅
      (baseRingTensorModule B S hS X (baseRingHomOfMap (f ≫ schemeSpaceMap j))).obj
        (ModuleCat.of (baseRing B S hS T')
          (closedSubspaceBaseIdeal B S hS (rangeSubspace B S hS j hj))))
    (hE : E = ((modulePullbackCompIsoOfEq B S hS f (rangeSchemeSpaceIso B S hS j hj).hom w).app
        (rangeConormalModule B S hS j hj)).symm ≪≫
      (modulePullback B S hS f).mapIso (conormalModuleRangeSchemeIso B S hS j hj hT') ≪≫
      (baseRingTensorModulePullbackCompIso B S hS f (schemeSpaceMap j)).app _) :
    baseRingTensorSection B S hS X (baseRingHomOfMap (f ≫ schemeSpaceMap j))
        (ModuleCat.of (baseRing B S hS T') (closedSubspaceBaseIdeal B S hS
          (rangeSubspace B S hS j hj))) c ≫ E.inv =
      modulePullbackGlobalSection B S hS h (rangeConormalSection B S hS j hj c) := by
  have h₁ := baseRingTensorSection_comp_pullbackCompIso_inv B S hS f (schemeSpaceMap j)
    (ModuleCat.of (baseRing B S hS T')
      (closedSubspaceBaseIdeal B S hS (rangeSubspace B S hS j hj))) c
  have h₂ := modulePullbackGlobalSection_mapIso_inv B S hS f (rangeSchemeSpaceIso B S hS j hj).hom
    (rangeConormalSection B S hS j hj c) (conormalModuleRangeSchemeIso B S hS j hj hT') _
    (baseRingTensorSection_conormalModuleRangeSchemeIso_inv B S hS j hj hT' c)
  have h₃ := modulePullbackGlobalSection_comp_modulePullbackCompIsoOfEq_app_hom B S hS f
    (rangeSchemeSpaceIso B S hS j hj).hom w (rangeConormalSection B S hS j hj c)
  subst hE
  refine (comp_trans_trans_inv _ _ _ _).trans ?_
  refine (congrArg (fun t => (t ≫ _) ≫ _) h₁).trans ?_
  refine (congrArg (fun t => t ≫ _) h₂).trans ?_
  exact h₃

end RangePullback

section SquareZero

variable (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)
  {X : AlgebraicSpaces B S hS} {T T' : BigFppfOver B S hS} (f : X ⟶ schemeSpace T) (j : T ⟶ T')
  (hj : IsSquareZeroClosedImmersion B S hS j)
  (hT' : IsAffine ((BigFppfOver.toScheme B S hS).obj T'))

/-- The section `c` of the ideal sheaf of `T ⊆ T'`, with the closed subspace spelled as the
square-zero subspace `AlgebraicGeometry.Space.squareZeroSubspace`. -/
abbrev squareZeroIdealSection (c : closedSubspaceBaseIdeal B S hS (rangeSubspace B S hS j hj.1)) :
    SheafOfModules.unit (structureRingSheaf B S hS ((schemeSpaceFunctor B S hS).obj T')) ⟶
      (definingIdealSheaf B S hS ((schemeSpaceFunctor B S hS).obj T')
        (squareZeroSubspace B S hS j hj)).toSheafOfModules :=
  rangeIdealSection B S hS j hj.1 c

/-- The class of `c` in the conormal module of `T ⊆ T'`, with the closed subspace spelled as the
square-zero subspace: the pullback to the closed subspace of the section `c` of its ideal sheaf. -/
abbrev squareZeroConormalSection
    (c : closedSubspaceBaseIdeal B S hS (rangeSubspace B S hS j hj.1)) :
    SheafOfModules.unit (structureRingSheaf B S hS (⟨(squareZeroSubspace B S hS j hj).1.toFunctor,
      (squareZeroSubspace B S hS j hj).2.1⟩ : AlgebraicSpaces B S hS)) ⟶
      conormalModule B S hS ((schemeSpaceFunctor B S hS).obj T') (squareZeroSubspace B S hS j hj) :=
  modulePullbackGlobalSection B S hS
    (subspaceInclusion B S hS ((schemeSpaceFunctor B S hS).obj T') (squareZeroSubspace B S hS j hj))
    (squareZeroIdealSection B S hS j hj c)

/-- The section `c` of the ideal sheaf of `T ⊆ T'`, followed by the inclusion into `𝒪_{T'}`, is
multiplication by the function `c`. -/
theorem squareZeroIdealSection_ι
    (c : closedSubspaceBaseIdeal B S hS (rangeSubspace B S hS j hj.1)) :
    squareZeroIdealSection B S hS j hj c ≫
        (definingIdealSheaf B S hS ((schemeSpaceFunctor B S hS).obj T')
          (squareZeroSubspace B S hS j hj)).ι =
      unitModuleMul B S hS ((schemeSpaceFunctor B S hS).obj T')
        (globalFunctionsOfMap (𝟙 (schemeSpace T')) c.1) := by
  have key : ∀ {Z₁ Z₂ : ClosedSubspaces B S hS (schemeSpace T').1} (e : Z₁ = Z₂),
      eqToHom (congrArg
          (fun Z => (definingIdealSheaf B S hS (schemeSpace T') Z).toSheafOfModules) e) ≫
        (definingIdealSheaf B S hS (schemeSpace T') Z₂).ι =
      (definingIdealSheaf B S hS (schemeSpace T') Z₁).ι := by
    intro _ _ e
    subst e
    exact Category.id_comp _
  refine (Category.assoc _ _ _).trans ?_
  refine (congrArg (_ ≫ ·)
    (key (preimageSubspace_id B S hS (rangeSubspace B S hS j hj.1)))).trans ?_
  exact preimageIdealSection_ι B S hS (𝟙 (schemeSpace T')) (rangeSubspace B S hS j hj.1) c

/-- `AlgebraicGeometry.Space.baseRingTensorSection_comp_pullbackRangeConormalIso_inv` with the
closed subspace spelled as the square-zero subspace. -/
theorem baseRingTensorSection_comp_pullbackSquareZeroConormalIso_inv
    {h : X ⟶ (⟨(squareZeroSubspace B S hS j hj).1.toFunctor,
      (squareZeroSubspace B S hS j hj).2.1⟩ : AlgebraicSpaces B S hS)}
    (w : f ≫ (rangeSchemeSpaceIso B S hS j hj.1).hom = h)
    (c : closedSubspaceBaseIdeal B S hS (rangeSubspace B S hS j hj.1))
    (E : (modulePullback B S hS h).obj
        (conormalModule B S hS ((schemeSpaceFunctor B S hS).obj T')
          (squareZeroSubspace B S hS j hj)) ≅
      (baseRingTensorModule B S hS X (baseRingHomOfMap (f ≫ schemeSpaceMap j))).obj
        (ModuleCat.of (baseRing B S hS T')
          (closedSubspaceBaseIdeal B S hS (rangeSubspace B S hS j hj.1))))
    (hE : E = ((modulePullbackCompIsoOfEq B S hS f (rangeSchemeSpaceIso B S hS j hj.1).hom w).app
        (rangeConormalModule B S hS j hj.1)).symm ≪≫
      (modulePullback B S hS f).mapIso (conormalModuleRangeSchemeIso B S hS j hj.1 hT') ≪≫
      (baseRingTensorModulePullbackCompIso B S hS f (schemeSpaceMap j)).app _) :
    baseRingTensorSection B S hS X (baseRingHomOfMap (f ≫ schemeSpaceMap j))
        (ModuleCat.of (baseRing B S hS T') (closedSubspaceBaseIdeal B S hS
          (rangeSubspace B S hS j hj.1))) c ≫ E.inv =
      modulePullbackGlobalSection B S hS h (squareZeroConormalSection B S hS j hj c) :=
  baseRingTensorSection_comp_pullbackRangeConormalIso_inv B S hS f j hj.1 hT' w c E hE

end SquareZero



namespace ProperFlatLift

open Deformation.Artin

variable {B : BigFppfSite.{u}} {S : Scheme.{u}} {hS : B.Contains S}
  {A : Type u} [CommRing A] {toS : Spec (.of A) ⟶ S} {hA : B.Contains (Spec (.of A))}
  (x : CartesianProperFlatSpaces B S hS)
  (hx : (cartesianProperFlatProjection B S hS).obj x = algebraOver A B S hS toS hA)
  {T' : BigFppfOver B S hS} (i : algebraOver A B S hS toS hA ⟶ T')
  (hi : IsSquareZeroClosedImmersion B S hS i)
  (hT' : IsAffine ((BigFppfOver.toScheme B S hS).obj T'))

/-- `chartPulledBackConormalIdealIso`, with the spaces spelled as
`AlgebraicGeometry.Space.rangeSchemeSpaceIso` spells them. -/
theorem chartPulledBackConormalIdealIso_eq_scheme :
    chartPulledBackConormalIdealIso x hx i hi hT' =
      ((modulePullbackCompIsoOfEq B S hS (chartStructureMap x hx)
          (rangeSchemeSpaceIso B S hS i hi.1).hom
          (specialMap_eq_chartStructureMap_comp x hx i hi).symm).app
        (rangeConormalModule B S hS i hi.1)).symm ≪≫
      (modulePullback B S hS (chartStructureMap x hx)).mapIso
        (conormalModuleRangeSchemeIso B S hS i hi.1 hT') ≪≫
      (baseRingTensorModulePullbackCompIso B S hS (chartStructureMap x hx)
        (schemeSpaceMap i)).app _ :=
  rfl

/-- **The sections `1 ⊗ c` of `𝒪_X ⊗_{Γ(T')} I` are the pulled-back conormal classes**, read
through `chartPulledBackConormalIdealIso`. -/
theorem baseRingTensorSection_comp_chartPulledBackConormalIdealIso_inv
    (c : closedSubspaceBaseIdeal B S hS (rangeSubspace B S hS i hi.1)) :
    baseRingTensorSection B S hS x.obj.obj.left
        (baseRingHomOfMap (chartStructureMap x hx ≫ schemeSpaceMap i))
        (ModuleCat.of (baseRing B S hS T') (closedSubspaceBaseIdeal B S hS
          (rangeSubspace B S hS i hi.1))) c ≫
        (chartPulledBackConormalIdealIso x hx i hi hT').inv =
      modulePullbackGlobalSection B S hS (specialMap i hi x hx)
        (squareZeroConormalSection B S hS i hi c) :=
  baseRingTensorSection_comp_pullbackSquareZeroConormalIso_inv B S hS (chartStructureMap x hx) i hi
    hT' (specialMap_eq_chartStructureMap_comp x hx i hi).symm c
    (chartPulledBackConormalIdealIso x hx i hi hT')
    (chartPulledBackConormalIdealIso_eq_scheme x hx i hi hT')

/-- **The section `1 ⊗ n` of `𝒪_X ⊗_A N` is the pulled-back conormal class of `e(n)`**, read
through `chartPulledBackConormalIso`: for an `A`-module `N` identified by `e` with the ideal of
`Spec A ⊆ T'`, the section `1 ⊗ n` is the pullback to `X` of the class in the conormal module of
the function `e(n)`. -/
theorem baseRingTensorSection_comp_chartPulledBackConormalIso_inv (N : ModuleCat.{u} A)
    (e : (ModuleCat.restrictScalars.{u} (chartThickeningRingHom i)).obj N ≅
      ModuleCat.of (baseRing B S hS T')
        (closedSubspaceBaseIdeal B S hS (rangeSubspace B S hS i hi.1))) (n : N) :
    baseRingTensorSection B S hS x.obj.obj.left (chartBaseRingHom x hx) N n ≫
        (chartPulledBackConormalIso x hx i hi hT' N e).inv =
      modulePullbackGlobalSection B S hS (specialMap i hi x hx)
        (squareZeroConormalSection B S hS i hi (e.hom.hom n)) :=
  CategoryTheory.comp_trans_mapIso_symm_trans_eqToIso_trans_app_inv_eq
    (fun φ => baseRingTensorModule B S hS x.obj.obj.left φ)
    (baseRingHomOfMap_chartStructureMap_comp x hx i)
    (chartPulledBackConormalIdealIso x hx i hi hT') e
    ((baseRingTensorModuleRestrictScalarsIso B S hS _ _ _
      (surjective_chartThickeningRingHom i hi hT')))
    (baseRingTensorSection B S hS x.obj.obj.left (chartBaseRingHom x hx) N n)
    (fun φ => baseRingTensorSection B S hS x.obj.obj.left φ
      ((ModuleCat.restrictScalars.{u} (chartThickeningRingHom i)).obj N) n)
    (baseRingTensorSection B S hS x.obj.obj.left
      (baseRingHomOfMap (chartStructureMap x hx ≫ schemeSpaceMap i))
      (ModuleCat.of (baseRing B S hS T') (closedSubspaceBaseIdeal B S hS
        (rangeSubspace B S hS i hi.1))) (e.hom.hom n))
    _ (baseRingTensorSection_restrictScalarsIso_hom B S hS _ _
      (surjective_chartThickeningRingHom i hi hT') N n)
    (baseRingTensorSection_map B S hS _ _ e.hom n)
    (baseRingTensorSection_comp_chartPulledBackConormalIdealIso_inv x hx i hi hT' (e.hom.hom n))
    (chartPulledBackConormalIso x hx i hi hT' N e)
    (chartPulledBackConormalIso.eq_1 x hx i hi hT' N e)

/-- `baseRingTensorSection_comp_chartPulledBackConormalIso_inv`, read forwards: the pulled-back
conormal class of `e(n)` is carried to `1 ⊗ n`. -/
theorem modulePullbackGlobalSection_comp_chartPulledBackConormalIso_hom (N : ModuleCat.{u} A)
    (e : (ModuleCat.restrictScalars.{u} (chartThickeningRingHom i)).obj N ≅
      ModuleCat.of (baseRing B S hS T')
        (closedSubspaceBaseIdeal B S hS (rangeSubspace B S hS i hi.1))) (n : N) :
    modulePullbackGlobalSection B S hS (specialMap i hi x hx)
        (squareZeroConormalSection B S hS i hi (e.hom.hom n)) ≫
        (chartPulledBackConormalIso x hx i hi hT' N e).hom =
      baseRingTensorSection B S hS x.obj.obj.left (chartBaseRingHom x hx) N n :=
  ((Iso.comp_inv_eq _).1
    (baseRingTensorSection_comp_chartPulledBackConormalIso_inv x hx i hi hT' N e n)).symm

end ProperFlatLift

end AlgebraicGeometry.Space

end
