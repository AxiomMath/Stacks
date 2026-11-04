module

public import StacksFrontier.CategoryTheory.Sites.Cohomology.DerivedPullback.MixedDerivedTensor.LinearDerivedMixedTensor
public import StacksFrontier.CategoryTheory.Sites.Cohomology.DerivedPullback.MixedDerivedTensor.CoefficientChangeExtendScalars

/-!
# The derived tensor product over a smaller sheaf of rings, with values in `D(O)`

Let `α : R ⟶ O` be a map of sheaves of commutative rings on a site `(C, J)`.  For a sheaf `H`
of `O`-modules and a sheaf `N` of `R`-modules the tensor product `H ⊗_R N` (sections
`H(U) ⊗_{R(U)} N(U)`, sheafified) is a sheaf of `O`-modules through `H`.  This file derives
that bifunctor: it constructs

`- ⊗^L_R - : D(O) ⥤ D(R) ⥤ D(O)`

computed by K-flat resolutions with flat terms of the second factor, and records that such a
resolution computes it.

The two inputs are the cancellation of a base change `H ⊗_R N ≅ H ⊗_O (O ⊗_R N)` of sheaves
of `O`-modules, natural in both variables, and Stacks 0G7E and 06YY at the change of
coefficient rings `α`: the extension of scalars `O ⊗_R N` of a K-flat complex with flat terms
is K-flat, and it carries quasi-isomorphisms between such complexes to quasi-isomorphisms.  So
`Tot(H ⊗_R N) ≅ Tot(H ⊗_O (O ⊗_R N))` inverts quasi-isomorphisms in `H` and is invariant under
quasi-isomorphisms of `N`, which is what the one-sided descent
`CochainComplex.KFlatBifunctor.derivedBifunctorOfRight` consumes.

## Main definitions

* `Stacks.Cohomology.MixedDerivedTensor.coeffMixedDerivedTensor`: **the derived tensor product
  over `R`**, `D(O) ⥤ D(R) ⥤ D(O)`.
* `Stacks.Cohomology.MixedDerivedTensor.coeffMixedDerivedTensorComparison`: its value at a
  complex `H` of `O`-modules and a K-flat complex `N` of `R`-modules with flat terms is the
  class of `Tot(H ⊗_R N)`.

## Main results

* `Stacks.Cohomology.MixedDerivedTensor.coeffMixedDerivedTensorComparison_naturality`: the
  comparison is natural in both complexes.

## Implementation notes

The site-presented construction `Stacks.Cohomology.MixedDerivedTensor.mixedDerivedTensor` is
the case `α = f⁻¹O' ⟶ O` of a morphism of ringed sites; it reads the extension of scalars as
the pullback along the ring-theoretic half of the factorization of that morphism.  Here the
extension of scalars is `Stacks.FlatChangeOfRings.extendScalars α` itself, the functor the
cancellation of a base change is stated with, so nothing in this file mentions a morphism of
ringed topoi other than the change of coefficients along `α`, whose underlying functor is the
identity of the site.

## References

* [The Stacks Project, Tag 08I6](https://stacks.math.columbia.edu/tag/08I6)
* [The Stacks Project, Tag 06YU](https://stacks.math.columbia.edu/tag/06YU)
* [The Stacks Project, Tag 0G7E](https://stacks.math.columbia.edu/tag/0G7E)
* [The Stacks Project, Tag 06YY](https://stacks.math.columbia.edu/tag/06YY)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry
open Stacks.Cohomology.DerivedPullbackPushforwardAdjunction
open Stacks.Sheaves.DerivedPullback Stacks.Sheaves.DerivedPullback.KFlatPullback

namespace Stacks.Cohomology.MixedDerivedTensor

universe u

attribute [local instance] HasDerivedCategory.standard

variable {C : Type u} [SmallCategory C] {J : GrothendieckTopology C}
  [J.HasSheafCompose (forget₂ CommRingCat.{u} RingCat.{u})]
  [HasSheafify J AddCommGrpCat.{u}] [J.WEqualsLocallyBijective AddCommGrpCat.{u}]
  {R O : Sheaf J CommRingCat.{u}} (α : R ⟶ O)

/-! ### The cancellation of a base change, in both variables -/

section Underived

/-- **`H ⊗_R N ≅ H ⊗_O (O ⊗_R N)`** as sheaves of `O`-modules, for a sheaf `H` of `O`-modules
and a sheaf `N` of `R`-modules. -/
def coeffMixedTensorExtendIso
    (H : SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf O))
    (N : SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf R)) :
    ((Stacks.MixedBaseChange.mixedSheafTensor α).obj H).obj N ≅
      ((Stacks.SheafOfModules.Tensor.sheafTensor.{u, u, u, u, u} O).obj H).obj
        ((Stacks.FlatChangeOfRings.extendScalars α).obj N) :=
  ((Stacks.MixedBaseChange.mixedSheafBaseChangeNatIso α N).app H).symm

/-- `coeffMixedTensorExtendIso` is natural in the sheaf of `O`-modules. -/
lemma coeffMixedTensorExtendIso_naturality_fst
    {H H' : SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf O)} (φ : H ⟶ H')
    (N : SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf R)) :
    ((Stacks.MixedBaseChange.mixedSheafTensor α).map φ).app N ≫
        (coeffMixedTensorExtendIso α H' N).hom =
      (coeffMixedTensorExtendIso α H N).hom ≫
        ((Stacks.SheafOfModules.Tensor.sheafTensor.{u, u, u, u, u} O).map φ).app
          ((Stacks.FlatChangeOfRings.extendScalars α).obj N) :=
  (Stacks.MixedBaseChange.mixedSheafBaseChangeNatIso α N).inv.naturality φ

/-- `coeffMixedTensorExtendIso` is natural in the sheaf of `R`-modules. -/
lemma coeffMixedTensorExtendIso_naturality_snd
    (H : SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf O))
    {N N' : SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf R)} (v : N ⟶ N') :
    ((Stacks.MixedBaseChange.mixedSheafTensor α).obj H).map v ≫
        (coeffMixedTensorExtendIso α H N').hom =
      (coeffMixedTensorExtendIso α H N).hom ≫
        ((Stacks.SheafOfModules.Tensor.sheafTensor.{u, u, u, u, u} O).obj H).map
          ((Stacks.FlatChangeOfRings.extendScalars α).map v) :=
  Stacks.MixedBaseChange.conj_square
    ((Stacks.MixedBaseChange.mixedSheafBaseChangeNatIso α N).app H)
    ((Stacks.MixedBaseChange.mixedSheafBaseChangeNatIso α N').app H)
    (Stacks.MixedBaseChange.mixedSheafBaseChange_naturality_snd α v H).symm

end Underived

/-! ### The derived tensor product over `R` -/

section Derived

variable [(Stacks.SheafOfModules.Tensor.sheafTensor.{u, u, u, u, u} O).Additive]
  [∀ M, ((Stacks.SheafOfModules.Tensor.sheafTensor.{u, u, u, u, u} O).obj M).Additive]
  [∀ (A B : CochainComplex (SheafOfModules.{u}
      (Stacks.SheafOfModules.Tensor.ringSheaf O)) ℤ),
    HomologicalComplex.HasMapBifunctor A B
      (Stacks.SheafOfModules.Tensor.sheafTensor.{u, u, u, u, u} O) (ComplexShape.up ℤ)]

/-- **`Tot(H ⊗_R N) ≅ Tot(H ⊗_O (O ⊗_R N))`**, for a complex `H` of `O`-modules and a complex
`N` of `R`-modules: `coeffMixedTensorExtendIso` in each bidegree. -/
def coeffMixedTotalExtendIso
    (K : CochainComplex (SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf O)) ℤ)
    (N : CochainComplex (SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf R)) ℤ) :
    HomologicalComplex.mapBifunctor K N (Stacks.MixedBaseChange.mixedSheafTensor α)
        (ComplexShape.up ℤ) ≅
      HomologicalComplex.mapBifunctor K
        ((Stacks.Cohomology.CoefficientChange.extendScalarsComplex α).obj N)
        (Stacks.SheafOfModules.Tensor.sheafTensor.{u, u, u, u, u} O) (ComplexShape.up ℤ) :=
  transportTotalIso (Stacks.MixedBaseChange.mixedSheafTensor α)
    (Stacks.SheafOfModules.Tensor.sheafTensor.{u, u, u, u, u} O) (𝟭 _)
    (Stacks.FlatChangeOfRings.extendScalars α) (coeffMixedTensorExtendIso α)
    (fun u e ↦ coeffMixedTensorExtendIso_naturality_fst α u e)
    (fun a _ _ v ↦ coeffMixedTensorExtendIso_naturality_snd α a v) K N

/-- `coeffMixedTotalExtendIso` is natural in both complexes. -/
lemma coeffMixedTotalExtendIso_hom_naturality
    {K K' : CochainComplex (SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf O)) ℤ}
    {N N' : CochainComplex (SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf R)) ℤ}
    (u : K ⟶ K') (v : N ⟶ N') :
    HomologicalComplex.mapBifunctorMap u v (Stacks.MixedBaseChange.mixedSheafTensor α)
          (ComplexShape.up ℤ) ≫
        (coeffMixedTotalExtendIso α K' N').hom =
      (coeffMixedTotalExtendIso α K N).hom ≫
        HomologicalComplex.mapBifunctorMap u
          ((Stacks.Cohomology.CoefficientChange.extendScalarsComplex α).map v)
          (Stacks.SheafOfModules.Tensor.sheafTensor.{u, u, u, u, u} O) (ComplexShape.up ℤ) :=
  transportTotalIso_hom_naturality (Stacks.MixedBaseChange.mixedSheafTensor α)
    (Stacks.SheafOfModules.Tensor.sheafTensor.{u, u, u, u, u} O) (𝟭 _)
    (Stacks.FlatChangeOfRings.extendScalars α) (coeffMixedTensorExtendIso α)
    (fun u e ↦ coeffMixedTensorExtendIso_naturality_fst α u e)
    (fun a _ _ v ↦ coeffMixedTensorExtendIso_naturality_snd α a v) u v

/-- **The tensor product over `R` with a K-flat complex of `R`-modules with flat terms is
K-flat in the first variable.**  `Tot(G ⊗_R N) ≅ Tot(G ⊗_O (O ⊗_R N))`, and `O ⊗_R N` is K-flat
over `O` by Stacks 0G7E at the change of coefficients. -/
theorem coeffModelsRight_le :
    IsKFlat (Y := Stacks.Cohomology.ringedTopos J R) ≤
      CochainComplex.KFlatBifunctor.kFlatObjects (Stacks.MixedBaseChange.mixedSheafTensor α) := by
  intro N hN G hG n
  exact (Stacks.Cohomology.CoefficientChange.kFlat_extendScalarsComplex α N.as hN.1 hN.2 G hG
    n).of_iso (coeffMixedTotalExtendIso α G N.as).symm

/-- A square of isomorphisms commuting in the source of a functor gives one in the target, so
the right side is invertible after applying the functor iff the left side is. -/
private theorem isIso_map_iff_of_square {C D : Type*} [Category C] [Category D] (F : C ⥤ D)
    {A B A' B' : C} {a : A ⟶ A'} {b : B ⟶ B'} (e : A ≅ B) (e' : A' ≅ B')
    (h : a ≫ e'.hom = e.hom ≫ b) : IsIso (F.map a) ↔ IsIso (F.map b) :=
  have h' := F.congr_map h
  ⟨fun _ ↦ isIso_of_square (F.mapIso e) (F.mapIso e') (by simpa using h'),
    fun _ ↦ isIso_of_square' (F.mapIso e) (F.mapIso e') (by simpa using h')⟩

/-- **The tensor product over `R` with a fixed complex of `O`-modules carries
quasi-isomorphisms between K-flat complexes of `R`-modules with flat terms to
quasi-isomorphisms.**  After `Tot(- ⊗_R -) ≅ Tot(- ⊗_O (O ⊗_R -))` this is the invariance of the
one-sided K-flat comparison of Stacks 06YU over `O`, because extension of scalars carries such a
quasi-isomorphism to a quasi-isomorphism of K-flat complexes (Stacks 06YY at the change of
coefficients). -/
theorem coeffQuasiIso_mixedTensor_map
    (K : CochainComplex (SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf O)) ℤ)
    {N N' : CochainComplex (SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf R)) ℤ}
    (b : N ⟶ N')
    (hN : IsKFlat (Y := Stacks.Cohomology.ringedTopos J R)
      ((HomotopyCategory.quotient _ (ComplexShape.up ℤ)).obj N))
    (hN' : IsKFlat (Y := Stacks.Cohomology.ringedTopos J R)
      ((HomotopyCategory.quotient _ (ComplexShape.up ℤ)).obj N'))
    (hb : QuasiIso b) :
    QuasiIso ((((Stacks.MixedBaseChange.mixedSheafTensor α).map₂HomologicalComplex
      (ComplexShape.up ℤ) (ComplexShape.up ℤ) (ComplexShape.up ℤ)).obj K).map b) := by
  have hQb : IsIso (DerivedCategory.Q.map b) :=
    (DerivedCategory.isIso_Q_map_iff_quasiIso _ _).2 hb
  have hp : IsIso (DerivedCategory.Q.map
      ((pullbackComplex (RingedToposSiteHom.coefficientChange.{u, u, u} J α)).map b)) :=
    isIso_of_square _ _ (flatPullbackIso_naturality
      (RingedToposSiteHom.coefficientChange.{u, u, u} J α) (Functor.isMorphismOfSites_id J) b
      hN.1 hN'.1 hN.2 hN'.2)
  have he : IsIso (DerivedCategory.Q.map
      ((Stacks.Cohomology.CoefficientChange.extendScalarsComplex α).map b)) :=
    (isIso_map_iff_of_square DerivedCategory.Q
      ((Stacks.Cohomology.CoefficientChange.pullbackComplexIsoExtendScalars α).app N)
      ((Stacks.Cohomology.CoefficientChange.pullbackComplexIsoExtendScalars α).app N')
      ((Stacks.Cohomology.CoefficientChange.pullbackComplexIsoExtendScalars α).hom.naturality
        b)).1 hp
  have hL := Stacks.Cohomology.CoefficientChange.kFlat_extendScalarsComplex α N hN.1 hN.2
  have hL' := Stacks.Cohomology.CoefficientChange.kFlat_extendScalarsComplex α N' hN'.1 hN'.2
  have hT : IsIso (DerivedCategory.Q.map (HomologicalComplex.mapBifunctorMap (𝟙 K)
      ((Stacks.Cohomology.CoefficientChange.extendScalarsComplex α).map b)
      (Stacks.SheafOfModules.Tensor.sheafTensor.{u, u, u, u, u} O) (ComplexShape.up ℤ))) := by
    have h := (Stacks.DerivedTensor.RingedSite.canonicalDerivedTensorProduct
      O).comparisonRight_naturality (𝟙 K)
        ((Stacks.Cohomology.CoefficientChange.extendScalarsComplex α).map b) hL hL'
    rw [DerivedCategory.Q.map_id, CategoryTheory.Functor.map_id, NatTrans.id_app,
      Category.id_comp] at h
    exact isIso_of_square _ _ h
  exact (DerivedCategory.isIso_Q_map_iff_quasiIso _ _).1
    ((isIso_map_iff_of_square DerivedCategory.Q (coeffMixedTotalExtendIso α K N)
      (coeffMixedTotalExtendIso α K N') (coeffMixedTotalExtendIso_hom_naturality α (𝟙 K) b)).2 hT)

/-- The functor from the K-flat complexes of `R`-modules with flat terms to `D(R)` is a
localization at the quasi-isomorphisms between them. -/
instance coeffModelsRight_isLocalization :
    (CochainComplex.KFlatBifunctor.modelsRightQ
        (IsKFlat (Y := Stacks.Cohomology.ringedTopos J R))).IsLocalization
      (CochainComplex.KFlatBifunctor.modelsRightW
        (IsKFlat (Y := Stacks.Cohomology.ringedTopos J R))) :=
  flatKFlatModelsQ_isLocalization (Stacks.Cohomology.ringedTopos J R)

/-- **The derived tensor product over `R`**, `D(O) ⥤ D(R) ⥤ D(O)`: the derived bifunctor of
`(H, N) ↦ H ⊗_R N`, computed by K-flat resolutions with flat terms of the second factor
(Stacks 06YS).  Its values are `O`-modules through the first factor. -/
def coeffMixedDerivedTensor :
    DerivedCategory (SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf O)) ⥤
      DerivedCategory (SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf R)) ⥤
        DerivedCategory (SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf O)) :=
  CochainComplex.KFlatBifunctor.derivedBifunctorOfRight
    (Stacks.MixedBaseChange.mixedSheafTensor α)
    (IsKFlat (Y := Stacks.Cohomology.ringedTopos J R)) (coeffModelsRight_le α)
    (fun K _ _ b hN hN' hb ↦ coeffQuasiIso_mixedTensor_map α K b hN hN' hb)

/-- **A K-flat complex of `R`-modules with flat terms computes the derived tensor product over
`R`**: its value at a complex `H` of `O`-modules and such a complex `N` is the class of
`Tot(H ⊗_R N)`. -/
def coeffMixedDerivedTensorComparison
    (K : CochainComplex (SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf O)) ℤ)
    (N : CochainComplex (SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf R)) ℤ)
    (hN : IsKFlat (Y := Stacks.Cohomology.ringedTopos J R)
      ((HomotopyCategory.quotient _ (ComplexShape.up ℤ)).obj N)) :
    ((coeffMixedDerivedTensor α).obj (DerivedCategory.Q.obj K)).obj (DerivedCategory.Q.obj N) ≅
      DerivedCategory.Q.obj (HomologicalComplex.mapBifunctor K N
        (Stacks.MixedBaseChange.mixedSheafTensor α) (ComplexShape.up ℤ)) :=
  CochainComplex.KFlatBifunctor.comparisonOfRight (Stacks.MixedBaseChange.mixedSheafTensor α)
    (IsKFlat (Y := Stacks.Cohomology.ringedTopos J R)) (coeffModelsRight_le α)
    (fun K _ _ b hN hN' hb ↦ coeffQuasiIso_mixedTensor_map α K b hN hN' hb) K N hN

/-- The comparison is natural in both complexes. -/
lemma coeffMixedDerivedTensorComparison_naturality
    {K K' : CochainComplex (SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf O)) ℤ}
    {N N' : CochainComplex (SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf R)) ℤ}
    (u : K ⟶ K') (v : N ⟶ N')
    (hN : IsKFlat (Y := Stacks.Cohomology.ringedTopos J R)
      ((HomotopyCategory.quotient _ (ComplexShape.up ℤ)).obj N))
    (hN' : IsKFlat (Y := Stacks.Cohomology.ringedTopos J R)
      ((HomotopyCategory.quotient _ (ComplexShape.up ℤ)).obj N')) :
    ((coeffMixedDerivedTensor α).map (DerivedCategory.Q.map u)).app (DerivedCategory.Q.obj N) ≫
        ((coeffMixedDerivedTensor α).obj (DerivedCategory.Q.obj K')).map
          (DerivedCategory.Q.map v) ≫
        (coeffMixedDerivedTensorComparison α K' N' hN').hom =
      (coeffMixedDerivedTensorComparison α K N hN).hom ≫
        DerivedCategory.Q.map (HomologicalComplex.mapBifunctorMap u v
          (Stacks.MixedBaseChange.mixedSheafTensor α) (ComplexShape.up ℤ)) :=
  CochainComplex.KFlatBifunctor.comparisonOfRight_naturality
    (Stacks.MixedBaseChange.mixedSheafTensor α)
    (IsKFlat (Y := Stacks.Cohomology.ringedTopos J R)) (coeffModelsRight_le α)
    (fun K _ _ b hN hN' hb ↦ coeffQuasiIso_mixedTensor_map α K b hN hN' hb) u v hN hN'

end Derived

end Stacks.Cohomology.MixedDerivedTensor

end
