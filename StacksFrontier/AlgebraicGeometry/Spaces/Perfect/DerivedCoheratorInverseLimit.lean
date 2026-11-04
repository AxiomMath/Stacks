module

public import StacksFrontier.AlgebraicGeometry.Spaces.Perfect.DerivedCoherator
public import StacksFrontier.AlgebraicGeometry.Spaces.Perfect.DerivedCoheratorBounded
public import StacksFrontier.AlgebraicGeometry.Spaces.NoetherianCoherator.DerivedPushforwardBound
public import StacksFrontier.AlgebraicGeometry.Spaces.SmallEtaleChartModuleCohomologyVanishing
public import StacksFrontier.AlgebraicGeometry.Spaces.ModuleHigherPushforwardEtaleBaseChange
public import StacksFrontier.AlgebraicGeometry.Perfect.Coherator.InverseLimitQuasiCoherent
public import StacksFrontier.Algebra.Homology.DerivedCategory.DerivedFunctorSingleAcyclic
public import StacksFrontier.CategoryTheory.Sites.Cohomology.FilteredColimits.GlobalCohomologyOnALargeSite
public import StacksFrontier.CategoryTheory.Sites.Cohomology.UnboundedDerivedFunctor.LeftTExactness
public import StacksFrontier.Homology.Injectives.DerivedCategory.DerivedLimit
public import StacksFrontier.Homology.DerivedCategory.InverseSystem.MilnorShortExact
public import StacksFrontier.Homology.DerivedCategory.InverseSystem.ProIsomorphism
public import StacksFrontier.Homology.DerivedCategory.InverseSystem.ProIsomorphismInterleaving
public import StacksCore.Tactic.StacksAttribute

/-!
# Derived limits of quasi-coherent sheaves and the coherator of an algebraic space

Let `X` be a quasi-compact and quasi-separated algebraic space over a scheme `S`, let `DQ_X` be the
right adjoint of the inclusion `D_QCoh(𝒪_X) ⥤ D(𝒪_X)` (Stacks 0CR4) and let `(𝓕ₙ)` be an
inverse system of quasi-coherent `𝒪_X`-modules.  Example 0CST asserts:

1. `DQ_X(R lim 𝓕ₙ) = (R lim in D_QCoh(𝒪_X))(𝓕ₙ)`, the first `R lim` taken in `D(𝒪_X)`, because
   `DQ_X` is an exact right adjoint and so commutes with products and with derived limits;
2. for `K = R lim 𝓕ₙ` and every affine `U` étale over `X`,
   `H^i(U, K) = H^i(R lim Γ(U, 𝓕ₙ))`, the derived limit on the right taken in `D(Ab)`, because
   `RΓ(U, -)` commutes with derived limits and the quasi-coherent `𝓕ₙ` have no higher cohomology
   on the affine `U`;
3. hence `H^i(U, K) = 0` unless `i ∈ [0, 1]`;
4. hence, by Stacks 0CSS, `DQ_X(K)` (which is the `R lim` in `D_QCoh(𝒪_X)` by 1.) lies in
   `D^b_QCoh(𝒪_X)` and has vanishing cohomology sheaves in negative degrees.

## Main results

* `AlgebraicGeometry.Space.isDerivedLimit_coherator_obj`: assertion 1, for every coherator `DQ`
  (every right adjoint of the inclusion) and every inverse system in `D_QCoh(𝒪_X)`, at every
  model of `D(𝒪_X)`.
* `AlgebraicGeometry.Space.nonempty_homology_chartSections_iso_of_isDerivedLimit_single`:
  assertion 2.
* `AlgebraicGeometry.Space.isZero_homology_chartSections_of_isDerivedLimit_single`:
  assertion 3.
* `AlgebraicGeometry.Space.exists_isZero_homology_coherator_obj_of_isDerivedLimit_single`:
  assertion 4.

## Implementation notes

A derived limit is the predicate `CategoryTheory.Pretriangulated.IsDerivedLimit` (Stacks 08TC):
`K` sits in a distinguished triangle `K ⟶ ∏ Kₙ ⟶ ∏ Kₙ ⟶ K[1]` whose middle map is `1 - shift`.
It is unique up to non-unique isomorphism, so every statement is made for every derived limit.
The system `(𝓕ₙ)` enters `D(𝒪_X)` through `DerivedCategory.singleFunctor _ 0`, and the system
`(Γ(U, 𝓕ₙ))` enters `D(Ab)` the same way.  The instance arguments `HasProduct` record that the
countable products defining these derived limits exist; they always do, by
`Stacks.KInjectiveProducts.hasProductsOfShape_derivedCategory_sheafOfModules` in `D(𝒪_X)` and by
Stacks 07KC in `D(Ab)`.

As in Stacks 0CSS (`AlgebraicGeometry.Space.exists_isZero_homology_coherator_obj`), the
cohomology `H^i(U, K)` over an affine étale chart `U` is the cohomology of the complex of sections
over `U` of a K-injective complex `I` representing `K`, i.e. of the unbounded derived sections
`RΓ(U, K)`.

Assertions 1–3 are stated at arbitrary models of `D(𝒪_X)` and `D(Ab)`.  Assertion 4 is stated
at the standard model, the one at which Stacks 0CSS is.

## References

* [Stacks Project, Tag 0CST](https://stacks.math.columbia.edu/tag/0CST)
* [Stacks Project, Tag 0CSS](https://stacks.math.columbia.edu/tag/0CSS)
* [Stacks Project, Tag 0CR4](https://stacks.math.columbia.edu/tag/0CR4)
* [Stacks Project, Tag 08TC](https://stacks.math.columbia.edu/tag/08TC)
* [Stacks Project, Tag 08U1](https://stacks.math.columbia.edu/tag/08U1)
* [Stacks Project, Tag 07KY](https://stacks.math.columbia.edu/tag/07KY)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits CategoryTheory.Pretriangulated Opposite
open Stacks.SheafOfModules.Tensor (ringSheaf)

attribute [-instance] Stacks.Cohomology.SiteModules.moduleSheavesAbelian

attribute [local instance 5000] SheafOfModules.instAbelian

universe w w' u

namespace AlgebraicGeometry.Space

variable (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)

section AnyModel

variable (X : AlgebraicSpaces B S hS) [HasDerivedCategory.{w} (Modules.{u, u} B S hS X.1 X.2)]

/-- **Stacks 0CST, the coherator commutes with derived limits.**  Let `X` be an algebraic space
over `S`, `DQ` a right adjoint of the inclusion `ι : D_QCoh(𝒪_X) ⥤ D(𝒪_X)` and `F` an inverse
system in `D_QCoh(𝒪_X)`.  If `L` is a derived limit of `F` computed in `D(𝒪_X)`, then the
product of `F` exists in `D_QCoh(𝒪_X)` and `DQ L` is a derived limit of `F` there:
`DQ_X(R lim Fₙ) = (R lim in D_QCoh(𝒪_X))(Fₙ)`.

Such a `DQ` exists when `X` is quasi-compact and quasi-separated, by Stacks 0CR4
(`AlgebraicGeometry.Space.isLeftAdjoint_ι_derivedCategoryB_isQuasicoherentOnSite`); the system of
the source is the system of quasi-coherent sheaves `(𝓕ₙ)`, placed in degree `0`. -/
@[stacks 0CST "assertion DQ_X(R lim F_n) = (R lim in D_QCoh(O_X))(F_n): for every right adjoint DQ \
of the inclusion D_QCoh(O_X) -> D(O_X), at every model of D(O_X), and every inverse system in \
D_QCoh(O_X); DQ_X exists on a qcqs X by 0CR4"]
theorem isDerivedLimit_coherator_obj
    (DQ : DerivedCategory (Modules.{u, u} B S hS X.1 X.2) ⥤
      (DerivedCategoryB.derivedCategoryB (SheafOfModules.isQuasicoherentOnSite.{u + 1, u, u, u}
        (ringSheaf (smallEtaleRingedSite B S hS X.1 X.2).O))).FullSubcategory)
    (adj : (DerivedCategoryB.derivedCategoryB (SheafOfModules.isQuasicoherentOnSite.{u + 1, u, u, u}
      (ringSheaf (smallEtaleRingedSite B S hS X.1 X.2).O))).ι ⊣ DQ)
    (F : ℕᵒᵖ ⥤ (DerivedCategoryB.derivedCategoryB
      (SheafOfModules.isQuasicoherentOnSite.{u + 1, u, u, u}
        (ringSheaf (smallEtaleRingedSite B S hS X.1 X.2).O))).FullSubcategory)
    [HasProduct fun n : ℕ ↦ (F ⋙ (DerivedCategoryB.derivedCategoryB
      (SheafOfModules.isQuasicoherentOnSite.{u + 1, u, u, u}
        (ringSheaf (smallEtaleRingedSite B S hS X.1 X.2).O))).ι).obj (op n)]
    (L : DerivedCategory (Modules.{u, u} B S hS X.1 X.2))
    (hL : IsDerivedLimit (F ⋙ (DerivedCategoryB.derivedCategoryB
      (SheafOfModules.isQuasicoherentOnSite.{u + 1, u, u, u}
        (ringSheaf (smallEtaleRingedSite B S hS X.1 X.2).O))).ι) L) :
    ∃ h : HasProduct fun n : ℕ ↦ F.obj (op n),
      letI := h
      IsDerivedLimit F (DQ.obj L) := by
  let P := DerivedCategoryB.derivedCategoryB (SheafOfModules.isQuasicoherentOnSite.{u + 1, u, u, u}
    (ringSheaf (smallEtaleRingedSite B S hS X.1 X.2).O))
  let : DQ.CommShift ℤ := adj.rightAdjointCommShift ℤ
  let : adj.CommShift ℤ := adj.commShift_of_leftAdjoint ℤ
  have : adj.IsTriangulated := Adjunction.IsTriangulated.mk' adj
  have : DQ.IsRightAdjoint := adj.isRightAdjoint
  obtain ⟨hprod₀, h⟩ := Stacks.Injectives.isDerivedLimit_map_rightAdjoint DQ (F ⋙ P.ι) L hL
  have hprod : HasProduct fun n : ℕ ↦ ((F ⋙ P.ι) ⋙ DQ).obj (op n) := hprod₀
  let c : (F ⋙ P.ι) ⋙ DQ ≅ F :=
    Functor.associator F P.ι DQ ≪≫ (Functor.isoWhiskerLeft F (asIso adj.unit)).symm ≪≫
      F.rightUnitor
  have hF : HasProduct fun n : ℕ ↦ F.obj (op n) :=
    let := hprod
    hasProduct_of_equiv_of_iso (fun n : ℕ ↦ ((F ⋙ P.ι) ⋙ DQ).obj (op n)) _ (.refl ℕ)
      (c.symm.app <| op ·)
  let := hprod
  exact ⟨hF, IsDerivedLimit.of_natIso c h⟩

end AnyModel

section Sections

attribute [local instance] isGrothendieckAbelian_modules enoughInjectives_modules
  hasInjectiveResolutions_modules

variable (X : AlgebraicSpaces B S hS)

/-- Sections over a chart preserve countable products, being an evaluation of sheaves of
modules followed by the forgetful functor to abelian groups. -/
theorem preservesLimitsOfShape_discrete_chartSectionsAb (U : SmallEtale B S hS X.1) :
    PreservesLimitsOfShape (Discrete ℕ) (chartSectionsAb B S hS X U) := by
  dsimp only [chartSectionsAb]
  have : PreservesLimitsOfShape (Discrete ℕ) (SheafOfModules.evaluation
      (ringSheaf (smallEtaleRingedSite B S hS X.1 X.2).O) (op U)) :=
    SheafOfModules.evaluationPreservesLimitsOfShape _ _ _
  infer_instance

/-- The higher derived functors of the sections over an affine chart vanish on a quasi-coherent
module. -/
theorem isZero_rightDerived_chartSectionsAb_of_isAffineChart (U : SmallEtale B S hS X.1)
    (hU : IsAffineChart B S hS X.1 U) (M : Modules.{u, u} B S hS X.1 X.2)
    (hM : M.IsQuasicoherentOnSite) (p : ℕ) (hp : 0 < p) :
    IsZero (((chartSectionsAb B S hS X U).rightDerived p).obj M) :=
  IsZero.of_iso ((forget₂ (ModuleCat.{u} _) AddCommGrpCat.{u}).map_isZero
      (isZero_rightDerived_evaluation_of_isQuasicoherentOnSite B S hS X.1 X.2 U hU M hM p hp))
    ((Stacks.Cohomology.ColimitsOfCohomology.rightDerivedCompExactIso
      (SheafOfModules.evaluation (ringSheaf (smallEtaleRingedSite B S hS X.1 X.2).O) (op U))
      (forget₂ (ModuleCat.{u} _) AddCommGrpCat.{u}) p).app M)

section Models

variable [HasDerivedCategory.{w} (Modules.{u, u} B S hS X.1 X.2)]
  [HasDerivedCategory.{w'} AddCommGrpCat.{u}]

/-- **`RΓ(U, R lim 𝓕ₙ) = R lim Γ(U, 𝓕ₙ)`.**  For an inverse system `(𝓕ₙ)` of quasi-coherent
modules, a derived limit `L` of `(𝓕ₙ[0])` in `D(𝒪_X)`, an affine étale chart `U` and a K-injective
complex `I` representing `L`, there is a derived limit `M` in `D(Ab)` of the system
`(Γ(U, 𝓕ₙ)[0])` with `H^i(Γ(U, I^•)) ≅ H^i(M)` for every `i`; `M` is `RΓ(U, L)`. -/
private theorem exists_isDerivedLimit_chartSections
    (𝓕 : ℕᵒᵖ ⥤ Modules.{u, u} B S hS X.1 X.2)
    (hqc : ∀ n : ℕ, (𝓕.obj (op n)).IsQuasicoherentOnSite)
    [HasProduct fun n : ℕ ↦
      (𝓕 ⋙ DerivedCategory.singleFunctor (Modules.{u, u} B S hS X.1 X.2) 0).obj (op n)]
    (L : DerivedCategory (Modules.{u, u} B S hS X.1 X.2))
    (hL : IsDerivedLimit (𝓕 ⋙ DerivedCategory.singleFunctor _ 0) L)
    (U : SmallEtale B S hS X.1) (hU : IsAffineChart B S hS X.1 U)
    (I : CochainComplex (Modules.{u, u} B S hS X.1 X.2) ℤ) (hI : I.IsKInjective)
    (eI : Nonempty (DerivedCategory.Q.obj I ≅ L)) :
    ∃ (M : DerivedCategory AddCommGrpCat.{u}) (_ : HasProduct fun n : ℕ ↦
        (𝓕 ⋙ chartSectionsAb B S hS X U ⋙
          DerivedCategory.singleFunctor AddCommGrpCat.{u} 0).obj (op n)),
      IsDerivedLimit (𝓕 ⋙ chartSectionsAb B S hS X U ⋙
          DerivedCategory.singleFunctor AddCommGrpCat.{u} 0) M ∧
        ∀ i : ℤ, Nonempty ((((chartSectionsAb B S hS X U).mapHomologicalComplex
          (ComplexShape.up ℤ)).obj I).homology i ≅
            (DerivedCategory.homologyFunctor AddCommGrpCat.{u} i).obj M) := by
  obtain ⟨eI⟩ := eI
  let A := Modules.{u, u} B S hS X.1 X.2
  let F := chartSectionsAb B S hS X U
  have := preservesLimitsOfShape_discrete_chartSectionsAb B S hS X U
  let RF := Stacks.DerivedFunctor.totalRightDerived F
  let α := (Stacks.DerivedFunctor.homotopyMap F).totalRightDerivedUnit DerivedCategory.Qh
    (HomotopyCategory.quasiIso A (ComplexShape.up ℤ))
  let := Functor.IsRightDerivedFunctor.commShift RF α
    (HomotopyCategory.quasiIso A (ComplexShape.up ℤ)) ℤ
  have := Stacks.Injectives.rightDerivedFunctor_isTriangulated F RF α
  obtain ⟨p, δ, hT⟩ := hL
  obtain ⟨hP, δ', hT'⟩ := Stacks.Injectives.isDerivedLimit_map_rightDerivedFunctor F RF α
    (𝓕 ⋙ DerivedCategory.singleFunctor A 0) L p ⟨δ, hT⟩
  have hRL : IsDerivedLimit ((𝓕 ⋙ DerivedCategory.singleFunctor A 0) ⋙ RF) (RF.obj L) :=
    ⟨_, δ', hT'⟩
  have hiso : ∀ n : ℕᵒᵖ, IsIso ((Functor.whiskerLeft 𝓕
      (Stacks.DerivedFunctor.singleUnit F RF α)).app n) := fun n =>
    Stacks.DerivedFunctor.isIso_singleUnit_app F RF α
      (fun M => Stacks.DerivedFunctor.isGE_totalRightDerived_obj F _ 0)
      (exists_quasiIso_isKInjective_modules B S hS X.1 X.2) (𝓕.obj n)
      (isZero_rightDerived_chartSectionsAb_of_isAffineChart B S hS X U hU (𝓕.obj n) (hqc n.unop))
  have := NatIso.isIso_of_isIso_app (Functor.whiskerLeft 𝓕
      (Stacks.DerivedFunctor.singleUnit F RF α))
  let c : (𝓕 ⋙ DerivedCategory.singleFunctor A 0) ⋙ RF ≅
      𝓕 ⋙ F ⋙ DerivedCategory.singleFunctor AddCommGrpCat.{u} 0 :=
    (asIso (Functor.whiskerLeft 𝓕 (Stacks.DerivedFunctor.singleUnit F RF α))).symm
  have hP' : HasProduct fun n : ℕ ↦ ((𝓕 ⋙ DerivedCategory.singleFunctor A 0) ⋙ RF).obj (op n) :=
    hP
  have hG : HasProduct fun n : ℕ ↦
      (𝓕 ⋙ F ⋙ DerivedCategory.singleFunctor AddCommGrpCat.{u} 0).obj (op n) :=
    let := hP'
    hasProduct_of_equiv_of_iso
      (fun n : ℕ ↦ ((𝓕 ⋙ DerivedCategory.singleFunctor A 0) ⋙ RF).obj (op n)) _ (.refl ℕ)
      (c.symm.app <| op ·)
  refine ⟨RF.obj L, hG, IsDerivedLimit.of_natIso c hRL, fun i => ⟨?_⟩⟩
  exact ((DerivedCategory.homologyFunctorFactors AddCommGrpCat.{u} i).app _).symm ≪≫
    (DerivedCategory.homologyFunctor AddCommGrpCat.{u} i).mapIso
      (CategoryTheory.PushforwardMayerVietoris.rightDerivedObjIsoOfKInjective
        (exists_quasiIso_isKInjective_modules B S hS X.1 X.2) F inferInstance RF α
        inferInstance I hI ≪≫ RF.mapIso eI)

/-- **Stacks 0CST, `H^i(U, K) = H^i(R lim Γ(U, 𝓕ₙ))`.**  Let `(𝓕ₙ)` be an inverse system of
quasi-coherent `𝒪_X`-modules on an algebraic space `X`, let `L = R lim 𝓕ₙ` be a derived limit in
`D(𝒪_X)` of the system `(𝓕ₙ)` placed in degree `0`, and let `U` be an affine étale chart of `X`.
Then for every derived limit `R = R lim Γ(U, 𝓕ₙ)` in `D(Ab)` of the abelian groups `Γ(U, 𝓕ₙ)`
placed in degree `0`, and every `i`, `H^i(U, L) ≅ H^i(R)`.

`H^i(U, L)` is the cohomology of the complex of sections over `U` of any K-injective complex `I`
representing `L`. -/
@[stacks 0CST "assertion H^i(U, K) = H^i(R lim Gamma(U, F_n)) for K = R lim F_n in D(O_X) and U \
affine etale over X; R lim Gamma(U, F_n) is any derived limit in D(Ab), at any models; \
H^i(U, K) is computed on a K-injective representative, as in 0CSS"]
theorem nonempty_homology_chartSections_iso_of_isDerivedLimit_single
    (𝓕 : ℕᵒᵖ ⥤ Modules.{u, u} B S hS X.1 X.2)
    (hqc : ∀ n : ℕ, (𝓕.obj (op n)).IsQuasicoherentOnSite)
    [HasProduct fun n : ℕ ↦
      (𝓕 ⋙ DerivedCategory.singleFunctor (Modules.{u, u} B S hS X.1 X.2) 0).obj (op n)]
    (L : DerivedCategory (Modules.{u, u} B S hS X.1 X.2))
    (hL : IsDerivedLimit (𝓕 ⋙ DerivedCategory.singleFunctor _ 0) L)
    (U : SmallEtale B S hS X.1) (hU : IsAffineChart B S hS X.1 U)
    (I : CochainComplex (Modules.{u, u} B S hS X.1 X.2) ℤ) (hI : I.IsKInjective)
    (eI : Nonempty (DerivedCategory.Q.obj I ≅ L))
    [HasProduct fun n : ℕ ↦ (𝓕 ⋙ chartSectionsAb B S hS X U ⋙
      DerivedCategory.singleFunctor AddCommGrpCat.{u} 0).obj (op n)]
    (R : DerivedCategory AddCommGrpCat.{u})
    (hR : IsDerivedLimit (𝓕 ⋙ chartSectionsAb B S hS X U ⋙
      DerivedCategory.singleFunctor AddCommGrpCat.{u} 0) R)
    (i : ℤ) :
    Nonempty ((((chartSectionsAb B S hS X U).mapHomologicalComplex (ComplexShape.up ℤ)).obj
      I).homology i ≅ (DerivedCategory.homologyFunctor AddCommGrpCat.{u} i).obj R) := by
  obtain ⟨M, hM, hML, he⟩ :=
    exists_isDerivedLimit_chartSections B S hS X 𝓕 hqc L hL U hU I hI eI
  obtain ⟨e⟩ := he i
  obtain ⟨e'⟩ := Rlim.Pro.nonempty_iso_of_isDerivedLimit_of_pro_isomorphism _ _ M R hML hR
    (InverseSequence.ProIso.ofNatIso (Iso.refl _))
  exact ⟨e ≪≫ (DerivedCategory.homologyFunctor AddCommGrpCat.{u} i).mapIso e'⟩

end Models

variable [HasDerivedCategory.{w} (Modules.{u, u} B S hS X.1 X.2)]

/-- **Stacks 0CST, `H^i(U, K) = 0` unless `i ∈ [0, 1]`.**  Let `(𝓕ₙ)` be an inverse system of
quasi-coherent `𝒪_X`-modules on an algebraic space `X` and `L = R lim 𝓕ₙ` a derived limit in
`D(𝒪_X)` of the system `(𝓕ₙ)` placed in degree `0`.  Then `H^i(U, L) = 0` for every affine étale
chart `U` of `X` and every `i ∉ [0, 1]`. -/
@[stacks 0CST "assertion H^i(U, R lim F_n) = 0 for i outside [0, 1] and U affine etale over X, \
at any model of D(O_X)"]
theorem isZero_homology_chartSections_of_isDerivedLimit_single
    (𝓕 : ℕᵒᵖ ⥤ Modules.{u, u} B S hS X.1 X.2)
    (hqc : ∀ n : ℕ, (𝓕.obj (op n)).IsQuasicoherentOnSite)
    [HasProduct fun n : ℕ ↦
      (𝓕 ⋙ DerivedCategory.singleFunctor (Modules.{u, u} B S hS X.1 X.2) 0).obj (op n)]
    (L : DerivedCategory (Modules.{u, u} B S hS X.1 X.2))
    (hL : IsDerivedLimit (𝓕 ⋙ DerivedCategory.singleFunctor _ 0) L)
    (U : SmallEtale B S hS X.1) (hU : IsAffineChart B S hS X.1 U)
    (I : CochainComplex (Modules.{u, u} B S hS X.1 X.2) ℤ) (hI : I.IsKInjective)
    (eI : Nonempty (DerivedCategory.Q.obj I ≅ L)) (i : ℤ) (hi : i < 0 ∨ 1 < i) :
    IsZero ((((chartSectionsAb B S hS X U).mapHomologicalComplex (ComplexShape.up ℤ)).obj
      I).homology i) := by
  let := HasDerivedCategory.standard AddCommGrpCat.{u}
  obtain ⟨M, hM, hML, he⟩ :=
    exists_isDerivedLimit_chartSections B S hS X 𝓕 hqc L hL U hU I hI eI
  obtain ⟨e⟩ := he i
  refine IsZero.of_iso ?_ e
  have hterm : ∀ (n : ℕ) (j : ℤ), j ≠ 0 →
      IsZero ((DerivedCategory.homologyFunctor AddCommGrpCat.{u} j).obj
        ((𝓕 ⋙ chartSectionsAb B S hS X U ⋙
          DerivedCategory.singleFunctor AddCommGrpCat.{u} 0).obj (op n))) := by
    intro n j hj
    let T := (DerivedCategory.singleFunctor AddCommGrpCat.{u} 0).obj
      ((chartSectionsAb B S hS X U).obj (𝓕.obj (op n)))
    show IsZero ((DerivedCategory.homologyFunctor AddCommGrpCat.{u} j).obj T)
    rcases lt_or_gt_of_ne hj with hj | hj
    · exact T.isZero_of_isGE 0 j hj
    · exact T.isZero_of_isLE 0 j hj
  obtain ⟨a, b, -, hdeg⟩ := DerivedCategory.isDerivedLimit_homology_shortExact
    (𝓕 ⋙ chartSectionsAb B S hS X U ⋙ DerivedCategory.singleFunctor AddCommGrpCat.{u} 0) M hML
  obtain ⟨e, ι, q, w, -, -, -, hShortExact⟩ := hdeg i
  refine isZero_X₂_of_shortExact hShortExact ?_ ?_
  · exact isZero_cokernel_of_isZero
      (isZero_limit_of_forall_isZero _ fun n ↦ hterm n.as (i - 1) (by omega)) _
  · exact isZero_limit_of_forall_isZero _ fun n ↦ hterm n.unop i (by omega)

end Sections

section Bounded

attribute [local instance] HasDerivedCategory.standard

/-- **Stacks 0CST, `DQ_X(R lim 𝓕ₙ)` is in `D^b_QCoh(𝒪_X)` with no negative cohomology.**  Let
`X` be a quasi-compact and quasi-separated algebraic space over `S` and `DQ` a right adjoint of
the inclusion `D_QCoh(𝒪_X) ⥤ D(𝒪_X)`.  There is an integer `N` such that for every inverse system
`(𝓕ₙ)` of quasi-coherent `𝒪_X`-modules and every derived limit `L = R lim 𝓕ₙ` in `D(𝒪_X)` of
`(𝓕ₙ)` placed in degree `0`, the cohomology sheaves `H^i(DQ L)` vanish for `i < 0` and for
`i > 1 + N`.  By `AlgebraicGeometry.Space.isDerivedLimit_coherator_obj`, `DQ L` is the `R lim`
of `(𝓕ₙ)` in `D_QCoh(𝒪_X)`.

This is Stacks 0CSS (`AlgebraicGeometry.Space.exists_isZero_homology_coherator_obj`) with
`[a, b] = [0, 1]`. -/
@[stacks 0CST "conclusion: the R lim in D_QCoh(O_X), i.e. DQ_X(R lim F_n), lies in \
D^b_QCoh(O_X) and has vanishing cohomology sheaves in negative degrees (in [0, 1 + N], N = N(X) \
uniform), by 0CSS; at the standard model, the one of 0CSS"]
theorem exists_isZero_homology_coherator_obj_of_isDerivedLimit_single (X : AlgebraicSpaces B S hS)
    (hXqc : IsQuasiCompactSpace B S hS X.1)
    (hXqs : IsAbsolutelyQuasiSeparated B S hS B.contains_terminal X.1)
    (DQ : DerivedCategory (Modules.{u, u} B S hS X.1 X.2) ⥤
      (DerivedCategoryB.derivedCategoryB (SheafOfModules.isQuasicoherentOnSite.{u + 1, u, u, u}
        (ringSheaf (smallEtaleRingedSite B S hS X.1 X.2).O))).FullSubcategory)
    (adj : (DerivedCategoryB.derivedCategoryB (SheafOfModules.isQuasicoherentOnSite.{u + 1, u, u, u}
      (ringSheaf (smallEtaleRingedSite B S hS X.1 X.2).O))).ι ⊣ DQ) :
    ∃ N : ℤ, ∀ (𝓕 : ℕᵒᵖ ⥤ Modules.{u, u} B S hS X.1 X.2),
      (∀ n : ℕ, (𝓕.obj (op n)).IsQuasicoherentOnSite) →
      ∀ [HasProduct fun n : ℕ ↦
        (𝓕 ⋙ DerivedCategory.singleFunctor (Modules.{u, u} B S hS X.1 X.2) 0).obj (op n)]
        (L : DerivedCategory (Modules.{u, u} B S hS X.1 X.2)),
        IsDerivedLimit (𝓕 ⋙ DerivedCategory.singleFunctor _ 0) L →
        ∀ i : ℤ, i < 0 ∨ 1 + N < i →
          IsZero ((DerivedCategory.homologyFunctor (Modules.{u, u} B S hS X.1 X.2) i).obj
            ((DerivedCategoryB.derivedCategoryB
              (SheafOfModules.isQuasicoherentOnSite.{u + 1, u, u, u}
                (ringSheaf (smallEtaleRingedSite B S hS X.1 X.2).O))).ι.obj (DQ.obj L))) := by
  obtain ⟨N, hN⟩ := exists_isZero_homology_coherator_obj B S hS X hXqc hXqs DQ adj
  refine ⟨N, fun 𝓕 hqc _ L hL i hi => hN 0 1 L (fun U hU I hI eI j hj => ?_) i hi⟩
  exact isZero_homology_chartSections_of_isDerivedLimit_single B S hS X 𝓕 hqc L hL U hU I hI eI
    j hj

end Bounded

end AlgebraicGeometry.Space

end
