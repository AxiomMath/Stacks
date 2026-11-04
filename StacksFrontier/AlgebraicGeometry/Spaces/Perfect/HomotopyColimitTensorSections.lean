module

public import StacksFrontier.AlgebraicGeometry.Spaces.Perfect.CountableHomotopyColimit
public import StacksFrontier.AlgebraicGeometry.Spaces.QuasicoherentDerivedPushforwardDirectSums
public import StacksFrontier.AlgebraicGeometry.Spaces.QuasicoherentDerivedTensorClosed
public import StacksFrontier.AlgebraicGeometry.Spaces.SmallEtaleDerivedPullbackCompAssoc
public import StacksFrontier.AlgebraicGeometry.Spaces.SmallEtaleDerivedPullbackTensorCoherence
public import StacksFrontier.AlgebraicGeometry.Spaces.SmallEtaleProjectionFormulaIso
public import StacksFrontier.CategoryTheory.Adjunction.ProjectionUnitNatTrans
public import StacksFrontier.CategoryTheory.Limits.PreservesColimitOfEquivalenceComp
public import StacksFrontier.CategoryTheory.Sites.Cohomology.DerivedTensor.SheafTensorColimits

/-!
# Derived sections of a tensor product with a homotopy colimit

Let `p : X ⟶ T` be a quasi-compact and quasi-separated morphism from an algebraic space to an
affine scheme `T = Spec A`, let `P = hocolim Eₙ` in `D(𝒪_X)` with every `Eₙ` perfect, and let
`K ∈ D_QCoh(𝒪_X)`. Then

`RΓ(X, P ⊗^L K) = hocolim RΓ(X, Eₙ ⊗^L K)` in `D(A)`:

`- ⊗^L K`, `Rp_*` and `RΓ(T, -)` are triangulated and commute with the direct sums involved, the
first because the derived tensor product does, the other two on `D_QCoh` (Stacks 08FB), which
contains `Eₙ ⊗^L K`. This is the formal step of the proof of Stacks 0CRW.

## Main results

* `AlgebraicGeometry.Space.isHomotopyColimitCocone_representedAffineDerivedSections_tensor`.

## References

* [Stacks Project, Tag 0CRW](https://stacks.math.columbia.edu/tag/0CRW)
* [Stacks Project, Tag 08FB](https://stacks.math.columbia.edu/tag/08FB)
* [Stacks Project, Tag 090Z](https://stacks.math.columbia.edu/tag/090Z)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits CategoryTheory.Pretriangulated

universe u

namespace AlgebraicGeometry.Space

attribute [-instance] Stacks.Cohomology.SiteModules.moduleSheavesAbelian
  Stacks.Cohomology.SiteModules.moduleSheavesGrothendieck
attribute [local instance 20000] AddCommGrpCat.FilteredColimits.forget_preservesFilteredColimits
attribute [local instance 5000] SheafOfModules.instAbelian
attribute [local instance 10000] HasDerivedCategory.standard
attribute [local instance 5000] SmallEtale.instHasSheafify SmallEtale.instWEqualsLocallyBijective
  isGrothendieckAbelian_ringedToposStructureRingSheaf
attribute [local instance] isGrothendieckAbelian_modules

variable {B : BigFppfSite.{u}} {S : Scheme.{u}} {hS : B.Contains S}

/-- **`RΓ(X, (hocolim Eₙ) ⊗^L K) = hocolim RΓ(X, Eₙ ⊗^L K)`** in `D(A)`, for `p : X ⟶ Spec A`
quasi-compact and quasi-separated, `Eₙ` perfect and `K ∈ D_QCoh(𝒪_X)`: coprojections
`cₙ : Eₙ ⟶ P` exhibiting `P` as a derived colimit are carried to coprojections exhibiting
`RΓ(X, P ⊗^L K)` as a derived colimit. -/
theorem isHomotopyColimitCocone_representedAffineDerivedSections_tensor
    {X : AlgebraicSpaces B S hS} (T : BigFppfOver B S hS)
    [IsAffine ((BigFppfOver.toScheme B S hS).obj T)]
    (p : X ⟶ ⟨yoneda.obj T, isAlgebraicSpace_yoneda B S hS T⟩)
    (hpqc : IsQuasiCompact B S hS p.hom) (hpqs : IsQuasiSeparated B S hS p.hom)
    (E : ℕ ⥤ DerivedCategory (Modules.{u, u} B S hS X.1 X.2))
    (hE : ∀ n, (smallEtaleRingedSite B S hS X.1 X.2).IsPerfect (E.obj n))
    {P : DerivedCategory (Modules.{u, u} B S hS X.1 X.2)} {c : ∀ n, E.obj n ⟶ P}
    (hc : IsHomotopyColimitCocone E c)
    (K : DerivedCategory (Modules.{u, u} B S hS X.1 X.2)) (hK : QcohDerived B S hS X K) :
    IsHomotopyColimitCocone
      (E ⋙ (smallEtaleDerivedTensor B S hS X).flip.obj K ⋙ derivedModulePushforward B S hS p ⋙
        representedAffineDerivedSections B S hS T)
      fun n ↦ (representedAffineDerivedSections B S hS T).map
        ((derivedModulePushforward B S hS p).map
          (((smallEtaleDerivedTensor B S hS X).flip.obj K).map (c n))) := by
  let Tt := smallEtaleDerivedTensorProduct B S hS X
  let : ((smallEtaleDerivedTensor B S hS X).flip.obj K).CommShift ℤ := Tt.commShift_left K
  have : ((smallEtaleDerivedTensor B S hS X).flip.obj K).IsTriangulated := Tt.exact_left K
  let G₁ : DerivedCategory (Modules.{u, u} B S hS X.1 X.2) ⥤
      DerivedCategory (Modules.{u, u} B S hS X.1 X.2) :=
    (smallEtaleDerivedTensor B S hS X).flip.obj K
  have : PreservesColimitsOfShape (Discrete (ULift.{u} ℕ)) G₁ :=
    Stacks.SheafOfModules.DerivedTensorProduct.preservesColimitsOfShape_tensor_flip_obj Tt K _
  have : PreservesColimitsOfShape (Discrete ℕ) G₁ :=
    preservesColimitsOfShape_of_equiv (Discrete.equivalence Equiv.ulift) _
  have h₁ := @IsHomotopyColimitCocone.map _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ hc G₁
    (Tt.commShift_left K) (Tt.exact_left K) _ _
  have hq : ∀ n, QcohDerived B S hS X ((E ⋙ G₁).obj n) := fun n =>
    qcohDerived_smallEtaleDerivedTensor X _ _ (qcohDerived_of_isPerfect _ _ _ X _ (hE n)) hK
  let := derivedModulePushforward_commShift B S hS p
  have := derivedModulePushforward_isTriangulated B S hS p
  have : PreservesColimit (Discrete.functor ((E ⋙ G₁).obj ∘ Equiv.ulift.{u}))
      (derivedModulePushforward B S hS p) :=
    preservesColimit_derivedModulePushforward B S hS p hpqc hpqs _ fun k => hq k.down
  have : PreservesColimit (Discrete.functor (E ⋙ G₁).obj) (derivedModulePushforward B S hS p) :=
    preservesColimit_discrete_of_equiv Equiv.ulift.{u} (E ⋙ G₁).obj _
  have h₂ := h₁.map (derivedModulePushforward B S hS p)
  have hq₂ : ∀ n, QcohDerived B S hS ⟨yoneda.obj T, isAlgebraicSpace_yoneda B S hS T⟩
      (((E ⋙ G₁) ⋙ derivedModulePushforward B S hS p).obj n) := fun n =>
    qcohDerived_derivedModulePushforward_obj B S hS p hpqc hpqs _ (hq n)
  have : PreservesColimit (Discrete.functor ((E ⋙ G₁) ⋙ derivedModulePushforward B S hS p).obj)
      (representedAffineDerivedSections B S hS T) :=
    preservesColimit_representedAffineDerivedSections T _ hq₂
      (qcohDerived_sigma_nat ⟨yoneda.obj T, isAlgebraicSpace_yoneda B S hS T⟩ _ hq₂)
  exact h₂.map (representedAffineDerivedSections B S hS T)

/-- **Stacks 0CRW (2) from `Rf_*𝒪_U = hocolim Eₙ`.** Let `f : U ⟶ X` be quasi-compact and
quasi-separated, `p : X ⟶ Spec A` quasi-compact and quasi-separated and `q = f ≫ p`. If
`Rf_*𝒪_U = hocolim Eₙ` with `Eₙ` perfect, then `RΓ(U, Lf^*K) = hocolim RΓ(X, Eₙ ⊗^L K)` in
`D(A)` functorially in `K ∈ D_QCoh(𝒪_X)`: there are maps `RΓ(X, Eₙ ⊗^L K) ⟶ RΓ(U, Lf^*K)`
natural in `K` exhibiting the derived colimit for every such `K`. -/
theorem exists_isHomotopyColimitCocone_derivedSections_pullback_of_isHomotopyColimit
    {U X : AlgebraicSpaces B S hS} (T : BigFppfOver B S hS)
    [IsAffine ((BigFppfOver.toScheme B S hS).obj T)] (f : U ⟶ X)
    (p : X ⟶ ⟨yoneda.obj T, isAlgebraicSpace_yoneda B S hS T⟩)
    (q : U ⟶ ⟨yoneda.obj T, isAlgebraicSpace_yoneda B S hS T⟩) (hq : f ≫ p = q)
    (hfqc : IsQuasiCompact B S hS f.hom) (hfqs : IsQuasiSeparated B S hS f.hom)
    (hpqc : IsQuasiCompact B S hS p.hom) (hpqs : IsQuasiSeparated B S hS p.hom)
    (E : ℕ ⥤ DerivedCategory (Modules.{u, u} B S hS X.1 X.2))
    (hE : ∀ n, (smallEtaleRingedSite B S hS X.1 X.2).IsPerfect (E.obj n))
    (hP : IsHomotopyColimit E ((derivedModulePushforward B S hS f).obj (structureDerived U))) :
    ∃ ι : ∀ n, (smallEtaleDerivedTensor B S hS X).obj (E.obj n) ⋙
        derivedModulePushforward B S hS p ⋙ representedAffineDerivedSections B S hS T ⟶
          smallEtaleDerivedModulePullback B S hS f ⋙ derivedModulePushforward B S hS q ⋙
            representedAffineDerivedSections B S hS T,
      ∀ K, QcohDerived B S hS X K →
        IsHomotopyColimitCocone
          (E ⋙ (smallEtaleDerivedTensor B S hS X).flip.obj K ⋙
            derivedModulePushforward B S hS p ⋙ representedAffineDerivedSections B S hS T)
          fun n ↦ (ι n).app K := by
  subst hq
  obtain ⟨c, hc⟩ := hP.exists_isHomotopyColimitCocone
  let RΓ := representedAffineDerivedSections B S hS T
  let ρ := CategoryTheory.PullbackInternalHom.projectionUnitNatTrans
    (smallEtaleDerivedModuleAdjunction B S hS f) (smallEtaleDerivedTensor B S hS X)
    (smallEtaleDerivedTensor B S hS U) (smallEtaleDerivedPullbackTensorIso f)
    (structureDerived U) (smallEtaleDerivedTensorLeftUnitor U)
  let π : (smallEtaleDerivedTensor B S hS X).obj
        ((derivedModulePushforward B S hS f).obj (structureDerived U)) ⋙
        derivedModulePushforward B S hS p ⋙ RΓ ⟶
      smallEtaleDerivedModulePullback B S hS f ⋙ derivedModulePushforward B S hS (f ≫ p) ⋙ RΓ :=
    Functor.whiskerRight ρ (derivedModulePushforward B S hS p ⋙ RΓ) ≫
      Functor.whiskerLeft (smallEtaleDerivedModulePullback B S hS f)
        (Functor.whiskerRight (smallEtaleDerivedPushforwardCompIsoToposHom B S hS f p).hom RΓ)
  refine ⟨fun n ↦ Functor.whiskerRight ((smallEtaleDerivedTensor B S hS X).map (c n))
    (derivedModulePushforward B S hS p ⋙ RΓ) ≫ π, fun K hK ↦ ?_⟩
  have hO : QcohDerived B S hS U (structureDerived U) :=
    qcohDerived_singleFunctor_structureModule (X := U.1) (hX := U.2)
  have hφ := isIso_smallEtaleProjectionFormulaMap B S hS f hfqc hfqs _ hO _ hK
  have hρ : IsIso (ρ.app K) := IsIso.comp_isIso' hφ inferInstance
  have : IsIso (π.app K) :=
    IsIso.comp_isIso'
      ((derivedModulePushforward B S hS p ⋙ RΓ).mapIso (@asIso _ _ _ _ (ρ.app K) hρ)).isIso_hom
      (RΓ.mapIso ((smallEtaleDerivedPushforwardCompIsoToposHom B S hS f p).app
        ((smallEtaleDerivedModulePullback B S hS f).obj K))).isIso_hom
  exact (isHomotopyColimitCocone_representedAffineDerivedSections_tensor T p hpqc hpqs E hE hc K
    hK).comp_iso (asIso (π.app K))

end AlgebraicGeometry.Space

end
