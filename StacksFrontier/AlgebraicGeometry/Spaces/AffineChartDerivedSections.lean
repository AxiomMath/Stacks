module

public import StacksFrontier.AlgebraicGeometry.SheafComplexLocality.Basic
public import StacksFrontier.AlgebraicGeometry.Spaces.AffineChartCohomologyVanishing
public import StacksFrontier.AlgebraicGeometry.Spaces.DerivedModulePushforward
public import StacksFrontier.AlgebraicGeometry.Spaces.QuasicoherentCokernelsOnSite
public import StacksFrontier.AlgebraicGeometry.Spaces.QuasicoherentDerivedFunctorAmplitudeUnbounded
public import StacksFrontier.Homology.DerivedIndexing.Basic

/-!
# Derived sections over an affine étale chart of an object of `D_QCoh`

Let `X` be an algebraic space over a scheme `S` contained in a big fppf site `B`, let `U` be an
étale chart of `X` whose underlying scheme is affine, and let `RΓ(U, -)` be a right derived functor
of the sections functor `Γ(U, -) : Mod(𝒪_X) ⥤ Ab` on the unbounded derived category. For every `E`
in `D_QCoh(𝒪_X)` lying in degrees `≤ c`, `RΓ(U, E)` lies in degrees `≤ c`.

Exactness of a complex of `𝒪_X`-modules in a degree is tested on its complexes of sections over the
affine étale charts of `X`.

## Main results

* `AlgebraicGeometry.Space.isZero_rightDerivedPlus_sectionsFunctor_of_isAffineChart`:
  `RᵖΓ(U, M) = 0` for `p ≥ 1` and `M` quasi-coherent, in the derived-category indexing.
* `AlgebraicGeometry.Space.isLE_rightDerived_sectionsFunctor_obj_of_isAffineChart`: `RΓ(U, E)`
  lies in degrees `≤ c` whenever `E` in `D_QCoh(𝒪_X)` does.
* `AlgebraicGeometry.Space.exactAt_of_forall_isAffineChart`: a complex of `𝒪_X`-modules is exact
  in degree `j` if its complexes of sections over all affine étale charts are.
* `AlgebraicGeometry.Space.exactAt_sections_of_isKInjective_of_isAffineChart`: the sections over
  an affine étale chart of a K-injective complex with quasi-coherent cohomology in degrees `≤ c`
  are exact above `c`.

## References

* [Stacks Project, Tag 08F7](https://stacks.math.columbia.edu/tag/08F7)
* [Stacks Project, Tag 03DW](https://stacks.math.columbia.edu/tag/03DW)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits Opposite

attribute [local instance 5000] SheafOfModules.instAbelian

universe u

namespace AlgebraicGeometry.Space

attribute [local instance] HasDerivedCategory.standard

variable (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)
  (X : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u) (hX : IsAlgebraicSpace B S hS X)

attribute [local instance] hasProductsOfShape_nat_modules_ringUniverse
  enoughInjectives_modules_ringUniverse isGrothendieckAbelian_modules_ringUniverse

/-- The sections functor over an étale chart commutes with countable products. -/
instance preservesLimitsOfShape_nat_sectionsFunctor (U : SmallEtale B S hS X) :
    PreservesLimitsOfShape (Discrete ℕ)
      (Stacks.Cohomology.SiteInverseLimits.sectionsFunctor (smallEtaleRingedSite B S hS X hX) U) :=
  inferInstance

/-- A quasi-coherent module on an algebraic space has no higher cohomology on an affine étale
chart, in the derived-category indexing of the right derived functors. -/
theorem isZero_rightDerivedPlus_sectionsFunctor_of_isAffineChart
    (U : SmallEtale B S hS X) (hU : IsAffineChart B S hS X U)
    (M : Modules.{u, u} B S hS X hX) (hM : M.IsQuasicoherentOnSite) (p : ℤ) (hp : 1 ≤ p) :
    IsZero (((Stacks.Cohomology.SiteInverseLimits.sectionsFunctor
      (smallEtaleRingedSite B S hS X hX) U).rightDerivedPlus p).obj M) := by
  obtain ⟨n, rfl⟩ : ∃ n : ℕ, p = n := ⟨p.toNat, by omega⟩
  exact (Stacks.DerivedIndexing.isZero_rightDerived_obj_iff _ n M).1
    (isZero_rightDerived_sectionsFunctor_of_isAffineChart B S hS X hX M hM U hU n (by omega))

variable (U : SmallEtale B S hS X) (hU : IsAffineChart B S hS X U)
  (RF : DerivedCategory (Modules.{u, u} B S hS X hX) ⥤ DerivedCategory AddCommGrpCat.{u})
  (α : (Stacks.Cohomology.SiteInverseLimits.sectionsFunctor
      (smallEtaleRingedSite B S hS X hX) U).mapHomotopyCategory (ComplexShape.up ℤ) ⋙
      DerivedCategory.Qh ⟶ DerivedCategory.Qh ⋙ RF)
  [RF.IsRightDerivedFunctor α
    (HomotopyCategory.quasiIso (Modules.{u, u} B S hS X hX) (ComplexShape.up ℤ))]

include hU α in
/-- If `E` has quasi-coherent cohomology sheaves and lives in degrees `≤ c`, then so does
`RΓ(U, E)`, for every right derived functor `RΓ(U, -)` of the sections over an affine étale chart
`U`. -/
theorem isLE_rightDerived_sectionsFunctor_obj_of_isAffineChart
    (E : DerivedCategory (Modules.{u, u} B S hS X hX))
    (hqc : ∀ q : ℤ, ((DerivedCategory.homologyFunctor
      (Modules.{u, u} B S hS X hX) q).obj E).IsQuasicoherentOnSite)
    (c : ℤ) (hE : E.IsLE c) : (RF.obj E).IsLE c := by
  simpa using isLE_rightDerived_obj_of_isLE B S hS X hX
    (Stacks.Cohomology.SiteInverseLimits.sectionsFunctor (smallEtaleRingedSite B S hS X hX) U)
    RF α 1 (fun M hM p hp => isZero_rightDerivedPlus_sectionsFunctor_of_isAffineChart
      B S hS X hX U hU M hM p (by exact_mod_cast hp)) E hqc c hE

/-! ### Exactness of a complex of modules is tested on affine étale charts -/

omit hU in
/-- A cochain complex of `𝒪_X`-modules on an algebraic space is exact in degree `j` as soon as its
complex of sections over every affine étale chart is exact in degree `j`. -/
theorem exactAt_of_forall_isAffineChart (K : CochainComplex (Modules.{u, u} B S hS X hX) ℤ)
    (j : ℤ)
    (h : ∀ A : SmallEtale B S hS X, IsAffineChart B S hS X A →
      (((Stacks.Cohomology.SiteInverseLimits.sectionsFunctor
        (smallEtaleRingedSite B S hS X hX) A).mapHomologicalComplex
          (ComplexShape.up ℤ)).obj K).ExactAt j) :
    K.ExactAt j := by
  rw [K.exactAt_iff' (j - 1) j (j + 1) (by simp) (by simp)]
  refine Stacks.SheafOfModules.ComplexLocality.exact_of_locallyExact _ fun {V} z hz => ?_
  refine ⟨Sieve.coverByImage (AffineEtale.inclusion B S hS X) V,
    coverByImage_affineEtaleInclusion_mem B S hS X hX V, ?_⟩
  rintro W p ⟨⟨A, q, r, hqr⟩⟩
  have hA := h A.obj A.property
  rw [HomologicalComplex.exactAt_iff' _ (j - 1) j (j + 1) (by simp) (by simp),
    ShortComplex.ab_exact_iff] at hA
  obtain ⟨x, hx⟩ := hA ((K.X j).val.map r.op z)
    ((PresheafOfModules.naturality_apply (K.d j (j + 1)).val r.op z).trans
      ((congrArg ((K.X (j + 1)).val.map r.op) hz).trans (map_zero _)))
  refine ⟨(K.X (j - 1)).val.map q.op x, ?_⟩
  refine (PresheafOfModules.naturality_apply (K.d (j - 1) j).val q.op x).trans ?_
  refine (congrArg ((K.X j).val.map q.op) hx).trans ?_
  rw [← hqr]
  exact ((K.X j).val.map_comp_apply r.op q.op z).symm

/-! ### Sections of a K-injective complex over an affine étale chart -/

include hU in
/-- The complex of sections over an affine étale chart of a K-injective complex of `𝒪_X`-modules
with quasi-coherent cohomology vanishing above `c` is exact above `c`. -/
theorem exactAt_sections_of_isKInjective_of_isAffineChart
    (I : CochainComplex (Modules.{u, u} B S hS X hX) ℤ) (hI : I.IsKInjective)
    (hqc : ∀ q : ℤ, (I.homology q).IsQuasicoherentOnSite)
    (c : ℤ) (hc : ∀ q : ℤ, c < q → IsZero (I.homology q)) (j : ℤ) (hj : c < j) :
    (((Stacks.Cohomology.SiteInverseLimits.sectionsFunctor
        (smallEtaleRingedSite B S hS X hX) U).mapHomologicalComplex
          (ComplexShape.up ℤ)).obj I).ExactAt j := by
  set Fs := Stacks.Cohomology.SiteInverseLimits.sectionsFunctor
    (smallEtaleRingedSite B S hS X hX) U
  obtain ⟨hpw, hiso⟩ :=
    Functor.hasPointwiseRightDerivedFunctor_and_isIso_app_of_exists_quasiIso_isKInjective.{
      u + 1, u + 1, u + 1, u + 1, u + 1, u + 1}
    (Fs.mapHomotopyCategory (ComplexShape.up ℤ) ⋙ DerivedCategory.Qh)
    (exists_quasiIso_isKInjective_modules B S hS X hX)
  have : (Fs.mapHomotopyCategory (ComplexShape.up ℤ) ⋙ DerivedCategory.Qh).HasRightDerivedFunctor
      (HomotopyCategory.quasiIso (Modules.{u, u} B S hS X hX) (ComplexShape.up ℤ)) :=
    Functor.hasRightDerivedFunctor_of_hasPointwiseRightDerivedFunctor _ _
  let RF := (Fs.mapHomotopyCategory (ComplexShape.up ℤ) ⋙ DerivedCategory.Qh).totalRightDerived
    DerivedCategory.Qh
    (HomotopyCategory.quasiIso (Modules.{u, u} B S hS X hX) (ComplexShape.up ℤ))
  let α := (Fs.mapHomotopyCategory (ComplexShape.up ℤ) ⋙ DerivedCategory.Qh).totalRightDerivedUnit
    DerivedCategory.Qh
    (HomotopyCategory.quasiIso (Modules.{u, u} B S hS X hX) (ComplexShape.up ℤ))
  have hα := hiso DerivedCategory.Qh RF α I hI
  let E := DerivedCategory.Q.obj I
  have e (q : ℤ) := (DerivedCategory.homologyFunctorFactors (Modules.{u, u} B S hS X hX) q).app I
  have hEqc : ∀ q : ℤ, ((DerivedCategory.homologyFunctor
      (Modules.{u, u} B S hS X hX) q).obj E).IsQuasicoherentOnSite := fun q =>
    SheafOfModules.IsQuasicoherentOnSite.of_iso (e q).symm (hqc q)
  have hEc : E.IsLE c := by
    rw [DerivedCategory.isLE_iff]
    exact fun q hq => (hc q hq).of_iso (e q)
  have hLE := isLE_rightDerived_sectionsFunctor_obj_of_isAffineChart B S hS X hX U hU RF α E
    hEqc c hEc
  have hz : IsZero ((DerivedCategory.homologyFunctor AddCommGrpCat.{u} j).obj
      (RF.obj (DerivedCategory.Qh.obj ((HomotopyCategory.quotient _ _).obj I)))) :=
    (RF.obj E).isZero_of_isLE c j hj |>.of_iso
      ((DerivedCategory.homologyFunctor AddCommGrpCat.{u} j).mapIso
        (RF.mapIso ((DerivedCategory.quotientCompQhIso _).app I)))
  have hz' : IsZero ((DerivedCategory.homologyFunctor AddCommGrpCat.{u} j).obj
      (DerivedCategory.Q.obj ((Fs.mapHomologicalComplex (ComplexShape.up ℤ)).obj I))) :=
    hz.of_iso ((DerivedCategory.homologyFunctor AddCommGrpCat.{u} j).mapIso
      ((DerivedCategory.quotientCompQhIso _).app _).symm ≪≫
      (DerivedCategory.homologyFunctor AddCommGrpCat.{u} j).mapIso
        (@asIso _ _ _ _ (α.app ((HomotopyCategory.quotient _ _).obj I)) hα))
  rw [HomologicalComplex.exactAt_iff_isZero_homology]
  exact hz'.of_iso
    ((DerivedCategory.homologyFunctorFactors AddCommGrpCat.{u} j).app _).symm

end AlgebraicGeometry.Space

end
