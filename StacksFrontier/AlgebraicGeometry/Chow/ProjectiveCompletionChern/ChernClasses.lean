module

public import StacksFrontier.AlgebraicGeometry.Chow.ProjectiveCompletionChern.KoszulDerived
public import StacksFrontier.AlgebraicGeometry.Chow.ChernClassDerived.Criteria
public import StacksFrontier.AlgebraicGeometry.Chow.ChernClassDerived.DerivedChernClasses
public import StacksFrontier.AlgebraicGeometry.Chow.ProjectiveBundleFormula.Formula

/-!
# The Chern classes of `i_* 𝒪_X` on the projective completion

Let `X` be locally of finite type over the base of chapter 42, `𝒞` finite locally free of rank
`r`, `π : E = Proj_X(Sym^*(𝒞)[T]) ⟶ X` the projective completion and `i : X ⟶ E` its zero section.
The Koszul complex of `φ : 𝒦 ⟶ 𝒪_E`, `𝒦 = Ker(π^*(𝒞 ⊕ 𝒪_X) ⟶ 𝒪_E(1))` of rank `r`, resolves
`i_* 𝒪_X`, so `i_* 𝒪_X` is represented by a bounded complex of finite locally free modules, its
Chern classes are defined (Stacks 0GUE (2)), and its total Chern class is the alternating product
`∏_n c(⋀ⁿ 𝒦)^{(-1)ⁿ}` of the Koszul complex. By Stacks 0FEE this vanishes in the degrees
`1, …, r - 1` and is `-(r - 1)! c_r(𝒦)` in degree `r`.

## Main definitions

* `Stacks.Chow.ProjectiveCompletion.zeroSecObject`: `i_* 𝒪_X` as an object of `D(𝒪_E)`.

## Main results

* `Stacks.Chow.ProjectiveCompletion.hasDefinedChernClasses_zeroSecObject`: its Chern classes are
  defined.
* `Stacks.Chow.ProjectiveCompletion.perfectChernClass_zeroSecObject_eq_zero`: `c_t(i_* 𝒪_X) = 0`
  for `t = 1, …, r - 1`, the first conclusion of Stacks 0FEF.
* `Stacks.Chow.ProjectiveCompletion.homComponent_perfectChernClass_zeroSecObject_rank`:
  `c_r(i_* 𝒪_X) = -(r - 1)! c_r(𝒦)`.

## References

* [Stacks Project, Tag 0FEF](https://stacks.math.columbia.edu/tag/0FEF)
* [Stacks Project, Tag 0FEE](https://stacks.math.columbia.edu/tag/0FEE)
* [Stacks Project, Tag 0GUE](https://stacks.math.columbia.edu/tag/0GUE)
-/

@[expose] public noncomputable section

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits StrictlyPerfect

universe u

namespace Stacks.Chow.ProjectiveCompletion

attribute [local instance 2000] HasDerivedCategory.standard

variable {X : Scheme.{u}} (𝒞 : X.Modules)
  [AlgebraicGeometry.SheafOfModules.IsFiniteLocallyFree.{u, u, u} 𝒞] (r : ℕ)
  [AlgebraicGeometry.SheafOfModules.IsFiniteLocallyFreeOfRank.{u, u, u} 𝒞 r]

attribute [local instance] isFiniteLocallyFreeOfRank_kernelModule

/-- **`i_* 𝒪_X` as an object of `D(𝒪_E)`**, in degree zero. -/
abbrev zeroSecObject : DerivedCategory (space 𝒞).Modules :=
  (DerivedCategory.singleFunctor (space 𝒞).Modules 0).obj (zeroSecUnit 𝒞 r)

/-- The Koszul complex of `φ` vanishes in the degrees below `-r`. -/
theorem isZero_koszulComplex_X_of_lt {m : ℤ} (hm : m < -(r : ℤ)) :
    IsZero ((Scheme.Modules.koszulComplex (kernelModule 𝒞) (koszulMap 𝒞)).X m) := by
  obtain ⟨n, rfl⟩ : ∃ n : ℕ, -(n : ℤ) = m := ⟨(-m).toNat, by omega⟩
  have h := isFiniteLocallyFreeOfRank_koszulComplex (kernelModule 𝒞) (koszulMap 𝒞) r (-(n : ℤ))
  rw [koszulRank_neg, Nat.choose_eq_zero_of_lt (by omega)] at h
  exact isZero_of_isFiniteLocallyFreeOfRank_zero _

include r in
/-- The Koszul complex of `φ` is bounded. -/
theorem bounded_koszulComplex :
    CochainComplex.bounded (space 𝒞).Modules
      (Scheme.Modules.koszulComplex (kernelModule 𝒞) (koszulMap 𝒞)) :=
  (CochainComplex.bounded_iff _).2 ⟨-(r : ℤ), 0,
    (CochainComplex.isStrictlyGE_iff _ _).2 fun _ hi => isZero_koszulComplex_X_of_lt 𝒞 r hi,
    (CochainComplex.isStrictlyLE_iff _ _).2 fun _ hi =>
      Scheme.Modules.isZero_koszulComplex_X _ _ hi⟩

include r in
/-- The terms of the Koszul complex of `φ` are finite locally free. -/
theorem isFiniteLocallyFree_koszulComplex_X (m : ℤ) :
    SheafOfModules.IsFiniteLocallyFree (R := structureSheafOfRings (space 𝒞).toRingedSpace)
      ((Scheme.Modules.koszulComplex (kernelModule 𝒞) (koszulMap 𝒞)).X m) :=
  ⟨(AlgebraicGeometry.SheafOfModules.IsFiniteLocallyFreeOfRank.isFiniteLocallyFree _
    (koszulRank r m) (hM := isFiniteLocallyFreeOfRank_koszulComplex (kernelModule 𝒞)
      (koszulMap 𝒞) r m)).exists_isFiniteLocallyFreeData⟩

include r in
/-- The Koszul complex of `φ` is a locally bounded complex of finite locally free modules. -/
theorem isLocallyBoundedFiniteLocallyFree_koszulComplex :
    IsLocallyBoundedFiniteLocallyFree
      (Scheme.Modules.koszulComplex (kernelModule 𝒞) (koszulMap 𝒞)) :=
  isLocallyBoundedFiniteLocallyFree_of_bounded _ (bounded_koszulComplex 𝒞 r)
    (isFiniteLocallyFree_koszulComplex_X 𝒞 r)

/-- **The Chern classes of `i_* 𝒪_X` are defined**: it is represented by the Koszul complex of
`φ`, a bounded complex of finite locally free modules. -/
theorem hasDefinedChernClasses_zeroSecObject : HasDefinedChernClasses (zeroSecObject 𝒞 r) :=
  hasDefinedChernClasses_of_bounded_isFiniteLocallyFree _ _ (bounded_koszulComplex 𝒞 r)
    (isFiniteLocallyFree_koszulComplex_X 𝒞 r) ⟨koszulComplexIso 𝒞 r⟩

include r in
/-- The projective completion is locally of finite type over `X`. -/
theorem locallyOfFiniteType_proj : LocallyOfFiniteType (proj 𝒞) :=
  have := isFiniteLocallyFreeOfRank_module 𝒞 r
  locallyOfFiniteType_bundleProj (module 𝒞) r

variable (C : ChowSituation.{u}) (sX : X ⟶ C.S) [LocallyOfFiniteType sX]

include r in
/-- The projective completion is locally of finite type over the base. -/
theorem locallyOfFiniteType_proj_comp : LocallyOfFiniteType (proj 𝒞 ≫ sX) :=
  have := locallyOfFiniteType_proj 𝒞 r
  locallyOfFiniteType_comp _ _

/-- **The total Chern class of `i_* 𝒪_X` is that of its Koszul resolution.** -/
theorem perfectChernClass_zeroSecObject :
    letI := locallyOfFiniteType_proj_comp 𝒞 r C sX
    perfectChernClass C (proj 𝒞 ≫ sX) (hasDefinedChernClasses_zeroSecObject 𝒞 r) =
      complexChernBounded C (proj 𝒞 ≫ sX)
        (Scheme.Modules.koszulComplex (kernelModule 𝒞) (koszulMap 𝒞)) (koszulRank r)
        (isFiniteLocallyFreeOfRank_koszulComplex (kernelModule 𝒞) (koszulMap 𝒞) r) := by
  let := locallyOfFiniteType_proj_comp 𝒞 r C sX
  exact (perfectChernClass_eq_complexChern C (proj 𝒞 ≫ sX) _
    (isLocallyBoundedFiniteLocallyFree_koszulComplex 𝒞 r) (koszulComplexIso 𝒞 r)).trans
    (complexChern_eq_complexChernBounded C (proj 𝒞 ≫ sX) _ _ _)

/-- **Stacks 0FEF, the first conclusion**: `c_t(i_* 𝒪_X) = 0` for `t = 1, …, r - 1`, for the zero
section `i : X ⟶ E` of the projective completion `E = Proj_X(Sym^*(𝒞)[T])` of a locally free
module `𝒞` of rank `r`. -/
theorem perfectChernClass_zeroSecObject_eq_zero (t : ℕ) (ht0 : 0 < t) (ht : t < r) :
    letI := locallyOfFiniteType_proj_comp 𝒞 r C sX
    perfectChernClass C (proj 𝒞 ≫ sX) (hasDefinedChernClasses_zeroSecObject 𝒞 r) t = 0 := by
  let := locallyOfFiniteType_proj_comp 𝒞 r C sX
  have h := homComponent_complexChernBounded_koszulComplex_of_lt C (proj 𝒞 ≫ sX)
    (kernelModule 𝒞) (koszulMap 𝒞) r ht0 ht
  rw [← perfectChernClass_zeroSecObject 𝒞 r C sX] at h
  have h' := congrArg (fun c : TotalChowClass C (proj 𝒞 ≫ sX) => c t) h
  rw [TotalChowClass.homComponent_apply, ite_eq_left rfl] at h'
  exact h'

/-- **The top Chern class of `i_* 𝒪_X`**: `c_r(i_* 𝒪_X) = -(r - 1)! c_r(𝒦)` for `r ≥ 1`. -/
theorem homComponent_perfectChernClass_zeroSecObject_rank (hr : r ≠ 0) :
    letI := locallyOfFiniteType_proj_comp 𝒞 r C sX
    TotalChowClass.homComponent r
        (perfectChernClass C (proj 𝒞 ≫ sX) (hasDefinedChernClasses_zeroSecObject 𝒞 r)) =
      -((r - 1).factorial • TotalChowClass.homComponent r
        (totalChern C (proj 𝒞 ≫ sX) (kernelModule 𝒞) r)) := by
  let := locallyOfFiniteType_proj_comp 𝒞 r C sX
  rw [perfectChernClass_zeroSecObject 𝒞 r C sX]
  exact homComponent_complexChernBounded_koszulComplex_rank C (proj 𝒞 ≫ sX) (kernelModule 𝒞)
    (koszulMap 𝒞) r hr

end Stacks.Chow.ProjectiveCompletion

end
