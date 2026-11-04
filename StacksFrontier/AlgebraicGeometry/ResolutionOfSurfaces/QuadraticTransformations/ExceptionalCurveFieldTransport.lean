module

public import StacksFrontier.Algebra.Category.ModuleCat.Sheaf.PullbackInvertible.Basic
public import StacksFrontier.AlgebraicGeometry.MoreMorphisms.AffineStratification.ProjectiveSpace
public import StacksFrontier.AlgebraicGeometry.PicardUFD.ProjectiveSpaceCocycle
public import StacksFrontier.AlgebraicGeometry.ProjectiveCohomology.ModelComparison
public import StacksFrontier.AlgebraicGeometry.ProjectiveSpace.Cohomology.ProjectiveLineTopDimension
public import StacksFrontier.AlgebraicGeometry.ProjectiveSpace.Cohomology.ProjectiveLineVanishing
public import StacksFrontier.AlgebraicGeometry.PullbackPseudofunctor.Basic
public import StacksFrontier.AlgebraicGeometry.Surfaces.ExceptionalCurve
public import StacksFrontier.AlgebraicGeometry.Surfaces.ExceptionalCurveTwistSections
import StacksCore.Tactic.EgaSgaAttribute

/-!
# Changing the field an exceptional curve of the first kind is presented over

`AlgebraicGeometry.Scheme.IdealSheafData.IsExceptionalCurveOfFirstKind` is stated relative to a
chosen presentation `e : 𝐏¹_k ≅ E` of the curve as the projective line over a field `k`: it says
that `E` is an effective Cartier divisor and that its normal sheaf pulls back along `e` to `𝒪(-1)`.
This file shows that the property does not depend on the presentation, even between presentations
over two different fields.

In step 3 of [Stacks, Tag 0C5R](https://stacks.math.columbia.edu/tag/0C5R) the exceptional curve
`E` of the blowup at a closed point `x` is presented over `κ(x)` and the exceptional curve `E'` of
the blowup at `y` over `κ(y)`, by
`Stacks.Blowup.exists_isExceptionalCurveOfFirstKind_exceptionalIdeal_vanishingIdeal`; the source
identifies the two curves and so works over a single field, which this transport allows.

The point is the sign. That `θ^* 𝒪(-1)` is some twist `𝒪(m)` for an isomorphism `θ` of projective
lines is [Stacks, Tag 0BXJ], and `m = ±1` would follow from `θ^*` being an isomorphism of Picard
groups; ruling out `m = 1` needs an asymmetry between `𝒪(1)` and `𝒪(-1)` that survives an arbitrary
isomorphism of schemes. Having no cohomology at all characterises `-1` among the twists on the
projective line, because the vanishing range of [Stacks, Tag 01XU] is sharp at both ends.

## Main results

* `AlgebraicGeometry.isZero_Hgroup_twistingSheaf_neg_one` — `𝒪(-1)` on `𝐏¹_k` has no cohomology
  in any degree, in the `Hgroup` spelling. This is [Stacks, Tag 01XU] at `n = 1`.
* `AlgebraicGeometry.not_isZero_twistCohomology_zero_of_nonneg` — a nonnegative twist on `𝐏¹_k`
  has nonzero `H⁰`.
* `AlgebraicGeometry.not_isZero_twistCohomology_one_of_le_neg_two` — a twist below `-1` on `𝐏¹_k`
  has nonzero `H¹`.
* `AlgebraicGeometry.eq_neg_one_of_isZero_Hgroup_twistingSheaf` — if `𝒪(m)` on `𝐏¹_k` has
  vanishing `H⁰` and `H¹`, then `m = -1`.
* `AlgebraicGeometry.nonempty_iso_twistingSheaf_neg_one_of_isZero_Hgroup` — an invertible
  module on `𝐏¹_k` with vanishing `H⁰` and `H¹` is `𝒪(-1)`.
* `AlgebraicGeometry.nonempty_pullback_twistingSheaf_neg_one_iso` — an isomorphism of
  projective lines over two fields carries `𝒪(-1)` to `𝒪(-1)`.
* `AlgebraicGeometry.Scheme.IdealSheafData.isExceptionalCurveOfFirstKind_of_iso` — being an
  exceptional curve of the first kind does not depend on which field the curve is presented over.

## References

* [Stacks Project, Tag 0C5R](https://stacks.math.columbia.edu/tag/0C5R)
* [Stacks Project, Tag 0BXJ](https://stacks.math.columbia.edu/tag/0BXJ)
* [Stacks Project, Tag 01XU](https://stacks.math.columbia.edu/tag/01XU)
* [Stacks Project, Tag 0C2K](https://stacks.math.columbia.edu/tag/0C2K)
-/

@[expose] public noncomputable section

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits RingedSpaceModuleAdjunction
open Stacks.ProjectiveCohomology Stacks.ProjectiveSpace.Cohomology

universe u

namespace AlgebraicGeometry

attribute [local instance] MvPolynomial.gradedAlgebra

/-! ### The cohomology of `𝒪(-1)` on the projective line, in the `Hgroup` spelling -/

/-- `𝒪(-1)` on `𝐏¹_k` has no cohomology in any degree: [Stacks, Tag 01XU] at `n = 1`. -/
@[sga "6 VI 2.8" "partial"]
public theorem isZero_Hgroup_twistingSheaf_neg_one (k : Type u) [Field k] (q : ℕ) :
    IsZero (Hgroup (projectiveLineProj k).ringCatSheaf ⊤ q
      (ProjectiveSpectrum.Proj.twistingSheaf
        (MvPolynomial.homogeneousSubmodule (Fin 2) k) (-1))) := by
  refine (isZero_twistCohomology_iff_isZero_Hgroup k 1 (-1) q).mp ?_
  rcases eq_or_ne q 1 with rfl | hq1
  · exact isZero_twistCohomology_one_of_neg_one_le k le_rfl
  rcases Nat.lt_or_ge q 2 with hlt | hge
  · obtain rfl : q = 0 := by omega
    exact isZero_twistCohomology_zero_of_neg k (by norm_num)
  · exact isZero_twistCohomology_of_two_le k (-1) hge

/-! ### Which twist has no cohomology -/

/-- For `0 ≤ d`, the twist `𝒪(d)` on `𝐏¹_k` has nonzero `H⁰`. -/
public theorem not_isZero_twistCohomology_zero_of_nonneg (k : Type u) [Field k] {d : ℤ}
    (hd : 0 ≤ d) : ¬ IsZero (twistCohomology k 1 d 0) := by
  intro h
  have := ModuleCat.subsingleton_of_isZero ((twistCohomologyZeroIsoSections k 1 d).isZero_iff.mp h)
  exact (projectiveLineProjTwistSectionsBasis k d hd).ne_zero 0
    (Subsingleton.elim _ _)

/-- For `d ≤ -2`, the twist `𝒪(d)` on `𝐏¹_k` has nonzero `H¹`. -/
public theorem not_isZero_twistCohomology_one_of_le_neg_two (k : Type u) [Field k] {d : ℤ}
    (hd : d ≤ -2) : ¬ IsZero (twistCohomology k 1 d 1) := by
  intro h
  obtain ⟨n, hn⟩ : ∃ n : ℕ, d = -(n : ℤ) := ⟨(-d).toNat, by omega⟩
  have hn2 : 2 ≤ n := by omega
  have hrank := finrank_twistCohomology_line_top k n
  rw [← hn] at hrank
  have := ModuleCat.subsingleton_of_isZero h
  have hzero : Module.finrank k (twistCohomology k 1 d 1) = 0 := Module.finrank_zero_of_subsingleton
  omega

/-- If `H⁰` and `H¹` of the twist `𝒪(m)` on `𝐏¹_k` vanish, then `m = -1`. -/
public theorem eq_neg_one_of_isZero_Hgroup_twistingSheaf (k : Type u) [Field k] {m : ℤ}
    (h0 : IsZero (Hgroup (projectiveLineProj k).ringCatSheaf ⊤ 0
      (ProjectiveSpectrum.Proj.twistingSheaf
        (MvPolynomial.homogeneousSubmodule (Fin 2) k) m)))
    (h1 : IsZero (Hgroup (projectiveLineProj k).ringCatSheaf ⊤ 1
      (ProjectiveSpectrum.Proj.twistingSheaf
        (MvPolynomial.homogeneousSubmodule (Fin 2) k) m))) : m = -1 := by
  have hneg : m < 0 := by
    by_contra hge
    exact not_isZero_twistCohomology_zero_of_nonneg k (not_lt.mp hge)
      ((isZero_twistCohomology_iff_isZero_Hgroup k 1 m 0).mpr h0)
  have hge : -1 ≤ m := by
    by_contra hlt
    exact not_isZero_twistCohomology_one_of_le_neg_two k (by omega)
      ((isZero_twistCohomology_iff_isZero_Hgroup k 1 m 1).mpr h1)
  omega

/-- An invertible module on `𝐏¹_k` whose `H⁰` and `H¹` vanish is isomorphic to `𝒪(-1)`. -/
public theorem nonempty_iso_twistingSheaf_neg_one_of_isZero_Hgroup (k : Type u) [Field k]
    (L : (projectiveLineProj k).Modules)
    (hL : Stacks.SheafOfModules.IsInvertible (projectiveLineProj k).presheaf
      (projectiveLineProj k).ringCatIsSheaf L)
    (h0 : IsZero (Hgroup (projectiveLineProj k).ringCatSheaf ⊤ 0 L))
    (h1 : IsZero (Hgroup (projectiveLineProj k).ringCatSheaf ⊤ 1 L)) :
    Nonempty (L ≅ ProjectiveSpectrum.Proj.twistingSheaf
      (MvPolynomial.homogeneousSubmodule (Fin 2) k) (-1)) := by
  obtain ⟨m, ⟨φ⟩⟩ := Stacks.PicardUFD.exists_iso_twistingSheaf_general k 1 L hL
  have key (q : ℕ) (h : IsZero (Hgroup (projectiveLineProj k).ringCatSheaf ⊤ q L)) :=
    IsZero.of_iso h ((Hfunctor (projectiveLineProj k).ringCatSheaf ⊤ q).mapIso φ).symm
  have hm : m = -1 := eq_neg_one_of_isZero_Hgroup_twistingSheaf k (key 0 h0) (key 1 h1)
  exact ⟨hm ▸ φ⟩

/-! ### The pullback of `𝒪(-1)` along an isomorphism of projective lines -/

/-- For an isomorphism `θ : 𝐏¹_k ≅ 𝐏¹_{k'}` of projective lines over two fields,
`θ^* 𝒪_{k'}(-1) ≅ 𝒪_k(-1)`. -/
public theorem nonempty_pullback_twistingSheaf_neg_one_iso {k k' : Type u} [Field k] [Field k']
    (θ : projectiveLineProj k ≅ projectiveLineProj k') :
    Nonempty ((modulePullback θ.hom.toLRSHom.toShHom).obj
        (ProjectiveSpectrum.Proj.twistingSheaf
          (MvPolynomial.homogeneousSubmodule (Fin 2) k') (-1)) ≅
      ProjectiveSpectrum.Proj.twistingSheaf
        (MvPolynomial.homogeneousSubmodule (Fin 2) k) (-1)) := by
  have key (q : ℕ) := (Stacks.Cohomology.SchemeIso.isZero_Hgroup_pullback_iff θ _ q).mpr
    (isZero_Hgroup_twistingSheaf_neg_one k' q)
  have := Stacks.PicardUFD.isInvertible_twistingSheaf k' 1 (-1)
  exact nonempty_iso_twistingSheaf_neg_one_of_isZero_Hgroup k _
    (Stacks.RingedSpace.modulePullback_isInvertible θ.hom.toLRSHom.toShHom _) (key 0) (key 1)

/-! ### The transport of the exceptional-curve property -/

/-- If the subscheme cut out by `D` is presented as the projective line both over `k'` and
over `k`, and `D` is an exceptional curve of the first kind for the first presentation, then it
is one for the second. -/
public theorem Scheme.IdealSheafData.isExceptionalCurveOfFirstKind_of_iso {X : Scheme.{u}}
    {D : X.IdealSheafData} {k k' : Type u} [Field k] [Field k']
    (e : projectiveLineProj k ≅ D.subscheme) (e' : projectiveLineProj k' ≅ D.subscheme)
    (hE' : D.IsExceptionalCurveOfFirstKind k' e') : D.IsExceptionalCurveOfFirstKind k e := by
  obtain ⟨φ⟩ := hE'.2
  obtain ⟨ψ⟩ := nonempty_pullback_twistingSheaf_neg_one_iso (e ≪≫ e'.symm)
  refine ⟨hE'.1, ⟨?_⟩⟩
  have hcomp : (e ≪≫ e'.symm).hom.toLRSHom.toShHom ≫ e'.hom.toLRSHom.toShHom =
      e.hom.toLRSHom.toShHom :=
    by rw [← LocallyRingedSpace.comp_toShHom, ← Scheme.Hom.comp_toLRSHom]; simp
  refine ((Stacks.RingedSpace.modulePullbackCongr hcomp).app _).symm ≪≫ ?_
  refine ((Stacks.RingedSpace.modulePullbackComp (e ≪≫ e'.symm).hom.toLRSHom.toShHom
    e'.hom.toLRSHom.toShHom).app _).symm ≪≫ ?_
  exact (modulePullback (e ≪≫ e'.symm).hom.toLRSHom.toShHom).mapIso φ ≪≫ ψ

end AlgebraicGeometry

end
