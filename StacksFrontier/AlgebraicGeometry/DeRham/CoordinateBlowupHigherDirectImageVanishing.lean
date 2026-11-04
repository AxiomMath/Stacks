module

public import StacksFrontier.AlgebraicGeometry.Divisors.EtaPullbackAffineChart
public import StacksFrontier.AlgebraicGeometry.AffineHigherDirectImage.SecondLegCollapse
public import StacksFrontier.AlgebraicGeometry.Cohomology.AffineCoveringNumber.Basic
public import StacksFrontier.AlgebraicGeometry.Cohomology.Cech.AffineIntersectionComparison
public import StacksFrontier.AlgebraicGeometry.DeRham.BlowupFormsDerivedComparison
public import StacksFrontier.AlgebraicGeometry.DeRham.BlowupFormsPoleBound
public import StacksFrontier.AlgebraicGeometry.DeRham.CoordinateBlowupFormsGlobalSections
public import StacksFrontier.AlgebraicGeometry.DeRham.FormsDirectImageSection
public import StacksFrontier.AlgebraicGeometry.HigherDirectImageQcqs.AffineBaseSectionsNatIndexed
public import StacksFrontier.AlgebraicGeometry.MoreMorphisms.CoordinateBlowupSmooth

/-!
# Higher direct images along the coordinate blowup vanish in degrees `≥ n`

Fix a ring `R`, put `S = Spec R`, and let `b : L ⟶ X = 𝐀^{m+n}_S` be the blowing up of `X` along
the coordinate subspace `Z = 𝐀^m_S` (Section 0FUB of the Stacks project). For every
quasi-coherent `𝒪_L`-module `F` and every `q ≥ n`,

`H^q(Rb_*F) = R^q b_*F = 0`,

in particular for `F = Ω^a_{L/S}` and every `a`. This is the vanishing that the uniqueness half of
the proof of [Stacks, Tag 0G5J] reads off, on the coordinate model, from clause (3) of
[Stacks, Tag 0FUR] (or 0FUU) together with the bound on the fibre dimension of `E ⟶ Z`
([Stacks, Tag 0E7D]).

## The proof

It does not go through clause (3). The blowup `L` is separated, `b` being separated and `X`
affine, and the `n` standard charts `Spec A[I/y_i]` cover it, so by [Stacks, Tag 01XI] the
cohomology `H^q(L, F)` of a quasi-coherent module vanishes in every degree `q ≥ n`. On the affine
base `X` the module `R^q b_*F` is quasi-coherent with global sections `H^q(L, F)`
([Stacks, Tag 01XK]), hence zero; and `R^q b_*F` is the `q`-th cohomology sheaf of the derived
direct image `Rb_*(F[0])`.

## Main results

* `Stacks.DeRham.isZero_homology_schemeDerivedPushforward_of_isZero_rightDerived`: over an
  affine base, `H^q(Rf_*F) = 0` as soon as `H^q(X, F) = 0`, for qcqs `f` and quasi-coherent `F`.
* `Stacks.DeRham.isZero_rightDerived_sections_coordinateBlowup`: `H^q(L, F) = 0` for `q ≥ n`.
* `Stacks.DeRham.isZero_homology_coordinateBlowupDerivedPushforward`: `H^q(Rb_*F) = 0` for
  `q ≥ n`.
* `Stacks.DeRham.isZero_homology_coordinateBlowupFormsDerivedDirectImage`:
  `H^q(Rb_*Ω^a_{L/S}) = 0` for `q ≥ n`.

No `@[stacks]` attribute: the statement is a step inside the proof of [Stacks, Tag 0G5J].

## References

* [Stacks Project, Tag 0FUR](https://stacks.math.columbia.edu/tag/0FUR)
* [Stacks Project, Tag 0G5J](https://stacks.math.columbia.edu/tag/0G5J)
* [Stacks Project, Tag 01XI](https://stacks.math.columbia.edu/tag/01XI)
* [Stacks Project, Tag 01XK](https://stacks.math.columbia.edu/tag/01XK)
-/

@[expose] public noncomputable section

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits Opposite TopologicalSpace

universe u

attribute [local instance 10000] HasDerivedCategory.standard

namespace Stacks.DeRham

/-- **Over an affine base, `H^q(Rf_*F)` vanishes with `H^q(X, F)`.** For a quasi-compact and
quasi-separated `f : X ⟶ S` with `S` affine and a quasi-coherent `F`, the module `R^q f_*F` is
quasi-coherent with global sections `H^q(X, F)` ([Stacks, Tag 01XK]), so it is zero when
`H^q(X, F)` is; and `R^q f_*F` is the `q`-th cohomology sheaf of `Rf_*(F[0])`. -/
theorem isZero_homology_schemeDerivedPushforward_of_isZero_rightDerived {X S : Scheme.{u}}
    (f : X ⟶ S) [QuasiCompact f] [QuasiSeparated f] [IsAffine S] (F : X.Modules)
    [F.IsQuasicoherent] (q : ℕ)
    (h : IsZero (((_root_.SheafOfModules.evaluation X.ringCatSheaf (op ⊤)).rightDerived q).obj
      F)) :
    IsZero ((DerivedCategory.homologyFunctor S.Modules (q : ℤ)).obj
      ((schemeDerivedPushforward f).obj ((DerivedCategory.singleFunctor X.Modules 0).obj F))) := by
  have h1 := Stacks.AlgebraicGeometry.HigherDirectImageQcoh.sectionsRightDerivedPushforwardIso
    f F q
  have h2 : IsZero (((Scheme.Modules.pushforward f).rightDerived q).obj F) := by
    refine Stacks.Divisors.Eta.isZero_of_subsingleton_sections_top _ ?_
    have := ((ModuleCat.restrictScalars f.appTop.hom).map_isZero h).of_iso h1.symm
    exact ModuleCat.isZero_iff_subsingleton.mp this
  have h3 := (Stacks.DerivedIndexing.isZero_rightDerived_obj_iff
    (Scheme.Modules.pushforward f) q F).1 h2
  obtain ⟨e⟩ := Stacks.AffineHigherDirectImage.nonempty_homologyFunctor_derivedPushforward_iso
    f F (q : ℤ)
  exact h3.of_iso e

variable (R : Type u) [CommRing R] (m n : ℕ)

/-- **The coordinate blowup is separated**: the blowing-up morphism is separated and its target
`𝐀^{m+n}_S` is affine. -/
instance isSeparated_coordinateBlowup : (coordinateBlowup R m n).IsSeparated := by
  constructor
  rw [← terminal.comp_from (coordinateBlowupToAmbient R m n)]
  infer_instance

/-- **The `n` standard charts cover the coordinate blowup**, as a supremum of affine opens. -/
theorem iSup_coordinateChartOpen :
    ⨆ i : Fin n, (coordinateChartOpen R m n i).1 = ⊤ := by
  refine eq_top_iff.mpr fun x _ => ?_
  obtain ⟨i, y, hy⟩ := Stacks.MoreMorphisms.exists_mem_range_coordinateBlowupChart R m n x
  exact TopologicalSpace.Opens.mem_iSup.mpr ⟨i, ⟨y, hy⟩⟩

/-- **`H^q(L, F) = 0` for `q ≥ n`** and every quasi-coherent `𝒪_L`-module `F`: the separated
scheme `L` is covered by the `n` affine standard charts ([Stacks, Tag 01XI]). -/
theorem isZero_rightDerived_sections_coordinateBlowup (F : (coordinateBlowup R m n).Modules)
    [F.IsQuasicoherent] (q : ℕ) (hq : n ≤ q) :
    IsZero (((_root_.SheafOfModules.evaluation (coordinateBlowup R m n).ringCatSheaf
      (op ⊤)).rightDerived q).obj F) :=
  Stacks.Cohomology.Cech.isZero_rightDerived_evaluation_of_isZero_hgroup _ ⊤ F q
    (Stacks.AlgebraicGeometry.AffineCoveringNumber.isZero_cohomology_of_finite_affine_cover _
      (fun i : Fin n => (coordinateChartOpen R m n i).1) (fun i => (coordinateChartOpen R m n i).2)
      (iSup_coordinateChartOpen R m n) F q hq)

/-- **`H^q(Rb_*F) = 0` for `q ≥ n`** and every quasi-coherent `𝒪_L`-module `F`, where
`b : L ⟶ X` is the coordinate blowup. -/
theorem isZero_homology_coordinateBlowupDerivedPushforward
    (F : (coordinateBlowup R m n).Modules) [F.IsQuasicoherent] (q : ℤ) (hq : (n : ℤ) ≤ q) :
    IsZero ((DerivedCategory.homologyFunctor _ q).obj
      ((schemeDerivedPushforward (coordinateBlowupToAmbient R m n)).obj
        ((DerivedCategory.singleFunctor _ 0).obj F))) := by
  obtain ⟨q, rfl⟩ : ∃ k : ℕ, q = k := ⟨q.toNat, by omega⟩
  exact isZero_homology_schemeDerivedPushforward_of_isZero_rightDerived _ F q
    (isZero_rightDerived_sections_coordinateBlowup R m n F q (by omega))

/-- **`H^q(Rb_*Ω^a_{L/S}) = 0` for `q ≥ n`**, for every `a ≥ 0`: the vanishing on the coordinate
model that the uniqueness half of the proof of [Stacks, Tag 0G5J] uses. -/
theorem isZero_homology_coordinateBlowupFormsDerivedDirectImage (a : ℕ) (q : ℤ)
    (hq : (n : ℤ) ≤ q) :
    IsZero ((DerivedCategory.homologyFunctor _ q).obj
      ((schemeDerivedPushforward (coordinateBlowupToAmbient R m n)).obj
        (formsSingle (coordinateBlowupToBase R m n) a))) :=
  have := Scheme.Hom.isQuasicoherent_relativeDifferentialForms (coordinateBlowupToBase R m n) a
  isZero_homology_coordinateBlowupDerivedPushforward R m n _ q hq

end Stacks.DeRham
