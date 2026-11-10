module

public import StacksFrontier.AlgebraicGeometry.Curves.StableContraction.TricanonicalEmbedding
public import StacksFrontier.AlgebraicGeometry.Variety.Curve.NonpositiveDegreeSection
public import StacksFrontier.AlgebraicGeometry.AffineNonvanishing.Basic
public import StacksFrontier.AlgebraicGeometry.Ample.Defs
public import StacksFrontier.AlgebraicGeometry.ProjectionFormula.HigherDirectImage
public import StacksFrontier.AlgebraicGeometry.Curves.ComplementaryCurve.DualizingSheaf
public import StacksFrontier.AlgebraicGeometry.Curves.ComplementaryCurve.IntersectionDegree
public import StacksFrontier.AlgebraicGeometry.Curves.ContractingRationalTails.GeometricallyIntegral
public import StacksFrontier.AlgebraicGeometry.Curves.VanishingResults.AutomaticProperties

/-!
# Ample invertible modules have positive degree on curves

Let `L` be an ample invertible module on a scheme `Y` and `g : C ⟶ Y` a morphism from a proper
integral curve over a field `k`. Some section of a positive power `L^{⊗ n}` does not vanish at
the image of a point of `C`, so its pullback is a nonzero section of `g^*(L^{⊗ n})`, which has
nonnegative degree by [Stacks, Tag 0B40]; hence `deg(g^*L) ≥ 0`. If `g` is affine and the curve
has dimension one, the pulled-back section has an affine nonvanishing locus, which is not the
whole (non-affine) curve, so the section vanishes somewhere and the degree is positive.

This is the half of "a nodal curve with ample dualizing sheaf has no rational tail" that does
not use [Stacks, Tag 0E63]: the dualizing sheaf restricted to a rational tail has negative
degree.

## Main results

* `AlgebraicGeometry.invertibleCurveDegree_pullback_nonneg_of_isAmple`.
* `AlgebraicGeometry.topologicalKrullDim_le_zero_of_isAffine`: an affine scheme proper over a
  field has dimension zero.
* `AlgebraicGeometry.invertibleCurveDegree_pullback_pos_of_isAmple_of_isAffineHom`.
* `AlgebraicGeometry.not_isRationalTail_of_isAmple_dualizingSheafOverField`: a reduced curve with
  `H⁰ = k` and invertible ample dualizing sheaf has no rational tail, given that `ω_C` is
  invertible over `Γ(C, 𝒪_C)` for the would-be tail `C`.

## References

* [Stacks Project, Tag 0B40](https://stacks.math.columbia.edu/tag/0B40)
* [Stacks Project, Tag 0E63](https://stacks.math.columbia.edu/tag/0E63)
* [Stacks Project, Tag 0E7Q](https://stacks.math.columbia.edu/tag/0E7Q)
-/

@[expose] public noncomputable section

open CategoryTheory Opposite

universe u

namespace AlgebraicGeometry

/-- A section of some `L^{⊗ n}`, `n ≥ 1`, pulls back to a nonzero section of `g^*(L^{⊗ n})`, so
`n · deg(g^*L)` is nonnegative, and positive if `g` is affine unless the curve is affine. -/
private theorem exists_pos_mul_degree_pullback (k : Type u) [Field k]
    {C Y : Scheme.{u}} (f : C ⟶ Spec (.of k)) [IsProper f] [IsIntegral C]
    (hdim : topologicalKrullDim C ≤ 1) (g : C ⟶ Y) (L : Y.Modules)
    [SheafOfModules.IsInvertible Y.presheaf Y.ringCatSheaf.2 L]
    [SheafOfModules.IsInvertible C.presheaf C.ringCatSheaf.2 ((Scheme.Modules.pullback g).obj L)]
    (hL : Scheme.Modules.IsAmple Y L) :
    ∃ n : ℕ, 0 < n ∧ 0 ≤ (n : ℤ) * invertibleCurveDegree k f hdim
        ((Scheme.Modules.pullback g).obj L) ∧
      (IsAffineHom g → IsAffine C ∨
        0 < (n : ℤ) * invertibleCurveDegree k f hdim ((Scheme.Modules.pullback g).obj L)) := by
  obtain ⟨x⟩ : Nonempty C := inferInstance
  obtain ⟨n, hn, s, hgx, haff⟩ := hL.exists_affine_nonvanishingLocus (g x)
  let Ln := Stacks.SheafOfModules.Invertible.tensorPower Y.presheaf Y.ringCatSheaf.2 L (n : ℤ)
  have hLn : Stacks.SheafOfModules.IsInvertible Y.presheaf
      (structureSheafRing Y.toRingedSpace).property Ln :=
    Scheme.Modules.isInvertible_tensorPower Y L n
  let : SheafOfModules.IsInvertible C.presheaf C.ringCatSheaf.2
      ((Scheme.Modules.pullback g).obj Ln) :=
    Stacks.Modules.isInvertible_pullback g _
  have hx : x ∈ g ⁻¹ᵁ Stacks.SheafOfModules.nonvanishingOpen (X := Y.toRingedSpace) Ln s := hgx
  have haffC : IsAffineHom g → IsAffineOpen
      (g ⁻¹ᵁ Stacks.SheafOfModules.nonvanishingOpen (X := Y.toRingedSpace) Ln s) :=
    fun _ => haff.preimage g
  rw [Stacks.SheafOfModules.preimage_nonvanishingOpen g Ln s] at hx haffC
  have hne := eval_top_ne_zero_of_mem_nonvanishingLocus _ _ hx
  have : Stacks.SheafOfModules.IsInvertible C.sheaf.obj C.ringCatSheaf.property
      ((Scheme.Modules.pullback g).obj Ln) :=
    Stacks.ProjectionFormula.isInvertible_schemeModulesPullback g Ln
  have hdeg := invertibleCurveDegree_pullback_tensorPower g f hdim L n
  refine ⟨n, hn, ?_, fun hg => ?_⟩
  · rw [← hdeg]
    exact invertibleCurveDegree_nonneg_of_eval_top_ne_zero k f hdim
      ((Scheme.Modules.pullback g).obj Ln) _ hne
  · by_cases hzero : ∃ y : C, y ∉ Stacks.SheafOfModules.nonvanishingLocus (X := C.toRingedSpace)
        ((Scheme.Modules.pullback g).obj Ln)
        (Stacks.SheafOfModules.modulePullbackSection g.toLRSHom Ln s)
    · rw [← hdeg]
      exact Or.inr (invertibleCurveDegree_pos_of_eval_top_ne_zero k f hdim
        ((Scheme.Modules.pullback g).obj Ln) _ hne hzero)
    · push Not at hzero
      have htop : IsAffineOpen (⊤ : C.Opens) := by
        convert haffC hg using 1
        ext y
        exact ⟨fun _ => hzero y, fun _ => trivial⟩
      have : IsAffine (⊤ : C.Opens).toScheme := htop
      exact Or.inl (IsAffine.of_isIso C.topIso.inv)

/-- **The pullback of an ample invertible module to a proper integral curve has nonnegative
degree**: a section of some `L^{⊗ n}`, `n ≥ 1`, not vanishing at the image of a point pulls back
to a nonzero section of `g^*(L^{⊗ n})` ([Stacks, Tag 0H78]), whose degree `n · deg(g^*L)` is then
nonnegative ([Stacks, Tag 0B40]). -/
theorem invertibleCurveDegree_pullback_nonneg_of_isAmple (k : Type u) [Field k]
    {C Y : Scheme.{u}} (f : C ⟶ Spec (.of k)) [IsProper f] [IsIntegral C]
    (hdim : topologicalKrullDim C ≤ 1) (g : C ⟶ Y) (L : Y.Modules)
    [SheafOfModules.IsInvertible Y.presheaf Y.ringCatSheaf.2 L]
    (hL : Scheme.Modules.IsAmple Y L) :
    letI : SheafOfModules.IsInvertible C.presheaf C.ringCatSheaf.2
        ((Scheme.Modules.pullback g).obj L) :=
      Stacks.Modules.isInvertible_pullback g _
    0 ≤ invertibleCurveDegree k f hdim ((Scheme.Modules.pullback g).obj L) := by
  let : SheafOfModules.IsInvertible C.presheaf C.ringCatSheaf.2
      ((Scheme.Modules.pullback g).obj L) :=
    Stacks.Modules.isInvertible_pullback g _
  obtain ⟨n, hn, h0, -⟩ := exists_pos_mul_degree_pullback k f hdim g L hL
  exact nonneg_of_mul_nonneg_right h0 (by exact_mod_cast hn)

/-- **An affine scheme proper over a field has dimension zero**: its ring of global functions is
finite-dimensional over the field ([Stacks, Tag 02O6]), hence Artinian. -/
theorem topologicalKrullDim_le_zero_of_isAffine (k : Type u) [Field k] {C : Scheme.{u}}
    (f : C ⟶ Spec (.of k)) [IsProper f] [IsAffine C] : topologicalKrullDim C ≤ 0 := by
  let : Algebra k Γ(C, ⊤) := ((Scheme.ΓSpecIso (.of k)).inv ≫ f.appTop).hom.toAlgebra
  have := forall_finiteDimensional_cohomologyOverField_unit k f 0
  have : FiniteDimensional k Γ(C, ⊤) :=
    Module.Finite.equiv (cohomologyOverFieldZeroIsoSections k f
      (SheafOfModules.unit C.ringCatSheaf)).toLinearEquiv
  have : IsArtinianRing Γ(C, ⊤) := IsArtinianRing.of_finite k Γ(C, ⊤)
  have h := (isArtinianRing_iff_krullDimLE_zero (R := Γ(C, ⊤))).mp inferInstance
  rw [Ring.KrullDimLE, Order.krullDimLE_iff, ← ringKrullDim, Nat.cast_zero,
    ← PrimeSpectrum.topologicalKrullDim_eq_ringKrullDim Γ(C, ⊤)] at h
  rwa [IsHomeomorph.topologicalKrullDim_eq _ C.isoSpec.hom.homeomorph.isHomeomorph]

/-- **The pullback of an ample invertible module along an affine morphism out of a proper
integral curve has positive degree**: a section `s` of some `L^{⊗ n}`, `n ≥ 1`, with `Y_s` affine
and meeting the image pulls back to a nonzero section whose nonvanishing locus `g⁻¹Y_s` is
affine, hence not all of the curve, which is proper of dimension one; so the section vanishes
somewhere and `n · deg(g^*L) > 0` ([Stacks, Tag 0B40]). -/
theorem invertibleCurveDegree_pullback_pos_of_isAmple_of_isAffineHom (k : Type u) [Field k]
    {C Y : Scheme.{u}} (f : C ⟶ Spec (.of k)) [IsProper f] [IsIntegral C]
    (hdim : topologicalKrullDim C = 1) (g : C ⟶ Y) [IsAffineHom g] (L : Y.Modules)
    [SheafOfModules.IsInvertible Y.presheaf Y.ringCatSheaf.2 L]
    (hL : Scheme.Modules.IsAmple Y L) :
    letI : SheafOfModules.IsInvertible C.presheaf C.ringCatSheaf.2
        ((Scheme.Modules.pullback g).obj L) :=
      Stacks.Modules.isInvertible_pullback g _
    0 < invertibleCurveDegree k f hdim.le ((Scheme.Modules.pullback g).obj L) := by
  let : SheafOfModules.IsInvertible C.presheaf C.ringCatSheaf.2
      ((Scheme.Modules.pullback g).obj L) :=
    Stacks.Modules.isInvertible_pullback g _
  obtain ⟨n, hn, -, h0⟩ := exists_pos_mul_degree_pullback k f hdim.le g L hL
  rcases h0 inferInstance with hC | h0
  · have := topologicalKrullDim_le_zero_of_isAffine k f
    rw [hdim] at this
    exact absurd this (by decide)
  · exact pos_of_mul_pos_right h0 (by positivity)

/-- **A curve with ample dualizing sheaf has no rational tail.** Let `X` be reduced and proper of
dimension one over `k` with `H⁰(X, 𝒪_X) = k`, with `ω_X` invertible and ample, and let `C` be an
integral closed subscheme with `ω_C` invertible over `Γ(C, 𝒪_C)`. If `C` were a rational tail,
then `deg(ω_X|_C) = -[Γ(C, 𝒪_C) : k] < 0` by the exact sequence
`0 ⟶ ω_C ⟶ ω_X|_C ⟶ 𝒪_{C ∩ X'} ⟶ 0` of [Stacks, Tag 0E34] (the computation of
[Stacks, Tag 0E63]), while `deg(ω_X|_C) > 0` since `ω_X` is ample and `C ⟶ X` is affine. -/
theorem not_isRationalTail_of_isAmple_dualizingSheafOverField (k : Type u) [Field k]
    (X : Scheme.{u}) [X.Over (Spec (.of k))] [IsProper (X ↘ Spec (.of k))]
    [IsIso ((Scheme.ΓSpecIso (.of k)).inv ≫ (X ↘ Spec (.of k)).appTop)] [IsReduced X]
    (hdim : topologicalKrullDim X = 1)
    [SheafOfModules.IsInvertible X.presheaf X.ringCatSheaf.2
      (Stacks.Duality.dualizingSheafOverField (X ↘ Spec (.of k)))]
    (hL : Scheme.Modules.IsAmple X (Stacks.Duality.dualizingSheafOverField (X ↘ Spec (.of k))))
    (C : X.IdealSheafData) [IsIntegral C.subscheme]
    (hωC : letI : Field Γ(C.subscheme, ⊤) :=
        (isField_of_universallyClosed k (C.subschemeι ≫ (X ↘ Spec (.of k)))).toField
      haveI : IsProper C.subscheme.toSpecΓ :=
        Stacks.AlgebraicGeometry.ProperGeomConnected.isProper_toSpecΓ
          (C.subschemeι ≫ (X ↘ Spec (.of k)))
      SheafOfModules.IsInvertible C.subscheme.presheaf C.subscheme.ringCatSheaf.2
        (Stacks.Duality.dualizingSheafOverField C.subscheme.toSpecΓ)) :
    ¬ IsRationalTail k X C := by
  intro hC
  let fC := C.subschemeι ≫ (X ↘ Spec (.of k))
  have hCdim : topologicalKrullDim C.subscheme = 1 :=
    Stacks.Curves.topologicalKrullDim_subscheme_eq_one_of_isRationalTail k X hdim C hC
  have hXeq : TopologicalSpace.Equidimensional X :=
    equidimensional_of_isIso_globalSections_of_dimension_one k (X ↘ Spec (.of k)) hdim
  have hCeq : TopologicalSpace.Equidimensional C.subscheme :=
    TopologicalSpace.Equidimensional.of_preirreducibleSpace C.subscheme
  obtain ⟨a, b, w, hS⟩ := (Stacks.Curves.dualizingSheafOverField_closedSubcurve_of_isInvertible
    (X ↘ Spec (.of k)) hXeq hdim C hCeq hCdim).2.2.2.2.2.2.2.2.1
  let : SheafOfModules.IsInvertible C.subscheme.presheaf C.subscheme.ringCatSheaf.2
      ((Scheme.Modules.pullback C.subschemeι).obj
        (Stacks.Duality.dualizingSheafOverField (X ↘ Spec (.of k)))) :=
    Stacks.Modules.isInvertible_pullback C.subschemeι _
  let : Field Γ(C.subscheme, ⊤) := (isField_of_universallyClosed k fC).toField
  let : Algebra k Γ(C.subscheme, ⊤) := ((Scheme.ΓSpecIso (.of k)).inv ≫ fC.appTop).hom.toAlgebra
  have : IsProper C.subscheme.toSpecΓ :=
    Stacks.AlgebraicGeometry.ProperGeomConnected.isProper_toSpecΓ fC
  have := hωC
  have : IsIso ((Scheme.ΓSpecIso (.of Γ(C.subscheme, ⊤))).inv ≫
      C.subscheme.toSpecΓ.appTop) := by
    rw [Scheme.toSpecΓ_appTop]
    infer_instance
  have hf : C.subscheme.toSpecΓ ≫ Spec.map (CommRingCat.ofHom (algebraMap k Γ(C.subscheme, ⊤))) =
      fC := by
    change C.subscheme.toSpecΓ ≫ Spec.map ((Scheme.ΓSpecIso (.of k)).inv ≫ fC.appTop) = fC
    rw [Spec.map_comp, ← Category.assoc, ← Scheme.toSpecΓ_naturality]
    simp
  have hneg := invertibleCurveDegree_eq_neg_of_isRationalTail hdim hC Γ(C.subscheme, ⊤)
    C.subscheme.toSpecΓ hf hS (Iso.refl _) (Iso.refl _)
  have hpos := invertibleCurveDegree_pullback_pos_of_isAmple_of_isAffineHom k fC hCdim
    C.subschemeι _ hL
  change 0 < invertibleCurveDegree k fC _ (ShortComplex.mk a b w).X₂ at hpos
  rw [hneg] at hpos
  omega

end AlgebraicGeometry
