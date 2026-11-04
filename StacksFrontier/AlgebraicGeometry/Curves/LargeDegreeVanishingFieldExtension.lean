module

public import StacksFrontier.AlgebraicGeometry.Curves.LargeDegreeVanishing
public import StacksFrontier.AlgebraicGeometry.PicardScheme.Jacobian.CurveBaseChangeDegree
public import StacksFrontier.AlgebraicGeometry.Curves.GenusCurve.SeparableDegreeFibres
public import StacksFrontier.AlgebraicGeometry.Chow.VoevodskyNilpotence.SmashPowerSymmetricPower
public import StacksFrontier.AlgebraicGeometry.CoherenceCriteria.Basic
public import StacksFrontier.AlgebraicGeometry.PullbackInvertible.Basic
public import StacksFrontier.AlgebraicGeometry.ProperCohomologyFinite.OverFieldProper
public import StacksFrontier.AlgebraicGeometry.Picard.CurveDegreeHom

/-!
# Vanishing of `H¹` in large degree on a base change of a curve

Let `X` be a smooth proper geometrically irreducible curve of genus `g` over a field `k`, and
`X_K` its base change to a field extension `K`. For an invertible module `ℒ` on `X_K` with
`deg ℒ ≥ 2g - 1` we have `H¹(X_K, ℒ) = 0` and `dim_K H⁰(X_K, ℒ) = deg ℒ + 1 - g`.

Over an algebraically closed field this is [Stacks, Tag 0B90] together with Riemann–Roch. In
general one passes to the algebraic closure `Ω` of `K`: the dimensions of cohomology, the degree
and the genus are unchanged by the extension `Ω/K` ([Stacks, Tag 02KH]), and `X_Ω` is a proper
curve over `Ω`.

## Main results

* `AlgebraicGeometry.isZero_cohomologyOverField_one_and_finrank_zero_of_baseChange`.
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits

universe u

namespace AlgebraicGeometry

open Stacks.RingedSpace (structureIsSheaf)

/-- The degree of an invertible module is unchanged by an extension of the ground field, with the
properness, the dimension bound and the invertibility on the base change taken as hypotheses.
The base's `AlgebraicGeometry.invertibleCurveDegree_baseChange_field` derives those three. -/
theorem invertibleCurveDegree_baseChange_field_of_baseChangeHypotheses (K Ω : Type u) [Field K]
    [Field Ω] [Algebra K Ω]
    {Y Y' : Scheme.{u}} (g : Y' ⟶ Y) (π' : Y' ⟶ Spec (.of Ω)) (π : Y ⟶ Spec (.of K))
    (h : IsPullback g π' π (Spec.map (CommRingCat.ofHom (algebraMap K Ω)))) [IsProper π]
    [IsProper π'] (hdim : topologicalKrullDim Y ≤ 1) (hdim' : topologicalKrullDim Y' ≤ 1)
    (M : Y.Modules) [hM : SheafOfModules.IsInvertible Y.presheaf Y.ringCatSheaf.2 M]
    [hM' : SheafOfModules.IsInvertible Y'.presheaf Y'.ringCatSheaf.2
      ((Scheme.Modules.pullback g).obj M)] :
    invertibleCurveDegree Ω π' hdim' ((Scheme.Modules.pullback g).obj M) =
      invertibleCurveDegree K π hdim M := by
  have : SheafOfModules.IsInvertible Y.sheaf.obj Y.ringCatSheaf.property M := hM
  have hq : M.IsQuasicoherent := Stacks.Divisors.isQuasicoherent_of_isInvertible M
  unfold invertibleCurveDegree
  congr 1
  · exact finsum_congr fun n => by
      rw [finrank_cohomologyOverField_baseChange_field K Ω g π' π h M n]
  · exact finsum_congr fun n => by
      rw [finrank_cohomologyOverField_unit_baseChange π g π' h n]

/-- A zero module over a field has dimension zero. -/
private theorem finrank_eq_zero_of_isZero {K : Type u} [Field K] {M : ModuleCat.{u} K}
    (hM : IsZero M) : Module.finrank K M = 0 :=
  have := ModuleCat.isZero_iff_subsingleton.mp hM
  Module.finrank_zero_of_subsingleton

/-- **`H¹ = 0` and Riemann–Roch in degree `≥ 2g - 1` on a base change of a curve.** Let `X` be a
smooth proper geometrically irreducible curve of genus `g` over `k`, `X_K` its base change to a
field `K`, and `ℒ` invertible on `X_K` of degree `≥ 2g - 1`. Then `H¹(X_K, ℒ) = 0` and
`dim_K H⁰(X_K, ℒ) = deg ℒ + 1 - g`. -/
theorem isZero_cohomologyOverField_one_and_finrank_zero_of_baseChange (k : Type u) [Field k]
    {X : Scheme.{u}} (f : X ⟶ Spec (.of k)) [IsProper f] [Smooth f] [GeometricallyIrreducible f]
    [SmoothOfRelativeDimension 1 f] {K : Type u} [Field K] [Algebra k K] {Y' : Scheme.{u}}
    (g' : Y' ⟶ X) (π' : Y' ⟶ Spec (.of K))
    (h : IsPullback g' π' f (Spec.map (CommRingCat.ofHom (algebraMap k K)))) [IsProper π']
    (hdim' : topologicalKrullDim Y' ≤ 1) (M : Y'.Modules)
    (hM : Stacks.SheafOfModules.IsInvertible Y'.presheaf (structureIsSheaf Y'.toRingedSpace) M)
    (hdeg : 2 * (genus f : ℤ) - 1 ≤ invertibleCurveDegreeHom K π' hdim'
      (Stacks.SheafOfModules.picardClass Y'.presheaf (structureIsSheaf Y'.toRingedSpace) M hM)) :
    IsZero (cohomologyOverField K π' M 1) ∧
      (Module.finrank K (cohomologyOverField K π' M 0) : ℤ) =
        invertibleCurveDegreeHom K π' hdim'
          (Stacks.SheafOfModules.picardClass Y'.presheaf (structureIsSheaf Y'.toRingedSpace) M hM)
          + 1 - genus f := by
  have hMa : SheafOfModules.IsInvertible Y'.presheaf Y'.ringCatSheaf.2 M :=
    (Stacks.SheafOfModules.isInvertible_iff_algebraicGeometry _ _ M).1 hM
  have : SheafOfModules.IsInvertible Y'.sheaf.obj Y'.ringCatSheaf.property M := hMa
  rw [invertibleCurveDegreeHom_picardClass] at hdeg ⊢
  -- pass to an algebraic closure `Ω` of `K`
  set Ω := AlgebraicClosure K
  let a : Spec (.of Ω) ⟶ Spec (.of K) := Spec.map (CommRingCat.ofHom (algebraMap K Ω))
  have hsq : IsPullback (pullback.fst π' a) (pullback.snd π' a) π' a :=
    IsPullback.of_hasPullback _ _
  set π'' := pullback.snd π' a
  set q := pullback.fst π' a
  have hcomp : IsPullback (q ≫ g') π'' f (Spec.map (CommRingCat.ofHom
      ((algebraMap K Ω).comp (algebraMap k K)))) := by
    rw [CommRingCat.ofHom_comp, Spec.map_comp]
    exact hsq.paste_horiz h
  have hgenus : genus π'' = genus f := genus_eq_of_isPullback k Ω _ (q ≫ g') π'' f hcomp
  have : SmoothOfRelativeDimension 1 π' :=
    (smoothOfRelativeDimension_isStableUnderBaseChange 1).of_isPullback h ‹_›
  have : GeometricallyIrreducible π' :=
    MorphismProperty.of_isPullback h ‹GeometricallyIrreducible f›
  have : SmoothOfRelativeDimension 1 π'' :=
    (smoothOfRelativeDimension_isStableUnderBaseChange 1).of_isPullback hsq ‹_›
  have : GeometricallyIrreducible π'' :=
    MorphismProperty.of_isPullback hsq ‹GeometricallyIrreducible π'›
  have : IsProper π'' := MorphismProperty.of_isPullback hsq ‹IsProper π'›
  have : IsCurve Ω π'' := Stacks.Chow.isCurve_of_smoothOfRelativeDimension_one π''
  have hdim'' : topologicalKrullDim (pullback (C := Scheme.{u}) π' a) ≤ 1 :=
    (IsCurve.topologicalKrullDim_eq_one (k := Ω) (f := π'')).le
  have := hM
  have hMa'' : SheafOfModules.IsInvertible (pullback (C := Scheme.{u}) π' a).presheaf
      (pullback (C := Scheme.{u}) π' a).ringCatSheaf.2 ((Scheme.Modules.pullback q).obj M) :=
    (Stacks.SheafOfModules.isInvertible_iff_algebraicGeometry _ _ _).1
      (Stacks.Modules.isInvertible_pullback q M)
  have hdeg'' := invertibleCurveDegree_baseChange_field_of_baseChangeHypotheses K Ω q π'' π' hsq
    hdim' hdim'' M
  have hq : M.IsQuasicoherent := Stacks.Divisors.isQuasicoherent_of_isInvertible M
  -- `H¹` vanishes over `Ω` by [Stacks, Tag 0B90], hence over `K`
  have h1Ω : IsZero (cohomologyOverField Ω π'' ((Scheme.Modules.pullback q).obj M) 1) :=
    isZero_cohomologyOverField_one_of_two_mul_genus_sub_one_le_invertibleCurveDegree Ω π''
      ((Scheme.Modules.pullback q).obj M) hMa'' (by
        rw [hgenus]
        convert hdeg using 1)
  have hfr1 : Module.finrank K (cohomologyOverField K π' M 1) = 0 := by
    rw [← finrank_cohomologyOverField_baseChange_field K Ω q π'' π' hsq M 1]
    exact finrank_eq_zero_of_isZero h1Ω
  have : IsLocallyNoetherian Y' := LocallyOfFiniteType.isLocallyNoetherian π'
  have : M.IsCoherent := Stacks.AlgebraicGeometry.CoherentKernel.isCoherent_of_isInvertible Y' M
  have := finiteDimensional_cohomologyOverField_of_isProper K π' M 1
  have h1 : IsZero (cohomologyOverField K π' M 1) :=
    ModuleCat.isZero_iff_subsingleton.mpr (Module.finrank_zero_iff.mp hfr1)
  refine ⟨h1, ?_⟩
  -- Riemann–Roch: `deg ℒ = h⁰(ℒ) - χ(𝒪) = h⁰(ℒ) - (1 - g)`
  have hχ := finsum_finrank_cohomologyOverField_unit_baseChange f g' π' h
  have hsum : ∑ᶠ n : ℕ, (-1 : ℤ) ^ n * (Module.finrank K (cohomologyOverField K π' M n) : ℤ) =
      Module.finrank K (cohomologyOverField K π' M 0) := by
    rw [finsum_eq_single _ 0]
    · simp
    · intro n hn
      rcases n with _ | _ | n
      · exact absurd rfl hn
      · simp [hfr1]
      · simp [finrank_eq_zero_of_isZero
          (isZero_cohomologyOverField_of_topologicalKrullDim_le K π' M (d := 1) hdim'
            (by omega : 1 < n + 2))]
  have hdef : invertibleCurveDegree K π' hdim' M =
      (∑ᶠ n : ℕ, (-1 : ℤ) ^ n * (Module.finrank K (cohomologyOverField K π' M n) : ℤ)) -
        ∑ᶠ n : ℕ, (-1 : ℤ) ^ n * (Module.finrank K
          (cohomologyOverField K π' (SheafOfModules.unit Y'.ringCatSheaf) n) : ℤ) :=
    rfl
  rw [hdef, hsum, hχ]
  ring

end AlgebraicGeometry

end
