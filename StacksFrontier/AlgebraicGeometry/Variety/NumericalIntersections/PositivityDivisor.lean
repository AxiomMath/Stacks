module

public import StacksFrontier.AlgebraicGeometry.AmplePredicateBridge.Basic
public import StacksFrontier.AlgebraicGeometry.Divisors.InvertibleSheaf
public import StacksFrontier.AlgebraicGeometry.Divisors.InvertibleSheafGeneral
public import StacksFrontier.AlgebraicGeometry.Divisors.RegularSectionCorrespondence
public import StacksFrontier.AlgebraicGeometry.PowerFamilyBridge.Ample
public import StacksFrontier.AlgebraicGeometry.Variety.Curve.SectionDegree
public import StacksFrontier.AlgebraicGeometry.Variety.NumericalIntersections.DivisorIntersectionProper

/-!
# A positive power of an ample module is the sheaf of a nonempty effective Cartier divisor

On an integral scheme `W`, proper over a field and of positive dimension, with an ample
invertible module `𝓜`, there are an `n ≥ 1` and an effective Cartier divisor `D ⊂ W` with
`𝓜^{⊗ n} ≅ 𝒪_W(D)`, and `D` is nonempty. This is a step of the proof of [Stacks, Tag 0BEV].

A global section `s` of `𝓜^{⊗ n}` whose nonvanishing locus `W_s` is affine and contains a chosen
point exists by [Stacks, Tag 09NV].  On an integral scheme a nonzero global section of an
invertible module is regular, so the zero scheme of `s` is an effective Cartier divisor `D` with
`𝒪_W(D) ≅ 𝓜^{⊗ n}` ([Stacks, Tag 02OR] (4) and [Stacks, Tag 01X0] (2)), and the support of `D` is
the complement of `W_s`.  If `D` were empty then `W_s` would be all of `W`, making `W` affine;
but a scheme both proper over a field and affine is finite over the field, hence
zero-dimensional, contradicting `dim W > 0`.

## Main results

* `AlgebraicGeometry.topologicalKrullDim_le_zero_of_isAffine_of_isProper`: a scheme proper over a
  field and affine is zero-dimensional.
* `AlgebraicGeometry.exists_effectiveCartierDivisor_tensorPower_of_isAmple`: the statement above.

## References

* [Stacks Project, Tag 0BEV](https://stacks.math.columbia.edu/tag/0BEV)
* [Stacks Project, Tag 09NV](https://stacks.math.columbia.edu/tag/09NV)
* [Stacks Project, Tag 02OR](https://stacks.math.columbia.edu/tag/02OR)
* [Stacks Project, Tag 01X0](https://stacks.math.columbia.edu/tag/01X0)
-/

@[expose] public noncomputable section

open CategoryTheory TopologicalSpace Opposite

universe u

namespace AlgebraicGeometry

/-- **A scheme proper over a field and affine is zero-dimensional.** Properness plus affineness
of the structure morphism is finiteness ([Stacks, Tag 01WN]), a finite morphism to a field is
locally quasi-finite, and a locally Artinian scheme is discrete. -/
public theorem topologicalKrullDim_le_zero_of_isAffine_of_isProper (k : Type u) [Field k]
    {X : Scheme.{u}} (f : X ⟶ Spec (.of k)) [IsProper f] [IsAffine X] :
    topologicalKrullDim X ≤ 0 := by
  have : IsFinite f :=
    (IsFinite.iff_isProper_and_isAffineHom (f := f)).2 ⟨inferInstance, inferInstance⟩
  have : IsLocallyArtinian X := IsLocallyArtinian.of_locallyQuasiFinite f
  exact topologicalKrullDim_zero_of_discreteTopology X

/-- **A positive power of an ample invertible module on an integral scheme proper over a field
and of positive dimension is the sheaf of a nonempty effective Cartier divisor.** -/
public theorem exists_effectiveCartierDivisor_tensorPower_of_isAmple (k : Type u) [Field k]
    {W : Scheme.{u}} (g : W ⟶ Spec (.of k)) [IsProper g] [IsIntegral W]
    (hdim : 0 < topologicalKrullDim W) (M : W.Modules)
    [Stacks.Ample.IsInvertibleModule W M] (hM : Scheme.Modules.IsAmple W M) :
    ∃ (n : ℕ) (D : W.IdealSheafData), 1 ≤ n ∧
      Stacks.Divisors.IsEffectiveCartierDivisor D ∧ Nonempty D.subscheme ∧
      Nonempty (Scheme.Modules.tensorPowerModules M (n : ℤ) ≅
        Stacks.Divisors.invertibleSheaf D) := by
  classical
  have : IsLocallyNoetherian W := LocallyOfFiniteType.isLocallyNoetherian g
  have : CompactSpace W := QuasiCompact.compactSpace_of_compactSpace g
  obtain ⟨x₀⟩ : Nonempty W := inferInstance
  -- [Stacks, Tag 09NV]: an affine `W_s` containing `x₀`
  obtain ⟨n, hn, s, haff, hTs, -⟩ :=
    Stacks.AmpleFiniteAffineNonvanishing.exists_affine_nonvanishingOpen_containing_finite M
      (Stacks.PowerFamilyBridge.isAmple_of_modulesIsAmple W M hM)
      (Set.finite_singleton x₀) ⊤ (fun _ _ => trivial)
  have : SheafOfModules.IsInvertible W.sheaf.obj W.ringCatSheaf.property
      (Stacks.Ample.tensorPowModule W M (n : ℤ)) :=
    InvertibleSheafGeneral.isInvertible_of_isInvertibleModule _
  have hx₀ : x₀ ∈ Stacks.Ample.nonvanishingLocus (Stacks.Ample.tensorPowModule W M (n : ℤ)) s :=
    (Stacks.AmpleTheory.coe_powNonvanishingOpen W M n s) ▸ hTs rfl
  have hne0 : s ≠ 0 := by
    intro h
    rw [h, Stacks.Ample.mem_nonvanishingLocus_iff] at hx₀
    exact hx₀ (by simp)
  set t := (Stacks.SheafOfModules.sectionsOfTop
    (Stacks.Ample.tensorPowModule W M (n : ℤ)) s).eval (op ⊤)
  have hevaltop : t = s := Stacks.SheafOfModules.sectionsOfTop_eval_top _ s
  have hne0' : t ≠ 0 := by
    rwa [hevaltop]
  have hreg := isRegularSection_of_eval_top_ne_zero _ _ hne0'
  -- [Stacks, Tag 02OR] (4) and [Stacks, Tag 01X0] (2)
  refine ⟨n, zeroScheme W (Stacks.Ample.tensorPowModule W M (n : ℤ)) t,
    hn, (isEffectiveCartierDivisor_zeroScheme_iff_isRegularSection W _ _).2 hreg, ?_, ?_⟩
  · by_contra hcon
    have : IsEmpty (zeroScheme W (Stacks.Ample.tensorPowModule W M (n : ℤ)) t).subscheme :=
      not_nonempty_iff.mp hcon
    have hsupp : (zeroScheme W (Stacks.Ample.tensorPowModule W M (n : ℤ)) t).supportSet
        = (∅ : Set W) := by
      rw [show ∀ D : W.IdealSheafData, D.supportSet = (D.support : Set W) from fun _ => rfl,
        ← Scheme.IdealSheafData.range_subschemeι]
      exact Set.range_eq_empty _
    have hcompl := nonvanishingLocus_eq_compl_supportSet_zeroScheme
      (Stacks.Ample.tensorPowModule W M (n : ℤ)) _ hne0'
    rw [hsupp, Set.compl_empty] at hcompl
    have huniv : Stacks.Ample.nonvanishingLocus
        (Stacks.Ample.tensorPowModule W M (n : ℤ)) s = (Set.univ : Set W) := by
      rw [← hevaltop, ← Stacks.AmplePredicateBridge.coe_nonvanishingOpen_eval W _
        (Stacks.SheafOfModules.sectionsOfTop (Stacks.Ample.tensorPowModule W M (n : ℤ)) s)]
      exact hcompl
    have htop : Stacks.AmpleTheory.powNonvanishingOpen W M n s = (⊤ : W.Opens) :=
      Opens.ext ((Stacks.AmpleTheory.coe_powNonvanishingOpen W M n s).trans huniv)
    rw [htop] at haff
    have : IsAffine (⊤ : W.Opens).toScheme := haff
    have : IsAffine W := IsAffine.of_isIso W.topIso.inv
    exact absurd hdim (not_lt_of_ge (topologicalKrullDim_le_zero_of_isAffine_of_isProper k g))
  · obtain ⟨e, -⟩ := (existsUnique_invertibleSheafIso_zeroScheme W _ _ hreg).exists
    exact ⟨(Stacks.PowerFamilyBridge.invertibleTensorPowerModuleIso W M (n : ℤ)).trans e.symm⟩

end AlgebraicGeometry

end
