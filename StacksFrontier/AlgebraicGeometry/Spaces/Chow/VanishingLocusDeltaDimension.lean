module

public import StacksFrontier.AlgebraicGeometry.Spaces.AdmissibleBlowupSeparation
public import StacksFrontier.AlgebraicGeometry.Spaces.EffectiveCartierComplement
public import StacksFrontier.AlgebraicGeometry.Spaces.InvertibleModuleTriviality
public import StacksFrontier.AlgebraicGeometry.Spaces.ZeroSchemeEffectiveCartier
public import StacksFrontier.AlgebraicGeometry.Spaces.Chow.CanonicalGysinRule
public import StacksFrontier.AlgebraicGeometry.Spaces.Chow.EffectiveCartierIntersection
public import StacksFrontier.AlgebraicGeometry.Spaces.Chow.PrincipalDivisorRationalEquivalence
public import StacksFrontier.AlgebraicGeometry.Spaces.Chow.TrivialRestrictionGysin

/-!
# The δ-dimension of the vanishing locus of a nonzero section

Let `X/B` be a good algebraic space which is integral, with `n = dim_δ(X)`, let `ℒ` be an
invertible `𝒪_X`-module and let `s ∈ Γ(X, ℒ)` be a **nonzero** global section. Then the
vanishing locus `Z(s)` of Stacks 0845 has

`dim_δ(Z(s)) ≤ n - 1`,

so that the cycle `[Z(s)]_{n-1}` of Stacks 0EE9 is an element of `Z_{n-1}(X)`.

## Main results

* `AlgebraicGeometry.Space.isRegularSection_of_ne_zero`: on an integral algebraic space a nonzero
  global section of an invertible module is a regular section.
* `AlgebraicGeometry.Space.not_top_le_zeroSchemeSubfunctor_of_ne_zero`: the zero scheme of such a
  section is not all of `X`.
* `AlgebraicGeometry.Space.notMem_subspacePointSet_vanishingLocus_genericPoint`: the generic point
  of `X` does not lie on `|Z(s)|`.
* `AlgebraicGeometry.Space.deltaDimensionSubspace_vanishingLocus_le`: `dim_δ(Z(s)) ≤ n - 1`.
* `AlgebraicGeometry.Space.deltaDimensionClosed_univ_vanishingLocus_le`: the same bound read on
  `Z(s)` as a good algebraic space over the base.

## References

* [Stacks Project, Tag 0845](https://stacks.math.columbia.edu/tag/0845)
* [Stacks Project, Tag 0846](https://stacks.math.columbia.edu/tag/0846)
* [Stacks Project, Tag 0843](https://stacks.math.columbia.edu/tag/0843)
* [Stacks Project, Tag 083S](https://stacks.math.columbia.edu/tag/083S)
* [Stacks Project, Tag 0AD4](https://stacks.math.columbia.edu/tag/0AD4)
* [Stacks Project, Tag 0EDX](https://stacks.math.columbia.edu/tag/0EDX)
* [Stacks Project, Tag 0EE9](https://stacks.math.columbia.edu/tag/0EE9)
* [Stacks Project, Tag 0EQF](https://stacks.math.columbia.edu/tag/0EQF)
-/

@[expose] public noncomputable section

open CategoryTheory Opposite

universe u

namespace AlgebraicGeometry.Space

attribute [local instance] pointTopology

/-! ### A nonzero section of an invertible module on an integral space is regular -/

section Regular

variable (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)
    (X : AlgebraicSpaces B S hS) (L : Modules.{u, u} B S hS X.1 X.2)
    (hinv : AlgebraicGeometry.SheafOfModules.IsInvertible (structureCommRings B S hS X)
      (structureRingSheaf B S hS X).property L)
    (hint : IsIntegralSpace B S hS X.1)

include hinv hint in
/-- On an integral algebraic space a nonzero global section of an invertible module is a
regular section in the sense of Stacks 0843: the morphism `𝒪_X ⟶ ℒ` it defines is a
monomorphism. -/
theorem isRegularSection_of_ne_zero {s : L.sections} (hs : s ≠ 0) :
    AlgebraicGeometry.IsRegularSection (structurePresheaf B S hS X.1)
      (Stacks.SheafOfModules.Tensor.ringSheaf
        (smallEtaleRingedSite B S hS X.1 X.2).O).property s := by
  have ht : L.unitHomEquiv.symm s ≠ 0 := by
    intro h
    refine hs ?_
    have h2 : L.unitHomEquiv (L.unitHomEquiv.symm s) = L.unitHomEquiv 0 := by rw [h]
    rw [Equiv.apply_symm_apply] at h2
    refine h2.trans (Subtype.ext (funext fun U => ?_))
    rw [SheafOfModules.unitHomEquiv_apply_coe]
    rfl
  exact mono_of_ne_zero B S hS X.1 X.2 hint L
    (Stacks.SheafOfModules.IsInvertible.ofAlgebraicGeometry _ _ _ hinv) _ ht

include hinv hint in
/-- The zero scheme of a nonzero section of an invertible module on an integral algebraic space
is not all of `X`. -/
theorem not_top_le_zeroSchemeSubfunctor_of_ne_zero {s : L.sections} (hs : s ≠ 0) :
    ¬ ((⊤ : Subfunctor X.1) ≤ zeroSchemeSubfunctor B S hS X L s) := by
  intro hle
  have hfull : subspacePointSet B S hS X.1 (zeroScheme B S hS X L s).1 = Set.univ := by
    refine Set.eq_univ_of_univ_subset ?_
    rw [← range_pointsMap_ι_top B S hS (F := X.1)]
    rintro - ⟨y, rfl⟩
    rw [← Subfunctor.homOfLe_ι hle, pointsMap_comp]
    exact ⟨_, rfl⟩
  have hdense : Dense (subspacePointSet B S hS X.1
      (openComplement B S hS (zeroScheme B S hS X L s).1)) :=
    dense_subspacePointSet_of_isSchemeTheoreticallyDense B S hS _
      (isSchemeTheoreticallyDense_openComplement_of_isEffectiveCartierDivisor B S hS X _
        (isEffectiveCartierDivisor_zeroScheme_of_isRegularSection B S hS X L s hinv
          (isRegularSection_of_ne_zero B S hS X L hinv hint hs)))
  have hcompl : subspacePointSet B S hS X.1
      (openComplement B S hS (zeroScheme B S hS X L s).1) =
      (subspacePointSet B S hS X.1 (zeroScheme B S hS X L s).1)ᶜ :=
    range_pointsMap_ι_openComplement B S hS _
  rw [hcompl, hfull, Set.compl_univ] at hdense
  have : IrreducibleSpace (points B S hS X.1) := hint.2.2
  obtain ⟨x⟩ := (inferInstance : Nonempty (points B S hS X.1))
  have hempty : (Set.univ : Set (points B S hS X.1)) = ∅ := by
    rw [← dense_iff_closure_eq.1 hdense, closure_empty]
  exact (Set.univ_eq_empty_iff.1 hempty).false x

end Regular

/-! ### The δ-dimension bound -/

section Bound

variable (D : BaseSpaceDimensionSituation.{u})
    {X : (BigFppfOver D.site D.base D.base_mem)ᵒᵖ ⥤ Type u}
    (sX : X ⟶ D.space) (hX : D.IsGood sX)
    (hint : IsIntegralSpace D.site D.base D.base_mem X)
    (L : Modules.{u, u} D.site D.base D.base_mem X hX.1)
    (hL : IsInvertibleSheaf D sX hX L)

/-- The generic point of `X` read as the integral closed subspace `⊤` is the generic point of
`X`. -/
private theorem ambientGenericPoint_top_eq_genericPoint :
    (IntegralClosedSubspace.top D.site D.base D.base_mem hX.1 hint).ambientGenericPoint
      D.site D.base D.base_mem = genericPoint D.site D.base D.base_mem hX.1 hint := by
  have : T0Space (points D.site D.base D.base_mem X) :=
    t0Space_points_of_isDecentSpace D.site D.base D.base_mem hX.1 hint.2.1
  refine IsGenericPoint.eq ?_ (isGenericPoint_genericPoint D.site D.base D.base_mem hX.1 hint)
  have h := (IntegralClosedSubspace.top D.site D.base D.base_mem hX.1
    hint).isGenericPoint_ambientGenericPoint D.site D.base D.base_mem hX.1
  rwa [subspacePointSet, IntegralClosedSubspace.range_pointsMap_top] at h

include hint hL in
/-- The generic point of an integral algebraic space does not lie on the vanishing locus of a
nonzero global section of an invertible module. -/
theorem notMem_subspacePointSet_vanishingLocus_genericPoint {s : L.sections} (hs : s ≠ 0) :
    genericPoint D.site D.base D.base_mem hX.1 hint ∉
      subspacePointSet D.site D.base D.base_mem X (vanishingLocus D sX hX L s).1 := by
  rw [← ambientGenericPoint_top_eq_genericPoint D sX hX hint]
  exact notMem_subspacePointSet_ambientGenericPoint_of_not_le D hX.1
    (vanishingLocus D sX hX L s).1 (vanishingLocus D sX hX L s).2
    (IntegralClosedSubspace.top D.site D.base D.base_mem hX.1 hint)
    (not_top_le_zeroSchemeSubfunctor_of_ne_zero D.site D.base D.base_mem ⟨X, hX.1⟩ L hL hint hs)

include hint hL in
/-- In Situation 0EDT let `X/B` be good, let `X` be integral with `n = dim_δ(X)`, let `ℒ` be an
invertible `𝒪_X`-module and let `s ∈ Γ(X, ℒ)` be a nonzero global section. Then the vanishing
locus `Z(s)` of Stacks 0845 has δ-dimension at most `n - 1`, so the cycle `[Z(s)]_{n-1}` of
Stacks 0EE9 exists as an element of `Z_{n-1}(X)`. -/
theorem deltaDimensionSubspace_vanishingLocus_le {s : L.sections} (hs : s ≠ 0) {n : ℤ}
    (hn : deltaDimensionClosed D sX hX Set.univ isClosed_univ = (n : EInt)) :
    deltaDimensionSubspace D sX hX (vanishingLocus D sX hX L s).1
        (vanishingLocus D sX hX L s).2 ≤ ((n - 1 : ℤ) : EInt) := by
  have hgen := notMem_subspacePointSet_vanishingLocus_genericPoint D sX hX hint L hL hs
  have hWdim : deltaDimension D sX
      (IntegralClosedSubspace.top D.site D.base D.base_mem hX.1 hint) = (n - 1) + 1 := by
    rw [deltaDimension_top D sX hX hint hn]
    ring
  rw [deltaDimensionSubspace_eq_deltaDimensionClosed]
  refine (deltaDimensionClosed_le_coe_iff D sX hX _ _ (n - 1)).2 fun t ht => ?_
  refine inducedDimensionValue_le_of_mem_of_ne D sX hX (n - 1)
    (IntegralClosedSubspace.top D.site D.base D.base_mem hX.1 hint) hWdim ?_ ?_
  · rw [subspacePointSet, IntegralClosedSubspace.range_pointsMap_top]
    exact Set.mem_univ t
  · rw [ambientGenericPoint_top_eq_genericPoint D sX hX hint]
    exact fun h => hgen (h ▸ ht)

include hint hL in
/-- `dim_δ(D) ≤ n - 1` for `D = Z(s)` read as a good algebraic space over the base: the
δ-dimension of the whole of `D` computed along `D → B` is at most `n - 1`, so the cycle
`[D]_{n-1}` of Stacks 0EE9 lies in `Z_{n-1}(D)`. -/
theorem deltaDimensionClosed_univ_vanishingLocus_le {s : L.sections} (hs : s ≠ 0) {n : ℤ}
    (hn : deltaDimensionClosed D sX hX Set.univ isClosed_univ = (n : EInt)) :
    deltaDimensionClosed D ((vanishingLocus D sX hX L s).1.ι ≫ sX)
        (isGood_vanishingLocus D sX hX L s) Set.univ isClosed_univ ≤ ((n - 1 : ℤ) : EInt) := by
  have hE := isGood_vanishingLocus D sX hX L s
  have hbound := deltaDimensionSubspace_vanishingLocus_le D sX hX hint L hL hs hn
  rw [deltaDimensionSubspace_eq_deltaDimensionClosed] at hbound
  have hpt := (deltaDimensionClosed_le_coe_iff D sX hX _ _ (n - 1)).1 hbound
  have hlqf : IsLocallyQuasiFinite D.site D.base D.base_mem (vanishingLocus D sX hX L s).1.ι :=
    isLocallyQuasiFinite_of_isImmersion D.site D.base D.base_mem _
      (isImmersion_of_isClosedImmersion D.site D.base D.base_mem
        (vanishingLocus D sX hX L s).2.2)
  refine (deltaDimensionClosed_le_coe_iff D _ hE _ _ (n - 1)).2 fun t _ => ?_
  have hcomp : inducedDimensionValue D.site D.base D.base_mem D.delta
      ((vanishingLocus D sX hX L s).1.ι ≫ sX) t =
      inducedDimensionValue D.site D.base D.base_mem D.delta sX
        (pointsMap D.site D.base D.base_mem (vanishingLocus D sX hX L s).1.toFunctor
          (vanishingLocus D sX hX L s).1.ι t) :=
    D.deltaValue_comp_of_isLocallyQuasiFinite hE.1 hX.1 _ sX hlqf hX.2.2 t
  rw [hcomp]
  exact hpt _ ⟨t, rfl⟩

end Bound

end AlgebraicGeometry.Space

end
