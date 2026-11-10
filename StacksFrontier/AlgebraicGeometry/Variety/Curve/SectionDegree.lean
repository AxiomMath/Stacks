module

public import StacksFrontier.AlgebraicGeometry.AffineCohomologyVanishing.Basic
public import StacksFrontier.AlgebraicGeometry.Ample.AmpleCriteria
public import StacksFrontier.AlgebraicGeometry.Ample.StructureSheaf
public import StacksFrontier.AlgebraicGeometry.ClosedImmersionEuler.Basic
public import StacksFrontier.AlgebraicGeometry.ClosedLift.Basic
public import StacksFrontier.AlgebraicGeometry.ClosedPushforward.Coherent
public import StacksFrontier.AlgebraicGeometry.CoherenceCriteria.Basic
public import StacksFrontier.AlgebraicGeometry.CoherentPullback.Basic
public import StacksFrontier.AlgebraicGeometry.ComponentMultiplicity.ZeroDimensional
public import StacksFrontier.AlgebraicGeometry.CurveDegreeTensor.Cohomological
public import StacksFrontier.AlgebraicGeometry.CurveDegreeZeroScheme.Basic
public import StacksFrontier.AlgebraicGeometry.Divisors.CanonicalSectionNonvanishing
public import StacksFrontier.AlgebraicGeometry.Divisors.EffectiveCartier.Decomposition
public import StacksFrontier.AlgebraicGeometry.Divisors.RegularSectionCorrespondence
public import StacksFrontier.AlgebraicGeometry.Divisors.RegularSectionIntegral
public import StacksFrontier.AlgebraicGeometry.Divisors.TwistSectionMinimality
public import StacksFrontier.AlgebraicGeometry.Divisors.ZeroSchemeIdealSheaf
public import StacksFrontier.AlgebraicGeometry.EulerCharIso.Basic
public import StacksFrontier.AlgebraicGeometry.InvertibleBridge.Basic
public import StacksFrontier.AlgebraicGeometry.LiftInvertible.Basic
public import StacksFrontier.AlgebraicGeometry.Morphisms.FiniteType.NoetherianSource
public import StacksFrontier.AlgebraicGeometry.PicardBaseChange.Injectivity
public import StacksFrontier.AlgebraicGeometry.ProperCohomologyFinite.OverFieldProper
public import StacksFrontier.AlgebraicGeometry.Variety.Curve.DivisorDegree
public import StacksFrontier.AlgebraicGeometry.Variety.EulerChar.AdditivityUnconditional
public import StacksFrontier.AlgebraicGeometry.Variety.EulerChar.CohomologyComparison
public import StacksFrontier.Algebra.Category.ModuleCat.Sheaf.InvertibleCompare
public import StacksCore.Tactic.StacksAttribute

/-!
# Invertible modules with a nonzero section on a proper curve

Let `k` be a field, `X` a proper scheme of dimension at most one over `k` which is integral, and
`ℒ` an invertible `𝒪_X`-module with a nonzero global section `s`. Then `s` is a regular section,
its zero scheme `Z(s)` is an effective Cartier divisor finite over `k`, and

`deg(ℒ) = dim_k H⁰(Z(s), ℒ|_{Z(s)})`,

which is nonnegative: this is part (1) of [Stacks, Tag 0B40] and the identity its proof rests on.
If moreover `ℒ^{⊗ -1}` has a nonzero global section then `ℒ ≅ 𝒪_X`, which is part (3).

That dimension is positive as soon as `s` vanishes somewhere, which is part (2); and if the
degree is nonpositive then `Z(s)` is empty, so `s` vanishes nowhere and multiplication by it
trivializes `ℒ`, which is part (4).

## Main results

The elided prefix throughout is `AlgebraicGeometry`.

* `isFinite_zeroScheme_of_eval_top_ne_zero`: the zero scheme of a nonzero global section of an
  invertible module on a proper scheme of dimension at most one over a field is finite over that
  field.
* `nonempty_unit_iso_of_supportSet_zeroScheme_eq_empty`: an invertible module with a nonzero
  global section whose zero scheme is empty is isomorphic to the structure sheaf.
* `isZero_cohomologyOverField_pos_of_isAffine`: the positive-degree cohomology of a
  quasi-coherent module on an affine scheme over a field vanishes.
* `eulerCharacteristic_eq_finrank_cohomologyOverField_zero_of_isFinite`: on a scheme finite over
  a field the Euler characteristic of a coherent module is the dimension of its `H⁰`.
* `invertibleCurveDegree_eq_finrank_cohomologyOverField_zero_zeroScheme`: the degree identity
  displayed above.
* `invertibleCurveDegree_nonneg_of_eval_top_ne_zero`: **part (1)** of [Stacks, Tag 0B40].
* `invertibleCurveDegree_pos_of_eval_top_ne_zero`: **part (2)** of [Stacks, Tag 0B40].
* `isIso_unitHomEquiv_symm_of_invertibleCurveDegree_nonpos` and
  `isTrivial_of_invertibleCurveDegree_nonpos`: **part (4)** of [Stacks, Tag 0B40], in the
  stronger form the source's proof supports and in the form the text states.
* `tensorInverseHomSection`: the global section of `ℒ ⊗ 𝒩^{⊗ -1}` attached to a morphism
  `𝒩 ⟶ ℒ`.
* `invertibleCurveDegree_le_of_hom_ne_zero`,
  `isIso_of_invertibleCurveDegree_eq_of_hom_ne_zero` and `invertibleCurveDegree_eq_of_isIso`:
  **part (5)** of [Stacks, Tag 0B40], the inequality and both directions of its equality
  clause.
* `tensorPairing_zero_right`: the section pairing of a trivialization vanishes on a zero second
  argument.
* `nonempty_nonvanishingLocus_of_eval_top_ne_zero`: on an integral scheme the nonvanishing locus
  of a nonzero global section of an invertible module is nonempty.
* `globalSectionsMulNegOne_ne_zero`: on an integral scheme the product of a nonzero global
  section of an invertible module and a nonzero global section of its inverse is nonzero.
* `isTrivial_of_eval_top_ne_zero_of_inverse`: **part (3)** of [Stacks, Tag 0B40].

## References

* [Stacks Project, Tag 0B40](https://stacks.math.columbia.edu/tag/0B40)
* [Stacks Project, Tag 0AYY](https://stacks.math.columbia.edu/tag/0AYY)
* [Stacks Project, Tag 01CY](https://stacks.math.columbia.edu/tag/01CY)
* [Stacks Project, Tag 01X0](https://stacks.math.columbia.edu/tag/01X0)
* [Stacks Project, Tag 01XB](https://stacks.math.columbia.edu/tag/01XB)
* [Stacks Project, Tag 02O6](https://stacks.math.columbia.edu/tag/02O6)
* [Stacks Project, Tag 02OQ](https://stacks.math.columbia.edu/tag/02OQ)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits Opposite
open Stacks.SheafOfModules.TensorStalkRingedSpace (toTensorSheafSection)
open Stacks.SheafOfModules (tensorPairing nonvanishingLocus nonvanishingOpen)
open Stacks.SheafOfModules.Invertible (tensorPowerModule globalSectionsMulNegOne mulNegOneIso)
open Stacks.AlgebraicGeometry.ComponentDegrees
  (discreteTopology_of_isProper_of_topologicalKrullDim_le_zero)

universe u

-- Sheafification on the opens of a space is the instance of the small site here; the instance for
-- enlarged coefficients would make the abelian structures built from it differ by unfolding.
attribute [-instance] Stacks.Cohomology.SpectralLimit.hasSheafifyOpensMax

namespace AlgebraicGeometry

variable (k : Type u) [Field k] {X : Scheme.{u}} (f : X ⟶ Spec (.of k))

/-! ### The zero scheme of a nonzero section -/

/-- The zero scheme of a nonzero global section on an integral scheme is an effective Cartier
divisor. -/
private theorem isEffectiveCartierDivisor_zeroScheme_of_eval_top_ne_zero [IsIntegral X]
    (L : X.Modules) [SheafOfModules.IsInvertible X.sheaf.obj X.ringCatSheaf.property L]
    (s : L.sections) (hs : s.eval (op ⊤) ≠ 0) :
    Stacks.Divisors.IsEffectiveCartierDivisor (zeroScheme X L (s.eval (op ⊤))) :=
  (isEffectiveCartierDivisor_zeroScheme_iff_isRegularSection X L s).mpr
    (isRegularSection_of_eval_top_ne_zero L s hs)

/-- **The zero scheme of a nonzero global section of an invertible module on a proper scheme of
dimension at most one over a field is finite over that field.** -/
theorem isFinite_zeroScheme_of_eval_top_ne_zero [IsProper f] [IsIntegral X]
    (hdim : topologicalKrullDim X ≤ 1) (L : X.Modules)
    [SheafOfModules.IsInvertible X.sheaf.obj X.ringCatSheaf.property L] (s : L.sections)
    (hs : s.eval (op ⊤) ≠ 0) :
    IsFinite ((zeroScheme X L (s.eval (op ⊤))).subschemeι ≫ f) :=
  have _hD := isEffectiveCartierDivisor_zeroScheme_of_eval_top_ne_zero L s hs
  isFinite_divisorSubscheme k f hdim (zeroScheme X L (s.eval (op ⊤)))

/-- **An invertible module with a nonzero global section whose zero scheme is empty is
isomorphic to the structure sheaf.** -/
theorem nonempty_unit_iso_of_supportSet_zeroScheme_eq_empty [IsIntegral X] (L : X.Modules)
    [SheafOfModules.IsInvertible X.sheaf.obj X.ringCatSheaf.property L] (s : L.sections)
    (hs : s.eval (op ⊤) ≠ 0)
    (hempty : (zeroScheme X L (s.eval (op ⊤))).supportSet = ∅) :
    Nonempty ((SheafOfModules.unit X.ringCatSheaf : X.Modules) ≅ L) :=
  have hreg : IsRegularSection X.sheaf.obj X.ringCatSheaf.property s :=
    isRegularSection_of_eval_top_ne_zero L s hs
  have _hD := isEffectiveCartierDivisor_zeroScheme_of_eval_top_ne_zero L s hs
  have hunit := Stacks.Divisors.isIso_unitToInvertibleSheaf_of_supportSet_eq_empty
    (zeroScheme X L (s.eval (op ⊤))) hempty
  ⟨@asIso _ _ _ _
      (Stacks.Divisors.unitToInvertibleSheaf (zeroScheme X L (s.eval (op ⊤)))) hunit ≪≫
    (invertibleSheafIsoZeroSchemeOfIsRegularSection L s hreg).symm⟩

/-- **On an integral scheme the nonvanishing locus of a nonzero global section of an invertible
module is the complement of its zero scheme.** -/
theorem nonvanishingLocus_eq_compl_supportSet_zeroScheme [IsIntegral X] (L : X.Modules)
    [SheafOfModules.IsInvertible X.sheaf.obj X.ringCatSheaf.property L] (s : L.sections)
    (hs : s.eval (op ⊤) ≠ 0) :
    nonvanishingLocus (X := X.toRingedSpace) L s =
      (zeroScheme X L (s.eval (op ⊤))).supportSetᶜ :=
  have hreg : IsRegularSection X.sheaf.obj X.ringCatSheaf.property s :=
    isRegularSection_of_eval_top_ne_zero L s hs
  have _hD := isEffectiveCartierDivisor_zeroScheme_of_eval_top_ne_zero L s hs
  have hsec : _root_.SheafOfModules.sectionsMap
      (invertibleSheafIsoZeroSchemeOfIsRegularSection L s hreg).hom s =
      Stacks.Divisors.canonicalSections (zeroScheme X L (s.eval (op ⊤))) :=
    Scheme.Modules.sections_ext_of_eval_top
      (invertibleSheafIsoZeroSchemeOfIsRegularSection_section L s hreg)
  (Stacks.SheafOfModules.nonvanishingLocus_sectionsMap X.toRingedSpace
    (invertibleSheafIsoZeroSchemeOfIsRegularSection L s hreg) s).symm.trans
      ((congrArg (nonvanishingLocus (X := X.toRingedSpace)
        (Stacks.Divisors.invertibleSheaf' (zeroScheme X L (s.eval (op ⊤))))) hsec).trans
          (Stacks.Divisors.nonvanishingChart_canonicalSections
            (zeroScheme X L (s.eval (op ⊤)))))

/-! ### The Euler characteristic on a scheme finite over the base field -/

/-- **The positive-degree cohomology of a quasi-coherent module on an affine scheme over a field
vanishes.** This is Serre vanishing, [Stacks, Tag 01XB], for
`AlgebraicGeometry.cohomologyOverField`. -/
theorem isZero_cohomologyOverField_pos_of_isAffine {Z : Scheme.{u}} (g : Z ⟶ Spec (.of k))
    [IsAffine Z] (G : Z.Modules) [G.IsQuasicoherent] (i : ℕ) (hi : 0 < i) :
    IsZero (cohomologyOverField k g G i) :=
  (isZero_cohomologyOverField_iff_isZero_hgroup k g G i).mpr
    (Stacks.Cohomology.Cech.isZero_hgroup_of_isAffineOpen Z G ⊤ (isAffineOpen_top Z) i hi)

/-- **On a scheme finite over a field the Euler characteristic of a coherent module is the
dimension of its space of sections in degree zero.** -/
theorem eulerCharacteristic_eq_finrank_cohomologyOverField_zero_of_isFinite {Z : Scheme.{u}}
    (g : Z ⟶ Spec (.of k)) [IsFinite g] (G : Z.Modules) (hG : SheafOfModules.IsCoherent G) :
    @eulerCharacteristic k _ Z g _ G hG =
      (Module.finrank k (cohomologyOverField k g G 0) : ℤ) := by
  have hqc : G.IsQuasicoherent :=
    (Stacks.AlgebraicGeometry.CoherentTFAE.isQuasicoherent_isFiniteType_of_isCoherent G).1
  have hZ : IsAffine Z := isAffine_of_isAffineHom g
  have hz : ∀ m, 1 ≤ m → Module.finrank k (cohomologyOverField k g G m) = 0 := fun m hm =>
    have := ModuleCat.subsingleton_of_isZero (isZero_cohomologyOverField_pos_of_isAffine k g G m hm)
    Module.finrank_zero_of_subsingleton
  rw [eulerCharacteristic_eq_finsum, finsum_eq_sum_of_support_subset
    (f := fun m : ℕ => (-1 : ℤ) ^ m * (Module.finrank k (cohomologyOverField k g G m) : ℤ))
    (s := Finset.range 1) fun m hm => ?_]
  · rw [Finset.sum_range_one]; ring
  · by_contra hn
    simp only [Finset.coe_range, Set.mem_Iio, not_lt] at hn
    simp [hz m hn] at hm

/-! ### The degree of an invertible module with a nonzero section -/

/-- **[Stacks, Tag 02O6] over a field base**, in universally quantified form: the cohomology of
a coherent module on a scheme proper over a field is finite dimensional. -/
alias cohomologyFiniteDimensionalOverField_of_isProper := cohomologyFiniteDimensionalOverField

/-- **[Stacks, Tag 02O6] at the structure sheaf of a scheme proper over a field.** -/
theorem forall_finiteDimensional_cohomologyOverField_unit [IsProper f] (n : ℕ) :
    FiniteDimensional k (cohomologyOverField k f (SheafOfModules.unit X.ringCatSheaf) n) :=
  have : IsLocallyNoetherian X := LocallyOfFiniteType.isLocallyNoetherian f
  finiteDimensional_cohomologyOverField_of_isProper k f (SheafOfModules.unit X.ringCatSheaf) n

/-- **The degree of an invertible module with a regular global section is the dimension of the
sections of its restriction to the zero scheme of that section**:
`deg(ℒ) = dim_k H⁰(Z(s), ℒ|_{Z(s)})` for a regular global section `s`. -/
theorem invertibleCurveDegree_eq_finrank_cohomologyOverField_zero_zeroScheme_of_isRegularSection
    [IsProper f] (hdim : topologicalKrullDim X ≤ 1) (L : X.Modules)
    [hL : SheafOfModules.IsInvertible X.sheaf.obj X.ringCatSheaf.property L] (s : L.sections)
    (hreg : IsRegularSection X.sheaf.obj X.ringCatSheaf.property s)
    (hunit : ∀ n, FiniteDimensional k
      (cohomologyOverField k f (SheafOfModules.unit X.ringCatSheaf) n)) :
    @invertibleCurveDegree k _ X f _ hdim L hL =
      (Module.finrank k (cohomologyOverField k
        ((zeroScheme X L (s.eval (op ⊤))).subschemeι ≫ f)
        ((Scheme.Modules.pullback (zeroScheme X L (s.eval (op ⊤))).subschemeι).obj L) 0) : ℤ) := by
  have hD : Stacks.Divisors.IsEffectiveCartierDivisor (zeroScheme X L (s.eval (op ⊤))) :=
    (isEffectiveCartierDivisor_zeroScheme_iff_isRegularSection X L s).mpr hreg
  have hfin : IsFinite ((zeroScheme X L (s.eval (op ⊤))).subschemeι ≫ f) :=
    isFinite_divisorSubscheme k f hdim (zeroScheme X L (s.eval (op ⊤)))
  have hnoeth : IsLocallyNoetherian X := LocallyOfFiniteType.isLocallyNoetherian f
  have hnoethZ : IsLocallyNoetherian (zeroScheme X L (s.eval (op ⊤))).subscheme :=
    isLocallyNoetherian_of_isFinite ((zeroScheme X L (s.eval (op ⊤))).subschemeι ≫ f)
  have hLstacks : Stacks.SheafOfModules.IsInvertible X.sheaf.obj X.ringCatSheaf.property L :=
    Stacks.SheafOfModules.IsInvertible.ofAlgebraicGeometry _ _ _ hL
  have hLcoh : SheafOfModules.IsCoherent L :=
    Stacks.AlgebraicGeometry.CoherenceCriteria.isCoherent_of_isInvertible X L
  have hpull : SheafOfModules.IsCoherent
      ((Scheme.Modules.pullback (zeroScheme X L (s.eval (op ⊤))).subschemeι).obj L) :=
    isCoherent_pullback (zeroScheme X L (s.eval (op ⊤))).subschemeι L
  have hpush : SheafOfModules.IsCoherent
      ((Scheme.Modules.pushforward (zeroScheme X L (s.eval (op ⊤))).subschemeι).obj
        ((Scheme.Modules.pullback (zeroScheme X L (s.eval (op ⊤))).subschemeι).obj L)) :=
    isCoherent_pushforward_of_isClosedImmersion (zeroScheme X L (s.eval (op ⊤))).subschemeι _
  rw [invertibleCurveDegree_eq_eulerCharacteristic_zeroScheme_of_isFinite k f hdim L s hreg hunit,
    eulerCharacteristic_pushforward_of_isClosedImmersion k
      (zeroScheme X L (s.eval (op ⊤))).subschemeι f
      ((Scheme.Modules.pullback (zeroScheme X L (s.eval (op ⊤))).subschemeι).obj L) hpull hpush,
    eulerCharacteristic_eq_finrank_cohomologyOverField_zero_of_isFinite k
      ((zeroScheme X L (s.eval (op ⊤))).subschemeι ≫ f)
      ((Scheme.Modules.pullback (zeroScheme X L (s.eval (op ⊤))).subschemeι).obj L) hpull]

/-- **The degree of an invertible module with a nonzero global section is the dimension of the
sections of its restriction to the zero scheme of that section**, on an integral scheme, where a
nonzero section is regular. -/
theorem invertibleCurveDegree_eq_finrank_cohomologyOverField_zero_zeroScheme [IsProper f]
    [IsIntegral X] (hdim : topologicalKrullDim X ≤ 1) (L : X.Modules)
    [hL : SheafOfModules.IsInvertible X.sheaf.obj X.ringCatSheaf.property L] (s : L.sections)
    (hs : s.eval (op ⊤) ≠ 0)
    (hunit : ∀ n, FiniteDimensional k
      (cohomologyOverField k f (SheafOfModules.unit X.ringCatSheaf) n)) :
    @invertibleCurveDegree k _ X f _ hdim L hL =
      (Module.finrank k (cohomologyOverField k
        ((zeroScheme X L (s.eval (op ⊤))).subschemeι ≫ f)
        ((Scheme.Modules.pullback (zeroScheme X L (s.eval (op ⊤))).subschemeι).obj L) 0) : ℤ) :=
  invertibleCurveDegree_eq_finrank_cohomologyOverField_zero_zeroScheme_of_isRegularSection k f
    hdim L s (isRegularSection_of_eval_top_ne_zero L s hs) hunit

/-- **The degree of an invertible module with a nonzero global section is nonnegative**, on a
proper integral scheme of dimension at most one over a field. -/
@[stacks 0B40 "part (1)"]
theorem invertibleCurveDegree_nonneg_of_eval_top_ne_zero [IsProper f] [IsIntegral X]
    (hdim : topologicalKrullDim X ≤ 1) (L : X.Modules)
    [hL : SheafOfModules.IsInvertible X.sheaf.obj X.ringCatSheaf.property L] (s : L.sections)
    (hs : s.eval (op ⊤) ≠ 0) :
    0 ≤ @invertibleCurveDegree k _ X f _ hdim L hL := by
  rw [invertibleCurveDegree_eq_finrank_cohomologyOverField_zero_zeroScheme k f hdim L s hs
    (forall_finiteDimensional_cohomologyOverField_unit k f)]
  exact Int.natCast_nonneg _

/-! ### A section vanishing at a point -/

/-- **The zero scheme of a global section with a zero is nonempty.** -/
theorem nonempty_zeroScheme_subscheme_of_exists_notMem_nonvanishingLocus [IsIntegral X]
    (L : X.Modules) [SheafOfModules.IsInvertible X.sheaf.obj X.ringCatSheaf.property L]
    (s : L.sections) (hs : s.eval (op ⊤) ≠ 0)
    (hzero : ∃ y : X, y ∉ nonvanishingLocus (X := X.toRingedSpace) L s) :
    Nonempty (zeroScheme X L (s.eval (op ⊤))).subscheme := by
  obtain ⟨y, hy⟩ := hzero
  rw [nonvanishingLocus_eq_compl_supportSet_zeroScheme L s hs] at hy
  simp only [Set.mem_compl_iff, not_not] at hy
  have : y ∈ Set.range (zeroScheme X L (s.eval (op ⊤))).subschemeι := by
    rw [Scheme.IdealSheafData.range_subschemeι]; exact hy
  obtain ⟨z, -⟩ := this
  exact ⟨z⟩

/-- **The restriction of an invertible module to the zero scheme of a regular global section is
trivial**, on a proper scheme of dimension at most one over a field. -/
theorem nonempty_pullback_zeroScheme_iso_unit_of_isRegularSection [IsProper f]
    (hdim : topologicalKrullDim X ≤ 1) (L : X.Modules)
    [hL : SheafOfModules.IsInvertible X.sheaf.obj X.ringCatSheaf.property L] (s : L.sections)
    (hreg : IsRegularSection X.sheaf.obj X.ringCatSheaf.property s) :
    Nonempty ((Scheme.Modules.pullback (zeroScheme X L (s.eval (op ⊤))).subschemeι).obj L ≅
      SheafOfModules.unit (zeroScheme X L (s.eval (op ⊤))).subscheme.ringCatSheaf) := by
  have hD : Stacks.Divisors.IsEffectiveCartierDivisor (zeroScheme X L (s.eval (op ⊤))) :=
    (isEffectiveCartierDivisor_zeroScheme_iff_isRegularSection X L s).mpr hreg
  have hfin : IsFinite ((zeroScheme X L (s.eval (op ⊤))).subschemeι ≫ f) :=
    isFinite_divisorSubscheme k f hdim (zeroScheme X L (s.eval (op ⊤)))
  have hdim0 : topologicalKrullDim (zeroScheme X L (s.eval (op ⊤))).subscheme ≤ 0 :=
    topologicalKrullDim_divisorSubscheme_le_zero hdim (zeroScheme X L (s.eval (op ⊤)))
  have hdisc : DiscreteTopology
      ((zeroScheme X L (s.eval (op ⊤))).subscheme : Type u) :=
    discreteTopology_of_isProper_of_topologicalKrullDim_le_zero k
      ((zeroScheme X L (s.eval (op ⊤))).subschemeι ≫ f) hdim0
  have hLpre : SheafOfModules.IsInvertible X.presheaf X.ringCatSheaf.2 L := hL
  have hpull : SheafOfModules.IsInvertible
      (zeroScheme X L (s.eval (op ⊤))).subscheme.presheaf
      (zeroScheme X L (s.eval (op ⊤))).subscheme.ringCatSheaf.2
      ((Scheme.Modules.pullback (zeroScheme X L (s.eval (op ⊤))).subschemeι).obj L) :=
    Stacks.AlgebraicGeometry.Tag09NY.isInvertible_modulePullback
      (zeroScheme X L (s.eval (op ⊤))).subschemeι L hLpre
  have hpull' : Stacks.SheafOfModules.IsInvertible
      (zeroScheme X L (s.eval (op ⊤))).subscheme.presheaf
      (zeroScheme X L (s.eval (op ⊤))).subscheme.ringCatSheaf.2
      ((Scheme.Modules.pullback (zeroScheme X L (s.eval (op ⊤))).subschemeι).obj L) :=
    Stacks.InvertibleBridge.stacksIsInvertible_of_algebraicGeometryIsInvertible
  exact Stacks.SheafOfModules.nonempty_iso_unit_of_discreteTopology
    (zeroScheme X L (s.eval (op ⊤))).subscheme _

/-- **The restriction of an invertible module to the zero scheme of a global section is
trivial**, on a proper integral scheme of dimension at most one over a field, where a nonzero
section is regular. -/
theorem nonempty_pullback_zeroScheme_iso_unit [IsProper f] [IsIntegral X]
    (hdim : topologicalKrullDim X ≤ 1) (L : X.Modules)
    [hL : SheafOfModules.IsInvertible X.sheaf.obj X.ringCatSheaf.property L] (s : L.sections)
    (hs : s.eval (op ⊤) ≠ 0) :
    Nonempty ((Scheme.Modules.pullback (zeroScheme X L (s.eval (op ⊤))).subschemeι).obj L ≅
      SheafOfModules.unit (zeroScheme X L (s.eval (op ⊤))).subscheme.ringCatSheaf) :=
  nonempty_pullback_zeroScheme_iso_unit_of_isRegularSection k f hdim L s
    (isRegularSection_of_eval_top_ne_zero L s hs)

/-- **The degree of an invertible module with a nonzero global section whose zero scheme is
nonempty is positive.** -/
theorem invertibleCurveDegree_pos_of_nonempty_zeroScheme [IsProper f] [IsIntegral X]
    (hdim : topologicalKrullDim X ≤ 1) (L : X.Modules)
    [hL : SheafOfModules.IsInvertible X.sheaf.obj X.ringCatSheaf.property L] (s : L.sections)
    (hs : s.eval (op ⊤) ≠ 0)
    (hne : Nonempty (zeroScheme X L (s.eval (op ⊤))).subscheme) :
    0 < @invertibleCurveDegree k _ X f _ hdim L hL := by
  obtain ⟨e⟩ := nonempty_pullback_zeroScheme_iso_unit k f hdim L s hs
  rw [invertibleCurveDegree_eq_finrank_cohomologyOverField_zero_zeroScheme k f hdim L s hs
      (forall_finiteDimensional_cohomologyOverField_unit k f),
    finrank_cohomologyOverField_eq_of_iso k
      ((zeroScheme X L (s.eval (op ⊤))).subschemeι ≫ f) e 0]
  have _ : FiniteDimensional k (cohomologyOverField k
      ((zeroScheme X L (s.eval (op ⊤))).subschemeι ≫ f)
      (SheafOfModules.unit (zeroScheme X L (s.eval (op ⊤))).subscheme.ringCatSheaf) 0) :=
    forall_finiteDimensional_cohomologyOverField_unit k
      ((zeroScheme X L (s.eval (op ⊤))).subschemeι ≫ f) 0
  have _ : Nontrivial (cohomologyOverField k
      ((zeroScheme X L (s.eval (op ⊤))).subschemeι ≫ f)
      (SheafOfModules.unit (zeroScheme X L (s.eval (op ⊤))).subscheme.ringCatSheaf) 0) := by
    have _ : Nonempty ((⊤ : (zeroScheme X L (s.eval (op ⊤))).subscheme.Opens) :
        Type u) := ⟨⟨Classical.choice hne, trivial⟩⟩
    have _ : Nontrivial
        Γ(SheafOfModules.unit (zeroScheme X L (s.eval (op ⊤))).subscheme.ringCatSheaf, ⊤) :=
      Scheme.component_nontrivial (zeroScheme X L (s.eval (op ⊤))).subscheme ⊤
    exact (cohomologyOverFieldZeroEquivSections k
      ((zeroScheme X L (s.eval (op ⊤))).subschemeι ≫ f)
      (SheafOfModules.unit (zeroScheme X L (s.eval (op ⊤))).subscheme.ringCatSheaf)).nontrivial
  exact_mod_cast Module.finrank_pos (R := k)

/-- **A nonzero section with a zero forces positive degree.** On a proper integral scheme of
dimension at most one over a field, a nonzero global section of an invertible module which
vanishes at some point forces the degree of that module to be positive. -/
@[stacks 0B40 "part (2)"]
theorem invertibleCurveDegree_pos_of_eval_top_ne_zero [IsProper f] [IsIntegral X]
    (hdim : topologicalKrullDim X ≤ 1) (L : X.Modules)
    [hL : SheafOfModules.IsInvertible X.sheaf.obj X.ringCatSheaf.property L] (s : L.sections)
    (hs : s.eval (op ⊤) ≠ 0)
    (hzero : ∃ y : X, y ∉ nonvanishingLocus (X := X.toRingedSpace) L s) :
    0 < @invertibleCurveDegree k _ X f _ hdim L hL :=
  invertibleCurveDegree_pos_of_nonempty_zeroScheme k f hdim L s hs
    (nonempty_zeroScheme_subscheme_of_exists_notMem_nonvanishingLocus L s hs hzero)

/-! ### A section of an invertible module of nonpositive degree -/

/-- **An invertible module of nonpositive degree with a nonzero global section has empty zero
scheme.** -/
theorem supportSet_zeroScheme_eq_empty_of_invertibleCurveDegree_nonpos [IsProper f] [IsIntegral X]
    (hdim : topologicalKrullDim X ≤ 1) (L : X.Modules)
    [hL : SheafOfModules.IsInvertible X.sheaf.obj X.ringCatSheaf.property L] (s : L.sections)
    (hs : s.eval (op ⊤) ≠ 0) (hdeg : @invertibleCurveDegree k _ X f _ hdim L hL ≤ 0) :
    (zeroScheme X L (s.eval (op ⊤))).supportSet = ∅ := by
  by_contra hne
  obtain ⟨x, hx⟩ := Set.nonempty_iff_ne_empty.mpr hne
  have hrange : x ∈ Set.range (zeroScheme X L (s.eval (op ⊤))).subschemeι := by
    rw [Scheme.IdealSheafData.range_subschemeι]; exact hx
  obtain ⟨z, -⟩ := hrange
  exact absurd (invertibleCurveDegree_pos_of_nonempty_zeroScheme k f hdim L s hs ⟨z⟩)
    (not_lt.mpr hdeg)

/-- **Multiplication by a nowhere vanishing global section of an invertible module is an
isomorphism `𝒪_X ⟶ ℒ`.** -/
theorem isIso_unitHomEquiv_symm_of_nonvanishingLocus_eq_univ (L : X.Modules)
    [hL : SheafOfModules.IsInvertible X.presheaf X.ringCatSheaf.property L] (s : L.sections)
    (hs : nonvanishingLocus (X := X.toRingedSpace) L s = Set.univ) :
    IsIso (L.unitHomEquiv.symm s) := by
  have _ : ∀ x : X.toRingedSpace.carrier,
      IsLocalRing (Stacks.SheafOfModules.TensorStalkRingedSpace.ringStalk X.toRingedSpace x) :=
    fun x => X.isLocalRing x
  have hLs : Stacks.SheafOfModules.IsInvertible X.toRingedSpace.presheaf
      (structureSheafRing X.toRingedSpace).property L :=
    Stacks.SheafOfModules.IsInvertible.ofAlgebraicGeometry _ _ _ hL
  have hle : ∀ V : X.Opens, V ≤ nonvanishingOpen (X := X.toRingedSpace) L s := by
    intro V x _
    change x ∈ nonvanishingLocus (X := X.toRingedSpace) L s
    rw [hs]
    exact Set.mem_univ x
  exact Stacks.SheafOfModules.isIso_of_isIso_val_app _ fun A => by
    rw [ConcreteCategory.isIso_iff_bijective]
    exact Stacks.SheafOfModules.bijective_smul_eval_of_le_nonvanishingOpen
      (X := X.toRingedSpace) L s A.unop (hle A.unop)

/-- **A nonzero section of a module of nonpositive degree trivializes it.** On a proper integral
scheme of dimension at most one over a field, let `ℒ` be an invertible module with `deg(ℒ) ≤ 0`
and a nonzero global section `s`. Then multiplication by `s` is an isomorphism `𝒪_X ⟶ ℒ`. -/
@[stacks 0B40 "part (4), in the stronger form the source's proof supports and the text does \
not state: the multiplication map O_X -> L of the given section is itself an isomorphism, not \
merely L isomorphic to O_X abstractly. The weaker reading is the corollary \
isTrivial_of_invertibleCurveDegree_nonpos beside it"]
theorem isIso_unitHomEquiv_symm_of_invertibleCurveDegree_nonpos [IsProper f] [IsIntegral X]
    (hdim : topologicalKrullDim X ≤ 1) (L : X.Modules)
    [hL : SheafOfModules.IsInvertible X.sheaf.obj X.ringCatSheaf.property L] (s : L.sections)
    (hs : s.eval (op ⊤) ≠ 0) (hdeg : @invertibleCurveDegree k _ X f _ hdim L hL ≤ 0) :
    IsIso (L.unitHomEquiv.symm s) :=
  have hL' : SheafOfModules.IsInvertible X.presheaf X.ringCatSheaf.property L := hL
  isIso_unitHomEquiv_symm_of_nonvanishingLocus_eq_univ L s
    (by
      rw [nonvanishingLocus_eq_compl_supportSet_zeroScheme L s hs,
        supportSet_zeroScheme_eq_empty_of_invertibleCurveDegree_nonpos k f hdim L s hs hdeg,
        Set.compl_empty])

/-- **An invertible module of nonpositive degree with a nonzero global section is trivial**, on
a proper integral scheme of dimension at most one over a field. -/
@[stacks 0B40 "part (4) as stated -- L is isomorphic to O_X"]
theorem isTrivial_of_invertibleCurveDegree_nonpos [IsProper f] [IsIntegral X]
    (hdim : topologicalKrullDim X ≤ 1) (L : X.Modules)
    [hL : SheafOfModules.IsInvertible X.sheaf.obj X.ringCatSheaf.property L] (s : L.sections)
    (hs : s.eval (op ⊤) ≠ 0) (hdeg : @invertibleCurveDegree k _ X f _ hdim L hL ≤ 0) :
    SheafOfModules.IsTrivial X.presheaf X.ringCatSheaf.property L :=
  have h := isIso_unitHomEquiv_symm_of_invertibleCurveDegree_nonpos k f hdim L s hs hdeg
  ⟨(@asIso _ _ _ _ (L.unitHomEquiv.symm s) h).symm⟩

/-! ### An invertible module whose inverse also has a nonzero section -/

/-- The inverse `𝒩^{⊗ -1}` of an invertible module is invertible. -/
private theorem isInvertible_tensorPowerModule_neg_one (N : X.Modules)
    [SheafOfModules.IsInvertible X.presheaf X.ringCatSheaf.property N] :
    SheafOfModules.IsInvertible X.presheaf X.ringCatSheaf.property (tensorPowerModule N (-1)) :=
  Stacks.SheafOfModules.Invertible.tensorPower_isInvertible X.presheaf X.ringCatSheaf.property
    N (-1)

/-- **The section pairing of a trivialization `ℒ ⊗ 𝒩 ≅ 𝒪_X` vanishes when its second argument
does.** -/
theorem tensorPairing_zero_right
    {L N : SheafOfModules.{u} (structureSheafRing X.toRingedSpace)}
    (ψ : ((Stacks.SheafOfModules.Tensor.sheafTensor
        ⟨X.toRingedSpace.presheaf, X.toRingedSpace.IsSheaf⟩).obj L).obj N ≅
          _root_.SheafOfModules.unit _) (W : X.Opens)
    (a : L.val.obj (op W)) :
    tensorPairing ψ W a (0 : N.val.obj (op W)) = 0 := by
  have hz : toTensorSheafSection X.toRingedSpace L N (op W) 0 = 0 :=
    ((Stacks.SheafOfModules.TensorStalkRingedSpace.sheafifyUnit X.toRingedSpace
      ((PresheafOfModules.tensorObj (O := (X.toRingedSpace).presheaf) (L.val)
        (N.val)))).app (op W)).hom.map_zero
  unfold tensorPairing
  rw [TensorProduct.tmul_zero, hz]
  exact (ψ.hom.val.app (op W)).hom.map_zero

/-- **On an integral scheme a nonzero global section of an invertible module vanishes somewhere
short of everywhere: its nonvanishing locus is nonempty.** -/
theorem nonempty_nonvanishingLocus_of_eval_top_ne_zero [IsIntegral X] (L : X.Modules)
    [SheafOfModules.IsInvertible X.sheaf.obj X.ringCatSheaf.property L] (s : L.sections)
    (hs : s.eval (op ⊤) ≠ 0) :
    (nonvanishingLocus (X := X.toRingedSpace) L s).Nonempty := by
  have hD := isEffectiveCartierDivisor_zeroScheme_of_eval_top_ne_zero L s hs
  rw [nonvanishingLocus_eq_compl_supportSet_zeroScheme L s hs, Set.nonempty_compl]
  intro hall
  have hnd := isNowhereDense_supportSet_of_isEffectiveCartierDivisor
    (zeroScheme X L (s.eval (op ⊤))) hD
  rw [IsNowhereDense, hall] at hnd
  simp only [closure_univ, interior_univ] at hnd
  obtain ⟨x⟩ : Nonempty X := inferInstance
  exact (Set.eq_empty_iff_forall_notMem.mp hnd x) (Set.mem_univ x)

/-- **On an integral scheme the product of a nonzero global section of an invertible module and a
nonzero global section of its inverse is nonzero.** -/
theorem globalSectionsMulNegOne_ne_zero [IsIntegral X] (L : X.Modules)
    [hL : SheafOfModules.IsInvertible X.presheaf X.ringCatSheaf.property L]
    (s : L.sections) (hs : s.eval (op ⊤) ≠ 0)
    (t : (tensorPowerModule L (-1)).sections) (ht : t.eval (op ⊤) ≠ 0) :
    globalSectionsMulNegOne L (s.eval (op ⊤)) (t.eval (op ⊤)) ≠ 0 := by
  have hL' : SheafOfModules.IsInvertible X.sheaf.obj X.ringCatSheaf.property L := hL
  have hN' : SheafOfModules.IsInvertible X.sheaf.obj X.ringCatSheaf.property
      (tensorPowerModule L (-1)) :=
    isInvertible_tensorPowerModule_neg_one L
  have hLs : Stacks.SheafOfModules.IsInvertible X.presheaf X.ringCatSheaf.property L :=
    Stacks.SheafOfModules.IsInvertible.ofAlgebraicGeometry _ _ _ hL
  intro hzero
  set ψ := mulNegOneIso X.presheaf X.ringCatSheaf.property L with hψ
  set V : X.Opens := nonvanishingOpen (X := X.toRingedSpace) L s with hVdef
  obtain ⟨x, hx⟩ := nonempty_nonvanishingLocus_of_eval_top_ne_zero L s hs
  have hi : V ⟶ (⊤ : X.Opens) := homOfLE le_top
  have htop : tensorPairing ψ ⊤ (s.eval (op ⊤)) (t.eval (op ⊤)) = 0 := by
    rw [show tensorPairing ψ ⊤ (s.eval (op ⊤)) (t.eval (op ⊤)) =
        globalSectionsMulNegOne L (s.eval (op ⊤)) (t.eval (op ⊤)) from
      Stacks.SheafOfModules.Invertible.mulNegOneIso_toSheafify X.presheaf
        X.ringCatSheaf.property L (op ⊤) _ _]
    exact hzero
  have hSV : s.eval (op V) = (L.val.map hi.op).hom (s.eval (op ⊤)) := by
    simp [PresheafOfModules.sections.eval]
  have hres := Stacks.SheafOfModules.tensorPairing_res ψ hi (s.eval (op ⊤)) (t.eval (op ⊤))
  rw [htop, map_zero] at hres
  have h0 : tensorPairing ψ V (s.eval (op V))
      (((tensorPowerModule L (-1)).val.map hi.op).hom (t.eval (op ⊤))) = 0 := by
    rw [hSV]; exact hres.symm
  have hz := Stacks.SheafOfModules.tensorPairing_left_injective ψ s V (fun y hy => hy)
    (h0.trans (tensorPairing_zero_right ψ V (s.eval (op V))).symm)
  exact ht (@eq_zero_of_map_le_top_eq_zero_of_isIntegral X _ (tensorPowerModule L (-1)) hN'
    (t.eval (op ⊤)) V ⟨⟨x, hx⟩⟩ hz)

/-- **An invertible module whose inverse also has a nonzero section is trivial.** If an
invertible module `ℒ` on an integral scheme universally closed over a field and its inverse
`ℒ^{⊗ -1}` both have nonzero global sections, then `ℒ ≅ 𝒪_X`. -/
@[stacks 0B40 "part (3)"]
theorem isTrivial_of_eval_top_ne_zero_of_inverse [IsIntegral X] [UniversallyClosed f]
    (L : X.Modules) [hL : SheafOfModules.IsInvertible X.presheaf X.ringCatSheaf.property L]
    (s : L.sections) (hs : s.eval (op ⊤) ≠ 0)
    (t : (tensorPowerModule L (-1)).sections) (ht : t.eval (op ⊤) ≠ 0) :
    SheafOfModules.IsTrivial X.presheaf X.ringCatSheaf.property L := by
  have hfield : IsField Γ(X, ⊤) := isField_of_universallyClosed k f
  obtain ⟨b, hb⟩ := hfield.mul_inv_cancel (globalSectionsMulNegOne_ne_zero L s hs t ht)
  exact Stacks.AlgebraicGeometry.PicardBaseChange.isTrivial_of_isUnit_globalSectionsMulNegOne
    L _ _ (IsUnit.of_mul_eq_one b hb)

/-! ### A nonzero map of invertible modules -/

/-- The tensor product of an invertible module with the inverse of an invertible module is
invertible. -/
theorem isInvertible_tensorSheaf_tensorPowerModule_neg_one (L N : X.Modules)
    [hL : SheafOfModules.IsInvertible X.presheaf X.ringCatSheaf.property L]
    [hN : SheafOfModules.IsInvertible X.presheaf X.ringCatSheaf.property N] :
    SheafOfModules.IsInvertible X.presheaf X.ringCatSheaf.property
      (((Stacks.SheafOfModules.Tensor.sheafTensor
          ⟨X.toRingedSpace.presheaf, X.toRingedSpace.IsSheaf⟩).obj L).obj
          (tensorPowerModule N (-1))) :=
  have hNinv := isInvertible_tensorPowerModule_neg_one N
  have _ : Stacks.SheafOfModules.IsInvertible X.presheaf X.ringCatSheaf.property L :=
    Stacks.SheafOfModules.IsInvertible.ofAlgebraicGeometry _ _ _ hL
  have _ : Stacks.SheafOfModules.IsInvertible X.presheaf X.ringCatSheaf.property
      (tensorPowerModule N (-1)) :=
    Stacks.SheafOfModules.IsInvertible.ofAlgebraicGeometry _ _ _ hNinv
  Stacks.InvertibleBridge.isInvertible_iff.mpr
    (Stacks.SheafOfModules.isInvertible_tensorSheaf X.presheaf X.ringCatSheaf.property L
      (tensorPowerModule N (-1)))

/-- **The global section of `ℒ ⊗ 𝒩^{⊗ -1}` attached to a morphism `φ : 𝒩 ⟶ ℒ`**, for `𝒩`
invertible: tensor `φ` by `𝒩^{⊗ -1}` and read its source `𝒩 ⊗ 𝒩^{⊗ -1}` as `𝒪_X`. -/
noncomputable def tensorInverseHomSection (N L : X.Modules)
    [SheafOfModules.IsInvertible X.presheaf X.ringCatSheaf.property N] (φ : N ⟶ L) :
    (((Stacks.SheafOfModules.Tensor.sheafTensor
        ⟨X.toRingedSpace.presheaf, X.toRingedSpace.IsSheaf⟩).obj L).obj
        (tensorPowerModule N (-1))).sections :=
  (((Stacks.SheafOfModules.Tensor.sheafTensor
      ⟨X.toRingedSpace.presheaf, X.toRingedSpace.IsSheaf⟩).obj L).obj
      (tensorPowerModule N (-1))).unitHomEquiv
    ((mulNegOneIso X.presheaf X.ringCatSheaf.property N).inv ≫
      ((Stacks.SheafOfModules.Tensor.sheafTensor.{_, _, u, u, u}
          ⟨X.toRingedSpace.presheaf, X.toRingedSpace.IsSheaf⟩).flip.obj
        (tensorPowerModule N (-1))).map φ)

/-- **The section attached to a nonzero morphism is nonzero.** -/
theorem eval_top_tensorInverseHomSection_ne_zero (N L : X.Modules)
    [SheafOfModules.IsInvertible X.presheaf X.ringCatSheaf.property N] (φ : N ⟶ L)
    (hφ : φ ≠ 0) : (tensorInverseHomSection N L φ).eval (op ⊤) ≠ 0 := by
  have hinv := isInvertible_tensorPowerModule_neg_one N
  have hEq : ((Stacks.SheafOfModules.Tensor.sheafTensor.{_, _, u, u, u}
          ⟨X.toRingedSpace.presheaf, X.toRingedSpace.IsSheaf⟩).flip.obj
      (tensorPowerModule N (-1))).IsEquivalence := inferInstance
  have hAdd : ((Stacks.SheafOfModules.Tensor.sheafTensor.{_, _, u, u, u}
          ⟨X.toRingedSpace.presheaf, X.toRingedSpace.IsSheaf⟩).flip.obj
      (tensorPowerModule N (-1))).Additive := inferInstance
  intro h
  have hzero : (((Stacks.SheafOfModules.Tensor.sheafTensor
      ⟨X.toRingedSpace.presheaf, X.toRingedSpace.IsSheaf⟩).obj L).obj
      (tensorPowerModule N (-1))).unitHomEquiv
      0 = 0 :=
    Scheme.Modules.sections_ext_of_eval_top rfl
  have hs : tensorInverseHomSection N L φ =
      (((Stacks.SheafOfModules.Tensor.sheafTensor
          ⟨X.toRingedSpace.presheaf, X.toRingedSpace.IsSheaf⟩).obj L).obj
          (tensorPowerModule N (-1))).unitHomEquiv 0 := by
    rw [hzero]
    exact Scheme.Modules.sections_ext_of_eval_top h
  have hψ : (mulNegOneIso X.presheaf X.ringCatSheaf.property N).inv ≫
      ((Stacks.SheafOfModules.Tensor.sheafTensor.{_, _, u, u, u}
          ⟨X.toRingedSpace.presheaf, X.toRingedSpace.IsSheaf⟩).flip.obj
        (tensorPowerModule N (-1))).map φ =
      (0 : SheafOfModules.unit (Stacks.SheafOfModules.Tensor.ringSheaf
            ⟨X.toRingedSpace.presheaf, X.toRingedSpace.IsSheaf⟩) ⟶
          ((Stacks.SheafOfModules.Tensor.sheafTensor.{_, _, u, u, u}
              ⟨X.toRingedSpace.presheaf, X.toRingedSpace.IsSheaf⟩).flip.obj
            (tensorPowerModule N (-1))).obj L) :=
    (((Stacks.SheafOfModules.Tensor.sheafTensor
        ⟨X.toRingedSpace.presheaf, X.toRingedSpace.IsSheaf⟩).obj L).obj
        (tensorPowerModule N (-1))).unitHomEquiv.injective hs
  have hmap : ((Stacks.SheafOfModules.Tensor.sheafTensor.{_, _, u, u, u}
          ⟨X.toRingedSpace.presheaf, X.toRingedSpace.IsSheaf⟩).flip.obj
      (tensorPowerModule N (-1))).map φ = 0 :=
    ((Iso.inv_comp_eq (mulNegOneIso X.presheaf X.ringCatSheaf.property N)).mp hψ).trans
      Limits.comp_zero
  exact hφ (((Stacks.SheafOfModules.Tensor.sheafTensor.{_, _, u, u, u}
          ⟨X.toRingedSpace.presheaf, X.toRingedSpace.IsSheaf⟩).flip.obj
    (tensorPowerModule N (-1))).map_injective
      (hmap.trans (Functor.map_zero ((Stacks.SheafOfModules.Tensor.sheafTensor.{_, _, u, u, u}
          ⟨X.toRingedSpace.presheaf, X.toRingedSpace.IsSheaf⟩).flip.obj
        (tensorPowerModule N (-1))) N L).symm))

/-- **If multiplication by the section attached to `φ` is an isomorphism then so is `φ`.** -/
theorem isIso_of_isIso_unitHomEquiv_symm_tensorInverseHomSection (N L : X.Modules)
    [SheafOfModules.IsInvertible X.presheaf X.ringCatSheaf.property N] (φ : N ⟶ L)
    (h : IsIso ((((Stacks.SheafOfModules.Tensor.sheafTensor
        ⟨X.toRingedSpace.presheaf, X.toRingedSpace.IsSheaf⟩).obj L).obj
        (tensorPowerModule N (-1))).unitHomEquiv.symm
      (tensorInverseHomSection N L φ))) : IsIso φ := by
  have hinv := isInvertible_tensorPowerModule_neg_one N
  have hEq : ((Stacks.SheafOfModules.Tensor.sheafTensor.{_, _, u, u, u}
          ⟨X.toRingedSpace.presheaf, X.toRingedSpace.IsSheaf⟩).flip.obj
      (tensorPowerModule N (-1))).IsEquivalence := inferInstance
  rw [tensorInverseHomSection, Equiv.symm_apply_apply] at h
  let h' : IsIso ((mulNegOneIso X.presheaf X.ringCatSheaf.property N).inv ≫
      ((Stacks.SheafOfModules.Tensor.sheafTensor.{_, _, u, u, u}
          ⟨X.toRingedSpace.presheaf, X.toRingedSpace.IsSheaf⟩).flip.obj
        (tensorPowerModule N (-1))).map φ) := h
  let h2 : IsIso (((Stacks.SheafOfModules.Tensor.sheafTensor.{_, _, u, u, u}
          ⟨X.toRingedSpace.presheaf, X.toRingedSpace.IsSheaf⟩).flip.obj
      (tensorPowerModule N (-1))).map φ) :=
    @IsIso.of_isIso_comp_left _ _ _ _ _
      (mulNegOneIso X.presheaf X.ringCatSheaf.property N).inv
      (((Stacks.SheafOfModules.Tensor.sheafTensor.{_, _, u, u, u}
          ⟨X.toRingedSpace.presheaf, X.toRingedSpace.IsSheaf⟩).flip.obj
        (tensorPowerModule N (-1))).map φ)
      (Iso.isIso_inv (mulNegOneIso X.presheaf X.ringCatSheaf.property N)) h'
  exact isIso_of_fully_faithful ((Stacks.SheafOfModules.Tensor.sheafTensor.{_, _, u, u, u}
          ⟨X.toRingedSpace.presheaf, X.toRingedSpace.IsSheaf⟩).flip.obj
    (tensorPowerModule N (-1))) φ

/-- **The degree of `ℒ ⊗ 𝒩^{⊗ -1}` is `deg(ℒ) - deg(𝒩)`**, on a proper curve over a field. -/
theorem invertibleCurveDegree_tensorSheaf_tensorPowerModule_neg_one [IsCurve k f] [IsProper f]
    (hdim : topologicalKrullDim X ≤ 1) (N L : X.Modules)
    [hN : SheafOfModules.IsInvertible X.presheaf X.ringCatSheaf.property N]
    [hL : SheafOfModules.IsInvertible X.presheaf X.ringCatSheaf.property L] :
    @invertibleCurveDegree k _ X f _ hdim
        (((Stacks.SheafOfModules.Tensor.sheafTensor
            ⟨X.toRingedSpace.presheaf, X.toRingedSpace.IsSheaf⟩).obj L).obj
            (tensorPowerModule N (-1)))
        (isInvertible_tensorSheaf_tensorPowerModule_neg_one L N) =
      invertibleCurveDegree k f hdim L - invertibleCurveDegree k f hdim N := by
  have hNinv := isInvertible_tensorPowerModule_neg_one N
  have hTL : SheafOfModules.IsInvertible X.presheaf X.ringCatSheaf.property
      (((Stacks.SheafOfModules.Tensor.sheafTensor
          ⟨X.toRingedSpace.presheaf, X.toRingedSpace.IsSheaf⟩).obj L).obj
          (tensorPowerModule N (-1))) :=
    isInvertible_tensorSheaf_tensorPowerModule_neg_one L N
  have hTN : SheafOfModules.IsInvertible X.presheaf X.ringCatSheaf.property
      (((Stacks.SheafOfModules.Tensor.sheafTensor
          ⟨X.toRingedSpace.presheaf, X.toRingedSpace.IsSheaf⟩).obj N).obj
          (tensorPowerModule N (-1))) :=
    isInvertible_tensorSheaf_tensorPowerModule_neg_one N N
  have h1 := curveDegree_tensorSheaf_eq_add k f hdim L (tensorPowerModule N (-1)) 1 1
  have h2 := curveDegree_tensorSheaf_eq_add k f hdim N (tensorPowerModule N (-1)) 1 1
  have h3 : invertibleCurveDegree k f hdim
      (((Stacks.SheafOfModules.Tensor.sheafTensor
          ⟨X.toRingedSpace.presheaf, X.toRingedSpace.IsSheaf⟩).obj N).obj
          (tensorPowerModule N (-1))) = 0 :=
    invertibleCurveDegree_eq_zero_of_iso_unit k f hdim _
      (mulNegOneIso X.presheaf X.ringCatSheaf.property N)
  rw [invertibleCurveDegree_eq_curveDegree_one k f hdim
      (((Stacks.SheafOfModules.Tensor.sheafTensor
          ⟨X.toRingedSpace.presheaf, X.toRingedSpace.IsSheaf⟩).obj N).obj
          (tensorPowerModule N (-1)))] at h3
  rw [invertibleCurveDegree_eq_curveDegree_one k f hdim
      (((Stacks.SheafOfModules.Tensor.sheafTensor
          ⟨X.toRingedSpace.presheaf, X.toRingedSpace.IsSheaf⟩).obj L).obj
          (tensorPowerModule N (-1))),
    invertibleCurveDegree_eq_curveDegree_one k f hdim L,
    invertibleCurveDegree_eq_curveDegree_one k f hdim N]
  simp only [one_mul, Nat.cast_one] at h1 h2 h3 ⊢
  omega

/-- **A nonzero morphism of invertible modules does not decrease the degree.** On a proper
curve over a field, a nonzero morphism `𝒩 ⟶ ℒ` of invertible modules forces
`deg(𝒩) ≤ deg(ℒ)`. -/
@[stacks 0B40 "part (5), the inequality deg(N) <= deg(L)"]
theorem invertibleCurveDegree_le_of_hom_ne_zero [IsCurve k f] [IsProper f]
    (hdim : topologicalKrullDim X ≤ 1) (N L : X.Modules)
    [hN : SheafOfModules.IsInvertible X.presheaf X.ringCatSheaf.property N]
    [hL : SheafOfModules.IsInvertible X.presheaf X.ringCatSheaf.property L]
    (φ : N ⟶ L) (hφ : φ ≠ 0) :
    invertibleCurveDegree k f hdim N ≤ invertibleCurveDegree k f hdim L := by
  have hnn := invertibleCurveDegree_nonneg_of_eval_top_ne_zero k f hdim
    (((Stacks.SheafOfModules.Tensor.sheafTensor
        ⟨X.toRingedSpace.presheaf, X.toRingedSpace.IsSheaf⟩).obj L).obj
        (tensorPowerModule N (-1)))
    (hL := isInvertible_tensorSheaf_tensorPowerModule_neg_one L N)
    (tensorInverseHomSection N L φ) (eval_top_tensorInverseHomSection_ne_zero N L φ hφ)
  rw [invertibleCurveDegree_tensorSheaf_tensorPowerModule_neg_one k f hdim N L] at hnn
  omega

/-- **A nonzero morphism of invertible modules of equal degree is an isomorphism**, on a proper
curve over a field. -/
@[stacks 0B40 "part (5), the equality case: the morphism is an isomorphism"]
theorem isIso_of_invertibleCurveDegree_eq_of_hom_ne_zero [IsCurve k f] [IsProper f]
    (hdim : topologicalKrullDim X ≤ 1) (N L : X.Modules)
    [hN : SheafOfModules.IsInvertible X.presheaf X.ringCatSheaf.property N]
    [hL : SheafOfModules.IsInvertible X.presheaf X.ringCatSheaf.property L]
    (φ : N ⟶ L) (hφ : φ ≠ 0)
    (heq : invertibleCurveDegree k f hdim N = invertibleCurveDegree k f hdim L) : IsIso φ := by
  have hdeg : @invertibleCurveDegree k _ X f _ hdim
      (((Stacks.SheafOfModules.Tensor.sheafTensor
          ⟨X.toRingedSpace.presheaf, X.toRingedSpace.IsSheaf⟩).obj L).obj
          (tensorPowerModule N (-1)))
      (isInvertible_tensorSheaf_tensorPowerModule_neg_one L N) ≤ 0 := by
    rw [invertibleCurveDegree_tensorSheaf_tensorPowerModule_neg_one k f hdim N L, heq]
    omega
  exact isIso_of_isIso_unitHomEquiv_symm_tensorInverseHomSection N L φ
    (isIso_unitHomEquiv_symm_of_invertibleCurveDegree_nonpos k f hdim
      (((Stacks.SheafOfModules.Tensor.sheafTensor
          ⟨X.toRingedSpace.presheaf, X.toRingedSpace.IsSheaf⟩).obj L).obj
          (tensorPowerModule N (-1)))
      (hL := isInvertible_tensorSheaf_tensorPowerModule_neg_one L N)
      (tensorInverseHomSection N L φ)
      (eval_top_tensorInverseHomSection_ne_zero N L φ hφ) hdeg)

/-- **An isomorphism of invertible modules preserves the degree**, on a proper scheme of
dimension at most one over a field. -/
@[stacks 0B40 "part (5), the converse of the equality case: an isomorphism has equal degrees, \
so the equality holds exactly when the morphism is an isomorphism"]
theorem invertibleCurveDegree_eq_of_isIso [IsProper f] (hdim : topologicalKrullDim X ≤ 1)
    (N L : X.Modules)
    [hN : SheafOfModules.IsInvertible X.presheaf X.ringCatSheaf.property N]
    [hL : SheafOfModules.IsInvertible X.presheaf X.ringCatSheaf.property L]
    (φ : N ⟶ L) [IsIso φ] :
    invertibleCurveDegree k f hdim N = invertibleCurveDegree k f hdim L :=
  invertibleCurveDegree_eq_of_iso k f hdim (asIso φ)

/-- **The degree of an invertible module with a nonzero global section is the dimension of the
ring of functions on the zero scheme of that section**: `deg(ℒ) = dim_k Γ(D, 𝒪_D)` for every
`D` equal to the zero scheme `Z(s)`. -/
theorem invertibleCurveDegree_eq_finrank_globalSections_zeroScheme_of_dim_le_one [IsProper f]
    [IsIntegral X] (hdim : topologicalKrullDim X ≤ 1) (L : X.Modules)
    [hL : SheafOfModules.IsInvertible X.sheaf.obj X.ringCatSheaf.property L] (s : L.sections)
    (hs : s.eval (op ⊤) ≠ 0) (D : X.IdealSheafData)
    (hD : zeroScheme X L (s.eval (op ⊤)) = D) :
    letI : Algebra k Γ(D.subscheme, ⊤) :=
      ((Scheme.ΓSpecIso (.of k)).inv ≫ (D.subschemeι ≫ f).appTop).hom.toAlgebra
    @invertibleCurveDegree k _ X f _ hdim L hL =
      (Module.finrank k Γ(D.subscheme, ⊤) : ℤ) := by
  subst hD
  have h254 := invertibleCurveDegree_eq_finrank_cohomologyOverField_zero_zeroScheme k f hdim L s
    hs (forall_finiteDimensional_cohomologyOverField_unit k f)
  have hiso := (nonempty_pullback_zeroScheme_iso_unit k f hdim L s hs).some
  have htriv := finrank_cohomologyOverField_eq_of_iso k
    ((zeroScheme X L (s.eval (op ⊤))).subschemeι ≫ f) hiso 0
  have hΓ := finrank_cohomologyOverField_zero_unit_eq_finrank_globalSections k
    ((zeroScheme X L (s.eval (op ⊤))).subschemeι ≫ f)
  rw [h254, htriv, hΓ]

end AlgebraicGeometry

end
