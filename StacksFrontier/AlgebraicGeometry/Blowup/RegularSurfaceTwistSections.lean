module

public import StacksFrontier.Algebra.Category.ModuleCat.Sheaf.InvertibleDualEvaluation
public import StacksFrontier.AlgebraicGeometry.AmpleCohomologicalCriterion.IdealSubobject
public import StacksFrontier.AlgebraicGeometry.Blowup.AmbientSectionsDomain
public import StacksFrontier.AlgebraicGeometry.Blowup.ProjectiveLineReesRelation
public import StacksFrontier.AlgebraicGeometry.Chow.Degrees.DimensionLayerStructureSheafClass
public import StacksFrontier.AlgebraicGeometry.ConormalSourceTransport.Basic
public import StacksFrontier.AlgebraicGeometry.Divisors.ZeroSchemeIdealSheaf
public import StacksFrontier.AlgebraicGeometry.ProjectiveSpace.Cohomology.HypersurfaceCohomology
public import StacksFrontier.AlgebraicGeometry.ProjectiveSpace.Cohomology.ProjectiveLineVanishing
public import StacksFrontier.AlgebraicGeometry.ProjectiveSpace.HyperplaneIsProjectiveSpace
public import StacksCore.Tactic.StacksAttribute

/-!
# The twisted global sections of the blowup of a regular local surface

Let `(A, 𝔪)` be a regular local ring of dimension two and let `X ⟶ Spec A` be the blowup of
`Spec A` in `𝔪`. This file proves that the canonical map

`𝔪ⁿ ⟶ Γ(X, 𝒪_X(n))`

is **bijective for every `n ≥ 0`**, so that `Γ(X, 𝒪_X(n)) = 𝔪ⁿ` in that range. For `n ≥ 0` this
is [Stacks, Tag 0AGS] part (4), whose statement there is `Γ(X, 𝒪_X(n)) = 𝔪^{max(0,n)}`.

## The two halves

**Injectivity** holds in every degree and with no threshold:
`Stacks.Blowup.injective_ambientSections_maximalIdeal`. A regular local ring is a domain, so the
Rees algebra of `𝔪` is a subalgebra of `A[T]` and therefore has no zero divisors, which is what
kills the kernel.

**Surjectivity** is the ideal-sheaf sequence of the blowup inside the projective line, and it is
where the work of this file goes. Let `x₀, x₁` be a minimal generating pair of `𝔪` and let
`i : X ⟶ 𝐏¹_A = Proj A[T₀, T₁]` be the closed immersion of [Stacks, Tag 0AGQ]. Then:

* the kernel of the graded presentation `A[T₀, T₁] ⟶ ⨁ₙ 𝔪ⁿ` is the single degree-one relation
  `x₁T₀ - x₀T₁` (`Stacks.Blowup.ker_reesPresentation_maximalIdeal_eq_span_relation`), so `X` is
  the zero scheme of that relation read as a global section of `𝒪(1)`
  (`Stacks.ProjectiveSpace.exists_iso_zeroScheme_subscheme`);
* the relation is a nonzero polynomial and `A` is a domain, so the section is a nonzerodivisor
  and the ideal sheaf of its zero scheme is `𝒪(1)^∨ ≅ 𝒪(-1)`
  (`AlgebraicGeometry.isIso_zeroSchemeIdealModuleHom` and
  `AlgebraicGeometry.ProjectiveSpectrum.Proj.twistNegOneIsoDualTwistOne` below);
* hence the obstruction to lifting a global section of `(i_*𝒪_X)(n)` to `𝒪_{𝐏¹}(n)` is
  `H¹(𝐏¹_A, 𝒪(n-1))`, which vanishes for every `n ≥ 0` by Serre's computation on the projective
  line (`Stacks.ProjectiveSpace.Cohomology.isZero_lineCohomology_one_of_neg_one_le`);
* a lifted section is the canonical section of a homogeneous polynomial of degree `n`
  (`Stacks.ProjectiveSpace.Cohomology.surjective_degreeSection`), and the transport along
  `Proj ψ` of `Stacks.Blowup.surjective_degreeSection_of_surjective_comp` carries it to the
  canonical section of its image in the Rees algebra.

The general route to surjectivity,
`Stacks.Blowup.exists_forall_surjective_twistedSectionsAddHom_blowUpSpecToProjSpace`, gets the
same conclusion from Serre vanishing applied to the coherent ideal sheaf and so only for *large*
`n`, with no information about the threshold. That route remains valid; what the identification
of the ideal sheaf with `𝒪(-1)` adds is that the threshold may be taken to be `0`, which is the
content of part (4).

## Main results

The elided prefix is `Stacks.Blowup`.

* `AlgebraicGeometry.ProjectiveSpectrum.Proj.twistNegOneIsoDualTwistOne`: `𝒪(-1) ≅ 𝒪(1)^∨`, from
  `𝒪(1) ⊗ 𝒪(-1) ≅ 𝒪`, which is `AlgebraicGeometry.ProjectiveSpectrum.Proj.twistNegTensorIsoUnit`
  at `d = -1`.
* `nonempty_kernelProjSpaceQuotientMapIsoTwistNegOne`: **the ideal sheaf of the blowup of a
  regular local surface inside the projective line is `𝒪(-1)`.**
* `isZero_hgroup_one_twist_of_iso_twistNegOne` and
  `surjective_twistedSectionsAddHom_projSpaceQuotientMap_maximalIdeal`: every global section of
  `(i_*𝒪_X)(n)` comes from `𝐏¹_A` for every `n ≥ 0`.
* `surjective_degreeSection_reesGrading_maximalIdeal` and
  `surjective_ambientSections_maximalIdeal`: the canonical map `𝔪ⁿ ⟶ Γ(X, 𝒪_X(n))` is surjective
  in every nonnegative degree.
* `bijective_ambientSections_maximalIdeal`: **[Stacks, Tag 0AGS] part (4) for `n ≥ 0`.** Through
  `Stacks.Blowup.sectionsIsoIdealPow` this is the isomorphism of `A`-modules
  `Γ(X, 𝒪_X(n)) ≅ 𝔪ⁿ` that the source writes as an equality.

## The negative range

The range `n < 0` of part (4), where the assertion is `Γ(X, 𝒪_X(n)) = A` (the exponent being
`max(0,n) = 0`), is `Stacks.Blowup.bijective_negSections_maximalIdeal` in
`StacksFrontier/AlgebraicGeometry/Blowup/RegularSurfaceNegativeTwistSections.lean`, a descending
induction anchored at `n = 0` on the result of this file.

## Implementation notes

`AlgebraicGeometry.ProjectiveSpectrum.Proj.twistNegTensorIsoUnit` is stated at the degrees
`(-d, d)`; reading it at `d = -1` produces the first factor as `𝒪(-(-1))` rather than `𝒪(1)`,
and unification does not identify those indices on its own, so the correction is made by an
explicit `CategoryTheory.eqToIso`.

The degree-one index is written `((1 : ℕ) : ℤ)` throughout, which is the spelling
`Stacks.ProjectiveSpace.exists_iso_zeroScheme_subscheme` and `AlgebraicGeometry.zeroScheme` are
quoted at.

As in `StacksFrontier/AlgebraicGeometry/Blowup/ProjectiveLineIdealOfEquations.lean`,
`Stacks.Blowup.blowUpSpecToProjSpace` is by definition `AlgebraicGeometry.Proj.map` of the Rees
presentation while the closed-immersion instance is phrased at the former spelling, and instance
search does not unfold the definition to reach it; one `have` supplies the instance at the
`Proj.map` spelling, which is harmless because `AlgebraicGeometry.IsClosedImmersion` is a `Prop`.

## References

* [Stacks Project, Tag 01MT](https://stacks.math.columbia.edu/tag/01MT)
* [Stacks Project, Tag 01WY](https://stacks.math.columbia.edu/tag/01WY)
* [Stacks Project, Tag 02OQ](https://stacks.math.columbia.edu/tag/02OQ)
* [Stacks Project, Tag 0AG6](https://stacks.math.columbia.edu/tag/0AG6)
* [Stacks Project, Tag 0AGQ](https://stacks.math.columbia.edu/tag/0AGQ)
* [Stacks Project, Tag 0AGS](https://stacks.math.columbia.edu/tag/0AGS)
* [Stacks Project, Tag 0B8K](https://stacks.math.columbia.edu/tag/0B8K)
* [Stacks Project, Tag 0C6K](https://stacks.math.columbia.edu/tag/0C6K)
-/

@[expose] public noncomputable section

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits MonoidalCategory Opposite
open TopologicalSpace
open AlgebraicGeometry.ProjectiveSpectrum.Proj
open MvPolynomial (C X)

universe u w

attribute [local instance] MvPolynomial.gradedAlgebra
attribute [local instance] Stacks.ProjectiveSpace.Cohomology.hypersurfaceModulesMonoidal

/-! ### `𝒪(-1)` is the dual of `𝒪(1)` -/

namespace AlgebraicGeometry.ProjectiveSpectrum.Proj

section Twist

variable {S : Type u} {σ : Type w} [CommRing S] [SetLike σ S] [AddSubgroupClass σ S]
  (𝒮 : ℕ → σ) [GradedRing 𝒮]

attribute [local implicit_reducible] TopCat.Sheaf sheafCompose
  Stacks.SheafOfModules.TensorSheafification.structureSheaf
attribute [local instance_reducible] ProjectiveSpectrum.top

/-- **`𝒪(-1)` is the dual of `𝒪(1)` on `Proj 𝒮`**, for `𝒮` generated in degree one: it is a
tensor inverse of `𝒪(1)` by `AlgebraicGeometry.ProjectiveSpectrum.Proj.twistNegTensorIsoUnit` at
`d = -1` (whose first factor `𝒪(-(-1))` is `𝒪(1)` up to `eqToIso`), and a tensor inverse is the
dual by [Stacks, Tag 0B8K]. -/
def twistNegOneIsoDualTwistOne (hgen : Algebra.adjoin (𝒮 0) ((𝒮 1 : Set S)) = ⊤) :
    twistingSheafModule 𝒮 (-1) ≅
      Stacks.AlgebraicGeometry.ReflexiveModules.dualSheaf
        (twistingSheafModule 𝒮 ((1 : ℕ) : ℤ)) :=
  Stacks.SheafOfModules.Invertible.tensorInverseIsoDualSheaf
    (AlgebraicGeometry.Proj 𝒮).sheaf.obj (AlgebraicGeometry.Proj 𝒮).ringCatSheaf.property
    (twistingSheafModule 𝒮 ((1 : ℕ) : ℤ)) (twistingSheafModule 𝒮 (-1))
    (eqToIso (congrArg (fun e : ℤ => (twistingSheafModule 𝒮 e ⊗ twistingSheafModule 𝒮 (-1) :
      (AlgebraicGeometry.Proj 𝒮).Modules)) (show ((1 : ℕ) : ℤ) = -(-1) by norm_num)) ≪≫
      twistNegTensorIsoUnit 𝒮 hgen (-1))

end Twist

end AlgebraicGeometry.ProjectiveSpectrum.Proj

/-! ### The ideal sheaf of the blowup of a regular local surface inside the projective line -/

namespace Stacks.Blowup

open IsLocalRing
open Stacks.ProjectiveCohomology (polyGrading)
open Stacks.LocalCohomology.UniformityIII (ambientSections)

section IdealSheaf

attribute [local implicit_reducible] TopCat.Sheaf sheafCompose
  Stacks.SheafOfModules.TensorSheafification.structureSheaf
attribute [local instance_reducible] ProjectiveSpectrum.top

variable (A : Type u) [CommRing A] [IsRegularLocalRing A] (hdim : ringKrullDim A = 2)
  (x : Fin 2 → A) (hx : ∀ i, x i ∈ maximalIdeal A)
  (hspan : maximalIdeal A = Ideal.span (Set.range x))

include hdim hspan in
/-- **The relation `x₁T₀ - x₀T₁` of a minimal generating pair of the maximal ideal of a regular
local surface is a nonzero polynomial.** If it vanished both coefficients would, so the maximal
ideal would be generated by `0` and `A` would be a field, of dimension `0` rather than `2`. -/
theorem relation_maximalIdeal_ne_zero :
    (C (x 1) * X 0 - C (x 0) * X 1 : MvPolynomial (Fin 2) A) ≠ 0 := by
  intro h
  have hco := fun i : Fin 2 =>
    congrArg (fun p : MvPolynomial (Fin 2) A => p.coeff (Finsupp.single i 1)) h
  have hbot : maximalIdeal A = ⊥ := by
    rw [hspan, Ideal.span_eq_bot]
    rintro r ⟨i, rfl⟩
    fin_cases i
    · simpa [MvPolynomial.coeff_C_mul, MvPolynomial.coeff_X, MvPolynomial.coeff_sub,
        Finsupp.single_eq_single_iff] using hco 1
    · simpa [MvPolynomial.coeff_C_mul, MvPolynomial.coeff_X, MvPolynomial.coeff_sub,
        Finsupp.single_eq_single_iff] using hco 0
  exact (by norm_num : (2 : WithBot ℕ∞) ≠ 0)
    (hdim.symm.trans (ringKrullDim_eq_zero_of_isField
      (IsLocalRing.isField_iff_maximalIdeal_eq.2 hbot)))

include hdim hx hspan in
/-- **The ideal sheaf of the blowup of a regular local surface inside the projective line is
`𝒪(-1)`.** For `A` regular local of dimension two and `x₀, x₁` a minimal generating pair of its
maximal ideal, the kernel of the canonical map `𝒪_{𝐏¹_A} ⟶ i_*𝒪_X` along the closed immersion of
the blowup `X` of `Spec A` in `𝔪` into `𝐏¹_A` is the twisting sheaf `𝒪(-1)`.

The kernel of the graded presentation is the single degree-one relation `x₁T₀ - x₀T₁`, so `X` is
the zero scheme of the global section of `𝒪(1)` that relation determines; the relation is a
nonzero polynomial over a domain, so that section is a nonzerodivisor and the ideal sheaf of its
zero scheme is `𝒪(1)^∨`, which is `𝒪(-1)`. -/
theorem nonempty_kernelProjSpaceQuotientMapIsoTwistNegOne :
    Nonempty ((kernel (projSpaceQuotientMap (A := A) (I := maximalIdeal A) x hx hspan) :
        (AlgebraicGeometry.Proj (polyGrading A 1)).Modules) ≅
      twistingSheafModule (polyGrading A 1) (-1)) := by
  classical
  have : IsDomain A := IsRegularLocalRing.isDomain A
  set 𝒮 : ℕ → Submodule A (MvPolynomial (Fin 2) A) := polyGrading A 1 with h𝒮
  have hgen : Algebra.adjoin (𝒮 0) ((𝒮 1 : Set (MvPolynomial (Fin 2) A))) = ⊤ :=
    MvPolynomial.adjoin_homogeneousSubmodule_one_eq_top (Fin 2) A
  set l : 𝒮 1 := ⟨C (x 1) * X 0 - C (x 0) * X 1,
    (MvPolynomial.mem_homogeneousSubmodule 1 _).2 (isHomogeneous_relation x)⟩ with hl
  set L : (AlgebraicGeometry.Proj 𝒮).Modules := twistingSheafModule 𝒮 ((1 : ℕ) : ℤ) with hL
  set s : L.sections :=
    Stacks.PresheafOfModules.sectionOfTop L.val (degreeSection 𝒮 1 l) with hs
  have hstop : s.eval (op ⊤) = degreeSection 𝒮 1 l :=
    Stacks.PresheafOfModules.sectionOfTop_val_top _ _
  have hsne : s.eval (op ⊤) ≠ 0 := by
    rw [hstop]
    exact Stacks.ProjectiveSpace.Cohomology.degreeSection_ne_zero A 1 1 l
      (relation_maximalIdeal_ne_zero A hdim x hspan)
  have hsreg : AlgebraicGeometry.IsRegularSection (AlgebraicGeometry.Proj 𝒮).sheaf.obj
      (AlgebraicGeometry.Proj 𝒮).ringCatSheaf.property s :=
    AlgebraicGeometry.isRegularSection_of_eval_top_ne_zero L s hsne
  have hsurj : Function.Surjective
      ((reesPresentation (maximalIdeal A) x hx) :
        MvPolynomial (Fin 2) A → reesAlgebra (maximalIdeal A)) :=
    surjective_reesPresentation (maximalIdeal A) x hx hspan
  have hψ : HomogeneousIdeal.irrelevant (reesGrading (maximalIdeal A)) ≤
      (HomogeneousIdeal.irrelevant 𝒮).map (reesPresentation (maximalIdeal A) x hx) :=
    AlgebraicGeometry.Proj.irrelevant_le_map_of_surjective _ hsurj
  have hker : RingHom.ker ((reesPresentation (maximalIdeal A) x hx) :
        MvPolynomial (Fin 2) A →+* reesAlgebra (maximalIdeal A))
      = Ideal.span {(l : MvPolynomial (Fin 2) A)} :=
    ker_reesPresentation_maximalIdeal_eq_span_relation A hdim x hx hspan
  obtain ⟨φ, hφ⟩ := Stacks.ProjectiveSpace.exists_iso_zeroScheme_subscheme
    𝒮 (reesGrading (maximalIdeal A)) (reesPresentation (maximalIdeal A) x hx) hψ hsurj hgen l hker
  have : IsIso φ.hom := ⟨⟨φ.inv, φ.hom_inv_id, φ.inv_hom_id⟩⟩
  have hreg : ∀ U : (AlgebraicGeometry.Proj 𝒮).Opens, Function.Injective
      fun r : Γ(AlgebraicGeometry.Proj 𝒮, U) =>
        r • L.presheaf.map (homOfLE (le_top : U ≤ ⊤)).op (degreeSection 𝒮 1 l) := by
    intro U
    rw [← hstop]
    exact AlgebraicGeometry.injective_smul_res_of_isRegularSection L s hsreg U
  have hiso := AlgebraicGeometry.isIso_zeroSchemeIdealModuleHom L (degreeSection 𝒮 1 l) hreg
  exact ⟨Stacks.Conormal.AffineCotangent.SourceTransport.idealSheafIsoOfIsoSourceOfCompEq φ
      (AlgebraicGeometry.zeroScheme (AlgebraicGeometry.Proj 𝒮) L (degreeSection 𝒮 1 l)).subschemeι
      (AlgebraicGeometry.Proj.map (reesPresentation (maximalIdeal A) x hx) hψ) hφ ≪≫
    (asIso (AlgebraicGeometry.zeroSchemeIdealModuleHom L (degreeSection 𝒮 1 l))).symm ≪≫
      (twistNegOneIsoDualTwistOne 𝒮 hgen).symm⟩

end IdealSheaf

/-! ### Surjectivity on twisted sections in every nonnegative degree -/

/-- **`H¹(𝐏¹_R, ℱ(n)) = 0` for `n ≥ 0` and `ℱ ≅ 𝒪(-1)`.** The `n`-th twist of `𝒪(-1)` is
`𝒪(n - 1)` ([Stacks, Tag 01MT]) and `H¹(𝐏¹_R, 𝒪(d)) = 0` for `d ≥ -1` by Serre's computation on
the projective line. -/
theorem isZero_hgroup_one_twist_of_iso_twistNegOne (R : Type u) [CommRing R]
    (F : SheafOfModules.{u} (Stacks.ProjectiveSpace.Cohomology.projRingSheaf R 1))
    (ε : F ≅ twistingSheaf (polyGrading R 1) (-1)) {n : ℤ} (hn : 0 ≤ n) :
    IsZero (Hgroup (Stacks.ProjectiveSpace.Cohomology.projRingSheaf R 1) ⊤ 1
      (twistSheafOfModules (polyGrading R 1) F n)) := by
  have hmul : twistSheafOfModules (polyGrading R 1) (twistingSheaf (polyGrading R 1) (-1)) n ≅
      twistingSheaf (polyGrading R 1) (-1 + n) :=
    @asIso _ _ _ _
      (Stacks.AlgebraicGeometry.ProjInvertibleLocus.twistMultiplicationMap
        (polyGrading R 1) (-1) n)
      (Stacks.AlgebraicGeometry.ProjRepresentsF1.isIso_twistMultiplicationMap_of_adjoin
        (polyGrading R 1) (Stacks.ProjectiveSpace.SerreVanishing.adjoin_one_polyGrading R 1)
        (-1) n)
  have hline : IsZero (((Stacks.Cohomology.sectionsFunctor
      (AlgebraicGeometry.Proj (polyGrading R 1)) ⊤).rightDerived 1).obj
      (twistingSheaf (polyGrading R 1) (-1 + n))) :=
    Stacks.ProjectiveSpace.Cohomology.isZero_lineCohomology_one_of_neg_one_le R (by omega)
  have hz : IsZero (Hgroup (Stacks.ProjectiveSpace.Cohomology.projRingSheaf R 1) ⊤ 1
      (twistingSheaf (polyGrading R 1) (-1 + n))) :=
    (Stacks.Cohomology.CechAcyclic.isZero_rightDerived_evaluation_iff_isZero_Hgroup
      (Stacks.ProjectiveSpace.Cohomology.projRingSheaf R 1) ⊤ 1
      (twistingSheaf (polyGrading R 1) (-1 + n))).mp hline
  exact hz.of_iso ((Hfunctor (Stacks.ProjectiveSpace.Cohomology.projRingSheaf R 1) ⊤ 1).mapIso
    ((Stacks.AlgebraicGeometry.ProjTwistFunctor.twistFunctor (polyGrading R 1) n).mapIso ε ≪≫
      hmul))

section Sections

variable (A : Type u) [CommRing A] [IsRegularLocalRing A] (hdim : ringKrullDim A = 2)
  (x : Fin 2 → A) (hx : ∀ i, x i ∈ maximalIdeal A)
  (hspan : maximalIdeal A = Ideal.span (Set.range x))

include hdim hx hspan in
/-- **Every global section of `(i_*𝒪_X)(n)` comes from the projective line, for `n ≥ 0`.** For
`A` regular local of dimension two, `x₀, x₁` a minimal generating pair of its maximal ideal and
`i : X ⟶ 𝐏¹_A` the closed immersion of the blowup, the map
`Γ(𝐏¹_A, 𝒪(n)) ⟶ Γ(𝐏¹_A, (i_*𝒪_X)(n))` is surjective for every `n ≥ 0`.

This is
`Stacks.ProjectiveSpace.Cohomology.surjective_twistedSectionsAddHom_of_isZero_firstCohomology`
at `Stacks.Blowup.projSpaceQuotientMap`, whose kernel is `𝒪(-1)`; the hypothesis it needs is
`H¹(𝐏¹_A, 𝒪(n-1)) = 0`, which holds for `n ≥ 0`. Compared with
`Stacks.Blowup.exists_forall_surjective_twistedSectionsAddHom_blowUpSpecToProjSpace`, which gets
the same conclusion from Serre vanishing and therefore only for large `n`, the threshold here is
explicit and equal to zero. -/
theorem surjective_twistedSectionsAddHom_projSpaceQuotientMap_maximalIdeal {n : ℤ}
    (hn : 0 ≤ n) :
    Function.Surjective (Stacks.AlgebraicGeometry.ProjTwistDegreeOneStep.twistedSectionsAddHom
      (polyGrading A 1) (projSpaceQuotientMap (A := A) (I := maximalIdeal A) x hx hspan) n) := by
  obtain ⟨ε⟩ := nonempty_kernelProjSpaceQuotientMapIsoTwistNegOne A hdim x hx hspan
  exact
    @Stacks.ProjectiveSpace.Cohomology.surjective_twistedSectionsAddHom_of_isZero_firstCohomology
      A _ 1 _ _ (projSpaceQuotientMap (A := A) (I := maximalIdeal A) x hx hspan)
      (epi_projSpaceQuotientMap x hx hspan) n
      (isZero_hgroup_one_twist_of_iso_twistNegOne A _ ε hn)

include hdim hx hspan in
/-- **Every global section of `𝒪_X(n)` is the canonical section of a degree-`n` element of the
Rees algebra of the maximal ideal**, for every `n : ℕ`.

The section lifts to `𝐏¹_A` because the ideal sheaf of the blowup there is `𝒪(-1)` and
`H¹(𝐏¹_A, 𝒪(n-1)) = 0` for `n ≥ 0`
(`Stacks.Blowup.surjective_twistedSectionsAddHom_projSpaceQuotientMap_maximalIdeal`); on `𝐏¹_A`
it is the canonical section of a homogeneous polynomial of degree `n`
(`Stacks.ProjectiveSpace.Cohomology.surjective_degreeSection`); and the transport along
`Proj ψ` of `Stacks.Blowup.surjective_degreeSection_of_surjective_comp` carries that to the
canonical section of its image in the Rees algebra. -/
theorem surjective_degreeSection_reesGrading_maximalIdeal (n : ℕ) :
    Function.Surjective (degreeSection (reesGrading (maximalIdeal A)) n) := by
  have hsurj := surjective_reesPresentation (maximalIdeal A) x hx hspan
  have hgen := Stacks.ProjectiveSpace.SerreVanishing.adjoin_one_polyGrading A 1
  have : IsClosedImmersion (AlgebraicGeometry.Proj.map
      (reesPresentation (maximalIdeal A) x hx)
      (AlgebraicGeometry.Proj.irrelevant_le_map_of_surjective _ hsurj)) :=
    isClosedImmersion_blowUpSpecToProjSpace (maximalIdeal A) x hx hspan
  exact surjective_degreeSection_of_surjective_comp (polyGrading A 1)
    (reesGrading (maximalIdeal A)) (reesPresentation (maximalIdeal A) x hx) _
    hsurj hgen n
    (Function.Surjective.comp
      (twistedSectionsUnitMap_surjective (polyGrading A 1) (reesGrading (maximalIdeal A))
        (reesPresentation (maximalIdeal A) x hx) _
        hsurj hgen (n : ℤ))
      (surjective_twistedSectionsAddHom_projSpaceQuotientMap_maximalIdeal A hdim x hx hspan
        (Int.natCast_nonneg n)))
    (Stacks.ProjectiveSpace.Cohomology.surjective_degreeSection A 1 n)

end Sections

/-- **The canonical map `𝔪ⁿ ⟶ Γ(X, 𝒪_X(n))` is surjective in every nonnegative degree**, for
`𝔪` the maximal ideal of a regular local ring of dimension two and `X` the blowup of `Spec A` in
`𝔪`. A minimal generating pair of `𝔪` is available because `𝔪` has `spanFinrank` two; the
statement does not depend on the choice. -/
theorem surjective_ambientSections_maximalIdeal (A : Type u) [CommRing A] [IsRegularLocalRing A]
    (hdim : ringKrullDim A = 2) (n : ℕ) :
    Function.Surjective (ambientSections (maximalIdeal A) n) := by
  obtain ⟨x, hspan⟩ := exists_range_eq_maximalIdeal A hdim
  have hx : ∀ i, x i ∈ maximalIdeal A := fun i => by
    rw [hspan]; exact Ideal.subset_span ⟨i, rfl⟩
  exact surjective_ambientSections_of_surjective_degreeSection n
    (surjective_degreeSection_reesGrading_maximalIdeal A hdim x hx hspan n)

/-- **Stacks Project, Tag 0AGS part (4) in nonnegative degrees.** Let `(A, 𝔪)` be a regular
local ring of dimension two and let `X ⟶ Spec A` be the blowup of `Spec A` in `𝔪`. Then the
canonical map `𝔪ⁿ ⟶ Γ(X, 𝒪_X(n))` is bijective for every `n : ℕ`, which is the assertion
`Γ(X, 𝒪_X(n)) = 𝔪^{max(0,n)}` of the source in that range; through
`Stacks.Blowup.sectionsIsoIdealPow` it is the isomorphism of `A`-modules the equality denotes.

Injectivity is unconditional (`Stacks.Blowup.injective_ambientSections_maximalIdeal`), the Rees
algebra of a nonzero ideal of a domain having no zero divisors. Surjectivity in degree `n ≥ 0` is
`Stacks.Blowup.surjective_ambientSections_maximalIdeal`, where it comes from the identification
of the ideal sheaf of the blowup inside `𝐏¹_A` with `𝒪(-1)` and the vanishing of
`H¹(𝐏¹_A, 𝒪(n-1))` for `n ≥ 0`.

The range `n < 0` of part (4), where the exponent `max(0,n)` is `0`, is
`Stacks.Blowup.bijective_negSections_maximalIdeal`. -/
@[stacks 0AGS "part (4) for n at least 0: for the blowup X of Spec A in the maximal ideal m of a \
regular local ring A of dimension two, the canonical map from m^n to the global sections of \
O_X(n) is bijective, which is Gamma(X, O_X(n)) = m^(max 0 n) in that range"]
theorem bijective_ambientSections_maximalIdeal (A : Type u) [CommRing A] [IsRegularLocalRing A]
    (hdim : ringKrullDim A = 2) (n : ℕ) :
    Function.Bijective (ambientSections (maximalIdeal A) n) :=
  ⟨injective_ambientSections_maximalIdeal A hdim n,
    surjective_ambientSections_maximalIdeal A hdim n⟩

end Stacks.Blowup

end
