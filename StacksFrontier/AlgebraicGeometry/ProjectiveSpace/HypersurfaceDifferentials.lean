module

public import StacksFrontier.AlgebraicGeometry.ProjEulerSequence.Exactness
public import StacksFrontier.AlgebraicGeometry.ProjectiveBundleSplitting.PullbackStableLocallyFree
public import StacksFrontier.AlgebraicGeometry.ProjectiveSpace.Cohomology.HypersurfaceTwistCohomology
public import StacksFrontier.AlgebraicGeometry.Divisors.ConormalZeroScheme
public import StacksFrontier.AlgebraicGeometry.Perfect.Coherator.FlatPushforwardCoherator
public import StacksFrontier.AlgebraicGeometry.ConormalSequenceRight.SchemeShortExact

/-!
# A smooth hypersurface in `𝐏ⁿ`, `n ≥ 3`, has no global differential forms

Let `k` be a field, let `s` be a global section of `𝒪(d)` on `𝐏ⁿ_k` with nonzero value on the whole
space, and let `i : Z ⟶ 𝐏ⁿ_k` be the inclusion of its zero scheme. If `Z` is smooth over `k` and
`n ≥ 3`, then `H⁰(Z, Ω_{Z/k}) = 0`. The argument is the classical one:

* the conormal sequence `0 ⟶ 𝒞_{Z/𝐏ⁿ} ⟶ i^* Ω_{𝐏ⁿ/k} ⟶ Ω_{Z/k} ⟶ 0` is short exact because `Z`
  is smooth ([Stacks, Tag 06AA]);
* `𝒞_{Z/𝐏ⁿ} ≅ i^* 𝒪(-d)` (`AlgebraicGeometry.conormalSheafZeroSchemeIso`), and
  `H¹(Z, i^* 𝒪(-d)) = 0` since `H¹(𝐏ⁿ, 𝒪(-d)) = H²(𝐏ⁿ, 𝒪(-2d)) = 0` for `n ≥ 3`;
* the Euler sequence `0 ⟶ Ω_{𝐏ⁿ/k} ⟶ 𝒪(-1)^{⊕(n+1)} ⟶ 𝒪 ⟶ 0` ([Stacks, Tag 0FMH]) stays short
  exact after `i^*`, its third term being locally free, so `H⁰(Z, i^* Ω_{𝐏ⁿ/k})` injects into
  `H⁰(Z, i^* 𝒪(-1))^{⊕(n+1)}`, which vanishes since `H⁰(𝐏ⁿ, 𝒪(-1)) = H¹(𝐏ⁿ, 𝒪(-1-d)) = 0`;
* the long exact sequence of cohomology on `Z` ([Stacks, Tag 0111]) then gives
  `H⁰(Z, Ω_{Z/k}) = 0`, and a morphism `𝒪_Z ⟶ Ω_{Z/k}` is a global section.

## Main results

* `Stacks.AlgebraicGeometry.ProjEulerSequence.shortExact_map_pullback_eulerShortComplex`: **the
  restricted Euler sequence** `0 ⟶ i^* Ω_{𝐏ⁿ/R} ⟶ i^* 𝒪(-1)^{⊕(n+1)} ⟶ 𝒪_Z ⟶ 0` is short exact,
  for an arbitrary morphism `i : Z ⟶ 𝐏ⁿ_R`.
* `AlgebraicGeometry.Scheme.Modules.subsingleton_unit_hom_of_isZero_sections`: a module with no
  nonzero global sections receives no nonzero morphism from the structure sheaf.
* `Stacks.ProjectiveSpace.Differentials.isZero_sections_pullback_twistMinusOneSum`:
  `H⁰(Z, i^* 𝒪(-1)^{⊕(n+1)}) = 0` for a hypersurface in `𝐏ⁿ_k`, `n ≥ 2`.
* `Stacks.ProjectiveSpace.Differentials.subsingleton_unit_hom_relativeDifferentials_zeroScheme`
  and
  `Stacks.ProjectiveSpace.Differentials.subsingleton_unit_hom_relativeDifferentials_hypersurface`:
  **`H⁰(Z, Ω_{Z/k}) = 0` for a smooth hypersurface `Z ⊆ 𝐏ⁿ_k`, `n ≥ 3`**, for the zero scheme of a
  section and for the hypersurface of a nonzero homogeneous polynomial.

## References

* [Stacks Project, Tag 06AA](https://stacks.math.columbia.edu/tag/06AA)
* [Stacks Project, Tag 01UZ](https://stacks.math.columbia.edu/tag/01UZ)
* [Stacks Project, Tag 0FMH](https://stacks.math.columbia.edu/tag/0FMH)
* [Stacks Project, Tag 01XT](https://stacks.math.columbia.edu/tag/01XT)
* [Stacks Project, Tag 0111](https://stacks.math.columbia.edu/tag/0111)
-/

@[expose] public noncomputable section

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits Opposite
open Stacks.AlgebraicGeometry.ProjPolyChart (polyGrading projToSpecCoeff)
open Stacks.AlgebraicGeometry.ProjEulerSequence

attribute [local instance] MvPolynomial.gradedAlgebra

universe u

namespace AlgebraicGeometry.Scheme.Modules

/-- **A module with no nonzero global sections receives no nonzero morphism from the structure
sheaf**: a morphism `𝒪_X ⟶ M` is a global section of `M`
(`SheafOfModules.unitHomEquiv`), and a section is determined by its value on `X`. -/
theorem subsingleton_unit_hom_of_isZero_sections {X : Scheme.{u}} (M : X.Modules)
    (h : IsZero ((Stacks.Cohomology.sectionsFunctor X ⊤).obj M)) :
    Subsingleton (SheafOfModules.unit X.ringCatSheaf ⟶ M) := by
  have hs : Subsingleton ((Stacks.Cohomology.sectionsFunctor X ⊤).obj M) :=
    ModuleCat.subsingleton_of_isZero h
  refine ⟨fun φ ψ => M.unitHomEquiv.injective (Subtype.ext (funext fun U => ?_))⟩
  rw [← (M.unitHomEquiv φ).2 (homOfLE (le_top : U.unop ≤ ⊤)).op,
    ← (M.unitHomEquiv ψ).2 (homOfLE (le_top : U.unop ≤ ⊤)).op]
  exact congrArg _ (@Subsingleton.elim _ hs _ _)

end AlgebraicGeometry.Scheme.Modules

namespace Stacks.AlgebraicGeometry.ProjEulerSequence

variable (R : Type u) [CommRing R] (n : ℕ)

/-- The Euler sequence `Ω_{𝐏ⁿ/R} ⟶ 𝒪(-1)^{⊕(n+1)} ⟶ 𝒪` of [Stacks, Tag 0FMH], as a short complex
of `𝒪_{𝐏ⁿ}`-modules in the category `AlgebraicGeometry.Scheme.Modules`. -/
abbrev eulerShortComplex : ShortComplex (AlgebraicGeometry.Proj (polyGrading R n)).Modules :=
  ShortComplex.mk (eulerFirstArrow R n) (eulerSurjection R n)
    (eulerFirstArrow_comp_eulerSurjection R n)

/-- The Euler sequence is short exact (`shortExact_eulerSequence`), read in
`AlgebraicGeometry.Scheme.Modules`. -/
theorem shortExact_eulerShortComplex : (eulerShortComplex R n).ShortExact :=
  shortExact_eulerSequence R n

/-- **The restricted Euler sequence.** For any morphism of schemes `i : Z ⟶ 𝐏ⁿ_R`,

`0 ⟶ i^* Ω_{𝐏ⁿ/R} ⟶ i^* 𝒪(-1)^{⊕(n+1)} ⟶ i^* 𝒪 ⟶ 0`

is short exact: the third term of the Euler sequence is the structure sheaf, which is locally
free, so the sequence splits at every stalk and stays exact after pullback
(`AlgebraicGeometry.shortExact_map_pullback_of_isLocallyFree`). -/
theorem shortExact_map_pullback_eulerShortComplex {Z : Scheme.{u}}
    (i : Z ⟶ AlgebraicGeometry.Proj (polyGrading R n)) :
    ((eulerShortComplex R n).map (Scheme.Modules.pullback i)).ShortExact :=
  shortExact_map_pullback_of_isLocallyFree i (shortExact_eulerShortComplex R n)
    (Stacks.SheafOfModules.Invertible.IsFiniteLocallyFreeOfRank.isLocallyFree
      (R := (AlgebraicGeometry.Proj (polyGrading R n)).ringCatSheaf) (SheafOfModules.unit _) 1)

end Stacks.AlgebraicGeometry.ProjEulerSequence

namespace Stacks.ProjectiveSpace.Differentials

open Stacks.ProjectiveSpace.Cohomology AlgebraicGeometry.ProjectiveSpectrum.Proj

variable (k : Type u) [Field k] (n : ℕ)

/-- Projective `n`-space over `k`. -/
local notation "𝐏" => AlgebraicGeometry.Proj (polyGrading k n)

/-- **`H⁰(Z, i^* 𝒪(-1)^{⊕(n+1)}) = 0` for a hypersurface `Z ⊆ 𝐏ⁿ_k`, `n ≥ 2`.** Global sections
commute with the finite direct sum, and each summand `H⁰(Z, i^* 𝒪(-1))` vanishes by
`Stacks.ProjectiveSpace.Cohomology.isZero_rightDerived_pullback_twistingSheaf`, since
`H⁰(𝐏ⁿ, 𝒪(-1)) = 0` and `H¹(𝐏ⁿ, 𝒪(-1-d)) = 0`. -/
theorem isZero_sections_pullback_twistMinusOneSum (hn : 2 ≤ n) (d : ℤ)
    (s : (twistingSheafModule (polyGrading k n) d).sections) (hs : s.eval (op ⊤) ≠ 0) :
    IsZero ((Stacks.Cohomology.sectionsFunctor (zeroScheme (𝐏)
          (twistingSheafModule (polyGrading k n) d) (s.eval (op ⊤))).subscheme ⊤).obj
        ((Scheme.Modules.pullback (zeroScheme (𝐏)
          (twistingSheafModule (polyGrading k n) d) (s.eval (op ⊤))).subschemeι).obj
            (twistMinusOneSum k n))) := by
  have := AlgebraicGeometry.pullback_additive (zeroScheme (𝐏)
    (twistingSheafModule (polyGrading k n) d) (s.eval (op ⊤))).subschemeι
  let G : SheafOfModules.{u}
      (Stacks.AlgebraicGeometry.ProjTrivialization.projRingSheaf (polyGrading k n)) ⥤
        ModuleCat.{u} _ :=
    Scheme.Modules.pullback (zeroScheme (𝐏)
      (twistingSheafModule (polyGrading k n) d) (s.eval (op ⊤))).subschemeι ⋙
    Stacks.Cohomology.sectionsFunctor (zeroScheme (𝐏)
      (twistingSheafModule (polyGrading k n) d) (s.eval (op ⊤))).subscheme ⊤
  have hG : G.Additive := ⟨fun {_ _ f g} =>
    (inferInstance : (Scheme.Modules.pullback (zeroScheme (𝐏)
      (twistingSheafModule (polyGrading k n) d) (s.eval (op ⊤))).subschemeι ⋙
    Stacks.Cohomology.sectionsFunctor (zeroScheme (𝐏)
      (twistingSheafModule (polyGrading k n) d) (s.eval (op ⊤))).subscheme ⊤).Additive).map_add
      (f := f) (g := g)⟩
  have hj : ∀ j, IsZero (G.obj (twistMinusOneFamily k n j)) := fun j =>
    (isZero_rightDerived_pullback_twistingSheaf k n 0 d (-1) s hs
      (isZero_twistCohomology k n (-1) 0 (by omega))
      (isZero_twistCohomology k n (-1 - d) (0 + 1) (by omega))).of_iso
      ((Functor.rightDerivedZeroIsoSelf (Stacks.Cohomology.sectionsFunctor
        (zeroScheme (𝐏)
          (twistingSheafModule (polyGrading k n) d) (s.eval (op ⊤))).subscheme ⊤)).app
        ((Scheme.Modules.pullback (zeroScheme (𝐏)
          (twistingSheafModule (polyGrading k n) d) (s.eval (op ⊤))).subschemeι).obj
            (twistingSheafModule (polyGrading k n) (-1)))).symm
  refine IsZero.of_iso ?_ (G.mapBiproduct (twistMinusOneFamily k n))
  exact (IsZero.iff_id_eq_zero _).2 (biproduct.hom_ext _ _ fun j => (hj j).eq_of_tgt _ _)

/-- **A smooth hypersurface in `𝐏ⁿ_k`, `n ≥ 3`, has no global differential forms.** Let `s` be a
global section of `𝒪(d)` on `𝐏ⁿ_k` with nonzero value on the whole space and suppose its zero
scheme `Z` is smooth over `k`. Then every morphism `𝒪_Z ⟶ Ω_{Z/k}` is zero, that is
`H⁰(Z, Ω_{Z/k}) = 0`. See the module docstring for the argument. -/
theorem subsingleton_unit_hom_relativeDifferentials_zeroScheme (hn : 3 ≤ n) (d : ℤ)
    (s : (twistingSheafModule (polyGrading k n) d).sections) (hs : s.eval (op ⊤) ≠ 0)
    (h : AlgebraicGeometry.Smooth ((zeroScheme (𝐏)
      (twistingSheafModule (polyGrading k n) d) (s.eval (op ⊤))).subschemeι ≫
        projToSpecCoeff k n)) :
    Subsingleton (SheafOfModules.unit (zeroScheme (𝐏)
        (twistingSheafModule (polyGrading k n) d) (s.eval (op ⊤))).subscheme.ringCatSheaf ⟶
      Scheme.Hom.relativeDifferentials ((zeroScheme (𝐏)
        (twistingSheafModule (polyGrading k n) d) (s.eval (op ⊤))).subschemeι ≫
          projToSpecCoeff k n)) := by
  have hgen := MvPolynomial.adjoin_homogeneousSubmodule_one_eq_top (Fin (n + 1)) k
  let i := (zeroScheme (𝐏) (twistingSheafModule (polyGrading k n) d)
    (s.eval (op ⊤))).subschemeι
  let Q := Stacks.Cohomology.sectionsFunctor (zeroScheme (𝐏)
    (twistingSheafModule (polyGrading k n) d) (s.eval (op ⊤))).subscheme ⊤
  have hC := Stacks.ConormalSequenceRight.conormalShortComplex_shortExact i
    (projToSpecCoeff k n) h
  have h𝒞 : IsZero ((Q.rightDerived 1).obj
      (Stacks.ConormalSequenceRight.conormalShortComplex i (projToSpecCoeff k n)).X₁) :=
    (isZero_rightDerived_pullback_twistingSheaf k n 1 d (-d) s hs
      (isZero_twistCohomology k n (-d) 1 (by omega))
      (isZero_twistCohomology k n (-d - d) (1 + 1) (by omega))).of_iso
      ((Q.rightDerived 1).mapIso (conormalSheafZeroSchemeIso (𝐏)
        (twistingSheafModule (polyGrading k n) d) s (twistingSheafModule (polyGrading k n) (-d))
        (twistNegTensorIsoUnit (polyGrading k n) hgen d)
        (isRegularSection_of_eval_top_ne_zero _ s hs)))
  have hE := shortExact_map_pullback_eulerShortComplex k n i
  obtain ⟨-, hmono, -⟩ := Stacks.Cohomology.RightDerivedDelta.exists_delta_exact_composableArrows₅
    hE Q
  have hB : IsZero ((Q.rightDerived 0).obj ((eulerShortComplex k n).map
      (Scheme.Modules.pullback i)).X₂) :=
    (isZero_sections_pullback_twistMinusOneSum k n (by omega) d s hs).of_iso
      ((Functor.rightDerivedZeroIsoSelf _).app _)
  have hΩ : IsZero ((Q.rightDerived 0).obj
      (Stacks.ConormalSequenceRight.conormalShortComplex i (projToSpecCoeff k n)).X₂) :=
    @IsZero.of_mono _ _ _ _ _ _ hmono hB
  have h0 := Stacks.Cohomology.RightDerivedDelta.isZero_rightDerived_X₃ hC Q 0 hΩ h𝒞
  exact Scheme.Modules.subsingleton_unit_hom_of_isZero_sections _
    (h0.of_iso ((Functor.rightDerivedZeroIsoSelf _).app _).symm)

end Stacks.ProjectiveSpace.Differentials

namespace Stacks.ProjectiveSpace.Differentials

open Stacks.ProjectiveSpace.Cohomology AlgebraicGeometry.ProjectiveSpectrum.Proj

variable (k : Type u) [Field k] (n : ℕ)

/-- Projective `n`-space over `k`. -/
local notation "𝐏" => AlgebraicGeometry.Proj (polyGrading k n)

/-- **A smooth hypersurface in `𝐏ⁿ_k`, `n ≥ 3`, has no global differential forms**, for the
hypersurface `V(F)` of a nonzero homogeneous polynomial `F` of degree `d`, cut out by the zero
scheme of the section of `𝒪(d)` attached to `F`: if `V(F)` is smooth over `k` then
`H⁰(V(F), Ω_{V(F)/k}) = 0`. -/
theorem subsingleton_unit_hom_relativeDifferentials_hypersurface (hn : 3 ≤ n) (d : ℕ)
    (F : polyGrading k n d) (hF : (F : MvPolynomial (Fin (n + 1)) k) ≠ 0)
    (h : AlgebraicGeometry.Smooth ((zeroScheme (𝐏)
      (twistingSheafModule (polyGrading k n) (d : ℤ))
        (degreeSection (polyGrading k n) d F)).subschemeι ≫
        projToSpecCoeff k n)) :
    Subsingleton (SheafOfModules.unit (zeroScheme (𝐏)
        (twistingSheafModule (polyGrading k n) (d : ℤ))
          (degreeSection (polyGrading k n) d F)).subscheme.ringCatSheaf ⟶
      Scheme.Hom.relativeDifferentials ((zeroScheme (𝐏)
        (twistingSheafModule (polyGrading k n) (d : ℤ))
          (degreeSection (polyGrading k n) d F)).subschemeι ≫ projToSpecCoeff k n)) := by
  have ht := Stacks.PresheafOfModules.sectionOfTop_val_top
    (twistingSheafModule (polyGrading k n) (d : ℤ)).val (degreeSection (polyGrading k n) d F)
  obtain ⟨s, hs, hJ⟩ : ∃ s : (twistingSheafModule (polyGrading k n) (d : ℤ)).sections,
      s.eval (op ⊤) ≠ 0 ∧ degreeSection (polyGrading k n) d F = s.eval (op ⊤) :=
    ⟨_, ht ▸ degreeSection_ne_zero k n d F hF, ht.symm⟩
  rw [hJ] at h ⊢
  exact subsingleton_unit_hom_relativeDifferentials_zeroScheme k n hn _ s hs h

end Stacks.ProjectiveSpace.Differentials

end
