module

public import StacksFrontier.AlgebraicGeometry.ProjectiveSpace.Cohomology.HypersurfaceCohomology
public import StacksFrontier.AlgebraicGeometry.ProjectiveSpace.Cohomology.TwistCohomologyMonomial
public import StacksFrontier.AlgebraicGeometry.ClosedImmersionCohomology.Basic

/-!
# The cohomology of the twists restricted to a hypersurface

Let `k` be a field, let `s` be a global section of `𝒪(d)` on `𝐏ⁿ_k` whose value on the whole
space is nonzero, and let `i : Z ⟶ 𝐏ⁿ_k` be the inclusion of its zero scheme. For every `e : ℤ`
the twisted zero-scheme sequence of [Stacks, Tag 0C6K] with `M = 𝒪(e - d)`, read through
`𝒪(e - d) ⊗ 𝒪(d) ≅ 𝒪(e)` ([Stacks, Tag 01MT]), is

`0 ⟶ 𝒪(e - d) ⟶ 𝒪(e) ⟶ i_* i^* 𝒪(e) ⟶ 0`,

and its long exact sequence ([Stacks, Tag 0111]) gives `H^q(𝐏ⁿ_k, i_* i^* 𝒪(e)) = 0` as soon as
`H^q(𝐏ⁿ_k, 𝒪(e))` and `H^{q+1}(𝐏ⁿ_k, 𝒪(e - d))` vanish. The comparison of [Stacks, Tag 01EX]
along the closed immersion `i` moves the vanishing to `H^q(Z, i^* 𝒪(e))`.

Combined with [Stacks, Tag 01XT] (`Stacks.ProjectiveSpace.Cohomology.isZero_twistCohomology`)
this gives, for a hypersurface of any degree in `𝐏ⁿ_k`, `H⁰(Z, i^* 𝒪(-1)) = 0` for `n ≥ 2` and
`H¹(Z, i^* 𝒪(-d)) = 0` for `n ≥ 3`, which is what the vanishing of `H⁰(Z, Ω_{Z/k})` uses.

## Main results

* `AlgebraicGeometry.ProjectiveSpectrum.Proj.twistTensorIsoTwist`: `𝒪(a) ⊗ 𝒪(b) ≅ 𝒪(c)` on
  `Proj 𝒮` for `a + b = c` and `𝒮` generated in degree one.
* `Stacks.ProjectiveSpace.Cohomology.isZero_rightDerived_pushforward_pullback_twistingSheaf`:
  `H^q(𝐏ⁿ_k, i_* i^* 𝒪(e)) = 0` from `H^q(𝐏ⁿ_k, 𝒪(e)) = 0` and
  `H^{q+1}(𝐏ⁿ_k, 𝒪(e - d)) = 0`.
* `Stacks.ProjectiveSpace.Cohomology.isZero_rightDerived_pullback_twistingSheaf`: the same
  vanishing for `H^q(Z, i^* 𝒪(e))`, the cohomology on the hypersurface itself.

## References

* [Stacks Project, Tag 0C6K](https://stacks.math.columbia.edu/tag/0C6K)
* [Stacks Project, Tag 01MT](https://stacks.math.columbia.edu/tag/01MT)
* [Stacks Project, Tag 0111](https://stacks.math.columbia.edu/tag/0111)
* [Stacks Project, Tag 01EX](https://stacks.math.columbia.edu/tag/01EX)
* [Stacks Project, Tag 01XT](https://stacks.math.columbia.edu/tag/01XT)
-/

@[expose] public noncomputable section

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits MonoidalCategory Opposite
open Stacks.AlgebraicGeometry.ProjPolyChart (polyGrading projToSpecCoeff)
open AlgebraicGeometry.ProjectiveSpectrum.Proj

universe u

attribute [local instance] MvPolynomial.gradedAlgebra

/-- The tensor product sheaf of [Stacks, Tag 01CA] as a monoidal structure on the `𝒪_X`-modules
of a scheme, as in `StacksFrontier.AlgebraicGeometry.Divisors.ZeroSchemeExactSequenceTwist`. -/
local instance Stacks.ProjectiveSpace.Cohomology.hypersurfaceTwistModulesMonoidal
    (X : AlgebraicGeometry.Scheme.{u}) : MonoidalCategory X.Modules :=
  Stacks.SheafOfModules.sheafTensorMonoidal X.sheaf.obj X.ringCatSheaf.property

namespace AlgebraicGeometry.ProjectiveSpectrum.Proj

section Twist

variable {S : Type u} {σ : Type u} [CommRing S] [SetLike σ S] [AddSubgroupClass σ S]
  (𝒮 : ℕ → σ) [GradedRing 𝒮]

attribute [local implicit_reducible] TopCat.Sheaf sheafCompose
  Stacks.SheafOfModules.TensorSheafification.structureSheaf
attribute [local instance_reducible] ProjectiveSpectrum.top

/-- **`𝒪(a) ⊗ 𝒪(b) ≅ 𝒪(c)` on `Proj 𝒮` whenever `a + b = c`**, for `𝒮` generated in degree
one: Equation 01MO of [Stacks, Tag 01MT], followed by the identification of `𝒪(a + b)` with
`𝒪(c)`. -/
def twistTensorIsoTwist (hgen : Algebra.adjoin (𝒮 0) ((𝒮 1 : Set S)) = ⊤) (a b c : ℤ)
    (h : a + b = c) :
    (twistingSheafModule 𝒮 a ⊗ twistingSheafModule 𝒮 b :
        (AlgebraicGeometry.Proj 𝒮).Modules) ≅ twistingSheafModule 𝒮 c :=
  Stacks.AlgebraicGeometry.ProjTwistDegreeOneCover.twistMultiplicationIso 𝒮
      (Stacks.AlgebraicGeometry.ProjDegreeOne.iSup_basicOpen_degreeOne_eq_top 𝒮 hgen) a b ≪≫
    eqToIso (congrArg (twistingSheaf 𝒮) h)

end Twist

end AlgebraicGeometry.ProjectiveSpectrum.Proj

namespace Stacks.ProjectiveSpace.Cohomology

variable (k : Type u) [Field k] (n : ℕ)

/-- **The restriction of a twist to a hypersurface has vanishing cohomology, read on `𝐏ⁿ_k`.**
For a global section `s` of `𝒪(d)` with nonzero value on the whole space, zero scheme `Z(s)` and
inclusion `i`, the long exact sequence of `0 ⟶ 𝒪(e - d) ⟶ 𝒪(e) ⟶ i_* i^* 𝒪(e) ⟶ 0` gives
`H^q(𝐏ⁿ_k, i_* i^* 𝒪(e)) = 0` whenever `H^q(𝐏ⁿ_k, 𝒪(e))` and `H^{q+1}(𝐏ⁿ_k, 𝒪(e - d))`
vanish. -/
theorem isZero_rightDerived_pushforward_pullback_twistingSheaf (q : ℕ) (d e : ℤ)
    (s : (twistingSheafModule (polyGrading k n) d).sections) (hs : s.eval (op ⊤) ≠ 0)
    (h₁ : IsZero (twistCohomology k n e q))
    (h₂ : IsZero (twistCohomology k n (e - d) (q + 1))) :
    IsZero (((Stacks.Cohomology.sectionsFunctor (Proj (polyGrading k n)) ⊤).rightDerived q).obj
      ((Scheme.Modules.pushforward (zeroScheme (Proj (polyGrading k n))
          (twistingSheafModule (polyGrading k n) d) (s.eval (op ⊤))).subschemeι).obj
        ((Scheme.Modules.pullback (zeroScheme (Proj (polyGrading k n))
          (twistingSheafModule (polyGrading k n) d) (s.eval (op ⊤))).subschemeι).obj
            (twistingSheafModule (polyGrading k n) e)))) := by
  have hgen := MvPolynomial.adjoin_homogeneousSubmodule_one_eq_top (Fin (n + 1)) k
  obtain ⟨w, hse⟩ := shortExact_zeroScheme_twist_of_isRegularSection
    (Proj (polyGrading k n)) (twistingSheafModule (polyGrading k n) d) s
    (isRegularSection_of_eval_top_ne_zero (twistingSheafModule (polyGrading k n) d) s hs)
    (twistingSheafModule (polyGrading k n) (e - d))
  let β := twistTensorIsoTwist (polyGrading k n) hgen (e - d) d e (sub_add_cancel e d)
  have hX₂ := (isZero_rightDerived_sections_twistingSheaf k n q e h₁).of_iso
    (((Stacks.Cohomology.sectionsFunctor (Proj (polyGrading k n)) ⊤).rightDerived q).mapIso β)
  have hX₁ := isZero_rightDerived_sections_twistingSheaf k n (q + 1) (e - d) h₂
  have h3 := Stacks.Cohomology.RightDerivedDelta.isZero_rightDerived_X₃ hse
    (Stacks.Cohomology.sectionsFunctor (Proj (polyGrading k n)) ⊤) q hX₂ hX₁
  exact h3.of_iso (((Stacks.Cohomology.sectionsFunctor (Proj (polyGrading k n)) ⊤).rightDerived
    q).mapIso ((Scheme.Modules.pushforward _).mapIso ((Scheme.Modules.pullback _).mapIso β.symm)))

/-- **The restriction of a twist to a hypersurface has vanishing cohomology.** For a global
section `s` of `𝒪(d)` with nonzero value on the whole space, zero scheme `Z = Z(s)` and inclusion
`i`, `H^q(Z, i^* 𝒪(e)) = 0` whenever `H^q(𝐏ⁿ_k, 𝒪(e))` and `H^{q+1}(𝐏ⁿ_k, 𝒪(e - d))` vanish. The
vanishing on `𝐏ⁿ_k` is `isZero_rightDerived_pushforward_pullback_twistingSheaf`, and the
comparison of [Stacks, Tag 01EX] along the closed immersion `i` carries it to `Z`. -/
theorem isZero_rightDerived_pullback_twistingSheaf (q : ℕ) (d e : ℤ)
    (s : (twistingSheafModule (polyGrading k n) d).sections) (hs : s.eval (op ⊤) ≠ 0)
    (h₁ : IsZero (twistCohomology k n e q))
    (h₂ : IsZero (twistCohomology k n (e - d) (q + 1))) :
    IsZero (((Stacks.Cohomology.sectionsFunctor (zeroScheme (Proj (polyGrading k n))
          (twistingSheafModule (polyGrading k n) d) (s.eval (op ⊤))).subscheme ⊤).rightDerived
            q).obj
        ((Scheme.Modules.pullback (zeroScheme (Proj (polyGrading k n))
          (twistingSheafModule (polyGrading k n) d) (s.eval (op ⊤))).subschemeι).obj
            (twistingSheafModule (polyGrading k n) e))) := by
  have h := isZero_rightDerived_pushforward_pullback_twistingSheaf k n q d e s hs h₁ h₂
  have h' := h.of_iso (Stacks.Cohomology.ClosedImmersion.cohomologyObjIsoPushforward
    (zeroScheme (Proj (polyGrading k n)) (twistingSheafModule (polyGrading k n) d)
      (s.eval (op ⊤))).subschemeι
    ((Scheme.Modules.pullback (zeroScheme (Proj (polyGrading k n))
          (twistingSheafModule (polyGrading k n) d) (s.eval (op ⊤))).subschemeι).obj
            (twistingSheafModule (polyGrading k n) e)) q).symm
  -- restriction of scalars does not change the carrier
  have hs := ModuleCat.subsingleton_of_isZero h'
  exact @ModuleCat.isZero_of_subsingleton _ _ _ hs

end Stacks.ProjectiveSpace.Cohomology

end
