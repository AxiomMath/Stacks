module

public import StacksFrontier.AlgebraicGeometry.Crystalline.BigSite.BinaryProductPatch
public import StacksFrontier.AlgebraicGeometry.Crystalline.SmallSite.StandardCoverAcyclicity
public import StacksFrontier.AlgebraicGeometry.Crystalline.SmallSite.WholeSpaceSystemCohomology

/-!
# Vanishing of crystalline cohomology of `F ⊗ Ω^i` from three inputs

Fix a global crystalline situation `(p, (S, I, γ), X)` with `X` and `S` affine and let `F` be a
sheaf of `𝒪_{X/S}`-modules on the small crystalline site `Cris(X/S)`. This file shows that
`H^j(Cris(X/S), F ⊗_{𝒪_{X/S}} Ω^i_{X/S}) = 0` as soon as the tensor sheaf satisfies the abelian
forms of the two hypotheses of [Stacks, Tag 07JN] and the complex `M(0) → M(1) → M(2) → ⋯` built
from it is acyclic, and it reduces the Čech condition `HasStandardCechVanishing` of an abelian
sheaf to the vanishing of Zariski Čech cohomology on the ambient schemes of the objects.

## Main results

* `hasStandardCechVanishing_of_isZero_ambientCechHomology`: an abelian sheaf `G` on `Cris(X/S)`
  satisfies `HasStandardCechVanishing` if, for every object `A` with affine ambient scheme `T`,
  the positive-degree homology of the Zariski Čech complex of `W ↦ Γ(A|_W, G)` vanishes on the
  covers of `T` by the basic opens of a standard open cover of its spectrum.
* `subsingleton_cohomology_tensorDifferentialFormsSheaf_of_isZero_homology`:
  `H^j(Cris(X/S), F ⊗_{𝒪_{X/S}} Ω^i_{X/S}) = 0` given the abelian forms of the two hypotheses of
  [Stacks, Tag 07JN] for the tensor sheaf and the vanishing in degree `j` of the homology of the
  complex `M(0) → M(1) → M(2) → ⋯` built from it.
* `vanishing07LF_of_isZero_homology_sectionsComplex`: the proposition `Vanishing07LF` follows from
  these three inputs, each quantified over the sheaves `F` satisfying the two hypotheses of
  [Stacks, Tag 07JN] and over `i > 0`.

## References

* [Stacks Project, Tag 07LF](https://stacks.math.columbia.edu/tag/07LF)
* [Stacks Project, Tag 07JN](https://stacks.math.columbia.edu/tag/07JN)
* [Stacks Project, Tag 07JJ](https://stacks.math.columbia.edu/tag/07JJ)
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry Opposite
open scoped AlgebraicGeometry

universe u

noncomputable section

namespace Crystalline.GlobalCrystallineSituation.SmallSite

variable {S : GlobalCrystallineSituation.{u}}

/-! ### Hypothesis (1) for an arbitrary abelian sheaf, reduced to the ambient scheme -/

/-- An abelian sheaf `G` on `Cris(X/S)` satisfies `HasStandardCechVanishing` if, for every object
`A` whose ambient divided power scheme `T` is affine and every finite family `g` of global sections
of `T` whose basic opens form a standard open cover of `Spec Γ(T, 𝒪_T)`, the positive-degree
homology of the Zariski Čech complex of the presheaf `W ↦ Γ(A|_W, G)` on the cover of `T` by those
basic opens vanishes. -/
theorem hasStandardCechVanishing_of_isZero_ambientCechHomology
    (G : Sheaf (smallTopology S) AddCommGrpCat.{u + 1})
    (h : ∀ (A : CrystallineThickening S), IsAffine A.obj.thickening.target.scheme →
      ∀ {n : ℕ} (g : Fin n → Γ(A.obj.thickening.target.scheme, ⊤)),
        PrimeSpectrum.IsStandardOpenCoverOfSpectrum g → ∀ p : ℕ, 0 < p →
          IsZero (((cechComplexFunctor
              fun i ↦ A.obj.thickening.target.scheme.basicOpen (g i)).obj
            ((CrystallineThickening.restrictOpenFunctor A).op ⋙ G.obj)).homology p)) :
    HasStandardCechVanishing G := by
  intro A E hE p hp
  obtain ⟨E, hEcov⟩ := E
  obtain ⟨hA, n, g, hg, hEeq⟩ := hE
  have : IsAffine A.obj.thickening.target.scheme := hA
  change E = _ at hEeq
  subst hEeq
  refine CrystallineThickening.isZero_cechCohomology_restrictOpenHypercover A _ G.obj p ?_
  refine Stacks.CategoryTheory.CechComplex.isZero_homology_of_ulift
    (fun j : Fin n ↦ A.obj.thickening.target.scheme.basicOpen (g j))
    ((CrystallineThickening.restrictOpenFunctor A).op ⋙ G.obj) p ?_
  exact h A hA g hg p hp

/-! ### Vanishing of the cohomology of the tensor sheaf -/

section Affine

variable [IsAffine S.X] [IsAffine S.S.scheme]

/-- For a global crystalline situation with `X` and `S` affine, a sheaf of `𝒪_{X/S}`-modules `F`,
and `i`, `j` in `ℕ`, the cohomology group `H^j(Cris(X/S), F ⊗_{𝒪_{X/S}} Ω^i_{X/S})` vanishes if
the tensor sheaf satisfies the conclusion of [Stacks, Tag 07JJ] (`hvan`), its transition maps
along closed immersions between objects over the whole of `X` are surjective (`hsurj`), and the
complex `M(0) → M(1) → M(2) → ⋯` built from it has vanishing homology in degree `j` (`hacyc`). -/
theorem subsingleton_cohomology_tensorDifferentialFormsSheaf_of_isZero_homology
    (F : SheafOfModules.{u} (structureSheaf S)) (i j : ℕ)
    (hvan : Vanishing07JJ S (tensorDifferentialFormsSheaf F i))
    (hsurj : HasSurjectiveWholeSpaceTransitions (tensorDifferentialFormsSheaf F i))
    (hacyc : IsZero ((sectionsComplex
        (wholeSpaceSystem S (isNilpotent_prime_sections_of_isAffine S))
        (tensorDifferentialFormsSheaf F i).obj).homology j)) :
    Subsingleton (cohomology S (tensorDifferentialFormsSheaf F i) j) := by
  obtain ⟨e⟩ := computesCohomology_wholeSpaceSystem_tensorDifferentialFormsSheaf
    (isNilpotent_prime_sections_of_isAffine S) F i hvan hsurj j
  exact AddCommGrpCat.subsingleton_of_isZero (hacyc.of_iso e.symm)

/-- The proposition `Vanishing07LF` holds given three inputs, each quantified over a sheaf of
`𝒪_{X/S}`-modules `F` satisfying the two hypotheses of [Stacks, Tag 07JN] and over `i > 0`: the
conclusion of [Stacks, Tag 07JJ] for the tensor sheaf, the surjectivity of its transition maps
over the whole of `X`, and the acyclicity of the complex `M(0) → M(1) → M(2) → ⋯` built from it. -/
theorem vanishing07LF_of_isZero_homology_sectionsComplex
    (hvan : ∀ F : SheafOfModules.{u} (structureSheaf S), IsLocallyQuasiCoherent F →
      CohomologyRestriction.IsSurjectiveComparison F.val → ∀ i : ℕ, 0 < i →
        Vanishing07JJ S (tensorDifferentialFormsSheaf F i))
    (hsurj : ∀ F : SheafOfModules.{u} (structureSheaf S), IsLocallyQuasiCoherent F →
      CohomologyRestriction.IsSurjectiveComparison F.val → ∀ i : ℕ, 0 < i →
        HasSurjectiveWholeSpaceTransitions (tensorDifferentialFormsSheaf F i))
    (hacyc : ∀ F : SheafOfModules.{u} (structureSheaf S), IsLocallyQuasiCoherent F →
      CohomologyRestriction.IsSurjectiveComparison F.val → ∀ i : ℕ, 0 < i → ∀ j : ℕ,
        IsZero ((sectionsComplex
          (wholeSpaceSystem S (isNilpotent_prime_sections_of_isAffine S))
          (tensorDifferentialFormsSheaf F i).obj).homology j)) :
    Vanishing07LF S := fun _ _ F hF hM i j hi ↦
  subsingleton_cohomology_tensorDifferentialFormsSheaf_of_isZero_homology F i j
    (hvan F hF hM i hi) (hsurj F hF hM i hi) (hacyc F hF hM i hi j)

end Affine

end Crystalline.GlobalCrystallineSituation.SmallSite

end

end
