module

public import StacksFrontier.AlgebraicGeometry.Crystalline.SmallSite.LevelLimitNaturality
public import StacksFrontier.AlgebraicGeometry.Crystalline.SmallSite.LevelRestrictionSurjectivity

/-!
# The complex `M(0) → M(1) → M(2) → ⋯` of [Stacks, Tag 07JN], under the source's own hypotheses

Work in a global crystalline situation `(p, (S, I, γ), X)` with `X` and `S` affine and `p`
nilpotent on `Γ(X, ⊤)`, and let `F` be a sheaf of `𝒪_{X/S}`-modules on the small crystalline site
`Cris(X/S)` satisfying the two hypotheses of [Stacks, Tag 07JN]:

1. `F` is locally quasi-coherent
   (`Crystalline.GlobalCrystallineSituation.SmallSite.IsLocallyQuasiCoherent`);
2. for every morphism of `Cris(X/S)` whose map on ambient schemes is a closed immersion the
   comparison morphism `c_f : f^* F_{T'} ⟶ F_T` is locally surjective
   (`...SmallSite.CohomologyRestriction.IsSurjectiveComparison`).

Then the complex `M(0) → M(1) → M(2) → ⋯` of the system `(X, T(n)_e, δ(n))` computes
`RΓ(Cris(X/S), F)` degreewise, in the sense of `...SmallSite.ComputesCohomology`, through an
explicit comparison map which is an isomorphism in every degree. The same holds for an abelian
coefficient sheaf satisfying `...SmallSite.Vanishing07JJ` and
`...SmallSite.HasSurjectiveWholeSpaceTransitions`, the abelian forms of (1) and (2).

## Main definitions

* `...SmallSite.computesCohomologyMapsWholeSpaceSystemOfAbelian` — the comparison map of
  [Stacks, Tag 07JN] for an abelian coefficient sheaf.
* `...SmallSite.computesCohomologyMapsWholeSpaceSystemOfIsSurjectiveComparison` — the comparison
  map `H ʲ(M(•)) ⟶ H ʲ(Cris(X/S), F)` of [Stacks, Tag 07JN] under hypotheses (1) and (2).

## Main results

* `...SmallSite.surjective_affineSections_uniformLevelSystem_transition` — for every completed
  thickening `B` and every `e`, the restriction of the affine-side sections of `F` along the
  uniform level drop `B/(p)^{N + e + 1} ↠ B/(p)^{N + e}` is surjective, under hypotheses (1) and
  (2).
* `...SmallSite.computesCohomology_wholeSpaceSystem_of_abelian` — the conclusion of
  [Stacks, Tag 07JN] for an abelian coefficient sheaf satisfying `...SmallSite.Vanishing07JJ` and
  `...SmallSite.HasSurjectiveWholeSpaceTransitions`.
* `...SmallSite.isIso_computesCohomologyMapsWholeSpaceSystemOfIsSurjectiveComparison` — the
  comparison map of [Stacks, Tag 07JN] is an isomorphism in every degree.
* `...SmallSite.computesCohomology_wholeSpaceSystem_of_isSurjectiveComparison` — the degreewise
  form of [Stacks, Tag 07JN]: the conclusion of the proposition for the system
  `(X, T(n)_e, δ(n))`, under hypotheses (1) and (2).
* `...SmallSite.computesCohomology_wholeSpaceSystem_tensorDifferentialFormsSheaf` — the same
  conclusion at the coefficient sheaf `F ⊗_{𝒪_{X/S}} Ω^i_{X/S}` of [Stacks, Tag 07LF], under the
  abelian forms of the two hypotheses for that sheaf.

## References

* [Stacks Project, Tag 07JN](https://stacks.math.columbia.edu/tag/07JN)
* [Stacks Project, Tag 07LF](https://stacks.math.columbia.edu/tag/07LF)
* [Stacks Project, Tag 07JJ](https://stacks.math.columbia.edu/tag/07JJ)
* [Stacks Project, Tag 07JM](https://stacks.math.columbia.edu/tag/07JM)
* [Stacks Project, Tag 07L4](https://stacks.math.columbia.edu/tag/07L4)
* [Stacks Project, Tag 07KI](https://stacks.math.columbia.edu/tag/07KI)
* [Stacks Project, Tag 07KG](https://stacks.math.columbia.edu/tag/07KG)
* [Stacks Project, Tag 07HN](https://stacks.math.columbia.edu/tag/07HN)
* [Stacks Project, Tag 07H8](https://stacks.math.columbia.edu/tag/07H8)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits Opposite AlgebraicGeometry

namespace Crystalline.GlobalCrystallineSituation.SmallSite

open Crystalline

universe u

variable {S : GlobalCrystallineSituation.{u}} [IsAffine S.X] [IsAffine S.S.scheme]
  (hp : IsNilpotent (S.p : Γ(S.X, ⊤))) [WholeSpacePresentation S hp]

omit [WholeSpacePresentation S hp] in
/-- **The level restrictions of the uniform-cutoff system of every completed thickening are
surjective** for an abelian sheaf `G` satisfying `...SmallSite.HasSurjectiveWholeSpaceTransitions`:
for every object `B` of `Cris^∧(C/A)` and every `e`, the restriction map of the affine-side
sections of `G` along the level drop `B/(p)^{N + e + 1} ↠ B/(p)^{N + e}` is surjective, `N` being
the uniform cutoff `Crystalline.uniformLevel`. -/
theorem surjective_affineSections_uniformLevelSystem_transition_of_abelian
    (G : Sheaf (smallTopology S) AddCommGrpCat.{u + 1})
    (hG : HasSurjectiveWholeSpaceTransitions G)
    (B : CompletedCrystallineThickening.{u, u, u} (affineSituation S hp)) (e : ℕ) :
    Function.Surjective (ConcreteCategory.hom
      ((affineSections S hp G.obj).map
        ((uniformLevelSystem B).transition (Nat.le_succ e)))) :=
  surjective_affineSections_finiteLevelSystem_transition_of_abelian hp G hG (uniformLevelSystem B)
    (Nat.le_succ e)

omit [WholeSpacePresentation S hp] in
/-- **The level restrictions of the uniform-cutoff system of every completed thickening are
surjective** for a sheaf of `𝒪_{X/S}`-modules `F` which is locally quasi-coherent and whose
comparison maps `c_f` along closed immersions are locally surjective: for every object `B` of
`Cris^∧(C/A)` and every `e`, the restriction map of the affine-side sections of `F` along the
level drop `B/(p)^{N + e + 1} ↠ B/(p)^{N + e}` is surjective. -/
theorem surjective_affineSections_uniformLevelSystem_transition
    (F : SheafOfModules.{u} (structureSheaf S)) (hF : IsLocallyQuasiCoherent F)
    (hM : CohomologyRestriction.IsSurjectiveComparison F.val)
    (B : CompletedCrystallineThickening.{u, u, u} (affineSituation S hp)) (e : ℕ) :
    Function.Surjective (ConcreteCategory.hom
      ((affineSections S hp (abelianSheaf F).obj).map
        ((uniformLevelSystem B).transition (Nat.le_succ e)))) :=
  surjective_affineSections_finiteLevelSystem_transition hp F hF hM (uniformLevelSystem B)
    (Nat.le_succ e)

/-- **The conclusion of [Stacks, Tag 07JN] for the system `(X, T(n)_e, δ(n))` and an abelian
coefficient sheaf satisfying the abelian forms of the tag's two hypotheses.** For an abelian sheaf
`G` on `Cris(X/S)` over an affine situation which satisfies

1. `...SmallSite.Vanishing07JJ`, the conclusion of [Stacks, Tag 07JJ] — the vanishing of
   `H^p(Cris(X/S)/(U, T, δ), G)` for `p > 0` over every object with affine ambient scheme; and
2. `...SmallSite.HasSurjectiveWholeSpaceTransitions` — the surjectivity of the transition maps of
   `G` along closed immersions between objects over the whole of `X`,

the complex `M(0) → M(1) → M(2) → ⋯` computes `RΓ(Cris(X/S), G)` in the graded sense of
`Crystalline.GlobalCrystallineSituation.SmallSite.ComputesCohomology`. -/
theorem computesCohomology_wholeSpaceSystem_of_abelian
    (G : Sheaf (smallTopology S) AddCommGrpCat.{u + 1}) (hvan : Vanishing07JJ S G)
    (hsurj : HasSurjectiveWholeSpaceTransitions G) :
    ComputesCohomology (wholeSpaceSystem S hp) G :=
  computesCohomology_wholeSpaceSystem_of_abelianSurjective hp G hvan
    (surjective_affineSections_uniformLevelSystem_transition_of_abelian hp G hsurj)

/-- **The comparison map of [Stacks, Tag 07JN] for an abelian coefficient sheaf**: in degree
`j`, the map from the `j`-th cohomology of the complex `M(0) → M(1) → ⋯` of sections of `G` to
`H ʲ(Cris(X/S), G)`. -/
noncomputable def computesCohomologyMapsWholeSpaceSystemOfAbelian
    (G : Sheaf (smallTopology S) AddCommGrpCat.{u + 1}) (hvan : Vanishing07JJ S G)
    (hsurj : HasSurjectiveWholeSpaceTransitions G) (j : ℕ) :
    (sectionsComplex (wholeSpaceSystem S hp) G.obj).homology j ⟶
      (cohomologyFunctor S j).obj G :=
  computesCohomologyMapsWholeSpaceSystemOfAbelianSurjective hp G hvan
    (surjective_affineSections_uniformLevelSystem_transition_of_abelian hp G hsurj) j

/-- **The comparison map `computesCohomologyMapsWholeSpaceSystemOfAbelian` is an isomorphism in
every degree.** -/
theorem isIso_computesCohomologyMapsWholeSpaceSystemOfAbelian
    (G : Sheaf (smallTopology S) AddCommGrpCat.{u + 1}) (hvan : Vanishing07JJ S G)
    (hsurj : HasSurjectiveWholeSpaceTransitions G) (j : ℕ) :
    IsIso (computesCohomologyMapsWholeSpaceSystemOfAbelian hp G hvan hsurj j) :=
  isIso_computesCohomologyMapsWholeSpaceSystemOfAbelianSurjective hp G hvan
    (surjective_affineSections_uniformLevelSystem_transition_of_abelian hp G hsurj) j

/-- **The comparison map of [Stacks, Tag 07JN]**: for a sheaf of `𝒪_{X/S}`-modules `F` on
`Cris(X/S)` over an affine situation which is locally quasi-coherent and whose comparison maps
`c_f` along closed immersions are locally surjective, the map

`H ʲ(M(0) → M(1) → ⋯) ⟶ H ʲ(Cris(X/S), F)`

of the tag's conclusion. -/
noncomputable def computesCohomologyMapsWholeSpaceSystemOfIsSurjectiveComparison
    (F : SheafOfModules.{u} (structureSheaf S)) (hF : IsLocallyQuasiCoherent F)
    (hM : CohomologyRestriction.IsSurjectiveComparison F.val) (j : ℕ) :
    (sectionsComplex (wholeSpaceSystem S hp) (abelianSheaf F).obj).homology j ⟶
      (cohomologyFunctor S j).obj (abelianSheaf F) :=
  computesCohomologyMapsWholeSpaceSystemOfAbelian hp (abelianSheaf F)
    (vanishing07JJ_abelianSheaf F hF) (hasSurjectiveWholeSpaceTransitions_abelianSheaf F hF hM) j

/-- **The comparison map of [Stacks, Tag 07JN] is an isomorphism in every degree.** -/
theorem isIso_computesCohomologyMapsWholeSpaceSystemOfIsSurjectiveComparison
    (F : SheafOfModules.{u} (structureSheaf S)) (hF : IsLocallyQuasiCoherent F)
    (hM : CohomologyRestriction.IsSurjectiveComparison F.val) (j : ℕ) :
    IsIso (computesCohomologyMapsWholeSpaceSystemOfIsSurjectiveComparison hp F hF hM j) :=
  isIso_computesCohomologyMapsWholeSpaceSystemOfAbelian hp (abelianSheaf F)
    (vanishing07JJ_abelianSheaf F hF) (hasSurjectiveWholeSpaceTransitions_abelianSheaf F hF hM) j

/-- **The conclusion of [Stacks, Tag 07JN], degreewise, for the system `(X, T(n)_e, δ(n))`.**
For a sheaf of `𝒪_{X/S}`-modules `F` on `Cris(X/S)` over an affine situation which is

1. locally quasi-coherent, and
2. such that the comparison morphisms `c_f` along closed immersions are locally surjective,

the complex `M(0) → M(1) → M(2) → ⋯` computes `RΓ(Cris(X/S), F)` in the graded sense of
`Crystalline.GlobalCrystallineSituation.SmallSite.ComputesCohomology`. -/
theorem computesCohomology_wholeSpaceSystem_of_isSurjectiveComparison
    (F : SheafOfModules.{u} (structureSheaf S)) (hF : IsLocallyQuasiCoherent F)
    (hM : CohomologyRestriction.IsSurjectiveComparison F.val) :
    ComputesCohomology (wholeSpaceSystem S hp) (abelianSheaf F) := fun j =>
  have := isIso_computesCohomologyMapsWholeSpaceSystemOfIsSurjectiveComparison hp F hF hM j
  ⟨asIso (computesCohomologyMapsWholeSpaceSystemOfIsSurjectiveComparison hp F hF hM j)⟩

/-! ### The coefficient sheaf of Stacks 07LF -/

/-- **The conclusion of [Stacks, Tag 07JN] for the coefficient sheaf `F ⊗_{𝒪_{X/S}} Ω^i_{X/S}` of
[Stacks, Tag 07LF]**, under the abelian forms of the tag's two hypotheses for that sheaf: the
complex `M(0) → M(1) → M(2) → ⋯` built from `...SmallSite.tensorDifferentialFormsSheaf F i`
computes `RΓ(Cris(X/S), F ⊗_{𝒪_{X/S}} Ω^i_{X/S})`. -/
theorem computesCohomology_wholeSpaceSystem_tensorDifferentialFormsSheaf
    (F : SheafOfModules.{u} (structureSheaf S)) (i : ℕ)
    (hvan : Vanishing07JJ S (tensorDifferentialFormsSheaf F i))
    (hsurj : HasSurjectiveWholeSpaceTransitions (tensorDifferentialFormsSheaf F i)) :
    ComputesCohomology (wholeSpaceSystem S hp) (tensorDifferentialFormsSheaf F i) :=
  computesCohomology_wholeSpaceSystem_of_abelian hp (tensorDifferentialFormsSheaf F i) hvan hsurj

end Crystalline.GlobalCrystallineSituation.SmallSite

end
