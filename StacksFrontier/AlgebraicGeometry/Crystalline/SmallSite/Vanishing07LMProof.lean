module

public import StacksCore.Tactic.StacksAttribute
public import StacksFrontier.AlgebraicGeometry.Crystalline.SmallSite.RestrictCrystallineDifferentials
public import StacksFrontier.AlgebraicGeometry.Crystalline.SmallSite.RestrictQuasiCoherent
public import StacksFrontier.AlgebraicGeometry.Crystalline.SmallSite.Transport07LMReduction

/-!
# `Ru_{X/S, *}(F ⊗ Ω^i_{X/S}) = 0` for `i > 0`

Fix a global crystalline situation `(p, (S, I, γ), X)` of [Stacks, Tag 07MF].  This module proves
the vanishing

`Ru_{X/S, *}(F ⊗_{𝒪_{X/S}} Ω^i_{X/S}) = 0` for `i > 0`

in the generality [Stacks, Tag 07LN] gives it — for any sheaf of `𝒪_{X/S}`-modules `F` satisfying
conditions (1) and (2) of [Stacks, Proposition 60.19.1, Tag 07JN], namely local quasi-coherence
and local surjectivity of the comparison morphisms `c_f` along the morphisms of `Cris(X/S)` whose
map on ambient schemes is a closed immersion — and specialises it to a crystal in quasi-coherent
modules, which is the sharper, "in fact", clause of [Stacks, Proposition 60.23.1, Tag 07LM].

## The proof is the source's

Four steps, all of them now theorems of this library.

* **The local-to-global criterion.**
  `...SmallSite.isZero_derivedZariskiDirectImage_of_locallyIsZero` of
  `SmallSite/ZariskiDirectImageLocalVanishing.lean` is [Stacks, Tag 072W] for `u_{X/S}` as a
  vanishing criterion, and `...SmallSite.isCoveringFamily_isAffineOverAffine` of the same file says
  that the affine opens of `X` mapping into an affine open of `S` cover `X`.  Together, by
  `...SmallSite.vanishing07LM_of_isZero_rightDerived_zariskiDirectImageSections`, they reduce the
  vanishing to the per-open statement about the right derived functors of
  `ℋ ↦ Γ(V, u_{X/S, *}ℋ)`.
* **The identification of those functors with the cohomology of the restricted site.**
  `...SmallSite.isZero_rightDerived_zariskiDirectImageSections_of_isZero` of
  `SmallSite/RestrictedSiteSections.lean`, which is the clause
  `(Ru_{X/S, *}ℋ)|_{V_{Zar}} = Ru_{V/S|_W, *}(ℋ|)` of [Stacks, Tag 07KL] in the form the
  reduction consumes.
* **[Stacks, Tag 07LF] itself**, `...SmallSite.vanishing07LF` of
  `SmallSite/LevelFormsCosimplicialIso.lean`, whose affineness hypotheses the restricted situation
  `(p, S|_W, V)` satisfies for `V` and `W` affine.
* **The transport of the coefficients along the restriction.**
  `...SmallSite.Transport07LMForms` asks that the restriction to `Cris(V/S|_W)` of
  `F ⊗_{𝒪_{X/S}} Ω^i_{X/S}` be the corresponding sheaf of the restricted situation, for a sheaf of
  `𝒪_{V/S|_W}`-modules which again satisfies the two conditions.  By
  `...SmallSite.transport07LMForms_of_crysDifferentialsIso` this follows from two module-level
  statements, and both are now available:
  `...SmallSite.smallExtendCrysDifferentialsIso` of
  `SmallSite/RestrictCrystallineDifferentials.lean` — the crystalline differentials of the
  restricted situation are the restriction of `Ω_{X/S}`,
  because over an object of `Cris(V/S|_W)` both are the divided power differentials of
  `Γ(T, 𝒪_T)` modulo the differentials of the sections pulled back from the base, and an open
  immersion of divided power bases does not change those sections — and
  `...SmallSite.exists_smallExtendRestriction_of_vanishingHypotheses` of
  `SmallSite/RestrictQuasiCoherent.lean`, the transport of conditions (1) and (2) themselves.

## Main results

Everything lives in the namespace `Crystalline.GlobalCrystallineSituation.SmallSite`.

* `transport07LMForms` — the transport of the coefficients, from its two module-level inputs.
* `vanishing07LM` — `...SmallSite.Vanishing07LM`, the vanishing clause at the generality of
  [Stacks, Tag 07LN].
* `isZero_derivedZariskiDirectImage_of_vanishingHypotheses` — **[Stacks, Tag 07LN]**, the same
  statement written out.
* `isZero_derivedZariskiDirectImage_tensorDifferentialFormsSheaf` — the "in fact" clause of
  [Stacks, Tag 07LM]: the vanishing for a crystal in quasi-coherent modules.  The proposition, both
  clauses together, is `...SmallSite.stacks07LM` of `SmallSite/Proposition07LM.lean`.
* `vanishing07LMForms` — the vanishing clause read at `F = 𝒪_{X/S}`, which is what the derivation
  of the leading assertion of [Stacks, Tag 07LM] at `F = 𝒪_{X/S}` consumes.
* `isIso_derivedZariskiDirectImageFunctor_map_crysDeRhamPlusTruncation` — that derivation with its
  hypothesis discharged: at `F = 𝒪_{X/S}` the truncation map of the de Rham complex becomes an
  isomorphism of `D⁺(Ab(X_{Zar}))` after `Ru_{X/S, *}`.

## Implementation notes

The two `HasDerivedCategory` arguments are a choice of universe for the morphisms of the two
derived categories involved; they are what makes `Ru_{X/S, *}` expressible at all, and the library
supplies canonical instances in
`Crystalline.GlobalCrystallineSituation.SmallSite.hasDerivedCategorySheaf` and
`...hasDerivedCategoryZariskiSheaf`.

## References

* [Stacks Project, Tag 072W](https://stacks.math.columbia.edu/tag/072W)
* [Stacks Project, Tag 07JN](https://stacks.math.columbia.edu/tag/07JN)
* [Stacks Project, Tag 07KL](https://stacks.math.columbia.edu/tag/07KL)
* [Stacks Project, Tag 07LF](https://stacks.math.columbia.edu/tag/07LF)
* [Stacks Project, Tag 07LM](https://stacks.math.columbia.edu/tag/07LM)
* [Stacks Project, Tag 07LN](https://stacks.math.columbia.edu/tag/07LN)
* [Stacks Project, Tag 07MF](https://stacks.math.columbia.edu/tag/07MF)
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry Opposite

universe w w' u

noncomputable section

namespace Crystalline.GlobalCrystallineSituation.SmallSite

variable (S : GlobalCrystallineSituation.{u})
  [HasDerivedCategory.{w} (Sheaf (smallTopology S) AddCommGrpCat.{u + 1})]
  [HasDerivedCategory.{w'} (Sheaf (opensTopology S) AddCommGrpCat.{u + 1})]

omit [HasDerivedCategory.{w} (Sheaf (smallTopology S) AddCommGrpCat.{u + 1})]
  [HasDerivedCategory.{w'} (Sheaf (opensTopology S) AddCommGrpCat.{u + 1})] in
/-- **The transport of the coefficients of the vanishing clause of [Stacks, Tag 07LM] along
`smallExtend`.**  The restriction to `Cris(V/S|_W)` of `F ⊗_{𝒪_{X/S}} Ω^i_{X/S}` is the
corresponding sheaf of the restricted situation `(p, S|_W, V)`, for a sheaf of `𝒪_{V/S|_W}`-modules
which again satisfies conditions (1) and (2) of [Stacks, Tag 07JN].

Its two module-level inputs are `smallExtendCrysDifferentialsIso`, that the crystalline
differentials of the restricted situation are the restriction of `Ω_{X/S}`, and
`exists_smallExtendRestriction_of_vanishingHypotheses`, the transport of the two conditions. -/
theorem transport07LMForms : Transport07LMForms S :=
  transport07LMForms_of_crysDifferentialsIso S
    (fun W V hVW ↦ smallExtendCrysDifferentialsIso S W V hVW)
    (fun W V hVW F hqc hsurj ↦
      exists_smallExtendRestriction_of_vanishingHypotheses S W V hVW F hqc hsurj)

/-- **The vanishing clause of [Stacks, Tag 07LM], at the generality [Stacks, Tag 07LN] gives
it.**  For a sheaf of `𝒪_{X/S}`-modules satisfying conditions (1) and (2) of [Stacks, Tag 07JN]
and every `i > 0`, `Ru_{X/S, *}(F ⊗_{𝒪_{X/S}} Ω^i_{X/S}) = 0`. -/
theorem vanishing07LM : Vanishing07LM S :=
  vanishing07LM_of_transport07LMForms S (transport07LMForms S)

/-- **Stacks Project, Remark 60.23.2, Tag 07LN.**  For any sheaf of `𝒪_{X/S}`-modules `F` on the
small crystalline site satisfying conditions (1) and (2) of [Stacks, Proposition 60.19.1,
Tag 07JN] — `F` is locally quasi-coherent, and for every morphism of `Cris(X/S)` whose map on
ambient schemes is a closed immersion the comparison morphism `c_f : f^*F_{T'} ⟶ F_T` is
surjective — and for every `i > 0`,

`Ru_{X/S, *}(F ⊗_{𝒪_{X/S}} Ω^i_{X/S}) = 0`.

This is the conclusion the remark observes holds at that generality rather than only for a
crystal, the proof of [Stacks, Proposition 60.23.1, Tag 07LM] using nothing else about `F`.  It is
the source's own argument: the local-to-global criterion [Stacks, Tag 072W] for `u_{X/S}` reduces
it to an affine open `V` of `X` mapping into an affine open `W` of `S`, over such an open the
right derived functors of `ℋ ↦ Γ(V, u_{X/S, *}ℋ)` are the cohomology of `Cris(V/S|_W)` by
[Stacks, Tag 07KL], the coefficient sheaf transports to the restricted situation together with
conditions (1) and (2), and [Stacks, Tag 07LF] kills that cohomology in every degree. -/
@[stacks 07LN "the remark's conclusion itself: Ru_{X/S,*}(F ⊗ Ω^i_{X/S}) = 0 for every i > 0 and \
EVERY sheaf of O_{X/S}-modules F satisfying conditions (1) local quasi-coherence and (2) local \
surjectivity of the comparison map c_f along a closed immersion, of 07JN -- which is the \
generality the remark gives the vanishing clause of 07LM, weaker than being a crystal. The proof \
is the source's: 072W for u_{X/S} reduces to an affine open of X over an affine open of S, 07KL \
identifies the sections functors there with the cohomology of Cris(V/S|_W), the coefficients \
transport along that restriction together with the two conditions, and 07LF kills the cohomology"]
theorem isZero_derivedZariskiDirectImage_of_vanishingHypotheses
    (F : SheafOfModules.{u} (structureSheaf S)) (hqc : IsLocallyQuasiCoherent F)
    (hsurj : CohomologyRestriction.IsSurjectiveComparison F.val) (i : ℕ) (hi : 0 < i) :
    IsZero ((derivedZariskiDirectImage S).obj (tensorDifferentialFormsSheaf F i)) :=
  vanishing07LM S F hqc hsurj i hi

/-- **The vanishing clause of [Stacks, Proposition 60.23.1, Tag 07LM].**  For `F` a crystal in
quasi-coherent `𝒪_{X/S}`-modules on `Cris(X/S)` and every `i > 0`,

`Ru_{X/S, *}(F ⊗_{𝒪_{X/S}} Ω^i_{X/S}) = 0`.

This is the sharper of the proposition's two assertions — the source introduces it with "in fact"
— and it is what accounts for the other.  A crystal in quasi-coherent modules satisfies conditions
(1) and (2) of [Stacks, Tag 07JN] by [Stacks, Tag 07IT]
(`satisfiesVanishingHypotheses_of_isQuasicoherentOnSite`), so this is the specialisation of
`isZero_derivedZariskiDirectImage_of_vanishingHypotheses` to the sheaves the proposition speaks
about.  The proposition, with its leading assertion, is `...SmallSite.stacks07LM` of
`SmallSite/Proposition07LM.lean`. -/
theorem isZero_derivedZariskiDirectImage_tensorDifferentialFormsSheaf
    (F : SheafOfModules.{u} (structureSheaf S)) (hF : F.IsQuasicoherentOnSite) (i : ℕ)
    (hi : 0 < i) :
    IsZero ((derivedZariskiDirectImage S).obj (tensorDifferentialFormsSheaf F i)) :=
  isZero_derivedZariskiDirectImage_tensorDifferentialFormsSheaf_of_vanishing07LM S
    (vanishing07LM S) F hF i hi

/-- **The vanishing clause read at `F = 𝒪_{X/S}`**, where `F ⊗_{𝒪_{X/S}} Ω^i_{X/S} = Ω^i_{X/S}`.
This is the specialisation of `vanishing07LM` along `tensorDifferentialFormsSheafUnitIso`. -/
theorem vanishing07LMForms : Vanishing07LMForms S :=
  vanishing07LMForms_of_vanishing07LM S (vanishing07LM S)

/-- **The leading assertion of [Stacks, Tag 07LM] at `F = 𝒪_{X/S}`.**  The truncation map

`(𝒪_{X/S} → Ω¹_{X/S} → Ω²_{X/S} → ⋯) ⟶ 𝒪_{X/S}[0]`

becomes an isomorphism in `D⁺(Ab(X_{Zar}))` after `Ru_{X/S, *}`.  This is
`isIso_derivedZariskiDirectImageFunctor_map_crysDeRhamTruncation` with its hypothesis discharged
by `vanishing07LMForms`. -/
theorem isIso_derivedZariskiDirectImageFunctor_map_crysDeRhamPlusTruncation :
    IsIso ((derivedZariskiDirectImageFunctor S).map
      (DerivedCategory.Plus.Qh.map
        ((HomotopyCategory.Plus.quotient _).map (crysDeRhamPlusTruncation S)))) :=
  isIso_derivedZariskiDirectImageFunctor_map_crysDeRhamTruncation S (vanishing07LMForms S)

end Crystalline.GlobalCrystallineSituation.SmallSite

end

end
