module

public import StacksFrontier.AlgebraicGeometry.Crystalline.ChainEnvelope07Q9
public import StacksFrontier.AlgebraicGeometry.Crystalline.Cosimplicial.ColumnAcyclicity
public import StacksFrontier.AlgebraicGeometry.Crystalline.Cosimplicial.PairPullbackHom07Q9
public import StacksFrontier.AlgebraicGeometry.Crystalline.Cosimplicial.PairZigzagCone07Q9
public import StacksFrontier.AlgebraicGeometry.Crystalline.SmallSite.ChainOpenCech07Q9
public import StacksFrontier.AlgebraicGeometry.Crystalline.SmallSite.CrystalCosimplicialPair
public import StacksFrontier.AlgebraicGeometry.Crystalline.SmallSite.SourceSectionsMoore07Q9

/-!
# The Čech pullback of the unit over a chain open, from the de Rham side

Let `W ⊆ X` be an open over which `f` is a chain of `n` successive `α_p`-extensions, as in
[Stacks, Tag 07Q9]. The restriction of the crystal `ℱ` to `W` has the cosimplicial pair
`crystalCosimplicialPair` over the cosimplicial envelope `D(•)` of the canonical presentation of
`Γ(W)`, its base change along the morphism `D(•) ⟶ D'(•)` to the envelope of the chain
presentation of `Γ(f⁻¹(W))` is a cosimplicial pair over `D'(•)`, and `m ↦ 1 ⊗ m` is a morphism of
pairs. The Čech pullback of the unit `ℱ ⟶ f_{cris, *}f_cris^*ℱ` is, up to isomorphism of arrows,
the universe lift of the morphism of Moore complexes of this morphism of pairs, and through the
zigzag of [Stacks, Tag 07LG] its cone has the cohomology of the cone of the morphism of the rows
zero `M ⊗̂_D Ω^•_D ⟶ M' ⊗̂_{D'} Ω^•_{D'}`.

## Main definitions

* `chainPullbackHom07Q9` — the morphism of cosimplicial pairs over the chain open, from
  `chainTargetPair07Q9` to `chainSourcePair07Q9`.
* `sectionsMapArrowIso07Q9` — the Čech pullback of the unit as the universe lift of the Moore map
  of `chainPullbackHom07Q9`, as an isomorphism of arrows.

## Main results

* `smul_id_homology_sectionsMap_of_rowZero07Q9` — the cone of the Čech pullback from the cone of
  the morphism of the rows zero.

## References

* [Stacks Project, Lemma 60.26.3, Tag 07Q9](https://stacks.math.columbia.edu/tag/07Q9)
* [Stacks Project, Proposition 60.21.3, Tag 07LG](https://stacks.math.columbia.edu/tag/07LG)
-/

@[expose] public section

open CategoryTheory AlgebraicGeometry Opposite

universe u

noncomputable section

namespace Crystalline.GlobalCrystallineSituation.SmallSite

variable (S : GlobalCrystallineSituation.{u}) {V : S.S.scheme.Opens} {W : S.X.Opens}
  (hV : IsAffineOpen V) (hW : IsAffineOpen W) (hVW : W ≤ sourceToBase S ⁻¹ᵁ V)
  {X' : Scheme.{u}} (f : X' ⟶ S.X) (hW₂ : IsAffineOpen (f ⁻¹ᵁ W)) {p n : ℕ}
  (ch : AlphaPChain p Γ(S.X, W) n) (e : Γ(X', f ⁻¹ᵁ W) ≅ ch.top)
  (he : f.app W ≫ e.hom = ch.toTop)
  (F : SheafOfModules.{u} (structureSheaf S)) (hF : IsQuasiCoherentCrystal S F)
  [IsAffine (restrict S V W hVW).X] [IsAffine (restrict S V W hVW).S.scheme]

/-- **The morphism of cosimplicial pairs over a chain open**: the base change `m ↦ 1 ⊗ m` of the
cosimplicial pair of the restriction of `ℱ` to `W` along the morphism of cosimplicial envelopes
attached to the chain. -/
abbrev chainPullbackHom07Q9 :=
  (wholeSpaceCosimplicialModule (isNilpotent_prime_openSituation07Q9 S hW hVW)
    (restrictCrystal07Q9 S V W hVW F hF)).pairPullbackHom07Q9
    (chainEnvelopeHom07Q9 S hW hVW f hW₂ ch e)
    (crystalPairFormsConnection (isNilpotent_prime_openSituation07Q9 S hW hVW)
      (restrictCrystal07Q9 S V W hVW F hF))
    (crystalCoprojectionBeta (isNilpotent_prime_openSituation07Q9 S hW hVW)
      (restrictCrystal07Q9 S V W hVW F hF))
    (crystalCoprojectionBeta_of_tmul (isNilpotent_prime_openSituation07Q9 S hW hVW)
      (restrictCrystal07Q9 S V W hVW F hF))
    (crystalPairFormsConnection_horizontal_delta (isNilpotent_prime_openSituation07Q9 S hW hVW)
      (restrictCrystal07Q9 S V W hVW F hF))
    (hasIntegrableConnection_crystalPairFormsConnection
      (isNilpotent_prime_openSituation07Q9 S hW hVW) (restrictCrystal07Q9 S V W hVW F hF))

/-- The cosimplicial pair of the restriction of `ℱ` to `W`, over the envelope of the canonical
presentation of `Γ(W)`: the source of `chainPullbackHom07Q9`. -/
abbrev chainTargetPair07Q9 :=
  (wholeSpaceCosimplicialModule (isNilpotent_prime_openSituation07Q9 S hW hVW)
    (restrictCrystal07Q9 S V W hVW F hF)).baseChangePair
      (crystalPairFormsConnection (isNilpotent_prime_openSituation07Q9 S hW hVW)
        (restrictCrystal07Q9 S V W hVW F hF))
      (crystalCoprojectionBeta (isNilpotent_prime_openSituation07Q9 S hW hVW)
        (restrictCrystal07Q9 S V W hVW F hF))
      (crystalCoprojectionBeta_of_tmul (isNilpotent_prime_openSituation07Q9 S hW hVW)
        (restrictCrystal07Q9 S V W hVW F hF))
      (crystalPairFormsConnection_horizontal_delta (isNilpotent_prime_openSituation07Q9 S hW hVW)
        (restrictCrystal07Q9 S V W hVW F hF))
      (hasIntegrableConnection_crystalPairFormsConnection
        (isNilpotent_prime_openSituation07Q9 S hW hVW) (restrictCrystal07Q9 S V W hVW F hF))

/-- The base change of `chainTargetPair07Q9` to the envelope of the chain presentation of
`Γ(f⁻¹(W))`: the target of `chainPullbackHom07Q9`. -/
abbrev chainSourcePair07Q9 :=
  (wholeSpaceCosimplicialModule (isNilpotent_prime_openSituation07Q9 S hW hVW)
    (restrictCrystal07Q9 S V W hVW F hF)).pullbackPair07Q9
      (chainEnvelopeHom07Q9 S hW hVW f hW₂ ch e)
      (crystalPairFormsConnection (isNilpotent_prime_openSituation07Q9 S hW hVW)
        (restrictCrystal07Q9 S V W hVW F hF))
      (crystalCoprojectionBeta (isNilpotent_prime_openSituation07Q9 S hW hVW)
        (restrictCrystal07Q9 S V W hVW F hF))
      (crystalCoprojectionBeta_of_tmul (isNilpotent_prime_openSituation07Q9 S hW hVW)
        (restrictCrystal07Q9 S V W hVW F hF))
      (crystalPairFormsConnection_horizontal_delta (isNilpotent_prime_openSituation07Q9 S hW hVW)
        (restrictCrystal07Q9 S V W hVW F hF))
      (hasIntegrableConnection_crystalPairFormsConnection
        (isNilpotent_prime_openSituation07Q9 S hW hVW) (restrictCrystal07Q9 S V W hVW F hF))

/-- **The Čech pullback over a chain open is the universe lift of the Moore map of the morphism
of pairs**, as an isomorphism of arrows. -/
def sectionsMapArrowIso07Q9 :
    Arrow.mk ((chainCechSystemHom07Q9 S hV hW hVW f hW₂ ch e he).sectionsMap
        (crisModuleUnit (overSituation S f) S (𝟙 S.S) f (overSituation_compat S f)
          ((moduleULift S).obj F))) ≅
      Arrow.mk ((AddCommGrpCat.uliftFunctor.{u + 1, u}.mapHomologicalComplex _).map
        ((AlgebraicTopology.alternatingCofaceMapComplex AddCommGrpCat.{u}).map
          (chainPullbackHom07Q9 S hW hVW f hW₂ ch e F hF).carrierMap07Q9)) :=
  Arrow.isoMk (openSectionsMooreIso07Q9 S hV hW hVW F hF)
    (sourceSectionsMooreIso07Q9 S hV hW hVW f hW₂ (chainPresentation07Q9 S hW hVW f hW₂ ch e)
      (surjective_chainPresentation07Q9 S hW hVW f hW₂ ch e he)
      (chainPresentationRename07Q9 S hW hVW f hW₂) (chainPresentationRename07Q9_C S hW hVW f hW₂)
      (chainPresentation07Q9_comp_rename S hW hVW f hW₂ ch e) F hF
      (chainEnvelopeHom07Q9 S hW hVW f hW₂ ch e) (fun _ _ ↦ rfl))
    (sectionsMap_sourceSectionsMooreIso07Q9 S hV hW hVW f hW₂
      (chainPresentation07Q9 S hW hVW f hW₂ ch e)
      (surjective_chainPresentation07Q9 S hW hVW f hW₂ ch e he)
      (chainPresentationRename07Q9 S hW hVW f hW₂) (chainPresentationRename07Q9_C S hW hVW f hW₂)
      (chainPresentation07Q9_comp_rename S hW hVW f hW₂ ch e) F hF
      (chainEnvelopeHom07Q9 S hW hVW f hW₂ ch e) (fun _ _ ↦ rfl)).symm

/-- **The cone of the Čech pullback over a chain open from the cone of the rows zero.**  If the
coprojections of the rows of the two double complexes are quasi-isomorphisms and `q` kills the
cohomology of the cone of the morphism of the rows zero of `chainPullbackHom07Q9`, then `q` kills
the cohomology of the cone of the Čech pullback of the unit. -/
theorem smul_id_homology_sectionsMap_of_rowZero07Q9 (q : ℤ)
    (hrow : ∀ b : ℕ, QuasiIso ((chainTargetPair07Q9 S hW hVW F hF).rowFromZeroHom b))
    (hrow' : ∀ b : ℕ, QuasiIso ((chainSourcePair07Q9 S hW hVW f hW₂ ch e F hF).rowFromZeroHom b))
    (h : ∀ j : ℤ, q • 𝟙 ((CochainComplex.mappingCone (HomologicalComplex.extendMap
      ((chainPullbackHom07Q9 S hW hVW f hW₂ ch e F hF).degreeDeRhamMap 0)
      ComplexShape.embeddingUpNat)).homology j) = 0) (j : ℤ) :
    q • 𝟙 ((CochainComplex.mappingCone (HomologicalComplex.extendMap
      ((chainCechSystemHom07Q9 S hV hW hVW f hW₂ ch e he).sectionsMap
        (crisModuleUnit (overSituation S f) S (𝟙 S.S) f (overSituation_compat S f)
          ((moduleULift S).obj F))) ComplexShape.embeddingUpNat)).homology j) = 0 :=
  CosimplicialCompletedPair.Hom.smul_id_homology_of_arrowIso_ulift_carrierMooreMap_of_complete
    (chainPullbackHom07Q9 S hW hVW f hW₂ ch e F hF) q
    (fun b ↦ wholeSpaceCosimplicialModuleIsAdicComplete _ _ b)
    (fun b ↦ CosimplicialCompletedModule.pullback07Q9_isAdicComplete _ _ b)
    (isZero_homology_alternatingCofaceMapComplex_doubleComplex_X _ _
      (canonicalPresentation_surjective _) _) hrow
    (isZero_homology_alternatingCofaceMapComplex_doubleComplex_X _ _
      (surjective_chainPresentation07Q9 S hW hVW f hW₂ ch e he) _) hrow' _
    (sectionsMapArrowIso07Q9 S hV hW hVW f hW₂ ch e he F hF) h j

end Crystalline.GlobalCrystallineSituation.SmallSite
