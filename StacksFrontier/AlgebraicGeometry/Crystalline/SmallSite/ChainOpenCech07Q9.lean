module

public import StacksFrontier.AlgebraicGeometry.Crystalline.SmallSite.AlphaPCoverBasis07Q9
public import StacksFrontier.AlgebraicGeometry.Crystalline.SmallSite.CrisInverseImageLevels07Q9
public import StacksFrontier.AlgebraicGeometry.Crystalline.SmallSite.OpenCechPackage07Q9
public import StacksFrontier.AlgebraicGeometry.Crystalline.SmallSite.PerOpenCech07Q9

/-!
# The local step of [Stacks, Tag 07Q9] over a chain open, from the Čech pullback

Over an open `W ⊆ X` over which `f` is a chain of `α_p`-extensions, the Čech system of `W` for the
canonical presentation of `Γ(W)` and that of `f⁻¹(W)` for the presentation attached to the chain
are related by the morphism `chainCechSystemHom07Q9` over `f`.  This file feeds them to
`chainConeAnnihilation_of_cechPullback`: the cone of the sections over `W` of the lift of the unit
to injective resolutions has cohomology killed by `q` as soon as the cone of the Čech pullback
`M_{T'}(ℱ) ⟶ M_T(f_cris^*ℱ)` has.  The goodness of `ℱ` on the system of `W` is
[Stacks, Tag 07JJ] and the surjectivity of its level transitions; that of `f_cris^*ℱ` on the
system of `f⁻¹(W)` is `vanishingOnLevels07Q9_chainCechSystem` and
`hasSurjectiveLevelTransitions_chainCechSystem07Q9`.

## References

* [Stacks Project, Lemma 60.26.3, Tag 07Q9](https://stacks.math.columbia.edu/tag/07Q9)
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

/-- **The local step over a chain open.**  For a crystal in quasi-coherent modules `ℱ` on
`Cris(X/S)`, if the cone of the Čech pullback along the unit `ℱ ⟶ f_{cris, *}f_cris^*ℱ` has
cohomology killed by `q`, then so has the cone of the sections over `W` of the lift of the unit to
injective resolutions. -/
theorem chainConeAnnihilation_of_chainOpen07Q9 (F : SheafOfModules.{u} (structureSheaf S))
    (hF : IsQuasiCoherentCrystal S F)
    (q : ℕ)
    (h : ∀ j : ℤ, (q : ℤ) • 𝟙 ((CochainComplex.mappingCone (HomologicalComplex.extendMap
      ((chainCechSystemHom07Q9 S hV hW hVW f hW₂ ch e he).sectionsMap
        (crisModuleUnit (overSituation S f) S (𝟙 S.S) f (overSituation_compat S f)
          ((moduleULift S).obj F))) ComplexShape.embeddingUpNat)).homology j) = 0) :
    ChainConeAnnihilation q (sectionsChainMap S W
      (crisResolutionMap (overSituation S f) S (𝟙 S.S) f (overSituation_compat S f)
        ((moduleULift S).obj F) (injectiveResolution _) (injectiveResolution _))) :=
  chainConeAnnihilation_of_cechPullback (chainCechSystemHom07Q9 S hV hW hVW f hW₂ ch e he)
    (isOpenProCovering_openSystem07Q9 S hV hW hVW _ _)
    (isOpenProCovering_openSystem07Q9 (overSituation S f) hV hW₂
      (preimage_le_overSituation07Q9 S hVW f) _ _)
    (hasAffineMonoLevels_openSystem07Q9 S hV hW hVW _ _)
    (hasAffineMonoLevels_openSystem07Q9 (overSituation S f) hV hW₂
      (preimage_le_overSituation07Q9 S hVW f) _ _)
    ((moduleULift S).obj F)
    (vanishingOnLevels07Q9_of_vanishing07JJ (hasAffineMonoLevels_openSystem07Q9 S hV hW hVW _ _)
      (abelianSheaf_vanishing07JJ_of_isQuasiCoherentCrystal F hF))
    (hasSurjectiveLevelTransitions_openSystem07Q9 S hV hW hVW _ _ F hF)
    (vanishingOnLevels07Q9_chainCechSystem S hV hW hVW f hW₂ ch e he F hF)
    (hasSurjectiveLevelTransitions_chainCechSystem07Q9 S hV hW hVW f hW₂ ch e he F hF)
    (injectiveResolution _) (injectiveResolution _) q h

end Crystalline.GlobalCrystallineSituation.SmallSite
