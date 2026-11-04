module

public import StacksFrontier.Algebra.Homology.DerivedCategory.ConeHomologyLadder
public import StacksFrontier.AlgebraicGeometry.Crystalline.SmallSite.CechPullbackOpen07Q9
public import StacksFrontier.AlgebraicGeometry.Crystalline.SmallSite.Comparison07Q9
public import StacksFrontier.AlgebraicGeometry.Crystalline.SmallSite.Resolution07Q9

/-!
# The local step of [Stacks, Tag 07Q9] reduced to Čech complexes

Over an open `W` of `X` covered by a Čech system `T'` of `Cris(X/S)`, and with a Čech system `T`
of `Cris(X'/S)` covering `f⁻¹W` together with a morphism of systems over `f`, the map
`Γ(Cris(W/S), J) ⟶ Γ(Cris(f⁻¹W/S), J')` of injective resolutions — the sections over `W` of
`u_{X/S, *}` of the lift `ψ : J ⟶ f_{cris, *}J'` of the unit `ℱ ⟶ f_{cris, *}ℱ'` — is
isomorphic, in the arrow category of `D(Ab)`, to the Čech pullback
`M_{T'}(ℱ) ⟶ M_T(ℱ')` of the complexes `M(0) → M(1) → ⋯` of [Stacks, Tag 07JN].  So the
annihilation of the cohomology of the cone of the first follows from that of the second.

The zigzag is: both maps go, by quasi-isomorphisms, to the map of total complexes of the Čech
double complexes of the two resolutions — the first by `cechAugmentationOpen` (the Čech complex of
an injective sheaf resolves its sections over `W`), the second by `cechComparison` (the
resolutions resolve the Čech complexes column by column, the sheaves being acyclic on the
affine objects of the systems).

## References

* [Stacks Project, Lemma 60.26.3, Tag 07Q9](https://stacks.math.columbia.edu/tag/07Q9)
* [Stacks Project, Proposition 60.20.1, Tag 07JN](https://stacks.math.columbia.edu/tag/07JN)
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry TopologicalSpace Opposite

universe u

noncomputable section

namespace Crystalline.GlobalCrystallineSituation.SmallSite

variable {S S' : GlobalCrystallineSituation.{u}} {fS : S.S ⟶ S'.S} {fX : S.X ⟶ S'.X}
  {hf : S.toClosedFiber ≫ DividedPowerScheme.closedFiberMap fS = fX ≫ S'.toClosedFiber}
  {T : SimplicialObject (ℕ ⥤ CrystallineThickening S)}
  {T' : SimplicialObject (ℕ ⥤ CrystallineThickening S')}

/-- **The local step of [Stacks, Tag 07Q9] from the Čech pullback.**  If the cone of the Čech
pullback `M_{T'}(ℱ) ⟶ M_T(ℱ')` along the unit `ℱ ⟶ f_{cris, *}ℱ'` has cohomology killed by `q`,
then so has the cone of the sections over `W` of the lift of the unit to injective
resolutions. -/
theorem chainConeAnnihilation_of_cechPullback (Φ : CechSystemHom fS fX hf T T')
    {W : S'.X.Opens} (hT'W : IsOpenProCovering S' W T')
    (hTW : IsOpenProCovering S (fX ⁻¹ᵁ W) T) (hT'a : HasAffineMonoLevels T')
    (hTa : HasAffineMonoLevels T) (F : ModuleSheaf S')
    (hG' : VanishingOnLevels07Q9 T' ((toAbelianSheaf S').obj F))
    (hGs' : HasSurjectiveLevelTransitions T' ((toAbelianSheaf S').obj F))
    (hG : VanishingOnLevels07Q9 T
      ((toAbelianSheaf S).obj ((crisModuleInverseImage fS fX hf).obj F)))
    (hGs : HasSurjectiveLevelTransitions T
      ((toAbelianSheaf S).obj ((crisModuleInverseImage fS fX hf).obj F)))
    (J : InjectiveResolution ((toAbelianSheaf S').obj F))
    (J' : InjectiveResolution ((toAbelianSheaf S).obj ((crisModuleInverseImage fS fX hf).obj F)))
    (q : ℕ)
    (h : ∀ j : ℤ, (q : ℤ) • 𝟙 ((CochainComplex.mappingCone (HomologicalComplex.extendMap
      (Φ.sectionsMap (crisModuleUnit S S' fS fX hf F)) ComplexShape.embeddingUpNat)).homology j)
        = 0) :
    ChainConeAnnihilation q (sectionsChainMap S' W (crisResolutionMap S S' fS fX hf F J J')) := by
  let ψ := crisResolutionMap S S' fS fX hf F J J'
  let Ψ := HomologicalComplex₂.total.map ((cechDoubleComplex T').map ψ ≫
    Φ.cechDoubleMap J'.cocomplex) (ComplexShape.up ℤ)
  have := Φ.quasiIso_cechAugmentationOpen_comp_cechDoubleMap hT'W hTW J'.cocomplex
  have wα : HomologicalComplex.extendMap (sectionsChainMap S' W ψ) ComplexShape.embeddingUpNat ≫
      (cechAugmentationOpen hT'W (((crisDirectImage S S' fS fX hf).mapHomologicalComplex
        _).obj J'.cocomplex) ≫ HomologicalComplex₂.total.map (Φ.cechDoubleMap J'.cocomplex)
          (ComplexShape.up ℤ)) =
      cechAugmentationOpen hT'W J.cocomplex ≫ Ψ := by
    simp only [Ψ, HomologicalComplex₂.total.map_comp]
    exact (Category.assoc _ _ _).symm.trans ((congrArg (· ≫ _)
      (cechAugmentationOpen_naturality hT'W ψ).symm).trans (Category.assoc _ _ _))
  let := HasDerivedCategory.standard AddCommGrpCat.{u + 1}
  exact fun j ↦ Stacks.ConeLadder.smul_id_homology_mappingCone_of_zigzag (q : ℤ) _ _ Ψ _ _ _ _
    wα (Φ.cechComparison_comp_cechDoubleMap hT'a hG' hGs' hTa hG hGs
      (crisModuleUnit S S' fS fX hf F) J J' ψ
      (ι_f_zero_comp_crisResolutionMap_f_zero S S' fS fX hf F J J')).symm h j

end Crystalline.GlobalCrystallineSituation.SmallSite

end

end
