module

public import StacksFrontier.AlgebraicGeometry.Artin.ContractionEqualizerRepresents
import Mathlib.CategoryTheory.Sites.Limits
import StacksFrontier.AlgebraicGeometry.FormalSpace.ClosedImmersion
import StacksFrontier.AlgebraicGeometry.Spaces.ClosedImmersionCriteria
import StacksFrontier.AlgebraicGeometry.Spaces.ClosedImmersionProper
import StacksFrontier.AlgebraicGeometry.Spaces.Equalizer
import StacksFrontier.AlgebraicGeometry.Spaces.Morphisms.Proper
import StacksFrontier.AlgebraicGeometry.Spaces.Morphisms.ProperCriteria
import StacksFrontier.AlgebraicGeometry.Spaces.ProperClosedImmersion
import StacksFrontier.AlgebraicGeometry.Spaces.SeparatedTfae

/-!
# The equalizer data of Stacks 0GHD under separatedness

In the situation of Stacks 0GH8, let `V` be a scheme over `S` and let `d` be the data of Stacks
0GHD over `V`: two elements of `F(V)` with chosen compatibility witnesses, the fibre product
`V' = V'₁ ×_V V'₂`, the equalizer `E' ⟶ V'` of the two morphisms `V' ⟶ X'`, the closed set
`Z = Z₁ ∩ Z₂` and the equalizer `E_W ⟶ V_{/Z}` of the two morphisms `V_{/Z} ⟶ W`
(`AlgebraicGeometry.Artin.ContractionEqualizer`).

The proof of Stacks 0GHF applies Stacks 0GHE to the triple of Stacks 0GHD (4) over `V`. This file
proves, over `S`, the three inputs that Stacks 0GHE needs and that come from the separatedness of
`X'` and `W` over `S`:

* `AlgebraicGeometry.Artin.ContractionEqualizer.isProper_toBase`: if `X' ⟶ S` is separated then
  `E' ⟶ V` is proper, the equalizer `E' ⟶ V'` being a base change of the diagonal of `X'`;
* `AlgebraicGeometry.Artin.ContractionEqualizer.isClosedImmersion_pullbackSnd_offCenter`: if
  `E' ⟶ V` is proper then `E' ×_V (V ∖ Z) ⟶ V ∖ Z` is a closed immersion, being proper and, by
  Stacks 0GHD (2), a monomorphism (Stacks 04XV in the form of
  `AlgebraicGeometry.Space.closedImmersion_conditions_tfae`);
* `AlgebraicGeometry.Artin.ContractionEqualizer.isClosedImmersion_ι_EW`: if `W ⟶ S` is separated
  then `E_W ⟶ V_{/Z}` is a closed immersion, being a base change of the diagonal of `W`.

## References

* [Stacks Project, Tag 04XV](https://stacks.math.columbia.edu/tag/04XV)
* [Stacks Project, Tag 0GHD](https://stacks.math.columbia.edu/tag/0GHD)
* [Stacks Project, Tag 0GHE](https://stacks.math.columbia.edu/tag/0GHE)
* [Stacks Project, Tag 0GHF](https://stacks.math.columbia.edu/tag/0GHF)
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits

universe u

namespace AlgebraicGeometry.Artin.ContractionEqualizer

open ContractionSituation

attribute [local instance] Space.pointTopology

variable {B : BigFppfSite.{u}} {S : Scheme.{u}} {hS : B.Contains S}
variable {c : ContractionSituation B S hS} {V : BigFppfOver B S hS}
    (d : ContractionEqualizer c V)

/-- If `X'` is separated over `S`, the equalizer `E' ⟶ V'` of the two morphisms `V' ⟶ X'` is a
closed immersion: it is a base change of the diagonal of `X'`. -/
theorem isClosedImmersion_equalizer_ι (hX' : Space.IsSeparated B S hS (terminal.from c.X')) :
    Space.IsClosedImmersion B S hS (equalizer.ι d.x₁ d.x₂) :=
  (Space.isClosedImmersion_isStableUnderBaseChange B S hS).of_isPullback
    (isPullback_equalizer_prod d.x₁ d.x₂).flip
    ((Space.isSeparatedOver_iff_isSeparated_of_isTerminal B S hS terminalIsTerminal _).2 hX')

/-- If `X'` is separated over `S`, the morphism `E' ⟶ V` of Stacks 0GHD is proper: it is the
composite of the closed immersion `E' ⟶ V'`, of the base change `V' ⟶ V'₁` of the proper
morphism `V'₂ ⟶ V`, and of the proper morphism `V'₁ ⟶ V`. -/
theorem isProper_toBase (hX' : Space.IsSeparated B S hS (terminal.from c.X')) :
    Space.IsProper B S hS d.toBase :=
  Space.isProper_comp B S hS d.isAlgebraicSpace_eqz d.isAlgebraicSpace_fibProd
    (isAlgebraicSpace_yoneda B S hS V) _ _
    (Space.isProper_of_isClosedImmersion B S hS d.isAlgebraicSpace_eqz d.isAlgebraicSpace_fibProd _
      (d.isClosedImmersion_equalizer_ι hX'))
    (Space.isProper_comp B S hS d.isAlgebraicSpace_fibProd d.w₁.isAlgebraicSpace_V'
      (isAlgebraicSpace_yoneda B S hS V) _ _
      (Space.isProper_pullback_fst B S hS d.w₂.isAlgebraicSpace_V'
        (isAlgebraicSpace_yoneda B S hS V)
        d.w₁.isAlgebraicSpace_V' d.w₂.p d.w₁.p d.w₂.isProper_p)
      d.w₁.isProper_p)

/-- The open subspace `V ∖ Z` of `V` is an algebraic space over `S`. -/
theorem isAlgebraicSpace_offCenter : IsAlgebraicSpace B S hS d.offCenter.toFunctor :=
  (Space.isOpenSubspace_openSubspaceOfPoints B S hS (isAlgebraicSpace_yoneda B S hS V) d.Zᶜ
    d.isClosed_Z.isOpen_compl).1

/-- The fibre product `E' ×_V (V ∖ Z)` is an algebraic space over `S`. -/
theorem isAlgebraicSpace_pullback_offCenter :
    IsAlgebraicSpace B S hS (pullback d.toBase d.offCenter.ι) :=
  isAlgebraicSpace_pullback B S hS _ _ d.isAlgebraicSpace_eqz d.isAlgebraicSpace_offCenter
    (isAlgebraicSpace_yoneda B S hS V)

/-- If `E' ⟶ V` is proper, so is its base change `E' ×_V (V ∖ Z) ⟶ V ∖ Z`. -/
theorem isProper_pullbackSnd_offCenter (hp : Space.IsProper B S hS d.toBase) :
    Space.IsProper B S hS (pullback.snd d.toBase d.offCenter.ι) := by
  have hsq : IsPullback
      (ObjectProperty.homMk (pullback.fst d.toBase d.offCenter.ι) :
        (⟨_, d.isAlgebraicSpace_pullback_offCenter⟩ : AlgebraicSpaces B S hS) ⟶
          ⟨d.eqz, d.isAlgebraicSpace_eqz⟩)
      (ObjectProperty.homMk (pullback.snd d.toBase d.offCenter.ι) :
        (⟨_, d.isAlgebraicSpace_pullback_offCenter⟩ : AlgebraicSpaces B S hS) ⟶
          ⟨_, d.isAlgebraicSpace_offCenter⟩)
      (ObjectProperty.homMk d.toBase :
        (⟨d.eqz, d.isAlgebraicSpace_eqz⟩ : AlgebraicSpaces B S hS) ⟶
          schemeSpace V)
      (ObjectProperty.homMk d.offCenter.ι :
        (⟨_, d.isAlgebraicSpace_offCenter⟩ : AlgebraicSpaces B S hS) ⟶
          schemeSpace V) :=
    IsPullback.of_map_of_faithful
      (ObjectProperty.ι (fun F : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u =>
        IsAlgebraicSpace B S hS F)) (IsPullback.of_hasPullback _ _)
  exact (Space.isProper_isStableUnderBaseChange B S hS).of_isPullback hsq hp

/-- If `E' ⟶ V` is proper, then `E' ×_V (V ∖ Z) ⟶ V ∖ Z` is a closed immersion: it is proper,
and a monomorphism by Stacks 0GHD (2), and a universally closed monomorphism locally of finite
type is a closed immersion. -/
theorem isClosedImmersion_pullbackSnd_offCenter (hp : Space.IsProper B S hS d.toBase) :
    Space.IsClosedImmersion B S hS (pullback.snd d.toBase d.offCenter.ι) := by
  have hp := d.isProper_pullbackSnd_offCenter hp
  have key := ((Space.closedImmersion_conditions_tfae B S hS d.isAlgebraicSpace_pullback_offCenter
    d.isAlgebraicSpace_offCenter (pullback.snd d.toBase d.offCenter.ι)).out 4 1).1
  exact key ⟨hp.2.2, hp.2.1.1, d.mono_pullbackSnd_offCenter⟩

/-- If `W` is separated over `S`, the equalizer `E_W ⟶ V_{/Z}` of the two morphisms
`V_{/Z} ⟶ W` is a closed immersion: it is a base change of the diagonal of `W`. -/
theorem isClosedImmersion_ι_EW (hW : FormalSpace.IsSeparatedMorphism B S hS (terminal.from c.W)) :
    FormalSpace.IsClosedImmersion B S hS (equalizer.ι d.xhat₁ d.xhat₂) := by
  have : HasLimitsOfSize.{u + 1, u + 1} (FormalSpace.FppfSheaf B S hS) := inferInstance
  have : HasLimitsOfShape WalkingCospan (FormalSpace.FppfSheaf B S hS) :=
    (hasFiniteLimits_of_hasLimitsOfSize.{u + 1, u + 1} (FormalSpace.FppfSheaf B S hS)).out _
  have : HasPullback (terminal.from c.W) (terminal.from c.W) :=
    HasLimitsOfShape.has_limit _
  have hd : diag c.W = pullback.diagonal (terminal.from c.W) ≫ (prodIsoPullback c.W c.W).inv := by
    refine prod.hom_ext ?_ ?_ <;> simp
  have hdiag : FormalSpace.IsClosedImmersion B S hS (diag c.W) := by
    rw [hd]
    exact FormalSpace.isClosedImmersion_comp B S hS _ _ hW
      (FormalSpace.isClosedImmersion_of_isIso B S hS _)
  exact FormalSpace.isClosedImmersion_of_isPullback B S hS
    (isPullback_equalizer_prod d.xhat₁ d.xhat₂).flip hdiag

end AlgebraicGeometry.Artin.ContractionEqualizer
