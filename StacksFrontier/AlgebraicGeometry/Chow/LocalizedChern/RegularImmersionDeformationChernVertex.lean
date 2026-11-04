module

public import StacksFrontier.AlgebraicGeometry.Chow.InfinityCentreExceptionalCompletionCone
public import StacksFrontier.AlgebraicGeometry.Chow.LocalizedChern.RegularImmersionDeformationChern
public import StacksFrontier.AlgebraicGeometry.Chow.LocalizedChern.RegularImmersionDeformationChernTorIndependent
public import StacksFrontier.AlgebraicGeometry.DerivedQCoh.StructureSheafAsADerivedUnit
public import StacksFrontier.AlgebraicGeometry.PseudoCoherent.RelativeTorIndependentBaseChange
public import StacksFrontier.AlgebraicGeometry.PseudoCoherent.ThickeningQuasicoherent

/-!
# `Q|_E` is the structure sheaf of the vertex

Let `i : Z ⟶ X` be a closed immersion, `W` the blowup of `𝐏¹_X` in `∞(Z)` read as a modification
of `X ×_S 𝐏¹_S`, `W_∞` its fibre at infinity, `E = W_∞ ×_X Z` and `e : E ⟶ W_∞ ⟶ W`, and let
`i' : 𝐏¹_Z ⟶ W` be the closed immersion of Stacks 0FE9 and `Q = i'_*𝒪_{𝐏¹_Z}[0]`. In the proof of
Stacks 0FEG the restriction `Q|_E = Le^*Q` is computed: the base change of `i'` along `e` is the
vertex `Z ⟶ C_ZX ⟶ E` of the normal cone (Stacks 0FE9), and the square is Tor independent,
`E ⊆ W` being an effective Cartier divisor which pulls back to the effective Cartier divisor
`(𝐏¹_Z)_∞`. So the derived base change map of Stacks 0E23 identifies `Le^*Q` with the pushforward
of `𝒪_Z` along the vertex, placed in degree `0`.

## Main definitions

* `Stacks.Chow.derivedPullbackSinglePushforwardUnitIsoOfTorIndependent` — for a cartesian square
  `Z' ⟶ X'`, `Z ⟶ X` with `i : Z ⟶ X` a closed immersion and `Z`, `X'` Tor independent over
  `X`, `Lf^*(i_*𝒪_Z[0]) ≅ i'_*𝒪_{Z'}[0]`.
* `Stacks.Chow.derivedPullbackExceptionalFibreLineIso` — `Q|_E ≅ v_*𝒪_Z[0]`, `v` the vertex.

## Main results

* `Stacks.Chow.isPullback_vertex_lineToBlowupAtInfinity` — the base change of `𝐏¹_Z ⟶ W` along
  `E = W_∞ ×_X Z ⟶ W` is the vertex `Z ⟶ E`.
* `Stacks.Chow.torIndependent_lineToBlowupAtInfinity_exceptionalFibre` — `𝐏¹_Z` and `E` are Tor
  independent over `W`.
* `Stacks.Chow.vertex_comp_exceptionalDivisorToCentre` — the vertex is a section of `E ⟶ Z`.

## References

* [Stacks Project, Tag 0FEG](https://stacks.math.columbia.edu/tag/0FEG)
* [Stacks Project, Tag 0FE9](https://stacks.math.columbia.edu/tag/0FE9)
* [Stacks Project, Tag 0E23](https://stacks.math.columbia.edu/tag/0E23)
-/

@[expose] public noncomputable section

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits
open Stacks.AlgebraicGeometry.ReflexiveModules

universe u

namespace Stacks.Chow

attribute [local instance 10000] HasDerivedCategory.standard

/-! ### Tor-independent base change of the structure sheaf of a closed subscheme -/

section TorIndependentBaseChange

/-- **Tor-independent base change of `i_*𝒪_Z`** (Stacks 0E23). For a cartesian square

```
Z' --i'--> X'
|g          |f
Z --i-----> X
```

with `i` a closed immersion and `Z`, `X'` Tor independent over `X`, the derived pullback of
`i_*𝒪_Z[0]` along `f` is `i'_*𝒪_{Z'}[0]`: the derived base change map
`Lf^*(Ri_*𝒪_Z) ⟶ Ri'_*(Lg^*𝒪_Z)` is invertible, `Ri_*` and `Ri'_*` of a module in degree `0` are
its pushforward in degree `0`, and `Lg^*𝒪_Z[0] = 𝒪_{Z'}[0]`. -/
def derivedPullbackSinglePushforwardUnitIsoOfTorIndependent {Z' X' Z X : Scheme.{u}}
    {i' : Z' ⟶ X'} {g : Z' ⟶ Z} {f : X' ⟶ X} {i : Z ⟶ X} (sq : IsPullback i' g f i)
    [IsClosedImmersion i] (h : TorIndependent i f) :
    (Cohomology.DerivedAdjunctionOnRingedSpaces.derivedPullback f.toLRSHom.toShHom).obj
        ((DerivedCategory.singleFunctor X.Modules 0).obj
          ((Scheme.Modules.pushforward i).obj (SheafOfModules.unit Z.ringCatSheaf))) ≅
      (DerivedCategory.singleFunctor X'.Modules 0).obj
          ((Scheme.Modules.pushforward i').obj (SheafOfModules.unit Z'.ringCatSheaf)) := by
  haveI : IsClosedImmersion i' := MorphismProperty.of_isPullback sq.flip inferInstance
  have hiso := derivedBaseChangeIsoOfTorIndependent sq inferInstance h
    ((DerivedCategory.singleFunctor Z.Modules 0).obj (SheafOfModules.unit Z.ringCatSheaf))
  exact (Cohomology.DerivedAdjunctionOnRingedSpaces.derivedPullback f.toLRSHom.toShHom).mapIso
      (Stacks.Thickenings.derivedPushforwardSingleIso i.toLRSHom.toShHom
        i.isClosedEmbedding _).symm ≪≫
    @asIso _ _ _ _ _ hiso ≪≫
    (Cohomology.DerivedAdjunctionOnRingedSpaces.derivedPushforward i'.toLRSHom.toShHom).mapIso
      (Stacks.RingedSpace.derivedPullbackSingleUnitIso g.toLRSHom.toShHom) ≪≫
    Stacks.Thickenings.derivedPushforwardSingleIso i'.toLRSHom.toShHom i'.isClosedEmbedding _

end TorIndependentBaseChange

/-! ### The base change of `𝐏¹_Z ⟶ W` to `E = W_∞ ×_X Z` -/

section Vertex

variable {X S Z : Scheme.{u}} (f : X ⟶ S) (i : Z ⟶ X) [IsClosedImmersion i]

/-- `E = W_∞ ×_X Z ⟶ W_∞ ⟶ W` is the exceptional divisor `E ⊆ W`, read through
`E ≅ W_∞ ×_X Z` (`Stacks.Chow.isPullback_exceptionalDivisorToFibreAtInfinity`). -/
theorem pullback_fst_comp_modificationInclusionAtInfinity_blowupAtInfinity :
    pullback.fst (modificationProjectionAtInfinity f
        (blowupAtInfinityToProjectiveLineProduct i.ker f)) i ≫
      modificationInclusionAtInfinity f (blowupAtInfinityToProjectiveLineProduct i.ker f) =
    (isPullback_exceptionalDivisorToFibreAtInfinity f i).isoPullback.inv ≫
      (exceptionalIdealAtInfinity i.ker).subschemeι := by
  rw [← exceptionalDivisorToFibreAtInfinity_inclusion, IsPullback.isoPullback_inv_fst_assoc]

/-- The ideal of `E = W_∞ ×_X Z` in `W` is that of the exceptional divisor. -/
theorem ker_pullback_fst_comp_modificationInclusionAtInfinity_blowupAtInfinity :
    (pullback.fst (modificationProjectionAtInfinity f
        (blowupAtInfinityToProjectiveLineProduct i.ker f)) i ≫
      modificationInclusionAtInfinity f (blowupAtInfinityToProjectiveLineProduct i.ker f)).ker =
    exceptionalIdealAtInfinity i.ker := by
  rw [pullback_fst_comp_modificationInclusionAtInfinity_blowupAtInfinity,
    Scheme.Hom.ker_comp_of_isIso, Scheme.IdealSheafData.ker_subschemeι]

/-- **The base change of `𝐏¹_Z ⟶ W` along `E = W_∞ ×_X Z ⟶ W` is the vertex** `Z ⟶ C_ZX ⟶ E`
(the proof of Stacks 0FE9), read in `W_∞ ×_X Z`. -/
theorem isPullback_vertex_lineToBlowupAtInfinity :
    IsPullback
      ((normalConeZeroSection i ≫ normalConeToExceptionalDivisor i) ≫
        (isPullback_exceptionalDivisorToFibreAtInfinity f i).isoPullback.hom)
      (i.toImage ≫ lineInfinitySection i.ker.subscheme)
      (pullback.fst (modificationProjectionAtInfinity f
        (blowupAtInfinityToProjectiveLineProduct i.ker f)) i ≫
          modificationInclusionAtInfinity f (blowupAtInfinityToProjectiveLineProduct i.ker f))
      (lineToBlowupAtInfinity i.ker) := by
  refine (isPullback_lineToBlowupAtInfinity_exceptionalIdealAtInfinity i).flip.of_iso
    (Iso.refl _) (isPullback_exceptionalDivisorToFibreAtInfinity f i).isoPullback
    (Iso.refl _) (Iso.refl _) ?_ ?_ ?_ ?_
  · simp
  · simp
  · rw [pullback_fst_comp_modificationInclusionAtInfinity_blowupAtInfinity, Iso.hom_inv_id_assoc,
      Iso.refl_hom, Category.comp_id]
  · simp

/-- **`𝐏¹_Z` and `E = W_∞ ×_X Z` are Tor independent over `W`**: `E ⟶ W` is the inclusion of
the exceptional divisor, an effective Cartier divisor pulling back to `(𝐏¹_Z)_∞`. -/
theorem torIndependent_lineToBlowupAtInfinity_exceptionalFibre :
    TorIndependent (lineToBlowupAtInfinity i.ker)
      (pullback.fst (modificationProjectionAtInfinity f
        (blowupAtInfinityToProjectiveLineProduct i.ker f)) i ≫
          modificationInclusionAtInfinity f (blowupAtInfinityToProjectiveLineProduct i.ker f)) :=
  torIndependent_of_isEffectiveCartierDivisor_ker _ _
    (by
      rw [ker_pullback_fst_comp_modificationInclusionAtInfinity_blowupAtInfinity]
      exact isEffectiveCartierDivisor_exceptionalIdealAtInfinity i.ker)
    (by
      rw [ker_pullback_fst_comp_modificationInclusionAtInfinity_blowupAtInfinity,
        comap_exceptionalIdealAtInfinity_lineToBlowupAtInfinity]
      exact lineInfinityDivisor_isEffectiveCartierDivisor _)

/-- **`Q|_E` is the structure sheaf of the vertex** (the proof of Stacks 0FEG): for
`Q = i'_*𝒪_{𝐏¹_Z}[0]` and `e : E = W_∞ ×_X Z ⟶ W`, `Le^*Q ≅ v_*𝒪_Z[0]` with `v : Z ⟶ E` the
vertex of the normal cone, by Tor-independent base change. -/
def derivedPullbackExceptionalFibreLineIso :
    (Cohomology.DerivedAdjunctionOnRingedSpaces.derivedPullback
      (pullback.fst (modificationProjectionAtInfinity f
        (blowupAtInfinityToProjectiveLineProduct i.ker f)) i ≫
          modificationInclusionAtInfinity f
            (blowupAtInfinityToProjectiveLineProduct i.ker f)).toLRSHom.toShHom).obj
        ((DerivedCategory.singleFunctor _ 0).obj ((Scheme.Modules.pushforward
          (lineToBlowupAtInfinity i.ker)).obj (SheafOfModules.unit _))) ≅
      (DerivedCategory.singleFunctor _ 0).obj ((Scheme.Modules.pushforward
        ((normalConeZeroSection i ≫ normalConeToExceptionalDivisor i) ≫
          (isPullback_exceptionalDivisorToFibreAtInfinity f i).isoPullback.hom)).obj
            (SheafOfModules.unit Z.ringCatSheaf)) :=
  derivedPullbackSinglePushforwardUnitIsoOfTorIndependent
    (isPullback_vertex_lineToBlowupAtInfinity f i)
    (torIndependent_lineToBlowupAtInfinity_exceptionalFibre f i)

/-- **The vertex is a section of `E ⟶ Z`.** -/
theorem vertex_comp_exceptionalDivisorToCentre :
    (normalConeZeroSection i ≫ normalConeToExceptionalDivisor i) ≫
      exceptionalDivisorToCentre i = 𝟙 Z := by
  rw [← cancel_mono i, Category.assoc, exceptionalDivisorToCentre_comp_toX, Category.assoc,
    normalConeToExceptionalDivisor_comp_toBase, normalConeZeroSection_toBase_assoc,
    Category.id_comp]

/-- Under `E ≅ 𝐏(𝒞 ⊕ 𝒪_Z)` the vertex is a closed immersion, being a section of the separated
morphism `𝐏(𝒞 ⊕ 𝒪_Z) ⟶ Z`. -/
instance isClosedImmersion_vertex_comp_exceptionalDivisorIsoProjectiveCompletion_hom
    [IsLocallyNoetherian Z] (hi : Stacks.AlgebraicGeometry.RegularIdealSheaf.IsRegularImmersion i) :
    IsClosedImmersion ((normalConeZeroSection i ≫ normalConeToExceptionalDivisor i) ≫
      (exceptionalDivisorIsoProjectiveCompletion i hi).hom) := by
  have : IsClosedImmersion (((normalConeZeroSection i ≫ normalConeToExceptionalDivisor i) ≫
      (exceptionalDivisorIsoProjectiveCompletion i hi).hom) ≫
        Stacks.ProjectiveCompletion.projectiveCompletionProj
          (dualSheaf (VirtualNormalBundle.ofIsRegularImmersion i hi).bundle)) := by
    rw [Category.assoc, exceptionalDivisorIsoProjectiveCompletion_hom_projection,
      vertex_comp_exceptionalDivisorToCentre]
    infer_instance
  exact IsClosedImmersion.of_comp _ (Stacks.ProjectiveCompletion.projectiveCompletionProj
    (dualSheaf (VirtualNormalBundle.ofIsRegularImmersion i hi).bundle))

end Vertex

end Stacks.Chow

end
