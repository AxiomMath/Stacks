module

public import StacksFrontier.AlgebraicGeometry.Chow.LocalizedChern.RegularImmersionDeformationChernVertex
public import StacksFrontier.AlgebraicGeometry.Chow.LocalizedChern.RegularImmersionDeformationChernZeroSection
public import StacksFrontier.AlgebraicGeometry.Chow.LocalizedChern.RegularImmersionDeformationTop
public import StacksFrontier.AlgebraicGeometry.Morphism.KerChart

/-!
# `Q|_E` is the pushforward of `𝒪_Z` along the zero section, and `c'_t(Q) = 0` for `0 < t < r`

Let `i : Z ⟶ X` be a regular closed immersion of codimension `r`, `W` the blowup of `𝐏¹_X` in
`∞(Z)`, read as a modification of `X ×_S 𝐏¹_S`, with fibre at infinity `W_∞`,
`E = W_∞ ×_X Z` and `e : E ⟶ W_∞ ⟶ W`, let `i' : 𝐏¹_Z ⟶ W` be the closed immersion of
Stacks 0FE9 and `Q = i'_*𝒪_{𝐏¹_Z}[0]`. In the proof of Stacks 0FEG:

* `Q|_E = Le^*Q` is the pushforward of `𝒪_Z` along the vertex `Z ⟶ C_ZX ⟶ E` of the normal cone
  (Tor-independent base change, `Stacks.Chow.derivedPullbackExceptionalFibreLineIso`);
* under `E ≅ P = 𝐏(𝒞 ⊕ 𝒪_Z)`, `𝒞` the conormal sheaf, the vertex is the zero section
  `i_0 : 𝐏(𝒪_Z) ⟶ P` of Stacks 0FEF
  (`Stacks.Chow.ker_vertex_comp_exceptionalDivisorIsoProjectiveCompletion_hom`), so
  `Le^*Q ≅ Lφ^*(i_{0,*}𝒪_Z[0])` for `φ : E ≅ P`;
* hence `c'_t(Q) = 0` for `0 < t < r`, the Chern classes `c_t(i_{0,*}𝒪_Z)` vanishing in that range
  by Stacks 0FEF, and `c'_r(Q) = (-1)^{r-1}(r-1)! c(Z ⟶ X, 𝒩)` by part (F)
  (`Stacks.Chow.modificationChernClass_eq_regularNormalGysinClass`).

## Main definitions

* `Stacks.Chow.derivedPullbackExceptionalFibreZeroSectionIso` — `Le^*Q ≅ Lφ^*(i_{0,*}𝒪_Z[0])`.

## Main results

* `Stacks.Chow.modificationChernClass_lineToBlowupAtInfinity_eq_zero` — `c'_t(Q) = 0` for
  `0 < t < r`.
* `Stacks.Chow.modificationChernClass_lineToBlowupAtInfinity_eq_regularNormalGysinClass` —
  `c'_r(Q) = (-1)^{r-1}(r-1)! c(Z ⟶ X, 𝒩)`.

## References

* [Stacks Project, Tag 0FEG](https://stacks.math.columbia.edu/tag/0FEG)
* [Stacks Project, Tag 0FEF](https://stacks.math.columbia.edu/tag/0FEF)
* [Stacks Project, Tag 0F9K](https://stacks.math.columbia.edu/tag/0F9K)
-/

@[expose] public noncomputable section

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits
open Stacks.AlgebraicGeometry.ReflexiveModules Stacks.AlgebraicGeometry.RegularIdealSheaf

universe u

namespace Stacks.Chow

attribute [local instance 10000] HasDerivedCategory.standard

section Identification

variable {X S Z : Scheme.{u}} (f : X ⟶ S) (i : Z ⟶ X) [IsClosedImmersion i]
  [IsLocallyNoetherian Z] (hi : IsRegularImmersion i) (r : ℕ)
  [AlgebraicGeometry.SheafOfModules.IsFiniteLocallyFreeOfRank.{u, u, u} (conormalModule i) r]

/-- **`Q|_E` is the pushforward of `𝒪_Z` along the zero section** (the proof of Stacks 0FEG): for
`Q = i'_*𝒪_{𝐏¹_Z}[0]`, `e : E = W_∞ ×_X Z ⟶ W` and `φ : E ≅ P = 𝐏(𝒞 ⊕ 𝒪_Z)`
(`Stacks.Chow.exceptionalFibreIsoProjectiveCompletion`), `Le^*Q ≅ Lφ^*(i_{0,*}𝒪_Z[0])` with
`i_0 : 𝐏(𝒪_Z) ⟶ P` the zero section of Stacks 0FEF. Both sides are the structure sheaf of the
vertex of the normal cone, pushed forward to `E`: the left by Tor-independent base change, the
right by flat base change along `φ`, the vertex being the zero section under `φ`. -/
def derivedPullbackExceptionalFibreZeroSectionIso :
    (Cohomology.DerivedAdjunctionOnRingedSpaces.derivedPullback
      (pullback.fst (modificationProjectionAtInfinity f
        (blowupAtInfinityToProjectiveLineProduct i.ker f)) i ≫
          modificationInclusionAtInfinity f
            (blowupAtInfinityToProjectiveLineProduct i.ker f)).toLRSHom.toShHom).obj
        ((DerivedCategory.singleFunctor _ 0).obj ((Scheme.Modules.pushforward
          (lineToBlowupAtInfinity i.ker)).obj (SheafOfModules.unit _))) ≅
      (Cohomology.DerivedAdjunctionOnRingedSpaces.derivedPullback
        (exceptionalFibreIsoProjectiveCompletion f i hi).hom.toLRSHom.toShHom).obj
        ((DerivedCategory.singleFunctor _ 0).obj ((Scheme.Modules.pushforward
          (Stacks.ProjectiveCompletion.zeroSection
            (dualSheaf (VirtualNormalBundle.ofIsRegularImmersion i hi).bundle))).obj
              (SheafOfModules.unit
                (Stacks.Chow.bundle (Stacks.Ample.unitModule Z)).ringCatSheaf))) :=
  let hker := ker_vertex_comp_exceptionalDivisorIsoProjectiveCompletion_hom i hi r
  let θ := Stacks.AlgebraicGeometry.KerChart.isoOfKerEq _ _ hker
  have hθ := Stacks.AlgebraicGeometry.KerChart.isoOfKerEq_hom_comp _ _ hker
  have sq : IsPullback ((normalConeZeroSection i ≫ normalConeToExceptionalDivisor i) ≫
        (isPullback_exceptionalDivisorToFibreAtInfinity f i).isoPullback.hom) θ.inv
      (exceptionalFibreIsoProjectiveCompletion f i hi).hom
      (Stacks.ProjectiveCompletion.zeroSection
        (dualSheaf (VirtualNormalBundle.ofIsRegularImmersion i hi).bundle)) := by
    refine IsPullback.of_vert_isIso ⟨?_⟩
    rw [← hθ, Iso.inv_hom_id_assoc]
    simp only [exceptionalFibreIsoProjectiveCompletion, Iso.trans_hom, Iso.symm_hom,
      Category.assoc, Iso.hom_inv_id_assoc]
  derivedPullbackExceptionalFibreLineIso f i ≪≫
    (derivedPullbackSinglePushforwardUnitIsoOfTorIndependent sq
      (torIndependent_of_flat_right _ _)).symm

end Identification

/-! ### The classes `c'_t(Q)` -/

section Chern

variable (C : ChowSituation.{u}) {X Z : Scheme.{u}} (sX : X ⟶ C.S) [LocallyOfFiniteType sX]
  (i : Z ⟶ X) [IsClosedImmersion i] {r : ℕ}

/-- **`c'_t(Q) = 0` for `0 < t < r`** (part of the proof of Stacks 0FEG). Let `i : Z ⟶ X` be a
regular closed immersion of codimension `r`, `W` the blowup of `𝐏¹_X` in `∞(Z)` and
`Q = i'_*𝒪_{𝐏¹_Z}[0]` for the closed immersion `i' : 𝐏¹_Z ⟶ W` of Stacks 0FE9. For `0 < t < r`
the class `c'_t(Q) ∈ A^t(Z ⟶ X)` of Stacks 0F9K, taken with `T = X'` the strict transform,
vanishes: `Q|_E` is the pushforward of `𝒪_Z` along the zero section of `E ≅ 𝐏(𝒞 ⊕ 𝒪_Z)`
(`Stacks.Chow.derivedPullbackExceptionalFibreZeroSectionIso`), whose Chern classes of degree
`0 < t < r` vanish by Stacks 0FEF. -/
theorem modificationChernClass_lineToBlowupAtInfinity_eq_zero
    (hreg : IsRegularClosedImmersionOfCodim i r)
    (hQ : HasDefinedChernClasses ((DerivedCategory.singleFunctor _ 0).obj
      ((Scheme.Modules.pushforward (lineToBlowupAtInfinity i.ker)).obj (SheafOfModules.unit _))))
    (t : ℕ) (ht : 0 < t) (htr : t < r) (hT hrank) :
    modificationChernClass C sX (blowupAtInfinityToProjectiveLineProduct i.ker sX)
      (isIso_pullback_snd_blowupAtInfinityToProjectiveLineProduct i.ker sX) i
      (strictTransformToFibreAtInfinity sX i) hQ t hT hrank = 0 := by
  have : IsLocallyNoetherian Z := LocallyOfFiniteType.isLocallyNoetherian (i ≫ sX)
  have hi := hreg.isRegularImmersion
  have := hreg.isFiniteLocallyFreeOfRank_conormalModule
  have := Stacks.ProjectiveCompletion.flat_projectiveCompletionProj
    (dualSheaf (VirtualNormalBundle.ofIsRegularImmersion i hi).bundle) r
  have := Stacks.ProjectiveCompletion.locallyOfFiniteType_projectiveCompletionProj
    (dualSheaf (VirtualNormalBundle.ofIsRegularImmersion i hi).bundle) r
  refine modificationChernClass_eq_zero_of_derivedPullback_iso C sX _ _ i _ hQ t
    (Stacks.ProjectiveCompletion.projectiveCompletionProj
      (dualSheaf (VirtualNormalBundle.ofIsRegularImmersion i hi).bundle) ≫ i ≫ sX)
    (exceptionalFibreIsoProjectiveCompletion sX i hi).hom ?_
    (Stacks.ProjectiveCompletion.hasDefinedChernClasses_pushforward_zeroSection _ r)
    ((chernClass_pushforward_zeroSection C (i ≫ sX) _ r (by omega)).1 t ht htr)
    (derivedPullbackExceptionalFibreZeroSectionIso sX i hi r) hT hrank
  rw [exceptionalFibreIsoProjectiveCompletion_hom_projection_assoc, ← pullback.condition_assoc]
  rfl

/-- **`c'_r(Q) = (-1)^{r-1}(r-1)! c(Z ⟶ X, 𝒩)`** (part (F) of the proof of Stacks 0FEG), for
`Q = i'_*𝒪_{𝐏¹_Z}[0]` with defined Chern classes and `Q|_{X'}` finite locally free of rank `< r`:
`Stacks.Chow.modificationChernClass_eq_regularNormalGysinClass` at the identification
`Stacks.Chow.derivedPullbackExceptionalFibreZeroSectionIso` of `Q|_E`. -/
theorem modificationChernClass_lineToBlowupAtInfinity_eq_regularNormalGysinClass
    (hreg : IsRegularClosedImmersionOfCodim i r) (hr : r ≠ 0)
    (hQ : HasDefinedChernClasses ((DerivedCategory.singleFunctor _ 0).obj
      ((Scheme.Modules.pushforward (lineToBlowupAtInfinity i.ker)).obj (SheafOfModules.unit _))))
    (hrank) :
    modificationChernClass C sX (blowupAtInfinityToProjectiveLineProduct i.ker sX)
        (isIso_pullback_snd_blowupAtInfinityToProjectiveLineProduct i.ker sX) i
        (strictTransformToFibreAtInfinity sX i) hQ r
        (mem_range_strictTransformToFibreAtInfinity sX i) hrank =
      ((-1 : ℤ) ^ (r - 1) * ((r - 1).factorial : ℤ)) •
        regularNormalGysinClass C (i ≫ sX) sX i rfl hreg := by
  have : IsLocallyNoetherian Z := LocallyOfFiniteType.isLocallyNoetherian (i ≫ sX)
  have := hreg.isFiniteLocallyFreeOfRank_conormalModule
  exact modificationChernClass_eq_regularNormalGysinClass C sX i hreg hr hQ hrank
    (derivedPullbackExceptionalFibreZeroSectionIso sX i hreg.isRegularImmersion r)

end Chern

end Stacks.Chow

end
