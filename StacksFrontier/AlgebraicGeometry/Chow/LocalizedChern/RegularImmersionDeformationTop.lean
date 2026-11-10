module

public import StacksFrontier.AlgebraicGeometry.Chow.BivariantLemmas.ExcessNormalSheaf
public import StacksFrontier.AlgebraicGeometry.Chow.BivariantLemmas.VirtualNormalBundleClassBaseChange
public import StacksFrontier.AlgebraicGeometry.Chow.InfinityCentreExceptionalCompletionCone
public import StacksFrontier.AlgebraicGeometry.Chow.LocalizedChern.ModificationComparison
public import StacksFrontier.AlgebraicGeometry.Chow.LocalizedChern.RegularImmersionDeformationChern
public import StacksFrontier.AlgebraicGeometry.Chow.LocalizedChern.RegularImmersionStructureSheaf
public import StacksFrontier.AlgebraicGeometry.Chow.ZeroSectionKoszul.ChernClassZeroSection

/-!
# The top class `c'_r(Q)` of the deformation of `i_*𝒪_Z` to the normal cone

Let `(S, δ)` be the base situation of chapter 42 of the Stacks Project, `X` locally of finite
type over `S`, and `i : Z ⟶ X` a regular closed immersion of codimension `r ≥ 1`, with conormal
sheaf `𝒞`, normal sheaf `𝒩 = 𝒞^∨`, normal bundle `N` and projective completion
`P = 𝐏(𝒞 ⊕ 𝒪_Z)`, the vector bundle `N ⊆ P` being the complement of the divisor at infinity. Let
`b : W ⟶ 𝐏¹_X` be the blowup in `∞(Z)`, with fibre at infinity `W_∞`, strict transform
`X' ⊆ W_∞`, `E = W_∞ ×_X Z` and `e : E ⟶ W_∞ ⟶ W`, and let `C ∈ A⁰(W_∞ ⟶ X)` be the class of
Stacks 0F9J and `j : C_ZX ⟶ W_∞` the open immersion of Stacks 0FBH.

In the proof of Stacks 0FEG the object `Q ∈ D(𝒪_W)` restricts on `E ≅ P` to the pushforward
`i_{0,*}𝒪_Z` of the structure sheaf along the zero section, and the second assertion

  `c'_r(Q) = (-1)^{r-1} (r-1)! c(Z ⟶ X, 𝒩)   in   A^r(Z ⟶ X)`

follows from Stacks 0FEF. By the characterization of Stacks 0FBK it suffices to show
`p^*(c'_r(Q) ∩ α) = (-1)^{r-1}(r-1)! ι_* j^*(C ∩ α)` on every test scheme `T ⟶ X`. There
`C ∩ α = a_* β₁ + b_* β₂` along the closed cover `W_∞ ×_X T = (X' ×_X T) ∪ (E ×_X T)`
(Stacks 0F94). Both sides kill `a_* β₁`: the extension `c'_r(Q|_E)` of Stacks 0F9H vanishes on
it, and `j^*` does because the normal cone misses `X'`. On `b_* β₂` the left side is
`p^*π'_*(c_r(i_{0,*}𝒪_Z) ∩ β₂)`, computed on `E ×_X T ≅ (Z ×_X T) ×_Z P`, and Stacks 0FEF turns
it into `(-1)^{r-1}(r-1)!` times the restriction of `β₂` to `V' ≅ N ×_X T`; the right side is the
restriction of `β₂` to `C_ZX ×_X T ≅ N ×_X T`, and the two open immersions into `E ×_X T` agree
because `C_ZX ⟶ E ≅ P` is `C_ZX ⟶ N ⟶ P`
(`Stacks.Chow.normalConeToExceptionalDivisor_comp_exceptionalDivisorIsoProjectiveCompletion_hom`).

## Main definitions

* `Stacks.Chow.exceptionalFibreIsoProjectiveCompletion` — `W_∞ ×_X Z ≅ 𝐏(𝒞 ⊕ 𝒪_Z)` over `Z`.
* `Stacks.Chow.normalConeToExceptionalFibre` — the open immersion `C_ZX ⟶ W_∞ ×_X Z`.
* `Stacks.Chow.exceptionalTestIso`, `Stacks.Chow.bundleTestIsoComplement`,
  `Stacks.Chow.normalConeTestToExceptional` — `E ×_X T ≅ (Z ×_X T) ×_Z P`, `N ×_X T ≅ V'`, and
  the open immersion `C_ZX ×_X T ⟶ E ×_X T`, over a test scheme `T ⟶ X`.

## Main results

* `Stacks.Chow.bundleFlatPullbackChow_perfectChernClass_exceptionalTest` — Stacks 0FEF on the
  exceptional divisor over a test scheme.
* `Stacks.Chow.bundleFlatPullback_modificationChernClass_cap` —
  `p^*(c'_r(Q) ∩ α) = (-1)^{r-1}(r-1)! ι_* j^*(C ∩ α)` on every test scheme.
* `Stacks.Chow.modificationChernClass_eq_regularNormalGysinClass_of_derivedPullback_iso`,
  `Stacks.Chow.modificationChernClass_eq_regularNormalGysinClass` — **the second assertion of the
  proof of Stacks 0FEG**: `c'_r(Q) = (-1)^{r-1}(r-1)! c(Z ⟶ X, 𝒩)`.

## Implementation notes

The identification `Le^*Q ≅ Lφ^*(i_{0,*}𝒪_Z)` of the restriction of `Q` to `E` is a hypothesis
of the results here, for an isomorphism `φ : E ≅ 𝐏(𝒞 ⊕ 𝒪_Z)` over `Z` under which the open
immersion `C_ZX ⟶ E` is `C_ZX ⟶ N ⟶ 𝐏(𝒞 ⊕ 𝒪_Z)`; for `Q = i'_*𝒪_{𝐏¹_Z}` it is the
Tor-independent base change of Stacks 0FE9. The isomorphism
`Stacks.Chow.exceptionalFibreIsoProjectiveCompletion` has these properties.

The degree `r` is required to be nonzero, as the factor `(r-1)!` of the source presupposes.

## References

* [Stacks Project, Tag 0FEG](https://stacks.math.columbia.edu/tag/0FEG)
* [Stacks Project, Tag 0FEF](https://stacks.math.columbia.edu/tag/0FEF)
* [Stacks Project, Tag 0FBK](https://stacks.math.columbia.edu/tag/0FBK)
* [Stacks Project, Tag 0F9K](https://stacks.math.columbia.edu/tag/0F9K)
* [Stacks Project, Tag 0F9H](https://stacks.math.columbia.edu/tag/0F9H)
* [Stacks Project, Tag 0F94](https://stacks.math.columbia.edu/tag/0F94)
* [Stacks Project, Tag 0FBH](https://stacks.math.columbia.edu/tag/0FBH)
* [Stacks Project, Tag 0FE9](https://stacks.math.columbia.edu/tag/0FE9)
-/

@[expose] public noncomputable section

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits
open Stacks.AlgebraicGeometry.ReflexiveModules Stacks.AlgebraicGeometry.RegularIdealSheaf
open Stacks.ProjectiveCompletion

universe u

namespace Stacks.Chow

/-! ### The exceptional divisor over a test scheme -/

section ExceptionalBaseChange

/-- **`E ×_I (I ×_X V) = E ×_Z (Z ×_X V)`** for `E = I ×_X Z`: the square formed by the
projection `(I ×_X Z) ×_I (I ×_X V) ⟶ I ×_X Z`, the morphism
`Stacks.Chow.exceptionalBaseChangeMap` to `Z ×_X V`, and the projections to `Z` is cartesian. -/
theorem isPullback_exceptionalBaseChangeMap {I X Z V : Scheme.{u}} (π : I ⟶ X) (z : Z ⟶ X)
    (g : V ⟶ X) :
    IsPullback (pullback.fst (pullback.fst π z) (pullback.fst π g))
      (exceptionalBaseChangeMap π z g) (pullback.snd π z) (pullback.fst z g) := by
  have s := (IsPullback.of_hasPullback (pullback.fst π z) (pullback.fst π g)).paste_vert
    (IsPullback.of_hasPullback π g)
  rw [← exceptionalBaseChangeMap_snd, pullback.condition (f := π) (g := z)] at s
  exact s.of_bot (exceptionalBaseChangeMap_fst π z g).symm (IsPullback.of_hasPullback z g)

end ExceptionalBaseChange

section Geometry

variable {X S Z : Scheme.{u}} (f : X ⟶ S) (i : Z ⟶ X) [IsClosedImmersion i]

/-- The open immersion `C_ZX ⟶ E = W_∞ ×_X Z` of Stacks 0FBH, read into the chosen fibre
product: it is `j : C_ZX ⟶ W_∞` together with the projection `C_ZX ⟶ Z`. -/
def normalConeToExceptionalFibre :
    Stacks.Conormal.normalCone i ⟶
      pullback (modificationProjectionAtInfinity f
        (blowupAtInfinityToProjectiveLineProduct i.ker f)) i :=
  pullback.lift (normalConeToFibreAtInfinity i f) (Stacks.Conormal.normalConeToBase i)
    (normalConeToFibreAtInfinity_comp_projection i f)

/-- The open immersion `C_ZX ⟶ W_∞ ×_X Z` followed by the projection to `W_∞` is `j`. -/
@[reassoc (attr := simp)]
theorem normalConeToExceptionalFibre_fst :
    normalConeToExceptionalFibre f i ≫ pullback.fst _ _ = normalConeToFibreAtInfinity i f :=
  pullback.lift_fst _ _ _

/-- The open immersion `C_ZX ⟶ W_∞ ×_X Z` lies over `Z`. -/
@[reassoc (attr := simp)]
theorem normalConeToExceptionalFibre_snd :
    normalConeToExceptionalFibre f i ≫ pullback.snd _ _ = Stacks.Conormal.normalConeToBase i :=
  pullback.lift_snd _ _ _

/-- Through `E ≅ W_∞ ×_X Z`, the open immersion `C_ZX ⟶ W_∞ ×_X Z` is the open immersion
`C_ZX ⟶ E` of Stacks 0FBH. -/
theorem normalConeToExceptionalFibre_isoPullback_inv :
    normalConeToExceptionalFibre f i ≫
        (isPullback_exceptionalDivisorToFibreAtInfinity f i).isoPullback.inv =
      normalConeToExceptionalDivisor i := by
  rw [← cancel_mono (exceptionalDivisorToFibreAtInfinity f i ≫
      modificationInclusionAtInfinity f (blowupAtInfinityToProjectiveLineProduct i.ker f)),
    Category.assoc, IsPullback.isoPullback_inv_fst_assoc, normalConeToExceptionalFibre_fst_assoc,
    normalConeToFibreAtInfinity_inclusion, exceptionalDivisorToFibreAtInfinity_inclusion]

/-- `C_ZX ⟶ W_∞ ×_X Z` is an open immersion: it is `C_ZX ⟶ E` of Stacks 0FBH followed by
`E ≅ W_∞ ×_X Z`. -/
instance isOpenImmersion_normalConeToExceptionalFibre :
    IsOpenImmersion (normalConeToExceptionalFibre f i) := by
  have h : normalConeToExceptionalFibre f i = normalConeToExceptionalDivisor i ≫
      (isPullback_exceptionalDivisorToFibreAtInfinity f i).isoPullback.hom := by
    rw [← normalConeToExceptionalFibre_isoPullback_inv, Category.assoc, Iso.inv_hom_id,
      Category.comp_id]
  rw [h]
  infer_instance

/-- **The strict transform misses the normal cone**: inside `W_∞`, the image of `X' ⟶ W_∞` is
disjoint from that of the open immersion `j : C_ZX ⟶ W_∞` of Stacks 0FBH, whose image is
`W_∞ ∖ X'`. -/
theorem disjoint_range_strictTransformToFibreAtInfinity :
    Disjoint (Set.range (strictTransformToFibreAtInfinity f i).base)
      (Set.range (normalConeToFibreAtInfinity i f).base) := by
  refine Set.disjoint_left.mpr ?_
  rintro _ ⟨a, rfl⟩ ⟨c, hc⟩
  have h1 : (modificationInclusionAtInfinity f
      (blowupAtInfinityToProjectiveLineProduct i.ker f)).base
        ((strictTransformToFibreAtInfinity f i).base a) ∈
        (strictTransformIdealAtInfinity i.ker).support := by
    rw [← Scheme.Hom.comp_apply, strictTransformToFibreAtInfinity_inclusion]
    exact (Set.ext_iff.mp (Scheme.IdealSheafData.range_subschemeι
      (strictTransformIdealAtInfinity i.ker)) _).mp ⟨a, rfl⟩
  have h2 : (normalConeToFibreAtInfinity i f).base c ∈
      (normalConeToFibreAtInfinity i f).opensRange := ⟨c, rfl⟩
  rw [opensRange_normalConeToFibreAtInfinity, hc] at h2
  exact h2 h1

variable [IsLocallyNoetherian Z] (hi : IsRegularImmersion i)

/-- **`W_∞ ×_X Z ≅ 𝐏(𝒞 ⊕ 𝒪_Z)`**: the scheme `E = W_∞ ×_X Z` of Stacks 0F9K, for the blowup at
infinity of a regular closed immersion, is the projective completion of the normal bundle, through
the exceptional divisor (`Stacks.Chow.isPullback_exceptionalDivisorToFibreAtInfinity` and
`Stacks.Chow.exceptionalDivisorIsoProjectiveCompletion`). -/
def exceptionalFibreIsoProjectiveCompletion :
    pullback (modificationProjectionAtInfinity f
        (blowupAtInfinityToProjectiveLineProduct i.ker f)) i ≅
      projectiveCompletion (dualSheaf (VirtualNormalBundle.ofIsRegularImmersion i hi).bundle) :=
  (isPullback_exceptionalDivisorToFibreAtInfinity f i).isoPullback.symm ≪≫
    exceptionalDivisorIsoProjectiveCompletion i hi

/-- The isomorphism `W_∞ ×_X Z ≅ 𝐏(𝒞 ⊕ 𝒪_Z)` lies over `Z`. -/
@[reassoc (attr := simp)]
theorem exceptionalFibreIsoProjectiveCompletion_hom_projection :
    (exceptionalFibreIsoProjectiveCompletion f i hi).hom ≫
        projectiveCompletionProj
          (dualSheaf (VirtualNormalBundle.ofIsRegularImmersion i hi).bundle) =
      pullback.snd _ _ := by
  rw [exceptionalFibreIsoProjectiveCompletion, Iso.trans_hom, Iso.symm_hom, Category.assoc,
    exceptionalDivisorIsoProjectiveCompletion_hom_projection, IsPullback.isoPullback_inv_snd]

/-- **The normal cone in `W_∞ ×_X Z ≅ 𝐏(𝒞 ⊕ 𝒪_Z)`**: the open immersion `C_ZX ⟶ W_∞ ×_X Z`
followed by `W_∞ ×_X Z ≅ 𝐏(𝒞 ⊕ 𝒪_Z)` is `C_ZX ⟶ N ⟶ 𝐏(𝒞 ⊕ 𝒪_Z)`, the closed immersion of the
normal cone into the normal bundle followed by the vector bundle in its projective completion. -/
@[reassoc]
theorem normalConeToExceptionalFibre_comp_isoProjectiveCompletion_hom :
    normalConeToExceptionalFibre f i ≫ (exceptionalFibreIsoProjectiveCompletion f i hi).hom =
      (VirtualNormalBundle.ofIsRegularImmersion i hi).normalConeEmbedding ≫
        toCompletion (dualSheaf (VirtualNormalBundle.ofIsRegularImmersion i hi).bundle) := by
  rw [exceptionalFibreIsoProjectiveCompletion, Iso.trans_hom, Iso.symm_hom,
    ← Category.assoc, normalConeToExceptionalFibre_isoPullback_inv,
    normalConeToExceptionalDivisor_comp_exceptionalDivisorIsoProjectiveCompletion_hom]

end Geometry

/-! ### The normal cone over a test scheme -/

section NormalConeTest

variable {X S Z : Scheme.{u}} (f : X ⟶ S) (i : Z ⟶ X) [IsClosedImmersion i] {T : Scheme.{u}}
  (g : T ⟶ X)

local notation "π∞" =>
  modificationProjectionAtInfinity f (blowupAtInfinityToProjectiveLineProduct (Scheme.Hom.ker i) f)

/-- The base change `C_ZX ×_X T ⟶ E ×_{W_∞} (W_∞ ×_X T)` of the open immersion
`C_ZX ⟶ E = W_∞ ×_X Z` along a test scheme `T ⟶ X`, with `C_ZX ⟶ X` written as
`C_ZX ⟶ N ⟶ Z ⟶ X` through a virtual normal bundle. -/
def normalConeTestToExceptional (𝒩 : VirtualNormalBundle i) :
    pullback (𝒩.normalConeEmbedding ≫ 𝒩.projection ≫ i) g ⟶
      pullback (pullback.fst π∞ i) (pullback.fst π∞ g) :=
  pullback.lift (pullback.fst _ _ ≫ normalConeToExceptionalFibre f i) (normalConeTestMap f i 𝒩 g)
    (by simp)

/-- The base change of `C_ZX ⟶ E` lies over `C_ZX ⟶ E`. -/
@[reassoc (attr := simp)]
theorem normalConeTestToExceptional_fst (𝒩 : VirtualNormalBundle i) :
    normalConeTestToExceptional f i g 𝒩 ≫ pullback.fst _ _ =
      pullback.fst _ _ ≫ normalConeToExceptionalFibre f i :=
  pullback.lift_fst _ _ _

/-- The base change of `C_ZX ⟶ E`, followed by `E ×_{W_∞} (W_∞ ×_X T) ⟶ W_∞ ×_X T`, is the base
change of `j : C_ZX ⟶ W_∞`. -/
@[reassoc (attr := simp)]
theorem normalConeTestToExceptional_snd (𝒩 : VirtualNormalBundle i) :
    normalConeTestToExceptional f i g 𝒩 ≫ pullback.snd _ _ = normalConeTestMap f i 𝒩 g :=
  pullback.lift_snd _ _ _

/-- The morphism `C_ZX ×_X T ⟶ E ×_{W_∞} (W_∞ ×_X T)` lies over `X`, hence over the base. -/
@[reassoc]
theorem normalConeTestToExceptional_comp_projection (𝒩 : VirtualNormalBundle i) :
    normalConeTestToExceptional f i g 𝒩 ≫ pullback.fst _ _ ≫ pullback.fst π∞ i ≫ π∞ =
      pullback.fst (𝒩.normalConeEmbedding ≫ 𝒩.projection ≫ i) g ≫
        Stacks.Conormal.normalConeToBase i ≫ i := by
  rw [normalConeTestToExceptional_fst_assoc, normalConeToExceptionalFibre_fst_assoc,
    normalConeToFibreAtInfinity_comp_projection]

/-- The square of `C_ZX ×_X T ⟶ E ×_{W_∞} (W_∞ ×_X T)` over `C_ZX ⟶ E` is cartesian. -/
theorem isPullback_normalConeTestToExceptional (𝒩 : VirtualNormalBundle i) :
    IsPullback (pullback.fst (𝒩.normalConeEmbedding ≫ 𝒩.projection ≫ i) g)
      (normalConeTestToExceptional f i g 𝒩) (normalConeToExceptionalFibre f i)
      (pullback.fst (pullback.fst π∞ i) (pullback.fst π∞ g)) := by
  refine IsPullback.of_bot ?_ (normalConeTestToExceptional_fst f i g 𝒩).symm
    (IsPullback.of_hasPullback (pullback.fst π∞ i) (pullback.fst π∞ g))
  rw [normalConeTestToExceptional_snd, normalConeToExceptionalFibre_fst]
  exact isPullback_pullbackMap_fst _ _ _ _ g

/-- The base change of the open immersion `C_ZX ⟶ E` is an open immersion. -/
instance isOpenImmersion_normalConeTestToExceptional (𝒩 : VirtualNormalBundle i) :
    IsOpenImmersion (normalConeTestToExceptional f i g 𝒩) :=
  MorphismProperty.of_isPullback (isPullback_normalConeTestToExceptional f i g 𝒩)
    (P := @IsOpenImmersion) inferInstance

/-- The base change `C_ZX ×_X T ⟶ N ×_X T` of `ι : C_ZX ⟶ N` is an isomorphism when `ι` is. -/
instance isIso_bivariantPushforwardBaseChange_normalConeEmbedding (𝒩 : VirtualNormalBundle i)
    [IsIso 𝒩.normalConeEmbedding] :
    IsIso (bivariantPushforwardBaseChange 𝒩.normalConeEmbedding (𝒩.projection ≫ i) g) := by
  unfold bivariantPushforwardBaseChange
  infer_instance

end NormalConeTest

/-! ### The test-scheme base changes -/

section TestGeometry

variable {X S Z : Scheme.{u}} (f : X ⟶ S) (i : Z ⟶ X) [IsClosedImmersion i]
  [IsLocallyNoetherian Z] (hi : IsRegularImmersion i) {T : Scheme.{u}} (g : T ⟶ X)


local notation "π∞" =>
  modificationProjectionAtInfinity f (blowupAtInfinityToProjectiveLineProduct (Scheme.Hom.ker i) f)
local notation "𝒩ᵢ" => VirtualNormalBundle.ofIsRegularImmersion i hi
local notation "𝒞ᵢ" =>
  dualSheaf (VirtualNormalBundle.bundle (VirtualNormalBundle.ofIsRegularImmersion i hi))

variable {f i hi} in
/-- The square `E ×_{W_∞} (W_∞ ×_X T) ⟶ Z ×_X T`, `E ×_{W_∞} (W_∞ ×_X T) ⟶ E ⟶ 𝐏(𝒞 ⊕ 𝒪_Z)`
over `Z ×_X T ⟶ Z ⟵ 𝐏(𝒞 ⊕ 𝒪_Z)` is cartesian, for an isomorphism `E ≅ 𝐏(𝒞 ⊕ 𝒪_Z)` over `Z`. -/
theorem isPullback_exceptionalTest (φ : pullback π∞ i ⟶ projectiveCompletion 𝒞ᵢ) [IsIso φ]
    (hφ : φ ≫ projectiveCompletionProj 𝒞ᵢ = pullback.snd π∞ i) :
    IsPullback (exceptionalBaseChangeMap π∞ i g)
      (pullback.fst (pullback.fst π∞ i) (pullback.fst π∞ g) ≫ φ)
      (pullback.fst i g) (projectiveCompletionProj 𝒞ᵢ) := by
  have h := (isPullback_exceptionalBaseChangeMap π∞ i g).flip.paste_vert
    (IsPullback.of_vert_isIso (snd := φ) (f := 𝟙 Z) (g := projectiveCompletionProj 𝒞ᵢ)
      (fst := pullback.snd π∞ i) ⟨by rw [Category.comp_id, hφ]⟩)
  rwa [Category.comp_id] at h

variable {f i hi} in
/-- **`E ×_{W_∞} (W_∞ ×_X T) ≅ (Z ×_X T) ×_Z 𝐏(𝒞 ⊕ 𝒪_Z)`**: over a test scheme `T ⟶ X`, the
base change of `E = W_∞ ×_X Z` is the test scheme of Stacks 0FEF over `Z ×_X T`, through an
isomorphism `E ≅ 𝐏(𝒞 ⊕ 𝒪_Z)` over `Z`. -/
def exceptionalTestIso (φ : pullback π∞ i ⟶ projectiveCompletion 𝒞ᵢ) [IsIso φ]
    (hφ : φ ≫ projectiveCompletionProj 𝒞ᵢ = pullback.snd π∞ i) :
    pullback (pullback.fst π∞ i) (pullback.fst π∞ g) ≅
      pullback (pullback.fst i g) (projectiveCompletionProj 𝒞ᵢ) :=
  (isPullback_exceptionalTest g φ hφ).isoPullback

variable {f i hi} in
/-- The isomorphism `E ×_{W_∞} (W_∞ ×_X T) ≅ (Z ×_X T) ×_Z 𝐏(𝒞 ⊕ 𝒪_Z)` lies over `Z ×_X T`. -/
@[reassoc (attr := simp)]
theorem exceptionalTestIso_hom_fst (φ : pullback π∞ i ⟶ projectiveCompletion 𝒞ᵢ) [IsIso φ]
    (hφ : φ ≫ projectiveCompletionProj 𝒞ᵢ = pullback.snd π∞ i) :
    (exceptionalTestIso g φ hφ).hom ≫ pullback.fst _ _ = exceptionalBaseChangeMap π∞ i g := by
  rw [exceptionalTestIso, IsPullback.isoPullback_hom_fst]

variable {f i hi} in
/-- The isomorphism `E ×_{W_∞} (W_∞ ×_X T) ≅ (Z ×_X T) ×_Z 𝐏(𝒞 ⊕ 𝒪_Z)` lies over
`φ : E ≅ 𝐏(𝒞 ⊕ 𝒪_Z)`. -/
@[reassoc (attr := simp)]
theorem exceptionalTestIso_hom_snd (φ : pullback π∞ i ⟶ projectiveCompletion 𝒞ᵢ) [IsIso φ]
    (hφ : φ ≫ projectiveCompletionProj 𝒞ᵢ = pullback.snd π∞ i) :
    (exceptionalTestIso g φ hφ).hom ≫ pullback.snd _ _ = pullback.fst _ _ ≫ φ := by
  rw [exceptionalTestIso, IsPullback.isoPullback_hom_snd]

/-- The vector bundle `N = 𝐕(𝒞)` of the normal bundle in its projective completion. -/
abbrev normalBundleToCompletion : (𝒩ᵢ).totalSpace ⟶ projectiveCompletion 𝒞ᵢ :=
  toCompletion 𝒞ᵢ

/-- The vector bundle `N ⟶ 𝐏(𝒞 ⊕ 𝒪_Z)` lies over `Z`. -/
@[reassoc]
theorem normalBundleToCompletion_projection :
    normalBundleToCompletion i hi ≫ projectiveCompletionProj 𝒞ᵢ = (𝒩ᵢ).projection :=
  toCompletion_comp_projectiveCompletionProj _

/-- The open immersion `N ×_X T ⟶ (Z ×_X T) ×_Z 𝐏(𝒞 ⊕ 𝒪_Z)`, the base change of the vector
bundle `N = 𝐕(𝒞)` in its projective completion along the test scheme. -/
def bundleTestToCompletion :
    pullback ((𝒩ᵢ).projection ≫ i) g ⟶
      pullback (pullback.fst i g) (projectiveCompletionProj 𝒞ᵢ) :=
  pullback.lift (bundleTestBaseChange i (𝒩ᵢ).projection g)
    (pullback.fst ((𝒩ᵢ).projection ≫ i) g ≫ normalBundleToCompletion i hi) (by
      rw [bundleTestBaseChange_fst, Category.assoc, normalBundleToCompletion_projection])

/-- `N ×_X T ⟶ (Z ×_X T) ×_Z 𝐏(𝒞 ⊕ 𝒪_Z)` lies over `Z ×_X T`. -/
@[reassoc (attr := simp)]
theorem bundleTestToCompletion_fst :
    bundleTestToCompletion i hi g ≫ pullback.fst _ _ = bundleTestBaseChange i (𝒩ᵢ).projection g :=
  pullback.lift_fst _ _ _

/-- `N ×_X T ⟶ (Z ×_X T) ×_Z 𝐏(𝒞 ⊕ 𝒪_Z)` lies over `N ⟶ 𝐏(𝒞 ⊕ 𝒪_Z)`. -/
@[reassoc (attr := simp)]
theorem bundleTestToCompletion_snd :
    bundleTestToCompletion i hi g ≫ pullback.snd _ _ =
      pullback.fst ((𝒩ᵢ).projection ≫ i) g ≫ normalBundleToCompletion i hi :=
  pullback.lift_snd _ _ _

/-- The square `N ×_X T ⟶ N`, `N ×_X T ⟶ (Z ×_X T) ×_Z 𝐏(𝒞 ⊕ 𝒪_Z)` over `N ⟶ 𝐏(𝒞 ⊕ 𝒪_Z)` is
cartesian. -/
theorem isPullback_bundleTestToCompletion :
    IsPullback (pullback.fst ((𝒩ᵢ).projection ≫ i) g) (bundleTestToCompletion i hi g)
      (normalBundleToCompletion i hi)
      (pullback.snd (pullback.fst i g) (projectiveCompletionProj 𝒞ᵢ)) := by
  refine IsPullback.of_bot ?_ (bundleTestToCompletion_snd i hi g).symm
    (IsPullback.of_hasPullback (pullback.fst i g) (projectiveCompletionProj 𝒞ᵢ)).flip
  rw [bundleTestToCompletion_fst, normalBundleToCompletion_projection]
  exact isPullback_bundleTestBaseChange i (𝒩ᵢ).projection g

/-- The open `V' ⊆ (Z ×_X T) ×_Z 𝐏(𝒞 ⊕ 𝒪_Z)` sits in a cartesian square over
`N ⟶ 𝐏(𝒞 ⊕ 𝒪_Z)`. -/
theorem isPullback_complementOpenBaseChange :
    IsPullback
      (pullback.snd (pullback.fst i g) (projectiveCompletionProj 𝒞ᵢ) ∣_ complementOpen 𝒞ᵢ ≫
        (complementIso 𝒞ᵢ).inv)
      (complementOpenBaseChange (pullback.fst i g) 𝒞ᵢ).ι (normalBundleToCompletion i hi)
      (pullback.snd (pullback.fst i g) (projectiveCompletionProj 𝒞ᵢ)) := by
  have h := (isPullback_morphismRestrict
    (pullback.snd (pullback.fst i g) (projectiveCompletionProj 𝒞ᵢ)) (complementOpen 𝒞ᵢ)).paste_horiz
      (IsPullback.of_horiz_isIso (fst := (complementIso 𝒞ᵢ).inv) (g := 𝟙 _)
        (snd := (complementOpen 𝒞ᵢ).ι) (f := normalBundleToCompletion i hi)
        ⟨by rw [Category.comp_id, Iso.inv_comp_eq, complementIso_hom_ι]⟩)
  rwa [Category.comp_id] at h

/-- **`N ×_X T ≅ V'`**: the open `V' ⊆ (Z ×_X T) ×_Z 𝐏(𝒞 ⊕ 𝒪_Z)` of Stacks 0FEF, the base
change of the complement of the divisor at infinity, is the base change `N ×_X T` of the vector
bundle. -/
def bundleTestIsoComplement :
    pullback ((𝒩ᵢ).projection ≫ i) g ≅ (complementOpenBaseChange (pullback.fst i g) 𝒞ᵢ).toScheme :=
  (isPullback_bundleTestToCompletion i hi g).isoIsPullback _ _
    (isPullback_complementOpenBaseChange i hi g)

/-- The isomorphism `N ×_X T ≅ V'` followed by the inclusion of `V'` is
`N ×_X T ⟶ (Z ×_X T) ×_Z 𝐏(𝒞 ⊕ 𝒪_Z)`. -/
@[reassoc (attr := simp)]
theorem bundleTestIsoComplement_hom_ι :
    (bundleTestIsoComplement i hi g).hom ≫ (complementOpenBaseChange (pullback.fst i g) 𝒞ᵢ).ι =
      bundleTestToCompletion i hi g :=
  IsPullback.isoIsPullback_hom_snd _ _ (isPullback_bundleTestToCompletion i hi g)
    (isPullback_complementOpenBaseChange i hi g)

variable {f i hi} in
/-- **The normal cone over the test scheme, in the two test schemes of Stacks 0FEF**: for an
isomorphism `φ : E ≅ 𝐏(𝒞 ⊕ 𝒪_Z)` over `Z` under which `C_ZX ⟶ E` is `C_ZX ⟶ N ⟶ 𝐏(𝒞 ⊕ 𝒪_Z)`,
the base change of `C_ZX ⟶ N ⟶ 𝐏(𝒞 ⊕ 𝒪_Z)` agrees with that of `C_ZX ⟶ E ≅ 𝐏(𝒞 ⊕ 𝒪_Z)`, as
morphisms `C_ZX ×_X T ⟶ (Z ×_X T) ×_Z 𝐏(𝒞 ⊕ 𝒪_Z)`. -/
theorem bivariantPushforwardBaseChange_comp_bundleTestToCompletion
    (φ : pullback π∞ i ⟶ projectiveCompletion 𝒞ᵢ) [IsIso φ]
    (hφ : φ ≫ projectiveCompletionProj 𝒞ᵢ = pullback.snd π∞ i)
    (hcone : normalConeToExceptionalFibre f i ≫ φ =
      (𝒩ᵢ).normalConeEmbedding ≫ normalBundleToCompletion i hi) :
    bivariantPushforwardBaseChange (𝒩ᵢ).normalConeEmbedding ((𝒩ᵢ).projection ≫ i) g ≫
        bundleTestToCompletion i hi g =
      normalConeTestToExceptional f i g 𝒩ᵢ ≫ (exceptionalTestIso g φ hφ).hom := by
  refine pullback.hom_ext (pullback.hom_ext ?_ ?_) ?_
  · simp only [Category.assoc, bundleTestToCompletion_fst, bundleTestBaseChange_fst,
      bivariantPushforwardBaseChange_fst_assoc, exceptionalTestIso_hom_fst_assoc,
      exceptionalBaseChangeMap_fst, normalConeTestToExceptional_fst_assoc,
      normalConeToExceptionalFibre_snd, VirtualNormalBundle.normalConeEmbedding_projection]
  · simp only [Category.assoc, bundleTestToCompletion_fst, bundleTestBaseChange_snd,
      bivariantPushforwardBaseChange_snd, exceptionalTestIso_hom_fst_assoc,
      exceptionalBaseChangeMap_snd, normalConeTestToExceptional_snd_assoc]
    simp
  · simp only [Category.assoc, bundleTestToCompletion_snd, bivariantPushforwardBaseChange_fst_assoc,
      exceptionalTestIso_hom_snd, normalConeTestToExceptional_fst_assoc, hcone]

/-- An isomorphism `φ : E ≅ 𝐏(𝒞 ⊕ 𝒪_Z)` over `Z` is compatible with the structure morphisms to
the base. -/
private theorem comp_structure_of_isoProjectiveCompletion
    (φ : pullback π∞ i ⟶ projectiveCompletion 𝒞ᵢ)
    (hφ : φ ≫ projectiveCompletionProj 𝒞ᵢ = pullback.snd π∞ i) :
    φ ≫ (projectiveCompletionProj 𝒞ᵢ ≫ i ≫ f) = pullback.fst π∞ i ≫ π∞ ≫ f := by
  rw [reassoc_of% hφ, ← pullback.condition_assoc (f := π∞) (g := i)]

end TestGeometry

/-! ### Restriction to opens and pushforward -/

section Restriction

variable (C : ChowSituation.{u}) {A B B' : Scheme.{u}}

/-- Restriction of Chow classes along open immersions depends on the structure morphisms, the
open immersion, the degree and the class only up to equality and heterogeneous equality. -/
theorem chowGroupRestrict_heq_of_eq {sA sA' : A ⟶ C.S} [LocallyOfFiniteType sA]
    [LocallyOfFiniteType sA'] {sB sB' : B ⟶ C.S} [LocallyOfFiniteType sB]
    [LocallyOfFiniteType sB'] (v v' : B ⟶ A) [IsOpenImmersion v] [IsOpenImmersion v']
    (hsA : sA = sA') (hsB : sB = sB') (hvv' : v = v') (hv : v ≫ sA = sB) (hv' : v' ≫ sA' = sB')
    {k k' : ℤ} (hk : k = k') (x : chowGroup C sA k) (x' : chowGroup C sA' k') (hx : x ≍ x') :
    chowGroupRestrict C sA sB v hv k x ≍ chowGroupRestrict C sA' sB' v' hv' k' x' := by
  subst hsA hsB hvv' hk
  cases hx
  rfl

/-- **Restriction to an open subscheme disjoint from the image of a proper morphism kills the
pushforward**: by the open-immersion case of Stacks 02RG it is the pushforward of a class on the
empty fibre product. -/
theorem chowGroupRestrict_properChowPushforward_eq_zero (sA : A ⟶ C.S) [LocallyOfFiniteType sA]
    (sB : B ⟶ C.S) [LocallyOfFiniteType sB] (sB' : B' ⟶ C.S) [LocallyOfFiniteType sB']
    (q : A ⟶ B) [IsProper q] (hq : q ≫ sB = sA) (m : B' ⟶ B) [IsOpenImmersion m]
    (hm : m ≫ sB = sB') (hdisj : Disjoint (Set.range q.base) (Set.range m.base)) (k : ℤ)
    (hfac : ProperPushforwardFactorsThroughRationalEquivalence C sA sB q hq k)
    (α : chowGroup C sA k) :
    chowGroupRestrict C sB sB' m hm k (properChowPushforward C sA sB q hq k hfac α) = 0 := by
  have : IsEmpty ↥(pullback q m) := ⟨fun x ↦ by
    refine Set.disjoint_left.mp hdisj ⟨(pullback.fst q m).base x, rfl⟩
      ⟨(pullback.snd q m).base x, ?_⟩
    rw [← Scheme.Hom.comp_apply, ← Scheme.Hom.comp_apply, pullback.condition]⟩
  rw [chowGroupRestrict_properChowPushforward C sA sB (pullback.snd q m ≫ sB') sB' q hq
    (pullback.fst q m) (by rw [← hq, ← hm, ← Category.assoc, pullback.condition, Category.assoc])
    m hm (pullback.snd q m) rfl (IsPullback.of_hasPullback q m) k hfac
    (properPushforwardDescends C _ _ _ _ _) α]
  rw [(subsingleton_chowGroup_of_isEmpty C (pullback.snd q m ≫ sB') k).elim
    (chowGroupRestrict C sA _ (pullback.fst q m) _ k α) 0, map_zero]

/-- **Restriction to an open subscheme through which the open immersion factors, of a
pushforward along a monomorphism**: if `m = u ≫ q` with `q` proper and a monomorphism and `u` an
open immersion, restricting `q_* α` along `m` is restricting `α` along `u`. This is the
open-immersion case of Stacks 02RG for the cartesian square `u, 𝟙, q, m`. -/
theorem chowGroupRestrict_properChowPushforward_of_comp_eq (sA : A ⟶ C.S)
    [LocallyOfFiniteType sA] (sB : B ⟶ C.S) [LocallyOfFiniteType sB] (sB' : B' ⟶ C.S)
    [LocallyOfFiniteType sB'] (q : A ⟶ B) [IsProper q] [Mono q] (hq : q ≫ sB = sA)
    (m : B' ⟶ B) [IsOpenImmersion m] (hm : m ≫ sB = sB') (u : B' ⟶ A) [IsOpenImmersion u]
    (hu : u ≫ sA = sB') (huq : u ≫ q = m) (k : ℤ)
    (hfac : ProperPushforwardFactorsThroughRationalEquivalence C sA sB q hq k)
    (α : chowGroup C sA k) :
    chowGroupRestrict C sB sB' m hm k (properChowPushforward C sA sB q hq k hfac α) =
      chowGroupRestrict C sA sB' u hu k α := by
  rw [chowGroupRestrict_properChowPushforward C sA sB sB' sB' q hq u hu m hm (𝟙 B')
    (Category.id_comp _) (IsPullback.of_vert_isIso_mono ⟨by rw [huq, Category.id_comp]⟩) k hfac
    (properPushforwardDescends C _ _ _ _ _) α]
  exact chowPush_id C sB' k _

end Restriction

/-! ### Chern classes of isomorphic pullbacks on test schemes -/

section ChernTransport

attribute [local instance 10000] HasDerivedCategory.standard

variable (C : ChowSituation.{u}) {Y W P : Scheme.{u}} (sW : W ⟶ C.S) [LocallyOfFiniteType sW]
  (sP : P ⟶ C.S) [LocallyOfFiniteType sP]

/-- **The Chern classes of two objects whose pullbacks to `Y` agree operate alike on test schemes
over `Y`.** For `e : Y ⟶ W` and `φ : Y ⟶ P` over the base and `Le^*Q ≅ Lφ^*G`, the operation of
`c_p(Q)` on `T ⟶ Y ⟶ W` is that of `c_p(G)` on `T ⟶ Y ⟶ P`: both are the operation of
`c_p(Le^*Q) = c_p(Lφ^*G)` on `T ⟶ Y`, Chern classes commuting with restriction. -/
theorem perfectChernClass_idRule_heq_of_derivedPullback_iso {Q : DerivedCategory W.Modules}
    (hQ : HasDefinedChernClasses Q) {G : DerivedCategory P.Modules} (hG : HasDefinedChernClasses G)
    (e : Y ⟶ W) [LocallyOfFiniteType e] (φ : Y ⟶ P) [LocallyOfFiniteType φ]
    (hφ : φ ≫ sP = e ≫ sW)
    (ψ : (Cohomology.DerivedAdjunctionOnRingedSpaces.derivedPullback e.toLRSHom.toShHom).obj Q ≅
      (Cohomology.DerivedAdjunctionOnRingedSpaces.derivedPullback φ.toLRSHom.toShHom).obj G)
    (p : ℕ) {T : Scheme.{u}} (y : T ⟶ Y) [LocallyOfFiniteType y] [LocallyOfFiniteType (y ≫ e)]
    [LocallyOfFiniteType (y ≫ φ)] (k : ℤ) (γ : chowGroup C ((y ≫ e) ≫ sW) k)
    (γ' : chowGroup C ((y ≫ φ) ≫ sP) k) (hγ : γ ≍ γ') :
    (perfectChernClass C sW hQ p).idRule C sW (gysinSystemOfInvertible C) (y ≫ e) k γ ≍
      (perfectChernClass C sP hG p).idRule C sP (gysinSystemOfInvertible C) (y ≫ φ) k γ' := by
  have hQE := hQ.derivedPullback e
  have hGE := hG.derivedPullback φ
  have hs : (y ≫ e) ≫ sW = y ≫ e ≫ sW := Category.assoc _ _ _
  set γ₀ := chowGroupCongr C hs k γ
  have hγ₀ : γ₀ ≍ γ := chowGroupCongr_heq C hs k γ
  refine (TotalChowClass.op_res_apply e rfl (perfectChernClass C sW hQ) y k p γ₀ γ
    hγ₀).symm.trans ?_
  rw [res_perfectChernClass_derivedPullback_of_comp_eq C sW hQ e rfl hQE,
    perfectChernClass_congr C (e ≫ sW) hQE hGE ψ,
    ← res_perfectChernClass_derivedPullback_of_comp_eq C sP hG φ hφ hGE]
  exact TotalChowClass.op_res_apply φ hφ (perfectChernClass C sP hG) y k p γ₀ γ'
    (hγ₀.trans hγ)

end ChernTransport

/-! ### Stacks 0FEF in every degree -/

section ZeroSectionDegree

attribute [local instance 10000] HasDerivedCategory.standard

variable (C : ChowSituation.{u}) {X X' : Scheme.{u}} (sX : X ⟶ C.S) [LocallyOfFiniteType sX]
  (𝒞 : X.Modules) (r : ℕ) [SheafOfModules.IsFiniteLocallyFreeOfRank.{u, u, u} 𝒞 r]
  [SheafOfModules.IsFiniteLocallyFree.{u, u, u} 𝒞] (sX' : X' ⟶ C.S) [LocallyOfFiniteType sX']
  (g : X' ⟶ X) [LocallyOfFiniteType g] (hg : g ≫ sX = sX')

/-- **The cap-product identity of Stacks 0FEF on a test scheme `X' ×_X E`, in every degree**:
`p'^*(π'_*(c_r(i_*𝒪_X) ∩ α)) = (-1)^{r-1}(r-1)! α|_{V'}` for `α ∈ CH_d(X' ×_X E)`, the third
clause of `Stacks.Chow.chernClass_pushforward_zeroSection` read without writing `d` as
`k + r`. The two sides lie in the degrees `(d - r) + r` and `d`. -/
theorem bundlePullback_perfectChernClass_pushforward_zeroSection_heq (hr : r ≠ 0) (d : ℤ)
    (α : chowGroup C (pullback.snd g (projectiveCompletionProj 𝒞) ≫
      projectiveCompletionProj 𝒞 ≫ sX) d) :
    haveI := flat_projectiveCompletionProj 𝒞 r
    haveI := locallyOfFiniteType_projectiveCompletionProj 𝒞 r
    bundlePullback C sX'
        ((complementOpenBaseChange g 𝒞).ι ≫ pullback.snd g (projectiveCompletionProj 𝒞) ≫
          projectiveCompletionProj 𝒞 ≫ sX)
        ((complementOpenBaseChange g 𝒞).ι ≫ pullback.fst g (projectiveCompletionProj 𝒞))
        (by rw [Category.assoc, pullback_fst_comp_eq_pullback_snd_comp C sX sX' g hg 𝒞]) r
        (relativeDimension_complementOpenBaseChange g 𝒞 r) (d - r)
        (properChowPushforward C
          (pullback.snd g (projectiveCompletionProj 𝒞) ≫ projectiveCompletionProj 𝒞 ≫ sX) sX'
          (pullback.fst g (projectiveCompletionProj 𝒞))
          (pullback_fst_comp_eq_pullback_snd_comp C sX sX' g hg 𝒞) (d - r)
          (properPushforwardDescends C _ _ _ _ _)
          ((perfectChernClass C (projectiveCompletionProj 𝒞 ≫ sX)
            (hasDefinedChernClasses_pushforward_zeroSection 𝒞 r) r).idRule C _
            (gysinSystemOfInvertible C) (pullback.snd g (projectiveCompletionProj 𝒞)) d α)) ≍
      ((-1 : ℤ) ^ (r - 1) * (Nat.factorial (r - 1) : ℤ)) •
        chowGroupOpensRestrictOfIsOpenImmersion C
          (pullback.snd g (projectiveCompletionProj 𝒞) ≫ projectiveCompletionProj 𝒞 ≫ sX)
          (complementOpenBaseChange g 𝒞) d α := by
  have := flat_projectiveCompletionProj 𝒞 r
  have := locallyOfFiniteType_projectiveCompletionProj 𝒞 r
  have hd : d = d - r + r := by ring
  set α' := chowGroupCast C _ hd α
  have hα : α ≍ α' := (chowGroupCast_heq C _ hd α).symm
  have H := (chernClass_pushforward_zeroSection C sX 𝒞 r hr).2.2 sX' g hg (d - r) α'
  refine HEq.trans ?_ ((chowGroupCast_heq C _ _ _).symm.trans ((heq_of_eq H).trans ?_))
  · refine heq_map_index (by ring : d - r = d - r + r - r) ?_ fun n x ↦ bundlePullback C sX'
      ((complementOpenBaseChange g 𝒞).ι ≫ pullback.snd g (projectiveCompletionProj 𝒞) ≫
        projectiveCompletionProj 𝒞 ≫ sX)
      ((complementOpenBaseChange g 𝒞).ι ≫ pullback.fst g (projectiveCompletionProj 𝒞))
      (by rw [Category.assoc, pullback_fst_comp_eq_pullback_snd_comp C sX sX' g hg 𝒞]) r
      (relativeDimension_complementOpenBaseChange g 𝒞 r) n x
    refine properChowPushforward_heq_congr C _ _ _ _ (by ring) _ _ _ _ ?_
    exact heq_map_index hd hα fun n x ↦ (perfectChernClass C (projectiveCompletionProj 𝒞 ≫ sX)
      (hasDefinedChernClasses_pushforward_zeroSection 𝒞 r) r).idRule C _
      (gysinSystemOfInvertible C) (pullback.snd g (projectiveCompletionProj 𝒞)) n x
  · exact heq_map_index hd.symm hα.symm fun n x ↦
      ((-1 : ℤ) ^ (r - 1) * (Nat.factorial (r - 1) : ℤ)) •
        chowGroupOpensRestrictOfIsOpenImmersion C
          (pullback.snd g (projectiveCompletionProj 𝒞) ≫ projectiveCompletionProj 𝒞 ≫ sX)
          (complementOpenBaseChange g 𝒞) n x

end ZeroSectionDegree

/-! ### The top Chern class on the exceptional divisor over a test scheme -/

section ExceptionalTop

attribute [local instance 10000] HasDerivedCategory.standard

variable (C : ChowSituation.{u}) {X Z : Scheme.{u}} (sX : X ⟶ C.S) [LocallyOfFiniteType sX]
  (i : Z ⟶ X) [IsClosedImmersion i] [IsLocallyNoetherian Z] (hi : IsRegularImmersion i) (r : ℕ)
  [SheafOfModules.IsFiniteLocallyFreeOfRank.{u, u, u}
    (VirtualNormalBundle.ofIsRegularImmersion i hi).bundle r]
  {T : Scheme.{u}} (g : T ⟶ X) [LocallyOfFiniteType g]

local notation "π∞" =>
  modificationProjectionAtInfinity sX
    (blowupAtInfinityToProjectiveLineProduct (Scheme.Hom.ker i) sX)
local notation "𝒩ᵢ" => VirtualNormalBundle.ofIsRegularImmersion i hi
local notation "𝒞ᵢ" =>
  dualSheaf (VirtualNormalBundle.bundle (VirtualNormalBundle.ofIsRegularImmersion i hi))

/-- **Stacks 0FEF on the exceptional divisor over a test scheme.** Let `φ : E ≅ 𝐏(𝒞 ⊕ 𝒪_Z)` be
an isomorphism over `Z` under which the open immersion `C_ZX ⟶ E` of Stacks 0FBH is
`C_ZX ⟶ N ⟶ 𝐏(𝒞 ⊕ 𝒪_Z)`, and let `T ⟶ X` be a test scheme, `E_T = E ×_{W_∞} (W_∞ ×_X T)`. For
`β ∈ CH_k(E_T)`, flat pullback along `N ×_X T ⟶ Z ×_X T` of the pushforward along
`E_T ⟶ Z ×_X T` of `c_r(i_*𝒪) ∩ β` (with `i : Z ⟶ 𝐏(𝒞 ⊕ 𝒪_Z)` the zero section, the cap
product taken on `E_T ⟶ E ⟶ 𝐏(𝒞 ⊕ 𝒪_Z)`) is `(-1)^{r-1}(r-1)!` times the pushforward along
`C_ZX ×_X T ≅ N ×_X T` of the restriction of `β` to the open `C_ZX ×_X T ⊆ E_T`. The two sides
lie in the degrees `(k - r) + r` and `k`. -/
theorem bundleFlatPullbackChow_perfectChernClass_exceptionalTest (hr : r ≠ 0)
    (φ : pullback π∞ i ⟶ projectiveCompletion 𝒞ᵢ) [IsIso φ]
    (hφ : φ ≫ projectiveCompletionProj 𝒞ᵢ = pullback.snd π∞ i)
    (hcone : normalConeToExceptionalFibre sX i ≫ φ =
      (𝒩ᵢ).normalConeEmbedding ≫ normalBundleToCompletion i hi) (k : ℤ)
    (β : chowGroup C (pullback.fst (pullback.fst π∞ i) (pullback.fst π∞ g) ≫
      (pullback.fst π∞ i ≫ π∞ ≫ sX)) k)
    (γ : chowGroup C ((pullback.fst (pullback.fst π∞ i) (pullback.fst π∞ g) ≫ φ) ≫
      (projectiveCompletionProj 𝒞ᵢ ≫ i ≫ sX)) k) (hγ : γ ≍ β) :
    haveI := flat_projectiveCompletionProj 𝒞ᵢ r
    haveI := locallyOfFiniteType_projectiveCompletionProj 𝒞ᵢ r
    haveI := locallyOfFiniteType_normalConeToBase C sX i
    bundleFlatPullbackChow C (i ≫ sX) ((𝒩ᵢ).projection ≫ i ≫ sX) i (𝒩ᵢ).projection rfl r
        ((𝒩ᵢ).flat_projection_of_rank r) ((𝒩ᵢ).relativeDimension_projection_of_rank r)
        (flatPullbackDescends C) g (k - r)
        (chowPush C _ (pullback.fst i g ≫ i ≫ sX) (exceptionalBaseChangeMap π∞ i g)
          (by rw [← Category.assoc, exceptionalBaseChangeMap_fst, Category.assoc,
            ← reassoc_of% hφ, Category.assoc]) (k - r)
          ((perfectChernClass C (projectiveCompletionProj 𝒞ᵢ ≫ i ≫ sX)
            (hasDefinedChernClasses_pushforward_zeroSection 𝒞ᵢ r) r).idRule C _
            (gysinSystemOfInvertible C)
            (pullback.fst (pullback.fst π∞ i) (pullback.fst π∞ g) ≫ φ) k γ)) ≍
      ((-1 : ℤ) ^ (r - 1) * ((r - 1).factorial : ℤ)) •
        chowPush C (pullback.fst ((𝒩ᵢ).normalConeEmbedding ≫ (𝒩ᵢ).projection ≫ i) g ≫
            (Stacks.Conormal.normalConeToBase i ≫ i ≫ sX))
          (pullback.fst ((𝒩ᵢ).projection ≫ i) g ≫ ((𝒩ᵢ).projection ≫ i ≫ sX))
          (bivariantPushforwardBaseChange (𝒩ᵢ).normalConeEmbedding ((𝒩ᵢ).projection ≫ i) g)
          (bivariantPushforwardBaseChange_comp_structure
            (by rw [(𝒩ᵢ).normalConeEmbedding_projection_assoc]) ((𝒩ᵢ).projection ≫ i) g) k
          (chowGroupRestrict C _ _ (normalConeTestToExceptional sX i g 𝒩ᵢ)
            (normalConeTestToExceptional_comp_projection_assoc sX i g 𝒩ᵢ sX) k β) := by
  have := flat_projectiveCompletionProj 𝒞ᵢ r
  have := locallyOfFiniteType_projectiveCompletionProj 𝒞ᵢ r
  have := locallyOfFiniteType_normalConeToBase C sX i
  have := VirtualNormalBundle.isIso_normalConeEmbedding_ofIsRegularImmersion hi
  have := (𝒩ᵢ).flat_projection_of_rank r
  have hΦq := exceptionalTestIso_hom_snd g φ hφ
  have hΦπ := exceptionalTestIso_hom_fst g φ hφ
  have hy : (exceptionalTestIso g φ hφ).hom ≫ (pullback.snd (pullback.fst i g)
      (projectiveCompletionProj 𝒞ᵢ) ≫ projectiveCompletionProj 𝒞ᵢ ≫ i ≫ sX) =
      (pullback.fst (pullback.fst π∞ i) (pullback.fst π∞ g) ≫ φ) ≫
        (projectiveCompletionProj 𝒞ᵢ ≫ i ≫ sX) := by
    rw [reassoc_of% hΦq, Category.assoc]
  -- the cap product, pushed forward to `Z ×_X T`, is computed on `(Z ×_X T) ×_Z 𝐏(𝒞 ⊕ 𝒪_Z)`
  have h1 : chowPush C _ (pullback.fst i g ≫ i ≫ sX) (exceptionalBaseChangeMap π∞ i g)
      (by rw [← Category.assoc, exceptionalBaseChangeMap_fst, Category.assoc,
        ← reassoc_of% hφ, Category.assoc]) (k - r)
      ((perfectChernClass C (projectiveCompletionProj 𝒞ᵢ ≫ i ≫ sX)
        (hasDefinedChernClasses_pushforward_zeroSection 𝒞ᵢ r) r).idRule C _
        (gysinSystemOfInvertible C) (pullback.fst (pullback.fst π∞ i) (pullback.fst π∞ g) ≫ φ)
        k γ) =
      chowPush C _ (pullback.fst i g ≫ i ≫ sX)
        (pullback.fst (pullback.fst i g) (projectiveCompletionProj 𝒞ᵢ))
        (pullback_fst_comp_eq_pullback_snd_comp C (i ≫ sX) (pullback.fst i g ≫ i ≫ sX)
          (pullback.fst i g) rfl 𝒞ᵢ) (k - r)
        ((perfectChernClass C (projectiveCompletionProj 𝒞ᵢ ≫ i ≫ sX)
          (hasDefinedChernClasses_pushforward_zeroSection 𝒞ᵢ r) r).idRule C _
          (gysinSystemOfInvertible C) (pullback.snd (pullback.fst i g)
            (projectiveCompletionProj 𝒞ᵢ)) k
          (chowPush C _ _ (exceptionalTestIso g φ hφ).hom hy k γ)) := by
    rw [BivariantClass.idRule_chowPush C (gysinSystemOfInvertible C) _ _ _
      (exceptionalTestIso g φ hφ).hom _ hΦq k γ]
    exact (chowPush_comp C _ _ _ _ _ _ hΦπ _ _ _ (k - r) _).symm
  rw [h1]
  set y := chowPush C _ _ (exceptionalTestIso g φ hφ).hom hy k γ with hydef
  set V := complementOpenBaseChange (pullback.fst i g) 𝒞ᵢ
  set Ψ := bundleTestIsoComplement i hi g
  have H := bundlePullback_perfectChernClass_pushforward_zeroSection_heq C (i ≫ sX) 𝒞ᵢ r
    (pullback.fst i g ≫ i ≫ sX) (pullback.fst i g) rfl hr k y
  have hcomp : bundleTestBaseChange i (𝒩ᵢ).projection g =
      Ψ.hom ≫ (V.ι ≫ pullback.fst (pullback.fst i g) (projectiveCompletionProj 𝒞ᵢ)) := by
    rw [← Category.assoc, bundleTestIsoComplement_hom_ι, bundleTestToCompletion_fst]
  have hΨ : Ψ.hom ≫ (V.ι ≫ pullback.snd (pullback.fst i g) (projectiveCompletionProj 𝒞ᵢ) ≫
      projectiveCompletionProj 𝒞ᵢ ≫ i ≫ sX) =
      pullback.fst ((𝒩ᵢ).projection ≫ i) g ≫ ((𝒩ᵢ).projection ≫ i ≫ sX) := by
    rw [bundleTestIsoComplement_hom_ι_assoc, bundleTestToCompletion_snd_assoc,
      normalBundleToCompletion_projection_assoc]
  have hΨ0 : AlgebraicGeometry.RelativeDimension Ψ.hom 0 := relativeDimension_of_isOpenImmersion _
  have hVr := relativeDimension_complementOpenBaseChange (pullback.fst i g) 𝒞ᵢ r
  have := locallyOfFiniteType_bundleTestBaseChange i (𝒩ᵢ).projection g
  have := flat_bundleTestBaseChange i (𝒩ᵢ).projection ((𝒩ᵢ).flat_projection_of_rank r) g
  unfold bundleFlatPullbackChow
  have hcs : (Ψ.hom ≫ (V.ι ≫ pullback.fst (pullback.fst i g) (projectiveCompletionProj 𝒞ᵢ))) ≫
      (pullback.fst i g ≫ i ≫ sX) =
      pullback.fst ((𝒩ᵢ).projection ≫ i) g ≫ ((𝒩ᵢ).projection ≫ i ≫ sX) := by
    rw [← hcomp]
    exact bundleTestBaseChange_comp_structureMorphism i _ _ _ rfl g
  refine (flatPullbackChow_heq_congr C _ _ _ _ _ hcs hcomp (zero_add r).symm _
    (hΨ0.comp_of_flat _ _ hVr) rfl _ (flatPullbackDescends C _ _ _ _ _ _ _) _ _ HEq.rfl).trans ?_
  refine (flatPullbackChow_comp C _ _ _ Ψ.hom _ hΨ (by rw [Category.assoc,
    pullback_fst_comp_eq_pullback_snd_comp C (i ≫ sX) (pullback.fst i g ≫ i ≫ sX)
      (pullback.fst i g) rfl 𝒞ᵢ]) 0 r hΨ0 hVr (k - r)
    (flatPullbackDescends C _ _ _ _ _ _ _) (flatPullbackDescends C _ _ _ _ _ _ _)
    (flatPullbackDescends C _ _ _ _ _ _ _) _).symm.trans ?_
  refine (heq_chowGroupRestrict_flatPullbackChow C _ _ Ψ.hom hΨ hΨ0 _
    (flatPullbackDescends C _ _ _ _ _ _ _) _).symm.trans ?_
  refine (chowGroupRestrict_heq_of_eq C Ψ.hom Ψ.hom rfl rfl rfl hΨ hΨ (by ring) _ _ H).trans
    (heq_of_eq ?_)
  rw [map_zsmul]
  congr 1
  have hy' : y = chowGroupRestrict C _ _ (exceptionalTestIso g φ hφ).inv
      (by rw [← hy, Iso.inv_hom_id_assoc]) k γ :=
    chowPushforwardOfIso_hom_eq_chowGroupRestrict C _ _ (exceptionalTestIso g φ hφ) hy k γ
  have hx := chowPushforwardOfIso_hom_eq_chowGroupRestrict C _ _
    (asIso (bivariantPushforwardBaseChange (𝒩ᵢ).normalConeEmbedding ((𝒩ᵢ).projection ≫ i) g))
    (bivariantPushforwardBaseChange_comp_structure
      (by rw [(𝒩ᵢ).normalConeEmbedding_projection_assoc]) ((𝒩ᵢ).projection ≫ i) g) k
    (chowGroupRestrict C _ _ (normalConeTestToExceptional sX i g 𝒩ᵢ)
      (normalConeTestToExceptional_comp_projection_assoc sX i g 𝒩ᵢ sX) k β)
  refine Eq.trans ?_ hx.symm
  change chowGroupRestrict C _ _ Ψ.hom hΨ k (chowGroupRestrict C _ _ V.ι rfl k y) = _
  rw [chowGroupRestrict_comp, hy', chowGroupRestrict_comp]
  refine Eq.trans ?_ (chowGroupRestrict_comp C _ _ _ _ k _ _ _ β).symm
  have hmor : (Ψ.hom ≫ V.ι) ≫ (exceptionalTestIso g φ hφ).inv =
      (asIso (bivariantPushforwardBaseChange (𝒩ᵢ).normalConeEmbedding
        ((𝒩ᵢ).projection ≫ i) g)).inv ≫ normalConeTestToExceptional sX i g 𝒩ᵢ := by
    rw [bundleTestIsoComplement_hom_ι, Iso.eq_inv_comp, asIso_hom,
      reassoc_of% (bivariantPushforwardBaseChange_comp_bundleTestToCompletion g φ hφ hcone),
      Iso.hom_inv_id, Category.comp_id]
  refine eq_of_heq (chowGroupRestrict_heq_of_eq C _ _ ?_ rfl hmor _ _ rfl γ β hγ)
  rw [Category.assoc, comp_structure_of_isoProjectiveCompletion sX i hi φ hφ]

end ExceptionalTop

/-! ### The class `c'_r(Q)` on a test scheme -/

section TopClass

attribute [local instance 10000] HasDerivedCategory.standard

variable (C : ChowSituation.{u}) {X Z : Scheme.{u}} (sX : X ⟶ C.S) [LocallyOfFiniteType sX]
  (i : Z ⟶ X) [IsClosedImmersion i] [IsLocallyNoetherian Z] (hi : IsRegularImmersion i) (r : ℕ)
  [SheafOfModules.IsFiniteLocallyFreeOfRank.{u, u, u}
    (VirtualNormalBundle.ofIsRegularImmersion i hi).bundle r]

local notation "π∞" =>
  modificationProjectionAtInfinity sX
    (blowupAtInfinityToProjectiveLineProduct (Scheme.Hom.ker i) sX)
local notation "ι∞" =>
  modificationInclusionAtInfinity sX (blowupAtInfinityToProjectiveLineProduct (Scheme.Hom.ker i) sX)
local notation "𝒩ᵢ" => VirtualNormalBundle.ofIsRegularImmersion i hi
local notation "𝒞ᵢ" =>
  dualSheaf (VirtualNormalBundle.bundle (VirtualNormalBundle.ofIsRegularImmersion i hi))

/-- **The extension `c'_r(Q|_E)` against `j^*` on a test scheme**, for every class `β` on
`W_∞ ×_X T`: flat pullback along `N ×_X T ⟶ Z ×_X T` of the pushforward to `Z ×_X T` of
`c'_r(Q|_E) ∩ β` is `(-1)^{r-1}(r-1)!` times the pushforward along `C_ZX ×_X T ≅ N ×_X T` of
`β|_{C_ZX ×_X T}`. Both sides are additive in `β`, and `β = a_* β₁ + b_* β₂` along the closed
cover `W_∞ ×_X T = (X' ×_X T) ∪ (E ×_X T)` (Stacks 0F94): the first term goes to zero on both
sides, because the extension vanishes on it and the normal cone misses `X'`; the second is
`Stacks.Chow.bundleFlatPullbackChow_perfectChernClass_exceptionalTest`, because the extension caps
`b_* β₂` as `c_r(Q)|_E = c_r(Le^*Q) = c_r(Lφ^*(i_{0,*}𝒪_Z))` does. -/
theorem bundleFlatPullbackChow_modificationExtension_cap (hr : r ≠ 0)
    {Q : DerivedCategory (blowupAtInfinity (Scheme.Hom.ker i)).Modules}
    (hQ : HasDefinedChernClasses Q)
    (hrank : ∃ M : (strictTransformIdealAtInfinity (Scheme.Hom.ker i)).subscheme.Modules,
      IsFiniteLocallyFreeOfRankLT M r ∧
        Nonempty ((Cohomology.DerivedAdjunctionOnRingedSpaces.derivedPullback
          (strictTransformToFibreAtInfinity sX i ≫ ι∞).toLRSHom.toShHom).obj Q ≅
            (DerivedCategory.singleFunctor _ 0).obj M))
    (φ : pullback π∞ i ⟶ projectiveCompletion 𝒞ᵢ) [IsIso φ]
    (hφ : φ ≫ projectiveCompletionProj 𝒞ᵢ = pullback.snd π∞ i)
    (hcone : normalConeToExceptionalFibre sX i ≫ φ =
      (𝒩ᵢ).normalConeEmbedding ≫ normalBundleToCompletion i hi)
    (ψ : (Cohomology.DerivedAdjunctionOnRingedSpaces.derivedPullback
        (pullback.fst π∞ i ≫ ι∞).toLRSHom.toShHom).obj Q ≅
      (Cohomology.DerivedAdjunctionOnRingedSpaces.derivedPullback φ.toLRSHom.toShHom).obj
        ((DerivedCategory.singleFunctor (projectiveCompletion 𝒞ᵢ).Modules 0).obj
          ((Scheme.Modules.pushforward (Stacks.ProjectiveCompletion.zeroSection 𝒞ᵢ)).obj
            (SheafOfModules.unit (Stacks.Chow.bundle (Stacks.Ample.unitModule Z)).ringCatSheaf))))
    {T : Scheme.{u}} (g : T ⟶ X) [LocallyOfFiniteType g] (k : ℤ)
    (β : chowGroup C (pullback.fst π∞ g ≫ π∞ ≫ sX) k) :
    haveI := locallyOfFiniteType_normalConeToBase C sX i
    chowGroupDegreeEquiv C (pullback.fst ((𝒩ᵢ).projection ≫ i) g ≫ (𝒩ᵢ).projection ≫ i ≫ sX)
        (by ring : k - (r : ℤ) + (r : ℤ) = k + ((0 : ℕ) : ℤ))
        (bundleFlatPullbackChow C (i ≫ sX) ((𝒩ᵢ).projection ≫ i ≫ sX) i (𝒩ᵢ).projection rfl r
          ((𝒩ᵢ).flat_projection_of_rank r) ((𝒩ᵢ).relativeDimension_projection_of_rank r)
          (flatPullbackDescends C) g (k - r)
          (chowPush C _ (pullback.fst i g ≫ (i ≫ sX)) (exceptionalBaseChangeMap π∞ i g)
            (exceptionalBaseChangeMap_comp_structure _ i g sX) (k - r)
            ((modificationExtension i (strictTransformToFibreAtInfinity sX i)
              (mem_range_strictTransformToFibreAtInfinity sX i)
              (vanishesOver_perfectChernClass_of_rankLT C _ _ hQ r hrank)).cap
              (pullback.fst π∞ g) k β))) =
      ((-1 : ℤ) ^ (r - 1) * ((r - 1).factorial : ℤ)) •
        properChowPushforward C
          (pullback.fst ((𝒩ᵢ).normalConeEmbedding ≫ (𝒩ᵢ).projection ≫ i) g ≫
            (Stacks.Conormal.normalConeToBase i ≫ i ≫ sX))
          (pullback.fst ((𝒩ᵢ).projection ≫ i) g ≫ ((𝒩ᵢ).projection ≫ i ≫ sX))
          (bivariantPushforwardBaseChange (𝒩ᵢ).normalConeEmbedding ((𝒩ᵢ).projection ≫ i) g)
          (bivariantPushforwardBaseChange_comp_structure
            (by rw [(𝒩ᵢ).normalConeEmbedding_projection_assoc]) ((𝒩ᵢ).projection ≫ i) g)
          (k + ((0 : ℕ) : ℤ)) (properPushforwardDescends C _ _ _ _ _)
          (flatPullbackChow C _ _ (normalConeTestMap sX i 𝒩ᵢ g)
            (normalConeTestMap_comp_structureMorphism (i ≫ sX) sX i rfl 𝒩ᵢ g) 0
            (relativeDimension_of_isOpenImmersion _) k (flatPullbackDescends C _ _ _ _ _ _ _)
            β) := by
  have := locallyOfFiniteType_normalConeToBase C sX i
  have := VirtualNormalBundle.isIso_normalConeEmbedding_ofIsRegularImmersion hi
  obtain ⟨⟨β₁, β₂⟩, rfl⟩ := surjective_closedCoverPullbackSum C (π∞ ≫ sX)
    (strictTransformToFibreAtInfinity sX i) (pullback.fst π∞ i) _ rfl
    (range_union_range_pullbackFst_eq_univ i (strictTransformToFibreAtInfinity sX i)
      (mem_range_strictTransformToFibreAtInfinity sX i)) (pullback.fst π∞ g) k β
  have key := fun γ : chowGroup C (pullback.fst π∞ g ≫ π∞ ≫ sX) k ↦
    heq_chowGroupRestrict_flatPullbackChow C _ _ (normalConeTestMap sX i 𝒩ᵢ g)
      (normalConeTestMap_comp_structureMorphism (i ≫ sX) sX i rfl 𝒩ᵢ g)
      (relativeDimension_of_isOpenImmersion _) k (flatPullbackDescends C _ _ _ _ _ _ _) γ
  rw [closedCoverSum_apply]
  simp only [map_add, smul_add]
  congr 1
  · -- the strict transform: both sides vanish, the normal cone missing `X'`
    rw [modificationExtension_cap_first, map_zero, map_zero, map_zero]
    have h := key (chowPush C _ _
      (pullback.snd (strictTransformToFibreAtInfinity sX i) (pullback.fst π∞ g))
        (pullbackSnd_comp_structureMorphism rfl _) k β₁)
    rw [chowGroupRestrict_properChowPushforward_eq_zero] at h
    · rw [chowGroup_eq_zero_of_heq_zero C (by ring) h.symm, map_zero, smul_zero]
    · refine Set.disjoint_left.mpr ?_
      rintro _ ⟨a, rfl⟩ ⟨c, hc⟩
      refine Set.disjoint_left.mp (disjoint_range_strictTransformToFibreAtInfinity sX i)
        ⟨(pullback.fst (strictTransformToFibreAtInfinity sX i) (pullback.fst π∞ g)).base a, rfl⟩
        ⟨(pullback.fst ((𝒩ᵢ).normalConeEmbedding ≫ (𝒩ᵢ).projection ≫ i) g).base c, ?_⟩
      have h₁ := congrArg (fun x ↦ (pullback.fst π∞ g).base x) hc
      simp only at h₁
      rw [← Scheme.Hom.comp_apply, ← Scheme.Hom.comp_apply, ← pullback.condition] at h₁
      rw [← Scheme.Hom.comp_apply, ← Scheme.Hom.comp_apply, ← h₁, pullback.lift_fst]
  · -- the exceptional divisor: Stacks 0FEF
    rw [modificationExtension_cap_second]
    set n := pullback.fst (pullback.fst π∞ i) (pullback.fst π∞ g)
    have hs₁ : n ≫ (pullback.fst π∞ i ≫ π∞ ≫ sX) = ((n ≫ pullback.fst π∞ i) ≫ ι∞) ≫
        (modificationProjection sX (blowupAtInfinityToProjectiveLineProduct i.ker sX) ≫ sX) := by
      simp only [Category.assoc]
    have hφs := comp_structure_of_isoProjectiveCompletion sX i hi φ hφ
    have hs₂ : n ≫ (pullback.fst π∞ i ≫ π∞ ≫ sX) = (n ≫ φ) ≫
        (projectiveCompletionProj 𝒞ᵢ ≫ i ≫ sX) := by
      rw [Category.assoc n φ, hφs]
    have hres := modificationRestriction_idRule_heq i
      (perfectChernClass C (modificationProjection sX
        (blowupAtInfinityToProjectiveLineProduct i.ker sX) ≫ sX) hQ r) n k β₂
      (chowGroupCongr C hs₁ k β₂) (chowGroupCongr_heq C hs₁ k β₂).symm
    have hφ' : φ ≫ (projectiveCompletionProj 𝒞ᵢ ≫ i ≫ sX) = (pullback.fst π∞ i ≫ ι∞) ≫
        (modificationProjection sX (blowupAtInfinityToProjectiveLineProduct i.ker sX) ≫ sX) := by
      rw [hφs]
      simp only [Category.assoc]
    have htr := perfectChernClass_idRule_heq_of_derivedPullback_iso C
      (modificationProjection sX (blowupAtInfinityToProjectiveLineProduct i.ker sX) ≫ sX)
      (projectiveCompletionProj 𝒞ᵢ ≫ i ≫ sX) hQ
      (hasDefinedChernClasses_pushforward_zeroSection 𝒞ᵢ r) (pullback.fst π∞ i ≫ ι∞) φ hφ' ψ r n
      k (chowGroupCongr C (by rw [hs₁, Category.assoc n]) k β₂) (chowGroupCongr C hs₂ k β₂)
      ((chowGroupCongr_heq C _ k β₂).trans (chowGroupCongr_heq C hs₂ k β₂).symm)
    have hcong := BivariantClass.idRule_heq_congr (perfectChernClass C (modificationProjection sX
        (blowupAtInfinityToProjectiveLineProduct i.ker sX) ≫ sX) hQ r)
      (Category.assoc n (pullback.fst π∞ i) ι∞) k (chowGroupCongr C hs₁ k β₂)
      (chowGroupCongr C (by rw [hs₁, Category.assoc n]) k β₂)
      ((chowGroupCongr_heq C hs₁ k β₂).trans (chowGroupCongr_heq C _ k β₂).symm)
    have hE := bundleFlatPullbackChow_perfectChernClass_exceptionalTest C sX i hi r g hr φ hφ hcone
      k β₂ (chowGroupCongr C hs₂ k β₂) (chowGroupCongr_heq C hs₂ k β₂)
    have h2 := key (chowPush C _ _ (pullback.snd (pullback.fst π∞ i) (pullback.fst π∞ g))
      (pullbackSnd_comp_structureMorphism rfl _) k β₂)
    have h3 := chowGroupRestrict_properChowPushforward_of_comp_eq C
      (n ≫ (pullback.fst π∞ i ≫ π∞ ≫ sX)) (pullback.fst π∞ g ≫ π∞ ≫ sX)
      (pullback.fst ((𝒩ᵢ).normalConeEmbedding ≫ (𝒩ᵢ).projection ≫ i) g ≫
        (Stacks.Conormal.normalConeToBase i ≫ i ≫ sX))
      (pullback.snd (pullback.fst π∞ i) (pullback.fst π∞ g))
      (pullbackSnd_comp_structureMorphism rfl _) (normalConeTestMap sX i 𝒩ᵢ g)
      (normalConeTestMap_comp_structureMorphism (i ≫ sX) sX i rfl 𝒩ᵢ g)
      (normalConeTestToExceptional sX i g 𝒩ᵢ)
      (normalConeTestToExceptional_comp_projection_assoc sX i g 𝒩ᵢ sX)
      (normalConeTestToExceptional_snd sX i g 𝒩ᵢ) k (properPushforwardDescends C _ _ _ _ _) β₂
    rw [h3] at h2
    refine eq_of_heq ((chowGroupDegreeEquiv_heq C _ _ _).trans (HEq.trans ?_ (hE.trans
      (heq_map_index (by ring) (properChowPushforward_heq_congr C _ _ _ _ (by ring) _ _ _ _ h2)
        fun n x ↦ ((-1 : ℤ) ^ (r - 1) * ((r - 1).factorial : ℤ)) • x))))
    refine heq_of_eq (congrArg _ (eq_of_heq (chowPush_heq C _ _ _ hs₂ rfl rfl ?_)))
    exact hres.trans (hcong.trans htr)

/-- **`p^*(c'_r(Q) ∩ α) = (-1)^{r-1}(r-1)! ι_* j^*(C ∩ α)` on every test scheme**, the
computation of the proof of Stacks 0FEG. Let `i : Z ⟶ X` be a regular closed immersion whose
normal bundle has rank `r ≥ 1`, `W` the blowup of `𝐏¹_X` in `∞(Z)`, `E = W_∞ ×_X Z`,
`e : E ⟶ W_∞ ⟶ W`, and let `φ : E ≅ 𝐏(𝒞 ⊕ 𝒪_Z)` be an isomorphism over `Z` under which the open
immersion `C_ZX ⟶ E` is `C_ZX ⟶ N ⟶ 𝐏(𝒞 ⊕ 𝒪_Z)`. If `Le^*Q ≅ Lφ^*(i_{0,*}𝒪_Z)` for the zero
section `i_0`, then on every test scheme `T ⟶ X`, flat pullback along `N ×_X T ⟶ Z ×_X T` of
`c'_r(Q) ∩ α` is `(-1)^{r-1}(r-1)!` times `(ι_* ∘ j^* ∘ C) ∩ α`.

On `W_∞ ×_X T = (X' ×_X T) ∪ (E ×_X T)` the class `C ∩ α` is `a_* β₁ + b_* β₂` (Stacks 0F94).
The extension `c'_r(Q|_E)` kills `a_* β₁` and caps `b_* β₂` as `c_r(Q)|_E = c_r(i_{0,*}𝒪_Z)`
does, which Stacks 0FEF computes
(`Stacks.Chow.bundleFlatPullbackChow_perfectChernClass_exceptionalTest`); and `j^*` kills
`a_* β₁`, the normal cone missing `X'`, and restricts `b_* β₂` to `C_ZX ×_X T ⊆ E ×_X T`. -/
theorem bundleFlatPullback_modificationChernClass_cap (hr : r ≠ 0)
    {Q : DerivedCategory (blowupAtInfinity (Scheme.Hom.ker i)).Modules}
    (hQ : HasDefinedChernClasses Q)
    (hrank : ∃ M : (strictTransformIdealAtInfinity (Scheme.Hom.ker i)).subscheme.Modules,
      IsFiniteLocallyFreeOfRankLT M r ∧
        Nonempty ((Cohomology.DerivedAdjunctionOnRingedSpaces.derivedPullback
          (strictTransformToFibreAtInfinity sX i ≫ ι∞).toLRSHom.toShHom).obj Q ≅
            (DerivedCategory.singleFunctor _ 0).obj M))
    (φ : pullback π∞ i ⟶ projectiveCompletion 𝒞ᵢ) [IsIso φ]
    (hφ : φ ≫ projectiveCompletionProj 𝒞ᵢ = pullback.snd π∞ i)
    (hcone : normalConeToExceptionalFibre sX i ≫ φ =
      (𝒩ᵢ).normalConeEmbedding ≫ normalBundleToCompletion i hi)
    (ψ : (Cohomology.DerivedAdjunctionOnRingedSpaces.derivedPullback
        (pullback.fst π∞ i ≫ ι∞).toLRSHom.toShHom).obj Q ≅
      (Cohomology.DerivedAdjunctionOnRingedSpaces.derivedPullback φ.toLRSHom.toShHom).obj
        ((DerivedCategory.singleFunctor (projectiveCompletion 𝒞ᵢ).Modules 0).obj
          ((Scheme.Modules.pushforward (Stacks.ProjectiveCompletion.zeroSection 𝒞ᵢ)).obj
            (SheafOfModules.unit (Stacks.Chow.bundle (Stacks.Ample.unitModule Z)).ringCatSheaf))))
    {T : Scheme.{u}} (g : T ⟶ X) [LocallyOfFiniteType g] (k : ℤ) (α : chowGroup C (g ≫ sX) k) :
    bundleFlatPullback C (i ≫ sX) ((𝒩ᵢ).projection ≫ i ≫ sX) i (𝒩ᵢ).projection rfl r
        ((𝒩ᵢ).flat_projection_of_rank r) ((𝒩ᵢ).relativeDimension_projection_of_rank r)
        (flatPullbackDescends C) g k
        ((modificationChernClass C sX (blowupAtInfinityToProjectiveLineProduct i.ker sX)
          (isIso_pullback_snd_blowupAtInfinityToProjectiveLineProduct i.ker sX) i
          (strictTransformToFibreAtInfinity sX i) hQ r
          (mem_range_strictTransformToFibreAtInfinity sX i) hrank).cap g k α) =
      ((-1 : ℤ) ^ (r - 1) * ((r - 1).factorial : ℤ)) •
        (virtualNormalConeClass C (i ≫ sX) sX i rfl 𝒩ᵢ).cap g k α := by
  have := locallyOfFiniteType_normalConeToBase C sX i
  have := VirtualNormalBundle.isIso_normalConeEmbedding_ofIsRegularImmersion hi
  have hL := localizedModificationClass_cap_heq (gysinAtInfinityData C sX
    (blowupAtInfinityToProjectiveLineProduct i.ker sX)
    (isIso_pullback_snd_blowupAtInfinityToProjectiveLineProduct i.ker sX)) i
    (strictTransformToFibreAtInfinity sX i) (mem_range_strictTransformToFibreAtInfinity sX i)
    (vanishesOver_perfectChernClass_of_rankLT C _ _ hQ r hrank) g k α
  have hR := virtualNormalConeClass_cap_heq C (i ≫ sX) sX i rfl 𝒩ᵢ g k α
  have hcore := bundleFlatPullbackChow_modificationExtension_cap C sX i hi r hr hQ hrank φ hφ
    hcone ψ g (k - 0) ((gysinAtInfinityClass C sX (blowupAtInfinityToProjectiveLineProduct i.ker sX)
      (isIso_pullback_snd_blowupAtInfinityToProjectiveLineProduct i.ker sX)).cap g k α)
  rw [bundleFlatPullback_apply]
  refine eq_of_heq ((chowGroupDegreeEquiv_heq C _ _ _).trans ?_)
  refine (heq_map_index (by ring : k - (r : ℤ) = (k - 0) - r) hL fun n x ↦
    bundleFlatPullbackChow C (i ≫ sX) ((𝒩ᵢ).projection ≫ i ≫ sX) i (𝒩ᵢ).projection rfl r
      ((𝒩ᵢ).flat_projection_of_rank r) ((𝒩ᵢ).relativeDimension_projection_of_rank r)
      (flatPullbackDescends C) g n x).trans ?_
  refine (chowGroupDegreeEquiv_heq C _ _ _).symm.trans ((heq_of_eq hcore).trans ?_)
  exact heq_map_index (by ring) hR.symm fun n x ↦ ((-1 : ℤ) ^ (r - 1) * ((r - 1).factorial : ℤ)) • x

end TopClass

/-! ### Part (F) of Stacks 0FEG -/

section Formula

attribute [local instance 10000] HasDerivedCategory.standard

variable (C : ChowSituation.{u}) {X Z : Scheme.{u}} (sX : X ⟶ C.S) [LocallyOfFiniteType sX]
  (i : Z ⟶ X) [IsClosedImmersion i] [IsLocallyNoetherian Z] {r : ℕ}
  (hreg : IsRegularClosedImmersionOfCodim i r)

local notation "π∞" =>
  modificationProjectionAtInfinity sX
    (blowupAtInfinityToProjectiveLineProduct (Scheme.Hom.ker i) sX)
local notation "ι∞" =>
  modificationInclusionAtInfinity sX (blowupAtInfinityToProjectiveLineProduct (Scheme.Hom.ker i) sX)
local notation "𝒩ᵣ" => VirtualNormalBundle.ofIsRegularImmersion i (hreg.isRegularImmersion)
local notation "𝒞ᵣ" =>
  dualSheaf (VirtualNormalBundle.bundle (VirtualNormalBundle.ofIsRegularImmersion i
    (hreg.isRegularImmersion)))

/-- **Part (F) of the proof of Stacks 0FEG: `c'_r(Q) = (-1)^{r-1}(r-1)! c(Z ⟶ X, 𝒩)`**, from an
identification of `Q|_E`. Let `i : Z ⟶ X` be a regular closed immersion of codimension `r ≥ 1`,
`b : W ⟶ 𝐏¹_X` the blowup in `∞(Z)` with strict transform `X' ⊆ W_∞`, `E = W_∞ ×_X Z` and
`e : E ⟶ W_∞ ⟶ W`. Let `φ : E ≅ 𝐏(𝒞 ⊕ 𝒪_Z)` be an isomorphism over `Z`, `𝒞` the conormal
sheaf, under which the open immersion `C_ZX ⟶ E` of Stacks 0FBH is `C_ZX ⟶ N ⟶ 𝐏(𝒞 ⊕ 𝒪_Z)`.
If `Q ∈ D(𝒪_W)` has defined Chern classes, `Q|_{X'}` is finite locally free of rank `< r` in
degree `0`, and `Le^*Q ≅ Lφ^*(i_{0,*}𝒪_Z)` for the zero section `i_0 : Z ⟶ 𝐏(𝒞 ⊕ 𝒪_Z)`, then
the class `c'_r(Q) ∈ A^r(Z ⟶ X)` of Stacks 0F9K is `(-1)^{r-1}(r-1)!` times the class
`c(Z ⟶ X, 𝒩)` of Stacks 0FBK of the normal sheaf `𝒩 = 𝒞^∨`.

By Stacks 0FBK (`Stacks.Chow.cap_eq_virtualNormalBundleClass_cap`) and Stacks 02TY it suffices
that `p^*(c'_r(Q) ∩ α) = (-1)^{r-1}(r-1)! ι_* j^*(C ∩ α)` on every test scheme, which is
`Stacks.Chow.bundleFlatPullback_modificationChernClass_cap`. -/
theorem modificationChernClass_eq_regularNormalGysinClass_of_derivedPullback_iso (hr : r ≠ 0)
    {Q : DerivedCategory (blowupAtInfinity (Scheme.Hom.ker i)).Modules}
    (hQ : HasDefinedChernClasses Q)
    (hrank : ∃ M : (strictTransformIdealAtInfinity (Scheme.Hom.ker i)).subscheme.Modules,
      IsFiniteLocallyFreeOfRankLT M r ∧
        Nonempty ((Cohomology.DerivedAdjunctionOnRingedSpaces.derivedPullback
          (strictTransformToFibreAtInfinity sX i ≫ ι∞).toLRSHom.toShHom).obj Q ≅
            (DerivedCategory.singleFunctor _ 0).obj M))
    (φ : pullback π∞ i ⟶ projectiveCompletion 𝒞ᵣ) [IsIso φ]
    (hφ : φ ≫ projectiveCompletionProj 𝒞ᵣ = pullback.snd π∞ i)
    (hcone : normalConeToExceptionalFibre sX i ≫ φ =
      (𝒩ᵣ).normalConeEmbedding ≫ normalBundleToCompletion i (hreg.isRegularImmersion))
    (ψ : (Cohomology.DerivedAdjunctionOnRingedSpaces.derivedPullback
        (pullback.fst π∞ i ≫ ι∞).toLRSHom.toShHom).obj Q ≅
      (Cohomology.DerivedAdjunctionOnRingedSpaces.derivedPullback φ.toLRSHom.toShHom).obj
        ((DerivedCategory.singleFunctor (projectiveCompletion 𝒞ᵣ).Modules 0).obj
          ((Scheme.Modules.pushforward (Stacks.ProjectiveCompletion.zeroSection 𝒞ᵣ)).obj
            (SheafOfModules.unit (Stacks.Chow.bundle (Stacks.Ample.unitModule Z)).ringCatSheaf)))) :
    modificationChernClass C sX (blowupAtInfinityToProjectiveLineProduct i.ker sX)
        (isIso_pullback_snd_blowupAtInfinityToProjectiveLineProduct i.ker sX) i
        (strictTransformToFibreAtInfinity sX i) hQ r
        (mem_range_strictTransformToFibreAtInfinity sX i) hrank =
      ((-1 : ℤ) ^ (r - 1) * ((r - 1).factorial : ℤ)) •
        regularNormalGysinClass C (i ≫ sX) sX i rfl hreg := by
  have := hreg.isFiniteLocallyFreeOfRank_conormalModule
  refine BivariantClass.ext C _ _ _ _ _ _ fun g _ k α ↦ ?_
  rw [BivariantClass.zsmul_cap]
  have hinj : Function.Injective (bundleFlatPullback C (i ≫ sX) ((𝒩ᵣ).projection ≫ i ≫ sX) i
      (𝒩ᵣ).projection rfl r ((𝒩ᵣ).flat_projection_of_rank r)
      ((𝒩ᵣ).relativeDimension_projection_of_rank r)
      (flatPullbackDescends C) g k) :=
    fun x y h ↦ (bijective_bundleFlatPullbackChow C (i ≫ sX) i 𝒩ᵣ r g (k - r)).1
      ((chowGroupDegreeEquiv C _ _).injective (by rwa [bundleFlatPullback_apply,
        bundleFlatPullback_apply] at h))
  apply hinj
  rw [bundleFlatPullback_modificationChernClass_cap C sX i hreg.isRegularImmersion r hr hQ hrank
    φ hφ hcone ψ g k α, map_zsmul]
  exact congrArg _ (isVirtualNormalBundleClass_virtualNormalBundleClass C (i ≫ sX) sX i rfl 𝒩ᵣ r
    g k α).symm

/-- **Part (F) of the proof of Stacks 0FEG**, for the isomorphism
`Stacks.Chow.exceptionalFibreIsoProjectiveCompletion : W_∞ ×_X Z ≅ 𝐏(𝒞 ⊕ 𝒪_Z)` built from the
exceptional divisor: if `Q|_{X'}` is finite locally free of rank `< r` in degree `0` and
`Le^*Q ≅ Lφ^*(i_{0,*}𝒪_Z)` along it, then `c'_r(Q) = (-1)^{r-1}(r-1)! c(Z ⟶ X, 𝒩)`. -/
theorem modificationChernClass_eq_regularNormalGysinClass (hr : r ≠ 0)
    {Q : DerivedCategory (blowupAtInfinity (Scheme.Hom.ker i)).Modules}
    (hQ : HasDefinedChernClasses Q)
    (hrank : ∃ M : (strictTransformIdealAtInfinity (Scheme.Hom.ker i)).subscheme.Modules,
      IsFiniteLocallyFreeOfRankLT M r ∧
        Nonempty ((Cohomology.DerivedAdjunctionOnRingedSpaces.derivedPullback
          (strictTransformToFibreAtInfinity sX i ≫ ι∞).toLRSHom.toShHom).obj Q ≅
            (DerivedCategory.singleFunctor _ 0).obj M))
    (ψ : (Cohomology.DerivedAdjunctionOnRingedSpaces.derivedPullback
        (pullback.fst π∞ i ≫ ι∞).toLRSHom.toShHom).obj Q ≅
      (Cohomology.DerivedAdjunctionOnRingedSpaces.derivedPullback
        (exceptionalFibreIsoProjectiveCompletion sX i
          (hreg.isRegularImmersion)).hom.toLRSHom.toShHom).obj
        ((DerivedCategory.singleFunctor (projectiveCompletion 𝒞ᵣ).Modules 0).obj
          ((Scheme.Modules.pushforward (Stacks.ProjectiveCompletion.zeroSection 𝒞ᵣ)).obj
            (SheafOfModules.unit (Stacks.Chow.bundle (Stacks.Ample.unitModule Z)).ringCatSheaf)))) :
    modificationChernClass C sX (blowupAtInfinityToProjectiveLineProduct i.ker sX)
        (isIso_pullback_snd_blowupAtInfinityToProjectiveLineProduct i.ker sX) i
        (strictTransformToFibreAtInfinity sX i) hQ r
        (mem_range_strictTransformToFibreAtInfinity sX i) hrank =
      ((-1 : ℤ) ^ (r - 1) * ((r - 1).factorial : ℤ)) •
        regularNormalGysinClass C (i ≫ sX) sX i rfl hreg :=
  modificationChernClass_eq_regularNormalGysinClass_of_derivedPullback_iso C sX i hreg hr hQ hrank
    _ (exceptionalFibreIsoProjectiveCompletion_hom_projection sX i _)
    (normalConeToExceptionalFibre_comp_isoProjectiveCompletion_hom sX i _) ψ

end Formula

end Stacks.Chow

end
