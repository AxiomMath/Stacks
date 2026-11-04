module

public import StacksFrontier.Algebra.Category.ModuleCat.Sheaf.CoherentFinitePresentation
public import StacksFrontier.AlgebraicGeometry.AffinePushforward.Basic
public import StacksFrontier.AlgebraicGeometry.AmpleTwistAcyclicity.Basic
public import StacksFrontier.AlgebraicGeometry.CoherentAbelian.HigherDirectImage
public import StacksFrontier.AlgebraicGeometry.Divisors.RegularSectionAssociatedPoints
public import StacksFrontier.AlgebraicGeometry.Morphisms.Support.Specialization
public import StacksFrontier.AlgebraicGeometry.ProperCoherenceWitness.IsoOverOpen
public import StacksFrontier.AlgebraicGeometry.ProperCoherenceWitness.Reduction
public import StacksFrontier.AlgebraicGeometry.TwistedSheaf.PushforwardTwist
public import StacksCore.Tactic.StacksAttribute

/-!
# The two stalk clauses of the Chow twist

Let `i : Z ⟶ X` be a closed immersion with `Z` integral, `π : Y ⟶ Z` a morphism which is an
isomorphism above a dense open `U` of `Z`, `M` an invertible `𝒪_Y`-module and `ξ` the generic
point of the range of `i`. Then the stalk of the direct image `(π ≫ i)_* M` at `ξ` has length
one, and if `π_* M` is quasi-coherent then `(π ≫ i)_* M` is supported exactly on the range of
`i`. From these the witness sheaves of [Stacks, Tag 01YI] exist, which gives the coherence of
higher direct images under a proper morphism, [Stacks, Tag 02O5], and the finiteness of
cohomology over a Noetherian affine base, [Stacks, Tag 02O6].

## Main results

* `AlgebraicGeometry.ProperCoherenceWitness.genericPoint_mem_of_dense`: the generic point of an
  integral scheme lies in every dense open.
* `AlgebraicGeometry.ProperCoherenceWitness.length_stalk_pushforward_chowTwist`: the length
  clause.
* `AlgebraicGeometry.ProperCoherenceWitness.supp_pushforward_chowTwist`: the support clause.
* `AlgebraicGeometry.ProperCoherenceWitness.chowTwistGenericStalk_of_isQuasicoherent`: both
  clauses together, in the shape of `ChowTwistGenericStalk`'s body.
* `AlgebraicGeometry.ProperCoherenceWitness.hasGenericCoherentWitness`: the witness sheaves of
  [Stacks, Tag 01YI].
* `AlgebraicGeometry.ProperCoherenceWitness.higherDirectImageIsCoherent`,
  `AlgebraicGeometry.ProperCoherenceWitness.higherDirectImageIsCoherentOverAffineBase` and
  `AlgebraicGeometry.ProperCoherenceWitness.isCoherent_pushforward`: coherence of higher direct
  images and of the direct image under a proper morphism to a locally Noetherian base,
  [Stacks, Tag 02O5].
* `AlgebraicGeometry.ProperCoherenceWitness.moduleFinite_cohomology`: finiteness of the
  cohomology of a coherent module on a scheme proper over a Noetherian affine base,
  [Stacks, Tag 02O6].

## References

* [Stacks Project, Tag 01YI](https://stacks.math.columbia.edu/tag/01YI)
* [Stacks Project, Tag 02O5](https://stacks.math.columbia.edu/tag/02O5)
* [Stacks Project, Tag 02O6](https://stacks.math.columbia.edu/tag/02O6)
* [Stacks Project, Tag 05AC](https://stacks.math.columbia.edu/tag/05AC)
* [Stacks Project, Tag 0EE3](https://stacks.math.columbia.edu/tag/0EE3)
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits TopologicalSpace Topology Opposite
open AlgebraicGeometry
open Stacks.Ample
open Stacks.Cohomology.AffineBase
open Stacks.AlgebraicGeometry.IsoOverOpen

universe u

namespace AlgebraicGeometry.ProperCoherenceWitness

open AlgebraicGeometry.ProperCoherentImage

attribute [local instance 10000] HasDerivedCategory.standard

/-! ### The generic point of an integral scheme lies in every dense open -/

/-- The generic point of an integral scheme lies in every dense open. -/
@[ega "I 7.1.10" "special case"]
theorem genericPoint_mem_of_dense {Z : Scheme.{u}} [IsIntegral Z] {U : Z.Opens}
    (hU : Dense (U : Set Z)) : genericPoint Z ∈ U := by
  refine ((genericPoint_spec Z).mem_open_set_iff U.isOpen).mpr ?_
  simpa using hU.nonempty

/-! ### The two clauses -/

variable {X Y Z : Scheme.{u}}

/-- A generic point of the range of a closed immersion from an integral scheme is the image of
the generic point. -/
private theorem eq_base_genericPoint_of_isGenericPoint {X Z : Scheme.{u}} (i : Z ⟶ X)
    [IsClosedImmersion i] [IsIntegral Z] {ξ : X} (hξ : IsGenericPoint ξ (Set.range i.base)) :
    ξ = i.base (genericPoint Z) := by
  have h := (genericPoint_spec Z).image i.continuous
  rw [Set.image_univ, i.isClosedEmbedding.isClosed_range.closure_eq] at h
  exact hξ.eq h

/-- **The length clause of the Chow twist.** For `i : Z ⟶ X` a closed immersion with `Z`
integral, `π : Y ⟶ Z` an isomorphism above a dense open `U` of `Z`, `M` an invertible
`𝒪_Y`-module and `ξ` the generic point of the range of `i`, the stalk of `(π ≫ i)_* M` at `ξ`
has length one over `𝒪_{X,ξ}`. -/
theorem length_stalk_pushforward_chowTwist (i : Z ⟶ X) [IsClosedImmersion i] [IsIntegral Z]
    (π : Y ⟶ Z) (U : Z.Opens) (hU : Dense (U : Set Z)) [IsIso (π ∣_ U)] (M : Y.Modules)
    [IsInvertibleModule Y M] {ξ : X} (hξ : IsGenericPoint ξ (Set.range i.base)) :
    Module.length (X.presheaf.stalk ξ)
      (((Scheme.Modules.pushforward (π ≫ i)).obj M).presheaf.stalk ξ) = 1 := by
  have hζU : genericPoint Z ∈ U := genericPoint_mem_of_dense hU
  obtain ⟨y, hy, hπy⟩ := exists_mem_preimage π U hζU
  have hξeq := eq_base_genericPoint_of_isGenericPoint i hξ
  have hpt : (π ≫ i).base y = ξ := by rw [hξeq, ← hπy, Scheme.Hom.comp_apply]
  have hlen := length_stalk_pushforward_comp i i.isClosedEmbedding.isInducing π U M hy
  rw [hpt] at hlen
  rw [hlen]
  have hinvAG : AlgebraicGeometry.SheafOfModules.IsInvertible Y.sheaf.obj
      Y.ringCatSheaf.property M := ‹IsInvertibleModule Y M›
  obtain ⟨e⟩ := Stacks.Divisors.nonempty_stalk_linearEquiv_of_isInvertible M y
  have hisoy : IsIso (π.stalkMap y) := isIso_stalkMap π U hy
  have hfieldZ : IsField (Z.presheaf.stalk (π.base y)) := by
    rw [hπy]
    exact Field.toIsField _
  have hfield : IsField (Y.presheaf.stalk y) :=
    MulEquiv.isField hfieldZ ((asIso (π.stalkMap y)).commRingCatIsoToRingEquiv).symm.toMulEquiv
  rw [e.length_eq, Module.length_eq_one_iff, isSimpleModule_self_iff_isUnit]
  exact ⟨⟨hfield.exists_pair_ne⟩, fun _ hx => isUnit_iff_exists_inv.mpr (hfield.mul_inv_cancel hx)⟩

/-- **The support clause of the Chow twist.** In the situation of
`AlgebraicGeometry.ProperCoherenceWitness.length_stalk_pushforward_chowTwist`, and with `π_* M`
quasi-coherent, the support of `(π ≫ i)_* M` is exactly the range of `i`. -/
theorem supp_pushforward_chowTwist (i : Z ⟶ X) [IsClosedImmersion i] [IsIntegral Z]
    (π : Y ⟶ Z) (U : Z.Opens) (hU : Dense (U : Set Z)) [IsIso (π ∣_ U)] (M : Y.Modules)
    [IsInvertibleModule Y M] [((Scheme.Modules.pushforward π).obj M).IsQuasicoherent] {ξ : X}
    (hξ : IsGenericPoint ξ (Set.range i.base)) :
    SheafOfModules.supp ((Scheme.Modules.pushforward (π ≫ i)).obj M) = Set.range i.base := by
  have hsuppeq : SheafOfModules.supp
        ((Scheme.Modules.pushforward i).obj ((Scheme.Modules.pushforward π).obj M)) =
      SheafOfModules.supp ((Scheme.Modules.pushforward (π ≫ i)).obj M) :=
    SheafOfModules.supp_eq_of_iso ((Scheme.Modules.pushforwardComp π i).app M)
  have hmem : ξ ∈ SheafOfModules.supp ((Scheme.Modules.pushforward (π ≫ i)).obj M) :=
    (SheafOfModules.mem_supp_iff_nontrivial_stalk _ ξ).mpr <| @IsSimpleModule.nontrivial _ _ _ _ _
      (Module.length_eq_one_iff.mp (length_stalk_pushforward_chowTwist i π U hU M hξ))
  have hstab : StableUnderSpecialization
      (SheafOfModules.supp ((Scheme.Modules.pushforward (π ≫ i)).obj M)) := by
    rw [← hsuppeq]
    exact Scheme.Modules.stableUnderSpecialization_supp X _
  refine subset_antisymm ?_ fun x hx => ?_
  · rw [← hsuppeq, AlgebraicGeometry.supp_pushforward_of_isClosedImmersion]
    exact Set.image_subset_range _ _
  · exact hstab (specializes_iff_mem_closure.mpr (hξ ▸ hx)) hmem

/-- **The support and length clauses of
`AlgebraicGeometry.ProperCoherenceWitness.ChowTwistGenericStalk`**, for `π_* M` quasi-coherent. -/
theorem chowTwistGenericStalk_of_isQuasicoherent (X Z Y : Scheme.{u}) (i : Z ⟶ X) (π : Y ⟶ Z)
    (U : Z.Opens) (M : Y.Modules) (hi : IsClosedImmersion i) (hZ : IsIntegral Z)
    (hU : Dense (U : Set Z)) (hiso : IsIso (π ∣_ U)) (hM : IsInvertibleModule Y M)
    (hqc : ((Scheme.Modules.pushforward π).obj M).IsQuasicoherent) (ξ : X)
    (hξ : IsGenericPoint ξ (Set.range i.base)) :
    SheafOfModules.supp ((Scheme.Modules.pushforward (π ≫ i)).obj M) = Set.range i.base ∧
      (letI : Module (X.presheaf.stalk ξ)
          (((Scheme.Modules.pushforward (π ≫ i)).obj M).presheaf.stalk ξ) :=
        PresheafOfModules.instModuleCarrierStalkCommRingCatCarrierAbPresheafOpensCarrier
          (R := X.presheaf) ((Scheme.Modules.pushforward (π ≫ i)).obj M).val ξ
       Module.length (X.presheaf.stalk ξ)
         (((Scheme.Modules.pushforward (π ≫ i)).obj M).presheaf.stalk ξ) = 1) := by
  have := hi
  have := hZ
  have := hiso
  have := hM
  have := hqc
  exact ⟨supp_pushforward_chowTwist i π U hU M hξ,
    length_stalk_pushforward_chowTwist i π U hU M hξ⟩

/-! ### The witness sheaves -/

/-- **The witness sheaves of [Stacks, Tag 01YI] exist.** -/
theorem hasGenericCoherentWitness : HasGenericCoherentWitness.{u} := by
  intro X S f hSaff hSnoeth hfproper Z i hi hZ ξ hξ
  have : IsAffine S := hSaff
  have : IsLocallyNoetherian S := hSnoeth
  have : IsProper f := hfproper
  have : IsClosedImmersion i := hi
  have : IsIntegral Z := hZ
  have hNX : IsNoetherian X := isNoetherian_of_isProper_of_isAffine f
  have hLNX : IsLocallyNoetherian X := inferInstance
  obtain ⟨Y, π, U, M, -, hdense, hisoU, hMinv, hMcoh, hπMcoh, hcoh⟩ :=
    exists_chowTwist_forall_isCoherent
      Stacks.AlgebraicGeometry.AmpleTwistAcyclicity.vanishingOverAffineBase f i
  have hqc : ((Scheme.Modules.pushforward π).obj M).IsQuasicoherent :=
    isQuasicoherent_of_isCoherent _
  obtain ⟨hsupp, hlen⟩ :=
    chowTwistGenericStalk_of_isQuasicoherent X Z Y i π U M hi hZ hdense hisoU hMinv hqc ξ hξ
  have hξeq := eq_base_genericPoint_of_isGenericPoint i hξ
  have hkill : Stacks.ClosedImmersion.StalkKilledByMaximalIdeal
      ((Scheme.Modules.pushforward (π ≫ i)).obj M) ξ := by
    rw [hξeq]
    exact Stacks.AlgebraicGeometry.ProperCoherenceWitnessStalk.stalkKilledByMaximalIdeal_pushforward
      i (genericPoint Z) (genericPoint_spec Z) ((Scheme.Modules.pushforward π).obj M)
  exact ⟨(Scheme.Modules.pushforward (π ≫ i)).obj M,
    Stacks.AlgebraicGeometry.FiniteDirectImageCoherent.isCoherent_pushforward_of_isFinite i
      ((Scheme.Modules.pushforward π).obj M),
    hsupp, hkill, hlen, hcoh⟩

/-! ### The conclusions of [Stacks, Tag 02O5] and [Stacks, Tag 02O6] -/

/-- **Coherence of higher direct images.** Let `S` be a locally Noetherian scheme, let
`f : X ⟶ S` be proper and let `F` be a coherent `𝒪_X`-module. Then `R ⁱ f_* F` is a coherent
`𝒪_S`-module for every `i ≥ 0`. -/
@[stacks 02O5]
theorem higherDirectImageIsCoherent : HigherDirectImageIsCoherent.{u} :=
  higherDirectImageIsCoherent_of_genericWitness hasGenericCoherentWitness

/-- **[Stacks, Tag 02O5]'s assertion about higher direct images, over an affine base.** -/
theorem higherDirectImageIsCoherentOverAffineBase :
    HigherDirectImageIsCoherentOverAffineBase.{u} :=
  higherDirectImageIsCoherentOverAffineBase_of_genericWitness hasGenericCoherentWitness

/-- **Coherence of the direct image.** For `f : X ⟶ S` proper onto a locally Noetherian base and
`F` coherent, `f_* F` is coherent. -/
@[stacks 02O5, ega "III 2.2.5" "partial"]
theorem isCoherent_pushforward {X S : Scheme.{u}} (f : X ⟶ S) [IsLocallyNoetherian S]
    [IsProper f] (F : X.Modules) [F.IsCoherent] :
    ((Scheme.Modules.pushforward f).obj F).IsCoherent :=
  (CoherentAbelian.isCoherent_higherDirectImage_zero_iff f F).mp
    (by simpa using higherDirectImageIsCoherent X S f ‹_› ‹_› F ‹_› 0)

/-- **Finiteness of cohomology.** Let `S = Spec A` with `A` Noetherian, let `f : X ⟶ S` be proper
and let `F` be a coherent `𝒪_X`-module. Then `Hⁱ(X, F)` is a finite `A`-module for every `i ≥ 0`.
Here the base is an affine locally Noetherian scheme and `A` is its ring of global sections. -/
@[stacks 02O6, ega "III 3.2.3"]
theorem moduleFinite_cohomology {X S : Scheme.{u}} (f : X ⟶ S) [IsProper f] [IsAffine S]
    [IsLocallyNoetherian S] (F : X.Modules) [F.IsCoherent] (i : ℕ) :
    Module.Finite Γ(S, ⊤) ((ModuleCat.restrictScalars f.appTop.hom).obj
      (((moduleGlobalSections X).rightDerived i).obj F)) :=
  moduleFinite_cohomology_of_genericWitness hasGenericCoherentWitness f F i

end AlgebraicGeometry.ProperCoherenceWitness

end
