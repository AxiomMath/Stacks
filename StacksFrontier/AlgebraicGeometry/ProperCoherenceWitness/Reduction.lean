module

public import StacksFrontier.AlgebraicGeometry.ProperCoherenceWitness.Basic
public import StacksFrontier.AlgebraicGeometry.ProperCoherenceWitness.ChowTwist
public import StacksFrontier.AlgebraicGeometry.ProperCoherenceWitness.GenericStalk

/-!
# [Stacks, Tag 02O5] reduced to one local statement about a stalk

`AlgebraicGeometry.ProperCoherenceWitness.HasGenericCoherentWitness` asks, for every integral
closed subscheme `i : Z ⟶ X` of the source of a proper morphism `f : X ⟶ S` onto an affine
locally Noetherian base, for a coherent `𝒪_X`-module satisfying five conditions. Coherence and
the coherence of every higher direct image along `f` hold for the module
`AlgebraicGeometry.ProperCoherenceWitness.exists_chowTwist_forall_isCoherent` produces from
`Stacks.AlgebraicGeometry.RelativeAmpleTwistVanishing.VanishingOverAffineBase`, and annihilation
of the stalk at the generic point by the maximal ideal holds for every direct image along a
closed immersion. The remaining two conditions, on the support and on the length of the stalk at
the generic point, are the hypothesis `ChowTwistGenericStalk`; granted it and
`VanishingOverAffineBase`, the conclusions of [Stacks, Tag 02O5] and [Stacks, Tag 02O6] follow.

## Main results

All of the following live in the namespace `AlgebraicGeometry.ProperCoherenceWitness`.

* `ChowTwistGenericStalk`: the support and length conditions on the stalk of the Chow twist at
  the generic point, as a `Prop`.
* `hasGenericCoherentWitness_of_chowTwistGenericStalk`:
  `VanishingOverAffineBase` together with `ChowTwistGenericStalk` gives
  `HasGenericCoherentWitness`.
* `higherDirectImageIsCoherent_of_chowTwistGenericStalk`: hence [Stacks, Tag 02O5]'s first
  assertion.
* `moduleFinite_cohomology_of_chowTwistGenericStalk`: hence [Stacks, Tag 02O6]'s conclusion.

## References

* [Stacks Project, Tag 01YI](https://stacks.math.columbia.edu/tag/01YI)
* [Stacks Project, Tag 02O1](https://stacks.math.columbia.edu/tag/02O1)
* [Stacks Project, Tag 02O5](https://stacks.math.columbia.edu/tag/02O5)
* [Stacks Project, Tag 02O6](https://stacks.math.columbia.edu/tag/02O6)
* [Stacks Project, Tag 0EE3](https://stacks.math.columbia.edu/tag/0EE3)
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits
open AlgebraicGeometry
open Stacks.Ample
open Stacks.Cohomology.AffineBase

universe u

namespace AlgebraicGeometry.ProperCoherenceWitness

open AlgebraicGeometry.ProperCoherentImage

attribute [local instance 10000] HasDerivedCategory.standard

/-! ### The remaining obligation -/

/-- **The support and length conditions of the witness sheaf, for the module the Chow
construction produces**, as a `Prop`: for every closed immersion `i : Z ⟶ X` with `Z` integral,
every `π : Y ⟶ Z` which is an isomorphism above a dense open of `Z`, every invertible
`𝒪_Y`-module `M` and every generic point `ξ` of the range of `i`, the module
`(π ≫ i)_* M = i_* π_* M` is supported exactly on that range and its stalk at `ξ` has length
one. -/
def ChowTwistGenericStalk : Prop :=
  ∀ (X Z Y : Scheme.{u}) (i : Z ⟶ X) (π : Y ⟶ Z) (U : Z.Opens) (M : Y.Modules),
    IsClosedImmersion i → IsIntegral Z → Dense (U : Set Z) → IsIso (π ∣_ U) →
      IsInvertibleModule Y M →
      ∀ ξ : X, IsGenericPoint ξ (Set.range i.base) →
        SheafOfModules.supp ((Scheme.Modules.pushforward (π ≫ i)).obj M) = Set.range i.base ∧
          (letI : Module (X.presheaf.stalk ξ)
              (((Scheme.Modules.pushforward (π ≫ i)).obj M).presheaf.stalk ξ) :=
            PresheafOfModules.instModuleCarrierStalkCommRingCatCarrierAbPresheafOpensCarrier
              (R := X.presheaf) ((Scheme.Modules.pushforward (π ≫ i)).obj M).val ξ
           Module.length (X.presheaf.stalk ξ)
             (((Scheme.Modules.pushforward (π ≫ i)).obj M).presheaf.stalk ξ) = 1)

/-! ### The witness sheaves from the two inputs -/

/-- **The witness sheaves of [Stacks, Tag 01YI], from the vanishing input of
[Stacks, Tag 02O1] and the stalk conditions.** Granted `VanishingOverAffineBase` and
`AlgebraicGeometry.ProperCoherenceWitness.ChowTwistGenericStalk`,
`AlgebraicGeometry.ProperCoherenceWitness.HasGenericCoherentWitness` holds. -/
theorem hasGenericCoherentWitness_of_chowTwistGenericStalk
    (haffine : Stacks.AlgebraicGeometry.RelativeAmpleTwistVanishing.VanishingOverAffineBase.{u})
    (hstalk : ChowTwistGenericStalk.{u}) :
    HasGenericCoherentWitness.{u} := by
  intro X S f hSaff hSnoeth hfproper Z i hi hZ ξ hξ
  have : IsAffine S := hSaff
  have : IsLocallyNoetherian S := hSnoeth
  have : IsProper f := hfproper
  have : IsClosedImmersion i := hi
  have : IsIntegral Z := hZ
  have hNX : IsNoetherian X := isNoetherian_of_isProper_of_isAffine f
  have hLNX : IsLocallyNoetherian X := inferInstance
  obtain ⟨Y, π, U, M, -, hdense, hisoU, hMinv, hMcoh, hπMcoh, hcoh⟩ :=
    exists_chowTwist_forall_isCoherent haffine f i
  obtain ⟨hsupp, hlen⟩ := hstalk X Z Y i π U M hi hZ hdense hisoU hMinv ξ hξ
  have hclosed : IsClosed (Set.range i.base) := i.isClosedEmbedding.isClosed_range
  have hgen : IsGenericPoint (i.base (genericPoint Z)) (Set.range i.base) := by
    have h := (genericPoint_spec Z).image i.continuous
    rwa [Set.image_univ, hclosed.closure_eq] at h
  have hξeq : ξ = i.base (genericPoint Z) := hξ.eq hgen
  have hkill : Stacks.ClosedImmersion.StalkKilledByMaximalIdeal
      ((Scheme.Modules.pushforward (π ≫ i)).obj M) ξ := by
    rw [hξeq]
    exact Stacks.AlgebraicGeometry.ProperCoherenceWitnessStalk.stalkKilledByMaximalIdeal_pushforward
      i (genericPoint Z) (genericPoint_spec Z) ((Scheme.Modules.pushforward π).obj M)
  have := hπMcoh
  exact ⟨(Scheme.Modules.pushforward (π ≫ i)).obj M,
    Stacks.AlgebraicGeometry.FiniteDirectImageCoherent.isCoherent_pushforward_of_isFinite i
      ((Scheme.Modules.pushforward π).obj M),
    hsupp, hkill, hlen, hcoh⟩

/-! ### The conclusions of [Stacks, Tag 02O5] and [Stacks, Tag 02O6] -/

/-- **[Stacks, Tag 02O5]'s first assertion from the two inputs.** Every higher direct image of a
coherent module along a proper morphism is coherent, granted `haffine` and
`ChowTwistGenericStalk`. -/
theorem higherDirectImageIsCoherent_of_chowTwistGenericStalk
    (haffine : Stacks.AlgebraicGeometry.RelativeAmpleTwistVanishing.VanishingOverAffineBase.{u})
    (hstalk : ChowTwistGenericStalk.{u}) :
    HigherDirectImageIsCoherent.{u} :=
  higherDirectImageIsCoherent_of_genericWitness
    (hasGenericCoherentWitness_of_chowTwistGenericStalk haffine hstalk)

/-- **[Stacks, Tag 02O5]'s first assertion over an affine base, from the two inputs.** -/
theorem higherDirectImageIsCoherentOverAffineBase_of_chowTwistGenericStalk
    (haffine : Stacks.AlgebraicGeometry.RelativeAmpleTwistVanishing.VanishingOverAffineBase.{u})
    (hstalk : ChowTwistGenericStalk.{u}) :
    HigherDirectImageIsCoherentOverAffineBase.{u} :=
  higherDirectImageIsCoherentOverAffineBase_of_genericWitness
    (hasGenericCoherentWitness_of_chowTwistGenericStalk haffine hstalk)

/-- **[Stacks, Tag 02O6]'s conclusion from the two inputs.** For `f : X ⟶ S` proper onto an
affine locally Noetherian base and `F` coherent, `Hⁱ(X, F)` is a finite `Γ(S, ⊤)`-module. -/
theorem moduleFinite_cohomology_of_chowTwistGenericStalk
    (haffine : Stacks.AlgebraicGeometry.RelativeAmpleTwistVanishing.VanishingOverAffineBase.{u})
    (hstalk : ChowTwistGenericStalk.{u}) {X S : Scheme.{u}} (f : X ⟶ S) [IsProper f]
    [IsAffine S] [IsLocallyNoetherian S] (F : X.Modules) [F.IsCoherent] (i : ℕ) :
    Module.Finite Γ(S, ⊤) ((ModuleCat.restrictScalars f.appTop.hom).obj
      (((moduleGlobalSections X).rightDerived i).obj F)) :=
  moduleFinite_cohomology_of_genericWitness
    (hasGenericCoherentWitness_of_chowTwistGenericStalk haffine hstalk) f F i

end AlgebraicGeometry.ProperCoherenceWitness

end
