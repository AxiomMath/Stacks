module

public import StacksFrontier.AlgebraicGeometry.CoherentDevissage.GenericStalkCriterion
public import StacksFrontier.AlgebraicGeometry.ProperCoherenceFrontier.Basic
public import StacksFrontier.AlgebraicGeometry.ProperCoherentImage.Devissage

/-!
# [Stacks, Tag 02O5] reduced to one witness sheaf per integral closed subscheme

The dévissage of [Stacks, Tag 01YI], applied to the property `P F` = "`R ᵖ f_* F` is coherent
for every `p`", asks for a single coherent module per integral closed subscheme `i : Z ⟶ X`: one
`𝒢` supported exactly on the range of `i`, whose stalk at the generic point `ξ` is killed by the
maximal ideal and has length one, and which satisfies `P`. It also asks that `P` satisfy the
two-out-of-three condition in a short exact sequence; the middle position is
`AlgebraicGeometry.ProperCoherentImage.isCoherent_higherDirectImage_X₂_of_shortExact`, and the two
outer positions are proved here by the five-term criterion [Stacks, Tag 02MO (2)]. So the first
assertion of [Stacks, Tag 02O5], and the conclusion of [Stacks, Tag 02O6], follow from the
existence of the witness sheaves, `HasGenericCoherentWitness`.

## Main results

All of the following live in the namespace `AlgebraicGeometry.ProperCoherenceWitness`.

* `isCoherent_higherDirectImage_X₃_of_shortExact` and
  `isCoherent_higherDirectImage_X₁_of_shortExact`: coherence of all the higher direct images
  propagates to the right-hand and to the left-hand term of a short exact sequence.
* `forall_isCoherent_higherDirectImage_twoOutOfThree`: the two-out-of-three condition for
  coherence of all the higher direct images.
* `HasGenericCoherentWitness`: the existence of the witness sheaves, as a `Prop`.
* `isCoherent_higherDirectImage_of_genericWitness`: [Stacks, Tag 02O5]'s first assertion for one
  proper morphism onto an affine locally Noetherian base, from the witness sheaves for that
  morphism alone.
* `higherDirectImageIsCoherentOverAffineBase_of_genericWitness` and
  `higherDirectImageIsCoherent_of_genericWitness`: the affine-base case and the whole of that
  assertion, from `HasGenericCoherentWitness`.
* `moduleFinite_cohomology_of_genericWitness`: **[Stacks, Tag 02O6]'s conclusion** from the same.

## Implementation notes

Writing `Fᵖ` for `R ᵖ f_*` and `δ` for the connecting morphisms of
`AlgebraicGeometry.ProperCoherentImage.higherDirectImageDeltaFunctor`, the five consecutive terms
centred on the module whose coherence is wanted are

* at `Fᵖ(X₃)`: `Fᵖ(X₁) ⟶ Fᵖ(X₂) ⟶ Fᵖ(X₃) ⟶ Fᵖ⁺¹(X₁) ⟶ Fᵖ⁺¹(X₂)`, whose four outer entries are
  terms of `X₁` and `X₂` in degrees `p` and `p + 1`;
* at `Fᵖ⁺¹(X₁)`: `Fᵖ(X₂) ⟶ Fᵖ(X₃) ⟶ Fᵖ⁺¹(X₁) ⟶ Fᵖ⁺¹(X₂) ⟶ Fᵖ⁺¹(X₃)`, whose four outer entries
  are terms of `X₂` and `X₃` in degrees `p` and `p + 1`.

In each case the outer entries are covered by the two hypotheses. In degree zero the left-hand
position uses the window `0 ⟶ 0 ⟶ F⁰(X₁) ⟶ F⁰(X₂) ⟶ F⁰(X₃)`, exact at `F⁰(X₁)` because
`F⁰(X₁) ⟶ F⁰(X₂)` is a monomorphism, with the terminal object as the zero object.

Two `CategoryTheory.HasDerivedCategory` instances for `X.Modules` are in scope, and
`CategoryTheory.HasDerivedCategory.standard`, the one the imported statements use, is given
priority.

## References

* [Stacks Project, Tag 02O5](https://stacks.math.columbia.edu/tag/02O5)
* [Stacks Project, Tag 02O6](https://stacks.math.columbia.edu/tag/02O6)
* [Stacks Project, Tag 01YI](https://stacks.math.columbia.edu/tag/01YI)
* [Stacks Project, Tag 02MO](https://stacks.math.columbia.edu/tag/02MO)
* [Stacks Project, Tag 0200](https://stacks.math.columbia.edu/tag/0200)
* [Stacks Project, Tag 02O4](https://stacks.math.columbia.edu/tag/02O4)
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits
open AlgebraicGeometry
open Stacks.Cohomology.AffineBase

universe u

namespace AlgebraicGeometry.ProperCoherenceWitness

open AlgebraicGeometry.ProperCoherentImage

attribute [local instance 10000] HasDerivedCategory.standard

/-! ### The two outer positions of the two-out-of-three condition -/

/-- **Coherence of all the higher direct images propagates to the right-hand term of a short
exact sequence.** Let `0 ⟶ F₁ ⟶ F₂ ⟶ F₃ ⟶ 0` be a short exact sequence of `𝒪_X`-modules. If
every higher direct image of `F₁` and every higher direct image of `F₂` is coherent, then so is
every higher direct image of `F₃`. -/
theorem isCoherent_higherDirectImage_X₃_of_shortExact {X S : Scheme.{u}} (f : X ⟶ S)
    {T : ShortComplex X.Modules} (hT : T.ShortExact)
    (h₁ : ∀ p : ℕ,
      (((Scheme.Modules.pushforward f).rightDerivedPlus (p : ℤ)).obj T.X₁).IsCoherent)
    (h₂ : ∀ p : ℕ,
      (((Scheme.Modules.pushforward f).rightDerivedPlus (p : ℤ)).obj T.X₂).IsCoherent)
    (p : ℕ) :
    (((Scheme.Modules.pushforward f).rightDerivedPlus (p : ℤ)).obj T.X₃).IsCoherent :=
  isCoherent_of_exact₄
    (f₀ := ((higherDirectImageDeltaFunctor f).functor p).map T.f)
    (f₁ := ((higherDirectImageDeltaFunctor f).functor p).map T.g)
    (f₂ := (higherDirectImageDeltaFunctor f).δ hT p)
    (f₃ := ((higherDirectImageDeltaFunctor f).functor (p + 1)).map T.f)
    ((higherDirectImageDeltaFunctor f).map_f_comp_map_g (S := T) p)
    ((higherDirectImageDeltaFunctor f).map_g_δ hT p)
    ((higherDirectImageDeltaFunctor f).δ_map_f hT p)
    ((higherDirectImageDeltaFunctor f).exact_map hT p)
    ((higherDirectImageDeltaFunctor f).exact_δ₁ hT p)
    ((higherDirectImageDeltaFunctor f).exact_δ₂ hT p)
    (h₁ p) (h₂ p) (h₁ (p + 1)) (h₂ (p + 1))

/-- **Coherence of all the higher direct images propagates to the left-hand term of a short exact
sequence.** Let `0 ⟶ F₁ ⟶ F₂ ⟶ F₃ ⟶ 0` be a short exact sequence of `𝒪_X`-modules. If every
higher direct image of `F₂` and every higher direct image of `F₃` is coherent, then so is every
higher direct image of `F₁`. -/
theorem isCoherent_higherDirectImage_X₁_of_shortExact {X S : Scheme.{u}} (f : X ⟶ S)
    {T : ShortComplex X.Modules} (hT : T.ShortExact)
    (h₂ : ∀ p : ℕ,
      (((Scheme.Modules.pushforward f).rightDerivedPlus (p : ℤ)).obj T.X₂).IsCoherent)
    (h₃ : ∀ p : ℕ,
      (((Scheme.Modules.pushforward f).rightDerivedPlus (p : ℤ)).obj T.X₃).IsCoherent)
    (p : ℕ) :
    (((Scheme.Modules.pushforward f).rightDerivedPlus (p : ℤ)).obj T.X₁).IsCoherent := by
  match p with
  | 0 =>
      have hZ : IsZero (⊤_ S.Modules) :=
        (isZero_zero S.Modules).of_iso (HasZeroObject.zeroIsoTerminal (C := S.Modules)).symm
      have hzc : (⊤_ S.Modules).IsCoherent :=
        ObjectProperty.prop_of_isZero
          (P := fun M : SheafOfModules.{u} S.ringCatSheaf => M.IsCoherent) hZ
      exact isCoherent_of_exact₄
        (f₀ := (0 : (⊤_ S.Modules) ⟶ (⊤_ S.Modules)))
        (f₁ := (0 : (⊤_ S.Modules) ⟶
          ((higherDirectImageDeltaFunctor f).functor 0).obj T.X₁))
        (f₂ := ((higherDirectImageDeltaFunctor f).functor 0).map T.f)
        (f₃ := ((higherDirectImageDeltaFunctor f).functor 0).map T.g)
        zero_comp zero_comp
        ((higherDirectImageDeltaFunctor f).map_f_comp_map_g (S := T) 0)
        (ShortComplex.exact_of_isZero_X₂ _ hZ)
        ((ShortComplex.exact_iff_mono _ rfl).2 ((higherDirectImageDeltaFunctor f).mono_map_f hT))
        ((higherDirectImageDeltaFunctor f).exact_map hT 0)
        hzc hzc (h₂ 0) (h₃ 0)
  | (q + 1) =>
      exact isCoherent_of_exact₄
        (f₀ := ((higherDirectImageDeltaFunctor f).functor q).map T.g)
        (f₁ := (higherDirectImageDeltaFunctor f).δ hT q)
        (f₂ := ((higherDirectImageDeltaFunctor f).functor (q + 1)).map T.f)
        (f₃ := ((higherDirectImageDeltaFunctor f).functor (q + 1)).map T.g)
        ((higherDirectImageDeltaFunctor f).map_g_δ hT q)
        ((higherDirectImageDeltaFunctor f).δ_map_f hT q)
        ((higherDirectImageDeltaFunctor f).map_f_comp_map_g (S := T) (q + 1))
        ((higherDirectImageDeltaFunctor f).exact_δ₁ hT q)
        ((higherDirectImageDeltaFunctor f).exact_δ₂ hT q)
        ((higherDirectImageDeltaFunctor f).exact_map hT (q + 1))
        (h₂ q) (h₃ q) (h₂ (q + 1)) (h₃ (q + 1))

/-- **The two-out-of-three condition for coherence of all the higher direct images.** For a short
exact sequence `0 ⟶ F₁ ⟶ F₂ ⟶ F₃ ⟶ 0` of `𝒪_X`-modules, if every higher direct image of two of
the three terms is coherent then the same holds for the third. -/
theorem forall_isCoherent_higherDirectImage_twoOutOfThree {X S : Scheme.{u}} (f : X ⟶ S)
    (T : ShortComplex X.Modules) (hT : T.ShortExact) :
    ((∀ q : ℕ, (((Scheme.Modules.pushforward f).rightDerivedPlus (q : ℤ)).obj T.X₁).IsCoherent) ∧
        (∀ q : ℕ,
          (((Scheme.Modules.pushforward f).rightDerivedPlus (q : ℤ)).obj T.X₂).IsCoherent) →
        ∀ q : ℕ, (((Scheme.Modules.pushforward f).rightDerivedPlus (q : ℤ)).obj T.X₃).IsCoherent)
      ∧ ((∀ q : ℕ,
            (((Scheme.Modules.pushforward f).rightDerivedPlus (q : ℤ)).obj T.X₁).IsCoherent) ∧
          (∀ q : ℕ,
            (((Scheme.Modules.pushforward f).rightDerivedPlus (q : ℤ)).obj T.X₃).IsCoherent) →
          ∀ q : ℕ,
            (((Scheme.Modules.pushforward f).rightDerivedPlus (q : ℤ)).obj T.X₂).IsCoherent)
      ∧ ((∀ q : ℕ,
            (((Scheme.Modules.pushforward f).rightDerivedPlus (q : ℤ)).obj T.X₂).IsCoherent) ∧
          (∀ q : ℕ,
            (((Scheme.Modules.pushforward f).rightDerivedPlus (q : ℤ)).obj T.X₃).IsCoherent) →
          ∀ q : ℕ,
            (((Scheme.Modules.pushforward f).rightDerivedPlus (q : ℤ)).obj T.X₁).IsCoherent) :=
  ⟨fun h q => isCoherent_higherDirectImage_X₃_of_shortExact f hT h.1 h.2 q,
    fun h q => isCoherent_higherDirectImage_X₂_of_shortExact f hT h.1 h.2 q,
    fun h q => isCoherent_higherDirectImage_X₁_of_shortExact f hT h.1 h.2 q⟩

/-! ### [Stacks, Tag 02O5] from the witness sheaves -/

/-- **The witness sheaves of [Stacks, Tag 01YI] for coherence of the higher direct images**, as a
`Prop`: for every proper morphism `f : X ⟶ S` onto an affine locally Noetherian scheme, every
integral closed subscheme `i : Z ⟶ X` and every generic point `ξ` of its range, there is a
coherent `𝒪_X`-module `𝒢` supported exactly on the range of `i`, whose stalk at `ξ` is killed by
the maximal ideal and has length one over the local ring at `ξ`, and all of whose higher direct
images along `f` are coherent. -/
def HasGenericCoherentWitness : Prop :=
  ∀ (X S : Scheme.{u}) (f : X ⟶ S), IsAffine S → IsLocallyNoetherian S → IsProper f →
    ∀ (Z : Scheme.{u}) (i : Z ⟶ X), IsClosedImmersion i → IsIntegral Z →
      ∀ ξ : X, IsGenericPoint ξ (Set.range i.base) →
        ∃ G : X.Modules, SheafOfModules.IsCoherent G ∧
          SheafOfModules.supp G = Set.range i.base ∧
          Stacks.ClosedImmersion.StalkKilledByMaximalIdeal G ξ ∧
          (letI : Module (X.presheaf.stalk ξ) (G.presheaf.stalk ξ) :=
            PresheafOfModules.instModuleCarrierStalkCommRingCatCarrierAbPresheafOpensCarrier
              (R := X.presheaf) G.val ξ
           Module.length (X.presheaf.stalk ξ) (G.presheaf.stalk ξ) = 1) ∧
          ∀ q : ℕ,
            (((Scheme.Modules.pushforward f).rightDerivedPlus (q : ℤ)).obj G).IsCoherent

/-- **[Stacks, Tag 02O5]'s first assertion for one morphism, from the witness sheaves for that
morphism.** For `f : X ⟶ S` proper onto an affine locally Noetherian base, every higher direct
image of every coherent module is coherent as soon as each integral closed subscheme of `X`
carries a witness sheaf. -/
theorem isCoherent_higherDirectImage_of_genericWitness {X S : Scheme.{u}} (f : X ⟶ S)
    [IsAffine S] [IsLocallyNoetherian S] [IsProper f]
    (hgeneric : ∀ (Z : Scheme.{u}) (i : Z ⟶ X), IsClosedImmersion i → IsIntegral Z →
      ∀ ξ : X, IsGenericPoint ξ (Set.range i.base) →
        ∃ G : X.Modules, SheafOfModules.IsCoherent G ∧
          SheafOfModules.supp G = Set.range i.base ∧
          Stacks.ClosedImmersion.StalkKilledByMaximalIdeal G ξ ∧
          (letI : Module (X.presheaf.stalk ξ) (G.presheaf.stalk ξ) :=
            PresheafOfModules.instModuleCarrierStalkCommRingCatCarrierAbPresheafOpensCarrier
              (R := X.presheaf) G.val ξ
           Module.length (X.presheaf.stalk ξ) (G.presheaf.stalk ξ) = 1) ∧
          ∀ q : ℕ,
            (((Scheme.Modules.pushforward f).rightDerivedPlus (q : ℤ)).obj G).IsCoherent)
    (F : X.Modules) (hF : F.IsCoherent) (p : ℕ) :
    (((Scheme.Modules.pushforward f).rightDerivedPlus (p : ℤ)).obj F).IsCoherent :=
  have : IsNoetherian X := isNoetherian_of_isProper_of_isAffine f
  Stacks.AlgebraicGeometry.CoherentDevissage.property_of_isCoherent_of_generic_stalk X
    (fun G => ∀ q : ℕ,
      (((Scheme.Modules.pushforward f).rightDerivedPlus (q : ℤ)).obj G).IsCoherent)
    (isCoherent_higherDirectImage_terminal f)
    (fun T hT _ _ _ => forall_isCoherent_higherDirectImage_twoOutOfThree f T hT)
    hgeneric F hF p

/-- **The affine-base case of [Stacks, Tag 02O5]'s first assertion from the witness sheaves.** -/
theorem higherDirectImageIsCoherentOverAffineBase_of_genericWitness
    (hgen : HasGenericCoherentWitness.{u}) :
    HigherDirectImageIsCoherentOverAffineBase.{u} := by
  intro X S f hS hN hf F hF p
  have : IsAffine S := hS
  have : IsLocallyNoetherian S := hN
  have : IsProper f := hf
  exact isCoherent_higherDirectImage_of_genericWitness f
    (fun Z i hi hZ ξ hξ => hgen X S f ‹_› ‹_› ‹_› Z i hi hZ ξ hξ) F hF p

/-- **[Stacks, Tag 02O5]'s first assertion from the witness sheaves.** -/
theorem higherDirectImageIsCoherent_of_genericWitness (hgen : HasGenericCoherentWitness.{u}) :
    HigherDirectImageIsCoherent.{u} :=
  higherDirectImageIsCoherent_of_overAffineBase
    (higherDirectImageIsCoherentOverAffineBase_of_genericWitness hgen)

/-- **[Stacks, Tag 02O6]'s conclusion from the witness sheaves.** For `f : X ⟶ S` proper onto an
affine locally Noetherian base and `F` coherent, `Hⁱ(X, F)` is a finite `Γ(S, ⊤)`-module. -/
theorem moduleFinite_cohomology_of_genericWitness (hgen : HasGenericCoherentWitness.{u})
    {X S : Scheme.{u}} (f : X ⟶ S) [IsProper f] [IsAffine S] [IsLocallyNoetherian S]
    (F : X.Modules) [F.IsCoherent] (i : ℕ) :
    Module.Finite Γ(S, ⊤) ((ModuleCat.restrictScalars f.appTop.hom).obj
      (((moduleGlobalSections X).rightDerived i).obj F)) :=
  ProperCoherenceFrontier.moduleFinite_cohomology_of_integralIdeals
    (higherDirectImageIsCoherentOnIntegralIdeals_of_overAffineBase
      (higherDirectImageIsCoherentOverAffineBase_of_genericWitness hgen)) f F i

end AlgebraicGeometry.ProperCoherenceWitness

end
