module

public import StacksFrontier.AlgebraicGeometry.AmplePullbackPart1.TensorPowerTensor
public import StacksFrontier.AlgebraicGeometry.FiniteDirectImageCoherent.Basic
public import StacksFrontier.AlgebraicGeometry.LocallyProjectiveCoherentImage.Basic
public import StacksFrontier.AlgebraicGeometry.ProjectiveSpace.AmpleTwistingSheaf
public import StacksFrontier.AlgebraicGeometry.ProperCoherenceWitness.LerayCollapse
public import StacksFrontier.AlgebraicGeometry.ProperCoherentImage.ChowProjective
public import StacksFrontier.AlgebraicGeometry.RelativeAmple.CompositionPermanence
public import StacksFrontier.AlgebraicGeometry.RelativeAmpleTwistVanishing.Basic
public import StacksFrontier.AlgebraicGeometry.RelativeSerreVanishing.Basic
public import StacksFrontier.AlgebraicGeometry.TwistInvertibleOverBase.Basic

/-!
# The Chow twist of an integral closed subscheme and the coherence of its higher direct images

Let `f : X ⟶ S` be proper onto an affine locally Noetherian base and let `i : Z ⟶ X` be a closed
immersion. This file carries out **steps 4 to 6 of the source's proof of [Stacks, Tag 02O5]** —
everything about the witness sheaf of [Stacks, Tag 01YI] except the three conditions on its stalk
at the generic point.

Chow's lemma supplies a proper surjective `π : Y ⟶ Z`, an isomorphism above a dense open `U ⊆ Z`,
with **both** `π` and `π ≫ i ≫ f` H-projective. The H-projective presentation of `π ≫ i ≫ f`
over the affine `S` gives `ℒ = ι ^* 𝒪(1)`, relatively ample for `π ≫ i ≫ f` and hence — the base
only getting smaller — for `π`. The vanishing theorem [Stacks, Tag 02O1] then chooses a power
`n` with `R ᵖ π_* (𝒪_Y ⊗ ℒ ^⊗ n) = 0` for every `p > 0`, and

`𝒢 = i_* π_* (𝒪_Y ⊗ ℒ ^⊗ n) = (π ≫ i)_* (𝒪_Y ⊗ ℒ ^⊗ n)`

has all of its higher direct images along `f` coherent: the relative Leray collapse of
`Stacks.AlgebraicGeometry.ProperCoherenceWitnessLeray` turns `R ᵖ (i ≫ f)_* π_* (…)` into
`R ᵖ (π ≫ i ≫ f)_* (…)`, which is coherent by the projective case [Stacks, Tag 02O4]; the closed
immersion is then crossed by
`…ClosedImmersionRelativeLeray.forall_isCoherent_rightDerived_pushforward_iff`.

## Main results

All of the following live in the namespace `AlgebraicGeometry.ProperCoherenceWitness`.

* `exists_isRelativelyAmple_of_isProjectiveMorphism`: an H-projective morphism
  onto an **affine** base carries a relatively ample invertible module, namely the pullback of
  the hyperplane sheaf along the presentation. **Unconditional.**
* `exists_chowTwist_forall_isCoherent`: the data above — `Y`, `π`, the dense open `U`, the twist
  `M`, the coherence of `π_* M` and the coherence of every `R ᵖ f_* ((π ≫ i)_* M)`. Carries
  `haffine` and nothing else.

## Implementation notes

**No `@[stacks 02O5]` attribute is attached to anything here**, for two reasons. The hypothesis
`Stacks.AlgebraicGeometry.RelativeAmpleTwistVanishing.VanishingOverAffineBase` is carried — it is
the one input of [Stacks, Tag 02O1] that is not discharged in this repository, and it is passed
straight through, so that a proof of it turns these statements into unconditional ones by a single
application. And the conclusion is not [Stacks, Tag 02O5]'s: what is produced here is the
cohomological clause of the witness sheaf of
`AlgebraicGeometry.ProperCoherenceWitness.HasGenericCoherentWitness`, not that whole predicate.

**What is still owed for `HasGenericCoherentWitness`**: the three conditions at the generic point
`ξ` of `Set.range i.base`, namely `SheafOfModules.supp 𝒢 = Set.range i.base`,
`Stacks.ClosedImmersion.StalkKilledByMaximalIdeal 𝒢 ξ` and `Module.length … = 1`. The input this
file hands them is the conjunction `Dense U`, `IsIso (π ∣_ U)` and `IsInvertibleModule Y M`: on
`U` the module `π_* M` is the direct image of an invertible module along an isomorphism, hence
invertible, and `ξ` lies in `U` because `U` is a nonempty open of the irreducible `Z`. That half
is **not** proved here.

**Only the vanishing along `π` is used, not the vanishing along `π ≫ i ≫ f`.** The source's proof
chooses `n` killing both, because it packages the conclusion as *"the higher direct images vanish
and the direct image is coherent"*. Here the composite's contribution is taken from
[Stacks, Tag 02O4], which gives coherence of `R ᵖ (π ≫ i ≫ f)_*` in **every** degree with no
vanishing needed, so one application of [Stacks, Tag 02O1] suffices.

## References

* [Stacks Project, Tag 0200](https://stacks.math.columbia.edu/tag/0200)
* [Stacks Project, Tag 01VT](https://stacks.math.columbia.edu/tag/01VT)
* [Stacks Project, Tag 01YI](https://stacks.math.columbia.edu/tag/01YI)
* [Stacks Project, Tag 02O1](https://stacks.math.columbia.edu/tag/02O1)
* [Stacks Project, Tag 02O4](https://stacks.math.columbia.edu/tag/02O4)
* [Stacks Project, Tag 02O5](https://stacks.math.columbia.edu/tag/02O5)
* [Stacks Project, Tag 0C4L](https://stacks.math.columbia.edu/tag/0C4L)
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits
open AlgebraicGeometry
open Stacks.Ample Stacks.RelativeVeryAmple Stacks.AmpleProjectiveImmersion
open Stacks.AlgebraicGeometry.ClosedImmersionRelativeLeray (
  forall_isCoherent_rightDerived_pushforward_iff)
open Stacks.AlgebraicGeometry.ProperCoherenceWitnessLeray (
  forall_isCoherent_rightDerived_pushforward_pushforward_of_isZero isCoherentPlus_of_isCoherent)
open Stacks.AlgebraicGeometry.RelativeAmpleTwistVanishing (
  exists_isZero_rightDerivedPlus_pushforward_tensorPowModule)

universe u

namespace AlgebraicGeometry.ProperCoherenceWitness

attribute [local instance 10000] HasDerivedCategory.standard

/-! ### The relatively ample sheaf of an H-projective presentation -/

/-- **An H-projective morphism onto an affine base carries a relatively ample invertible
module.** If `h : Y ⟶ S` is H-projective and `S` is affine, the pullback `ι ^* 𝒪(1)` of the
hyperplane sheaf along the closed immersion `ι : Y ⟶ ℙⁿ_S` presenting `h` is invertible and ample
relative to `h`. **No hypothesis beyond the two displayed.**

Invertibility is `AlgebraicGeometry.isInvertibleModule_pullback_projectiveSpaceTwistingSheaf`.
For relative ampleness, the presentation *is* the clause
`Stacks.AmpleProjectiveImmersion.HasImmersionTwistOver` of [Stacks, Tag 01VS] at degree `1` —
a closed immersion is an immersion, the two spellings of the structure morphism of `ℙⁿ_S` agree,
and `Stacks.Ample.tensorPowModuleOneIso` identifies the first tensor power with the module
itself — so
`Stacks.AlgebraicGeometry.ProjectiveSpace.isRelativelyAmple_of_exists_hasImmersionTwistOver`,
which is [Stacks, Tag 01VT] (5) ⟹ (2) with no named input left, applies. -/
theorem exists_isRelativelyAmple_of_isProjectiveMorphism {Y S : Scheme.{u}}
    [IsAffine S] (h : Y ⟶ S) (hh : IsProjectiveMorphism h) :
    ∃ L : Y.Modules, ∃ hL : IsInvertibleModule Y L,
      letI : IsInvertibleModule Y L := hL
      Stacks.RelativeAmple.IsRelativelyAmple h L := by
  obtain ⟨n, ι, hι, hcomm⟩ := hh
  have hci : IsClosedImmersion ι := hι
  have hProper : IsProper h := isProper_of_isProjectiveMorphism h ⟨n, ι, hι, hcomm⟩
  refine ⟨(Scheme.Modules.pullback ι).obj (projectiveSpaceTwistingSheaf n S), inferInstance, ?_⟩
  exact Stacks.ProjectiveSpace.isRelativelyAmple_of_exists_hasImmersionTwistOver h _
    inferInstance ⟨1, le_rfl, n, ι, inferInstance, hcomm, ⟨tensorPowModuleOneIso Y _⟩⟩

/-! ### The Chow twist and the coherence of its higher direct images -/

/-- **Steps 4 to 6 of the source's proof of [Stacks, Tag 02O5].** Let `f : X ⟶ S` be proper onto
an affine locally Noetherian base and let `i : Z ⟶ X` be a closed immersion. Then there are a
scheme `Y`, a **surjective** `π : Y ⟶ Z`, a **dense** open `U ⊆ Z` above which `π` is an
**isomorphism**, and an **invertible, coherent** `𝒪_Y`-module `M`, such that `π_* M` is coherent
and **every** higher direct image of `(π ≫ i)_* M = i_* π_* M` along `f` is coherent.

The module `M` is `𝒪_Y ⊗ ℒ ^⊗ n` for `ℒ` the relatively ample sheaf of the H-projective
presentation and `n` the bound of [Stacks, Tag 02O1]; the source's `𝒢` is `(π ≫ i)_* M`.

`haffine` — [Stacks, Tag 02O1] over an affine base, one degree at a time — is the single
hypothesis, and it enters only through
`…RelativeAmpleTwistVanishing.exists_isZero_rightDerivedPlus_pushforward_tensorPowModule`.
Everything else is unconditional: Chow's lemma in the H-projective shape
(`AlgebraicGeometry.ProperCoherentImage.exists_isProjectiveMorphism_chowModification_subscheme`),
[Stacks, Tag 0C4L] for the passage from relative ampleness over `S` to relative ampleness over
`Z`, [Stacks, Tag 02O4] for the projective case, and the two Leray collapses. -/
theorem exists_chowTwist_forall_isCoherent
    (haffine : Stacks.AlgebraicGeometry.RelativeAmpleTwistVanishing.VanishingOverAffineBase.{u})
    {X S : Scheme.{u}} (f : X ⟶ S) [IsAffine S] [IsLocallyNoetherian S] [IsProper f]
    {Z : Scheme.{u}} (i : Z ⟶ X) [IsClosedImmersion i] :
    ∃ (Y : Scheme.{u}) (π : Y ⟶ Z) (U : Z.Opens) (M : Y.Modules),
      Surjective π ∧ Dense (U : Set Z) ∧ IsIso (π ∣_ U) ∧
        IsInvertibleModule Y M ∧ M.IsCoherent ∧
        ((Scheme.Modules.pushforward π).obj M).IsCoherent ∧
        ∀ q : ℕ, (((Scheme.Modules.pushforward f).rightDerivedPlus (q : ℤ)).obj
          ((Scheme.Modules.pushforward (π ≫ i)).obj M)).IsCoherent := by
  obtain ⟨Y, π, U, hπ, hπsurj, hprojπ, hprojcomp, hdense, hiso⟩ :=
    ProperCoherentImage.exists_isProjectiveMorphism_chowModification_subscheme f i
  have hπp : IsProper π := hπ
  have hNZ : IsNoetherian Z := ProperCoherentImage.isNoetherian_of_isProper_of_isAffine (i ≫ f)
  have hpropercomp : IsProper (π ≫ i ≫ f) := isProper_of_isProjectiveMorphism _ hprojcomp
  have hNY : IsNoetherian Y :=
    ProperCoherentImage.isNoetherian_of_isProper_of_isAffine (π ≫ i ≫ f)
  -- Step B: the relatively ample sheaf, for the composite and hence for `π`.
  obtain ⟨L, hLinv, hLample⟩ :=
    exists_isRelativelyAmple_of_isProjectiveMorphism (π ≫ i ≫ f) hprojcomp
  have hLπ : Stacks.RelativeAmple.IsRelativelyAmple π L :=
    Stacks.RelativeAmpleCompositionPermanence.isRelativelyAmple_of_comp π (i ≫ f) L hLample
      inferInstance
  -- Step C: the power of `ℒ` killing the positive higher direct images along `π`.
  have hO : (unitModule Y).IsCoherent :=
    Stacks.AlgebraicGeometry.CoherenceCriteria.structureSheaf_isCoherent Y
  obtain ⟨n₀, hn₀⟩ :=
    exists_isZero_rightDerivedPlus_pushforward_tensorPowModule haffine π (unitModule Y) L hLπ
  have hpow : AlgebraicGeometry.SheafOfModules.IsInvertible Y.presheaf Y.ringCatSheaf.2
      (tensorPowModule Y L (n₀ : ℤ)) := isInvertibleModule_tensorPowModule Y L (n₀ : ℤ)
  have hMcoh : (Stacks.RelativeVeryAmple.tensorModules Y (unitModule Y)
      (tensorPowModule Y L (n₀ : ℤ))).IsCoherent :=
    AlgebraicGeometry.SheafOfModules.isCoherent_tensorSheaf_of_isInvertible Y
      (unitModule Y) (tensorPowModule Y L (n₀ : ℤ))
  have hMinv : IsInvertibleModule Y (Stacks.RelativeVeryAmple.tensorModules Y (unitModule Y)
      (tensorPowModule Y L (n₀ : ℤ))) :=
    Stacks.AmplePullbackPart1.isInvertibleModule_tensorModules Y (unitModule Y)
      (tensorPowModule Y L (n₀ : ℤ))
  refine ⟨Y, π, U, Stacks.RelativeVeryAmple.tensorModules Y (unitModule Y)
    (tensorPowModule Y L (n₀ : ℤ)), hπsurj, hdense, hiso, hMinv, hMcoh, ?_, ?_⟩
  · -- `π_* M` is coherent: [Stacks, Tag 02O4] in degree zero.
    have h0 := LocallyProjectiveCoherentImage.isCoherent_rightDerived_of_isProjectiveMorphism
      π hprojπ _ hMcoh 0
    have := h0
    exact Stacks.AlgebraicGeometry.CoherentDevissage.isCoherent_of_iso (R := Z.ringCatSheaf)
      (Stacks.AlgebraicGeometry.DerivedPushforward.pushforwardRightDerivedZeroObjIso π _).symm
  · -- Steps D and E's cohomological half.
    intro q
    exact isCoherentPlus_of_isCoherent f _ q ((forall_isCoherent_rightDerived_pushforward_iff i f
      ((Scheme.Modules.pushforward π).obj _)).2
      (forall_isCoherent_rightDerived_pushforward_pushforward_of_isZero π (i ≫ f) _
        (fun m hm => (Stacks.DerivedIndexing.isZero_rightDerived_obj_iff _ m _).2
          (hn₀ n₀ m le_rfl hm))
        (fun m => LocallyProjectiveCoherentImage.isCoherent_rightDerived_of_isProjectiveMorphism
          (π ≫ i ≫ f) hprojcomp _ hMcoh m)) q)

end AlgebraicGeometry.ProperCoherenceWitness

end
