module

public import StacksCore.Tactic.StacksAttribute
public import StacksFrontier.AlgebraicGeometry.Spaces.CoherentDerivedComparison
public import StacksFrontier.AlgebraicGeometry.Spaces.CoherentSchemeTheoreticSupport
public import StacksFrontier.AlgebraicGeometry.Spaces.FiniteClosedImmersion
public import StacksFrontier.AlgebraicGeometry.Spaces.FiniteDirectImageCoherence
public import StacksFrontier.AlgebraicGeometry.Spaces.LocallyNoetherianFiniteType
public import StacksFrontier.AlgebraicGeometry.Spaces.Perfect.ProperModuleSupport

/-!
# Coherence of the higher direct images of a module with proper support

Let `f : X ⟶ Y` be a morphism of algebraic spaces over a scheme `S` which is locally of finite
type, with `Y` locally Noetherian, and let `𝓕` be a coherent `𝒪_X`-module whose support is
proper over `Y`.  **Stacks 08GC** asserts that `R^p f_*𝓕` is a coherent `𝒪_Y`-module for every
`p ≥ 0`.  That is proved here, following the source: Stacks 0CZI writes `𝓕 = i_*𝓖` for a closed
subspace `i : Z → X` with `Z` proper over `Y` and `𝓖` quasi-coherent of finite type on `Z`;
Stacks 07UH makes the higher direct images along `i` vanish; the relative Leray spectral
sequence of Stacks 0734 then degenerates and identifies `R^p f_*𝓕` with `R^p (f ∘ i)_*𝓖`,
which is coherent by Stacks 08AR.

The higher direct images are `CategoryTheory.Functor.rightDerived` of
`AlgebraicGeometry.Space.modulePushforward`, at the module universe `u` of the structure rings
where that functor lives; injective resolutions are available there by
`AlgebraicGeometry.Space.hasInjectiveResolutions_modules`, which is what makes the conclusion
of this tag writable at all.  See the implementation notes.

## Main definitions

* `AlgebraicGeometry.Space.CoherentHigherDirectImageOfProper`: **Stacks 08AR** for a fixed
  target, as a property of that target: the higher direct images of a coherent module along a
  proper morphism to it are coherent.  This development does not prove it; it is the hypothesis
  `h08AR` below.
* `AlgebraicGeometry.Space.HigherDirectImageCompOfAcyclic`: the degeneration of the relative
  Leray spectral sequence of **Stacks 0734** that the source uses, as a property of `f`: for a
  morphism `i` into `X` whose higher direct images of `𝓖` vanish in positive degrees,
  `R^p f_*(i_*𝓖) ≅ R^p (i ≫ f)_*𝓖` for every `p`.  It is the hypothesis `h0734` below.

## Main results

* `AlgebraicGeometry.Space.isCoherent_rightDerived_modulePushforward_of_hasProperSupport`:
  **Stacks 08GC**, granted the named hypotheses `h03DW`, `h08AR` and `h0734`.

## Implementation notes

**That `R^p f_*𝓕` can be written.**  `AlgebraicGeometry.Space.modulePushforward` is a functor
`Modules.{u, u} ⥤ Modules.{u, u}`, its module universe pinned to the universe `u` of the
structure rings, and `AlgebraicGeometry.Space.hasInjectiveResolutions_modules` supplies
`HasInjectiveResolutions` for `Modules.{u, u}` through `EssentiallySmall.{u}` of the small
étale site — no smallness of that site is needed.  So
`(modulePushforward B S hS f).rightDerived p` is a functor at exactly the universe at which
`AlgebraicGeometry.Space.IsCoherent` of `Modules.{u, u}` is available, and the conclusion of
this tag is a statement about the same objects the hypotheses are about.  The instance is
introduced by `have :=` inside the statements, as in
`AlgebraicGeometry.Space.isZero_rightDerived_modulePushforward_of_isFinite` and
`AlgebraicGeometry.Space.moduleHigherPushforwardChartBaseChangeIso`, since it is a theorem and
not an instance.

The contrary remark in the implementation notes of
`StacksFrontier.AlgebraicGeometry.Spaces.ProperCohomologyFinite` — that there are no higher direct
images of modules along a morphism of algebraic spaces at all — is about the module universe
`max (u + 1) w` at which `AlgebraicGeometry.Space.cohomologyOverBase` lives, where
`modulePushforward` indeed does not exist.  At module universe `u` the higher direct images are
available and are used in several files of this tree.

**Why Stacks 0734 is carried.**  `Stacks.Cohomology.Leray.exists_relativeLeraySpectralSequence`
is the library's form of Stacks 0734, and it is stated for ringed topoi
`AlgebraicGeometry.RingedTopos.{u, u, u}`, all three universes equal; the small étale ringed
topos of an algebraic space is `AlgebraicGeometry.RingedTopos.{u, u + 1, u}`
(`AlgebraicGeometry.Space.smallEtaleRingedTopos`), so it is not an instance of that statement,
and a morphism of algebraic spaces induces no functor between the small étale sites along which
the site-level comparison
`Stacks.Cohomology.HigherDirectImage.rightDerivedPushforwardToSheafIso` could be used either.
Hence `h0734`, which asks only for the consequence the source draws from the spectral sequence
and asks for it only under the vanishing that Stacks 07UH supplies.

**Why Stacks 08AR is carried.**  It has no presence in this library, nor has its scheme-level
counterpart Stacks 02O5; the implementation notes of
`StacksDraft.AlgebraicGeometry.F3.HigherDirectImageCoherent.Basic` record that dévissage for
coherent modules, Chow's lemma, the relative Leray spectral sequence and the vanishing for
relatively ample invertible sheaves are all missing.  It is carried in its own shape, with
`𝓖` coherent and the conclusion coherent, so nothing of Stacks 07UB is smuggled into it.

**What is not carried.**  Stacks 0CZI, Stacks 07UH, Stacks 04ZK and Stacks 07UG are applied,
not assumed, and Stacks 0CZI carries no input of its own.  The one such input appearing here is
`h03DW`, the input of the vanishing half of Stacks 07UH, quoted in the form that lemma takes
it.  Coherence of `𝓖` is *derived*: the source asserts it, and here `X` is locally
Noetherian by Stacks 04ZK from `hf` and `hY`, whence
`AlgebraicGeometry.Space.isCoherent_of_modulePushforward_closedSubspace` — the step of
Stacks 07UG — upgrades the quasi-coherent finite type module that Stacks 0CZI produces to a
coherent one.

## References

* [Stacks Project, Lemma 75.7.10 (Tag 08GC)](https://stacks.math.columbia.edu/tag/08GC)
* [Stacks Project, Lemma 75.7.7 (Tag 0CZI)](https://stacks.math.columbia.edu/tag/0CZI)
* [Stacks Project, Lemma 69.20.2 (Tag 08AR)](https://stacks.math.columbia.edu/tag/08AR)
* [Stacks Project, Lemma 69.12.9 (Tag 07UH)](https://stacks.math.columbia.edu/tag/07UH)
* [Stacks Project, Lemma 21.14.7 (Tag 0734)](https://stacks.math.columbia.edu/tag/0734)
* [Stacks Project, Tag 07UG](https://stacks.math.columbia.edu/tag/07UG)
* [Stacks Project, Tag 07UB](https://stacks.math.columbia.edu/tag/07UB)
* [Stacks Project, Tag 04ZK](https://stacks.math.columbia.edu/tag/04ZK)
* [Stacks Project, Tag 03DW](https://stacks.math.columbia.edu/tag/03DW)
* [Stacks Project, Tag 02O5](https://stacks.math.columbia.edu/tag/02O5)
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits

attribute [local instance 5000] SheafOfModules.instAbelian

attribute [local instance 5000] CategoryTheory.IsGrothendieckAbelian.enoughInjectives

universe u

namespace AlgebraicGeometry.Space

variable (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)

/-! ### The two carried inputs -/

/-- **Stacks 08AR as a property of the target.**  An algebraic space `Y` over `S` has coherent
higher direct images from proper morphisms when for every proper `g : Z ⟶ Y` and every coherent
`𝒪_Z`-module `𝓖` the module `R^p g_*𝓖` is coherent, in every degree `p`.

Stacks 08AR says that every locally Noetherian `Y` has this property.  Neither it nor its
scheme-level counterpart Stacks 02O5 is available in this library, so it is carried as the
hypothesis `h08AR` of
`AlgebraicGeometry.Space.isCoherent_rightDerived_modulePushforward_of_hasProperSupport`. -/
def CoherentHigherDirectImageOfProper (Y : AlgebraicSpaces B S hS) : Prop :=
  ∀ (Z : AlgebraicSpaces B S hS) (g : Z ⟶ Y), IsProper B S hS g.hom →
    ∀ G : Modules.{u, u} B S hS Z.1 Z.2, IsCoherent B S hS Z.1 Z.2 G → ∀ p : ℕ,
      have := hasInjectiveResolutions_modules B S hS Z.1 Z.2
      IsCoherent B S hS Y.1 Y.2 (((modulePushforward B S hS g).rightDerived p).obj G)

/-- **The degeneration of the relative Leray spectral sequence of Stacks 0734 that Stacks 08GC
uses, as a property of `f : X ⟶ Y`.**  For every closed immersion `i : Z ⟶ X` and every
`𝒪_Z`-module `𝓖` whose higher direct images along `i` vanish in positive degrees, the
identification

`R^p f_*(i_*𝓖) ≅ R^p (i ≫ f)_*𝓖`

holds in every degree `p`.

This is what the source draws from Stacks 0734: with `R^q i_*𝓖 = 0` for `q > 0` the second page
`R^p f_*(R^q i_*𝓖)` of the spectral sequence is concentrated in the row `q = 0`, so the spectral
sequence degenerates onto its abutment `R^{p+q} (i ≫ f)_*𝓖`.  Stacks 0734 needs nothing of `i`
beyond the vanishing, so the closed immersion hypothesis is not used by the mathematics; it is
there to keep the hypothesis no stronger than the one application below makes of it.  The library's
form of Stacks 0734, `Stacks.Cohomology.Leray.exists_relativeLeraySpectralSequence`, is stated
for ringed topoi with all three universes equal and does not apply to the small étale ringed
topos of an algebraic space; see the implementation notes of this file. -/
def HigherDirectImageCompOfAcyclic {X Y : AlgebraicSpaces B S hS} (f : X ⟶ Y) : Prop :=
  ∀ (Z : AlgebraicSpaces B S hS) (i : Z ⟶ X), IsClosedImmersion B S hS i.hom →
    ∀ G : Modules.{u, u} B S hS Z.1 Z.2,
    (∀ q : ℕ, 0 < q →
      have := hasInjectiveResolutions_modules B S hS Z.1 Z.2
      IsZero (((modulePushforward B S hS i).rightDerived q).obj G)) →
    ∀ p : ℕ,
      have := hasInjectiveResolutions_modules B S hS X.1 X.2
      have := hasInjectiveResolutions_modules B S hS Z.1 Z.2
      Nonempty (((modulePushforward B S hS f).rightDerived p).obj
          ((modulePushforward B S hS i).obj G) ≅
        ((modulePushforward B S hS (i ≫ f)).rightDerived p).obj G)

/-! ### Stacks 08GC -/

/-- **Stacks 08GC.**  Let `S` be a scheme, let `f : X ⟶ Y` be a morphism of algebraic spaces
over `S` which is locally of finite type with `Y` locally Noetherian, and let `𝓕` be a coherent
`𝒪_X`-module whose support is proper over `Y`.  Then `R^p f_*𝓕` is a coherent `𝒪_Y`-module for
every `p`.

The proof is the source's.  Properness of the support feeds Stacks 0CZI,
`AlgebraicGeometry.Space.hasProperSupport_tfae`, whose third condition produces a closed
subspace `Z ⊆ X` proper over `Y` and a quasi-coherent `𝒪_Z`-module `𝓖` of finite type with
`i_*𝓖 ≅ 𝓕`, where `i : Z → X` is the inclusion; `𝓖` is coherent because `X` is locally
Noetherian by Stacks 04ZK, which is where `hf` and `hY` are used, so that the step of
Stacks 07UG applies.  A closed immersion is finite by Stacks 081Y, so the higher direct images
along `i` vanish by the vanishing half of Stacks 07UH; `h0734` then identifies `R^p f_*(i_*𝓖)`
with `R^p (i ≫ f)_*𝓖`, which `h08AR` makes coherent, and coherence transports along the two
isomorphisms because it is invariant under isomorphism of modules.

The three carried inputs are `h03DW`, the input of the vanishing half of Stacks 07UH; `h08AR`,
Stacks 08AR; and `h0734`, the degeneration of the relative Leray spectral sequence.  See the
module documentation for each. -/
@[stacks 08GC "granted three named hypotheses, none of them this conclusion. (1) h08AR, \
Stacks 08AR itself — coherence of the higher direct images of a coherent module along a proper \
morphism to Y — which has no presence in this library, nor has its scheme-level counterpart \
Stacks 02O5, the dévissage for coherent modules, Chow's lemma and the vanishing for relatively \
ample invertible sheaves that would prove it all being absent; it is carried in its own shape, \
with the module coherent and the conclusion coherent. (2) h0734, the degeneration of the \
relative Leray spectral sequence of Stacks 0734 that the source's last step is, namely \
R^p f_*(i_* G) = R^p (f ∘ i)_* G when the higher direct images along i vanish; the formalized \
Stacks 0734 is stated for ringed topoi with all three universes equal and the small étale \
ringed topos of an algebraic space is RingedTopos u (u+1) u, so it does not apply, and the \
vanishing that h0734 asks for is discharged here from Stacks 07UH. (3) h03DW, the étale-affine \
case of Stacks 03DW, which is the hypothesis of the vanishing half of the formalized Stacks 07UH \
and is quoted in the form that lemma takes it. \
Stacks 0CZI, Stacks 07UH, Stacks 081Y, Stacks 04ZK and the coherence step of Stacks 07UG are \
applied and not assumed, so the source's hypotheses are all consumed: proper support is the \
input of Stacks 0CZI, and f locally of finite type together with Y locally Noetherian give \
local Noetherianity of X by Stacks 04ZK, which is what makes the module of Stacks 0CZI \
coherent"]
theorem isCoherent_rightDerived_modulePushforward_of_hasProperSupport
    {X Y : AlgebraicSpaces B S hS} (f : X ⟶ Y)
    (hf : IsLocallyOfFiniteType B S hS f.hom)
    (hY : HasEtaleLocalProperty B S hS Y.1 (fun T : Scheme.{u} => IsLocallyNoetherian T))
    (F : Modules.{u, u} B S hS X.1 X.2) (hF : IsCoherent B S hS X.1 X.2 F)
    (hsupp : HasProperSupport B S hS X.2 Y.2 f.hom hf ((SheafOfModules.toSheaf _).obj F))
    (h03DW : ∀ (Z : ClosedSubspaces B S hS X.1)
      (hrep : yoneda.relativelyRepresentable (closedSubspaceInclusion B S hS X Z).hom)
      (G : Modules.{u, u} B S hS (closedSubspaceToSpace B S hS X Z).1
        (closedSubspaceToSpace B S hS X Z).2) (n : ℕ),
      ChartwiseIsZeroHigherDirectImage B S hS (closedSubspaceInclusion B S hS X Z) hrep G n)
    (h08AR : CoherentHigherDirectImageOfProper B S hS Y)
    (h0734 : HigherDirectImageCompOfAcyclic B S hS f) (p : ℕ) :
    have := hasInjectiveResolutions_modules B S hS X.1 X.2
    IsCoherent B S hS Y.1 Y.2 (((modulePushforward B S hS f).rightDerived p).obj F) := by
  have _hFc := hF
  have _hFcs := hF.toIsCoherentOnSite
  have _hinjX := hasInjectiveResolutions_modules B S hS X.1 X.2
  change IsCoherent B S hS Y.1 Y.2 (((modulePushforward B S hS f).rightDerived p).obj F)
  obtain ⟨Z, G, hGqc, -, hZp, ⟨e⟩⟩ :=
    ((hasProperSupport_tfae B S hS X Y f.hom hf F hF.toIsQuasicoherentOnSite
      (isFiniteTypeOnSite_of_isCoherentOnSite B S hS X F)
      hF.toIsCoherentOnSite.isFiniteType).out 1 3).1 hsupp
  have hXn := isLocallyNoetherian_of_isLocallyOfFiniteType B S hS X.2 Y.2 f.hom hf hY
  have hGcoh := isCoherent_of_modulePushforward_closedSubspace B S hS X hXn F Z G hGqc e
  have hfin : IsFinite B S hS (closedSubspaceInclusion B S hS X Z).hom :=
    isFinite_of_isClosedImmersion B S hS _ Z.2.2
  have hiso := (h0734 (closedSubspaceToSpace B S hS X Z)
    (closedSubspaceInclusion B S hS X Z) Z.2.2 G
    (fun q _ => isZero_rightDerived_modulePushforward_of_isFinite B S hS
      (closedSubspaceInclusion B S hS X Z) hfin G q (h03DW Z _ G q)) p).some
  have hcoh := h08AR (closedSubspaceToSpace B S hS X Z)
    (closedSubspaceInclusion B S hS X Z ≫ f) hZp G hGcoh p
  exact (isCoherent.{u, u} B S hS Y.1 Y.2).prop_of_iso
    (((modulePushforward B S hS f).rightDerived p).mapIso e)
    ((isCoherent.{u, u} B S hS Y.1 Y.2).prop_of_iso hiso.symm hcoh)

end AlgebraicGeometry.Space

end
