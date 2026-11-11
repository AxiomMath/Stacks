module

public import StacksCore.Tactic.StacksAttribute
public import StacksFrontier.AlgebraicGeometry.Spaces.CoherentDerivedComparison
public import StacksFrontier.AlgebraicGeometry.Spaces.CoherentSchemeTheoreticSupport
public import StacksFrontier.AlgebraicGeometry.Spaces.FiniteClosedImmersion
public import StacksFrontier.AlgebraicGeometry.Spaces.FiniteDirectImageCoherence
public import StacksFrontier.AlgebraicGeometry.Spaces.LocallyNoetherianFiniteType
public import StacksFrontier.AlgebraicGeometry.Spaces.Perfect.ProperModuleSupport

/-!
# The inputs of Stacks 08GC as properties of the target and of the morphism

Let `f : X ⟶ Y` be a morphism of algebraic spaces over a scheme `S` which is locally of finite
type, with `Y` locally Noetherian, and let `𝓕` be a coherent `𝒪_X`-module whose support is
proper over `Y`.  **Stacks 08GC** asserts that `R^p f_*𝓕` is a coherent `𝒪_Y`-module for every
`p ≥ 0`.  The source's proof writes `𝓕 = i_*𝓖` for a closed subspace `i : Z → X` proper over `Y`
(Stacks 0CZI), uses that the higher direct images along `i` vanish (Stacks 07UH), the
degeneration of the relative Leray spectral sequence (Stacks 0734) and Stacks 08AR.  This file
names the last two inputs as properties, so that the reduction can be stated against them.

Stacks 08GC itself is
`AlgebraicGeometry.Space.isCoherent_higherDirectImage_of_hasProperSupport`; both properties below
are proved: `AlgebraicGeometry.Space.coherentHigherDirectImageOfProper_of_isLocallyNoetherian`
(Stacks 08AR over a locally Noetherian target) and
`AlgebraicGeometry.Space.higherDirectImageCompOfAcyclic` (Stacks 0734).

The higher direct images are `CategoryTheory.Functor.rightDerived` of
`AlgebraicGeometry.Space.modulePushforward`, at the module universe `u` of the structure rings
where that functor lives; injective resolutions are available there by
`AlgebraicGeometry.Space.hasInjectiveResolutions_modules`.

## Main definitions

* `AlgebraicGeometry.Space.CoherentHigherDirectImageOfProper`: **Stacks 08AR** for a fixed
  target, as a property of that target: the higher direct images of a coherent module along a
  proper morphism to it are coherent.
* `AlgebraicGeometry.Space.HigherDirectImageCompOfAcyclic`: the degeneration of the relative
  Leray spectral sequence of **Stacks 0734** that the source uses, as a property of `f`: for a
  closed immersion `i` into `X` whose higher direct images of `𝓖` vanish in positive degrees,
  `R^p f_*(i_*𝓖) ≅ R^p (i ≫ f)_*𝓖` for every `p`.

## Main results

* `AlgebraicGeometry.Space.isCoherent_rightDerived_modulePushforward_of_hasProperSupport`: the
  reduction of Stacks 08GC to its inputs.

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

/-! ### The two inputs -/

/-- **Stacks 08AR as a property of the target.**  An algebraic space `Y` over `S` has coherent
higher direct images from proper morphisms when for every proper `g : Z ⟶ Y` and every coherent
`𝒪_Z`-module `𝓖` the module `R^p g_*𝓖` is coherent, in every degree `p`.

Stacks 08AR says that every locally Noetherian `Y` has this property; that is
`AlgebraicGeometry.Space.coherentHigherDirectImageOfProper_of_isLocallyNoetherian`. -/
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
sequence degenerates onto its abutment `R^{p+q} (i ≫ f)_*𝓖`.  Every morphism has this property:
`AlgebraicGeometry.Space.higherDirectImageCompOfAcyclic`. -/
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

/-! ### The reduction of Stacks 08GC to its inputs -/

/-- **The reduction of Stacks 08GC to its inputs.**  Let `f : X ⟶ Y` be a morphism of algebraic
spaces over `S` which is locally of finite type with `Y` locally Noetherian, and let `𝓕` be a
coherent `𝒪_X`-module whose support is proper over `Y`.  If the inclusions of closed subspaces
of `X` have vanishing chartwise higher direct images (`h03DW`), `Y` has the property
`CoherentHigherDirectImageOfProper` (`h08AR`) and `f` has the property
`HigherDirectImageCompOfAcyclic` (`h0734`), then `R^p f_*𝓕` is coherent for every `p`.

Stacks 08GC itself, with none of these, is
`AlgebraicGeometry.Space.isCoherent_higherDirectImage_of_hasProperSupport`.  The proof follows
the source: Stacks 0CZI (`AlgebraicGeometry.Space.hasProperSupport_tfae`) gives a closed
subspace `i : Z → X` proper over `Y` and a module `𝓖` with `i_*𝓖 ≅ 𝓕`, coherent because `X` is
locally Noetherian by Stacks 04ZK; the higher direct images along the finite `i` vanish
(Stacks 07UH), `h0734` identifies `R^p f_*(i_*𝓖)` with `R^p (i ≫ f)_*𝓖`, and `h08AR` makes it
coherent. -/
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
