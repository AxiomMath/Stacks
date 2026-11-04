module

public import Mathlib.CategoryTheory.Abelian.RightDerived
public import StacksCore.Algebra.Homology.SpectralSequence.PageInfinity
public import StacksCore.CategoryTheory.Filtration.GradedPieces
public import StacksFrontier.AlgebraicGeometry.RelativeLeray.Basic
public import StacksFrontier.Topology.Sheaves.Functors.Module.EnoughInjectives
import StacksCore.Tactic.EgaSgaAttribute

/-!
# The shape of the relative Leray spectral sequence

For composable morphisms of ringed spaces `X ⟶ Y ⟶ Z`, the relative Leray spectral sequence
has second page `R ᵖ g_*(R^q f_* 𝓕)` and abuts to `R^{p+q}(g ∘ f)_* 𝓕`. The spectral sequence
and its filtered abutment are functorial in the module `𝓕`. There is also a version for
bounded below complexes.

This file carries the *shape* of [Stacks, Tag 01F6] — the convergence structures and the two
packages of data that the tag asks for — and nothing else. The two constructions
`relativeLeraySpectralSequence` and `relativeLeraySpectralSequencePlus` are **not** here, and
nothing in this directory carries the tag `01F6`. The mathematical input they need is proved:
`Stacks.RelativeLeray.rightAcyclic_modulePushforward_obj_injective` is the acyclicity
hypothesis and `Stacks.RelativeLeray.exists_spectralSequence_relativeLeray` the resulting
spectral sequence in the presentation [Stacks, Tag 015N] delivers. What is missing is the
passage from that presentation to the data below; see the implementation notes.

## Main definitions

* `Stacks.RelativeLeray.AbutsTo` records convergence to a graded object by a finite
  decreasing filtration.
* `Stacks.RelativeLeray.FirstQuadrantAbutsTo` records the finite filtered abutment of a
  first-quadrant spectral sequence.
* `Stacks.RelativeLeray.FunctorialFirstQuadrantAbutsTo` records a functorial such abutment.
* `Stacks.RelativeLeray.FunctorialRightHalfPlaneAbutsTo` records a functorial abutment for a
  right-half-plane spectral sequence.
* `Stacks.RelativeLeray.RelativeLeraySpectralSequenceData` packages the relative Leray spectral
  sequence for modules, including its natural second-page identification and filtered abutment.
* `Stacks.RelativeLeray.RelativeLeraySpectralSequencePlusData` packages the bounded-below-complex
  version.

## Main results

* `Stacks.RelativeLeray.FunctorialFirstQuadrantAbutsTo.obj`: evaluating a functorial abutment at
  an object of the parameter category recovers the finite filtered abutment of the individual
  spectral sequence there.

## Implementation notes

The filtered abutment is functorial: its underlying-object functor is naturally isomorphic to
the higher direct image, and the infinity-page identifications commute with the actual
spectral-sequence maps. In particular, the maps on the higher direct images preserve the
filtration and induce the prescribed maps on its graded pieces. Evaluating
`FunctorialFirstQuadrantAbutsTo.obj` recovers the finite filtered abutment of an individual
spectral sequence.

The bounded-below construction uses the standard derived categories and the existing
infinity-page API underlying `AbutsTo`.

**What separates these structures from what is proved.** Two routes reach a relative Leray
spectral sequence, and they fail to be the data below in different places.

*The filtered-complex route*, `Stacks.RelativeLeray.exists_spectralSequence_relativeLeray`,
produces for one object of `D⁺(Mod(𝒪_X))` at a time a `CohomologicalSpectralSequence` carried
on `ℤ × ℤ` from page `0`, presented by a filtered complex, with a `Nonempty`-valued second-page
identification and the filtration `F ᵖH ⁿ` of the abutment. Four things separate it from
`sequence` and `abutment`: it chooses a Cartan-Eilenberg resolution, so it is a function of an
object and not of a morphism (the functorial spectral sequence of a double complex does exist,
`Stacks.Cohomology.CechSpectral.totalSpectralSequence₂Functor`, with the naturality of its page
identifications; what is missing is a functorial Cartan-Eilenberg resolution to feed it); the
index type is `ℤ × ℤ` and the starting page `0`, which is item (c) of the implementation notes
of `StacksDraft.Ch20.Sec13.Tag01ES`; the page identifications are `Nonempty`-valued, which is
item (a) there; and nothing identifies the graded pieces of `F ᵖH ⁿ` with
`SpectralSequence.pageInfinity`.

*The spectral-object route*, `StacksFrontier.AlgebraicGeometry.RelativeLeray.SpectralObject`,
does better on three of those four. `Stacks.RelativeLeray.spectralObjectFunctor` is an honest
functor on `D⁺(Mod(𝒪_Y))`, the page identification
`Stacks.RelativeLeray.pageTwoIsoTruncation` is a `def`, and Mathlib's
`CategoryTheory.Abelian.SpectralObject.coreE₂CohomologicalNat` carries the `ℕ × ℕ` indexing
from page two directly. Exactly two things are missing there, and both are Mathlib-level:

1. *Functoriality of the spectral sequence in the spectral object.* There is no functor
   `CategoryTheory.Abelian.SpectralObject C ι ⥤ CategoryTheory.SpectralSequence C c r₀`;
   `SpectralObject.spectralSequence` is defined on objects only.
2. *Convergence.* No filtration of `H ⁿ(⊥ ≤ ⊤)` by the images of the `H ⁿ(p ≤ ⊤)`, and no
   comparison of its graded pieces with `SpectralSequence.pageInfinity`. Mathlib records this
   as an open task of the author of the machinery, in the header of
   `Mathlib/CategoryTheory/Triangulated/SpectralObject.lean`.

## References

* [Stacks Project, Tag 01F6](https://stacks.math.columbia.edu/tag/01F6)
* [Stacks Project, Tag 015N](https://stacks.math.columbia.edu/tag/015N)
* [Stacks Project, Tag 01ES](https://stacks.math.columbia.edu/tag/01ES)
-/

@[expose] public section

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits Opposite
open RingedSpaceModuleAdjunction

universe u v w

namespace Stacks.RelativeLeray

attribute [local instance] HasDerivedCategory.standard

/-- A cohomological spectral sequence `E`, starting at any page `r₀`, abuts to a graded family
`H` if it has an infinity page at every bidegree and, for every `n`, the objects `E_∞^{p,n-p}`
are the successive quotients of a finite decreasing filtration on `H n`.

This is deliberately **not** called `CategoryTheory.SpectralSequence.AbutsTo`, which is where
the notion belongs and where [Stacks, Tag 01F2] states it. Nothing in the library declares that
name today, so this file would have to squat on it to use dot notation, and the next hand to
land 01F2 would then hit a duplicate declaration. The notion is stated here, in this
directory's own namespace, and is applied prefix rather than by dot notation. -/
@[ega "0 11.1.1" "items (e), special case"]
def AbutsTo {C : Type v} [Category.{w} C] [Abelian C] {r₀ : ℤ}
    (E : CohomologicalSpectralSequence C r₀) (H : ℤ → C) : Prop :=
  (∀ p q : ℤ, E.HasPageInfinityAt (p, q)) ∧
    ∃ (F : ∀ n : ℤ, ℤ → Subobject (H n)) (hF : ∀ n : ℤ, Antitone (F n)),
      (∀ n : ℤ, ∃ a b : ℤ, a ≤ b ∧ F n a = ⊤ ∧ F n b = ⊥) ∧
      ∀ p q : ℤ, Nonempty
        (E.pageInfinity (p, q) ≅
          cokernel (Subobject.ofLE (F (p + q) (p + 1)) (F (p + q) p)
            (hF (p + q) (by omega))))

/-- A finite filtered abutment for a first-quadrant cohomological spectral sequence. -/
structure FirstQuadrantAbutsTo
    {A : Type*} [Category A] [Abelian A]
    (E : E₂CohomologicalSpectralSequenceNat A) (H : ℕ → A) where
  /-- The spectral sequence stabilizes at every bidegree. -/
  hasPageInfinityAt (p q : ℕ) : E.HasPageInfinityAt (p, q)
  /-- The filtration of the abutment in each total degree. -/
  filtration (n : ℕ) : FilteredObject A ℤᵒᵖ
  /-- The underlying object of the filtration is the asserted abutment. -/
  abutmentIso (n : ℕ) : (filtration n).X ≅ H n
  /-- The filtration of every abutment object is finite. -/
  isFinite (n : ℕ) : Filtration.IsFinite (filtration n).filtration
  /-- In total degree `n`, the zeroth filtration step is the whole abutment. -/
  isTop (n : ℕ) :
    (filtration n).filtration.subobject (op (0 : ℤ)) = ⊤
  /-- In total degree `n`, the `(n + 1)`-st filtration step is zero. -/
  isBot (n : ℕ) :
    (filtration n).filtration.subobject (op ((n : ℤ) + 1)) = ⊥
  /-- The infinity term is the corresponding associated graded object. -/
  gradedIso (p q : ℕ) :
    E.pageInfinity (p, q) ≅
      (FilteredObject.gr (p : ℤ)).obj (filtration (p + q))

/-- A functorial finite filtered abutment for a first-quadrant cohomological spectral
sequence. Naturality of `gradedIso` identifies the associated-graded map with the
map on infinity pages induced by the actual spectral-sequence map. -/
@[ega "0 11.1.1" "items (e), special case"]
structure FunctorialFirstQuadrantAbutsTo
    {D A : Type*} [Category D] [Category A] [Abelian A]
    (E : D ⥤ E₂CohomologicalSpectralSequenceNat A) (H : ℕ → D ⥤ A) where
  /-- The functorial filtration of the abutment in each total degree. -/
  filtration (n : ℕ) : D ⥤ FilteredObject A ℤᵒᵖ
  /-- The underlying object is naturally the asserted abutment. -/
  abutmentIso (n : ℕ) : filtration n ⋙ FilteredObject.forget ≅ H n
  /-- Every abutment filtration is finite. -/
  isFinite (K : D) (n : ℕ) : Filtration.IsFinite ((filtration n).obj K).filtration
  /-- In total degree `n`, the zeroth step is the whole abutment. -/
  isTop (K : D) (n : ℕ) :
    ((filtration n).obj K).filtration.subobject (op (0 : ℤ)) = ⊤
  /-- In total degree `n`, the `(n + 1)`-st step is zero. -/
  isBot (K : D) (n : ℕ) :
    ((filtration n).obj K).filtration.subobject (op ((n : ℤ) + 1)) = ⊥
  /-- The infinity term is the corresponding associated graded object. -/
  gradedIso (K : D) (p q : ℕ) :
    (E.obj K).pageInfinity (p, q) ≅
      (FilteredObject.gr (p : ℤ)).obj ((filtration (p + q)).obj K)
  /-- Compatibility with the actual maps on the infinity page. -/
  gradedIso_naturality {K L : D} (φ : K ⟶ L) (p q : ℕ) :
    SpectralSequence.Hom.mapPageInfinity (E.map φ) (p, q) ≫
        (gradedIso L p q).hom =
      (gradedIso K p q).hom ≫
        (FilteredObject.gr (p : ℤ)).map ((filtration (p + q)).map φ)

/-- The filtered abutment at an individual object of the parameter category. -/
noncomputable def FunctorialFirstQuadrantAbutsTo.obj
    {D A : Type*} [Category D] [Category A] [Abelian A]
    {E : D ⥤ E₂CohomologicalSpectralSequenceNat A} {H : ℕ → D ⥤ A}
    (h : FunctorialFirstQuadrantAbutsTo E H) (K : D) :
    FirstQuadrantAbutsTo (E.obj K) (fun n => (H n).obj K) where
  hasPageInfinityAt _ _ := inferInstance
  filtration n := (h.filtration n).obj K
  abutmentIso n := (h.abutmentIso n).app K
  isFinite n := h.isFinite K n
  isTop n := h.isTop K n
  isBot n := h.isBot K n
  gradedIso p q := h.gradedIso K p q

/-- A functorial finite filtered abutment for a right-half-plane cohomological
spectral sequence. The associated-graded maps agree with the actual maps on
infinity pages. -/
@[ega "0 11.1.1" "items (e), special case"]
structure FunctorialRightHalfPlaneAbutsTo
    {D A : Type*} [Category D] [Category A] [Abelian A]
    (E : D ⥤ E₂CohomologicalSpectralSequence A) (H : ℤ → D ⥤ A) where
  /-- The functorial filtration of the abutment in each total degree. -/
  filtration (n : ℤ) : D ⥤ FilteredObject A ℤᵒᵖ
  /-- The underlying object is naturally the asserted abutment. -/
  abutmentIso (n : ℤ) : filtration n ⋙ FilteredObject.forget ≅ H n
  /-- Every abutment filtration is finite. -/
  isFinite (K : D) (n : ℤ) : Filtration.IsFinite ((filtration n).obj K).filtration
  /-- The zeroth filtration step is the whole abutment. -/
  isTop (K : D) (n : ℤ) :
    ((filtration n).obj K).filtration.subobject (op (0 : ℤ)) = ⊤
  /-- Objectwise convergence in the standard finite-filtration sense. -/
  abutsTo (K : D) : AbutsTo (E.obj K) (fun n => (H n).obj K)
  /-- The infinity term is the corresponding associated graded object. -/
  gradedIso (K : D) (p q : ℤ) :
    (E.obj K).pageInfinity (p, q) ≅
      (FilteredObject.gr p).obj ((filtration (p + q)).obj K)
  /-- Compatibility with the actual maps on the infinity page. -/
  gradedIso_naturality {K L : D} (φ : K ⟶ L) (p q : ℤ) :
    SpectralSequence.Hom.mapPageInfinity (E.map φ) (p, q) ≫
        (gradedIso L p q).hom =
      (gradedIso K p q).hom ≫
        (FilteredObject.gr p).map ((filtration (p + q)).map φ)

section Data

/-- The complete data of the relative Leray spectral sequence for modules. -/
structure RelativeLeraySpectralSequenceData {X Y Z : RingedSpace.{u, u}}
    (f : X ⟶ Y) (g : Y ⟶ Z) where
  /-- The spectral sequence, functorial in the module. -/
  sequence : SheafOfModules.{u} (structureSheafRing X) ⥤
    E₂CohomologicalSpectralSequenceNat (SheafOfModules.{u} (structureSheafRing Z))
  /-- Its natural second-page identification
  `E₂^{p,q} ≅ R^p g_* (R^q f_* -)`. -/
  pageTwoIso (p q : ℕ) :
    sequence ⋙ SpectralSequence.pageFunctor _ _ 2 2 ⋙
        HomologicalComplex.eval _ _ (p, q) ≅
      (modulePushforward f).rightDerived q ⋙ (modulePushforward g).rightDerived p
  /-- Its functorial filtered abutment by the higher direct images of the composite. -/
  abutment : FunctorialFirstQuadrantAbutsTo sequence (fun n =>
    (modulePushforward (f ≫ g)).rightDerived n)

/-- The complete data of the relative Leray spectral sequence for bounded below
complexes. -/
structure RelativeLeraySpectralSequencePlusData {X Y Z : RingedSpace.{u, u}}
    (f : X ⟶ Y) (g : Y ⟶ Z) where
  /-- The spectral sequence, functorial in the bounded below complex. -/
  sequence : DerivedCategory.Plus (SheafOfModules.{u} (structureSheafRing X)) ⥤
    E₂CohomologicalSpectralSequence (SheafOfModules.{u} (structureSheafRing Z))
  /-- Its natural second-page identification
  `E₂^{p,q} ≅ R^p g_* (H^q(Rf_* -))`. -/
  pageTwoIso (p : ℕ) (q : ℤ) :
    sequence ⋙ SpectralSequence.pageFunctor _ _ 2 2 ⋙
        HomologicalComplex.eval _ _ ((p : ℤ), q) ≅
      (modulePushforward f).rightDerivedFunctorPlus ⋙
        DerivedCategory.Plus.homologyFunctor _ q ⋙
        (modulePushforward g).rightDerived p
  /-- The terms with negative first coordinate vanish. -/
  pageTwo_isZero (K : DerivedCategory.Plus (SheafOfModules.{u} (structureSheafRing X)))
      (p q : ℤ) (hp : p < 0) :
    IsZero ((sequence.obj K).page 2 |>.X (p, q))
  /-- Its functorial filtered abutment by the cohomology of the derived direct image
  of the composite. -/
  abutment : FunctorialRightHalfPlaneAbutsTo sequence (fun n =>
    (modulePushforward (f ≫ g)).rightDerivedFunctorPlus ⋙
      DerivedCategory.Plus.homologyFunctor (SheafOfModules.{u} (structureSheafRing Z)) n)

end Data

end Stacks.RelativeLeray

end
