module

public import Mathlib.AlgebraicGeometry.Morphisms.Finite
public import StacksFrontier.AlgebraicGeometry.AffineCohomologyVanishing.Basic
public import StacksFrontier.AlgebraicGeometry.CoherentDevissage.Coherence
public import StacksFrontier.AlgebraicGeometry.ProperMapping.CoherenceClosure
public import StacksFrontier.AlgebraicGeometry.AffineCohomologyVanishing.Basic

/-!
# Higher direct images of coherent modules: the affine case, and the closure theory it needs

[Stacks, Tag 02O5] (the proper mapping theorem) asserts that for a proper morphism
`f : X ⟶ S` to a locally Noetherian scheme and a coherent `𝒪_X`-module `F`, every higher direct
image `R ⁱ f_* F` is coherent. That statement is **not** proved here; see the implementation
notes for what still blocks it.

What is proved here is the reduction of [Stacks, Tag 02O5] for an **affine** morphism to its
degree-zero assertion, together with the closure theory of coherent modules on a scheme that
the source's dévissage consumes:

* for an affine morphism `f` and quasi-coherent `F`, all higher direct images vanish in positive
  degrees ([Stacks, Tag 01XC], proved elsewhere), so they are coherent there for free;
* consequently, for an affine morphism, the whole of [Stacks, Tag 02O5] reduces to the single
  assertion that the ordinary direct image `f_* F` is coherent — in every degree, positive,
  zero and negative;
* in particular the higher direct images along a finite morphism vanish in positive degrees,
  which is the first assertion of [Stacks, Tag 01Y6];
* coherent modules on a scheme are closed under kernels, images, cokernels, extensions and
  finite direct sums.

The two reductions of [Stacks, Tag 02O5] in degrees `i ≤ 0` that
`StacksFrontier/AlgebraicGeometry/HigherDirectImageCoherent/Basic.lean` proves for `Scheme.{0}`
are restated here for `Scheme.{u}`, which the universe-polymorphic transport lemmas of
`StacksFrontier/AlgebraicGeometry/CoherentDevissage/Coherence.lean` now make possible.

## Main results

* `Stacks.AlgebraicGeometry.ProperMapping.isCoherent_higherDirectImage_of_neg`: `R ⁱ f_* F` is
  coherent for `i < 0`, for an arbitrary morphism of `Scheme.{u}` and an arbitrary module.
* `Stacks.AlgebraicGeometry.ProperMapping.isCoherent_higherDirectImage_zero_iff`: `R ⁰ f_* F` is
  coherent if and only if `f_* F` is, again with no hypothesis.
* `Stacks.AlgebraicGeometry.ProperMapping.isCoherent_higherDirectImage_of_isAffineHom_of_pos`:
  for an affine morphism and a coherent module, `R ⁱ f_* F` is coherent for every `i > 0`.
* `Stacks.AlgebraicGeometry.ProperMapping.isCoherent_higherDirectImage_of_isAffineHom`:
  **[Stacks, Tag 02O5] for an affine morphism, reduced to its degree-zero assertion.** Given
  that `f_* F` is coherent, `R ⁱ f_* F` is coherent for every `i : ℤ`.
* `Stacks.AlgebraicGeometry.ProperMapping.isCoherent_kernel_modules`,
  `isCoherent_image_modules`, `isCoherent_cokernel_modules`,
  `isCoherent_X₂_of_shortExact_modules`, `isCoherent_X₃_of_shortExact_modules`,
  `isCoherent_sigma_modules`: the closure theory of [Stacks, Tag 01BY] for `X.Modules`.

## Implementation notes

**What still blocks [Stacks, Tag 02O5].** The source's proof reduces to `S` affine Noetherian,
runs the dévissage of [Stacks, Tag 01YG] on `X`, and for an integral closed subscheme
`Z ⊆ X` with `g = f|_Z` produces a coherent `𝒢` on `Z` with `R ᵖ g_* 𝒢 = 0` for `p > 0` and
`g_* 𝒢` coherent, by applying Chow's lemma to `Z → S` and killing the higher direct images of a
relatively ample invertible sheaf by twisting. Of those, four
ingredients are missing from this repository and three of them are missing from Mathlib entirely:

* [Stacks, Tag 01YF], the existence of the dévissage filtration — recorded as the one remaining
  hypothesis of
  `Stacks.AlgebraicGeometry.CoherentDevissage.property_of_forall_hasIdealDevissage`;
* [Stacks, Tag 01XZ] into coherence is proved, in
  `StacksFrontier.AlgebraicGeometry.CoherentOfFiniteType`, and with it BOTH halves of
  [Stacks, Tag 01Y1] — so the "sandwiched between two coherent modules" step of the dévissage is
  available. The hypothesis `h` of `isCoherent_higherDirectImage_of_isAffineHom` below is
  thereby REDUCED but not discharged: that file's
  `isCoherent_higherDirectImage_of_isAffineHom` needs only that `f_* F` is quasi-coherent and of
  finite type, and BOTH of those are genuinely absent here — quasi-coherence of a pushforward
  exists only for a morphism between affine schemes, not for an affine morphism, and nothing in
  the repo gives finite type of a pushforward. That single statement, for a finite or affine
  morphism, is what remains for the degree-zero half of [Stacks, Tag 01Y6] and for the affine
  case of 02O5;
* Chow's lemma, [Stacks, Tag 0200];
* ampleness — but only its theory, not its language. Pinned Mathlib has no ample invertible
  sheaf, no relatively ample sheaf, no projective or locally projective morphism of schemes, no
  twisting sheaf `𝒪(n)` and no Serre vanishing; the one thing it does have is
  `AlgebraicGeometry.IsProper (AlgebraicGeometry.Proj.toSpecZero 𝒜)`. This repository supplies
  each of them itself, so [Stacks, Tag 02O1] and [Stacks, Tag 02O4] *are* statable here and what
  is absent is their proofs: ampleness is `Stacks.Ample.IsAmple` ([Stacks, Tag 01PS]), relative
  ampleness is `Stacks.RelativeAmple.IsRelativelyAmple` ([Stacks, Tag 01VH]), projectivity is
  `AlgebraicGeometry.IsProjectiveMorphism` with `AlgebraicGeometry.IsLocallyProjectiveMorphism`
  beside it ([Stacks, Tag 01W8]), and `𝒪(n)` is replaced by the tensor powers of an invertible
  module ([Stacks, Tag 01CU]). [Stacks, Tag 02O4] is moreover already reduced to its projective
  case by
  `AlgebraicGeometry.ProjectiveCoherentImage.isCoherent_higherDirectImage_of_locallyProjective`.

The relative Leray spectral sequence, [Stacks, Tag 01F6], is the fifth ingredient; the
`Stacks.Cohomology.VanishingDirectImages.cohomology_iso_pushforward_of_isZero_rightDerived`
covers the degenerate case it is used in, but only as a `Nonempty (· ≅ ·)`.

**The predicate is written `_root_.SheafOfModules.IsCoherent` throughout, and that is not
cosmetic.** Coherence is declared twice in this library, and inside the `Stacks.` namespace both
the unqualified name and the dot notation `F.IsCoherent` resolve to the *other* constant,
`Stacks.SheafOfModules.IsCoherent`, because resolution relative to the enclosing namespace wins
over the root. Leaving the predicate unqualified here produces no error and silently states a
different theorem. `ProperMapping/CoherenceClosure.lean` bridges the two constants; this file
specialises that bridge to `X.Modules`. The specialisation is not automatic, because
`AlgebraicGeometry.Scheme.Modules` is a `def` and instance search does not see through it at
reducible transparency.

**Degrees are integers.** `R ⁱ f_*` is `(Scheme.Modules.pushforward f).rightDerivedPlus i` with
`i : ℤ`, so the affine case splits into the three cases `i < 0`, `i = 0` and `i > 0`, each with
its own reason: the derived functor vanishes below zero, agrees with `f_*` at zero because `f_*`
is a right adjoint and hence left exact, and vanishes above zero by [Stacks, Tag 01XC].

## References

* [Stacks Project, Tag 02O5](https://stacks.math.columbia.edu/tag/02O5)
* [Stacks Project, Tag 01Y6](https://stacks.math.columbia.edu/tag/01Y6)
* [Stacks Project, Tag 01XC](https://stacks.math.columbia.edu/tag/01XC)
* [Stacks Project, Tag 01BY](https://stacks.math.columbia.edu/tag/01BY)
-/

@[expose] public section

open CategoryTheory Limits SheafOfModules TopologicalSpace
open AlgebraicGeometry

universe u

attribute [local instance] HasDerivedCategory.standard

namespace Stacks.AlgebraicGeometry.ProperMapping

/-! ### Closure theory for modules on a scheme -/

section Modules

variable {X : Scheme.{u}}

/-- **Stacks Project, Tag 01BY (3), kernels**, for modules on a scheme. -/
theorem isCoherent_kernel_modules {M N : X.Modules}
    (hM : _root_.SheafOfModules.IsCoherent M) (hN : _root_.SheafOfModules.IsCoherent N)
    (φ : M ⟶ N) : _root_.SheafOfModules.IsCoherent (kernel φ) :=
  isCoherent_kernel hM hN φ

/-- **The image of a morphism of coherent modules on a scheme is coherent.** -/
theorem isCoherent_image_modules {M N : X.Modules}
    (hM : _root_.SheafOfModules.IsCoherent M) (hN : _root_.SheafOfModules.IsCoherent N)
    (φ : M ⟶ N) : _root_.SheafOfModules.IsCoherent (Abelian.image φ) :=
  isCoherent_image hM hN φ

/-- **Stacks Project, Tag 01BY (3), cokernels**, for modules on a scheme. This is the statement
that a quotient of a coherent module by a coherent submodule is coherent, which the
dévissage engine `Stacks.AlgebraicGeometry.CoherentDevissage.HasIdealDevissage` has to carry as
data for want of it. -/
theorem isCoherent_cokernel_modules {M N : X.Modules}
    (hM : _root_.SheafOfModules.IsCoherent M) (hN : _root_.SheafOfModules.IsCoherent N)
    (φ : M ⟶ N) : _root_.SheafOfModules.IsCoherent (cokernel φ) :=
  isCoherent_cokernel hM hN φ

/-- **Stacks Project, Tag 01BY (4)**, for modules on a scheme: the middle term of a short exact
sequence with coherent outer terms is coherent. This is the two-out-of-three hypothesis of the
dévissage of [Stacks, Tag 01YG]. -/
theorem isCoherent_X₂_of_shortExact_modules {S : ShortComplex X.Modules} (hS : S.ShortExact)
    (h₁ : _root_.SheafOfModules.IsCoherent S.X₁) (h₃ : _root_.SheafOfModules.IsCoherent S.X₃) :
    _root_.SheafOfModules.IsCoherent S.X₂ :=
  isCoherent_X₂_of_shortExact hS h₁ h₃

/-- **Stacks Project, Tag 01BY (3), cokernels**, for modules on a scheme in short exact
sequence form: the third term of a short exact sequence whose first two terms are coherent is
coherent. -/
theorem isCoherent_X₃_of_shortExact_modules {S : ShortComplex X.Modules} (hS : S.ShortExact)
    (h₁ : _root_.SheafOfModules.IsCoherent S.X₁) (h₂ : _root_.SheafOfModules.IsCoherent S.X₂) :
    _root_.SheafOfModules.IsCoherent S.X₃ :=
  isCoherent_X₃_of_shortExact hS h₁ h₂

/-- **A finite direct sum of coherent modules on a scheme is coherent.** -/
theorem isCoherent_sigma_modules {J : Type*} [Finite J] (M : J → X.Modules)
    (hM : ∀ j, _root_.SheafOfModules.IsCoherent (M j)) :
    _root_.SheafOfModules.IsCoherent (∐ M) :=
  isCoherent_sigma M hM

end Modules

/-! ### Higher direct images in non-positive degrees, for `Scheme.{u}` -/

section NonPositive

variable {X S : Scheme.{u}} (f : X ⟶ S) (F : X.Modules)

/-- **Higher direct images are coherent in negative degrees**, for the trivial reason that they
vanish: this needs no hypothesis on the morphism `f` nor on the module `F`.

This is `Stacks.AlgebraicGeometry.HigherDirectImageCoherent.isCoherent_higherDirectImage_of_neg`
with the universe restriction to `Scheme.{0}` removed. -/
theorem isCoherent_higherDirectImage_of_neg (p : ℤ) (hp : p < 0) :
    _root_.SheafOfModules.IsCoherent
      (((Scheme.Modules.pushforward f).rightDerivedPlus p).obj F) :=
  CoherentDevissage.isCoherent_of_isZero (R := S.ringCatSheaf)
    (HigherDirectImage.isZero_higherDirectImage_of_neg f F p hp)

/-- **Coherence of `R ⁰ f_* F` is coherence of `f_* F`.** The pushforward functor on modules
over schemes is a right adjoint, hence left exact, so it agrees with its own zeroth right
derived functor; coherence then transports along that isomorphism.

This reduces the degree-`0` case of [Stacks, Tag 02O5] to the assertion about ordinary direct
images, with no hypothesis on `f`. It is
`Stacks.AlgebraicGeometry.HigherDirectImageCoherent.isCoherent_higherDirectImage_zero_iff` with
the universe restriction to `Scheme.{0}` removed. -/
theorem isCoherent_higherDirectImage_zero_iff :
    _root_.SheafOfModules.IsCoherent
        (((Scheme.Modules.pushforward f).rightDerivedPlus 0).obj F) ↔
      _root_.SheafOfModules.IsCoherent ((Scheme.Modules.pushforward f).obj F) :=
  ⟨fun _ => CoherentDevissage.isCoherent_of_iso (R := S.ringCatSheaf)
      (HigherDirectImage.higherDirectImageZeroIso f F).symm,
    fun _ => CoherentDevissage.isCoherent_of_iso (R := S.ringCatSheaf)
      (HigherDirectImage.higherDirectImageZeroIso f F)⟩

end NonPositive

/-! ### The affine case of the proper mapping theorem -/

section Affine

variable {X S : Scheme.{u}} (f : X ⟶ S) (F : X.Modules)

/-- **Higher direct images of a coherent module along an affine morphism are coherent in
positive degrees**, because they vanish: a coherent module is quasi-coherent, so
[Stacks, Tag 01XC] applies, and a zero module is coherent. -/
theorem isCoherent_higherDirectImage_of_isAffineHom_of_pos [IsAffineHom f]
    (hF : _root_.SheafOfModules.IsCoherent F) (p : ℤ) (hp : 0 < p) :
    _root_.SheafOfModules.IsCoherent
      (((Scheme.Modules.pushforward f).rightDerivedPlus p).obj F) :=
  have := hF
  have := isQuasicoherent_of_isCoherent F
  CoherentDevissage.isCoherent_of_isZero (R := S.ringCatSheaf)
    (Stacks.Cohomology.Affine.isZero_rightDerived_pushforward_of_isAffineHom f F p hp)

/-- **[Stacks, Tag 02O5] for an affine morphism, reduced to its degree-zero assertion.** For an
affine morphism `f` and a coherent module `F`, every higher direct image `R ⁱ f_* F` is coherent
as soon as the ordinary direct image `f_* F` is: in negative degrees `R ⁱ f_* F` vanishes, in
degree `0` it is `f_* F`, and in positive degrees it vanishes by [Stacks, Tag 01XC].

No Noetherian hypothesis is used, and no properness: the whole of the proper mapping theorem
for affine morphisms is reduced to the single remaining input, the hypothesis `h`. That
hypothesis is not discharged anywhere in this repository; see the implementation notes. -/
theorem isCoherent_higherDirectImage_of_isAffineHom [IsAffineHom f]
    (hF : _root_.SheafOfModules.IsCoherent F)
    (h : _root_.SheafOfModules.IsCoherent ((Scheme.Modules.pushforward f).obj F)) (p : ℤ) :
    _root_.SheafOfModules.IsCoherent
      (((Scheme.Modules.pushforward f).rightDerivedPlus p).obj F) := by
  rcases lt_trichotomy p 0 with hp | rfl | hp
  · exact isCoherent_higherDirectImage_of_neg f F p hp
  · exact (isCoherent_higherDirectImage_zero_iff f F).2 h
  · exact isCoherent_higherDirectImage_of_isAffineHom_of_pos f F hF p hp

/-- **[Stacks, Tag 01Y6] and [Stacks, Tag 02O5] for a finite morphism, reduced to the
degree-zero assertion.** A finite morphism is affine, so
`isCoherent_higherDirectImage_of_isAffineHom` applies. -/
theorem isCoherent_higherDirectImage_of_isFinite [AlgebraicGeometry.IsFinite f]
    (hF : _root_.SheafOfModules.IsCoherent F)
    (h : _root_.SheafOfModules.IsCoherent ((Scheme.Modules.pushforward f).obj F)) (p : ℤ) :
    _root_.SheafOfModules.IsCoherent
      (((Scheme.Modules.pushforward f).rightDerivedPlus p).obj F) :=
  isCoherent_higherDirectImage_of_isAffineHom f F hF h p

end Affine

end Stacks.AlgebraicGeometry.ProperMapping

end
