module

public import Mathlib.AlgebraicGeometry.Morphisms.Finite
public import StacksCore.Tactic.StacksAttribute
public import StacksFrontier.AlgebraicGeometry.AffineCohomologyVanishing.Basic
public import StacksFrontier.AlgebraicGeometry.CoherenceCriteria.Basic
public import StacksFrontier.AlgebraicGeometry.CoherentAbelian.HigherDirectImage
public import StacksFrontier.AlgebraicGeometry.CoherentDevissage.Coherence
public import StacksFrontier.AlgebraicGeometry.Divisors.AssociatedPoints.Finiteness
public import StacksFrontier.AlgebraicGeometry.Duality.RightAdjointPushforward.AffineSections
public import StacksFrontier.AlgebraicGeometry.HigherDirectImage.Basic
public import StacksFrontier.AlgebraicGeometry.HigherDirectImageCoherent.Basic
public import StacksFrontier.Homology.DerivedIndexing.Basic

/-!
# Coherence of the direct images along a finite morphism

Let `f : X ⟶ S` be a finite morphism of schemes with `S` locally Noetherian, and let `F` be a
coherent `𝒪_X`-module. [Stacks, Tag 01Y6] asserts that `Rᵖ f_* F = 0` for `p > 0` and that
`f_* F` is coherent. This file proves both, by the route of the source: the vanishing is
[Stacks, Tag 01XC] together with the fact that a finite morphism is affine, and the coherence is
[Stacks, Tag 01XZ] together with the algebra fact that a finite module over a finite algebra is
a finite module over the base ([Stacks, Tag 00GJ], `Module.Finite.trans`).

Since a finite morphism is proper, the consequence recorded in the source's remark after
[Stacks, Tag 01Y6] — that *all* the higher direct images are then coherent, the positive ones
because they vanish — is the conclusion of [Stacks, Tag 02O5] (EGA III 3.2.1) for the special
case of a **finite** morphism. It is stated here as
`isCoherent_higherDirectImage_of_isFinite`. **No `@[stacks 02O5]` attribute is attached**: that
tag asserts the conclusion for every proper morphism, and finiteness is a strictly stronger
hypothesis. See the implementation notes for what remains of [Stacks, Tag 02O5].

## Main definitions

* `Stacks.AlgebraicGeometry.FiniteDirectImageCoherent.specModuleIsoSections`: the
  `Γ(X, U)`-module `specModule F hU` of [Stacks, Tag 01XZ] (4) is the module of sections of `F`
  over the affine open `U`.

## Main results

* `Stacks.AlgebraicGeometry.FiniteDirectImageCoherent.isFiniteTildeOn_of_moduleFinite_sections`:
  a quasi-coherent module whose sections over an affine open form a finite module satisfies
  condition (4) of [Stacks, Tag 01XZ] there. This is the converse of
  `AlgebraicGeometry.moduleFinite_sections_on_affine`.
* `…FiniteDirectImageCoherent.moduleFinite_sections_pushforward_of_isFinite`: for `f` finite and
  `F` quasi-coherent of finite type, the sections of `f_* F` over an affine open of `S` form a
  finite module.
* `Stacks.AlgebraicGeometry.FiniteDirectImageCoherent.isCoherent_pushforward_of_isFinite`:
  coherence of `f_* F`.
* `Stacks.AlgebraicGeometry.FiniteDirectImageCoherent.isZero_higherDirectImage_of_isFinite`:
  vanishing of `Rᵖ f_* F` for `p > 0`.
* `Stacks.AlgebraicGeometry.FiniteDirectImageCoherent.isCoherent_higherDirectImage_zero_iff`:
  coherence of `R⁰ f_* F` is coherence of `f_* F`, with no hypothesis on `f` at all.
* `Stacks.AlgebraicGeometry.FiniteDirectImageCoherent.isCoherent_higherDirectImage_of_isFinite`
  and `isCoherent_rightDerived_of_isFinite`: coherence of every higher direct image along a
  finite morphism, for the two indexings of the right derived functors.

## Implementation notes

**What this leaves of [Stacks, Tag 02O5].** Quasi-coherence of `Rᵖ f_* F` along a proper
morphism is already available unconditionally
(`Stacks.AlgebraicGeometry.HigherDirectImageQcoh.isQuasicoherent_higherDirectImage`, a proper
morphism being quasi-compact and quasi-separated), and on a locally Noetherian scheme coherence
is quasi-coherence together with finite type
(`Stacks.AlgebraicGeometry.CoherenceCriteria.isCoherent_of_isQuasicoherent_of_isFiniteType`).
So the whole residue of [Stacks, Tag 02O5] for a general proper morphism is

  `(((Scheme.Modules.pushforward f).rightDerivedPlus (i : ℤ)).obj F).IsFiniteType`.

That residue is the finiteness theorem itself, and the source proves it by dévissage
([Stacks, Tag 01YI]) over Chow's lemma ([Stacks, Tag 0200]), the relative Leray spectral
sequence ([Stacks, Tag 01F6]) and the relative-ample vanishing of [Stacks, Tag 02O1] — none of
which is available. For a finite morphism no such input is needed, which is why this file can
discharge that case in full.

**Scalars on the direct image.** `Γ(f_* F, V)` is *definitionally* `Γ(F, f ⁻¹ᵁ V)`, with the
`Γ(S, V)`-action obtained from the `Γ(X, f ⁻¹ᵁ V)`-action by restriction along `f.app V`. The
`Module` instance that instance search finds on `Γ(f_* F, V)` is therefore the restricted one
and not the `Γ(X, f ⁻¹ᵁ V)`-one, so the latter is supplied by hand with `inferInstanceAs`; the
scalar tower that relates them holds by `rfl` once `Algebra.smul_def` has unfolded the action of
`Γ(S, V)` on `Γ(X, f ⁻¹ᵁ V)`.

**Where `specModuleIsoSections` comes from.** `IsAffineOpen.isoSpec_inv_ι` is a `rfl`, so the
twice-restricted module `specRestrict F hU` of `Stacks.AlgebraicGeometry.CoherentTFAE` and the
once-restricted `F.restrict hU.fromSpec` of `AlgebraicGeometry.moduleSpecSectionsIso` are
related by `Scheme.Modules.restrictFunctorComp` alone.

## References

* [Stacks Project, Tag 01Y6](https://stacks.math.columbia.edu/tag/01Y6)
* [Stacks Project, Tag 01XC](https://stacks.math.columbia.edu/tag/01XC)
* [Stacks Project, Tag 01XZ](https://stacks.math.columbia.edu/tag/01XZ)
* [Stacks Project, Tag 02O5](https://stacks.math.columbia.edu/tag/02O5)
-/

@[expose] public section

open CategoryTheory Limits
open AlgebraicGeometry
open Stacks.AlgebraicGeometry.CoherentTFAE

universe u

attribute [local instance] HasDerivedCategory.standard

namespace Stacks.AlgebraicGeometry.FiniteDirectImageCoherent

/-! ### Sections over an affine open and condition (4) of Tag 01XZ -/

/-- The module `specModule F hU` is the module of sections of `F` over `U`. The restriction of `F`
to `Spec Γ(X, U)` used by `Stacks.AlgebraicGeometry.CoherentTFAE.specModule` goes along
`hU.isoSpec.inv` followed by `U.ι`, which *is* `hU.fromSpec`
(`AlgebraicGeometry.IsAffineOpen.isoSpec_inv_ι`), so composing the comparison of the two
restrictions with `AlgebraicGeometry.moduleSpecSectionsIso` identifies the two modules. -/
noncomputable def specModuleIsoSections {X : Scheme.{u}} (F : X.Modules) (U : X.affineOpens) :
    specModule F U.2 ≅ ModuleCat.of Γ(X, U.1) Γ(F, U.1) :=
  have : IsOpenImmersion U.2.fromSpec := U.2.isOpenImmersion_fromSpec
  moduleSpecΓFunctor.mapIso
      ((Scheme.Modules.restrictFunctorComp U.2.isoSpec.inv U.1.ι).app F).symm ≪≫
    AlgebraicGeometry.moduleSpecSectionsIso F U

/-- A quasi-coherent module with finitely generated sections over an affine open satisfies
condition (4) of [Stacks, Tag 01XZ] there. This is the converse of
`AlgebraicGeometry.moduleFinite_sections_on_affine`: finiteness of the sections transports to
finiteness of `specModule F hU` along `specModuleIsoSections`, which is exactly the input of
`Stacks.AlgebraicGeometry.CoherentTFAE.isFiniteTildeOn_of_finite_specModule`. -/
theorem isFiniteTildeOn_of_moduleFinite_sections {X : Scheme.{u}} (F : X.Modules)
    [F.IsQuasicoherent] (U : X.affineOpens) (h : Module.Finite Γ(X, U.1) Γ(F, U.1)) :
    IsFiniteTildeOn F U.1 U.2 :=
  have : Module.Finite Γ(X, U.1) (specModule F U.2) :=
    Module.Finite.equiv (specModuleIsoSections F U).toLinearEquiv.symm
  isFiniteTildeOn_of_finite_specModule F U.1 U.2 this

/-! ### The direct image along a finite morphism -/

/-- The sections of `f_* F` over an affine open form a finite module, for `f` finite and `F`
quasi-coherent of finite type.

This is the algebra fact of [Stacks, Tag 01Y6]: writing `V = Spec A` and `f ⁻¹ᵁ V = Spec B`, the
module `Γ(f_* F, V) = Γ(F, f ⁻¹ᵁ V)` is finite over `B` by
`AlgebraicGeometry.moduleFinite_sections_on_affine`, the ring `B` is finite over `A` by
`AlgebraicGeometry.IsFinite.finite_app`, and finiteness composes ([Stacks, Tag 00GJ]). -/
theorem moduleFinite_sections_pushforward_of_isFinite {X S : Scheme.{u}} (f : X ⟶ S)
    [IsFinite f] (F : X.Modules) [F.IsQuasicoherent] [F.IsFiniteType] (V : S.affineOpens) :
    Module.Finite Γ(S, V.1) Γ((Scheme.Modules.pushforward f).obj F, V.1) := by
  let _ : Algebra Γ(S, V.1) Γ(X, f ⁻¹ᵁ V.1) := (f.app V.1).hom.toAlgebra
  have hAB : Module.Finite Γ(S, V.1) Γ(X, f ⁻¹ᵁ V.1) := IsFinite.finite_app f V.1 V.2
  let _ : Module Γ(X, f ⁻¹ᵁ V.1) Γ((Scheme.Modules.pushforward f).obj F, V.1) :=
    inferInstanceAs (Module Γ(X, f ⁻¹ᵁ V.1) Γ(F, f ⁻¹ᵁ V.1))
  have : Module.Finite Γ(X, f ⁻¹ᵁ V.1) Γ((Scheme.Modules.pushforward f).obj F, V.1) :=
    AlgebraicGeometry.moduleFinite_sections_on_affine F _ (V.2.preimage f)
  have : IsScalarTower Γ(S, V.1) Γ(X, f ⁻¹ᵁ V.1)
      Γ((Scheme.Modules.pushforward f).obj F, V.1) :=
    ⟨fun x y z => by rw [Algebra.smul_def, RingHom.algebraMap_toAlgebra, mul_smul]; rfl⟩
  exact Module.Finite.trans Γ(X, f ⁻¹ᵁ V.1) _

/-- The direct image of a coherent module along a finite morphism to a locally Noetherian scheme is
coherent.

It is quasi-coherent because a finite morphism is affine, and on every affine open of the target
its sections form a finite module, which is condition (5) of [Stacks, Tag 01XZ]. -/
@[instance,
  stacks 01Y6 "the direct image is coherent",
  ega "III 3.2.2" "finite case",
  ega "III 4.8.6" "scheme case"]
theorem isCoherent_pushforward_of_isFinite {X S : Scheme.{u}} (f : X ⟶ S) [IsFinite f]
    [IsLocallyNoetherian S] (F : X.Modules) [F.IsCoherent] :
    ((Scheme.Modules.pushforward f).obj F).IsCoherent := by
  obtain ⟨hqc, hft⟩ := isQuasicoherent_isFiniteType_of_isCoherent F
  exact Stacks.AlgebraicGeometry.CoherenceCriteria.isCoherent_of_isFiniteTildeOn _ fun V hV =>
    isFiniteTildeOn_of_moduleFinite_sections _ ⟨V, hV⟩
      (moduleFinite_sections_pushforward_of_isFinite f F ⟨V, hV⟩)

/-- The higher direct images of a quasi-coherent module along a finite morphism vanish in positive
degrees, a finite morphism being affine; this is [Stacks, Tag 01XC]. No hypothesis on the target is
used. -/
@[stacks 01Y6 "the higher direct images vanish"]
theorem isZero_higherDirectImage_of_isFinite {X S : Scheme.{u}} (f : X ⟶ S) [IsFinite f]
    (F : X.Modules) [F.IsQuasicoherent] (p : ℤ) (hp : 0 < p) :
    IsZero (((Scheme.Modules.pushforward f).rightDerivedPlus p).obj F) :=
  Stacks.Cohomology.Affine.isZero_rightDerived_pushforward_of_isAffineHom f F p hp

/-! ### All the higher direct images along a finite morphism -/

/-- Coherence of `R⁰ f_* F` is coherence of `f_* F`. The pushforward functor on sheaves of
modules over schemes is a right adjoint, hence left exact, so it agrees with its own zeroth
right derived functor. No hypothesis on `f` or on `F` is used.

This is an alias of `AlgebraicGeometry.CoherentAbelian.isCoherent_higherDirectImage_zero_iff`.
`Stacks.AlgebraicGeometry.HigherDirectImageCoherent.isCoherent_higherDirectImage_zero_iff` is
the same statement confined to `Scheme.{0}`; this is the universe-polymorphic form. -/
alias isCoherent_higherDirectImage_zero_iff :=
  AlgebraicGeometry.CoherentAbelian.isCoherent_higherDirectImage_zero_iff

/-- [Stacks, Tag 02O5] for a finite morphism. Every higher direct image of a coherent module along
a finite morphism to a locally Noetherian scheme is coherent: in negative degrees and in positive
degrees because the sheaf vanishes, and in degree `0` because it is the direct image, which is
[Stacks, Tag 01Y6].

A finite morphism is proper, so this is the conclusion of [Stacks, Tag 02O5] under the strictly
stronger hypothesis `IsFinite f` in place of `IsProper f`. **No `@[stacks 02O5]` attribute is
attached**, because the tag asserts the conclusion for every proper morphism; the residue for a
general proper morphism is recorded in the implementation notes of this file. -/
@[instance,
  ega "II 7.3.12" "finite morphisms",
  ega "III 2.2.1" "clause (i), special case",
  ega "III 2.4.1" "Clause (i), special case",
  ega "III 3.2.1" "finite morphisms",
  ega "III 6.7.9" "special case"]
theorem isCoherent_higherDirectImage_of_isFinite {X S : Scheme.{u}} (f : X ⟶ S) [IsFinite f]
    [IsLocallyNoetherian S] (F : X.Modules) [F.IsCoherent] (p : ℤ) :
    (((Scheme.Modules.pushforward f).rightDerivedPlus p).obj F).IsCoherent := by
  obtain ⟨hqc, -⟩ := isQuasicoherent_isFiniteType_of_isCoherent F
  obtain rfl | hp := eq_or_ne p 0
  · exact (isCoherent_higherDirectImage_zero_iff f F).2
      (isCoherent_pushforward_of_isFinite f F)
  · refine Stacks.AlgebraicGeometry.CoherentDevissage.isCoherent_of_isZero ?_
    rcases hp.lt_or_gt with hp | hp
    exacts [Stacks.AlgebraicGeometry.HigherDirectImage.isZero_higherDirectImage_of_neg f F p hp,
      isZero_higherDirectImage_of_isFinite f F p hp]

/-- [Stacks, Tag 02O5] for a finite morphism, for Mathlib's `ℕ`-indexed right derived
functors. The two indexings are compared by `Stacks.DerivedIndexing.rightDerivedIso`. **No
`@[stacks 02O5]` attribute is attached**, for the reason given on
`isCoherent_higherDirectImage_of_isFinite`. -/
@[instance]
theorem isCoherent_rightDerived_of_isFinite {X S : Scheme.{u}} (f : X ⟶ S) [IsFinite f]
    [IsLocallyNoetherian S] (F : X.Modules) [F.IsCoherent] (i : ℕ) :
    (((Scheme.Modules.pushforward f).rightDerived i).obj F).IsCoherent :=
  have := isCoherent_higherDirectImage_of_isFinite f F (i : ℤ)
  Stacks.AlgebraicGeometry.CoherentDevissage.isCoherent_of_iso (R := S.ringCatSheaf)
    ((Stacks.DerivedIndexing.rightDerivedIso (Scheme.Modules.pushforward f) i).app F)

end Stacks.AlgebraicGeometry.FiniteDirectImageCoherent

end
