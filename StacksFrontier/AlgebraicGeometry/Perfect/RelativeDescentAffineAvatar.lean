module

public import StacksFrontier.AlgebraicGeometry.Duality.DerivedTilde.QuasiCoherentDerivedPullback
public import StacksFrontier.AlgebraicGeometry.Modules.QuasicoherentDerivedPullbackOpenImmersion
public import StacksFrontier.AlgebraicGeometry.Perfect.RelativeDescentAffineCase
public import StacksFrontier.AlgebraicGeometry.PseudoCoherent.QuasicoherentCohomology

/-!
# The ring-level avatars of the affine case of Tag 0DI7

The affine case of Stacks 0DI7 is stated in
`StacksFrontier/AlgebraicGeometry/Perfect/RelativeDescentAffineCase.lean` through the bundle
`AlgebraicGeometry.RelativeDescentSituation.AffineDerivedHomEquiv`, and
`AlgebraicGeometry.RelativeDescentSituation.affineDerivedHomEquivOfBaseIso` reduces that bundle
to four pieces: the two ring-level avatars `𝕂`, `𝕃` of `K₀|_{V₀}` and `L₀|_{V₀}` together with
identifications `eK₀`, `eL₀` of the transports of those restrictions to `Spec Γ(V₀)` with the
derived sheafifications of the avatars; pseudo-coherence of `𝕂`; and finite Tor dimension of
`𝕃` over `Γ(W₀)`.

This file discharges the first piece unconditionally. For an affine open `V₀` of a scheme `X`
and an object `E` of `D(𝒪_X)` with quasi-coherent cohomology, the transport of `E|_{V₀}` to
`Spec Γ(V₀)` is the derived sheafification of an object of `D(Γ(V₀))`. The two steps are
[Stacks, Tag 08DW] part (1), that derived pullback preserves quasi-coherence of the cohomology
sheaves, applied to the open immersion `V₀ ⟶ X` and then to `(Scheme.isoSpec V₀)⁻¹`, and
[Stacks, Tag 06Z0], that every object of `D_QCoh(𝒪_{Spec R})` is a derived sheafification.

For the first argument `K₀` of Tag 0DI7 quasi-coherence of the cohomology sheaves is not a
hypothesis: `K₀` is only assumed pseudo-coherent, and [Stacks, Tag 08E5] supplies the rest.

## Which clause of Tag 08E5 is used, and the erratum

Tag 08E5 has three clauses. For an `m`-pseudo-coherent object `E` of `D(𝒪_X)`: (i) `H^i(E)` is
quasi-coherent for `i > m`; (ii) `H^m(E)` is a quotient of a quasi-coherent module; (iii) a
pseudo-coherent object lies in `D_QCoh(𝒪_X)`.

**Clause (ii) is false as the source states it** — a Stacks erratum.
The counterexample is on `X = Spec k[x,y]`. Take the line `L = V(x)` with closed immersion
`i : L → X`, the sheaf of rings `Q = i_*i^{-1}𝒪_X` formed with the *ordinary* inverse image, the
points `p₀ = (0,0)` and `p₁ = (0,1)`, the opens `U = X ∖ {p₀}` and `V = X ∖ {p₁}`, and the
section `g = x - y(y-1)`, which is invertible on `Q|_{U ∩ V}`. Glueing `Q|_U` to `Q|_V` by
`a = g·b` produces a locally cyclic module `F` for which `F[0]` is `0`-pseudo-coherent, every
global section of `F` vanishes in the fibre at `p₁`, and `F` is therefore not globally
generated; since `X` is affine, no quasi-coherent module surjects onto `F`. Quasi-compactness
and quasi-separatedness do not repair the clause — `Spec k[x,y]` has both. The corrected clause
is local: every point of `X` has a neighbourhood on which `H^m(E)` is a quotient of a
quasi-coherent module. Clauses (i) and (iii) are unchanged.

**The erratum does not touch Tag 0DI7.** The only clause of Tag 08E5 that the route to Tag 0DI7
uses is (iii), and it is used in exactly one place: to know that the pseudo-coherent first
argument `K₀` has quasi-coherent cohomology, so that Tag 06Z0 produces its ring-level avatar.
Clause (ii) is used nowhere in that route — not in its global form and not in its corrected
local form. In this file that use is
`AlgebraicGeometry.isQuasicoherentDerived_of_isPseudoCoherent` of
`StacksFrontier/AlgebraicGeometry/PseudoCoherent/QuasicoherentCohomology.lean`, whose own proof
goes through clause (i) only. The corrected local form of clause (ii) is proved in that same
file as `AlgebraicGeometry.exists_local_epi_homology_of_isPseudoCoherentFrom` and is not cited
here.

## Main results

* `AlgebraicGeometry.IsAvatarOver`: `M` is the ring-level avatar of `E` over the affine open
  `V₀`, in the shape `affineDerivedHomEquivOfBaseIso` consumes.
* `AlgebraicGeometry.exists_isAvatarOver_of_isQuasicoherent`: over an affine open `V₀` of a
  scheme `X`, an object of `D(𝒪_X)` with quasi-coherent cohomology has such an avatar.
* `AlgebraicGeometry.exists_isAvatarOver_of_isPseudoCoherent`: the same for a pseudo-coherent
  object, with quasi-coherence supplied by [Stacks, Tag 08E5] clause (iii).
* `AlgebraicGeometry.RelativeDescentSituation.nonempty_affineDerivedHomEquiv_of_avatarProperties`:
  the affine dictionary of Tag 0DI7 from the avatars and their pseudo-coherence and finite Tor
  dimension; its naturality is
  `AlgebraicGeometry.RelativeDescentSituation.isNatural_affineDerivedHomEquivOfLiftedAvatar`.

## Implementation notes

The quasi-coherence transport is taken at
`AlgebraicGeometry.isQuasicoherent_homology_derivedPullback_of_isOpenImmersion`, which is stated
at `CategoryTheory.HasDerivedCategory.standard` and at the ringed-space spelling
`SheafOfModules (structureSheafRing X.toRingedSpace)` that
`Stacks.Cohomology.DerivedAdjunctionOnRingedSpaces.derivedPullback` asks for; both morphisms it
is applied to, `V₀ ⟶ X` and `(Scheme.isoSpec V₀)⁻¹`, are open immersions.

Per the implementation notes of
`StacksFrontier/AlgebraicGeometry/DerivedQCoh/AffineDerivedEquivalenceStandard.lean` the attribute
here is `attribute [local instance 10000] HasDerivedCategory.standard`, not the plain local
attribute: the import closure carries *global* locally small instances, which beat a
default-priority local attribute.

`nonempty_affineDerivedHomEquiv_of_avatarProperties` takes the two ring-level properties of the
avatars as arguments. They are supplied from the sheaf-level hypotheses of Tag 0DI7 by
`AlgebraicGeometry.RelativeDescentSituation.isPseudoCoherent_of_isAvatarOver` ([Stacks,
Tag 08E7]) and `AlgebraicGeometry.RelativeDescentSituation.hasFiniteTorDimension_of_isAvatarOver`
([Stacks, Tag 0DHY]), in
`StacksFrontier/AlgebraicGeometry/Perfect/RelativeDescentAffineDictionaryNatural.lean`.

## References

* [Stacks Project, Tag 0DI7](https://stacks.math.columbia.edu/tag/0DI7)
* [Stacks Project, Tag 0DI6](https://stacks.math.columbia.edu/tag/0DI6)
* [Stacks Project, Lemma 36.10.1 (Tag 08E5)](https://stacks.math.columbia.edu/tag/08E5)
* [Stacks Project, Tag 06Z0](https://stacks.math.columbia.edu/tag/06Z0)
* [Stacks Project, Tag 08DW](https://stacks.math.columbia.edu/tag/08DW)
* [Stacks Project, Tag 08E7](https://stacks.math.columbia.edu/tag/08E7)
* [Stacks Project, Lemma 36.10.4 (Tag 0DHY)](https://stacks.math.columbia.edu/tag/0DHY)
-/

@[expose] public noncomputable section

open CategoryTheory Opposite
open RingedSpaceModuleAdjunction
open StacksDraft.TorAmplitude
open Stacks.Cohomology.DerivedAdjunctionOnRingedSpaces (derivedPullback)

attribute [local instance 10000] HasDerivedCategory.standard

universe u

namespace AlgebraicGeometry

/-! ### The avatar of an object with quasi-coherent cohomology over an affine open -/

/-- **`M` is the ring-level avatar of `E` over the affine open `V₀`.** The transport of
`E|_{V₀}` to `Spec Γ(V₀)` along `(Scheme.isoSpec V₀)⁻¹` is the derived sheafification of the
object `M` of `D(Γ(V₀))`. This is the shape in which
`AlgebraicGeometry.RelativeDescentSituation.affineDerivedHomEquivOfBaseIso` consumes the
comparison over `V₀`. -/
def IsAvatarOver (X : Scheme.{u}) (V₀ : X.Opens) (hV₀ : IsAffineOpen V₀)
    (E : DerivedCategory (SheafOfModules.{u} (structureSheafRing X.toRingedSpace)))
    (M : DerivedCategory (ModuleCat.{u} Γ(V₀.toScheme, ⊤))) : Prop :=
  have : IsAffine V₀.toScheme := hV₀
  Nonempty ((derivedPullback (Scheme.isoSpec V₀.toScheme).inv.toLRSHom.toShHom).obj
      ((derivedPullback V₀.ι.toLRSHom.toShHom).obj E) ≅
    derivedTildeObj Γ(V₀.toScheme, ⊤) M)

/-- **An object of `D(𝒪_X)` with quasi-coherent cohomology has a ring-level avatar over every
affine open.** Let `V₀` be an affine open of a scheme `X` and let `E` be an object of `D(𝒪_X)`
all of whose cohomology sheaves are quasi-coherent. Then the transport of `E|_{V₀}` along
`(Scheme.isoSpec V₀)⁻¹` to `Spec Γ(V₀)` is isomorphic to the derived sheafification of an object
of `D(Γ(V₀))`.

Derived pullback along an open immersion preserves quasi-coherence of the cohomology sheaves
([Stacks, Tag 08DW] part (1)), applied first to `V₀ ⟶ X` and then to `(Scheme.isoSpec V₀)⁻¹`; the
resulting object of `D_QCoh(𝒪_{Spec Γ(V₀)})` is a derived sheafification by [Stacks,
Tag 06Z0]. -/
theorem exists_isAvatarOver_of_isQuasicoherent (X : Scheme.{u}) (V₀ : X.Opens)
    (hV₀ : IsAffineOpen V₀)
    (E : DerivedCategory (SheafOfModules.{u} (structureSheafRing X.toRingedSpace)))
    (hE : ∀ n : ℤ, ((DerivedCategory.homologyFunctor
      (SheafOfModules.{u} (structureSheafRing X.toRingedSpace)) n).obj E).IsQuasicoherent) :
    ∃ M : DerivedCategory (ModuleCat.{u} Γ(V₀.toScheme, ⊤)), IsAvatarOver X V₀ hV₀ E M := by
  have : IsAffine V₀.toScheme := hV₀
  have hres : ∀ n : ℤ, ((DerivedCategory.homologyFunctor
      (SheafOfModules.{u} (structureSheafRing V₀.toScheme.toRingedSpace)) n).obj
      ((derivedPullback V₀.ι.toLRSHom.toShHom).obj E)).IsQuasicoherent := fun n =>
    isQuasicoherent_homology_derivedPullback_of_isOpenImmersion V₀.ι E hE n
  have hspec : ∀ n : ℤ, ((DerivedCategory.homologyFunctor
      (SheafOfModules.{u} (structureSheafRing (Spec Γ(V₀.toScheme, ⊤)).toRingedSpace)) n).obj
      ((derivedPullback (Scheme.isoSpec V₀.toScheme).inv.toLRSHom.toShHom).obj
        ((derivedPullback V₀.ι.toLRSHom.toShHom).obj E))).IsQuasicoherent := fun n =>
    isQuasicoherent_homology_derivedPullback_of_isOpenImmersion
      (Scheme.isoSpec V₀.toScheme).inv _ hres n
  obtain ⟨M, ⟨e⟩⟩ := StandardModel.exists_iso_mapDerivedCategory Γ(V₀.toScheme, ⊤) _ hspec
  exact ⟨M, ⟨e.symm⟩⟩

/-- **A pseudo-coherent object of `D(𝒪_X)` has a ring-level avatar over every affine open.**
The hypothesis of `exists_isAvatarOver_of_isQuasicoherent` is supplied by [Stacks, Tag 08E5]: a
pseudo-coherent object of `D(𝒪_X)` lies in `D_QCoh(𝒪_X)`.

That is clause (iii) of Tag 08E5, which the erratum leaves unchanged; the clause
the erratum corrects — that `H^m(E)` is *globally* a quotient of a quasi-coherent module — is
not used here, and neither is its corrected local form. See the module documentation. -/
theorem exists_isAvatarOver_of_isPseudoCoherent (X : Scheme.{u}) (V₀ : X.Opens)
    (hV₀ : IsAffineOpen V₀)
    (E : DerivedCategory (SheafOfModules.{u} (structureSheafRing X.toRingedSpace)))
    (hE : RingedSpace.IsPseudoCoherent (X := X.toRingedSpace) E) :
    ∃ M : DerivedCategory (ModuleCat.{u} Γ(V₀.toScheme, ⊤)), IsAvatarOver X V₀ hV₀ E M :=
  exists_isAvatarOver_of_isQuasicoherent X V₀ hV₀ E
    (isQuasicoherentDerived_of_isPseudoCoherent X E hE)

namespace RelativeDescentSituation

variable {I : Type u} [Preorder I] [IsDirected I (· ≤ ·)] (D : RelativeDescentSituation.{u, u} I)

/-- **The data half of the affine dictionary of Tag 0DI7.**
`affineDerivedHomEquivOfBaseIso` asks for the two ring-level avatars, identifications of the
transports of `K₀|_{V₀}` and `L₀|_{V₀}` with their derived sheafifications, pseudo-coherence of
the first avatar and finite Tor dimension of the second. The avatars and the identifications
are not extra data: `K₀` is pseudo-coherent, hence lies in `D_QCoh(𝒪_{X₀})` by [Stacks, Tag
08E5], and `L₀` lies there by hypothesis, so [Stacks, Tag 08DW] part (1) and [Stacks, Tag 06Z0]
produce both. What is left is the two ring-level properties, which are [Stacks, Tag 08E7] and
[Stacks, Tag 0DHY].

This produces an `AffineDerivedHomEquiv`, not an
`AlgebraicGeometry.RelativeDescentSituation.AffineRingTranslation`: the naturality predicate
`AffineDerivedHomEquiv.IsNatural`, the composition cocycle of
`AlgebraicGeometry.StandardModel.affinePullbackComparison`, is not supplied here. -/
theorem nonempty_affineDerivedHomEquiv_of_avatarProperties
    (W₀ : (D.descent.system.obj (op D.descent.base)).Opens) (V₀ : D.X₀.left.Opens)
    (hV₀ : IsAffineOpen V₀) (hVW : V₀ ≤ D.X₀.hom ⁻¹ᵁ W₀) (hW₀ : IsAffineOpen W₀)
    (K₀ L₀ : DerivedCategory (SheafOfModules.{u} (structureSheafRing D.X₀.left.toRingedSpace)))
    (hK₀ : RingedSpace.IsPseudoCoherent (X := D.X₀.left.toRingedSpace) K₀)
    (hL₀qc : ∀ n : ℤ, ((DerivedCategory.homologyFunctor
      (SheafOfModules.{u} (structureSheafRing D.X₀.left.toRingedSpace)) n).obj L₀).IsQuasicoherent)
    (hprop : ∀ 𝕂 𝕃 : DerivedCategory (ModuleCat.{u} Γ(V₀.toScheme, ⊤)),
      IsAvatarOver D.X₀.left V₀ hV₀ K₀ 𝕂 → IsAvatarOver D.X₀.left V₀ hV₀ L₀ 𝕃 →
      letI : Algebra Γ(W₀.toScheme, ⊤) Γ(V₀.toScheme, ⊤) :=
        ((D.X₀.hom.resLE W₀ V₀ hVW).appTop).hom.toAlgebra
      StacksDraft.PseudoCoherence.IsPseudoCoherent 𝕂 ∧
        HasFiniteTorDimensionCanonical Γ(W₀.toScheme, ⊤)
          ((ModuleCat.restrictScalars
            (algebraMap Γ(W₀.toScheme, ⊤) Γ(V₀.toScheme, ⊤))).mapDerivedCategory.obj 𝕃)) :
    Nonempty (D.AffineDerivedHomEquiv W₀ V₀ hV₀ hVW K₀ L₀) := by
  obtain ⟨𝕂, hK⟩ := exists_isAvatarOver_of_isPseudoCoherent D.X₀.left V₀ hV₀ K₀ hK₀
  obtain ⟨𝕃, hL⟩ := exists_isAvatarOver_of_isQuasicoherent D.X₀.left V₀ hV₀ L₀ hL₀qc
  obtain ⟨h𝕂, h𝕃⟩ := hprop 𝕂 𝕃 hK hL
  obtain ⟨eK₀⟩ := hK
  obtain ⟨eL₀⟩ := hL
  exact ⟨D.affineDerivedHomEquivOfBaseIso W₀ V₀ hV₀ hVW K₀ L₀ hW₀ 𝕂 𝕃 h𝕂 h𝕃 eK₀ eL₀⟩

end RelativeDescentSituation

end AlgebraicGeometry

end
