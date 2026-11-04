module

public import StacksFrontier.AlgebraicGeometry.DerivedPushforward.IsoTransport
public import StacksFrontier.AlgebraicGeometry.LocalCohomology.FiniteLocallyFreeComplementAffine
public import StacksFrontier.AlgebraicGeometry.ProperCohomologyFinite.Locality
public import StacksCore.Tactic.StacksAttribute

/-!
# Coherence of the higher direct images of a finite locally free module along an open immersion

Let `X` be a locally Noetherian scheme, `U` an open subscheme and `j : U → X` the inclusion.  If
the higher direct images `R^p j_* 𝒪_U` are coherent for `0 ≤ p < n`, then so are `R^p j_* ℱ` for
every finite locally free `𝒪_U`-module `ℱ`.  This is [Stacks, Tag 0BLT], and it is proved here.

The source's proof is *"the question is local on `X`, hence we may assume `X` is affine; say
`X = Spec A` and `Z = V(I)`; via [Stacks, Tag 0BK0] our lemma follows from [Stacks, Tag 0BPY]"*.
The second sentence is
`Stacks.LocalCohomologySequence.isCoherent_rightDerived_zeroLocusCompl_of_structureSheaf`, the
affine case, already in the library.  This file is the first sentence.

## Main results

* `Stacks.LocalCohomologySequence.isCoherent_rightDerived_opens_of_structureSheaf` — the affine
  case at an arbitrary open of `Spec A` rather than at the complement of a named vanishing
  locus.
* `Stacks.LocalCohomologySequence.isCoherent_rightDerived_of_isFiniteLocallyFree_affine` — the
  case of an open immersion into an arbitrary affine locally Noetherian scheme.
* `Stacks.LocalCohomologySequence.isCoherent_rightDerived_of_isFiniteLocallyFree` —
  **[Stacks, Tag 0BLT]**.

## Implementation notes

"Local on `X`" is
`Stacks.AlgebraicGeometry.ProperCohomologyFinite`'s
`isCoherent_rightDerivedPlus_of_forall_isAffineOpen`, whose hypotheses an open immersion into a
locally Noetherian scheme satisfies: `QuasiCompact j` holds because `X` is locally Noetherian
([Stacks, Tag 01OX]), and `QuasiSeparated j` because `j` is a monomorphism.  It reduces the tag
to an affine open `V` of `X` and the restricted morphism `j ∣_ V`, and that case is **not** the
affine case already in the library: `V.toScheme` is an affine scheme rather than `Spec` of a
ring, and `j ∣_ V` is an open immersion rather than the inclusion of an open of `V`.  The two
are bridged in two steps.

The first step is `isCoherent_rightDerived_of_isFiniteLocallyFree_affine`, which moves an open
immersion `g : W ⟶ T` into an *affine* scheme to `Spec Γ(T, ⊤)` along
`AlgebraicGeometry.Scheme.isoSpec` and along `AlgebraicGeometry.Scheme.Hom.isoOpensRange` on the
source.  This is the only place the
higher direct images are transported along an isomorphism of schemes, and the transport is
`Stacks.AlgebraicGeometry.DerivedPushforward.rightDerivedTransportIso`; the source open is then
the range of `g ≫ T.isoSpec.hom`, so no description of it is needed, and
`isCoherent_rightDerived_opens_of_structureSheaf` names it as the complement of a vanishing locus
only because every closed subset of a spectrum is one
(`PrimeSpectrum.isClosed_iff_zeroLocus_ideal`).

The second step instantiates that at `g = j ∣_ V`.  Its structure-sheaf hypothesis comes from
the tag's own hypothesis by [Stacks, Tag 01E5] — restriction to an open of the base commutes with
the higher direct image, as
`Stacks.AlgebraicGeometry.SchemeHigherDirectImage.rightDerivedPlusRestrictObjIso` — together with
`AlgebraicGeometry.Scheme.Modules.restrictUnitIso`, the restriction of a structure sheaf being a
structure sheaf.  The two indexings of the derived functors are compared by
`Stacks.DerivedIndexing.rightDerivedIso`.

**No hypothesis of this file is the affine case of the tag at the tag's own data.** The affine
case is applied, not assumed, and it is applied at the restricted morphism over an affine open,
never at `X` itself.

## References

* [Stacks Project, Tag 0BLT](https://stacks.math.columbia.edu/tag/0BLT)
* [Stacks Project, Tag 0BK0](https://stacks.math.columbia.edu/tag/0BK0)
* [Stacks Project, Tag 0BPY](https://stacks.math.columbia.edu/tag/0BPY)
* [Stacks Project, Tag 01E5](https://stacks.math.columbia.edu/tag/01E5)
* [Stacks Project, Tag 01OX](https://stacks.math.columbia.edu/tag/01OX)
-/

@[expose] public noncomputable section

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits Opposite TopologicalSpace
open Stacks.AlgebraicGeometry.CoherentDevissage
open Stacks.AlgebraicGeometry.DerivedPushforward
open Stacks.AlgebraicGeometry.ProperCohomologyFinite
open Stacks.AlgebraicGeometry.SchemeHigherDirectImage

universe u

attribute [local instance] HasDerivedCategory.standard

namespace Stacks.LocalCohomologySequence

/-! ### The affine case at an arbitrary open of a spectrum -/

/-- **The affine case of [Stacks, Tag 0BLT] at an arbitrary open.** Let `A` be a Noetherian ring,
`W` an open of `Spec A` and `j : W → Spec A` the inclusion.  If `R^p j_* 𝒪_W` is coherent for
`0 ≤ p < n`, then so is `R^p j_* ℱ` for every finite locally free `𝒪_W`-module `ℱ`.

Every closed subset of a spectrum is the vanishing locus of an ideal, so `W` is the complement of
one and this is
`Stacks.LocalCohomologySequence.isCoherent_rightDerived_zeroLocusCompl_of_structureSheaf`. -/
public theorem isCoherent_rightDerived_opens_of_structureSheaf {A : CommRingCat.{u}}
    [IsNoetherianRing A] (W : (Spec A).Opens) (n : ℕ)
    (hO : ∀ p : ℕ, p < n →
      (((Scheme.Modules.pushforward W.ι).rightDerived p).obj
        (SheafOfModules.unit W.toScheme.ringCatSheaf)).IsCoherent)
    (F : W.toScheme.Modules) (hF : Scheme.Modules.IsFiniteLocallyFree F) :
    ∀ p : ℕ, p < n →
      (((Scheme.Modules.pushforward W.ι).rightDerived p).obj F).IsCoherent := by
  obtain ⟨I, hI⟩ := (PrimeSpectrum.isClosed_iff_zeroLocus_ideal ((W : Set (Spec A)))ᶜ).mp
    W.isOpen.isClosed_compl
  obtain rfl : zeroLocusCompl I = W := Opens.ext (compl_eq_comm.mpr hI)
  exact isCoherent_rightDerived_zeroLocusCompl_of_structureSheaf I n hO F hF

/-! ### An open immersion into an affine scheme -/

/-- **[Stacks, Tag 0BLT] for an open immersion into an affine locally Noetherian scheme.** If
`R^p g_* 𝒪_W` is coherent for `0 ≤ p < n`, then so is `R^p g_* ℱ` for every finite locally free
`𝒪_W`-module `ℱ`.

`T` is identified with `Spec Γ(T, ⊤)` by `AlgebraicGeometry.Scheme.isoSpec` and `W` with the range
of `g ≫ T.isoSpec.hom` by `AlgebraicGeometry.Scheme.Hom.isoOpensRange`; the square they form
commutes by `AlgebraicGeometry.Scheme.Hom.isoOpensRange_hom_ι`, so
`Stacks.AlgebraicGeometry.DerivedPushforward.rightDerivedTransportIso` carries the higher direct
images between the two, and `isCoherent_rightDerived_opens_of_structureSheaf` applies on the
spectrum.  Both the finite local freeness of the transported `ℱ` and the identification of the
transported structure sheaf with the structure sheaf of the range use
`…DerivedPushforward.restrictInvIsoPushforward`: pushforward along the isomorphism is restriction
along its inverse. -/
public theorem isCoherent_rightDerived_of_isFiniteLocallyFree_affine {W T : Scheme.{u}}
    [IsAffine T] [IsLocallyNoetherian T] (g : W ⟶ T) [IsOpenImmersion g] (n : ℕ)
    (hO : ∀ p : ℕ, p < n →
      (((Scheme.Modules.pushforward g).rightDerived p).obj
        (SheafOfModules.unit W.ringCatSheaf)).IsCoherent)
    (F : W.Modules) (hF : Scheme.Modules.IsFiniteLocallyFree F) :
    ∀ p : ℕ, p < n → (((Scheme.Modules.pushforward g).rightDerived p).obj F).IsCoherent := by
  have hNoeth : IsNoetherianRing Γ(T, (⊤ : T.Opens)) :=
    IsLocallyNoetherian.component_noetherian ⟨⊤, isAffineOpen_top T⟩
  intro p hp
  refine isCoherent_rightDerived_of_transport g (Scheme.Hom.opensRange (g ≫ T.isoSpec.hom)).ι
    (Scheme.Hom.isoOpensRange (g ≫ T.isoSpec.hom)) T.isoSpec
    (Scheme.Hom.isoOpensRange_hom_ι (g ≫ T.isoSpec.hom)) p F ?_
  refine isCoherent_rightDerived_opens_of_structureSheaf _ n (fun p' hp' => ?_) _ ?_ p hp
  · have := isCoherent_rightDerived_transport g _ _ T.isoSpec
      (Scheme.Hom.isoOpensRange_hom_ι (g ≫ T.isoSpec.hom)) p'
      (SheafOfModules.unit W.ringCatSheaf) (hO p' hp')
    exact isCoherent_of_iso
      (((Scheme.Modules.pushforward
          (Scheme.Hom.opensRange (g ≫ T.isoSpec.hom)).ι).rightDerived p').mapIso
        ((Scheme.Modules.restrictUnitIso
            (Scheme.Hom.isoOpensRange (g ≫ T.isoSpec.hom)).inv).symm ≪≫
          (restrictInvIsoPushforward (Scheme.Hom.isoOpensRange (g ≫ T.isoSpec.hom))).app
            (SheafOfModules.unit W.ringCatSheaf)))
  · exact Scheme.Modules.IsFiniteLocallyFree.of_iso
      ((restrictInvIsoPushforward (Scheme.Hom.isoOpensRange (g ≫ T.isoSpec.hom))).app F)
      (Scheme.Modules.IsFiniteLocallyFree.restrict
        (Scheme.Hom.isoOpensRange (g ≫ T.isoSpec.hom)).inv hF)

/-! ### Tag 0BLT -/

/-- The `ℕ`-indexed and `ℤ`-indexed right derived functors of a pushforward have the same
coherence at a module. -/
private theorem isCoherent_rightDerived_iff_rightDerivedPlus {X Y : Scheme.{u}} (f : X ⟶ Y)
    (n : ℕ) (F : X.Modules) :
    (((Scheme.Modules.pushforward f).rightDerived n).obj F).IsCoherent ↔
      (((Scheme.Modules.pushforward f).rightDerivedPlus (n : ℤ)).obj F).IsCoherent :=
  ⟨fun _ => isCoherent_of_iso
      ((Stacks.DerivedIndexing.rightDerivedIso (Scheme.Modules.pushforward f) n).app F).symm,
   fun _ => isCoherent_of_iso
      ((Stacks.DerivedIndexing.rightDerivedIso (Scheme.Modules.pushforward f) n).app F)⟩

/-- **[Stacks, Tag 0BLT].** Let `X` be a locally Noetherian scheme, let `j : U → X` be the
inclusion of an open subscheme and let `n ≥ 0`.  If `R^p j_* 𝒪_U` is coherent for `0 ≤ p < n`,
then so is `R^p j_* ℱ` for `0 ≤ p < n` and every finite locally free `𝒪_U`-module `ℱ`.

The inclusion is taken to be an arbitrary open immersion `j`, which is the same statement: an
open immersion is the inclusion of its open image composed with an isomorphism.

The question is local on `X`: coherence of a higher direct image along the quasi-compact
quasi-separated `j` may be checked on every affine open `V` of `X`, for the restricted morphism
`j ∣_ V` and the restricted module, by
`…ProperCohomologyFinite.isCoherent_rightDerivedPlus_of_forall_isAffineOpen`.  That case is
`isCoherent_rightDerived_of_isFiniteLocallyFree_affine`, `V.toScheme` being affine and locally
Noetherian; its hypothesis on the structure sheaf is the tag's hypothesis restricted to `V` by
[Stacks, Tag 01E5], and its finite local freeness is the restriction of `ℱ`. -/
@[stacks 0BLT]
public theorem isCoherent_rightDerived_of_isFiniteLocallyFree {U X : Scheme.{u}}
    [IsLocallyNoetherian X] (j : U ⟶ X) [IsOpenImmersion j] (n : ℕ)
    (hO : ∀ p : ℕ, p < n →
      (((Scheme.Modules.pushforward j).rightDerived p).obj
        (SheafOfModules.unit U.ringCatSheaf)).IsCoherent)
    (F : U.Modules) (hF : Scheme.Modules.IsFiniteLocallyFree F) :
    ∀ p : ℕ, p < n →
      (((Scheme.Modules.pushforward j).rightDerived p).obj F).IsCoherent := by
  have hUN : IsLocallyNoetherian U := isLocallyNoetherian_of_isOpenImmersion j
  have hFclass : AlgebraicGeometry.SheafOfModules.IsFiniteLocallyFree.{u, u, u} F :=
    (Scheme.Modules.isFiniteLocallyFree_iff F).mp hF
  have hFcoh : F.IsCoherent :=
    Stacks.AlgebraicGeometry.CoherenceCriteria.isCoherent_of_isFiniteLocallyFree _ F
  obtain ⟨_, -⟩ :=
    Stacks.AlgebraicGeometry.CoherentTFAE.isQuasicoherent_isFiniteType_of_isCoherent F
  intro p hp
  have key : (((Scheme.Modules.pushforward j).rightDerivedPlus (p : ℤ)).obj F).IsCoherent := by
    refine isCoherent_rightDerivedPlus_of_forall_isAffineOpen j F p (fun V => ?_)
    have hVaff : IsAffine (V : X.Opens).toScheme := V.2
    refine isCoherent_rightDerived_of_isFiniteLocallyFree_affine (j ∣_ (V : X.Opens)) n
      (fun p' hp' => ?_) _ ?_ p hp
    · have := Stacks.AlgebraicGeometry.ReflexiveModules.isCoherent_restrict_of_isOpenImmersion
        (V : X.Opens).ι _
        ((isCoherent_rightDerived_iff_rightDerivedPlus j p' _).mp (hO p' hp'))
      have := isCoherent_of_iso (rightDerivedPlusRestrictObjIso j (V : X.Opens) p'
        (SheafOfModules.unit U.ringCatSheaf))
      have := (isCoherent_rightDerived_iff_rightDerivedPlus (j ∣_ (V : X.Opens)) p' _).mpr this
      exact isCoherent_of_iso
        (((Scheme.Modules.pushforward (j ∣_ (V : X.Opens))).rightDerived p').mapIso
          (Scheme.Modules.restrictUnitIso (j ⁻¹ᵁ (V : X.Opens)).ι).symm)
    · exact Scheme.Modules.IsFiniteLocallyFree.restrict (j ⁻¹ᵁ (V : X.Opens)).ι hF
  exact (isCoherent_rightDerived_iff_rightDerivedPlus j p F).mpr key

end Stacks.LocalCohomologySequence

end
