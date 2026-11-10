module

public import StacksFrontier.AlgebraicGeometry.DerivedQCoh.AnyModel.GenerationStepOnASubcategory
public import StacksFrontier.AlgebraicGeometry.DerivedQCoh.AnyModel.HomOutOfSupportedPushforward
public import StacksFrontier.AlgebraicGeometry.DerivedQCoh.AnyModel.SupportedPushforwardPerfect
public import StacksFrontier.AlgebraicGeometry.DerivedQCoh.PerfectGeneratorInduction
public import StacksFrontier.AlgebraicGeometry.DerivedQCoh.SupportedPushforwardScheme
public import StacksFrontier.AlgebraicGeometry.Duality.CompactGeneration.SupportedDirectSums
public import StacksFrontier.AlgebraicGeometry.QuasiCoherent.Coherator.QcqsPushforwardAnyModel
public import StacksFrontier.AlgebraicGeometry.Rouquier.SupportedGeneratorIsoSpec
public import StacksFrontier.AlgebraicGeometry.Rouquier.SupportedPerfectSummand
import StacksCore.Tactic.StacksAttribute

/-!
# The inductive step of Tag 0A9A: two opens, one of them a spectrum

Let `X` be a quasi-compact quasi-separated scheme covered by two opens `U` and `V`, with `U`
quasi-compact and `V` presented by an isomorphism `e : V ≅ Spec A`, and let `T ⊆ X` be closed with
quasi-compact complement. If `D_{QCoh, U ∩ T}(𝒪_U)` has a perfect weak triangulated generator then
so does `D_{QCoh,T}(𝒪_X)`.

This is the inductive step of [Stacks, Tag 0A9A], and it is
`Stacks.DerivedQCoh.hasPerfectGenerator_of_two_opens` -- the inductive step of
[Stacks, Tag 09IS] -- with the support condition carried along. The generator is again a
biproduct `Q ⊞ K`:

* `Q` is a perfect object of `D(𝒪_X)` supported on `T` whose restriction to `U` has the given
  generator as a direct summand, which is the supported form of [Stacks, Tag 09IQ],
  `Stacks.Rouquier.exists_isPerfect_supported_retract_derivedRestrict`;
* `K = Rj_{V*}K_V` is the derived direct image of the perfect generator of
  `D_{QCoh, V ∩ (T ∖ U)}(𝒪_V)` supplied by the affine case
  `Stacks.Rouquier.exists_isPerfect_generator_supported_of_iso_spec`.

**Where the supported statement differs from the unsupported one.** In [Stacks, Tag 09IS] the
detecting object on `V` is the Koszul object of a sequence cutting `X ∖ U` out of `V`; here it is
the affine generator for the smaller closed set

`S := T ∖ U`,

which is closed, has quasi-compact complement `Tᶜ ∪ U`, and is contained in `V` because `U` and
`V` cover `X`. At `T` the whole space one has `S = X ∖ U` and the two agree -- the affine
generator of `Stacks.Rouquier.exists_isPerfect_generator_supported_of_iso_spec` *is* a Koszul
object -- so what is below is a generalisation of the 09IS step and not a parallel construction.
Taking the affine generator rather than rebuilding the Koszul object is what keeps the proof
short: the three properties the detecting object has to have are exactly the three the affine case
delivers.

## Main results

* `Stacks.Rouquier.exists_isPerfect_isWeakTriangulatedGenerator_supported_of_two_opens` -- the
  statement above.
* `Stacks.Rouquier.isCompact_compl_preimage_of_isOpenEmbedding` -- inside a quasi-compact open of
  a quasi-separated space, the complement of the preimage of a closed set with quasi-compact
  complement is quasi-compact.

## Implementation notes

**The model is the locally small one** of
`StacksFrontier/Homology/DerivedCategory/LocallySmall.lean`,
as everything in `StacksFrontier/AlgebraicGeometry/Rouquier/` is: no
`CategoryTheory.HasDerivedCategory` binder appears below, so instance search supplies the global
instances.

**The subcategory instances are seated by hand, at the `AlgebraicGeometry.Scheme.Modules`
spelling.** `Stacks.Duality.quasiCoherentSupported_isTriangulated` and
`Stacks.Duality.quasiCoherentSupported_isClosedUnderIsomorphisms` of
`StacksFrontier/AlgebraicGeometry/Duality/CompactGeneration/SupportedDirectSums.lean` are instances,
but they are stated in the spelling `SheafOfModules.{u} Z.ringCatSheaf` while
`Stacks.Duality.OpenImmersion.isWeakTriangulatedGenerator_biprod_of_detection_of_prop` asks for
them at `AlgebraicGeometry.Scheme.Modules`, and those two types carry separately declared
`Category` instances, so synthesis does not cross between them. The two subcategories are
therefore bound with the ambient category written out, and their four instances introduced from
the `Stacks.Duality` statements that take the weak-Serre input explicitly -- as
`Stacks.DerivedQCoh.hasPerfectGenerator_of_two_opens` does for `D_QCoh`.

Two further seatings are needed for the same reason. `CategoryTheory.Limits.HasBinaryBiproducts`
of the full subcategory is not an instance anywhere: `D_{QCoh,T}(𝒪_X)` is closed under binary
products because it is triangulated and strictly full
(`CategoryTheory.ObjectProperty.IsClosedUnderBinaryProducts`), and
`CategoryTheory.Limits.HasBinaryBiproducts.of_hasBinaryProducts` turns that into biproducts, but
it is a theorem and not an instance. And the biproduct itself is bound before the conclusion is
refined: elaborated against the conclusion's type it would be read in the `SheafOfModules`
spelling, where that seating does not apply.

**The affine open is presented by an isomorphism with a spectrum rather than by
`AlgebraicGeometry.IsAffineOpen`**, which is the shape
`Stacks.DerivedQCoh.hasPerfectGenerator_of_two_opens` and the affine case
`Stacks.Rouquier.exists_isPerfect_generator_supported_of_iso_spec` both use. `IsAffine V` and
`CompactSpace V` are recovered from it below, so nothing is assumed beyond affineness of `V`.

**No `@[stacks]` attribute is attached.** [Stacks, Tag 0A9A] is the quasi-compact quasi-separated
*scheme* statement, obtained from this step by the induction principle [Stacks, Tag 08DR] in
`StacksFrontier/AlgebraicGeometry/Rouquier/SupportedGeneratorQcqs.lean`, which carries the tag; what
is below is one step of that induction, which the source states inside the proof of 0A9A rather
than as a numbered result. [Stacks, Tag 09IS] is the unsupported statement and is registered on
`Stacks.DerivedQCoh.hasPerfectGenerator_of_two_opens`.

**`Stacks.Rouquier.isCompact_compl_preimage_of_isOpenEmbedding` is about topological spaces** and
belongs in `StacksFrontier/Topology/`; it is here because that tree was outside the scope of the
work that needed it.

## References

* [Stacks Project, Tag 0A9A](https://stacks.math.columbia.edu/tag/0A9A)
* [Stacks Project, Tag 09IS](https://stacks.math.columbia.edu/tag/09IS)
* [Stacks Project, Tag 09IQ](https://stacks.math.columbia.edu/tag/09IQ)
* [Stacks Project, Tag 09IR](https://stacks.math.columbia.edu/tag/09IR)
* [Stacks Project, Tag 08DF](https://stacks.math.columbia.edu/tag/08DF)
* [Stacks Project, Tag 08DP](https://stacks.math.columbia.edu/tag/08DP)
-/

-- This file uses the locally small derived-category models below, which are not
-- global instances (see `StacksFrontier.Homology.DerivedCategory.LocallySmall`):
-- `D(R)` for `R`-modules.
-- `D(R)` for sheaves of modules on a small site.
-- `D(𝒪_X)` for a scheme.
attribute [local instance] ModuleCat.hasDerivedCategory
attribute [local instance] SheafOfModules.hasDerivedCategory
attribute [local instance] AlgebraicGeometry.Scheme.Modules.hasDerivedCategory

@[expose] public noncomputable section

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits CategoryTheory.ObjectProperty
open CategoryTheory.Pretriangulated TopologicalSpace
open Stacks.Cohomology.PerfectComplexes (IsPerfect)
open Stacks.DerivedQCoh (cohomologySupportedOn_derivedPushforward_scheme cohomologySupportedOn_mono)
open Stacks.DerivedQCoh.AnyModel (isDQCoh_of_isPerfect isPerfect_biprod_fullSubcategory
  isPerfect_derivedPushforward_of_cohomologySupportedOn isZero_of_isZero_derivedRestrict_of_cover
  rightOrthogonal_shiftClosure_singleton_derivedPushforward_iff)
open Stacks.Duality.OpenImmersion (cohomologySupportedOn_compl_range_iff_isZero_derivedRestrict
  derivedRestrict liftDerivedRestrict isWeakTriangulatedGenerator_biprod_of_detection_of_prop)

universe u

namespace Stacks.Rouquier

/-- **Inside a quasi-compact open, the complement of the preimage of a closed set with
quasi-compact complement is quasi-compact**, on a quasi-separated space. The open is presented as
the range of an open embedding, which is the shape the induction of [Stacks, Tag 0A9A] consumes;
the image of that complement in the ambient space is `Tᶜ ∩ range f`, an intersection of two
quasi-compact opens. -/
theorem isCompact_compl_preimage_of_isOpenEmbedding {X : Type*} {Y : Type*} [TopologicalSpace X]
    [TopologicalSpace Y] [QuasiSeparatedSpace X] {f : Y → X} (hf : Topology.IsOpenEmbedding f)
    (hfc : IsCompact (Set.range f)) (T : Set X) (hT : IsClosed T) (hTc : IsCompact Tᶜ) :
    IsCompact (f ⁻¹' T)ᶜ := by
  refine hf.isEmbedding.isCompact_iff.mpr ?_
  rw [← Set.preimage_compl, Set.image_preimage_eq_inter_range]
  exact QuasiSeparatedSpace.inter_isCompact _ _ hT.isOpen_compl hTc hf.isOpen_range hfc

/-- **The inductive step of [Stacks, Tag 0A9A].** Let `X` be a quasi-compact quasi-separated
scheme covered by a quasi-compact open `U` and an open `V` presented by an isomorphism
`e : V ≅ Spec A`, and let `T ⊆ X` be closed with quasi-compact complement. If
`D_{QCoh, U ∩ T}(𝒪_U)` has a perfect weak triangulated generator then so does
`D_{QCoh,T}(𝒪_X)`.

The generator is `Q ⊞ K` of
`Stacks.Duality.OpenImmersion.isWeakTriangulatedGenerator_biprod_of_detection_of_prop` at
`A = D_{QCoh,T}(𝒪_X)` and `B = D_{QCoh, U ∩ T}(𝒪_U)`, whose hypotheses are discharged as follows.
`Q` is the perfect object of `D(𝒪_X)` supported on `T` restricting to a retract of the given
generator, which is the supported form of [Stacks, Tag 09IQ]; `K = Rj_{V*}K_V` is the derived
direct image of the affine generator for `S = T ∖ U`, perfect by [Stacks, Tag 08DP] because `K_V`
is supported on `S` and `S ⊆ V`, and supported on `S` -- hence on `T` -- by [Stacks, Tag 08DF].
`hres` is `Stacks.Rouquier.quasiCoherentSupported_derivedRestrict`; `hpush` is part (1) of
[Stacks, Tag 08D5] together with 08DF again; the counit is invertible because `Rj_{U*}` along an
open immersion is fully faithful; and the closure under cones is triangulatedness of
`D_{QCoh,T}(𝒪_X)`.

`hdet` is [Stacks, Tag 09IR] for `S`: an object `M` of `D_{QCoh,T}(𝒪_X)` restricting to zero on
`U` is supported on `S`, so orthogonality to the shifts of `Rj_{V*}K_V` descends to orthogonality
of `M|_V` to the shifts of `K_V`, whence `M|_V = 0` by the detection property of the affine
generator; and `M|_U = 0` together with `M|_V = 0` on a cover gives `M = 0`. -/
theorem exists_isPerfect_isWeakTriangulatedGenerator_supported_of_two_opens {X : Scheme.{u}}
    [CompactSpace X] [QuasiSeparatedSpace X] (U V : X.Opens) (hU : IsCompact (U : Set X))
    {A : Type u} [CommRing A] (e : V.toScheme ≅ Spec (CommRingCat.of A)) (hUV : U ⊔ V = ⊤)
    (T : Set X) (hT : IsClosed T) (hTc : IsCompact Tᶜ)
    (hgenU : ∃ P : Stacks.Duality.QuasiCoherentSupportedDerivedCategory U.toScheme
        (⇑U.ι.base ⁻¹' T),
      IsPerfect (X := U.toScheme.toRingedSpace) P.obj ∧
        (ObjectProperty.singleton P).IsWeakTriangulatedGenerator) :
    ∃ G : Stacks.Duality.QuasiCoherentSupportedDerivedCategory X T,
      IsPerfect (X := X.toRingedSpace) G.obj ∧
        (ObjectProperty.singleton G).IsWeakTriangulatedGenerator := by
  classical
  let : CompactSpace U.toScheme := isCompact_iff_compactSpace.mp hU
  let : IsAffine V.toScheme := IsAffine.of_isIso e.hom
  let hVcs : CompactSpace V.toScheme := inferInstance
  have hVc : IsCompact (V : Set X) := isCompact_iff_compactSpace.2 hVcs
  -- The two subcategories, with their triangulatedness seated by hand.
  let AX : ObjectProperty (DerivedCategory X.Modules) :=
    Stacks.Duality.quasiCoherentSupported X T
  let BU : ObjectProperty (DerivedCategory U.toScheme.Modules) :=
    Stacks.Duality.quasiCoherentSupported U.toScheme (⇑U.ι.base ⁻¹' T)
  let : AX.IsTriangulated :=
    Stacks.Duality.quasiCoherentSupported_isTriangulated X T
      (Stacks.AlgebraicGeometry.QuasicoherentWeakSerre.isQuasicoherent_isWeakSerre X)
  let : BU.IsTriangulated :=
    Stacks.Duality.quasiCoherentSupported_isTriangulated U.toScheme (⇑U.ι.base ⁻¹' T)
      (Stacks.AlgebraicGeometry.QuasicoherentWeakSerre.isQuasicoherent_isWeakSerre U.toScheme)
  let : AX.IsClosedUnderIsomorphisms :=
    Stacks.Duality.quasiCoherentSupported_isClosedUnderIsomorphisms X T
      (Stacks.AlgebraicGeometry.QuasicoherentWeakSerre.isQuasicoherent_isWeakSerre X)
  let : BU.IsClosedUnderIsomorphisms :=
    Stacks.Duality.quasiCoherentSupported_isClosedUnderIsomorphisms U.toScheme
      (⇑U.ι.base ⁻¹' T)
      (Stacks.AlgebraicGeometry.QuasicoherentWeakSerre.isQuasicoherent_isWeakSerre U.toScheme)
  -- `S = T ∖ U`: closed, with quasi-compact complement, and contained in `V`.
  have hcover : ∀ x : X, x ∈ U ∨ x ∈ V := fun x => hUV.ge (Set.mem_univ x)
  let S : Set X := T ∩ (U : Set X)ᶜ
  have hS : IsClosed S := hT.inter U.isOpen.isClosed_compl
  have hSc : IsCompact Sᶜ := by
    change IsCompact (T ∩ (U : Set X)ᶜ)ᶜ
    rw [Set.compl_inter, compl_compl]
    exact hTc.union hU
  have hSV : S ⊆ (V : Set X) := fun x hx => (hcover x).resolve_left hx.2
  have hSU : S ⊆ ((U : Set X))ᶜ := fun _ hx => hx.2
  have hST : S ⊆ T := fun _ hx => hx.1
  -- The detecting object on `V`: the affine generator for the preimage of `S`.
  obtain ⟨KV, hKVmem, hKVperf, hKVdet⟩ :=
    exists_isPerfect_generator_supported_of_iso_spec e (⇑V.ι.base ⁻¹' S)
      (hS.preimage V.ι.continuous)
      (isCompact_compl_preimage_of_isOpenEmbedding V.ι.isOpenEmbedding
        (by rw [Scheme.Opens.range_ι]; exact hVc) S hS hSc)
  have hKVsupp : Stacks.Cohomology.PushforwardRestriction.CohomologySupportedOn
      V.toScheme.ringCatSheaf (⇑V.ι.base ⁻¹' S) KV :=
    cohomologySupportedOn_of_derivedSupported _ _ _ hKVmem.2
  -- Its derived direct image: perfect, quasi-coherent, and supported on `S` hence on `T`.
  let K : DerivedCategory X.Modules := (Stacks.Duality.derivedPushforward V.ι).obj KV
  have hKperf : IsPerfect (X := X.toRingedSpace) K :=
    isPerfect_derivedPushforward_of_cohomologySupportedOn X V S hS hSV KV hKVperf hKVsupp
  have hKS : Stacks.Cohomology.PushforwardRestriction.CohomologySupportedOn X.ringCatSheaf S K :=
    cohomologySupportedOn_derivedPushforward_scheme X V S hS KV hKVsupp
  have hKmem : AX K :=
    ⟨fun n =>
      Stacks.Duality.isQuasicoherent_homology_derivedPushforward_opens V ⟨KV, hKVmem.1⟩ n,
      derivedSupported_of_cohomologySupportedOn _ _ _
        (cohomologySupportedOn_mono _ hST hKS)⟩
  -- `hKzero`: `K` restricts to zero on `U`, being supported on `S ⊆ X ∖ U`.
  have hKzero : IsZero ((derivedRestrict U.ι).obj K) :=
    (cohomologySupportedOn_compl_range_iff_isZero_derivedRestrict U.ι K).1
      (cohomologySupportedOn_mono _ (by rw [Scheme.Opens.range_ι]; exact hSU) hKS)
  -- The two closure hypotheses of the generation step.
  have hres : ∀ W : AX.FullSubcategory, BU ((derivedRestrict U.ι).obj W.obj) := fun W =>
    quasiCoherentSupported_derivedRestrict U.ι T W.obj W.2
  have hpush : ∀ L : BU.FullSubcategory,
      AX ((Stacks.Duality.derivedPushforward U.ι).obj L.obj) := fun L =>
    ⟨fun n =>
      Stacks.Duality.isQuasicoherent_homology_derivedPushforward_opens U ⟨L.obj, L.2.1⟩ n,
      derivedSupported_of_cohomologySupportedOn _ _ _
        (cohomologySupportedOn_derivedPushforward_scheme X U T hT L.obj
          (cohomologySupportedOn_of_derivedSupported _ _ _ L.2.2))⟩
  have hA : ∀ Tr : Triangle (DerivedCategory X.Modules),
      Tr ∈ distTriang (DerivedCategory X.Modules) → AX Tr.obj₁ → AX Tr.obj₂ → AX Tr.obj₃ :=
    fun Tr hTr h₁ h₂ => AX.ext_of_isTriangulatedClosed₃ Tr hTr h₁ h₂
  -- `hdet`: [Stacks, Tag 09IR] for `S`.
  have hdet : ∀ M : DerivedCategory X.Modules, AX M →
      IsZero ((derivedRestrict U.ι).obj M) →
      ((ObjectProperty.singleton K).shiftClosure ℤ).rightOrthogonal M → IsZero M := by
    intro M hM hMU hortho
    have hMUsupp : Stacks.Cohomology.PushforwardRestriction.CohomologySupportedOn X.ringCatSheaf
        (Set.range ⇑U.ι.base)ᶜ M :=
      (cohomologySupportedOn_compl_range_iff_isZero_derivedRestrict U.ι M).2 hMU
    have hMS : Stacks.Cohomology.PushforwardRestriction.CohomologySupportedOn X.ringCatSheaf S M :=
      fun n x hx => by
        by_cases hxT : x ∈ T
        · refine hMUsupp n x ?_
          rw [Set.mem_compl_iff, not_not, Scheme.Opens.range_ι]
          by_contra hxU
          exact hx ⟨hxT, hxU⟩
        · exact cohomologySupportedOn_of_derivedSupported _ _ _ hM.2 n x hxT
    have hMV := (rightOrthogonal_shiftClosure_singleton_derivedPushforward_iff V S hS hSV KV
      hKVsupp M).1 hortho
    have hMVzero : IsZero ((Scheme.Modules.restrictFunctor V.ι).mapDerivedCategory.obj M) := by
      refine hKVdet _ (quasiCoherentSupported_derivedRestrict V.ι S M
        ⟨hM.1, derivedSupported_of_cohomologySupportedOn _ _ _ hMS⟩) fun n => ⟨fun a b => ?_⟩
      have hz := (rightOrthogonal_shiftClosure_singleton_iff_forall_hom_eq_zero _ _).1 hMV n
      exact (hz a).trans (hz b).symm
    exact isZero_of_isZero_derivedRestrict_of_cover U V hcover hMU hMVzero
  -- The generator, and the two assertions about it.
  obtain ⟨P, hPperf, hPgen⟩ := hgenU
  obtain ⟨Q, hQperf, hQT, i, p, hip⟩ :=
    exists_isPerfect_supported_retract_derivedRestrict U hU T hT
      (fun W hW => QuasiSeparatedSpace.inter_isCompact _ _ W.isOpen hW hT.isOpen_compl hTc)
      P.obj hPperf (cohomologySupportedOn_of_derivedSupported _ _ _ P.2.2)
  have hQmem : AX Q :=
    ⟨isDQCoh_of_isPerfect (AlgebraicGeometry.Scheme.Modules.hasDerivedCategory X) Q hQperf,
      derivedSupported_of_cohomologySupportedOn _ _ _ hQT⟩
  let Qo : AX.FullSubcategory := ⟨Q, hQmem⟩
  let Ko : AX.FullSubcategory := ⟨K, hKmem⟩
  have hret : Retract P ((liftDerivedRestrict U.ι AX BU hres).obj Qo) :=
    ObjectProperty.retractOfι BU i p hip
  let : HasBinaryBiproducts AX.FullSubcategory := HasBinaryBiproducts.of_hasBinaryProducts
  let G : AX.FullSubcategory := Qo ⊞ Ko
  refine ⟨G, ?_, ?_⟩
  · exact isPerfect_biprod_fullSubcategory AX Qo Ko hQperf hKperf
  · exact isWeakTriangulatedGenerator_biprod_of_detection_of_prop U.ι AX BU hres hpush hA
      (K := Ko) hret hPgen hKzero (fun _ => inferInstance) hdet

end Stacks.Rouquier

end
