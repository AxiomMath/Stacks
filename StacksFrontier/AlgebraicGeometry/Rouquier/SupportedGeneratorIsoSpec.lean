module

public import StacksFrontier.AlgebraicGeometry.Duality.OpenImmersion.TwistedInverseImageRestrictionSupport
public import StacksFrontier.AlgebraicGeometry.Rouquier.AffineSupportedGenerator

/-!
# A perfect generator for `D_{QCoh,T}(𝒪_Y)` on a scheme isomorphic to a spectrum

Let `Y` be a scheme isomorphic to `Spec A` and let `T ⊆ Y` be a closed subset whose complement is
quasi-compact. This file transports
`Stacks.Rouquier.exists_isPerfect_generator_supported_spec` — the affine base case of
[Stacks, Tag 0A9A], proved on `Spec A` literally — across the isomorphism, so that it applies to
an arbitrary affine scheme and hence to an affine open of an arbitrary scheme.

That is the step [Stacks, Tag 09IS] takes in
`Stacks.DerivedQCoh.AnyModel.hasPerfectGenerator_of_iso_spec`, and it is taken here in the same
two pieces.

**Perfectness is not transported.** Carrying perfectness along an isomorphism of schemes at the
locally small derived category is exactly what `Stacks.DerivedQCoh.isPerfect_derivedRestrict`
does not provide, that statement installing `CategoryTheory.HasDerivedCategory.standard` as a
file-local instance. The generator is therefore not an abstract perfect object of
`D_{QCoh,T}(𝒪_{Spec A})` read on `Y`, but the Koszul object of an explicit sequence cutting `T`
out of `Spec A`, for which `Stacks.Koszul.TwoOpens.isPerfect_derivedRestrict_koszulObject` gives
perfectness of the restriction along an *arbitrary* open immersion into `Spec A` — an
isomorphism out of `Y` included. This is why the existential of
`Stacks.Rouquier.exists_isPerfect_generator_supported_spec` is not the statement consumed below:
its three constituents `Stacks.Rouquier.quasiCoherentSupported_koszulObject`,
`Stacks.Koszul.Truncation.isPerfect_koszulObject` and
`Stacks.Rouquier.isZero_of_subsingleton_hom_koszulObject` are used one at a time at the named
Koszul object.

**Detection is transported, and the support condition with it.** An object `M` of
`D_{QCoh,T}(𝒪_Y)` restricts along `e.inv` to an object of `D_{QCoh,e.inv⁻¹T}(𝒪_{Spec A})`; the
Koszul object detects the vanishing of that restriction, and restriction along `e.hom` reflects
both the zero object and the vanishing of all morphisms out of all shifts of an object. The three
inputs are `Stacks.DerivedQCoh.AnyModel.isZero_of_isZero_derivedRestrict_of_compEqId`,
`Stacks.DerivedQCoh.AnyModel.faithful_derivedRestrict_of_compEqId` and
`Stacks.DerivedQCoh.AnyModel.forall_hom_shift_eq_zero_of_faithful`.

## Main definitions

None.

## Main results

* `Stacks.Rouquier.cohomologySupportedOn_derivedRestrict` — restriction along an open immersion
  of schemes pulls the supporting set back.
* `Stacks.Rouquier.quasiCoherentSupported_derivedRestrict` — hence it carries
  `D_{QCoh,T}(𝒪_Y)` into `D_{QCoh,j⁻¹T}(𝒪_X)`.
* `Stacks.Rouquier.isZero_of_forall_hom_derivedRestrict_of_iso` — detection of the zero object of
  a full subcategory travels along an isomorphism of schemes.
* `Stacks.Rouquier.exists_isPerfect_generator_supported_of_iso_spec` and
  `Stacks.Rouquier.exists_isPerfect_isWeakTriangulatedGenerator_supported_of_iso_spec` — the base
  case of [Stacks, Tag 0A9A] at a scheme presented by an isomorphism with a spectrum.

## Implementation notes

**No `@[stacks 0A9A]` attribute is attached, and none is possible here.** Tag 0A9A is the
statement for a quasi-compact quasi-separated *scheme*; what is proved below is its base case,
on a scheme isomorphic to an affine one. Three further steps — the supported form of
[Stacks, Tag 09IQ], the extension by zero of a supported perfect object, and the induction
principle [Stacks, Tag 08DR] — stand between this file and the tag, which is registered on
`Stacks.Rouquier.exists_isPerfect_isWeakTriangulatedGenerator_supported` of
`StacksFrontier/AlgebraicGeometry/Rouquier/SupportedGeneratorQcqs.lean`.

**`Stacks.Rouquier.isZero_of_forall_hom_derivedRestrict_of_iso` subsumes
`Stacks.DerivedQCoh.AnyModel.isZero_of_forall_hom_derivedRestrict_of_iso`.** The two differ only
in which subcategory the detection statement is read in: there `D_QCoh(𝒪_Z)`, here an arbitrary
`B ⊆ D(𝒪_Z)` whose membership for the restricted object is a hypothesis. The proof is the same
three lines. The dedup-correct move is to delete the 09IS version and have its one call site pass
`B = D_QCoh(𝒪_Z)` together with
`Stacks.Duality.OpenImmersion.derivedCategoryB_derivedRestrict e.inv M hM`; that file is not
this one's to change, and the one-line form of the change is recorded in the report of the work
that produced this file.

**`Stacks.Rouquier.cohomologySupportedOn_derivedRestrict` generalises
`Stacks.DerivedQCoh.cohomologySupportedOn_derivedRestriction`** from the inclusion of an open
subscheme to an arbitrary open immersion of schemes, which is what an isomorphism of schemes
needs. It is a separate declaration rather than a generalisation in place because the existing
statement is about `ExtensionByZeroModules.jStar` over a sheaf of rings on a topological space,
with the restricted ring spelled `resRing U O`; rephrasing it for a morphism of schemes would
change the spelling of its conclusion and so of its four call sites. The two proofs are different
as well: the one below reads the stalk comparison
`Stacks.Duality.OpenImmersion.stalkRestrictHomologyIso` off, where the existing one builds it.

**The model is the locally small one** of `StacksFrontier/Homology/DerivedCategory/LocallySmall.lean`:
no `CategoryTheory.HasDerivedCategory` binder appears below, so instance search supplies the
global instances. This is forced by the affine base case this file transports; see the
implementation notes of
`StacksFrontier/AlgebraicGeometry/Rouquier/AffineSupportedGenerator.lean`.

## References

* [Stacks Project, Tag 0A9A](https://stacks.math.columbia.edu/tag/0A9A)
* [Stacks Project, Tag 09IS](https://stacks.math.columbia.edu/tag/09IS)
* [Stacks Project, Tag 08DA](https://stacks.math.columbia.edu/tag/08DA)
* [Rouquier, Theorem 6.8, *Dimensions of triangulated categories*]
-/

-- This file uses the locally small derived-category models below, which are not
-- global instances (see `StacksFrontier.Homology.DerivedCategory.LocallySmall`):
-- `D(R)` for sheaves of modules on a small site.
-- `D(𝒪_X)` for a scheme.
attribute [local instance] SheafOfModules.hasDerivedCategory
attribute [local instance] AlgebraicGeometry.Scheme.Modules.hasDerivedCategory

@[expose] public noncomputable section

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits CategoryTheory.ObjectProperty
open TopologicalSpace
open Stacks.Cohomology.PerfectComplexes (IsPerfect)
open Stacks.Koszul.Truncation (koszulObject)
open Stacks.DerivedQCoh.AnyModel (derivedRestrictCompIsoId
  faithful_derivedRestrict_of_compEqId forall_hom_shift_eq_zero_of_faithful
  isZero_of_isZero_derivedRestrict_of_compEqId)

universe u

namespace Stacks.Rouquier

/-! ### Support pulls back along an open immersion -/

/-- **Restriction along an open immersion pulls the supporting set back.** If the cohomology of
`E` is supported on `T ⊆ Y` then the cohomology of `j^*E` is supported on `j⁻¹T`, for any open
immersion `j : X ⟶ Y` of schemes.

The stalk of the `n`-th cohomology sheaf of `j^*E` at `x` is the stalk of the `n`-th cohomology
sheaf of `E` at `j(x)`, which is
`Stacks.Duality.OpenImmersion.stalkRestrictHomologyIso`; there is nothing else to the
statement. -/
theorem cohomologySupportedOn_derivedRestrict {X Y : Scheme.{u}} (j : X ⟶ Y) [IsOpenImmersion j]
    (T : Set Y) (E : DerivedCategory Y.Modules)
    (hE : Stacks.Cohomology.PushforwardRestriction.CohomologySupportedOn Y.ringCatSheaf T E) :
    Stacks.Cohomology.PushforwardRestriction.CohomologySupportedOn X.ringCatSheaf
      (j.base ⁻¹' T) ((Stacks.Duality.OpenImmersion.derivedRestrict j).obj E) :=
  fun n x hx => (hE n (j.base x) hx).of_iso
    (Stacks.Duality.OpenImmersion.stalkRestrictHomologyIso j n E x)

/-- **Restriction along an open immersion carries `D_{QCoh,T}(𝒪_Y)` into
`D_{QCoh,j⁻¹T}(𝒪_X)`.** Quasi-coherence of the cohomology sheaves is preserved by
`Stacks.Duality.OpenImmersion.derivedCategoryB_derivedRestrict` and the support condition by
`Stacks.Rouquier.cohomologySupportedOn_derivedRestrict`, read through the two bridges between the
spellings of support of
`StacksFrontier/AlgebraicGeometry/Rouquier/AffineSupportedGenerator.lean`. -/
theorem quasiCoherentSupported_derivedRestrict {X Y : Scheme.{u}} (j : X ⟶ Y)
    [IsOpenImmersion j] (T : Set Y) (E : DerivedCategory Y.Modules)
    (hE : Stacks.Duality.quasiCoherentSupported Y T E) :
    Stacks.Duality.quasiCoherentSupported X (j.base ⁻¹' T)
      ((Scheme.Modules.restrictFunctor j).mapDerivedCategory.obj E) :=
  ⟨Stacks.Duality.OpenImmersion.derivedCategoryB_derivedRestrict j E hE.1,
    derivedSupported_of_cohomologySupportedOn _ _ _
      (cohomologySupportedOn_derivedRestrict j T E
        (cohomologySupportedOn_of_derivedSupported _ _ _ hE.2))⟩

/-! ### Detection of the zero object along an isomorphism of schemes -/

/-- **Detection of the zero object of a full subcategory travels along an isomorphism of
schemes.** Let `e : Y ≅ Z`, let `B ⊆ D(𝒪_Z)` and let `K` be an object of `D(𝒪_Z)` detecting the
zero object of `B`, in the sense that an object of `B` receiving only zero maps from the shifts of
`K` is zero. Then `K|_Y` detects the zero object among those `M` of `D(𝒪_Y)` whose restriction
along `e.inv` lies in `B`.

Restriction along `e.hom` is faithful and commutes with the shift, so it reflects the vanishing of
the morphisms out of all shifts of an object
(`Stacks.DerivedQCoh.AnyModel.forall_hom_shift_eq_zero_of_faithful`), and it reflects the zero
object (`Stacks.DerivedQCoh.AnyModel.isZero_of_isZero_derivedRestrict_of_compEqId`); both because
restricting along `e.inv` and then along `e.hom` is the identity. -/
theorem isZero_of_forall_hom_derivedRestrict_of_iso {Y Z : Scheme.{u}} (e : Y ≅ Z)
    (B : ObjectProperty (DerivedCategory Z.Modules)) (K : DerivedCategory Z.Modules)
    (hdet : ∀ N : DerivedCategory Z.Modules, B N →
      (∀ (n : ℤ) (g : K⟦n⟧ ⟶ N), g = 0) → IsZero N)
    (M : DerivedCategory Y.Modules)
    (hM : B ((Scheme.Modules.restrictFunctor e.inv).mapDerivedCategory.obj M))
    (h : ∀ (n : ℤ)
      (g : ((Scheme.Modules.restrictFunctor e.hom).mapDerivedCategory.obj K)⟦n⟧ ⟶ M), g = 0) :
    IsZero M := by
  let := faithful_derivedRestrict_of_compEqId e.inv e.hom e.inv_hom_id
  refine isZero_of_isZero_derivedRestrict_of_compEqId e.hom e.inv e.hom_inv_id
    (hdet _ hM ?_)
  exact forall_hom_shift_eq_zero_of_faithful
    (Scheme.Modules.restrictFunctor e.hom).mapDerivedCategory
    ((derivedRestrictCompIsoId e.hom e.inv e.hom_inv_id).app M) h

/-! ### The base case of [Stacks, Tag 0A9A] at a scheme isomorphic to a spectrum -/

/-- The two preimages along an isomorphism of schemes undo each other. -/
theorem preimage_hom_preimage_inv {Y Z : Scheme.{u}} (e : Y ≅ Z) (T : Set Y) :
    e.hom.base ⁻¹' (e.inv.base ⁻¹' T) = T := by
  ext y
  show e.inv.base (e.hom.base y) ∈ T ↔ y ∈ T
  show (e.hom ≫ e.inv).base y ∈ T ↔ y ∈ T
  rw [e.hom_inv_id]
  rfl

/-- **The base case of [Stacks, Tag 0A9A] at a scheme presented by an isomorphism with a
spectrum.** Let `e : Y ≅ Spec A` and let `T ⊆ Y` be closed with quasi-compact complement. There is
an object of `D(𝒪_Y)` which lies in `D_{QCoh,T}(𝒪_Y)`, is perfect, and detects the zero object of
`D_{QCoh,T}(𝒪_Y)`.

It is the Koszul object of a sequence cutting `e.inv⁻¹T` out of `Spec A`, read on `Y` along
`e.hom`: perfect by `Stacks.Koszul.TwoOpens.isPerfect_derivedRestrict_koszulObject`, supported and
quasi-coherent by `Stacks.Rouquier.quasiCoherentSupported_derivedRestrict` applied to
`Stacks.Rouquier.quasiCoherentSupported_koszulObject`, and detecting by
`Stacks.Rouquier.isZero_of_forall_hom_derivedRestrict_of_iso` applied to
`Stacks.Rouquier.isZero_of_subsingleton_hom_koszulObject`. -/
theorem exists_isPerfect_generator_supported_of_iso_spec {Y : Scheme.{u}} {A : Type u}
    [CommRing A] (e : Y ≅ Spec (CommRingCat.of A)) (T : Set Y) (hT : IsClosed T)
    (hTc : IsCompact Tᶜ) :
    ∃ G : DerivedCategory Y.Modules,
      Stacks.Duality.quasiCoherentSupported Y T G ∧
        IsPerfect (X := Y.toRingedSpace) G ∧
        ∀ E : DerivedCategory Y.Modules, Stacks.Duality.quasiCoherentSupported Y T E →
          (∀ n : ℤ, Subsingleton (G⟦n⟧ ⟶ E)) → IsZero E := by
  have hT' : IsClosed (e.inv.base ⁻¹' T) := hT.preimage e.inv.continuous
  have hT'c : IsCompact (e.inv.base ⁻¹' T)ᶜ := by
    rw [← Set.preimage_compl]
    exact (Scheme.homeoOfIso e.symm).isCompact_preimage.mpr hTc
  obtain ⟨r, f, hfT⟩ := exists_openComplement_eq_compl (e.inv.base ⁻¹' T) hT' hT'c
  have hG : Stacks.Duality.quasiCoherentSupported Y (e.hom.base ⁻¹' (e.inv.base ⁻¹' T))
      ((Scheme.Modules.restrictFunctor e.hom).mapDerivedCategory.obj (koszulObject f)) :=
    quasiCoherentSupported_derivedRestrict e.hom _ _
      (quasiCoherentSupported_koszulObject f _ hfT)
  rw [preimage_hom_preimage_inv] at hG
  refine ⟨_, hG, Stacks.Koszul.TwoOpens.isPerfect_derivedRestrict_koszulObject f e.hom, ?_⟩
  intro E hE horth
  refine isZero_of_forall_hom_derivedRestrict_of_iso e _ (koszulObject f) ?_ E
    (quasiCoherentSupported_derivedRestrict e.inv T E hE) fun n g => (horth n).allEq g 0
  intro N hN hn
  exact isZero_of_subsingleton_hom_koszulObject f _ hfT N hN
    fun n => subsingleton_of_forall_eq 0 (hn n)

/-- **The base case of [Stacks, Tag 0A9A] at a scheme presented by an isomorphism with a
spectrum, read inside `D_{QCoh,T}(𝒪_Y)`.** The generator produced by
`Stacks.Rouquier.exists_isPerfect_generator_supported_of_iso_spec` is a weak triangulated
generator of the subcategory, in the `CategoryTheory.ObjectProperty.singleton` spelling that the
inductive step of [Stacks, Tag 09IS] consumes.

The identification of generation inside the full subcategory with generation read in `D(𝒪_Y)` is
`CategoryTheory.ObjectProperty.isWeakTriangulatedGenerator_singleton_iff`. -/
theorem exists_isPerfect_isWeakTriangulatedGenerator_supported_of_iso_spec {Y : Scheme.{u}}
    {A : Type u} [CommRing A] (e : Y ≅ Spec (CommRingCat.of A)) (T : Set Y) (hT : IsClosed T)
    (hTc : IsCompact Tᶜ) :
    ∃ G : Stacks.Duality.QuasiCoherentSupportedDerivedCategory Y T,
      IsPerfect (X := Y.toRingedSpace) G.obj ∧
        (ObjectProperty.singleton G).IsWeakTriangulatedGenerator := by
  obtain ⟨G, hGmem, hGperf, hGdet⟩ := exists_isPerfect_generator_supported_of_iso_spec e T hT hTc
  refine ⟨⟨G, hGmem⟩, hGperf, ?_⟩
  refine (@ObjectProperty.isWeakTriangulatedGenerator_singleton_iff _ _ _ _
    (Stacks.Duality.quasiCoherentSupported Y T)
    (Stacks.Duality.Supported.quasiCoherentSupported_isTriangulated Y T).toIsStableUnderShift
    ⟨G, hGmem⟩).2 ?_
  intro E hE hzero
  exact hGdet E hE fun n => ⟨fun g h => (hzero n g).trans (hzero n h).symm⟩

end Stacks.Rouquier

end
