module

public import StacksFrontier.AlgebraicGeometry.Duality.CompactGeneration.PerfectIsCompactCover
public import StacksFrontier.AlgebraicGeometry.Duality.CompactGeneration.QcqsPerfectGenerator
public import StacksFrontier.AlgebraicGeometry.Duality.CompactGeneration.SupportedDirectSums
public import StacksFrontier.AlgebraicGeometry.Perfect.PerfectApproximation.Comparison
public import StacksFrontier.CategoryTheory.Triangulated.NeemanThomason
public import StacksFrontier.Topology.Sheaves.Cohomology.PerfectComplexes.PseudoCoherentAndFiniteTorDimension
public import StacksFrontier.Topology.Sheaves.Cohomology.PerfectComplexes.TriangulatedSubcategory

/-!
# Compact and perfect objects of `D_{QCoh,T}(𝒪_X)`

[Stacks, Tag 0A9B] reads, for `X` a quasi-compact and quasi-separated scheme and `T ⊆ X` a closed
subset whose complement is quasi-compact:

> an object of `D_{QCoh,T}(𝒪_X)` is compact if and only if it is perfect as an object of
> `D(𝒪_X)`.

The source's proof has two halves, and this file is the two halves.

* **Perfect implies compact.** By [Stacks, Tag 09M1] a perfect object is compact in
  `D_QCoh(𝒪_X)` (`Stacks.Duality.PerfectCompact.isCompactObject_of_isPerfect`), "hence a fortiori
  of any subcategory preserved under taking direct sums": `D_{QCoh,T}(𝒪_X)` is a full subcategory
  of `D_QCoh(𝒪_X)` closed under the direct sums of `D(𝒪_X)`
  (`Stacks.Duality.Supported.quasiCoherentSupported_isClosedUnderCoproducts`), so compactness
  descends along the inclusion (`Stacks.Duality.Supported.isCompactObject_of_isCompactObject_obj`).
* **Compact implies perfect.** Let `E` be a perfect generator of `D_{QCoh,T}(𝒪_X)`
  ([Stacks, Tag 0A9A], `Stacks.Duality.SupportedGeneration.hasCompactSupportedGenerators` and
  `Stacks.Duality.SupportedGeneration.isPerfect_of_isCompactObject`); it is compact. Then
  [Stacks, Tag 09SR] says that the triangulated envelope of `E` is *exactly* the subcategory of
  compact objects, so every compact object is built from `E` by shifts, finite direct sums,
  cones and direct summands. Each of those preserves perfectness: the perfect objects form a
  triangulated subcategory of `D(𝒪_X)` ([Stacks, Tag 08CR],
  `Stacks.Cohomology.PerfectTriangulatedSubcategory.isTriangulated_isPerfect`) which is stable
  under retracts ([Stacks, Tag 08CS], `Stacks.Cohomology.TorAmplitude.isPerfect_of_biprod`
  together with the splitting of a retract in a pretriangulated category); so the preimage of
  perfectness along the inclusion of `D_{QCoh,T}(𝒪_X)` is a retract-closed triangulated
  subcategory containing `E`, and the minimality of the envelope finishes.

## Main results

* `Stacks.Duality.Supported.isPerfect_of_retract` — a retract, in `D(𝒪_X)`, of a perfect object
  is perfect. This is the thickness clause of [Stacks, Tag 08CS] in retract form.
* `Stacks.Duality.Supported.isCompactObject_of_isCompactObject_obj` — an object of
  `D_{QCoh,T}(𝒪_X)` compact in `D_QCoh(𝒪_X)` is compact in `D_{QCoh,T}(𝒪_X)`.
* `Stacks.Duality.Supported.isPerfect_of_isCompactObject_of_generator` — every compact object of
  `D_{QCoh,T}(𝒪_X)` is perfect once `D_{QCoh,T}(𝒪_X)` has a compact perfect generator.
* `Stacks.Duality.Supported.exists_isCompactObject_isPerfect_isWeakTriangulatedGenerator` — the
  generator of [Stacks, Tag 0A9A] as an object of `D_{QCoh,T}(𝒪_X)`, compact there.
* `Stacks.Duality.Supported.isCompactObject_iff_isPerfect_of_isClosed` — **[Stacks, Tag 0A9B]**.

## Implementation notes

**Generation is [Stacks, Tag 09SJ](3).** The generator hypothesis of
`isPerfect_of_isCompactObject_of_generator` is
`CategoryTheory.ObjectProperty.IsWeakTriangulatedGenerator` of the singleton class of `E`, read
in the category `D_{QCoh,T}(𝒪_X)`: every object of that category receiving only zero morphisms
from the integer shifts of `E` is zero. It is the hypothesis [Stacks, Tag 09SR] consumes.

**The derived category is the locally small one.** As in
`StacksFrontier/AlgebraicGeometry/Duality/CompactGeneration/SupportedDirectSums.lean`, every
statement is at `SheafOfModules.hasDerivedCategory`, the model of
`StacksFrontier/Homology/DerivedCategory/LocallySmall.lean`, whose morphisms lie in the universe
`u` of `𝒪_X`-modules. That is forced: compactness is tested against direct sums indexed by the
morphism universe, and with `CategoryTheory.HasDerivedCategory.standard` the direct sums of
`D_{QCoh,T}(𝒪_X)` would be indexed one universe below the morphisms and the statement would be
about a different notion of compactness.

**Two spellings of `D_QCoh(𝒪_X)`.** `Stacks.Duality.quasiCoherentDerivedCategory X`, at which
[Stacks, Tag 09M1] is proved, is a full subcategory of `D(X.Modules)`, while
`Stacks.Duality.derivedQuasiCoherent X`, of which `D_{QCoh,T}(𝒪_X)` is a subproperty, lives on
`D(SheafOfModules 𝒪_X)`. The two full subcategories are the same category by `rfl`, and the
statements below cross between them by unification.

**Perfectness is spelled twice in this development.** The predicate used in the statements is
`AlgebraicGeometry.RingedSpace.IsPerfect`; the triangulated and summand lemmas are stated for
`Stacks.Cohomology.PerfectComplexes.IsPerfect`. The two agree at coinciding universes, by
`Stacks.Cohomology.PerfectComplexes.isPerfect_iff_ringedSpace`.

## References

* [Stacks Project, Tag 0A9B](https://stacks.math.columbia.edu/tag/0A9B)
* [Stacks Project, Tag 0A9A](https://stacks.math.columbia.edu/tag/0A9A)
* [Stacks Project, Tag 09M1](https://stacks.math.columbia.edu/tag/09M1)
* [Stacks Project, Tag 09SR](https://stacks.math.columbia.edu/tag/09SR)
* [Stacks Project, Tag 09SJ](https://stacks.math.columbia.edu/tag/09SJ)
* [Stacks Project, Tag 08CR](https://stacks.math.columbia.edu/tag/08CR)
* [Stacks Project, Tag 08CS](https://stacks.math.columbia.edu/tag/08CS)
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
open CategoryTheory.Pretriangulated

universe u

namespace Stacks.Duality.Supported

/-! ### Retracts of perfect objects -/

/-- **A retract of a perfect object of `D(𝒪_X)` is perfect.** This is the thickness clause of
[Stacks, Tag 08CS], which that tag states for the two summands of a biproduct, in the retract
form that the minimality of a triangulated envelope consumes.

A retraction `i : A ⟶ B`, `r : B ⟶ A` makes `i⟦1⟧` a split monomorphism, so the third map of a
distinguished triangle on `i` is killed by it and vanishes; the triangle therefore splits
(`CategoryTheory.Pretriangulated.exists_iso_binaryBiproduct_of_distTriang`), identifying `B` with
`A ⊞ Z`, and [Stacks, Tag 08CS] makes `A` perfect. -/
theorem isPerfect_of_retract {X : AlgebraicGeometry.RingedSpace.{u, u}}
    [HasDerivedCategory.{u} (StrictlyPerfect.OXMod.{u, u, u} X)]
    {A B : DerivedCategory (StrictlyPerfect.OXMod.{u, u, u} X)} (ret : Retract A B)
    (hB : Stacks.Cohomology.PerfectComplexes.IsPerfect (X := X) B) :
    Stacks.Cohomology.PerfectComplexes.IsPerfect (X := X) A := by
  obtain ⟨Z, g, h, mem⟩ := distinguished_cocone_triangle ret.i
  have hi : IsSplitMono (ret.i⟦(1 : ℤ)⟧') :=
    ⟨⟨⟨ret.r⟦(1 : ℤ)⟧', by simp [← Functor.map_comp, ret.retract]⟩⟩⟩
  have h0 : h = 0 := by
    have h1 := comp_distTriang_mor_zero₃₁ _ mem
    simp only [Triangle.mk_mor₃, Triangle.mk_mor₁, Triangle.mk_obj₁] at h1
    exact (cancel_mono (ret.i⟦(1 : ℤ)⟧')).1 (by simpa using h1)
  obtain ⟨e, -, -⟩ := exists_iso_binaryBiproduct_of_distTriang _ mem h0
  exact (Stacks.Cohomology.TorAmplitude.isPerfect_of_biprod A Z
    (ObjectProperty.prop_of_iso
      (fun L : DerivedCategory (StrictlyPerfect.OXMod.{u, u, u} X) =>
        Stacks.Cohomology.PerfectComplexes.IsPerfect (X := X) L) e hB)).1

/-! ### Compactness in `D_QCoh(𝒪_X)` and in `D_{QCoh,T}(𝒪_X)` -/

section

variable (Z : Scheme.{u}) (T : Set Z)

/-- `D_{QCoh,T}(𝒪_Z)` is contained in `D_QCoh(𝒪_Z)`. -/
theorem quasiCoherentSupported_le_derivedQuasiCoherent :
    Stacks.Duality.quasiCoherentSupported Z T ≤ Stacks.Duality.derivedQuasiCoherent Z :=
  fun _ hK => hK.1

/-- **An object of `D_{QCoh,T}(𝒪_Z)` which is compact in `D_QCoh(𝒪_Z)` is compact in
`D_{QCoh,T}(𝒪_Z)`.** Both are full subcategories of `D(𝒪_Z)` closed under its direct sums
indexed by the morphism universe, so the inclusion `D_{QCoh,T}(𝒪_Z) ⥤ D_QCoh(𝒪_Z)` is fully
faithful and preserves those direct sums, and compactness descends along it
(`CategoryTheory.isCompactObject_of_fullyFaithful`). -/
theorem isCompactObject_of_isCompactObject_obj
    (K : Stacks.Duality.QuasiCoherentSupportedDerivedCategory Z T)
    (hK : IsCompactObject.{u}
      ((ιOfLE (quasiCoherentSupported_le_derivedQuasiCoherent Z T)).obj K)) :
    IsCompactObject.{u} K := by
  have _ : HasCoproducts.{u} (DerivedCategory (SheafOfModules.{u} Z.ringCatSheaf)) := fun J =>
    Stacks.SmallDerivedCategory.hasColimitsOfShape_discrete_derivedCategory _ J
  have _ : ∀ J : Type u,
      (Stacks.Duality.quasiCoherentSupported Z T).IsClosedUnderColimitsOfShape (Discrete J) :=
    quasiCoherentSupported_isClosedUnderCoproducts Z T
  have _ : ∀ J : Type u,
      (Stacks.Duality.derivedQuasiCoherent Z).IsClosedUnderColimitsOfShape (Discrete J) :=
    derivedQuasiCoherent_isClosedUnderCoproducts Z
  let h := quasiCoherentSupported_le_derivedQuasiCoherent Z T
  have _ : (ιOfLE h ⋙ (Stacks.Duality.derivedQuasiCoherent Z).ι).Additive :=
    inferInstanceAs (Stacks.Duality.quasiCoherentSupported Z T).ι.Additive
  have _ : (ιOfLE h).Additive :=
    Functor.additive_of_comp_faithful (ιOfLE h) (Stacks.Duality.derivedQuasiCoherent Z).ι
  have _ : ∀ J : Type u, PreservesColimitsOfShape (Discrete J) (ιOfLE h) := fun J =>
    have : PreservesColimitsOfShape (Discrete J)
        (ιOfLE h ⋙ (Stacks.Duality.derivedQuasiCoherent Z).ι) :=
      inferInstanceAs (PreservesColimitsOfShape (Discrete J)
        (Stacks.Duality.quasiCoherentSupported Z T).ι)
    preservesColimitsOfShape_of_reflects_of_preserves (ιOfLE h)
      (Stacks.Duality.derivedQuasiCoherent Z).ι
  exact isCompactObject_of_fullyFaithful (ιOfLE h) K hK

end

/-! ### Compact objects are perfect, given a perfect compact generator -/

section

variable (Z : Scheme.{u}) (T : Set Z)

/-- **Every compact object of `D_{QCoh,T}(𝒪_Z)` is perfect, once `D_{QCoh,T}(𝒪_Z)` has a
compact generator `E` which is perfect as an object of `D(𝒪_Z)`.**

By [Stacks, Tag 09SR] the triangulated envelope of `E` is exactly the subcategory of compact
objects: "any compact object can be constructed out of `E` by a finite sequence of operations
consisting of (a) taking shifts, (b) taking finite direct sums, (c) taking cones, and (d) taking
direct summands". Perfectness survives all four, being a triangulated ([Stacks, Tag 08CR]) and
retract-closed ([Stacks, Tag 08CS], `Stacks.Duality.Supported.isPerfect_of_retract`) property of
objects of `D(𝒪_Z)`; so its preimage along the full inclusion of `D_{QCoh,T}(𝒪_Z)` is a
retract-closed triangulated subcategory containing `E`, which by `triangEnvelope_le_iff` contains
the whole envelope. -/
theorem isPerfect_of_isCompactObject_of_generator
    (E : Stacks.Duality.QuasiCoherentSupportedDerivedCategory Z T)
    (hEperf : AlgebraicGeometry.RingedSpace.IsPerfect (X := Z.toRingedSpace) E.obj)
    (hEgen : (ObjectProperty.singleton E).IsWeakTriangulatedGenerator)
    (hEcompact : IsCompactObject.{u} E)
    (K : Stacks.Duality.QuasiCoherentSupportedDerivedCategory Z T)
    (hK : IsCompactObject.{u} K) :
    AlgebraicGeometry.RingedSpace.IsPerfect (X := Z.toRingedSpace) K.obj := by
  have _ : HasCoproducts.{u} (Stacks.Duality.QuasiCoherentSupportedDerivedCategory Z T) :=
    hasCoproducts_quasiCoherentSupportedDerivedCategory Z T
  -- [Stacks, Tag 09SR]: the envelope of `E` is the subcategory of compact objects.
  have henv : (ObjectProperty.singleton E).triangEnvelope =
      IsCompactObject.{u, _, _}
        (C := Stacks.Duality.QuasiCoherentSupportedDerivedCategory Z T) :=
    ((isWeakTriangulatedGenerator_iff_triangEnvelope_eq_isCompactObject_and_isCompactlyGenerated
      E).1 hEgen).1
  -- Perfectness is a retract-closed triangulated property of objects of `D(𝒪_Z)`. The two
  -- spellings `OXMod Z.toRingedSpace` and `SheafOfModules Z.ringCatSheaf` of the modules are the
  -- same by `rfl`, but instance search does not unfold between them, so the three instances are
  -- transported here by an explicit ascription.
  -- Perfectness is a retract-closed triangulated property of objects of `D(𝒪_Z)`. The two
  -- spellings `OXMod Z.toRingedSpace` and `SheafOfModules Z.ringCatSheaf` of the modules are the
  -- same by `rfl`, but instance search does not unfold between them, so the three instances are
  -- transported here by an explicit ascription.
  let P : ObjectProperty (DerivedCategory (SheafOfModules.{u} Z.ringCatSheaf)) := fun L =>
    Stacks.Cohomology.PerfectComplexes.IsPerfect (X := Z.toRingedSpace) L
  have _ : P.IsClosedUnderIsomorphisms :=
    Stacks.Cohomology.PerfectComplexes.isClosedUnderIsomorphisms_isPerfect
  have _ : P.IsTriangulated :=
    Stacks.Cohomology.PerfectTriangulatedSubcategory.isTriangulated_isPerfect Z.toRingedSpace
  have _ : P.IsStableUnderRetracts := ⟨fun ret hB => isPerfect_of_retract ret hB⟩
  have _ := P.inverseImage_isStableUnderRetracts (Stacks.Duality.quasiCoherentSupported Z T).ι
  have hle : (ObjectProperty.singleton E).triangEnvelope ≤
      P.inverseImage (Stacks.Duality.quasiCoherentSupported Z T).ι := by
    rw [ObjectProperty.triangEnvelope_le_iff, ObjectProperty.singleton_le_iff]
    exact (Stacks.Cohomology.PerfectComplexes.isPerfect_iff_ringedSpace E.obj).2 hEperf
  exact (Stacks.Cohomology.PerfectComplexes.isPerfect_iff_ringedSpace K.obj).1
    (hle K (by rwa [henv]))

end

/-! ### [Stacks, Tag 0A9B] -/

section

variable (X : Scheme.{u}) [CompactSpace X] [QuasiSeparatedSpace X] (T : Set X)

/-- **The compact generator of `D_{QCoh,T}(𝒪_X)`, as an object of `D_{QCoh,T}(𝒪_X)`.** For `X`
quasi-compact and quasi-separated and `T ⊆ X` closed with quasi-compact complement,
`D_{QCoh,T}(𝒪_X)` has an object which is compact there, perfect as an object of `D(𝒪_X)`, and a
generator in the sense of [Stacks, Tag 09SJ](3). This is [Stacks, Tag 0A9A], in the form
[Stacks, Tag 09SR] consumes: the generator of
`Stacks.Duality.SupportedGeneration.hasCompactSupportedGenerators`, which is perfect by
`Stacks.Duality.SupportedGeneration.isPerfect_of_isCompactObject`. -/
theorem exists_isCompactObject_isPerfect_isWeakTriangulatedGenerator (hT : IsClosed T)
    (hTc : IsCompact Tᶜ) :
    ∃ E : Stacks.Duality.QuasiCoherentSupportedDerivedCategory X T,
      IsCompactObject.{u} E ∧
        AlgebraicGeometry.RingedSpace.IsPerfect (X := X.toRingedSpace) E.obj ∧
        (ObjectProperty.singleton E).IsWeakTriangulatedGenerator := by
  obtain ⟨G, hGc, hGT, hGgen⟩ :=
    Stacks.Duality.SupportedGeneration.hasCompactSupportedGenerators X T hT hTc
  let E : Stacks.Duality.QuasiCoherentSupportedDerivedCategory X T := ⟨G.obj, G.2, hGT⟩
  refine ⟨E, isCompactObject_of_isCompactObject_obj X T E hGc,
    Stacks.Duality.SupportedGeneration.isPerfect_of_isCompactObject X G hGc, ?_⟩
  rw [isWeakTriangulatedGenerator_iff]
  intro K hK
  by_contra h
  push Not at h
  -- a morphism `E⟦n⟧ ⟶ K` vanishes once its transpose `E ⟶ K⟦-n⟧` does
  have hEK : ∀ (n : ℤ) (g : E⟦n⟧ ⟶ K), g = 0 := fun n g => by
    have hf := h E (by simp) (-n)
      ((shiftFunctorCompIsoId _ n (-n) (add_neg_cancel n)).inv.app E ≫ g⟦-n⟧')
    rw [Preadditive.IsIso.comp_left_eq_zero] at hf
    exact (shiftFunctor _ (-n)).map_injective (by rw [hf, Functor.map_zero])
  let K' : Stacks.Duality.quasiCoherentDerivedCategory X := ⟨K.obj, K.2.1⟩
  have hK' : IsZero K' := hGgen K' K.2.2
    ((Stacks.Duality.QcqsGeneration.forall_hom_shift_eq_zero_iff _ G K').2
      ((Stacks.Duality.QcqsGeneration.forall_hom_shift_eq_zero_iff _ E K).1 hEK))
  exact hK (isZero_fullSubcategory_of_isZero_obj ((DerivedCategoryB.derivedCategoryB
    (A := X.Modules) (SheafOfModules.isQuasicoherent X.ringCatSheaf)).ι.map_isZero hK'))

/-- **[Stacks, Tag 0A9B].** Let `X` be a quasi-compact and quasi-separated scheme and let
`T ⊆ X` be a closed subset such that `X ∖ T` is quasi-compact. An object of `D_{QCoh,T}(𝒪_X)` is
compact (in `D_{QCoh,T}(𝒪_X)`) if and only if it is perfect as an object of `D(𝒪_X)`.

Perfect objects are compact in `D_QCoh(𝒪_X)` by [Stacks, Tag 09M1]
(`Stacks.Duality.PerfectCompact.isCompactObject_of_isPerfect`), hence in the full subcategory
`D_{QCoh,T}(𝒪_X)`, which is closed under direct sums
(`Stacks.Duality.Supported.isCompactObject_of_isCompactObject_obj`). Conversely
`D_{QCoh,T}(𝒪_X)` has a compact perfect generator ([Stacks, Tag 0A9A],
`Stacks.Duality.Supported.exists_isCompactObject_isPerfect_isWeakTriangulatedGenerator`), so
every compact object is built from it by shifts, cones, finite direct sums and summands
([Stacks, Tag 09SR]), and is perfect
(`Stacks.Duality.Supported.isPerfect_of_isCompactObject_of_generator`). -/
@[stacks 0A9B]
theorem isCompactObject_iff_isPerfect_of_isClosed (hT : IsClosed T) (hTc : IsCompact Tᶜ)
    (K : Stacks.Duality.QuasiCoherentSupportedDerivedCategory X T) :
    IsCompactObject.{u} K ↔
      AlgebraicGeometry.RingedSpace.IsPerfect (X := X.toRingedSpace) K.obj := by
  refine ⟨fun hK => ?_, fun hK => isCompactObject_of_isCompactObject_obj X T K
    (Stacks.Duality.PerfectCompact.isCompactObject_of_isPerfect X ⟨K.obj, K.2.1⟩ hK)⟩
  obtain ⟨E, hEc, hEperf, hEgen⟩ :=
    exists_isCompactObject_isPerfect_isWeakTriangulatedGenerator X T hT hTc
  exact isPerfect_of_isCompactObject_of_generator X T E hEperf hEgen hEc K hK

end

end Stacks.Duality.Supported

end
