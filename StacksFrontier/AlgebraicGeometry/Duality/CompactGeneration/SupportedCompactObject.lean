module

public import StacksFrontier.AlgebraicGeometry.DerivedQCoh.StructureSheafSpelling
public import StacksFrontier.AlgebraicGeometry.Duality.CompactGeneration.PerfectIsCompact
public import StacksFrontier.AlgebraicGeometry.Duality.CompactGeneration.SupportedDirectSums
public import StacksFrontier.AlgebraicGeometry.Perfect.BoundedLocallyFreeComplexes.SaturationFromRetractModels
public import StacksFrontier.AlgebraicGeometry.Rouquier.SupportedGeneratorQcqs
public import StacksFrontier.CategoryTheory.Triangulated.CompactObjects
public import StacksFrontier.Topology.Sheaves.Cohomology.PerfectComplexes.PseudoCoherentAndFiniteTorDimension
public import StacksFrontier.Topology.Sheaves.Cohomology.PerfectComplexes.TriangulatedSubcategory
public import StacksCore.Tactic.StacksAttribute

/-!
# Compact objects of the derived category with support

Let `X` be a quasi-compact quasi-separated scheme and `T ⊆ X` a closed subset with quasi-compact
complement. An object of `D_{QCoh,T}(𝒪_X)` — the complexes of `𝒪_X`-modules whose cohomology
sheaves are quasi-coherent and supported on `T` — is a compact object of that category exactly
when it is perfect as an object of `D(𝒪_X)`. The forward implication holds for any closed `T`
once `X` is quasi-compact and quasi-separated; the converse holds for an arbitrary scheme and an
arbitrary subset once a perfect generator of `D_{QCoh,T}(𝒪_X)` is given.

## Main results

* `Stacks.Duality.Supported.isCompactObject_of_isCompactObject_toQuasiCoherent`: an object of
  `D_{QCoh,T}(𝒪_X)` which is compact in `D_QCoh(𝒪_X)` is compact in `D_{QCoh,T}(𝒪_X)`.
* `Stacks.Duality.Supported.isCompactObject_of_isPerfect`: a perfect object of
  `D_{QCoh,T}(𝒪_X)` is compact, for `X` quasi-compact and quasi-separated.
* `Stacks.Duality.Supported.isPerfect_of_isCompactObject`: a compact object of
  `D_{QCoh,T}(𝒪_X)` is perfect, given a perfect generator of that category.
* `Stacks.Duality.Supported.isCompactObject_iff_isPerfect`: the two conditions agree, for `X`
  quasi-compact and quasi-separated and `T` closed with quasi-compact complement.

## Implementation notes

*The universe.* Compactness is read against families indexed by `Type u`, the Grothendieck
universe of the `𝒪_X`-modules, and the generator criterion
`isWeakTriangulatedGenerator_iff_triangEnvelope_eq_isCompactObject_and_isCompactlyGenerated`
reads it against families indexed by the hom universe of the category. The derived category is
therefore taken at a model whose morphisms lie in `Type u`; in the two directional statements it
is a binder, so that `SheafOfModules.hasDerivedCategory` and any other such model both
instantiate it. `isCompactObject_iff_isPerfect` is stated at the locally small model, where the
perfect generator of `D_{QCoh,T}(𝒪_X)` is available.

*The two spellings of the `𝒪_X`-modules.* `D_{QCoh,T}(𝒪_X)` is a full subcategory of the derived
category of `AlgebraicGeometry.SheafOfModules X.ringCatSheaf`, whereas perfectness is stated for
`StrictlyPerfect.OXMod X.toRingedSpace`. The two are the same type with the same instances
(`Stacks.DerivedQCoh.oxMod_eq_sheafOfModules` is `rfl`) but instance search does not cross
between them, so the chosen derived category is moved across as a term by
`Stacks.DerivedQCoh.hasDerivedCategoryOxMod` and seated as a local instance, scoped to the section
carrying the binder.

## References

* [The Stacks Project, Lemma 36.17.3 (0A9B)](https://stacks.math.columbia.edu/tag/0A9B)
* [The Stacks Project, Proposition 36.17.1 (09M1)](https://stacks.math.columbia.edu/tag/09M1)
* [The Stacks Project, Lemma 36.15.4 (0A9A)](https://stacks.math.columbia.edu/tag/0A9A)
* [The Stacks Project, Lemma 20.49.9 (08CS)](https://stacks.math.columbia.edu/tag/08CS)
-/

-- This file uses the locally small derived-category models below, which are not
-- global instances (see `StacksFrontier.Homology.DerivedCategory.LocallySmall`):
-- `D(R)` for sheaves of modules on a small site.
attribute [local instance] SheafOfModules.hasDerivedCategory

@[expose] public noncomputable section

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits CategoryTheory.ObjectProperty
open Stacks.Cohomology.PerfectComplexes

universe u

namespace Stacks.Duality.Supported

section AnyModel

variable (X : Scheme.{u}) (T : Set X)
  [h : HasDerivedCategory.{u} (SheafOfModules.{u} X.ringCatSheaf)]

/-- The chosen derived category of `SheafOfModules X.ringCatSheaf`, read at the spelling
`StrictlyPerfect.OXMod X.toRingedSpace` in which perfectness is stated. -/
local instance hasDerivedCategoryOxMod : HasDerivedCategory.{u}
    (StrictlyPerfect.OXMod.{u, u} X.toRingedSpace) :=
  Stacks.DerivedQCoh.hasDerivedCategoryOxMod X h

/-! ### Compactness passes from `D_QCoh(𝒪_X)` to `D_{QCoh,T}(𝒪_X)` -/

/-- The inclusion of `D_{QCoh,T}(𝒪_X)` into `D_QCoh(𝒪_X)`: a complex whose cohomology sheaves
are quasi-coherent and supported on `T` has in particular quasi-coherent cohomology sheaves. -/
def toQuasiCoherent : QuasiCoherentSupportedDerivedCategory X T ⥤
    (derivedQuasiCoherent X).FullSubcategory :=
  ObjectProperty.ιOfLE (fun _ hK ↦ hK.1)

/-- The inclusion of `D_{QCoh,T}(𝒪_X)` into `D_QCoh(𝒪_X)` is a full functor. -/
instance : (toQuasiCoherent X T).Full :=
  inferInstanceAs (ObjectProperty.ιOfLE (fun _ hK ↦ hK.1)).Full

/-- The inclusion of `D_{QCoh,T}(𝒪_X)` into `D_QCoh(𝒪_X)` is a faithful functor. -/
instance : (toQuasiCoherent X T).Faithful :=
  inferInstanceAs (ObjectProperty.ιOfLE (fun _ hK ↦ hK.1)).Faithful

/-- The inclusion of `D_{QCoh,T}(𝒪_X)` into `D_QCoh(𝒪_X)`, composed with the inclusion of the
latter into `D(𝒪_X)`, is the inclusion of the former into `D(𝒪_X)`. -/
private def toQuasiCoherentCompι :
    toQuasiCoherent X T ⋙ (derivedQuasiCoherent X).ι ≅ (quasiCoherentSupported X T).ι :=
  ObjectProperty.ιOfLECompιIso (fun _ hK ↦ hK.1)

/-- **The direct sums of `D_{QCoh,T}(𝒪_X)` are the direct sums of `D_QCoh(𝒪_X)`**: the inclusion
of `D_{QCoh,T}(𝒪_X)` into `D_QCoh(𝒪_X)` preserves direct sums indexed by `Type u`. -/
instance preservesColimitsOfShape_toQuasiCoherent (I : Type u) :
    PreservesColimitsOfShape (Discrete I) (toQuasiCoherent X T) := by
  have := Stacks.SmallDerivedCategory.hasColimitsOfShape_discrete_derivedCategory
    (SheafOfModules.{u} X.ringCatSheaf) I
  have := quasiCoherentSupported_isClosedUnderCoproducts X T I
  have := derivedQuasiCoherent_isClosedUnderCoproducts X I
  have : PreservesColimitsOfShape (Discrete I)
      (toQuasiCoherent X T ⋙ (derivedQuasiCoherent X).ι) :=
    preservesColimitsOfShape_of_natIso (toQuasiCoherentCompι X T).symm
  exact preservesColimitsOfShape_of_reflects_of_preserves (toQuasiCoherent X T)
    (derivedQuasiCoherent X).ι

/-- The inclusion of `D_{QCoh,T}(𝒪_X)` into `D_QCoh(𝒪_X)` is an additive functor. -/
instance : (toQuasiCoherent X T).Additive :=
  have : (toQuasiCoherent X T ⋙ (derivedQuasiCoherent X).ι).Additive :=
    Functor.additive_of_iso (toQuasiCoherentCompι X T).symm
  Functor.additive_of_comp_faithful (toQuasiCoherent X T) (derivedQuasiCoherent X).ι

/-- **Compactness in `D_QCoh(𝒪_X)` implies compactness in `D_{QCoh,T}(𝒪_X)`.** -/
theorem isCompactObject_of_isCompactObject_toQuasiCoherent
    (K : QuasiCoherentSupportedDerivedCategory X T)
    (hK : IsCompactObject.{u} ((toQuasiCoherent X T).obj K)) : IsCompactObject.{u} K :=
  CategoryTheory.isCompactObject_of_fullyFaithful (toQuasiCoherent X T) K hK

/-! ### Perfectness, as a property of the supported category -/

/-- The property of being perfect, on the derived category at the spelling
`StrictlyPerfect.OXMod X.toRingedSpace`. -/
private abbrev isPerfectProperty :
    ObjectProperty (DerivedCategory (StrictlyPerfect.OXMod.{u, u} X.toRingedSpace)) :=
  fun K => IsPerfect (X := X.toRingedSpace) K

/-- **Perfectness is stable under retracts**: a direct summand of a perfect object of `D(𝒪_X)` is
perfect. -/
theorem isStableUnderRetracts_isPerfect :
    ObjectProperty.IsStableUnderRetracts
      (show ObjectProperty (DerivedCategory (StrictlyPerfect.OXMod.{u, u} X.toRingedSpace)) from
        fun K => IsPerfect (X := X.toRingedSpace) K) :=
  have : ObjectProperty.IsSaturated (isPerfectProperty X) :=
    Stacks.Perfect.BoundedLocallyFreeComplexes.isSaturated_isPerfect_of_biprod
      Stacks.Cohomology.TorAmplitude.isPerfect_of_biprod
  CategoryTheory.ObjectProperty.isStableUnderRetracts_of_isSaturated_of_isClosedUnderIsomorphisms _

/-! ### The two directions, at an arbitrary model and with the generator given -/

/-- **A perfect object of `D_{QCoh,T}(𝒪_X)` is compact**, for `X` quasi-compact and
quasi-separated. -/
theorem isCompactObject_of_isPerfect [CompactSpace X] [QuasiSeparatedSpace X]
    (K : QuasiCoherentSupportedDerivedCategory X T)
    (hK : IsPerfect (X := X.toRingedSpace) K.obj) : IsCompactObject.{u} K :=
  isCompactObject_of_isCompactObject_toQuasiCoherent X T K
    (_root_.AlgebraicGeometry.isCompactObject_of_isPerfect X ((toQuasiCoherent X T).obj K) hK)

/-- **A compact object of `D_{QCoh,T}(𝒪_X)` is perfect**, given a perfect generator `E` of that
category. -/
theorem isPerfect_of_isCompactObject
    (E : QuasiCoherentSupportedDerivedCategory X T)
    (hE : IsPerfect (X := X.toRingedSpace) E.obj)
    (hEcompact : IsCompactObject.{u} E)
    (hgen : (ObjectProperty.singleton E).IsWeakTriangulatedGenerator)
    (K : QuasiCoherentSupportedDerivedCategory X T) (hK : IsCompactObject.{u} K) :
    IsPerfect (X := X.toRingedSpace) K.obj := by
  have := hasCoproducts_quasiCoherentSupportedDerivedCategory X T
  have := hEcompact
  have hclassical : (ObjectProperty.singleton E).triangEnvelope =
      IsCompactObject.{u, _, _} (C := QuasiCoherentSupportedDerivedCategory X T) :=
    (isWeakTriangulatedGenerator_iff_triangEnvelope_eq_isCompactObject_and_isCompactlyGenerated
      E).mp hgen |>.1
  let P : ObjectProperty (DerivedCategory (SheafOfModules.{u} X.ringCatSheaf)) :=
    fun L ↦ IsPerfect (X := X.toRingedSpace) L
  have : P.IsClosedUnderIsomorphisms :=
    inferInstanceAs (ObjectProperty.IsClosedUnderIsomorphisms (isPerfectProperty X))
  have : P.IsTriangulated := inferInstanceAs (ObjectProperty.IsTriangulated (isPerfectProperty X))
  have : P.IsStableUnderRetracts := isStableUnderRetracts_isPerfect X
  let R : ObjectProperty (QuasiCoherentSupportedDerivedCategory X T) :=
    P.inverseImage (quasiCoherentSupported X T).ι
  have : R.IsStableUnderRetracts :=
    ⟨fun ret hL ↦ P.prop_of_retract (ret.map (quasiCoherentSupported X T).ι) hL⟩
  have hEnv : (ObjectProperty.singleton E).triangEnvelope ≤ R :=
    (ObjectProperty.triangEnvelope_le_iff _).2 fun _ hY => by
      obtain rfl := (ObjectProperty.singleton_iff _ _).1 hY
      exact hE
  exact hEnv K (hclassical ▸ hK)

end AnyModel

/-! ### The tag -/

section Tag

variable (X : Scheme.{u}) (T : Set X)

/-- **An object of `D_{QCoh,T}(𝒪_X)` is compact if and only if it is perfect as an object of
`D(𝒪_X)`**, for `X` quasi-compact and quasi-separated and `T` closed with quasi-compact
complement. The derived category is taken at the locally small model. -/
@[stacks 0A9B "compactness in `D_{QCoh,T}(𝒪_X)` is perfectness in `D(𝒪_X)`, with nothing \
carried. Both results the source cites are proved in this library and discharged in the proof: \
Tag 09M1, that a perfect object of `D_QCoh(𝒪_X)` is a compact object of it, as \
`AlgebraicGeometry.isCompactObject_of_isPerfect`, and Tag 0A9A, that `D_{QCoh,T}(𝒪_X)` is \
generated by a perfect object, as \
`Stacks.Rouquier.exists_isPerfect_isWeakTriangulatedGenerator_supported`. They are discharged at \
the cost of the source's own hypotheses that `X` be quasi-compact and quasi-separated and that \
`T` be closed with quasi-compact complement, which are Tag 0A9B's hypotheses too and are used \
for nothing else. The source's step (d), that a direct summand of a perfect object is perfect, \
is Tag 08CS and is proved in this library, so it is not a hypothesis. The derived category is \
the locally small model rather than a binder, Tag 0A9A being available at no other; the two \
directions at an arbitrary model are `Stacks.Duality.Supported.isCompactObject_of_isPerfect` \
and, with the generator given, `Stacks.Duality.Supported.isPerfect_of_isCompactObject`"]
theorem isCompactObject_iff_isPerfect [CompactSpace X] [QuasiSeparatedSpace X]
    (hT : IsClosed T) (hTc : IsCompact Tᶜ)
    (K : QuasiCoherentSupportedDerivedCategory X T) :
    IsCompactObject.{u} K ↔ IsPerfect (X := X.toRingedSpace) K.obj := by
  obtain ⟨E, hE, hgen⟩ :=
    Stacks.Rouquier.exists_isPerfect_isWeakTriangulatedGenerator_supported X T hT hTc
  exact ⟨isPerfect_of_isCompactObject X T E hE
      (isCompactObject_of_isPerfect X T E hE) hgen K,
    isCompactObject_of_isPerfect X T K⟩

end Tag

end Stacks.Duality.Supported

end
