module

public import StacksFrontier.CategoryTheory.Sites.Cohomology.KFlat.ResolutionsOnARingedSite
public import StacksFrontier.CategoryTheory.Sites.Cohomology.DerivedTensor.KFlatResolutionInstances
public import StacksFrontier.Homology.KFlat.BifunctorLocalization
public import StacksFrontier.CategoryTheory.Sites.Modules.FlatTensorShortExact
import StacksCore.Tactic.StacksAttribute

/-!
# Left K-flat resolutions on a ringed site

Every complex of `O`-modules admits a quasi-isomorphism from a complex which is K-flat for
the *flipped* tensor bifunctor, equivalently left K-flat in the sense of
`CochainComplex.KFlatBifunctor.KFlatLeft`. This is the mirror of Tag 06YS, and it is what
makes the left-hand localization of `Tag06YUPieces` unconditional for `⊗_O`.

## Main results

* `Stacks.DerivedTensor.RingedSite.kFlatFlip_single_of_isFlat`: a flat module in a single degree is
  K-flat for
  the flipped bifunctor.
* `Stacks.DerivedTensor.RingedSite.exists_kFlatFlipResolution`: every complex admits a
  quasi-isomorphism from a
  complex which is K-flat for the flipped bifunctor.
* `Stacks.DerivedTensor.RingedSite.exists_kFlatLeft_quasiIso`: the same, phrased with `KFlatLeft`,
  which is the
  hypothesis `CochainComplex.KFlatBifunctor.kFlatQLeft_isLocalization` takes.
* `Stacks.DerivedTensor.RingedSite.kFlatQLeft_isLocalization`: so `D(Mod(O))` is also the
  localization of the
  *left* K-flat complexes. With `Stacks.DerivedTensor.RingedSite.kFlatQ_isLocalization` both
    localizations
  that `Localization.lift₂` consumes now hold unconditionally for the ringed-site tensor.

The `CategoryTheory.LocalizerMorphism.HasLeftResolutions` instance for the left K-flat complexes,
`Stacks.DerivedTensor.RingedSite.kFlatLocalizerLeft_hasLeftResolutions`, is stated with the site's
universes free, in
`StacksFrontier.CategoryTheory.Sites.Cohomology.DerivedTensor.KFlatResolutionInstances`. From it
`CochainComplex.KFlatBifunctor.kFlatQLeft_isLocalization_of_hasLeftResolutions` gives the
localization above by instance search.

## Implementation notes

The two K-flatness statements are **not** identified with one another. `KFlatLeft F` is
`KFlat F.flip`, a condition on a *different* bifunctor, and nothing here claims
`KFlatLeft F ↔ KFlat F` for the symmetric `⊗_O`; each side is established separately by running
the bifunctor-generic engine of `StacksTag06YQ` twice, once at
`Stacks.SheafOfModules.Tensor.sheafTensor.{u, u, u, u, u} R` (Tag 06YS) and once at its flip
(here). Both runs start from the one ladder of
`DerivedTensor.ResolutionByExtensionsByZero.exists_resolutionByDirectSumsExtensionsByZero`, so the
same complex in fact satisfies both — but that is a property of the construction, not a symmetry
argument, and it is not asserted as an identification of the two predicates.

Of the engine's three sheaf-specific inputs, two are already available at the flip:
`SheafOfModules.preservesColimitsOfSize_sheafTensor_flip_obj` is an instance, and the
sequential-colimit exactness input does not mention the bifunctor at all. The third, the
base case, is the one place the symmetry of `⊗_O` enters, and it enters at the level of
*modules* rather than of complexes:
  `Stacks.SheafOfModules.FlatTensorShortExact.preservesFiniteLimits_sheafTensor_obj_of_isFlat`
is 03EU's flatness criterion transported along
  `Stacks.SheafOfModules.FlatTensorShortExact.flipIso`. No braiding of total
complexes is needed anywhere.

## References

* [Stacks Project, Tag 06YS](https://stacks.math.columbia.edu/tag/06YS)
* [Stacks Project, Tag 06YU](https://stacks.math.columbia.edu/tag/06YU)
-/

@[expose] public section

universe u d

open CategoryTheory CategoryTheory.Limits

namespace Stacks.DerivedTensor.RingedSite

variable {C : Type u} [SmallCategory.{u} C] {J : GrothendieckTopology C}
  [HasWeakSheafify J AddCommGrpCat.{u}] [J.WEqualsLocallyBijective AddCommGrpCat.{u}]
  (R : Sheaf J CommRingCat.{u})

/-- `X ⊗_O -` and `- ⊗_O X` both commute with sequential colimits, `Mod(O)` being monoidal
closed. These are the hypothesis `hF` of 06YQ's criteria read at `⊗_O` and at its flip. -/
private lemma hF_sheafTensor_flip :
    ∀ X : SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf.{u, u, u} R),
      PreservesColimitsOfShape ℕ
        ((Stacks.SheafOfModules.Tensor.sheafTensor.{u, u, u, u, u} R).flip.obj X) :=
  fun _ ↦ ⟨fun {_} ↦ inferInstance⟩

variable [(Stacks.SheafOfModules.Tensor.sheafTensor.{u, u, u, u, u} R).Additive]
  [∀ M, ((Stacks.SheafOfModules.Tensor.sheafTensor.{u, u, u, u, u} R).obj M).Additive]

variable [∀ (K₁ K₂ : CochainComplex
      (SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf.{u, u, u} R)) ℤ),
    HomologicalComplex.HasMapBifunctor K₁ K₂
      (Stacks.SheafOfModules.Tensor.sheafTensor.{u, u, u, u, u} R)
      (ComplexShape.up ℤ)]

/-- **A flat module placed in a single degree is K-flat for the flipped tensor bifunctor.**
The base case of the left-hand run of 06YQ's engine. Its hypothesis is that `M ⊗_O ·` carries
acyclic complexes to acyclic ones, and for flat `M` that functor is exact — by 03EU's
criterion transported along the module-level symmetry
  `Stacks.SheafOfModules.FlatTensorShortExact.flipIso`. -/
theorem kFlatFlip_single_of_isFlat
    (M : SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf.{u, u, u} R))
    (hM : AlgebraicGeometry.SheafOfModules.IsFlat.{u, u, u, u} (O := R) M) (q : ℤ) :
    CochainComplex.KFlatBifunctor.KFlat
      (Stacks.SheafOfModules.Tensor.sheafTensor.{u, u, u, u, u} R).flip
      ((HomologicalComplex.single _ (ComplexShape.up ℤ) q).obj M) := by
  have hlim :=
    Stacks.SheafOfModules.FlatTensorShortExact.preservesFiniteLimits_sheafTensor_obj_of_isFlat R M
      hM
  refine CochainComplex.KFlatBifunctor.kFlat_single_of_exact _ M q (fun G hG ↦ ?_)
  exact HomologicalComplex.Acyclic.map
    ((Stacks.SheafOfModules.Tensor.sheafTensor.{u, u, u, u, u} R).obj M) hG

/-- **Every complex of `O`-modules admits a quasi-isomorphism from a complex which is K-flat
for the flipped tensor bifunctor.** This is 06YS's colimit assembly — the same ladder of
077J, the same `kFlat_of_isColimit` over the same tower — read at `(⊗_O)ᶠˡᶦᵖ` instead of at
`⊗_O`. Only the base case differs, and that is `kFlatFlip_single_of_isFlat`. -/
theorem exists_kFlatFlipResolution
    (G : CochainComplex (SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf.{u, u, u} R)) ℤ)
      :
    ∃ (P : CochainComplex
        (SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf.{u, u, u} R)) ℤ) (f : P ⟶ G),
      CochainComplex.KFlatBifunctor.KFlat
        (Stacks.SheafOfModules.Tensor.sheafTensor.{u, u, u, u, u} R).flip P ∧
      QuasiIso f := by
  obtain ⟨L⟩ :=
    Stacks.DerivedTensor.ResolutionByExtensionsByZero.exists_resolutionByDirectSumsExtensionsByZero
      R G
  refine ⟨colimit L.system, L.colimitComparison, ?_, L.colimit_quasiIso⟩
  refine CochainComplex.KFlatBifunctor.kFlat_of_isColimit _ (colimit.cocone L.system)
    (colimit.isColimit _) (hF_sheafTensor_flip R)
    (Stacks.SheafOfModules.KFlatResolution.hexact_sheafOfModules R) (fun n ↦ ?_)
  obtain ⟨b, hb⟩ := L.boundedAbove n
  have := hb
  exact CochainComplex.KFlatBifunctor.kFlat_of_isStrictlyLE _ (L.system.obj n) b
    (hF_sheafTensor_flip R) (Stacks.SheafOfModules.KFlatResolution.hexact_sheafOfModules R)
    (fun q ↦ kFlatFlip_single_of_isFlat R _
      (Stacks.SheafOfModules.KFlatResolution.isFlat_of_isSumOfExtensionByZeroStructureSheaves R _
        (L.term_isSum n q)) q)

/-- The same statement phrased with `KFlatLeft`, which is the shape
`CochainComplex.KFlatBifunctor.kFlatQLeft_isLocalization` takes. The rephrasing is
`kFlatLeft_iff_kFlat_flip`; it relates `KFlatLeft (⊗_O)` to K-flatness for the *flipped*
bifunctor, and asserts nothing about `KFlat (⊗_O)`. -/
theorem exists_kFlatLeft_quasiIso
    (G : CochainComplex (SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf.{u, u, u} R)) ℤ)
      :
    ∃ (P : CochainComplex
        (SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf.{u, u, u} R)) ℤ) (f : P ⟶ G),
      CochainComplex.KFlatBifunctor.KFlatLeft
        (Stacks.SheafOfModules.Tensor.sheafTensor.{u, u, u, u, u} R) P ∧
      QuasiIso f := by
  obtain ⟨P, f, hP, hf⟩ := exists_kFlatFlipResolution R G
  exact ⟨P, f, (CochainComplex.KFlatBifunctor.kFlatLeft_iff_kFlat_flip _ P).2 hP, hf⟩

/-- **`D(Mod(O))` is the localization of the *left* K-flat complexes of `O`-modules at the
quasi-isomorphisms.** Together with `Stacks.DerivedTensor.RingedSite.kFlatQ_isLocalization` this
  supplies both
localizations that `Localization.lift₂` consumes in order to descend `⊗_O` to a bifunctor on
`D(Mod(O))`. -/
theorem kFlatQLeft_isLocalization
    [HasDerivedCategory.{d}
      (SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf.{u, u, u} R))] :
    (CochainComplex.KFlatBifunctor.kFlatQLeft
        (Stacks.SheafOfModules.Tensor.sheafTensor.{u, u, u, u, u} R)).IsLocalization
      (CochainComplex.KFlatBifunctor.kFlatQuasiIsoLeft
        (Stacks.SheafOfModules.Tensor.sheafTensor.{u, u, u, u, u} R))
        :=
  inferInstance

end Stacks.DerivedTensor.RingedSite

end
