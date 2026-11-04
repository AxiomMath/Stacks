module

public import StacksFrontier.CategoryTheory.Functor.Bifunctor
public import StacksFrontier.Homology.KFlat.Bifunctor
public import StacksFrontier.Algebra.Homology.MapBifunctorNatIso
public import StacksFrontier.CategoryTheory.Triangulated.Localization
public import Mathlib.CategoryTheory.Localization.Resolution
public import Mathlib.Algebra.Homology.DerivedCategory.Basic
public import Mathlib.Algebra.Homology.DerivedCategory.HomologySequence
public import Mathlib.Algebra.Homology.BifunctorFlip
public import Mathlib.Algebra.Homology.Localization
public import Mathlib.CategoryTheory.Localization.Bifunctor
import StacksCore.Tactic.StacksAttribute

/-!
# The derived category is the localization of the K-flat complexes

For an additive bifunctor `F : A ⥤ B ⥤ D` between abelian categories, the complexes of
objects of `B` which are K-flat for `F` span a triangulated subcategory of the homotopy
category `K(B)`, and — as soon as every complex admits a K-flat resolution — the inclusion
of that subcategory localizes to the whole derived category `D(B)`.

The same holds in the left variable, for the mirror predicate `KFlatLeft`. Together the two
localizations are what `Localization.lift₂` consumes in order to descend `F` to a bifunctor
`D(A) ⥤ D(B) ⥤ D(D)`, and the two quasi-isomorphism-preservation results
(`quasiIso_of_kFlat`, `quasiIso_of_kFlatLeft`) are its two `IsInvertedBy` conditions.

`StacksFrontier.Homology.Tor.DerivedTensor` carries the corresponding steps out only for
`ModuleCat R`, and through the monoidal structure on complexes rather than through `F`, so
nothing there applies to the tensor product of sheaves of modules on a ringed site.

## Main definitions

* `CochainComplex.KFlatBifunctor.acyclicPreimage`: for a fixed `G`, the objects `K` of
  `K(B)` with `Tot(F(G, K))` acyclic, as an object property of `K(B)`.
* `CochainComplex.KFlatBifunctor.kFlatObjects`: the K-flat objects of `K(B)`.
* `CochainComplex.KFlatBifunctor.kFlatQuasiIso`: the quasi-isomorphisms between them.
* `CochainComplex.KFlatBifunctor.kFlatLocalizer`: the inclusion of the K-flat objects as a
  morphism of localizers.
* `CochainComplex.KFlatBifunctor.kFlatQ`: the K-flat objects viewed in `D(B)`.
* `CochainComplex.KFlatBifunctor.homotopyBifunctor`: the descent of `F` to a bifunctor
  `K(A) ⥤ K(B) ⥤ K(D)` on the homotopy categories.
* `CochainComplex.KFlatBifunctor.derivedBifunctor`: given K-flat resolutions on both sides,
  the further descent to a bifunctor `D(A) ⥤ D(B) ⥤ D(D)` on the derived categories.
* `CochainComplex.KFlatBifunctor.KFlatLeft`: K-flatness in the *first* argument of `F`, with
  `kFlatObjectsLeft`, `kFlatQuasiIsoLeft`, `kFlatLocalizerLeft` and `kFlatQLeft` mirroring
  the above on the `A` side.

## Main results

* `CochainComplex.KFlatBifunctor.kFlatObjects_isTriangulated`: `kFlatObjects F` is a
  triangulated object property.
* `CochainComplex.KFlatBifunctor.kFlatLocalizer_hasLeftResolutions`: a supply of K-flat
  resolutions gives Mathlib's `CategoryTheory.LocalizerMorphism.HasLeftResolutions` for the
  inclusion of the K-flat objects.
* `CochainComplex.KFlatBifunctor.kFlatLocalizer_isLocalizedEquivalence_of_hasLeftResolutions`
  and `kFlatLocalizerLeft_isLocalizedEquivalence_of_hasLeftResolutions` (instances): under
  `HasLeftResolutions` the inclusion of the (left) K-flat objects is a localized equivalence.
* `CochainComplex.KFlatBifunctor.kFlatQ_isLocalization_of_hasLeftResolutions` and
  `kFlatQLeft_isLocalization_of_hasLeftResolutions` (instances): `D(B)` and `D(A)` are the
  localizations of the (left) K-flat objects at the quasi-isomorphisms. These are what a descent
  of a bifunctor by `Localization.lift₂` consumes.
* `CochainComplex.KFlatBifunctor.kFlatLocalizer_isLocalizedEquivalence`,
  `kFlatLocalizerLeft_isLocalizedEquivalence`, `kFlatQ_isLocalization` and
  `kFlatQLeft_isLocalization`: the same, with the existence of resolutions as the explicit
  hypothesis `hres`.
* `CochainComplex.KFlatBifunctor.quasiIso_of_kFlatLeft`: the mirror of
  `quasiIso_of_kFlat`, so that both variables of `IsInvertedBy₂` are available.
* `CochainComplex.KFlatBifunctor.kFlatLeft_iff_kFlat_flip`: left K-flatness for `F` is
  K-flatness for `F.flip`, so the whole bifunctor-generic K-flatness engine of
  `StacksTag06YQ` applies to the left predicate too.
* `CochainComplex.KFlatBifunctor.totalToHomotopy_inverts`: `Tot(F(-, -))` inverts homotopy
  equivalences in each variable, which is what `Localization.lift₂` needs to produce
  `homotopyBifunctor`.
* `CochainComplex.KFlatBifunctor.kFlatToDerived_inverts`: `Tot(F(-, -))` inverts
  quasi-isomorphisms between (left) K-flat objects, which is what the second
  `Localization.lift₂` needs to produce `derivedBifunctor`.

## Implementation notes

K-flatness is an intersection over all acyclic `G` of the preimage of the acyclic objects of
`K(D)` along `Φ_G = Tot(F(G, -))`, which is a triangulated functor by Tag 0G6E
(`Stacks.SheafOfModules.Tensor.Reduction.bifunctorPhi_isTriangulated`). Each preimage is therefore
triangulated, and the three closure properties are checked one acyclic `G` at a time. The
`CommShift` datum `Stacks.SheafOfModules.Tensor.Reduction.bifunctorXi F G` has to be seated by hand
before each use, since `bifunctorPhi_isTriangulated` is stated under a `letI` for it.

`acyclicPreimage` and `kFlatObjects` are `abbrev`s rather than `def`s on purpose: the three
closure instances of the preimage of a triangulated object property are invisible to
instance search behind a semireducible definition, and each use above needs them.

The supply of K-flat resolutions is the instance argument
`[(kFlatLocalizer F).HasLeftResolutions]`, and `[(kFlatLocalizerLeft F).HasLeftResolutions]` for
the left variable (Mathlib's `CategoryTheory.LocalizerMorphism.HasLeftResolutions`), so that
the localized equivalences and the localizations below are instances. For the ringed-site tensor
product it is registered, at the universe restrictions of
`Stacks.SheafOfModules.KFlatResolution.exists_kFlatResolution`, by
`Stacks.DerivedTensor.RingedSite.kFlatLocalizer_hasLeftResolutions` and
`Stacks.DerivedTensor.RingedSite.kFlatLocalizerLeft_hasLeftResolutions`. The forms taking the
existence of resolutions as a hypothesis `hres` are kept alongside.

The homotopy-category descent does not build a homotopy equivalence of total complexes by
hand. Tag 0G6E's one-sided descents `bifunctorPhi`/`bifunctorPhiR` already exist, and a
functor sends an isomorphism to an isomorphism, so each variable's `IsInvertedBy` condition
is that observation transported along `bifunctorPhiFactors`/`bifunctorPhiRFactors`. The
final `IsInvertedBy₂` step needs the goal restated with `change` rather than `dsimp`: after
`rintro` it is phrased through `Functor.uncurry` and the pair projections, which instance
search will not reduce.

The derived descent is a second `Localization.lift₂`, over the two K-flat localizations.
Its `IsInvertedBy₂` condition is reduced to the complex level by the `Lifting₂.fst`/`.snd`
data of `homotopyBifunctor`, which have to be supplied by hand with both morphism properties
written out: left as `_` the second one stays a metavariable and instance search reports
itself stuck rather than failing. The resulting isomorphism must moreover be stated in the
`Qh ∘ quotient` spelling and not as `DerivedCategory.Q`, because the two differ across the
unexposed `HomologicalComplexUpToQuasiIso.Qh` and the application is then rejected.

The left predicate is stated directly, as a condition on the first argument, rather than as
`KFlat F.flip`; `kFlatLeft_iff_kFlat_flip` then identifies the two. That identification is
the only place a transpose of total complexes is needed, and Mathlib's
`HomologicalComplex.mapBifunctorFlipIso` supplies it with its Koszul signs already handled,
so no braiding of total complexes has to be built — which matters because the only such
braiding in this repository, `TotalTensorComplex.cochainComplex_symmetricMonoidalCategory`,
is stated for `ModuleCat` alone.

## References

* [Stacks Project, Tag 0G6E](https://stacks.math.columbia.edu/tag/0G6E)
* [Stacks Project, Tag 06YU](https://stacks.math.columbia.edu/tag/06YU)
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits Pretriangulated

noncomputable section

namespace CochainComplex.KFlatBifunctor

variable {A B D : Type*} [Category A] [Category B] [Category D]
  [Abelian A] [Abelian B] [Abelian D]
  (F : A ⥤ B ⥤ D) [F.Additive] [∀ X, (F.obj X).Additive]
  [∀ (K₁ : HomologicalComplex A (ComplexShape.up ℤ))
      (K₂ : HomologicalComplex B (ComplexShape.up ℤ)),
      K₁.HasMapBifunctor K₂ F (ComplexShape.up ℤ)]

/-- The objects `K` of `K(B)` whose image under `Φ_G = Tot(F(G, -))` is acyclic. -/
abbrev acyclicPreimage (G : CochainComplex A ℤ) :
    ObjectProperty (HomotopyCategory B (ComplexShape.up ℤ)) :=
  (HomotopyCategory.subcategoryAcyclic D).inverseImage
    (Stacks.SheafOfModules.Tensor.Reduction.bifunctorPhi F G)

/-- The K-flat objects of the homotopy category `K(B)`. -/
abbrev kFlatObjects : ObjectProperty (HomotopyCategory B (ComplexShape.up ℤ)) :=
  fun K ↦ KFlat F K.as

/-- K-flatness of an object of `K(B)` is membership in every `acyclicPreimage` at an acyclic
complex, which is what exhibits it as an intersection of triangulated object properties. -/
theorem kFlatObjects_iff (K : HomotopyCategory B (ComplexShape.up ℤ)) :
    kFlatObjects F K ↔
      ∀ G : CochainComplex A ℤ, G.Acyclic → acyclicPreimage F G K := by
  constructor
  · intro hK G hG
    exact (mem_subcategoryAcyclic_bifunctorPhi_iff F G K.as).2 (hK G hG)
  · intro hK G hG
    exact (mem_subcategoryAcyclic_bifunctorPhi_iff F G K.as).1 (hK G hG)

/-- An object property which is the intersection of a family of triangulated object properties
is triangulated. -/
private theorem isTriangulated_of_forall_isTriangulated {C ι : Type*} [Category C]
    [HasZeroObject C] [HasShift C ℤ] [Preadditive C]
    [∀ n : ℤ, (CategoryTheory.shiftFunctor C n).Additive] [Pretriangulated C]
    (P : ObjectProperty C) (S : ι → Prop) (Q : ι → ObjectProperty C)
    [∀ i, (Q i).IsClosedUnderIsomorphisms] (hQ : ∀ i, S i → (Q i).IsTriangulated)
    (hP : ∀ K, P K ↔ ∀ i, S i → Q i K) :
    P.IsTriangulated := by
  refine { exists_zero := ?_, isStableUnderShiftBy := ?_, ext₂' := ?_ }
  · obtain ⟨Z, hZ⟩ := ‹HasZeroObject C›
    refine ⟨Z, hZ, (hP _).2 fun i hi ↦ ?_⟩
    have := hQ i hi
    exact (Q i).prop_of_isZero hZ
  · refine fun n ↦ ⟨fun K hK ↦ (hP _).2 fun i hi ↦ ?_⟩
    have := hQ i hi
    exact (Q i).le_shift n K ((hP K).1 hK i hi)
  · intro T hT h₁ h₃
    refine P.le_isoClosure _ ((hP _).2 fun i hi ↦ ?_)
    have := hQ i hi
    exact (Q i).ext_of_isTriangulatedClosed₂ T hT ((hP _).1 h₁ i hi) ((hP _).1 h₃ i hi)

/-- The K-flat objects span a triangulated subcategory of `K(B)`: each `acyclicPreimage` is
the preimage of the acyclic objects along the triangulated functor `Φ_G`, and K-flatness is
their intersection. -/
theorem kFlatObjects_isTriangulated : (kFlatObjects F).IsTriangulated :=
  isTriangulated_of_forall_isTriangulated _ (fun G : CochainComplex A ℤ ↦ G.Acyclic)
    (acyclicPreimage F) (fun G _ ↦ by
      let := Stacks.SheafOfModules.Tensor.Reduction.bifunctorXi F G
      have := Stacks.SheafOfModules.Tensor.Reduction.bifunctorPhi_isTriangulated F G
      infer_instance) (kFlatObjects_iff F)

/-! ### K-flatness in the left variable -/

/-- A cochain complex `K` of objects of `A` is **left K-flat for `F`** when the total complex
`Tot(F(K, G))` is acyclic for every acyclic cochain complex `G` of objects of `B`.

This is the mirror of `KFlat`, which constrains the *second* argument of `F`. For a general
bifunctor the two predicates are genuinely different conditions on genuinely different
categories; they coincide only through a symmetry of `F`, and establishing that for the
total complexes costs the Koszul-sign braiding, which exists in this repository only for
`ModuleCat`. Stating the mirror predicate directly avoids it entirely. -/
def KFlatLeft (K : CochainComplex A ℤ) : Prop :=
  ∀ G : CochainComplex B ℤ, G.Acyclic → (totalComplex F K G).Acyclic

/-- `Tot(F(K, -))` for a left K-flat `K` takes a morphism with acyclic mapping cone to a
morphism with acyclic mapping cone. The cone of the image is the image of the cone, by
`Stacks.SheafOfModules.Tensor.Reduction.bifunctorMappingConeIso` — the left-factor-fixed companion
  of the
`bifunctorMappingConeIsoR` which `acyclic_mappingCone_of_kFlat` uses. -/
theorem acyclic_mappingCone_of_kFlatLeft (K : CochainComplex A ℤ) (hK : KFlatLeft F K)
    {X Y : CochainComplex B ℤ} (f : X ⟶ Y)
    (hf : (CochainComplex.mappingCone f).Acyclic) :
    (CochainComplex.mappingCone
      (((F.map₂HomologicalComplex (ComplexShape.up ℤ) (ComplexShape.up ℤ)
        (ComplexShape.up ℤ)).obj K).map f)).Acyclic := by
  intro n
  exact HomologicalComplex.ExactAt.of_iso (hK (CochainComplex.mappingCone f) hf n)
    (Stacks.SheafOfModules.Tensor.Reduction.bifunctorMappingConeIso F K f)

/-- **The total complex with a left K-flat first factor preserves quasi-isomorphisms in the
second factor.** This is the mirror of `quasiIso_of_kFlat`, and together with it supplies
both variables of the `IsInvertedBy₂` condition that descends `F` to a bifunctor on the
derived category. -/
theorem quasiIso_of_kFlatLeft (K : CochainComplex A ℤ) (hK : KFlatLeft F K)
    {X Y : CochainComplex B ℤ} (f : X ⟶ Y) (hf : QuasiIso f) :
    QuasiIso (((F.map₂HomologicalComplex (ComplexShape.up ℤ) (ComplexShape.up ℤ)
      (ComplexShape.up ℤ)).obj K).map f) :=
  (quasiIso_iff_acyclic_mappingCone _).2
    (acyclic_mappingCone_of_kFlatLeft F K hK f ((quasiIso_iff_acyclic_mappingCone f).1 hf))

section Flip

/-- Transposing the arguments of `F` exchanges left and right K-flatness: the two total
complexes are the two total complexes of transposed double complexes, and Mathlib's
`HomologicalComplex.mapBifunctorFlipIso` identifies them, Koszul signs included.

This is what puts the whole bifunctor-generic K-flatness engine of `StacksTag06YQ` —
`kFlat_single_of_exact`, `kFlat_of_isStrictlyLE`, `kFlat_of_isColimit` and the rest — behind
the left predicate as well, by reading it at `F.flip`. No hand-built braiding of total
complexes is needed, which is the cost the `ModuleCat`-only
`TotalTensorComplex.cochainComplex_symmetricMonoidalCategory` would have imposed. -/
theorem kFlatLeft_iff_kFlat_flip (K : CochainComplex A ℤ) :
    KFlatLeft F K ↔ KFlat F.flip K :=
  ⟨fun hK G hG n ↦ (hK G hG n).of_iso
      (HomologicalComplex.mapBifunctorFlipIso K G F (ComplexShape.up ℤ)).symm,
    fun hK G hG n ↦ (hK G hG n).of_iso
      (HomologicalComplex.mapBifunctorFlipIso K G F (ComplexShape.up ℤ))⟩

end Flip

/-- The image in `K(D)` of `Tot(F(K, G))` is acyclic exactly when the vertex `Φ^R_G(K)`
obtained from the right-case descended functor is: the mirror of
`mem_subcategoryAcyclic_bifunctorPhi_iff`, by `bifunctorPhiRFactors`. -/
theorem mem_subcategoryAcyclic_bifunctorPhiR_iff
    (G : CochainComplex B ℤ) (K : CochainComplex A ℤ) :
    HomotopyCategory.subcategoryAcyclic D
        ((Stacks.SheafOfModules.Tensor.Reduction.bifunctorPhiR F G).obj
          ((HomotopyCategory.quotient A (ComplexShape.up ℤ)).obj K)) ↔
      (totalComplex F K G).Acyclic := by
  rw [← HomotopyCategory.quotient_obj_mem_subcategoryAcyclic_iff_acyclic]
  exact (HomotopyCategory.subcategoryAcyclic D).prop_iff_of_iso
    ((Stacks.SheafOfModules.Tensor.Reduction.bifunctorPhiRFactors F G).app K)

/-- The objects `K` of `K(A)` whose image under `Φ^R_G = Tot(F(-, G))` is acyclic. -/
abbrev acyclicPreimageLeft (G : CochainComplex B ℤ) :
    ObjectProperty (HomotopyCategory A (ComplexShape.up ℤ)) :=
  (HomotopyCategory.subcategoryAcyclic D).inverseImage
    (Stacks.SheafOfModules.Tensor.Reduction.bifunctorPhiR F G)

/-- The left K-flat objects of the homotopy category `K(A)`. -/
abbrev kFlatObjectsLeft : ObjectProperty (HomotopyCategory A (ComplexShape.up ℤ)) :=
  fun K ↦ KFlatLeft F K.as

/-- Left K-flatness of an object of `K(A)` is membership in every `acyclicPreimageLeft` at
an acyclic complex. -/
theorem kFlatObjectsLeft_iff (K : HomotopyCategory A (ComplexShape.up ℤ)) :
    kFlatObjectsLeft F K ↔
      ∀ G : CochainComplex B ℤ, G.Acyclic → acyclicPreimageLeft F G K :=
  ⟨fun hK G hG ↦ (mem_subcategoryAcyclic_bifunctorPhiR_iff F G K.as).2 (hK G hG),
    fun hK G hG ↦ (mem_subcategoryAcyclic_bifunctorPhiR_iff F G K.as).1 (hK G hG)⟩

/-- The left K-flat objects span a triangulated subcategory of `K(A)`, by the mirror of
`kFlatObjects_isTriangulated` through `bifunctorPhiR_isTriangulated`. -/
theorem kFlatObjectsLeft_isTriangulated : (kFlatObjectsLeft F).IsTriangulated :=
  isTriangulated_of_forall_isTriangulated _ (fun G : CochainComplex B ℤ ↦ G.Acyclic)
    (acyclicPreimageLeft F) (fun G _ ↦ by
      let := Stacks.SheafOfModules.Tensor.Reduction.bifunctorXiR F G
      have := Stacks.SheafOfModules.Tensor.Reduction.bifunctorPhiR_isTriangulated F G
      infer_instance) (kFlatObjectsLeft_iff F)

/-! ### The K-flat subcategory localizes to the derived category -/

/-- The quasi-isomorphisms of `K(C)` are saturated and compatible with the triangulation, being
the homological kernel of the homology functor. -/
theorem quasiIso_isSaturated_and_isCompatibleWithTriangulation (C : Type*) [Category C]
    [Abelian C] :
    (HomotopyCategory.quasiIso C (ComplexShape.up ℤ)).IsSaturated ∧
      (HomotopyCategory.quasiIso C (ComplexShape.up ℤ)).IsCompatibleWithTriangulation := by
  let H := HomotopyCategory.homologyFunctor C (ComplexShape.up ℤ) 0
  refine CategoryTheory.Functor.isSaturated_and_isCompatibleWithTriangulation H _
    fun X Y f ↦ ?_
  let _ : H.ShiftSequence ℤ := CategoryTheory.Functor.ShiftSequence.tautological H ℤ
  rw [HomotopyCategory.quasiIso_eq_trW_subcategoryAcyclic]
  exact H.mem_homologicalKernel_trW_iff f

/-- The quasi-isomorphisms between K-flat objects of `K(B)`. -/
abbrev kFlatQuasiIso : MorphismProperty (kFlatObjects F).FullSubcategory :=
  (HomotopyCategory.quasiIso B (ComplexShape.up ℤ)).inverseImage (kFlatObjects F).ι

/-- The inclusion of the K-flat objects of `K(B)`, as a morphism of localizers. -/
def kFlatLocalizer :
    CategoryTheory.LocalizerMorphism (kFlatQuasiIso F)
      (HomotopyCategory.quasiIso B (ComplexShape.up ℤ)) where
  functor := (kFlatObjects F).ι
  map _ _ _ hf := hf

/-- A supply of K-flat resolutions makes every object of `K(B)` resolvable by a K-flat one.
For `F = ⊗_O` on a ringed site the hypothesis is
  `Stacks.SheafOfModules.KFlatResolution.exists_kFlatResolution`. -/
theorem kFlatLocalizer_hasLeftResolutions
    (hres : ∀ G : CochainComplex B ℤ, ∃ (P : CochainComplex B ℤ) (f : P ⟶ G),
      KFlat F P ∧ QuasiIso f) :
    (kFlatLocalizer F).HasLeftResolutions := by
  intro X
  obtain ⟨K, rfl⟩ := HomotopyCategory.quotient_obj_surjective X
  obtain ⟨P, f, hP, hf⟩ := hres K
  exact ⟨{
    X₁ := ⟨(HomotopyCategory.quotient B (ComplexShape.up ℤ)).obj P, hP⟩
    w := (HomotopyCategory.quotient B (ComplexShape.up ℤ)).map f
    hw := (HomotopyCategory.quotient_map_mem_quasiIso_iff f).2 hf }⟩

/-- **The K-flat objects localize to the whole derived category.** The inclusion of the
K-flat subcategory of `K(B)` is a localized equivalence for the quasi-isomorphisms: the
quasi-isomorphisms are saturated and compatible with the triangulation because they are the
homological kernel of the homology functor, the K-flat objects are a triangulated
subcategory, and every object has a K-flat resolution. -/
instance kFlatLocalizer_isLocalizedEquivalence_of_hasLeftResolutions
    [(kFlatLocalizer F).HasLeftResolutions] :
    (kFlatLocalizer F).IsLocalizedEquivalence := by
  let P := kFlatObjects F
  let _ : P.IsTriangulated := kFlatObjects_isTriangulated F
  obtain ⟨hS, _⟩ := quasiIso_isSaturated_and_isCompatibleWithTriangulation B
  exact (P.isSaturated_and_isCompatibleWithTriangulation_inverseImage_ι_and_isLocalizedEquivalence
    _ hS).2.2 ‹_›

/-- `kFlatLocalizer_isLocalizedEquivalence_of_hasLeftResolutions`, with the existence of K-flat
resolutions as the explicit hypothesis `hres` instead of an instance. -/
theorem kFlatLocalizer_isLocalizedEquivalence
    (hres : ∀ G : CochainComplex B ℤ, ∃ (P : CochainComplex B ℤ) (f : P ⟶ G),
      KFlat F P ∧ QuasiIso f) :
    (kFlatLocalizer F).IsLocalizedEquivalence :=
  have := kFlatLocalizer_hasLeftResolutions F hres
  inferInstance

/-- The quasi-isomorphisms between left K-flat objects of `K(A)`. -/
abbrev kFlatQuasiIsoLeft : MorphismProperty (kFlatObjectsLeft F).FullSubcategory :=
  (HomotopyCategory.quasiIso A (ComplexShape.up ℤ)).inverseImage (kFlatObjectsLeft F).ι

/-- The inclusion of the left K-flat objects of `K(A)`, as a morphism of localizers. -/
def kFlatLocalizerLeft :
    CategoryTheory.LocalizerMorphism (kFlatQuasiIsoLeft F)
      (HomotopyCategory.quasiIso A (ComplexShape.up ℤ)) where
  functor := (kFlatObjectsLeft F).ι
  map _ _ _ hf := hf

/-- A supply of left K-flat resolutions resolves every object of `K(A)`. -/
theorem kFlatLocalizerLeft_hasLeftResolutions
    (hres : ∀ G : CochainComplex A ℤ, ∃ (P : CochainComplex A ℤ) (f : P ⟶ G),
      KFlatLeft F P ∧ QuasiIso f) :
    (kFlatLocalizerLeft F).HasLeftResolutions := by
  intro X
  obtain ⟨K, rfl⟩ := HomotopyCategory.quotient_obj_surjective X
  obtain ⟨P, f, hP, hf⟩ := hres K
  exact ⟨{
    X₁ := ⟨(HomotopyCategory.quotient A (ComplexShape.up ℤ)).obj P, hP⟩
    w := (HomotopyCategory.quotient A (ComplexShape.up ℤ)).map f
    hw := (HomotopyCategory.quotient_map_mem_quasiIso_iff f).2 hf }⟩

/-- **The left K-flat objects localize to the whole derived category `D(A)`**, the mirror of
`kFlatLocalizer_isLocalizedEquivalence_of_hasLeftResolutions`. -/
instance kFlatLocalizerLeft_isLocalizedEquivalence_of_hasLeftResolutions
    [(kFlatLocalizerLeft F).HasLeftResolutions] :
    (kFlatLocalizerLeft F).IsLocalizedEquivalence := by
  let P := kFlatObjectsLeft F
  let _ : P.IsTriangulated := kFlatObjectsLeft_isTriangulated F
  obtain ⟨hS, _⟩ := quasiIso_isSaturated_and_isCompatibleWithTriangulation A
  exact (P.isSaturated_and_isCompatibleWithTriangulation_inverseImage_ι_and_isLocalizedEquivalence
    _ hS).2.2 ‹_›

/-- `kFlatLocalizerLeft_isLocalizedEquivalence_of_hasLeftResolutions`, with the existence of left
K-flat resolutions as the explicit hypothesis `hres` instead of an instance. -/
theorem kFlatLocalizerLeft_isLocalizedEquivalence
    (hres : ∀ G : CochainComplex A ℤ, ∃ (P : CochainComplex A ℤ) (f : P ⟶ G),
      KFlatLeft F P ∧ QuasiIso f) :
    (kFlatLocalizerLeft F).IsLocalizedEquivalence :=
  have := kFlatLocalizerLeft_hasLeftResolutions F hres
  inferInstance

/-- A functor isomorphic to a triangulated functor carries a shift commutation making it
triangulated. -/
private theorem exists_commShift_isTriangulated_of_iso {C E : Type*} [Category* C] [Category* E]
    [HasShift C ℤ] [HasShift E ℤ] [HasZeroObject C] [HasZeroObject E] [Preadditive C]
    [Preadditive E] [∀ n : ℤ, (CategoryTheory.shiftFunctor C n).Additive]
    [∀ n : ℤ, (CategoryTheory.shiftFunctor E n).Additive] [Pretriangulated C] [Pretriangulated E]
    {F₁ F₂ : C ⥤ E} [F₁.CommShift ℤ] [F₁.IsTriangulated] (e : F₁ ≅ F₂) :
    ∃ s : F₂.CommShift ℤ, letI := s; F₂.IsTriangulated := by
  let _ := Functor.CommShift.ofIso e ℤ
  have _ := Functor.CommShift.ofIso_compatibility e ℤ
  exact ⟨inferInstance, Functor.isTriangulated_of_iso e⟩

/-! ### The descent of `F` to the homotopy categories -/

section HomotopyDescent

/-- `Tot(F(-, -))` as a bifunctor on cochain complexes, landing in `K(D)`. -/
abbrev totalToHomotopy :
    CochainComplex A ℤ ⥤ CochainComplex B ℤ ⥤ HomotopyCategory D (ComplexShape.up ℤ) :=
  F.map₂HomologicalComplex (ComplexShape.up ℤ) (ComplexShape.up ℤ) (ComplexShape.up ℤ) ⋙
    (Functor.whiskeringRight _ _ _).obj
      (HomotopyCategory.quotient D (ComplexShape.up ℤ))

/-- A functor of complexes which factors through `K(C)` sends homotopy equivalences to
isomorphisms, since the factorization sends the isomorphism in `K(C)` to an isomorphism. -/
private theorem isIso_map_of_homotopyEquivalences {C E : Type*} [Category C] [Category E]
    [Abelian C] (Φ : HomotopyCategory C (ComplexShape.up ℤ) ⥤ E)
    (T : CochainComplex C ℤ ⥤ E) (e : HomotopyCategory.quotient C (ComplexShape.up ℤ) ⋙ Φ ≅ T)
    {X Y : CochainComplex C ℤ} (f : X ⟶ Y)
    (hf : HomologicalComplex.homotopyEquivalences C (ComplexShape.up ℤ) f) : IsIso (T.map f) := by
  have : IsIso ((HomotopyCategory.quotient C (ComplexShape.up ℤ)).map f) :=
    CategoryTheory.Localization.inverts (HomotopyCategory.quotient C (ComplexShape.up ℤ))
      (HomologicalComplex.homotopyEquivalences C (ComplexShape.up ℤ)) f hf
  exact (NatIso.isIso_map_iff e f).1 (Φ.map_isIso _)

/-- A homotopy equivalence in the **first** variable becomes an isomorphism in `K(D)`. The
descended functor `Φ^R_{K₂}` of Tag 0G6E sends the image of a homotopy equivalence, which is
already an isomorphism of `K(A)`, to an isomorphism; `bifunctorPhiRFactors` transports that
back to the total complexes. -/
theorem isIso_quotient_map_map_app
    {K₁ L₁ : CochainComplex A ℤ} (f : K₁ ⟶ L₁)
    (hf : HomologicalComplex.homotopyEquivalences A (ComplexShape.up ℤ) f)
    (K₂ : CochainComplex B ℤ) :
    IsIso ((HomotopyCategory.quotient D (ComplexShape.up ℤ)).map
      (((F.map₂HomologicalComplex (ComplexShape.up ℤ) (ComplexShape.up ℤ)
        (ComplexShape.up ℤ)).map f).app K₂)) :=
  isIso_map_of_homotopyEquivalences _ ((totalToHomotopy F).flip.obj K₂)
    (Stacks.SheafOfModules.Tensor.Reduction.bifunctorPhiRFactors F K₂) f hf

/-- A homotopy equivalence in the **second** variable becomes an isomorphism in `K(D)`, by
the same argument through `bifunctorPhiFactors`. -/
theorem isIso_quotient_map_obj_map
    (L₁ : CochainComplex A ℤ)
    {K₂ L₂ : CochainComplex B ℤ} (g : K₂ ⟶ L₂)
    (hg : HomologicalComplex.homotopyEquivalences B (ComplexShape.up ℤ) g) :
    IsIso ((HomotopyCategory.quotient D (ComplexShape.up ℤ)).map
      (((F.map₂HomologicalComplex (ComplexShape.up ℤ) (ComplexShape.up ℤ)
        (ComplexShape.up ℤ)).obj L₁).map g)) :=
  isIso_map_of_homotopyEquivalences _ ((totalToHomotopy F).obj L₁)
    (Stacks.SheafOfModules.Tensor.Reduction.bifunctorPhiFactors F L₁) g hg

/-- **`Tot(F(-, -))` inverts homotopy equivalences in both variables**, which is the
`IsInvertedBy₂` condition that `Localization.lift₂` requires. -/
theorem totalToHomotopy_inverts :
    MorphismProperty.IsInvertedBy₂
      (HomologicalComplex.homotopyEquivalences A (ComplexShape.up ℤ))
      (HomologicalComplex.homotopyEquivalences B (ComplexShape.up ℤ))
      (totalToHomotopy F) := by
  rintro ⟨K₁, K₂⟩ ⟨L₁, L₂⟩ ⟨f, g⟩ ⟨hf, hg⟩
  have h₁ := isIso_quotient_map_map_app F f hf K₂
  have h₂ := isIso_quotient_map_obj_map F L₁ g hg
  change IsIso ((HomotopyCategory.quotient D (ComplexShape.up ℤ)).map
        (((F.map₂HomologicalComplex (ComplexShape.up ℤ) (ComplexShape.up ℤ)
          (ComplexShape.up ℤ)).map f).app K₂) ≫
      (HomotopyCategory.quotient D (ComplexShape.up ℤ)).map
        (((F.map₂HomologicalComplex (ComplexShape.up ℤ) (ComplexShape.up ℤ)
          (ComplexShape.up ℤ)).obj L₁).map g))
  infer_instance

/-- **The descent of `F` to a bifunctor on the homotopy categories**,
`K(A) ⥤ K(B) ⥤ K(D)`. Homotopy invariance in each variable is Tag 0G6E's one-sided
descents, and `HomotopyCategory.quotient` is a localization at the homotopy equivalences. -/
@[sga "4½ Etat_0 1.3.3" "special case"]
noncomputable def homotopyBifunctor :
    HomotopyCategory A (ComplexShape.up ℤ) ⥤ HomotopyCategory B (ComplexShape.up ℤ) ⥤
      HomotopyCategory D (ComplexShape.up ℤ) :=
  CategoryTheory.Localization.lift₂ (totalToHomotopy F) (totalToHomotopy_inverts F)
    (HomotopyCategory.quotient A (ComplexShape.up ℤ))
    (HomotopyCategory.quotient B (ComplexShape.up ℤ))

/-- The descent agrees with `Tot(F(-, -))` on complexes, as a `Lifting₂` datum. -/
noncomputable instance homotopyBifunctor_lifting :
    CategoryTheory.Localization.Lifting₂
      (HomotopyCategory.quotient A (ComplexShape.up ℤ))
      (HomotopyCategory.quotient B (ComplexShape.up ℤ))
      (HomologicalComplex.homotopyEquivalences A (ComplexShape.up ℤ))
      (HomologicalComplex.homotopyEquivalences B (ComplexShape.up ℤ))
      (totalToHomotopy F) (homotopyBifunctor F) :=
  inferInstanceAs (CategoryTheory.Localization.Lifting₂ _ _ _ _ _
    (CategoryTheory.Localization.lift₂ (totalToHomotopy F) (totalToHomotopy_inverts F) _ _))

end HomotopyDescent

/-- The quasi-isomorphisms between the objects of a triangulated subcategory of `K(C)` admit a
left calculus of fractions: they are the `trW` of the acyclic objects pulled back along the
inclusion. -/
private theorem hasLeftCalculusOfFractions_quasiIso_inverseImage_ι (C : Type*) [Category C]
    [Abelian C] (P : ObjectProperty (HomotopyCategory C (ComplexShape.up ℤ)))
    [P.IsTriangulated] :
    ((HomotopyCategory.quasiIso C (ComplexShape.up ℤ)).inverseImage P.ι).HasLeftCalculusOfFractions
    := by
  have h : (HomotopyCategory.quasiIso C (ComplexShape.up ℤ)).inverseImage P.ι =
      ((HomotopyCategory.subcategoryAcyclic C).inverseImage P.ι).trW := by
    ext X Y f
    change HomotopyCategory.quasiIso _ _ (P.ι.map f) ↔ _
    rw [HomotopyCategory.quasiIso_eq_trW_subcategoryAcyclic]
    exact ((HomotopyCategory.subcategoryAcyclic C).inverseImage_trW_iff P.ι f).symm
  rw [h]
  infer_instance

/-- The quasi-isomorphisms between K-flat objects admit a left calculus of fractions: they
are the `trW` of the acyclic objects pulled back along the inclusion, and `kFlatObjects` is
triangulated. This is one of the preliminaries the exactness of the descended bifunctor
rests on. -/
theorem kFlatQuasiIso_hasLeftCalculusOfFractions :
    (kFlatQuasiIso F).HasLeftCalculusOfFractions :=
  have := kFlatObjects_isTriangulated F
  hasLeftCalculusOfFractions_quasiIso_inverseImage_ι B _

/-- The mirror, on the left K-flat objects of `K(A)`. -/
theorem kFlatQuasiIsoLeft_hasLeftCalculusOfFractions :
    (kFlatQuasiIsoLeft F).HasLeftCalculusOfFractions :=
  have := kFlatObjectsLeft_isTriangulated F
  hasLeftCalculusOfFractions_quasiIso_inverseImage_ι A _

section Derived

variable [HasDerivedCategory B]

/-- The K-flat objects of `K(B)`, viewed in the derived category `D(B)`. -/
abbrev kFlatQ : (kFlatObjects F).FullSubcategory ⥤ DerivedCategory B :=
  (kFlatObjects F).ι ⋙ DerivedCategory.Qh

/-- **`D(B)` is the localization of the K-flat objects of `K(B)` at the
quasi-isomorphisms.** This is the input a bifunctor descent by `Localization.lift₂`
consumes: a bifunctor defined on K-flat complexes and inverting quasi-isomorphisms between
them descends to `D(B)`. -/
instance kFlatQ_isLocalization_of_hasLeftResolutions [(kFlatLocalizer F).HasLeftResolutions] :
    (kFlatQ F).IsLocalization (kFlatQuasiIso F) :=
  LocalizerMorphism.IsLocalizedEquivalence.isLocalization
    (kFlatLocalizer F) (DerivedCategory.Qh (C := B))

/-- `kFlatQ_isLocalization_of_hasLeftResolutions`, with the existence of K-flat resolutions as
the explicit hypothesis `hres` instead of an instance. -/
theorem kFlatQ_isLocalization
    (hres : ∀ G : CochainComplex B ℤ, ∃ (P : CochainComplex B ℤ) (f : P ⟶ G),
      KFlat F P ∧ QuasiIso f) :
    (kFlatQ F).IsLocalization (kFlatQuasiIso F) :=
  have := kFlatLocalizer_hasLeftResolutions F hres
  inferInstance

end Derived

section DerivedLeft

variable [HasDerivedCategory A]

/-- The left K-flat objects of `K(A)`, viewed in the derived category `D(A)`. -/
abbrev kFlatQLeft : (kFlatObjectsLeft F).FullSubcategory ⥤ DerivedCategory A :=
  (kFlatObjectsLeft F).ι ⋙ DerivedCategory.Qh

/-- **`D(A)` is the localization of the left K-flat objects of `K(A)` at the
quasi-isomorphisms.** With `kFlatQ_isLocalization_of_hasLeftResolutions` this supplies both
localizations that `Localization.lift₂` needs in order to descend `F` to a bifunctor
`D(A) ⥤ D(B) ⥤ D(D)`. -/
instance kFlatQLeft_isLocalization_of_hasLeftResolutions
    [(kFlatLocalizerLeft F).HasLeftResolutions] :
    (kFlatQLeft F).IsLocalization (kFlatQuasiIsoLeft F) :=
  LocalizerMorphism.IsLocalizedEquivalence.isLocalization
    (kFlatLocalizerLeft F) (DerivedCategory.Qh (C := A))

/-- `kFlatQLeft_isLocalization_of_hasLeftResolutions`, with the existence of left K-flat
resolutions as the explicit hypothesis `hres` instead of an instance. -/
theorem kFlatQLeft_isLocalization
    (hres : ∀ G : CochainComplex A ℤ, ∃ (P : CochainComplex A ℤ) (f : P ⟶ G),
      KFlatLeft F P ∧ QuasiIso f) :
    (kFlatQLeft F).IsLocalization (kFlatQuasiIsoLeft F) :=
  have := kFlatLocalizerLeft_hasLeftResolutions F hres
  inferInstance

end DerivedLeft

/-! ### The descent to the derived categories -/

section DerivedDescent

variable [HasDerivedCategory A] [HasDerivedCategory B] [HasDerivedCategory D]

/-- If `Φ` lifts `T` along a localization `L`, then `G ∘ Φ` inverts `L f` once `G ∘ T` inverts
`f`. -/
private theorem isIso_map_map_of_lifting {C H E E' : Type*} [Category C] [Category H]
    [Category E] [Category E'] (L : C ⥤ H) (W : MorphismProperty C) (T : C ⥤ E) (Φ : H ⥤ E)
    [CategoryTheory.Localization.Lifting L W T Φ] (G : E ⥤ E') {X Y : C} (f : X ⟶ Y)
    (h : IsIso (G.map (T.map f))) : IsIso (G.map (Φ.map (L.map f))) :=
  (NatIso.isIso_map_iff (Functor.isoWhiskerRight
    (CategoryTheory.Localization.Lifting.iso L W T Φ) G) f).2 h

omit [HasDerivedCategory A] [HasDerivedCategory B] in
/-- A quasi-isomorphism of `K(A)` becomes an isomorphism of `D(D)` after `Tot(F(-, K₂))`,
for K-flat `K₂`. The `Lifting₂.snd` datum of `homotopyBifunctor` turns this into the
corresponding statement about total complexes, which is `quasiIso_of_kFlat`. -/
theorem isIso_Qh_map_homotopyBifunctor_map_app
    {X Y : HomotopyCategory A (ComplexShape.up ℤ)} (φ : X ⟶ Y)
    (hφ : HomotopyCategory.quasiIso A (ComplexShape.up ℤ) φ)
    (Z : HomotopyCategory B (ComplexShape.up ℤ)) (hZ : kFlatObjects F Z) :
    IsIso ((DerivedCategory.Qh (C := D)).map
      (((homotopyBifunctor F).map φ).app Z)) := by
  obtain ⟨K₁, rfl⟩ := HomotopyCategory.quotient_obj_surjective X
  obtain ⟨L₁, rfl⟩ := HomotopyCategory.quotient_obj_surjective Y
  obtain ⟨K₂, rfl⟩ := HomotopyCategory.quotient_obj_surjective Z
  obtain ⟨f, rfl⟩ := (HomotopyCategory.quotient A (ComplexShape.up ℤ)).map_surjective φ
  have hiso : IsIso ((DerivedCategory.Qh (C := D)).map
      ((HomotopyCategory.quotient D (ComplexShape.up ℤ)).map
        (((F.map₂HomologicalComplex (ComplexShape.up ℤ) (ComplexShape.up ℤ)
          (ComplexShape.up ℤ)).map f).app K₂))) := by
    rw [DerivedCategory.isIso_Qh_map_iff, HomotopyCategory.quotient_map_mem_quasiIso_iff]
    exact quasiIso_of_kFlat F K₂ hZ f ((HomotopyCategory.quotient_map_mem_quasiIso_iff f).1 hφ)
  have := CategoryTheory.Localization.Lifting₂.snd
    (HomotopyCategory.quotient A (ComplexShape.up ℤ))
    (HomotopyCategory.quotient B (ComplexShape.up ℤ))
    (HomologicalComplex.homotopyEquivalences A (ComplexShape.up ℤ))
    (HomologicalComplex.homotopyEquivalences B (ComplexShape.up ℤ))
    (totalToHomotopy F) (homotopyBifunctor F) K₂
  exact isIso_map_map_of_lifting (HomotopyCategory.quotient A (ComplexShape.up ℤ))
    (HomologicalComplex.homotopyEquivalences A (ComplexShape.up ℤ))
    ((totalToHomotopy F).flip.obj K₂)
    ((homotopyBifunctor F).flip.obj ((HomotopyCategory.quotient B (ComplexShape.up ℤ)).obj K₂))
    _ f hiso

omit [HasDerivedCategory A] [HasDerivedCategory B] in
/-- The mirror: a quasi-isomorphism of `K(B)` becomes an isomorphism of `D(D)` after
`Tot(F(K₁, -))` for left K-flat `K₁`, by `quasiIso_of_kFlatLeft`. -/
theorem isIso_Qh_map_homotopyBifunctor_obj_map
    (W : HomotopyCategory A (ComplexShape.up ℤ)) (hW : kFlatObjectsLeft F W)
    {X Y : HomotopyCategory B (ComplexShape.up ℤ)} (ψ : X ⟶ Y)
    (hψ : HomotopyCategory.quasiIso B (ComplexShape.up ℤ) ψ) :
    IsIso ((DerivedCategory.Qh (C := D)).map
      (((homotopyBifunctor F).obj W).map ψ)) := by
  obtain ⟨K₁, rfl⟩ := HomotopyCategory.quotient_obj_surjective W
  obtain ⟨K₂, rfl⟩ := HomotopyCategory.quotient_obj_surjective X
  obtain ⟨L₂, rfl⟩ := HomotopyCategory.quotient_obj_surjective Y
  obtain ⟨g, rfl⟩ := (HomotopyCategory.quotient B (ComplexShape.up ℤ)).map_surjective ψ
  have hiso : IsIso ((DerivedCategory.Qh (C := D)).map
      ((HomotopyCategory.quotient D (ComplexShape.up ℤ)).map
        (((F.map₂HomologicalComplex (ComplexShape.up ℤ) (ComplexShape.up ℤ)
          (ComplexShape.up ℤ)).obj K₁).map g))) := by
    rw [DerivedCategory.isIso_Qh_map_iff, HomotopyCategory.quotient_map_mem_quasiIso_iff]
    exact quasiIso_of_kFlatLeft F K₁ hW g ((HomotopyCategory.quotient_map_mem_quasiIso_iff g).1 hψ)
  have := CategoryTheory.Localization.Lifting₂.fst
    (HomotopyCategory.quotient A (ComplexShape.up ℤ))
    (HomotopyCategory.quotient B (ComplexShape.up ℤ))
    (HomologicalComplex.homotopyEquivalences A (ComplexShape.up ℤ))
    (HomologicalComplex.homotopyEquivalences B (ComplexShape.up ℤ))
    (totalToHomotopy F) (homotopyBifunctor F) K₁
  exact isIso_map_map_of_lifting (HomotopyCategory.quotient B (ComplexShape.up ℤ))
    (HomologicalComplex.homotopyEquivalences B (ComplexShape.up ℤ))
    ((totalToHomotopy F).obj K₁)
    ((homotopyBifunctor F).obj ((HomotopyCategory.quotient A (ComplexShape.up ℤ)).obj K₁))
    _ g hiso

/-- `Tot(F(-, -))` on the (left) K-flat objects of the homotopy categories, landing in
`D(D)`: the bifunctor whose descent along the two localizations is the derived bifunctor. -/
noncomputable abbrev kFlatToDerived :
    (kFlatObjectsLeft F).FullSubcategory ⥤ (kFlatObjects F).FullSubcategory ⥤
      DerivedCategory D :=
  ((((Functor.whiskeringLeft₂ (DerivedCategory D)).obj (kFlatObjectsLeft F).ι).obj
      (kFlatObjects F).ι).obj
    (homotopyBifunctor F ⋙ (Functor.whiskeringRight _ _ _).obj
      (DerivedCategory.Qh (C := D))))

omit [HasDerivedCategory A] [HasDerivedCategory B] in
/-- **`Tot(F(-, -))` inverts quasi-isomorphisms between (left) K-flat objects**, which is the
`IsInvertedBy₂` condition `Localization.lift₂` needs in order to descend the bifunctor from
the K-flat objects of the homotopy categories to the derived categories.

Unlike the `ModuleCat` template, which has only one preservation lemma and supplies the
other variable from the Koszul braiding, both variables here are a preservation lemma of its
own: `quasiIso_of_kFlat` in the first and `quasiIso_of_kFlatLeft` in the second. -/
theorem kFlatToDerived_inverts :
    MorphismProperty.IsInvertedBy₂ (kFlatQuasiIsoLeft F) (kFlatQuasiIso F)
      (kFlatToDerived F) := by
  rintro ⟨K, L⟩ ⟨K', L'⟩ ⟨f, g⟩ ⟨hf, hg⟩
  have h₁ : IsIso ((DerivedCategory.Qh (C := D)).map
      (((homotopyBifunctor F).map f.hom).app L.1)) :=
    isIso_Qh_map_homotopyBifunctor_map_app F f.hom hf L.1 L.2
  have h₂ : IsIso ((DerivedCategory.Qh (C := D)).map
      (((homotopyBifunctor F).obj K'.1).map g.hom)) :=
    isIso_Qh_map_homotopyBifunctor_obj_map F K'.1 K'.2 g.hom hg
  change IsIso ((DerivedCategory.Qh (C := D)).map
        (((homotopyBifunctor F).map f.hom).app L.1) ≫
      (DerivedCategory.Qh (C := D)).map
        (((homotopyBifunctor F).obj K'.1).map g.hom))
  infer_instance

/-- **The derived bifunctor** `D(A) ⥤ D(B) ⥤ D(D)` induced by `F`, obtained by descending
`Tot(F(-, -))` along the two K-flat localizations. -/
noncomputable def derivedBifunctor
    [(kFlatQLeft F).IsLocalization (kFlatQuasiIsoLeft F)]
    [(kFlatQ F).IsLocalization (kFlatQuasiIso F)] :
    DerivedCategory A ⥤ DerivedCategory B ⥤ DerivedCategory D :=
  CategoryTheory.Localization.lift₂ (kFlatToDerived F) (kFlatToDerived_inverts F)
    (kFlatQLeft F) (kFlatQ F)

section Comparison

variable [(kFlatQLeft F).IsLocalization (kFlatQuasiIsoLeft F)]
  [(kFlatQ F).IsLocalization (kFlatQuasiIso F)]

/-- `derivedBifunctor` is induced by `kFlatToDerived`, as a `Lifting₂` datum. -/
noncomputable instance derivedBifunctor_lifting :
    CategoryTheory.Localization.Lifting₂ (kFlatQLeft F) (kFlatQ F)
      (kFlatQuasiIsoLeft F) (kFlatQuasiIso F)
      (kFlatToDerived F) (derivedBifunctor F) := by
  unfold derivedBifunctor
  infer_instance

/-- The natural isomorphism exhibiting `derivedBifunctor` as the descent of
`kFlatToDerived`. -/
noncomputable def derivedBifunctorComparisonIso :=
  CategoryTheory.Localization.Lifting₂.iso (kFlatQLeft F) (kFlatQ F)
    (kFlatQuasiIsoLeft F) (kFlatQuasiIso F) (kFlatToDerived F) (derivedBifunctor F)

/-- **On (left) K-flat representatives the derived bifunctor is the total complex.** This is
what identifies `derivedBifunctor` as the *derived* functor of `F` rather than an arbitrary
exact bifunctor, and it is the `comparison` field of the ringed-site statement of Tag 06YU.

The chain is two `Lifting₂` isomorphisms — the derived descent and the homotopy descent —
followed by `DerivedCategory.quotientCompQhIso` in each of the three variables, which is the
`Q` versus `Qh ∘ quotient` bridge. -/
noncomputable def comparison (K : CochainComplex A ℤ) (L : CochainComplex B ℤ)
    (hK : KFlatLeft F K) (hL : KFlat F L) :
    ((derivedBifunctor F).obj (DerivedCategory.Q.obj K)).obj (DerivedCategory.Q.obj L) ≅
      DerivedCategory.Q.obj (totalComplex F K L) :=
  ((derivedBifunctor F).mapIso
      ((DerivedCategory.quotientCompQhIso A).app K).symm).app
      (DerivedCategory.Q.obj L) ≪≫
    ((derivedBifunctor F).obj ((DerivedCategory.Qh (C := A)).obj
      ((HomotopyCategory.quotient A (ComplexShape.up ℤ)).obj K))).mapIso
      ((DerivedCategory.quotientCompQhIso B).app L).symm ≪≫
    ((derivedBifunctorComparisonIso F).app
        ⟨(HomotopyCategory.quotient A (ComplexShape.up ℤ)).obj K, hK⟩).app
      ⟨(HomotopyCategory.quotient B (ComplexShape.up ℤ)).obj L, hL⟩ ≪≫
    (DerivedCategory.Qh (C := D)).mapIso
      (((CategoryTheory.Localization.Lifting₂.iso
          (HomotopyCategory.quotient A (ComplexShape.up ℤ))
          (HomotopyCategory.quotient B (ComplexShape.up ℤ))
          (HomologicalComplex.homotopyEquivalences A (ComplexShape.up ℤ))
          (HomologicalComplex.homotopyEquivalences B (ComplexShape.up ℤ))
          (totalToHomotopy F) (homotopyBifunctor F)).app K).app L) ≪≫
    (DerivedCategory.quotientCompQhIso D).app (totalComplex F K L)

end Comparison
section Exactness

variable [(kFlatQLeft F).IsLocalization (kFlatQuasiIsoLeft F)]
  [(kFlatQ F).IsLocalization (kFlatQuasiIso F)]

attribute [local instance] kFlatObjects_isTriangulated kFlatObjectsLeft_isTriangulated

/-- The one-sided descent `Φ^R_{K₂}` of Tag 0G6E is a lift of `Tot(F(-, K₂))` along the
homotopy quotient; that is exactly what `bifunctorPhiRFactors` says. -/
noncomputable instance liftingBifunctorPhiR (K₂ : CochainComplex B ℤ) :
    CategoryTheory.Localization.Lifting
      (HomotopyCategory.quotient A (ComplexShape.up ℤ))
      (HomologicalComplex.homotopyEquivalences A (ComplexShape.up ℤ))
      ((totalToHomotopy F).flip.obj K₂)
      (Stacks.SheafOfModules.Tensor.Reduction.bifunctorPhiR F K₂) :=
  ⟨Stacks.SheafOfModules.Tensor.Reduction.bifunctorPhiRFactors F K₂⟩

/-- `(homotopyBifunctor F).flip.obj` at the image of `K₂` is the same lift, so the two are
isomorphic by uniqueness of lifts along a localization. This is the identification that lets
Tag 0G6E's triangulatedness be read on the descended bifunctor. -/
noncomputable def homotopyBifunctorFlipIsoPhiR (K₂ : CochainComplex B ℤ) :
    (homotopyBifunctor F).flip.obj
        ((HomotopyCategory.quotient B (ComplexShape.up ℤ)).obj K₂) ≅
      Stacks.SheafOfModules.Tensor.Reduction.bifunctorPhiR F K₂ :=
  letI := CategoryTheory.Localization.Lifting₂.snd
    (HomotopyCategory.quotient A (ComplexShape.up ℤ))
    (HomotopyCategory.quotient B (ComplexShape.up ℤ))
    (HomologicalComplex.homotopyEquivalences A (ComplexShape.up ℤ))
    (HomologicalComplex.homotopyEquivalences B (ComplexShape.up ℤ))
    (totalToHomotopy F) (homotopyBifunctor F) K₂
  CategoryTheory.Localization.liftNatIso
    (HomotopyCategory.quotient A (ComplexShape.up ℤ))
    (HomologicalComplex.homotopyEquivalences A (ComplexShape.up ℤ))
    ((totalToHomotopy F).flip.obj K₂) ((totalToHomotopy F).flip.obj K₂)
    ((homotopyBifunctor F).flip.obj
      ((HomotopyCategory.quotient B (ComplexShape.up ℤ)).obj K₂))
    (Stacks.SheafOfModules.Tensor.Reduction.bifunctorPhiR F K₂) (Iso.refl _)

/-- The mirror lift, for the second variable: `Φ_{K₁}` lifts `Tot(F(K₁, -))`. -/
noncomputable instance liftingBifunctorPhi (K₁ : CochainComplex A ℤ) :
    CategoryTheory.Localization.Lifting
      (HomotopyCategory.quotient B (ComplexShape.up ℤ))
      (HomologicalComplex.homotopyEquivalences B (ComplexShape.up ℤ))
      ((totalToHomotopy F).obj K₁)
      (Stacks.SheafOfModules.Tensor.Reduction.bifunctorPhi F K₁) :=
  ⟨Stacks.SheafOfModules.Tensor.Reduction.bifunctorPhiFactors F K₁⟩

/-- The mirror identification, for the second variable. Together with
`homotopyBifunctorFlipIsoPhiR` this makes Tag 0G6E's triangulatedness available on the
descended bifunctor in **both** variables — with no braiding, which is what the `ModuleCat`
template needs for its second variable. -/
noncomputable def homotopyBifunctorObjIsoPhi (K₁ : CochainComplex A ℤ) :
    (homotopyBifunctor F).obj
        ((HomotopyCategory.quotient A (ComplexShape.up ℤ)).obj K₁) ≅
      Stacks.SheafOfModules.Tensor.Reduction.bifunctorPhi F K₁ :=
  letI := CategoryTheory.Localization.Lifting₂.fst
    (HomotopyCategory.quotient A (ComplexShape.up ℤ))
    (HomotopyCategory.quotient B (ComplexShape.up ℤ))
    (HomologicalComplex.homotopyEquivalences A (ComplexShape.up ℤ))
    (HomologicalComplex.homotopyEquivalences B (ComplexShape.up ℤ))
    (totalToHomotopy F) (homotopyBifunctor F) K₁
  CategoryTheory.Localization.liftNatIso
    (HomotopyCategory.quotient B (ComplexShape.up ℤ))
    (HomologicalComplex.homotopyEquivalences B (ComplexShape.up ℤ))
    ((totalToHomotopy F).obj K₁) ((totalToHomotopy F).obj K₁)
    ((homotopyBifunctor F).obj
      ((HomotopyCategory.quotient A (ComplexShape.up ℤ)).obj K₁))
    (Stacks.SheafOfModules.Tensor.Reduction.bifunctorPhi F K₁) (Iso.refl _)

omit [HasDerivedCategory A] [HasDerivedCategory B]
  [(kFlatQLeft F).IsLocalization (kFlatQuasiIsoLeft F)]
  [(kFlatQ F).IsLocalization (kFlatQuasiIso F)] in
/-- **Fixing a K-flat right factor gives a shift-compatible triangulated functor** on the
left K-flat objects. Via `homotopyBifunctorFlipIsoPhiR` this is Tag 0G6E's `Φ^R` composed
with the inclusion and `Qh`, each of which is triangulated. -/
theorem kFlatToDerived_exact_left (L : (kFlatObjects F).FullSubcategory) :
    ∃ s : ((kFlatToDerived F).flip.obj L).CommShift ℤ,
      letI := s; ((kFlatToDerived F).flip.obj L).IsTriangulated := by
  obtain ⟨X, hX⟩ := L
  obtain ⟨K₂, rfl⟩ := HomotopyCategory.quotient_obj_surjective X
  let _ := Stacks.SheafOfModules.Tensor.Reduction.bifunctorXiR F K₂
  have _ := Stacks.SheafOfModules.Tensor.Reduction.bifunctorPhiR_isTriangulated F K₂
  let e : (kFlatObjectsLeft F).ι ⋙
      Stacks.SheafOfModules.Tensor.Reduction.bifunctorPhiR F K₂ ⋙ DerivedCategory.Qh ≅
      (kFlatToDerived F).flip.obj
        ⟨(HomotopyCategory.quotient B (ComplexShape.up ℤ)).obj K₂, hX⟩ :=
    Functor.isoWhiskerLeft (kFlatObjectsLeft F).ι
      (Functor.isoWhiskerRight (homotopyBifunctorFlipIsoPhiR F K₂).symm
        (DerivedCategory.Qh (C := D)))
  exact exists_commShift_isTriangulated_of_iso e

omit [HasDerivedCategory A] [HasDerivedCategory B]
  [(kFlatQLeft F).IsLocalization (kFlatQuasiIsoLeft F)]
  [(kFlatQ F).IsLocalization (kFlatQuasiIso F)] in
/-- **Fixing a left K-flat left factor gives a shift-compatible triangulated functor** on the
K-flat objects, by the mirror argument through `homotopyBifunctorObjIsoPhi` and Tag 0G6E's
`Φ`. No braiding is used: the two one-sided descents are both triangulated in Tag06YM. -/
theorem kFlatToDerived_exact_right (K : (kFlatObjectsLeft F).FullSubcategory) :
    ∃ s : ((kFlatToDerived F).obj K).CommShift ℤ,
      letI := s; ((kFlatToDerived F).obj K).IsTriangulated := by
  obtain ⟨X, hX⟩ := K
  obtain ⟨K₁, rfl⟩ := HomotopyCategory.quotient_obj_surjective X
  let _ := Stacks.SheafOfModules.Tensor.Reduction.bifunctorXi F K₁
  have _ := Stacks.SheafOfModules.Tensor.Reduction.bifunctorPhi_isTriangulated F K₁
  let e : (kFlatObjects F).ι ⋙
      Stacks.SheafOfModules.Tensor.Reduction.bifunctorPhi F K₁ ⋙ DerivedCategory.Qh ≅
      (kFlatToDerived F).obj
        ⟨(HomotopyCategory.quotient A (ComplexShape.up ℤ)).obj K₁, hX⟩ :=
    Functor.isoWhiskerLeft (kFlatObjects F).ι
      (Functor.isoWhiskerRight (homotopyBifunctorObjIsoPhi F K₁).symm
        (DerivedCategory.Qh (C := D)))
  exact exists_commShift_isTriangulated_of_iso e

attribute [local instance] kFlatQuasiIso_hasLeftCalculusOfFractions
  kFlatQuasiIsoLeft_hasLeftCalculusOfFractions

omit [HasDerivedCategory A] [HasDerivedCategory D]
  [(kFlatQLeft F).IsLocalization (kFlatQuasiIsoLeft F)] in
/-- The K-flat objects are essentially surjective onto the derived category. -/
theorem kFlatQ_essSurj : (kFlatQ F).EssSurj :=
  CategoryTheory.Localization.essSurj (kFlatQ F) (kFlatQuasiIso F)

omit [HasDerivedCategory B] [HasDerivedCategory D]
  [(kFlatQ F).IsLocalization (kFlatQuasiIso F)] in
/-- The mirror, on the left. -/
theorem kFlatQLeft_essSurj : (kFlatQLeft F).EssSurj :=
  CategoryTheory.Localization.essSurj (kFlatQLeft F) (kFlatQuasiIsoLeft F)

attribute [local instance] kFlatQ_essSurj kFlatQLeft_essSurj

omit [HasDerivedCategory A] [HasDerivedCategory D]
  [(kFlatQLeft F).IsLocalization (kFlatQuasiIsoLeft F)] in
/-- Arrows of the derived category are essentially surjective images of arrows between
K-flat objects; needed to descend triangulatedness along the localization. -/
theorem kFlatQ_mapArrow_essSurj : (kFlatQ F).mapArrow.EssSurj :=
  CategoryTheory.Localization.essSurj_mapArrow (kFlatQ F) (kFlatQuasiIso F)

omit [HasDerivedCategory B] [HasDerivedCategory D]
  [(kFlatQ F).IsLocalization (kFlatQuasiIso F)] in
/-- The mirror, on the left. -/
theorem kFlatQLeft_mapArrow_essSurj : (kFlatQLeft F).mapArrow.EssSurj :=
  CategoryTheory.Localization.essSurj_mapArrow (kFlatQLeft F) (kFlatQuasiIsoLeft F)

attribute [local instance] kFlatQ_mapArrow_essSurj kFlatQLeft_mapArrow_essSurj

/-- **`exact_left`: tensoring in the left variable is exact.** Transported from
`kFlatToDerived_exact_left` along the localization, at a K-flat preimage of the fixed object
of `D(B)`. -/
theorem derivedBifunctor_exact_left (L : DerivedCategory B) :
    ∃ s : ((derivedBifunctor F).flip.obj L).CommShift ℤ,
      letI := s; ((derivedBifunctor F).flip.obj L).IsTriangulated := by
  let K := (kFlatQ F).objPreimage L
  obtain ⟨_, _⟩ := kFlatToDerived_exact_left F K
  let _ := CategoryTheory.Localization.Lifting₂.snd (kFlatQLeft F) (kFlatQ F)
    (kFlatQuasiIsoLeft F) (kFlatQuasiIso F) (kFlatToDerived F) (derivedBifunctor F) K
  let _ := Functor.commShiftOfLocalization (kFlatQLeft F) (kFlatQuasiIsoLeft F) ℤ
    ((kFlatToDerived F).flip.obj K) ((derivedBifunctor F).flip.obj ((kFlatQ F).obj K))
  have _ := Functor.isTriangulated_of_localization (kFlatQLeft F) (kFlatQuasiIsoLeft F)
    ((kFlatToDerived F).flip.obj K) ((derivedBifunctor F).flip.obj ((kFlatQ F).obj K))
  let e := (derivedBifunctor F).flip.mapIso ((kFlatQ F).objObjPreimageIso L)
  exact exists_commShift_isTriangulated_of_iso e

/-- **`exact_right`: tensoring in the right variable is exact.** The mirror, through
`kFlatToDerived_exact_right` and `Lifting₂.fst`. The `ModuleCat` template obtains this from
its braiding; here it is the symmetric argument, with no symmetry of `F` involved. -/
theorem derivedBifunctor_exact_right (K : DerivedCategory A) :
    ∃ s : ((derivedBifunctor F).obj K).CommShift ℤ,
      letI := s; ((derivedBifunctor F).obj K).IsTriangulated := by
  let K' := (kFlatQLeft F).objPreimage K
  obtain ⟨_, _⟩ := kFlatToDerived_exact_right F K'
  let _ := CategoryTheory.Localization.Lifting₂.fst (kFlatQLeft F) (kFlatQ F)
    (kFlatQuasiIsoLeft F) (kFlatQuasiIso F) (kFlatToDerived F) (derivedBifunctor F) K'
  let _ := Functor.commShiftOfLocalization (kFlatQ F) (kFlatQuasiIso F) ℤ
    ((kFlatToDerived F).obj K') ((derivedBifunctor F).obj ((kFlatQLeft F).obj K'))
  have _ := Functor.isTriangulated_of_localization (kFlatQ F) (kFlatQuasiIso F)
    ((kFlatToDerived F).obj K') ((derivedBifunctor F).obj ((kFlatQLeft F).obj K'))
  let e := (derivedBifunctor F).mapIso ((kFlatQLeft F).objObjPreimageIso K)
  exact exists_commShift_isTriangulated_of_iso e

end Exactness

end DerivedDescent

/-! ### Naturality of the K-flat comparison -/

section Naturality

variable [HasDerivedCategory A] [HasDerivedCategory B] [HasDerivedCategory D]
  [(kFlatQLeft F).IsLocalization (kFlatQuasiIsoLeft F)]
  [(kFlatQ F).IsLocalization (kFlatQuasiIso F)]

/-- The left K-flat cochain complexes, as an object property of `CochainComplex A ℤ`. -/
abbrev kFlatComplexesLeft : ObjectProperty (CochainComplex A ℤ) := fun K ↦ KFlatLeft F K

/-- The K-flat cochain complexes, as an object property of `CochainComplex B ℤ`. -/
abbrev kFlatComplexes : ObjectProperty (CochainComplex B ℤ) := fun K ↦ KFlat F K

/-- The homotopy quotient, from left K-flat complexes to left K-flat objects. -/
noncomputable abbrev kFlatQuotientLeft :
    (kFlatComplexesLeft F).FullSubcategory ⥤ (kFlatObjectsLeft F).FullSubcategory :=
  (kFlatObjectsLeft F).lift
    ((kFlatComplexesLeft F).ι ⋙ HomotopyCategory.quotient A (ComplexShape.up ℤ))
    (fun K ↦ K.2)

/-- The homotopy quotient, from K-flat complexes to K-flat objects. -/
noncomputable abbrev kFlatQuotient :
    (kFlatComplexes F).FullSubcategory ⥤ (kFlatObjects F).FullSubcategory :=
  (kFlatObjects F).lift
    ((kFlatComplexes F).ι ⋙ HomotopyCategory.quotient B (ComplexShape.up ℤ))
    (fun K ↦ K.2)

/-- Left K-flat complexes viewed in `D(A)`. -/
noncomputable abbrev kFlatComplexQLeft :=
  (kFlatComplexesLeft F).ι ⋙ (DerivedCategory.Q (C := A))

/-- K-flat complexes viewed in `D(B)`. -/
noncomputable abbrev kFlatComplexQ :=
  (kFlatComplexes F).ι ⋙ (DerivedCategory.Q (C := B))

/-- Taking the homotopy quotient and then into `D(A)` is going into `D(A)` directly. -/
noncomputable def kFlatQuotientCompQIsoLeft :
    kFlatQuotientLeft F ⋙ kFlatQLeft F ≅ kFlatComplexQLeft F :=
  Functor.isoWhiskerLeft (kFlatComplexesLeft F).ι (DerivedCategory.quotientCompQhIso A)

/-- The mirror, in `D(B)`. -/
noncomputable def kFlatQuotientCompQIso :
    kFlatQuotient F ⋙ kFlatQ F ≅ kFlatComplexQ F :=
  Functor.isoWhiskerLeft (kFlatComplexes F).ι (DerivedCategory.quotientCompQhIso B)

/-- `Tot(F(-, -))` on complexes, landing in `D(D)`. -/
noncomputable abbrev complexToDerived :=
  F.map₂HomologicalComplex (ComplexShape.up ℤ) (ComplexShape.up ℤ) (ComplexShape.up ℤ) ⋙
    (Functor.whiskeringRight _ _ _).obj (DerivedCategory.Q (C := D))

/-- Its restriction to the (left) K-flat complexes. -/
noncomputable abbrev kFlatComplexToDerived :=
  (((Functor.whiskeringLeft₂ (DerivedCategory D)).obj (kFlatComplexesLeft F).ι).obj
    (kFlatComplexes F).ι).obj (complexToDerived F)

/-- **The K-flat comparison as a natural isomorphism of bifunctors** on the (left) K-flat
complexes. Bundling it this way is what makes `comparison_naturality` a single application
of naturality, rather than five squares chased by hand. -/
noncomputable def derivedComparisonNatIso :
    (((Functor.whiskeringLeft₂ (DerivedCategory D)).obj (kFlatComplexQLeft F)).obj
        (kFlatComplexQ F)).obj (derivedBifunctor F) ≅
      kFlatComplexToDerived F :=
  let qL := kFlatQuotientCompQIsoLeft F
  let qR := kFlatQuotientCompQIso F
  let h := CategoryTheory.Localization.Lifting₂.iso
    (HomotopyCategory.quotient A (ComplexShape.up ℤ))
    (HomotopyCategory.quotient B (ComplexShape.up ℤ))
    (HomologicalComplex.homotopyEquivalences A (ComplexShape.up ℤ))
    (HomologicalComplex.homotopyEquivalences B (ComplexShape.up ℤ))
    (totalToHomotopy F) (homotopyBifunctor F)
  ((((Functor.whiskeringLeft₂ (DerivedCategory D)).mapIso qL.symm).app
      (kFlatComplexQ F)).app (derivedBifunctor F)) ≪≫
    ((((Functor.whiskeringLeft₂ (DerivedCategory D)).obj
        (kFlatQuotientLeft F ⋙ kFlatQLeft F)).mapIso qR.symm).app
      (derivedBifunctor F)) ≪≫
    (((Functor.whiskeringLeft₂ (DerivedCategory D)).obj (kFlatQuotientLeft F)).obj
      (kFlatQuotient F)).mapIso (derivedBifunctorComparisonIso F) ≪≫
    (((Functor.whiskeringLeft₂ (DerivedCategory D)).obj (kFlatComplexesLeft F).ι).obj
      (kFlatComplexes F).ι).mapIso
      (Functor.isoWhiskerRight h ((Functor.whiskeringRight _ _ _).obj
          (DerivedCategory.Qh (C := D))) ≪≫
        Functor.isoWhiskerLeft
          (F.map₂HomologicalComplex (ComplexShape.up ℤ) (ComplexShape.up ℤ)
            (ComplexShape.up ℤ))
          ((Functor.whiskeringRight _ _ _).mapIso
            (DerivedCategory.quotientCompQhIso D)))

omit [HasDerivedCategory A] [HasDerivedCategory B]
  [(kFlatQLeft F).IsLocalization (kFlatQuasiIsoLeft F)]
  [(kFlatQ F).IsLocalization (kFlatQuasiIso F)] in
/-- `HomologicalComplex.mapBifunctorMap_comp` at a pair of identities, after `DerivedCategory.Q`,
in the spelling `comparison_naturality`'s right-hand side actually has. Stated separately
because the merge must fire on `Q.map a ≫ Q.map b` directly; left to `← Functor.map_comp`
inside a `simp` set it does not. -/
theorem Q_map_mapBifunctorMap_merge
    {K K' : CochainComplex A ℤ} {L L' : CochainComplex B ℤ} (f : K ⟶ K') (g : L ⟶ L') :
    DerivedCategory.Q.map (HomologicalComplex.mapBifunctorMap f (𝟙 L) F
          (ComplexShape.up ℤ)) ≫
        DerivedCategory.Q.map (HomologicalComplex.mapBifunctorMap (𝟙 K') g F
          (ComplexShape.up ℤ)) =
      DerivedCategory.Q.map (HomologicalComplex.mapBifunctorMap f g F
        (ComplexShape.up ℤ)) := by
  rw [← Functor.map_comp, HomologicalComplex.mapBifunctorMap_comp, Category.comp_id,
    Category.id_comp]

/-- The bundled natural isomorphism is, componentwise, the comparison. -/
theorem derivedComparisonNatIso_app (K : CochainComplex A ℤ) (L : CochainComplex B ℤ)
    (hK : KFlatLeft F K) (hL : KFlat F L) :
    ((derivedComparisonNatIso F).app ⟨K, hK⟩).app ⟨L, hL⟩ = comparison F K L hK hL :=
  rfl

/-- **The K-flat comparison is natural in both complexes.** This is 06YU's
`comparison_naturality`, and the last field of the derived tensor product outside the
one-sided comparisons. -/
theorem comparison_naturality {K K' : CochainComplex A ℤ} {L L' : CochainComplex B ℤ}
    (f : K ⟶ K') (g : L ⟶ L')
    (hK : KFlatLeft F K) (hK' : KFlatLeft F K')
    (hL : KFlat F L) (hL' : KFlat F L') :
    ((derivedBifunctor F).map (DerivedCategory.Q.map f)).app (DerivedCategory.Q.obj L) ≫
        ((derivedBifunctor F).obj (DerivedCategory.Q.obj K')).map
          (DerivedCategory.Q.map g) ≫
        (comparison F K' L' hK' hL').hom =
      (comparison F K L hK hL).hom ≫
        DerivedCategory.Q.map
          (HomologicalComplex.mapBifunctorMap f g F (ComplexShape.up ℤ)) := by
  refine Eq.trans ?_ (congrArg (fun t ↦ (comparison F K L hK hL).hom ≫ t)
    (Q_map_mapBifunctorMap_merge F f g))
  let f' : (⟨K, hK⟩ : (kFlatComplexesLeft F).FullSubcategory) ⟶ ⟨K', hK'⟩ := ⟨f⟩
  let g' : (⟨L, hL⟩ : (kFlatComplexes F).FullSubcategory) ⟶ ⟨L', hL'⟩ := ⟨g⟩
  have h := (Functor.uncurry.map (derivedComparisonNatIso F).hom).naturality
    ((f', g') : (⟨K, hK⟩, ⟨L, hL⟩) ⟶ (⟨K', hK'⟩, ⟨L', hL'⟩))
  simp only [Functor.uncurry_obj_obj, Functor.whiskeringLeft₂_obj_obj_obj_obj_obj,
    Functor.comp_obj, ObjectProperty.ι_obj, Functor.whiskeringRight_obj_obj,
    Functor.uncurry_obj_map, Functor.whiskeringLeft₂_obj_obj_obj_map_app, Functor.comp_map,
    ObjectProperty.ι_map, Functor.whiskeringLeft₂_obj_obj_obj_obj_map, Functor.uncurry_map_app,
    Category.assoc, Functor.whiskeringRight_obj_map, Functor.whiskerRight_app,
    Functor.map₂HomologicalComplex_map_app, Functor.map₂HomologicalComplex_obj_map,
    f', g'] at h
  exact h

end Naturality

end CochainComplex.KFlatBifunctor

end

end
