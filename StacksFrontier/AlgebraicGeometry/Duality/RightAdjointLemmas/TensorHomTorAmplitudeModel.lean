module

public import StacksFrontier.AlgebraicGeometry.Duality.RightAdjointLemmas.ExactSupportDerivedInternalHomBifunctor
public import StacksFrontier.AlgebraicGeometry.Duality.RightAdjointLemmas.ExactSupportSitePseudoCoherent
public import StacksFrontier.AlgebraicGeometry.Duality.RightAdjointLemmas.ExactSupportSiteTensorHomDiagonalCurrying
public import StacksFrontier.AlgebraicGeometry.Duality.RightAdjointLemmas.TensorHomTorAmplitudeIso
public import StacksFrontier.Topology.Sheaves.Cohomology.DerivedPushforward.ClosedEmbeddingProjectionFormulaDerived
public import StacksFrontier.Topology.Sheaves.Cohomology.InternalHom.DerivedTensorHomDiagonalModels
public import StacksFrontier.Topology.Sheaves.Cohomology.InternalHom.DerivedTensorHomDiagonalPseudoCoherent
public import StacksFrontier.Topology.Sheaves.Cohomology.TorAmplitude.LocalTorAmplitudeGE
import StacksCore.Tactic.StacksAttribute

/-!
# [Stacks, Tag 0E2N]: the tensor–Hom map for a pseudo-coherent closed immersion

Let `i : Z ⟶ X` be a pseudo-coherent closed immersion of schemes, `M ∈ D_QCoh(𝒪_X)` locally of
Tor amplitude in `[a, ∞)` and `K ∈ D⁺_QCoh(𝒪_X)`. [Stacks, Tag 0E2N] asserts that the canonical
map

`R ℰom(𝒪_Z, K) ⊗^L_{𝒪_Z} Li^*M ⟶ R ℰom(𝒪_Z, K ⊗^L_{𝒪_X} M)`

is an isomorphism in `D(𝒪_Z)`. This file constructs the map on models and proves the assertion,
as `Stacks.Duality.TensorHomTorAmplitude.isIso_tensorDerivedSheafHomModelMap_of_closedImmersion`.

## The construction

Choose a K-injective model `I` of `K`, a K-flat model `A` of `M`, and a K-injective resolution
`q : Tot(A ⊗ I) ⟶ J`. On `Z`, `R ℰom(𝒪_Z, K)` is the class of `ℰom^•_Z(𝒪_Z, ℰom(𝒪_Z, I))`,
`Li^*M` the class of the K-flat `i^*A`, and `R ℰom(𝒪_Z, K ⊗^L M)` the class of
`ℰom^•_Z(𝒪_Z, ℰom(𝒪_Z, J))`. The canonical map is the class of the morphism of complexes `zMap`
whose pushforward to `X` is

`i_*Tot(ℰom^•_Z(𝒪_Z, ℰom(𝒪_Z, I)) ⊗ i^*A) ≅ Tot(A ⊗ ℰom^•(i_* 𝒪_Z, I))`
`⟶ ℰom^•(i_* 𝒪_Z, J) ≅ i_* ℰom^•_Z(𝒪_Z, ℰom(𝒪_Z, J))`,

the isomorphisms being the complex-level projection formula of [Stacks, Tag 0B55], the
complex-level [Stacks, Tag 0E2I] and the Koszul symmetry, and the middle arrow the morphism of
[Stacks, Tag 0BYR], `a ⊗ φ ↦ (s ↦ a ⊗ φ(s))` followed by `q`. Such a morphism exists and is
unique because `i_*` is fully faithful on complexes of modules. This is the map of the source's
proof, the counit `Ri_* R ℰom(𝒪_Z, K) ⟶ K` tensored with the identity of `M` and read through the
projection formula, written on representatives.

The adjunction-theoretic description of the same map is
`Stacks.Duality.TensorHomTorAmplitude.tensorDerivedSheafHomMap`; the two are not compared in
this library.

## The proof

After pushforward the map is, up to isomorphisms of complexes, the morphism of
[Stacks, Tag 0BYR] at models of `(M, K, Ri_* 𝒪_Z)`, so it is a quasi-isomorphism exactly when the
diagonal of [Stacks, Tag 0BYS] there is invertible
(`AlgebraicGeometry.RingedSite.isIso_derivedTensorHomDiagonal_iff_quasiIso_ofModels`). That
diagonal is invertible by the site form of [Stacks, Tag 0ATK] part (3),
`RingedSite.isIso_derivedTensorHomDiagonal_of_isPseudoCoherent_of_hasTorAmplitudeGE`:
`Ri_* 𝒪_Z` is pseudo-coherent ([Stacks, Tag 08FT],
`AlgebraicGeometry.Scheme.isPseudoCoherentSite_pushforward_derivedStructureSheaf`), `K` is
bounded below, and `M` has Tor amplitude in `[a, ∞)`, which the local hypothesis gives by
`Stacks.Cohomology.TorAmplitude.hasTorAmplitudeGE_of_locallyHasTorAmplitudeGE`. Finally the
derived pushforward along `i` reflects isomorphisms ([Stacks, Tag 08KS]).

## Implementation notes

The import of `LocalTorAmplitudeGE` brings the locally small derived category of sheaves of
modules into scope as a global instance; everything here, as everywhere in this development, is
stated at `HasDerivedCategory.standard`, which is therefore given priority.

The ringed-space spelling `structureSheafRing S.X` and the site spelling
`(ambientRingedSite S).ringSheaf` of the same sheaf of rings are definitionally but not reducibly
equal, so the statements below name their models with explicit types and the one composite that
crosses the two spellings is handled by `isIso_map_comp₃`, stated in bare categories.

## References

* [Stacks Project, Tag 0E2N](https://stacks.math.columbia.edu/tag/0E2N)
* [Stacks Project, Tag 0BYR](https://stacks.math.columbia.edu/tag/0BYR)
* [Stacks Project, Tag 0BYS](https://stacks.math.columbia.edu/tag/0BYS)
* [Stacks Project, Tag 0ATK](https://stacks.math.columbia.edu/tag/0ATK)
* [Stacks Project, Tag 0B55](https://stacks.math.columbia.edu/tag/0B55)
* [Stacks Project, Tag 0E2I](https://stacks.math.columbia.edu/tag/0E2I)
* [Stacks Project, Tag 08FT](https://stacks.math.columbia.edu/tag/08FT)
* [Stacks Project, Tag 08KS](https://stacks.math.columbia.edu/tag/08KS)
-/

@[expose] public noncomputable section

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits Opposite
open RingedSpaceModuleAdjunction
open Stacks.DerivedTensor.RingedSite

attribute [local instance 2000] HasDerivedCategory.standard

universe u

namespace Stacks.Duality.TensorHomTorAmplitude

variable (S : ClosedQuotientMorphismOfRingedSpaces.{u})

/-- `𝒪_Z` placed in degree zero, at the spelling `RingedSite.derivedStructureSheaf` uses. -/
abbrev structureComplexZ :
    CochainComplex (SheafOfModules.{u} (structureSheafRing S.Z)) ℤ :=
  (Stacks.SheafOfModules.ringedSite S.Z.sheaf).structureSheafComplex

/-- `i_* 𝒪_Z` placed in degree zero, as a complex of `𝒪_X`-modules. -/
abbrev pushforwardStructureComplexX :
    CochainComplex (SheafOfModules.{u} (structureSheafRing S.X)) ℤ :=
  ((modulePushforward S.i).mapHomologicalComplex (ComplexShape.up ℤ)).obj (structureComplexZ S)

/-- The class of `i_* 𝒪_Z` is `Ri_* 𝒪_Z`, `i_*` being exact. -/
def pushforwardStructureComplexXIso :
    DerivedCategory.Q.obj (pushforwardStructureComplexX S) ≅ pushforwardDerivedStructureSheaf S :=
  ((modulePushforward S.i).mapDerivedCategoryFactors.app (structureComplexZ S)).symm

variable (K M : DerivedCategory (SheafOfModules.{u} (structureSheafRing S.X)))

/-- The chosen K-injective model `I` of `K`. -/
abbrev injModel :
    CochainComplex (SheafOfModules.{u} (structureSheafRing S.X)) ℤ :=
  (ambientRingedSite S).kInjectiveModel K

/-- The chosen K-flat model `A` of `M`. -/
abbrev flatModel :
    CochainComplex (SheafOfModules.{u} (structureSheafRing S.X)) ℤ :=
  (ambientRingedSite S).kFlatModel M

/-- The chosen model of `K` represents it. -/
def injModelIso : DerivedCategory.Q.obj (injModel S K) ≅ K :=
  (ambientRingedSite S).kInjectiveModelIso K

/-- The chosen model of `M` represents it. -/
def flatModelIso : DerivedCategory.Q.obj (flatModel S M) ≅ M :=
  (ambientRingedSite S).kFlatModelIso M

/-- The chosen model `I` of `K` is K-injective. -/
instance isKInjective_injModel :
    CochainComplex.IsKInjective
      (C := SheafOfModules.{u} (structureSheafRing S.X)) (injModel S K) :=
  (ambientRingedSite S).isKInjective_kInjectiveModel K

/-- The chosen K-injective resolution `J` of `Tot(A ⊗ I)`. -/
abbrev tensorInjModel :
    CochainComplex (SheafOfModules.{u} (structureSheafRing S.X)) ℤ :=
  (ambientRingedSite S).kInjectiveResolution.obj
    ((ambientRingedSite S).tensorTotal (flatModel S M) (injModel S K))

/-- The augmentation `q : Tot(A ⊗ I) ⟶ J`, a quasi-isomorphism. -/
abbrev tensorInjAug :
    (ambientRingedSite S).tensorTotal (flatModel S M) (injModel S K) ⟶ tensorInjModel S K M :=
  (ambientRingedSite S).kInjectiveAugmentation.app _

/-- The resolution `J` of `Tot(A ⊗ I)` is K-injective. -/
instance isKInjective_tensorInjModel :
    CochainComplex.IsKInjective
      (C := SheafOfModules.{u} (structureSheafRing S.X))
      (tensorInjModel S K M) :=
  (inferInstance : ((ambientRingedSite S).kInjectiveResolution.obj
    ((ambientRingedSite S).tensorTotal (flatModel S M) (injModel S K))).IsKInjective)

/-- The complex-level morphism of [Stacks, Tag 0BYR] at these models, out of `i_* 𝒪_Z`:
`Tot(A ⊗ ℰom^•(i_* 𝒪_Z, I)) ⟶ ℰom^•(i_* 𝒪_Z, Tot(A ⊗ I)) ⟶ ℰom^•(i_* 𝒪_Z, J)`, sending
`a ⊗ φ` to `s ↦ a ⊗ φ(s)` and then applying `q`. -/
abbrev omega :
    (ambientRingedSite S).tensorTotal (flatModel S M)
        ((ambientRingedSite S).sheafHomComplex (pushforwardStructureComplexX S)
          (injModel S K)).obj ⟶
      ((ambientRingedSite S).sheafHomComplex (pushforwardStructureComplexX S)
        (tensorInjModel S K M)).obj :=
  (ambientRingedSite S).derivedTensorHomMapOfModels (tensorInjAug S K M)

/-- The augmentation is invertible in the derived category. -/
theorem isIso_Q_map_tensorInjAug : IsIso (DerivedCategory.Q.map (tensorInjAug S K M)) :=
  (DerivedCategory.isIso_Q_map_iff_quasiIso _ _).2 inferInstance

/-- **The diagonal of [Stacks, Tag 0BYS] at `(M, K, Ri_* 𝒪_Z)` is invertible exactly when
`omega` is a quasi-isomorphism**: `omega` is the complex-level morphism of [Stacks, Tag 0BYR] at
one admissible choice of models, the K-flat `A`, the K-injective `I` and `J`, and the complex
`i_* 𝒪_Z` representing `Ri_* 𝒪_Z`. -/
theorem quasiIso_omega_iff :
    IsIso ((ambientRingedSite S).derivedTensorHomDiagonal M K
        (pushforwardDerivedStructureSheaf S)) ↔
      QuasiIso (omega S K M) :=
  have := (ambientRingedSite S).isKInjective_kInjectiveModel K
  (ambientRingedSite S).isIso_derivedTensorHomDiagonal_iff_quasiIso_ofModels M K
    (pushforwardDerivedStructureSheaf S) ((ambientRingedSite S).isKFlat_kFlatModel M)
    ((ambientRingedSite S).kFlatModelIso M) ((ambientRingedSite S).kInjectiveModelIso K)
    (pushforwardStructureComplexXIso S) (tensorInjAug S K M) (isIso_Q_map_tensorInjAug S K M)

/-! ### The complex-level map on `Z` -/

/-- `ℰom^•_Z(𝒪_Z, ℰom(𝒪_Z, F))`, the model of `R ℰom(𝒪_Z, F)` used on `Z` for a K-injective
`F`. -/
abbrev homZ
    (F : CochainComplex (SheafOfModules.{u} (structureSheafRing S.X)) ℤ) :
    CochainComplex (SheafOfModules.{u} (structureSheafRing S.Z)) ℤ :=
  (Stacks.SheafOfModules.sheafHomComplex S.Z.sheaf (structureComplexZ S)
    ((S.sheafHomExactSupport.mapHomologicalComplex (ComplexShape.up ℤ)).obj F)).obj

/-- The complex-level comparison `i_* ℰom^•_Z(𝒪_Z, ℰom(𝒪_Z, F)) ≅ ℰom^•_X(i_* 𝒪_Z, F)` of
[Stacks, Tag 0E2I]. -/
abbrev pushHomIso
    (F : CochainComplex (SheafOfModules.{u} (structureSheafRing S.X)) ℤ) :
    ((modulePushforward S.i).mapHomologicalComplex (ComplexShape.up ℤ)).obj (homZ S F) ≅
      ((ambientRingedSite S).sheafHomComplex (pushforwardStructureComplexX S) F).obj :=
  (S.pushforwardSheafHomComplex).iso (structureComplexZ S) F

/-- The model on `Z` of the source of the map: `Tot(ℰom^•_Z(𝒪_Z, ℰom(𝒪_Z, I)) ⊗ i^*A)`. -/
abbrev sourceZ :
    CochainComplex (SheafOfModules.{u} (structureSheafRing S.Z)) ℤ :=
  ((Stacks.SheafOfModules.Tensor.tensorComplex S.Z.sheaf).obj (homZ S (injModel S K))).obj
    ((Stacks.Cohomology.DerivedPullbackTensor.pullbackComplex S.i).obj (flatModel S M))

/-- The model on `Z` of the target of the map: `ℰom^•_Z(𝒪_Z, ℰom(𝒪_Z, J))`. -/
abbrev targetZ :
    CochainComplex (SheafOfModules.{u} (structureSheafRing S.Z)) ℤ :=
  homZ S (tensorInjModel S K M)

/-- The pushforward of the source model identified with the source of `omega`: the inverse of
the complex-level projection formula of [Stacks, Tag 0B55], the comparison of
[Stacks, Tag 0E2I] in the first factor, the Koszul symmetry of the total tensor complex, and the
comparison of the two total tensor complexes. -/
def pushedSourceIso :
    ((modulePushforward S.i).mapHomologicalComplex (ComplexShape.up ℤ)).obj (sourceZ S K M) ≅
      (ambientRingedSite S).tensorTotal (flatModel S M)
        ((ambientRingedSite S).sheafHomComplex (pushforwardStructureComplexX S)
          (injModel S K)).obj :=
  (Stacks.Cohomology.ClosedEmbeddingProjectionFormulaComplexes.complexProjectionFormulaIso S.i
      S.isClosedEmbedding (homZ S (injModel S K)) (flatModel S M)).symm ≪≫
    ((Stacks.SheafOfModules.Tensor.tensorComplex S.X.sheaf).mapIso
      (pushHomIso S (injModel S K))).app (flatModel S M) ≪≫
    Stacks.SheafOfModules.Tensor.tensorComplexFlipIso S.X.sheaf _ (flatModel S M) ≪≫
    ((ambientRingedSite S).tensorTotalIsoTensorComplex (flatModel S M) _).symm

/-- The complex-level map on `X` that the canonical map pushes forward to:

`i_*Tot(ℰom^•_Z(𝒪_Z, ℰom(𝒪_Z, I)) ⊗ i^*A) ≅ Tot(A ⊗ ℰom^•(i_* 𝒪_Z, I))`
`⟶ ℰom^•(i_* 𝒪_Z, J) ≅ i_* ℰom^•_Z(𝒪_Z, ℰom(𝒪_Z, J))`,

the middle arrow being `omega`, the complex-level morphism of [Stacks, Tag 0BYR]. -/
def pushedMap :
    ((modulePushforward S.i).mapHomologicalComplex (ComplexShape.up ℤ)).obj (sourceZ S K M) ⟶
      ((modulePushforward S.i).mapHomologicalComplex (ComplexShape.up ℤ)).obj (targetZ S K M) :=
  (pushedSourceIso S K M).hom ≫ omega S K M ≫ (pushHomIso S (tensorInjModel S K M)).inv

omit S K M in
/-- A functor sends a threefold composite of morphisms it inverts to an isomorphism; stated in a
bare category so that it applies across the two spellings of the category of modules. -/
theorem isIso_map_comp₃ {C D : Type*} [Category C] [Category D] (F : C ⥤ D) {a b c d : C}
    (f : a ⟶ b) (g : b ⟶ c) (h : c ⟶ d) (hf : IsIso (F.map f)) (hg : IsIso (F.map g))
    (hh : IsIso (F.map h)) : IsIso (F.map (f ≫ g ≫ h)) := by
  rw [F.map_comp, F.map_comp]
  infer_instance

/-- `pushedMap` is a quasi-isomorphism as soon as `omega` is: its other two factors are
isomorphisms of complexes. -/
theorem isIso_Q_map_pushedMap (h : QuasiIso (omega S K M)) :
    IsIso (DerivedCategory.Q.map (pushedMap S K M)) :=
  isIso_map_comp₃ DerivedCategory.Q _ _ _
    (DerivedCategory.Q.mapIso (pushedSourceIso S K M)).isIso_hom
    ((DerivedCategory.isIso_Q_map_iff_quasiIso _ _).2 h)
    (DerivedCategory.Q.mapIso (pushHomIso S (tensorInjModel S K M))).isIso_inv

/-- `i_*` is fully faithful on complexes: the preimage is taken degreewise. -/
def pushforwardComplexFullyFaithful :
    ((modulePushforward S.i).mapHomologicalComplex (ComplexShape.up ℤ)).FullyFaithful where
  preimage {A B} f :=
    { f := fun n ↦ S.fullyFaithfulModulePushforward.preimage (f.f n)
      comm' := fun i j hij ↦ S.fullyFaithfulModulePushforward.map_injective (by
        simp only [Functor.map_comp, Functor.FullyFaithful.map_preimage]
        exact f.comm' i j hij) }
  map_preimage {A B} f := HomologicalComplex.hom_ext _ _ fun n ↦ by
    exact S.fullyFaithfulModulePushforward.map_preimage (f.f n)
  preimage_map {A B} f := HomologicalComplex.hom_ext _ _ fun n ↦ by
    exact S.fullyFaithfulModulePushforward.preimage_map (f.f n)

/-- **The complex-level form of the canonical map of [Stacks, Tag 0E2N]**, a morphism of
complexes of `𝒪_Z`-modules

`Tot(ℰom^•_Z(𝒪_Z, ℰom(𝒪_Z, I)) ⊗_{𝒪_Z} i^*A) ⟶ ℰom^•_Z(𝒪_Z, ℰom(𝒪_Z, J))`:

the unique morphism whose pushforward is `pushedMap`, `i_*` being fully faithful on complexes
of modules along a closed quotient morphism (`pushforwardComplexFullyFaithful`). On sections it
sends `φ ⊗ a` to `s ↦ q(φ(s) ⊗ a)` up to the Koszul sign, which is the source's description of the
canonical map: the counit `Ri_* R ℰom(𝒪_Z, K) ⟶ K` tensored with `M`, read through the
projection formula. -/
def zMap : sourceZ S K M ⟶ targetZ S K M :=
  (pushforwardComplexFullyFaithful S).preimage (pushedMap S K M)

/-- The pushforward of `zMap` is `pushedMap`. -/
theorem pushforward_zMap :
    ((modulePushforward S.i).mapHomologicalComplex (ComplexShape.up ℤ)).map (zMap S K M) =
      pushedMap S K M :=
  (pushforwardComplexFullyFaithful S).map_preimage _

/-- `zMap` is a quasi-isomorphism as soon as `omega` is: its pushforward is, and the derived
pushforward along `i` reflects isomorphisms. -/
theorem isIso_Q_map_zMap (h : QuasiIso (omega S K M)) :
    IsIso (DerivedCategory.Q.map (zMap S K M)) := by
  refine Stacks.Duality.ExactSupportBaseChange.isIso_of_isIso_modulePushforward_map S _ ?_
  have hn := ((modulePushforward S.i).mapDerivedCategoryFactors).hom.naturality (zMap S K M)
  simp only [Functor.comp_map, pushforward_zMap] at hn
  have e : (modulePushforward S.i).mapDerivedCategory.map (DerivedCategory.Q.map (zMap S K M)) =
      ((modulePushforward S.i).mapDerivedCategoryFactors).hom.app (sourceZ S K M) ≫
        DerivedCategory.Q.map (pushedMap S K M) ≫
          ((modulePushforward S.i).mapDerivedCategoryFactors).inv.app (targetZ S K M) := by
    rw [← reassoc_of% hn, Iso.hom_inv_id_app]
    exact (Category.comp_id _).symm
  rw [e]
  have := isIso_Q_map_pushedMap S K M h
  infer_instance

/-! ### The comparisons with the derived objects -/

/-- `R ℰom(𝒪_Z, -)` at the class of a K-injective complex `F` is the class of
`ℰom^•_Z(𝒪_Z, ℰom(𝒪_Z, F))`. -/
def derivedSheafHomExactSupportModelIso
    (F : CochainComplex (SheafOfModules.{u} (structureSheafRing S.X)) ℤ)
    [F.IsKInjective] :
    S.derivedSheafHomExactSupport.obj (DerivedCategory.Q.obj F) ≅
      DerivedCategory.Q.obj (homZ S F) :=
  S.derivedSheafHomExactSupportKInjectiveIso F ≪≫
    ((Stacks.SheafOfModules.ringedSite S.Z.sheaf).derivedStructureSheafHomNatIso.app
      (DerivedCategory.Q.obj ((S.sheafHomExactSupport.mapHomologicalComplex
        (ComplexShape.up ℤ)).obj F))).symm ≪≫
    @AlgebraicGeometry.RingedSite.derivedSheafHomComparison
      (Stacks.SheafOfModules.ringedSite S.Z.sheaf) _ (structureComplexZ S)
      ((S.sheafHomExactSupport.mapHomologicalComplex (ComplexShape.up ℤ)).obj F)
      (S.isKInjective_sheafHomExactSupport F)

/-- The source `R ℰom(𝒪_Z, K) ⊗^L_{𝒪_Z} Li^*M` of the map of [Stacks, Tag 0E2N] is the class
of `sourceZ`: `K` is replaced by `I`, `M` by the K-flat `A`, and the derived tensor product with
the K-flat `i^*A` is computed by the total tensor complex (the comparison of the target of the
projection formula on models, `targetModelIso`). -/
def sourceIso :
    (derivedSheafHomTensorPullback S K).obj M ≅ DerivedCategory.Q.obj (sourceZ S K M) :=
  ((derivedTensorProductFunctor S.Z.sheaf).mapIso
      (S.derivedSheafHomExactSupport.mapIso (injModelIso S K).symm ≪≫
        derivedSheafHomExactSupportModelIso S (injModel S K))).app
      ((Stacks.Cohomology.DerivedAdjunctionOnRingedSpaces.derivedPullback S.i).obj M) ≪≫
    ((derivedTensorProductFunctor S.Z.sheaf).obj
        (DerivedCategory.Q.obj (homZ S (injModel S K)))).mapIso
      ((Stacks.Cohomology.DerivedAdjunctionOnRingedSpaces.derivedPullback S.i).mapIso
        (flatModelIso S M).symm) ≪≫
    (Stacks.Cohomology.ClosedEmbeddingProjectionFormulaComplexes.targetModelIso S.i
      (homZ S (injModel S K)) (flatModel S M) ((ambientRingedSite S).isKFlat_kFlatModel M)).symm

/-- `K ⊗^L M` is the class of the K-injective resolution `J` of `Tot(A ⊗ I)`. -/
def tensorModelIso :
    ((derivedTensorProductFunctor S.X.sheaf).obj K).obj M ≅
      DerivedCategory.Q.obj (tensorInjModel S K M) :=
  ((derivedTensorProductFunctor S.X.sheaf).mapIso (injModelIso S K).symm).app M ≪≫
    ((derivedTensorProductFunctor S.X.sheaf).obj (DerivedCategory.Q.obj (injModel S K))).mapIso
      (flatModelIso S M).symm ≪≫
    (Stacks.DerivedTensor.RingedSite.canonicalDerivedTensorProduct S.X.sheaf).comparisonRight
      (injModel S K) (flatModel S M) ((ambientRingedSite S).isKFlat_kFlatModel M) ≪≫
    DerivedCategory.Q.mapIso
      (Stacks.SheafOfModules.Tensor.tensorComplexFlipIso S.X.sheaf (injModel S K)
        (flatModel S M)) ≪≫
    DerivedCategory.Q.mapIso ((ambientRingedSite S).tensorTotalIsoTensorComplex
      (flatModel S M) (injModel S K)).symm ≪≫
    (haveI := isIso_Q_map_tensorInjAug S K M
     asIso (DerivedCategory.Q.map (tensorInjAug S K M)))

/-- The target `R ℰom(𝒪_Z, K ⊗^L_{𝒪_X} M)` of the map of [Stacks, Tag 0E2N] is the class of
`targetZ`. -/
def targetIso :
    (derivedSheafHomTensor S K).obj M ≅ DerivedCategory.Q.obj (targetZ S K M) :=
  S.derivedSheafHomExactSupport.mapIso (tensorModelIso S K M) ≪≫
    derivedSheafHomExactSupportModelIso S (tensorInjModel S K M)

/-! ### The canonical map and its invertibility -/

/-- **The canonical map of [Stacks, Tag 0E2N]**, constructed on models:

`R ℰom(𝒪_Z, K) ⊗^L_{𝒪_Z} Li^*M ⟶ R ℰom(𝒪_Z, K ⊗^L_{𝒪_X} M)`

is the class of `zMap` read through `sourceIso` and `targetIso`. It is defined for arbitrary
`K` and `M` on a closed quotient morphism of ringed spaces. -/
def tensorDerivedSheafHomModelMap :
    (derivedSheafHomTensorPullback S K).obj M ⟶ (derivedSheafHomTensor S K).obj M :=
  (sourceIso S K M).hom ≫ DerivedCategory.Q.map (zMap S K M) ≫ (targetIso S K M).inv

/-- The canonical map is invertible as soon as the diagonal of [Stacks, Tag 0BYS] at
`(M, K, Ri_* 𝒪_Z)` is. -/
theorem isIso_tensorDerivedSheafHomModelMap_of_isIso_diagonal
    (hd : IsIso ((ambientRingedSite S).derivedTensorHomDiagonal M K
      (pushforwardDerivedStructureSheaf S))) :
    IsIso (tensorDerivedSheafHomModelMap S K M) := by
  have := isIso_Q_map_zMap S K M ((quasiIso_omega_iff S K M).1 hd)
  unfold tensorDerivedSheafHomModelMap
  infer_instance

/-- **[Stacks, Tag 0E2N] on a closed quotient morphism of ringed spaces.** The canonical map is
an isomorphism when `Ri_* 𝒪_Z` is pseudo-coherent on the site of opens of `X`, `K` is bounded
below and `M` has Tor amplitude in `[a, ∞)`: these are the hypotheses of
[Stacks, Tag 0ATK] part (3) in its site form, at the diagonal of [Stacks, Tag 0BYS]. -/
theorem isIso_tensorDerivedSheafHomModelMap (a : ℤ)
    (hG : (ambientRingedSite S).IsPseudoCoherent (pushforwardDerivedStructureSheaf S))
    (hK : DerivedCategoryB.IsBoundedBelow K)
    (hM : (Stacks.SheafOfModules.canonicalDerivedTensorProduct
      (ambientRingedSite S)).HasTorAmplitudeGE M a) :
    IsIso (tensorDerivedSheafHomModelMap S K M) := by
  have hd : IsIso ((ambientRingedSite S).derivedTensorHomDiagonal M K
      (pushforwardDerivedStructureSheaf S)) := by
    refine
      (ambientRingedSite S).isIso_derivedTensorHomDiagonal_of_isPseudoCoherent_of_hasTorAmplitudeGE
        _ _ _ a ?_ ?_ ?_
    · exact hG
    · exact hK
    · exact hM
  exact isIso_tensorDerivedSheafHomModelMap_of_isIso_diagonal S K M hd

/-! ### [Stacks, Tag 0E2N] -/

/-- For a pseudo-coherent closed immersion of schemes, `Ri_* 𝒪_Z` is pseudo-coherent on the
site of opens of `X` ([Stacks, Tag 08FT]). -/
theorem pseudoCoherent_closedImmersion {Z X : Scheme.{u}} (i : Z ⟶ X)
    [IsClosedImmersion i] (hi : AlgebraicGeometry.PseudoCoherent i) :
    (ambientRingedSite
        (Stacks.ClosedImmersion.closedQuotientOfClosedImmersion i)).IsPseudoCoherent
      (pushforwardDerivedStructureSheaf
        (Stacks.ClosedImmersion.closedQuotientOfClosedImmersion i)) :=
  AlgebraicGeometry.Scheme.isPseudoCoherentSite_pushforward_derivedStructureSheaf i hi

/-- The hypothesis of [Stacks, Tag 0E2N] on `M`, local Tor amplitude in `[a, ∞)`, gives Tor
amplitude in `[a, ∞)` for the derived tensor product the diagonal of [Stacks, Tag 0BYS] is
stated with. -/
theorem torAmplitude_of_locally (X : Scheme.{u})
    (M : DerivedCategory (SheafOfModules.{u}
        (structureSheafRing X.toRingedSpace))) (a : ℤ)
    (hM : Stacks.Cohomology.TorAmplitude.LocallyHasTorAmplitudeGE X.toRingedSpace M a) :
    (Stacks.SheafOfModules.canonicalDerivedTensorProduct
      (Stacks.SheafOfModules.ringedSite X.toRingedSpace.sheaf)).HasTorAmplitudeGE M a :=
  Stacks.SheafOfModules.DerivedTensorProduct.hasTorAmplitudeGE_transfer
    (Stacks.Cohomology.TorAmplitude.derTensorSite X.toRingedSpace) _
    (Stacks.Cohomology.TorAmplitude.hasTorAmplitudeGE_of_locallyHasTorAmplitudeGE M a hM)

/-- **[Stacks, Tag 0E2N].** Let `i : Z ⟶ X` be a pseudo-coherent closed immersion of schemes, let
`M ∈ D_QCoh(𝒪_X)` locally have Tor amplitude in `[a, ∞)` and let `K ∈ D⁺_QCoh(𝒪_X)`. Then the
canonical map

`R ℰom(𝒪_Z, K) ⊗^L_{𝒪_Z} Li^*M ⟶ R ℰom(𝒪_Z, K ⊗^L_{𝒪_X} M)`

is an isomorphism in `D(𝒪_Z)`. The quasi-coherence hypotheses on `K` and `M` are part of the
statement and are not used. -/
@[stacks 0E2N "the canonical map is `tensorDerivedSheafHomModelMap`: on a K-injective model \
`I` of `K` and a K-flat model `A` of `M` it is the class of the morphism of complexes whose \
pushforward is the inverse projection formula followed by the interchange of 0BYR, \
`phi (x) a |-> (s |-> phi(s) (x) a)`, that is the counit `Ri_* R Hom(O_Z, K) -> K` tensored \
with `M`; the quasi-coherence of `K` and `M` is part of the statement and is not used"]
theorem isIso_tensorDerivedSheafHomModelMap_of_closedImmersion {Z X : Scheme.{u}} (i : Z ⟶ X)
    [IsClosedImmersion i] (hi : AlgebraicGeometry.PseudoCoherent i)
    (K M : DerivedCategory (SheafOfModules.{u}
        (structureSheafRing X.toRingedSpace))) (a : ℤ)
    (_hMq : @Stacks.DerivedQCoh.IsDQCoh _ _ _
        (structureSheafRing X.toRingedSpace) _ _ _ _ _ M)
    (hM : Stacks.Cohomology.TorAmplitude.LocallyHasTorAmplitudeGE X.toRingedSpace M a)
    (hK : DerivedCategoryB.IsBoundedBelow K)
    (_hKq : @Stacks.DerivedQCoh.IsDQCoh _ _ _
        (structureSheafRing X.toRingedSpace) _ _ _ _ _ K) :
    IsIso (tensorDerivedSheafHomModelMap
      (Stacks.ClosedImmersion.closedQuotientOfClosedImmersion i) K M) := by
  have h1 : (Stacks.SheafOfModules.canonicalDerivedTensorProduct (ambientRingedSite
      (Stacks.ClosedImmersion.closedQuotientOfClosedImmersion i))).HasTorAmplitudeGE M a :=
    torAmplitude_of_locally X M a hM
  have h2 := pseudoCoherent_closedImmersion i hi
  exact isIso_tensorDerivedSheafHomModelMap
    (Stacks.ClosedImmersion.closedQuotientOfClosedImmersion i) K M a h2 hK h1

end Stacks.Duality.TensorHomTorAmplitude

end
