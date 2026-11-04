module

public import StacksFrontier.AlgebraicGeometry.Duality.CompactlySupportedCohomology.ShriekAdjunction
public import StacksFrontier.AlgebraicGeometry.Duality.CompactlySupportedCohomology.ShriekTriangles
public import StacksFrontier.AlgebraicGeometry.Duality.CompactlySupportedCohomology.ShriekTrianglesLan
public import StacksFrontier.AlgebraicGeometry.Duality.ExtensionZeroCoherent.DeligneSystemCoreCoherent
public import
  StacksFrontier.AlgebraicGeometry.Duality.ExtensionZeroCoherent.DeligneSystemRestrictionLifting
public import StacksFrontier.AlgebraicGeometry.Duality.ExtensionZeroCoherent.RestrictionLiftingTransfer
public import StacksFrontier.AlgebraicGeometry.Duality.ExtensionZeroCoherent.RestrictionLiftingColimit
public import StacksFrontier.AlgebraicGeometry.Duality.UpperShriekCoherent
public import StacksFrontier.AlgebraicGeometry.Duality.UpperShriekDuality
public import StacksFrontier.AlgebraicGeometry.ProperSupportCoherent.BoundedBelowDerivedDirectImage

/-!
# The adjointness of `Rf_!` and `f^!`

In Situation [Stacks, Tag 0F42] let `f : X ⟶ Y` be a morphism of `FTS_S`. For `K` in
`D^b_{Coh}(𝒪_X)` and `L` in `D^+_{Coh}(𝒪_Y)`,

`Hom_X(K, f^! L) = Hom_{Pro-D^+_{Coh}(𝒪_Y)}(Rf_! K, L)`,

bifunctorially in `K` and `L` ([Stacks, Tag 0G51]).

For a compactification `j : X ⟶ X̄` with structure morphism `f̄ : X̄ ⟶ Y` this is the chain
`Hom(Rf̄_* Rj_! K, L) = Hom(Rj_! K, f̄^! L) = Hom(K, j^* f̄^! L)` of
`CategoryTheory.shriekHomEquiv`, instantiated with: `Rf̄_*` on `D^+_{Coh}`, which it preserves
for `f̄` proper; its right adjoint `f̄^!`, which preserves `D^+_{Coh}` by [Stacks, Tag 0AU1]; and
[Stacks, Tag 0G4K] for the Deligne systems computing `Rj_!`. Finally `j^* f̄^! = f^!` by
construction of `f^!` ([Stacks, Section 0A9Y]).

## Main definitions

* `Stacks.Duality.TwistedInverseImageDuality.pushPlusCoh`: `Rf_* : D^+_{Coh}(𝒪_X) ⥤ D^+_{Coh}(𝒪_Y)`
  for a proper morphism of Noetherian schemes.
* `Stacks.Duality.TwistedInverseImageDuality.upperShriekPlusCoh`: its right adjoint `f^!`.
* `Stacks.Duality.TwistedInverseImageDuality.pushPlusCohAdjunction`: `Rf_* ⊣ f^!` on `D^+_{Coh}`.
* `AlgebraicGeometry.lowerShriekHomEquiv`: the bijection
  `Hom_{Pro-D^+_{Coh}(𝒪_Y)}(Rf_! K, L) ≃ Hom_X(K, f^! L)`.
* `AlgebraicGeometry.lowerShriekHomIso`: **[Stacks, Tag 0G51]**, the bijection as an isomorphism
  of bifunctors.

## Implementation notes

Everything is read at the standard model `CategoryTheory.HasDerivedCategory.standard`, where
`Rf_!` (`AlgebraicGeometry.lowerShriek`) lives; `f^!` is read there through
`Stacks.Duality.UpperShriekDuality.upperShriekStd`, the comparison of models being the identity
on objects.

## References

* [Stacks Project, Tag 0G51](https://stacks.math.columbia.edu/tag/0G51)
* [Stacks Project, Tag 0G4K](https://stacks.math.columbia.edu/tag/0G4K)
* [Stacks Project, Tag 0AU1](https://stacks.math.columbia.edu/tag/0AU1)
-/

-- This file uses the locally small derived-category models below, which are not
-- global instances (see `StacksFrontier.Homology.DerivedCategory.LocallySmall`):
-- `D(𝒪_X)` for a scheme.
attribute [local instance] AlgebraicGeometry.Scheme.Modules.hasDerivedCategory

@[expose] public noncomputable section

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits CategoryTheory.Pretriangulated Opposite

attribute [local instance] CategoryTheory.uliftCategory

universe u v

namespace CategoryTheory.Functor

/-- A functor between categories with objects and morphisms in `Type v` has pointwise left Kan
extensions of functors to `Type v`: `Type v` has the colimits over the comma categories
involved. -/
theorem hasPointwiseLeftKanExtension_of_type {C D : Type v} [Category.{v} C] [Category.{v} D]
    (L : C ⥤ D) (A : C ⥤ Type v) : L.HasPointwiseLeftKanExtension A :=
  fun _ => inferInstance

/-- A functor between categories with objects and morphisms in `Type v` has left Kan extensions of
functors to `Type v`. -/
theorem hasLeftKanExtension_of_type {C D : Type v} [Category.{v} C] [Category.{v} D]
    (L : C ⥤ D) (A : C ⥤ Type v) : L.HasLeftKanExtension A :=
  have := hasPointwiseLeftKanExtension_of_type L A
  inferInstance

end CategoryTheory.Functor

namespace Stacks.Duality.TwistedInverseImageDuality

/-! ### `D^+_{Coh}` at the two models -/

section Models

variable {X : Scheme.{u}}

/-- **`D^+_{Coh}` does not depend on the model**: an object of `D(𝒪_X)` is in `D^+_{Coh}` at the
standard model if and only if it is at the locally small model. -/
theorem plusCoh_iff (E : Std X) :
    plusCoh X E ↔ DerivedCategoryB.derivedCategoryBPlus (fun M : X.Modules => M.IsCoherent)
      ((comparison X).functor.obj E) := by
  have key (i : ℤ) : ((@DerivedCategory.homologyFunctor X.Modules _ _
      (PerfectApproximation.standardModel X) i).obj E).IsCoherent ↔
      ((DerivedCategory.homologyFunctor X.Modules i).obj E).IsCoherent :=
    ⟨fun h => Stacks.AlgebraicGeometry.CoherentDevissage.isCoherent_of_iso
      (PerfectApproximation.homologyStandardIso E i), fun h =>
      Stacks.AlgebraicGeometry.CoherentDevissage.isCoherent_of_iso
        (PerfectApproximation.homologyStandardIso E i).symm⟩
  exact and_congr (exists_congr fun n => forall_congr' fun i => forall_congr' fun hi =>
    PerfectApproximation.isZero_homology_standard_iff E i) (forall_congr' key)

/-- **The right adjoint `f^!` of `Rf_*` preserves `D^+_{Coh}`** for a proper morphism of Noetherian
schemes: this is [Stacks, Tag 0AU1] for `f` as a morphism of `FTS_Y`, compactified by itself. -/
theorem plusCoh_rightAdjointStd_obj {Y : Scheme.{u}} (f : X ⟶ Y) [IsNoetherian X] [IsNoetherian Y]
    [IsProper f]
    (L : (plusCoh Y).FullSubcategory) :
    plusCoh X ((rightAdjointStd f).obj ((ObjectProperty.ιOfLE plusCoh_le_qcoh).obj L)) := by
  let f' : FTS.mk f ⟶ FTS.mk (𝟙 Y) :=
    MorphismProperty.Over.homMk f (Category.comp_id f) trivial
  have : IsProper f'.left := ‹IsProper f›
  have h := derivedCategoryBPlus_upperShriek f' (properCompactification f')
    ⟨(comparison Y).functor.obj L.obj, plusCoh_le_qcoh _ L.property⟩
    ((plusCoh_iff L.obj).1 L.property)
  have h₂ : DerivedCategoryB.derivedCategoryBPlus (fun M : X.Modules => M.IsCoherent)
      ((twistedInverseImage f (isQuasicoherent_homology_derivedPushforward_of_qcqs f)).obj
        ⟨(comparison Y).functor.obj L.obj, plusCoh_le_qcoh _ L.property⟩).obj :=
    (DerivedCategoryB.derivedCategoryBPlus_isClosedUnderIsomorphisms _
      (WeakSerre.isWeakSerre_of_isWeakSerreClass _)).of_iso
        ((ObjectProperty.ι _).mapIso ((upperShriekProperIso f').app _)) h
  exact (plusCoh_iff _).2 h₂

end Models

attribute [local instance 10000] HasDerivedCategory.standard

/-! ### `Rf_*` on `D^+_{Coh}` -/

section Pushforward

/-- `D^b_{Coh}(𝒪_X) ⊆ D^+_{Coh}(𝒪_X)`. -/
theorem boundedCoherentDerived_le_plusCoh (X : Scheme.{u}) :
    boundedCoherentDerived X ≤ plusCoh X :=
  fun _ h => ⟨h.1.1, h.2⟩

variable {X Y : Scheme.{u}} (f : X ⟶ Y)

/-- **`Rf_*` preserves `D^+_{Coh}` for a proper morphism to a Noetherian scheme.** It preserves
lower bounds; and in degree `n` the truncation triangle `τ^{≤ n}E ⟶ E ⟶ τ^{> n}E` identifies
`H^n(Rf_*E)` with `H^n(Rf_*τ^{≤ n}E)`, which is coherent by [Stacks, Tag 08E2], `τ^{≤ n}E`
lying in `D^b_{Coh}`. -/
theorem plusCoh_derivedPushforwardModules_obj [IsNoetherian Y] [IsProper f] (E : Std X)
    (hE : plusCoh X E) : plusCoh Y ((derivedPushforwardModules f).obj E) := by
  have : IsLocallyNoetherian X := LocallyOfFiniteType.isLocallyNoetherian f
  have : CompactSpace X := QuasiCompact.compactSpace_of_compactSpace f
  have : IsNoetherian X := ⟨⟩
  obtain ⟨b, hb⟩ := (DerivedCategoryB.isBoundedBelow_iff_exists_isGE E).1 hE.1
  refine ⟨(DerivedCategoryB.isBoundedBelow_iff_exists_isGE _).2
    ⟨b, Stacks.AlgebraicGeometry.ProperSupportCoherent.isGE_derivedPushforward f E b hb⟩,
    fun n => ?_⟩
  have hB := mem_boundedCoherentDerived_derivedPushforward f
    ((DerivedCategory.TStructure.t.truncLE n).obj E) (boundedCoherentDerived_truncLE_obj n E hE)
  have h₁ : ((DerivedCategory.homologyFunctor Y.Modules n).obj
      ((derivedPushforwardModules f).obj
        ((DerivedCategory.TStructure.t.truncLE n).obj E))).IsCoherent := hB.2 n
  let T := (derivedPushforwardModules f).mapTriangle.obj
    ((DerivedCategory.TStructure.t.triangleLEGT n).obj E)
  have hdist : T ∈ distTriang (DerivedCategory Y.Modules) :=
    (derivedPushforwardModules f).map_distinguished _
      (DerivedCategory.TStructure.t.triangleLEGT_distinguished n E)
  have h₃ : T.obj₃.IsGE (n + 1) :=
    Stacks.AlgebraicGeometry.ProperSupportCoherent.isGE_derivedPushforward f
      ((DerivedCategory.TStructure.t.truncGT n).obj E) (n + 1)
      (DerivedCategory.TStructure.t.isGE_truncGT_obj E n (n + 1))
  have hz := T.obj₃.isZero_of_isGE (n + 1) n (by omega)
  have hz' := T.obj₃.isZero_of_isGE (n + 1) (n - 1) (by omega)
  have : Epi ((DerivedCategory.homologyFunctor Y.Modules n).map T.mor₁) :=
    ((DerivedCategory.homologyFunctor Y.Modules 0).homologySequence_epi_shift_map_mor₁_iff
      T hdist n).2 (hz.eq_of_tgt _ _)
  have : Mono ((DerivedCategory.homologyFunctor Y.Modules n).map T.mor₁) :=
    ((DerivedCategory.homologyFunctor Y.Modules 0).homologySequence_mono_shift_map_mor₁_iff
      T hdist (n - 1) n (by omega)).2 (hz'.eq_of_src _ _)
  have : IsIso ((DerivedCategory.homologyFunctor Y.Modules n).map T.mor₁) :=
    isIso_of_mono_of_epi _
  have : ((DerivedCategory.homologyFunctor Y.Modules n).obj T.obj₁).IsCoherent := h₁
  exact Stacks.AlgebraicGeometry.CoherentDevissage.isCoherent_of_iso (R := Y.ringCatSheaf)
    (asIso ((DerivedCategory.homologyFunctor Y.Modules n).map T.mor₁)).symm

variable [IsNoetherian X] [IsNoetherian Y] [IsProper f]

/-- **`Rf_* : D^+_{Coh}(𝒪_X) ⥤ D^+_{Coh}(𝒪_Y)`** for a proper morphism of Noetherian schemes. -/
abbrev pushPlusCoh : (plusCoh X).FullSubcategory ⥤ (plusCoh Y).FullSubcategory :=
  (plusCoh Y).lift ((plusCoh X).ι ⋙ push f) fun E =>
    plusCoh_derivedPushforwardModules_obj f E.obj E.property

end Pushforward

/-! ### The right adjoint `f^!` on `D^+_{Coh}` -/

section Shriek

attribute [local instance] Stacks.Cohomology.ProjectionFormulaPerfect.hasSheafifyOpens
  Stacks.Cohomology.ProjectionFormulaPerfect.wEqualsLocallyBijectiveOpens
attribute [local instance] Stacks.AssociatedSheaf.abelianModulesRingSheaf

variable {X Y : Scheme.{u}} (f : X ⟶ Y) [IsNoetherian X] [IsNoetherian Y] [IsProper f]

/-- **`f^! : D^+_{Coh}(𝒪_Y) ⥤ D^+_{Coh}(𝒪_X)`** for a proper morphism of Noetherian schemes: the
right adjoint `a` of `Rf_* : D_{QCoh}(𝒪_X) ⥤ D_{QCoh}(𝒪_Y)` of [Stacks, Tag 0A9E], read at the
standard model and restricted to `D^+_{Coh}`. -/
abbrev upperShriekPlusCoh : (plusCoh Y).FullSubcategory ⥤ (plusCoh X).FullSubcategory :=
  (plusCoh X).lift (ObjectProperty.ιOfLE plusCoh_le_qcoh ⋙ rightAdjointStd f)
    (plusCoh_rightAdjointStd_obj f)

/-- The adjunction bijection `(Rf_* K ⟶ L) ≃ (K ⟶ f^! L)` on `D^+_{Coh}`. -/
def pushPlusCohHomEquiv (K : (plusCoh X).FullSubcategory) (L : (plusCoh Y).FullSubcategory) :
    ((pushPlusCoh f).obj K ⟶ L) ≃ (K ⟶ (upperShriekPlusCoh f).obj L) :=
  ((plusCoh Y).fullyFaithfulι.homEquiv (X := (pushPlusCoh f).obj K) (Y := L)).trans
    ((adjunctionHomEquiv f ((ObjectProperty.ιOfLE plusCoh_le_qcoh).obj L) K.obj
      (plusCoh_le_qcoh _ K.property)).trans
      ((plusCoh X).fullyFaithfulι.homEquiv (X := K) (Y := (upperShriekPlusCoh f).obj L)).symm)

/-- The bijection `adjunctionHomEquiv f M F hF` is natural in `F`. -/
theorem adjunctionHomEquiv_naturality_left (M : (qcoh Y).FullSubcategory) {F F' : Std X}
    (hF : qcoh X F) (hF' : qcoh X F') (g : F' ⟶ F) (h : (push f).obj F ⟶ M.obj) :
    adjunctionHomEquiv f M F' hF' ((push f).map g ≫ h) = g ≫ adjunctionHomEquiv f M F hF h :=
  DualityFormula.transportedHomEquiv_naturality_left M hF hF' g h

/-- The bijection `adjunctionHomEquiv f M F hF` is natural in `M`. -/
theorem adjunctionHomEquiv_naturality_right {M M' : (qcoh Y).FullSubcategory} (φ : M ⟶ M')
    (F : Std X) (hF : qcoh X F) (h : (push f).obj F ⟶ M.obj) :
    adjunctionHomEquiv f M' F hF (h ≫ φ.hom) =
      adjunctionHomEquiv f M F hF h ≫ (rightAdjointStd f).map φ :=
  DualityFormula.transportedHomEquiv_naturality_right φ F hF h

/-- The underlying morphism of `pushPlusCohHomEquiv f K L g` is the image of `g` under
`adjunctionHomEquiv`. -/
theorem pushPlusCohHomEquiv_apply_hom (K : (plusCoh X).FullSubcategory)
    (L : (plusCoh Y).FullSubcategory) (g : (pushPlusCoh f).obj K ⟶ L) :
    (pushPlusCohHomEquiv f K L g).hom =
      adjunctionHomEquiv f ((ObjectProperty.ιOfLE plusCoh_le_qcoh).obj L) K.obj
        (plusCoh_le_qcoh _ K.property) g.hom :=
  rfl

/-- The bijection `pushPlusCohHomEquiv f K L` is natural in `K`. -/
theorem pushPlusCohHomEquiv_naturality_left {K' K : (plusCoh X).FullSubcategory} (k : K' ⟶ K)
    (L : (plusCoh Y).FullSubcategory) (g : (pushPlusCoh f).obj K ⟶ L) :
    pushPlusCohHomEquiv f K' L ((pushPlusCoh f).map k ≫ g) = k ≫ pushPlusCohHomEquiv f K L g := by
  ext
  exact adjunctionHomEquiv_naturality_left f
    ((ObjectProperty.ιOfLE plusCoh_le_qcoh).obj L) (plusCoh_le_qcoh _ K.property)
    (plusCoh_le_qcoh _ K'.property) k.hom g.hom

/-- The bijection `pushPlusCohHomEquiv f K L` is natural in `L`. -/
theorem pushPlusCohHomEquiv_naturality_right (K : (plusCoh X).FullSubcategory)
    {L L' : (plusCoh Y).FullSubcategory} (g : (pushPlusCoh f).obj K ⟶ L) (l : L ⟶ L') :
    pushPlusCohHomEquiv f K L' (g ≫ l) =
      pushPlusCohHomEquiv f K L g ≫ (upperShriekPlusCoh f).map l := by
  ext
  exact adjunctionHomEquiv_naturality_right f
    ((ObjectProperty.ιOfLE plusCoh_le_qcoh).map l) K.obj (plusCoh_le_qcoh _ K.property) g.hom

/-- The hom-set description of `Rf_* ⊣ f^!` on `D^+_{Coh}`. -/
def pushPlusCohCoreHomEquiv : Adjunction.CoreHomEquiv (pushPlusCoh f) (upperShriekPlusCoh f) where
  homEquiv := pushPlusCohHomEquiv f
  homEquiv_naturality_left_symm {K' K L} k g := by
    rw [Equiv.symm_apply_eq, pushPlusCohHomEquiv_naturality_left, Equiv.apply_symm_apply]
  homEquiv_naturality_right {K L L'} g l := pushPlusCohHomEquiv_naturality_right f K g l

/-- **`Rf_* ⊣ f^!` on `D^+_{Coh}`** for a proper morphism of Noetherian schemes. -/
def pushPlusCohAdjunction : pushPlusCoh f ⊣ upperShriekPlusCoh f :=
  Adjunction.mkOfHomEquiv (pushPlusCohCoreHomEquiv f)

end Shriek

end Stacks.Duality.TwistedInverseImageDuality

namespace AlgebraicGeometry

open Stacks.Duality Stacks.Duality.TwistedInverseImageDuality Stacks.Duality.UpperShriekDuality

attribute [local instance 10000] HasDerivedCategory.standard
attribute [local instance 10000] CategoryTheory.Functor.hasLeftKanExtension_of_type
attribute [local instance] Stacks.Cohomology.ProjectionFormulaPerfect.hasSheafifyOpens
  Stacks.Cohomology.ProjectionFormulaPerfect.wEqualsLocallyBijectiveOpens
attribute [local instance] Stacks.AssociatedSheaf.abelianModulesRingSheaf

/-- The inclusion `D^b_{Coh}(𝒪_X) ⊆ D^+_{Coh}(𝒪_X)`. -/
abbrev boundedCoherentToPlusCoh (X : Scheme.{u}) :
    BoundedCoherentDerived X ⥤ (plusCoh X).FullSubcategory :=
  ObjectProperty.ιOfLE (boundedCoherentDerived_le_plusCoh X)

/-- The inclusion `D^b_{Coh}(𝒪_X) ⊆ D^+_{Coh}(𝒪_X)` is full. -/
instance (X : Scheme.{u}) : (boundedCoherentToPlusCoh X).Full :=
  ObjectProperty.full_ιOfLE (boundedCoherentDerived_le_plusCoh X)

/-- The inclusion `D^b_{Coh}(𝒪_X) ⊆ D^+_{Coh}(𝒪_X)` is faithful. -/
instance (X : Scheme.{u}) : (boundedCoherentToPlusCoh X).Faithful :=
  ObjectProperty.faithful_ιOfLE (boundedCoherentDerived_le_plusCoh X)

section CompactificationData

variable {X X' Y : Scheme.{u}} (j : X ⟶ X') [IsOpenImmersion j] [IsNoetherian X']
  (fbar : X' ⟶ Y) [IsProper fbar] [IsNoetherian Y]

/-- `Rf̄_*` on `D^b_{Coh}` is the restriction of `Rf̄_*` on `D^+_{Coh}`. -/
def properPushforwardPlusCohIso :
    properPushforwardBoundedCoherent fbar ⋙ boundedCoherentToPlusCoh Y ≅
      boundedCoherentToPlusCoh X' ⋙ pushPlusCoh fbar :=
  NatIso.ofComponents (fun _ => Iso.refl _)
    (fun _ => (Category.comp_id _).trans (Category.id_comp _).symm)

/-- Restriction `j^*` on `D^b_{Coh}` is the restriction of `Lj^*` on `D^+_{Coh}`. -/
def restrictPlusCohIso :
    boundedCoherentToPlusCoh X' ⋙ (plusCoh X').ι ⋙ pull j ≅
      restrictBoundedCoherentLift j ⋙ (boundedCoherentDerived X).ι :=
  NatIso.ofComponents
    (fun K => ((Scheme.Modules.derivedRestrictIsoDerivedPullback j).app K.obj).symm)
    (fun φ => ((Scheme.Modules.derivedRestrictIsoDerivedPullback j).inv.naturality φ.hom))

/-- **[Stacks, Tag 0G4K] for the Deligne systems computing `Rj_!`**, read in `D^+_{Coh}` with
restriction written as `Lj^*`. -/
theorem restrictionLifting_values_plusCoh (K : BoundedCoherentDerived X)
    (N : (plusCoh X').FullSubcategory) :
    RestrictionLifting ((DeligneSystem.values j).system K ⋙ boundedCoherentToPlusCoh X')
      ((plusCoh X').ι ⋙ pull j) N := by
  have h₀ := (DeligneSystem.ofValue j K).restrictionLifting_of_derivedCategoryBPlus N.obj
    ⟨N.property.1, N.property.2⟩
  exact RestrictionLifting.of_fullyFaithful_comp _ _ _ N
    (RestrictionLifting.of_natIsoFunctor _ (Scheme.Modules.derivedRestrictIsoDerivedPullback j) h₀)

/-- **`Hom_{Pro-D^+_{Coh}(𝒪_Y)}(Rf̄_* Rj_! K, L) = Hom_X(K, j^* f̄^! L)`** for an open immersion
`j : X ⟶ X̄` and a proper `f̄ : X̄ ⟶ Y` of Noetherian schemes. -/
def shriekHomEquivOfOpenImmersion (K : BoundedCoherentDerived X)
    (L : (plusCoh Y).FullSubcategory) :
    ((ProSeq.map (boundedCoherentToPlusCoh Y)).obj
        ((CompactificationData.ofOpenImmersion j fbar).shriekImage.obj K) ⟶ ProSeq.const.obj L) ≃
      ((boundedCoherentDerived X).ι.obj K ⟶ (pull j).obj ((upperShriekPlusCoh fbar).obj L).obj) :=
  shriekHomEquiv (boundedCoherentToPlusCoh X') (properPushforwardBoundedCoherent fbar)
    (boundedCoherentToPlusCoh Y) (pushPlusCoh fbar) (properPushforwardPlusCohIso fbar)
    (pushPlusCohAdjunction fbar) (DeligneSystem.values j) (boundedCoherentDerived X).ι
    ((plusCoh X').ι ⋙ pull j) (restrictPlusCohIso j) (restrictionLifting_values_plusCoh j) K L

/-- The bijection `shriekHomEquivOfOpenImmersion j fbar K L` is natural in `L`. -/
theorem shriekHomEquivOfOpenImmersion_comp_const (K : BoundedCoherentDerived X)
    {L L' : (plusCoh Y).FullSubcategory} (g : L ⟶ L')
    (φ : (ProSeq.map (boundedCoherentToPlusCoh Y)).obj
        ((CompactificationData.ofOpenImmersion j fbar).shriekImage.obj K) ⟶ ProSeq.const.obj L) :
    shriekHomEquivOfOpenImmersion j fbar K L' (φ ≫ ProSeq.const.map g) =
      shriekHomEquivOfOpenImmersion j fbar K L φ ≫
        (pull j).map ((upperShriekPlusCoh fbar).map g).hom :=
  shriekHomEquiv_comp_const _ _ _ _ _ _ _ _ _ _ _ K g φ

/-- The bijection `shriekHomEquivOfOpenImmersion j fbar K L` is natural in `K`. -/
theorem shriekHomEquivOfOpenImmersion_map_comp {K' K : BoundedCoherentDerived X} (k : K' ⟶ K)
    (L : (plusCoh Y).FullSubcategory)
    (φ : (ProSeq.map (boundedCoherentToPlusCoh Y)).obj
        ((CompactificationData.ofOpenImmersion j fbar).shriekImage.obj K) ⟶ ProSeq.const.obj L) :
    shriekHomEquivOfOpenImmersion j fbar K' L
        ((ProSeq.map (boundedCoherentToPlusCoh Y)).map
          ((CompactificationData.ofOpenImmersion j fbar).shriekImage.map k) ≫ φ) =
      (boundedCoherentDerived X).ι.map k ≫ shriekHomEquivOfOpenImmersion j fbar K L φ :=
  shriekHomEquiv_shriekProMap_comp _ _ _ _ _ _ _ _ _ _ _ k L φ

end CompactificationData

section FTS

variable {S : Scheme.{u}} [IsNoetherian S] {X₁ Y₁ : FTS S} (f : X₁ ⟶ Y₁)
  (c : CompactificationOf (Over.mk f.left))

/-- `j^* f̄^! = f^!` on `D^+_{Coh}(𝒪_Y)`, at the standard model: this is the construction of `f^!`
([Stacks, Section 0A9Y]). -/
def pullUpperShriekPlusCohIso :
    upperShriekPlusCoh c.toBase ⋙ (plusCoh c.space).ι ⋙ pull c.immersion ≅ upperShriekStd f c :=
  (Functor.associator _ _ _).symm ≪≫
    Functor.isoWhiskerRight (ObjectProperty.liftCompιIso _ _ _) (pull c.immersion) ≪≫
    Functor.associator _ _ _ ≪≫ (upperShriekStdIso f c).symm

/-- **The bijection of [Stacks, Tag 0G51]**:
`Hom_{Pro-D^+_{Coh}(𝒪_Y)}(Rf_! K, L) ≃ Hom_X(K, f^! L)` for `K` in `D^b_{Coh}(𝒪_X)` and `L` in
`D^+_{Coh}(𝒪_Y)`, with `Rf_!` and `f^!` computed at the compactification `c`. -/
def lowerShriekHomEquiv (K : BoundedCoherentDerived X₁.left)
    (L : (plusCoh Y₁.left).FullSubcategory) :
    ((ProSeq.map (boundedCoherentToPlusCoh Y₁.left)).obj ((lowerShriek f c).obj K) ⟶
        ProSeq.const.obj L) ≃
      ((boundedCoherentDerived X₁.left).ι.obj K ⟶ (upperShriekStd f c).obj L) :=
  (shriekHomEquivOfOpenImmersion c.immersion c.toBase K L).trans
    { toFun := fun x => x ≫ (pullUpperShriekPlusCohIso f c).hom.app L
      invFun := fun y => y ≫ (pullUpperShriekPlusCohIso f c).inv.app L
      left_inv := fun x => (Category.assoc _ _ _).trans ((congrArg (x ≫ ·)
        ((pullUpperShriekPlusCohIso f c).hom_inv_id_app L)).trans (Category.comp_id x))
      right_inv := fun y => (Category.assoc _ _ _).trans ((congrArg (y ≫ ·)
        ((pullUpperShriekPlusCohIso f c).inv_hom_id_app L)).trans (Category.comp_id y)) }

/-- `lowerShriekHomEquiv f c K L φ` is `shriekHomEquivOfOpenImmersion` applied to `φ`, followed by
the identification `pullUpperShriekPlusCohIso f c` of `j^* f̄^! L` with `f^! L`. -/
theorem lowerShriekHomEquiv_apply (K : BoundedCoherentDerived X₁.left)
    (L : (plusCoh Y₁.left).FullSubcategory)
    (φ : (ProSeq.map (boundedCoherentToPlusCoh Y₁.left)).obj ((lowerShriek f c).obj K) ⟶
        ProSeq.const.obj L) :
    lowerShriekHomEquiv f c K L φ =
      shriekHomEquivOfOpenImmersion c.immersion c.toBase K L φ ≫
        (pullUpperShriekPlusCohIso f c).hom.app L :=
  rfl

/-- `AlgebraicGeometry.lowerShriekHomEquiv` is natural in `L`. -/
theorem lowerShriekHomEquiv_comp_const (K : BoundedCoherentDerived X₁.left)
    {L L' : (plusCoh Y₁.left).FullSubcategory} (g : L ⟶ L')
    (φ : (ProSeq.map (boundedCoherentToPlusCoh Y₁.left)).obj ((lowerShriek f c).obj K) ⟶
        ProSeq.const.obj L) :
    lowerShriekHomEquiv f c K L' (φ ≫ ProSeq.const.map g) =
      lowerShriekHomEquiv f c K L φ ≫ (upperShriekStd f c).map g := by
  rw [lowerShriekHomEquiv_apply, lowerShriekHomEquiv_apply,
    shriekHomEquivOfOpenImmersion_comp_const]
  exact (Category.assoc _ _ _).trans ((congrArg (shriekHomEquivOfOpenImmersion c.immersion c.toBase
    K L φ ≫ ·) ((pullUpperShriekPlusCohIso f c).hom.naturality g)).trans
      (Category.assoc _ _ _).symm)

/-- `AlgebraicGeometry.lowerShriekHomEquiv` is natural in `K`. -/
theorem lowerShriekHomEquiv_map_comp {K' K : BoundedCoherentDerived X₁.left} (k : K' ⟶ K)
    (L : (plusCoh Y₁.left).FullSubcategory)
    (φ : (ProSeq.map (boundedCoherentToPlusCoh Y₁.left)).obj ((lowerShriek f c).obj K) ⟶
        ProSeq.const.obj L) :
    lowerShriekHomEquiv f c K' L
        ((ProSeq.map (boundedCoherentToPlusCoh Y₁.left)).map ((lowerShriek f c).map k) ≫ φ) =
      (boundedCoherentDerived X₁.left).ι.map k ≫ lowerShriekHomEquiv f c K L φ := by
  rw [lowerShriekHomEquiv_apply, lowerShriekHomEquiv_apply,
    shriekHomEquivOfOpenImmersion_map_comp]
  exact Category.assoc _ _ _

/-- In Situation [Stacks, Tag 0F42] let `f : X ⟶ Y` be a morphism of `FTS_S`. Then `Rf_!` and
`f^!` are adjoint in the following sense: for `K` in `D^b_{Coh}(𝒪_X)` and `L` in
`D^+_{Coh}(𝒪_Y)`

`Hom_X(K, f^! L) = Hom_{Pro-D^+_{Coh}(𝒪_Y)}(Rf_! K, L)`,

bifunctorially in `K` and `L`: an isomorphism of functors
`D^b_{Coh}(𝒪_X)ᵒᵖ ⥤ D^+_{Coh}(𝒪_Y) ⥤ Type`, with components
`AlgebraicGeometry.lowerShriekHomEquiv`. Here `Rf_!` and `f^!` are computed at an arbitrary
compactification `c` of `X` over `Y`, `Rf_! K` is viewed in `Pro-D^+_{Coh}(𝒪_Y)` through
`D^b_{Coh} ⊆ D^+_{Coh}`, and `f^! L` is read at the standard model of `D(𝒪_X)`
(`Stacks.Duality.UpperShriekDuality.upperShriekStd`). -/
@[stacks 0G51]
def lowerShriekHomIso :
    (lowerShriek f c ⋙ ProSeq.map (boundedCoherentToPlusCoh Y₁.left)).op ⋙ coyoneda ⋙
        (Functor.whiskeringLeft _ _ _).obj ProSeq.const ≅
      (boundedCoherentDerived X₁.left).ι.op ⋙ coyoneda ⋙
        (Functor.whiskeringLeft _ _ _).obj (upperShriekStd f c) :=
  NatIso.ofComponents
    (fun K => NatIso.ofComponents
      (fun L => (lowerShriekHomEquiv f c K.unop L).toIso)
      (fun {L L'} g => by
        ext φ
        exact lowerShriekHomEquiv_comp_const f c K.unop g φ))
    (fun {K K'} k => by
      ext L φ
      exact lowerShriekHomEquiv_map_comp f c k.unop L φ)

end FTS

end AlgebraicGeometry

end
