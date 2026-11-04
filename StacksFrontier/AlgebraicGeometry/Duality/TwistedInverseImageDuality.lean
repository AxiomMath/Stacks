module

public import StacksFrontier.AlgebraicGeometry.Duality.CompactGeneration.QcqsCoherator
public import StacksFrontier.CategoryTheory.Monoidal.ProjectionFormulaComparisonMap
public import StacksFrontier.AlgebraicGeometry.Duality.CompactGeneration.QcqsCompactGeneration
public import StacksFrontier.AlgebraicGeometry.Duality.DerivedTilde.SchemeBiduality
public import StacksFrontier.AlgebraicGeometry.Duality.DerivedTilde.SchemeCoherentDuality
public import StacksFrontier.AlgebraicGeometry.Duality.RelativeDualizing.CoherentDerivedSubcategory
public import StacksFrontier.AlgebraicGeometry.Duality.RelativeDualizing.CoherentDuality
public import StacksFrontier.AlgebraicGeometry.Duality.RightAdjointPushforward.ProjectionFormulaLocallySmall
public import StacksFrontier.AlgebraicGeometry.Duality.TwistedInverseImage.BoundedBelow
public import StacksFrontier.AlgebraicGeometry.Duality.TwistedInverseImage.BoundedBelowPlus
public import StacksFrontier.AlgebraicGeometry.PseudoCoherent.Noetherian.CoherentHomology
public import StacksFrontier.AlgebraicGeometry.PseudoCoherent.TransportAlongIso
public import StacksFrontier.CategoryTheory.Monoidal.DualityFormulaYoneda
public import StacksFrontier.CategoryTheory.Sites.Cohomology.InternalHom.DerivedCurryingHomEquivNaturality
public import StacksFrontier.Topology.Sheaves.Cohomology.DerivedPushforward.ProjectionFormulaQCohCoproducts
public import StacksFrontier.Topology.Sheaves.Cohomology.InternalHom.DerivedCompositionTransposeReduction

/-!
# The twisted inverse image of a dual

Let `f : X ⟶ Y` be a quasi-compact quasi-separated morphism of quasi-compact quasi-separated
schemes with `Y` Noetherian, let `a` be the right adjoint of `Rf_* : D_QCoh(𝒪_X) ⥤ D_QCoh(𝒪_Y)`
of [Stacks, Tag 0A9E] and let `K` be a dualizing complex on `Y`, with duality functor
`D_Y = R𝓗om(-, K)`. For `M` in `D^+_Coh(𝒪_Y)` there is an isomorphism

`a(M) ≅ R𝓗om(Lf^* D_Y(M), a(K))`,

natural in `M`. This is the step of the proof of [Stacks, Tag 0AU2] on the compactification: for
`F` in `D_QCoh(𝒪_X)` the morphisms `F ⟶ R𝓗om(Lf^* D_Y(M), a(K))` are, by [Stacks, Tag 08DJ],
the definition of `a`, [Stacks, Tag 08EU], [Stacks, Tag 08DJ] again and [Stacks, Tag 0A89], the
morphisms `Rf_* F ⟶ M`, that is the morphisms `F ⟶ a(M)`.

## Main results

* `Stacks.Duality.isPseudoCoherent_derivedSheafHom_of_isDualizingComplex`: on a Noetherian
  scheme, `D_Y(M)` is pseudo-coherent for `M` in `D^+_Coh(𝒪_Y)`.
* `Stacks.Duality.TwistedInverseImageDuality.dualityIso`: the natural isomorphism above.

## Implementation notes

The derived internal Hom, the derived tensor product, the projection formula and biduality are
available at the standard model `CategoryTheory.HasDerivedCategory.standard`, and `a` at the
locally small model. The chain of bijections is formed at the standard model; the adjunction
`Rf_* ⊣ a` is read there through `StacksDraft.DerivedModel.schemeModulesComparison` and
`StacksDraft.DerivedModel.derivedPushforwardModelIso`
(`CategoryTheory.DualityFormula.transportedHomEquiv`).

## References

* [Stacks Project, Tag 0AU2](https://stacks.math.columbia.edu/tag/0AU2)
* [Stacks Project, Tag 08E8](https://stacks.math.columbia.edu/tag/08E8)
* [Stacks Project, Tag 08EU](https://stacks.math.columbia.edu/tag/08EU)
-/

-- This file uses the locally small derived-category models below, which are not
-- global instances (see `StacksFrontier.Homology.DerivedCategory.LocallySmall`):
-- `D(𝒪_X)` for a scheme.
attribute [local instance] AlgebraicGeometry.Scheme.Modules.hasDerivedCategory

@[expose] public noncomputable section

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits Opposite

universe u

namespace Stacks.Duality

/-! ### Boundedness and pseudo-coherence of duals -/

section Bounds

attribute [local instance 10000] HasDerivedCategory.standard

/-- If the homology sheaves of `E` are coherent, they are quasi-coherent. -/
private theorem isQuasicoherent_homology_of_isCoherent {X : Scheme.{u}}
    (E : DerivedCategory X.Modules)
    (h : ∀ i : ℤ, ((DerivedCategory.homologyFunctor X.Modules i).obj E).IsCoherent) (i : ℤ) :
    ((DerivedCategory.homologyFunctor X.Modules i).obj E).IsQuasicoherent :=
  have := h i
  (Stacks.AlgebraicGeometry.CoherentTFAE.isQuasicoherent_isFiniteType_of_isCoherent (X := X)
    ((DerivedCategory.homologyFunctor X.Modules i).obj E)).1

variable {X : Scheme.{u}} [IsLocallyNoetherian X]

/-- **The dual of an object of `D^+_Coh` is pseudo-coherent** on a Noetherian scheme: it lies in
`D^-_Coh` ([Stacks, Tag 0A89]), and on a Noetherian scheme the objects of `D^-_Coh` are the
pseudo-coherent ones ([Stacks, Tag 08E8]). -/
theorem isPseudoCoherent_derivedSheafHom_of_isDualizingComplex [IsNoetherian X]
    {K L : DerivedCategory X.Modules} (hK : IsDualizingComplex K)
    (hL : DerivedCategoryB.derivedCategoryBPlus (A := X.Modules) (isCoherentSheaf X) L) :
    RingedSpace.IsPseudoCoherent (X := X.toRingedSpace)
      (((Stacks.SheafOfModules.derivedSheafHom X.sheaf).obj (op L)).obj K) := by
  have hc := fun i => isCoherent_homology_derivedSheafHom_of_isDualizingComplex hK hL.2 i
  exact (isPseudoCoherent_iff_boundedAbove_coherent_homology X
    ⟨_, isQuasicoherent_homology_of_isCoherent _ hc⟩).2
    ⟨isBoundedAbove_derivedSheafHom_of_isDualizingComplex hK hL.2 hL.1, hc⟩

end Bounds

namespace TwistedInverseImageDuality

/-! ### Naturality of the tensor–internal-Hom adjunction in the middle variable -/

section Site

attribute [local instance 10000] HasDerivedCategory.standard

variable (X : RingedSite.{u, u, u})
  [HasSheafify X.J AddCommGrpCat.{u}]
  [X.J.WEqualsLocallyBijective AddCommGrpCat.{u}]
  [(Stacks.SheafOfModules.Tensor.sheafTensor.{u, u, u} X.O).Additive]
  [∀ A, ((Stacks.SheafOfModules.Tensor.sheafTensor.{u, u, u} X.O).obj A).Additive]
  [∀ (K₁ K₂ : HomologicalComplex (SheafOfModules.{u}
      (Stacks.SheafOfModules.Tensor.ringSheaf.{u, u, u} X.O)) (ComplexShape.up ℤ)),
    HomologicalComplex.HasMapBifunctor K₁ K₂ (Stacks.SheafOfModules.Tensor.sheafTensor X.O)
      (ComplexShape.up ℤ)]

/-- The bijection of the adjunction `- ⊗ᴸ B ⊣ R𝓗om(B, -)` of [Stacks, Tag 08J8] is natural in
`B`: precomposing `R𝓗om(B, Z) ⟶ R𝓗om(B', Z)` corresponds to tensoring with `B' ⟶ B`. -/
theorem derivedTensorSheafHomAdjunction_homEquiv_symm_naturality_middle
    (A : DerivedCategory
      (SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf.{u, u, u} X.O)))
    {B B' : DerivedCategory
      (SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf.{u, u, u} X.O))}
    (Z : DerivedCategory
      (SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf.{u, u, u} X.O)))
    (l : B' ⟶ B)
    (θ : A ⟶ ((RingedSite.derivedSheafHomBifunctor X).obj (op B)).obj Z) :
    ((RingedSite.derivedTensorSheafHomAdjunction X B').homEquiv A Z).symm
        (θ ≫ ((RingedSite.derivedSheafHomBifunctor X).map l.op).app Z) =
      ((Stacks.SheafOfModules.derivedTensorProductFunctor X).obj A).map l ≫
        ((RingedSite.derivedTensorSheafHomAdjunction X B).homEquiv A Z).symm θ := by
  simp only [RingedSite.derivedTensorSheafHomAdjunction, Adjunction.mkOfHomEquiv_homEquiv,
    Equiv.coe_fn_symm_mk]
  rw [RingedSite.derivedCurryHomEquiv_dinaturality]

end Site

/-! ### The ingredients at the standard model -/

section Standard

attribute [local instance 10000] HasDerivedCategory.standard

variable (X : Scheme.{u})

/-- `D(𝒪_X)` at the standard model. -/
abbrev Std := DerivedCategory (SheafOfModules.{u}
  (Stacks.SheafOfModules.Tensor.ringSheaf (Stacks.SheafOfModules.ringedSite X.sheaf).O))

/-- The derived tensor product of `D(𝒪_X)` at which [Stacks, Tag 08J8] is stated. -/
abbrev tensor : Std X ⥤ Std X ⥤ Std X :=
  Stacks.SheafOfModules.derivedTensorProductFunctor (Stacks.SheafOfModules.ringedSite X.sheaf)

/-- The derived internal Hom of `D(𝒪_X)`. -/
abbrev sheafHom : (Std X)ᵒᵖ ⥤ Std X ⥤ Std X :=
  RingedSite.derivedSheafHomBifunctor (Stacks.SheafOfModules.ringedSite X.sheaf)

/-- The adjunction `- ⊗ᴸ B ⊣ R𝓗om(B, -)` of [Stacks, Tag 08J8] on `D(𝒪_X)`. -/
abbrev tensorHomAdjunction (B : Std X) : (tensor X).flip.obj B ⊣ (sheafHom X).obj (op B) :=
  RingedSite.derivedTensorSheafHomAdjunction (Stacks.SheafOfModules.ringedSite X.sheaf) B

/-- The tensor–internal-Hom bijection of [Stacks, Tag 08J8]. -/
def curry (A B Z : Std X) :
    (A ⟶ ((sheafHom X).obj (op B)).obj Z) ≃ (((tensor X).obj A).obj B ⟶ Z) :=
  ((tensorHomAdjunction X B).homEquiv A Z).symm

/-- The bijection `curry` is natural in the first variable: precomposing with `k : A' ⟶ A`
corresponds to precomposing with `k ⊗ᴸ B`. -/
theorem curry_naturality_left {A A' : Std X} (B Z : Std X) (k : A' ⟶ A)
    (θ : A ⟶ ((sheafHom X).obj (op B)).obj Z) :
    curry X A' B Z (k ≫ θ) = ((tensor X).map k).app B ≫ curry X A B Z θ :=
  (tensorHomAdjunction X B).homEquiv_naturality_left_symm k θ

/-- The bijection `curry` is natural in the middle variable: postcomposing with
`R𝓗om(B, Z) ⟶ R𝓗om(B', Z)` corresponds to precomposing with `A ⊗ᴸ l` for `l : B' ⟶ B`. -/
theorem curry_naturality_middle (A : Std X) {B B' : Std X} (Z : Std X) (l : B' ⟶ B)
    (θ : A ⟶ ((sheafHom X).obj (op B)).obj Z) :
    curry X A B' Z (θ ≫ ((sheafHom X).map l.op).app Z) =
      ((tensor X).obj A).map l ≫ curry X A B Z θ := by
  simp only [curry, tensorHomAdjunction]
  rw [derivedTensorSheafHomAdjunction_homEquiv_symm_naturality_middle]

end Standard

section Projection

attribute [local instance 10000] HasDerivedCategory.standard
attribute [local instance] Stacks.Cohomology.ProjectionFormulaPerfect.hasSheafifyOpens
  Stacks.Cohomology.ProjectionFormulaPerfect.wEqualsLocallyBijectiveOpens
  Stacks.AssociatedSheaf.abelianModulesRingSheaf

variable {X Y : Scheme.{u}} (f : X ⟶ Y)

/-- `Rf_*` at the standard model. -/
abbrev push : Std X ⥤ Std Y :=
  Stacks.Cohomology.DerivedAdjunctionOnRingedSpaces.derivedPushforward f.toLRSHom.toShHom

/-- `Lf^*` at the standard model. -/
abbrev pull : Std Y ⥤ Std X :=
  Stacks.Cohomology.DerivedAdjunctionOnRingedSpaces.derivedPullback f.toLRSHom.toShHom

/-- **The projection formula map** `Rf_*F ⊗ᴸ D ⟶ Rf_*(F ⊗ᴸ Lf^*D)` of [Stacks, Tag 08EU], read
at the derived tensor product of [Stacks, Tag 08J8]. -/
def projectionMap (F : Std X) (D : Std Y) :
    ((tensor Y).obj ((push f).obj F)).obj D ⟶
      (push f).obj (((tensor X).obj F).obj ((pull f).obj D)) :=
  DualityFormula.conjugateProjection (ProjectionFormulaLocallySmall.standardTensorIso X)
    (ProjectionFormulaLocallySmall.standardTensorIso Y) (push f) (pull f)
    (Stacks.Cohomology.DerivedProjectionFormula.projectionFormulaMap f.toLRSHom.toShHom) F D

/-- The projection formula map `projectionMap` is natural in the object `F` of `D(𝒪_X)`. -/
theorem projectionMap_natural_left {F F' : Std X} (g : F' ⟶ F) (D : Std Y) :
    ((tensor Y).map ((push f).map g)).app D ≫ projectionMap f F D =
      projectionMap f F' D ≫ (push f).map (((tensor X).map g).app ((pull f).obj D)) :=
  DualityFormula.conjugateProjection_natural_left _ _ _ _ _
    (fun g D => Stacks.Cohomology.DerivedProjectionFormula.projectionFormulaMap_natural_left
      f.toLRSHom.toShHom g D) g D

/-- The projection formula map `projectionMap` is natural in the object `D` of `D(𝒪_Y)`. -/
theorem projectionMap_natural_right (F : Std X) {D D' : Std Y} (d : D ⟶ D') :
    ((tensor Y).obj ((push f).obj F)).map d ≫ projectionMap f F D' =
      projectionMap f F D ≫ (push f).map (((tensor X).obj F).map ((pull f).map d)) :=
  DualityFormula.conjugateProjection_natural_right _ _ _ _ _
    (fun F _ _ d => Stacks.Cohomology.DerivedProjectionFormula.projectionFormulaMap_natural_right
      f.toLRSHom.toShHom F d) F d

/-- For `f` quasi-compact and quasi-separated and `F`, `D` with quasi-coherent cohomology, the
projection formula map `Rf_*F ⊗ᴸ D ⟶ Rf_*(F ⊗ᴸ Lf^*D)` is an isomorphism. -/
theorem isIso_projectionMap [QuasiCompact f] [QuasiSeparated f] (F : Std X) (D : Std Y)
    (hF : Stacks.DerivedQCoh.IsDQCoh (R := structureSheafRing X.toRingedSpace) F)
    (hD : Stacks.DerivedQCoh.IsDQCoh (R := structureSheafRing Y.toRingedSpace) D) :
    IsIso (projectionMap f F D) :=
  DualityFormula.isIso_conjugateProjection _ _ _ _ _ F D
    (Stacks.Cohomology.ProjectionFormulaQCoh.isIso_projectionFormulaMap_of_isDQCoh f F D hF hD)

end Projection

/-! ### Duals, biduality and the subcategories at the standard model -/

/-- The comparison of the standard and the locally small model of `D(𝒪_X)`. -/
abbrev comparison (X : Scheme.{u}) : Std X ≌ DerivedCategory X.Modules :=
  StacksDraft.DerivedModel.schemeModulesComparison X

/-- Bounded below cohomology, at the locally small model. -/
abbrev IsBoundedBelowLS {X : Scheme.{u}} (E : DerivedCategory X.Modules) : Prop :=
  DerivedCategoryB.IsBoundedBelow E

/-- `D^+_QCoh` at the locally small model, as a property of objects. -/
abbrev qcohPlusProperty (X : Scheme.{u}) : ObjectProperty (DerivedCategory X.Modules) :=
  DerivedCategoryB.derivedCategoryBPlus (A := X.Modules)
    (SheafOfModules.isQuasicoherent X.ringCatSheaf)

section StandardProperties

attribute [local instance 10000] HasDerivedCategory.standard

variable {X Y : Scheme.{u}} (f : X ⟶ Y)

/-- `D_QCoh` read at the standard model. -/
abbrev qcoh (X : Scheme.{u}) : ObjectProperty (Std X) :=
  DualityFormula.transportedProperty (comparison X) (Coherator.quasiCoherentProp X)

/-- `D^+_Coh(𝒪_X)` at the standard model. -/
abbrev plusCoh (X : Scheme.{u}) : ObjectProperty (Std X) :=
  fun M => @DerivedCategoryB.derivedCategoryBPlus X.Modules _ _
    (AlgebraicGeometry.PerfectApproximation.standardModel X) (isCoherentSheaf X) M

/-- An object of `D(𝒪_X)` at the standard model lies in `qcoh X` if and only if its cohomology
sheaves are quasi-coherent. -/
theorem qcoh_iff_isDQCoh (E : Std X) :
    qcoh X E ↔ Stacks.DerivedQCoh.IsDQCoh (R := structureSheafRing X.toRingedSpace) E :=
  ⟨fun h i => (AlgebraicGeometry.PerfectApproximation.isQuasicoherent_homology_standard_iff
      ((comparison X).functor.obj E) i).2 (h i),
    fun h i => (AlgebraicGeometry.PerfectApproximation.isQuasicoherent_homology_standard_iff
      ((comparison X).functor.obj E) i).1 (h i)⟩

/-- On a locally Noetherian scheme, an object of `D(𝒪_X)` with coherent cohomology sheaves lies
in `qcoh X`. -/
theorem qcoh_of_isCoherent [IsLocallyNoetherian X] (E : Std X)
    (h : ∀ i : ℤ, ((DerivedCategory.homologyFunctor X.Modules i).obj E).IsCoherent) : qcoh X E :=
  (qcoh_iff_isDQCoh E).2 (isQuasicoherent_homology_of_isCoherent E h)

/-- On a locally Noetherian scheme, `D^+_Coh(𝒪_X)` is contained in `D_QCoh(𝒪_X)`. -/
theorem plusCoh_le_qcoh [IsLocallyNoetherian X] : plusCoh X ≤ qcoh X :=
  fun E h => qcoh_of_isCoherent E h.2

/-- The biduality morphism `M ⟶ R𝓗om(R𝓗om(M, K), K)` of [Stacks, Tag 0A89]. -/
def bidual (Y : Scheme.{u}) (K M : Std Y) :
    M ⟶ ((sheafHom Y).obj (op (((sheafHom Y).obj (op M)).obj K))).obj K :=
  RingedSite.derivedBiduality (Stacks.SheafOfModules.ringedSite Y.sheaf) K M

/-- The biduality morphism `bidual` is natural in `M`. -/
theorem bidual_naturality (Y : Scheme.{u}) (K : Std Y) {M M' : Std Y} (φ : M ⟶ M') :
    φ ≫ bidual Y K M' = bidual Y K M ≫
      ((sheafHom Y).map (((sheafHom Y).map φ.op).app K).op).app K := by
  simp only [bidual]
  rw [RingedSite.derivedBiduality_naturality]

/-- For a dualizing complex `K` on a locally Noetherian scheme and `M` in `D^+_Coh`, the biduality
morphism `M ⟶ R𝓗om(R𝓗om(M, K), K)` is an isomorphism. -/
theorem isIso_bidual [IsLocallyNoetherian Y] {K : Std Y} (hK : IsDualizingComplex K) (M : Std Y)
    (hM : plusCoh Y M) : IsIso (bidual Y K M) :=
  isIso_derivedBiduality_of_isDualizingComplex K M hK hM.2

/-- For a dualizing complex `K` on a locally Noetherian scheme and `M` in `D^+_Coh`, the dual
`R𝓗om(M, K)` has quasi-coherent cohomology. -/
theorem qcoh_dual [IsLocallyNoetherian Y] {K : Std Y} (hK : IsDualizingComplex K) (M : Std Y)
    (hM : plusCoh Y M) : qcoh Y (((sheafHom Y).obj (op M)).obj K) :=
  qcoh_of_isCoherent _ fun i => isCoherent_homology_derivedSheafHom_of_isDualizingComplex hK hM.2 i

/-- For a dualizing complex `K` on `Y`, `M` in `D^+_Coh(𝒪_Y)` and `F` in `D_QCoh(𝒪_X)`, the
object `F ⊗ᴸ Lf^* R𝓗om(M, K)` has quasi-coherent cohomology. -/
theorem qcoh_tensor_pull [IsLocallyNoetherian Y] {K : Std Y} (hK : IsDualizingComplex K)
    (M : Std Y) (hM : plusCoh Y M) (F : Std X) (hF : qcoh X F) :
    qcoh X (((tensor X).obj F).obj ((pull f).obj (((sheafHom Y).obj (op M)).obj K))) := by
  refine (qcoh_iff_isDQCoh _).2 ?_
  refine Stacks.DerivedQCoh.isDQCoh_of_iso (R := structureSheafRing X.toRingedSpace)
    (((ProjectionFormulaLocallySmall.standardTensorIso X).app F).app _) ?_
  exact Stacks.Cohomology.ProjectionFormulaQCohCoproducts.isDQCoh_derivedTensor_obj X F _
    ((qcoh_iff_isDQCoh F).1 hF)
    (Stacks.Cohomology.ProjectionFormulaQCohCoproducts.isDQCoh_derivedPullback_obj f _
      ((qcoh_iff_isDQCoh _).1 (qcoh_dual hK M hM)))

/-- For `f` quasi-compact and quasi-separated, `F` in `qcoh X` and `D` in `qcoh Y`, the
projection formula map `projectionMap f F D` is an isomorphism. -/
theorem isIso_projectionMap_of_qcoh [QuasiCompact f] [QuasiSeparated f] (F : Std X) (D : Std Y)
    (hF : qcoh X F) (hD : qcoh Y D) : IsIso (projectionMap f F D) :=
  isIso_projectionMap f F D ((qcoh_iff_isDQCoh F).1 hF) ((qcoh_iff_isDQCoh D).1 hD)

/-- Being a dualizing complex ([Stacks, Tag 0A87]), at the standard model. -/
abbrev IsDualizing [IsLocallyNoetherian Y] (K : Std Y) : Prop := IsDualizingComplex K

/-- A dualizing complex on a locally Noetherian scheme has quasi-coherent cohomology. -/
theorem qcoh_of_isDualizingComplex [IsLocallyNoetherian Y] {K : Std Y} (hK : IsDualizingComplex K) :
    qcoh Y K :=
  qcoh_of_isCoherent K fun i => isCoherent_homology_of_isDualizingComplex hK i

/-- A dualizing complex on a quasi-compact locally Noetherian scheme has bounded below cohomology,
read at the locally small model. -/
theorem isBoundedBelow_of_isDualizingComplex_standard [IsLocallyNoetherian Y] [CompactSpace Y]
    {K : Std Y} (hK : IsDualizingComplex K) :
    IsBoundedBelowLS ((comparison Y).functor.obj K) := by
  obtain ⟨n, hn⟩ := isBoundedBelow_of_isDualizingComplex _ hK
  exact ⟨n, fun i hi => (AlgebraicGeometry.PerfectApproximation.isZero_homology_standard_iff
    ((comparison Y).functor.obj K) i).1 (hn i hi)⟩

/-- **`R𝓗om(Lf^* D_Y(M), A)` has quasi-coherent cohomology** for `M` in `D^+_Coh(𝒪_Y)` and `A` in
`D^+_QCoh(𝒪_X)`: `D_Y(M)` is pseudo-coherent, so is its derived pullback ([Stacks, Tag 09U7]),
and [Stacks, Tag 0A6H] part (1) applies. -/
theorem qcoh_sheafHom_pull [IsNoetherian Y] {K : Std Y} (hK : IsDualizingComplex K) (M : Std Y)
    (hM : plusCoh Y M) (A : Std X)
    (hA : qcohPlusProperty X ((comparison X).functor.obj A)) :
    qcoh X (((sheafHom X).obj (op ((pull f).obj (((sheafHom Y).obj (op M)).obj K)))).obj A) := by
  have hP := AlgebraicGeometry.Scheme.Hom.isPseudoCoherent_derivedPullback f _
    (isPseudoCoherent_derivedSheafHom_of_isDualizingComplex hK hM)
  have hP' := (AlgebraicGeometry.PerfectApproximation.isPseudoCoherent_standard_iff
    ((comparison X).functor.obj ((pull f).obj (((sheafHom Y).obj (op M)).obj K)))).1 hP
  intro i
  exact InternalHom.isQuasicoherent_homology_derivedSheafHom_of_isPseudoCoherent _ _ hP' hA i

end StandardProperties

/-! ### The duality formula on the compactification -/

section Formula

variable {X Y : Scheme.{u}} (f : X ⟶ Y) [QuasiCompact f] [QuasiSeparated f]
  [CompactSpace X] [QuasiSeparatedSpace X] [CompactSpace Y] [QuasiSeparatedSpace Y]

/-- `Rf_*` at the two models. -/
def pushModelIso :
    push f ⋙ (comparison Y).functor ≅
      (comparison X).functor ⋙ Stacks.Duality.derivedPushforward f :=
  StacksDraft.DerivedModel.derivedPushforwardModelIso f.toLRSHom.toShHom

/-- The twisted inverse image `a` of [Stacks, Tag 0A9E], read at the standard model. -/
abbrev rightAdjointStd : (qcoh Y).FullSubcategory ⥤ Std X :=
  DualityFormula.transportedRightAdjoint (comparison X) (comparison Y)
    (Coherator.quasiCoherentProp X) (Coherator.quasiCoherentProp Y)
    (twistedInverseImage f (isQuasicoherent_homology_derivedPushforward_of_qcqs f))

/-- The adjunction bijection `(Rf_* F ⟶ M) ≃ (F ⟶ a M)` of [Stacks, Tag 0A9E], read at the
standard model. -/
abbrev adjunctionHomEquiv (M : (qcoh Y).FullSubcategory) (F : Std X) (hF : qcoh X F) :
    ((push f).obj F ⟶ M.obj) ≃ (F ⟶ (rightAdjointStd f).obj M) :=
  DualityFormula.transportedHomEquiv (comparison X) (comparison Y) (push f)
    (Stacks.Duality.derivedPushforward f) (pushModelIso f) (Coherator.quasiCoherentProp X)
    (Coherator.quasiCoherentProp Y)
    (quasiCoherentDerivedPushforward f (isQuasicoherent_homology_derivedPushforward_of_qcqs f))
    (ObjectProperty.liftCompιIso _ _ (isQuasicoherent_homology_derivedPushforward_of_qcqs f))
    (twistedInverseImage f (isQuasicoherent_homology_derivedPushforward_of_qcqs f))
    (twistedInverseImageAdjunction f (isQuasicoherent_homology_derivedPushforward_of_qcqs f))
    M F hF

variable [IsNoetherian Y] {K : Std Y} (hK : IsDualizing K)

/-- `K` as an object of `D_QCoh(𝒪_Y)` at the standard model. -/
abbrev dualizingObject (hK : IsDualizing K) : (qcoh Y).FullSubcategory :=
  ⟨K, qcoh_of_isDualizingComplex hK⟩

/-- **The duality formula on a proper-type morphism, [Stacks, Tag 0AU2]**: for `f : X ⟶ Y` qcqs
between qcqs schemes with `Y` Noetherian, `a` the right adjoint of `Rf_*` on `D_QCoh` and `K` a
dualizing complex on `Y`, there is an isomorphism `a(M) ≅ R𝓗om(Lf^* R𝓗om(M, K), a(K))` natural
in `M ∈ D^+_Coh(𝒪_Y)`. -/
def dualityIso :
    ObjectProperty.ιOfLE plusCoh_le_qcoh ⋙ rightAdjointStd f ≅
      (plusCoh Y).ι ⋙ ((sheafHom Y).flip.obj K).rightOp ⋙ (pull f).op ⋙
        (sheafHom X).flip.obj ((rightAdjointStd f).obj (dualizingObject hK)) :=
  DualityFormula.dualityFormulaIso (TX := tensor X) (HX := sheafHom X) (cX := curry X)
    (TY := tensor Y) (HY := sheafHom Y) (cY := curry Y) (π := push f) (p := pull f)
    (PX := qcoh X) (PY := qcoh Y) (a := rightAdjointStd f) (α := adjunctionHomEquiv f)
    (ρ := projectionMap f) (K := dualizingObject hK) (β := bidual Y K) (𝓜 := plusCoh Y)
    (h𝓜 := plusCoh_le_qcoh)
    (hρ := fun F D hF hD => isIso_projectionMap_of_qcoh f F D hF hD)
    (hβ := fun M hM => isIso_bidual hK M hM)
    (hD := fun M hM => qcoh_dual hK M hM)
    (hT := fun M F hM hF => qcoh_tensor_pull f hK M hM F hF)
    (fun B Z k θ => curry_naturality_left X B Z k θ)
    (fun A _ _ Z l θ => curry_naturality_middle X A Z l θ)
    (fun B Z k θ => curry_naturality_left Y B Z k θ)
    (fun A _ _ Z l θ => curry_naturality_middle Y A Z l θ)
    (fun M _ _ hF hF' g h => DualityFormula.transportedHomEquiv_naturality_left M hF hF' g h)
    (fun φ F hF h => DualityFormula.transportedHomEquiv_naturality_right φ F hF h)
    (fun g D => projectionMap_natural_left f g D)
    (fun F _ _ d => projectionMap_natural_right f F d)
    (fun φ => bidual_naturality Y K φ)
    (fun M => ((twistedInverseImage f (isQuasicoherent_homology_derivedPushforward_of_qcqs f)).obj
      ⟨(comparison Y).functor.obj M.obj, M.property⟩).property)
    (fun M hM => qcoh_sheafHom_pull f hK M hM _
      ⟨isBoundedBelow_twistedInverseImage_obj f _
        (isBoundedBelow_of_isDualizingComplex_standard hK),
        ((twistedInverseImage f (isQuasicoherent_homology_derivedPushforward_of_qcqs f)).obj
          ⟨(comparison Y).functor.obj K, qcoh_of_isDualizingComplex hK⟩).property⟩)

end Formula

end TwistedInverseImageDuality

end Stacks.Duality

end
