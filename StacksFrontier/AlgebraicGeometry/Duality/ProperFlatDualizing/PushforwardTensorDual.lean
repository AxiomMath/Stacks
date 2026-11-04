module

public import StacksFrontier.AlgebraicGeometry.Duality.ProperFlatDualizing.Basic
public import StacksFrontier.AlgebraicGeometry.Duality.ProperFlatDualizing.AbstractTensorDual
public import StacksFrontier.Topology.Sheaves.Cohomology.InternalHom.PerfectDualLeftDual
public import StacksFrontier.Topology.Sheaves.Cohomology.InternalHom.DualityPairingCupProduct
public import StacksFrontier.Topology.Sheaves.Cohomology.DerivedPushforward.ProjectionFormulaQuasiCoherent
public import StacksFrontier.AlgebraicGeometry.DerivedQCoh.DualOfAPerfectComplex
public import StacksFrontier.AlgebraicGeometry.Perfect.PerfectApproximation.DerivedSectionsTensorPseudoCoherence
public import StacksFrontier.AlgebraicGeometry.Duality.DerivedTilde.QuasiCoherentDerivedPullback

/-!
# `Rf_*(E ⊗ a(𝒪_Y))` is the dual of `Rf_*(E^∨)` for a perfect `E`

Let `f : X ⟶ Y` be a morphism of quasi-compact and quasi-separated schemes, `a` the right adjoint
of `Rf_* : D_QCoh(𝒪_X) ⥤ D_QCoh(𝒪_Y)` and `ω = a(𝒪_Y)`. For a perfect object `E` of `D(𝒪_X)`
with dual `E^∨` such that `Rf_*E^∨` is perfect there is an isomorphism

  `Rf_*(E ⊗^L ω) ≅ (Rf_*E^∨)^∨`.

This is the first display of the proof of [Stacks, Tag 0E4L]: for `M ∈ D_QCoh(𝒪_Y)`

  `Hom(M, Rf_*(E ⊗ ω)) = Hom(Lf^*M, E ⊗ ω) = Hom(E^∨ ⊗ Lf^*M, ω) = Hom(Rf_*(E^∨ ⊗ Lf^*M), 𝒪_Y)`
  `                   = Hom(Rf_*E^∨ ⊗ M, 𝒪_Y) = Hom(M, (Rf_*E^∨)^∨)`,

by the adjunction `Lf^* ⊣ Rf_*`, the duality of the perfect object `E` ([Stacks, Tag 08DQ]), the
adjunction `Rf_* ⊣ a`, the projection formula ([Stacks, Tag 08EU]) and the duality of the
perfect object `Rf_*E^∨`; the abstract argument is
`CategoryTheory.MonoidalCategory.RelativeDuality.tensorDualIso`.

## Main results

* `Stacks.Duality.StandardModel.pushforwardTensorDualIso` — the isomorphism above.

## Implementation notes

Everything is read at the standard model, in the spelling `DerivedCategory Z.Modules`, with the
monoidal structure `Stacks.SheafOfModules.derivedMonoidalStructure` re-seated on that spelling as
`Stacks.Duality.StandardModel.monoidal`; the derived pullback of the ringed spaces is re-typed in
the same spelling as `Stacks.Duality.StandardModel.pullback`. Unifying the several spellings of the
category of `𝒪_Z`-modules at the level of morphisms is expensive, and these re-typings keep every
morphism in one spelling.
-/

@[expose] public noncomputable section

open AlgebraicGeometry CategoryTheory CategoryTheory.MonoidalCategory Opposite

universe u

namespace Stacks.Duality.StandardModel

attribute [local instance 10000] HasDerivedCategory.standard

attribute [local instance] Stacks.Topology.SheafTensorAdditiveOnOpens.sheafTensorAdditive
  Stacks.Topology.SheafTensorAdditiveOnOpens.sheafTensorObjAdditive
  Stacks.Topology.SheafTensorAdditiveOnOpens.hasMapBifunctorSheafTensor

open Stacks.SheafOfModules

/-- The monoidal structure of [Stacks, Tag 0FPT] on `D(𝒪_Z)`, in the spelling
`DerivedCategory Z.Modules`. -/
@[instance_reducible]
def monoidal (Z : Scheme.{u}) : MonoidalCategory (DerivedCategory Z.Modules) :=
  derivedMonoidalStructure Z.sheaf

/-- The symmetry of the monoidal structure `Stacks.Duality.StandardModel.monoidal`. -/
@[instance_reducible]
def symmetric (Z : Scheme.{u}) :
    @SymmetricCategory (DerivedCategory Z.Modules) _ (monoidal Z) :=
  derivedSymmetricStructure Z.sheaf

/-- The derived tensor product of [Stacks, Tag 0FPT], in the spelling
`DerivedCategory Z.Modules`. -/
def tensor (Z : Scheme.{u}) :
    DerivedCategory Z.Modules ⥤ DerivedCategory Z.Modules ⥤ DerivedCategory Z.Modules :=
  Stacks.SheafOfModules.derivedTensor Z.sheaf

/-- The derived tensor product of [Stacks, Tag 06YU], in the spelling
`DerivedCategory Z.Modules`. -/
def tensor' (Z : Scheme.{u}) :
    DerivedCategory Z.Modules ⥤ DerivedCategory Z.Modules ⥤ DerivedCategory Z.Modules :=
  Stacks.DerivedTensor.RingedSite.derivedTensorProductFunctor Z.sheaf

/-- The two derived tensor products agree. -/
def tensorIso (Z : Scheme.{u}) : tensor Z ≅ tensor' Z :=
  derivedTensorCanonicalIso Z.toRingedSpace

/-- The tensor product of `Stacks.Duality.StandardModel.monoidal` is `tensor`. -/
theorem curriedTensor_monoidal (Z : Scheme.{u}) :
    @curriedTensor (DerivedCategory Z.Modules) _ (monoidal Z) = tensor Z :=
  curriedTensor_derivedMonoidalStructure Z.sheaf

/-- The dual `K^∨ = R𝓗om(K, 𝒪_Z)` of [Stacks, Tag 08DQ], in the spelling
`DerivedCategory Z.Modules`. -/
def dual {Z : Scheme.{u}} (K : DerivedCategory Z.Modules) : DerivedCategory Z.Modules :=
  derivedDual Z.sheaf K

/-- The duality of [Stacks, Tag 08DQ] for a perfect object. -/
@[instance_reducible]
def exactPairingDual {Z : Scheme.{u}} (K : DerivedCategory Z.Modules)
    (hK : Stacks.Cohomology.PerfectComplexes.IsPerfect (X := Z.toRingedSpace) K) :
    @ExactPairing (DerivedCategory Z.Modules) _ (monoidal Z) K (dual K) := by
  letI := monoidal Z
  exact exactPairingDerivedDual Z.sheaf K
    (Stacks.Cohomology.PerfectComplexes.isPerfect_ringedSite_of_isPerfect Z.toRingedSpace K hK)

/-- Perfect objects of `D(𝒪_Z)` have quasi-coherent cohomology. -/
theorem isQuasicoherent_homology_of_isPerfect {Z : Scheme.{u}} (K : DerivedCategory Z.Modules)
    (hK : Stacks.Cohomology.PerfectComplexes.IsPerfect (X := Z.toRingedSpace) K) (i : ℤ) :
    ((DerivedCategory.homologyFunctor Z.Modules i).obj K).IsQuasicoherent :=
  AlgebraicGeometry.isQuasicoherentDerived_of_isPseudoCoherent Z K
    (Stacks.Cohomology.TorAmplitude.isPseudoCoherent_of_isPerfect K hK) i

variable {X Y : Scheme.{u}} (f : X ⟶ Y)

/-- The derived pullback `Lf^*` of [Stacks, Tag 079W], in the spelling
`DerivedCategory Z.Modules`. -/
def pullback : DerivedCategory Y.Modules ⥤ DerivedCategory X.Modules :=
  Cohomology.DerivedAdjunctionOnRingedSpaces.derivedPullback f.toLRSHom.toShHom

/-- The adjunction `Lf^* ⊣ Rf_*` of [Stacks, Tag 079W]. -/
def pullbackAdjunction : pullback f ⊣ derivedPushforward f :=
  Cohomology.DerivedAdjunctionOnRingedSpaces.derivedAdjunction f.toLRSHom.toShHom

/-- The projection-formula morphism `Rf_*E ⊗ K ⟶ Rf_*(E ⊗ Lf^*K)` of [Stacks, Tag 0B53]. -/
def projectionFormulaMap (E : DerivedCategory X.Modules) (K : DerivedCategory Y.Modules) :
    ((tensor' Y).obj ((derivedPushforward f).obj E)).obj K ⟶
      (derivedPushforward f).obj (((tensor' X).obj E).obj ((pullback f).obj K)) :=
  Stacks.Cohomology.DerivedProjectionFormula.projectionFormulaMap f.toLRSHom.toShHom E K

/-- The projection-formula morphism `Rf_*E ⊗ K ⟶ Rf_*(E ⊗ Lf^*K)` is natural in `K`. -/
theorem projectionFormulaMap_natural (E : DerivedCategory X.Modules)
    {K K' : DerivedCategory Y.Modules} (k : K ⟶ K') :
    ((tensor' Y).obj ((derivedPushforward f).obj E)).map k ≫ projectionFormulaMap f E K' =
      projectionFormulaMap f E K ≫
        (derivedPushforward f).map (((tensor' X).obj E).map ((pullback f).map k)) :=
  Stacks.Cohomology.DerivedProjectionFormula.projectionFormulaMap_natural_right
    f.toLRSHom.toShHom E k

section Dual

variable [CompactSpace X] [QuasiSeparatedSpace X] [CompactSpace Y] [QuasiSeparatedSpace Y]
  (E : DerivedCategory X.Modules)
  (hE : Stacks.Cohomology.PerfectComplexes.IsPerfect (X := X.toRingedSpace) E)

omit [CompactSpace X] [QuasiSeparatedSpace X] [CompactSpace Y] [QuasiSeparatedSpace Y] in
include hE in
/-- `E^∨ ⊗ Lf^*M` has quasi-coherent cohomology for `M ∈ D_QCoh(𝒪_Y)`. -/
theorem isQuasicoherent_dual_tensor_pullback (M : DerivedCategory Y.Modules)
    (hM : DerivedCategoryB.derivedCategoryB (A := Y.Modules)
      (SheafOfModules.isQuasicoherent Y.ringCatSheaf) M) :
    DerivedCategoryB.derivedCategoryB (A := X.Modules)
      (SheafOfModules.isQuasicoherent X.ringCatSheaf)
      (((tensor X).obj (dual E)).obj ((pullback f).obj M)) :=
  AlgebraicGeometry.isQuasicoherent_homology_derivedTensor_obj_obj X _ _
    (Stacks.DerivedQCoh.isQuasicoherent_homology_derivedDual X E hE)
    (Stacks.Duality.isQuasicoherent_homology_derivedPullback_anyModel f M hM)

/-- The projection formula `Rf_*E^∨ ⊗ M ≅ Rf_*(E^∨ ⊗ Lf^*M)` of [Stacks, Tag 08EU] for
`M ∈ D_QCoh(𝒪_Y)`. -/
def projectionFormulaDualIso (M : DerivedCategory Y.Modules)
    (hM : DerivedCategoryB.derivedCategoryB (A := Y.Modules)
      (SheafOfModules.isQuasicoherent Y.ringCatSheaf) M) :
    ((tensor Y).obj ((derivedPushforward f).obj (dual E))).obj M ≅
      (derivedPushforward f).obj
        (((tensor X).obj (dual E)).obj ((pullback f).obj M)) :=
  ((tensorIso Y).app _).app M ≪≫
    @asIso _ _ _ _ (projectionFormulaMap f (dual E) M)
      (Stacks.Cohomology.DerivedProjectionFormula.isIso_projectionFormulaMap_quasiCoherent f _
        (Stacks.DerivedQCoh.isQuasicoherent_homology_derivedDual X E hE) M hM) ≪≫
    (derivedPushforward f).mapIso (((tensorIso X).app _).app _).symm

omit [CompactSpace Y] in
/-- The forward map of `projectionFormulaDualIso` is `projectionFormulaMap`, conjugated by the
comparison isomorphisms `tensorIso` of the two derived tensor products. -/
theorem projectionFormulaDualIso_hom (M : DerivedCategory Y.Modules)
    (hM : DerivedCategoryB.derivedCategoryB (A := Y.Modules)
      (SheafOfModules.isQuasicoherent Y.ringCatSheaf) M) :
    (projectionFormulaDualIso f E hE M hM).hom =
      ((tensorIso Y).hom.app _).app M ≫ projectionFormulaMap f (dual E) M ≫
        (derivedPushforward f).map (((tensorIso X).inv.app _).app _) :=
  rfl

/-- Three commuting squares paste to a square whose bottom row is `t ≫ p ≫ F.map i`. -/
private theorem comp_eq_comp_of_three_squares {C D : Type*} [Category C] [Category D] (F : D ⥤ C)
    {S S' T T' : C} {U U' V V' : D} {a : S ⟶ S'} {t : S' ⟶ T} {p : T ⟶ F.obj U}
    {i : U ⟶ V} {t' : S ⟶ T'} {b : T' ⟶ T} {p' : T' ⟶ F.obj U'} {c : U' ⟶ U}
    {i' : U' ⟶ V'} {w : V' ⟶ V} (h₁ : a ≫ t = t' ≫ b) (h₂ : b ≫ p = p' ≫ F.map c)
    (h₃ : c ≫ i = i' ≫ w) :
    a ≫ t ≫ p ≫ F.map i = (t' ≫ p' ≫ F.map i') ≫ F.map w := by
  rw [← Category.assoc, h₁, Category.assoc, ← Category.assoc b, h₂, Category.assoc,
    ← F.map_comp, h₃, F.map_comp]
  simp only [Category.assoc]

omit [CompactSpace Y] in
/-- The isomorphism `Rf_*E^∨ ⊗ M ≅ Rf_*(E^∨ ⊗ Lf^*M)` is natural in `M`. -/
theorem projectionFormulaDualIso_naturality (M M' : DerivedCategory Y.Modules)
    (hM : DerivedCategoryB.derivedCategoryB (A := Y.Modules)
      (SheafOfModules.isQuasicoherent Y.ringCatSheaf) M)
    (hM' : DerivedCategoryB.derivedCategoryB (A := Y.Modules)
      (SheafOfModules.isQuasicoherent Y.ringCatSheaf) M')
    (g : M' ⟶ M) :
    ((tensor Y).obj ((derivedPushforward f).obj (dual E))).map g ≫
        (projectionFormulaDualIso f E hE M hM).hom =
      (projectionFormulaDualIso f E hE M' hM').hom ≫
        (derivedPushforward f).map (((tensor X).obj (dual E)).map ((pullback f).map g)) := by
  have h₁ := ((tensorIso Y).hom.app ((derivedPushforward f).obj (dual E))).naturality g
  have h₂ := projectionFormulaMap_natural f (dual E) g
  have h₃ := ((tensorIso X).inv.app (dual E)).naturality ((pullback f).map g)
  rw [projectionFormulaDualIso_hom, projectionFormulaDualIso_hom]
  exact comp_eq_comp_of_three_squares _ h₁ h₂ h₃

omit [CompactSpace Y] in
/-- The isomorphism `Rf_*E^∨ ⊗ M ≅ Rf_*(E^∨ ⊗ Lf^*M)` is natural with respect to a morphism
`E'^∨ ⟶ E^∨` between the duals of perfect objects. -/
theorem projectionFormulaDualIso_naturality_left (E' : DerivedCategory X.Modules)
    (hE' : Stacks.Cohomology.PerfectComplexes.IsPerfect (X := X.toRingedSpace) E')
    (h : dual E' ⟶ dual E) (M : DerivedCategory Y.Modules)
    (hM : DerivedCategoryB.derivedCategoryB (A := Y.Modules)
      (SheafOfModules.isQuasicoherent Y.ringCatSheaf) M) :
    ((tensor Y).map ((derivedPushforward f).map h)).app M ≫
        (projectionFormulaDualIso f E hE M hM).hom =
      (projectionFormulaDualIso f E' hE' M hM).hom ≫
        (derivedPushforward f).map (((tensor X).map h).app ((pullback f).obj M)) := by
  have h₁ := congrArg (fun t => t.app M)
    ((tensorIso Y).hom.naturality ((derivedPushforward f).map h))
  have h₂ := Stacks.Cohomology.DerivedProjectionFormula.projectionFormulaMap_natural_left
    f.toLRSHom.toShHom h M
  have h₃ := congrArg (fun t => t.app ((pullback f).obj M)) ((tensorIso X).inv.naturality h)
  simp only [NatTrans.comp_app] at h₁ h₃
  have h₂' : ((tensor' Y).map ((derivedPushforward f).map h)).app M ≫
      projectionFormulaMap f (dual E) M =
      projectionFormulaMap f (dual E') M ≫
        (derivedPushforward f).map (((tensor' X).map h).app ((pullback f).obj M)) := h₂
  rw [projectionFormulaDualIso_hom, projectionFormulaDualIso_hom]
  exact comp_eq_comp_of_three_squares _ h₁ h₂' h₃

variable (hP : Stacks.Cohomology.PerfectComplexes.IsPerfect (X := Y.toRingedSpace)
  ((derivedPushforward f).obj (dual E)))

/-- **`Rf_*(E ⊗^L ω) ≅ (Rf_*E^∨)^∨`** for a perfect `E` with `Rf_*E^∨` perfect, `ω = a(𝒪_Y)`. The
first display of the proof of [Stacks, Tag 0E4L]. -/
def pushforwardTensorDualIso :
    letI := monoidal X
    (derivedPushforward f).obj (E ⊗ (relativeDualizingComplex f).obj) ≅
      dual ((derivedPushforward f).obj (dual E)) := by
  letI := monoidal X
  letI := monoidal Y
  letI := symmetric Y
  letI : ExactPairing E (dual E) := exactPairingDual E hE
  letI : ExactPairing ((derivedPushforward f).obj (dual E))
      (dual ((derivedPushforward f).obj (dual E))) := exactPairingDual _ hP
  have hEω : DerivedCategoryB.derivedCategoryB (A := X.Modules)
      (SheafOfModules.isQuasicoherent X.ringCatSheaf) (E ⊗ (relativeDualizingComplex f).obj) :=
    AlgebraicGeometry.isQuasicoherent_homology_derivedTensor_obj_obj X _ _
      (isQuasicoherent_homology_of_isPerfect E hE) (relativeDualizingComplex f).property
  exact RelativeDuality.tensorDualIsoOfEq (pullbackAdjunction f)
    (isQuasicoherent_homology_derivedPushforward f)
    (twistedInverseImageAdjunction f (isQuasicoherent_homology_derivedPushforward f))
    (structureSheaf Y) (Iso.refl _) E (dual E) (dual ((derivedPushforward f).obj (dual E)))
    (curriedTensor_monoidal X) (curriedTensor_monoidal Y)
    (isQuasicoherent_dual_tensor_pullback f E hE) (projectionFormulaDualIso f E hE)
    (projectionFormulaDualIso_naturality f E hE)
    (isQuasicoherent_homology_derivedPushforward f ⟨_, hEω⟩)
    (Stacks.DerivedQCoh.isQuasicoherent_homology_derivedDual Y _ hP)

end Dual

end Stacks.Duality.StandardModel

end
