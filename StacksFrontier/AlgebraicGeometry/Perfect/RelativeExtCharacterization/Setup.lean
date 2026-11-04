module

public import StacksFrontier.AlgebraicGeometry.Perfect.RelativeDerivedHomDualCore
public import StacksFrontier.Topology.Sheaves.Cohomology.DerivedPushforward.ProjectionFormulaQCoh
public import StacksFrontier.Topology.Sheaves.Cohomology.DerivedPushforward.ProjectionFormulaUnitKFlat
public import StacksFrontier.Topology.Sheaves.Cohomology.DerivedPushforward.InternalHomPullbackMap
public import StacksFrontier.Topology.Sheaves.Cohomology.InternalHom.DerivedTensorInternalHom
public import StacksFrontier.Topology.Sheaves.Cohomology.InternalHom.DerivedTensorHomDiagonalPerfect
public import StacksFrontier.Topology.Sheaves.Cohomology.InternalHom.PerfectBidual
public import StacksFrontier.Topology.Sheaves.Cohomology.InternalHom.PerfectDual
public import StacksFrontier.Topology.Sheaves.Cohomology.InternalHomEvaluation.PerfectEvaluation
public import StacksFrontier.Topology.Sheaves.Cohomology.InternalHomEvaluation.DerivedEvaluation
public import StacksFrontier.Topology.Sheaves.Cohomology.InternalHom.DerivedApplicationCompositionReduction
public import StacksFrontier.Topology.Sheaves.Cohomology.InternalHom.CompositionApplicationLawGeneral
public import StacksFrontier.Topology.Sheaves.Cohomology.InternalHom.DerivedTensorHomAdjunctionOnARingedSpace
public import StacksFrontier.CategoryTheory.Sites.Cohomology.DerivedTensor.ModelComparison
import StacksCore.Tactic.EgaSgaAttribute

/-!
# Vocabulary for the relative `Ext` characterization of [Stacks, Tag 0DJV]

Names, at the standard model of the derived categories of modules on a scheme, for the derived
internal Hom `R𝓗om(A, B)` and the maps it induces in each variable, for the diagonal
`K ⊗^L R𝓗om(M, L) ⟶ R𝓗om(M, K ⊗^L L)` of [Stacks, Tag 0BYS] (invertible for a perfect `M`,
[Stacks, Tag 0ATN]), for evaluation and biduality `M ≅ (M^∨)^∨` of a perfect object
([Stacks, Tags 0A8U, 08DQ]), and the derived tensor product the projection formula is stated
with, together with its comparison with the one of the monoidal structure.

## Main definitions

* `Stacks.AlgebraicGeometry.RelativeExtCharacterization.bidualIso`: biduality, natural in `M`
  (`bidualIso_hom_naturality`).
* `Stacks.AlgebraicGeometry.RelativeExtCharacterization.dualHomIso`:
  `R𝓗om(M^∨, N) ≅ N ⊗^L M` for a perfect `M`, natural in `M` and `N`.
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits Opposite MonoidalCategory
open AlgebraicGeometry

universe u

attribute [local implicit_reducible] TopCat.Sheaf structureSheafRing CategoryTheory.sheafCompose
  AlgebraicGeometry.SheafedSpace.sheaf

namespace Stacks.AlgebraicGeometry.RelativeExtCharacterization

open Stacks.SheafOfModules Stacks.AlgebraicGeometry.RelativeDerivedHomDual

attribute [local instance] derivedMonoidalStructure derivedSymmetricStructure

/-- `R𝓗om(A, B)` on `D(𝒪_Z)`. -/
abbrev rhom {Z : Scheme.{u}} (A B : DStd Z) : DStd Z := ((derivedSheafHom Z.sheaf).obj (op A)).obj B

/-- The map `R𝓗om(A', B) ⟶ R𝓗om(A, B)` induced by `a : A ⟶ A'`. -/
abbrev rhomMapL {Z : Scheme.{u}} {A A' : DStd Z} (a : A ⟶ A') (B : DStd Z) :
    rhom A' B ⟶ rhom A B :=
  ((derivedSheafHom Z.sheaf).map a.op).app B

/-- The map `R𝓗om(A, B) ⟶ R𝓗om(A, B')` induced by `b : B ⟶ B'`. -/
abbrev rhomMapR {Z : Scheme.{u}} (A : DStd Z) {B B' : DStd Z} (b : B ⟶ B') :
    rhom A B ⟶ rhom A B' :=
  ((derivedSheafHom Z.sheaf).obj (op A)).map b

/-- The diagonal `K ⊗ R𝓗om(M, L) ⟶ R𝓗om(M, K ⊗ L)` of [Stacks, Tag 0BYS]. -/
abbrev diag {Z : Scheme.{u}} (K L M : DStd Z) : K ⊗ rhom M L ⟶ rhom M (K ⊗ L) :=
  RingedSite.derivedTensorHomDiagonal (ringedSite Z.sheaf) K L M

/-- The diagonal `K ⊗ R𝓗om(M, L) ⟶ R𝓗om(M, K ⊗ L)` is an isomorphism for a perfect `M`. -/
theorem isIso_diag {Z : Scheme.{u}} (K L M : DStd Z) (hM : IsPerfectSite M) :
    IsIso (diag K L M) :=
  RingedSite.isIso_derivedTensorHomDiagonal_of_isPerfect (ringedSite Z.sheaf) K L M hM

/-- The diagonal is natural in `M`. -/
@[reassoc]
theorem diag_natural_hom {Z : Scheme.{u}} (K L : DStd Z) {M M' : DStd Z} (g : M' ⟶ M) :
    K ◁ rhomMapL g L ≫ diag K L M' = diag K L M ≫ rhomMapL g (K ⊗ L) :=
  RingedSite.derivedTensorHomDiagonal_natural_hom (ringedSite Z.sheaf) K L g

/-- The diagonal is natural in `K`. -/
@[reassoc]
theorem diag_natural_left {Z : Scheme.{u}} (L M : DStd Z) {K K' : DStd Z} (g : K ⟶ K') :
    g ▷ rhom M L ≫ diag K' L M = diag K L M ≫ rhomMapR M (g ▷ L) :=
  RingedSite.derivedTensorHomDiagonal_natural_left (ringedSite Z.sheaf) L M g

/-- The diagonal is natural in `L`. -/
@[reassoc]
theorem diag_natural_right {Z : Scheme.{u}} (K M : DStd Z) {L L' : DStd Z} (g : L ⟶ L') :
    K ◁ rhomMapR M g ≫ diag K L' M = diag K L M ≫ rhomMapR M (K ◁ g) :=
  RingedSite.derivedTensorHomDiagonal_natural_right (ringedSite Z.sheaf) K M g

/-- The dual `R𝓗om(M, 𝒪)` of a perfect `M` is perfect. -/
theorem isPerfectStd_dual {Z : Scheme.{u}} (M : DStd Z) (hM : IsPerfectSite M) :
    IsPerfectSite (rhom M (unitObj Z)) :=
  isPerfect_derivedDual Z.sheaf M hM

/-- Evaluation `R𝓗om(𝒪, 𝒪) ⊗ K ⟶ R𝓗om(R𝓗om(K, 𝒪), 𝒪)` of [Stacks, Tag 0A8U] at
`L = M = 𝒪`. -/
abbrev ev {Z : Scheme.{u}} (K : DStd Z) :
    rhom (unitObj Z) (unitObj Z) ⊗ K ⟶ rhom (rhom K (unitObj Z)) (unitObj Z) :=
  derivedSheafHomEvaluation Z.sheaf K (unitObj Z) (unitObj Z)

/-- Evaluation is natural in `K`. -/
theorem ev_naturality {Z : Scheme.{u}} {K K' : DStd Z} (φ : K ⟶ K') :
    rhom (unitObj Z) (unitObj Z) ◁ φ ≫ ev K' =
      ev K ≫ rhomMapL (rhomMapL φ (unitObj Z)) (unitObj Z) := by
  have hev := derivedSheafHomEvaluation_natural Z.sheaf φ (𝟙 (unitObj Z)) (𝟙 (unitObj Z))
  have e1 : derivedSheafHomMap Z.sheaf (𝟙 (unitObj Z)) (𝟙 (unitObj Z)) =
      𝟙 (rhom (unitObj Z) (unitObj Z)) :=
    @RingedSite.derivedSheafHomMap_id (ringedSite Z.sheaf)
      (HasDerivedCategory.standard _)
      (derivedInternalHom Z.sheaf) (unitObj Z) (unitObj Z)
  have e2 : derivedTensorMap Z.sheaf (𝟙 (rhom (unitObj Z) (unitObj Z))) φ =
      rhom (unitObj Z) (unitObj Z) ◁ φ :=
    @RingedSite.derivedTensorMap_id_left (ringedSite Z.sheaf) _ _ _ _ _
      (HasDerivedCategory.standard _)
      _ _ _ _ φ
  have e3 : ∀ {A A' : DStd Z} (a : A ⟶ A'),
      derivedSheafHomMap Z.sheaf a (𝟙 (unitObj Z)) = rhomMapL a (unitObj Z) := fun a ↦
    @RingedSite.derivedSheafHomMap_id_right (ringedSite Z.sheaf)
      (HasDerivedCategory.standard _)
      (derivedInternalHom Z.sheaf) _ _ a (unitObj Z)
  rw [e1, e2, e3, e3] at hev
  exact hev

/-- The trivialisation `𝒪 ≅ R𝓗om(𝒪, 𝒪)`. -/
abbrev unitHomIso (Z : Scheme.{u}) : unitObj Z ≅ rhom (unitObj Z) (unitObj Z) :=
  (derivedDualStructureSheafIso Z.sheaf).symm

/-- **Biduality** `M ≅ (M^∨)^∨` for a perfect `M` ([Stacks, Tag 08DQ]): the left unitor, the
trivialisation of `R𝓗om(𝒪, 𝒪)` and evaluation, which is invertible at a perfect object
([Stacks, Tag 0G40]). -/
@[sga "5 III 6.2" "special case"]
def bidualIso {Z : Scheme.{u}} (M : DStd Z) (hM : IsPerfectSite M) :
    M ≅ rhom (rhom M (unitObj Z)) (unitObj Z) :=
  (λ_ M).symm ≪≫ whiskerRightIso (unitHomIso Z) M ≪≫
    @asIso _ _ _ _ (ev M) (derivedSheafHomEvaluation_isIso_of_isPerfect Z.sheaf _ _ _ hM)

/-- The forward map of `bidualIso` is the inverse left unitor, followed by the trivialisation of
`R𝓗om(𝒪, 𝒪)` and evaluation. -/
theorem bidualIso_hom {Z : Scheme.{u}} (M : DStd Z) (hM : IsPerfectSite M) :
    (bidualIso M hM).hom = (λ_ M).inv ≫ (unitHomIso Z).hom ▷ M ≫ ev M := rfl

/-- **Biduality is natural.** -/
theorem bidualIso_hom_naturality {Z : Scheme.{u}} {K K' : DStd Z} (φ : K ⟶ K')
    (hK : IsPerfectSite K) (hK' : IsPerfectSite K') :
    φ ≫ (bidualIso K' hK').hom =
      (bidualIso K hK).hom ≫ rhomMapL (rhomMapL φ (unitObj Z)) (unitObj Z) := by
  rw [bidualIso_hom, bidualIso_hom, ← Category.assoc φ, leftUnitor_inv_naturality,
    Category.assoc, ← Category.assoc (_ ◁ φ), whisker_exchange, Category.assoc,
    ev_naturality]
  simp only [Category.assoc]

/-- Precomposition with an isomorphism `A ≅ B` is a bijection `(B ⟶ Y) → (A ⟶ Y)`. -/
theorem bijective_iso_comp {C : Type*} [Category C] {A B Y : C} (e : A ≅ B) :
    Function.Bijective (fun x : B ⟶ Y ↦ e.hom ≫ x) :=
  ⟨fun a b h ↦ by simpa using congrArg (e.inv ≫ ·) h, fun y ↦ ⟨e.inv ≫ y, by simp⟩⟩

/-- Postcomposition with an isomorphism `A ≅ B` is a bijection `(Y ⟶ A) → (Y ⟶ B)`. -/
theorem bijective_comp_iso {C : Type*} [Category C] {A B Y : C} (e : A ≅ B) :
    Function.Bijective (fun x : Y ⟶ A ↦ x ≫ e.hom) :=
  ⟨fun a b h ↦ by simpa using congrArg (· ≫ e.inv) h, fun y ↦ ⟨y ≫ e.inv, by simp⟩⟩

section BaseSide

variable {S : Scheme.{u}}

/-- `R𝓗om(M^∨, N) ≅ N ⊗ M` for a perfect `M`: the inverse of the diagonal of
[Stacks, Tag 0BYS] at the perfect source `M^∨`, followed by biduality. -/
def dualHomIso (M : DStd S) (hM : IsPerfectSite M) (N : DStd S) :
    rhom (rhom M (unitObj S)) N ≅ N ⊗ M :=
  haveI := isIso_diag N (unitObj S) _ (isPerfectStd_dual M hM)
  ((derivedSheafHom S.sheaf).obj (op (rhom M (unitObj S)))).mapIso (ρ_ N).symm ≪≫
    (asIso (diag N (unitObj S) (rhom M (unitObj S)))).symm ≪≫
    whiskerLeftIso N (bidualIso M hM).symm

/-- The forward map of `dualHomIso` is the inverse right unitor, followed by the inverse of the
diagonal and the inverse of biduality. -/
theorem dualHomIso_hom (M : DStd S) (hM : IsPerfectSite M) (N : DStd S) :
    haveI := isIso_diag N (unitObj S) _ (isPerfectStd_dual M hM)
    (dualHomIso M hM N).hom =
      rhomMapR _ (ρ_ N).inv ≫ inv (diag N (unitObj S) (rhom M (unitObj S))) ≫
        N ◁ (bidualIso M hM).inv := rfl

/-- `dualHomIso` is natural in `N`. -/
theorem dualHomIso_naturality_right (M : DStd S) (hM : IsPerfectSite M) {N N' : DStd S}
    (g : N ⟶ N') :
    rhomMapR _ g ≫ (dualHomIso M hM N').hom = (dualHomIso M hM N).hom ≫ g ▷ M := by
  have := isIso_diag N (unitObj S) _ (isPerfectStd_dual M hM)
  have := isIso_diag N' (unitObj S) _ (isPerfectStd_dual M hM)
  rw [dualHomIso_hom, dualHomIso_hom]
  have h1 : rhomMapR (rhom M (unitObj S)) g ≫ rhomMapR _ (ρ_ N').inv =
      rhomMapR _ (ρ_ N).inv ≫ rhomMapR _ (g ▷ unitObj S) := by
    simp only [← Functor.map_comp, rightUnitor_inv_naturality]
    rfl
  have h2 := diag_natural_left (unitObj S) (rhom M (unitObj S)) g
  rw [← Category.assoc, h1, Category.assoc, Category.assoc]
  congr 1
  rw [← cancel_epi (diag N (unitObj S) (rhom M (unitObj S))), ← reassoc_of% h2]
  simp [whisker_exchange]

/-- `dualHomIso` is natural in `M`. -/
theorem dualHomIso_naturality_left {M M' : DStd S} (m : M' ⟶ M) (hM : IsPerfectSite M)
    (hM' : IsPerfectSite M') (N : DStd S) :
    rhomMapL (rhomMapL m (unitObj S)) N ≫ (dualHomIso M hM N).hom =
      (dualHomIso M' hM' N).hom ≫ N ◁ m := by
  have := isIso_diag N (unitObj S) _ (isPerfectStd_dual M hM)
  have := isIso_diag N (unitObj S) _ (isPerfectStd_dual M' hM')
  rw [dualHomIso_hom, dualHomIso_hom]
  have h1 : rhomMapL (rhomMapL m (unitObj S)) N ≫ rhomMapR _ (ρ_ N).inv =
      rhomMapR _ (ρ_ N).inv ≫ rhomMapL (rhomMapL m (unitObj S)) (N ⊗ unitObj S) :=
    (((derivedSheafHom S.sheaf).map (rhomMapL m (unitObj S)).op).naturality (ρ_ N).inv).symm
  have h2 := diag_natural_hom N (unitObj S) (rhomMapL m (unitObj S))
  have h3 := bidualIso_hom_naturality m hM' hM
  rw [← Category.assoc, h1, Category.assoc, Category.assoc]
  congr 1
  rw [← cancel_epi (diag N (unitObj S) (rhom M' (unitObj S))), ← reassoc_of% h2]
  simp only [IsIso.hom_inv_id_assoc, Category.assoc, ← MonoidalCategory.whiskerLeft_comp]
  congr 1
  rw [Iso.comp_inv_eq, Category.assoc, h3, Iso.inv_hom_id_assoc]

end BaseSide

variable {X S : Scheme.{u}} (f : X ⟶ S)

/-- The derived tensor product of the projection formula, at the standard model. -/
abbrev tensorPF (Z : Scheme.{u}) : DStd Z ⥤ DStd Z ⥤ DStd Z :=
  @Stacks.DerivedTensor.RingedSite.derivedTensorProductFunctor _ _ _ Z.sheaf _ _
    (HasDerivedCategory.standard _) _ _ _

/-- The two derived tensor products agree. -/
def tensorPFIso (Z : Scheme.{u}) : tensorPF Z ≅ derivedTensor Z.sheaf :=
  @Stacks.DerivedTensor.RingedSite.derivedTensorProductFunctorIsoSheafOfModules
    (ringedSite Z.sheaf) _ _ (HasDerivedCategory.standard _) _ _ _

end Stacks.AlgebraicGeometry.RelativeExtCharacterization
