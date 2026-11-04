module

public import Mathlib.Algebra.Homology.DerivedCategory.FullyFaithful
public import StacksFrontier.Algebra.Category.ModuleCat.Sheaf.UnitEndomorphismsCommute
public import StacksFrontier.AlgebraicGeometry.ClosedPushforward.Basic
public import StacksFrontier.AlgebraicGeometry.Duality.ClosedImmersionRightAdjointSheafHom
public import StacksFrontier.AlgebraicGeometry.Duality.ClosedImmersionRightAdjointSheafHomLocallySmall
public import StacksFrontier.AlgebraicGeometry.Duality.RelativeDualizingComplexCriterion
public import StacksFrontier.AlgebraicGeometry.Duality.UpperShriekDiagonal
public import StacksFrontier.AlgebraicGeometry.Duality.UpperShriekFlatDualizing
public import StacksFrontier.CategoryTheory.CurriedActionIsIso
public import StacksFrontier.Homology.DerivedCategory.ModelComparisonTransport

/-!
# `f^!𝒪_Y` is a relative dualizing complex

Let `S` be Noetherian and `f : X ⟶ Y` a flat morphism of `FTS S`. Then `f^!𝒪_Y`, at any
compactification, is the first component of a relative dualizing complex for `X` over `Y`
([Stacks, Tag 0E9W]), for every open `W ⊆ X ×_Y X` through which the diagonal factors as a closed
immersion.

## Main results

* `Stacks.Duality.isRankOneHom_diagonalObject` — `Hom(Δ_*𝒪_X, L pr₁^* f^!𝒪_Y|_W)` is free of rank
  one over the commutative ring `End(Δ_*𝒪_X)`.
* `Stacks.Duality.exists_isRelativeDualizingComplex_upperShriek` — [Stacks, Tag 0E9W].
-/

-- This file uses the locally small derived-category models below, which are not
-- global instances (see `StacksFrontier.Homology.DerivedCategory.LocallySmall`):
-- `D(R)` for sheaves of modules on a small site.
-- `D(𝒪_X)` for a scheme.
attribute [local instance] SheafOfModules.hasDerivedCategory
attribute [local instance] AlgebraicGeometry.Scheme.Modules.hasDerivedCategory

@[expose] public noncomputable section

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits RingedSpaceModuleAdjunction

universe u

namespace Stacks.Duality

section ClosedImmersion

variable {Z W : Scheme.{u}} (i : Z ⟶ W) [IsClosedImmersion i]

/-- The endomorphisms of `𝒪_Z` in `D(𝒪_Z)` commute. -/
theorem derivedStructureSheaf_endomorphisms_commute
    (c d : DerivedPushforward.derivedStructureSheaf Z ⟶
      DerivedPushforward.derivedStructureSheaf Z) : c ≫ d = d ≫ c := by
  obtain ⟨c₀, hc⟩ := (DerivedCategory.singleFunctor Z.Modules 0).map_surjective c.hom
  obtain ⟨d₀, hd⟩ := (DerivedCategory.singleFunctor Z.Modules 0).map_surjective d.hom
  refine ObjectProperty.hom_ext _ ?_
  show c.hom ≫ d.hom = d.hom ≫ c.hom
  rw [← hc, ← hd]
  exact ((DerivedCategory.singleFunctor Z.Modules 0).map_comp c₀ d₀).symm.trans
    ((congrArg (DerivedCategory.singleFunctor Z.Modules 0).map
      (SheafOfModules.unit_endomorphisms_commute (fun U a b => mul_comm a b) c₀ d₀)).trans
      ((DerivedCategory.singleFunctor Z.Modules 0).map_comp d₀ c₀))

/-- `Ri_*` restricted to the structure sheaf in degree zero is full: it is `i_*` followed by the
degree-zero functor, both full ([Stacks, Tag 08KS]). -/
instance full_singleFunctor_comp_derivedPushforward :
    (DerivedCategory.singleFunctor Z.Modules 0 ⋙ derivedPushforward i).Full := by
  have : (modulePushforward (Stacks.Duality.closedQuotient i).i).Full :=
    (RingedSpaceModuleAdjunction.ClosedQuotientMorphismOfRingedSpaces.fullyFaithfulModulePushforward
      (Stacks.Duality.closedQuotient i)).full
  have : (DerivedCategory.singleFunctor
      (SheafOfModules (structureSheafRing (Stacks.Duality.closedQuotient i).X)) 0).Full :=
    inferInstance
  have hF : (modulePushforward (Stacks.Duality.closedQuotient i).i ⋙ DerivedCategory.singleFunctor
      (SheafOfModules (structureSheafRing (Stacks.Duality.closedQuotient i).X)) 0).Full :=
    Functor.Full.comp _ _
  exact @Functor.Full.of_iso _ _ _ _ _ _ hF
    (((modulePushforward (Stacks.Duality.closedQuotient i).i).mapDerivedCategorySingleFunctor
      0).symm ≪≫
      Functor.isoWhiskerLeft _ (LocallySmall.closedImmersionPushforwardModelIso i))

/-- `Ri_*` is surjective on the endomorphisms of `𝒪_Z` in `D_QCoh`. -/
theorem surjective_quasiCoherentDerivedPushforward_map_derivedStructureSheaf
    (hpush : ∀ (K : quasiCoherentDerivedCategory Z) (n : ℤ),
      ((DerivedCategory.homologyFunctor W.Modules n).obj
        ((derivedPushforward i).obj K.obj)).IsQuasicoherent) :
    Function.Surjective (fun c : DerivedPushforward.derivedStructureSheaf Z ⟶
        DerivedPushforward.derivedStructureSheaf Z =>
      (quasiCoherentDerivedPushforward i hpush).map c) := by
  intro c'
  obtain ⟨c₀, hc₀⟩ :=
    (DerivedCategory.singleFunctor Z.Modules 0 ⋙ derivedPushforward i).map_surjective c'.hom
  exact ⟨ObjectProperty.homMk ((DerivedCategory.singleFunctor Z.Modules 0).map c₀),
    ObjectProperty.hom_ext _ hc₀⟩

/-- `i_*𝒪_Z` is the underlying `𝒪_W`-module of the sheaf of algebras `i_*𝒪_Z`. -/
def modulePushforwardUnitIso :
    (modulePushforward (Stacks.Duality.closedQuotient i).i).obj
        (SheafOfModules.unit (structureSheafRing Z.toRingedSpace)) ≅
      RelativeSpec.AlgebraSheaf.moduleOfAlgebra (AffineAlgebraEquivalence.pushforwardAlgebra i) :=
  Iso.refl _

/-- **`R ℰom(𝒪_Z, -)` read at the two models.** The right derived functor of sheaf Hom with exact
support at the standard model and at the locally small model agree up to the comparison
equivalences. -/
def derivedSheafHomExactSupportModelIso :
    (Stacks.Duality.closedQuotient i).derivedSheafHomExactSupport ⋙
        (Stacks.Injectives.grothendieckModelEquiv
          (SheafOfModules.{u} (structureSheafRing (Stacks.Duality.closedQuotient i).Z))).functor ≅
      (Stacks.Injectives.grothendieckModelEquiv
          (SheafOfModules.{u} (structureSheafRing (Stacks.Duality.closedQuotient i).X))).functor ⋙
        LocallySmall.derivedSheafHomExactSupport i :=
  StacksDraft.DerivedModel.rightDerivedModelIso
    (HomotopyCategory.quasiIso
      (SheafOfModules.{u} (structureSheafRing (Stacks.Duality.closedQuotient i).X))
      (ComplexShape.up ℤ))
    (Stacks.Duality.closedQuotient i).derivedSheafHomExactSupportComparison
    (LocallySmall.derivedSheafHomExactSupportComparison i)
    (StacksDraft.DerivedModel.shrinkComparisonQhIso
      (SheafOfModules.{u} (structureSheafRing (Stacks.Duality.closedQuotient i).X))).symm
    (Functor.associator _ _ _ ≪≫
      Functor.isoWhiskerLeft _ (StacksDraft.DerivedModel.shrinkComparisonQhIso
        (SheafOfModules.{u} (structureSheafRing (Stacks.Duality.closedQuotient i).Z))).symm)

end ClosedImmersion

section RankOne

variable {S : Scheme.{u}} [IsNoetherian S] {X Y : FTS S} (f : X ⟶ Y)
  (j : CompactificationOf (Over.mk f.left)) (D : f.left.DiagonalOpen) [Flat f.left]

open DiagonalUpperShriek in
/-- **`Hom(Δ_*𝒪_X, L p^* f^!𝒪_Y)` is free of rank one over `End(Δ_*𝒪_X)`** in `D_QCoh(𝒪_W)`,
`p = pr₁|_W`: by adjunction it is `Hom(𝒪_X, Δ^! L p^* f^!𝒪_Y) = Hom(𝒪_X, 𝒪_X)`
(`Stacks.Duality.diagonalUpperShriekIso`), and `Δ_*` is fully faithful on `𝒪_X`. -/
theorem isRankOneHom_quasiCoherentDerivedPushforward_diag :
    IsRankOneHom
      ((quasiCoherentDerivedPushforward D.diag
          (isQuasicoherent_homology_derivedPushforward_of_qcqs D.diag)).obj
        (DerivedPushforward.derivedStructureSheaf X.left))
      ((quasiCoherentDerivedPullback' D.proj).obj
        ((upperShriek f j).obj (DerivedPushforward.derivedStructureSheaf Y.left))) :=
  IsRankOneHom.of_adjunction
    (twistedInverseImageAdjunction D.diag
      (isQuasicoherent_homology_derivedPushforward_of_qcqs D.diag))
    (derivedStructureSheaf_endomorphisms_commute (Z := X.left))
    (surjective_quasiCoherentDerivedPushforward_map_derivedStructureSheaf D.diag _)
    (diagonalUpperShriekIso f j D)

/-- `Δ_*𝒪_X` in `D_QCoh(𝒪_W)` at the locally small model is the sheaf of algebras `Δ_*𝒪_X` in
degree zero, read at the standard model and carried over. -/
def quasiCoherentDerivedPushforwardDiagIso :
    ((quasiCoherentDerivedPushforward D.diag
        (isQuasicoherent_homology_derivedPushforward_of_qcqs D.diag)).obj
      (DerivedPushforward.derivedStructureSheaf X.left)).obj ≅
    (Stacks.Injectives.grothendieckModelEquiv D.W.Modules).functor.obj D.diagonalObject :=
  (LocallySmall.closedImmersionPushforwardModelIso D.diag).symm.app _ ≪≫
    ((modulePushforward (Stacks.Duality.closedQuotient D.diag).i).mapDerivedCategorySingleFunctor
      0).app _ ≪≫
    (DerivedCategory.singleFunctor _ 0).mapIso (modulePushforwardUnitIso D.diag)

/-- `L p^* f^!𝒪_Y` at the locally small model, carried from the standard model. -/
def quasiCoherentDerivedPullbackProjIso :
    ((quasiCoherentDerivedPullback' D.proj).obj
        ((upperShriek f j).obj (DerivedPushforward.derivedStructureSheaf Y.left))).obj ≅
    (Stacks.Injectives.grothendieckModelEquiv D.W.Modules).functor.obj
      (D.derivedPullbackProj (relativeDualizingComplexObj f j)) :=
  ((StacksDraft.DerivedModel.derivedPullbackModelIso D.proj.toLRSHom.toShHom).app
    (relativeDualizingComplexObj f j)).symm

/-- **`Hom(Δ_*𝒪_X, L pr₁^* f^!𝒪_Y|_W)` is free of rank one over `End(Δ_*𝒪_X)`**, at the standard
model of `D(𝒪_W)` at which relative dualizing complexes are stated. -/
theorem isRankOneHom_diagonalObject :
    IsRankOneHom D.diagonalObject (D.derivedPullbackProj (relativeDualizingComplexObj f j)) :=
  IsRankOneHom.of_fullyFaithful
    (Stacks.Injectives.grothendieckModelEquiv D.W.Modules).fullyFaithfulFunctor
    (((isRankOneHom_quasiCoherentDerivedPushforward_diag f j D).map
      (ObjectProperty.fullyFaithfulι _)).of_iso (quasiCoherentDerivedPushforwardDiagIso f D)
      (quasiCoherentDerivedPullbackProjIso f j D))

open DiagonalUpperShriek in
/-- **`R ℰom(𝒪_X, L p^* f^!𝒪_Y) ≅ 𝒪_X`** at the locally small model: `L p^* f^!𝒪_Y` is bounded
below, so `R ℰom(𝒪_X, -)` computes `Δ^!` on it ([Stacks, Tag 0A9X]), and
`Δ^! L p^* f^!𝒪_Y ≅ 𝒪_X` (`Stacks.Duality.diagonalUpperShriekIso`). -/
theorem nonempty_derivedSheafHomExactSupport_pullbackProj_iso :
    Nonempty ((LocallySmall.derivedSheafHomExactSupport D.diag).obj
        ((quasiCoherentDerivedPullback' D.proj).obj
          ((upperShriek f j).obj (DerivedPushforward.derivedStructureSheaf Y.left))).obj ≅
      (DerivedPushforward.derivedStructureSheaf X.left).obj) := by
  have hpc : PseudoCoherent D.diag := FTS.pseudoCoherent_left_of_isClosedImmersion (diagHom f D)
  have hq := isQuasicoherent_homology_derivedPushforward_of_qcqs D.diag
  obtain ⟨e⟩ := LocallySmall.isDerivedSheafHomRightAdjoint_of_pseudoCoherent D.diag hpc hq
    (twistedInverseImage D.diag hq) (twistedInverseImageAdjunction D.diag hq)
  have hbdd : DerivedCategoryB.IsBoundedBelow
      ((quasiCoherentDerivedPullback' D.proj).obj
        ((upperShriek f j).obj (DerivedPushforward.derivedStructureSheaf Y.left))).obj :=
    DerivedCategoryB.isBoundedBelow_of_iso ((ObjectProperty.ι _).mapIso
        (pullbackProjUpperShriekIso f j D).symm)
      (isBoundedBelow_upperShriek_obj (sndRestrict f D) (sndRestrictCompactification f j D) _
        (structureSheafPlus X.left).property)
  exact ⟨(e.app ⟨_, hbdd⟩).symm ≪≫ (ObjectProperty.ι _).mapIso (diagonalUpperShriekIso f j D)⟩

end RankOne

section DualIso

attribute [local instance 10000] HasDerivedCategory.standard

variable {S : Scheme.{u}} [IsNoetherian S] {X Y : FTS S} (f : X ⟶ Y)
  (j : CompactificationOf (Over.mk f.left)) (D : f.left.DiagonalOpen) [Flat f.left]

/-- `Δ_*𝒪_X` in `D(𝒪_W)` is `Ri_*𝒪_X` for the exact functor `i_*`, at the standard model. -/
def diagonalObjectIso :
    D.diagonalObject ≅
      (modulePushforward (Stacks.Duality.closedQuotient D.diag).i).mapDerivedCategory.obj
        (RingedSite.derivedStructureSheaf
          (Stacks.SheafOfModules.ringedSite (Stacks.Duality.closedQuotient D.diag).Z.sheaf)) :=
  (DerivedCategory.singleFunctor _ 0).mapIso (modulePushforwardUnitIso D.diag).symm ≪≫
    ((modulePushforward (Stacks.Duality.closedQuotient D.diag).i).mapDerivedCategorySingleFunctor
      0).symm.app _

/-- **`R ℰom(𝒪_X, L p^* f^!𝒪_Y) ≅ 𝒪_X` at the standard model**, carried over from the locally
small model (`nonempty_derivedSheafHomExactSupport_pullbackProj_iso`). -/
theorem nonempty_derivedSheafHomExactSupport_derivedPullbackProj_iso :
    Nonempty ((Stacks.Duality.closedQuotient D.diag).derivedSheafHomExactSupport.obj
        (D.derivedPullbackProj (relativeDualizingComplexObj f j)) ≅
      RingedSite.derivedStructureSheaf
        (Stacks.SheafOfModules.ringedSite (Stacks.Duality.closedQuotient D.diag).Z.sheaf)) := by
  obtain ⟨χ⟩ := nonempty_derivedSheafHomExactSupport_pullbackProj_iso f j D
  exact ⟨(Stacks.Injectives.grothendieckModelEquiv (SheafOfModules.{u}
      (structureSheafRing (Stacks.Duality.closedQuotient D.diag).Z))).fullyFaithfulFunctor
      |>.preimageIso
    ((derivedSheafHomExactSupportModelIso D.diag).app _ ≪≫
      (LocallySmall.derivedSheafHomExactSupport D.diag).mapIso
        (quasiCoherentDerivedPullbackProjIso f j D).symm ≪≫ χ)⟩

attribute [local instance] Stacks.Topology.SheafTensorAdditiveOnOpens.sheafTensorAdditive
  Stacks.Topology.SheafTensorAdditiveOnOpens.sheafTensorObjAdditive
  Stacks.Topology.SheafTensorAdditiveOnOpens.hasMapBifunctorSheafTensor

/-- **`Δ_*𝒪_X ≅ R𝓗om_{𝒪_W}(Δ_*𝒪_X, L p^* f^!𝒪_Y)`**: `R𝓗om(Δ_*𝒪_X, -) = Δ_* R ℰom(𝒪_X, -)`
([Stacks, Tag 0A77]) and `R ℰom(𝒪_X, L p^* f^!𝒪_Y) ≅ 𝒪_X`. -/
theorem nonempty_diagonalObject_iso_derivedSheafHom :
    Nonempty (D.diagonalObject ≅
      ((Stacks.SheafOfModules.derivedSheafHom D.W.sheaf).obj (Opposite.op D.diagonalObject)).obj
        (D.derivedPullbackProj (relativeDualizingComplexObj f j))) := by
  obtain ⟨χ⟩ := nonempty_derivedSheafHomExactSupport_derivedPullbackProj_iso f j D
  exact ⟨diagonalObjectIso f D ≪≫
    ((modulePushforward (Stacks.Duality.closedQuotient D.diag).i).mapDerivedCategory.mapIso
      χ).symm ≪≫
    (ClosedQuotientMorphismOfRingedSpaces.derivedSheafHomExactSupportPushforwardNatIso
      (Stacks.Duality.closedQuotient D.diag)).app _ ≪≫
    ((Stacks.SheafOfModules.derivedSheafHom D.W.sheaf).mapIso (diagonalObjectIso f D).op).app _⟩

end DualIso

section Main

attribute [local instance 10000] HasDerivedCategory.standard

variable {S : Scheme.{u}} [IsNoetherian S] {X Y : FTS S} (f : X ⟶ Y)
  (j : CompactificationOf (Over.mk f.left)) [Flat f.left]

/-- **Stacks Project, Tag 0E9W.** In Situation 48.16.1 (`S` Noetherian), let
`f : X ⟶ Y` be a flat morphism of `FTS S`, with `f^!` computed at any compactification `j`. Then
`f^!𝒪_Y` is the first component of a relative dualizing complex for `X` over `Y`
(Definition 0E2T): for every open `W ⊆ X ×_Y X` through which the diagonal factors as a closed
immersion `Δ : X ⟶ W` there is `ξ : Δ_*𝒪_X ⟶ L pr₁^* f^!𝒪_Y|_W` making `(f^!𝒪_Y, ξ)` a relative
dualizing complex. -/
@[stacks 0E9W]
theorem exists_isRelativeDualizingComplex_upperShriek (D : f.left.DiagonalOpen) :
    letI := locallyOfFinitePresentation_left f
    ∃ ξ : D.diagonalObject ⟶ D.derivedPullbackProj (relativeDualizingComplexObj f j),
      Scheme.Hom.IsRelativeDualizingComplex.{u + 1, u} f.left
        (RingedSpace.canonicalCertifiedDerivedSheafTensoringFamily _) D
        (relativeDualizingComplexObj f j) ξ := by
  let := locallyOfFinitePresentation_left f
  obtain ⟨ψ⟩ := nonempty_diagonalObject_iso_derivedSheafHom f j D
  have h := isRankOneHom_diagonalObject f j D
  obtain ⟨θ, hθ⟩ := h.2
  refine ⟨θ, ?_⟩
  constructor
  · exact (upperShriek_structureSheaf_isPerfectRelativeTo_and_isIso_homothety f j).1
  · exact D.isIso_diagonalAction_of_isRankOneHom _ h θ hθ ψ

end Main

end Stacks.Duality

end
