module

public import Mathlib.Algebra.Category.Grp.AB
public import Mathlib.Algebra.Category.ModuleCat.Products
public import Mathlib.Algebra.Category.ModuleCat.Projective
public import Mathlib.Algebra.Category.ModuleCat.Sheaf.Limits
public import Mathlib.Algebra.Category.ModuleCat.Sheaf.PullbackContinuous
public import Mathlib.Algebra.Category.ModuleCat.Stalk
public import Mathlib.Algebra.Homology.DerivedCategory.HomologySequence
public import Mathlib.Algebra.Homology.ShortComplex.ShortExact
public import Mathlib.CategoryTheory.Sites.Abelian
public import Mathlib.CategoryTheory.Sites.Point.Skyscraper
public import Mathlib.CategoryTheory.Sites.PreservesSheafification
public import Mathlib.LinearAlgebra.StdBasis
public import Mathlib.RingTheory.LocalRing.Module
public import Mathlib.RingTheory.LocalRing.RingHom.Basic
public import Mathlib.Topology.Sheaves.Module
public import Mathlib.Topology.Sheaves.Over
public import Mathlib.Topology.Sheaves.Points
public import StacksCore.Tactic.StacksAttribute
public import StacksFrontier.Algebra.Category.ModuleCat.Sheaf.StalkFreeCover
public import StacksFrontier.Algebra.Category.ModuleCat.Sheaf.ULiftFiniteColimits
public import StacksFrontier.CategoryTheory.Sites.UniverseLiftColimits
public import StacksFrontier.Topology.Sheaves.Cohomology.PerfectComplexes.Defs
public import StacksFrontier.Topology.Sheaves.Modules.LocallyFree
import StacksFrontier.Algebra.Homology.StrictlyPerfectLiftModuleUniverse
public import StacksFrontier.Topology.Sheaves.Cohomology.PerfectComplexes.FiniteFreeLocus.Locus

/-!
# Free charts near a point of the finite free locus of a strictly perfect complex

This file proves, for a strictly perfect complex `P` of `𝒪_X`-modules and a point `x` with
local stalk at which all cohomology stalks of `P` are finite free, that these stalks stay
finite free on an open neighbourhood of `x`, one ingredient of [Stacks, Tag 0GT1].

## Main ingredients

* Restriction of `𝒪_X`-modules to an open subspace preserves homology, and finite freeness of
  cohomology stalks passes in both directions along a local quasi-isomorphism.
* Transport of sheaves of modules along a homeomorphism of the underlying spaces preserves
  finite free stalks and free charts.
* [Stacks, Tag 0B8J] for the universe-lifted sheaves used here: a finitely presented sheaf of
  modules with a finite free stalk at a point is free on an open neighbourhood of that point.
  Applied to the opcycles of `P`, and to the homology of short complexes whose cokernel is a
  direct summand of a finite free module, this gives the neighbourhood.

## References

* [Stacks Project, Tag 0GT1](https://stacks.math.columbia.edu/tag/0GT1)
* [Stacks Project, Tag 0B8J](https://stacks.math.columbia.edu/tag/0B8J)
-/

@[expose] public noncomputable section

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits TopologicalSpace StrictlyPerfect
  AlgebraicGeometry.RingedSpace.PseudoCoherence

namespace Stacks.Cohomology.PerfectComplexes

universe u v d

attribute [local instance] HasDerivedCategory.standard

/-- `RingCat.{max u v}` has all colimits indexed by `v`-small categories. -/
local instance : HasColimitsOfSize.{v, v} RingCat.{max u v} :=
  hasColimitsOfSizeShrink.{v, v, max u v, max u v} _

section

universe u₁ v₁ u₂ v₂
open CategoryTheory.Functor

/-- Pushforward of sheaves of modules along a continuous and cocontinuous functor that is itself
a left adjoint, taken along an isomorphism of sheaves of rings, is a left adjoint. -/
lemma pushforward_isLeftAdjoint
    {C : Type u₁} [Category.{v₁} C] {D : Type u₂} [Category.{v₂} D]
    {J : GrothendieckTopology C} {K : GrothendieckTopology D} {F : C ⥤ D}
    {S : Sheaf J RingCat.{u}} {R : Sheaf K RingCat.{u}}
    [F.IsContinuous J K] [F.IsCocontinuous J K] [F.IsLeftAdjoint]
    (φ : S ⟶ (F.sheafPushforwardContinuous RingCat.{u} J K).obj R) (hφ : IsIso φ) :
    (SheafOfModules.pushforward.{v} φ).IsLeftAdjoint := by
  have := hφ
  let adj := Adjunction.ofIsLeftAdjoint F
  let shAdj := adj.sheafPushforwardContinuous (E := RingCat.{u}) J K
  let ψ : R ⟶ (F.rightAdjoint.sheafPushforwardContinuous RingCat.{u} K J).obj S :=
    shAdj.unit.app R ≫ (F.rightAdjoint.sheafPushforwardContinuous _ _ _).map (inv φ)
  have key₁ : ψ ≫ (F.rightAdjoint.sheafPushforwardContinuous RingCat.{u} K J).map φ =
      shAdj.unit.app R := by
    simp only [ψ, Category.assoc, ← Functor.map_comp, IsIso.inv_hom_id,
      CategoryTheory.Functor.map_id]
    exact Category.comp_id _
  have key₂ : φ ≫ (F.sheafPushforwardContinuous RingCat.{u} J K).map ψ ≫
      shAdj.counit.app S = 𝟙 S := by
    rw [show ψ = shAdj.unit.app R ≫
        (F.rightAdjoint.sheafPushforwardContinuous RingCat.{u} K J).map (inv φ) from rfl,
      Functor.map_comp, Category.assoc, shAdj.counit_naturality (inv φ),
      shAdj.left_triangle_components_assoc, IsIso.hom_inv_id]
  have hu : (shAdj.unit.app R).hom = whiskerRight (NatTrans.op adj.counit) R.obj := rfl
  exact (SheafOfModules.pushforwardPushforwardAdj.{v} adj φ ψ
    (hu.symm.trans (congrArg (fun α => α.hom) key₁.symm))
    (congrArg (fun α => α.hom) key₂)).isLeftAdjoint

/-- Restriction of `𝒪_X`-modules to an open subspace preserves homology. -/
lemma restrictModules_preservesHomology (X : RingedSpace.{u, v}) (U : Opens X) :
    (restrictModules X U).PreservesHomology := by
  let J := Opens.grothendieckTopology (X.restrict U.isOpenEmbedding).carrier
  let K := Opens.grothendieckTopology X.carrier
  let F := U.isOpenEmbedding.functor
  let : F.IsContinuous J K := U.isOpenEmbedding.functor_isContinuous
  let : F.IsLeftAdjoint := U.isOpenEmbedding.isOpenMap.adjunction.isLeftAdjoint
  let : F.IsCocontinuous J K :=
    (U.isOpenEmbedding.isOpenMap.adjunction.isCocontinuous_iff_coverPreserving J K).mpr
      (coverPreserving_opens_map _)
  let R := structureSheafOfRings (X.restrict U.isOpenEmbedding)
  let : (restrictModules X U).IsLeftAdjoint := pushforward_isLeftAdjoint _ (IsIso.id _)
  let : PreservesFiniteColimits (restrictModules X U) := inferInstance
  let : PreservesFiniteLimits (restrictModules X U) := by
    let A := SheafOfModules.toSheaf.{v} (structureSheafOfRings X) ⋙
      sheafToPresheaf K Ab.{v}
    let G := SheafOfModules.toSheaf.{v} R ⋙ sheafToPresheaf J Ab.{v}
    let B := (whiskeringLeft _ _ Ab.{v}).obj F.op
    let : PreservesFiniteLimits A := by dsimp [A]; infer_instance
    let : PreservesFiniteLimits B := by dsimp [B]; infer_instance
    have hAB : PreservesFiniteLimits (A ⋙ B) := comp_preservesFiniteLimits A B
    let e : restrictModules X U ⋙ G ≅ A ⋙ B := Iso.refl _
    have : PreservesFiniteLimits (restrictModules X U ⋙ G) :=
      preservesFiniteLimits_of_natIso (F := A ⋙ B) e.symm
    exact preservesFiniteLimits_of_reflects_of_preserves _ G
  infer_instance

/-- A quasi-isomorphism of complexes induces isomorphisms on homology in every degree. -/
private lemma isIso_homologyMap_of_quasiIso
    {X : RingedSpace.{u, v}} {K L : CochainComplex (OXMod.{u, v} X) ℤ}
    (f : K ⟶ L) [hf : QuasiIso f] (i : ℤ) :
    IsIso (HomologicalComplex.homologyMap f i) :=
  (quasiIsoAt_iff_isIso_homologyMap f i).mp (hf.quasiIsoAt i)

/-- For a quasi-isomorphism from a complex `P` to the restriction of `K` to an open set, finite
freeness of the cohomology stalks of `P` and of `K` are equivalent. -/
private lemma finite_free_homology_stalk_iff_of_local_quasiIso
    {X : RingedSpace.{u, v}} (K : CochainComplex (OXMod.{u, v} X) ℤ) (U : Opens X)
    (P : CochainComplex (OXMod.{u, v} (X.restrict U.isOpenEmbedding)) ℤ)
    (f : P ⟶ ((restrictModules X U).mapHomologicalComplex
      (ComplexShape.up ℤ)).obj K) [QuasiIso f] (x : U) (i : ℤ) :
    (Module.Finite (structureSheafStalk (X.restrict U.isOpenEmbedding) x)
        (moduleSheafStalk (P.homology i) x) ∧
      Module.Free (structureSheafStalk (X.restrict U.isOpenEmbedding) x)
        (moduleSheafStalk (P.homology i) x)) ↔
    Module.Finite (structureSheafStalk X x) (moduleSheafStalk (K.homology i) x) ∧
      Module.Free (structureSheafStalk X x) (moduleSheafStalk (K.homology i) x) := by
  let F := restrictModules X U
  let : F.PreservesHomology := restrictModules_preservesHomology X U
  let : IsIso (HomologicalComplex.homologyMap f i) := isIso_homologyMap_of_quasiIso f i
  let e := asIso (HomologicalComplex.homologyMap f i) ≪≫ (K.sc i).mapHomologyIso F
  have h₁ := finite_free_stalk_iff_of_iso e x
  have h₂ := finite_free_sheafColimit_iff_stalk (F.obj (K.homology i)) x
  have h₃ := finite_free_stalk_restrict_iff (K.homology i) U x
  exact ⟨fun h => h₃.mp (h₂.mpr (h₁.mp h)), fun h => h₁.mpr (h₂.mp (h₃.mpr h))⟩

/-- Finite freeness of the cohomology stalks passes from a complex to a complex mapping
quasi-isomorphically to its restriction to an open set. -/
lemma finite_free_homology_stalk_of_local_quasiIso
    {X : RingedSpace.{u, v}} (K : CochainComplex (OXMod.{u, v} X) ℤ) (U : Opens X)
    (P : CochainComplex (OXMod.{u, v} (X.restrict U.isOpenEmbedding)) ℤ)
    (f : P ⟶ ((restrictModules X U).mapHomologicalComplex
      (ComplexShape.up ℤ)).obj K) [QuasiIso f] (x : U)
    (hH : ∀ i, Module.Finite (structureSheafStalk X x) (moduleSheafStalk (K.homology i) x) ∧
      Module.Free (structureSheafStalk X x) (moduleSheafStalk (K.homology i) x)) (i : ℤ) :
    Module.Finite (structureSheafStalk (X.restrict U.isOpenEmbedding) x)
        (moduleSheafStalk (P.homology i) x) ∧
      Module.Free (structureSheafStalk (X.restrict U.isOpenEmbedding) x)
        (moduleSheafStalk (P.homology i) x) :=
  (finite_free_homology_stalk_iff_of_local_quasiIso K U P f x i).mpr (hH i)

/-- The stalks of the structure sheaf of an open subspace are the stalks of the ambient space,
so locality of the stalks is inherited by open subspaces. -/
lemma isLocalRing_structureSheafStalk_restrict
    (X : RingedSpace.{u, v}) (U : Opens X) (x : U)
    [IsLocalRing (structureSheafStalk X x)] :
    IsLocalRing (structureSheafStalk (X.restrict U.isOpenEmbedding) (restrictPoint U x)) := by
  let Y := X.restrict U.isOpenEmbedding
  let F := (OpenNhds.inclusion (restrictPoint U x)).op
  let A := (OpenNhds.inclusion (x : X)).op ⋙ (structureSheafULift X).obj
  let y := opensPoint U x
  have : (U.isOpenEmbedding.functorNhds y).Initial :=
    Functor.initial_of_adjunction (U.isOpenEmbedding.adjunctionNhds y)
  let G : (OpenNhds (restrictPoint U x))ᵒᵖ ⥤ (OpenNhds (x : X))ᵒᵖ :=
    (U.isOpenEmbedding.functorNhds y).op
  have : G.Final := by
    change ((U.isOpenEmbedding.functorNhds y).op).Final
    infer_instance
  let cR : Cocone (F ⋙ (structureSheafULift Y).obj) := (colimit.cocone A).whisker G
  let hcR : IsColimit cR := (Functor.Final.isColimitWhiskerEquiv G _).symm
    (colimit.isColimit A)
  let : IsLocalRing cR.pt := ‹IsLocalRing (structureSheafStalk X x)›
  exact (hcR.coconePointUniqueUpToIso
    (colimit.isColimit (F ⋙ (structureSheafULift Y).obj))).ringCatIsoToRingEquiv.isLocalRing

end

section

universe w
open CategoryTheory.Functor
attribute [local instance] liftModulesFunctor_additive
/-- A homeomorphism carries covering families of opens to covering families. -/
private lemma homeomorphOpens_coverPreserving {A : TopCat.{u}} {B : TopCat.{v}}
    (h : A ≃ₜ B) : CoverPreserving (Opens.grothendieckTopology A)
      (Opens.grothendieckTopology B) h.opensCongr.equivalence.functor := by
  constructor
  intro U S hS y hy
  obtain ⟨V, f, hf, hx⟩ := hS (h.symm y) hy
  exact ⟨_, h.opensCongr.equivalence.functor.map f,
    ⟨_, f, 𝟙 _, hf, rfl⟩, hx⟩

/-- The functor on opens induced by a homeomorphism is continuous for the open-cover topologies. -/
private lemma homeomorphOpens_isContinuous {A : TopCat.{u}} {B : TopCat.{v}}
    (h : A ≃ₜ B) : h.opensCongr.equivalence.functor.IsContinuous
      (Opens.grothendieckTopology A) (Opens.grothendieckTopology B) :=
  Functor.isContinuous_of_coverPreserving (compatiblePreservingOfFlat _ _)
    (homeomorphOpens_coverPreserving h)


/-- Transport a sheaf of rings along a homeomorphism of the underlying spaces. -/
private def homeomorphRingSheaf {A : TopCat.{v}} {B : TopCat.{w}}
    (h : A ≃ₜ B) (R : Sheaf (Opens.grothendieckTopology B) RingCat.{u}) :
    Sheaf (Opens.grothendieckTopology A) RingCat.{u} := by
  let : h.opensCongr.equivalence.functor.IsContinuous
      (Opens.grothendieckTopology A) (Opens.grothendieckTopology B) :=
    homeomorphOpens_isContinuous h
  exact (h.opensCongr.equivalence.functor.sheafPushforwardContinuous RingCat.{u} _ _).obj R

/-- Transport sheaves of modules along a homeomorphism of the underlying spaces. -/
private def homeomorphModules {A : TopCat.{v}} {B : TopCat.{w}}
    (h : A ≃ₜ B) (R : Sheaf (Opens.grothendieckTopology B) RingCat.{u}) :
    SheafOfModules.{u} R ⥤ SheafOfModules.{u} (homeomorphRingSheaf h R) := by
  let : h.opensCongr.equivalence.functor.IsContinuous
      (Opens.grothendieckTopology A) (Opens.grothendieckTopology B) :=
    homeomorphOpens_isContinuous h
  exact SheafOfModules.pushforward.{u} (F := h.opensCongr.equivalence.functor)
    (𝟙 (homeomorphRingSheaf h R))

/-- Transport of sheaves of modules along a homeomorphism is a left adjoint. -/
private lemma homeomorphModules_isLeftAdjoint {A : TopCat.{v}} {B : TopCat.{w}}
    (h : A ≃ₜ B) (R : Sheaf (Opens.grothendieckTopology B) RingCat.{u}) :
    (homeomorphModules h R).IsLeftAdjoint := by
  let F := h.opensCongr.equivalence.functor
  let : F.IsContinuous (Opens.grothendieckTopology A)
      (Opens.grothendieckTopology B) := homeomorphOpens_isContinuous h
  let : F.IsCocontinuous (Opens.grothendieckTopology A)
      (Opens.grothendieckTopology B) :=
    (h.opensCongr.equivalence.toAdjunction.isCocontinuous_iff_coverPreserving _ _).mpr
      (homeomorphOpens_coverPreserving h.symm)
  exact pushforward_isLeftAdjoint _ (IsIso.id _)

/-- A homeomorphism carries the open neighbourhoods of a point order-isomorphically to those of
its image. -/
private def homeomorphNhds {A : TopCat.{v}} {B : TopCat.{w}}
    (h : A ≃ₜ B) (x : A) : OpenNhds x ≃o OpenNhds (h x) where
  toFun U := ⟨h.opensCongr U.val, by simpa using U.property⟩
  invFun V := ⟨h.opensCongr.symm V.val, V.property⟩
  left_inv U := Subtype.ext (h.opensCongr.symm_apply_apply U.val)
  right_inv U := Subtype.ext (h.opensCongr.apply_symm_apply U.val)
  map_rel_iff' := h.opensCongr.map_rel_iff

/-- An equivalence of sites induces an equivalence between the categories of sheaves of modules
over a sheaf of rings and over its pushforward. -/
def modulesEquivalence
    {C : Type v} [Category.{v} C] {D : Type w} [Category.{w} D]
    (J : GrothendieckTopology C) (K : GrothendieckTopology D) (e : C ≌ D)
    [e.functor.IsContinuous J K] [e.inverse.IsContinuous K J]
    [e.functor.IsCocontinuous J K]
    (R : Sheaf K RingCat.{u}) :
    SheafOfModules.{u} R ≌ SheafOfModules.{u}
      ((e.functor.sheafPushforwardContinuous RingCat.{u} J K).obj R) := by
  let adj := e.toAdjunction.sheafPushforwardContinuous (E := RingCat.{u}) J K
  have key₁ : adj.unit.app R ≫ (e.inverse.sheafPushforwardContinuous RingCat.{u} K J).map
      (𝟙 ((e.functor.sheafPushforwardContinuous RingCat.{u} J K).obj R)) = adj.unit.app R := by
    rw [CategoryTheory.Functor.map_id]
    exact Category.comp_id _
  have key₂ : 𝟙 ((e.functor.sheafPushforwardContinuous RingCat.{u} J K).obj R) ≫
      (e.functor.sheafPushforwardContinuous RingCat.{u} J K).map (adj.unit.app R) ≫
        adj.counit.app _ = 𝟙 _ := by
    rw [Category.id_comp, adj.left_triangle_components]
  have hu : (adj.unit.app R).hom = whiskerRight (NatTrans.op e.counit) R.obj := rfl
  exact SheafOfModules.pushforwardPushforwardEquivalence e (𝟙 _) (adj.unit.app R)
    (hu.symm.trans (congrArg (fun α => α.hom) key₁.symm))
    (congrArg (fun α => α.hom) key₂)

/-- Finite freeness of a stalk is preserved when a sheaf of modules is transported along a
homeomorphism. -/
private lemma finite_free_stalk_homeomorph
    {A : TopCat.{max u v}} {B : TopCat.{v}} (h : A ≃ₜ B)
    (R : Sheaf (Opens.grothendieckTopology B) RingCat.{max u v})
    (M : SheafOfModules.{max u v} R) (x : A)
    (hM : Module.Finite ↑(colimit ((OpenNhds.inclusion (h x)).op ⋙ R.obj))
        ((sheafColimitFunctor R (OpenNhds.inclusion (h x)).op).obj M) ∧
      Module.Free ↑(colimit ((OpenNhds.inclusion (h x)).op ⋙ R.obj))
        ((sheafColimitFunctor R (OpenNhds.inclusion (h x)).op).obj M)) :
    let S := homeomorphRingSheaf h R
    let N := (homeomorphModules h R).obj M
    Module.Finite ↑(TopCat.Presheaf.stalk S.obj x) ↑(TopCat.Presheaf.stalk N.val.presheaf x) ∧
      Module.Free ↑(TopCat.Presheaf.stalk S.obj x) ↑(TopCat.Presheaf.stalk N.val.presheaf x) := by
  let S := homeomorphRingSheaf h R
  let N := (homeomorphModules h R).obj M
  let F := (OpenNhds.inclusion x).op
  let G := (homeomorphNhds h x).equivalence.functor.op
  let DR := (OpenNhds.inclusion (h x)).op ⋙ R.obj
  let DM := (OpenNhds.inclusion (h x)).op ⋙ M.val.presheaf
  let cR : Cocone (F ⋙ S.obj) := (colimit.cocone DR).whisker G
  let cM : Cocone (F ⋙ N.val.presheaf) := (colimit.cocone DM).whisker G
  let hcR : IsColimit cR := (Functor.Final.isColimitWhiskerEquiv G _).symm
    (colimit.isColimit DR)
  let hcM : IsColimit cM := (Functor.Final.isColimitWhiskerEquiv G _).symm
    (colimit.isColimit DM)
  let (j : (OpenNhds x)ᵒᵖ) : Module ((F ⋙ S.obj).obj j)
      ((F ⋙ N.val.presheaf).obj j) := (N.val.obj (F.obj j)).isModule
  let (j : (OpenNhds (h x))ᵒᵖ) : Module (DR.obj j) (DM.obj j) :=
    (M.val.obj ((OpenNhds.inclusion (h x)).op.obj j)).isModule
  let : Module cR.pt cM.pt :=
    ((sheafColimitFunctor R (OpenNhds.inclusion (h x)).op).obj M).isModule
  let : Module ↑(colimit (F ⋙ S.obj)) ↑(colimit (F ⋙ N.val.presheaf)) :=
    ((sheafColimitFunctor S F).obj N).isModule
  let e := colimitModuleEquiv (F ⋙ S.obj) (F ⋙ N.val.presheaf)
    (fun f r m => N.val.map_smul _ _ _) cR hcR cM hcM
    (fun j r m => IsColimit.ι_smul DR DM (fun f r m => M.val.map_smul _ _ _)
      (colimit.isColimit DR) (colimit.isColimit DM) (G.obj j) r m)
  let q := ((colimit.isColimit (F ⋙ S.obj)).coconePointUniqueUpToIso hcR).ringCatIsoToRingEquiv
  let : RingHomInvPair q.toRingHom q.symm.toRingHom := RingHomInvPair.of_ringEquiv q
  let : RingHomInvPair q.symm.toRingHom q.toRingHom := RingHomInvPair.of_ringEquiv_symm q
  let : RingHomInvPair
      ((colimit.isColimit (F ⋙ S.obj)).coconePointUniqueUpToIso
        hcR).ringCatIsoToRingEquiv.toRingHom
      ((colimit.isColimit (F ⋙ S.obj)).coconePointUniqueUpToIso
        hcR).ringCatIsoToRingEquiv.symm.toRingHom :=
    RingHomInvPair.of_ringEquiv q
  let : RingHomInvPair
      ((colimit.isColimit (F ⋙ S.obj)).coconePointUniqueUpToIso
        hcR).ringCatIsoToRingEquiv.symm.toRingHom
      ((colimit.isColimit (F ⋙ S.obj)).coconePointUniqueUpToIso
        hcR).ringCatIsoToRingEquiv.toRingHom :=
    RingHomInvPair.of_ringEquiv_symm q
  let : Module.Finite cR.pt cM.pt := hM.1
  let : Module.Free cR.pt cM.pt := hM.2
  change Module.Finite ↑(colimit (F ⋙ S.obj)) ↑(colimit (F ⋙ N.val.presheaf)) ∧
    Module.Free ↑(colimit (F ⋙ S.obj)) ↑(colimit (F ⋙ N.val.presheaf))
  exact ⟨Module.Finite.of_surjective e.symm.toLinearMap e.symm.surjective,
    Module.Free.of_equiv e.symm⟩

/-- The functor on opens induced by a homeomorphism is cocontinuous for the open-cover
topologies. -/
private lemma homeomorphOpens_isCocontinuous {A : TopCat.{u}} {B : TopCat.{v}}
    (h : A ≃ₜ B) : h.opensCongr.equivalence.functor.IsCocontinuous
      (Opens.grothendieckTopology A) (Opens.grothendieckTopology B) :=
  (h.opensCongr.equivalence.toAdjunction.isCocontinuous_iff_coverPreserving _ _).mpr
    (homeomorphOpens_coverPreserving h.symm)

/-- A trivialisation of the transport of a sheaf of modules along a homeomorphism over an open
set is a trivialisation of the sheaf itself over the image open set. -/
private lemma chart_of_homeomorph
    {A : TopCat.{v}} {B : TopCat.{w}} (h : A ≃ₜ B)
    (R : Sheaf (Opens.grothendieckTopology B) RingCat.{u})
    (M : SheafOfModules.{u} R) (U : Opens A) (I : Type u)
    [HasSheafify ((Opens.grothendieckTopology A).over U) Ab.{u}]
    [((Opens.grothendieckTopology A).over U).WEqualsLocallyBijective Ab.{u}]
    [HasSheafify ((Opens.grothendieckTopology B).over (h.opensCongr U)) Ab.{u}]
    [((Opens.grothendieckTopology B).over (h.opensCongr U)).WEqualsLocallyBijective Ab.{u}]
    (eh : ((homeomorphModules h R).obj M).over U ≅ SheafOfModules.free I) :
    Nonempty ((M.over (h.opensCongr U)) ≅ SheafOfModules.free I) := by
  let e := h.opensCongr.equivalence
  let J := Opens.grothendieckTopology A
  let K := Opens.grothendieckTopology B
  let : e.functor.IsContinuous J K := homeomorphOpens_isContinuous h
  let : e.functor.IsCocontinuous J K := homeomorphOpens_isCocontinuous h
  let eU := Over.postEquiv (X := U) e
  let : eU.functor.IsContinuous (J.over U) (K.over (e.functor.obj U)) :=
    Functor.isContinuous_of_coverPreserving (compatiblePreservingOfFlat _ _)
      ((homeomorphOpens_coverPreserving h).overPost U)
  let : eU.functor.IsCocontinuous (J.over U) (K.over (e.functor.obj U)) :=
    inferInstanceAs ((Over.post (X := U) e.functor).IsCocontinuous _ _)
  let : eU.inverse.IsContinuous (K.over (e.functor.obj U)) (J.over U) :=
    Functor.isContinuous_of_coverPreserving (compatiblePreservingOfFlat _ _)
      ((eU.toAdjunction.isCocontinuous_iff_coverPreserving _ _).mp inferInstance)
  let : HasSheafify (K.over (e.functor.obj U)) Ab.{u} :=
    ‹HasSheafify ((Opens.grothendieckTopology B).over (h.opensCongr U)) Ab.{u}›
  let : (K.over (e.functor.obj U)).WEqualsLocallyBijective Ab.{u} :=
    ‹((Opens.grothendieckTopology B).over (h.opensCongr U)).WEqualsLocallyBijective Ab.{u}›
  let E := modulesEquivalence (J.over U) (K.over (e.functor.obj U)) eU
    (R.over (e.functor.obj U))
  let ε : SheafOfModules.unit _ ≅ E.functor.obj (SheafOfModules.unit _) := Iso.refl _
  let e' : E.functor.obj (M.over (e.functor.obj U)) ≅
      E.functor.obj (SheafOfModules.free I) :=
    eh ≪≫ SheafOfModules.mapFreeIso E.functor I ε
  exact ⟨(Functor.FullyFaithful.ofFullyFaithful E.functor).preimageIso e'⟩

/-- Presheaves of abelian groups on the open sets of `B` admit a sheafification. -/
local instance (B : TopCat.{v}) :
    HasSheafify (Opens.grothendieckTopology B) Ab.{max u v} :=
  hasSheafifyEssentiallySmallSite.{v, max u v, v, (max u v) + 1, max u v} _ _

/-- On the open sets of `B`, a morphism of presheaves of abelian groups becomes an isomorphism
after sheafification exactly when it is locally bijective. -/
local instance (B : TopCat.{v}) :
    (Opens.grothendieckTopology B).WEqualsLocallyBijective Ab.{max u v} :=
  GrothendieckTopology.WEqualsLocallyBijective.ofEssentiallySmall.{v, max u v, v,
    (max u v) + 1, max u v} _

/-- Presheaves of abelian groups on the open subsets of `U` admit a sheafification. -/
local instance (B : TopCat.{v}) (U : Opens B) :
    HasSheafify ((Opens.grothendieckTopology B).over U) Ab.{max u v} :=
  hasSheafifyEssentiallySmallSite.{v, max u v, v, (max u v) + 1, max u v} _ _

/-- On the open subsets of `U`, a morphism of presheaves of abelian groups becomes an
isomorphism after sheafification exactly when it is locally bijective. -/
local instance (B : TopCat.{v}) (U : Opens B) :
    ((Opens.grothendieckTopology B).over U).WEqualsLocallyBijective Ab.{max u v} :=
  GrothendieckTopology.WEqualsLocallyBijective.ofEssentiallySmall.{v, max u v, v,
    (max u v) + 1, max u v} _

/-- A finite free module is isomorphic to the finitely supported functions on `ULift (Fin n)`
for some `n`. -/
private lemma exists_finsupp_linearEquiv_of_finite_free
    (R M : Type u) [Ring R] [AddCommGroup M] [Module R M]
    [Module.Finite R M] [Module.Free R M] :
    ∃ n : ℕ, Nonempty (M ≃ₗ[R] (ULift.{u} (Fin n) →₀ R)) := by
  classical
  cases subsingleton_or_nontrivial R with
  | inl h =>
    let := h
    let : Subsingleton M := Module.subsingleton R M
    exact ⟨0, ⟨LinearEquiv.ofSubsingleton _ _⟩⟩
  | inr h =>
    let := h
    let κ := Module.Free.ChooseBasisIndex R M
    let b := Module.Free.chooseBasis R M
    let : Finite κ := Module.Finite.finite_basis b
    let : Fintype κ := Fintype.ofFinite _
    exact ⟨Fintype.card κ, ⟨b.repr.trans (Finsupp.domLCongr
      ((Fintype.equivFin κ).trans Equiv.ulift.symm))⟩⟩

/-- **Stacks, Tag 0B8J** for the universe-lifted sheaves used here: a finitely presented sheaf of
modules whose stalk at a point is finite free is isomorphic to a finite free sheaf on some
open neighbourhood of that point. -/
lemma exists_chart_of_presentation
    {B : TopCat.{v}} (R : Sheaf (Opens.grothendieckTopology B) RingCat.{max u v})
    (M : SheafOfModules.{max u v} R) (p : M.Presentation) (hp : p.IsFinite)
    (x : B)
    (hx : Module.Finite ↑(colimit ((OpenNhds.inclusion x).op ⋙ R.obj))
        ((sheafColimitFunctor R (OpenNhds.inclusion x).op).obj M) ∧
      Module.Free ↑(colimit ((OpenNhds.inclusion x).op ⋙ R.obj))
        ((sheafColimitFunctor R (OpenNhds.inclusion x).op).obj M)) :
    ∃ U : Opens B, x ∈ U ∧ ∃ n : ℕ,
      Nonempty (M.over U ≅ SheafOfModules.free (ULift.{max u v} (Fin n))) := by
  let A := TopCat.of (ULift.{u} B)
  let h : A ≃ₜ B := Homeomorph.ulift
  let S := homeomorphRingSheaf h R
  let F := homeomorphModules h R
  let : F.IsLeftAdjoint := homeomorphModules_isLeftAdjoint h R
  let η : SheafOfModules.unit S ≅ F.obj (SheafOfModules.unit R) := Iso.refl _
  let p' := p.map F η
  let : p'.IsFinite :=
    ⟨⟨inferInstanceAs (Finite p.generators.I)⟩, ⟨inferInstanceAs (Finite p.relations.I)⟩⟩
  have hfp := isFinitePresentation_of_finite_presentation p'
  have hx' := finite_free_stalk_homeomorph h R M (ULift.up x) hx
  let N := F.obj M
  let : Module ↑(TopCat.Presheaf.stalk S.obj (ULift.up x))
      ↑(TopCat.Presheaf.stalk N.val.presheaf (ULift.up x)) :=
    N.val.instModuleCarrierStalkRingCatCarrierAbPresheafOpensCarrier (ULift.up x)
  let : Module.Finite ↑(TopCat.Presheaf.stalk S.obj (ULift.up x))
      ↑(TopCat.Presheaf.stalk N.val.presheaf (ULift.up x)) := hx'.1
  let : Module.Free ↑(TopCat.Presheaf.stalk S.obj (ULift.up x))
      ↑(TopCat.Presheaf.stalk N.val.presheaf (ULift.up x)) := hx'.2
  obtain ⟨n, he⟩ := exists_finsupp_linearEquiv_of_finite_free
    ↑(TopCat.Presheaf.stalk S.obj (ULift.up x))
    ↑(TopCat.Presheaf.stalk N.val.presheaf (ULift.up x))
  obtain ⟨U, hxU, ⟨eU⟩⟩ := Stacks.SheafOfModules.exists_iso_free_over_of_stalk_iso_free
    N hfp (ULift.up x) n he
  exact ⟨h.opensCongr U, hxU, n, chart_of_homeomorph h R M U _ eU⟩

/-- If all cohomology stalks of a strictly perfect complex at a point with local stalk are
finite free, then each object of opcycles of its universe lift is finite free on an open
neighbourhood of the point. -/
lemma exists_chart_lifted_opcycles
    {X : RingedSpace.{u, v}} (K : CochainComplex (OXMod.{u, v} X) ℤ)
    (hK : IsStrictlyPerfect K) (x : X) [IsLocalRing (structureSheafStalk X x)]
    (hH : ∀ i, Module.Finite (structureSheafStalk X x) (moduleSheafStalk (K.homology i) x) ∧
      Module.Free (structureSheafStalk X x) (moduleSheafStalk (K.homology i) x)) (i : ℤ) :
    let L := ((liftModulesFunctor X).mapHomologicalComplex (ComplexShape.up ℤ)).obj K
    ∃ U : Opens X, x ∈ U ∧ ∃ n : ℕ,
      Nonempty ((L.opcycles i).over U ≅ SheafOfModules.free (ULift.{max u v} (Fin n))) := by
  let L := ((liftModulesFunctor X).mapHomologicalComplex (ComplexShape.up ℤ)).obj K
  obtain ⟨n, ⟨r⟩⟩ := exists_retract_free_liftModulesFunctor
    (K.X ((ComplexShape.up ℤ).prev i)) (hK.directSummand _)
  obtain ⟨m, ⟨s⟩⟩ := exists_retract_free_liftModulesFunctor (K.X i) (hK.directSummand _)
  let p₀ := cokernelPresentationOfRetracts (L.sc i).f r s
  let : p₀.IsFinite := ⟨⟨inferInstanceAs (Finite (ULift.{max u v} (Fin m)))⟩,
    ⟨inferInstanceAs (Finite (ULift.{max u v} (Fin m) ⊕ ULift.{max u v} (Fin n)))⟩⟩
  let p := p₀.ofIsIso (L.sc i).opcyclesIsoCokernel.inv
  exact exists_chart_of_presentation (structureSheafULift X) (L.opcycles i) p
    (inferInstanceAs (p₀.ofIsIso (L.sc i).opcyclesIsoCokernel.inv).IsFinite) x
    (lifted_opcycles_stalk_finite_free K hK x hH i)

/-- The homology of a short complex whose third term and whose cokernel are projective is a
retract of its opcycles. -/
private lemma homology_retract_opcycles_of_projective_cokernel
    {C : Type*} [Category C] [Abelian C] (S : ShortComplex C)
    [Projective S.X₃] [Projective (cokernel S.g)] :
    Nonempty (Retract S.homology S.opcycles) := by
  let : Projective (Abelian.image S.g) := projective_image_of_projective_cokernel S.g
  let : Projective (Abelian.coimage S.g) :=
    Projective.of_iso (Abelian.coimageIsoImage S.g).symm inferInstance
  obtain ⟨q, hw, hT⟩ := exists_shortExact_homologyι S
  exact ⟨⟨S.homologyι, hT.splittingOfProjective.r, hT.splittingOfProjective.f_r⟩⟩

/-- Finite free stalks for the opcycles of the universe lift of a strictly perfect complex give
finite free cohomology stalks for the complex itself. -/
private lemma finite_free_homology_of_opcycles
    {X : RingedSpace.{u, v}} (K : CochainComplex (OXMod.{u, v} X) ℤ)
    (hK : IsStrictlyPerfect K) (x : X) [IsLocalRing (structureSheafStalk X x)]
    (hC : ∀ i : ℤ,
      let L := ((liftModulesFunctor X).mapHomologicalComplex (ComplexShape.up ℤ)).obj K
      let T := sheafColimitFunctor (structureSheafULift X) (OpenNhds.inclusion x).op
      Module.Finite (structureSheafStalk X x) (T.obj (L.opcycles i)) ∧
        Module.Free (structureSheafStalk X x) (T.obj (L.opcycles i))) (i : ℤ) :
    Module.Finite (structureSheafStalk X x) (moduleSheafStalk (K.homology i) x) ∧
      Module.Free (structureSheafStalk X x) (moduleSheafStalk (K.homology i) x) := by
  let R := structureSheafStalk X x
  let : CommRing R := structureSheafStalkCommRing X x
  let L := ((liftModulesFunctor X).mapHomologicalComplex (ComplexShape.up ℤ)).obj K
  let T := sheafColimitFunctor (structureSheafULift X) (OpenNhds.inclusion x).op
  let : T.Additive := sheafColimitFunctor_additive _ _
  let : PreservesFiniteLimits T := sheafColimitFunctor_preservesFiniteLimits _ x
  let : PreservesFiniteColimits T := sheafColimitFunctor_preservesFiniteColimits _ x
  let : (liftModulesFunctor X).PreservesHomology := liftModulesFunctor_preservesHomology X
  let P := (T.mapHomologicalComplex (ComplexShape.up ℤ)).obj L
  have hCX (j : ℤ) : Module.Finite R (P.opcycles j) ∧ Projective (P.opcycles j) := by
    let : Module.Finite R (T.obj (L.opcycles j)) := (hC j).1
    let : Module.Free R (T.obj (L.opcycles j)) := (hC j).2
    let e : P.opcycles j ≅ T.obj (L.opcycles j) := (L.sc j).mapOpcyclesIso T
    exact ⟨Module.Finite.equiv e.symm.toLinearEquiv,
      Projective.of_iso e.symm inferInstance⟩
  have hPX (j : ℤ) : Projective (P.X j) := by
    obtain ⟨n, ⟨r⟩⟩ := exists_retract_free_liftModulesFunctor (K.X j) (hK.directSummand j)
    have hfree := finite_free_sheafColimit_free (structureSheafULift X)
      (OpenNhds.inclusion x).op (ULift.{max u v} (Fin n))
    let : Module.Free R (T.obj (SheafOfModules.free (ULift.{max u v} (Fin n)))) := hfree.2
    exact projective_of_retract (r.map T)
  let j := (ComplexShape.up ℤ).next i
  have hj : j = i + 1 := (ComplexShape.up ℤ).next_eq' rfl
  have hprev : (ComplexShape.up ℤ).prev j = i :=
    (ComplexShape.up ℤ).prev_eq' hj.symm
  let : Projective (P.sc i).X₃ := hPX j
  let : Projective (cokernel (P.sc i).g) := by
    have h := Projective.of_iso (P.sc j).opcyclesIsoCokernel (hCX j).2
    change Projective (cokernel (P.d ((ComplexShape.up ℤ).prev j) j)) at h
    rwa [hprev] at h
  obtain ⟨r⟩ := homology_retract_opcycles_of_projective_cokernel (P.sc i)
  let r : Retract (P.homology i) (P.opcycles i) := r
  let : Module.Finite R (P.opcycles i) := (hCX i).1
  let : Projective (P.opcycles i) := (hCX i).2
  let : Projective (P.homology i) := projective_of_retract r
  let : Module.Finite R (P.homology i) := Module.Finite.of_surjective r.r.hom
    (fun m => ⟨r.i m, ConcreteCategory.congr_hom r.retract m⟩)
  let : Module.Free R (P.homology i) := Module.free_of_flat_of_isLocalRing
  let e : P.homology i ≅ T.obj ((liftModulesFunctor X).obj (K.homology i)) :=
    (L.sc i).mapHomologyIso T ≪≫
    T.mapIso ((K.sc i).mapHomologyIso (liftModulesFunctor X))
  exact (finite_free_sheafColimit_iff_stalk (K.homology i) x).mp
    ⟨Module.Finite.equiv e.toLinearEquiv, Module.Free.of_equiv e.toLinearEquiv⟩

/-- Finite freeness of all cohomology stalks of a strictly perfect complex at one point
propagates to an open neighbourhood of that point. -/
lemma exists_open_finite_free_homology_stalk
    {X : RingedSpace.{u, v}} [∀ x : X, IsLocalRing (structureSheafStalk X x)]
    (K : CochainComplex (OXMod.{u, v} X) ℤ) (hK : IsStrictlyPerfect K) (x : X)
    (hx : ∀ i, Module.Finite (structureSheafStalk X x) (moduleSheafStalk (K.homology i) x) ∧
      Module.Free (structureSheafStalk X x) (moduleSheafStalk (K.homology i) x)) :
    ∃ U : Opens X, x ∈ U ∧ ∀ y ∈ U, ∀ i : ℤ,
      Module.Finite (structureSheafStalk X y) (moduleSheafStalk (K.homology i) y) ∧
        Module.Free (structureSheafStalk X y) (moduleSheafStalk (K.homology i) y) := by
  classical
  let L := ((liftModulesFunctor X).mapHomologicalComplex (ComplexShape.up ℤ)).obj K
  choose U hxU n e using exists_chart_lifted_opcycles K hK x hx
  let s := hK.bounded.toFinset
  let W : Opens X := ⟨⋂ i ∈ s, (U i : Set X),
    isOpen_biInter_finset (fun i _ => (U i).isOpen)⟩
  refine ⟨W, Set.mem_iInter.mpr fun i => Set.mem_iInter.mpr fun _ => hxU i, ?_⟩
  intro y hy i
  apply finite_free_homology_of_opcycles K hK y _ i
  intro j
  let T := sheafColimitFunctor (structureSheafULift X) (OpenNhds.inclusion y).op
  let : T.Additive := sheafColimitFunctor_additive _ _
  by_cases hj : IsZero (K.X j)
  · have hz : IsZero (L.X j) := (liftModulesFunctor X).map_isZero hj
    have hzC : IsZero (L.opcycles j) :=
      hz.of_iso ((L.sc j).opcyclesIsoX₂ (hz.eq_of_tgt _ _))
    let : Subsingleton (T.obj (L.opcycles j)) :=
      ModuleCat.subsingleton_of_isZero (T.map_isZero hzC)
    exact ⟨inferInstance, inferInstance⟩
  · have hj' : j ∈ s := hK.bounded.mem_toFinset.mpr hj
    have hyj : y ∈ U j := Set.mem_iInter.mp (Set.mem_iInter.mp hy j) hj'
    exact finite_free_stalkColimit_of_chart (structureSheafULift X) (L.opcycles j)
      (U j) ⟨y, hyj⟩ _ (e j).some

/-- Finite freeness of a cohomology stalk passes back from a complex mapping
quasi-isomorphically to the restriction of a complex to the complex itself. -/
lemma finite_free_homology_stalk_of_local_quasiIso_reverse
    {X : RingedSpace.{u, v}} (K : CochainComplex (OXMod.{u, v} X) ℤ) (U : Opens X)
    (P : CochainComplex (OXMod.{u, v} (X.restrict U.isOpenEmbedding)) ℤ)
    (f : P ⟶ ((restrictModules X U).mapHomologicalComplex
      (ComplexShape.up ℤ)).obj K) [QuasiIso f] (x : U) (i : ℤ)
    (h : Module.Finite (structureSheafStalk (X.restrict U.isOpenEmbedding) x)
        (moduleSheafStalk (P.homology i) x) ∧
      Module.Free (structureSheafStalk (X.restrict U.isOpenEmbedding) x)
        (moduleSheafStalk (P.homology i) x)) :
    Module.Finite (structureSheafStalk X x) (moduleSheafStalk (K.homology i) x) ∧
      Module.Free (structureSheafStalk X x) (moduleSheafStalk (K.homology i) x) :=
  (finite_free_homology_stalk_iff_of_local_quasiIso K U P f x i).mp h

end

end Stacks.Cohomology.PerfectComplexes

end
