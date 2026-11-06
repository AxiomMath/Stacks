module

public import StacksFrontier.Algebra.Category.ModuleCat.Sheaf.InvertibleCompare
public import StacksFrontier.Algebra.Category.ModuleCat.Sheaf.InvertibleRankOneLocal
public import StacksFrontier.AlgebraicGeometry.AmpleImmersionReduction.Generation
public import StacksFrontier.AlgebraicGeometry.Cohomology.GlobalGeneration.Stalks
public import StacksFrontier.AlgebraicGeometry.Descent.EffectiveEpi.QuasicoherentSections
public import StacksFrontier.AlgebraicGeometry.FinGenFromCover.Basic
public import StacksFrontier.AlgebraicGeometry.InvertibleLocallyFree.Basic
public import StacksFrontier.AlgebraicGeometry.NonvanishingSpelling.Basic
public import StacksFrontier.AlgebraicGeometry.Recovery27.PullbackFreeIso
public import StacksFrontier.AlgebraicGeometry.SheafRankOne.Basic

/-!
# Generation by global sections as a presentation by a free module

Let `X` be a scheme and `M` an `𝒪_X`-module. A family `(s_i)` of global sections of `M` indexed
by a type `ι` determines a morphism `free ι ⟶ M` out of the free module, and Mathlib's
`SheafOfModules.freeHomEquiv` is the bijection between the two data. This module compares two
conditions on such a family:

* `Stacks.ProjectiveFromSections.GeneratesStalks`, the hypothesis of Stacks Tag 01NE: the germs
  of the `s_i` generate every stalk of `M` over `𝒪_{X,x}`;
* `Epi` of the associated morphism out of the free module, which is how a *quotient* of the free
  module is presented, for instance in the Grassmannian functor of Stacks Tag 089S.

It also proves that invertibility is finite local freeness of rank one, and the compatibility of
the morphism out of the free module with pullback along a morphism of schemes.

## Main results

* `Stacks.ProjectiveFromSections.isFiniteLocallyFreeOfRank_one_of_isInvertibleModule` and
  `Stacks.ProjectiveFromSections.isInvertibleModule_of_isFiniteLocallyFreeOfRank_one`:
  invertibility of an `𝒪_X`-module is finite local freeness of rank one.
* `Stacks.ProjectiveFromSections.epi_freeHomEquiv_symm_of_generatesStalks` and
  `Stacks.ProjectiveFromSections.generatesStalks_of_epi_freeHomEquiv_symm`: for an invertible
  module, generation of the stalks by a family of global sections is exactly surjectivity of the
  associated morphism out of the free module; the second direction needs no invertibility.
* `Stacks.ProjectiveFromSections.freeHomEquiv_pullbackFreeIso_inv`: the pullback of the morphism
  out of the free module determined by a family of global sections is the morphism determined by
  the pulled-back sections.

## References

* [Stacks Project, Tag 01AN](https://stacks.math.columbia.edu/tag/01AN)
* [Stacks Project, Tag 01NE](https://stacks.math.columbia.edu/tag/01NE)
* [Stacks Project, Tag 089S](https://stacks.math.columbia.edu/tag/089S)
* [Stacks Project, Tag 0B8M](https://stacks.math.columbia.edu/tag/0B8M)
-/

@[expose] public noncomputable section

open AlgebraicGeometry CategoryTheory Opposite TopologicalSpace
open scoped Stacks.ModuleStalk Stacks.FinGenFromCover

universe u

namespace Stacks.ProjectiveFromSections

attribute [local implicit_reducible] AlgebraicGeometry.Scheme.Modules
  AlgebraicGeometry.Scheme.Modules.Hom AlgebraicGeometry.Scheme.Modules.pullback
  AlgebraicGeometry.Scheme.Modules.pushforward
  TopCat.Sheaf CategoryTheory.sheafCompose
  SheafOfModules.unit PresheafOfModules.unit

/-! ### Invertibility and rank one -/

/-- An invertible `𝒪_X`-module is finite locally free of rank one. -/
theorem isFiniteLocallyFreeOfRank_one_of_isInvertibleModule {X : Scheme.{u}} (M : X.Modules)
    [Stacks.Ample.IsInvertibleModule X M] :
    AlgebraicGeometry.SheafOfModules.IsFiniteLocallyFreeOfRank (R := X.ringCatSheaf) M 1 :=
  Stacks.SheafRankOne.isFiniteLocallyFreeOfRank_one_of_isInvertible_scheme X M

open Stacks.InvertibleLocallyFree in
/-- An `𝒪_X`-module that is finite locally free of rank one is invertible. -/
theorem isInvertibleModule_of_isFiniteLocallyFreeOfRank_one {X : Scheme.{u}} (M : X.Modules)
    [AlgebraicGeometry.SheafOfModules.IsFiniteLocallyFreeOfRank (R := X.ringCatSheaf) M 1] :
    Stacks.Ample.IsInvertibleModule X M := by
  have h := (isFiniteLocallyFreeOfRank_iff_invertible_isFiniteLocallyFreeOfRank
      X.presheaf (Stacks.SheafInternalHom.isSheaf_structureRingPresheaf X) M 1).mp (by assumption)
  exact Stacks.SheafOfModules.IsInvertible.toAlgebraicGeometry _ _ _
    (Stacks.SheafOfModules.Invertible.isInvertible_of_isFiniteLocallyFreeOfRank_one' M h)

/-- The global section of the module attached to a section by `sectionsEquiv.symm` evaluates back
to that section. -/
private theorem eval_sectionsEquiv_symm {X : Scheme.{u}} (M : X.Modules) (t : Γ(M, ⊤)) :
    ((Stacks.NonvanishingSpelling.sectionsEquiv X M).symm t).eval (op ⊤) = t :=
  (Stacks.NonvanishingSpelling.sectionsEquiv X M).apply_symm_apply t

/-- A family of global sections of an invertible module that generates every stalk presents the
module as a quotient of the free module on the index set. -/
theorem epi_freeHomEquiv_symm_of_generatesStalks {X : Scheme.{u}} {M : X.Modules}
    [Stacks.Ample.IsInvertibleModule X M] {ι : Type u} (s : ι → Γ(M, ⊤))
    (hs : Stacks.ProjectiveFromSections.GeneratesStalks s) :
    Epi (M.freeHomEquiv.symm
      (fun i => (Stacks.NonvanishingSpelling.sectionsEquiv X M).symm (s i))) := by
  refine (AlgebraicGeometry.generates_iff_stalkwise_generates X.ringCatSheaf M _).mpr fun x => ?_
  obtain ⟨i, hi⟩ := Stacks.ProjectiveFromSections.exists_mem_nvCover_of_generatesStalks s hs x
  simp only [eval_sectionsEquiv_symm]
  exact Stacks.FinGenFromCover.span_eq_top_of_mem_nonvanishingLocus M s hi

/-- A `RingCat`-stalk scalar multiple of an element of a module stalk is also a scalar multiple of
it over the `CommRingCat` stalk `𝒪_{X,x}`. -/
private theorem exists_commStalk_smul_eq {X : Scheme.{u}} (M : X.Modules) (x : X)
    (r' : (TopCat.Presheaf.stalk X.ringCatSheaf.obj x : RingCat))
    (m : TopCat.Presheaf.stalk (C := Ab.{u}) M.presheaf x) :
    ∃ r : X.presheaf.stalk x, r' • m = r • m := by
  obtain ⟨U, hU, r₀, hr⟩ := TopCat.Presheaf.exists_germ_eq X.ringCatSheaf.obj r'
  obtain ⟨V, hV, m₀, hm⟩ := TopCat.Presheaf.exists_germ_eq (C := Ab.{u}) M.presheaf m
  have hxW : x ∈ U ⊓ V := ⟨hU, hV⟩
  set r₁ := X.presheaf.map (homOfLE (inf_le_left (a := U) (b := V))).op r₀
  set m₁ := M.presheaf.map (homOfLE (inf_le_right (a := U) (b := V))).op m₀
  have hrW : (TopCat.Presheaf.germ X.ringCatSheaf.obj (U ⊓ V) x hxW).hom r₁ = r' :=
    (TopCat.Presheaf.germ_res_apply X.ringCatSheaf.obj (homOfLE inf_le_left) x hxW r₀).trans hr
  have hmW : (TopCat.Presheaf.germ (C := Ab.{u}) M.presheaf (U ⊓ V) x hxW).hom m₁ = m :=
    (TopCat.Presheaf.germ_res_apply (C := Ab.{u}) M.presheaf (homOfLE inf_le_right) x hxW
      m₀).trans hm
  refine ⟨(X.presheaf.germ (U ⊓ V) x hxW).hom r₁, ?_⟩
  rw [← hrW, ← hmW]
  exact (Stacks.FinGenFromCover.ringStalk_germ_smul M x (U ⊓ V) hxW r₁ m₁).symm.trans
    (Stacks.ModuleStalk.germ_smul M x (U ⊓ V) hxW r₁ m₁)

/-- A family of global sections presenting the module as a quotient of the free module on the
index set generates every stalk. -/
theorem generatesStalks_of_epi_freeHomEquiv_symm {X : Scheme.{u}} {M : X.Modules}
    {ι : Type u} (s : ι → Γ(M, ⊤))
    (hepi : Epi (M.freeHomEquiv.symm
      (fun i => (Stacks.NonvanishingSpelling.sectionsEquiv X M).symm (s i)))) :
    Stacks.ProjectiveFromSections.GeneratesStalks s := by
  classical
  intro x w
  have hspan := (AlgebraicGeometry.generates_iff_stalkwise_generates X.ringCatSheaf M
    (fun i => (Stacks.NonvanishingSpelling.sectionsEquiv X M).symm (s i))).mp hepi x
  simp only [eval_sectionsEquiv_symm] at hspan
  obtain ⟨c, hc⟩ := Finsupp.mem_span_range_iff_exists_finsupp.mp (Submodule.eq_top_iff'.mp hspan w)
  choose r hr using fun i => exists_commStalk_smul_eq M x (c i) ((M.presheaf.Γgerm x).hom (s i))
  refine ⟨c.support, r, ?_⟩
  rw [← hc]
  exact Finset.sum_congr rfl fun i _ => hr i

/-! ### Sections, reindexing, and the identity isomorphism -/

/-- The global section attached to the image of a section under a morphism of modules. -/
theorem sectionsEquiv_sectionsMap {X : Scheme.{u}} {M N : X.Modules} (φ : M ⟶ N)
    (s : (Stacks.NonvanishingSpelling.toSheafOfModules X M).sections) :
    Stacks.NonvanishingSpelling.sectionsEquiv X N (SheafOfModules.sectionsMap φ s) =
      Scheme.Modules.Hom.app φ ⊤ (Stacks.NonvanishingSpelling.sectionsEquiv X M s) :=
  rfl

/-- The identity isomorphism acts trivially on sections. -/
theorem homApp_refl {X : Scheme.{u}} (M : X.Modules) (U : X.Opens) (x : Γ(M, U)) :
    Scheme.Modules.Hom.app (Iso.refl M).hom U x = x := by
  rw [Iso.refl_hom, Scheme.Modules.Hom.id_app]
  rfl

/-- Generation of the stalks by a finite family of global sections is unchanged by passing to the
universe lift of the index type. -/
theorem generatesStalks_ulift_iff {X : Scheme.{u}} {L : X.Modules} {m : ℕ}
    (s : Fin m → Γ(L, ⊤)) :
    GeneratesStalks (fun i : ULift.{u} (Fin m) => s i.down) ↔ GeneratesStalks s := by
  constructor <;> intro h x w <;> obtain ⟨t, r, hw⟩ := h x w
  · exact ⟨t.map (Equiv.ulift.{u}).toEmbedding, fun i => r (ULift.up i), by rwa [Finset.sum_map]⟩
  · exact ⟨t.map (Equiv.ulift.{u}).symm.toEmbedding, fun j => r j.down, by rwa [Finset.sum_map]⟩


/-! ### Compatibility with pullback -/

section

variable {X Y : Scheme.{u}} (h : Y ⟶ X)
  [(SheafOfModules.pushforward.{u} h.toRingCatSheafHom).IsRightAdjoint]

/-- On the `i`-th summand of the free module, the inverse of `pullbackFreeIso` undoes the
canonical map out of the pullback of the unit module. -/
private theorem pullbackObjUnitToUnit_comp_ιFree_comp_inv (N : ℕ) (i : ULift.{u} (Fin N)) :
    SheafOfModules.pullbackObjUnitToUnit h.toRingCatSheafHom ≫
        SheafOfModules.ιFree i ≫ (Grassmannian.pullbackFreeIso h N).inv =
      (Scheme.Modules.pullback h).map (SheafOfModules.ιFree i) := by
  calc
    SheafOfModules.pullbackObjUnitToUnit h.toRingCatSheafHom ≫
          SheafOfModules.ιFree i ≫ (Grassmannian.pullbackFreeIso h N).inv =
        (SheafOfModules.pullbackObjUnitToUnit h.toRingCatSheafHom ≫
          SheafOfModules.ιFree i) ≫ (Grassmannian.pullbackFreeIso h N).inv :=
      (Category.assoc _ _ _).symm
    _ = ((Scheme.Modules.pullback h).map (SheafOfModules.ιFree i) ≫
          (Grassmannian.pullbackFreeIso h N).hom) ≫
          (Grassmannian.pullbackFreeIso h N).inv :=
      congrArg (fun m ↦ m ≫ (Grassmannian.pullbackFreeIso h N).inv)
        (Grassmannian.pullback_map_ιFree_comp_pullbackFreeIso_hom h N i).symm
    _ = (Scheme.Modules.pullback h).map (SheafOfModules.ιFree i) := by simp

/-- The section of the pullback cut out by the `i`-th summand of the pulled-back free
presentation is the pullback of the `i`-th member of the presentation. -/
private theorem pullbackObjUnitToUnit_comp_pullbackFreeIso_inv_comp (M : X.Modules) (N : ℕ)
    (q : SheafOfModules.free (R := X.ringCatSheaf) (ULift.{u} (Fin N)) ⟶ M)
    (i : ULift.{u} (Fin N)) :
    SheafOfModules.pullbackObjUnitToUnit h.toRingCatSheafHom ≫
        SheafOfModules.ιFree i ≫ (Grassmannian.pullbackFreeIso h N).inv ≫
          (Scheme.Modules.pullback h).map q =
      (Scheme.Modules.pullback h).map (SheafOfModules.ιFree i ≫ q) := by
  calc
    SheafOfModules.pullbackObjUnitToUnit h.toRingCatSheafHom ≫
          SheafOfModules.ιFree i ≫ (Grassmannian.pullbackFreeIso h N).inv ≫
            (Scheme.Modules.pullback h).map q =
        (SheafOfModules.pullbackObjUnitToUnit h.toRingCatSheafHom ≫
            SheafOfModules.ιFree i ≫ (Grassmannian.pullbackFreeIso h N).inv) ≫
          (Scheme.Modules.pullback h).map q := by
      rw [Category.assoc, Category.assoc]
    _ = (Scheme.Modules.pullback h).map (SheafOfModules.ιFree i) ≫
          (Scheme.Modules.pullback h).map q :=
      congrArg (fun m ↦ m ≫ (Scheme.Modules.pullback h).map q)
        (pullbackObjUnitToUnit_comp_ιFree_comp_inv h N i)
    _ = (Scheme.Modules.pullback h).map (SheafOfModules.ιFree i ≫ q) :=
      ((Scheme.Modules.pullback h).map_comp _ _).symm

/-- The canonical morphism out of the unit module is the adjoint of the canonical morphism out
of the pullback of the unit module. -/
private theorem unitToPushforwardObjUnit_eq :
    SheafOfModules.unitToPushforwardObjUnit h.toRingCatSheafHom =
      (Scheme.Modules.pullbackPushforwardAdjunction h).unit.app
          (SheafOfModules.unit X.ringCatSheaf) ≫
        (Scheme.Modules.pushforward h).map
          (SheafOfModules.pullbackObjUnitToUnit h.toRingCatSheafHom) :=
  (SheafOfModules.pullbackPushforwardAdjunction_homEquiv_pullbackObjUnitToUnit
      (φ := h.toRingCatSheafHom)).symm.trans
    ((SheafOfModules.pullbackPushforwardAdjunction h.toRingCatSheafHom).homEquiv_unit _ _ _)

/-- Pushing the `i`-th summand of the pulled-back free presentation forward along `h` and
precomposing with the canonical morphism out of the unit module gives the `i`-th member of the
presentation followed by the unit of the adjunction. -/
private theorem unitToPushforwardObjUnit_comp_pushforward_map (M : X.Modules) (N : ℕ)
    (q : SheafOfModules.free (R := X.ringCatSheaf) (ULift.{u} (Fin N)) ⟶ M)
    (i : ULift.{u} (Fin N)) :
    SheafOfModules.unitToPushforwardObjUnit h.toRingCatSheafHom ≫
        (Scheme.Modules.pushforward h).map
          (SheafOfModules.ιFree i ≫ (Grassmannian.pullbackFreeIso h N).inv ≫
            (Scheme.Modules.pullback h).map q) =
      (SheafOfModules.ιFree i ≫ q) ≫
        (Scheme.Modules.pullbackPushforwardAdjunction h).unit.app M := by
  calc
    SheafOfModules.unitToPushforwardObjUnit h.toRingCatSheafHom ≫
          (Scheme.Modules.pushforward h).map
            (SheafOfModules.ιFree i ≫ (Grassmannian.pullbackFreeIso h N).inv ≫
              (Scheme.Modules.pullback h).map q) =
        ((Scheme.Modules.pullbackPushforwardAdjunction h).unit.app
              (SheafOfModules.unit X.ringCatSheaf) ≫
            (Scheme.Modules.pushforward h).map
              (SheafOfModules.pullbackObjUnitToUnit h.toRingCatSheafHom)) ≫
          (Scheme.Modules.pushforward h).map
            (SheafOfModules.ιFree i ≫ (Grassmannian.pullbackFreeIso h N).inv ≫
              (Scheme.Modules.pullback h).map q) :=
      congrArg
        (fun m ↦ m ≫ (Scheme.Modules.pushforward h).map
          (SheafOfModules.ιFree i ≫ (Grassmannian.pullbackFreeIso h N).inv ≫
            (Scheme.Modules.pullback h).map q))
        (unitToPushforwardObjUnit_eq h)
    _ = (Scheme.Modules.pullbackPushforwardAdjunction h).unit.app
            (SheafOfModules.unit X.ringCatSheaf) ≫
          (Scheme.Modules.pushforward h).map
            (SheafOfModules.pullbackObjUnitToUnit h.toRingCatSheafHom ≫
              SheafOfModules.ιFree i ≫ (Grassmannian.pullbackFreeIso h N).inv ≫
                (Scheme.Modules.pullback h).map q) := by
      rw [Category.assoc, ← Functor.map_comp]
    _ = (Scheme.Modules.pullbackPushforwardAdjunction h).unit.app
            (SheafOfModules.unit X.ringCatSheaf) ≫
          (Scheme.Modules.pushforward h).map
            ((Scheme.Modules.pullback h).map (SheafOfModules.ιFree i ≫ q)) :=
      congrArg
        (fun m ↦ (Scheme.Modules.pullbackPushforwardAdjunction h).unit.app
            (SheafOfModules.unit X.ringCatSheaf) ≫ (Scheme.Modules.pushforward h).map m)
        (pullbackObjUnitToUnit_comp_pullbackFreeIso_inv_comp h M N q i)
    _ = (SheafOfModules.ιFree i ≫ q) ≫
          (Scheme.Modules.pullbackPushforwardAdjunction h).unit.app M :=
      ((Scheme.Modules.pullbackPushforwardAdjunction h).unit.naturality _).symm

omit [(SheafOfModules.pushforward.{u} h.toRingCatSheafHom).IsRightAdjoint] in
/-- The canonical morphism out of the unit module takes the unit section to the unit section. -/
private theorem unitToPushforwardObjUnit_val_app_one (U : X.Opens) :
    (SheafOfModules.unitToPushforwardObjUnit h.toRingCatSheafHom).val.app (op U)
        (1 : X.ringCatSheaf.obj.obj (op U)) =
      (1 : Y.ringCatSheaf.obj.obj (op (h ⁻¹ᵁ U))) :=
  (h.toRingCatSheafHom.hom.app (op U)).hom.map_one

end

/-- Pulling back a global section is applying the unit of the pullback-pushforward adjunction
over the whole of the target. -/
private theorem pullbackGlobalSections_apply {X Y : Scheme.{u}} (h : Y ⟶ X) (M : X.Modules)
    (s : Γ(M, ⊤)) :
    AlgebraicGeometry.pullbackGlobalSections h M s =
      ((Scheme.Modules.pullbackPushforwardAdjunction h).unit.app M).val.app
        (op (⊤ : X.Opens)) s := by
  show ((Scheme.Modules.pullback h).obj M).presheaf.map (𝟙 (op (⊤ : Y.Opens)))
      (((Scheme.Modules.pullbackPushforwardAdjunction h).unit.app M).val.app
        (op (⊤ : X.Opens)) s) = _
  exact Functor.map_id_apply _ _ _

/-- The pullback of the morphism out of the free module determined by a family of global sections
is the morphism determined by the pulled-back global sections. -/
theorem freeHomEquiv_pullbackFreeIso_inv {X Y : Scheme.{u}} (h : Y ⟶ X) (M : X.Modules) (N : ℕ)
    (q : SheafOfModules.free (R := X.ringCatSheaf) (ULift.{u} (Fin N)) ⟶ M)
    (i : ULift.{u} (Fin N)) :
    Stacks.NonvanishingSpelling.sectionsEquiv Y ((Scheme.Modules.pullback h).obj M)
        (((Scheme.Modules.pullback h).obj M).freeHomEquiv
          ((AlgebraicGeometry.Grassmannian.pullbackFreeIso h N).inv ≫
            (Scheme.Modules.pullback h).map q) i) =
      AlgebraicGeometry.pullbackGlobalSections h M
        (Stacks.NonvanishingSpelling.sectionsEquiv X M (M.freeHomEquiv q i)) := by
  let : (SheafOfModules.pushforward.{u} h.toRingCatSheafHom).IsRightAdjoint :=
    (Scheme.Modules.pullbackPushforwardAdjunction h).isRightAdjoint
  have key := congrArg
    (fun m : SheafOfModules.unit X.ringCatSheaf ⟶
        (Scheme.Modules.pushforward h).obj ((Scheme.Modules.pullback h).obj M) ↦
      m.val.app (op (⊤ : X.Opens)) (1 : X.ringCatSheaf.obj.obj (op ⊤)))
    (unitToPushforwardObjUnit_comp_pushforward_map h M N q i)
  have hleft : Stacks.NonvanishingSpelling.sectionsEquiv Y ((Scheme.Modules.pullback h).obj M)
        (((Scheme.Modules.pullback h).obj M).freeHomEquiv
          ((AlgebraicGeometry.Grassmannian.pullbackFreeIso h N).inv ≫
            (Scheme.Modules.pullback h).map q) i) =
      (SheafOfModules.unitToPushforwardObjUnit h.toRingCatSheafHom ≫
          (Scheme.Modules.pushforward h).map
            (SheafOfModules.ιFree i ≫
              (AlgebraicGeometry.Grassmannian.pullbackFreeIso h N).inv ≫
                (Scheme.Modules.pullback h).map q)).val.app (op (⊤ : X.Opens))
        (1 : X.ringCatSheaf.obj.obj (op ⊤)) := by
    show _ = ((Scheme.Modules.pushforward h).map
        (SheafOfModules.ιFree i ≫
          (AlgebraicGeometry.Grassmannian.pullbackFreeIso h N).inv ≫
            (Scheme.Modules.pullback h).map q)).val.app (op (⊤ : X.Opens))
          ((SheafOfModules.unitToPushforwardObjUnit h.toRingCatSheafHom).val.app
            (op (⊤ : X.Opens)) (1 : X.ringCatSheaf.obj.obj (op ⊤)))
    rw [unitToPushforwardObjUnit_val_app_one]
    rfl
  have hright := (pullbackGlobalSections_apply h M
    (Stacks.NonvanishingSpelling.sectionsEquiv X M (M.freeHomEquiv q i))).symm
  exact hleft.trans (key.trans hright)

end Stacks.ProjectiveFromSections

end
