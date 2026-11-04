module

public import Mathlib.AlgebraicGeometry.Morphisms.Finite
public import Mathlib.AlgebraicGeometry.Noetherian
public import Mathlib.AlgebraicGeometry.Morphisms.QuasiFinite
public import Mathlib.Algebra.Category.ModuleCat.Stalk
public import Mathlib.AlgebraicGeometry.Modules.Sheaf
public import StacksFrontier.Algebra.Category.ModuleCat.Sheaf.Coherent
public import StacksFrontier.RingTheory.Depth.Defs.Defs
public import StacksCore.Tactic.StacksAttribute
public import StacksFrontier.AlgebraicGeometry.CoherenceCriteria.Basic
public import StacksFrontier.AlgebraicGeometry.Divisors.HartogsExtension.Basic

/-!
# Sections over a punctured spectrum

Let `A` be a Noetherian local ring and let `Y` be finite over `Spec A`. If the local ring of `Y`
at every closed point has depth at least two, then `Y` is the spectrum of the ring of sections
over the inverse image of the punctured spectrum of `A`.

## Main results

* `AlgebraicGeometry.exists_iso_spec_sections_punctured_spectrum` identifies `Y` with the
  spectrum of the sections over the inverse image of the punctured spectrum.

## Implementation notes

The punctured spectrum is represented by the open complement of the closed point of the local
ring. The asserted isomorphism is characterized canonically: after mapping to the spectrum of
the global sections by restriction, it is the unit `Y.toSpecΓ` of the global-sections--spectrum
adjunction. The depth hypothesis is transported from the stalk of the structure sheaf to the
stalk of the unit sheaf of modules by `unitStalkLinearEquiv`.

## References

* [Stacks Project, Tag 0BM8](https://stacks.math.columbia.edu/tag/0BM8)
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits Opposite TopologicalSpace
open scoped AlgebraicGeometry

universe u

namespace AlgebraicGeometry

private lemma depth_eq_of_linearEquiv {R : Type u} [CommRing R] (I : Ideal R)
    {M N : Type u} [AddCommGroup M] [Module R M] [AddCommGroup N] [Module R N]
    (e : M ≃ₗ[R] N) :
    Module.depth R I M = Module.depth R I N := by
  have hset : {rs : List R | (∀ r ∈ rs, r ∈ I) ∧ RingTheory.Sequence.IsRegular M rs} =
      {rs : List R | (∀ r ∈ rs, r ∈ I) ∧ RingTheory.Sequence.IsRegular N rs} := by
    ext rs
    simp only [Set.mem_ofPred_eq, e.isRegular_congr rs]
  have htop : I • (⊤ : Submodule R M) = ⊤ ↔ I • (⊤ : Submodule R N) = ⊤ := by
    rw [← Submodule.map_eq_top_iff (e := e), Submodule.map_smul'', Submodule.map_top,
      LinearEquiv.range]
  simp only [Module.depth, hset, htop]

private noncomputable def unitStalkLinearEquiv {X : TopCat.{u}}
    (R : TopCat.Presheaf CommRingCat.{u} X) (x : X) :
    (ToType (TopCat.Presheaf.stalk
      (PresheafOfModules.unit (R ⋙ forget₂ _ RingCat.{u})).presheaf x))
      ≃ₗ[ToType (R.stalk x)] (ToType (R.stalk x)) := by
  set pIso : (forget₂ CommRingCat.{u} RingCat.{u} ⋙
      forget₂ RingCat.{u} AddCommGrpCat.{u}).obj (R.stalk x) ≅
      TopCat.Presheaf.stalk
        (PresheafOfModules.unit (R ⋙ forget₂ _ RingCat.{u})).presheaf x :=
    preservesColimitIso (forget₂ CommRingCat.{u} RingCat.{u} ⋙
      forget₂ RingCat.{u} AddCommGrpCat.{u}) ((OpenNhds.inclusion x).op ⋙ R) with hpIso
  set addE : (ToType (TopCat.Presheaf.stalk
      (PresheafOfModules.unit (R ⋙ forget₂ _ RingCat.{u})).presheaf x)) ≃+
      ToType (R.stalk x) := pIso.symm.addCommGroupIsoToAddEquiv
  -- The sections of the unit presheaf of modules over `U` are the sections of `R` over `U`,
  -- but the two spellings differ by unfolding `PresheafOfModules.unit`.  Taking `s` in the
  -- module spelling is what lets `germ_smul` and this lemma be used in the same rewrite below.
  have key : ∀ (U : Opens X) (hxU : x ∈ U)
      (s : ToType ((PresheafOfModules.unit (R ⋙ forget₂ _ RingCat.{u})).obj
        (Opposite.op U))),
      addE ((ConcreteCategory.hom (TopCat.Presheaf.germ
        (PresheafOfModules.unit (R ⋙ forget₂ _ RingCat.{u})).presheaf U x hxU)) s) =
      (ConcreteCategory.hom (R.germ U x hxU)) s := by
    intro U hxU s
    have h := ι_preservesColimitIso_inv (forget₂ CommRingCat.{u} RingCat.{u} ⋙
      forget₂ RingCat.{u} AddCommGrpCat.{u}) ((OpenNhds.inclusion x).op ⋙ R)
      (Opposite.op ⟨U, hxU⟩)
    rw [← hpIso] at h
    have h2 := congrArg (fun (f : _ ⟶ _) => (ConcreteCategory.hom f) s) h
    change (ConcreteCategory.hom (colimit.ι (((OpenNhds.inclusion x).op ⋙ R) ⋙
          (forget₂ CommRingCat.{u} RingCat.{u} ⋙ forget₂ RingCat.{u} AddCommGrpCat.{u}))
          (Opposite.op ⟨U, hxU⟩) ≫ pIso.inv)) s =
        (ConcreteCategory.hom ((forget₂ CommRingCat.{u} RingCat.{u} ⋙
          forget₂ RingCat.{u} AddCommGrpCat.{u}).map
          (colimit.ι ((OpenNhds.inclusion x).op ⋙ R) (Opposite.op ⟨U, hxU⟩)))) s
    exact h2
  refine { addE with toFun := addE, map_smul' := ?_ }
  intro r m
  obtain ⟨U, hxU, m₀, rfl⟩ := TopCat.Presheaf.exists_germ_eq
    (PresheafOfModules.unit (R ⋙ forget₂ _ RingCat.{u})).presheaf m
  obtain ⟨V, hxV, r₀, rfl⟩ := TopCat.Presheaf.exists_germ_eq R r
  set W : Opens X := U ⊓ V
  have hxW : x ∈ W := ⟨hxU, hxV⟩
  have hr : (ConcreteCategory.hom (R.germ V x hxV)) r₀ =
      (ConcreteCategory.hom (R.germ W x hxW))
        ((ConcreteCategory.hom (R.map (homOfLE (inf_le_right)).op)) r₀) := by
    rw [TopCat.Presheaf.germ_res_apply]
  have hm : (ConcreteCategory.hom (TopCat.Presheaf.germ
      (PresheafOfModules.unit (R ⋙ forget₂ _ RingCat.{u})).presheaf U x hxU)) m₀ =
      (ConcreteCategory.hom (TopCat.Presheaf.germ
        (PresheafOfModules.unit (R ⋙ forget₂ _ RingCat.{u})).presheaf W x hxW))
        ((ConcreteCategory.hom ((PresheafOfModules.unit
          (R ⋙ forget₂ _ RingCat.{u})).presheaf.map (homOfLE (inf_le_left)).op)) m₀) := by
    rw [TopCat.Presheaf.germ_res_apply]
  rw [hr, hm]
  set rr : ToType (R.obj (Opposite.op W)) :=
    (ConcreteCategory.hom (R.map (homOfLE (inf_le_right)).op)) r₀
  set mm : ToType ((PresheafOfModules.unit
      (R ⋙ forget₂ _ RingCat.{u})).obj (Opposite.op W)) :=
    (ConcreteCategory.hom ((PresheafOfModules.unit
      (R ⋙ forget₂ _ RingCat.{u})).presheaf.map (homOfLE (inf_le_left)).op)) m₀
  rw [← PresheafOfModules.germ_smul
    (PresheafOfModules.unit (R ⋙ forget₂ _ RingCat.{u})) x W hxW rr mm]
  rw [key, key]
  change ↑(R.obj (Opposite.op W)) at mm
  change (R.germ W x hxW).hom (rr * mm) =
    (R.germ W x hxW).hom rr * (R.germ W x hxW).hom mm
  exact map_mul _ _ _

/-- **Stacks Project, Tag 0BM8.** A scheme finite over the spectrum of a Noetherian local ring,
whose local rings at closed points all have depth at least two, is canonically the spectrum of
its sections over the inverse image of the punctured spectrum. -/
@[stacks 0BM8]
lemma exists_iso_spec_sections_punctured_spectrum
    (A : Type u) [CommRing A] [IsNoetherianRing A] [IsLocalRing A]
    {Y : Scheme.{u}} (π : Y ⟶ Spec (.of A)) [IsFinite π]
    (hdepth : ∀ y : Y, IsClosed ({y} : Set Y) →
      2 ≤ Module.depth (Y.presheaf.stalk y)
        (IsLocalRing.maximalIdeal (Y.presheaf.stalk y)) (Y.presheaf.stalk y)) :
    let U : (Spec (.of A)).Opens :=
      ⟨({IsLocalRing.closedPoint A} : Set (PrimeSpectrum A))ᶜ,
        IsLocalRing.isClosed_singleton_closedPoint A |>.isOpen_compl⟩
    let V : Y.Opens := π ⁻¹ᵁ U
    ∃ e : Y ≅ Spec Γ(Y, V),
      e.hom ≫ Spec.map (Y.presheaf.map (homOfLE le_top).op) = Y.toSpecΓ := by
  let X := Spec (.of A)
  let x₀ : X := IsLocalRing.closedPoint A
  let U : X.Opens :=
    ⟨({IsLocalRing.closedPoint A} : Set (PrimeSpectrum A))ᶜ,
      IsLocalRing.isClosed_singleton_closedPoint A |>.isOpen_compl⟩
  let V : Y.Opens := π ⁻¹ᵁ U
  have : IsLocallyNoetherian Y := LocallyOfFiniteType.isLocallyNoetherian π
  have : IsAffine Y := isAffine_of_isAffineHom π
  let F : Y.Modules := SheafOfModules.unit Y.ringCatSheaf
  have : F.IsCoherent := by dsimp [F]; infer_instance
  have hdepthV : ∀ y : Y, y ∉ (V : Set Y) →
      let M := TopCat.Presheaf.stalk (C := Ab.{u}) F.val.presheaf y
      let : Module (Y.presheaf.stalk y) M :=
        PresheafOfModules.instModuleCarrierStalkCommRingCatCarrierAbPresheafOpensCarrier
          F.val y
      (2 : ℕ∞) ≤ Module.depth (Y.presheaf.stalk y)
        (IsLocalRing.maximalIdeal (Y.presheaf.stalk y)) M := by
    intro y hy
    have hmap : π y = x₀ := by
      have hmem : π y ∈ ({IsLocalRing.closedPoint A} : Set X) := by
        change π y ∉ (({IsLocalRing.closedPoint A} : Set X)ᶜ) at hy
        simpa using hy
      simpa [x₀] using (Set.mem_singleton_iff.mp hmem)
    have hfiberClosed : IsClosed (π ⁻¹' ({x₀} : Set X)) :=
      (IsLocalRing.isClosed_singleton_closedPoint A).preimage π.continuous
    have hfiberDiscrete : _root_.IsDiscrete (π ⁻¹' ({x₀} : Set X)) :=
      π.isDiscrete_preimage_singleton x₀
    let : DiscreteTopology (π ⁻¹' ({x₀} : Set X)) :=
      (_root_.isDiscrete_iff_discreteTopology).mp hfiberDiscrete
    have hsingletonClosed : IsClosed ({⟨y, hmap⟩} : Set (π ⁻¹' ({x₀} : Set X))) :=
      isClosed_singleton
    have hyclosed : IsClosed ({y} : Set Y) := by
      convert hfiberClosed.isClosedMap_subtype_val _ hsingletonClosed using 1
      ext z
      simp
    let M := TopCat.Presheaf.stalk (C := Ab.{u}) F.val.presheaf y
    let : Module (Y.presheaf.stalk y) M :=
      PresheafOfModules.instModuleCarrierStalkCommRingCatCarrierAbPresheafOpensCarrier
        F.val y
    change (2 : ℕ∞) ≤ Module.depth (Y.presheaf.stalk y)
      (IsLocalRing.maximalIdeal (Y.presheaf.stalk y))
      (ToType (TopCat.Presheaf.stalk
        (PresheafOfModules.unit (Y.presheaf ⋙ forget₂ CommRingCat RingCat)).presheaf y))
    rw [depth_eq_of_linearEquiv (IsLocalRing.maximalIdeal (Y.presheaf.stalk y))
      (unitStalkLinearEquiv Y.presheaf y)]
    exact hdepth y hyclosed
  let ρ : CommRingCat.of Γ(Y, ⊤) ⟶ CommRingCat.of Γ(Y, V) :=
    Y.presheaf.map (homOfLE (show V ≤ (⊤ : Y.Opens) from le_top)).op
  have : IsIso ρ := (ConcreteCategory.isIso_iff_bijective ρ).mpr
    (AlgebraicGeometry.restriction_bijective_of_depth_ge_two Y F V hdepthV)
  let s : Spec Γ(Y, V) ⟶ Spec Γ(Y, ⊤) := Spec.map ρ
  have : IsIso s := by dsimp [s]; infer_instance
  let e : Y ≅ Spec Γ(Y, V) := asIso Y.toSpecΓ ≪≫ (asIso s).symm
  refine ⟨e, ?_⟩
  dsimp [e, s]
  simp

end AlgebraicGeometry

end
