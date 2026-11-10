module

public import StacksFrontier.Deformation.Smooth.CompleteLocalAlgebra.LiftingCriterion
import StacksFrontier.Deformation.Predeformation.PointsFromBase
import all StacksFrontier.Deformation.Smooth.CompleteLocalAlgebra.LocalizedBase
import all StacksFrontier.Deformation.Smooth.CompleteLocalAlgebra.LiftingCriterion

/-!
# Smooth complete local algebras: the power series condition (Stacks 0DYL, (5))

In the classical case the conditions of Stacks 0DYL are also equivalent to `R` being a
formal power series algebra over `Λ`:
`Deformation.smooth_formallySmooth_flat_specialFibre_powerSeries_tfae`.
-/

@[expose] public section

open CategoryTheory
open IsLocalRing
open scoped TensorProduct

universe u v w

namespace Deformation

variable {Λ : Type u} {k : Type w} [CommRing Λ] [Field k] [Algebra Λ k]

variable [IsNoetherianRing Λ] [Module.Finite Λ k]

omit [IsNoetherianRing Λ] [Module.Finite Λ k] in
private theorem restrictedRepresentableMap_isSmooth_iff_projection
    {L R : CompleteLocalAlgCat.{u, v, w} Λ k} (f : L ⟶ R)
    (hunique : ∀ A : ArtinianLocalAlgCat.{u, v, w} Λ k,
      Nonempty (L ⟶ artinianToComplete.obj A) ∧
        Subsingleton (L ⟶ artinianToComplete.obj A)) :
    IsSmooth (restrictedRepresentableMap f) ↔
      IsSmooth (restrictedCoyonedaProjection R) := by
  constructor
  · intro hs
    apply (restrictedCoyonedaProjection_lifts R).mpr
    intro B A q hq x
    let y := (hunique B).1.some
    let yE : (restrictedCoyoneda L).Elements := Functor.elementsMk _ B y
    let xE : (restrictedCoyoneda R).Elements := Functor.elementsMk _ A x
    let g : yE ⟶ (restrictedRepresentableMap f).obj xE :=
      Functor.Elements.homMk q ((hunique A).2.elim _ _)
    obtain ⟨x', h, a, hh, ha, ht⟩ := hs q hq yE xE g
      (IsHomLift.of_fac (p := (restrictedRepresentable L).p) q g rfl rfl rfl)
    rcases x' with @⟨B', z⟩
    have hB : B' = B := IsHomLift.domain_eq (p := (restrictedRepresentable R).p) q h
    subst B'
    have hv : h.hom = q := by
      have he := IsHomLift.fac' (p := (restrictedRepresentable R).p) q h
      change h.hom = (𝟙 B) ≫ q ≫ (𝟙 A) at he
      simpa only [Category.id_comp, Category.comp_id] using he
    refine ⟨z, ?_⟩
    apply CompleteLocalAlgCat.Hom.ext
    have hprop := congrArg CompleteLocalAlgCat.Hom.hom h.map_val
    simpa [xE, restrictedCoyoneda, restrictedCoyoneda_map_hom, hv] using hprop
  · intro hs B A q hq y x g hg
    let := hg
    have hy : y.obj = B := IsHomLift.domain_eq (p := (restrictedRepresentable L).p) q g
    have hx : x.obj = A := IsHomLift.codomain_eq (p := (restrictedRepresentable L).p) q g
    rcases y with @⟨B', y⟩
    rcases x with @⟨A', x⟩
    dsimp at hy hx
    subst B'
    subst A'
    obtain ⟨z, hz⟩ := (restrictedCoyonedaProjection_lifts R).mp hs q hq x
    let zE : (restrictedCoyoneda R).Elements := Functor.elementsMk _ B z
    let h : zE ⟶ Functor.elementsMk _ A x := Functor.Elements.homMk q hz
    let a : (restrictedRepresentableMap f).obj zE ⟶ Functor.elementsMk _ B y :=
      Functor.Elements.homMk (𝟙 B) ((hunique B).2.elim _ _)
    refine ⟨zE, h, a, ?_, ?_, ?_⟩
    · exact IsHomLift.of_fac (p := (restrictedRepresentable R).p) q h rfl rfl rfl
    · exact IsHomLift.of_fac (p := (restrictedRepresentable L).p) (𝟙 B) a rfl rfl rfl
    · apply Functor.Elements.hom_ext
      change q = (𝟙 B) ≫ g.hom
      rw [Category.id_comp]
      have he := IsHomLift.fac (p := (restrictedRepresentable L).p) q g
      change q = (𝟙 B) ≫ g.hom ≫ (𝟙 A) at he
      rw [Category.id_comp] at he
      exact he.trans (Category.comp_id g.hom)

omit [IsNoetherianRing Λ] [Module.Finite Λ k] in
private theorem structureMap_isLocal_of_residueEquiv
    [IsLocalRing Λ] {A : Type*} [CommRing A] [IsLocalRing A] [Algebra Λ A]
    (eΛ : ResidueField Λ ≃ₐ[Λ] k) (eA : ResidueField A ≃ₐ[Λ] k) :
    IsLocalHom (algebraMap Λ A) := by
  constructor
  intro a ha
  apply (residue_ne_zero_iff_isUnit a).mp
  intro hz
  have hzero : algebraMap Λ k a = 0 := by
    rw [← residueEquiv_structureMap eΛ a]
    simpa using congrArg eΛ hz
  have hzA : residue A (algebraMap Λ A a) = 0 := by
    apply eA.injective
    simpa only [map_zero, residueEquiv_structureMap] using hzero
  exact (residue_ne_zero_iff_isUnit _).mpr ha hzA

@[sga "7 XXII 4.4"]
private noncomputable def mvPowerSeries_mapAlgEquiv
    {K A B : Type*} [CommRing K] [CommRing A] [CommRing B]
    [Algebra K A] [Algebra K B] (σ : Type*) (e : A ≃ₐ[K] B) :
    MvPowerSeries σ A ≃ₐ[K] MvPowerSeries σ B where
  __ := MvPowerSeries.mapAlgHom e.toAlgHom
  invFun := MvPowerSeries.map e.symm.toRingHom
  left_inv f := by ext n; exact e.symm_apply_apply (f.coeff n)
  right_inv f := by ext n; exact e.apply_symm_apply (f.coeff n)

-- The power-series comparison elaborates the transported base and its algebra structures.
omit [IsNoetherianRing Λ] [Module.Finite Λ k] in
private theorem smooth_iff_powerSeries_of_small_base
    (R : CompleteLocalAlgCat.{u, v, w} Λ k) (c : IsNoetherianCompleteLocalRing Λ)
    (eΛ : letI := c.isLocal; ResidueField Λ ≃ₐ[Λ] k) [Small.{v} Λ] :
    IsSmooth (restrictedCoyonedaProjection R) ↔
      ∃ n : ℕ, Nonempty (R ≃ₐ[Λ] MvPowerSeries (Fin n) Λ) := by
  let : IsNoetherianRing Λ := c.isNoetherian
  let : IsLocalRing Λ := c.isLocal
  let : IsAdicComplete (maximalIdeal Λ) Λ := c.isComplete
  let e : Shrink.{v} Λ ≃ₐ[Λ] Λ := Shrink.algEquiv Λ Λ
  let : IsLocalRing (Shrink.{v} Λ) :=
    IsLocalRing.of_surjective' e.symm.toRingHom e.symm.surjective
  let : IsLocalHom e.toRingHom :=
    isLocalHom_of_leftInverse e.symm.toRingHom e.symm_apply_apply
  let : IsNoetherianRing (Shrink.{v} Λ) := isNoetherianRing_of_ringEquiv Λ e.symm
  have hc : IsAdicComplete (maximalIdeal (Shrink.{v} Λ)) (Shrink.{v} Λ) := by
    have hc' := (IsAdicComplete.congr_ringEquiv (maximalIdeal Λ) e.symm.toRingEquiv).mpr
      c.isComplete
    simpa only [IsLocalRing.map_ringEquiv_maximalIdeal] using hc'
  let L : CompleteLocalAlgCat.{u, v, w} Λ k :=
    { carrier := Shrink.{v} Λ
      completeLocal :=
        { isNoetherian := inferInstance
          isLocal := inferInstance
          isComplete := hc }
      residueEquiv := (ResidueField.mapAlgEquiv e).trans eΛ }
  let mk (X : CompleteLocalAlgCat.{u, v, w} Λ k) : L ⟶ X :=
    have : IsLocalHom (algebraMap Λ X) :=
      structureMap_isLocal_of_residueEquiv eΛ X.residueEquiv
    { hom := (Algebra.ofId Λ X).comp e.toAlgHom
      isLocal := RingHom.isLocalHom_comp (algebraMap Λ X) e.toRingHom
      residue_comm := fun a => by
        change X.residueEquiv (residue X (algebraMap Λ X (e a))) =
          eΛ (ResidueField.mapAlgEquiv e (residue _ a))
        rw [ResidueField.mapAlgEquiv_residue, residueEquiv_structureMap]
        exact (residueEquiv_structureMap eΛ (e a)).symm }
  let f : L ⟶ R := mk R
  have hunique : ∀ A : ArtinianLocalAlgCat.{u, v, w} Λ k,
      Nonempty (L ⟶ artinianToComplete.obj A) ∧
        Subsingleton (L ⟶ artinianToComplete.obj A) := by
    intro A
    refine ⟨⟨mk _⟩, ⟨fun g h => ?_⟩⟩
    apply CompleteLocalAlgCat.Hom.ext
    ext a
    have he : algebraMap Λ L (e a) = a := by
      apply e.injective
      rw [e.commutes]
      rfl
    rw [← he, g.hom.commutes, h.hom.commutes]
  rw [← restrictedRepresentableMap_isSmooth_iff_projection f hunique,
    restrictedRepresentableMap_isSmooth_iff_isPowerSeriesOver]
  let : Algebra L R := f.hom.toRingHom.toAlgebra
  let : IsScalarTower Λ L R := IsScalarTower.of_algebraMap_eq
    (fun a => (f.hom.commutes a).symm)
  have hsurj : Function.Surjective (algebraMap Λ L) := fun a =>
    ⟨e a, e.injective (e.commutes (e a))⟩
  change (∃ n : ℕ, Nonempty (R ≃ₐ[L] MvPowerSeries (Fin n) L)) ↔ _
  constructor
  · rintro ⟨n, ⟨h⟩⟩
    exact ⟨n, ⟨(h.restrictScalars Λ).trans (mvPowerSeries_mapAlgEquiv (Fin n) e)⟩⟩
  · rintro ⟨n, ⟨h⟩⟩
    exact ⟨n, ⟨AlgEquiv.extendScalarsOfSurjective hsurj
      (h.trans (mvPowerSeries_mapAlgEquiv (Fin n) e.symm))⟩⟩

/-- **Stacks 0DYL.** If the base is classical, the four smoothness conditions are also
equivalent to `R` being a formal power series algebra in finitely many variables over `Λ`. -/
@[stacks 0DYL "condition (5), classical case",
  ega "0 19.7.1" "classical case",
  ega "0 19.6.5" "complete, K=k: (2)⇔(5)"]
public theorem smooth_formallySmooth_flat_specialFibre_powerSeries_tfae
    (R : CompleteLocalAlgCat.{u, v, w} Λ k) (hΛ : IsClassical Λ k) :
    let k' := Λ ⧸ RingHom.ker (algebraMap Λ k)
    letI : (RingHom.ker (algebraMap Λ k)).IsMaximal :=
      Algebra.ker_algebraMap_isMaximal_of_isIntegral Λ k
    letI : Field k' := Ideal.Quotient.field _
    let Bbar := R ⊗[Λ] k'
    letI : Algebra k' Bbar := Algebra.TensorProduct.rightAlgebra
    List.TFAE [
      IsSmooth (restrictedCoyonedaProjection R),
      RingHom.FormallySmoothNAdic.{max u v} (algebraMap Λ R) (maximalIdeal R),
      Module.Flat Λ R ∧ Algebra.IsGeometricallyRegular k' Bbar,
      Module.Flat Λ R ∧
        RingHom.FormallySmoothNAdic.{max u v} (algebraMap k' Bbar)
          ((maximalIdeal R).map Algebra.TensorProduct.includeLeftRingHom),
      ∃ n : ℕ, Nonempty (R ≃ₐ[Λ] MvPowerSeries (Fin n) Λ)] := by
  dsimp only
  have h := smooth_formallySmooth_flat_specialFibre_tfae R
  obtain ⟨c, ⟨eΛ⟩⟩ := hΛ
  let : IsLocalRing Λ := c.isLocal
  let : IsLocalHom (algebraMap Λ R) :=
    structureMap_isLocal_of_residueEquiv eΛ R.residueEquiv
  tfae_have 1 ↔ 5 := by
    constructor
    · intro hs
      have hflat : Module.Flat Λ R ∧ _ := (h.out 1 3).mp hs
      have : Module.Flat Λ R := hflat.1
      have : Module.FaithfullyFlat Λ R := Module.FaithfullyFlat.of_flat_of_isLocalHom
      have : Small.{v} Λ := small_of_injective (FaithfulSMul.algebraMap_injective Λ R)
      exact (smooth_iff_powerSeries_of_small_base R c eΛ).mp hs
    · rintro ⟨n, ⟨e⟩⟩
      have hinj : Function.Injective (algebraMap Λ R) := by
        intro a b hab
        apply MvPowerSeries.C_injective (σ := Fin n)
        have heq := congrArg e hab
        rwa [e.commutes, e.commutes] at heq
      have : Small.{v} Λ := small_of_injective hinj
      exact (smooth_iff_powerSeries_of_small_base R c eΛ).mpr ⟨n, ⟨e⟩⟩
  tfae_have 1 ↔ 2 := h.out 1 2
  tfae_have 1 ↔ 3 := h.out 1 3
  tfae_have 1 ↔ 4 := h.out 1 4
  tfae_finish

end Deformation

end
