module

public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.CohomologicalDimension.Gabber.ZariskiRiemann.CenterStrictHenselizationLimitVanishing
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.CohomologicalDimension.Gabber.ZariskiRiemann.CenterLimitGermDeathOfInputs

/-!
# The limit layer of germ death at a valuation ring

This file proves `AlgebraicGeometry.Scheme.ZariskiRiemann.CenterLevelEventualVanishing`, the limit
layer of Gabber's germ-killing step at a valuation ring `V` of `K = Frac B` containing `B`
(Travaux de Gabber, Exposé XVIII-A, last remark of §2, Steps 2
and 4 of the proof). For a center range system `R_a` over the images `A_a ⊆ V` of the local rings at
the centers, the levels `η ×_{Spec A_a} Spec R_a` are identified with
`Spec R_a ×_{Spec B} Spec K`
(`AlgebraicGeometry.Scheme.ZariskiRiemann.CenterRangeSystem.levelComparison`): both are the
spectrum of the localization of `R_a` at the image of `B ∖ 0`, as `K` is the localization of `A_a`
at the image of `B ∖ 0` (`AlgebraicGeometry.Scheme.ZariskiRiemann.tensorBaseChangeEquiv`). The
latter form a cofiltered system with affine transition maps and limit
`Spec (colim R_a) ×_{Spec B} Spec K ≅ Spec (colim R_a ⊗_V K)`
(`AlgebraicGeometry.Scheme.ZariskiRiemann.isLimitLevelCone`), so Stacks 09YQ
(`Stacks.EtaleCohomology.LimitExt.exists_le_restriction_eq_zero_of_qcqs`) applies.

## Main definitions

* `AlgebraicGeometry.Scheme.ZariskiRiemann.tensorBaseChangeEquiv`: `R ⊗_A K ≃ₐ[R] R ⊗_B K` for
  `B → A ↪ K` with `K` the fraction field of `B`.
* `AlgebraicGeometry.Scheme.ZariskiRiemann.CenterRangeSystem.levelComparison`: the isomorphism
  `η ×_{Spec A_a} Spec R_a ⟶ Spec R_a ×_{Spec B} η`.
* `AlgebraicGeometry.Scheme.ZariskiRiemann.CenterRangeSystem.levelDiagram`: the levels of a
  center range system as a diagram, with limit cone
  `AlgebraicGeometry.Scheme.ZariskiRiemann.CenterRangeSystem.levelCone`.

## Main results

* `AlgebraicGeometry.Scheme.ZariskiRiemann.centerLevelEventualVanishing`:
  `CenterLevelEventualVanishing` holds.

## References

* Travaux de Gabber sur l'uniformisation locale et la cohomologie étale des schémas
  quasi-excellents, Exposé XVIII-A (L. Illusie), last remark of §2, Astérisque 363–364 (2014)
* [Stacks Project, Tag 09YQ](https://stacks.math.columbia.edu/tag/09YQ)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits Opposite
open AlgebraicGeometry AlgebraicGeometry.Scheme
open Stacks.StrictHenselization.DirectLimit
open scoped TensorProduct

universe u

namespace AlgebraicGeometry.Scheme.ZariskiRiemann

attribute [local instance high]
  Stacks.EtaleCohomology.ConstantTransport.hasExt_sheaf_smallEtaleTopology

open Stacks.EtaleCohomology Stacks.EtaleCohomology.LimitExt

section TensorBaseChange

variable {B : Type u} [CommRing B] {A : Type u} [CommRing A]
  [Algebra A (FractionRing B)] (β : B →+* A)
  (hβ : ∀ b, algebraMap A (FractionRing B) (β b) = algebraMap B (FractionRing B) b)
  (hinj : Function.Injective (algebraMap A (FractionRing B)))

include hβ hinj in
/-- If `B → A ↪ K = Frac B`, then `K` is the localization of `A` at the image of `B ∖ 0`. -/
theorem isLocalization_map_nonZeroDivisors :
    IsLocalization ((nonZeroDivisors B).map β) (FractionRing B) := by
  rw [isLocalization_iff]
  refine ⟨?_, ?_, ?_⟩
  · rintro ⟨_, b, hb, rfl⟩
    change IsUnit (algebraMap A (FractionRing B) (β b))
    rw [hβ]
    exact IsLocalization.map_units (FractionRing B) (⟨b, hb⟩ : nonZeroDivisors B)
  · intro z
    obtain ⟨⟨x, y⟩, h⟩ := IsLocalization.surj (nonZeroDivisors B) z
    refine ⟨⟨β x, ⟨β y, y, y.2, rfl⟩⟩, ?_⟩
    change z * algebraMap A (FractionRing B) (β y) = algebraMap A (FractionRing B) (β x)
    rw [hβ, hβ]
    exact h
  · intro x y hxy
    exact ⟨1, by rw [hinj hxy]⟩

variable (R : Type u) [CommRing R] [Algebra A R] [Algebra B R]
  (hR : ∀ b, algebraMap B R b = algebraMap A R (β b))

include hβ hinj hR in
/-- `R ⊗_A K` is the localization of `R` at the image of `B ∖ 0`. -/
theorem isLocalization_tensor_of_map :
    IsLocalization (Algebra.algebraMapSubmonoid R (nonZeroDivisors B))
      (R ⊗[A] FractionRing B) := by
  have := isLocalization_map_nonZeroDivisors β hβ hinj
  have h : Algebra.algebraMapSubmonoid R ((nonZeroDivisors B).map β) =
      Algebra.algebraMapSubmonoid R (nonZeroDivisors B) := by
    ext s
    constructor
    · rintro ⟨_, ⟨b, hb, rfl⟩, rfl⟩
      exact ⟨b, hb, hR b⟩
    · rintro ⟨b, hb, rfl⟩
      exact ⟨β b, ⟨b, hb, rfl⟩, (hR b).symm⟩
  rw [← h]
  infer_instance

/-- **`R ⊗_A K ≃ R ⊗_B K`** for `B → A ↪ K = Frac B` and an `A`-algebra `R` (with the
`B`-algebra structure through `B → A`): both are the localization of `R` at the image of
`B ∖ 0`. -/
def tensorBaseChangeEquiv : R ⊗[A] FractionRing B ≃ₐ[R] R ⊗[B] FractionRing B :=
  haveI := isLocalization_tensor_of_map β hβ hinj R hR
  IsLocalization.algEquiv (Algebra.algebraMapSubmonoid R (nonZeroDivisors B)) _ _

/-- `tensorBaseChangeEquiv` is the identity on `1 ⊗ x`. -/
theorem tensorBaseChangeEquiv_one_tmul (x : FractionRing B) :
    tensorBaseChangeEquiv β hβ hinj R hR (1 ⊗ₜ x) = 1 ⊗ₜ x := by
  have h := IsLocalization.ringHom_ext (nonZeroDivisors B)
    (j := (tensorBaseChangeEquiv β hβ hinj R hR).toRingHom.comp
      (Algebra.TensorProduct.includeRight :
        FractionRing B →ₐ[A] R ⊗[A] FractionRing B).toRingHom)
    (k := (Algebra.TensorProduct.includeRight :
        FractionRing B →ₐ[B] R ⊗[B] FractionRing B).toRingHom) ?_
  · exact RingHom.congr_fun h x
  · ext b
    have h1 : (1 : R) ⊗ₜ[A] algebraMap B (FractionRing B) b =
        algebraMap R (R ⊗[A] FractionRing B) (algebraMap B R b) := by
      rw [hR, ← hβ]
      exact (Algebra.TensorProduct.tmul_one_eq_one_tmul (A := R) (B := FractionRing B)
        (β b)).symm
    have h2 : (1 : R) ⊗ₜ[B] algebraMap B (FractionRing B) b =
        algebraMap R (R ⊗[B] FractionRing B) (algebraMap B R b) :=
      (Algebra.TensorProduct.tmul_one_eq_one_tmul (A := R) (B := FractionRing B) b).symm
    change tensorBaseChangeEquiv β hβ hinj R hR ((1 : R) ⊗ₜ[A] algebraMap B (FractionRing B) b) =
      (1 : R) ⊗ₜ[B] algebraMap B (FractionRing B) b
    rw [h1, h2, AlgEquiv.commutes]

end TensorBaseChange

namespace CenterRangeSystem

variable {B : Type u} [CommRing B] [IsDomain B] {V : ValuationSubring (FractionRing B)}
  {hV : ∀ b : B, algebraMap B (FractionRing B) b ∈ V} (S : CenterRangeSystem V hV)

/-- The projection `X_a ⟶ Spec R_a` of a level. -/
abbrev levelToStage (a : centerRanges V hV) : S.level a ⟶ Spec (.of (S.R a)) :=
  pullback.snd _ _

/-- The transition maps of the levels cover `Spec R_b ⟶ Spec R_a`. -/
@[reassoc]
theorem levelMap_levelToStage (a b : centerRanges V hV) (hab : a ≤ b) :
    S.levelMap a b hab ≫ S.levelToStage a =
      S.levelToStage b ≫ Spec.map (CommRingCat.ofHom (S.f a b hab)) :=
  pullback.lift_snd _ _ _

/-- Each level of a center range system is affine. -/
instance isAffine_level (a : centerRanges V hV) : IsAffine (S.level a) := by
  unfold CenterRangeSystem.level
  infer_instance

/-- The square making `levelComparison` well defined. -/
theorem levelComparison_w (a : centerRanges V hV) :
    S.levelToStage a ≫ Spec.map (CommRingCat.ofHom (levelBaseMap V hV S.R a)) =
      S.levelToGeneric a ≫ Spec.map (CommRingCat.ofHom (algebraMap B (FractionRing B))) := by
  have h := congrArg (· ≫ Spec.map (CommRingCat.ofHom (centerRangesBaseMap V hV a)))
    (pullback.condition (f := Spec.map (CommRingCat.ofHom (toFractionRing a)))
      (g := Spec.map (CommRingCat.ofHom (algebraMap a.1 (S.R a))))).symm
  simp only [Category.assoc, ← Spec.map_comp, ← CommRingCat.ofHom_comp] at h
  exact h

/-- **The comparison of levels** `η ×_{Spec A_a} Spec R_a ⟶ Spec R_a ×_{Spec B} η`. It is an
isomorphism (`isIso_levelComparison`). -/
def levelComparison (a : centerRanges V hV) : S.level a ⟶ ZariskiRiemann.level V hV S.R a :=
  pullback.lift (S.levelToStage a) (S.levelToGeneric a) (S.levelComparison_w a)

/-- The comparison of levels followed by the first projection is the projection to `Spec R_a`. -/
@[reassoc (attr := simp)]
theorem levelComparison_fst (a : centerRanges V hV) :
    S.levelComparison a ≫ pullback.fst _ _ = S.levelToStage a :=
  pullback.lift_fst _ _ _

/-- The comparison of levels commutes with the projections to the generic point `η`. -/
@[reassoc (attr := simp)]
theorem levelComparison_levelToGeneric (a : centerRanges V hV) :
    S.levelComparison a ≫ ZariskiRiemann.levelToGeneric V hV S.R a = S.levelToGeneric a :=
  pullback.lift_snd _ _ _

/-- **The comparison of levels is an isomorphism**: through `pullbackSpecIso` it is the spectrum
of `K ⊗_{A_a} R_a ≅ R_a ⊗_{A_a} K ≅ R_a ⊗_B K` (`tensorBaseChangeEquiv`). -/
instance isIso_levelComparison (a : centerRanges V hV) : IsIso (S.levelComparison a) := by
  let : Algebra a.1 (FractionRing B) := (toFractionRing a).toAlgebra
  let : Algebra B (S.R a) := (levelBaseMap V hV S.R a).toAlgebra
  have hβ : ∀ b, algebraMap a.1 (FractionRing B) (centerRangesBaseMap V hV a b) =
      algebraMap B (FractionRing B) b := fun _ => rfl
  have hinj : Function.Injective (algebraMap a.1 (FractionRing B)) :=
    fun x y h => Subtype.ext (Subtype.ext h)
  have hR : ∀ b, algebraMap B (S.R a) b = algebraMap a.1 (S.R a) (centerRangesBaseMap V hV a b) :=
    fun _ => rfl
  let χ := tensorBaseChangeEquiv (centerRangesBaseMap V hV a) hβ hinj (S.R a) hR
  let θ : S.R a ⊗[B] FractionRing B ≃+* FractionRing B ⊗[a.1] S.R a :=
    χ.symm.toRingEquiv.trans
      (Algebra.TensorProduct.comm a.1 (S.R a) (FractionRing B)).toRingEquiv
  have hθ1 : ∀ r : S.R a, θ (r ⊗ₜ 1) = 1 ⊗ₜ r := fun r => by
    have h1 : χ.symm (r ⊗ₜ[B] (1 : FractionRing B)) = r ⊗ₜ[a.1] (1 : FractionRing B) :=
      χ.symm.commutes r
    change Algebra.TensorProduct.comm a.1 (S.R a) (FractionRing B) (χ.symm (r ⊗ₜ 1)) = 1 ⊗ₜ r
    rw [h1, Algebra.TensorProduct.comm_tmul]
  have hθ2 : ∀ k : FractionRing B, θ (1 ⊗ₜ k) = k ⊗ₜ 1 := fun k => by
    have h2 : χ.symm ((1 : S.R a) ⊗ₜ[B] k) = (1 : S.R a) ⊗ₜ[a.1] k := by
      rw [AlgEquiv.symm_apply_eq]
      exact (tensorBaseChangeEquiv_one_tmul _ hβ hinj (S.R a) hR k).symm
    change Algebra.TensorProduct.comm a.1 (S.R a) (FractionRing B) (χ.symm (1 ⊗ₜ k)) = k ⊗ₜ 1
    rw [h2, Algebra.TensorProduct.comm_tmul]
  let φ : CommRingCat.of (S.R a ⊗[B] FractionRing B) ⟶
      CommRingCat.of (FractionRing B ⊗[a.1] S.R a) :=
    CommRingCat.ofHom θ.toRingHom
  let ψ : CommRingCat.of (FractionRing B ⊗[a.1] S.R a) ⟶
      CommRingCat.of (S.R a ⊗[B] FractionRing B) :=
    CommRingCat.ofHom θ.symm.toRingHom
  have e1 : φ ≫ ψ = 𝟙 _ := CommRingCat.hom_ext (RingHom.ext fun x => θ.symm_apply_apply x)
  have e2 : ψ ≫ φ = 𝟙 _ := CommRingCat.hom_ext (RingHom.ext fun x => θ.apply_symm_apply x)
  have : IsIso (Spec.map φ) :=
    ⟨⟨Spec.map ψ, by rw [← Spec.map_comp, e2, Spec.map_id],
      by rw [← Spec.map_comp, e1, Spec.map_id]⟩⟩
  let P := pullbackSpecIso a.1 (FractionRing B) (S.R a)
  let Q := pullbackSpecIso B (S.R a) (FractionRing B)
  have hI : IsIso (P.hom ≫ Spec.map φ ≫ Q.inv) := inferInstance
  have key : S.levelComparison a = P.hom ≫ Spec.map φ ≫ Q.inv := by
    refine pullback.hom_ext ?_ ?_
    · refine (S.levelComparison_fst a).trans ?_
      have h1 := pullbackSpecIso_inv_fst B (S.R a) (FractionRing B)
      have h3 : CommRingCat.ofHom (Algebra.TensorProduct.includeLeftRingHom :
            S.R a →+* S.R a ⊗[B] FractionRing B) ≫ φ =
          CommRingCat.ofHom ((Algebra.TensorProduct.includeRight :
            S.R a →ₐ[a.1] FractionRing B ⊗[a.1] S.R a) :
              S.R a →+* FractionRing B ⊗[a.1] S.R a) :=
        CommRingCat.hom_ext (RingHom.ext hθ1)
      refine (pullbackSpecIso_hom_snd a.1 (FractionRing B) (S.R a)).symm.trans
        (Eq.trans ?_ ((Category.assoc _ _ _).trans (congrArg (P.hom ≫ ·)
          (Category.assoc _ _ _))).symm)
      calc P.hom ≫ Spec.map (CommRingCat.ofHom
            ((Algebra.TensorProduct.includeRight :
              S.R a →ₐ[a.1] FractionRing B ⊗[a.1] S.R a) :
                S.R a →+* FractionRing B ⊗[a.1] S.R a))
        _ = P.hom ≫ Spec.map (CommRingCat.ofHom (Algebra.TensorProduct.includeLeftRingHom :
            S.R a →+* S.R a ⊗[B] FractionRing B) ≫ φ) :=
            congrArg (fun t => P.hom ≫ Spec.map t) h3.symm
        _ = P.hom ≫ Spec.map φ ≫ Spec.map (CommRingCat.ofHom
            (Algebra.TensorProduct.includeLeftRingHom :
              S.R a →+* S.R a ⊗[B] FractionRing B)) :=
            congrArg (P.hom ≫ ·) (Spec.map_comp _ _)
        _ = P.hom ≫ Spec.map φ ≫ Q.inv ≫ pullback.fst _ _ :=
            congrArg (fun t => P.hom ≫ Spec.map φ ≫ t) h1.symm
    · refine (S.levelComparison_levelToGeneric a).trans ?_
      have h1 := pullbackSpecIso_inv_snd B (S.R a) (FractionRing B)
      have h3 : CommRingCat.ofHom ((Algebra.TensorProduct.includeRight :
            FractionRing B →ₐ[B] S.R a ⊗[B] FractionRing B) :
              FractionRing B →+* S.R a ⊗[B] FractionRing B) ≫ φ =
          CommRingCat.ofHom (Algebra.TensorProduct.includeLeftRingHom :
            FractionRing B →+* FractionRing B ⊗[a.1] S.R a) :=
        CommRingCat.hom_ext (RingHom.ext hθ2)
      refine (pullbackSpecIso_hom_fst a.1 (FractionRing B) (S.R a)).symm.trans
        (Eq.trans ?_ ((Category.assoc _ _ _).trans (congrArg (P.hom ≫ ·)
          (Category.assoc _ _ _))).symm)
      calc P.hom ≫ Spec.map (CommRingCat.ofHom
            (Algebra.TensorProduct.includeLeftRingHom :
              FractionRing B →+* FractionRing B ⊗[a.1] S.R a))
        _ = P.hom ≫ Spec.map (CommRingCat.ofHom ((Algebra.TensorProduct.includeRight :
            FractionRing B →ₐ[B] S.R a ⊗[B] FractionRing B) :
              FractionRing B →+* S.R a ⊗[B] FractionRing B) ≫ φ) :=
            congrArg (fun t => P.hom ≫ Spec.map t) h3.symm
        _ = P.hom ≫ Spec.map φ ≫ Spec.map (CommRingCat.ofHom
            ((Algebra.TensorProduct.includeRight :
              FractionRing B →ₐ[B] S.R a ⊗[B] FractionRing B) :
                FractionRing B →+* S.R a ⊗[B] FractionRing B)) :=
            congrArg (P.hom ≫ ·) (Spec.map_comp _ _)
        _ = P.hom ≫ Spec.map φ ≫ Q.inv ≫ pullback.snd _ _ :=
            congrArg (fun t => P.hom ≫ Spec.map φ ≫ t) h1.symm
  rw [key]
  exact hI

/-- **The comparison of levels commutes with the transition maps.** -/
@[reassoc]
theorem levelMap_levelComparison (a b : centerRanges V hV) (hab : a ≤ b) :
    S.levelMap a b hab ≫ S.levelComparison a =
      S.levelComparison b ≫ levelTransition V hV S.R S.f S.f_algebraMap a b hab := by
  refine pullback.hom_ext ?_ ?_
  · simp only [Category.assoc]
    rw [S.levelComparison_fst a, levelTransition_fst, S.levelComparison_fst_assoc b]
    exact S.levelMap_levelToStage a b hab
  · simp only [Category.assoc]
    rw [S.levelComparison_levelToGeneric a, levelTransition_snd,
      S.levelComparison_levelToGeneric b]
    exact S.levelMap_levelToGeneric a b hab

/-- **The cofiltered diagram of the levels** `η ×_{Spec A_a} Spec R_a` of a center range
system, with the transition maps `levelMap`. -/
def levelDiagram : (centerRanges V hV)ᵒᵖ ⥤ Scheme.{u} where
  obj a := S.level a.unop
  map {a b} h := S.levelMap b.unop a.unop h.unop.le
  map_id a := by
    rw [← cancel_mono (S.levelComparison a.unop), S.levelMap_levelComparison, Category.id_comp]
    exact (congrArg (S.levelComparison a.unop ≫ ·)
      ((ZariskiRiemann.levelDiagram V hV S.R S.f S.f_algebraMap
        (hds := S.directedSystem)).map_id a)).trans (Category.comp_id _)
  map_comp {a b c} h g := by
    rw [← cancel_mono (S.levelComparison c.unop)]
    simp only [Category.assoc, levelMap_levelComparison, levelMap_levelComparison_assoc]
    exact congrArg (S.levelComparison a.unop ≫ ·)
      ((ZariskiRiemann.levelDiagram V hV S.R S.f S.f_algebraMap
        (hds := S.directedSystem)).map_comp h g)

/-- The transition maps of the levels are affine. -/
instance isAffineHom_levelDiagram_map {a b : (centerRanges V hV)ᵒᵖ} (g : a ⟶ b) :
    IsAffineHom (S.levelDiagram.map g) :=
  haveI : IsAffine (S.levelDiagram.obj a) := S.isAffine_level a.unop
  haveI : IsAffine (S.levelDiagram.obj b) := S.isAffine_level b.unop
  isAffineHom_of_isAffine _

/-- The levels `η ×_{Spec A_a} Spec R_a` and `Spec R_a ×_{Spec B} η` form isomorphic
diagrams. -/
def levelDiagramIso : S.levelDiagram ≅
    ZariskiRiemann.levelDiagram V hV S.R S.f S.f_algebraMap (hds := S.directedSystem) :=
  NatIso.ofComponents
    (fun a => @asIso _ _ _ _ (S.levelComparison a.unop) (S.isIso_levelComparison a.unop))
    (fun {a b} h => S.levelMap_levelComparison b.unop a.unop h.unop.le)

variable [Algebra V S.colimit]
  (hpin : ∀ (a : centerRanges V hV) (x : a.1), algebraMap V S.colimit x =
    Ring.DirectLimit.of S.R (fun a b h => S.f a b h) a (algebraMap a.1 (S.R a) x))

/-- The limit cone of the levels, with apex `Spec (colim R_a) ×_{Spec B} Spec K`. -/
def levelCone : Cone S.levelDiagram :=
  (Cone.postcompose S.levelDiagramIso.inv).obj
    (ZariskiRiemann.levelCone V hV S.R S.f S.f_algebraMap (hds := S.directedSystem) hpin)

/-- **`Spec (colim R_a) ×_{Spec B} Spec K` is the limit of the levels.** -/
def isLimitLevelCone : IsLimit (S.levelCone hpin) :=
  (IsLimit.postcomposeInvEquiv _ _).symm
    (ZariskiRiemann.isLimitLevelCone V hV S.R S.f S.f_algebraMap (hds := S.directedSystem) hpin)

/-- The legs of `levelCone` lie over `η`. -/
theorem levelCone_π_app_levelToGeneric (a : centerRanges V hV) :
    (S.levelCone hpin).π.app (op a) ≫ S.levelToGeneric a =
      pullback.snd (Spec.map (CommRingCat.ofHom (colimitBaseMap V hV S.R S.f)))
        (Spec.map (CommRingCat.ofHom (algebraMap B (FractionRing B)))) := by
  have h0 : S.levelDiagramIso.inv.app (op a) = inv (S.levelComparison a) := rfl
  have h : inv (S.levelComparison a) ≫ S.levelToGeneric a =
      ZariskiRiemann.levelToGeneric V hV S.R a := by
    rw [IsIso.inv_comp_eq]
    exact (S.levelComparison_levelToGeneric a).symm
  refine (Category.assoc _ _ _).trans ?_
  refine (congrArg (fun t => (ZariskiRiemann.levelCone V hV S.R S.f S.f_algebraMap
    (hds := S.directedSystem) hpin).π.app (op a) ≫ t ≫ S.levelToGeneric a) h0).trans ?_
  refine (congrArg ((ZariskiRiemann.levelCone V hV S.R S.f S.f_algebraMap
    (hds := S.directedSystem) hpin).π.app (op a) ≫ ·) h).trans ?_
  exact ZariskiRiemann.levelCone_π_app_levelToGeneric V hV S.R S.f S.f_algebraMap
    (hds := S.directedSystem) hpin a

end CenterRangeSystem

/-- **The limit layer of germ death at a valuation ring** (Steps 2 and 4
of Gabber's proof; Stacks 09YQ). For a center range system `R_a` whose colimit carries a compatible
`V`-algebra structure, if `H^q(Spec (colim R_a ⊗_V K), F|) = 0` then every class on a level
`η ×_{Spec A_a} Spec R_a` dies on all sufficiently large levels. -/
theorem centerLevelEventualVanishing : CenterLevelEventualVanishing.{u} := by
  intro B _ _ F q V hV S _ hpin hF a c
  have := S.directedSystem
  let : Algebra B S.colimit := (colimitBaseMap V hV S.R S.f).toAlgebra
  have hlim : Subsingleton (Sheaf.H.{u + 1} ((etaleAbelianInverseImage.{u, 0}
      (pullback.snd (Spec.map (CommRingCat.ofHom (colimitBaseMap V hV S.R S.f)))
        (Spec.map (CommRingCat.ofHom (algebraMap B (FractionRing B)))))).obj F) q) :=
    subsingleton_H_pullback_snd_of_tensor V hV S.colimit (fun _ => rfl) F q hF
  have hlim' := (subsingleton_H_iff_of_iso ((etaleAbelianInverseImageCompIso'.{u, 0}
    ((S.levelCone hpin).π.app (op a)) (S.levelToGeneric a) _
    (S.levelCone_π_app_levelToGeneric hpin a).symm).app F) q).mp hlim
  have : CompactSpace (S.levelDiagram.obj (op a)) :=
    inferInstanceAs (CompactSpace (S.level a))
  have : QuasiSeparatedSpace (S.levelDiagram.obj (op a)) :=
    inferInstanceAs (QuasiSeparatedSpace (S.level a))
  obtain ⟨b, hab, hb⟩ := exists_le_restriction_eq_zero_of_qcqs S.levelDiagram (S.levelCone hpin)
    (S.isLimitLevelCone hpin) a (S.levelSheaf F a) q c (hlim'.elim _ _)
  refine ⟨b, hab, fun b' hab' hbb' => ?_⟩
  have hcomp : S.levelMap a b' hab' = S.levelMap b b' hbb' ≫ S.levelMap a b hab :=
    S.levelDiagram.map_comp (homOfLE hbb').op (homOfLE hab).op
  have hb' : etaleCohomologyRestrictionMap.{u, 0, u + 1} (S.levelMap a b hab) _ q c = 0 := hb
  exact (restriction_restriction_eq_zero_iff (S.levelMap a b hab) (S.levelMap b b' hbb') _ hcomp
    _ q c).mp (by rw [hb', map_zero])

end AlgebraicGeometry.Scheme.ZariskiRiemann

end
