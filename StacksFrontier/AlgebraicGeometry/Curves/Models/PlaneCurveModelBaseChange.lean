module

public import Mathlib.RingTheory.TensorProduct.MvPolynomial
public import Mathlib.RingTheory.TensorProduct.Quotient
public import StacksFrontier.AlgebraicGeometry.Blowup.ProjBaseChangeGlobal
public import StacksFrontier.AlgebraicGeometry.Curves.Models.PlaneCurveModel
public import StacksFrontier.AlgebraicGeometry.HomogeneousQuotient.Defs
public import StacksFrontier.AlgebraicGeometry.ProjModelStructureMap.BaseChange

/-!
# Base change and linear coordinate changes of a plane curve `V(F)`

Let `F ∈ R[T₀, T₁, T₂]` be homogeneous and let `V(F) = Proj (R[T₀, T₁, T₂]/(F))`. This file
proves two facts about these plane curves.

* For a ring map `φ : R →+* S`, the base change of `V(F)` along `Spec S ⟶ Spec R` is `V(φ F)`.
  The square formed by `V(φ F) ⟶ V(F)`, the two structure morphisms and `Spec S ⟶ Spec R` is
  cartesian.
* A graded automorphism `σ` of `S[T₀, T₁, T₂]` with `σ F ∈ (G)` and `σ⁻¹ G ∈ (F)` induces an
  isomorphism `V(G) ≅ V(F)` over `Spec S`. Linear changes of coordinates are of this kind.

## Main definitions

* `Stacks.Models.PlaneCurveModel.coordHom`: the homomorphism `R[T]/(F) → S[T]/(G)` induced by a
  graded homomorphism of polynomial rings carrying `F` into `(G)`.
* `Stacks.Models.PlaneCurveModel.mapMap`: the morphism `V(φ F) ⟶ V(F)`.
* `Stacks.Models.PlaneCurveModel.changeMap`: the isomorphism `V(G) ⟶ V(F)` induced by a
  graded automorphism.

## Main results

* `Stacks.Models.PlaneCurveModel.isPullback_mapMap`: **base change of `V(F)` is `V(φ F)`.**
* `Stacks.Models.PlaneCurveModel.isIso_changeMap` and
  `Stacks.Models.PlaneCurveModel.changeMap_toSpec`: the coordinate change is an isomorphism
  over `Spec S`.

## Implementation notes

The base change goes through `Stacks.ProjBaseChange.isPullback_map_of_baseChange`
([Stacks, Tag 01N2]), which needs a grading by `R`-submodules. The grading of
`Stacks.Models.PlaneCurveModel.grading` is by additive subgroups, so the argument passes through
`moduleGrading F hF`, which has the same pieces as submodules. `moduleGradingIso F hF` identifies
the two `Proj`s. The graded isomorphism `S ⊗[R] R[T]/(F) ≅ S[T]/(φ F)` is `baseChangeEquiv`.
The argument follows the one for Weierstrass cubics in
`StacksFrontier/AlgebraicGeometry/Stacks/WeierstrassCubicIso.lean`, for an arbitrary homogeneous
equation.

## References

* [Stacks Project, Tag 01N2](https://stacks.math.columbia.edu/tag/01N2)
* [Stacks Project, Tag 0CDL](https://stacks.math.columbia.edu/tag/0CDL)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry MvPolynomial
open scoped TensorProduct

universe u

namespace Stacks.Models.PlaneCurveModel

attribute [local instance] MvPolynomial.gradedAlgebra

variable {R : Type u} [CommRing R]

/-! ### The degree-zero part and the structure morphism -/

section DegreeZero

variable (F : MvPolynomial (Fin 3) R) {d : ℕ} (hF : F.IsHomogeneous d)

/-- The constants `R → (R[T₀, T₁, T₂]/(F))₀`. -/
def toGradingZero : R →+* grading F hF 0 where
  toFun a := ⟨Ideal.Quotient.mk _ (C a),
    Stacks.HomogeneousIdeal.mk_mem_quotientGrading _
      (by rw [mem_homogeneousSubmodule]; exact isHomogeneous_C _ _)⟩
  map_one' := Subtype.ext
    (show Ideal.Quotient.mk (equationIdeal F hF).toIdeal (C 1) = 1 by rw [map_one, map_one])
  map_mul' a b := Subtype.ext
    (show Ideal.Quotient.mk (equationIdeal F hF).toIdeal (C (a * b)) =
      Ideal.Quotient.mk _ (C a) * Ideal.Quotient.mk _ (C b) by rw [map_mul, map_mul])
  map_zero' := Subtype.ext
    (show Ideal.Quotient.mk (equationIdeal F hF).toIdeal (C 0) = 0 by rw [map_zero, map_zero])
  map_add' a b := Subtype.ext
    (show Ideal.Quotient.mk (equationIdeal F hF).toIdeal (C (a + b)) =
      Ideal.Quotient.mk _ (C a) + Ideal.Quotient.mk _ (C b) by rw [map_add, map_add])

/-- `toGradingZero F hF a` is the class of the constant polynomial `C a`. -/
@[simp]
theorem coe_toGradingZero (a : R) :
    (toGradingZero F hF a : MvPolynomial (Fin 3) R ⧸ (equationIdeal F hF).toIdeal) =
      Ideal.Quotient.mk _ (C a) := rfl

/-- The structure morphism of `V(F)`, through the degree-zero part of its homogeneous coordinate
ring. -/
theorem toSpec_eq :
    toSpec F hF = Proj.toSpecZero (grading F hF) ≫
      Spec.map (CommRingCat.ofHom (toGradingZero F hF)) := by
  have key : CommRingCat.ofHom ((GradedRing.projZeroRingHom'
      (homogeneousSubmodule (Fin 3) R)).comp (algebraMap R (MvPolynomial (Fin 3) R))) ≫
      CommRingCat.ofHom
        (Stacks.HomogeneousIdeal.quotientMk (equationIdeal F hF)).gradedZeroRingHom =
      CommRingCat.ofHom (toGradingZero F hF) := by
    ext a
    show Ideal.Quotient.mk _ (DirectSum.decompose (homogeneousSubmodule (Fin 3) R)
      (MvPolynomial.C a) 0 : MvPolynomial (Fin 3) R) = Ideal.Quotient.mk _ (MvPolynomial.C a)
    rw [DirectSum.decompose_of_mem_same _ (by
      rw [mem_homogeneousSubmodule]; exact isHomogeneous_C _ _)]
  unfold toSpec Stacks.AlgebraicGeometry.ProjPolyChart.projToSpecCoeff embedding
  rw [← Category.assoc, AlgebraicGeometry.Proj.map_toSpecZero, Category.assoc, ← Spec.map_comp]
  exact congrArg (fun φ => Proj.toSpecZero (grading F hF) ≫ Spec.map φ) key

end DegreeZero

/-! ### Homomorphisms of homogeneous coordinate rings -/

section CoordHom

variable {S : Type u} [CommRing S] {F : MvPolynomial (Fin 3) R} {d : ℕ} {hF : F.IsHomogeneous d}
  {G : MvPolynomial (Fin 3) S} {e : ℕ} {hG : G.IsHomogeneous e}

/-- The graded ring homomorphism `R[T]/(F) → S[T]/(G)` induced by a graded ring homomorphism
`σ : R[T] → S[T]` that sends `F` into `(G)`. -/
def coordHom (σ : homogeneousSubmodule (Fin 3) R →+*ᵍ homogeneousSubmodule (Fin 3) S)
    (hσ : σ F ∈ (equationIdeal G hG).toIdeal) : grading F hF →+*ᵍ grading G hG where
  __ := Ideal.quotientMap (equationIdeal G hG).toIdeal σ.toRingHom <| by
    change Ideal.span {F} ≤ _
    rw [Ideal.span_le, Set.singleton_subset_iff]
    exact hσ
  map_mem {_ x} hx := by
    obtain ⟨a, ha, rfl⟩ := (Stacks.HomogeneousIdeal.mem_quotientGrading_iff _ x).mp hx
    exact Stacks.HomogeneousIdeal.mk_mem_quotientGrading _ (σ.map_mem ha)

/-- `coordHom σ hσ` sends the class of `p` to the class of `σ p`. -/
theorem coordHom_mk (σ : homogeneousSubmodule (Fin 3) R →+*ᵍ homogeneousSubmodule (Fin 3) S)
    (hσ : σ F ∈ (equationIdeal G hG).toIdeal) (p : MvPolynomial (Fin 3) R) :
    coordHom σ hσ (Ideal.Quotient.mk (equationIdeal F hF).toIdeal p) =
      Ideal.Quotient.mk (equationIdeal G hG).toIdeal (σ p) := rfl

/-- If `σ` sends each constant `a` to the constant `φ a`, then in degree zero `coordHom σ hσ` is
`φ`. -/
theorem gradedZeroRingHom_coordHom_comp
    (σ : homogeneousSubmodule (Fin 3) R →+*ᵍ homogeneousSubmodule (Fin 3) S)
    (hσ : σ F ∈ (equationIdeal G hG).toIdeal) (φ : R →+* S)
    (hφ : ∀ a, σ (MvPolynomial.C a) = MvPolynomial.C (φ a)) :
    (coordHom σ hσ).gradedZeroRingHom.comp (toGradingZero F hF) =
      (toGradingZero G hG).comp φ :=
  RingHom.ext fun a => Subtype.ext <| by
    show Ideal.Quotient.mk _ (σ (MvPolynomial.C a)) = Ideal.Quotient.mk _ (MvPolynomial.C (φ a))
    rw [hφ]

/-- A homomorphism of homogeneous coordinate rings lying over `φ` in degree zero induces a
morphism of plane curves over `Spec S ⟶ Spec R`. -/
theorem map_coordHom_toSpec
    (σ : homogeneousSubmodule (Fin 3) R →+*ᵍ homogeneousSubmodule (Fin 3) S)
    (hσ : σ F ∈ (equationIdeal G hG).toIdeal) (φ : R →+* S)
    (hφ : ∀ a, σ (MvPolynomial.C a) = MvPolynomial.C (φ a))
    (hirr : HomogeneousIdeal.irrelevant (grading G hG) ≤
      (HomogeneousIdeal.irrelevant (grading F hF)).map (coordHom σ hσ)) :
    Proj.map (coordHom σ hσ) hirr ≫ toSpec F hF =
      toSpec G hG ≫ Spec.map (CommRingCat.ofHom φ) := by
  rw [toSpec_eq, toSpec_eq, Proj.map_toSpecZero_assoc, Category.assoc, ← Spec.map_comp,
    ← Spec.map_comp, ← CommRingCat.ofHom_comp, ← CommRingCat.ofHom_comp,
    gradedZeroRingHom_coordHom_comp σ hσ φ hφ]

end CoordHom

/-- A graded ring homomorphism with a right inverse satisfies the hypothesis of `Proj.map`. -/
private theorem irrelevant_le_map_of_comp_eq_id {A B σ τ : Type u} [CommRing A] [SetLike σ A]
    [AddSubgroupClass σ A] [CommRing B] [SetLike τ B] [AddSubgroupClass τ B] {𝒜 : ℕ → σ}
    {ℬ : ℕ → τ} [GradedRing 𝒜] [GradedRing ℬ] (f : 𝒜 →+*ᵍ ℬ) (g : ℬ →+*ᵍ 𝒜)
    (h : f.comp g = GradedRingHom.id ℬ) :
    HomogeneousIdeal.irrelevant ℬ ≤ (HomogeneousIdeal.irrelevant 𝒜).map f :=
  Proj.irrelevant_le_map_of_surjective _ fun x =>
    ⟨g x, congrArg (fun f => GradedRingHom.toRingHom f x) h⟩

/-! ### Change of coefficients -/

section Map

variable {S : Type u} [CommRing S] (F : MvPolynomial (Fin 3) R) {d : ℕ} (hF : F.IsHomogeneous d)
  (φ : R →+* S)

/-- `MvPolynomial.map φ` sends `F` into the ideal of `φ F`. -/
theorem map_mem_equationIdeal :
    Stacks.ProjectiveCohomology.polyGradedMap (Fin 3) φ F ∈
      (equationIdeal (MvPolynomial.map φ F) (hF.map φ)).toIdeal :=
  Ideal.subset_span rfl

/-- The change of coefficients `R[T]/(F) → S[T]/(φ F)` along `φ : R →+* S`. -/
def mapHom : grading F hF →+*ᵍ grading (MvPolynomial.map φ F) (hF.map φ) :=
  coordHom (Stacks.ProjectiveCohomology.polyGradedMap (Fin 3) φ) (map_mem_equationIdeal F hF φ)

/-- The irrelevant ideal of `S[T]/(φ F)` lies in the ideal generated by the image of the
irrelevant ideal of `R[T]/(F)`. -/
theorem irrelevant_le_map_mapHom :
    HomogeneousIdeal.irrelevant (grading (MvPolynomial.map φ F) (hF.map φ)) ≤
      (HomogeneousIdeal.irrelevant (grading F hF)).map (mapHom F hF φ) := by
  refine (HomogeneousIdeal.irrelevant_le _).2 fun i hi x hx => ?_
  obtain ⟨q, hq, rfl⟩ := (Stacks.HomogeneousIdeal.mem_quotientGrading_iff _ x).mp hx
  have hq' : q.IsHomogeneous i := (mem_homogeneousSubmodule i q).1 hq
  rw [← q.support_sum_monomial_coeff, map_sum]
  refine Ideal.sum_mem _ fun m hm => ?_
  have hdeg : (monomial m (1 : R)).IsHomogeneous i := by
    refine isHomogeneous_monomial 1 ?_
    by_contra hne
    exact (MvPolynomial.mem_support_iff.mp hm) (hq'.coeff_eq_zero hne)
  have hmem : Ideal.Quotient.mk (equationIdeal F hF).toIdeal (monomial m 1) ∈
      (HomogeneousIdeal.irrelevant (grading F hF)).toIdeal :=
    HomogeneousIdeal.mem_irrelevant_of_mem _ hi
      (Stacks.HomogeneousIdeal.mk_mem_quotientGrading _ ((mem_homogeneousSubmodule i _).2 hdeg))
  have h : Ideal.Quotient.mk (equationIdeal (MvPolynomial.map φ F) (hF.map φ)).toIdeal
      (monomial m (q.coeff m)) =
      Ideal.Quotient.mk _ (MvPolynomial.C (q.coeff m)) *
        mapHom F hF φ (Ideal.Quotient.mk (equationIdeal F hF).toIdeal (monomial m 1)) := by
    show _ = _ * Ideal.Quotient.mk _ (MvPolynomial.map φ (monomial m 1))
    rw [← map_mul, MvPolynomial.map_monomial, map_one, C_mul_monomial, mul_one]
  rw [h]
  exact Ideal.mul_mem_left _ _ (Ideal.mem_map_of_mem _ hmem)

/-- The morphism `V(φ F) ⟶ V(F)` induced by the change of coefficients along `φ : R →+* S`. -/
def mapMap : scheme (MvPolynomial.map φ F) (hF.map φ) ⟶ scheme F hF :=
  Proj.map (mapHom F hF φ) (irrelevant_le_map_mapHom F hF φ)

/-- `mapMap F hF φ` lies over `Spec S ⟶ Spec R`. -/
theorem mapMap_toSpec :
    mapMap F hF φ ≫ toSpec F hF =
      toSpec (MvPolynomial.map φ F) (hF.map φ) ≫ Spec.map (CommRingCat.ofHom φ) :=
  map_coordHom_toSpec _ _ φ (fun a => MvPolynomial.map_C φ a) _

/-- Each graded piece of `S[T]/(G)` is stable under multiplication by scalars of `S`. -/
theorem smul_mem_grading {G : MvPolynomial (Fin 3) S} {e : ℕ} (hG : G.IsHomogeneous e) (c : S)
    {i : ℕ} {x : MvPolynomial (Fin 3) S ⧸ (equationIdeal G hG).toIdeal}
    (hx : x ∈ grading G hG i) : c • x ∈ grading G hG i := by
  obtain ⟨q, hq, rfl⟩ := (Stacks.HomogeneousIdeal.mem_quotientGrading_iff _ x).mp hx
  rw [← Ideal.Quotient.mkₐ_eq_mk S, ← map_smul]
  exact Stacks.HomogeneousIdeal.mk_mem_quotientGrading _ (Submodule.smul_mem _ c hq)

end Map

/-! ### The grading by submodules -/

section ModuleGrading

variable (F : MvPolynomial (Fin 3) R) {d : ℕ} (hF : F.IsHomogeneous d)

/-- The grading by total degree of `R[T]/(F)`, by `R`-submodules. -/
abbrev moduleGrading : ℕ → Submodule R (MvPolynomial (Fin 3) R ⧸ (equationIdeal F hF).toIdeal) :=
  Stacks.RingTheory.HomogeneousQuotient.quotientGrading (homogeneousSubmodule (Fin 3) R)
    (equationIdeal F hF)

/-- The graded pieces of `moduleGrading F hF` and of `grading F hF` have the same elements. -/
theorem mem_moduleGrading_iff {i : ℕ} (x : MvPolynomial (Fin 3) R ⧸ (equationIdeal F hF).toIdeal) :
    x ∈ moduleGrading F hF i ↔ x ∈ grading F hF i :=
  (Stacks.RingTheory.HomogeneousQuotient.mem_quotientGrading_iff _ _).trans
    (Stacks.HomogeneousIdeal.mem_quotientGrading_iff _ x).symm

/-- The identity, from the grading by additive subgroups to the grading by submodules. -/
def toModuleGrading : grading F hF →+*ᵍ moduleGrading F hF where
  __ := RingHom.id _
  map_mem {_ x} hx := (mem_moduleGrading_iff F hF x).2 hx

/-- The identity, from the grading by submodules to the grading by additive subgroups. -/
def fromModuleGrading : moduleGrading F hF →+*ᵍ grading F hF where
  __ := RingHom.id _
  map_mem {_ x} hx := (mem_moduleGrading_iff F hF x).1 hx

/-- The irrelevant ideal of `moduleGrading F hF` lies in the ideal generated by the image of the
irrelevant ideal of `grading F hF` under `toModuleGrading F hF`. -/
theorem irrelevant_le_map_toModuleGrading :
    HomogeneousIdeal.irrelevant (moduleGrading F hF) ≤
      (HomogeneousIdeal.irrelevant (grading F hF)).map (toModuleGrading F hF) :=
  Proj.irrelevant_le_map_of_surjective _ fun x => ⟨x, rfl⟩

/-- The irrelevant ideal of `grading F hF` lies in the ideal generated by the image of the
irrelevant ideal of `moduleGrading F hF` under `fromModuleGrading F hF`. -/
theorem irrelevant_le_map_fromModuleGrading :
    HomogeneousIdeal.irrelevant (grading F hF) ≤
      (HomogeneousIdeal.irrelevant (moduleGrading F hF)).map (fromModuleGrading F hF) :=
  Proj.irrelevant_le_map_of_surjective _ fun x => ⟨x, rfl⟩

/-- `toModuleGrading F hF` is a left inverse of `fromModuleGrading F hF`. -/
theorem toModuleGrading_comp_fromModuleGrading :
    (toModuleGrading F hF).comp (fromModuleGrading F hF) = GradedRingHom.id (moduleGrading F hF) :=
  GradedRingHom.ext fun _ => rfl

/-- `fromModuleGrading F hF` is a left inverse of `toModuleGrading F hF`. -/
theorem fromModuleGrading_comp_toModuleGrading :
    (fromModuleGrading F hF).comp (toModuleGrading F hF) = GradedRingHom.id (grading F hF) :=
  GradedRingHom.ext fun _ => rfl

/-- `Proj` of the two gradings of `R[T]/(F)` are the same scheme. -/
def moduleGradingIso : AlgebraicGeometry.Proj (moduleGrading F hF) ≅ scheme F hF where
  hom := Proj.map (toModuleGrading F hF) (irrelevant_le_map_toModuleGrading F hF)
  inv := Proj.map (fromModuleGrading F hF) (irrelevant_le_map_fromModuleGrading F hF)
  hom_inv_id :=
    (Proj.map_comp (fromModuleGrading F hF) (toModuleGrading F hF) _ _).symm.trans
      ((Proj.map_congr (toModuleGrading_comp_fromModuleGrading F hF) _ (by simp)).trans
        Proj.map_id)
  inv_hom_id :=
    (Proj.map_comp (toModuleGrading F hF) (fromModuleGrading F hF) _ _).symm.trans
      ((Proj.map_congr (fromModuleGrading_comp_toModuleGrading F hF) _ (by simp)).trans
        Proj.map_id)

/-- Under `moduleGradingIso F hF`, the structure morphism of `V(F)` is the structure morphism of
`Proj (moduleGrading F hF)` over `Spec R` through its degree-zero part. -/
theorem moduleGradingIso_hom_toSpec :
    (moduleGradingIso F hF).hom ≫ toSpec F hF =
      Proj.toSpecZero (moduleGrading F hF) ≫
        Spec.map (CommRingCat.ofHom (algebraMap R ↥(moduleGrading F hF 0))) := by
  show Proj.map (toModuleGrading F hF) (irrelevant_le_map_toModuleGrading F hF) ≫ _ = _
  rw [toSpec_eq, Proj.map_toSpecZero_assoc, ← Spec.map_comp, ← CommRingCat.ofHom_comp]
  congr 2

end ModuleGrading

/-! ### Base change of the homogeneous coordinate ring -/

section BaseChange

variable (F : MvPolynomial (Fin 3) R) {d : ℕ} (hF : F.IsHomogeneous d)
  (S : Type u) [CommRing S] [Algebra R S]

/-- The ideal of `φ F` is the extension of `(F)` along `R[T] → S ⊗[R] R[T] ≅ S[T]`. -/
theorem equationIdeal_map_eq :
    (equationIdeal (MvPolynomial.map (algebraMap R S) F) (hF.map _)).toIdeal =
      Ideal.map (MvPolynomial.algebraTensorAlgEquiv R S)
        (Ideal.map (Algebra.TensorProduct.includeRight :
            MvPolynomial (Fin 3) R →ₐ[R] S ⊗[R] MvPolynomial (Fin 3) R)
          (equationIdeal F hF).toIdeal) := by
  show Ideal.span {MvPolynomial.map (algebraMap R S) F} =
    Ideal.map _ (Ideal.map _ (Ideal.span {F}))
  rw [Ideal.map_span, Ideal.map_span, Set.image_singleton, Set.image_singleton]
  congr 2
  show _ = MvPolynomial.algebraTensorAlgEquiv R S (1 ⊗ₜ[R] F)
  rw [MvPolynomial.algebraTensorAlgEquiv_tmul, one_smul]

/-- `S ⊗[R] R[T]/(F) ≅ S[T]/(φ F)`. -/
def baseChangeEquiv :
    S ⊗[R] (MvPolynomial (Fin 3) R ⧸ (equationIdeal F hF).toIdeal) ≃ₐ[S]
      (MvPolynomial (Fin 3) S ⧸
        (equationIdeal (MvPolynomial.map (algebraMap R S) F) (hF.map _)).toIdeal) :=
  (Algebra.TensorProduct.tensorQuotientEquiv S _ S (equationIdeal F hF).toIdeal).trans
    (Ideal.quotientEquivAlg _ _ (MvPolynomial.algebraTensorAlgEquiv R S)
      (equationIdeal_map_eq F hF S))

/-- `baseChangeEquiv F hF S` sends `s ⊗ [p]` to the class of `C s * φ p`, where `φ` is
`algebraMap R S`. -/
@[simp]
theorem baseChangeEquiv_tmul (s : S) (p : MvPolynomial (Fin 3) R) :
    baseChangeEquiv F hF S (s ⊗ₜ[R] Ideal.Quotient.mk (equationIdeal F hF).toIdeal p) =
      Ideal.Quotient.mk _ (MvPolynomial.C s * MvPolynomial.map (algebraMap R S) p) := by
  show Ideal.quotientEquivAlg _ _ (MvPolynomial.algebraTensorAlgEquiv R S)
      (equationIdeal_map_eq F hF S)
      (Algebra.TensorProduct.tensorQuotientEquiv S (MvPolynomial (Fin 3) R) S
        (equationIdeal F hF).toIdeal
          (s ⊗ₜ[R] Ideal.Quotient.mk (equationIdeal F hF).toIdeal p)) = _
  rw [Algebra.TensorProduct.tensorQuotientEquiv_apply_tmul]
  show Ideal.Quotient.mk _ (MvPolynomial.algebraTensorAlgEquiv R S (s ⊗ₜ[R] p)) = _
  rw [MvPolynomial.algebraTensorAlgEquiv_tmul, smul_eq_C_mul]

/-- `baseChangeEquiv` as a homomorphism of graded rings. -/
def baseChangeGradedHom :
    Stacks.ProjBaseChange.grading (moduleGrading F hF) S →+*ᵍ
      grading (MvPolynomial.map (algebraMap R S) F) (hF.map _) where
  __ := (baseChangeEquiv F hF S).toRingEquiv.toRingHom
  map_mem := by
    intro i x hx
    have hx' : x ∈ Submodule.span S
        ((moduleGrading F hF i).map ((TensorProduct.mk R S _) 1)) := by
      rw [← Submodule.baseChange_eq_span]; exact hx
    refine Submodule.span_induction (p := fun x _ => baseChangeEquiv F hF S x ∈
      grading (MvPolynomial.map (algebraMap R S) F) (hF.map _) i) ?_ ?_ ?_ ?_ hx'
    · rintro _ ⟨b, hb, rfl⟩
      obtain ⟨p, hp, rfl⟩ :=
        (Stacks.RingTheory.HomogeneousQuotient.mem_quotientGrading_iff _ _).1 hb
      have h : baseChangeEquiv F hF S ((TensorProduct.mk R S _) 1
          (Ideal.Quotient.mk (equationIdeal F hF).toIdeal p)) =
          Ideal.Quotient.mk _ (MvPolynomial.map (algebraMap R S) p) := by
        change baseChangeEquiv F hF S (1 ⊗ₜ[R] Ideal.Quotient.mk (equationIdeal F hF).toIdeal p) =
          _
        rw [baseChangeEquiv_tmul, map_one, one_mul]
      rw [h]
      exact Stacks.HomogeneousIdeal.mk_mem_quotientGrading _
        ((mem_homogeneousSubmodule i _).2 (((mem_homogeneousSubmodule i p).1 hp).map _))
    · rw [map_zero]
      exact zero_mem _
    · intro x y _ _ hx hy
      rw [map_add]
      exact AddSubgroup.add_mem _ hx hy
    · intro c x _ hx
      rw [map_smul]
      exact smul_mem_grading _ c hx

/-- The inverse of `baseChangeGradedHom`, as a homomorphism of graded rings. -/
def baseChangeGradedInv :
    grading (MvPolynomial.map (algebraMap R S) F) (hF.map _) →+*ᵍ
      Stacks.ProjBaseChange.grading (moduleGrading F hF) S where
  __ := (baseChangeEquiv F hF S).symm.toRingEquiv.toRingHom
  map_mem := by
    classical
    intro i x hx
    obtain ⟨q, hq, rfl⟩ := (Stacks.HomogeneousIdeal.mem_quotientGrading_iff _ x).mp hx
    have hq' : q.IsHomogeneous i := (mem_homogeneousSubmodule i q).1 hq
    set z : S ⊗[R] (MvPolynomial (Fin 3) R ⧸ (equationIdeal F hF).toIdeal) :=
      ∑ m ∈ q.support, q.coeff m ⊗ₜ[R]
        Ideal.Quotient.mk (equationIdeal F hF).toIdeal (monomial m 1) with hzdef
    have hz : baseChangeEquiv F hF S z = Ideal.Quotient.mk _ q := by
      rw [hzdef, map_sum]
      simp only [baseChangeEquiv_tmul, MvPolynomial.map_monomial, map_one, C_mul_monomial,
        mul_one]
      rw [← map_sum, q.support_sum_monomial_coeff]
    have hmem : z ∈ Stacks.ProjBaseChange.grading (moduleGrading F hF) S i := by
      refine Submodule.sum_mem _ fun m hm => Submodule.tmul_mem_baseChange_of_mem _
        (Stacks.RingTheory.HomogeneousQuotient.quotientGrading_mk_mem _ _
          ((mem_homogeneousSubmodule i _).2 (isHomogeneous_monomial 1 ?_)))
      by_contra hne
      exact (MvPolynomial.mem_support_iff.mp hm) (hq'.coeff_eq_zero hne)
    change (baseChangeEquiv F hF S).symm (Ideal.Quotient.mk _ q) ∈ _
    rw [← hz, AlgEquiv.symm_apply_apply]
    exact hmem

/-- `baseChangeGradedInv F hF S` is a left inverse of `baseChangeGradedHom F hF S`. -/
theorem baseChangeGradedInv_comp_hom :
    (baseChangeGradedInv F hF S).comp (baseChangeGradedHom F hF S) = GradedRingHom.id _ :=
  GradedRingHom.ext fun x => (baseChangeEquiv F hF S).symm_apply_apply x

/-- `baseChangeGradedHom F hF S` is a left inverse of `baseChangeGradedInv F hF S`. -/
theorem baseChangeGradedHom_comp_inv :
    (baseChangeGradedHom F hF S).comp (baseChangeGradedInv F hF S) = GradedRingHom.id _ :=
  GradedRingHom.ext fun x => (baseChangeEquiv F hF S).apply_symm_apply x

/-- The change of coefficients along `algebraMap R S` is the inclusion `a ↦ 1 ⊗ a` into the base
change followed by `baseChangeGradedHom`. -/
theorem mapHom_comp_fromModuleGrading_eq :
    (mapHom F hF (algebraMap R S)).comp (fromModuleGrading F hF) =
      (baseChangeGradedHom F hF S).comp
        (Stacks.ProjBaseChange.includeRight (moduleGrading F hF) S) :=
  GradedRingHom.ext fun x => by
    obtain ⟨p, rfl⟩ := Ideal.Quotient.mk_surjective x
    show Ideal.Quotient.mk _ (MvPolynomial.map (algebraMap R S) p) =
      baseChangeEquiv F hF S (1 ⊗ₜ[R] Ideal.Quotient.mk (equationIdeal F hF).toIdeal p)
    rw [baseChangeEquiv_tmul, map_one, one_mul]

/-- The irrelevant ideal of `S[T]/(φ F)` lies in the ideal generated by the image of the
irrelevant ideal of `S ⊗[R] R[T]/(F)` under `baseChangeGradedHom F hF S`. -/
theorem irrelevant_le_map_baseChangeGradedHom :
    HomogeneousIdeal.irrelevant (grading (MvPolynomial.map (algebraMap R S) F) (hF.map _)) ≤
      (HomogeneousIdeal.irrelevant (Stacks.ProjBaseChange.grading (moduleGrading F hF) S)).map
        (baseChangeGradedHom F hF S) :=
  irrelevant_le_map_of_comp_eq_id _ (baseChangeGradedInv F hF S)
    (baseChangeGradedHom_comp_inv F hF S)

/-- The irrelevant ideal of `S ⊗[R] R[T]/(F)` lies in the ideal generated by the image of the
irrelevant ideal of `S[T]/(φ F)` under `baseChangeGradedInv F hF S`. -/
theorem irrelevant_le_map_baseChangeGradedInv :
    HomogeneousIdeal.irrelevant (Stacks.ProjBaseChange.grading (moduleGrading F hF) S) ≤
      (HomogeneousIdeal.irrelevant
        (grading (MvPolynomial.map (algebraMap R S) F) (hF.map _))).map
        (baseChangeGradedInv F hF S) :=
  irrelevant_le_map_of_comp_eq_id _ (baseChangeGradedHom F hF S)
    (baseChangeGradedInv_comp_hom F hF S)

/-- `isPullback_mapMap` for the structure map of an `R`-algebra `S`. -/
theorem isPullback_mapMap_algebraMap :
    IsPullback (mapMap F hF (algebraMap R S))
      (toSpec (MvPolynomial.map (algebraMap R S) F) (hF.map _))
      (toSpec F hF) (Spec.map (CommRingCat.ofHom (algebraMap R S))) := by
  have he := irrelevant_le_map_baseChangeGradedHom F hF S
  have he' := irrelevant_le_map_baseChangeGradedInv F hF S
  have hf := HomogeneousIdeal.irrelevant_le_map_comp (irrelevant_le_map_fromModuleGrading F hF)
    (irrelevant_le_map_mapHom F hF (algebraMap R S))
  have H := Stacks.ProjBaseChange.isPullback_map_of_baseChange (moduleGrading F hF) S hf he he'
    (baseChangeGradedInv_comp_hom F hF S) (baseChangeGradedHom_comp_inv F hF S)
    (mapHom_comp_fromModuleGrading_eq F hF S)
  refine H.of_iso (Iso.refl _) (moduleGradingIso F hF) (Iso.refl _) (Iso.refl _) ?_ ?_ ?_ ?_
  · rw [Proj.map_comp (fromModuleGrading F hF) (mapHom F hF (algebraMap R S))
      (irrelevant_le_map_fromModuleGrading F hF) (irrelevant_le_map_mapHom F hF (algebraMap R S)),
      Category.assoc]
    show mapMap F hF (algebraMap R S) ≫ (moduleGradingIso F hF).inv ≫
      (moduleGradingIso F hF).hom = _
    rw [Iso.inv_hom_id, Category.comp_id]
    exact (Category.id_comp _).symm
  · rw [Iso.refl_hom, Category.comp_id]
    refine Eq.trans ?_ (Category.id_comp _).symm
    rw [toSpec_eq]
    have hring : (baseChangeGradedHom F hF S).gradedZeroRingHom.comp
        (algebraMap S ↥(Stacks.ProjBaseChange.grading (moduleGrading F hF) S 0)) =
        toGradingZero (MvPolynomial.map (algebraMap R S) F) (hF.map _) := by
      refine RingHom.ext fun s => Subtype.ext ?_
      have h := baseChangeEquiv_tmul F hF S s 1
      rw [map_one, map_one, mul_one] at h
      exact h
    rw [Proj.map_toSpecZero_assoc, ← Spec.map_comp, ← CommRingCat.ofHom_comp, hring]
  · rw [Iso.refl_hom, Category.comp_id, moduleGradingIso_hom_toSpec]
  · simp

end BaseChange

/-- **The plane curve `V(F)` commutes with base change.** For a ring map `φ : R →+* S`, the
square formed by `mapMap F hF φ : V(φ F) ⟶ V(F)`, the two structure morphisms and
`Spec S ⟶ Spec R` is cartesian. -/
theorem isPullback_mapMap {S : Type u} [CommRing S] (F : MvPolynomial (Fin 3) R) {d : ℕ}
    (hF : F.IsHomogeneous d) (φ : R →+* S) :
    IsPullback (mapMap F hF φ) (toSpec (MvPolynomial.map φ F) (hF.map φ)) (toSpec F hF)
      (Spec.map (CommRingCat.ofHom φ)) := by
  let _ := φ.toAlgebra
  exact isPullback_mapMap_algebraMap F hF S

/-! ### Equal equations -/

/-- Equal equations cut out the same plane curve. -/
def schemeCongr {F G : MvPolynomial (Fin 3) R} {d e : ℕ} (hF : F.IsHomogeneous d)
    (hG : G.IsHomogeneous e) (h : F = G) : scheme F hF ≅ scheme G hG :=
  eqToIso (by subst h; rfl)

/-- `schemeCongr hF hG h` commutes with the structure morphisms to `Spec R`. -/
theorem schemeCongr_hom_toSpec {F G : MvPolynomial (Fin 3) R} {d e : ℕ} (hF : F.IsHomogeneous d)
    (hG : G.IsHomogeneous e) (h : F = G) :
    (schemeCongr hF hG h).hom ≫ toSpec G hG = toSpec F hF := by
  subst h
  exact Category.id_comp _

/-! ### Linear substitutions -/

/-- The graded endomorphism of `R[T₀, T₁, T₂]` substituting the linear forms `v j` for the
coordinates `Tⱼ`. -/
def linearSubst (v : Fin 3 → MvPolynomial (Fin 3) R) (hv : ∀ j, (v j).IsHomogeneous 1) :
    homogeneousSubmodule (Fin 3) R →+*ᵍ homogeneousSubmodule (Fin 3) R where
  __ := (aeval v).toRingHom
  map_mem {n p} hp := by
    have h := ((mem_homogeneousSubmodule n p).1 hp).aeval (n := 1) (τ := Fin 3) v hv
    rw [one_mul] at h
    exact (mem_homogeneousSubmodule _ _).2 h

/-- `linearSubst v hv` evaluates a polynomial at the linear forms `v`. -/
theorem linearSubst_apply (v : Fin 3 → MvPolynomial (Fin 3) R) (hv : ∀ j, (v j).IsHomogeneous 1)
    (p : MvPolynomial (Fin 3) R) : linearSubst v hv p = aeval v p := rfl

/-- `linearSubst v hv` fixes the constants. -/
theorem linearSubst_C (v : Fin 3 → MvPolynomial (Fin 3) R) (hv : ∀ j, (v j).IsHomogeneous 1)
    (a : R) : linearSubst v hv (C a) = C a := by
  rw [linearSubst_apply, aeval_C, algebraMap_eq]

/-- Two linear substitutions compose to the identity as soon as they do on the coordinates. -/
theorem linearSubst_comp_eq_id (v w : Fin 3 → MvPolynomial (Fin 3) R)
    (hv : ∀ j, (v j).IsHomogeneous 1) (hw : ∀ j, (w j).IsHomogeneous 1)
    (h : ∀ j, aeval v (w j) = X j) :
    (linearSubst v hv).comp (linearSubst w hw) = GradedRingHom.id _ := by
  have hcomp : (aeval v).comp (aeval w) = AlgHom.id R (MvPolynomial (Fin 3) R) :=
    MvPolynomial.algHom_ext fun j => by rw [AlgHom.comp_apply, aeval_X, h j]; rfl
  exact GradedRingHom.ext fun p => congrArg (fun f : MvPolynomial (Fin 3) R →ₐ[R] _ => f p) hcomp

/-! ### Graded automorphisms of the polynomial ring -/

section Change

variable {F G : MvPolynomial (Fin 3) R} {d e : ℕ} {hF : F.IsHomogeneous d}
  {hG : G.IsHomogeneous e}

/-- If `τ ∘ σ` is the identity of `R[T]`, then `coordHom τ hτ ∘ coordHom σ hσ` is the identity of
`R[T]/(F)`. -/
theorem coordHom_comp_coordHom
    (σ τ : homogeneousSubmodule (Fin 3) R →+*ᵍ homogeneousSubmodule (Fin 3) R)
    (hστ : τ.comp σ = GradedRingHom.id _) (hσ : σ F ∈ (equationIdeal G hG).toIdeal)
    (hτ : τ G ∈ (equationIdeal F hF).toIdeal) :
    (coordHom τ hτ).comp (coordHom σ hσ) = GradedRingHom.id (grading F hF) :=
  GradedRingHom.ext fun x => by
    obtain ⟨p, rfl⟩ := Ideal.Quotient.mk_surjective x
    show Ideal.Quotient.mk _ (τ (σ p)) = Ideal.Quotient.mk _ p
    exact congrArg (Ideal.Quotient.mk _) (congrArg (fun f => GradedRingHom.toRingHom f p) hστ)

/-- If `σ` has a right inverse `τ` with `τ G ∈ (F)`, then the irrelevant ideal of `R[T]/(G)` lies
in the ideal generated by the image of the irrelevant ideal of `R[T]/(F)` under `coordHom σ hσ`. -/
theorem irrelevant_le_map_coordHom
    (σ τ : homogeneousSubmodule (Fin 3) R →+*ᵍ homogeneousSubmodule (Fin 3) R)
    (hτσ : σ.comp τ = GradedRingHom.id _) (hσ : σ F ∈ (equationIdeal G hG).toIdeal)
    (hτ : τ G ∈ (equationIdeal F hF).toIdeal) :
    HomogeneousIdeal.irrelevant (grading G hG) ≤
      (HomogeneousIdeal.irrelevant (grading F hF)).map (coordHom σ hσ) :=
  irrelevant_le_map_of_comp_eq_id _ (coordHom τ hτ) (coordHom_comp_coordHom τ σ hτσ hτ hσ)

/-- The morphism `V(G) ⟶ V(F)` induced by a graded automorphism `σ` of `R[T]`, with inverse
`τ`, such that `σ F ∈ (G)` and `τ G ∈ (F)`. -/
def changeMap (σ τ : homogeneousSubmodule (Fin 3) R →+*ᵍ homogeneousSubmodule (Fin 3) R)
    (hτσ : σ.comp τ = GradedRingHom.id _) (hσ : σ F ∈ (equationIdeal G hG).toIdeal)
    (hτ : τ G ∈ (equationIdeal F hF).toIdeal) : scheme G hG ⟶ scheme F hF :=
  Proj.map (coordHom σ hσ) (irrelevant_le_map_coordHom σ τ hτσ hσ hτ)

/-- The morphism induced by a graded automorphism is an isomorphism. -/
theorem isIso_changeMap (σ τ : homogeneousSubmodule (Fin 3) R →+*ᵍ homogeneousSubmodule (Fin 3) R)
    (hστ : τ.comp σ = GradedRingHom.id _) (hτσ : σ.comp τ = GradedRingHom.id _)
    (hσ : σ F ∈ (equationIdeal G hG).toIdeal) (hτ : τ G ∈ (equationIdeal F hF).toIdeal) :
    IsIso (changeMap σ τ hτσ hσ hτ) :=
  Proj.isIso_map _ (irrelevant_le_map_coordHom τ σ hστ hτ hσ)
    (coordHom_comp_coordHom σ τ hστ hσ hτ) (coordHom_comp_coordHom τ σ hτσ hτ hσ)

/-- The morphism induced by an `R`-linear graded automorphism lies over `Spec R`. -/
theorem changeMap_toSpec
    (σ τ : homogeneousSubmodule (Fin 3) R →+*ᵍ homogeneousSubmodule (Fin 3) R)
    (hτσ : σ.comp τ = GradedRingHom.id _) (hσ : σ F ∈ (equationIdeal G hG).toIdeal)
    (hτ : τ G ∈ (equationIdeal F hF).toIdeal)
    (hC : ∀ a, σ (MvPolynomial.C a) = MvPolynomial.C a) :
    changeMap σ τ hτσ hσ hτ ≫ toSpec F hF = toSpec G hG := by
  rw [changeMap, map_coordHom_toSpec σ hσ (RingHom.id R) hC, CommRingCat.ofHom_id, Spec.map_id,
    Category.comp_id]

end Change

end Stacks.Models.PlaneCurveModel

end
