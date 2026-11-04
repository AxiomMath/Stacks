module

public import StacksFrontier.AlgebraicGeometry.WeilCohomology.Concrete.ProdTensorBridge
public import StacksFrontier.AlgebraicGeometry.WeilCohomology.Concrete.RealizationGraph
public import StacksFrontier.AlgebraicGeometry.WeilCohomology.Concrete.RealizationTensor
public import StacksFrontier.CategoryTheory.GradedObject.InvertibleLine
public import StacksFrontier.CategoryTheory.GradedObject.KoszulBraiding
public import StacksFrontier.CategoryTheory.GradedObject.KunnethIso
public import StacksFrontier.CategoryTheory.GradedObject.ModuleCatMonoidal
public import StacksFrontier.AlgebraicGeometry.Morphisms.Projective.AffineBase
public import StacksFrontier.AlgebraicGeometry.WeilCohomology.Correspondences.SmoothProjectiveComposition

/-!
# The realization of correspondences is a functor of symmetric monoidal categories

Let `W` be data (D0)–(D3) of Section 45.9 (Tag 0FHA) satisfying (A), (B) and (C), with coefficient
field `F` of characteristic zero, and let `G` be the functor of the proof of Stacks 0FHL on
correspondences of degree zero (`Stacks.WeilCohomology.WeilData.corrFunctor`). The source: "By
Lemma 0FHE we have that `G(Spec(k)) = H^*(Spec(k))` is canonically isomorphic to `F` as an
`F`-algebra. The Künneth axiom (B)(a) shows our functor is compatible with tensor products. Thus
our functor is a functor of symmetric monoidal categories." This file carries this out, for the
Koszul-signed symmetric structure on graded `F`-vector spaces (Stacks, Homology, Example 0FFX;
`CategoryTheory.GradedObject.koszulSymmetricCategory`):

* the tensorator is the Künneth isomorphism `H^*(X) ⊗ H^*(Y) ≅ H^*(X × Y)`,
  `a ⊗ b ↦ pr₁^*a ∪ pr₂^*b` (`WeilData.corrFunctorμIso`), natural by the tensor law
  `WeilData.corrMap_tensor`;
* the unit is `F ≅ H^*(Spec k)` (Stacks 0FHE, `WeilData.corrFunctorεIso`);
* the associativity, unit and commutativity constraints of correspondences are graphs of
  isomorphisms of schemes, which act by pullback (`WeilData.corrMap_graphCorr`), and the
  coherence identities become identities between pullbacks of exterior products; the
  commutativity constraint produces the Koszul sign by graded commutativity (D1).

## Main definitions

* `Stacks.WeilCohomology.WeilData.corrFunctorCoreMonoidal`, `corrFunctorMonoidal`,
  `corrFunctorBraided`.

## References

* [Stacks Project, Tag 0FHL](https://stacks.math.columbia.edu/tag/0FHL)
* [Stacks Project, Tag 0FHE](https://stacks.math.columbia.edu/tag/0FHE)
* [Stacks Project, Tag 0FFX](https://stacks.math.columbia.edu/tag/0FFX)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry Stacks.Chow MonoidalCategory
  CategoryTheory.GradedCategory

universe u w

namespace CategoryTheory.GradedObject.Monoidal

variable {R : Type w} [CommRing R] {M P : Type w} [AddCommGroup M] [Module R M] [AddCommGroup P]
  [Module R P] (𝒜 : ℤ → Submodule R M) (𝒞 : ℤ → Submodule R P) [DirectSum.Decomposition 𝒜]
  [DirectSum.Decomposition 𝒞] (φ : M →ₗ[R] P) (hφ : ∀ n x, x ∈ 𝒜 n → φ x ∈ 𝒞 n)
  (hbij : Function.Bijective φ)

include hφ hbij in
/-- A bijective linear map respecting gradings is bijective in each degree. -/
theorem bijective_restrict_of_bijective (n : ℤ) :
    Function.Bijective (φ.restrict (p := 𝒜 n) (q := 𝒞 n) (hφ n)) := by
  classical
  refine ⟨fun x y h ↦ Subtype.ext (hbij.1 (congrArg Subtype.val h)), fun c ↦ ?_⟩
  obtain ⟨m, hm⟩ := hbij.2 c
  refine ⟨DirectSum.decompose 𝒜 m n, Subtype.ext ?_⟩
  show φ (DirectSum.decompose 𝒜 m n) = c
  have hsum : φ m = ∑ i ∈ (DirectSum.decompose 𝒜 m).support, φ (DirectSum.decompose 𝒜 m i) := by
    conv_lhs => rw [← DirectSum.sum_support_decompose 𝒜 m]
    rw [map_sum]
  have hmem : φ m ∈ 𝒞 n := hm ▸ c.2
  have hc : (DirectSum.decompose 𝒞 (φ m) n : P) = φ m := DirectSum.decompose_of_mem_same 𝒞 hmem
  have key : (DirectSum.decompose 𝒞 (φ m) n : P) = φ (DirectSum.decompose 𝒜 m n) := by
    rw [hsum, DirectSum.decompose_sum, DFinsupp.finset_sum_apply,
      AddSubmonoidClass.coe_finset_sum]
    by_cases hn : n ∈ (DirectSum.decompose 𝒜 m).support
    · rw [Finset.sum_eq_single n (fun i _ hin ↦ by
        rw [DirectSum.decompose_of_mem_ne 𝒞 (hφ i _ (DirectSum.decompose 𝒜 m i).2) hin])
        (fun h ↦ absurd hn h),
        DirectSum.decompose_of_mem_same 𝒞 (hφ n _ (DirectSum.decompose 𝒜 m n).2)]
    · have h0 : DirectSum.decompose 𝒜 m n = 0 := DFinsupp.notMem_support_iff.1 hn
      rw [h0, ZeroMemClass.coe_zero, map_zero]
      exact Finset.sum_eq_zero fun i hi ↦ DirectSum.decompose_of_mem_ne 𝒞
        (hφ i _ (DirectSum.decompose 𝒜 m i).2) (fun h ↦ hn (h ▸ hi))
  rw [← key, hc, hm]

/-- **A bijective graded linear map is an isomorphism of graded modules.** -/
def gradedIsoOfBijective : gradedModule 𝒜 ≅ gradedModule 𝒞 :=
  GradedObject.isoMk _ _ fun n ↦ (LinearEquiv.ofBijective (φ.restrict (hφ n))
    (bijective_restrict_of_bijective 𝒜 𝒞 φ hφ hbij n)).toModuleIso

/-- The isomorphism `gradedIsoOfBijective` acts in each degree as `φ`. -/
theorem gradedIsoOfBijective_hom_apply (n : ℤ) (x : 𝒜 n) :
    (((gradedIsoOfBijective 𝒜 𝒞 φ hφ hbij).hom n).hom x : P) = φ x :=
  rfl

/-- Right whiskering on elements: `(φ ▷ Y)(x ⊗ y) = φ x ⊗ y`. -/
theorem whiskerRight_apply_ιTensorObj {X X' : GradedObject ℤ (ModuleCat.{w} R)} (φ : X ⟶ X')
    (Y : GradedObject ℤ (ModuleCat.{w} R)) (p q n : ℤ) (h : p + q = n) (x : X p) (y : Y q) :
    ((φ ▷ Y) n).hom ((ιTensorObj X Y p q n h).hom (x ⊗ₜ y)) =
      (ιTensorObj X' Y p q n h).hom ((φ p).hom x ⊗ₜ y) :=
  congrArg (fun ψ ↦ ψ.hom (x ⊗ₜ[R] y)) (ιTensorObj_whiskerRight φ Y p q n h)

/-- Left whiskering on elements: `(X ◁ φ)(x ⊗ y) = x ⊗ φ y`. -/
theorem whiskerLeft_apply_ιTensorObj (X : GradedObject ℤ (ModuleCat.{w} R))
    {Y Y' : GradedObject ℤ (ModuleCat.{w} R)} (φ : Y ⟶ Y') (p q n : ℤ) (h : p + q = n) (x : X p)
    (y : Y q) :
    ((X ◁ φ) n).hom ((ιTensorObj X Y p q n h).hom (x ⊗ₜ y)) =
      (ιTensorObj X Y' p q n h).hom (x ⊗ₜ (φ q).hom y) :=
  congrArg (fun ψ ↦ ψ.hom (x ⊗ₜ[R] y)) (ιTensorObj_whiskerLeft X φ p q n h)

/-- The inclusion of a summand of a threefold tensor product on elements. -/
theorem ιTensorObj₃'_apply (X₁ X₂ X₃ : GradedObject ℤ (ModuleCat.{w} R)) (p q r n : ℤ)
    (h : p + q + r = n) (x : X₁ p) (y : X₂ q) (z : X₃ r) :
    (ιTensorObj₃' X₁ X₂ X₃ p q r n h).hom ((x ⊗ₜ y) ⊗ₜ z) =
      (ιTensorObj (X₁ ⊗ X₂) X₃ (p + q) r n h).hom
        ((ιTensorObj X₁ X₂ p q (p + q) rfl).hom (x ⊗ₜ y) ⊗ₜ z) :=
  rfl

/-- Every element of the degree `0` part of the graded unit is a multiple of `1`. -/
private theorem exists_smul_unitOne (u : (𝟙_ (GradedObject ℤ (ModuleCat.{w} R))) 0) :
    ∃ c : R, c • unitOne = u :=
  ⟨(tensorUnit₀ (I := ℤ) (C := ModuleCat.{w} R)).hom.hom u, by
    rw [unitOne, ← map_smul, smul_eq_mul, mul_one, ← ModuleCat.comp_apply, Iso.hom_inv_id,
      ModuleCat.id_apply]⟩

/-- The graded unit is a subsingleton in every nonzero degree. -/
private theorem subsingleton_tensorUnit_apply {p : ℤ} (hp : p ≠ 0) :
    Subsingleton ((𝟙_ (GradedObject ℤ (ModuleCat.{w} R))) p) :=
  ModuleCat.subsingleton_of_isZero
    (isInitialTensorUnitApply (I := ℤ) (C := ModuleCat.{w} R) p hp).isZero

end CategoryTheory.GradedObject.Monoidal

namespace Stacks.WeilCohomology.WeilData

open SmoothProjectiveScheme GradedObject.Monoidal

variable {k : Type u} [Field k] {F : Type w} [Field F] [CharZero F] {W : WeilData k F}
  (hA : W.PoincareDuality) (hB : W.Kunneth) (hC : W.CycleClassAxiom hA.perfectPairing)

/-! ### The tensorator and the unit -/

/-- **The tensorator: the Künneth isomorphism** `H^*(X) ⊗ H^*(Y) ≅ H^*(X × Y)`,
`a ⊗ b ↦ pr₁^*a ∪ pr₂^*b` (axiom (B)(a)). -/
def corrFunctorμIso (X Y : DegreeZero ℚ (CorrespondenceCategory k)) :
    (corrFunctor hA hB hC).obj X ⊗ (corrFunctor hA hB hC).obj Y ≅
      (corrFunctor hA hB hC).obj (X ⊗ Y) :=
  kunnethIso (W.grade X.as) (W.grade Y.as) (W.grade (prod X.as Y.as)) (W.kunnethMap X.as Y.as)
    (fun p q a b ha hb ↦ SetLike.GradedMul.mul_mem (W.pull_grade _ p a ha)
      (W.pull_grade _ q b hb)) (hB.kunnethIsomorphism X.as Y.as)

/-- The Künneth isomorphism sends `a ⊗ b` to the exterior product `pr₁^*a ∪ pr₂^*b`. -/
theorem corrFunctorμIso_hom_apply (X Y : DegreeZero ℚ (CorrespondenceCategory k)) (p q n : ℤ)
    (h : p + q = n) (a : (corrFunctor hA hB hC).obj X p) (b : (corrFunctor hA hB hC).obj Y q) :
    ((corrFunctorμIso hA hB hC X Y).hom n).hom
        ((ιTensorObj ((corrFunctor hA hB hC).obj X) ((corrFunctor hA hB hC).obj Y) p q n h).hom
          (a ⊗ₜ b)) =
      (⟨W.pull (fst X.as Y.as) a.1 * W.pull (snd X.as Y.as) b.1,
        h ▸ (SetLike.GradedMul.mul_mem (W.pull_grade (fst X.as Y.as) p _ a.2)
          (W.pull_grade (snd X.as Y.as) q _ b.2) :
            W.pull (fst X.as Y.as) a.1 * W.pull (snd X.as Y.as) b.1 ∈
              W.grade (prod X.as Y.as) (p + q))⟩ : W.grade (prod X.as Y.as) n) :=
  kunnethIso_hom_apply _ _ _ _ _ _ p q n h a b

omit [CharZero F] in
include hB hC in
/-- `F ≅ H^*(Spec k)` respects the gradings (Stacks 0FHE). -/
theorem algebraMap_mem_grade_point (n : ℤ) (c : F)
    (hc : c ∈ concentratedGrading (R := F) F 0 n) :
    Algebra.linearMap F (W.H (point k)) c ∈ W.grade (point k) n := by
  by_cases hn : n = 0
  · subst hn
    exact SetLike.algebraMap_mem_graded (W.grade (point k)) c
  · rw [eq_zero_of_mem_concentratedGrading (M := F) hn hc, map_zero]
    exact Submodule.zero_mem _

/-- **The unit: `F ≅ H^*(Spec k)`** (Stacks 0FHE), `H^*(Spec k)` being `F` in degree `0`. -/
def corrFunctorεIso :
    𝟙_ (GradedObject ℤ (ModuleCat.{w} F)) ≅
      (corrFunctor hA hB hC).obj (𝟙_ (DegreeZero ℚ (CorrespondenceCategory k))) :=
  letI := concentratedDecomposition (R := F) F 0
  isoTensorUnitConcentrated.symm ≪≫
    gradedIsoOfBijective (concentratedGrading (R := F) F 0) (W.grade (point k))
      (Algebra.linearMap F (W.H (point k))) (algebraMap_mem_grade_point hA hB hC)
      (algebraMap_point_bijective hB.kunnethIsomorphism hC.point)

/-! ### The functor on graphs and on tensor products -/

/-- **`G([Γ_g]) = g^*`** for a morphism of correspondences of degree zero which is a graph. -/
theorem corrHomMap_of_val_eq_graphHom {X Y : DegreeZero ℚ (CorrespondenceCategory k)}
    (f : X ⟶ Y) (g : Y.as ⟶ X.as) (h : DegreeZero.val f = graphHom g) (n : ℤ) :
    corrHomMap hA hB hC f n = W.pullDeg g n := by
  rw [corrHomMap, h, graphHom, ← DirectSum.lof_eq_of ℚ, ChowMotiveCat.component_homOf]
  exact corrMap_graphCorr hA hB hC X.as Y.as g n

/-- The realization of the associativity constraint is pullback along its inverse. -/
theorem corrHomMap_associator_hom (X Y Z : DegreeZero ℚ (CorrespondenceCategory k)) (n : ℤ) :
    corrHomMap hA hB hC (α_ X Y Z).hom n = W.pullDeg (α_ X.as Y.as Z.as).inv n :=
  corrHomMap_of_val_eq_graphHom hA hB hC _ _ rfl n

/-- The realization of the left unit constraint is pullback along its inverse. -/
theorem corrHomMap_leftUnitor_hom (X : DegreeZero ℚ (CorrespondenceCategory k)) (n : ℤ) :
    corrHomMap hA hB hC (λ_ X).hom n = W.pullDeg (λ_ X.as).inv n :=
  corrHomMap_of_val_eq_graphHom hA hB hC _ _ rfl n

/-- The realization of the right unit constraint is pullback along its inverse. -/
theorem corrHomMap_rightUnitor_hom (X : DegreeZero ℚ (CorrespondenceCategory k)) (n : ℤ) :
    corrHomMap hA hB hC (ρ_ X).hom n = W.pullDeg (ρ_ X.as).inv n :=
  corrHomMap_of_val_eq_graphHom hA hB hC _ _ rfl n

/-- The realization of the commutativity constraint is pullback along its inverse. -/
theorem corrHomMap_braiding_hom (X Y : DegreeZero ℚ (CorrespondenceCategory k)) (n : ℤ) :
    corrHomMap hA hB hC (β_ X Y).hom n = W.pullDeg (β_ X.as Y.as).inv n :=
  corrHomMap_of_val_eq_graphHom hA hB hC _ _ rfl n

/-- The tensor product of two morphisms of correspondences of degree zero, as a homogeneous
correspondence of degree `0 + 0`. -/
theorem val_tensorHom {X₁ Y₁ X₂ Y₂ : DegreeZero ℚ (CorrespondenceCategory k)} (f : X₁ ⟶ Y₁)
    (g : X₂ ⟶ Y₂) :
    DegreeZero.val (f ⊗ₘ g) = ChowMotiveCat.homOf (X := (X₁ ⊗ X₂).as) (Y := (Y₁ ⊗ Y₂).as) (0 + 0)
      (CorrespondenceCategory.tensorCorr 0 0
        (ChowMotiveCat.component 0 (DegreeZero.val f))
        (ChowMotiveCat.component 0 (DegreeZero.val g))) := by
  rw [ChowMotiveCat.homOf, DirectSum.lof_eq_of]
  refine Eq.trans ?_ (CorrespondenceCategory.tensorHom_of_of
    (X₁ := GradedCompositionData.Obj.mk X₁.as) (Y₁ := GradedCompositionData.Obj.mk Y₁.as)
    (X₂ := GradedCompositionData.Obj.mk X₂.as) (Y₂ := GradedCompositionData.Obj.mk Y₂.as) _ _)
  rw [← DirectSum.lof_eq_of ℚ, ← DirectSum.lof_eq_of ℚ]
  show DegreeZero.val f ⊗ₘ DegreeZero.val g = ChowMotiveCat.homOf 0 _ ⊗ₘ ChowMotiveCat.homOf 0 _
  rw [← val_eq_homOf, ← val_eq_homOf]

/-- The tensor law, for the tensor product of correspondences of the category of
correspondences. -/
theorem corrMap_tensorCorr (X X' Y Y' : (SmoothProjectiveScheme k).FullSubcategory)
    (c : SmoothProjectiveCorr X Y 0) (c' : SmoothProjectiveCorr X' Y' 0) {p q : ℤ}
    (a : W.grade X p) (a' : W.grade X' q) :
    (corrMap hA hB hC (X ⊗ X') (Y ⊗ Y') (0 + 0) (p + q)
        (SmoothProjectiveCorr.toCorr (X ⊗ X') (Y ⊗ Y') (0 + 0)
          (CorrespondenceCategory.tensorCorr 0 0 c c'))
        ⟨W.pull (fst X X') a * W.pull (snd X X') a',
          (SetLike.GradedMul.mul_mem (W.pull_grade (fst X X') p _ a.2)
            (W.pull_grade (snd X X') q _ a'.2) :
              W.pull (fst X X') a * W.pull (snd X X') a' ∈ W.grade (prod X X') (p + q))⟩ :
        W.H (Y ⊗ Y')) =
      W.pull (fst Y Y') (corrMap hA hB hC X Y 0 p (SmoothProjectiveCorr.toCorr X Y 0 c) a) *
        W.pull (snd Y Y')
          (corrMap hA hB hC X' Y' 0 q (SmoothProjectiveCorr.toCorr X' Y' 0 c') a') :=
  corrMap_tensor hA hB hC X X' Y Y' _ _ a a'

/-- The tensor law, for objects `Z₁ = X × X'` and `Z₂ = Y × Y'` given up to equality, so that it
applies to products written in any form. -/
theorem corrMap_tensor_of_eq (X X' Y Y' : (SmoothProjectiveScheme k).FullSubcategory)
    (c : SmoothProjectiveCorr X Y 0) (c' : SmoothProjectiveCorr X' Y' 0) {p q : ℤ}
    (a : W.grade X p) (a' : W.grade X' q) (Z₁ Z₂ : (SmoothProjectiveScheme k).FullSubcategory)
    (h₁ : X ⊗ X' = Z₁) (h₂ : Y ⊗ Y' = Z₂) (T : SmoothProjectiveCorr Z₁ Z₂ (0 + 0))
    (hT : T ≍ CorrespondenceCategory.tensorCorr 0 0 c c') (e : W.grade Z₁ (p + q))
    (he : e ≍ (⟨W.pull (fst X X') a * W.pull (snd X X') a',
          (SetLike.GradedMul.mul_mem (W.pull_grade (fst X X') p _ a.2)
            (W.pull_grade (snd X X') q _ a'.2) :
              W.pull (fst X X') a * W.pull (snd X X') a' ∈ W.grade (prod X X') (p + q))⟩ :
        W.grade (X ⊗ X') (p + q)))
    (v : W.H Z₂) (hv : v ≍ (W.pull (fst Y Y')
        (corrMap hA hB hC X Y 0 p (SmoothProjectiveCorr.toCorr X Y 0 c) a) *
      W.pull (snd Y Y') (corrMap hA hB hC X' Y' 0 q (SmoothProjectiveCorr.toCorr X' Y' 0 c') a'))) :
    (corrMap hA hB hC Z₁ Z₂ (0 + 0) (p + q) (SmoothProjectiveCorr.toCorr Z₁ Z₂ (0 + 0) T) e :
        W.H Z₂) = v := by
  subst h₁ h₂
  rw [eq_of_heq hT, eq_of_heq he, eq_of_heq hv]
  exact corrMap_tensorCorr hA hB hC X X' Y Y' c c' a a'

/-- **The tensor law on exterior products**:
`G(f ⊗ g)(pr₁^*a ∪ pr₂^*a') = pr₁^*G(f)(a) ∪ pr₂^*G(g)(a')`. -/
theorem corrHomMap_tensorHom {X₁ Y₁ X₂ Y₂ : DegreeZero ℚ (CorrespondenceCategory k)}
    (f : X₁ ⟶ Y₁) (g : X₂ ⟶ Y₂) {p q : ℤ} (a : W.grade X₁.as p) (a' : W.grade X₂.as q) :
    (corrHomMap hA hB hC (f ⊗ₘ g) (p + q)
        ⟨W.pull (fst X₁.as X₂.as) a * W.pull (snd X₁.as X₂.as) a',
          (SetLike.GradedMul.mul_mem (W.pull_grade (fst X₁.as X₂.as) p _ a.2)
            (W.pull_grade (snd X₁.as X₂.as) q _ a'.2) :
              W.pull (fst X₁.as X₂.as) a * W.pull (snd X₁.as X₂.as) a' ∈
                W.grade (prod X₁.as X₂.as) (p + q))⟩ :
        W.H (Y₁ ⊗ Y₂).as) =
      W.pull (fst Y₁.as Y₂.as) (corrHomMap hA hB hC f p a) *
        W.pull (snd Y₁.as Y₂.as) (corrHomMap hA hB hC g q a') := by
  have key := corrMap_tensor_of_eq hA hB hC X₁.as X₂.as Y₁.as Y₂.as
    (ChowMotiveCat.component 0 (DegreeZero.val f)) (ChowMotiveCat.component 0 (DegreeZero.val g))
    a a' (X₁ ⊗ X₂).as (Y₁ ⊗ Y₂).as rfl rfl
    (CorrespondenceCategory.tensorCorr 0 0 (ChowMotiveCat.component 0 (DegreeZero.val f))
      (ChowMotiveCat.component 0 (DegreeZero.val g))) HEq.rfl
    ⟨W.pull (fst X₁.as X₂.as) a * W.pull (snd X₁.as X₂.as) a',
      (SetLike.GradedMul.mul_mem (W.pull_grade (fst X₁.as X₂.as) p _ a.2)
        (W.pull_grade (snd X₁.as X₂.as) q _ a'.2) :
          W.pull (fst X₁.as X₂.as) a * W.pull (snd X₁.as X₂.as) a' ∈
            W.grade (prod X₁.as X₂.as) (p + q))⟩ HEq.rfl
    (W.pull (fst Y₁.as Y₂.as) (corrHomMap hA hB hC f p a) *
      W.pull (snd Y₁.as Y₂.as) (corrHomMap hA hB hC g q a')) HEq.rfl
  have hmap : corrHomMap hA hB hC (f ⊗ₘ g) (p + q) =
      corrMap hA hB hC (X₁ ⊗ X₂).as (Y₁ ⊗ Y₂).as (0 + 0) (p + q)
        (SmoothProjectiveCorr.toCorr (X₁ ⊗ X₂).as (Y₁ ⊗ Y₂).as (0 + 0)
          (CorrespondenceCategory.tensorCorr 0 0 (ChowMotiveCat.component 0 (DegreeZero.val f))
            (ChowMotiveCat.component 0 (DegreeZero.val g)))) := by
    have h₀ : corrHomMap hA hB hC (f ⊗ₘ g) (p + q) =
        corrMap hA hB hC (X₁ ⊗ X₂).as (Y₁ ⊗ Y₂).as 0 (p + q)
          (SmoothProjectiveCorr.toCorr (X₁ ⊗ X₂).as (Y₁ ⊗ Y₂).as 0
            (ChowMotiveCat.component 0 (DegreeZero.val (f ⊗ₘ g)))) := rfl
    have h₁ := congrArg (fun t : (GradedCompositionData.Obj.mk (X₁ ⊗ X₂).as :
        CorrespondenceCategory k) ⟶ GradedCompositionData.Obj.mk (Y₁ ⊗ Y₂).as ↦
      corrMap hA hB hC (X₁ ⊗ X₂).as (Y₁ ⊗ Y₂).as 0 (p + q)
        (SmoothProjectiveCorr.toCorr (X₁ ⊗ X₂).as (Y₁ ⊗ Y₂).as 0 (ChowMotiveCat.component 0 t)))
      (val_tensorHom f g)
    exact h₀.trans (h₁.trans
      (corrMap_component_homOf hA hB hC _ _ (p + q) (0 + 0) (add_zero 0) _))
  exact (congrArg (fun φ : W.grade (X₁ ⊗ X₂).as (p + q) →ₗ[F] W.grade (Y₁ ⊗ Y₂).as (p + q) ↦
    ((φ ⟨W.pull (fst X₁.as X₂.as) a * W.pull (snd X₁.as X₂.as) a',
      (SetLike.GradedMul.mul_mem (W.pull_grade (fst X₁.as X₂.as) p _ a.2)
        (W.pull_grade (snd X₁.as X₂.as) q _ a'.2) :
          W.pull (fst X₁.as X₂.as) a * W.pull (snd X₁.as X₂.as) a' ∈
            W.grade (prod X₁.as X₂.as) (p + q))⟩ : W.grade (Y₁ ⊗ Y₂).as (p + q)) :
        W.H (Y₁ ⊗ Y₂).as)) hmap).trans key

/-! ### The monoidal structure -/

/-- Right whiskering on exterior products:
`G(f ▷ X')(pr₁^*a ∪ pr₂^*a') = pr₁^*G(f)(a) ∪ pr₂^*a'`. -/
theorem corrHomMap_whiskerRight {X Y : DegreeZero ℚ (CorrespondenceCategory k)} (f : X ⟶ Y)
    (X' : DegreeZero ℚ (CorrespondenceCategory k)) {p q : ℤ} (a : W.grade X.as p)
    (a' : W.grade X'.as q) :
    (corrHomMap hA hB hC (f ▷ X') (p + q)
        ⟨W.pull (fst X.as X'.as) a * W.pull (snd X.as X'.as) a',
          (SetLike.GradedMul.mul_mem (W.pull_grade (fst X.as X'.as) p _ a.2)
            (W.pull_grade (snd X.as X'.as) q _ a'.2) :
              W.pull (fst X.as X'.as) a * W.pull (snd X.as X'.as) a' ∈
                W.grade (prod X.as X'.as) (p + q))⟩ :
        W.H (Y ⊗ X').as) =
      W.pull (fst Y.as X'.as) (corrHomMap hA hB hC f p a) * W.pull (snd Y.as X'.as) a' := by
  rw [← MonoidalCategory.tensorHom_id, corrHomMap_tensorHom, corrHomMap_id, LinearMap.id_apply]

/-- Left whiskering on exterior products:
`G(X ◁ g)(pr₁^*a ∪ pr₂^*b) = pr₁^*a ∪ pr₂^*G(g)(b)`. -/
theorem corrHomMap_whiskerLeft (X : DegreeZero ℚ (CorrespondenceCategory k))
    {Y Y' : DegreeZero ℚ (CorrespondenceCategory k)} (g : Y ⟶ Y') {p q : ℤ} (a : W.grade X.as p)
    (b : W.grade Y.as q) :
    (corrHomMap hA hB hC (X ◁ g) (p + q)
        ⟨W.pull (fst X.as Y.as) a * W.pull (snd X.as Y.as) b,
          (SetLike.GradedMul.mul_mem (W.pull_grade (fst X.as Y.as) p _ a.2)
            (W.pull_grade (snd X.as Y.as) q _ b.2) :
              W.pull (fst X.as Y.as) a * W.pull (snd X.as Y.as) b ∈
                W.grade (prod X.as Y.as) (p + q))⟩ :
        W.H (X ⊗ Y').as) =
      W.pull (fst X.as Y'.as) a * W.pull (snd X.as Y'.as) (corrHomMap hA hB hC g q b) := by
  rw [← MonoidalCategory.id_tensorHom, corrHomMap_tensorHom, corrHomMap_id, LinearMap.id_apply]

/-- The Künneth isomorphism is natural in the left factor. -/
theorem corrFunctorμIso_hom_natural_left {X Y : DegreeZero ℚ (CorrespondenceCategory k)}
    (f : X ⟶ Y) (X' : DegreeZero ℚ (CorrespondenceCategory k)) :
    (corrFunctor hA hB hC).map f ▷ (corrFunctor hA hB hC).obj X' ≫
        (corrFunctorμIso hA hB hC Y X').hom =
      (corrFunctorμIso hA hB hC X X').hom ≫ (corrFunctor hA hB hC).map (f ▷ X') := by
  refine GradedObject.hom_ext _ _ fun n ↦ tensorObj_hom_ext fun p q hpq x y ↦ ?_
  subst hpq
  simp only [GradedObject.categoryOfGradedObjects_comp, ModuleCat.hom_comp, LinearMap.comp_apply]
  rw [whiskerRight_apply_ιTensorObj, corrFunctorμIso_hom_apply, corrFunctorμIso_hom_apply]
  refine Subtype.ext ?_
  exact (corrHomMap_whiskerRight hA hB hC f X' x y).symm

/-- The Künneth isomorphism is natural in the right factor. -/
theorem corrFunctorμIso_hom_natural_right {X Y : DegreeZero ℚ (CorrespondenceCategory k)}
    (X' : DegreeZero ℚ (CorrespondenceCategory k)) (g : X ⟶ Y) :
    (corrFunctor hA hB hC).obj X' ◁ (corrFunctor hA hB hC).map g ≫
        (corrFunctorμIso hA hB hC X' Y).hom =
      (corrFunctorμIso hA hB hC X' X).hom ≫ (corrFunctor hA hB hC).map (X' ◁ g) := by
  refine GradedObject.hom_ext _ _ fun n ↦ tensorObj_hom_ext fun p q hpq x y ↦ ?_
  subst hpq
  simp only [GradedObject.categoryOfGradedObjects_comp, ModuleCat.hom_comp, LinearMap.comp_apply]
  rw [whiskerLeft_apply_ιTensorObj, corrFunctorμIso_hom_apply, corrFunctorμIso_hom_apply]
  refine Subtype.ext ?_
  exact (corrHomMap_whiskerLeft hA hB hC X' g x y).symm

/-- The projections of a threefold product through the associativity constraint. -/
theorem associator_inv_fst_fst (X Y Z : (SmoothProjectiveScheme k).FullSubcategory) :
    (α_ X Y Z).inv ≫ fst (prod X Y) Z ≫ fst X Y = fst X (prod Y Z) :=
  (Iso.inv_comp_eq _).2 (prodLift_fst (fst (prod X Y) Z ≫ fst X Y)
    (prodLift (fst (prod X Y) Z ≫ snd X Y) (snd (prod X Y) Z))).symm

/-- The second component of the first factor through the inverse associativity constraint. -/
theorem associator_inv_fst_snd (X Y Z : (SmoothProjectiveScheme k).FullSubcategory) :
    (α_ X Y Z).inv ≫ fst (prod X Y) Z ≫ snd X Y = snd X (prod Y Z) ≫ fst Y Z :=
  (Iso.inv_comp_eq _).2 ((prodLift_snd_assoc (fst (prod X Y) Z ≫ fst X Y)
    (prodLift (fst (prod X Y) Z ≫ snd X Y) (snd (prod X Y) Z)) (fst Y Z)).trans
      (prodLift_fst _ _)).symm

/-- The second projection of a threefold product through the inverse associativity
constraint. -/
theorem associator_inv_snd (X Y Z : (SmoothProjectiveScheme k).FullSubcategory) :
    (α_ X Y Z).inv ≫ snd (prod X Y) Z = snd X (prod Y Z) ≫ snd Y Z :=
  (Iso.inv_comp_eq _).2 ((prodLift_snd_assoc (fst (prod X Y) Z ≫ fst X Y)
    (prodLift (fst (prod X Y) Z ≫ snd X Y) (snd (prod X Y) Z)) (snd Y Z)).trans
      (prodLift_snd _ _)).symm

omit [CharZero F] in
variable (W) in
/-- The associativity constraint on exterior products:
`α^*(pr₁^*(pr₁^*x ∪ pr₂^*y) ∪ pr₂^*z) = pr₁^*x ∪ pr₂^*(pr₁^*y ∪ pr₂^*z)`, for any morphism `α`
with the components of the inverse associativity constraint. -/
theorem pull_exterior_assoc {X Y Z : (SmoothProjectiveScheme k).FullSubcategory}
    (i : prod X (prod Y Z) ⟶ prod (prod X Y) Z)
    (h₁ : i ≫ fst (prod X Y) Z ≫ fst X Y = fst X (prod Y Z))
    (h₂ : i ≫ fst (prod X Y) Z ≫ snd X Y = snd X (prod Y Z) ≫ fst Y Z)
    (h₃ : i ≫ snd (prod X Y) Z = snd X (prod Y Z) ≫ snd Y Z) (x : W.H X) (y : W.H Y)
    (z : W.H Z) :
    W.pull i (W.pull (fst (prod X Y) Z) (W.pull (fst X Y) x * W.pull (snd X Y) y) *
        W.pull (snd (prod X Y) Z) z) =
      W.pull (fst X (prod Y Z)) x * W.pull (snd X (prod Y Z))
        (W.pull (fst Y Z) y * W.pull (snd Y Z) z) := by
  simp only [map_mul, pull_pull, ← Category.assoc] at h₁ h₂ h₃ ⊢
  rw [h₁, h₂, h₃, mul_assoc]

omit [CharZero F] in
variable (W) in
/-- The left unit constraint on exterior products: `λ^*(pr₁^*1 ∪ pr₂^*x) = x`. -/
theorem pull_exterior_leftUnit {X : (SmoothProjectiveScheme k).FullSubcategory}
    (i : X ⟶ prod (point k) X)
    (hi : i ≫ snd (point k) X = 𝟙 X) (e : W.H (point k)) (he : e = 1) (x : W.H X) :
    W.pull i (W.pull (fst (point k) X) e * W.pull (snd (point k) X) x) = x := by
  rw [he, map_one, one_mul, pull_pull, hi, W.pull_id]
  rfl

omit [CharZero F] in
variable (W) in
/-- The right unit constraint on exterior products: `ρ^*(pr₁^*x ∪ pr₂^*1) = x`. -/
theorem pull_exterior_rightUnit {X : (SmoothProjectiveScheme k).FullSubcategory}
    (i : X ⟶ prod X (point k))
    (hi : i ≫ fst X (point k) = 𝟙 X) (e : W.H (point k)) (he : e = 1) (x : W.H X) :
    W.pull i (W.pull (fst X (point k)) x * W.pull (snd X (point k)) e) = x := by
  rw [he, map_one, mul_one, pull_pull, hi, W.pull_id]
  rfl

/-- The inverse left unit constraint followed by the second projection is the identity. -/
theorem leftUnitor_inv_snd (X : (SmoothProjectiveScheme k).FullSubcategory) :
    (λ_ X).inv ≫ snd (point k) X = 𝟙 X :=
  Iso.inv_hom_id (λ_ X)

/-- The inverse right unit constraint followed by the first projection is the identity. -/
theorem rightUnitor_inv_fst (X : (SmoothProjectiveScheme k).FullSubcategory) :
    (ρ_ X).inv ≫ fst X (point k) = 𝟙 X :=
  Iso.inv_hom_id (ρ_ X)

/-- A morphism acting by a pullback acts by it on the elements of the realization. -/
theorem corrFunctor_map_apply_of_eq_pullDeg {X Y : DegreeZero ℚ (CorrespondenceCategory k)}
    (f : X ⟶ Y) (g : Y.as ⟶ X.as) (n : ℤ) (h : corrHomMap hA hB hC f n = W.pullDeg g n)
    (a : (corrFunctor hA hB hC).obj X n) :
    (((corrFunctor hA hB hC).map f n).hom a).1 = W.pull g a.1 :=
  congrArg (fun φ : W.grade X.as n →ₗ[F] W.grade Y.as n ↦ (φ a : W.H Y.as)) h

/-- The Künneth isomorphisms are compatible with the associativity constraints. -/
theorem corrFunctorμIso_associativity (X Y Z : DegreeZero ℚ (CorrespondenceCategory k)) :
    (corrFunctorμIso hA hB hC X Y).hom ▷ (corrFunctor hA hB hC).obj Z ≫
        (corrFunctorμIso hA hB hC (X ⊗ Y) Z).hom ≫ (corrFunctor hA hB hC).map (α_ X Y Z).hom =
      (α_ ((corrFunctor hA hB hC).obj X) ((corrFunctor hA hB hC).obj Y)
          ((corrFunctor hA hB hC).obj Z)).hom ≫
        (corrFunctor hA hB hC).obj X ◁ (corrFunctorμIso hA hB hC Y Z).hom ≫
          (corrFunctorμIso hA hB hC X (Y ⊗ Z)).hom := by
  refine GradedObject.hom_ext _ _ fun n ↦ tensorObj₃'_ext _ _ fun p q r h ↦
    ModuleCat.MonoidalCategory.tensor_ext₃' fun x y z ↦ ?_
  simp only [GradedObject.categoryOfGradedObjects_comp, ModuleCat.hom_comp, LinearMap.comp_apply]
  rw [ιTensorObj₃'_apply, whiskerRight_apply_ιTensorObj, corrFunctorμIso_hom_apply,
    corrFunctorμIso_hom_apply,
    associator_hom_apply_ιTensorObj p q r (p + q) (q + r) n rfl rfl h (by rw [← h, add_assoc]),
    whiskerLeft_apply_ιTensorObj, corrFunctorμIso_hom_apply, corrFunctorμIso_hom_apply]
  refine Subtype.ext ((corrFunctor_map_apply_of_eq_pullDeg hA hB hC _ _ n
    (corrHomMap_associator_hom hA hB hC X Y Z n) _).trans ?_)
  exact (pull_exterior_assoc W (α_ X.as Y.as Z.as).inv
    (associator_inv_fst_fst X.as Y.as Z.as) (associator_inv_fst_snd X.as Y.as Z.as)
    (associator_inv_snd X.as Y.as Z.as) x.1 y.1 z.1)

/-- The unit `F ≅ H^*(Spec k)` sends `1` to `1`. -/
theorem corrFunctorεIso_hom_unitOne :
    (((corrFunctorεIso hA hB hC).hom 0).hom unitOne).1 = 1 := by
  have h : (((isoTensorUnitConcentrated (R := F)).inv 0).hom unitOne : F) = 1 := by
    have e : (GradedObject.singleObjApplyIsoOfEq 0 (𝟙_ (ModuleCat.{w} F)) 0 rfl).hom.hom
        ((GradedObject.singleObjApplyIsoOfEq 0 (𝟙_ (ModuleCat.{w} F)) 0 rfl).inv.hom 1) = 1 := by
      rw [← ModuleCat.comp_apply, Iso.inv_hom_id, ModuleCat.id_apply]
    simp only [isoTensorUnitConcentrated, unitOne, tensorUnit₀, GradedObject.singleObjApplyIso,
      GradedObject.isoMk, dif_pos]
    exact e
  show Algebra.linearMap F (W.H (point k))
    (((isoTensorUnitConcentrated (R := F)).inv 0).hom unitOne : F) = 1
  rw [h, Algebra.linearMap_apply, map_one]

/-- The Künneth isomorphism and the unit are compatible with the left unit constraints. -/
theorem corrFunctor_left_unitality (X : DegreeZero ℚ (CorrespondenceCategory k)) :
    (λ_ ((corrFunctor hA hB hC).obj X)).hom =
      (corrFunctorεIso hA hB hC).hom ▷ (corrFunctor hA hB hC).obj X ≫
        (corrFunctorμIso hA hB hC (𝟙_ _) X).hom ≫ (corrFunctor hA hB hC).map (λ_ X).hom := by
  refine GradedObject.hom_ext _ _ fun n ↦ tensorObj_hom_ext fun p q hpq u x ↦ ?_
  by_cases hp : p = 0
  · subst hp
    obtain rfl : q = n := (zero_add q).symm.trans hpq
    obtain ⟨c, rfl⟩ := exists_smul_unitOne u
    simp only [GradedObject.categoryOfGradedObjects_comp, ModuleCat.hom_comp, LinearMap.comp_apply]
    rw [← TensorProduct.smul_tmul', map_smul, map_smul, map_smul, map_smul, map_smul]
    congr 1
    rw [leftUnitor_hom_apply_ιTensorObj, whiskerRight_apply_ιTensorObj, corrFunctorμIso_hom_apply]
    refine Subtype.ext (Eq.symm ((corrFunctor_map_apply_of_eq_pullDeg hA hB hC _ _ q
      (corrHomMap_leftUnitor_hom hA hB hC X q) _).trans ?_))
    exact pull_exterior_leftUnit W (λ_ X.as).inv (leftUnitor_inv_snd X.as) _
      (corrFunctorεIso_hom_unitOne hA hB hC) x.1
  · obtain rfl : u = 0 := (subsingleton_tensorUnit_apply hp).elim _ _
    simp only [TensorProduct.zero_tmul, map_zero]

/-- The Künneth isomorphism and the unit are compatible with the right unit constraints. -/
theorem corrFunctor_right_unitality (X : DegreeZero ℚ (CorrespondenceCategory k)) :
    (ρ_ ((corrFunctor hA hB hC).obj X)).hom =
      (corrFunctor hA hB hC).obj X ◁ (corrFunctorεIso hA hB hC).hom ≫
        (corrFunctorμIso hA hB hC X (𝟙_ _)).hom ≫ (corrFunctor hA hB hC).map (ρ_ X).hom := by
  refine GradedObject.hom_ext _ _ fun n ↦ tensorObj_hom_ext fun p q hpq x u ↦ ?_
  by_cases hq : q = 0
  · subst hq
    obtain rfl : p = n := (add_zero p).symm.trans hpq
    obtain ⟨c, rfl⟩ := exists_smul_unitOne u
    simp only [GradedObject.categoryOfGradedObjects_comp, ModuleCat.hom_comp, LinearMap.comp_apply]
    rw [TensorProduct.tmul_smul, map_smul, map_smul, map_smul, map_smul, map_smul]
    congr 1
    rw [rightUnitor_hom_apply_ιTensorObj, whiskerLeft_apply_ιTensorObj, corrFunctorμIso_hom_apply]
    refine Subtype.ext (Eq.symm ((corrFunctor_map_apply_of_eq_pullDeg hA hB hC _ _ p
      (corrHomMap_rightUnitor_hom hA hB hC X p) _).trans ?_))
    exact pull_exterior_rightUnit W (ρ_ X.as).inv (rightUnitor_inv_fst X.as) _
      (corrFunctorεIso_hom_unitOne hA hB hC) x.1
  · obtain rfl : u = 0 := (subsingleton_tensorUnit_apply hq).elim _ _
    simp only [TensorProduct.tmul_zero, map_zero]

/-- **The realization is a monoidal functor**, with the Künneth isomorphism as tensorator and
`F ≅ H^*(Spec k)` as unit. -/
def corrFunctorCoreMonoidal : (corrFunctor hA hB hC).CoreMonoidal where
  εIso := corrFunctorεIso hA hB hC
  μIso := corrFunctorμIso hA hB hC
  μIso_hom_natural_left := corrFunctorμIso_hom_natural_left hA hB hC
  μIso_hom_natural_right := corrFunctorμIso_hom_natural_right hA hB hC
  associativity := corrFunctorμIso_associativity hA hB hC
  left_unitality := corrFunctor_left_unitality hA hB hC
  right_unitality := corrFunctor_right_unitality hA hB hC

/-- **The realization as a monoidal functor.** -/
abbrev corrFunctorMonoidal : (corrFunctor hA hB hC).Monoidal :=
  (corrFunctorCoreMonoidal hA hB hC).toMonoidal

/-! ### The symmetry: the Koszul sign -/

/-- The inverse factor switch followed by the first projection is the second projection. -/
theorem braiding_inv_fst (X Y : (SmoothProjectiveScheme k).FullSubcategory) :
    (β_ X Y).inv ≫ fst X Y = snd Y X :=
  (Iso.inv_comp_eq _).2 (prodLift_snd (snd X Y) (fst X Y)).symm

/-- The inverse factor switch followed by the second projection is the first projection. -/
theorem braiding_inv_snd (X Y : (SmoothProjectiveScheme k).FullSubcategory) :
    (β_ X Y).inv ≫ snd X Y = fst Y X :=
  (Iso.inv_comp_eq _).2 (prodLift_fst (snd X Y) (fst X Y)).symm

omit [CharZero F] in
variable (W) in
/-- The commutativity constraint on exterior products, with the Koszul sign of graded
commutativity (D1): `σ^*(pr₁^*x ∪ pr₂^*y) = (-1)^{pq} pr₁^*y ∪ pr₂^*x`, for any morphism `σ`
with the components of the factor switch. -/
theorem pull_exterior_braid {X Y : (SmoothProjectiveScheme k).FullSubcategory}
    (i : prod Y X ⟶ prod X Y)
    (h₁ : i ≫ fst X Y = snd Y X) (h₂ : i ≫ snd X Y = fst Y X) {p q : ℤ} (x : W.H X) (y : W.H Y)
    (hx : x ∈ W.grade X p) (hy : y ∈ W.grade Y q) :
    W.pull i (W.pull (fst X Y) x * W.pull (snd X Y) y) =
      ((p * q).negOnePow : ℤ) • (W.pull (fst Y X) y * W.pull (snd Y X) x) := by
  rw [map_mul, pull_pull, pull_pull, h₁, h₂]
  exact W.graded_comm (prod Y X) p q _ _ (W.pull_grade _ p x hx) (W.pull_grade _ q y hy)

section Braided

attribute [local instance 10000] GradedObject.koszulBraidedCategory
  GradedObject.koszulSymmetricCategory

/-- The Künneth isomorphisms are compatible with the commutativity constraints, the Koszul
symmetry on graded `F`-vector spaces. -/
theorem corrFunctor_braided (X Y : DegreeZero ℚ (CorrespondenceCategory k)) :
    (corrFunctorμIso hA hB hC X Y).hom ≫ (corrFunctor hA hB hC).map (β_ X Y).hom =
      (β_ ((corrFunctor hA hB hC).obj X) ((corrFunctor hA hB hC).obj Y)).hom ≫
        (corrFunctorμIso hA hB hC Y X).hom := by
  refine GradedObject.hom_ext _ _ fun n ↦ tensorObj_hom_ext fun p q hpq x y ↦ ?_
  subst hpq
  simp only [GradedObject.categoryOfGradedObjects_comp, ModuleCat.hom_comp, LinearMap.comp_apply]
  have r : ((β_ ((corrFunctor hA hB hC).obj X) ((corrFunctor hA hB hC).obj Y)).hom (p + q)).hom
      ((ιTensorObj ((corrFunctor hA hB hC).obj X) ((corrFunctor hA hB hC).obj Y) p q (p + q)
        rfl).hom (x ⊗ₜ y)) =
      ((p * q).negOnePow : ℤ) • (ιTensorObj ((corrFunctor hA hB hC).obj Y)
        ((corrFunctor hA hB hC).obj X) q p (p + q) (add_comm q p)).hom (y ⊗ₜ x) :=
    koszulBraiding_hom_apply_ιTensorObj p q (p + q) rfl (add_comm q p) x y
  rw [r, map_zsmul, corrFunctorμIso_hom_apply, corrFunctorμIso_hom_apply]
  refine Subtype.ext ((corrFunctor_map_apply_of_eq_pullDeg hA hB hC _ _ (p + q)
    (corrHomMap_braiding_hom hA hB hC X Y (p + q)) _).trans ?_)
  exact pull_exterior_braid W (β_ X.as Y.as).inv (braiding_inv_fst X.as Y.as)
    (braiding_inv_snd X.as Y.as) x.1 y.1 x.2 y.2

/-- **The realization is a functor of symmetric monoidal categories**, for the Koszul-signed
symmetry of graded `F`-vector spaces (`GradedObject.koszulSymmetricCategory`). -/
abbrev corrFunctorBraided : (corrFunctor hA hB hC).Braided :=
  { corrFunctorMonoidal hA hB hC with
    braided := corrFunctor_braided hA hB hC }

end Braided

end Stacks.WeilCohomology.WeilData

end
