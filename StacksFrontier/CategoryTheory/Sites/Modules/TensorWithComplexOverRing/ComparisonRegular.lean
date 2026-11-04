module

public import StacksFrontier.CategoryTheory.Sites.Modules.TensorWithComplexOverRing.RegularExt
public import StacksFrontier.CategoryTheory.Sites.Modules.TensorWithComplexOverRing.TensorHomComparison

/-!
# The comparison `M ⊗_A Hom(L, K) ⟶ Hom(L, M ⊗_A K)` at the shifts of `Hom(K, K)`

Let `(C, O)` be a ringed site, let `R` be a commutative ring with a sheaf of commutative
`R`-algebra structures on `O`, let `K`, `L` be complexes of `O`-modules with endomorphism
differential graded `R`-algebras `A` and `B`, and let `E = Hom(K, K)`, the differential graded
`A`-module which is the regular module. This file proves that the comparison

`E[k] ⊗_A Hom(L, K) ⟶ Hom(L, E[k] ⊗_A K)`, `x ⊗ φ ↦ (x ⊗ -) ∘ φ`

of `AlgebraicGeometry.RingedSite.tensorHomComparison` is an isomorphism for every shift `E[k]`.

Every element of `E[k] ⊗_A Hom(L, K)` is `1 ⊗ φ` for some `φ`, by the balancing relation, so the
comparison is postcomposition with `1 ⊗ - : K → E[k] ⊗_A K`. That morphism is invertible: at
`k = 0` because the unit of the tensor-Hom adjunction is invertible at `E` and `E ⊗_A K ≅ K`
(Tag 09LV), which forces the image of the identity to be invertible; and at every `k` because the
unit is compatible with the degree-`k` identification `E ⟶ E[k]`
(`AlgebraicGeometry.RingedSite.tensorWithComplexDG_unit_map`).

## Main results

* `AlgebraicGeometry.RingedSite.exists_inverse_tensorUnit_repIdentity`: the morphism
  `1 ⊗ - : K → E ⊗_A K` is invertible.
* `AlgebraicGeometry.RingedSite.isIso_tensorHomComparison_shift`: the comparison is an
  isomorphism at `E[k]`.

## References

* [Stacks Project, Tag 09SU](https://stacks.math.columbia.edu/tag/09SU)
* [Stacks Project, Tag 09LV](https://stacks.math.columbia.edu/tag/09LV)
-/

@[expose] public noncomputable section

open CategoryTheory DifferentialGradedModule CochainComplex.HomComplex

namespace AlgebraicGeometry.RingedSite

universe u

variable (X : AlgebraicGeometry.RingedSite.{u, u, u})
  (R : Type u) [CommRing R] [Linear R (TensorModO.{u, u, u, u, u} X)]
  [ScalarSections.{u, u, u, u, u, u} X R]
  (K L : CochainComplex (ModO.{u, u, u, u} X) ℤ)

/-- `E = Hom(K, K)`, as a differential graded module over the endomorphism algebra `A` of `K`. -/
abbrev repSelf : DifferentialGradedModule.{u, u, u} (Rep.{u, u, u, u, u, u} X R K).algebra :=
  (Rep.{u, u, u, u, u, u} X R K).functor.obj (liftComplex.{u, u, u, u, u} X K)

omit [ScalarSections.{u, u, u, u, u, u} X R] in
/-- A homogeneous element `b ∈ A^n` acting on the identity of `K` gives the element of `E^n`
which is `b` itself, read as a morphism. -/
theorem exists_smul_repIdentity (n : ℤ) (b : (Rep.{u, u, u, u, u, u} X R K).algebra.grading n) :
    ∃ c : (repSelf X R K).grading n,
      (c : (repSelf X R K).M) =
        MulOpposite.op (b : (Rep.{u, u, u, u, u, u} X R K).algebra.A) •
          ((repIdentityOver.{u, u, u, u, u, u} X R K : (repSelf X R K).grading 0) :
            (repSelf X R K).M) ∧
      (Rep.{u, u, u, u, u, u} X R K).moduleHom (liftComplex.{u, u, u, u, u} X K) n c =
        (Rep.{u, u, u, u, u, u} X R K).algebraHom n b := by
  obtain ⟨c, hc, he⟩ := (Rep.{u, u, u, u, u, u} X R K).module_action
    (liftComplex.{u, u, u, u, u} X K) 0 n n (zero_add n)
    (repIdentityOver.{u, u, u, u, u, u} X R K) b
  refine ⟨c, hc, ?_⟩
  rw [he, moduleHom_repIdentityOver]
  exact (CompDG.{u, u, u, u, u, u} X R).id_comp _

omit [ScalarSections.{u, u, u, u, u, u} X R] in
/-- Every homogeneous element of `E` is a homogeneous element of `A` acting on the identity of
`K`. -/
theorem exists_eq_smul_repIdentity (n : ℤ) (z : (repSelf X R K).grading n) :
    ∃ b : (Rep.{u, u, u, u, u, u} X R K).algebra.grading n,
      MulOpposite.op (b : (Rep.{u, u, u, u, u, u} X R K).algebra.A) •
          ((repIdentityOver.{u, u, u, u, u, u} X R K : (repSelf X R K).grading 0) :
            (repSelf X R K).M) = (z : (repSelf X R K).M) := by
  refine ⟨((Rep.{u, u, u, u, u, u} X R K).algebraHom n).symm
    ((Rep.{u, u, u, u, u, u} X R K).moduleHom (liftComplex.{u, u, u, u, u} X K) n z), ?_⟩
  obtain ⟨c, hc, he⟩ := exists_smul_repIdentity X R K n
    (((Rep.{u, u, u, u, u, u} X R K).algebraHom n).symm
      ((Rep.{u, u, u, u, u, u} X R K).moduleHom (liftComplex.{u, u, u, u, u} X K) n z))
  rw [LinearEquiv.apply_symm_apply] at he
  rw [← hc]
  exact congrArg Subtype.val
    (((Rep.{u, u, u, u, u, u} X R K).moduleHom (liftComplex.{u, u, u, u, u} X K) n).injective he)

/-- The image of the identity of `K` under the unit of the tensor-Hom adjunction at `E`: the
degree-zero morphism `1 ⊗ - : K → E ⊗_A K`. -/
abbrev tensorUnitRepIdentity :
    (CompDG.{u, u, u, u, u, u} X R).Hom (liftComplex.{u, u, u, u, u} X K)
      ((tensorWithComplexDG.{u, u, u, u, u, u} X R K).functor.obj (repSelf X R K)) 0 :=
  (Rep.{u, u, u, u, u, u} X R K).moduleHom _ 0
    ⟨_, tensorUnitₗ_mem X R K (repSelf X R K) 0 (repIdentityOver.{u, u, u, u, u, u} X R K)⟩

/-- The degree-zero morphism `1 ⊗ - : K → E ⊗_A K` has a two-sided inverse of degree zero. -/
theorem exists_inverse_tensorUnitRepIdentity :
    ∃ J : (CompDG.{u, u, u, u, u, u} X R).Hom
        ((tensorWithComplexDG.{u, u, u, u, u, u} X R K).functor.obj (repSelf X R K))
        (liftComplex.{u, u, u, u, u} X K) 0,
      DGCategory.comp0 (tensorUnitRepIdentity X R K) J =
          (CompDG.{u, u, u, u, u, u} X R).id (liftComplex.{u, u, u, u, u} X K) ∧
        DGCategory.comp0 J (tensorUnitRepIdentity X R K) =
          (CompDG.{u, u, u, u, u, u} X R).id
            ((tensorWithComplexDG.{u, u, u, u, u, u} X R K).functor.obj (repSelf X R K)) := by
  let ρ : (show (CompDG.{u, u, u, u, u, u} X R).Comp from
        (tensorWithComplexDG.{u, u, u, u, u, u} X R K).functor.obj (repSelf X R K)) ≅
      (show (CompDG.{u, u, u, u, u, u} X R).Comp from liftComplex.{u, u, u, u, u} X K) :=
    tensorWithComplexDG_regular.{u, u, u, u, u, u} X R K
  have hη := isIso_tensorWithComplexDG_adjunction_unit_app_repOver.{u, u, u, u, u, u} X R K
  let φ : (show (dgCategory (Rep.{u, u, u, u, u, u} X R K).algebra).Comp from repSelf X R K) ≅
      (show (dgCategory (Rep.{u, u, u, u, u, u} X R K).algebra).Comp from repSelf X R K) :=
    @asIso _ _ _ _ ((tensorWithComplexDG.{u, u, u, u, u, u} X R K).adjunction.unit.app
      (show (dgCategory (Rep.{u, u, u, u, u, u} X R K).algebra).Comp from repSelf X R K)) hη ≪≫
      (Rep.{u, u, u, u, u, u} X R K).functor.onComp.mapIso ρ
  have hgf : ∀ z, φ.inv.1.1 (φ.hom.1.1 z) = z := fun z =>
    congrArg (fun g => g.1.1 z) φ.hom_inv_id
  have hfg : ∀ z, φ.hom.1.1 (φ.inv.1.1 z) = z := fun z =>
    congrArg (fun g => g.1.1 z) φ.inv_hom_id
  have hfe : φ.hom.1.1
        ((repIdentityOver.{u, u, u, u, u, u} X R K : (repSelf X R K).grading 0) :
          (repSelf X R K).M) =
      ((Rep.{u, u, u, u, u, u} X R K).functor.map ρ.hom.1).1
        (tensorUnitₗ X R K (repSelf X R K) (repIdentityOver.{u, u, u, u, u, u} X R K)) := rfl
  have hfe_mem : φ.hom.1.1
      ((repIdentityOver.{u, u, u, u, u, u} X R K : (repSelf X R K).grading 0) :
        (repSelf X R K).M) ∈ (repSelf X R K).grading 0 := by
    simpa using φ.hom.1.2.1 0
      ((repIdentityOver.{u, u, u, u, u, u} X R K : (repSelf X R K).grading 0) : (repSelf X R K).M)
      (repIdentityOver.{u, u, u, u, u, u} X R K).property
  obtain ⟨V, hV⟩ : ∃ V,
      V = (Rep.{u, u, u, u, u, u} X R K).moduleHom (liftComplex.{u, u, u, u, u} X K) 0
        ⟨_, hfe_mem⟩ := ⟨_, rfl⟩
  have hV' : V = DGCategory.comp0 (tensorUnitRepIdentity X R K) ρ.hom.1 := by
    obtain ⟨c, hc, he⟩ := (Rep.{u, u, u, u, u, u} X R K).map_comp _ _ 0 0 0 rfl ρ.hom.1
      ⟨_, tensorUnitₗ_mem X R K (repSelf X R K) 0 (repIdentityOver.{u, u, u, u, u, u} X R K)⟩
    have hc' : c = ⟨_, hfe_mem⟩ := Subtype.ext (hc.trans hfe.symm)
    rw [hV, ← hc', he]
    rfl
  -- the homogeneous elements acting on `φ e`
  have hact : ∀ b : (Rep.{u, u, u, u, u, u} X R K).algebra.grading 0,
      ∃ c : (repSelf X R K).grading 0,
        (c : (repSelf X R K).M) =
          φ.hom.1.1 (MulOpposite.op (b : (Rep.{u, u, u, u, u, u} X R K).algebra.A) •
            ((repIdentityOver.{u, u, u, u, u, u} X R K : (repSelf X R K).grading 0) :
              (repSelf X R K).M)) ∧
        (Rep.{u, u, u, u, u, u} X R K).moduleHom (liftComplex.{u, u, u, u, u} X K) 0 c =
          DGCategory.comp0 ((Rep.{u, u, u, u, u, u} X R K).algebraHom 0 b) V := by
    intro b
    obtain ⟨c, hc, he⟩ := (Rep.{u, u, u, u, u, u} X R K).module_action
      (liftComplex.{u, u, u, u, u} X K) 0 0 0 rfl ⟨_, hfe_mem⟩ b
    refine ⟨c, hc.trans (φ.hom.1.2.2 b
      ((repIdentityOver.{u, u, u, u, u, u} X R K : (repSelf X R K).grading 0) :
        (repSelf X R K).M)).symm, ?_⟩
    rw [he, hV]
    rfl
  -- `V ∘ B = id`
  have hz := φ.inv.1.2.1 0
    ((repIdentityOver.{u, u, u, u, u, u} X R K : (repSelf X R K).grading 0) : (repSelf X R K).M)
    (repIdentityOver.{u, u, u, u, u, u} X R K).property
  rw [add_zero] at hz
  obtain ⟨b, hb⟩ := exists_eq_smul_repIdentity X R K 0 ⟨_, hz⟩
  have hVB : DGCategory.comp0 ((Rep.{u, u, u, u, u, u} X R K).algebraHom 0 b) V =
      (CompDG.{u, u, u, u, u, u} X R).id _ := by
    obtain ⟨c, hc, he⟩ := hact b
    rw [hb, hfg] at hc
    have hce : c = repIdentityOver.{u, u, u, u, u, u} X R K := Subtype.ext hc
    rw [← he, hce, moduleHom_repIdentityOver]
  -- `((Rep.{u, u, u, u, u, u} X R K).algebraHom 0 b) ∘ V = id`
  have hBV : DGCategory.comp0 V ((Rep.{u, u, u, u, u, u} X R K).algebraHom 0 b) =
      (CompDG.{u, u, u, u, u, u} X R).id _ := by
    obtain ⟨c', hc', he'⟩ := hact (((Rep.{u, u, u, u, u, u} X R K).algebraHom 0).symm
      (DGCategory.comp0 V ((Rep.{u, u, u, u, u, u} X R K).algebraHom 0 b)))
    rw [LinearEquiv.apply_symm_apply, DGCategory.comp0_assoc, hVB, DGCategory.comp0_id] at he'
    have hc'e : c' = ⟨_, hfe_mem⟩ :=
      ((Rep.{u, u, u, u, u, u} X R K).moduleHom _ 0).injective (he'.trans hV)
    have h1 := congrArg Subtype.val hc'e
    rw [hc'] at h1
    have h2 := congrArg φ.inv.1.1 h1
    rw [hgf, hgf] at h2
    obtain ⟨c, hc, he⟩ := exists_smul_repIdentity X R K 0
      (((Rep.{u, u, u, u, u, u} X R K).algebraHom 0).symm
        (DGCategory.comp0 V ((Rep.{u, u, u, u, u, u} X R K).algebraHom 0 b)))
    rw [LinearEquiv.apply_symm_apply] at he
    rw [h2] at hc
    have hce : c = repIdentityOver.{u, u, u, u, u, u} X R K := Subtype.ext hc
    rw [← he, hce, moduleHom_repIdentityOver]
  -- assemble the inverse of `1 ⊗ -`
  have hρ1 : DGCategory.comp0 ρ.hom.1 ρ.inv.1 = (CompDG.{u, u, u, u, u, u} X R).id _ :=
    congrArg Subtype.val ρ.hom_inv_id
  refine ⟨DGCategory.comp0 ρ.hom.1 ((Rep.{u, u, u, u, u, u} X R K).algebraHom 0 b), ?_, ?_⟩
  · rw [← DGCategory.comp0_assoc, ← hV', hBV]
  · have hj : tensorUnitRepIdentity X R K = DGCategory.comp0 V ρ.inv.1 := by
      rw [hV', DGCategory.comp0_assoc, hρ1, DGCategory.comp0_id]
    rw [hj, DGCategory.comp0_assoc,
      ← DGCategory.comp0_assoc ((Rep.{u, u, u, u, u, u} X R K).algebraHom 0 b), hVB,
      DGCategory.id_comp0, hρ1]

/-! ### The shifts `E[k]` -/

omit [ScalarSections.{u, u, u, u, u, u} X R] in
/-- Postcomposition `Hom(L, Y) → Hom(L, Y')` with a homogeneous morphism `g : Y ⟶ Y'` having a
two-sided inverse is bijective. -/
theorem bijective_homPostcomp {Y Y' : (CompDG.{u, u, u, u, u, u} X R).Obj} {m n : ℤ}
    (g : (CompDG.{u, u, u, u, u, u} X R).Hom Y Y' n)
    (g' : (CompDG.{u, u, u, u, u, u} X R).Hom Y' Y m)
    (hmn : m + n = 0) (hnm : n + m = 0)
    (h₁ : (CompDG.{u, u, u, u, u, u} X R).comp hmn g' g = (CompDG.{u, u, u, u, u, u} X R).id Y)
    (h₂ : (CompDG.{u, u, u, u, u, u} X R).comp hnm g g' = (CompDG.{u, u, u, u, u, u} X R).id Y') :
    Function.Bijective ((Rep.{u, u, u, u, u, u} X R L).functor.map g).1 := by
  have e₁ := congrArg (fun f => ((Rep.{u, u, u, u, u, u} X R L).functor.map f).1) h₁
  have e₂ := congrArg (fun f => ((Rep.{u, u, u, u, u, u} X R L).functor.map f).1) h₂
  simp only [(Rep.{u, u, u, u, u, u} X R L).functor.map_comp,
    (Rep.{u, u, u, u, u, u} X R L).functor.map_id] at e₁ e₂
  exact Function.bijective_iff_has_inverse.2
    ⟨((Rep.{u, u, u, u, u, u} X R L).functor.map g').1, fun x => congrArg (fun f => f x) e₁,
      fun x => congrArg (fun f => f x) e₂⟩

variable (k : ℤ)

/-- The shift `E[k]` of `E = Hom(K, K)`. -/
abbrev repSelfShift : DifferentialGradedModule.{u, u, u} (Rep.{u, u, u, u, u, u} X R K).algebra :=
  shift (repSelf X R K) k

/-- The identity of `K`, as a homogeneous element of degree `-k` of `E[k]`. -/
def repIdentityShift : (repSelfShift X R K k).grading (0 + -k) :=
  ⟨((repIdentityOver.{u, u, u, u, u, u} X R K : (repSelf X R K).grading 0) : (repSelf X R K).M),
    (homogeneousMapToShift (repSelf X R K) k).2.1 0 _
      (repIdentityOver.{u, u, u, u, u, u} X R K).property⟩

/-- Postcomposition with `1 ⊗ - : K → E[k] ⊗_A K` is bijective on `Hom(L, -)`. -/
theorem bijective_homPostcomp_tensorUnit_shift :
    Function.Bijective ((Rep.{u, u, u, u, u, u} X R L).functor.map
      ((Rep.{u, u, u, u, u, u} X R K).moduleHom _ (0 + -k)
        ⟨_, tensorUnitₗ_mem X R K (repSelfShift X R K k) (0 + -k)
          (repIdentityShift X R K k)⟩)).1 := by
  have h := tensorWithComplexDG_unit_map.{u, u, u, u, u, u} X R K
    (homogeneousMapToShift (repSelf X R K) k) (repIdentityOver.{u, u, u, u, u, u} X R K)
  have h' : (Rep.{u, u, u, u, u, u} X R K).moduleHom _ (0 + -k)
        ⟨_, tensorUnitₗ_mem X R K (repSelfShift X R K k) (0 + -k) (repIdentityShift X R K k)⟩ =
      (CompDG.{u, u, u, u, u, u} X R).comp (show -k + 0 = 0 + -k by omega)
        ((tensorWithComplexDG.{u, u, u, u, u, u} X R K).functor.map
          (homogeneousMapToShift (repSelf X R K) k)) (tensorUnitRepIdentity X R K) := h
  rw [h', (Rep.{u, u, u, u, u, u} X R L).functor.map_comp]
  rw [dgCategory_comp_val, LinearMap.coe_comp]
  obtain ⟨J, hJ₁, hJ₂⟩ := exists_inverse_tensorUnitRepIdentity X R K
  refine Function.Bijective.comp ?_ (bijective_homPostcomp X R L _ J (zero_add 0) (zero_add 0)
    hJ₁ hJ₂)
  refine bijective_homPostcomp X R L _
    ((tensorWithComplexDG.{u, u, u, u, u, u} X R K).functor.map
      (homogeneousMapFromShift (repSelf X R K) k)) (add_neg_cancel k) (neg_add_cancel k) ?_ ?_
  · rw [← (tensorWithComplexDG.{u, u, u, u, u, u} X R K).functor.map_comp,
      homogeneousMapFromShift_comp_toShift,
      (tensorWithComplexDG.{u, u, u, u, u, u} X R K).functor.map_id]
  · rw [← (tensorWithComplexDG.{u, u, u, u, u, u} X R K).functor.map_comp,
      homogeneousMapToShift_comp_fromShift,
      (tensorWithComplexDG.{u, u, u, u, u, u} X R K).functor.map_id]

omit [ScalarSections.{u, u, u, u, u, u} X R] in
/-- Every element of `E[k] ⊗_A Hom(L, K)` is `1 ⊗ φ` for some `φ`: a homogeneous `x ∈ E[k]` is a
homogeneous `b ∈ A` acting on the identity of `K`, and `(1 · b) ⊗ φ = 1 ⊗ (b · φ)`. -/
theorem surjective_pure_repIdentityShift :
    Function.Surjective (((DifferentialGraded.Bimodule.tensorDGFunctor (homBimodule X R K L)).pure
      (repSelfShift X R K k)).toLinearMap
        ((repIdentityShift X R K k : (repSelfShift X R K k).grading (0 + -k)) :
          (repSelfShift X R K k).M)) := by
  rw [← LinearMap.range_eq_top, eq_top_iff,
    ← DifferentialGraded.Bimodule.pureSpan_eq_top (homBimodule X R K L) (repSelfShift X R K k)]
  refine Submodule.span_le.2 ?_
  rintro _ ⟨p, q, x, y, rfl⟩
  obtain ⟨b, hb⟩ :=
    exists_eq_smul_repIdentity X R K (p + k) ⟨(x : (repSelfShift X R K k).M), x.property⟩
  have hx : (x : (repSelfShift X R K k).M) =
      MulOpposite.op (b : (Rep.{u, u, u, u, u, u} X R K).algebra.A) •
      ((repIdentityShift X R K k : (repSelfShift X R K k).grading (0 + -k)) :
        (repSelfShift X R K k).M) := hb.symm
  refine ⟨((show (homBimodule X R K L).rightModule.grading (q + (p + k)) from
    ((homBimodule X R K L).leftAction.1.action (p + k) b).v q (q + (p + k)) (by omega) y) :
      (homBimodule X R K L).rightModule.M), ?_⟩
  change _ = ((DifferentialGraded.Bimodule.tensorDGFunctor (homBimodule X R K L)).pure
    (repSelfShift X R K k)).toLinearMap (x : (repSelfShift X R K k).M) (y : _)
  rw [hx]
  exact (((DifferentialGraded.Bimodule.tensorDGFunctor (homBimodule X R K L)).pure
    (repSelfShift X R K k)).balance (0 + -k) q (p + k) (repIdentityShift X R K k) y b).symm

/-- **The comparison `E[k] ⊗_A Hom(L, K) ⟶ Hom(L, E[k] ⊗_A K)` is an isomorphism.** On `1 ⊗ φ`
it is postcomposition with `1 ⊗ - : K → E[k] ⊗_A K`, which is bijective
(`AlgebraicGeometry.RingedSite.bijective_homPostcomp_tensorUnit_shift`), and every element is of
that form (`AlgebraicGeometry.RingedSite.surjective_pure_repIdentityShift`). -/
theorem isIso_tensorHomComparison_shift :
    IsIso (tensorHomComparison X R K L (repSelfShift X R K k)) := by
  set t := ((DifferentialGraded.Bimodule.tensorDGFunctor (homBimodule X R K L)).pure
      (repSelfShift X R K k)).toLinearMap
        ((repIdentityShift X R K k : (repSelfShift X R K k).grading (0 + -k)) :
          (repSelfShift X R K k).M) with ht
  have hΨ := bijective_homPostcomp_tensorUnit_shift X R K L k
  have hcomp : ∀ ψ, (tensorHomComparison X R K L (repSelfShift X R K k)).toFun (t ψ) =
      ((Rep.{u, u, u, u, u, u} X R L).functor.map
        ((Rep.{u, u, u, u, u, u} X R K).moduleHom _ (0 + -k)
          ⟨_, tensorUnitₗ_mem X R K (repSelfShift X R K k) (0 + -k)
            (repIdentityShift X R K k)⟩)).1 ψ := by
    intro ψ
    rw [ht, tensorHomComparison_pure, homComp_tensorUnitₗ]
    rfl
  have hsurj := surjective_pure_repIdentityShift X R K L k
  refine isIso_of_bijective _ ⟨fun z₁ z₂ h => ?_, fun w => ?_⟩
  · obtain ⟨ψ₁, rfl⟩ := hsurj z₁
    obtain ⟨ψ₂, rfl⟩ := hsurj z₂
    rw [hcomp, hcomp] at h
    rw [hΨ.1 h]
  · obtain ⟨ψ, hψ⟩ := hΨ.2 w
    exact ⟨t ψ, (hcomp ψ).trans hψ⟩

end AlgebraicGeometry.RingedSite

end
