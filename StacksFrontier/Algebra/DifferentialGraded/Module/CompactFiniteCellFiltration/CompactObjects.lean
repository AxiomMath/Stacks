module

public import Mathlib.CategoryTheory.Filtration.Basic
public import StacksCore.CategoryTheory.Filtration.Basic
public import StacksFrontier.Algebra.DifferentialGraded.Module.Bijective
public import StacksFrontier.Algebra.DifferentialGraded.Module.DerivedCategoryCoproducts
public import StacksFrontier.Algebra.DifferentialGraded.Module.DerivedCategoryDevissage
public import StacksFrontier.Algebra.DifferentialGraded.Module.EvaluationAtOne
public import StacksFrontier.Algebra.DifferentialGraded.Module.GradedSubmodule
public import StacksFrontier.Algebra.DifferentialGraded.Module.LongExactSequence
public import StacksFrontier.Algebra.DifferentialGraded.Module.OrthogonalAcyclic
public import StacksFrontier.Algebra.DifferentialGraded.Module.Shift
public import StacksFrontier.Algebra.DifferentialGraded.Module.Subquotient
public import StacksFrontier.Algebra.DifferentialGraded.Module.Telescope
public import StacksFrontier.CategoryTheory.Triangulated.CompactObjects
import StacksCore.Tactic.EgaSgaAttribute
public import StacksFrontier.Algebra.DifferentialGraded.Module.CompactFiniteCellFiltration.DirectSums
public import StacksFrontier.Algebra.DifferentialGraded.Module.CompactFiniteCellFiltration.FiniteSubfiltration

/-!
# The compact objects of the derived category of a differential graded algebra

Say that a differential graded `A`-module `P` **has a finite cell filtration** when it carries a
finite filtration by differential graded submodules whose successive quotients are *finite* direct
sums of shifts of the algebra. [Stacks, Tag 09R3] characterises the compact objects of `D(A, d)`:
they are exactly the retracts of the images of the modules with a finite cell filtration.

One implication is the dévissage of the compact objects out of the shifts `A[k]`, which are
compact because a morphism `A[k] ⟶ N` is right multiplication by a degree `-k` cocycle of `N`
(Tag 09K1) and a cocycle of a direct sum has finite support. The other is the source's argument: a
compact object is the image of a module `P` with a property-(P) filtration (Tag 09KP), whose
telescope (Tag 09KL) presents `P` as a derived colimit of the stages `FₙP`; a morphism out of a
compact object into a derived colimit factors through one stage (Tag 094A), and Tag 09R2 then cuts
that stage down to a submodule with a finite cell filtration.

## Main definitions and results

* `DifferentialGradedModule.HasFiniteCellFiltration`: a finite cell filtration.
* `DifferentialGradedModule.isAdmissibleShortExact_cokernelπ`: the graded splitting of a step.
* `DifferentialGradedModule.isCompactObject_iff_exists_retract_hasFiniteCellFiltration`:
  **Tag 09R3**.

## Implementation notes

Tag 09R3 says *direct summand*; the statement says *retract*. The two agree because `D(A, d)` is
idempotent complete ([Stacks, Tag 05QW], the last conjunct of the omnibus theorem of Tag 09QH).

## References

* [Stacks Project, Tag 09R3](https://stacks.math.columbia.edu/tag/09R3); also Tags 094A, 09K1,
  09KL, 09KP and 09QH.
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits

namespace DifferentialGradedModule

/- As in `CompactFiniteCellFiltration/DirectSums.lean`: the admissible-sequence pretriangulated
structure on the homotopy category is the one used throughout; it is not an instance, so it is
activated here explicitly. -/
attribute [local instance 10000] instPretriangulatedHomotopyCategory'

universe u u₁ u₂

variable {R : Type u} [CommRing R] {A : DifferentialGradedAlgebra.{u, u} R}

/-! ### Morphisms out of a compact object into a derived colimit

The fact of [Stacks, Tag 094A] that the characterisation of the compact objects consumes. A
system `(Gₙ, fₙ)` over `ℕ` with a direct sum `(V, σₙ)` carries the endomorphism `1 - f` of `V`
determined by `σₙ ≫ (1 - f) = σₙ - fₙ ≫ σₙ₊₁`, and a derived colimit of the system is the third
vertex of a distinguished triangle on it. Then a morphism out of a compact object into a derived
colimit factors through one term of the system.

The two halves it rests on — that `1 - f` is injective on the morphisms out of a compact object
(`CategoryTheory.Pretriangulated.eq_zero_of_comp_eq_zero_of_isColimitCofan`), and that a morphism
out of a compact object into `V` factors through one term after composition with any map
compatible with the transitions
(`CategoryTheory.Pretriangulated.exists_factor_comp_of_isColimitCofan`) — live in
`StacksFrontier.CategoryTheory.Triangulated.CompactObjects`, where the chosen-coproduct forms for a
functor `ℕ ⥤ D` are specialisations of them.

The direct sum is taken there as an arbitrary colimit cofan `(V, σₙ)` rather than as the chosen
coproduct `∐ₙ Gₙ`, which is what this application needs: here `V` is the image of a differential
graded module and the legs `σₙ` are images of homomorphisms, which the chosen coproduct would
only match up to unfolding. -/

section DerivedColimit

section HomotopyColimit

variable {D : Type u₂} [Category.{u₁} D] [Preadditive D] [HasZeroObject D] [HasShift D ℤ]
  [∀ n : ℤ, (CategoryTheory.shiftFunctor D n).Additive] [Pretriangulated D]

/-- In the triangle defining a derived colimit `L`, the structure morphism `p` is compatible with
the transition morphisms of the system. -/
private lemma leg_comp_eq_of_distTriang {G : ℕ → D} {t : ∀ n, G n ⟶ G (n + 1)} {V : D}
    {σ : ∀ n, G n ⟶ V} {a : V ⟶ V} (ha : ∀ n, σ n ≫ a = σ n - t n ≫ σ (n + 1))
    {L : D} {p : V ⟶ L} {q : L ⟶ V⟦(1 : ℤ)⟧}
    (hT : Pretriangulated.Triangle.mk a p q ∈ distTriang D) (n : ℕ) :
    σ n ≫ p = t n ≫ σ (n + 1) ≫ p := by
  have h0 : a ≫ p = 0 := Pretriangulated.comp_distTriang_mor_zero₁₂ _ hT
  have h : (σ n ≫ a) ≫ p = 0 := by rw [Category.assoc, h0, comp_zero]
  rwa [ha n, Preadditive.sub_comp, sub_eq_zero, Category.assoc] at h

/-- **[Stacks, Tag 094A].** A morphism from a compact object into a derived colimit of a system
over `ℕ` factors through one term of the system. The derived colimit is presented by a
distinguished triangle on the map `1 - fₙ`, here recorded as a map `a` of the direct sum whose
`n`-th leg is `σₙ - fₙ ≫ σₙ₊₁`. -/
private lemma exists_factorThrough_stage_of_distTriang (G : ℕ → D) (t : ∀ n, G n ⟶ G (n + 1))
    {V : D} (σ : ∀ n, G n ⟶ V) (hσ : IsColimit (Cofan.mk V σ))
    {a : V ⟶ V} (ha : ∀ n, σ n ≫ a = σ n - t n ≫ σ (n + 1))
    {L : D} {p : V ⟶ L} {q : L ⟶ V⟦(1 : ℤ)⟧}
    (hT : Pretriangulated.Triangle.mk a p q ∈ distTriang D)
    (K : D) [hK : IsCompactObject.{u} K] (ζ : K ⟶ L) :
    ∃ (n : ℕ) (ρ : K ⟶ G n), ρ ≫ σ n ≫ p = ζ := by
  have : IsCompactObject.{u} (K⟦(-1 : ℤ)⟧) :=
    (isCompactObject_iff_isCompactObject_obj (CategoryTheory.shiftFunctor D (-1 : ℤ)) K).mp hK
  have h0 : q ≫ a⟦(1 : ℤ)⟧' = 0 := Pretriangulated.comp_distTriang_mor_zero₃₁ _ hT
  have hζq : ζ ≫ q = 0 := by
    refine Pretriangulated.eq_zero_of_comp_shift_map_eq_zero (b := a)
      (fun g hg ↦ Pretriangulated.eq_zero_of_comp_eq_zero_of_isColimitCofan
        G t σ hσ ha _ g hg) _ ?_
    simp only [Category.assoc, h0, comp_zero]
  obtain ⟨ψ, hψ⟩ := Pretriangulated.Triangle.coyoneda_exact₃ _ hT _ hζq
  obtain ⟨n, ρ, hρ⟩ :=
    Pretriangulated.exists_factor_comp_of_isColimitCofan G t σ hσ p
      (leg_comp_eq_of_distTriang ha hT) K ψ
  exact ⟨n, ρ, hρ.symm.trans hψ.symm⟩

end HomotopyColimit

end DerivedColimit

/-! ### Morphisms out of a shift of the regular module

A homomorphism `A[k] ⟶ N` of differential graded modules is right multiplication by its value at
the unit, which is a cocycle of degree `-k`; it is null-homotopic exactly when that cocycle is a
coboundary. Reading this off for `N` a direct sum shows that `A[k]` is a compact object of
`D(A, d)`: a cocycle of a direct sum has finite support.
-/

section RegularModuleShift

/-- Right multiplication by a fixed element of a right differential graded module, as a map of
right `A`-modules out of the algebra. -/
private def rightMul {N : DifferentialGradedModule.{u, u, u} A} (y : N.M) :
    A.A →ₗ[MulOpposite A.A] N.M where
  toFun a := MulOpposite.op a • y
  map_add' a b := by rw [MulOpposite.op_add, add_smul]
  map_smul' c a := by
    change MulOpposite.op (a * c.unop) • y = c • (MulOpposite.op a • y)
    rw [MulOpposite.op_mul, MulOpposite.op_unop, mul_smul]

/-- Right multiplication, on an element of the algebra. -/
private lemma rightMul_apply {N : DifferentialGradedModule.{u, u, u} A} (y : N.M) (a : A.A) :
    rightMul y a = MulOpposite.op a • y := rfl

/-- The unit is homogeneous of degree `-k` in the `k`-th shift of the regular module. -/
private lemma one_mem_shift_grading (k : ℤ) :
    (1 : A.A) ∈ (shift (regularModule A) k).grading (-k) := by
  simp only [shift_grading, neg_add_cancel]
  exact SetLike.one_mem_graded A.grading

/-- The differential of the shift of the regular module, on an element of the algebra. -/
private lemma shift_regularModule_d (k : ℤ) (b : A.A) :
    (shift (regularModule A) k).d b = (k.negOnePow : ℤ) • A.d b := by
  rw [shift_d, LinearMap.smul_apply, Units.smul_def]

/-- The differential of the shift of the regular module kills the unit. -/
private lemma shift_regularModule_d_one (k : ℤ) :
    (shift (regularModule A) k).d (1 : A.A) = 0 := by
  rw [shift_regularModule_d, algebraDifferential_one, smul_zero]

/-- Right multiplication by `y` after the differential of the shift of the regular module. -/
private lemma rightMul_shift_d {N : DifferentialGradedModule.{u, u, u} A} (y : N.M) (k : ℤ)
    (b : A.A) :
    rightMul y ((shift (regularModule A) k).d b) = (k.negOnePow : ℤ) • rightMul y (A.d b) := by
  rw [shift_regularModule_d, map_zsmul]

/-- A homomorphism out of a shift of the regular module is right multiplication by its value at
the unit. -/
private lemma hom_shift_regularModule_apply {N : DifferentialGradedModule.{u, u, u} A} (k : ℤ)
    (f : shift (regularModule A) k ⟶ N) (b : A.A) :
    f.toFun b = MulOpposite.op b • f.toFun (1 : A.A) := by
  have h1b : (MulOpposite.op b • (1 : A.A) : A.A) = b := one_mul b
  simpa [h1b] using f.map_smul (1 : A.A) b

/-- Two homomorphisms out of a shift of the regular module agreeing at the unit are equal. -/
private lemma hom_shift_regularModule_ext {N : DifferentialGradedModule.{u, u, u} A} (k : ℤ)
    (f g : shift (regularModule A) k ⟶ N)
    (h : f.toFun (1 : A.A) = g.toFun (1 : A.A)) : f = g := by
  refine Hom.ext (LinearMap.ext fun a => ?_)
  exact ((hom_shift_regularModule_apply k f a).trans (by rw [h])).trans
    (hom_shift_regularModule_apply k g a).symm

/-- The homomorphism `A[k] ⟶ N` attached to a cocycle of degree `-k`: right multiplication by
that cocycle. -/
private def cocycleHom {N : DifferentialGradedModule.{u, u, u} A} (k : ℤ) {y : N.M}
    (hy : y ∈ N.grading (-k)) (hdy : N.d y = 0) : shift (regularModule A) k ⟶ N where
  toFun := (rightMul y).restrictScalars R
  map_smul x a := (rightMul y).map_smul (MulOpposite.op a) x
  map_grading n x hx := by
    have hx' : (x : A.A) ∈ A.grading (n + k) := hx
    have hm := N.smul_mem (-k) (n + k) y x hy hx'
    rwa [show -k + (n + k) = n from by ring] at hm
  map_d := LinearMap.ext fun b => by
    simp only [LinearMap.comp_apply, LinearMap.restrictScalars_apply]
    rw [rightMul_shift_d, rightMul_apply, rightMul_apply, leibniz_apply N (-k) y hy b, hdy,
      smul_zero, zero_add, Int.negOnePow_neg]

/-- The attached homomorphism takes the unit to the given cocycle. -/
private lemma cocycleHom_one {N : DifferentialGradedModule.{u, u, u} A} (k : ℤ) {y : N.M}
    (hy : y ∈ N.grading (-k)) (hdy : N.d y = 0) :
    (cocycleHom k hy hdy).toFun (1 : A.A) = y := by
  change MulOpposite.op (1 : A.A) • y = y
  rw [MulOpposite.op_one, one_smul]

/-- A homomorphism out of a shift of the regular module whose value at the unit is the coboundary
of a homogeneous element is null-homotopic: right multiplication by that element is a homotopy to
zero. The sign `(-1)^k` in the differential of the shift cancels against the sign produced by the
Leibniz rule. -/
private lemma homotopic_zero_of_d_eq {N : DifferentialGradedModule.{u, u, u} A} (k : ℤ)
    (g : shift (regularModule A) k ⟶ N) {z : N.M} (hz : z ∈ N.grading (-k - 1))
    (hdz : N.d z = g.toFun (1 : A.A)) : Homotopic g 0 := by
  have hsign : ((-k - 1).negOnePow : ℤ) + (k.negOnePow : ℤ) = 0 := by
    have hne : (-k - 1).negOnePow = -k.negOnePow := by
      rw [show -k - 1 = -(k + 1) from by ring, Int.negOnePow_neg, Int.negOnePow_add,
        Int.negOnePow_one, mul_neg_one]
    rw [hne]
    simp
  refine ⟨{ toLinearMap := rightMul z, map_grading := ?_, homotopy_eq := ?_ }⟩
  · intro n a ha
    have ha' : (a : A.A) ∈ A.grading (n + k) := ha
    have hmem := N.smul_mem (-k - 1) (n + k) z a hz ha'
    rwa [show -k - 1 + (n + k) = n - 1 from by ring] at hmem
  · intro b
    rw [Hom.hom_zero_toFun, LinearMap.zero_apply, sub_zero]
    rw [rightMul_shift_d, rightMul_apply, rightMul_apply, leibniz_apply N (-k - 1) z hz b, hdz,
      add_assoc, ← add_smul, hsign, zero_smul, add_zero]
    exact hom_shift_regularModule_apply k g b

/-- Evaluation of a homomorphism of differential graded modules at a fixed element, as an additive
map on the morphism group. -/
private def evalHom {M N : DifferentialGradedModule.{u, u, u} A} (x : M.M) : (M ⟶ N) →+ N.M where
  toFun f := f.toFun x
  map_zero' := by rw [Hom.hom_zero_toFun]; rfl
  map_add' f g := by rw [Hom.hom_add_toFun]; rfl

/-- A morphism of `K(A, d)` out of the image of a shift of the regular module into the image of a
direct sum of differential graded modules is a finite sum of morphisms into the summands: it is
right multiplication by a cocycle of the direct sum, and such a cocycle has finite support. -/
private lemma surjective_cofanMap_toHomotopyCategory_shift (k : ℤ) {I : Type u} [DecidableEq I]
    (N : I → DifferentialGradedModule.{u, u, u} A) :
    Function.Surjective (cofanMap ((toHomotopyCategory A).obj (shift (regularModule A) k))
      fun i => (toHomotopyCategory A).map (directSumInj N i)) := by
  classical
  intro φ
  obtain ⟨g, hg⟩ : ∃ g : shift (regularModule A) k ⟶ directSumObj N,
      (toHomotopyCategory A).map g = φ :=
    ⟨(toHomotopyCategory A).preimage φ, (toHomotopyCategory A).map_preimage φ⟩
  obtain ⟨y, hy⟩ : ∃ y : DirectSum I (fun i => (N i).M), g.toFun (1 : A.A) = y := ⟨_, rfl⟩
  have hygrad : ∀ i, y i ∈ (N i).grading (-k) := by
    have h := g.map_grading (-k) (1 : A.A) (one_mem_shift_grading k)
    rw [hy] at h
    exact h
  have hyd0 : directSumD N y = 0 := by
    have h : g.toFun ((shift (regularModule A) k).d (1 : A.A))
        = (directSumObj N).d (g.toFun (1 : A.A)) := LinearMap.congr_fun g.map_d (1 : A.A)
    rw [shift_regularModule_d_one, map_zero, hy] at h
    exact h.symm
  have hcoc : ∀ i, (N i).d (y i) = 0 := fun i => by
    have h := congrArg (fun w : DirectSum I (fun i => (N i).M) => w i) hyd0
    simpa only [directSumD_apply, DirectSum.zero_apply] using h
  refine ⟨∑ i ∈ DFinsupp.support y,
    DirectSum.of (fun i => ((toHomotopyCategory A).obj (shift (regularModule A) k) ⟶
      (toHomotopyCategory A).obj (N i))) i
      ((toHomotopyCategory A).map (cocycleHom k (hygrad i) (hcoc i))), ?_⟩
  have hsum : ∑ i ∈ DFinsupp.support y,
      (cocycleHom k (hygrad i) (hcoc i) ≫ directSumInj N i) = g := by
    refine hom_shift_regularModule_ext k _ _ ?_
    have hev := map_sum (evalHom (N := directSumObj N) (1 : A.A))
      (fun i => cocycleHom k (hygrad i) (hcoc i) ≫ directSumInj N i) (DFinsupp.support y)
    have hterm : ∀ i : I, (cocycleHom k (hygrad i) (hcoc i) ≫ directSumInj N i).toFun
        (1 : A.A) = DirectSum.of (fun i => (N i).M) i (y i) := by
      intro i
      change (directSumInj N i).toFun ((cocycleHom k (hygrad i) (hcoc i)).toFun (1 : A.A)) = _
      rw [cocycleHom_one, directSumInj_toFun_apply, DirectSum.lof_eq_of]
    have hgoal : (∑ i ∈ DFinsupp.support y,
        (cocycleHom k (hygrad i) (hcoc i) ≫ directSumInj N i)).toFun (1 : A.A)
        = ∑ i ∈ DFinsupp.support y,
          (cocycleHom k (hygrad i) (hcoc i) ≫ directSumInj N i).toFun (1 : A.A) := hev
    rw [hgoal]
    simp only [hterm]
    rw [DirectSum.sum_support_of y]
    exact hy.symm
  rw [map_sum]
  simp only [cofanMap_of, ← CategoryTheory.Functor.map_comp]
  rw [← CategoryTheory.Functor.map_sum, hsum, hg]

end RegularModuleShift

/-! ### Compactness of the shifts of the algebra -/

/-- **The image in `D(A, d)` of a shift of the regular module is a compact object.** Morphisms out
of it are computed in `K(A, d)` (Tag 09K1), every direct sum in `D(A, d)` is the image of a direct
sum of differential graded modules (Tag 09QI), and a morphism `A[k] ⟶ ⨁ᵢ Nᵢ` is right
multiplication by a degree `-k` cocycle of the direct sum, hence a finite sum of morphisms into
the summands. -/
private lemma isCompactObject_toDerivedCategory_shift_regularModule (k : ℤ) :
    IsCompactObject.{u} ((toHomotopyCategory A ⋙ (quasiIsomorphisms' A).Q).obj
      (shift (regularModule A) k)) := by
  classical
  constructor
  intro I _ E _
  change Function.Bijective (cofanMap _ (Limits.Sigma.ι E))
  set L := (quasiIsomorphisms' A).Q
  set Q := toHomotopyCategory A ⋙ L
  choose P a ha hP using fun i : I =>
    exists_isQuasiIsomorphism_leftOrthogonal A ((L.objPreimage (E i)).as)
  have hiso : ∀ i, IsIso (Q.map (a i)) := fun i =>
    isIso_q_map_of_isQuasiIsomorphism (a i) (ha i)
  let e : ∀ i, Q.obj (P i) ≅ E i := fun i =>
    (asIso (Q.map (a i))).trans
      (show Q.obj ((L.objPreimage (E i)).as) ≅ E i from L.objObjPreimageIso (E i))
  have hc : IsColimit (Cofan.mk (Q.obj (directSumObj P)) fun i => Q.map (directSumInj P i)) :=
    isColimitMapCoconeCofanMkEquiv Q P (directSumInj P)
      (isColimit_q_mapCocone_directSumObj P hP)
  -- the comparison of the two direct sums of the family `Q (P i)`
  let d : Q.obj (directSumObj P) ⟶ ∐ E :=
    Cofan.IsColimit.desc hc fun i => (e i).hom ≫ Limits.Sigma.ι E i
  have hd : ∀ i, Q.map (directSumInj P i) ≫ d = (e i).hom ≫ Limits.Sigma.ι E i := fun i =>
    Cofan.IsColimit.fac hc _ i
  let d' : (∐ E) ⟶ Q.obj (directSumObj P) :=
    Limits.Sigma.desc fun i => (e i).inv ≫ Q.map (directSumInj P i)
  have hd' : ∀ i, Limits.Sigma.ι E i ≫ d' = (e i).inv ≫ Q.map (directSumInj P i) := fun i =>
    Limits.Sigma.ι_comp_desc _ _
  have hdd' : d ≫ d' = 𝟙 _ := by
    refine Cofan.IsColimit.hom_ext hc _ _ fun i => ?_
    have h1 : Q.map (directSumInj P i) ≫ d ≫ d' = Q.map (directSumInj P i) := by
      rw [← Category.assoc, hd i, Category.assoc, hd' i, Iso.hom_inv_id_assoc]
    simpa using h1
  have hd'd : d' ≫ d = 𝟙 _ := by
    refine Limits.Sigma.hom_ext _ _ fun i => ?_
    have h1 : Limits.Sigma.ι E i ≫ d' ≫ d = Limits.Sigma.ι E i := by
      rw [← Category.assoc, hd' i, Category.assoc, hd i, Iso.inv_hom_id_assoc]
    simpa using h1
  refine bijective_cofanMap_of_iso _ (fun i => Q.map (directSumInj P i)) (Limits.Sigma.ι E) e
    ⟨d, d', hdd', hd'd⟩ hd ⟨injective_cofanMap _ _ hc, ?_⟩
  intro ψ
  obtain ⟨φ, hφ⟩ := (map_q_bijective_of_leftOrthogonal
    (leftOrthogonal_acyclic_toHomotopyCategory_shift_regularModule A k)
    ((toHomotopyCategory A).obj (directSumObj P))).surjective ψ
  obtain ⟨x, hx⟩ := surjective_cofanMap_toHomotopyCategory_shift k P φ
  have hφsum : φ = ∑ i ∈ DFinsupp.support x,
      x i ≫ (toHomotopyCategory A).map (directSumInj P i) := by
    rw [← hx]
    conv_lhs => rw [← DirectSum.sum_support_of x]
    rw [map_sum]
    refine Finset.sum_congr rfl fun i _ => ?_
    simp only [cofanMap_of]
  refine ⟨∑ i ∈ DFinsupp.support x,
    DirectSum.of (fun i => (Q.obj (shift (regularModule A) k) ⟶ Q.obj (P i))) i
      (L.map (x i)), ?_⟩
  rw [map_sum]
  simp only [cofanMap_of]
  rw [← hφ, hφsum, CategoryTheory.Functor.map_sum]
  exact Finset.sum_congr rfl fun i _ =>
    (L.map_comp (x i) ((toHomotopyCategory A).map (directSumInj P i))).symm

/-- **The image in `D(A, d)` of a finite direct sum of shifts of the regular module is a compact
object.** The compact objects are closed under isomorphisms and form a triangulated subcategory
(Tag 09QH), hence are closed under finite direct sums. -/
private lemma isCompactObject_toDerivedCategory_coproduct_shifts {J : Type u} [Finite J]
    (k : J → ℤ) :
    IsCompactObject.{u} ((toHomotopyCategory A ⋙ (quasiIsomorphisms' A).Q).obj
      (∐ fun j => shift (regularModule A) (k j))) := by
  let C : ObjectProperty (derivedCategory' A) := IsCompactObject.{u}
  obtain ⟨hcliso, hcltri, _⟩ :=
    isClosedUnderIsomorphisms_isTriangulated_isSaturated_and_isIdempotentComplete_isCompactObject
      (D := derivedCategory' A)
  have : C.IsClosedUnderIsomorphisms := hcliso
  have : C.IsTriangulated := hcltri
  have : C.IsClosedUnderFiniteCoproducts :=
    ⟨fun _ _ => C.isClosedUnderColimitsOfShape_of_preservesColimitsOfShape_ι _⟩
  exact C.prop_of_isColimit_cofan
    (isColimitCofanMkObjOfIsColimit (toHomotopyCategory A ⋙ (quasiIsomorphisms' A).Q)
      (fun j => shift (regularModule A) (k j)) _
      (coproductIsCoproduct fun j => shift (regularModule A) (k j)))
    (fun j => isCompactObject_toDerivedCategory_shift_regularModule (k j))

/-! ### Factoring through a stage of a property-(P) filtration -/

section PropertyPStage

/-- **A morphism of `D(A, d)` out of a compact object into the image of a module with a
property-(P) filtration factors through the image of one stage of the filtration.** The telescope
of Tag 09KL presents the module as the quotient term of an admissible short exact sequence whose
outer terms are the direct sum of the stages, so Tag 09K8 makes it a derived colimit of the
stages, and a morphism out of a compact object into a derived colimit factors through one term
(Tag 094A). -/
private lemma exists_factorThrough_propertyPFiltration_stage
    {P : DifferentialGradedModule.{u, u, u} A} (F : PropertyPFiltration P)
    (E : derivedCategory' A) [IsCompactObject.{u} E]
    (f : E ⟶ (toHomotopyCategory A ⋙ (quasiIsomorphisms' A).Q).obj P) :
    ∃ (n : ℕ) (g : E ⟶ (toHomotopyCategory A ⋙ (quasiIsomorphisms' A).Q).obj (F.F n)),
      g ≫ (toHomotopyCategory A ⋙ (quasiIsomorphisms' A).Q).map (F.ι n) = f := by
  classical
  obtain ⟨S, ι, α, β, huniv, hβ, hα, hab⟩ := exists_telescope_of_propertyPFiltration F
  -- the direct sum of the stages, read in the derived category
  have hS : IsColimit (Cofan.mk S ι) := by
    refine IsColimit.ofExistsUnique fun T => ?_
    obtain ⟨h, hh, huq⟩ := huniv T.pt fun i => T.ι.app ⟨i⟩
    exact ⟨h, by rintro ⟨i⟩; exact hh i, fun m hm => huq m fun i => hm ⟨i⟩⟩
  have hpres : PreservesColimitsOfShape (Discrete ℕ)
      (toHomotopyCategory A ⋙ (quasiIsomorphisms' A).Q) :=
    preservesColimitsOfShape_of_equiv
      (Discrete.equivalence (Equiv.ulift : ULift.{u} ℕ ≃ ℕ)) _
  have hcofan : IsColimit (Cofan.mk
      ((toHomotopyCategory A ⋙ (quasiIsomorphisms' A).Q).obj S)
      fun n : ℕ => (toHomotopyCategory A ⋙ (quasiIsomorphisms' A).Q).map (ι n)) :=
    isColimitCofanMkObjOfIsColimit _ (fun n : ℕ => F.F n) ι hS
  -- the telescope triangle
  obtain ⟨δ, hδ⟩ : ∃ δ : (toHomotopyCategory A ⋙ (quasiIsomorphisms' A).Q).obj P ⟶
        ((toHomotopyCategory A ⋙ (quasiIsomorphisms' A).Q).obj S)⟦(1 : ℤ)⟧,
      Pretriangulated.Triangle.mk ((toHomotopyCategory A ⋙ (quasiIsomorphisms' A).Q).map α)
          ((toHomotopyCategory A ⋙ (quasiIsomorphisms' A).Q).map β) δ
        ∈ distTriang (derivedCategory' A) :=
    ⟨_, ((quasiIsomorphisms' A).Q).map_distinguished _
      (associatedTriangle_mem_distTriang A α β hab)⟩
  have hα' : ∀ n : ℕ, ι n ≫ α = ι n - F.incl n ≫ ι (n + 1) := by
    intro n
    refine Hom.ext (LinearMap.ext fun x => ?_)
    rw [Hom.hom_sub_toFun]
    exact hα n x
  have ha : ∀ n : ℕ, (toHomotopyCategory A ⋙ (quasiIsomorphisms' A).Q).map (ι n) ≫
        (toHomotopyCategory A ⋙ (quasiIsomorphisms' A).Q).map α
      = (toHomotopyCategory A ⋙ (quasiIsomorphisms' A).Q).map (ι n) -
        (toHomotopyCategory A ⋙ (quasiIsomorphisms' A).Q).map (F.incl n) ≫
          (toHomotopyCategory A ⋙ (quasiIsomorphisms' A).Q).map (ι (n + 1)) := by
    intro n
    rw [← CategoryTheory.Functor.map_comp, ← CategoryTheory.Functor.map_comp, hα' n,
      CategoryTheory.Functor.map_sub]
  obtain ⟨n, ρ, hρ⟩ := exists_factorThrough_stage_of_distTriang
    (fun m : ℕ => (toHomotopyCategory A ⋙ (quasiIsomorphisms' A).Q).obj (F.F m))
    (fun m => (toHomotopyCategory A ⋙ (quasiIsomorphisms' A).Q).map (F.incl m))
    (fun m => (toHomotopyCategory A ⋙ (quasiIsomorphisms' A).Q).map (ι m)) hcofan ha hδ E f
  refine ⟨n, ρ, ?_⟩
  have hβ' : ι n ≫ β = F.ι n := by
    refine Hom.ext (LinearMap.ext fun x => ?_)
    exact hβ n x
  have hfac : (toHomotopyCategory A ⋙ (quasiIsomorphisms' A).Q).map (ι n) ≫
      (toHomotopyCategory A ⋙ (quasiIsomorphisms' A).Q).map β
      = (toHomotopyCategory A ⋙ (quasiIsomorphisms' A).Q).map (F.ι n) := by
    rw [← CategoryTheory.Functor.map_comp, hβ']
  rw [← hfac]
  exact hρ

end PropertyPStage

/-! ### The filtration of a stage of a property-(P) filtration by the earlier stages -/

section StageFiltration

open scoped ZeroObject

variable {P : DifferentialGradedModule.{u, u, u} A} (F : PropertyPFiltration P)

/-- The stages of a property-(P) filtration, as a system over `ℕ`. -/
private noncomputable abbrev propertyPDiagram : ℕ ⥤ DifferentialGradedModule.{u, u, u} A :=
  Functor.ofSequence fun n => F.incl n

/-- The transition maps of the system of stages are monomorphisms: each inclusion
`F_iP ⟶ F_{i+1}P` of a property-(P) filtration is injective, and monomorphisms compose. -/
private lemma mono_propertyPDiagram_map {i j : ℕ} (h : i ≤ j) :
    Mono ((propertyPDiagram F).map (homOfLE h)) := by
  induction j, h using Nat.le_induction with
  | base =>
    have h1 : (propertyPDiagram F).map (homOfLE (le_refl i)) = 𝟙 _ :=
      CategoryTheory.Functor.map_id _ _
    rw [h1]
    infer_instance
  | succ j hij ih =>
    have hsucc : (propertyPDiagram F).map (homOfLE (le_trans hij (Nat.le_succ j)))
        = (propertyPDiagram F).map (homOfLE hij) ≫
          (propertyPDiagram F).map (homOfLE (Nat.le_succ j)) :=
      (propertyPDiagram F).map_comp _ _
    have h2 : Mono ((propertyPDiagram F).map (homOfLE (Nat.le_succ j))) := by
      have h3 : (propertyPDiagram F).map (homOfLE (Nat.le_succ j)) = F.incl j :=
        Functor.ofSequence_map_homOfLE_succ (X := F.F) F.incl j
      rw [h3]
      exact mono_of_injective _ (F.incl_injective j)
    rw [hsucc]
    infer_instance

/-- Any morphism out of the zero differential graded module is a monomorphism. -/
private lemma mono_from_zero (M : DifferentialGradedModule.{u, u, u} A)
    (f : (0 : DifferentialGradedModule.{u, u, u} A) ⟶ M) : Mono f :=
  ⟨fun g h _ => (isZero_zero (DifferentialGradedModule.{u, u, u} A)).eq_of_tgt g h⟩

/-- **The filtration of the `n`-th stage of a property-(P) filtration by the earlier stages.**
Its `(i + 1)`-st step is the stage `F_{min i n}P`, and its `0`-th step is zero; so it is a finite
filtration, exhausted at `n + 1`, whose successive quotients are the graded pieces of the
property-(P) filtration. -/
private noncomputable abbrev stageFiltration (n : ℕ) : Filtration (F.F n) ℕ := by
  let D := propertyPDiagram F
  let X : ℕ → MonoOver (F.F n) := fun i =>
    match i with
    | 0 => @MonoOver.mk _ _ _ _ (0 : (0 : DifferentialGradedModule.{u, u, u} A) ⟶ F.F n)
        (mono_from_zero (F.F n) 0)
    | i + 1 => @MonoOver.mk _ _ _ _ (D.map (homOfLE (Nat.min_le_right i n)))
        (mono_propertyPDiagram_map F _)
  let t : ∀ i, X i ⟶ X (i + 1) := fun i =>
    match i with
    | 0 => MonoOver.homMk (0 : (0 : DifferentialGradedModule.{u, u, u} A) ⟶ D.obj (min 0 n))
        (by
          change (0 : (0 : DifferentialGradedModule.{u, u, u} A) ⟶ D.obj (min 0 n)) ≫
            D.map (homOfLE (Nat.min_le_right 0 n)) = 0
          exact zero_comp)
    | i + 1 => MonoOver.homMk (D.map (homOfLE (min_le_min_right n (Nat.le_succ i))))
        (by
          change D.map (homOfLE (min_le_min_right n (Nat.le_succ i))) ≫
            D.map (homOfLE (Nat.min_le_right (i + 1) n)) =
              D.map (homOfLE (Nat.min_le_right i n))
          rw [← D.map_comp]
          rfl)
  exact ⟨Functor.ofSequence t⟩

/-- The filtration of a stage starts at zero. -/
private lemma isZero_stageFiltration_obj_zero (n : ℕ) :
    IsZero ((stageFiltration F n).obj 0) := by
  change IsZero (0 : DifferentialGradedModule.{u, u, u} A)
  exact isZero_zero _

/-- The filtration of the `n`-th stage is exhausted at `n + 1`. -/
private lemma isIso_stageFiltration_ι_app (n : ℕ) :
    IsIso ((stageFiltration F n).ι.app (n + 1)) := by
  change IsIso ((propertyPDiagram F).map (homOfLE (Nat.min_le_right n n)))
  have h : ∀ (m : ℕ) (_ : m = n) (hm : m ≤ n),
      IsIso ((propertyPDiagram F).map (homOfLE hm)) := by
    intro m hmn hm
    subst hmn
    change IsIso ((propertyPDiagram F).map (𝟙 m))
    infer_instance
  exact h _ (min_self n) _

/-- The bottom stage of a property-(P) filtration is a direct sum of shifts of the algebra. -/
private noncomputable def propertyPBottomIso :
    F.F 0 ≅ ∐ fun j : F.bottomIndex => shift (regularModule A) (F.bottomShift j) :=
  letI := F.bottomDecidableEq
  Hom.isoOfBijective F.bottomMap F.bottom_bijective ≪≫
    (directSumObjIsoDirectSumShifts A F.bottomShift).symm ≪≫
      directSumObjIsoSigma fun j : F.bottomIndex => shift (regularModule A) (F.bottomShift j)

/-- The graded pieces of a property-(P) filtration are direct sums of shifts of the algebra. -/
private noncomputable def propertyPQuotientIso (i : ℕ) :
    cokernel (F.incl i) ≅
      ∐ fun j : F.quotientIndex i => shift (regularModule A) (F.quotientShift i j) :=
  letI := F.quotientDecidableEq i
  cokernelIsoOfExact (F.incl i) (F.quotientMap i) (F.quotient_surjective i)
      (F.quotientMap_eq_zero_iff i) ≪≫
    (directSumObjIsoDirectSumShifts A (F.quotientShift i)).symm ≪≫
      directSumObjIsoSigma fun j : F.quotientIndex i =>
        shift (regularModule A) (F.quotientShift i j)

/-- The successive quotients of the filtration of a stage by the earlier stages are direct sums of
shifts of the algebra: in degree `0` the bottom stage, and in degree `i + 1` the `i`-th graded
piece of the property-(P) filtration. -/
private lemma exists_stageFiltration_quotients (n : ℕ) :
    ∃ (J : Fin (n + 1) → Type u) (k : ∀ i, J i → ℤ),
      Nonempty (∀ i : Fin (n + 1),
        cokernel ((stageFiltration F n).diagram.map (homOfLE (Nat.le_succ i.val))) ≅
          ∐ fun j : J i => shift (regularModule A) (k i j)) := by
  classical
  let J : Fin (n + 1) → Type u := fun i =>
    match i.val with
    | 0 => F.bottomIndex
    | j + 1 => F.quotientIndex j
  let k : ∀ i : Fin (n + 1), J i → ℤ := fun i =>
    match i with
    | ⟨0, _⟩ => F.bottomShift
    | ⟨j + 1, _⟩ => F.quotientShift j
  refine ⟨J, k, ⟨?_⟩⟩
  rintro ⟨i, hi⟩
  cases i with
  | zero =>
    change cokernel (0 : (0 : DifferentialGradedModule.{u, u, u} A) ⟶ F.F (min 0 n)) ≅ _
    change cokernel (0 : (0 : DifferentialGradedModule.{u, u, u} A) ⟶ F.F 0) ≅
      ∐ fun j : F.bottomIndex => shift (regularModule A) (F.bottomShift j)
    exact cokernelZeroIsoTarget ≪≫ propertyPBottomIso F
  | succ i =>
    simp only [stageFiltration, Filtration.diagram, CategoryTheory.Functor.comp_map,
      Functor.ofSequence_map_homOfLE_succ]
    change cokernel ((propertyPDiagram F).map
      (homOfLE (min_le_min_right n (Nat.le_succ i)))) ≅ _
    have hi' : i + 1 ≤ n := by omega
    have hi'' : i ≤ n := by omega
    refine cokernel.mapIso _ (F.incl i)
      ((propertyPDiagram F).mapIso (eqToIso (min_eq_left hi'')))
      ((propertyPDiagram F).mapIso (eqToIso (min_eq_left hi'))) ?_ ≪≫
        propertyPQuotientIso F i
    have hf : F.incl i = (propertyPDiagram F).map (homOfLE (Nat.le_succ i)) :=
      (Functor.ofSequence_map_homOfLE_succ (X := F.F) F.incl i).symm
    rw [hf]
    change (propertyPDiagram F).map (homOfLE (min_le_min_right n (Nat.le_succ i))) ≫
        (propertyPDiagram F).map (eqToHom (min_eq_left hi')) =
      (propertyPDiagram F).map (eqToHom (min_eq_left hi'')) ≫
        (propertyPDiagram F).map (homOfLE (Nat.le_succ i))
    rw [← CategoryTheory.Functor.map_comp, ← CategoryTheory.Functor.map_comp]
    congr 1

end StageFiltration

/-! ### The characterisation of the compact objects -/

section Characterisation

/-- Every object of `D(A, d)` is isomorphic to the image of a differential graded module carrying
a property-(P) filtration: a property-(P) resolution of a representative (Tag 09KP) becomes an
isomorphism in the derived category. -/
private lemma exists_propertyPFiltration_model (E : derivedCategory' A) :
    ∃ P : DifferentialGradedModule.{u, u, u} A, Nonempty (PropertyPFiltration P) ∧
      Nonempty ((toHomotopyCategory A ⋙ (quasiIsomorphisms' A).Q).obj P ≅ E) := by
  obtain ⟨P, g, hg, hF⟩ :=
    exists_propertyP_resolution A ((((quasiIsomorphisms' A).Q).objPreimage E).as)
  have hq : quasiIsomorphisms' A ((toHomotopyCategory A).map g) :=
    (quasiIsomorphisms_map_iff' A g).2 hg
  have hiso : IsIso ((toHomotopyCategory A ⋙ (quasiIsomorphisms' A).Q).map g) :=
    Localization.inverts ((quasiIsomorphisms' A).Q) (quasiIsomorphisms' A) _ hq
  refine ⟨P, hF, ⟨(asIso ((toHomotopyCategory A ⋙ (quasiIsomorphisms' A).Q).map g)).trans
    (show (toHomotopyCategory A ⋙ (quasiIsomorphisms' A).Q).obj
        ((((quasiIsomorphisms' A).Q).objPreimage E).as) ≅ E from
      ((quasiIsomorphisms' A).Q).objObjPreimageIso E)⟩⟩

/-- A differential graded `A`-module **has a finite cell filtration** when it carries a finite
filtration `0 = F₋₁P ⊆ F₀P ⊆ ⋯ ⊆ FₙP = P` by differential graded submodules whose successive
quotients `F_{i+1}P/FᵢP` are *finite* direct sums of shifts of the algebra.

As in [Stacks, Tag 09R2], the filtration is a `CategoryTheory.Filtration P ℕ` with `F.obj (i + 1)`
playing the role of `FᵢP`, so that its two ends are `IsZero (F.obj 0)` and
`IsIso (F.ι.app (n + 1))`, and the successive quotient is the categorical cokernel of the step. -/
def HasFiniteCellFiltration (P : DifferentialGradedModule.{u, u, u} A) : Prop :=
  ∃ (n : ℕ) (F : Filtration P ℕ),
    IsZero (F.obj 0) ∧ IsIso (F.ι.app (n + 1)) ∧
      ∀ i : Fin (n + 1), ∃ (J : Type u) (_ : Finite J) (k : J → ℤ),
        Nonempty (cokernel (F.diagram.map (homOfLE (Nat.le_succ i.val))) ≅
          ∐ fun j : J => shift (regularModule A) (k j))

/-- A monomorphism of differential graded modules whose categorical cokernel is a direct sum of
shifts of the algebra sits in an admissible short exact sequence with its cokernel projection: the
epimorphism onto a direct sum of shifts splits as a map of graded modules. -/
@[sga "6 I 1.3" "more general"]
theorem isAdmissibleShortExact_cokernelπ {K M : DifferentialGradedModule.{u, u, u} A}
    (i : K ⟶ M) [Mono i] {I : Type u} (k : I → ℤ)
    (e : cokernel i ≅ ∐ fun j => shift (regularModule A) (k j)) :
    IsAdmissibleShortExact i (cokernel.π i) := by
  obtain ⟨s, hs⟩ := isAdmissibleEpi_of_epi_to_coproduct_shifts k (cokernel.π i ≫ e.hom)
  refine { injective := Hom.injective_of_mono A i
           surjective := Hom.surjective_of_epi A (cokernel.π i)
           exact := ?_
           admissibleMono := isAdmissibleMono_of_cokernel_iso_coproduct_shifts i k e
           admissibleEpi := ?_ }
  · refine Submodule.ext fun y => ?_
    constructor
    · rintro ⟨x, rfl⟩
      change (cokernel.π i).toFun (i.toFun x) = 0
      rw [← Hom.comp_toFun_apply, cokernel.condition, Hom.hom_zero_toFun, LinearMap.zero_apply]
    · intro hy
      exact (Hom.mem_range i y).mp (cokernelπ_eq_zero_mem_range i y hy)
  · refine ⟨{ toFun := s.toFun.comp e.hom.toFun
              map_smul := by
                intro x a
                simp only [LinearMap.comp_apply, e.hom.map_smul, s.map_smul]
              map_grading := by
                intro n x hx
                exact s.map_grading n _ (e.hom.map_grading n x hx) }, fun y => ?_⟩
    exact Hom.injective_of_mono A e.hom (hs (e.hom.toFun y))

/-- **The image of a module with a finite cell filtration is a compact object of `D(A, d)`.** The
compact objects are closed under isomorphisms, contain the zero object and are closed under
extensions in distinguished triangles (Tag 09QH), the steps of the filtration are admissible
monomorphisms because their quotients are direct sums of shifts of the algebra, and the images of
the finite direct sums of shifts are compact. -/
private lemma isCompactObject_of_hasFiniteCellFiltration
    {P : DifferentialGradedModule.{u, u, u} A} (hP : HasFiniteCellFiltration P) :
    IsCompactObject.{u} ((toHomotopyCategory A ⋙ (quasiIsomorphisms' A).Q).obj P) := by
  obtain ⟨n, F, hzero, htop, hquot⟩ := hP
  let C : ObjectProperty (derivedCategory' A) := IsCompactObject.{u}
  obtain ⟨hcliso, hcltri, _⟩ :=
    isClosedUnderIsomorphisms_isTriangulated_isSaturated_and_isIdempotentComplete_isCompactObject
      (D := derivedCategory' A)
  have hC₁ : C.IsClosedUnderIsomorphisms := hcliso
  have hC₂ : C.IsTriangulated := hcltri
  have key : ∀ i : ℕ, i ≤ n + 1 →
      C ((toHomotopyCategory A ⋙ (quasiIsomorphisms' A).Q).obj (F.obj i)) := by
    intro i hi
    induction i with
    | zero =>
      exact C.prop_of_isZero
        ((toHomotopyCategory A ⋙ (quasiIsomorphisms' A).Q).map_isZero hzero)
    | succ i ih =>
      obtain ⟨Jq, hJq, kq, ⟨eq⟩⟩ := hquot ⟨i, by omega⟩
      have hses := isAdmissibleShortExact_cokernelπ
        (F.diagram.map (homOfLE (Nat.le_succ i))) kq eq
      have hdist := ((quasiIsomorphisms' A).Q).map_distinguished _
        (associatedTriangle_mem_distTriang A _ _ hses)
      refine C.ext_of_isTriangulatedClosed₂ _ hdist (ih (by omega)) ?_
      exact C.prop_of_iso
        (((toHomotopyCategory A ⋙ (quasiIsomorphisms' A).Q).mapIso eq).symm)
        (isCompactObject_toDerivedCategory_coproduct_shifts kq)
  have htop' : IsIso ((toHomotopyCategory A ⋙ (quasiIsomorphisms' A).Q).map
      (F.ι.app (n + 1))) := inferInstance
  exact C.prop_of_iso
    (asIso ((toHomotopyCategory A ⋙ (quasiIsomorphisms' A).Q).map (F.ι.app (n + 1))))
    (key (n + 1) le_rfl)

/-- A morphism of `D(A, d)` out of a compact object into the image of a module with a finite
filtration whose quotients are direct sums of shifts of the algebra factors through the image of a
submodule with a *finite* cell filtration. This is [Stacks, Tag 09R2] with its conclusion read as
`DifferentialGradedModule.HasFiniteCellFiltration`. -/
private lemma exists_factorThrough_hasFiniteCellFiltration
    (A' : DifferentialGradedAlgebra.{u, u} R) (n : ℕ)
    (P : DifferentialGradedModule.{u, u, u} A') (F : Filtration P ℕ)
    (hzero : IsZero (F.obj 0)) (htop : IsIso (F.ι.app (n + 1)))
    (J : Fin (n + 1) → Type u) (k : ∀ i, J i → ℤ)
    (e : ∀ i : Fin (n + 1), cokernel (F.diagram.map (homOfLE (Nat.le_succ i.val))) ≅
      ∐ fun j : J i => shift (regularModule A') (k i j))
    (E : derivedCategory' A') [IsCompactObject.{u} E]
    (f : E ⟶ (toHomotopyCategory A' ⋙ (quasiIsomorphisms' A').Q).obj P) :
    ∃ (P' : DifferentialGradedModule.{u, u, u} A') (p : P' ⟶ P), HasFiniteCellFiltration P' ∧
      ∃ g : E ⟶ (toHomotopyCategory A' ⋙ (quasiIsomorphisms' A').Q).obj P',
        g ≫ (toHomotopyCategory A' ⋙ (quasiIsomorphisms' A').Q).map p = f := by
  obtain ⟨P', p, hp, F', β, hpb, ⟨J', e', q, hq, he⟩, g, hg⟩ :=
    exists_factorThrough_finiteSubfiltration A' n P F hzero htop J k e E f
  have hmonop : Mono p := hp
  refine ⟨P', p, ⟨n, F', ?_, (hpb (n + 1)).isIso_fst_of_isIso htop, ?_⟩, g, hg⟩
  · have hm : Mono (β 0) := (hpb 0).mono_snd_of_mono
    refine (IsZero.iff_id_eq_zero _).mpr ?_
    exact (cancel_mono (β 0)).mp (hzero.eq_of_tgt _ _)
  · intro i
    exact ⟨↑(J' i), inferInstance, fun j => k i j.val, ⟨e' i⟩⟩

/-- **A compact object of `D(A, d)` is a retract of the image of a module with a finite cell
filtration.** Replace the object by the image of a module `P` with a property-(P) filtration
(Tag 09KP); the morphism `E ⟶ P` inverse to that identification factors through a stage `FₙP`
(Tag 094A), and then through a differential graded submodule of `FₙP` with a finite cell
filtration (Tag 09R2). -/
private lemma exists_retract_hasFiniteCellFiltration_of_isCompactObject
    (E : derivedCategory' A) [IsCompactObject.{u} E] :
    ∃ P : DifferentialGradedModule.{u, u, u} A, HasFiniteCellFiltration P ∧
      ∃ (i : E ⟶ (toHomotopyCategory A ⋙ (quasiIsomorphisms' A).Q).obj P)
        (r : (toHomotopyCategory A ⋙ (quasiIsomorphisms' A).Q).obj P ⟶ E), i ≫ r = 𝟙 E := by
  obtain ⟨P, ⟨F⟩, ⟨eiso⟩⟩ := exists_propertyPFiltration_model E
  obtain ⟨n, g, hg⟩ := exists_factorThrough_propertyPFiltration_stage F E eiso.inv
  obtain ⟨J, k, ⟨a⟩⟩ := exists_stageFiltration_quotients F n
  obtain ⟨P', p, hP', g', hg'⟩ := exists_factorThrough_hasFiniteCellFiltration A n (F.F n)
    (stageFiltration F n) (isZero_stageFiltration_obj_zero F n)
    (isIso_stageFiltration_ι_app F n) J k a E g
  refine ⟨P', hP', g',
    (toHomotopyCategory A ⋙ (quasiIsomorphisms' A).Q).map p ≫
      (toHomotopyCategory A ⋙ (quasiIsomorphisms' A).Q).map (F.ι n) ≫ eiso.hom, ?_⟩
  rw [← Category.assoc, hg', ← Category.assoc, hg, eiso.inv_hom_id]

/-- **Stacks Tag 09R3.** *"Let `(A, d)` be a differential graded algebra. Let `E` be an object of
`D(A, d)`. The following are equivalent: (1) `E` is a compact object, and (2) `E` is a direct
summand of an object which is represented by a differential graded module `P` which has a finite
filtration `F_•` by differential graded submodules such that `F_iP/F_{i-1}P` are finite direct
sums of shifts of `A`."*

Condition (2) is read as: `E` is a retract of the image of a module with a finite cell filtration,
`DifferentialGradedModule.HasFiniteCellFiltration`. A retract is the same thing as a direct
summand here, the derived category of a differential graded algebra being idempotent complete
([Stacks, Tag 05QW]); the retract formulation is the one both implications produce and consume. -/
@[stacks 09R3]
theorem isCompactObject_iff_exists_retract_hasFiniteCellFiltration
    (A : DifferentialGradedAlgebra.{u, u} R) (E : derivedCategory' A) :
    IsCompactObject.{u} E ↔
      ∃ P : DifferentialGradedModule.{u, u, u} A, HasFiniteCellFiltration P ∧
        ∃ (i : E ⟶ (toHomotopyCategory A ⋙ (quasiIsomorphisms' A).Q).obj P)
          (r : (toHomotopyCategory A ⋙ (quasiIsomorphisms' A).Q).obj P ⟶ E), i ≫ r = 𝟙 E := by
  constructor
  · intro hE
    exact exists_retract_hasFiniteCellFiltration_of_isCompactObject E
  · rintro ⟨P, hP, i, r, hir⟩
    exact isCompactObject_of_retract (isCompactObject_of_hasFiniteCellFiltration hP) i r hir

end Characterisation

end DifferentialGradedModule

end
