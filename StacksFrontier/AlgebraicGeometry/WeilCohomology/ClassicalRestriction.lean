module

public import StacksFrontier.AlgebraicGeometry.WeilCohomology.ClassicalChowCycleData
public import StacksFrontier.AlgebraicGeometry.WeilCohomology.ClassicalKunnethTrace
public import StacksFrontier.AlgebraicGeometry.WeilCohomology.ClassicalTheoryPairing
public import StacksFrontier.AlgebraicGeometry.WeilCohomology.Concrete.ClosedImmersionClass
public import StacksFrontier.AlgebraicGeometry.WeilCohomology.Concrete.CohomologyOfPoint
public import StacksFrontier.AlgebraicGeometry.WeilCohomology.Concrete.WeilDataAxioms
public import StacksFrontier.AlgebraicGeometry.WeilCohomology.Concrete.WeilDataCoordinates
public import StacksFrontier.AlgebraicGeometry.Morphisms.Projective.AffineBase
public import StacksFrontier.AlgebraicGeometry.WeilCohomology.Correspondences.SmoothProjectiveComposition

/-!
# Restricting Weil data to smooth projective varieties

Data (D0)–(D3) satisfying (A), (B), (C) (Section 45.9, Tag 0FHA) are given on all smooth
projective schemes over `k`, with values in Tate twists. Over an algebraically closed field `k`
their restriction to the smooth projective varieties, read in a coordinate of the Tate line
`F(1)`, is a classical Weil cohomology theory except possibly for axioms (A)(c) and (A)(d)
(`Stacks.WeilCohomology.PreClassicalWeilCohomologyTheory`, the conclusion of Stacks 0FH1).

## Main definitions

* `ExternallyGradedAlgebra.ofGradedAlgebra`: the externally graded algebra of the pieces of a
  graded algebra.
* `Stacks.WeilCohomology.SmoothProjective.dim`: the dimension of a smooth projective variety.
* `Stacks.WeilCohomology.WeilDataAxioms.toPoincarePairingSetup`,
  `Stacks.WeilCohomology.WeilDataAxioms.toPreClassical`: the restriction.

## Implementation notes

The cohomology of a variety `X` is `H^n(X) = W.grade X n`, its pullbacks are `W.pullDeg` and its
cup product is `W.cup`, all by definition. The cycle class and trace maps are the coordinate
forms `W.cycleClassCoord` and `W.traceCoord`, read in the coordinate of `F(1)` with which the
twisted cup products are defined (`WeilData.twCoord`).

## References

* [Stacks Project, Tag 0FH1](https://stacks.math.columbia.edu/tag/0FH1)
* [Stacks Project, Section 45.9 (Tag 0FHA)](https://stacks.math.columbia.edu/tag/0FHA)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry Stacks.Chow
open scoped DirectSum TensorProduct

universe u v w

/-! ### The externally graded algebra of a graded algebra -/

namespace ExternallyGradedAlgebra

variable {F : Type v} [Field F] {A : Type w} [Ring A] [Algebra F A] (𝒜 : ℤ → Submodule F A)
  [GradedAlgebra 𝒜]

omit [GradedAlgebra 𝒜] in
/-- Homogeneous elements of equal degrees with equal values are heterogeneously equal. -/
theorem heq_of_coe_eq {i j : ℤ} (h : i = j) {a : 𝒜 i} {b : 𝒜 j} (hab : (a : A) = b) :
    a ≍ b := by
  subst h
  exact heq_of_eq (Subtype.ext hab)

/-- The externally graded algebra `n ↦ 𝒜 n` of the pieces of a graded algebra `𝒜`. -/
abbrev ofGradedAlgebra : ExternallyGradedAlgebra.{v, w} F where
  piece n := 𝒜 n
  mul _ _ := LinearMap.mk₂ F (fun a b ↦ ⟨a * b, SetLike.GradedMul.mul_mem a.2 b.2⟩)
    (fun _ _ _ ↦ Subtype.ext (add_mul _ _ _)) (fun _ _ _ ↦ Subtype.ext (smul_mul_assoc _ _ _))
    (fun _ _ _ ↦ Subtype.ext (mul_add _ _ _)) (fun _ _ _ ↦ Subtype.ext (mul_smul_comm _ _ _))
  one := ⟨1, SetLike.GradedOne.one_mem⟩
  mul_assoc i j l a b c := heq_of_coe_eq 𝒜 (add_assoc i j l) (_root_.mul_assoc (a : A) b c)
  one_mul i a := heq_of_coe_eq 𝒜 (zero_add i) (_root_.one_mul (a : A))
  mul_one i a := heq_of_coe_eq 𝒜 (add_zero i) (_root_.mul_one (a : A))

variable {𝒜}

/-- The product in `ofGradedAlgebra 𝒜` is the product in `A`. -/
@[simp]
theorem coe_ofGradedAlgebra_mul {i j : ℤ} (a : 𝒜 i) (b : 𝒜 j) :
    (((ofGradedAlgebra 𝒜).mul i j a b : 𝒜 (i + j)) : A) = a * b :=
  rfl

/-- The unit of `ofGradedAlgebra 𝒜` is the unit `1` of `A`. -/
@[simp]
theorem coe_ofGradedAlgebra_one : (((ofGradedAlgebra 𝒜).one : 𝒜 0) : A) = 1 :=
  rfl

omit [GradedAlgebra 𝒜] in
/-- Transport between pieces of equal degree does not change the underlying element. -/
@[simp]
theorem coe_degreeCast {i j : ℤ} (h : i = j) (a : 𝒜 i) :
    ((ExternallyGraded.degreeCast (R := F) (X := fun n ↦ 𝒜 n) h a : 𝒜 j) : A) = a := by
  subst h
  rfl

/-- The externally graded algebra of a graded algebra satisfying the Koszul sign rule is graded
commutative. -/
theorem ofGradedAlgebra_isGradedCommutative
    (h : ∀ (i j : ℤ) (a b : A), a ∈ 𝒜 i → b ∈ 𝒜 j → a * b = (Int.negOnePow (i * j) : ℤ) • (b * a)) :
    (ofGradedAlgebra 𝒜).IsGradedCommutative where
  graded_comm i j a b := by
    refine heq_of_coe_eq 𝒜 (add_comm i j) ?_
    rw [Submodule.coe_smul, coe_ofGradedAlgebra_mul, coe_ofGradedAlgebra_mul, h i j a b a.2 b.2,
      ← DifferentialGraded.intCast_negOnePow, Int.cast_smul_eq_zsmul]

end ExternallyGradedAlgebra

namespace Stacks.WeilCohomology

/-! ### The dimension of a smooth projective variety -/

namespace SmoothProjective

variable {k : Type u} [Field k]

/-- The dimension of a smooth projective variety: its structure morphism, smooth with irreducible
source, has pure relative dimension, which is the dimension of the underlying space. -/
def dim (X : (SmoothProjective k).FullSubcategory) : ℕ :=
  (exists_relativeDimension_of_smooth_of_preconnectedSpace X.obj.hom).choose

/-- The structure morphism of a smooth projective variety `X` has pure relative dimension
`dim X`. -/
theorem relativeDimension_dim (X : (SmoothProjective k).FullSubcategory) :
    RelativeDimension X.obj.hom (dim X) :=
  (exists_relativeDimension_of_smooth_of_preconnectedSpace X.obj.hom).choose_spec

/-- The Krull dimension of the underlying space of a smooth projective variety `X` is `dim X`. -/
theorem topologicalKrullDim_eq_dim (X : (SmoothProjective k).FullSubcategory) :
    topologicalKrullDim X.obj.left = (dim X : WithBot ℕ∞) :=
  topologicalKrullDim_eq_of_relativeDimension X.obj.hom (relativeDimension_dim X)

/-- A smooth projective variety `X` is nonempty and equidimensional of dimension `dim X`. -/
theorem isNonemptyEquidimensional_dim (X : (SmoothProjective k).FullSubcategory) :
    IsNonemptyEquidimensional ((toSchemeCat k).obj X) (dim X) :=
  isNonemptyEquidimensional X (topologicalKrullDim_eq_dim X)

end SmoothProjective

/-! ### Fibre products of varieties -/

namespace SmoothProjective

variable {k : Type u} [Field k] {X Y P : (SmoothProjective k).FullSubcategory} {p : P ⟶ X}
  {q : P ⟶ Y}

/-- A fibre product `P` of smooth projective varieties `X` and `Y` over `k` is isomorphic to the
product `X × Y` of smooth projective schemes. -/
def isoProdOfIsPullback (hP : IsPullback p.hom.left q.hom.left X.obj.hom Y.obj.hom) :
    (toSchemeCat k).obj P ≅
      SmoothProjectiveScheme.prod ((toSchemeCat k).obj X) ((toSchemeCat k).obj Y) where
  hom := ObjectProperty.homMk (Over.homMk hP.isoPullback.hom (by
    change hP.isoPullback.hom ≫ pullback.fst X.obj.hom Y.obj.hom ≫ X.obj.hom = P.obj.hom
    rw [IsPullback.isoPullback_hom_fst_assoc, Over.w p.hom]))
  inv := ObjectProperty.homMk (Over.homMk hP.isoPullback.inv (by
    change hP.isoPullback.inv ≫ P.obj.hom = pullback.fst X.obj.hom Y.obj.hom ≫ X.obj.hom
    rw [← Over.w p.hom, IsPullback.isoPullback_inv_fst_assoc]))
  hom_inv_id := ObjectProperty.hom_ext _ (Over.OverMorphism.ext hP.isoPullback.hom_inv_id)
  inv_hom_id := ObjectProperty.hom_ext _ (Over.OverMorphism.ext hP.isoPullback.inv_hom_id)

/-- The isomorphism `isoProdOfIsPullback hP` followed by the first projection is `p`. -/
theorem isoProdOfIsPullback_hom_fst (hP : IsPullback p.hom.left q.hom.left X.obj.hom Y.obj.hom) :
    (isoProdOfIsPullback hP).hom ≫ SmoothProjectiveScheme.fst _ _ = (toSchemeCat k).map p :=
  ObjectProperty.hom_ext _ (Over.OverMorphism.ext hP.isoPullback_hom_fst)

/-- The isomorphism `isoProdOfIsPullback hP` followed by the second projection is `q`. -/
theorem isoProdOfIsPullback_hom_snd (hP : IsPullback p.hom.left q.hom.left X.obj.hom Y.obj.hom) :
    (isoProdOfIsPullback hP).hom ≫ SmoothProjectiveScheme.snd _ _ = (toSchemeCat k).map q :=
  ObjectProperty.hom_ext _ (Over.OverMorphism.ext hP.isoPullback_hom_snd)

end SmoothProjective

/-! ### The axioms of Weil data in coordinates -/

namespace WeilData

variable {k : Type u} [Field k] {F : Type w} [Field F] {W : WeilData k F}

/-- **Axiom (A)(b) read in coordinates**: the pairings `(a, b) ↦ tr_X(a ∪ b)` are perfect. -/
theorem PerfectPairing.coord (hA : W.PerfectPairing)
    (X : (SmoothProjectiveScheme k).FullSubcategory) (d : ℕ)
    (hX : IsNonemptyEquidimensional X d) (i j : ℤ) (h : i + j = 2 * d) :
    ((W.cup X i j _ h).compr₂ (W.traceCoord X d hX)).IsPerfPair := by
  have := hA.pairingTw X d hX i j h 0 d (zero_add _)
  refine LinearMap.IsPerfPair.congr (p := W.pairingTw X d hX i j h 0 d (zero_add _))
    (W.twCoord X i 0).symm (W.twCoord X j d).symm _ ?_
  refine LinearMap.ext fun a ↦ LinearMap.ext fun b ↦ ?_
  simp only [LinearMap.compl₁₂_apply, LinearMap.compr₂_apply, LinearEquiv.coe_coe,
    LinearEquiv.symm_symm]
  exact (W.pairingTw_eq_traceCoord X d hX i j h 0 d _ a b).symm

/-- **Axiom (C)(a) read in coordinates**: `γ(f^!β) = f^*γ(β)`. -/
theorem cycleClassCoord_gysin (hC : W.CycleClassPullback)
    {X Y : (SmoothProjectiveScheme k).FullSubcategory}
    (f : X ⟶ Y) (i : ℤ) (β : codimensionChowGroup k Y.obj.hom i) :
    W.cycleClassCoord X i (codimensionGysin X.obj.hom Y.obj.hom (Over.w f.hom) i β) =
      W.pullDeg f _ (W.cycleClassCoord Y i β) := by
  rw [cycleClassCoord_apply, cycleClassCoord_apply, hC f i β, twCoord_pullTw]

/-- **Axiom (C)(c) read in coordinates**: `γ(α · β) = γ(α) ∪ γ(β)`. -/
theorem cycleClassCoord_mul (hC : W.CycleClassMul)
    (X : (SmoothProjectiveScheme k).FullSubcategory) (i j : ℤ)
    (α : codimensionChowGroup k X.obj.hom i) (β : codimensionChowGroup k X.obj.hom j) :
    W.cycleClassCoord X (i + j) (codimensionIntersectionProduct k X.obj.hom i j α β) =
      W.cup X (2 * i) (2 * j) _ (by ring) (W.cycleClassCoord X i α) (W.cycleClassCoord X j β) := by
  rw [cycleClassCoord_apply, hC X i j α β, twCoord_cupTw]
  rfl

/-- **Axiom (C)(d) read in coordinates**: `tr_{Spec k} γ([Spec k]) = 1`. -/
theorem traceCoord_cycleClassCoord_point (hC : W.CycleClassPoint) :
    W.traceCoord (SmoothProjectiveScheme.point k) 0 isNonemptyEquidimensional_point
      (W.cycleClassCoord (SmoothProjectiveScheme.point k) 0
        (fundamentalClass (SmoothProjectiveScheme.point k))) = 1 := by
  rw [← hC, trace_eq_traceCoord]
  rfl

/-- **Axiom (C)(b) read in coordinates**: for `f : X ⟶ Y` of nonempty equidimensional schemes of
dimensions `d` and `e` and `α ∈ CH^p(X)`, `tr_X(f^*b ∪ γ(α)) = tr_Y(b ∪ γ(f_*α))` for all `b` of
complementary degree. -/
theorem traceCoord_cup_cycleClassCoord_pushforward (hA : W.PerfectPairing)
    (hC : W.CycleClassPushforward hA) {X Y : (SmoothProjectiveScheme k).FullSubcategory}
    (f : X ⟶ Y) (d e : ℕ)
    (hX : IsNonemptyEquidimensional X d) (hY : IsNonemptyEquidimensional Y e) (p q : ℤ)
    (hpq : q = p + e - d) (α : codimensionChowGroup k X.obj.hom p) (i : ℤ)
    (hi : i + 2 * p = 2 * d) (hi' : i + 2 * q = 2 * e) (b : W.grade Y i) :
    W.traceCoord X d hX (W.cup X i (2 * p) _ hi (W.pullDeg f i b) (W.cycleClassCoord X p α)) =
      W.traceCoord Y e hY (W.cup Y i (2 * q) _ hi' b
        (W.cycleClassCoord Y q (equidimensionalPushforward f d e p q hpq α))) := by
  have hs : (e - q) + p = (d : ℤ) := by omega
  have hs' : (e - q) + q = (e : ℤ) := by omega
  set b' := (W.twCoord Y i (e - q)).symm b
  have h1 := W.pushforward_trace' hA f hX hY (2 * p) p (2 * q) q (by omega) (by omega) i (e - q)
    hi hs hi' hs' b' (W.cycleClass X p α)
  rw [← hC f d e hX hY p q hpq α, pairingTw_eq_traceCoord, pairingTw_eq_traceCoord,
    twCoord_pullTw] at h1
  simp only [b', LinearEquiv.apply_symm_apply] at h1
  exact h1

end WeilData

/-! ### The restriction -/

namespace WeilDataAxioms

open SmoothProjective (toSchemeCat)

variable {k : Type u} [Field k] [IsAlgClosed k] {F : Type w} [Field F] [CharZero F]
  (W : WeilDataAxioms k F)

omit [IsAlgClosed k] [CharZero F] in
/-- The trace pairing of `H^*(X) = W.grade X` is the pairing `(a, b) ↦ tr_X(a ∪ b)` of the
coordinate trace. -/
theorem tracePairing_ofGradedAlgebra (X : (SmoothProjectiveScheme k).FullSubcategory) (d : ℕ)
    (hX : IsNonemptyEquidimensional X d) (i : ℤ) :
    (ExternallyGradedAlgebra.ofGradedAlgebra (W.grade X)).tracePairing d
        (W.traceCoord X d hX) i =
      (W.cup X i (2 * (d : ℤ) - i) _ (by omega)).compr₂ (W.traceCoord X d hX) := by
  ext a b
  simp only [ExternallyGradedAlgebra.tracePairing, LinearMap.compr₂_apply, LinearMap.comp_apply]
  congr 1
  apply Subtype.ext
  rw [ExternallyGradedAlgebra.coe_degreeCast, ExternallyGradedAlgebra.coe_ofGradedAlgebra_mul,
    WeilData.coe_cup]

/-- The data `(D1)`, `(D3)` of a classical Weil cohomology theory with axioms `(A)(a)`, `(A)(b)`,
restricted from Weil data: `H^n(X) = W.grade X n` for a smooth projective variety `X`, pullback
`W.pullDeg`, and the trace `∫_X` read in coordinates. -/
abbrev toPoincarePairingSetup : PoincarePairingSetup.{u, w, w} k F where
  H X := ExternallyGradedAlgebra.ofGradedAlgebra (W.grade ((SmoothProjective.toSchemeCat k).obj X))
  gradedComm X := ExternallyGradedAlgebra.ofGradedAlgebra_isGradedCommutative (W.graded_comm _)
  dimension := SmoothProjective.dim
  dimension_eq := SmoothProjective.topologicalKrullDim_eq_dim
  pullback f i := W.pullDeg ((SmoothProjective.toSchemeCat k).map f) i
  pullback_id X i := by
    ext a
    rw [WeilData.coe_pullDeg, CategoryTheory.Functor.map_id, W.pull_id]
    rfl
  pullback_comp f g i := by
    ext a
    rw [WeilData.coe_pullDeg, CategoryTheory.Functor.map_comp, W.pull_comp]
    rfl
  pullback_one f := Subtype.ext (map_one (W.pull _))
  pullback_mul f i j a b := Subtype.ext (map_mul (W.pull _) _ _)
  integration X := W.traceCoord _ (SmoothProjective.dim X)
    (SmoothProjective.isNonemptyEquidimensional_dim X)
  finite X i := W.poincareDuality.finiteDimensionality _ _
    (SmoothProjective.isNonemptyEquidimensional_dim X) i
  perfect X i := by
    rw [tracePairing_ofGradedAlgebra]
    exact W.poincareDuality.perfectPairing.coord _ _ _ _ _ _

omit [IsAlgClosed k] [CharZero F] in
/-- Pullback along an isomorphism is bijective. -/
theorem bijective_pull_of_iso {X Y : (SmoothProjectiveScheme k).FullSubcategory} (e : X ≅ Y) :
    Function.Bijective (W.pull e.hom) := by
  refine Function.bijective_iff_has_inverse.2 ⟨W.pull e.inv, fun a ↦ ?_, fun a ↦ ?_⟩ <;>
    simp [← AlgHom.comp_apply, ← W.pull_comp, W.pull_id]

/-- **The Künneth axiom (B)(a) on a fibre product of varieties**: for a fibre product `P` of
smooth projective varieties `X`, `Y`, the map `H^*(X) ⊗ H^*(Y) → H^*(P)`,
`a ⊗ b ↦ p^*a ∪ q^*b`, of the restriction is bijective. -/
theorem bijective_kunnethMap {X Y P : (SmoothProjective k).FullSubcategory} (p : P ⟶ X)
    (q : P ⟶ Y) (hP : IsPullback p.hom.left q.hom.left X.obj.hom Y.obj.hom) :
    Function.Bijective (kunnethMap (W.toPoincarePairingSetup.H X) (W.toPoincarePairingSetup.H Y)
      (W.toPoincarePairingSetup.H P) (fun i ↦ W.toPoincarePairingSetup.pullback p i)
      fun j ↦ W.toPoincarePairingSetup.pullback q j) := by
  let e := SmoothProjective.isoProdOfIsPullback hP
  let dX := DirectSum.decomposeLinearEquiv (W.grade ((toSchemeCat k).obj X))
  let dY := DirectSum.decomposeLinearEquiv (W.grade ((toSchemeCat k).obj Y))
  let dP := DirectSum.decomposeLinearEquiv (W.grade ((toSchemeCat k).obj P))
  let g : ((⨁ i : ℤ, (W.toPoincarePairingSetup.H X).piece i) ⊗[F]
      ⨁ j : ℤ, (W.toPoincarePairingSetup.H Y).piece j) →ₗ[F]
        ⨁ n : ℤ, (W.toPoincarePairingSetup.H P).piece n :=
    dP.toLinearMap ∘ₗ (W.pull e.hom).toLinearMap ∘ₗ
      W.kunnethMap ((toSchemeCat k).obj X) ((toSchemeCat k).obj Y) ∘ₗ
        (TensorProduct.congr dX.symm dY.symm).toLinearMap
  suffices key : kunnethMap (W.toPoincarePairingSetup.H X) (W.toPoincarePairingSetup.H Y)
      (W.toPoincarePairingSetup.H P) (fun i ↦ W.toPoincarePairingSetup.pullback p i)
      (fun j ↦ W.toPoincarePairingSetup.pullback q j) = g by
    rw [key]
    exact dP.bijective.comp ((W.bijective_pull_of_iso e).comp
      ((W.kunneth.kunnethIsomorphism _ _).comp (TensorProduct.congr _ _).bijective))
  refine TensorProduct.ext' fun x y ↦ ?_
  induction x using DirectSum.induction_on with
  | zero => rw [TensorProduct.zero_tmul, map_zero, map_zero]
  | add x x' hx hx' => rw [TensorProduct.add_tmul, map_add, map_add, hx, hx']
  | of i a =>
    induction y using DirectSum.induction_on with
    | zero => rw [TensorProduct.tmul_zero, map_zero, map_zero]
    | add y y' hy hy' => rw [TensorProduct.tmul_add, map_add, map_add, hy, hy']
    | of j b =>
      rw [← DirectSum.lof_eq_of F, ← DirectSum.lof_eq_of F, kunnethMap_lof_tmul_lof]
      have hval : W.pull e.hom (W.kunnethMap ((toSchemeCat k).obj X) ((toSchemeCat k).obj Y)
          ((a : W.H ((toSchemeCat k).obj X)) ⊗ₜ (b : W.H ((toSchemeCat k).obj Y)))) =
          ((W.toPoincarePairingSetup.H P).mul i j (W.toPoincarePairingSetup.pullback p i a)
            (W.toPoincarePairingSetup.pullback q j b) : W.H ((toSchemeCat k).obj P)) := by
        rw [WeilData.kunnethMap_tmul, map_mul, ← AlgHom.comp_apply, ← AlgHom.comp_apply,
          ← W.pull_comp, ← W.pull_comp, SmoothProjective.isoProdOfIsPullback_hom_fst,
          SmoothProjective.isoProdOfIsPullback_hom_snd]
        rfl
      simp only [g, dX, dY, dP, LinearMap.coe_comp, Function.comp_apply, LinearEquiv.coe_coe,
        TensorProduct.congr_tmul, DirectSum.decomposeLinearEquiv_symm_apply,
        DirectSum.decomposeLinearEquiv_apply, DirectSum.lof_eq_of, DirectSum.decompose_symm_of,
        AlgHom.toLinearMap_apply]
      rw [hval, DirectSum.decompose_coe]

omit [IsAlgClosed k] [CharZero F] in
/-- `γ` of the class of `X` has trace `1` when `X ≅ Spec k`: by axiom (C)(b) for `X ⟶ Spec k`,
which carries `[X]` to `[Spec k]`, and axiom (C)(d). -/
theorem traceCoord_cycleClassCoord_fundamentalClass_of_isIso
    (X : (SmoothProjectiveScheme k).FullSubcategory)
    [IsIso X.obj.hom] (hX : IsNonemptyEquidimensional X 0) :
    W.traceCoord X 0 hX (W.cycleClassCoord X 0 (fundamentalClass X)) = 1 := by
  have : IsIso (SmoothProjectiveScheme.toPoint X).hom.left :=
    inferInstanceAs (IsIso X.obj.hom)
  have hpt := isNonemptyEquidimensional_point (k := k)
  have hfund : equidimensionalPushforward (SmoothProjectiveScheme.toPoint X) 0 0 0 0
      (by norm_num) (fundamentalClass X) =
        fundamentalClass (SmoothProjectiveScheme.point k) := by
    rw [equidimensionalPushforward_fundamentalClass _ hX hpt,
      WeilData.closedSubschemeClass_of_isIso _ hpt.relativeDimension]
  have h := WeilData.traceCoord_cup_cycleClassCoord_pushforward W.poincareDuality.perfectPairing
    W.cycleClassAxiom.pushforward (SmoothProjectiveScheme.toPoint X) 0 0 hX hpt 0 0
    (by norm_num) (fundamentalClass X) 0 (by norm_num) (by norm_num) ⟨1, SetLike.GradedOne.one_mem⟩
  rw [hfund] at h
  have h1 : W.cup X 0 (2 * 0) (2 * (0 : ℕ)) (by norm_num)
      (W.pullDeg (SmoothProjectiveScheme.toPoint X) 0 ⟨1, SetLike.GradedOne.one_mem⟩)
      (W.cycleClassCoord X 0 (fundamentalClass X)) = W.cycleClassCoord X 0 (fundamentalClass X) :=
    Subtype.ext (by simp)
  have h2 : W.cup (SmoothProjectiveScheme.point k) 0 (2 * 0) (2 * (0 : ℕ)) (by norm_num)
      ⟨1, SetLike.GradedOne.one_mem⟩ (W.cycleClassCoord (SmoothProjectiveScheme.point k) 0
        (fundamentalClass (SmoothProjectiveScheme.point k))) =
      W.cycleClassCoord (SmoothProjectiveScheme.point k) 0
        (fundamentalClass (SmoothProjectiveScheme.point k)) :=
    Subtype.ext (by simp)
  rw [h1, h2, WeilData.traceCoord_cycleClassCoord_point W.cycleClassAxiom.point] at h
  exact h

/-- **The restriction of Weil data to smooth projective varieties**, over an algebraically closed
field `k`: data `(D1)`, `(D2)`, `(D3)` satisfying all of `(A)`, `(B)`, `(C)` except possibly
`(A)(c)` and `(A)(d)`, with `H^n(X) = W.grade X n`, pullback `W.pullDeg`, cup product `W.cup`, and
the cycle class and trace maps read in the coordinate of `F(1)`. -/
def toPreClassical : PreClassicalWeilCohomologyTheory.{u, w, w, u} k F (chowCycleData k) where
  toPoincarePairingSetup := W.toPoincarePairingSetup
  cycleClass X r := W.cycleClassCoord ((SmoothProjective.toSchemeCat k).obj X) r
  kunneth X Y P p q hP := W.bijective_kunnethMap p q hP
  cycleClass_gysin f r β :=
    WeilData.cycleClassCoord_gysin W.cycleClassAxiom.pullback ((toSchemeCat k).map f) r β
  cycleClass_pushforward {X Y} f r α := by
    set S := W.toPoincarePairingSetup
    have := S.perfect Y (2 * (S.dimension X : ℤ) - 2 * r)
    apply (LinearMap.IsPerfPair.bijective_right ((S.H Y).tracePairing (S.dimension Y)
      (S.integration Y) (2 * (S.dimension X : ℤ) - 2 * r))).injective
    refine LinearMap.ext fun b ↦ ?_
    rw [LinearMap.flip_apply, LinearMap.flip_apply, ← S.integration_pullback_mul]
    simp only [S, tracePairing_ofGradedAlgebra, LinearMap.compr₂_apply]
    have h := WeilData.traceCoord_cup_cycleClassCoord_pushforward W.poincareDuality.perfectPairing
      W.cycleClassAxiom.pushforward ((SmoothProjective.toSchemeCat k).map f) _ _
      (SmoothProjective.isNonemptyEquidimensional_dim X)
      (SmoothProjective.isNonemptyEquidimensional_dim Y) r _ rfl α _ (by ring) (by ring) b
    convert h using 2 <;> exact Subtype.ext (by simp; rfl)
  cycleClass_mul X r s α β := by
    refine (WeilData.cycleClassCoord_mul W.cycleClassAxiom.mul _ r s α β).trans (Subtype.ext ?_)
    simp [ExternallyGradedAlgebra.evenCup]
    rfl
  integration_cycleClass_fundamental X hX h0 := by
    have : IsIso ((SmoothProjective.toSchemeCat k).obj X).obj.hom := hX
    have key : ∀ (d : ℕ) (hd : IsNonemptyEquidimensional ((SmoothProjective.toSchemeCat k).obj X) d)
        (h : 2 * (0 : ℤ) = 2 * (d : ℤ)), d = 0 →
        W.traceCoord _ d hd (ExternallyGraded.degreeCast (R := F)
          (X := fun n ↦ W.grade ((SmoothProjective.toSchemeCat k).obj X) n) h
          (W.cycleClassCoord _ 0 (fundamentalClass _))) = 1 := by
      rintro d hd h rfl
      rw [← W.traceCoord_cycleClassCoord_fundamentalClass_of_isIso _ hd]
      exact congrArg _ (Subtype.ext (by simp))
    exact key _ _ _ h0

/-- The data `(D1)`, `(D3)` of `W.toPreClassical` are `W.toPoincarePairingSetup`. -/
@[simp]
theorem toPreClassical_toPoincarePairingSetup :
    W.toPreClassical.toPoincarePairingSetup = W.toPoincarePairingSetup :=
  rfl

/-- The cycle class map of `W.toPreClassical` in codimension `r` is `W.cycleClassCoord` on the
underlying scheme. -/
theorem toPreClassical_cycleClass (X : (SmoothProjective k).FullSubcategory) (r : ℤ) :
    W.toPreClassical.cycleClass X r = W.cycleClassCoord ((toSchemeCat k).obj X) r :=
  rfl

end WeilDataAxioms


end Stacks.WeilCohomology

end
