module

public import StacksCore.Tactic.StacksAttribute
public import StacksFrontier.Algebra.DifferentialGraded.Module.DerivedEquivalenceBimodule
public import StacksFrontier.Algebra.DifferentialGraded.Module.DerivedEquivalenceRegularImage
public import StacksFrontier.Algebra.DifferentialGraded.Module.DGFunctorBimodule
public import StacksFrontier.Algebra.DifferentialGraded.Module.DGFunctorToComplexes
public import StacksFrontier.Algebra.DifferentialGraded.Module.HomComplexExtGeneral

/-! # A derived equivalence lifted to differential graded modules comes from a bimodule

Let `(A, d)` and `(B, d)` be differential graded algebras over a commutative ring `R` and let
`F : D(A, d) ⥤ D(B, d)` be an equivalence. [Stacks, Tag 09S9] observes that if `F` lifts to a
functor of differential graded categories `F^dg : Mod^dg_(A, d) ⥤ Mod^dg_(B, d)` (Tag 09LC), then
`N = F^dg(A)` carries a left `A`-module structure, compatible with the differential and commuting
with its right `B`-module structure, for which the equivalence `- ⊗_A^𝐋 N` of [Stacks, Tag 09S7]
exists. This file proves that.

The left action is the one `F^dg` transports from the regular module: a homogeneous `a ∈ A^n` acts
on `A` by left multiplication, which is a degree-`n` endomorphism of the right module `A` in the
differential graded category, and it acts on `N = F^dg(A)` through its image under `F^dg`. The
three hypotheses of Tag 09S7 then hold for the bimodule `N`:

* the class of `N` in `D(B, d)` is isomorphic to `F(A)`, because `F^dg` lifts `F`, so it is a
  compact object and a weak generator by
  `DifferentialGradedModule.isCompactObject_obj_q_regularModule` and
  `DifferentialGradedModule.isWeakTriangulatedGenerator_singleton_obj_q_regularModule`;
* the canonical map `H^k(A) → Hom_{D(B, d)}(N, N[k])` is, up to composing with isomorphisms that
  do not depend on the cohomology class, the bijection `H^k(A) ≃ Hom_{D(A, d)}(A, A[k])` followed
  by `F`, which is bijective on morphisms.

## Main definitions

* `DGCategory.DGFunctor.homotopyFunctor`: the functor `K(A, d) ⥤ K(B, d)` induced by a functor of
  differential graded categories `Mod^dg_(A, d) ⥤ Mod^dg_(B, d)` (Tags 09L8, 09LC).
* `DifferentialGraded.Bimodule.ofDGLift`: `F^dg(A)` as a differential graded `(A, B)`-bimodule.

## Main results

* `DifferentialGraded.Bimodule.bijective_cohomologyEndomorphismComparison_ofDGLift`: hypothesis (3)
  of Tag 09S7 for `F^dg(A)`.
* `DifferentialGraded.Bimodule.isEquivalence_derivedTensorFunctor_ofDGLift`: **Stacks 09S9**, the
  case of a functor lifted to the differential graded categories: `- ⊗_A^𝐋 F^dg(A)` is an
  equivalence `D(A, d) ⥤ D(B, d)`, and `F^dg(A)` satisfies the three hypotheses of Tag 09S7.
* `DifferentialGraded.Bimodule.isEquivalence_derivedTensorFunctor_of_iso_obj_q_regularModule`:
  **Stacks 09S9**, the reduction: a differential graded `(A, B)`-bimodule whose class in
  `D(B, d)` is isomorphic to `F(A)`, i.e. a left `A`-module structure on a differential graded
  `B`-module quasi-isomorphic to `N = F(A)`, gives the equivalence of Tag 09S7 as soon as its
  left action induces the identification `H^k(A) = Hom_{D(B,d)}(N, N[k])`.

## Implementation notes

*What "lifts" means.* A functor of differential graded categories `G : Mod^dg_(A, d) ⥤
Mod^dg_(B, d)` induces `K(G) : K(A, d) ⥤ K(B, d)` on homotopy categories (Tag 09L8, with
`K(A, d)` identified with the homotopy category of `Mod^dg_(A, d)` by Tag 09LC). It lifts `F`
when `K(G)` followed by the localization `K(B, d) ⥤ D(B, d)` is isomorphic to the localization
`K(A, d) ⥤ D(A, d)` followed by `F`, which is the hypothesis below.

*What is assumed of `F`.* As in `StacksDraft.Algebra.DifferentialGraded.Module.`
`DerivedEquivalenceRegularImage`, the source's `R`-linear equivalence of triangulated categories
is used only through its being an additive equivalence commuting with the translation; the
identification of the canonical map needs only that `F` is fully faithful.

*The left `A`-action needs a compatible identification.* The source says that a left `A`-module
structure on `N` compatible with the differential and commuting with the right `B`-action is all
that is needed. Not every such structure will do: for `A = B = R[x]/(x²)` in degree `0`, `F` the
identity and `x` acting by `0` on `N = B`, the functor `- ⊗_A^𝐋 N` sends `x ∈ Hom(A, A)` to `0`,
so it is not an equivalence. What is needed, and what the reduction below takes, is that the
canonical map `H^k(A) → Hom_{D(B,d)}(N, N[k])` the action induces is bijective — the
identification `H^k(A) = Hom_{D(B,d)}(N, N[k])` the remark has just established for `F`. In the
case of a differential graded lift that is proved, not assumed.

## References

* [Stacks Project, Tag 09S9](https://stacks.math.columbia.edu/tag/09S9), the remark proved here.
* [Stacks Project, Tag 09S7](https://stacks.math.columbia.edu/tag/09S7) for the equivalence,
  [Tag 09LC](https://stacks.math.columbia.edu/tag/09LC) for the differential graded category of
  differential graded modules and [Tag 09L8](https://stacks.math.columbia.edu/tag/09L8) for the
  functor induced on homotopy categories.
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits

universe u

attribute [local instance 10000] DifferentialGradedModule.instPretriangulatedHomotopyCategory'

namespace DGCategory.DGFunctor

open DifferentialGradedModule

variable {R : Type u} [CommRing R] {A B : DifferentialGradedAlgebra.{u, u} R}

/-- **The functor induced on homotopy categories** by a functor of differential graded categories
`G : Mod^dg_(A, d) ⥤ Mod^dg_(B, d)`: the functor `G.onK` of Tag 09L8 between the homotopy
categories of the two differential graded categories, read on `K(A, d)` and `K(B, d)` through the
identifications `DifferentialGradedModule.homotopyCategoryEquivalence` of Tag 09LC. -/
def homotopyFunctor (G : DGFunctor (dgCategory.{u, u, u} A) (dgCategory.{u, u, u} B)) :
    HomotopyCategory A ⥤ HomotopyCategory B :=
  (homotopyCategoryEquivalence A).functor ⋙ G.onK ⋙ (homotopyCategoryEquivalence B).inverse

end DGCategory.DGFunctor

namespace DifferentialGradedModule

variable {R : Type u} [CommRing R] {A B : DifferentialGradedAlgebra.{u, u} R}

section RegularMultiplication

variable (A)

/-- Left multiplication by homogeneous elements of degree `k`, as an `R`-linear map into the
degree-`k` endomorphisms of the regular module in the differential graded category. -/
def regularHomogeneousMulₗ (k : ℤ) :
    A.grading k →ₗ[R] (dgCategory.{u, u, u} A).Hom (regularModule A) (regularModule A) k where
  toFun := regularHomogeneousMul A k
  map_add' a b := Subtype.ext (LinearMap.ext fun x => add_mul (a : A.A) b x)
  map_smul' r a := Subtype.ext (LinearMap.ext fun x => smul_mul_assoc r (a : A.A) x)

/-- Left multiplication by the unit is the identity. -/
theorem regularHomogeneousMul_one :
    regularHomogeneousMul A 0 ⟨1, SetLike.one_mem_graded A.grading⟩ =
      (dgCategory.{u, u, u} A).id (regularModule A) :=
  Subtype.ext (LinearMap.ext fun b => one_mul (b : A.A))

/-- Left multiplication by a product is the composite of the left multiplications. -/
theorem regularHomogeneousMul_mul (n m : ℤ) (a : A.grading n) (b : A.grading m) :
    regularHomogeneousMul A (n + m)
        ⟨(a : A.A) * (b : A.A), SetLike.mul_mem_graded a.property b.property⟩ =
      (dgCategory.{u, u, u} A).comp rfl (regularHomogeneousMul A n a)
        (regularHomogeneousMul A m b) :=
  Subtype.ext (LinearMap.ext fun x => mul_assoc (a : A.A) (b : A.A) x)

/-- Left multiplication by `d a` is the differential of left multiplication by `a`. -/
theorem regularHomogeneousMul_d (n : ℤ) (a : A.grading n) :
    regularHomogeneousMul A (n + 1) ⟨A.d a, A.d_mem n a a.property⟩ =
      (dgCategory.{u, u, u} A).d (regularHomogeneousMul A n a) :=
  Subtype.ext (LinearMap.ext fun x =>
    (homogeneousMapDifferential_regularHomogeneousMul A n a x).symm)

end RegularMultiplication

variable (G : DGCategory.DGFunctor (dgCategory.{u, u, u} A) (dgCategory.{u, u, u} B))

/-- **The left action of `A` on `G(A)`.** A homogeneous `a ∈ A^n` acts on the complex underlying
`G(A)` through the cochain of the homogeneous map `G(a · -)`, the image under `G` of left
multiplication by `a` on the regular module. -/
def dgLiftLeftAction : A.LeftAction (G.obj (regularModule A)).toCochainComplex where
  action n :=
    (homogeneousMapToCochainₗ B (G.obj (regularModule A)) (G.obj (regularModule A)) n).comp
      ((G.mapₗ (regularModule A) (regularModule A) n).comp (regularHomogeneousMulₗ A n))
  map_one := by
    change homogeneousMapToCochain B (G.map (regularHomogeneousMul A 0 _)) = _
    rw [regularHomogeneousMul_one, G.map_id]
    exact homogeneousMapToCochain_id B _
  map_mul n m a b := by
    change homogeneousMapToCochain B (G.map (regularHomogeneousMul A (n + m) _)) = _
    rw [regularHomogeneousMul_mul, G.map_comp]
    exact homogeneousMapToCochain_comp B rfl _ _
  map_d n a := by
    change homogeneousMapToCochain B (G.map (regularHomogeneousMul A (n + 1) _)) = _
    rw [regularHomogeneousMul_d, G.map_d]
    exact homogeneousMapToCochain_d B _

/-- The left action of `A` on `G(A)` is by right `B`-linear cochains, so it is a differential
graded bimodule structure (Tag 0FQI). -/
def dgLiftBimoduleStructure : BimoduleStructure A B (G.obj (regularModule A)) :=
  ⟨dgLiftLeftAction G, fun n a =>
    isRightLinearCochain_homogeneousMapToCochain B (G.obj (regularModule A))
      (G.map (regularHomogeneousMul A n a))⟩

/-- `G(M)`, read as a differential graded `B`-module. -/
abbrev dgLiftObj (M : DifferentialGradedModule.{u, u, u} A) :
    DifferentialGradedModule.{u, u, u} B :=
  G.obj M

/-- The identity of `M[n]`, read as a homogeneous morphism `M ⟶ M[n]` of degree `-n`, is
closed. -/
theorem homogeneousMapToShift_closed (M : DifferentialGradedModule.{u, u, u} B) (n : ℤ) :
    (dgCategory.{u, u, u} B).d (homogeneousMapToShift M n) = 0 := by
  apply Subtype.ext
  apply LinearMap.ext
  intro x
  change n.negOnePow • M.d x - DifferentialGraded.gradedSign R (-n) • M.d x = 0
  rw [Units.smul_def, ← Int.cast_smul_eq_zsmul R, DifferentialGraded.intCast_negOnePow,
    show DifferentialGraded.gradedSign R (-n) = DifferentialGraded.gradedSign R n by
      simp only [DifferentialGraded.gradedSign, Int.natAbs_neg], sub_self]

/-- The image under `G` of a closed homogeneous morphism is closed. -/
theorem dgFunctor_map_closed {L M : DifferentialGradedModule.{u, u, u} A} {n : ℤ}
    (f : (dgCategory.{u, u, u} A).Hom L M n) (hf : (dgCategory.{u, u, u} A).d f = 0) :
    homogeneousMapDifferential B (G.map f) = 0 := by
  change (dgCategory.{u, u, u} B).d (G.map f) = 0
  rw [← G.map_d, hf, G.map_zero]

/-- **`G` commutes with the shift, on homomorphisms.** The homomorphism `G(M[n]) ⟶ G(M)[n]` whose
underlying map is the image under `G` of the identity `M[n] → M`, read as a closed homogeneous
morphism of degree `n`. -/
def dgLiftShiftHom (M : DifferentialGradedModule.{u, u, u} A) (n : ℤ) :
    dgLiftObj G (M.shift n) ⟶ (dgLiftObj G M).shift n :=
  General.homOfClosed B (G.obj (M.shift n)) (G.obj M) (G.map (homogeneousMapFromShift M n))
    (dgFunctor_map_closed G _ (homogeneousMapFromShift_closed M n))

/-- The inverse homomorphism `G(M)[n] ⟶ G(M[n])`: the image under `G` of the identity
`M → M[n]`, of degree `-n`, composed with the identity `G(M)[n] → G(M)`, of degree `n`. -/
def dgLiftShiftInv (M : DifferentialGradedModule.{u, u, u} A) (n : ℤ) :
    (dgLiftObj G M).shift n ⟶ dgLiftObj G (M.shift n) :=
  homOfCocycle B ⟨(dgCategory.{u, u, u} B).comp (neg_add_cancel n)
      (G.map (homogeneousMapToShift M n)) (homogeneousMapFromShift (G.obj M) n), by
    change (dgCategory.{u, u, u} B).d _ = 0
    rw [(dgCategory.{u, u, u} B).leibniz, ← G.map_d, homogeneousMapToShift_closed, G.map_zero,
      homogeneousMapFromShift_closed, DGCategory.comp_zero_left, DGCategory.comp_zero_right,
      smul_zero, add_zero]⟩

/-- The two homomorphisms comparing `G(M[n])` and `G(M)[n]` are mutually inverse. -/
def dgLiftShiftIso (M : DifferentialGradedModule.{u, u, u} A) (n : ℤ) :
    dgLiftObj G (M.shift n) ≅ (dgLiftObj G M).shift n where
  hom := dgLiftShiftHom G M n
  inv := dgLiftShiftInv G M n
  hom_inv_id := by
    refine Hom.ext ?_
    change (G.map (homogeneousMapToShift M n)).1 ∘ₗ LinearMap.id ∘ₗ
        (General.homOfClosed B _ _ _ _).toFun = LinearMap.id
    rw [General.homOfClosed_toFun, LinearMap.id_comp]
    change ((dgCategory.{u, u, u} B).comp (neg_add_cancel n) (G.map (homogeneousMapToShift M n))
      (G.map (homogeneousMapFromShift M n))).1 = ((dgCategory.{u, u, u} B).id _).1
    rw [← G.map_comp, homogeneousMapToShift_comp_fromShift, G.map_id]
  inv_hom_id := by
    refine Hom.ext ?_
    change (General.homOfClosed B _ _ _ _).toFun ∘ₗ (G.map (homogeneousMapToShift M n)).1 ∘ₗ
        LinearMap.id = LinearMap.id
    rw [General.homOfClosed_toFun, LinearMap.comp_id]
    change ((dgCategory.{u, u, u} B).comp (add_neg_cancel n) (G.map (homogeneousMapFromShift M n))
      (G.map (homogeneousMapToShift M n))).1 = ((dgCategory.{u, u, u} B).id _).1
    rw [← G.map_comp, homogeneousMapFromShift_comp_toShift, G.map_id]

/-- The homomorphism of differential graded `B`-modules induced by `G` on a homomorphism of
differential graded `A`-modules. -/
def dgLiftMap {L M : DifferentialGradedModule.{u, u, u} A} (f : L ⟶ M) :
    dgLiftObj G L ⟶ dgLiftObj G M :=
  homOfCocycle B (G.mapCocycle (cocycleOfHom A f))

/-- `G` acts on homotopy classes of homomorphisms through `dgLiftMap`. -/
theorem onK_map_homotopyCategoryEquivalence_functor_map {L M : DifferentialGradedModule.{u, u, u} A}
    (f : L ⟶ M) :
    G.onK.map ((homotopyCategoryEquivalence A).functor.map ((toHomotopyCategory A).map f)) =
      (homotopyCategoryEquivalence B).functor.map ((toHomotopyCategory B).map (dgLiftMap G f)) :=
  rfl

end DifferentialGradedModule

namespace DifferentialGraded.Bimodule

open DifferentialGradedModule CategoryTheory.ObjectProperty

variable {R : Type u} [CommRing R] {A B : DifferentialGradedAlgebra.{u, u} R}
  (G : DGCategory.DGFunctor (dgCategory.{u, u, u} A) (dgCategory.{u, u, u} B))

/-- **`G(A)` as a differential graded `(A, B)`-bimodule**, for `G : Mod^dg_(A, d) ⥤ Mod^dg_(B, d)`
a functor of differential graded categories: the right module is `G(A)` and a homogeneous
`a ∈ A^n` acts on the left through `G(a · -)`. -/
@[implicit_reducible]
def ofDGLift : Bimodule A B where
  rightModule := G.obj (regularModule A)
  leftAction := dgLiftBimoduleStructure G

/-- The right module underlying `ofDGLift G` is `G(A)`. -/
@[simp] theorem ofDGLift_rightModule : (ofDGLift G).rightModule = G.obj (regularModule A) := rfl

/-- Left multiplication by a homogeneous `a ∈ A^n` on `G(A)` is the image under `G` of left
multiplication by `a` on the regular module. -/
theorem ofDGLift_leftMultiplication (n : ℤ) (a : A.grading n) :
    (ofDGLift G).leftMultiplication n a = G.map (regularHomogeneousMul A n a) := by
  refine Subtype.ext (LinearMap.ext fun x => ?_)
  induction x using DirectSum.Decomposition.inductionOn (ofDGLift G).rightModule.grading with
  | zero => exact (map_zero _).trans (map_zero _).symm
  | @homogeneous p x =>
    rw [leftMultiplication_apply (ofDGLift G) n p a x]
    rfl
  | add x y hx hy => rw [map_add, map_add, hx, hy]

/-- The action of a cocycle `a` on `G(A)` is the image under `G` of the action of `a` on the
regular module, followed by the comparison `G(A[k]) ≅ G(A)[k]`. -/
theorem cocycleAction_ofDGLift (k : ℤ) (a : A.Cocycle k) :
    (ofDGLift G).cocycleAction k a =
      dgLiftMap G (regularCocycleHom A k a) ≫ dgLiftShiftHom G (regularModule A) k := by
  refine DifferentialGradedModule.Hom.ext ?_
  rw [cocycleAction_toFun, ofDGLift_leftMultiplication]
  change _ = (General.homOfClosed B _ _ _ _).toFun ∘ₗ (G.map (cocycleOfHom A
    (regularCocycleHom A k a)).1).1
  rw [General.homOfClosed_toFun]
  change _ = ((dgCategory.{u, u, u} B).comp (add_zero k)
    (G.map (homogeneousMapFromShift (regularModule A) k))
    (G.map (cocycleOfHom A (regularCocycleHom A k a)).1)).1
  rw [← G.map_comp]
  congr 2
  refine Subtype.ext ?_
  rw [dgCategory_comp_val, cocycleOfHom_val, regularCocycleHom_toFun]
  exact (LinearMap.id_comp _).symm

variable {G}
variable (F : derivedCategory' A ⥤ derivedCategory' B)
  (e : G.homotopyFunctor ⋙ (quasiIsomorphisms' B).Q ≅ (quasiIsomorphisms' A).Q ⋙ F)

include e in
/-- **Hypothesis (3) of [Stacks, Tag 09S7] for a differential graded lift.** If
`G : Mod^dg_(A, d) ⥤ Mod^dg_(B, d)` lifts a fully faithful `F : D(A, d) ⥤ D(B, d)`, then the
canonical map `H^k(A) → Hom_{D(B, d)}(G(A), G(A)[k])` of the bimodule `G(A)` is bijective for
every `k`.

The canonical map sends the class of a cocycle `a` to the image of `G(a · -)` composed with
`G(A[k]) ≅ G(A)[k]` (`DifferentialGraded.Bimodule.cocycleAction_ofDGLift`). Up to the unit of the
equivalence of Tag 09LC and that comparison, neither depending on `a`, this is the image under
`K(G)` of the class of left multiplication by `a`, and `e` makes that `F` applied to the class
of `a` in `Hom_{D(A,d)}(A, A[k])`; both steps are bijective. -/
theorem bijective_cohomologyEndomorphismComparison_ofDGLift [F.Full] [F.Faithful] (k : ℤ) :
    Function.Bijective ((ofDGLift G).cohomologyEndomorphismComparison k) := by
  let X := (toHomotopyCategory A).obj (regularModule A)
  let Y := (toHomotopyCategory A).obj ((regularModule A).shift k)
  let uX := (homotopyCategoryEquivalence B).unitIso.app
    ((toHomotopyCategory B).obj (G.obj (regularModule A)))
  let uY := (homotopyCategoryEquivalence B).unitIso.app
    ((toHomotopyCategory B).obj (G.obj ((regularModule A).shift k)))
  -- the bijection `H^k(A) ≃ Hom(Q_B K(G) A, Q_B K(G) A[k])` furnished by `e` and `F`
  let Φ : A.Cohomology k ≃ ((G.homotopyFunctor ⋙ (quasiIsomorphisms' B).Q).obj X ⟶
      (G.homotopyFunctor ⋙ (quasiIsomorphisms' B).Q).obj Y) :=
    ((cohomologyEquivDerivedHom A k).trans
      (Functor.FullyFaithful.ofFullyFaithful F).homEquiv).trans
        ((e.app X).symm.homCongr (e.app Y).symm)
  have hΦ : ∀ x, Φ x = (quasiIsomorphisms' B).Q.map
      (G.homotopyFunctor.map (cohomologyToHomotopyCategory A k x)) := by
    intro x
    have h := e.hom.naturality (cohomologyToHomotopyCategory A k x)
    simp only [Functor.comp_map] at h
    change e.hom.app X ≫ F.map ((quasiIsomorphisms' A).Q.map
      (cohomologyToHomotopyCategory A k x)) ≫ e.inv.app Y = _
    rw [← Category.assoc, ← h, Category.assoc, Iso.hom_inv_id_app, Category.comp_id]
  -- the same map, at the level of the homotopy category
  have hK : ∀ a : A.Cocycle k, (toHomotopyCategory B).map ((ofDGLift G).cocycleAction k a) =
      uX.hom ≫ G.homotopyFunctor.map ((toHomotopyCategory A).map (regularCocycleHom A k a)) ≫
        uY.inv ≫ (toHomotopyCategory B).map (dgLiftShiftHom G (regularModule A) k) := by
    intro a
    change _ = uX.hom ≫ (homotopyCategoryEquivalence B).inverse.map
      (G.onK.map ((homotopyCategoryEquivalence A).functor.map
        ((toHomotopyCategory A).map (regularCocycleHom A k a)))) ≫ uY.inv ≫ _
    change _ = uX.hom ≫ (homotopyCategoryEquivalence B).inverse.map
      ((homotopyCategoryEquivalence B).functor.map
        ((toHomotopyCategory B).map (dgLiftMap G (regularCocycleHom A k a)))) ≫ uY.inv ≫ _
    rw [Equivalence.inv_fun_map, cocycleAction_ofDGLift, Functor.map_comp]
    change _ = uX.hom ≫ (uX.inv ≫ _ ≫ uY.hom) ≫ uY.inv ≫ _
    simp only [Category.assoc, Iso.hom_inv_id_assoc]
  let Ψ : A.Cohomology k ≃
      (((toHomotopyCategory B) ⋙ (quasiIsomorphisms' B).Q).obj (ofDGLift G).rightModule ⟶
        ((toHomotopyCategory B) ⋙ (quasiIsomorphisms' B).Q).obj
          ((ofDGLift G).rightModule.shift k)) :=
    Φ.trans (((quasiIsomorphisms' B).Q.mapIso uX).symm.homCongr
      (((quasiIsomorphisms' B).Q.mapIso uY).symm ≪≫
        (quasiIsomorphisms' B).Q.mapIso ((toHomotopyCategory B).mapIso
          (dgLiftShiftIso G (regularModule A) k))))
  have hΨ : ∀ x, (ofDGLift G).cohomologyEndomorphismComparison k x = Ψ x := by
    intro x
    induction x using Quotient.ind with | _ a => ?_
    rw [cohomologyEndomorphismComparison_mk]
    change _ = (quasiIsomorphisms' B).Q.map uX.hom ≫ Φ (Quotient.mk _ a) ≫
      (quasiIsomorphisms' B).Q.map uY.inv ≫ (quasiIsomorphisms' B).Q.map
        ((toHomotopyCategory B).map (dgLiftShiftHom G (regularModule A) k))
    rw [hΦ, cohomologyToHomotopyCategory_mk, Functor.comp_map, hK, Functor.map_comp]
    congr 1
    exact ((quasiIsomorphisms' B).Q.map_comp _ _).trans
      (congrArg (_ ≫ ·) ((quasiIsomorphisms' B).Q.map_comp _ _))
  have : (ofDGLift G).cohomologyEndomorphismComparison k = Ψ := funext hΨ
  rw [this]
  exact Ψ.bijective

include e in
/-- **The class of `G(A)` is `F(A)`.** If `G` lifts `F`, the class of the bimodule `G(A)` in
`D(B, d)` is isomorphic to the image under `F` of the class of the regular module. -/
def objQRegularModuleIsoOfDGLift :
    ((toHomotopyCategory B) ⋙ (quasiIsomorphisms' B).Q).obj (ofDGLift G).rightModule ≅
      F.obj ((toHomotopyCategory A ⋙ (quasiIsomorphisms' A).Q).obj (regularModule A)) :=
  (quasiIsomorphisms' B).Q.mapIso ((homotopyCategoryEquivalence B).unitIso.app _) ≪≫
    e.app ((toHomotopyCategory A).obj (regularModule A))

include e in
/-- **Stacks 09S9, the case of a differential graded lift.** Let `(A, d)` and `(B, d)` be
differential graded algebras over a commutative ring `R` and let `F : D(A, d) ⥤ D(B, d)` be an
additive equivalence commuting with the translation. Suppose `F` lifts to a functor of
differential graded categories `G : Mod^dg_(A, d) ⥤ Mod^dg_(B, d)`, in the sense that
`K(G) : K(A, d) ⥤ K(B, d)` followed by the localization is isomorphic to the localization
followed by `F`. Then the left `A`-module structure on `N = G(A)` transported by `G` from the
regular module (`DifferentialGraded.Bimodule.ofDGLift`) makes `N` a differential graded
`(A, B)`-bimodule satisfying the three hypotheses of [Stacks, Tag 09S7] — its class in
`D(B, d)` is compact, it is a weak generator, and the canonical map
`H^k(A) → Hom_{D(B,d)}(N, N[k])` is bijective for every `k` — so that
`- ⊗_A^𝐋 N : D(A, d) ⥤ D(B, d)` is an equivalence. The class of `N` is isomorphic to `F(A)`
(`DifferentialGraded.Bimodule.objQRegularModuleIsoOfDGLift`). -/
@[stacks 09S9 "if F lifts to a differential graded functor, N = F(A) is an (A, B)-bimodule as in \
Tag 09S7, giving the equivalence - ⊗_A^L N"]
theorem isEquivalence_derivedTensorFunctor_ofDGLift [F.IsEquivalence] [F.Additive]
    [F.CommShift ℤ] :
    IsCompactObject.{u}
        ((toHomotopyCategory B ⋙ (quasiIsomorphisms' B).Q).obj (ofDGLift G).rightModule) ∧
      (ObjectProperty.singleton ((toHomotopyCategory B ⋙ (quasiIsomorphisms' B).Q).obj
        (ofDGLift G).rightModule)).IsWeakTriangulatedGenerator ∧
      (∀ k : ℤ, Function.Bijective ((ofDGLift G).cohomologyEndomorphismComparison k)) ∧
      (derivedTensorFunctor (ofDGLift G)).IsEquivalence := by
  have hiso := objQRegularModuleIsoOfDGLift F e
  have hc : IsCompactObject.{u}
      ((toHomotopyCategory B ⋙ (quasiIsomorphisms' B).Q).obj (ofDGLift G).rightModule) :=
    isCompactObject_of_iso hiso (isCompactObject_obj_q_regularModule A B F)
  have hg := isWeakTriangulatedGenerator_singleton_of_iso hiso.symm
    (isWeakTriangulatedGenerator_singleton_obj_q_regularModule A B F)
  have h3 := bijective_cohomologyEndomorphismComparison_ofDGLift F e
  exact ⟨hc, hg, h3, isEquivalence_derivedTensorFunctor_of_isWeakTriangulatedGenerator _ hg h3⟩

/-- **Stacks 09S9, the reduction to a left module structure.** Let `F : D(A, d) ⥤ D(B, d)` be an
additive equivalence commuting with the translation, and let `N` be a differential graded
`(A, B)`-bimodule whose class in `D(B, d)` is isomorphic to `F(A)` — a left `A`-module structure,
compatible with the differential and commuting with the right `B`-action, on a differential
graded `B`-module quasi-isomorphic to `F(A)`. If the left action induces the identification
`H^k(A) = Hom_{D(B,d)}(N, N[k])`, i.e. the canonical map is bijective for every `k`, then `N`
satisfies the three hypotheses of [Stacks, Tag 09S7] and `- ⊗_A^𝐋 N` is an equivalence.

Compactness and weak generation are invariant under isomorphism and hold for `F(A)`
(`DifferentialGradedModule.isCompactObject_obj_q_regularModule`,
`DifferentialGradedModule.isWeakTriangulatedGenerator_singleton_obj_q_regularModule`). -/
@[stacks 09S9 "a left A-module structure on a module quasi-isomorphic to N = F(A) inducing \
H^k(A) = Hom(N, N[k]) gives the equivalence of Tag 09S7"]
theorem isEquivalence_derivedTensorFunctor_of_iso_obj_q_regularModule [F.IsEquivalence]
    [F.Additive] [F.CommShift ℤ] (N : Bimodule A B)
    (hN : ((toHomotopyCategory B ⋙ (quasiIsomorphisms' B).Q).obj N.rightModule) ≅
      F.obj ((toHomotopyCategory A ⋙ (quasiIsomorphisms' A).Q).obj (regularModule A)))
    (h3 : ∀ k : ℤ, Function.Bijective (N.cohomologyEndomorphismComparison k)) :
    IsCompactObject.{u}
        ((toHomotopyCategory B ⋙ (quasiIsomorphisms' B).Q).obj N.rightModule) ∧
      (ObjectProperty.singleton ((toHomotopyCategory B ⋙ (quasiIsomorphisms' B).Q).obj
        N.rightModule)).IsWeakTriangulatedGenerator ∧
      (derivedTensorFunctor N).IsEquivalence := by
  have hc : IsCompactObject.{u}
      ((toHomotopyCategory B ⋙ (quasiIsomorphisms' B).Q).obj N.rightModule) :=
    isCompactObject_of_iso hN (isCompactObject_obj_q_regularModule A B F)
  have hg := isWeakTriangulatedGenerator_singleton_of_iso hN.symm
    (isWeakTriangulatedGenerator_singleton_obj_q_regularModule A B F)
  exact ⟨hc, hg, isEquivalence_derivedTensorFunctor_of_isWeakTriangulatedGenerator _ hg h3⟩

end DifferentialGraded.Bimodule

end
