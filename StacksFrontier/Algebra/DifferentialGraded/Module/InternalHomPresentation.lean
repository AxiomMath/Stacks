module

public import StacksFrontier.Algebra.DifferentialGraded.Module.InternalHom
public import StacksCore.Tactic.StacksAttribute

/-! # Presentations of the internal hom are canonically isomorphic

The internal hom `Hom^•_B(N, P)` of Tag 0FQR is characterized, not named: it is presented by a
`DifferentialGradedModule.HomModuleData`, which records a right differential graded `A`-module
together with identifications of its graded pieces with the homogeneous right-`B`-linear maps
`N → P`. Any two such presentations are therefore canonically isomorphic, by the isomorphism
that matches the two identifications, and that isomorphism is the unique one doing so.

## Main definitions

* `DifferentialGradedModule.HomModuleData.compare`: the canonical isomorphism between the
  modules of two presentations of `Hom^•_B(N, P)`.

## Main results

* `DifferentialGradedModule.homogeneousMap_ext`: a homogeneous right-`B`-linear map is
  determined by its values on homogeneous elements.
* `DifferentialGradedModule.HomModuleData.compare_homogeneousEquiv`: the characterizing
  property of the comparison isomorphism — it matches the two identifications.
* `DifferentialGradedModule.HomModuleData.compare_unique`: the comparison isomorphism is the
  only homomorphism with that property.
* `DifferentialGradedModule.HomModuleData.compare_self`,
  `DifferentialGradedModule.HomModuleData.compare_trans`: the comparison isomorphisms are
  reflexive and transitive, so they form a coherent system.

## Implementation notes

The comparison is assembled from its graded pieces with `DirectSum.toModule`, as elsewhere in
this directory; `DifferentialGradedModule.HomModuleData.compareHom_apply_grading` is the
degreewise formula, proved first and used to discharge every other obligation by
`DirectSum.Decomposition.inductionOn`.

Compatibility with the right `A`-action is where `DifferentialGradedModule.homogeneousMap_ext`
is needed: the `map_smul` field of a presentation records the action only through the *values* of
the associated homogeneous maps on homogeneous elements of `N`, so recovering an equality of
homogeneous maps from it requires knowing that those values determine the map.

## References

* [Stacks Project, Tag 0FQR](https://stacks.math.columbia.edu/tag/0FQR)
-/

@[expose] public noncomputable section

open CategoryTheory

universe u

namespace DifferentialGradedModule

variable {R : Type u} [CommRing R] {A B : DifferentialGradedAlgebra R}
  {N P : DifferentialGradedModule B} {L : BimoduleStructure A B N}

/-- A homogeneous right-`B`-linear map out of `N` is determined by its values on homogeneous
elements of `N`. -/
theorem homogeneousMap_ext {n : ℤ} {f g : HomogeneousMap B N P n}
    (h : ∀ (p : ℤ) (x : N.grading p), f.1 x = g.1 x) : f = g := by
  refine Subtype.ext (LinearMap.ext fun x => ?_)
  induction x using DirectSum.Decomposition.inductionOn N.grading with
  | zero => simp
  | @homogeneous p x => exact h p x
  | add x y hx hy => rw [map_add, map_add, hx, hy]

namespace HomModuleData

variable (H H' : HomModuleData A B N P L)

/-- The graded piece of the comparison: read a degree-`n` element of the first presentation as a
homogeneous map, then back through the second presentation. -/
def compareGraded (n : ℤ) : H.module.grading n →ₗ[R] H'.module.grading n :=
  (H'.homogeneousEquiv n).symm.toLinearMap ∘ₗ (H.homogeneousEquiv n).toLinearMap

/-- The graded piece of the comparison matches the two identifications with homogeneous maps. -/
@[simp] theorem homogeneousEquiv_compareGraded (n : ℤ) (f : H.module.grading n) :
    H'.homogeneousEquiv n (compareGraded H H' n f) = H.homogeneousEquiv n f :=
  (H'.homogeneousEquiv n).apply_symm_apply _

/-- An element of the second presentation whose identification with a homogeneous map agrees with
that of `f` is the graded piece of the comparison applied to `f`. -/
private theorem compareGraded_eq_of_homogeneousEquiv_eq {n : ℤ} (f : H.module.grading n)
    (g : H'.module.grading n) (h : H'.homogeneousEquiv n g = H.homogeneousEquiv n f) :
    compareGraded H H' n f = g :=
  (H'.homogeneousEquiv n).injective <| by rw [homogeneousEquiv_compareGraded, h]

/-- The underlying linear map of the comparison, assembled from its graded pieces. -/
def compareLinearMap : H.module.M →ₗ[R] H'.module.M :=
  (DirectSum.toModule R ℤ H'.module.M
      (fun n => (H'.module.grading n).subtype ∘ₗ compareGraded H H' n)).comp
    (DirectSum.decomposeLinearEquiv H.module.grading).toLinearMap

/-- On a homogeneous element of degree `n`, the comparison map is its graded piece in degree
`n`. -/
theorem compareLinearMap_apply_grading (n : ℤ) (f : H.module.grading n) :
    compareLinearMap H H' (f : H.module.M) = (compareGraded H H' n f : H'.module.M) := by
  have hdec : DirectSum.decomposeLinearEquiv H.module.grading (f : H.module.M) =
      DirectSum.lof R ℤ (fun i => H.module.grading i) n f := by simp
  simp only [compareLinearMap, LinearMap.comp_apply, LinearEquiv.coe_coe, hdec,
    DirectSum.toModule_lof, Submodule.coe_subtype]

/-- The comparison map preserves the grading. -/
theorem compareLinearMap_mem_grading (n : ℤ) (x : H.module.M)
    (hx : x ∈ H.module.grading n) :
    compareLinearMap H H' x ∈ H'.module.grading n := by
  rw [show x = ((⟨x, hx⟩ : H.module.grading n) : H.module.M) from rfl,
    compareLinearMap_apply_grading]
  exact (compareGraded H H' n ⟨x, hx⟩).property

/-- The comparison map commutes with the differentials. -/
theorem compareLinearMap_d (x : H.module.M) :
    compareLinearMap H H' (H.module.d x) = H'.module.d (compareLinearMap H H' x) := by
  induction x using DirectSum.Decomposition.inductionOn H.module.grading with
  | zero => simp
  | @homogeneous n f =>
    calc compareLinearMap H H' (H.module.d (f : H.module.M))
        = compareLinearMap H H' ((H.module.gradedDifferential n f : H.module.M)) := rfl
      _ = (compareGraded H H' (n + 1) (H.module.gradedDifferential n f) : H'.module.M) :=
          compareLinearMap_apply_grading H H' (n + 1) _
      _ = (H'.module.gradedDifferential n (compareGraded H H' n f) : H'.module.M) :=
          congrArg Subtype.val <| compareGraded_eq_of_homogeneousEquiv_eq H H' _ _ <| by
            rw [H.map_d, H'.map_d, homogeneousEquiv_compareGraded]
      _ = H'.module.d (compareLinearMap H H' (f : H.module.M)) := by
          rw [compareLinearMap_apply_grading]
          rfl
  | add x y hx hy => simp only [map_add, hx, hy]

/-- The comparison map is compatible with the right `A`-actions. -/
theorem compareLinearMap_op_smul (x : H.module.M) (a : A.A) :
    compareLinearMap H H' (MulOpposite.op a • x) =
      MulOpposite.op a • compareLinearMap H H' x := by
  induction a using DirectSum.Decomposition.inductionOn A.grading with
  | zero => simp
  | @homogeneous m a =>
    induction x using DirectSum.Decomposition.inductionOn H.module.grading with
    | zero => simp
    | @homogeneous n f =>
      have hmemH : MulOpposite.op (a : A.A) • (f : H.module.M) ∈ H.module.grading (n + m) :=
        H.module.smul_mem n m (f : H.module.M) (a : A.A) f.property a.property
      have hmemH' : MulOpposite.op (a : A.A) • (compareGraded H H' n f : H'.module.M) ∈
          H'.module.grading (n + m) :=
        H'.module.smul_mem n m _ (a : A.A) (compareGraded H H' n f).property a.property
      have key : compareGraded H H' (n + m) ⟨_, hmemH⟩ = ⟨_, hmemH'⟩ :=
        compareGraded_eq_of_homogeneousEquiv_eq H H' _ _ <| by
          apply homogeneousMap_ext
          intro p x
          rw [H'.map_smul n m p (compareGraded H H' n f) a x,
            H.map_smul n m p f a x, homogeneousEquiv_compareGraded]
      calc compareLinearMap H H' (MulOpposite.op (a : A.A) • (f : H.module.M))
          = (compareGraded H H' (n + m) ⟨_, hmemH⟩ : H'.module.M) :=
            compareLinearMap_apply_grading H H' (n + m) ⟨_, hmemH⟩
        _ = MulOpposite.op (a : A.A) • (compareGraded H H' n f : H'.module.M) :=
            congrArg Subtype.val key
        _ = MulOpposite.op (a : A.A) • compareLinearMap H H' (f : H.module.M) := by
            rw [compareLinearMap_apply_grading]
    | add x y hx hy => rw [smul_add, map_add, map_add, smul_add, hx, hy]
  | add a b ha hb =>
    rw [MulOpposite.op_add, add_smul, map_add, ha, hb, add_smul]

/-- The homomorphism of differential graded `A`-modules comparing two presentations of the
internal hom `Hom^•_B(N, P)`: it matches the two identifications of the graded pieces with
homogeneous right-`B`-linear maps. -/
def compareHom : H.module ⟶ H'.module where
  toFun := compareLinearMap H H'
  map_smul x a := compareLinearMap_op_smul H H' x a
  map_grading n x hx := compareLinearMap_mem_grading H H' n x hx
  map_d := LinearMap.ext (compareLinearMap_d H H')

/-- On a homogeneous element of degree `n`, the comparison homomorphism is its graded piece in
degree `n`. -/
@[simp] theorem compareHom_apply_grading (n : ℤ) (f : H.module.grading n) :
    (compareHom H H').toFun (f : H.module.M) = (compareGraded H H' n f : H'.module.M) :=
  compareLinearMap_apply_grading H H' n f

/-- The characterizing property of the comparison: it matches the identifications of the graded
pieces with homogeneous right-`B`-linear maps `N → P`. -/
theorem compareHom_homogeneousEquiv (n : ℤ) (f : H.module.grading n) :
    H'.homogeneousEquiv n ⟨(compareHom H H').toFun (f : H.module.M),
        (compareHom H H').map_grading n _ f.property⟩ =
      H.homogeneousEquiv n f := by
  rw [show (⟨(compareHom H H').toFun (f : H.module.M),
      (compareHom H H').map_grading n _ f.property⟩ : H'.module.grading n) =
      compareGraded H H' n f from Subtype.ext (compareHom_apply_grading H H' n f),
    homogeneousEquiv_compareGraded]

/-- A homomorphism matching the two identifications is the comparison homomorphism: there is at
most one such. -/
theorem compareHom_unique (φ : H.module ⟶ H'.module)
    (hφ : ∀ (n : ℤ) (f : H.module.grading n),
      H'.homogeneousEquiv n ⟨φ.toFun (f : H.module.M), φ.map_grading n _ f.property⟩ =
        H.homogeneousEquiv n f) :
    φ = compareHom H H' := by
  refine Hom.ext (LinearMap.ext fun x => ?_)
  induction x using DirectSum.Decomposition.inductionOn H.module.grading with
  | zero => simp
  | @homogeneous n f =>
    rw [compareHom_apply_grading]
    exact congrArg Subtype.val (compareGraded_eq_of_homogeneousEquiv_eq H H' f _ (hφ n f)).symm
  | add x y hx hy => rw [map_add, map_add, hx, hy]

/-- The comparison homomorphism of a presentation with itself is the identity. -/
@[simp] theorem compareHom_self : compareHom H H = 𝟙 H.module :=
  (compareHom_unique H H (𝟙 H.module) fun _ _ => by congr 1).symm

/-- The comparison homomorphisms compose: comparing `H` with `H'` and then `H'` with `H''` is
comparing `H` with `H''`. -/
theorem compareHom_comp (H'' : HomModuleData A B N P L) :
    compareHom H H' ≫ compareHom H' H'' = compareHom H H'' := by
  apply compareHom_unique
  intro n f
  rw [show (⟨(compareHom H H' ≫ compareHom H' H'').toFun (f : H.module.M),
      (compareHom H H' ≫ compareHom H' H'').map_grading n _ f.property⟩ :
        H''.module.grading n) =
      compareGraded H' H'' n (compareGraded H H' n f) from
        Subtype.ext ((congrArg (compareHom H' H'').toFun
          (compareHom_apply_grading H H' n f)).trans (compareHom_apply_grading H' H'' n _)),
    homogeneousEquiv_compareGraded, homogeneousEquiv_compareGraded]

/-- **Stacks 0FQR.** Any two presentations of the internal hom `Hom^•_B(N, P)` have canonically
isomorphic underlying differential graded `A`-modules. -/
def compare : H.module ≅ H'.module where
  hom := compareHom H H'
  inv := compareHom H' H
  hom_inv_id := by rw [compareHom_comp, compareHom_self]
  inv_hom_id := by rw [compareHom_comp, compareHom_self]

/-- The forward map of the comparison isomorphism is the comparison homomorphism. -/
@[simp] theorem compare_hom : (compare H H').hom = compareHom H H' := rfl

/-- The inverse of the comparison isomorphism is the comparison homomorphism in the opposite
direction. -/
@[simp] theorem compare_inv : (compare H H').inv = compareHom H' H := rfl

/-- The comparison isomorphism matches the two identifications of the graded pieces. -/
theorem compare_homogeneousEquiv (n : ℤ) (f : H.module.grading n) :
    H'.homogeneousEquiv n ((compare H H').hom.gradedMap n f) = H.homogeneousEquiv n f :=
  compareHom_homogeneousEquiv H H' n f

/-- The comparison isomorphism of a presentation with itself is the identity isomorphism. -/
@[simp] theorem compare_self : compare H H = Iso.refl H.module :=
  Iso.ext (compareHom_self H)

/-- The comparison isomorphisms compose: comparing `H` with `H'` and then `H'` with `H''` is
comparing `H` with `H''`. -/
theorem compare_trans (H'' : HomModuleData A B N P L) :
    compare H H' ≪≫ compare H' H'' = compare H H'' :=
  Iso.ext (compareHom_comp H H' H'')

end HomModuleData

end DifferentialGradedModule

end
