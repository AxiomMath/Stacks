module

public import Mathlib.CategoryTheory.Triangulated.Triangulated
public import StacksCore.Tactic.StacksAttribute
public import StacksFrontier.Algebra.DifferentialGraded.DerivedCategory.HomotopyCategoryShift
public import StacksFrontier.Algebra.DifferentialGraded.Module.MappingConeAdmissible
public import StacksFrontier.Algebra.DifferentialGraded.Module.MappingConeFunctorial
public import StacksFrontier.Algebra.DifferentialGraded.Module.MappingConeRotation
public import StacksFrontier.Algebra.DifferentialGraded.Module.MappingConeTriangle
public import StacksFrontier.Algebra.DifferentialGraded.Module.Pretriangulated

/-!
# The octahedron for two composable admissible monomorphisms

Let `(A, d)` be a differential graded algebra over a commutative ring `R` and let
`α : K ⟶ L` and `β : L ⟶ M` be composable homomorphisms of right differential graded
`A`-modules. The three cone triangles of `α`, `β ∘ α` and `β` fit into an octahedron: there are
morphisms between their third vertices making the four squares of the octahedron axiom commute,
and the resulting triangle on the third vertices is again distinguished.

The third vertex of the triangle produced by the octahedron axiom is the cone of the map
`C(α) ⟶ C(β ∘ α)` induced by the square `β ∘ α = (β ∘ α) ∘ 1`, and the comparison with `C(β)` is
an explicit homotopy equivalence written out in the direct-sum coordinates of the cones.

## Main definitions

* `DifferentialGradedModule.mappingConeMap`: the map of cones induced by a strictly commutative
  square of homomorphisms.

## Main results

* `DifferentialGradedModule.octahedron_of_isAdmissibleMono`: the octahedron of two composable
  admissible monomorphisms.

## Implementation notes

The map on cones induced by a commutative square is the diagonal matrix of the two maps, and is
written out here rather than extracted from
`DifferentialGradedModule.exists_mappingConeMap_of_homotopic_square`, because the octahedron
needs its explicit form in coordinates.

The comparison `C(C(α) ⟶ C(β ∘ α)) ⟶ C(β)` has a section, and the two composites are the identity
up to the explicit homotopies `mappingConeCancelHomotopy` and `mappingConeCancelBoundaryHomotopy`.
Those two homotopies are the only computational content of the proof; everything else is the
bookkeeping of the comparison between the shift of the homotopy category and the shift of
differential graded modules, handled through the `eqToHom` identities of
`StacksFrontier.Algebra.DifferentialGraded.DerivedCategory.HomotopyCategoryShift`.

## References

* [Stacks Project, Tag 09KI](https://stacks.math.columbia.edu/tag/09KI)
-/

@[expose] public section

open CategoryTheory

namespace DifferentialGradedModule

universe u

variable {R : Type u} [CommRing R] {A : DifferentialGradedAlgebra R}

private theorem mappingCone_coordinates_symm_eq_self {K L : DifferentialGradedModule A}
    (f : K ⟶ L) (x : L.M × K.M) : (cone f).coordinates.symm x = x := rfl

private theorem mappingConeModule_d_coordinates {K L : DifferentialGradedModule A} (f : K ⟶ L)
    (x : (coneModule f).M) :
    (coneModule f).d x =
      (cone f).coordinates.symm
        (L.d ((cone f).coordinates x).1 + f.toFun ((cone f).coordinates x).2,
          -K.d ((cone f).coordinates x).2) := by
  apply (cone f).coordinates.injective
  rw [LinearEquiv.apply_symm_apply]
  exact (cone f).differential x

/-- The map of cones induced by a strictly commutative square of homomorphisms of differential
graded modules: it is the diagonal matrix of the two maps in direct-sum coordinates. -/
noncomputable def mappingConeMap {K₁ L₁ K₂ L₂ : DifferentialGradedModule A}
    (f₁ : K₁ ⟶ L₁) (f₂ : K₂ ⟶ L₂) (a : K₁ ⟶ K₂) (b : L₁ ⟶ L₂)
    (h : Hom.comp b f₁ = Hom.comp f₂ a) :
    coneModule f₁ ⟶ coneModule f₂ where
  toFun := LinearMap.prodMap b.toFun a.toFun
  map_smul := by
    intro x r
    change (b.toFun (MulOpposite.op r • x.1), a.toFun (MulOpposite.op r • x.2)) =
      (MulOpposite.op r • b.toFun x.1, MulOpposite.op r • a.toFun x.2)
    exact Prod.ext (b.map_smul x.1 r) (a.map_smul x.2 r)
  map_grading := by
    intro n x hx
    change x.1 ∈ L₁.grading n ∧ x.2 ∈ K₁.grading (n + 1) at hx
    change b.toFun x.1 ∈ L₂.grading n ∧ a.toFun x.2 ∈ K₂.grading (n + 1)
    exact ⟨b.map_grading n x.1 hx.1, a.map_grading (n + 1) x.2 hx.2⟩
  map_d := by
    apply LinearMap.ext
    intro x
    change (b.toFun (L₁.d x.1 + f₁.toFun x.2), a.toFun (-K₁.d x.2)) =
      (L₂.d (b.toFun x.1) + f₂.toFun (a.toFun x.2), -K₂.d (a.toFun x.2))
    have hb : b.toFun (L₁.d x.1) = L₂.d (b.toFun x.1) := by
      simpa only [LinearMap.comp_apply] using LinearMap.congr_fun b.map_d x.1
    have ha : a.toFun (K₁.d x.2) = K₂.d (a.toFun x.2) := by
      simpa only [LinearMap.comp_apply] using LinearMap.congr_fun a.map_d x.2
    have hcomm : b.toFun (f₁.toFun x.2) = f₂.toFun (a.toFun x.2) :=
      congrArg (fun t : Hom K₁ L₂ => t.toFun x.2) h
    rw [map_add, hb, hcomm, map_neg, ha]

private theorem mappingConeMap_apply {K₁ L₁ K₂ L₂ : DifferentialGradedModule A}
    (f₁ : K₁ ⟶ L₁) (f₂ : K₂ ⟶ L₂) (a : K₁ ⟶ K₂) (b : L₁ ⟶ L₂)
    (h : Hom.comp b f₁ = Hom.comp f₂ a) (x : (coneModule f₁).M) :
    (mappingConeMap f₁ f₂ a b h).toFun x =
      (cone f₂).coordinates.symm
        (b.toFun ((cone f₁).coordinates x).1,
          a.toFun ((cone f₁).coordinates x).2) := by
  apply (cone f₂).coordinates.injective
  rw [LinearEquiv.apply_symm_apply, mappingCone_coordinates_apply f₂,
    mappingCone_coordinates_apply f₁]
  rfl

section Cancel

variable {K L M : DifferentialGradedModule A} (α : K ⟶ L) (β : L ⟶ M) (f : K ⟶ M)
  (hf : Hom.comp β α = Hom.comp f (Hom.id K))

/-- The underlying linear map of the comparison `C(C(α) ⟶ C(β ∘ α)) ⟶ C(β)`. -/
private noncomputable def mappingConeCancelLinearMap :
    (coneModule (mappingConeMap α f (Hom.id K) β hf)).M →ₗ[R] (coneModule β).M where
  toFun := fun x => (x.1.1, α.toFun x.1.2 + x.2.1)
  map_add' := by
    intro x y
    change (x.1.1 + y.1.1, α.toFun (x.1.2 + y.1.2) + (x.2.1 + y.2.1)) =
      (x.1.1, α.toFun x.1.2 + x.2.1) + (y.1.1, α.toFun y.1.2 + y.2.1)
    refine Prod.ext rfl ?_
    change α.toFun (x.1.2 + y.1.2) + (x.2.1 + y.2.1) =
      (α.toFun x.1.2 + x.2.1) + (α.toFun y.1.2 + y.2.1)
    rw [map_add α.toFun]
    abel
  map_smul' := by
    intro r x
    change (r • x.1.1, α.toFun (r • x.1.2) + r • x.2.1) = r • (x.1.1, α.toFun x.1.2 + x.2.1)
    rw [map_smul α.toFun]
    simp [smul_add]

private theorem mappingConeCancelLinearMap_apply
    (x : (coneModule (mappingConeMap α f (Hom.id K) β hf)).M) :
    mappingConeCancelLinearMap α β f hf x = (x.1.1, α.toFun x.1.2 + x.2.1) := rfl

/-- The underlying linear map of the section of the comparison
`C(C(α) ⟶ C(β ∘ α)) ⟶ C(β)`. -/
private noncomputable def mappingConeCancelSectionLinearMap :
    (coneModule β).M →ₗ[R]
      (coneModule (mappingConeMap α f (Hom.id K) β hf)).M where
  toFun := fun x => ((x.1, (0 : K.M)), (x.2, (0 : K.M)))
  map_add' := by
    intro x y
    change ((x.1 + y.1, (0 : K.M)), (x.2 + y.2, (0 : K.M))) =
      ((x.1, (0 : K.M)), (x.2, (0 : K.M))) + ((y.1, (0 : K.M)), (y.2, (0 : K.M)))
    apply Prod.ext <;> apply Prod.ext <;> simp
  map_smul' := by
    intro r x
    change ((r • x.1, (0 : K.M)), (r • x.2, (0 : K.M))) =
      r • ((x.1, (0 : K.M)), (x.2, (0 : K.M)))
    apply Prod.ext <;> apply Prod.ext <;> simp

private theorem mappingConeCancelSectionLinearMap_apply (x : (coneModule β).M) :
    mappingConeCancelSectionLinearMap α β f hf x = ((x.1, (0 : K.M)), (x.2, (0 : K.M))) := rfl

/-- The comparison `C(C(α) ⟶ C(β ∘ α)) ⟶ C(β)`. -/
private noncomputable def mappingConeCancel :
    coneModule (mappingConeMap α f (Hom.id K) β hf) ⟶ coneModule β where
  toFun := mappingConeCancelLinearMap α β f hf
  map_smul := by
    intro x r
    change (MulOpposite.op r • x.1.1,
        α.toFun (MulOpposite.op r • x.1.2) + MulOpposite.op r • x.2.1) =
      (MulOpposite.op r • x.1.1, MulOpposite.op r • (α.toFun x.1.2 + x.2.1))
    rw [α.map_smul, smul_add]
  map_grading := by
    intro n x hx
    rw [mappingConeCancelLinearMap_apply]
    have hx' := ((cone (mappingConeMap α f (Hom.id K) β hf)).grading_iff n x).mp hx
    have hx₁ := ((cone f).grading_iff n x.1).mp hx'.1
    have hx₂ := ((cone α).grading_iff (n + 1) x.2).mp hx'.2
    have hc₁ : (cone f).coordinates x.1 = x.1 := rfl
    have hc₂ : (cone α).coordinates x.2 = x.2 := rfl
    rw [hc₁] at hx₁
    rw [hc₂] at hx₂
    apply ((cone β).grading_iff n (Prod.mk x.1.1 (α.toFun x.1.2 + x.2.1))).mpr
    have hc₃ : (cone β).coordinates (Prod.mk x.1.1 (α.toFun x.1.2 + x.2.1)) =
        Prod.mk x.1.1 (α.toFun x.1.2 + x.2.1) := rfl
    rw [hc₃]
    exact ⟨hx₁.1, (L.grading (n + 1)).add_mem (α.map_grading (n + 1) x.1.2 hx₁.2) hx₂.1⟩
  map_d := by
    have hcomp (z : K.M) : f.toFun z = β.toFun (α.toFun z) :=
      (congrArg (fun t : Hom K M => t.toFun z) hf).symm
    have hαd (z : K.M) : α.toFun (K.d z) = L.d (α.toFun z) := LinearMap.congr_fun α.map_d z
    apply LinearMap.ext
    intro x
    obtain ⟨⟨m, k⟩, ⟨l, j⟩⟩ := x
    change (M.d m + f.toFun k + β.toFun l,
        α.toFun (-K.d k + j) + -(L.d l + α.toFun j)) =
      (M.d m + β.toFun (α.toFun k + l), -L.d (α.toFun k + l))
    refine Prod.ext ?_ ?_
    · change M.d m + f.toFun k + β.toFun l = M.d m + β.toFun (α.toFun k + l)
      rw [hcomp, map_add β.toFun]
      abel
    · change α.toFun (-K.d k + j) + -(L.d l + α.toFun j) = -L.d (α.toFun k + l)
      rw [map_add α.toFun, map_neg α.toFun, hαd, map_add L.d]
      abel

/-- The section of the comparison `C(C(α) ⟶ C(β ∘ α)) ⟶ C(β)`. -/
private noncomputable def mappingConeCancelSection :
    coneModule β ⟶ coneModule (mappingConeMap α f (Hom.id K) β hf) where
  toFun := mappingConeCancelSectionLinearMap α β f hf
  map_smul := by
    intro x r
    rw [mappingConeCancelSectionLinearMap_apply]
    change Prod.mk (Prod.mk (MulOpposite.op r • x.1) (0 : K.M))
        (Prod.mk (MulOpposite.op r • x.2) (0 : K.M)) =
      MulOpposite.op r • Prod.mk (Prod.mk x.1 (0 : K.M)) (Prod.mk x.2 (0 : K.M))
    refine Prod.ext ?_ ?_
    · apply Prod.ext <;> simp
    · apply Prod.ext <;> simp
  map_grading := by
    intro n x hx
    rw [mappingConeCancelSectionLinearMap_apply]
    have hx' := ((cone β).grading_iff n x).mp hx
    have hcβ : (cone β).coordinates x = x := rfl
    rw [hcβ] at hx'
    apply ((cone (mappingConeMap α f (Hom.id K) β hf)).grading_iff n
      (Prod.mk (Prod.mk x.1 (0 : K.M)) (Prod.mk x.2 (0 : K.M)))).mpr
    refine ⟨?_, ?_⟩
    · apply ((cone f).grading_iff n (Prod.mk x.1 (0 : K.M))).mpr
      have hc : (cone f).coordinates (Prod.mk x.1 (0 : K.M)) =
          Prod.mk x.1 (0 : K.M) := rfl
      rw [hc]
      exact ⟨hx'.1, (K.grading (n + 1)).zero_mem⟩
    · apply ((cone α).grading_iff (n + 1) (Prod.mk x.2 (0 : K.M))).mpr
      have hc : (cone α).coordinates (Prod.mk x.2 (0 : K.M)) =
          Prod.mk x.2 (0 : K.M) := rfl
      rw [hc]
      exact ⟨by simpa using hx'.2, by simp⟩
  map_d := by
    apply LinearMap.ext
    intro x
    obtain ⟨m, l⟩ := x
    refine Prod.ext (Prod.ext ?_ ?_) (Prod.ext ?_ ?_)
    · change M.d m + β.toFun l = M.d m + f.toFun (0 : K.M) + β.toFun l
      simp
    · change (0 : K.M) = -K.d (0 : K.M) + (Hom.id K).toFun (0 : K.M)
      simp
    · change -L.d l = -(L.d l + α.toFun (0 : K.M))
      simp
    · change (0 : K.M) = -(-K.d (0 : K.M))
      simp

/-- The underlying map of the homotopy exhibiting the comparison
`C(C(α) ⟶ C(β ∘ α)) ⟶ C(β)` as a homotopy equivalence. -/
private noncomputable def mappingConeCancelHomotopyLinearMap :
    (coneModule (mappingConeMap α f (Hom.id K) β hf)).M →ₗ[MulOpposite A.A]
      (coneModule (mappingConeMap α f (Hom.id K) β hf)).M where
  toFun := fun x => ((0, (0 : K.M)), (0, x.1.2))
  map_add' := by
    intro x y
    obtain ⟨⟨m, k⟩, ⟨l, j⟩⟩ := x
    obtain ⟨⟨m', k'⟩, ⟨l', j'⟩⟩ := y
    change (((0 : M.M), (0 : K.M)), ((0 : L.M), k + k')) =
      (((0 : M.M), (0 : K.M)), ((0 : L.M), k)) + (((0 : M.M), (0 : K.M)), ((0 : L.M), k'))
    simp
  map_smul' := by
    intro r x
    obtain ⟨⟨m, k⟩, ⟨l, j⟩⟩ := x
    change (((0 : M.M), (0 : K.M)), ((0 : L.M), r • k)) =
      r • (((0 : M.M), (0 : K.M)), ((0 : L.M), k))
    simp

/-- The comparison `C(C(α) ⟶ C(β ∘ α)) ⟶ C(β)` and its section are homotopy inverse. -/
private noncomputable def mappingConeCancelHomotopy :
    Homotopy (Hom.id (coneModule (mappingConeMap α f (Hom.id K) β hf)))
      (Hom.comp (mappingConeCancelSection α β f hf) (mappingConeCancel α β f hf)) where
  toLinearMap := mappingConeCancelHomotopyLinearMap α β f hf
  map_grading := by
    intro n x hx
    obtain ⟨⟨m, k⟩, ⟨l, j⟩⟩ := x
    change (m ∈ M.grading n ∧ k ∈ K.grading (n + 1)) ∧
      (l ∈ L.grading (n + 1) ∧ j ∈ K.grading (n + 1 + 1)) at hx
    change ((0 : M.M) ∈ M.grading (n - 1) ∧ (0 : K.M) ∈ K.grading (n - 1 + 1)) ∧
      ((0 : L.M) ∈ L.grading (n - 1 + 1) ∧ k ∈ K.grading (n - 1 + 1 + 1))
    refine ⟨⟨Submodule.zero_mem _, Submodule.zero_mem _⟩, Submodule.zero_mem _, ?_⟩
    simpa only [show n - 1 + 1 + 1 = n + 1 by omega] using hx.1.2
  homotopy_eq := by
    intro x
    obtain ⟨⟨m, k⟩, ⟨l, j⟩⟩ := x
    refine Prod.ext (Prod.ext ?_ ?_) (Prod.ext ?_ ?_)
    · change m - m = M.d (0 : M.M) + f.toFun (0 : K.M) + β.toFun (0 : L.M) + (0 : M.M)
      simp
    · change k - (0 : K.M) = -K.d (0 : K.M) + (Hom.id K).toFun k + (0 : K.M)
      simp [Hom.id]
    · change l - (α.toFun k + l) = -(L.d (0 : L.M) + α.toFun k) + (0 : L.M)
      simp
    · change j - (0 : K.M) = -(-K.d k) + (-K.d k + j)
      simp

/-- The underlying map of the homotopy identifying the connecting arrow of the cone of
`C(α) ⟶ C(β ∘ α)` with the one coming from `C(β)`. -/
private noncomputable def mappingConeCancelBoundaryLinearMap :
    (coneModule (mappingConeMap α f (Hom.id K) β hf)).M →ₗ[MulOpposite A.A]
      (shift (coneModule α) 1).M where
  toFun := fun x => ((0 : L.M), -x.1.2)
  map_add' := by
    intro x y
    change ((0 : L.M), -(x.1.2 + y.1.2)) = ((0 : L.M), -x.1.2) + ((0 : L.M), -y.1.2)
    refine Prod.ext ?_ ?_ <;> simp [add_comm]
  map_smul' := by
    intro r x
    change ((0 : L.M), -(r • x.1.2)) = r • ((0 : L.M), -x.1.2)
    simp

private theorem mappingConeCancelBoundaryLinearMap_apply
    (x : (coneModule (mappingConeMap α f (Hom.id K) β hf)).M) :
    mappingConeCancelBoundaryLinearMap α β f hf x = (0, -x.1.2) := rfl

/-- The connecting arrow of the cone of `C(α) ⟶ C(β ∘ α)` agrees, up to homotopy, with the
composite of the comparison with the connecting arrow of `C(β)`. -/
private noncomputable def mappingConeCancelBoundaryHomotopy :
    Homotopy (-coneProjection (mappingConeMap α f (Hom.id K) β hf))
      (mappingConeCancel α β f hf ≫ (-coneProjection β) ≫
        shiftMap (coneInclusion α) 1) where
  toLinearMap := mappingConeCancelBoundaryLinearMap α β f hf
  map_grading := by
    intro n x hx
    rw [mappingConeCancelBoundaryLinearMap_apply]
    change (0, -x.1.2) ∈ (shift (coneModule α) 1).grading (n - 1)
    rw [shift_grading, show n - 1 + 1 = n by omega]
    have hx' := ((cone (mappingConeMap α f (Hom.id K) β hf)).grading_iff n x).mp hx
    have hx₁ := ((cone f).grading_iff n x.1).mp hx'.1
    have hc : (cone f).coordinates x.1 = x.1 := rfl
    rw [hc] at hx₁
    exact ((cone α).grading_iff n (0, -x.1.2)).mpr
      ⟨(L.grading n).zero_mem, (K.grading (n + 1)).neg_mem hx₁.2⟩
  homotopy_eq := by
    intro x
    rcases x with ⟨⟨m, k⟩, ⟨l, j⟩⟩
    have hleft : (-coneProjection (mappingConeMap α f (Hom.id K) β hf)).toFun
        ((m, k), (l, j)) = ((-l, -j) : (shift (coneModule α) 1).M) := by
      change -(coneProjection (mappingConeMap α f (Hom.id K) β hf)).toFun
        ((m, k), (l, j)) = (-l, -j)
      rfl
    have hright : (mappingConeCancel α β f hf ≫ (-coneProjection β) ≫
        shiftMap (coneInclusion α) 1).toFun ((m, k), (l, j)) =
        ((-l - α.toFun k, (0 : K.M)) : (shift (coneModule α) 1).M) := by
      change (coneInclusion α).toFun
          (-(coneProjection β).toFun
            ((mappingConeCancel α β f hf).toFun ((m, k), (l, j)))) =
        ((-l - α.toFun k, (0 : K.M)) : (shift (coneModule α) 1).M)
      change (-(α.toFun k + l), (0 : K.M)) = (-l - α.toFun k, (0 : K.M))
      refine Prod.ext ?_ ?_
      · change -(α.toFun k + l) = -l - α.toFun k
        abel
      · rfl
    have hdh : (shift (coneModule α) 1).d
        (mappingConeCancelBoundaryLinearMap α β f hf ((m, k), (l, j))) =
        (α.toFun k, -K.d k) := by
      change (shift (coneModule α) 1).d
          ((0, -k) : (shift (coneModule α) 1).M) = (α.toFun k, -K.d k)
      rw [shift_d, Int.negOnePow_one, Units.smul_def]
      change (-1 : ℤ) • ((coneModule α).d ((0, -k) : (coneModule α).M)) =
        (α.toFun k, -K.d k)
      rw [neg_one_zsmul]
      change -((coneModule α).d (0, -k)) = (α.toFun k, -K.d k)
      change -(L.d 0 + α.toFun (-k), -K.d (-k)) = (α.toFun k, -K.d k)
      simp [map_neg]
    have hmapd : mappingConeCancelBoundaryLinearMap α β f hf
        ((coneModule (mappingConeMap α f (Hom.id K) β hf)).d ((m, k), (l, j))) =
        (0, K.d k - j) := by
      rw [mappingConeCancelBoundaryLinearMap_apply]
      change ((0 : L.M), -(-K.d k + j)) = ((0 : L.M), K.d k - j)
      refine Prod.ext rfl ?_
      change -(-K.d k + j) = K.d k - j
      abel
    rw [hdh, hmapd]
    calc
      _ = (((-l, -j) : (shift (coneModule α) 1).M) -
          ((-l - α.toFun k, (0 : K.M)) : (shift (coneModule α) 1).M)) := by
            rw [hleft, hright]
            rfl
      _ = (α.toFun k, -K.d k) + (0, K.d k - j) := by
            refine Prod.ext ?_ ?_
            · change -l - (-l - α.toFun k) = α.toFun k + 0
              abel
            · change -j - (0 : K.M) = -K.d k + (K.d k - j)
              abel

end Cancel

/-- Two composable homomorphisms of differential graded modules have distinguished triangles
forming an octahedron. -/
@[stacks 09KI]
theorem octahedron_of_isAdmissibleMono {K L M : DifferentialGradedModule A}
    (α : Hom K L) (β : Hom L M) (_hα : IsAdmissibleMono α) (_hβ : IsAdmissibleMono β) :
    let q := toHomotopyCategory A
    ∃ (Q₁ Q₂ Q₃ : HomotopyCategory A)
      (p₁ : q.obj L ⟶ Q₁) (d₁ : Q₁ ⟶ (q.obj K)⟦(1 : ℤ)⟧)
      (p₂ : q.obj M ⟶ Q₂) (d₂ : Q₂ ⟶ (q.obj K)⟦(1 : ℤ)⟧)
      (p₃ : q.obj M ⟶ Q₃) (d₃ : Q₃ ⟶ (q.obj L)⟦(1 : ℤ)⟧)
      (a : Q₁ ⟶ Q₂) (b : Q₂ ⟶ Q₃),
      IsDistinguishedTriangle A (Pretriangulated.Triangle.mk (q.map α) p₁ d₁) ∧
      IsDistinguishedTriangle A
        (Pretriangulated.Triangle.mk (q.map α ≫ q.map β) p₂ d₂) ∧
      IsDistinguishedTriangle A (Pretriangulated.Triangle.mk (q.map β) p₃ d₃) ∧
      (p₁ ≫ a = q.map β ≫ p₂) ∧
      (a ≫ d₂ = d₁) ∧
      (p₂ ≫ b = p₃) ∧
      (d₂ ≫ (q.map α)⟦1⟧' = b ≫ d₃) ∧
      IsDistinguishedTriangle A
        (Pretriangulated.Triangle.mk a b (d₃ ≫ p₁⟦1⟧')) := by
  let q := toHomotopyCategory A
  let f := Hom.comp β α
  have hf : Hom.comp β α = Hom.comp f (Hom.id K) := by
    apply Hom.ext
    rfl
  have hf' : Hom.comp (Hom.id M) f = Hom.comp β α := by
    apply Hom.ext
    rfl
  let g := mappingConeMap α f (Hom.id K) β hf
  let h := mappingConeMap f β α (Hom.id M) hf'
  let Q₁ := q.obj (coneModule α)
  let Q₂ := q.obj (coneModule f)
  let Q₃ := q.obj (coneModule β)
  let cK := eqToHom (toHomotopyCategory_obj_shift A K 1).symm
  let cL := eqToHom (toHomotopyCategory_obj_shift A L 1).symm
  let cCone := eqToHom (toHomotopyCategory_obj_shift A (coneModule α) 1).symm
  let p₁ := q.map (coneInclusion α)
  let d₁ := q.map (-coneProjection α) ≫ cK
  let p₂ := q.map (coneInclusion f)
  let d₂ := q.map (-coneProjection f) ≫ cK
  let p₃ := q.map (coneInclusion β)
  let d₃ := q.map (-coneProjection β) ≫ cL
  let a := q.map g
  let b := q.map h
  have hT₁ : IsDistinguishedTriangle A (mappingConeTriangle α) :=
    isDistinguishedTriangle_mappingConeTriangle A α
  have hT₂ : IsDistinguishedTriangle A (mappingConeTriangle f) :=
    isDistinguishedTriangle_mappingConeTriangle A f
  have hT₃ : IsDistinguishedTriangle A (mappingConeTriangle β) :=
    isDistinguishedTriangle_mappingConeTriangle A β
  have hinc₁ : coneInclusion α ≫ g = β ≫ coneInclusion f := by
    apply Hom.ext
    apply LinearMap.ext
    intro x
    change (β.toFun x, (0 : K.M)) = (β.toFun x, 0)
    rfl
  have hproj : g ≫ (-coneProjection f) = -coneProjection α := by
    apply Hom.ext
    apply LinearMap.ext
    intro x
    obtain ⟨l, k⟩ := x
    change -k = -k
    rfl
  have hinc₂ : coneInclusion f ≫ h = coneInclusion β := by
    apply Hom.ext
    apply LinearMap.ext
    intro x
    change (x, α.toFun 0) = (x, 0)
    simp
  have hcancelIncl : coneInclusion g ≫ mappingConeCancel α β f hf = h := by
    apply Hom.ext
    apply LinearMap.ext
    intro x
    obtain ⟨m, k⟩ := x
    change (m, α.toFun k + 0) = (m, α.toFun k)
    simp
  have hproj₂ : (-coneProjection f) ≫ shiftMap α 1 =
      h ≫ (-coneProjection β) := by
    apply Hom.ext
    apply LinearMap.ext
    intro x
    obtain ⟨m, k⟩ := x
    change α.toFun (-k) = -(α.toFun k)
    rw [map_neg]
  have hboundary : Homotopic (-coneProjection g)
      (mappingConeCancel α β f hf ≫ (-coneProjection β) ≫
        shiftMap (coneInclusion α) 1) :=
    ⟨mappingConeCancelBoundaryHomotopy α β f hf⟩
  have hboundaryEq := quotient_map_eq_of_homotopic hboundary
  have hcancelRight : mappingConeCancelSection α β f hf ≫ mappingConeCancel α β f hf =
      Hom.id (coneModule β) := by
    apply Hom.ext
    apply LinearMap.ext
    intro x
    change (x.1, α.toFun 0 + x.2) = (x.1, x.2)
    simp
  let qCancel := q.map (mappingConeCancel α β f hf)
  let qSection := q.map (mappingConeCancelSection α β f hf)
  have hcancelLeft : qCancel ≫ qSection = 𝟙 (q.obj (coneModule g)) := by
    rw [← Functor.map_comp]
    exact (quotient_map_eq_of_homotopic ⟨mappingConeCancelHomotopy α β f hf⟩).symm.trans
      (q.map_id _)
  have hcancelRight' : qSection ≫ qCancel = 𝟙 (q.obj (coneModule β)) := by
    rw [← Functor.map_comp]
    exact (congrArg q.map hcancelRight).trans (q.map_id _)
  let e₃ : q.obj (coneModule g) ≅ q.obj (coneModule β) :=
    { hom := qCancel
      inv := qSection
      hom_inv_id := hcancelLeft
      inv_hom_id := hcancelRight' }
  let T₄ := mappingConeTriangle g
  let T₄' := Pretriangulated.Triangle.mk a b (d₃ ≫ p₁⟦1⟧')
  have hthird : T₄.mor₂ ≫ e₃.hom = b := by
    dsimp only [T₄, e₃, b, h, mappingConeTriangle, Pretriangulated.Triangle.mk]
    rw [← Functor.map_comp, hcancelIncl]
  have hshiftCone : cCone = (q.commShiftIso (1 : ℤ)).hom.app (coneModule α) :=
    (toHomotopyCategory_commShiftIso_hom_app A (coneModule α) 1).symm
  have hshiftL : cL = (q.commShiftIso (1 : ℤ)).hom.app L :=
    (toHomotopyCategory_commShiftIso_hom_app A L 1).symm
  have hshiftK : cK = (q.commShiftIso (1 : ℤ)).hom.app K :=
    (toHomotopyCategory_commShiftIso_hom_app A K 1).symm
  have hnat {X Y : DifferentialGradedModule A} (u : X ⟶ Y) :
      q.map (shiftMap u 1) ≫ (q.commShiftIso (1 : ℤ)).hom.app Y =
        (q.commShiftIso (1 : ℤ)).hom.app X ≫
          (CategoryTheory.shiftFunctor (HomotopyCategory A) (1 : ℤ)).map (q.map u) :=
    q.commShiftIso_hom_naturality (X := X) (Y := Y) u (1 : ℤ)
  have hthirdArrow : T₄.mor₃ ≫ (𝟙 T₄.obj₁)⟦1⟧' = e₃.hom ≫ T₄'.mor₃ := by
    let S := CategoryTheory.shiftFunctor (HomotopyCategory A) (1 : ℤ)
    change (q.map (-coneProjection g) ≫ cCone) ≫
        S.map (𝟙 (q.obj (coneModule α))) =
      q.map (mappingConeCancel α β f hf) ≫
        (q.map (-coneProjection β) ≫ cL) ≫ S.map (q.map (coneInclusion α))
    have hmapid : S.map (𝟙 (q.obj (coneModule α))) =
        𝟙 (S.obj (q.obj (coneModule α))) := S.map_id _
    have hnatIncl := hnat (coneInclusion α)
    calc
      (q.map (-coneProjection g) ≫ cCone) ≫
          S.map (𝟙 (q.obj (coneModule α))) =
        q.map (-coneProjection g) ≫ cCone := by
          rw [hmapid, Category.comp_id]
      _ = q.map (-coneProjection g) ≫
          (q.commShiftIso (1 : ℤ)).hom.app (coneModule α) := by rw [hshiftCone]
      _ = q.map (mappingConeCancel α β f hf ≫ (-coneProjection β) ≫
            shiftMap (coneInclusion α) 1) ≫
            (q.commShiftIso (1 : ℤ)).hom.app (coneModule α) :=
          congrArg (fun z => z ≫ (q.commShiftIso (1 : ℤ)).hom.app (coneModule α))
            hboundaryEq
      _ = q.map (mappingConeCancel α β f hf) ≫
            q.map (-coneProjection β) ≫
              q.map (shiftMap (coneInclusion α) 1) ≫
                (q.commShiftIso (1 : ℤ)).hom.app (coneModule α) := by
          simp only [Functor.map_comp, Category.assoc]
      _ = q.map (mappingConeCancel α β f hf) ≫
            (q.map (-coneProjection β) ≫ cL) ≫
              S.map (q.map (coneInclusion α)) := by
          rw [hnatIncl, ← hshiftL]
          simp only [Category.assoc]
          rfl
  have e₄ : T₄ ≅ T₄' :=
    Pretriangulated.Triangle.isoMk T₄ T₄' (Iso.refl _) (Iso.refl _) e₃
      (by change q.map g = q.map g; rfl) hthird hthirdArrow
  have hT₄ : IsDistinguishedTriangle A T₄' :=
    isDistinguishedTriangle_of_iso A e₄ (isDistinguishedTriangle_mappingConeTriangle A g)
  refine ⟨Q₁, Q₂, Q₃, p₁, d₁, p₂, d₂, p₃, d₃, a, b, ?_, ?_, ?_, ?_, ?_, ?_, ?_, hT₄⟩
  · change IsDistinguishedTriangle A (mappingConeTriangle α)
    exact hT₁
  · change IsDistinguishedTriangle A (mappingConeTriangle f)
    exact hT₂
  · change IsDistinguishedTriangle A (mappingConeTriangle β)
    exact hT₃
  · dsimp only [p₁, a, p₂, q]
    rw [← Functor.map_comp, hinc₁, Functor.map_comp]
  · dsimp only [a, d₂, d₁, q]
    rw [← Category.assoc, ← Functor.map_comp, hproj]
  · dsimp only [p₂, b, p₃, q]
    rw [← Functor.map_comp, hinc₂]
  · dsimp only [d₂, b, d₃, q]
    rw [Category.assoc, hshiftK, ← hnat α, ← hshiftL, ← Category.assoc,
      ← Functor.map_comp, hproj₂, Functor.map_comp, Category.assoc]

end DifferentialGradedModule
