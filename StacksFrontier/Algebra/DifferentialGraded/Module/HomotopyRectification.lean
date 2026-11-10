module

public import StacksCore.Tactic.StacksAttribute
public import StacksFrontier.Algebra.DifferentialGraded.Module.Admissible
public import StacksFrontier.Algebra.DifferentialGraded.Module.CochainComplex
public import StacksFrontier.Algebra.DifferentialGraded.Module.HomotopyCategory

/-!
# Rectifying homotopy-commutative squares of differential graded modules

A square of homomorphisms of right differential graded modules which commutes only up to a
chosen homotopy can be made to commute strictly, at the cost of replacing one of its vertical
arrows by a homotopic one, as soon as one of its horizontal arrows is admissible: an admissible
epimorphism along the bottom rectifies the left arrow, an admissible monomorphism along the top
rectifies the right arrow.

As an application, a map into the middle term of an admissible short exact sequence which becomes
null-homotopic after projection, followed by a map out of the middle term which is null-homotopic
on the sub-object, has null-homotopic composite.

## Main results

* `DifferentialGradedModule.HomotopyCommutativeSquare.exists_rectification_of_isAdmissibleEpi`
  and
  `DifferentialGradedModule.HomotopyCommutativeSquare.exists_rectification_of_isAdmissibleMono`:
  the two rectifications.
* `DifferentialGradedModule.comp_homotopic_zero_of_isAdmissibleShortExact`: the null-homotopy of
  the composite.

## Implementation notes

In both rectifications the replacement arrow differs from the original by the commutator
`d ∘ H + H ∘ d` of the differentials with a degree `-1` map `H` built from the chosen homotopy
and the graded splitting. That commutator is a homomorphism of differential graded modules: it is
right `A`-linear by `commutator_map_smul`, which is proved by induction over the direct-sum
decomposition of the source, and it commutes with the differentials because they square to zero.

For the null-homotopy only the middle short exact sequence of the source is needed: its
projection rectifies the first map and its inclusion rectifies the second. The other two short
exact sequences and the other two squares of the source formulation impose no further conditions
on the conclusion.

## References

* [Stacks Project, Tag 09JV](https://stacks.math.columbia.edu/tag/09JV)
* [Stacks Project, Tag 09JY](https://stacks.math.columbia.edu/tag/09JY)
-/

@[expose] public section

namespace DifferentialGradedModule

universe u v w

variable {R : Type u} [CommRing R] {A : DifferentialGradedAlgebra.{u, v} R}

section Commutator

variable {M N : DifferentialGradedModule.{u, v, w} A}

/-- The commutator `d ∘ H + H ∘ d` of the differentials with a right `A`-linear map `H` of degree
`-1` is again right `A`-linear: the two Leibniz corrections cancel because the signs
`(-1)^n` and `(-1)^{n-1}` are opposite. -/
private theorem commutator_map_smul (H : M.M →ₗ[MulOpposite A.A] N.M)
    (hH : ∀ (n : ℤ) (x : M.M), x ∈ M.grading n → H x ∈ N.grading (n - 1))
    (x : M.M) (a : A.A) :
    (N.d.comp (H.restrictScalars R) + (H.restrictScalars R).comp M.d)
        (MulOpposite.op a • x) =
      MulOpposite.op a • (N.d.comp (H.restrictScalars R) +
        (H.restrictScalars R).comp M.d) x := by
  let Hlin : M.M →ₗ[R] N.M := H.restrictScalars R
  let D : M.M →ₗ[R] N.M := N.d.comp Hlin + Hlin.comp M.d
  change D (MulOpposite.op a • x) = MulOpposite.op a • D x
  induction x using DirectSum.Decomposition.inductionOn M.grading with
    | zero => simp [D]
    | @homogeneous n y =>
        have hy : (y : M.M) ∈ M.grading n := y.property
        have hHy : H y ∈ N.grading (n - 1) := hH n y hy
        have hHsmul : Hlin (MulOpposite.op a • (y : M.M)) =
            MulOpposite.op a • Hlin y := H.map_smul (MulOpposite.op a) y
        have hLd : M.d (MulOpposite.op a • (y : M.M)) =
            MulOpposite.op a • M.d y + (n.negOnePow : ℤ) •
              (MulOpposite.op (A.d a) • (y : M.M)) := M.leibniz_apply n y hy a
        have hNd : N.d (MulOpposite.op a • Hlin y) =
            MulOpposite.op a • N.d (Hlin y) + ((n - 1).negOnePow : ℤ) •
              (MulOpposite.op (A.d a) • Hlin y) :=
          N.leibniz_apply (n - 1) (Hlin y) (by simpa [Hlin] using hHy) a
        have hHsmul2 : Hlin (MulOpposite.op (A.d a) • (y : M.M)) =
            MulOpposite.op (A.d a) • Hlin y := H.map_smul (MulOpposite.op (A.d a)) y
        have hHsmulD : Hlin (MulOpposite.op a • M.d (y : M.M)) =
            MulOpposite.op a • Hlin (M.d y) := H.map_smul (MulOpposite.op a) (M.d y)
        have hZsmul : Hlin ((n.negOnePow : ℤ) •
            (MulOpposite.op (A.d a) • (y : M.M))) =
            (n.negOnePow : ℤ) • Hlin (MulOpposite.op (A.d a) • (y : M.M)) :=
          map_zsmul Hlin _ _
        have hsign : ((n - 1).negOnePow : ℤ) = -(n.negOnePow : ℤ) := by
          rw [Int.negOnePow_sub]
          simp
        change D (MulOpposite.op a • (y : M.M)) = MulOpposite.op a • D y
        dsimp [D]
        rw [hHsmul, hNd]
        rw [hLd, map_add, hZsmul, hHsmul2, hHsmulD]
        rw [smul_add, hsign]
        simp only [neg_smul]
        abel
    | add y z ihy ihz =>
        simpa only [smul_add, map_add] using congrArg₂ (· + ·) ihy ihz

/-- The commutator `d ∘ H + H ∘ d` of the differentials with a map `H` of degree `-1` preserves
the grading. -/
private theorem commutator_mem_grading (H : M.M →ₗ[MulOpposite A.A] N.M)
    (hH : ∀ (n : ℤ) (x : M.M), x ∈ M.grading n → H x ∈ N.grading (n - 1))
    (n : ℤ) (x : M.M) (hx : x ∈ M.grading n) :
    (N.d.comp (H.restrictScalars R) + (H.restrictScalars R).comp M.d) x ∈ N.grading n := by
  apply (N.grading n).add_mem
  · simpa [sub_add_cancel] using N.d_mem (n - 1) (H x) (hH n x hx)
  · simpa using hH (n + 1) (M.d x) (M.d_mem n x hx)

/-- The commutator `d ∘ H + H ∘ d` of the differentials with a map `H` commutes with `d`. -/
private theorem commutator_comm_d (H : M.M →ₗ[MulOpposite A.A] N.M) (x : M.M) :
    N.d ((N.d.comp (H.restrictScalars R) + (H.restrictScalars R).comp M.d) x) =
      (N.d.comp (H.restrictScalars R) + (H.restrictScalars R).comp M.d) (M.d x) := by
  have hNdd : N.d (N.d (H x)) = 0 := LinearMap.congr_fun N.d_comp_d (H x)
  have hMdd : M.d (M.d x) = 0 := LinearMap.congr_fun M.d_comp_d x
  simp [hNdd, hMdd]

end Commutator

namespace HomotopyCommutativeSquare

/-- An admissible epimorphism along the bottom of a homotopy-commutative square permits a
homotopic replacement of the left vertical arrow making the square commute strictly. -/
theorem exists_rectification_of_isAdmissibleEpi (S : HomotopyCommutativeSquare A)
    (hg : IsAdmissibleEpi S.g) :
    ∃ a' : Hom S.K S.M, Homotopic S.a a' ∧ Hom.comp S.g a' = Hom.comp S.b S.f := by
  obtain ⟨s, hs⟩ := hg
  let h₀ := S.h
  let H₀ := h₀.toLinearMap
  let H : S.K.M →ₗ[MulOpposite A.A] S.M.M :=
    { toFun := fun x => s.toFun (H₀ x)
      map_add' := by intro x y; simp only [H₀.map_add, s.toFun.map_add]
      map_smul' := by
        intro c x
        change s.toFun (H₀ (c • x)) = c • s.toFun (H₀ x)
        rw [H₀.map_smul c x]
        simpa using s.map_smul (H₀ x) (MulOpposite.unop c) }
  let Hlin : S.K.M →ₗ[R] S.M.M := H.restrictScalars R
  have hHgrade (n : ℤ) (x : S.K.M) (hx : x ∈ S.K.grading n) :
      H x ∈ S.M.grading (n - 1) :=
    s.map_grading (n - 1) (H₀ x) (h₀.map_grading n x hx)
  let C : S.K.M →ₗ[R] S.M.M := S.M.d.comp Hlin + Hlin.comp S.K.d
  have hCsmul (x : S.K.M) (a : A.A) :
      C (MulOpposite.op a • x) = MulOpposite.op a • C x :=
    commutator_map_smul H hHgrade x a
  have hCgrade (n : ℤ) (x : S.K.M) (hx : x ∈ S.K.grading n) : C x ∈ S.M.grading n :=
    commutator_mem_grading H hHgrade n x hx
  have hCd (x : S.K.M) : S.M.d (C x) = C (S.K.d x) := commutator_comm_d H x
  let a' : Hom S.K S.M :=
    { toFun := S.a.toFun + C
      map_smul := by
        intro x a
        simp only [LinearMap.add_apply, S.a.map_smul, hCsmul, smul_add]
      map_grading := by
        intro n x hx
        exact (S.M.grading n).add_mem (S.a.map_grading n x hx) (hCgrade n x hx)
      map_d := by
        ext x
        simp only [LinearMap.comp_apply, LinearMap.add_apply]
        have ha := LinearMap.congr_fun S.a.map_d x
        simp only [LinearMap.comp_apply] at ha
        rw [map_add, ha, hCd] }
  refine ⟨a', ?_, ?_⟩
  · refine ⟨⟨-H, ?_, ?_⟩⟩
    · intro n x hx
      exact Submodule.neg_mem _ (hHgrade n x hx)
    · intro x
      change S.a.toFun x - (S.a.toFun x + C x) = S.M.d (-H x) + (-H) (S.K.d x)
      simp only [map_neg, LinearMap.neg_apply]
      dsimp [C, Hlin]
      abel
  · ext x
    change S.g.toFun (a'.toFun x) = S.b.toFun (S.f.toFun x)
    have hgHx : S.g.toFun (H x) = H₀ x := hs (H₀ x)
    have hgHKdx : S.g.toFun (H (S.K.d x)) = H₀ (S.K.d x) := hs (H₀ (S.K.d x))
    have hgMd : S.g.toFun (S.M.d (H x)) = S.N.d (S.g.toFun (H x)) := by
      simpa using LinearMap.congr_fun S.g.map_d (H x)
    have hCg : S.g.toFun (C x) = S.N.d (H₀ x) + H₀ (S.K.d x) := by
      change S.g.toFun (S.M.d (H x) + H (S.K.d x)) = _
      rw [map_add, hgMd, hgHx, hgHKdx]
    have hrel : S.b.toFun (S.f.toFun x) - S.g.toFun (S.a.toFun x) =
        S.N.d (H₀ x) + H₀ (S.K.d x) := by
      simpa [Hom.comp] using h₀.homotopy_eq x
    change S.g.toFun (S.a.toFun x + C x) = S.b.toFun (S.f.toFun x)
    rw [map_add, hCg, ← hrel]
    abel

/-- An admissible monomorphism along the top of a homotopy-commutative square permits a
homotopic replacement of the right vertical arrow making the square commute strictly. -/
theorem exists_rectification_of_isAdmissibleMono (S : HomotopyCommutativeSquare A)
    (hf : IsAdmissibleMono S.f) :
    ∃ b' : Hom S.L S.N, Homotopic S.b b' ∧ Hom.comp b' S.f = Hom.comp S.g S.a := by
  obtain ⟨π, hπ⟩ := hf
  let h₀ := S.h
  let H₀ := h₀.toLinearMap
  let H : S.L.M →ₗ[MulOpposite A.A] S.N.M :=
    { toFun := fun x => H₀ (π.toFun x)
      map_add' := by intro x y; simp only [π.toFun.map_add, map_add]
      map_smul' := by
        intro c x
        change H₀ (π.toFun (MulOpposite.op (MulOpposite.unop c) • x)) = c • H₀ (π.toFun x)
        rw [π.map_smul x (MulOpposite.unop c)]
        exact H₀.map_smul c (π.toFun x) }
  let Hlin : S.L.M →ₗ[R] S.N.M := H.restrictScalars R
  have hHgrade (n : ℤ) (x : S.L.M) (hx : x ∈ S.L.grading n) :
      H x ∈ S.N.grading (n - 1) :=
    h₀.map_grading n (π.toFun x) (π.map_grading n x hx)
  let C : S.L.M →ₗ[R] S.N.M := S.N.d.comp Hlin + Hlin.comp S.L.d
  have hCsmul (x : S.L.M) (a : A.A) :
      C (MulOpposite.op a • x) = MulOpposite.op a • C x :=
    commutator_map_smul H hHgrade x a
  have hCgrade (n : ℤ) (x : S.L.M) (hx : x ∈ S.L.grading n) : C x ∈ S.N.grading n :=
    commutator_mem_grading H hHgrade n x hx
  have hCd (x : S.L.M) : S.N.d (C x) = C (S.L.d x) := commutator_comm_d H x
  let b' : Hom S.L S.N :=
    { toFun := S.b.toFun - C
      map_smul := by
        intro x a
        simp only [LinearMap.sub_apply, S.b.map_smul, hCsmul, smul_sub]
      map_grading := by
        intro n x hx
        exact (S.N.grading n).sub_mem (S.b.map_grading n x hx) (hCgrade n x hx)
      map_d := by
        ext x
        simp only [LinearMap.comp_apply, LinearMap.sub_apply]
        have hb := LinearMap.congr_fun S.b.map_d x
        simp only [LinearMap.comp_apply] at hb
        rw [map_sub, ← hb, hCd] }
  refine ⟨b', ?_, ?_⟩
  · refine ⟨⟨H, hHgrade, ?_⟩⟩
    intro x
    change S.b.toFun x - (S.b.toFun x - C x) = C x
    abel_nf
  · ext x
    have hLdf : S.L.d (S.f.toFun x) = S.f.toFun (S.K.d x) := by
      simpa using (LinearMap.congr_fun S.f.map_d x).symm
    have hhom : S.b.toFun (S.f.toFun x) - S.g.toFun (S.a.toFun x) =
        S.N.d (H₀ x) + H₀ (S.K.d x) := by
      simpa [Hom.comp] using h₀.homotopy_eq x
    have hCfx : C (S.f.toFun x) = S.N.d (H₀ x) + H₀ (S.K.d x) := by
      change S.N.d (H (S.f.toFun x)) + H (S.L.d (S.f.toFun x)) = _
      rw [hLdf]
      simp [H, hπ]
    change S.b.toFun (S.f.toFun x) - C (S.f.toFun x) = S.g.toFun (S.a.toFun x)
    rw [hCfx, ← hhom]
    abel

end HomotopyCommutativeSquare

section NullHomotopy

variable {L₁ K₂ L₂ M₂ L₃ : DifferentialGradedModule.{u, v, w} A}

/-- A homomorphism of differential graded modules, as a map of the underlying right
`A`-modules. -/
private def Hom.toOppositeLinearMap {M N : DifferentialGradedModule.{u, v, w} A} (f : Hom M N) :
    M.M →ₗ[MulOpposite A.A] N.M where
  toFun := f.toFun
  map_add' := f.toFun.map_add
  map_smul' a x := f.map_smul x (MulOpposite.unop a)

/-- Homotopies of the two factors of a composite compose to a homotopy of the composites. -/
private def homotopyComp {M₁ M₂ M₃ : DifferentialGradedModule.{u, v, w} A}
    {f₂ g₂ : Hom M₂ M₃} {f₁ g₁ : Hom M₁ M₂}
    (h₂ : Homotopy f₂ g₂) (h₁ : Homotopy f₁ g₁) :
    Homotopy (Hom.comp f₂ f₁) (Hom.comp g₂ g₁) where
  toLinearMap := h₂.toLinearMap.comp (Hom.toOppositeLinearMap f₁) +
    (Hom.toOppositeLinearMap g₂).comp h₁.toLinearMap
  map_grading n x hx := by
    change h₂.toLinearMap (f₁.toFun x) + g₂.toFun (h₁.toLinearMap x) ∈ _
    exact (M₃.grading (n - 1)).add_mem
      (h₂.map_grading n (f₁.toFun x) (f₁.map_grading n x hx))
      (g₂.map_grading (n - 1) (h₁.toLinearMap x) (h₁.map_grading n x hx))
  homotopy_eq x := by
    have hf₁d : M₂.d (f₁.toFun x) = f₁.toFun (M₁.d x) := by
      simpa using (LinearMap.congr_fun f₁.map_d x).symm
    have hg₂d : g₂.toFun (M₂.d (h₁.toLinearMap x)) =
        M₃.d (g₂.toFun (h₁.toLinearMap x)) := by
      simpa using LinearMap.congr_fun g₂.map_d (h₁.toLinearMap x)
    simp only [LinearMap.add_apply, LinearMap.comp_apply, map_add]
    change f₂.toFun (f₁.toFun x) - g₂.toFun (g₁.toFun x) =
      M₃.d (h₂.toLinearMap (f₁.toFun x)) + M₃.d (g₂.toFun (h₁.toLinearMap x)) +
        (h₂.toLinearMap (f₁.toFun (M₁.d x)) + g₂.toFun (h₁.toLinearMap (M₁.d x)))
    rw [← hf₁d, ← hg₂d]
    calc
      _ = (f₂.toFun (f₁.toFun x) - g₂.toFun (f₁.toFun x)) +
          g₂.toFun (f₁.toFun x - g₁.toFun x) := by rw [map_sub]; abel
      _ = _ := by rw [h₂.homotopy_eq, h₁.homotopy_eq, map_add]; abel

/-- A map which becomes null-homotopic after projection onto the quotient, followed by a map
which is null-homotopic on the sub-object, has null-homotopic composite. -/
@[stacks 09JY]
theorem comp_homotopic_zero_of_isAdmissibleShortExact
    (f₂ : Hom K₂ L₂) (g₂ : Hom L₂ M₂) (h₂ : IsAdmissibleShortExact f₂ g₂)
    (b : Hom L₁ L₂) (b' : Hom L₂ L₃)
    (hright₁ : Homotopic (Hom.comp g₂ b) 0)
    (hleft₂ : Homotopic (Hom.comp b' f₂) 0) :
    Homotopic (Hom.comp b' b) 0 := by
  let S₁ : HomotopyCommutativeSquare A := {
    K := L₁, L := L₁, M := L₂, N := M₂
    f := Hom.id L₁, a := b, b := 0, g := g₂
    h := (Classical.choice hright₁).symm }
  obtain ⟨b₁, hb₁, hgb₁⟩ :=
    S₁.exists_rectification_of_isAdmissibleEpi h₂.admissibleEpi
  let S₂ : HomotopyCommutativeSquare A := {
    K := K₂, L := L₂, M := K₂, N := L₃
    f := f₂, a := Hom.id K₂, b := b', g := 0
    h := Classical.choice hleft₂ }
  obtain ⟨b₂, hb₂, hb₂f⟩ :=
    S₂.exists_rectification_of_isAdmissibleMono h₂.admissibleMono
  have hzero : Hom.comp b₂ b₁ = 0 := by
    ext x
    have hx : b₁.toFun x ∈ LinearMap.ker g₂.toFun := by
      change g₂.toFun (b₁.toFun x) = 0
      have := congrArg (fun f : Hom L₁ M₂ => f.toFun x) hgb₁
      simpa [S₁, Hom.comp, Hom.zero, Hom.id] using this
    rw [← h₂.exact] at hx
    obtain ⟨y, hy⟩ := LinearMap.mem_range.mp hx
    have hkill := congrArg (fun f : Hom K₂ L₃ => f.toFun y) hb₂f
    change b₂.toFun (b₁.toFun x) = 0
    rw [← hy]
    simpa [S₂, Hom.comp, Hom.zero, Hom.id] using hkill
  have hcomp := homotopyComp (Classical.choice hb₂) (Classical.choice hb₁)
  rw [hzero] at hcomp
  exact ⟨hcomp⟩

end NullHomotopy

end DifferentialGradedModule
