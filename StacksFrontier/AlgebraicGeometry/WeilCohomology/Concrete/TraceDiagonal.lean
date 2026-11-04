module

public import StacksFrontier.AlgebraicGeometry.WeilCohomology.Concrete.WeilThreeAxioms
public import StacksFrontier.AlgebraicGeometry.WeilCohomology.Concrete.DiagonalExpansion
public import StacksFrontier.AlgebraicGeometry.WeilCohomology.Concrete.ClosedImmersionClass
public import StacksFrontier.AlgebraicGeometry.WeilCohomology.FirstChernClassSetup

/-!
# The diagonal class and the trace map of axiom (A6)

Let `𝔇` be data (D0), (D1), (D2') as in Section 45.14 (Tag 0FID) satisfying (A5), and let
`γ : CH^i(X) ⟶ H^{2i}(X)(i)` be a family of maps (it will be the cycle class map of Tag 0FIF).
For `X` nonempty and equidimensional of dimension `d`, the class of the diagonal
`γ([Δ]) ∈ H^{2d}(X × X)(d) = ⨁_i H^i(X) ⊗_F H^{2d-i}(X)(d)` (by (A5)) can be contracted against an
`F`-linear map `λ : H^{2d}(X)(d) ⟶ F`, viewed as a map `H^*(X)(d) ⟶ F` by precomposing with the
projection onto `H^{2d}(X)(d)`; axiom (A6) asks for a `λ` with `(id ⊗ λ) γ([Δ]) = 1`.

This file defines the contraction `(id ⊗ λ)` and the axiom for an arbitrary family `γ`, and
reduces the statements of Lemma 0FIJ and Remark 0FIK to the identity
`γ([Δ]) ∪ p₁^*a = γ([Δ]) ∪ p₂^*a` of the proof of Lemma 0FIJ, through the linear algebra of
`...Concrete.DiagonalExpansion`.

## Implementation notes

The contraction is computed in the coordinates `𝔇.κ` of the twists attached to the canonical
coordinate `𝔇.coord` of the line `F(1)`: an element of `H^*(X × X)(d) = H^*(X × X) ⊗ F(d)` is
written `x ⊗ ℓ`, `x` is expanded by (A5) as `∑ e ⊗ f`, and `(id ⊗ λ)(x ⊗ ℓ) = ∑ λ(f ⊗ ℓ) e`;
since `F(d)` is a line, `λ(f ⊗ ℓ) = c(ℓ) λ(f ⊗ c⁻¹(1))` for the coordinate `c`, so the
contraction does not depend on the coordinate.
-/

@[expose] public noncomputable section

open CategoryTheory AlgebraicGeometry TensorProduct DirectSum Stacks.Chow

universe u w

namespace Stacks.WeilCohomology

variable {k : Type u} [Field k]

/-- **The class `[Δ] ∈ CH^d(X × X)` of the diagonal** `Δ : X ⟶ X × X`. -/
def SmoothProjectiveScheme.diagonalClass (X : (SmoothProjectiveScheme k).FullSubcategory) (d : ℕ) :
    codimensionChowGroup k (SmoothProjectiveScheme.prod X X).obj.hom d :=
  closedSubschemeClass (SmoothProjectiveScheme.prod X X).obj.hom
    (SmoothProjectiveScheme.diag X).hom.left d

namespace FirstChernClassData

variable {F : Type w} [Field F] (𝔇 : FirstChernClassData k F)

/-- The projection `H^*(X) ⟶ H^n(X)` onto the degree-`n` part. -/
def projGrade (X : (SmoothProjectiveScheme k).FullSubcategory) (n : ℤ) : 𝔇.H X →ₗ[F] 𝔇.grade X n :=
  (DirectSum.component F ℤ (fun i => 𝔇.grade X i) n) ∘ₗ
    (DirectSum.decomposeLinearEquiv (𝔇.grade X)).toLinearMap

/-- The projection onto `H^n(X)`, viewed in `H^*(X)`, is the degree-`n` component of the
decomposition. -/
@[simp]
theorem coe_projGrade (X : (SmoothProjectiveScheme k).FullSubcategory) (n : ℤ) (a : 𝔇.H X) :
    (𝔇.projGrade X n a : 𝔇.H X) = decompose (𝔇.grade X) a n := rfl

/-- A linear map `λ : H^{2d}(X)(d) ⟶ F`, viewed as a map `H^*(X) ⟶ F` in the coordinate of the
twist: `a ↦ λ(κ⁻¹(a_{2d}))`. -/
def untwistTrace (X : (SmoothProjectiveScheme k).FullSubcategory) (d : ℕ)
    (lam : tateTwist F 𝔇.tate (𝔇.grade X (2 * (d : ℤ))) d →ₗ[F] F) : 𝔇.H X →ₗ[F] F :=
  lam ∘ₗ (tateTwistCoordinates 𝔇.coord (d : ℤ)).symm.toLinearMap ∘ₗ 𝔇.projGrade X (2 * (d : ℤ))

/-- The untwisted trace `a ↦ λ(κ⁻¹(a_{2d}))` vanishes on `H^i(X)` for `i ≠ 2d`. -/
theorem untwistTrace_eq_zero (X : (SmoothProjectiveScheme k).FullSubcategory) (d : ℕ)
    (lam : tateTwist F 𝔇.tate (𝔇.grade X (2 * (d : ℤ))) d →ₗ[F] F) (i : ℤ)
    (hi : i ≠ 2 * (d : ℤ)) (x : 𝔇.H X) (hx : x ∈ 𝔇.grade X i) : 𝔇.untwistTrace X d lam x = 0 := by
  have : 𝔇.projGrade X (2 * (d : ℤ)) x = 0 :=
    Subtype.ext (by rw [coe_projGrade, decompose_of_mem_ne _ hx hi]; rfl)
  simp [untwistTrace, this]

/-- The Künneth isomorphism of axiom (A5). -/
def kunnethEquiv (hA5 : 𝔇.KunnethAxiom) (X Y : (SmoothProjectiveScheme k).FullSubcategory) :
    𝔇.H X ⊗[F] 𝔇.H Y ≃ₗ[F] 𝔇.H (SmoothProjectiveScheme.prod X Y) :=
  LinearEquiv.ofBijective (𝔇.kunnethMap X Y) (hA5.2 X Y)

/-- **The contraction `(id ⊗ λ) : H^*(X × X)(d) ⟶ H^*(X)`** against a linear map
`λ : H^{2d}(X)(d) ⟶ F`, through the Künneth isomorphism of (A5). -/
def traceContract (hA5 : 𝔇.KunnethAxiom) (X : (SmoothProjectiveScheme k).FullSubcategory) (d : ℕ)
    (lam : tateTwist F 𝔇.tate (𝔇.grade X (2 * (d : ℤ))) d →ₗ[F] F) :
    tateTwist F 𝔇.tate (𝔇.H (SmoothProjectiveScheme.prod X X)) d →ₗ[F] 𝔇.H X :=
  DiagonalExpansion.contractRight (𝔇.untwistTrace X d lam) ∘ₗ
    (𝔇.kunnethEquiv hA5 X X).symm.toLinearMap ∘ₗ (𝔇.κ (SmoothProjectiveScheme.prod X X) d)

/-- **Axiom (A6)** for a family `γ` of cycle class maps: for every nonempty smooth projective `X`
equidimensional of dimension `d` there is an `F`-linear `λ : H^{2d}(X)(d) ⟶ F` with
`(id ⊗ λ) γ([Δ]) = 1`. -/
def TraceAxiomFor (hA5 : 𝔇.KunnethAxiom)
    (γ : ∀ (X : (SmoothProjectiveScheme k).FullSubcategory) (i : ℕ),
      codimensionChowGroup k X.obj.hom i →+ tateTwist F 𝔇.tate (𝔇.H X) i) : Prop :=
  ∀ (X : (SmoothProjectiveScheme k).FullSubcategory) (d : ℕ), IsNonemptyEquidimensional X d →
    ∃ lam : tateTwist F 𝔇.tate (𝔇.grade X (2 * (d : ℤ))) d →ₗ[F] F,
      𝔇.traceContract hA5 X d lam
        (γ (SmoothProjectiveScheme.prod X X) d (SmoothProjectiveScheme.diagonalClass X d)) = 1

/-! ### From the identity `η ∪ p₁^*a = η ∪ p₂^*a` to the duality -/

section Reduction

variable (hA5 : 𝔇.KunnethAxiom) (X : (SmoothProjectiveScheme k).FullSubcategory) (d : ℕ)

/-- The untwisted class of the diagonal, `η = κ(g) ∈ H^{2d}(X × X)`, for a class `g` of
`H^{2d}(X × X)(d)`. -/
abbrev untwistClass (g : tateTwist F 𝔇.tate (𝔇.H (SmoothProjectiveScheme.prod X X)) d) :
    𝔇.H (SmoothProjectiveScheme.prod X X) :=
  𝔇.κ (SmoothProjectiveScheme.prod X X) d g

/-- The inverse Künneth isomorphism sends `κ(g)` to any expansion `∑ e ⊗ f` of it. -/
private theorem kunnethEquiv_symm_untwistClass
    (g : tateTwist F 𝔇.tate (𝔇.H (SmoothProjectiveScheme.prod X X)) d)
    (l : List (ℤ × 𝔇.H X × 𝔇.H X))
    (hl : 𝔇.kunnethMap X X (DiagonalExpansion.tensorSum l) = 𝔇.untwistClass X d g) :
    (𝔇.kunnethEquiv hA5 X X).symm (𝔇.untwistClass X d g) = DiagonalExpansion.tensorSum l :=
  (LinearEquiv.symm_apply_eq _).2 hl.symm

/-- The contraction `(id ⊗ λ) g` read through a Künneth expansion `∑ e ⊗ f` of `κ(g)`. -/
private theorem traceContract_eq_sum
    (g : tateTwist F 𝔇.tate (𝔇.H (SmoothProjectiveScheme.prod X X)) d)
    (l : List (ℤ × 𝔇.H X × 𝔇.H X))
    (hl : 𝔇.kunnethMap X X (DiagonalExpansion.tensorSum l) = 𝔇.untwistClass X d g)
    (lam : tateTwist F 𝔇.tate (𝔇.grade X (2 * (d : ℤ))) d →ₗ[F] F) :
    𝔇.traceContract hA5 X d lam g = (l.map fun t => 𝔇.untwistTrace X d lam t.2.2 • t.2.1).sum := by
  simp only [traceContract, LinearMap.coe_comp, Function.comp_apply, LinearEquiv.coe_coe]
  rw [𝔇.kunnethEquiv_symm_untwistClass hA5 X d g l hl, DiagonalExpansion.map_tensorSum]
  simp

/-- **The data of the linear algebra** of `...Concrete.DiagonalExpansion` for the diagonal class:
given `g ∈ H^{2d}(X × X)(d)`, a trace `λ` normalised by `(id ⊗ λ) g = 1`, and
`η ∪ p₁^*a = η ∪ p₂^*a` for `η = κ(g)`, every Künneth expansion of `η` satisfies the hypotheses of
`DiagonalExpansion.DiagonalData`. -/
theorem exists_diagonalData
    (g : tateTwist F 𝔇.tate (𝔇.H (SmoothProjectiveScheme.prod X X)) d)
    (hg : 𝔇.untwistClass X d g ∈ 𝔇.grade (SmoothProjectiveScheme.prod X X) (2 * (d : ℤ)))
    (lam : tateTwist F 𝔇.tate (𝔇.grade X (2 * (d : ℤ))) d →ₗ[F] F)
    (hlam : 𝔇.traceContract hA5 X d lam g = 1)
    (hkey : ∀ a : 𝔇.H X, 𝔇.untwistClass X d g * 𝔇.pull (SmoothProjectiveScheme.fst X X) a =
      𝔇.untwistClass X d g * 𝔇.pull (SmoothProjectiveScheme.snd X X) a) :
    ∃ l, DiagonalExpansion.DiagonalData (𝔇.grade X) (𝔇.grade (SmoothProjectiveScheme.prod X X))
      (𝔇.pull (SmoothProjectiveScheme.fst X X)) (𝔇.pull (SmoothProjectiveScheme.snd X X))
      (2 * (d : ℤ)) (𝔇.untwistClass X d g) (𝔇.untwistTrace X d lam) l := by
  have hpull : ∀ {Y Z : (SmoothProjectiveScheme k).FullSubcategory} (f : Y ⟶ Z) (m : ℤ) (a : 𝔇.H Z),
      a ∈ 𝔇.grade Z m → 𝔇.pull f a ∈ 𝔇.grade Y m := fun f m a ha => 𝔇.pull_grade f m a ha
  obtain ⟨l, hl, hle⟩ := DiagonalExpansion.exists_expansion
    (fun m a ha => hpull _ m a ha) (fun m a ha => hpull _ m a ha) (hA5.2 X X).2 hg
  refine ⟨l, ⟨fun m a ha => hpull _ m a ha, fun m a ha => hpull _ m a ha,
    𝔇.graded_comm _, 𝔇.graded_comm _, (hA5.2 X X).1, ⟨d, by ring⟩, hl, hle,
    fun i hi x hx => 𝔇.untwistTrace_eq_zero X d lam i hi x hx, ?_, hkey⟩⟩
  simpa using (𝔇.traceContract_eq_sum hA5 X d g l hle lam).symm.trans hlam

/-- `λ` is determined by its untwisting. -/
theorem untwistTrace_injective :
    Function.Injective (𝔇.untwistTrace X d) := by
  intro lam lam' h
  refine LinearMap.ext fun y => ?_
  set z : 𝔇.grade X (2 * (d : ℤ)) :=
    tateTwistCoordinates (V := 𝔇.grade X (2 * (d : ℤ))) 𝔇.coord (d : ℤ) y
  have := LinearMap.congr_fun h (z : 𝔇.H X)
  have hp : 𝔇.projGrade X (2 * (d : ℤ)) (z : 𝔇.H X) = z :=
    Subtype.ext (by rw [coe_projGrade, decompose_of_mem_same _ (Submodule.coe_mem _)])
  simpa [untwistTrace, hp, z] using this

/-- **Uniqueness of the trace map** (the algebra of Remark 0FIK): under the identity
`η ∪ p₁^*a = η ∪ p₂^*a`, two linear maps `λ, λ' : H^{2d}(X)(d) ⟶ F` with
`(id ⊗ λ) g = (id ⊗ λ') g = 1` are equal. -/
theorem trace_unique_of_key
    (g : tateTwist F 𝔇.tate (𝔇.H (SmoothProjectiveScheme.prod X X)) d)
    (hg : 𝔇.untwistClass X d g ∈ 𝔇.grade (SmoothProjectiveScheme.prod X X) (2 * (d : ℤ)))
    (hkey : ∀ a : 𝔇.H X, 𝔇.untwistClass X d g * 𝔇.pull (SmoothProjectiveScheme.fst X X) a =
      𝔇.untwistClass X d g * 𝔇.pull (SmoothProjectiveScheme.snd X X) a)
    (lam lam' : tateTwist F 𝔇.tate (𝔇.grade X (2 * (d : ℤ))) d →ₗ[F] F)
    (hlam : 𝔇.traceContract hA5 X d lam g = 1) (hlam' : 𝔇.traceContract hA5 X d lam' g = 1) :
    lam = lam' := by
  obtain ⟨l, hD⟩ := 𝔇.exists_diagonalData hA5 X d g hg lam hlam hkey
  have h1 := (𝔇.traceContract_eq_sum hA5 X d g l hD.expansion lam').symm.trans hlam'
  exact (𝔇.untwistTrace_injective X d (DiagonalExpansion.trace_unique hD
    (fun i hi x hx => 𝔇.untwistTrace_eq_zero X d lam' i hi x hx) h1)).symm

/-- **Contraction against the `(i, j)` Künneth component of a class `g ∈ H^{2d}(X × X)(d)`**,
`μ ↦ (1 ⊗ μ)(g_{i,j}) ∈ H^i(X)` for `μ : H^j(X)(d) ⟶ F`: the class `κ(g)` is expanded by (A5)
as `∑ e ⊗ f`, and `μ` is applied to the degree-`j` part of `f`, twisted by `d`. -/
def diagonalContract (g : tateTwist F 𝔇.tate (𝔇.H (SmoothProjectiveScheme.prod X X)) d)
    (i j : ℤ) : (tateTwist F 𝔇.tate (𝔇.grade X j) d →ₗ[F] F) →ₗ[F] 𝔇.grade X i where
  toFun μ := 𝔇.projGrade X i (TensorProduct.rid F (𝔇.H X)
    (LinearMap.lTensor (𝔇.H X)
      (μ ∘ₗ (tateTwistCoordinates 𝔇.coord (d : ℤ)).symm.toLinearMap ∘ₗ 𝔇.projGrade X j)
      ((𝔇.kunnethEquiv hA5 X X).symm (𝔇.untwistClass X d g))))
  map_add' μ ν := by simp [LinearMap.add_comp, LinearMap.lTensor_add]
  map_smul' c μ := by simp [LinearMap.smul_comp, LinearMap.lTensor_smul]

/-- The contraction read through a Künneth expansion of the class. -/
theorem coe_diagonalContract_eq
    (g : tateTwist F 𝔇.tate (𝔇.H (SmoothProjectiveScheme.prod X X)) d) (i j : ℤ)
    (l : List (ℤ × 𝔇.H X × 𝔇.H X))
    (hl : 𝔇.kunnethMap X X (DiagonalExpansion.tensorSum l) = 𝔇.untwistClass X d g)
    (μ : tateTwist F 𝔇.tate (𝔇.grade X j) d →ₗ[F] F) :
    𝔇.diagonalContract hA5 X d g i j μ =
      DiagonalExpansion.diagonalContract (𝒜 := 𝔇.grade X) l i j
        (μ ∘ₗ (tateTwistCoordinates 𝔇.coord (d : ℤ)).symm.toLinearMap) := by
  have h := 𝔇.kunnethEquiv_symm_untwistClass hA5 X d g l hl
  apply Subtype.ext
  set φ := μ ∘ₗ (tateTwistCoordinates 𝔇.coord (d : ℤ)).symm.toLinearMap ∘ₗ 𝔇.projGrade X j
  have hsum : TensorProduct.rid F (𝔇.H X) (LinearMap.lTensor (𝔇.H X) φ
      (DiagonalExpansion.tensorSum l)) = (l.map fun t => φ t.2.2 • t.2.1).sum := by
    have := DiagonalExpansion.map_tensorSum
      ((TensorProduct.rid F (𝔇.H X)).toLinearMap ∘ₗ LinearMap.lTensor (𝔇.H X) φ) l
    simpa using this
  show ((𝔇.grade X i).subtype (𝔇.projGrade X i (TensorProduct.rid F (𝔇.H X)
    (LinearMap.lTensor (𝔇.H X) φ ((𝔇.kunnethEquiv hA5 X X).symm (𝔇.untwistClass X d g)))))) = _
  rw [h, hsum, map_list_sum, map_list_sum, DiagonalExpansion.coe_diagonalContract, List.map_map,
    List.map_map]
  refine congrArg List.sum (List.map_congr_left fun t _ => ?_)
  simp [φ]
  rfl

/-- **The perfect duality defined by the class of the diagonal** (the algebra of Remark 0FIK):
under the identity `η ∪ p₁^*a = η ∪ p₂^*a` and `(id ⊗ λ) g = 1`, contraction against the
`(i, j)` Künneth component of `g`, `(H^j(X)(d))^* ⟶ H^i(X)`, is bijective for `i + j = 2d`. -/
theorem bijective_diagonalContract_of_key
    (g : tateTwist F 𝔇.tate (𝔇.H (SmoothProjectiveScheme.prod X X)) d)
    (hg : 𝔇.untwistClass X d g ∈ 𝔇.grade (SmoothProjectiveScheme.prod X X) (2 * (d : ℤ)))
    (hkey : ∀ a : 𝔇.H X, 𝔇.untwistClass X d g * 𝔇.pull (SmoothProjectiveScheme.fst X X) a =
      𝔇.untwistClass X d g * 𝔇.pull (SmoothProjectiveScheme.snd X X) a)
    (lam : tateTwist F 𝔇.tate (𝔇.grade X (2 * (d : ℤ))) d →ₗ[F] F)
    (hlam : 𝔇.traceContract hA5 X d lam g = 1) {i j : ℤ} (hij : i + j = 2 * (d : ℤ)) :
    Function.Bijective (𝔇.diagonalContract hA5 X d g i j) := by
  obtain ⟨l, hD⟩ := 𝔇.exists_diagonalData hA5 X d g hg lam hlam hkey
  have hc : ⇑(𝔇.diagonalContract hA5 X d g i j) =
      DiagonalExpansion.diagonalContract (𝒜 := 𝔇.grade X) l i j ∘
        fun μ => μ ∘ₗ (tateTwistCoordinates 𝔇.coord (d : ℤ)).symm.toLinearMap :=
    funext fun μ => 𝔇.coe_diagonalContract_eq hA5 X d g i j l hD.expansion μ
  rw [hc]
  refine (DiagonalExpansion.bijective_diagonalContract hD hij).comp ?_
  set e := tateTwistCoordinates (V := 𝔇.grade X j) 𝔇.coord (d : ℤ)
  refine ⟨fun μ ν h => ?_, fun ν => ⟨ν ∘ₗ e.toLinearMap, ?_⟩⟩
  · refine LinearMap.ext fun x => ?_
    simpa using LinearMap.congr_fun h (e x)
  · refine LinearMap.ext fun x => ?_
    simp

end Reduction

end FirstChernClassData

end Stacks.WeilCohomology

end
