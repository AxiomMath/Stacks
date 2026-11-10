module

public import StacksFrontier.AlgebraicGeometry.WeilDeRham.TraceAxiomAlgClosedKunneth
public import StacksFrontier.AlgebraicGeometry.WeilDeRham.TraceAxiomAlgClosedClopenGysin
public import StacksFrontier.AlgebraicGeometry.WeilDeRham.TraceAxiomAlgClosedPointGeneration
public import StacksFrontier.AlgebraicGeometry.WeilDeRham.TraceAxiomAlgClosedProjectiveSpaceChern
public import StacksFrontier.AlgebraicGeometry.WeilDeRham.TraceAxiomAlgClosedProjectiveSpacePointClass
public import StacksFrontier.AlgebraicGeometry.WeilDeRham.FieldBaseChangeGlobalSections
public import StacksFrontier.AlgebraicGeometry.WeilCohomology.Concrete.BlowupTrace
public import StacksFrontier.AlgebraicGeometry.WeilCohomology.FirstChernClassSetup
public import StacksFrontier.AlgebraicGeometry.Picard.TorsionSmoothProjectiveCurve.PicardFunctorPoints
public import StacksFrontier.AlgebraicGeometry.Picard.CurveLineBundles.RiemannRoch
public import StacksFrontier.AlgebraicGeometry.Variety.Smooth.ConnectedIrreducible
public import StacksFrontier.AlgebraicGeometry.Variety.Bertini.VanishingDivisorOneStepReduction
public import StacksFrontier.AlgebraicGeometry.ProperGeomConnected.Basic
public import StacksFrontier.AlgebraicGeometry.Chow.BivariantLemmas.ConnectedComponents

/-!
# The trace axiom (A6) over an algebraically closed field

Let `k` be an algebraically closed field, `F` a field of characteristic zero and data (D0), (D1),
(D2') (`Stacks.WeilCohomology.FirstChernClassData`) satisfying (A1), (A2), (A3), (A5) and (A8) of
Section 45.14 of the Stacks Project, with `γ` the cycle class map of Lemma 0FIF
(`Stacks.WeilCohomology.FirstChernClassData.IsCohomologicalChernCharacter.codimensionCycleClass`,
for a cohomological Chern character `h : 𝔇.IsCohomologicalChernCharacter ch` of Tag 0FIE, which
exists under (A1) – (A4)). This file carries out, for any such data, the proof that Proposition
0FWD gives of axiom (A6) for de Rham cohomology (the source's paragraphs
"Axiom (A6)"), in the form `𝔇.TraceAxiomFor hA5 h.codimensionCycleClass` of the base, with the one
input the source takes from the theory at hand, Proposition 0FLC for de Rham cohomology, as a
hypothesis:

**(FIN)** every irreducible `X`, equidimensional of dimension `d`, has a morphism
`f : X ⟶ ℙ^d_k` with `f^*` injective on `H^{2d}(ℙ^d_k)`.

## The argument

Let `X` be nonempty, equidimensional of dimension `d`, with diagonal `Δ ⊆ X × X`, and write
`s = K⁻¹(γ([Δ])) ∈ H^*(X) ⊗ H^*(X)` through the Künneth isomorphism `K` of (A5). For a linear form
`λ` on `H^{2d}(X)(d)`, `h_λ = (1 ⊗ λ)(s)`
(`Stacks.WeilCohomology.FirstChernClassData.traceContract`) is to be `1`.

1. `h_λ ∈ H^0(X)`: `K` is graded, so only the Künneth component `γ_0 ∈ H^0 ⊗ H^{2d}` contributes
   (`Stacks.WeilDeRham.traceContract_diagonalClass_mem_grade_zero`).
2. For a rational point `x`, `ε_x(h_λ) = λ(γ([x]))`, where `ε_x` is evaluation at `x`: pull `s`
   back along `x × id` and use `(x × id)^![Δ] = [x]`
   (`Stacks.WeilDeRham.pointEval_traceContract_diagonalClass`).
3. For `X` irreducible, `H^0(X) = F` by (A8) and `Γ(X, 𝒪_X) = k` (Tag 0BUG)
   (`Stacks.WeilDeRham.exists_eq_algebraMap_of_mem_grade_zero`). With 2, `γ([x])` does not depend
   on `x` (`Stacks.WeilDeRham.cycleClass_pointChowClass_eq_of_irreducible`).
4. Still for `X` irreducible, `γ([x]) ≠ 0`: with `f` from (FIN) and a rational point `y` of
   `ℙ^d_k`, `f^*γ([y]) = γ(f^![y])`, `γ([y]) = d! ch^H_d(𝒪(1)) = c₁^H(𝒪(1))^d ≠ 0`
   (`Stacks.WeilDeRham.cycleClass_pointChowClass_projectiveSpace_ne_zero`, from
   `Stacks.WeilDeRham.codimensionCycleClass_pointChowClass_projectiveSpace` and
   `Stacks.WeilDeRham.cohomologicalChernCharacter_projectiveSpaceTwistClass_ne_zero`), and
   `f^![y]` is an integral combination of classes of rational points of `X`
   (`Stacks.WeilDeRham.mem_closure_pointChowClass`), all with the same class `γ([x])`
   (`Stacks.WeilDeRham.cycleClass_pointChowClass_ne_zero_of_irreducible`).
5. In general, let `X_i` be the connected components of `X` (open and closed, irreducible), with
   rational points `x_i`. The class of `x_i` restricts to `γ([x_i])` on `X_i` and to `0` on
   `X_j`, `j ≠ i` (`Stacks.WeilDeRham.codimensionGysin_clopen_pointChowClass_of_mem`,
   `Stacks.WeilDeRham.codimensionGysin_clopen_pointChowClass_of_not_mem`). Choose `λ_i` on
   `H^{2d}(X_i)(d)` with `λ_i(γ([x_i])) = 1` and `λ = ∑ λ_i ∘ ι_i^*`. Then `ι_i^* h_λ ∈ H^0(X_i)
   = F` is `ε_{x_i}(h_λ) = λ(γ([x_i])) = 1`, and `h_λ = 1` by (A1)
   (`Stacks.WeilDeRham.traceAxiom_cycleClass_of_isAlgClosed`).

The source reduces to `X` irreducible through `γ([Δ]) = ∑ γ([Δ_i])` in
`H^*(X × X) = ∏ H^*(X_i × X_j)`; here the components enter only through the restriction of the
classes of points, which is the same decomposition read on `X` instead of on `X × X`.

Here `γ([x])` is read in `H^{2d}(X)(d)`, where `λ` is defined
(`…IsCohomologicalChernCharacter.cycleClassGrade`).

## References

* [Stacks Project, Tag 0FWD](https://stacks.math.columbia.edu/tag/0FWD)
* [Stacks Project, Section 45.14 (Tag 0FID)](https://stacks.math.columbia.edu/tag/0FID)
* [Stacks Project, Tag 0FLC](https://stacks.math.columbia.edu/tag/0FLC)
* [Stacks Project, Tag 0BUG](https://stacks.math.columbia.edu/tag/0BUG)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry TensorProduct
open Stacks.WeilCohomology Stacks.WeilCohomology.SmoothProjectiveScheme
open Stacks.WeilCohomology.DiagonalExpansion (contractRight contractRight_tmul)

universe u w

namespace Stacks.WeilDeRham

variable {k : Type u} [Field k] {F : Type w} [Field F] {𝔇 : FirstChernClassData k F}

/-! ### `H^0` of an irreducible smooth projective scheme -/

/-- **`H^0(X) = F` for `X` irreducible**, `k` algebraically closed: by (A8) for the structure
morphism `X ⟶ Spec(k)`, which induces `k ≅ Γ(X, 𝒪_X)` (Tag 0BUG), `H^0(X)` is the image of
`H^0(Spec(k)) = F` (A5). -/
theorem exists_eq_algebraMap_of_mem_grade_zero [IsAlgClosed k] (hA5 : 𝔇.KunnethAxiom)
    (hA8 : 𝔇.GlobalSectionsAxiom) (Y : (SmoothProjectiveScheme k).FullSubcategory)
    [IrreducibleSpace ((toScheme k).obj Y)] {a : 𝔇.H Y} (ha : a ∈ 𝔇.grade Y 0) :
    ∃ c : F, a = algebraMap F (𝔇.H Y) c := by
  have : AlgebraicGeometry.IsReduced Y.obj.left :=
    Stacks.SectionsVanishingOnSubscheme.isReduced_of_smooth_over_field k Y.obj.hom
  have : IrreducibleSpace Y.obj.left := ‹IrreducibleSpace ((toScheme k).obj Y)›
  have : AlgebraicGeometry.IsIntegral Y.obj.left :=
    isIntegral_of_irreducibleSpace_of_isReduced _
  have : IsProper Y.obj.hom := (isProjective Y).isProper
  have h0 := AlgebraicGeometry.isIso_globalSections_of_isAlgClosed k Y.obj.hom
  have hiso : IsIso ((toScheme k).map (toPoint Y)).appTop :=
    IsIso.of_isIso_comp_left (Scheme.ΓSpecIso (.of k)).inv Y.obj.hom.appTop
  have : IsAffine ((toScheme k).obj (point k)) := inferInstanceAs (IsAffine (Spec (.of k)))
  have hb := bijective_gradedPieceMap_pull_of_isIso_appTop hA8 (toPoint Y) hiso
  obtain ⟨b, hb⟩ := hb.2 ⟨a, ha⟩
  obtain ⟨c, hc⟩ := hA5.1.2 (b : 𝔇.H (point k))
  refine ⟨c, ?_⟩
  have h1 : 𝔇.pull (toPoint Y) (b : 𝔇.H (point k)) = a := congrArg Subtype.val hb
  rw [← h1, ← hc, Algebra.linearMap_apply, AlgHom.commutes]

/-- **A class of `H^0` restricts to `1` on an irreducible `Y`** as soon as it evaluates to `1` at
one rational point of `Y`, since `H^0(Y) = F`. -/
private theorem pull_eq_one_of_pointEval_eq_one [IsAlgClosed k] (hA5 : 𝔇.KunnethAxiom)
    (hA8 : 𝔇.GlobalSectionsAxiom) {X Y : (SmoothProjectiveScheme k).FullSubcategory}
    [IrreducibleSpace ((toScheme k).obj Y)] (g : Y ⟶ X) {c : 𝔇.H X} (hc : c ∈ 𝔇.grade X 0)
    (y : Spec (.of k) ⟶ (toScheme k).obj Y) (hy : y ≫ Y.obj.hom = 𝟙 _)
    (h1 : pointEval hA5 (pointHom y hy ≫ g) c = 1) : 𝔇.pull g c = 1 := by
  obtain ⟨a, ha⟩ := exists_eq_algebraMap_of_mem_grade_zero hA5 hA8 Y (𝔇.pull_grade g 0 c hc)
  have e : pointEval hA5 (pointHom y hy) (𝔇.pull g c) = pointEval hA5 (pointHom y hy ≫ g) c := by
    simp only [pointEval, LinearMap.comp_apply, AlgHom.toLinearMap_apply, 𝔇.pull_comp,
      AlgHom.comp_apply]
  rw [ha, pointEval_algebraMap] at e
  rw [ha, e, h1, map_one]

/-- **A connected component of a smooth projective scheme is irreducible.** -/
private theorem irreducibleSpace_clopen_connectedComponentOpens
    (X : (SmoothProjectiveScheme k).FullSubcategory) [LocallyConnectedSpace X.obj.left]
    (i : _root_.ConnectedComponents X.obj.left)
    (hU : IsClopen (X.obj.left.connectedComponentOpens i : Set X.obj.left)) :
    IrreducibleSpace ((toScheme k).obj (clopen X (X.obj.left.connectedComponentOpens i) hU)) := by
  have : ConnectedSpace (clopen X (X.obj.left.connectedComponentOpens i) hU).obj.left := by
    obtain ⟨z, rfl⟩ := ConnectedComponents.surjective_coe i
    have hz : (X.obj.left.connectedComponentOpens (ConnectedComponents.mk z) : Set X.obj.left) =
        connectedComponent z := by
      change ConnectedComponents.mk ⁻¹' {ConnectedComponents.mk z} = _
      rw [connectedComponents_preimage_singleton]
    exact isConnected_iff_connectedSpace.1 (hz ▸ isConnected_connectedComponent)
  have h := irreducibleSpace_of_smooth_of_connectedSpace_of_compactSpace
    (clopen X (X.obj.left.connectedComponentOpens i) hU).obj.hom
  exact h

/-! ### Pulling back along `x × id` -/

section PointCross

variable [CharZero F] {ch : ∀ X : (SmoothProjectiveScheme k).FullSubcategory,
    VectorBundleKZero ((toScheme k).obj X) → ∀ n : ℕ, tateTwist F 𝔇.tate (𝔇.H X) n}
  (h : 𝔇.IsCohomologicalChernCharacter ch) (hA1 : 𝔇.CoproductAxiom)
  (hA3 : 𝔇.ProjectiveBundleAxiom) (hA5 : 𝔇.KunnethAxiom)
  {X : (SmoothProjectiveScheme k).FullSubcategory}

/-- **`ε_x((1 ⊗ λ)γ([Δ])) = λ(γ([x]))`** for a rational point `x` of `X`, equidimensional of
dimension `d`: pull `γ([Δ])` back along `x × id`
(`Stacks.WeilCohomology.SmoothProjectiveScheme.prodLift`), which gives `γ([x])`. -/
theorem pointEval_traceContract_diagonalClass {d : ℕ} (hd : RelativeDimension X.obj.hom d)
    (x : Spec (.of k) ⟶ (toScheme k).obj X) (hx : x ≫ X.obj.hom = 𝟙 _)
    (l : tateTwist F 𝔇.tate (𝔇.grade X (2 * (d : ℤ))) (d : ℤ) →ₗ[F] F) :
    pointEval hA5 (pointHom x hx)
        (𝔇.traceContract hA5 X d l (h.codimensionCycleClass (prod X X) d (diagonalClass X d))) =
      l (h.cycleClassGrade hA1 hA3 X d (pointChowClass x hx d)) := by
  have hjp := prodLift_fst (toPoint X ≫ pointHom x hx) (𝟙 X)
  have hjq := prodLift_snd (toPoint X ≫ pointHom x hx) (𝟙 X)
  change pointEval hA5 (pointHom x hx) (contractRight (𝔇.untwistTrace X d l)
    ((𝔇.kunnethEquiv hA5 X X).symm
      (𝔇.untwistClass X d (h.codimensionCycleClass (prod X X) d (diagonalClass X d))))) = _
  rw [pointEval_contractRight_eq hA5 (pointHom x hx) hjp hjq,
    pull_untwistClass_diagonalClass h hd x hx hjp hjq,
    ← coe_tateTwistCoordinates_cycleClassGrade h hA1 hA3, ← trace_eq_untwistTrace]

include hA1 hA3 in
/-- **`(1 ⊗ λ)γ([Δ])` lies in `H^0(X)`.** -/
theorem traceContract_diagonalClass_mem_grade_zero (X : (SmoothProjectiveScheme k).FullSubcategory)
    (d : ℕ) (l : tateTwist F 𝔇.tate (𝔇.grade X (2 * (d : ℤ))) (d : ℤ) →ₗ[F] F) :
    𝔇.traceContract hA5 X d l (h.codimensionCycleClass (prod X X) d (diagonalClass X d)) ∈
      𝔇.grade X 0 :=
  contractRight_kunnethEquiv_symm_mem_grade_zero hA5 X (2 * (d : ℤ))
    (𝔇.untwistClass_mem_of_mem_range X d
      (h.codimensionCycleClass_mem hA1 hA3 (prod X X) d (diagonalClass X d))) _ fun y => by
      rw [untwistTrace_decompose, _root_.GradedAlgebra.proj_apply]

end PointCross

/-! ### The class of a point of projective space -/

/-- **`γ([y]) ≠ 0` for a rational point `y` of `ℙ^d_k`** (Lemma 0FMJ in the form the proof of (A6)
uses): `γ([y]) = d! · ch^H_d(𝒪(1))`, which is nonzero by (A2), (A3) and (A5). -/
theorem cycleClass_pointChowClass_projectiveSpace_ne_zero [CharZero F]
    {ch : ∀ X : (SmoothProjectiveScheme k).FullSubcategory,
      VectorBundleKZero ((toScheme k).obj X) → ∀ n : ℕ, tateTwist F 𝔇.tate (𝔇.H X) n}
    (h : 𝔇.IsCohomologicalChernCharacter ch) (hA1 : 𝔇.CoproductAxiom) (hA2 : 𝔇.PullbackAxiom)
    (hA3 : 𝔇.ProjectiveBundleAxiom) (hA5 : 𝔇.KunnethAxiom) (d : ℕ)
    (y : Spec (.of k) ⟶ (toScheme k).obj (projectiveSpace k d))
    (hy : y ≫ (projectiveSpace k d).obj.hom = 𝟙 _) :
    h.codimensionCycleClass (projectiveSpace k d) d (pointChowClass y hy d) ≠ 0 := by
  rw [codimensionCycleClass_pointChowClass_projectiveSpace h hA1 hA3 d y hy,
    ← Nat.cast_smul_eq_nsmul F]
  exact smul_ne_zero (Nat.cast_ne_zero.2 (Nat.factorial_ne_zero d))
    (cohomologicalChernCharacter_projectiveSpaceTwistClass_ne_zero h hA1 hA2 hA3 hA5 d)

/-- **(FIN)**, the input of Proposition 0FLC: every irreducible smooth projective `X`,
equidimensional of dimension `d`, has a morphism `f : X ⟶ ℙ^d_k` with `f^*` injective on
`H^{2d}(ℙ^d_k)`. -/
def FiniteProjectionInjective (𝔇 : FirstChernClassData k F) : Prop :=
  ∀ (X : (SmoothProjectiveScheme k).FullSubcategory) (d : ℕ),
    IrreducibleSpace ((toScheme k).obj X) → RelativeDimension X.obj.hom d →
      ∃ f : X ⟶ projectiveSpace k d, ∀ a ∈ 𝔇.grade (projectiveSpace k d) (2 * (d : ℤ)),
        𝔇.pull f a = 0 → a = 0

/-! ### The irreducible case -/

section Irreducible

variable [CharZero F] {ch : ∀ X : (SmoothProjectiveScheme k).FullSubcategory,
    VectorBundleKZero ((toScheme k).obj X) → ∀ n : ℕ, tateTwist F 𝔇.tate (𝔇.H X) n}
  (h : 𝔇.IsCohomologicalChernCharacter ch) (hA1 : 𝔇.CoproductAxiom)
  (hA2 : 𝔇.PullbackAxiom) (hA3 : 𝔇.ProjectiveBundleAxiom) (hA5 : 𝔇.KunnethAxiom)
  (hA8 : 𝔇.GlobalSectionsAxiom)

include hA5 hA8 in
/-- **(a) The class `γ([x])` does not depend on the rational point `x`**, for `X` irreducible and
`k` algebraically closed: for every linear form `λ`, `λ(γ([x])) = ε_x((1 ⊗ λ)γ([Δ]))`, and
`(1 ⊗ λ)γ([Δ]) ∈ H^0(X) = F` has the same value at every point. -/
theorem cycleClass_pointChowClass_eq_of_irreducible [IsAlgClosed k]
    (X : (SmoothProjectiveScheme k).FullSubcategory) [IrreducibleSpace ((toScheme k).obj X)]
    {d : ℕ} (hd : RelativeDimension X.obj.hom d) (x x' : Spec (.of k) ⟶ (toScheme k).obj X)
    (hx : x ≫ X.obj.hom = 𝟙 _) (hx' : x' ≫ X.obj.hom = 𝟙 _) :
    h.cycleClassGrade hA1 hA3 X d (pointChowClass x hx d) =
      h.cycleClassGrade hA1 hA3 X d (pointChowClass x' hx' d) := by
  rw [← sub_eq_zero]
  refine (Module.forall_dual_apply_eq_zero_iff F _).1 fun l => ?_
  rw [map_sub, sub_eq_zero]
  obtain ⟨c, hc⟩ := exists_eq_algebraMap_of_mem_grade_zero hA5 hA8 X
    (traceContract_diagonalClass_mem_grade_zero h hA1 hA3 hA5 X d l)
  rw [← pointEval_traceContract_diagonalClass h hA1 hA3 hA5 hd x hx l,
    ← pointEval_traceContract_diagonalClass h hA1 hA3 hA5 hd x' hx' l, hc, pointEval_algebraMap,
    pointEval_algebraMap]

include hA2 hA5 hA8 in
/-- **(b) `γ([x]) ≠ 0`** for `X` irreducible and `k` algebraically closed, given (FIN): for
`f : X ⟶ ℙ^d_k` and a rational point `y` of `ℙ^d_k`, `f^*γ([y]) = γ(f^![y])` is nonzero, and
`f^![y]` is an integral combination of classes of rational points of `X`, which all have the
class `γ([x])`. -/
theorem cycleClass_pointChowClass_ne_zero_of_irreducible [IsAlgClosed k]
    (hFIN : FiniteProjectionInjective 𝔇)
    (X : (SmoothProjectiveScheme k).FullSubcategory) [IrreducibleSpace ((toScheme k).obj X)]
    {d : ℕ} (hd : RelativeDimension X.obj.hom d) (x : Spec (.of k) ⟶ (toScheme k).obj X)
    (hx : x ≫ X.obj.hom = 𝟙 _) :
    h.cycleClassGrade hA1 hA3 X d (pointChowClass x hx d) ≠ 0 := by
  intro h0
  obtain ⟨f, hf⟩ := hFIN X d inferInstance hd
  have : Nonempty (projectiveSpace k d).obj.left :=
    ⟨((toScheme k).map f).base (IrreducibleSpace.toNonempty (X := (toScheme k).obj X)).some⟩
  obtain ⟨y, hy⟩ :=
    Stacks.PicardFunctor.exists_section_of_isAlgClosed k (projectiveSpace k d).obj.hom
  have hG := cycleClass_codimensionGysin h hA1 hA3 f d (pointChowClass y hy d)
  have hcl := mem_closure_pointChowClass X hd
    (Stacks.Chow.codimensionGysin X.obj.hom (projectiveSpace k d).obj.hom (w f) d
      (pointChowClass y hy d))
  have key : ∀ β ∈ AddSubgroup.closure {β' | ∃ (x' : Spec (.of k) ⟶ (toScheme k).obj X)
      (hx' : x' ≫ X.obj.hom = 𝟙 _), β' = pointChowClass x' hx' d},
      h.cycleClassGrade hA1 hA3 X d β = 0 := fun β hβ => by
    induction hβ using AddSubgroup.closure_induction with
    | mem β hβ =>
      obtain ⟨x', hx', rfl⟩ := hβ
      rw [cycleClass_pointChowClass_eq_of_irreducible h hA1 hA3 hA5 hA8 X hd x' x hx' hx, h0]
    | zero => exact map_zero _
    | add β β' _ _ h1 h2 => rw [map_add, h1, h2, add_zero]
    | neg β _ h => rw [map_neg, h, neg_zero]
  rw [key _ hcl] at hG
  apply cycleClass_pointChowClass_projectiveSpace_ne_zero h hA1 hA2 hA3 hA5 d y hy
  have h2 := congrArg (fun v => ((tateTwistCoordinates 𝔇.coord (d : ℤ) v :
    𝔇.grade X (2 * (d : ℤ))) : 𝔇.H X)) hG
  simp only [map_zero, ZeroMemClass.coe_zero] at h2
  rw [tateTwistCoordinates_map] at h2
  have h3 := hf _ (SetLike.coe_mem _) h2.symm
  rw [coe_tateTwistCoordinates_cycleClassGrade h hA1 hA3] at h3
  exact (𝔇.κ _ _).map_eq_zero_iff.1 h3

include hA2 hA5 hA8 in
/-- **A linear form `λ` with `λ(γ([x])) = 1`**, for `X` irreducible and `k` algebraically closed,
given (FIN), since `γ([x]) ≠ 0`. -/
private theorem exists_dual_cycleClassGrade_pointChowClass_eq_one [IsAlgClosed k]
    (hFIN : FiniteProjectionInjective 𝔇)
    (X : (SmoothProjectiveScheme k).FullSubcategory) [IrreducibleSpace ((toScheme k).obj X)]
    {d : ℕ} (hd : RelativeDimension X.obj.hom d) (x : Spec (.of k) ⟶ (toScheme k).obj X)
    (hx : x ≫ X.obj.hom = 𝟙 _) :
    ∃ μ : tateTwist F 𝔇.tate (𝔇.grade X (2 * (d : ℤ))) (d : ℤ) →ₗ[F] F,
      μ (h.cycleClassGrade hA1 hA3 X d (pointChowClass x hx d)) = 1 := by
  obtain ⟨μ, hμ⟩ : ∃ μ : Module.Dual F _,
      μ (h.cycleClassGrade hA1 hA3 X d (pointChowClass x hx d)) ≠ 0 := by
    by_contra! hall
    exact cycleClass_pointChowClass_ne_zero_of_irreducible h hA1 hA2 hA3 hA5 hA8 hFIN X hd x hx
      ((Module.forall_dual_apply_eq_zero_iff F _).1 hall)
  exact ⟨(μ (h.cycleClassGrade hA1 hA3 X d (pointChowClass x hx d)))⁻¹ • μ,
    by rw [LinearMap.smul_apply, smul_eq_mul, inv_mul_cancel₀ hμ]⟩

include hA2 hA5 hA8 in
/-- **A linear form `λ = ∑ λ_i ∘ ι_i^*` with `λ(γ([x_i])) = 1`** for rational points `x_i` of the
connected components `X_i` of `X`, given (FIN): `λ_i(γ([x_i])) = 1` on `X_i`, and the class of
`x_i` restricts to `0` on `X_j` for `j ≠ i`. -/
private theorem exists_dual_cycleClassGrade_pointChowClass_components_eq_one [IsAlgClosed k]
    (hFIN : FiniteProjectionInjective 𝔇) (X : (SmoothProjectiveScheme k).FullSubcategory)
    [LocallyConnectedSpace X.obj.left] [Finite (_root_.ConnectedComponents X.obj.left)]
    {d : ℕ} (hd : RelativeDimension X.obj.hom d)
    (hU : ∀ i, IsClopen (X.obj.left.connectedComponentOpens i : Set X.obj.left))
    (x : ∀ i, Spec (.of k) ⟶ (toScheme k).obj (clopen X (X.obj.left.connectedComponentOpens i)
      (hU i)))
    (hx : ∀ i, x i ≫ (clopen X (X.obj.left.connectedComponentOpens i) (hU i)).obj.hom = 𝟙 _)
    (hx₁ : ∀ i, (x i ≫ (toScheme k).map (clopenInclusion X _ (hU i))) ≫ X.obj.hom = 𝟙 _) :
    ∃ l : tateTwist F 𝔇.tate (𝔇.grade X (2 * (d : ℤ))) (d : ℤ) →ₗ[F] F, ∀ i,
      l (h.cycleClassGrade hA1 hA3 X d
        (pointChowClass (x i ≫ (toScheme k).map (clopenInclusion X _ (hU i))) (hx₁ i) d)) = 1 := by
  have : Fintype (_root_.ConnectedComponents X.obj.left) := Fintype.ofFinite _
  set S : Scheme.{u} := X.obj.left
  set U : _root_.ConnectedComponents S → S.Opens := S.connectedComponentOpens
  set γ := h.cycleClassGrade hA1 hA3
  set ι := fun i => clopenInclusion X (U i) (hU i)
  -- linear forms `λ_i` with `λ_i(γ([x_i])) = 1`
  have hμ : ∀ i, ∃ μ : tateTwist F 𝔇.tate (𝔇.grade (clopen X (U i) (hU i)) (2 * (d : ℤ))) (d : ℤ)
      →ₗ[F] F, μ (γ (clopen X (U i) (hU i)) d (pointChowClass (x i) (hx i) d)) = 1 := fun i => by
    have := irreducibleSpace_clopen_connectedComponentOpens X i (hU i)
    have hdi := RelativeDimension.comp_of_flat (U i).ι X.obj.hom
      (Stacks.Chow.relativeDimension_of_isOpenImmersion (U i).ι) hd
    rw [zero_add] at hdi
    exact exists_dual_cycleClassGrade_pointChowClass_eq_one h hA1 hA2 hA3 hA5 hA8 hFIN _ hdi
      (x i) (hx i)
  choose μ hμ using hμ
  -- the restriction `ι_i^*` on `H^{2d}(-)(d)`
  set restr : ∀ i, tateTwist F 𝔇.tate (𝔇.grade X (2 * (d : ℤ))) (d : ℤ) →ₗ[F]
      tateTwist F 𝔇.tate (𝔇.grade (clopen X (U i) (hU i)) (2 * (d : ℤ))) (d : ℤ) := fun i =>
    tateTwistMap (gradedPieceMap (𝔇.grade X) (𝔇.grade (clopen X (U i) (hU i)))
      (𝔇.pull (ι i)) (𝔇.pull_grade (ι i)) (2 * (d : ℤ))) (d : ℤ)
  -- `ι_i^*γ([x_i]) = γ([x_i])`, and `ι_j^*γ([x_i]) = 0` for `j ≠ i`
  have hres : ∀ i j, restr j (γ X d (pointChowClass (x i ≫ (toScheme k).map (ι i)) (hx₁ i) d)) =
      γ (clopen X (U j) (hU j)) d (Stacks.Chow.codimensionGysin (clopen X (U j) (hU j)).obj.hom
        X.obj.hom (w (ι j)) d (pointChowClass (x i ≫ (toScheme k).map (ι i)) (hx₁ i) d)) :=
    fun i j => (cycleClass_codimensionGysin h hA1 hA3 (ι j) d _).symm
  have hres_ne : ∀ i j, j ≠ i →
      restr j (γ X d (pointChowClass (x i ≫ (toScheme k).map (ι i)) (hx₁ i) d)) = 0 :=
    fun i j hji => by
      rw [hres, codimensionGysin_clopen_pointChowClass_of_not_mem X hd (U j) (hU j) _ (hx₁ i)
        (fun z hz => ?_), map_zero]
      have h1 : ((x i ≫ (toScheme k).map (ι i)).base z : S) ∈ U i := ((x i).base z).2
      exact hji ((S.mem_connectedComponentOpens.1 hz).symm.trans
        (S.mem_connectedComponentOpens.1 h1))
  refine ⟨∑ i, μ i ∘ₗ restr i, fun i => ?_⟩
  simp only [LinearMap.sum_apply, LinearMap.comp_apply]
  rw [Finset.sum_eq_single i (fun j _ hji => by rw [hres_ne i j hji, map_zero])
    (fun h => absurd (Finset.mem_univ i) h), hres,
    codimensionGysin_clopen_pointChowClass_of_mem X hd (U i) (hU i) (x i) (hx i)]
  exact hμ i

end Irreducible

/-! ### The trace axiom (A6) -/

/-- **Stacks Project, Proposition 0FWD, axiom (A6), for any data over an algebraically closed
field.** Let `k` be algebraically closed and `F` of characteristic zero, and let data (D0), (D1),
(D2') satisfy (A1), (A2), (A3), (A5) and (A8), with `γ` the cycle class map of Lemma 0FIF for a
cohomological Chern character `ch^H` of Tag 0FIE. If every irreducible smooth projective `X` of
dimension `d` has a morphism to `ℙ^d_k` whose pullback is injective on `H^{2d}(ℙ^d_k)` (FIN, which
the source gets from Proposition 0FLC), then (A6) holds: for every nonempty equidimensional `X`
there is `λ` with `(1 ⊗ λ)γ([Δ]) = 1`. -/
theorem traceAxiom_cycleClass_of_isAlgClosed [IsAlgClosed k] [CharZero F]
    {ch : ∀ X : (SmoothProjectiveScheme k).FullSubcategory,
      VectorBundleKZero ((toScheme k).obj X) → ∀ n : ℕ, tateTwist F 𝔇.tate (𝔇.H X) n}
    (h : 𝔇.IsCohomologicalChernCharacter ch) (hA1 : 𝔇.CoproductAxiom) (hA2 : 𝔇.PullbackAxiom)
    (hA3 : 𝔇.ProjectiveBundleAxiom) (hA5 : 𝔇.KunnethAxiom) (hA8 : 𝔇.GlobalSectionsAxiom)
    (hFIN : FiniteProjectionInjective 𝔇) :
    𝔇.TraceAxiomFor hA5 h.codimensionCycleClass := by
  intro X d hX
  have hd := hX.relativeDimension
  set S : Scheme.{u} := X.obj.left
  have : IsLocallyNoetherian S := LocallyOfFiniteType.isLocallyNoetherian X.obj.hom
  have : Finite (_root_.ConnectedComponents S) :=
    Stacks.AlgebraicGeometry.ProperGeomConnected.finite_connectedComponents_of_noetherianSpace
  have : Fintype (_root_.ConnectedComponents S) := Fintype.ofFinite _
  -- the connected components `X_i`
  set U : _root_.ConnectedComponents S → S.Opens := S.connectedComponentOpens
  have hU : ∀ i, IsClopen (U i : Set S) := fun i =>
    ⟨S.isClosed_connectedComponentOpens i, (U i).isOpen⟩
  -- a rational point of each `X_i`
  have hpt : ∀ i, ∃ x : Spec (.of k) ⟶ (toScheme k).obj (clopen X (U i) (hU i)),
      x ≫ (clopen X (U i) (hU i)).obj.hom = 𝟙 _ := fun i => by
    obtain ⟨z, rfl⟩ := ConnectedComponents.surjective_coe i
    have : Nonempty (clopen X _ (hU (ConnectedComponents.mk z))).obj.left := ⟨⟨z, rfl⟩⟩
    exact Stacks.PicardFunctor.exists_section_of_isAlgClosed k
      (clopen X _ (hU (ConnectedComponents.mk z))).obj.hom
  choose x hx using hpt
  set ι := fun i => clopenInclusion X (U i) (hU i)
  have hx₁ : ∀ i, (x i ≫ (toScheme k).map (ι i)) ≫ X.obj.hom = 𝟙 _ := fun i => by
    rw [Category.assoc, w, hx i]
  obtain ⟨l, hl⟩ :=
    exists_dual_cycleClassGrade_pointChowClass_components_eq_one h hA1 hA2 hA3 hA5 hA8 hFIN X hd
      hU x hx hx₁
  refine ⟨l, ?_⟩
  set c := 𝔇.traceContract hA5 X d l (h.codimensionCycleClass (prod X X) d (diagonalClass X d))
  have hmem : c ∈ 𝔇.grade X 0 := traceContract_diagonalClass_mem_grade_zero h hA1 hA3 hA5 X d l
  -- `ι_i^* c = 1` on each component
  have hcomp : ∀ i, 𝔇.pull (ι i) c = 𝔇.pull (ι i) 1 := fun i => by
    have := irreducibleSpace_clopen_connectedComponentOpens X i (hU i)
    rw [map_one]
    refine pull_eq_one_of_pointEval_eq_one hA5 hA8 (ι i) hmem (x i) (hx i) ?_
    rw [show pointHom (x i) (hx i) ≫ ι i = pointHom _ (hx₁ i) from hom_ext' rfl, ← hl i]
    exact pointEval_traceContract_diagonalClass h hA1 hA3 hA5 hd _ _ l
  -- `c = 1` by (A1)
  obtain ⟨n, ⟨e⟩⟩ := Finite.exists_equiv_fin (_root_.ConnectedComponents S)
  exact (𝔇.bijective_pull_clopen hA1 X (Fin n) (fun j => U (e.symm j)) (fun j => hU (e.symm j))
    (fun j j' hjj' => S.disjoint_connectedComponentOpens (e.symm.injective.ne hjj'))
    (by
      rw [← S.iSup_connectedComponentOpens]
      exact e.symm.surjective.iSup_comp fun i => U i)).1 (funext fun j => hcomp (e.symm j))

end Stacks.WeilDeRham

end
