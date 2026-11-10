module

public import StacksFrontier.AlgebraicGeometry.DeRham.ProjectiveSpaceDeRhamEveryDimension
public import StacksFrontier.AlgebraicGeometry.DeRham.FirstChernClass.PicardFirstChernClass
public import StacksFrontier.AlgebraicGeometry.DeRham.CupProduct.CechCupComparison
public import StacksFrontier.AlgebraicGeometry.DeRham.CupProduct.DeRhamCupProductUnit
public import StacksFrontier.AlgebraicGeometry.DeRham.CupProduct.DeRhamCupProductLaws
public import StacksFrontier.AlgebraicGeometry.DeRham.CupProduct.EvenDegreeRing
public import StacksFrontier.AlgebraicGeometry.DeRham.WeilCohomology.DeRhamWeilData
public import
  StacksFrontier.AlgebraicGeometry.DeRham.DifferentialGradedAlgebra.ClassMorphismComposition
public import StacksFrontier.Algebra.Category.ModuleCat.Sheaf.InvertibleCompare

/-!
# The cup powers of `c₁^{dR}(𝒪(1))` form a basis of `H^*_{dR}(ℙⁿ_K/K)`

Let `K` be a field and `n ≥ 0`. By [Stacks, Tag 0FMJ] the de Rham cohomology `H^*_{dR}(ℙⁿ_K/K)` is
free over `K` on the cup powers `c₁^{dR}(𝒪(1))^i`, `0 ≤ i ≤ n`. That lemma is stated for the
cup powers computed by Čech cocycles, starting from the Čech unit. This file reads it for the cup
powers `ξ^t` of `AlgebraicGeometry.SheafOfModules.deRhamCohomologyPow` (`ξ^0 = 1`,
`ξ^{t+1} = ξ ∪ ξ^t`) of the de Rham first Chern class on the Picard group
(`Stacks.DeRhamBaseChange.deRhamFirstChernClassPicard`), which are the classes in which the
Leray--Hirsch theorem and the projective bundle formula are stated.

The two families agree up to one nonzero scalar: over a field `H⁰_{dR}(ℙⁿ_K/K)` is a line, the unit
`1` of the cup product is a nonzero multiple `λ` of the Čech unit (it is a two-sided unit, so it is
not zero), and the Čech cup product is the cup product of Section 0FM3, so `ξ^t = λ · c^t` by
induction, using graded commutativity in even degrees.

## Main results

* `Stacks.ProjectiveBundleDeRham.exists_basis_directSum_of_lines`: a direct sum of vector spaces
  which are lines in the degrees `d i` and zero elsewhere has the basis of the chosen generators.
* `Stacks.ProjectiveBundleDeRham.deRhamFirstChernClass_eq_deRhamFirstChernClassPicard`: the Čech
  first Chern class is the first Chern class on the Picard group.
* `Stacks.ProjectiveBundleDeRham.exists_basis_projectiveDeRhamCohomology_classPow`: the cup powers
  of `c₁^{dR}(𝒪(1))` form a `K`-basis of `⨁_m H^m_{dR}(ℙⁿ_K/K)`.

## References

* [Stacks Project, Tag 0FMJ](https://stacks.math.columbia.edu/tag/0FMJ)
* [Stacks Project, Tag 0FM3](https://stacks.math.columbia.edu/tag/0FM3)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry Opposite
open scoped Stacks.StandardDerivedModel

universe u

attribute [local instance] MvPolynomial.gradedAlgebra

namespace Stacks.ProjectiveBundleDeRham

/-! ### Linear algebra -/

section LinearAlgebra

variable {K : Type*} [Field K] {M : ℤ → Type*} [∀ m, AddCommGroup (M m)] [∀ m, Module K (M m)]

/-- A vector in a space with a one-element basis is the multiple of the basis vector by its
coordinate. -/
private theorem eq_repr_smul_of_basis_fin_one {V : Type*} [AddCommGroup V] [Module K V]
    (b : Module.Basis (Fin 1) K V) (y : V) : y = b.repr y 0 • b 0 := by
  simpa using (b.sum_repr y).symm

/-- **A direct sum of lines and zeros has the basis of the chosen generators**: if `M (d i)` is a
line spanned by `v i` for injective degrees `d` and `M m = 0` in every other degree, then the
`lof (d i) (v i)` form a basis of `⨁_m M m`. -/
theorem exists_basis_directSum_of_lines {ι : Type*} (d : ι → ℤ) (hd : Function.Injective d)
    (v : ∀ i, M (d i)) (hv : ∀ i, ∃ b : Module.Basis (Fin 1) K (M (d i)), b 0 = v i)
    (hz : ∀ m, (∀ i, m ≠ d i) → Subsingleton (M m)) :
    ∃ b : Module.Basis ι K (DirectSum ℤ M), ∀ i, b i = DirectSum.lof K ℤ M (d i) (v i) := by
  classical
  have hv0 : ∀ i, v i ≠ 0 := fun i => (hv i).elim fun b hb => hb ▸ b.ne_zero 0
  have hli : LinearIndependent K fun i => DirectSum.lof K ℤ M (d i) (v i) := by
    rw [linearIndependent_iff']
    intro s g hs i hi
    have h := congrArg (DirectSum.component K ℤ M (d i)) hs
    rw [map_sum, map_zero, Finset.sum_eq_single i] at h
    · rw [map_smul, DirectSum.component.lof_self] at h
      exact (smul_eq_zero.mp h).resolve_right (hv0 i)
    · intro j _ hji
      rw [map_smul, DirectSum.component.of, dite_eq_right (fun e => hji (hd e)), smul_zero]
    · intro his
      exact absurd hi his
  have hsp : ⊤ ≤ Submodule.span K (Set.range fun i => DirectSum.lof K ℤ M (d i) (v i)) := by
    rintro x -
    induction x using DirectSum.induction_on with
    | zero => exact Submodule.zero_mem _
    | add x y hx hy => exact Submodule.add_mem _ hx hy
    | of m y =>
      by_cases hm : ∃ i, d i = m
      · obtain ⟨i, rfl⟩ := hm
        obtain ⟨b, hb⟩ := hv i
        have hy : y = b.repr y 0 • v i := hb ▸ eq_repr_smul_of_basis_fin_one b y
        rw [← DirectSum.lof_eq_of K, hy, map_smul]
        exact Submodule.smul_mem _ _ (Submodule.subset_span ⟨i, rfl⟩)
      · have := hz m fun i e => hm ⟨i, e.symm⟩
        rw [Subsingleton.elim y 0, map_zero]
        exact Submodule.zero_mem _
  exact ⟨Module.Basis.mk hli hsp, fun i => Module.Basis.mk_apply hli hsp i⟩

end LinearAlgebra

/-! ### The Čech and the Picard first Chern class -/

section ChernClass

variable {X S : Scheme.{u}} (p : X ⟶ S) [IsAffineHom (pullback.diagonal (terminal.from X))]

omit [IsAffineHom (pullback.diagonal (terminal.from X))] in
/-- **The first Chern class computed by Čech cocycles is the first Chern class on the Picard
group**: both are the class formed by logarithmic differentiation, carried to the realization by
derived global sections of modules. -/
theorem deRhamFirstChernClass_eq_deRhamFirstChernClassPicard (L : X.Modules)
    (hL : AlgebraicGeometry.SheafOfModules.IsInvertible X.presheaf X.ringCatSheaf.2 L)
    (hL' : Stacks.SheafOfModules.IsInvertible X.toRingedSpace.sheaf.obj
      (_root_.structureSheaf X.toRingedSpace.sheaf).property L) :
    Stacks.DeRhamBaseChange.deRhamFirstChernClassPicard p
        (Stacks.WeilCohomology.picardClassOf X L hL) =
      Scheme.Hom.deRhamFirstChernClass p L hL' := by
  have e : Stacks.GluePicard.picardModelAddEquiv X.toRingedSpace
      (Stacks.WeilCohomology.picardClassOf X L hL) =
      Stacks.SheafOfModules.Picard.classOf X.toRingedSpace.sheaf.obj
        (_root_.structureSheaf X.toRingedSpace.sheaf).property L hL' :=
    Stacks.GluePicard.picardModelAddEquiv_classOf X.toRingedSpace L _
  refine (congrArg (fun c => (SheafOfModules.deRhamCohomologyAbelianIsoDeRhamCohomology
    (Scheme.Hom.deRhamAlgebras p) (SheafOfModules.deRhamDifferential (Scheme.Hom.deRhamAlgebras p))
      2).hom.hom (SheafOfModules.deRhamFirstChernClassAbelian (Scheme.Hom.deRhamAlgebras p)
        (SheafOfModules.deRhamDifferential (Scheme.Hom.deRhamAlgebras p)) c)) e).trans ?_
  rfl

end ChernClass

/-! ### Transport along equalities of degrees -/

section Reindex

variable {X S : Scheme.{u}} (p : X ⟶ S)

/-- The transport `eqToHom` of the module realization of de Rham cohomology along an equality of
degrees is `AlgebraicGeometry.SheafOfModules.reindexDeRhamCohomology`. -/
theorem eqToHom_hom_eq_reindexDeRhamCohomology {m k : ℤ} (h : m = k)
    (x : SheafOfModules.deRhamCohomology (Scheme.Hom.deRhamAlgebras p)
      (SheafOfModules.deRhamDifferential (Scheme.Hom.deRhamAlgebras p)) m) :
    (eqToHom (congrArg (SheafOfModules.deRhamCohomology (Scheme.Hom.deRhamAlgebras p)
        (SheafOfModules.deRhamDifferential (Scheme.Hom.deRhamAlgebras p))) h)).hom x =
      SheafOfModules.reindexDeRhamCohomology _ _ h x := by
  subst h
  rfl

/-- **The Čech cup product, read in a degree `k = i + j`, is the transported cup product of
Section 0FM3**, for `X` of affine diagonal. -/
theorem deRhamCup_eq_reindexDeRhamCohomology [IsAffineHom (pullback.diagonal (terminal.from X))]
    (i j k : ℤ) (h : i + j = k) (x : Scheme.Hom.deRhamCohomologyBaseModule p i)
    (y : Scheme.Hom.deRhamCohomologyBaseModule p j) :
    Scheme.Hom.deRhamCup p i j k h x y =
      SheafOfModules.reindexDeRhamCohomology _ _ h
        (SheafOfModules.deRhamCohomologyCup _ _ i j x y) := by
  subst h
  exact Scheme.Hom.deRhamCup_eq_deRhamCohomologyCup p i j x y

end Reindex

/-! ### Projective space over a field -/

section ProjectiveSpace

open Stacks.AlgebraicGeometry.ProjPolyChart Stacks.AlgebraicGeometry.ProjectiveSpaceDeRham

variable (A : Type u) [CommRing A] (n : ℕ)

/-- `𝒪(1)` on `ℙⁿ_A`, as a module on the scheme. -/
abbrev projectiveTwistOne : (AlgebraicGeometry.Proj (polyGrading A n)).Modules :=
  ProjectiveSpectrum.Proj.twistingSheaf (polyGrading A n) 1

/-- `𝒪(1)` is invertible on `ℙⁿ_A`, in the form in which Picard classes are formed. -/
theorem isInvertible_projectiveTwistOne :
    AlgebraicGeometry.SheafOfModules.IsInvertible
      (AlgebraicGeometry.Proj (polyGrading A n)).presheaf
      (AlgebraicGeometry.Proj (polyGrading A n)).ringCatSheaf.2 (projectiveTwistOne A n) :=
  (Stacks.InvertiblePullback.stacksIsInvertible_iff_algebraicGeometryIsInvertible _ _ _).mp
    (Stacks.AlgebraicGeometry.ProjectiveSpaceHodge.isInvertible_projectiveTwistingSheafOne A n)

/-- **The de Rham first Chern class `c₁^{dR}(𝒪(1)) ∈ H^2_{dR}(ℙⁿ_A/A)`**, on the Picard group. -/
abbrev projectiveChernClass :
    SheafOfModules.deRhamCohomology (Scheme.Hom.deRhamAlgebras (projToSpecCoeff A n))
      (SheafOfModules.deRhamDifferential (Scheme.Hom.deRhamAlgebras (projToSpecCoeff A n))) 2 :=
  Stacks.DeRhamBaseChange.deRhamFirstChernClassPicard (projToSpecCoeff A n)
    (Stacks.WeilCohomology.picardClassOf _ (projectiveTwistOne A n)
      (isInvertible_projectiveTwistOne A n))

/-- **The cup powers of `c₁^{dR}(𝒪(1))` form a basis of `H^*_{dR}(ℙⁿ_K/K)`** over a field `K`:
`(c₁^{dR}(𝒪(1))^i)_{0 ≤ i ≤ n}`, with `c^0 = 1` and `c^{i+1} = c ∪ c^i`, read in the degrees `2i`,
is a `K`-basis of `⨁_m H^m_{dR}(ℙⁿ_K/K)`. This is [Stacks, Tag 0FMJ] for these cup powers. -/
theorem exists_basis_projectiveDeRhamCohomology_classPow (K : Type u) [Field K] :
    ∃ b : Module.Basis (Fin (n + 1)) K
        (DirectSum ℤ fun m : ℤ => ↥(projectiveDeRhamCohomology K n m)),
      ∀ i : Fin (n + 1), b i = DirectSum.lof K ℤ (fun m : ℤ => ↥(projectiveDeRhamCohomology K n m))
        ((2 * (i : ℕ) : ℕ) : ℤ)
        (SheafOfModules.deRhamCohomologyPow _ _ 2 (projectiveChernClass K n) i) := by
  classical
  obtain ⟨hb, hz⟩ := exists_basis_and_isZero_projectiveDeRhamCohomology K n
  -- the Čech classes, read in the realization by derived global sections
  let raw : ℤ → Type u := fun m => SheafOfModules.deRhamCohomology
    (Scheme.Hom.deRhamAlgebras (projToSpecCoeff K n))
    (SheafOfModules.deRhamDifferential (Scheme.Hom.deRhamAlgebras (projToSpecCoeff K n))) m
  let ch : ∀ t : ℕ, raw ((2 * t : ℕ) : ℤ) := fun t => projectiveDeRhamChernPow K n t
  -- the unit is a nonzero multiple of the Čech unit
  obtain ⟨b0, hb0⟩ := hb 0 (Nat.zero_le n)
  let one : ↥(projectiveDeRhamCohomology K n (2 * ((0 : ℕ) : ℤ))) :=
    SheafOfModules.deRhamOneClass _ _
  let lam : K := b0.repr one 0
  have hone : one = lam • projectiveDeRhamChernPow K n 0 := by
    rw [← hb0]
    exact eq_repr_smul_of_basis_fin_one b0 one
  have hlam : lam ≠ 0 := by
    intro h0
    rw [h0, zero_smul] at hone
    apply b0.ne_zero 0
    rw [hb0]
    have h1 := SheafOfModules.deRhamCohomologyCup_one_left _ _ 0
      (show raw 0 from projectiveDeRhamChernPow K n 0)
    have h2 : (SheafOfModules.deRhamOneClass (Scheme.Hom.deRhamAlgebras (projToSpecCoeff K n))
        (SheafOfModules.deRhamDifferential (Scheme.Hom.deRhamAlgebras (projToSpecCoeff K n))) :
          raw 0) = 0 := hone
    rw [h2, SheafOfModules.deRhamCohomologyCup_zero_left,
      SheafOfModules.reindexDeRhamCohomology_zero] at h1
    exact h1.symm
  -- the scalar `λ`, acting through the global sections of the base ring sheaf
  let a : Stacks.DeRhamWeil.baseSectionRing (projToSpecCoeff K n) :=
    Stacks.DeRhamWeil.baseScalarHom (projToSpecCoeff K n)
      ((Scheme.ΓSpecIso (CommRingCat.of K)).inv.hom lam)
  -- the Čech first Chern class is the Picard one
  have hc : projectiveChernClass K n = Scheme.Hom.deRhamFirstChernClass (projToSpecCoeff K n)
      (projectiveTwistOne K n)
      (Stacks.AlgebraicGeometry.ProjectiveSpaceHodge.isInvertible_projectiveTwistingSheafOne K n) :=
    deRhamFirstChernClass_eq_deRhamFirstChernClassPicard _ _ _ _
  -- the recursion of the Čech powers
  have hch : ∀ t : ℕ, ch (t + 1) = SheafOfModules.reindexDeRhamCohomology _ _
      (by push_cast; ring : ((2 * t : ℕ) : ℤ) + ((2 : ℕ) : ℤ) = ((2 * (t + 1) : ℕ) : ℤ))
      (SheafOfModules.deRhamCohomologyCup _ _ ((2 * t : ℕ) : ℤ) ((2 : ℕ) : ℤ) (ch t)
        (projectiveChernClass K n)) := by
    intro t
    have e1 := Scheme.Hom.deRhamChernPow_succ (projToSpecCoeff K n) (projectiveTwistOne K n)
      (Stacks.AlgebraicGeometry.ProjectiveSpaceHodge.isInvertible_projectiveTwistingSheafOne K n) t
    rwa [deRhamCup_eq_reindexDeRhamCohomology, ← hc] at e1
  -- `ξ^t = λ c^t`
  have key : ∀ t : ℕ, (SheafOfModules.deRhamCohomologyPow _ _ 2 (projectiveChernClass K n) t :
      raw ((2 * t : ℕ) : ℤ)) = a • ch t := by
    intro t
    induction t with
    | zero => exact hone
    | succ t ih =>
      rw [SheafOfModules.deRhamCohomologyPow_succ, ih,
        SheafOfModules.deRhamCohomologyCup_smul_right,
        SheafOfModules.reindexDeRhamCohomology_smul, SheafOfModules.deRhamCohomologyCup_comm,
        Int.negOnePow_even _ ⟨((2 * t : ℕ) : ℤ), by push_cast; ring⟩, Units.val_one, one_smul,
        SheafOfModules.reindexDeRhamCohomology_reindexDeRhamCohomology, hch]
  refine exists_basis_directSum_of_lines (M := fun m : ℤ => ↥(projectiveDeRhamCohomology K n m))
    (fun i : Fin (n + 1) => ((2 * (i : ℕ) : ℕ) : ℤ)) ?_
    (fun i => SheafOfModules.deRhamCohomologyPow _ _ 2 (projectiveChernClass K n) i) ?_ ?_
  · intro i j h
    have h' : 2 * (i : ℕ) = 2 * (j : ℕ) := Nat.cast_injective h
    exact Fin.ext (by omega)
  · intro i
    obtain ⟨bi, hbi⟩ := hb i (Nat.lt_succ_iff.mp i.2)
    refine ⟨bi.isUnitSMul (w := fun _ => lam) (fun _ => hlam.isUnit), ?_⟩
    rw [Module.Basis.isUnitSMul_apply, hbi]
    exact (key i).symm
  · intro m hm
    exact ModuleCat.subsingleton_of_isZero (hz m fun i hi e => hm ⟨i, by omega⟩
      (by rw [e]; push_cast; ring))

end ProjectiveSpace

end Stacks.ProjectiveBundleDeRham
