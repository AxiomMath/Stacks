module

public import StacksFrontier.Algebra.DifferentialGraded.HomotopyRetractDerived
public import StacksFrontier.RingTheory.Koszul.ComparisonArrowTower

/-!
# The comparison map of Tag 0GZ7 in the derived category of `K_N`-modules

Let `f₁, …, f_r` be elements of a commutative ring `R` and let `K_m = R⟨ξ₁, …, ξ_r⟩` be the
Koszul differential graded algebra with `d ξᵢ = fᵢ ^ m`, with transition homomorphisms
`τ_{m,t} : K_m → K_t` and multiplication homomorphisms
`μ_m : K_m ⊗_R K_t → K_t`, `a ⊗ b ↦ τ_{m,t}(a) b`.

For `n ≥ t ≥ 1` take `N = n + t`. Then `N > n`, and the comparison data of
`Koszul.nonempty_koszulArrowData` produces a differential graded `K_N`-algebra `B` with a
quasi-isomorphism `ε : B → K_t` of left differential graded `K_N`-modules, an arrow
`β : B → K_n ⊗_R K_t` with `μ_n ∘ β = ε`, and an arrow `γ : K_N ⊗_R K_t → B` with
`ε ∘ γ = μ_N` and `β ∘ γ = τ_{N,n} ⊗ id`. Inverting `ε` in the derived category of left
differential graded `K_N`-modules gives
$$\sigma = \beta \circ \varepsilon^{-1} : {}_NK_t \longrightarrow {}_N(K_n \otimes_R K_t),$$
and the two identities above give **both** composites of the source: postcomposition with the
multiplication map `μ_n` is the identity of `{}_NK_t`, and precomposition with the
multiplication map `μ_N` is `τ_{N,n} ⊗ id`. Those are the two directions in which Tag 0GZ7 asks
the composite to be the transition map.

## Main definitions

* `Koszul.powTensorStructure`: the homomorphism `K_N → K_n ⊗_R K_t` making the tensor product a
  differential graded `K_N`-algebra.
* `Koszul.powTensorRestrictedModule` and `Koszul.powBaseTensorRestrictedModule`:
  `K_n ⊗_R K_t` and `K_N ⊗_R K_t` as left differential graded `K_N`-modules.
* `Koszul.powMulHom`, `Koszul.powMulBaseHom`, `Koszul.powTransitionTensorHom`: the two
  multiplication maps and `τ_{N,n} ⊗ id`, as homomorphisms of left differential graded
  `K_N`-modules.
* `Koszul.powDerived`: the canonical functor to the derived category of left differential
  graded `K_N`-modules.
* `Koszul.arrowEpsHom`, `Koszul.arrowBetaHom`, `Koszul.arrowGammaHom`: the three arrows of the
  comparison data, as homomorphisms of left differential graded `K_N`-modules.

## Main results

* `Koszul.exists_derivedComparisonArrow`: **Tag 0GZ7.**

## Implementation notes

Following the convention of the chapter a left differential graded module is recorded as a right
module over the graded opposite algebra, so the ambient derived category is
`D(K_Nᵒᵖᵖ, d)` and every homomorphism of differential graded algebras over `K_N` enters through
`DifferentialGradedModule.restrictedRegularHom`. Restriction of scalars does not change the
underlying cochain complex, so the homotopy retraction of `ε` — whose section and homotopy are
only `R`-linear — already makes the underlying cochain map a homotopy equivalence, hence a
quasi-isomorphism, hence invertible after localization; that is
`DifferentialGradedAlgebra.HomotopyRetract.isIso_derived`.

## References

* [Stacks Project, Tag 0GZ7](https://stacks.math.columbia.edu/tag/0GZ7)
* [Stacks Project, Tag 0GZ3](https://stacks.math.columbia.edu/tag/0GZ3)
* [Stacks Project, Tag 09KX](https://stacks.math.columbia.edu/tag/09KX)
-/

@[expose] public noncomputable section

namespace Koszul

universe u

open scoped ExteriorAlgebra TensorProduct

open CategoryTheory DifferentialGradedAlgebra DifferentialGradedModule
open DifferentialGraded.Bimodule

variable {R : Type u} [CommRing R] {r : ℕ}

section Structure

/-- **The homomorphism `K_N → K_n ⊗_R K_t`** making the tensor product a differential graded
`K_N`-algebra: the transition homomorphism followed by the inclusion of the first factor. -/
def powTensorStructure (f : Fin r → R) (t : ℕ) {n N : ℕ} (hn : 1 ≤ n) (hnN : n ≤ N) :
    (powAlgebra f N).Hom (tensorProduct (powAlgebra f n) (powAlgebra f t)) :=
  (tensorInclLeft (powAlgebra f n) (powAlgebra f t)).comp (powTransition f hn hnN)

/-- The structure homomorphism sends `a` to `τ_{N,n}(a) ⊗ 1`. -/
theorem powTensorStructure_apply (f : Fin r → R) (t : ℕ) {n N : ℕ} (hn : 1 ≤ n) (hnN : n ≤ N)
    (a : (powAlgebra f N).A) :
    (powTensorStructure f t hn hnN).toAlgebraHom a =
      GradedTensorProduct.includeLeft (powAlgebra f n).grading (powAlgebra f t).grading
        ((powTransition f hn hnN).toAlgebraHom a) := rfl

/-- **`{}_N(K_n ⊗_R K_t)`:** the tensor product `K_n ⊗_R K_t` as a left differential graded
`K_N`-module. -/
def powTensorRestrictedModule (f : Fin r → R) (t : ℕ) {n N : ℕ} (hn : 1 ≤ n) (hnN : n ≤ N) :
    DifferentialGradedModule.{u, u, u} (oppAlgebra (powAlgebra f N)) :=
  restrictScalars (oppHom (powTensorStructure f t hn hnN))
    (regularModule (oppAlgebra (tensorProduct (powAlgebra f n) (powAlgebra f t))))

/-- **`{}_N(K_N ⊗_R K_t)`:** the tensor product `K_N ⊗_R K_t` as a left differential graded
`K_N`-module, through the inclusion of the first factor. -/
def powBaseTensorRestrictedModule (f : Fin r → R) (t N : ℕ) :
    DifferentialGradedModule.{u, u, u} (oppAlgebra (powAlgebra f N)) :=
  restrictScalars (oppHom (tensorInclLeft (powAlgebra f N) (powAlgebra f t)))
    (regularModule (oppAlgebra (tensorProduct (powAlgebra f N) (powAlgebra f t))))

/-- The canonical functor from left differential graded `K_N`-modules to their derived
category. -/
abbrev powDerived (f : Fin r → R) (N : ℕ) :
    DifferentialGradedModule.{u, u, u} (oppAlgebra (powAlgebra f N)) ⥤
      derivedCategory' (oppAlgebra (powAlgebra f N)) :=
  toHomotopyCategory (oppAlgebra (powAlgebra f N)) ⋙
    (quasiIsomorphisms' (oppAlgebra (powAlgebra f N))).Q

end Structure

section Maps

variable (f : Fin r → R) {n t N : ℕ}

/-- **The multiplication map `μ_n : K_n ⊗_R K_t → K_t`**, as a homomorphism of left differential
graded `K_N`-modules. -/
def powMulHom (ht : 1 ≤ t) (htn : t ≤ n) (hnN : n ≤ N) :
    powTensorRestrictedModule f t (ht.trans htn) hnN ⟶
      powRestrictedModule f ht (htn.trans hnN) :=
  restrictedRegularHom (powTensorStructure f t (ht.trans htn) hnN)
    (powTransition f ht (htn.trans hnN)) (powMul f ht htn) fun a => by
      have h1 : (powMul f ht htn).toAlgebraHom
          ((powTensorStructure f t (ht.trans htn) hnN).toAlgebraHom a) =
          (powTransition f ht htn).toAlgebraHom
            ((powTransition f (ht.trans htn) hnN).toAlgebraHom a) :=
        congrArg (fun φ => φ ((powTransition f (ht.trans htn) hnN).toAlgebraHom a))
          (powMul_comp_includeLeft f ht htn)
      exact h1.trans (powTransition_comp_apply f ht htn hnN a)

/-- **The multiplication map `μ_N : K_N ⊗_R K_t → K_t`**, as a homomorphism of left differential
graded `K_N`-modules. -/
def powMulBaseHom (ht : 1 ≤ t) (hNt : t ≤ N) :
    powBaseTensorRestrictedModule f t N ⟶ powRestrictedModule f ht hNt :=
  restrictedRegularHom (tensorInclLeft (powAlgebra f N) (powAlgebra f t))
    (powTransition f ht hNt) (powMul f ht hNt) fun a =>
      congrArg (fun φ => φ a) (powMul_comp_includeLeft f ht hNt)

/-- **The homomorphism `τ_{N,n} ⊗ id : K_N ⊗_R K_t → K_n ⊗_R K_t`**, as a homomorphism of left
differential graded `K_N`-modules. -/
def powTransitionTensorHom (t : ℕ) (hn : 1 ≤ n) (hnN : n ≤ N) :
    powBaseTensorRestrictedModule f t N ⟶ powTensorRestrictedModule f t hn hnN :=
  restrictedRegularHom (tensorInclLeft (powAlgebra f N) (powAlgebra f t))
    (powTensorStructure f t hn hnN) (tensorHomLeft (powTransition f hn hnN) (powAlgebra f t))
    fun a => tensorHomLeft_tmul (powTransition f hn hnN) (powAlgebra f t) a 1

end Maps

section Arrows

variable {f : Fin r → R} {n t N : ℕ} {ht : 1 ≤ t} {htn : t ≤ n} {hnN : n ≤ N}
  (D : KoszulArrowData f n t N ht htn hnN)

/-- The comparison algebra `B` as a left differential graded `K_N`-module. -/
def arrowRestrictedModule :
    DifferentialGradedModule.{u, u, u} (oppAlgebra (powAlgebra f N)) :=
  restrictScalars (oppHom D.kappa) (regularModule (oppAlgebra D.carrier))

/-- **The quasi-isomorphism `ε : B → K_t`**, as a homomorphism of left differential graded
`K_N`-modules. -/
def arrowEpsHom :
    arrowRestrictedModule D ⟶ powRestrictedModule f ht (htn.trans hnN) :=
  restrictedRegularHom D.kappa (powTransition f ht (htn.trans hnN)) D.eps fun a =>
    congrArg (fun φ => φ a) D.eps_kappa

/-- **The arrow `β : B → K_n ⊗_R K_t`**, as a homomorphism of left differential graded
`K_N`-modules. -/
def arrowBetaHom :
    arrowRestrictedModule D ⟶ powTensorRestrictedModule f t (ht.trans htn) hnN :=
  restrictedRegularHom D.kappa (powTensorStructure f t (ht.trans htn) hnN) D.beta fun a =>
    congrArg (fun φ => φ a) D.beta_kappa

/-- **The arrow `γ : K_N ⊗_R K_t → B`**, as a homomorphism of left differential graded
`K_N`-modules. -/
def arrowGammaHom :
    powBaseTensorRestrictedModule f t N ⟶ arrowRestrictedModule D :=
  restrictedRegularHom (tensorInclLeft (powAlgebra f N) (powAlgebra f t)) D.kappa D.gamma
    fun a => D.gamma_includeLeft a

/-- `β` followed by the multiplication map `μ_n` is `ε`. -/
theorem arrowBetaHom_comp_powMulHom :
    arrowBetaHom D ≫ powMulHom f ht htn hnN = arrowEpsHom D :=
  restrictedRegularHom_comp_eq _ _ _ D.mul_beta

/-- `γ` followed by `ε` is the multiplication map `μ_N`. -/
theorem arrowGammaHom_comp_arrowEpsHom :
    arrowGammaHom D ≫ arrowEpsHom D = powMulBaseHom f ht (htn.trans hnN) :=
  restrictedRegularHom_comp_eq _ _ _ D.eps_gamma

/-- `γ` followed by `β` is `τ_{N,n} ⊗ id`. -/
theorem arrowGammaHom_comp_arrowBetaHom :
    arrowGammaHom D ≫ arrowBetaHom D = powTransitionTensorHom f t (ht.trans htn) hnN :=
  restrictedRegularHom_comp_eq _ _ _ D.beta_gamma

/-- **The quasi-isomorphism `ε` becomes an isomorphism in the derived category of left
differential graded `K_N`-modules.** -/
instance isIso_powDerived_arrowEpsHom : IsIso ((powDerived f N).map (arrowEpsHom D)) :=
  D.retract.isIso_derived D.kappa (powTransition f ht (htn.trans hnN))
    (fun a => congrArg (fun φ => φ a) D.eps_kappa)

/-- **The comparison map `σ = β ∘ ε⁻¹`** of Tag 0GZ7, in the derived category of left
differential graded `K_N`-modules. -/
def derivedComparisonArrow :
    (powDerived f N).obj (powRestrictedModule f ht (htn.trans hnN)) ⟶
      (powDerived f N).obj (powTensorRestrictedModule f t (ht.trans htn) hnN) :=
  inv ((powDerived f N).map (arrowEpsHom D)) ≫ (powDerived f N).map (arrowBetaHom D)

/-- **The first composite of Tag 0GZ7**: postcomposing `σ` with the multiplication map `μ_n`
gives the transition map `K_t → K_t`, which is the identity. -/
theorem derivedComparisonArrow_comp_powMulHom :
    derivedComparisonArrow D ≫ (powDerived f N).map (powMulHom f ht htn hnN) =
      CategoryStruct.id
        ((powDerived f N).obj (powRestrictedModule f ht (htn.trans hnN))) := by
  rw [derivedComparisonArrow, Category.assoc, ← Functor.map_comp,
    arrowBetaHom_comp_powMulHom, IsIso.inv_hom_id]

/-- **The second composite of Tag 0GZ7**: precomposing `σ` with the multiplication map `μ_N`
gives the transition map `τ_{N,n} ⊗ id` in the other direction. -/
theorem powMulBaseHom_comp_derivedComparisonArrow :
    (powDerived f N).map (powMulBaseHom f ht (htn.trans hnN)) ≫ derivedComparisonArrow D =
      (powDerived f N).map (powTransitionTensorHom f t (ht.trans htn) hnN) := by
  rw [derivedComparisonArrow, ← arrowGammaHom_comp_arrowEpsHom D, Functor.map_comp,
    Category.assoc, IsIso.hom_inv_id_assoc, ← Functor.map_comp,
    arrowGammaHom_comp_arrowBetaHom]

end Arrows

section Main

/-- **Tag 0GZ7.** *"For all `n ≥ t ≥ 1` there exists an `N > n` and a map
`K_t → K_n ⊗_R K_t` in `D(K_N, d)` whose composition with the multiplication map is the
transition map (in either direction)."*

Both composites are asserted: postcomposition with the multiplication map
`μ_n : K_n ⊗_R K_t → K_t` is the transition map `K_t → K_t`, which is the identity, and
precomposition with the multiplication map `μ_N : K_N ⊗_R K_t → K_t` is the transition map
`τ_{N,n} ⊗ id`. Here `K_t` carries the left `K_N`-action through `τ_{N,t}` and `K_n ⊗_R K_t`
carries it through `ξᵢ ↦ fᵢ^{N-n} ξᵢ ⊗ 1`; left differential graded modules are recorded as
right modules over the graded opposite algebra. -/
@[stacks 0GZ7]
theorem exists_derivedComparisonArrow (f : Fin r → R) {n t : ℕ} (ht : 1 ≤ t) (htn : t ≤ n) :
    ∃ (N : ℕ) (hnN : n < N),
      ∃ σ : (powDerived f N).obj (powRestrictedModule f ht (htn.trans hnN.le)) ⟶
            (powDerived f N).obj (powTensorRestrictedModule f t (ht.trans htn) hnN.le),
        σ ≫ (powDerived f N).map (powMulHom f ht htn hnN.le) =
            CategoryStruct.id
              ((powDerived f N).obj (powRestrictedModule f ht (htn.trans hnN.le))) ∧
          (powDerived f N).map (powMulBaseHom f ht (htn.trans hnN.le)) ≫ σ =
            (powDerived f N).map (powTransitionTensorHom f t (ht.trans htn) hnN.le) := by
  refine ⟨n + t, by omega, ?_⟩
  obtain ⟨D⟩ := nonempty_koszulArrowData (N := n + t) ht htn (by omega) (by omega) r f
  exact ⟨derivedComparisonArrow D, derivedComparisonArrow_comp_powMulHom D,
    powMulBaseHom_comp_derivedComparisonArrow D⟩

end Main

end Koszul
