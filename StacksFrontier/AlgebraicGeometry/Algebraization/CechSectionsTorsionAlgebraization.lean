module

public import StacksFrontier.AlgebraicGeometry.Algebraization.LefschetzGradedAlgebraization
public import StacksFrontier.RingTheory.LocalCohomology.LowDegree.CechSectionsTorsion

/-!
# Graded algebraization with the comparison supplied by sections on `U`

In the algebraization situation of a graded Noetherian ring `A` with irrelevant ideal `𝔞` and
homogeneous `I`, take the inverse system `(Nₙ)` to be the system of global sections
`Γ(U, Fₙ)` on `U = Spec(A) ∖ V(𝔞)` and the comparison `(Mₙ) → (Nₙ)` to be the restriction map.
Its kernel and cokernel are `𝔞`-power torsion, so the two torsion hypotheses of Stacks 0EL4 hold
and the finite graded module exists.

## Main definitions

* `Stacks.Algebraization.AlgebraizationSituation.complementRestriction` — the restriction map
  `M → Γ(U, F)` of the algebraization situation.

## Main results

* `Stacks.Algebraization.exists_finite_graded_algebraization_of_complementSections` — Stacks
  0EL4 with the comparison map and its two torsion hypotheses supplied.

## References

* [Stacks Project, Tag 0EL4](https://stacks.math.columbia.edu/tag/0EL4)
* [Stacks Project, Tag 0BK0](https://stacks.math.columbia.edu/tag/0BK0)
-/

@[expose] public noncomputable section

open AlgebraicGeometry Stacks.LocalCohomology

open scoped Pointwise

universe u v w

namespace Stacks.Algebraization

variable (S : AlgebraizationSituation.{u})

/-- The restriction map `M → Γ(U, F)` to sections on `U = Spec(A) ∖ V(𝔞)`, for a sheaf `F` on
`U` identified with the restriction of the sheaf associated to `M`. -/
def AlgebraizationSituation.complementRestriction (M : ModuleCat.{max u w} S.A)
    (F : SheafOfModules.{max u w} (complementZeroLocus S.A S.a : Scheme).ringCatSheaf)
    (e : F ≅ complementTilde S.A S.a M) :
    M →ₗ[S.A] complementGlobalSections S.A S.a F :=
  restrictionToComplement
    (localizationTriangleData.{w} S.A S.a S.a.fg_of_isNoetherianRing) M F e

/-- The kernel of the restriction map `M → Γ(U, F)` is `𝔞`-power torsion. -/
theorem isIPowerTorsion_ker_complementRestriction (M : ModuleCat.{max u w} S.A)
    (F : SheafOfModules.{max u w} (complementZeroLocus S.A S.a : Scheme).ringCatSheaf)
    (e : F ≅ complementTilde S.A S.a M) :
    IsIPowerTorsion S.A
      (LinearMap.ker (S.complementRestriction.{u, w} M F e)) S.a :=
  (isIPowerTorsion_lowDegreeComparison S.A S.a S.a.fg_of_isNoetherianRing M F e).1

/-- The cokernel of the restriction map `M → Γ(U, F)` is `𝔞`-power torsion. -/
theorem isIPowerTorsion_quotient_range_complementRestriction (M : ModuleCat.{max u w} S.A)
    (F : SheafOfModules.{max u w} (complementZeroLocus S.A S.a : Scheme).ringCatSheaf)
    (e : F ≅ complementTilde S.A S.a M) :
    IsIPowerTorsion S.A
      (complementGlobalSections S.A S.a F ⧸
        LinearMap.range (S.complementRestriction.{u, w} M F e)) S.a :=
  (isIPowerTorsion_lowDegreeComparison S.A S.a S.a.fg_of_isNoetherianRing M F e).2

/-- **Stacks Project, Tag 0EL4, with the 0BK0 comparison discharged.** In the algebraization
situation of a graded ring `A` whose irrelevant ideal is `𝔞` and whose ideal `I` is homogeneous,
let `(Mₙ)` be an inverse system of graded modules and let `(Γ(U, Fₙ))` be a graded inverse system
of sections on `U = Spec(A) ∖ V(𝔞)` whose transition maps are surjective with kernels
`Iⁿ Γ(U, Fₙ₊₁)`. If the restriction maps `Mₙ → Γ(U, Fₙ)` preserve degrees and commute with the
transitions, then there is a finite graded `A`-module `N` with `N/IⁿN ≃ Γ(U, Fₙ)` compatibly
with the transition maps, and `(Mₙ)` maps to `(N/IⁿN)` by degree-preserving maps with
`𝔞`-power torsion kernel and cokernel. -/
theorem exists_finite_graded_algebraization_of_complementSections
    {σ : Type v} [SetLike σ S.A] [AddSubmonoidClass σ S.A] {𝒜 : ℕ → σ} [GradedRing 𝒜]
    (hirr : S.a = (HomogeneousIdeal.irrelevant 𝒜).toIdeal) (hIhom : S.I.IsHomogeneous 𝒜)
    (M : ℕ → ModuleCat.{max u w} S.A)
    (ℳ : ∀ n, ℤ → AddSubgroup (M n)) [∀ n, DirectSum.Decomposition (ℳ n)]
    (s : ∀ n, M (n + 1) →ₗ[S.A] M n)
    (F : ℕ → SheafOfModules.{max u w} (complementZeroLocus S.A S.a : Scheme).ringCatSheaf)
    (ε : ∀ n, F n ≅ complementTilde S.A S.a (M n))
    [∀ n, Module.Finite S.A (complementGlobalSections S.A S.a (F n))]
    (𝒩 : ∀ n, ℤ → AddSubgroup (complementGlobalSections S.A S.a (F n)))
    [∀ n, DirectSum.Decomposition (𝒩 n)]
    (h𝒩 : ∀ (n i : ℕ) (d : ℤ) (a : S.A) (x : complementGlobalSections S.A S.a (F n)),
      a ∈ 𝒜 i → x ∈ 𝒩 n d → a • x ∈ 𝒩 n (i + d))
    (t : ∀ n, complementGlobalSections S.A S.a (F (n + 1)) →ₗ[S.A]
      complementGlobalSections S.A S.a (F n))
    (ht : ∀ (n : ℕ) (d : ℤ) (x : complementGlobalSections S.A S.a (F (n + 1))),
      x ∈ 𝒩 (n + 1) d → t n x ∈ 𝒩 n d)
    (htsurj : ∀ n, Function.Surjective (t n))
    (htker : ∀ n, LinearMap.ker (t n) =
      S.I ^ n • (⊤ : Submodule S.A (complementGlobalSections S.A S.a (F (n + 1)))))
    (hc : ∀ (n : ℕ) (d : ℤ) (x : M n), x ∈ ℳ n d →
      S.complementRestriction.{u, w} (M n) (F n) (ε n) x ∈ 𝒩 n d)
    (hcs : ∀ n, (t n).comp (S.complementRestriction.{u, w} (M (n + 1)) (F (n + 1)) (ε (n + 1))) =
      (S.complementRestriction.{u, w} (M n) (F n) (ε n)).comp (s n)) :
    ∃ (P : Type (max u w)) (_ : AddCommGroup P) (_ : Module S.A P) (𝒬 : ℤ → AddSubgroup P)
        (_ : DirectSum.Decomposition 𝒬)
        (e : ∀ n, (P ⧸ S.I ^ n • (⊤ : Submodule S.A P)) ≃ₗ[S.A]
          complementGlobalSections S.A S.a (F n))
        (g : ∀ n, M n →ₗ[S.A] P ⧸ S.I ^ n • (⊤ : Submodule S.A P)),
      Module.Finite S.A P ∧
      (∀ (i : ℕ) (d : ℤ) (a : S.A) (x : P), a ∈ 𝒜 i → x ∈ 𝒬 d → a • x ∈ 𝒬 (i + d)) ∧
      (∀ (n : ℕ) (d : ℤ) (x : P), x ∈ 𝒬 d → e n (Submodule.Quotient.mk x) ∈ 𝒩 n d) ∧
      (∀ (n : ℕ) (x : P),
        t n (e (n + 1) (Submodule.Quotient.mk x)) = e n (Submodule.Quotient.mk x)) ∧
      (∀ (n : ℕ) (x : M n),
        e n (g n x) = S.complementRestriction.{u, w} (M n) (F n) (ε n) x) ∧
      (∀ (n : ℕ) (d : ℤ) (x : M n), x ∈ ℳ n d →
        ∃ p ∈ 𝒬 d, g n x = Submodule.Quotient.mk p) ∧
      (∀ (n : ℕ) (x : M (n + 1)) (p : P), g (n + 1) x = Submodule.Quotient.mk p →
        g n (s n x) = Submodule.Quotient.mk p) ∧
      (∀ n, IsIPowerTorsion S.A (LinearMap.ker (g n)) S.a) ∧
      (∀ n, IsIPowerTorsion S.A
        ((P ⧸ S.I ^ n • (⊤ : Submodule S.A P)) ⧸ LinearMap.range (g n)) S.a) :=
  exists_finite_graded_algebraization S hirr hIhom ℳ s 𝒩 h𝒩 t ht htsurj htker
    (fun n => S.complementRestriction.{u, w} (M n) (F n) (ε n)) hc hcs
    (fun n => isIPowerTorsion_ker_complementRestriction S (M n) (F n) (ε n))
    (fun n => isIPowerTorsion_quotient_range_complementRestriction S (M n) (F n) (ε n))

end Stacks.Algebraization

end
