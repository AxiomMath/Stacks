module

public import StacksCore.Tactic.StacksAttribute
public import StacksFrontier.AlgebraicGeometry.CoherentAbelian.Basic
public import StacksFrontier.AlgebraicGeometry.FormalFunctions.AdicCompletionLimitComparison
public import StacksFrontier.AlgebraicGeometry.FormalFunctions.CohomologyIdealPowerComparison
public import StacksFrontier.AlgebraicGeometry.FormalGeometry.CompletionFunctor.FullyFaithfulComplete
public import StacksFrontier.RingTheory.AdicCompletion.IntertwinedFiltrationTopology

/-!
# The Artin--Rees chain, from [Stacks, Tag 02O8] to the theorem on formal functions

This file walks the chain of the Stacks project's section on the theorem on formal functions,
discharging at each step the result that the previous step has just proved. The declarations it
calls carry those results as hypotheses; here every such hypothesis is supplied, so the
statements below have the source's hypotheses and nothing more.

* [Stacks, Tag 02O8] is `Stacks.Cohomology.FormalFunctions.isCohomologyReesFinite`.
* [Stacks, Tag 02OA] follows, parts (1), (2) and (3) through
  `Stacks.RingTheory.ReesSystem.exists_uniform_bound_rees` applied to the cohomology system
  `Stacks.Cohomology.FormalFunctions.cohomologyIdealPowerSystem`, and parts (4) and (5) through
  `Stacks.Cohomology.FormalFunctions.exists_comparison_cohomology`.
* [Stacks, Tag 02OB] is
  `Stacks.Cohomology.FormalFunctions.exists_uniform_bound_cohomology_idealPowerQuotient_of_02O8`
  with its hypothesis discharged.
* [Stacks, Tag 02OC] follows, through
  `Stacks.Cohomology.FormalFunctions.formalFunctionsEquiv` for the isomorphism of `A`-modules
  and `Stacks.IntertwinedFiltration.isHomeomorph_adicCompletionEquivTowerLimit_limitTopology`
  for the assertion that it is a homeomorphism for the limit topologies.
* [Stacks, Tag 087U] is
  `Stacks.Algebraization.isIso_cohomologyToLimit_of_isProper_of_isAdicComplete`, and is
  registered here.

## Main results

In the namespace `Stacks.Cohomology.FormalFunctions`:

* `exists_uniform_bound_cohomology_of_isProper` — **[Stacks, Tag 02OA]**, all five parts.
* `exists_uniform_bound_cohomology_idealPowerQuotient_of_isProper` — **[Stacks, Tag 02OB]**.
* `exists_formalFunctionsEquiv_of_isProper` — **[Stacks, Tag 02OC]**.

## References

* [Stacks Project, Tag 02O8](https://stacks.math.columbia.edu/tag/02O8)
* [Stacks Project, Tag 02OA](https://stacks.math.columbia.edu/tag/02OA)
* [Stacks Project, Tag 02OB](https://stacks.math.columbia.edu/tag/02OB)
* [Stacks Project, Tag 02OC](https://stacks.math.columbia.edu/tag/02OC)
* [Stacks Project, Tag 087U](https://stacks.math.columbia.edu/tag/087U)
-/

@[expose] public noncomputable section

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits Opposite TopologicalSpace
open scoped ModuleCat.Algebra TensorProduct

universe u

attribute [local instance] AlgebraicGeometry.Scheme.Modules.submoduleCompleteLattice
attribute [local instance] AlgebraicGeometry.Scheme.Modules.mono_submodule_ι

namespace Stacks.Cohomology.FormalFunctions

open AlgebraicGeometry.CoherentAbelian
open Stacks.Algebraization Stacks.Cohomology.AffineBase Stacks.IntertwinedFiltration

attribute [local instance] AlgebraicGeometry.modulesLinear baseSectionsAlgebra

/-! ### [Stacks, Tag 02OA] -/

section Tag02OA

variable {A : Type u} [CommRing A] (I : Ideal A) (X : Over (Spec (.of A)))
  (F : X.left.Modules)

/-- **[Stacks, Tag 02OA].** For `A` Noetherian, `I ⊆ A` an ideal, `f : X ⟶ Spec A` proper and
`ℱ` coherent there is one integer `c ≥ 0` such that

1. the multiplication map `Iʳ⁻ᶜ ⊗ Hᵖ(X, Iᶜℱ) → Hᵖ(X, Iʳℱ)` is surjective for `r ≥ c`;
2. the image of `Hᵖ(X, Iⁿ⁺ᵐℱ) → Hᵖ(X, Iⁿℱ)` is contained in `Iᵐ⁻ᵉHᵖ(X, Iⁿℱ)` with
   `e = max(0, c - n)`, whenever `n + m ≥ c` — and, in the shape where the target is `Hᵖ(X, ℱ)`
   itself rather than `Hᵖ(X, I⁰ℱ)`, the image of `Hᵖ(X, Iʳℱ) → Hᵖ(X, ℱ)` is contained in
   `Iʳ⁻ᶜHᵖ(X, ℱ)` for `r ≥ c`, which is the source's `n = 0`;
3. `Ker(Hᵖ(X, Iᵏℱ) → Hᵖ(X, ℱ)) = Ker(Hᵖ(X, Iᵏℱ) → Hᵖ(X, Iᵐℱ))` whenever `m + c ≤ k`, which is
   the source's part (3) in the case `m = k - c`;
4. there are `A`-linear maps `cmp : IⁿHᵖ(X, ℱ) → Hᵖ(X, Iⁿ⁻ᶜℱ)` for `n ≥ c` whose two
   composites with the canonical maps are canonical: `cmp` followed by
   `Hᵖ(X, Iⁿ⁻ᶜℱ) → Hᵖ(X, ℱ)` is the inclusion of `IⁿHᵖ(X, ℱ)` — which, read inside
   `Iⁿ⁻²ᶜHᵖ(X, ℱ)`, where the image of `Hᵖ(X, Iⁿ⁻ᶜℱ) → Hᵖ(X, ℱ)` lies by part (2), is the
   source's composite `IⁿHᵖ(X, ℱ) → Hᵖ(X, Iⁿ⁻ᶜℱ) → Iⁿ⁻²ᶜHᵖ(X, ℱ)` — and, for `n ≥ 2c`, the
   image under `cmp` of the class of `x ∈ Hᵖ(X, Iⁿℱ)` in `Iⁿ⁻ᶜHᵖ(X, ℱ)` (the hypothesis
   `(y : Hᵖ(X, ℱ)) = ...` below says that `y` is that class, which lies in `Iⁿ⁻ᶜHᵖ(X, ℱ)` by
   part (2)) is the canonical image of `x` in `Hᵖ(X, Iⁿ⁻²ᶜℱ)`;
5. the two inverse systems `(Hᵖ(X, Iⁿℱ))` and `(IⁿHᵖ(X, ℱ))` are pro-isomorphic, in the
   explicit up-to-refinement sense `InverseSequence.ProIso`.

Parts (1), (2) and (3) are the Artin-Rees argument for Rees systems,
`Stacks.RingTheory.ReesSystem.exists_uniform_bound_rees`, run on
`Stacks.Cohomology.FormalFunctions.cohomologyIdealPowerSystem`: its finiteness input is
[Stacks, Tag 02O8], `Stacks.Cohomology.FormalFunctions.isCohomologyReesFinite`, and its two
compatibility laws are `cohomologyIdealPowerSystem_isTrMulCompatible`. Parts (4) and (5) are
`Stacks.Cohomology.FormalFunctions.exists_comparison_cohomology`, whose hypotheses are those
three parts. -/
@[stacks 02OA]
theorem exists_uniform_bound_cohomology_of_isProper [IsNoetherianRing A]
    (hX : AlgebraicGeometry.IsProper X.hom) [F.IsCoherent] (p : ℕ) :
    ∃ c : ℕ,
      (∀ r : ℕ, c ≤ r → Function.Surjective
        ((cohomologyTr I X F p (show r ≤ r - c + c by omega)).comp
          (cohomologyMulTensor I X F p (r - c) c))) ∧
      (∀ n m : ℕ, c ≤ n + m →
        LinearMap.range (cohomologyTr I X F p (Nat.le_add_right n m)) ≤
          I ^ (m - (c - n)) • (⊤ : Submodule A (cohomologyIdealPower I X F p n))) ∧
      (∀ r : ℕ, c ≤ r → LinearMap.range (cohomologyProj I X F p r) ≤
        I ^ (r - c) • (⊤ : Submodule A (cohomology X F p))) ∧
      (∀ (m k : ℕ) (hmk : m + c ≤ k),
        LinearMap.ker (cohomologyProj I X F p k) =
          LinearMap.ker (cohomologyTr I X F p
            (show m ≤ k from le_trans (Nat.le_add_right m c) hmk))) ∧
      (∃ cmp : ∀ n : ℕ, c ≤ n →
          ↥(I ^ n • (⊤ : Submodule A (cohomology X F p))) →ₗ[A]
            cohomologyIdealPower I X F p (n - c),
        (∀ (n : ℕ) (hn : c ≤ n) (y : ↥(I ^ n • (⊤ : Submodule A (cohomology X F p)))),
            cohomologyProj I X F p (n - c) (cmp n hn y) = (y : cohomology X F p)) ∧
          ∀ (n : ℕ) (hn : c + c ≤ n) (x : cohomologyIdealPower I X F p n)
            (y : ↥(I ^ (n - c) • (⊤ : Submodule A (cohomology X F p)))),
            (y : cohomology X F p) = cohomologyProj I X F p n x →
            cmp (n - c) (Nat.le_sub_of_add_le hn) y =
              cohomologyTr I X F p ((Nat.sub_le (n - c) c).trans (Nat.sub_le n c)) x) ∧
      Nonempty (InverseSequence.ProIso (cohomologyIdealPowerFunctor I X F p)
        (Stacks.RingTheory.idealPowerSmulSystem I (cohomology X F p))) := by
  have hfin : (cohomologyIdealPowerSystem I X F p).IsReesFinite :=
    isCohomologyReesFinite I X F p hX
  obtain ⟨c, h1, h2, h3, h4⟩ := (cohomologyIdealPowerSystem I X F p).exists_uniform_bound_rees
    (cohomologyIdealPowerSystem_isTrMulCompatible I X F p) hfin
  have h1' : ∀ r : ℕ, c ≤ r → Function.Surjective
      ((cohomologyTr I X F p (show r ≤ r - c + c by omega)).comp
        (cohomologyMulTensor I X F p (r - c) c)) := by
    intro r hr y
    have hle : (cohomologyIdealPowerSystem I X F p).mulSpan (r - c) c r
        (show r ≤ r - c + c by omega) ≤
        LinearMap.range ((cohomologyTr I X F p (show r ≤ r - c + c by omega)).comp
          (cohomologyMulTensor I X F p (r - c) c)) := by
      refine Submodule.span_le.2 ?_
      rintro _ ⟨⟨u, v⟩, rfl⟩
      exact ⟨u ⊗ₜ[A] v, rfl⟩
    rw [h1 r hr] at hle
    exact hle Submodule.mem_top
  have h2' : ∀ n m : ℕ, c ≤ n + m →
      LinearMap.range (cohomologyTr I X F p (Nat.le_add_right n m)) ≤
        I ^ (m - (c - n)) • (⊤ : Submodule A (cohomologyIdealPower I X F p n)) := fun n m hnm ↦
    (h2 n m hnm).trans_eq (by rw [Ideal.map_id])
  have h3' : ∀ r : ℕ, c ≤ r → LinearMap.range (cohomologyProj I X F p r) ≤
      I ^ (r - c) • (⊤ : Submodule A (cohomology X F p)) := fun r hr ↦
    (h3 r hr).trans_eq (by rw [Ideal.map_id])
  obtain ⟨cmp, hcmp, hcmp', hpro⟩ := exists_comparison_cohomology I X F p c h1' h3' h4
  exact ⟨c, h1', h2', h3', h4, ⟨cmp, hcmp, hcmp'⟩, hpro⟩

end Tag02OA

/-! ### [Stacks, Tag 02OB] -/

section Tag02OB

variable (A : Type u) [CommRing A] {X : Scheme.{u}} (f : X ⟶ Spec (.of A)) (J : Ideal A)
  (G : X.Modules)

/-- **[Stacks, Tag 02OB].** For `A` Noetherian, `J ⊆ A` an ideal, `f : X ⟶ Spec A` proper and
`ℱ` coherent there is a single `c ≥ 0` such that, with `𝓙 = J · 𝒪_X`:

1. `Ker(Hᵖ(X, ℱ) → Hᵖ(X, ℱ / 𝓙ⁿℱ)) ⊆ Jⁿ⁻ᶜHᵖ(X, ℱ)` for every `n ≥ c`;
2. the inverse system `n ↦ Hᵖ(X, ℱ / 𝓙ⁿℱ)` satisfies the Mittag-Leffler condition;
3. for every `k ≥ n + c` the image of `Hᵖ(X, ℱ / 𝓙ᵏℱ)` in `Hᵖ(X, ℱ / 𝓙ⁿℱ)` equals the image of
   `Hᵖ(X, ℱ)`.

This is
`Stacks.Cohomology.FormalFunctions.exists_uniform_bound_cohomology_idealPowerQuotient_of_02O8`
with its hypothesis, [Stacks, Tag 02O8] in general form, discharged by
`Stacks.FormalFunctions.isReesFinite_cohomologyIdealPowerSystem`. -/
@[stacks 02OB, sga "2 IX 1.1" "Clause (3), special case", sga "2 IX 2.1" "(iii)"]
theorem exists_uniform_bound_cohomology_idealPowerQuotient_of_isProper [IsNoetherianRing A]
    (hf : AlgebraicGeometry.IsProper f) [G.IsCoherent] (p : ℕ) :
    ∃ c : ℕ,
      (∀ n : ℕ, c ≤ n →
          LinearMap.ker (cohomologyOverBaseMap A f p
              (cokernel.π (C := X.Modules)
                (idealPowerMultiple (baseIdealSheaf A J f) n G).ι)).hom ≤
            J ^ (n - c) • (⊤ : Submodule A (cohomologyOverBase A f p G))) ∧
        IsMittagLefflerCategorical
          (adicQuotientSystem (baseIdealSheaf A J f) G ⋙
            (Stacks.Cohomology.AffineBase.moduleGlobalSections X).rightDerived p) ∧
        ∀ n k : ℕ, (hk : n + c ≤ k) →
          LinearMap.range
              (((Stacks.Cohomology.AffineBase.moduleGlobalSections X).rightDerived p).map
                (idealPowerQuotientDrop (baseIdealSheaf A J f)
                  ((Nat.le_add_right n c).trans hk) G)).hom =
            LinearMap.range
              (((Stacks.Cohomology.AffineBase.moduleGlobalSections X).rightDerived p).map
                (cokernel.π (C := X.Modules)
                  (idealPowerMultiple (baseIdealSheaf A J f) n G).ι)).hom :=
  exists_uniform_bound_cohomology_idealPowerQuotient_of_02O8 A f hf J G
    (stacksIsCoherent_of_isCoherent inferInstance) p
    Stacks.FormalFunctions.isReesFinite_cohomologyIdealPowerSystem

end Tag02OB

/-! ### [Stacks, Tag 02OC] -/

section Tag02OC

variable (A : Type u) [CommRing A] {X : Scheme.{u}} (f : X ⟶ Spec (.of A)) (I : Ideal A)
  (F : X.Modules)

/-- **[Stacks, Tag 02OC].** For `A` Noetherian, `I ⊆ A` an ideal, `f : X ⟶ Spec A` proper and
`ℱ` coherent, the maps `Hᵖ(X, ℱ)/IⁿHᵖ(X, ℱ) → Hᵖ(X, ℱ/𝓘ⁿℱ)` assemble into an isomorphism

  `Hᵖ(X, ℱ)^∧_I ≅ limₙ Hᵖ(X, ℱ/𝓘ⁿℱ)`

of `A`-modules, and that isomorphism is a homeomorphism for the limit topologies.

The second component says that the `n`-th projection of the isomorphism carries the image of a
class `x ∈ Hᵖ(X, ℱ)` to the image of `x` in `Hᵖ(X, ℱ/𝓘ⁿℱ)`, so the isomorphism is the one the
source's system of maps defines and not merely some isomorphism between the two modules. The
third is the source's further assertion: the limit topology on `Hᵖ(X, ℱ)^∧_I = limₙ Hᵖ(X, ℱ)/Iⁿ`
and the limit topology on `limₙ Hᵖ(X, ℱ/𝓘ⁿℱ)` correspond under it. By
`Stacks.IntertwinedFiltration.adicCompletionModuleLimitTopology_eq_adicModuleTopology` the
topology on the left is equally the `I`-adic topology of the completion, which is the source's
own footnote to the statement.

The module isomorphism is `Stacks.Cohomology.FormalFunctions.formalFunctionsEquiv` together
with `formalFunctionsEquiv_proj_of`, and the homeomorphism is
`Stacks.IntertwinedFiltration.isHomeomorph_adicCompletionEquivTowerLimit_limitTopology` for the
same map; the hypotheses of all three are clauses (1) and (3) of [Stacks, Tag 02OB], which come
from `exists_uniform_bound_cohomology_idealPowerQuotient_of_isProper`, together with the
finite generation of `I` that `IsNoetherianRing A` supplies. -/
@[stacks 02OC, ega "III 4.1.7"]
theorem exists_formalFunctionsEquiv_of_isProper [IsNoetherianRing A]
    (hf : AlgebraicGeometry.IsProper f) [F.IsCoherent] (p : ℕ) :
    ∃ e : AdicCompletion I (cohomologyOverBase A f p F) ≃ₗ[A]
        towerLimit (adicCohomologyTower A f I F p) (adicCohomologyTowerMap A f I F p),
      (∀ (n : ℕ) (x : cohomologyOverBase A f p F),
          towerLimit.proj n (e (AdicCompletion.of I (cohomologyOverBase A f p F) x)) =
            adicCohomologyProj A f I F p n x) ∧
        @IsHomeomorph _ _
          (adicCompletionModuleLimitTopology (M := cohomologyOverBase A f p F) I)
          (towerLimit.limitTopology (adicCohomologyTower A f I F p)
            (adicCohomologyTowerMap A f I F p)) e := by
  have := isQuasicoherent_of_isCoherent F
  obtain ⟨c, hker, -, hrange⟩ :=
    exists_uniform_bound_cohomology_idealPowerQuotient_of_isProper A f I F hf p
  refine ⟨formalFunctionsEquiv A f I F p c hker hrange,
    formalFunctionsEquiv_proj_of A f I F p c hker hrange, ?_⟩
  exact isHomeomorph_adicCompletionEquivTowerLimit_limitTopology
    (adicCohomologyTower A f I F p) (adicCohomologyTowerMap A f I F p)
    (adicCohomologyProj A f I F p) I c
    (adicCohomologyTowerMap_comp_adicCohomologyProj A f I F p)
    (pow_smul_top_le_ker_adicCohomologyProj A f I F p) hker
    (fun n k _ hk => Submodule.ext fun _ => (SetLike.ext_iff.1 (hrange n k hk) _))
    (Ideal.fg_of_isNoetherianRing I)

end Tag02OC

end Stacks.Cohomology.FormalFunctions

/-! ### [Stacks, Tag 087U] -/

/- [Stacks, Tag 087U] for every `p ≥ 0` — for `A` Noetherian and `J`-adically complete,
`f : X ⟶ Spec A` proper and `ℱ` coherent, `Hᵖ(X, ℱ) ⟶ limₙ Hᵖ(X, ℱ/Jⁿℱ)` is an isomorphism — is
`Stacks.Algebraization.isIso_cohomologyToLimit_of_isProper_of_isAdicComplete`, proved with no
hypothesis beyond the tag's own. It is registered here. -/
add_to_stacks 087U Stacks.Algebraization.isIso_cohomologyToLimit_of_isProper_of_isAdicComplete

end
