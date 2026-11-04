module

public import StacksFrontier.AlgebraicGeometry.FormalFunctions.CohomologyIdealPowerSystem
public import StacksFrontier.AlgebraicGeometry.FormalFunctions.IdealPowerQuotientCohomologyBound

/-!
# The two spellings of [Stacks, Tag 02OA]'s uniform bound

[Stacks, Tag 02OA] is proved in this library twice over, in two vocabularies that no declaration
related.

* `Stacks.Cohomology.FormalFunctions.exists_uniform_bound_cohomology` states its parts (2) at
  `n = 0` and (3) for a scheme presented as an object `X : Over (Spec A)`, with the cohomology
  modules and the maps between them named `cohomology`, `cohomologyProj` and `cohomologyTr`, all
  of them `A`-linear maps obtained from `Hᵖ(X, −)` by restricting scalars along
  `Stacks.Cohomology.AffineBase.baseSectionsAlgebra`.
* `Stacks.Cohomology.FormalFunctions.exists_uniform_bound_cohomology_idealPowerQuotient`, which
  is [Stacks, Tag 02OB], consumes those same two parts as the hypotheses `h02OA_image` and
  `h02OA_kernel`, for a scheme presented by its structure morphism `f : X ⟶ Spec A`, written with
  `cohomologyOverBase` and `cohomologyOverBaseMap`, whose `A`-action is restriction of scalars
  along `baseRingHom`, and with the transition maps spelled `submoduleInclusion` rather than
  `idealPowerMultipleMap`.

This file is the translation. With it, [Stacks, Tag 02OB] holds granted only [Stacks, Tag 02O8] —
the Rees-finiteness of `⨁ₙ Hᵖ(X, 𝓘ⁿℱ)` — and no longer granted [Stacks, Tag 02OA].

## Main results

* `Stacks.Cohomology.FormalFunctions.exists_range_le_cohomologyOverBase` — part (2) at `n = 0` of
  [Stacks, Tag 02OA] in the spelling of `h02OA_image`.
* `Stacks.Cohomology.FormalFunctions.exists_ker_eq_cohomologyRightDerived` — part (3) of
  [Stacks, Tag 02OA] in the spelling of `h02OA_kernel`.
* `Stacks.Cohomology.FormalFunctions.exists_uniform_bound_idealPowerQuotient_of_reesFinite` —
  the three clauses of [Stacks, Tag 02OB] granted [Stacks, Tag 02O8] alone.

## Implementation notes

The two presentations of the scheme are reconciled by instantiating the `Over (Spec A)` one at
`Over.mk f`, for which `(Over.mk f).left` is `X` and `(Over.mk f).hom` is `f` definitionally, so
`baseIdealSheaf A I (Over.mk f).hom` and `baseIdealSheaf A I f` are the same ideal sheaf. The
transition maps then agree on the nose: `cohomologyTr` is built from `idealPowerMultipleMap`,
`h02OA_kernel` from `Stacks.Algebraization.submoduleInclusion`, and both are
`SheafOfModules.Submodule.homOfLE` of a proof of the same inclusion.

What is *not* definitional is the `A`-module structure. `cohomologyProj` is an `A`-linear map for
the action coming from `baseSectionsAlgebra`, which pushes a scalar into `Γ(X, 𝒪_X)` by
`baseRingToSections` — the structure morphism followed by the restriction `Γ(X, ⊤) ⟶ Γ(X, ⊤)` —
whereas `cohomologyOverBase` restricts scalars along `baseRingHom`, the structure morphism alone.
The two ring maps differ by `X.presheaf.map (𝟙 ⊤)`, so the two `Module A` instances are distinct
terms and a `Submodule A` for one is not a `Submodule A` for the other. The *actions* are
nevertheless definitionally equal, since the restriction along `𝟙` is applied to a scalar and not
to a module structure, which is why `smul_mem_smul_of_mem_smul_top` below can rebuild a
membership in `I ^ e • ⊤` on the other side by `Submodule.smul_induction_on`: the generators
`a • x` are literally the same elements.

## References

* [Stacks Project, Tag 02OA](https://stacks.math.columbia.edu/tag/02OA)
* [Stacks Project, Tag 02OB](https://stacks.math.columbia.edu/tag/02OB)
* [Stacks Project, Tag 02O8](https://stacks.math.columbia.edu/tag/02O8)
-/

@[expose] public noncomputable section

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits Opposite
open Stacks.AlgebraicGeometry.IdealPower Stacks.Cohomology.AffineBase
open Stacks.Algebraization (submoduleInclusion)
open scoped ModuleCat.Algebra

universe u

namespace Stacks.Cohomology.FormalFunctions

attribute [local instance] AlgebraicGeometry.modulesLinear baseSectionsAlgebra

variable {A : Type u} [CommRing A] (I : Ideal A) {X : Scheme.{u}} (f : X ⟶ Spec (.of A))
  (F : X.Modules)

/-- **The two `A`-actions on the functions of a scheme over `Spec A` are the same ring map.**
`Stacks.Cohomology.AffineBase.baseSectionsAlgebra` sends `a` into `Γ(X, 𝒪_X)` through the
structure morphism followed by the restriction `Γ(X, ⊤) ⟶ Γ(X, ⊤)` along `𝟙 ⊤`, while
`baseRingHom` uses the structure morphism alone; the restriction is the identity. -/
theorem algebraMap_baseSections_eq_baseRingHom :
    (algebraMap A Γ((Over.mk f).left, ⊤) : A →+* Γ(X, ⊤)) = baseRingHom A f := by
  ext a
  calc (algebraMap A Γ((Over.mk f).left, ⊤)) a
      = (X.presheaf.map (homOfLE (le_refl (⊤ : X.Opens))).op).hom
        ((f.appTop).hom ((Scheme.ΓSpecIso (.of A)).inv.hom a)) := rfl
    _ = baseRingHom A f a := by
      rw [show (homOfLE (le_refl (⊤ : X.Opens))).op = 𝟙 _ from rfl,
        CategoryTheory.Functor.map_id]
      rfl

/-- **The identity is an `A`-linear equivalence between the two readings of `Hᵖ(X, ℱ)`**: the
one whose `A`-action comes from `baseSectionsAlgebra`, which is what
`Stacks.Cohomology.FormalFunctions.cohomology` is, and `cohomologyOverBase`, which restricts
scalars along `baseRingHom`. The underlying sets and additions are the same, and the two actions
agree by `algebraMap_baseSections_eq_baseRingHom`. -/
def cohomologyOverBaseEquiv (q : ℕ) :
    cohomology (Over.mk f) F q ≃ₗ[A] cohomologyOverBase A f q F :=
  { AddEquiv.refl (cohomology (Over.mk f) F q) with
    map_smul' := fun a x ↦ by
      change (algebraMap A Γ((Over.mk f).left, ⊤) a) • x = (baseRingHom A f a) • x
      rw [algebraMap_baseSections_eq_baseRingHom] }

/-- **Part (2) at `n = 0` of [Stacks, Tag 02OA], in the spelling `h02OA_image` of
[Stacks, Tag 02OB] asks for.** The hypothesis is the first clause of
`Stacks.Cohomology.FormalFunctions.exists_uniform_bound_cohomology`, whose `A`-module structure
is the one `Stacks.Cohomology.AffineBase.baseSectionsAlgebra` prescribes; the conclusion is the
same containment for the `A`-module structure of `cohomologyOverBase`, which restricts scalars
along `baseRingHom` instead. The two are carried into one another by
`cohomologyOverBaseEquiv`. -/
theorem exists_range_le_cohomologyOverBase (q : ℕ)
    (h : ∃ c : ℕ, ∀ r : ℕ, c ≤ r →
      LinearMap.range (cohomologyProj I (Over.mk f) F q r) ≤
        I ^ (r - c) • (⊤ : Submodule A (cohomology (Over.mk f) F q))) :
    ∃ c : ℕ, ∀ k : ℕ, c ≤ k →
      LinearMap.range (cohomologyOverBaseMap A f q
          (idealPowerMultiple (baseIdealSheaf A I f) k F).ι).hom ≤
        I ^ (k - c) • (⊤ : Submodule A (cohomologyOverBase A f q F)) := by
  obtain ⟨c, hc⟩ := h
  set e := cohomologyOverBaseEquiv f F q
  refine ⟨c, fun k hk ↦ ?_⟩
  have hmap : Submodule.map (e : cohomology (Over.mk f) F q →ₗ[A] cohomologyOverBase A f q F)
      (I ^ (k - c) • (⊤ : Submodule A (cohomology (Over.mk f) F q))) =
      I ^ (k - c) • (⊤ : Submodule A (cohomologyOverBase A f q F)) := by
    rw [Submodule.map_smul'', Submodule.map_top,
      LinearMap.range_eq_top_of_surjective _ e.surjective]
  rw [← hmap]
  exact fun y hy ↦ ⟨e.symm y, hc k hk hy, e.apply_symm_apply y⟩

/-- **Part (3) of [Stacks, Tag 02OA], in the spelling `h02OA_kernel` of [Stacks, Tag 02OB] asks
for.** The hypothesis is the second clause of
`Stacks.Cohomology.FormalFunctions.exists_uniform_bound_cohomology`, an equality of
`A`-submodules of the cohomology of `𝓘ᵏℱ`; the conclusion is the same equality read as
`Γ(X, 𝒪_X)`-submodules, with the transition map spelled by
`Stacks.Algebraization.submoduleInclusion` and the smaller exponent taken to be `k - c`. Both
kernels are cut out by the same equation on elements, so the two readings determine each other. -/
theorem exists_ker_eq_cohomologyRightDerived (q : ℕ)
    (h : ∃ c : ℕ, ∀ (m k : ℕ) (hmk : m + c ≤ k),
      LinearMap.ker (cohomologyProj I (Over.mk f) F q k) =
        LinearMap.ker (cohomologyTr I (Over.mk f) F q
          (le_trans (Nat.le_add_right m c) hmk))) :
    ∃ c : ℕ, ∀ k : ℕ, c ≤ k →
      LinearMap.ker (((moduleGlobalSections X).rightDerived q).map
          (idealPowerMultiple (baseIdealSheaf A I f) k F).ι).hom =
        LinearMap.ker (((moduleGlobalSections X).rightDerived q).map
          (submoduleInclusion (Stacks.Algebraization.idealPowerMultiple_antitone
            (baseIdealSheaf A I f) F (Nat.sub_le k c)))).hom := by
  obtain ⟨c, hc⟩ := h
  refine ⟨c, fun k hk ↦ Submodule.ext fun x ↦ ?_⟩
  exact SetLike.ext_iff.mp (hc (k - c) k (Nat.sub_add_cancel hk).le) x

/-- **[Stacks, Tag 02OB] granted [Stacks, Tag 02O8] alone.** The hypotheses `h02OA_image` and
`h02OA_kernel` of
`Stacks.Cohomology.FormalFunctions.exists_uniform_bound_cohomology_idealPowerQuotient` are
discharged here by `Stacks.Cohomology.FormalFunctions.exists_uniform_bound_cohomology`, which
proves them from the Rees-finiteness of `⨁ₙ Hᵖ(X, 𝓘ⁿℱ)`; that finiteness, [Stacks, Tag 02O8], is
the one hypothesis left, carried in the general form that
`exists_uniform_bound_cohomology` consumes.

The second clause is the Mittag-Leffler condition for the tower `n ↦ Hᵖ(X, ℱ/𝓘ⁿℱ)`, which is
what the properness clause of [Stacks, Tag 0A0M] rests on. -/
theorem exists_uniform_bound_idealPowerQuotient_of_reesFinite [IsNoetherianRing A]
    (hf : AlgebraicGeometry.IsProper f) (hF : SheafOfModules.IsCoherent F) (p : ℕ)
    (h02O8 : ∀ (A' : Type u) [CommRing A'] [IsNoetherianRing A'] (I' : Ideal A')
      (X' : Over (Spec (.of A'))) (_ : AlgebraicGeometry.IsProper X'.hom)
      (F' : X'.left.Modules) (_ : SheafOfModules.IsCoherent F') (p' : ℕ),
      (cohomologyIdealPowerSystem I' X' F' p').IsReesFinite) :
    ∃ c : ℕ,
      (∀ n : ℕ, c ≤ n →
          LinearMap.ker (cohomologyOverBaseMap A f p
              (cokernel.π (C := X.Modules)
                (idealPowerMultiple (baseIdealSheaf A I f) n F).ι)).hom ≤
            I ^ (n - c) • (⊤ : Submodule A (cohomologyOverBase A f p F))) ∧
        IsMittagLefflerCategorical
          (Stacks.Algebraization.adicQuotientSystem (baseIdealSheaf A I f) F ⋙
            (moduleGlobalSections X).rightDerived p) ∧
        ∀ n k : ℕ, (hk : n + c ≤ k) →
          LinearMap.range (((moduleGlobalSections X).rightDerived p).map
              (Stacks.Algebraization.idealPowerQuotientDrop (baseIdealSheaf A I f)
                ((Nat.le_add_right n c).trans hk) F)).hom =
            LinearMap.range (((moduleGlobalSections X).rightDerived p).map
              (cokernel.π (C := X.Modules)
                (idealPowerMultiple (baseIdealSheaf A I f) n F).ι)).hom := by
  refine exists_uniform_bound_cohomology_idealPowerQuotient A f I F p (fun q ↦ ?_) (fun q ↦ ?_)
  · obtain ⟨c, h₁, -⟩ := exists_uniform_bound_cohomology I (Over.mk f) F hf hF q h02O8
    exact exists_range_le_cohomologyOverBase I f F q ⟨c, h₁⟩
  · obtain ⟨c, -, h₂⟩ := exists_uniform_bound_cohomology I (Over.mk f) F hf hF q h02O8
    exact exists_ker_eq_cohomologyRightDerived I f F q ⟨c, h₂⟩

end Stacks.Cohomology.FormalFunctions

end
