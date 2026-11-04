module

public import Mathlib.LinearAlgebra.Dual.Lemmas
public import Mathlib.RingTheory.KrullDimension.Field
public import Mathlib.RingTheory.Spectrum.Prime.Topology
public import StacksFrontier.AlgebraicGeometry.Cohomology.ExtFromStructureSheafLinear
public import StacksFrontier.AlgebraicGeometry.Curves.LinearSeries
public import StacksFrontier.AlgebraicGeometry.Curves.VanishingResults.DualizingSheafClauseFive
public import StacksFrontier.AlgebraicGeometry.SerreAffinenessCriterion.VanishingCriterion
import StacksCore.Tactic.StacksAttribute

/-!
# `dim_k H¹(X, ω_X) = 1` for the dualizing sheaf of a proper curve

In Situation [Stacks, Tag 0B5D] — a field `k` and a proper one-dimensional `k`-scheme `X` with
`H⁰(X, 𝒪_X) = k` — let `ω_X = H^{-1}(f^×(𝒪_{Spec k}))` be the dualizing sheaf of
[Stacks, Tag 0BS2]. This file proves

  `dim_k H¹(X, ω_X) = 1`,

the equality that the proof of Lemma 53.5.1 of Section [Stacks, Tag 0B5B] reads off duality and
that the vanishing results for curves consume. **Nothing is carried.**

## Main results

The elided prefix is `AlgebraicGeometry.CohenMacaulayCurveSituation`.

* `finrank_hom_unit_dualizingComplex_eq_one`: **the upper bound's source.**
  `dim_k Hom_{D(𝒪_X)}(𝒪_X[0], ω_X^•) = 1`, which is clause (4) of [Stacks, Tag 0BS2] at
  `K = 𝒪_X` and `i = 0` read `k`-linearly, together with `H⁰(X, 𝒪_X) = k`.
* `finrank_cohomologyOverField_one_dualizingSheaf_le_one`: `dim_k H¹(X, ω_X) ≤ 1`.
* `not_isAffine`: `X` is not affine.
* `not_subsingleton_cohomologyOverField_one_dualizingSheaf`: `H¹(X, ω_X) ≠ 0`.
* `finrank_cohomologyOverField_one_dualizingSheafOverField_eq_one`: `dim_k H¹(X, ω_X) = 1`.

## The two bounds

**The upper bound.** Clause (4) of [Stacks, Tag 0BS2] in degree zero
(`Stacks.Duality.dualityLinearEquivZero`) identifies `Hom_{D(𝒪_X)}(𝒪_X[0], ω_X^•)` with the
`k`-linear dual of `H⁰(X, 𝒪_X)`, which is one-dimensional in Situation [Stacks, Tag 0B5D]; the
dual of a space has the same dimension as the space, so that morphism group is a line. The
truncation `τ^{≤ -1}(ω_X^•)` is `ω_X` placed in degree `-1`
(`Stacks.Duality.singleShiftOneIsoTruncLE`), and composing with `τ^{≤ -1}(ω_X^•) ⟶ ω_X^•`
embeds `Hom_{D(𝒪_X)}(𝒪_X[0], ω_X[0]⟦1⟧)` into that line: the composite is injective by
`Stacks.Duality.eq_zero_of_comp_truncLEι_app_eq_zero`, because `𝒪_X[0]` lies in `D^{≤ 0}`.
Finally that morphism group *is* `H¹(X, ω_X)`, `k`-linearly, by
`AlgebraicGeometry.zExtOneLinearEquivCohomologyOverField`. Both the `k`-linearity of that last
comparison and its transport between the two models of the derived category are what
`StacksFrontier/AlgebraicGeometry/Cohomology/ExtFromStructureSheafLinear.lean` supplies; without
them the embedding bounds no dimension over `k`.

**The lower bound is not a formal consequence of the upper one**: it fails for a complex
`ω_X^•` concentrated in degree zero, where `ω_X = H^{-1}(ω_X^•) = 0` and the one dimension of
`Hom_{D(𝒪_X)}(𝒪_X[0], ω_X^•)` is accounted for by `H^0(ω_X^•)`. Ruling that out is the content
of [Stacks, Tag 0BS3], and the route here does not go through it. Instead it uses clause (5) of
[Stacks, Tag 0BS2], `Hom(ℱ, ω_X) = Hom_k(H¹(X, ℱ), k)`, which is proved unconditionally as
`firstCohomologyDuality_dualizingSheafOverField`:

1. If `H¹(X, ω_X) = 0` then at `ℱ = ω_X` clause (5) makes `End(ω_X)` trivial, so `𝟙_{ω_X} = 0`
   and `ω_X` is a zero object.
2. Then at an arbitrary quasi-coherent `ℱ` clause (5) makes `Hom_k(H¹(X, ℱ), k)` trivial, and a
   `k`-vector space with trivial dual is trivial; so `H¹(X, ℱ) = 0` for **every** quasi-coherent
   `ℱ`.
3. Serre's criterion for affineness ([Stacks, Tag 01XF],
   `Stacks.SerreCriterion.isAffine_of_forall_isZero_H1_ideal`) then makes `X` affine.
4. An affine `X` with `Γ(X, 𝒪_X) = k` is `Spec` of a field, so `topologicalKrullDim X = 0`,
   contradicting `topologicalKrullDim X = 1`.

So the Cohen--Macaulayness of `X` — true in Situation [Stacks, Tag 0B5D], and the shape in which
[Stacks, Tag 0BS3] would supply the lower bound — is not needed: the global statement that `X`
is not affine does the same work, and it is available.

## References

* [Stacks Project, Tag 0B5B](https://stacks.math.columbia.edu/tag/0B5B)
* [Stacks Project, Tag 0BS2](https://stacks.math.columbia.edu/tag/0BS2)
* [Stacks Project, Tag 0BS3](https://stacks.math.columbia.edu/tag/0BS3)
* [Stacks Project, Tag 0B5D](https://stacks.math.columbia.edu/tag/0B5D)
* [Stacks Project, Tag 01XF](https://stacks.math.columbia.edu/tag/01XF)
-/

-- This file uses the locally small derived-category models below, which are not
-- global instances (see `StacksFrontier.Homology.DerivedCategory.LocallySmall`):
-- `D(𝒪_X)` for a scheme.
attribute [local instance] AlgebraicGeometry.Scheme.Modules.hasDerivedCategory

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Abelian CategoryTheory.Limits Opposite AlgebraicGeometry
  TopologicalSpace CategoryTheory.Triangulated
open Stacks.Duality.DerivedPushforward (derivedStructureSheaf)

universe u

namespace AlgebraicGeometry.CohenMacaulayCurveSituation

variable (S : CohenMacaulayCurveSituation.{u})

/-! ### The structure sheaf as an object of the quasi-coherent derived category -/

/-- `𝒪_X[0]` lies in `D^{≤ 0}`. Stated because the instance for a module placed in degree zero
is not found through the definition of `Stacks.Duality.DerivedPushforward.derivedStructureSheaf`,
the object `𝒪_X[0]` of `D_QCoh(𝒪_X)` in which clause (4) of [Stacks, Tag 0BS2] consumes it. -/
instance isLE_derivedStructureSheaf_obj :
    DerivedCategory.TStructure.t.IsLE
      (derivedStructureSheaf S.X).obj 0 :=
  inferInstanceAs (DerivedCategory.TStructure.t.IsLE
    ((DerivedCategory.singleFunctor S.X.Modules 0).obj (Stacks.Ample.unitModule S.X)) 0)

/-! ### The upper bound -/

/-- **`dim_k Hom_{D(𝒪_X)}(𝒪_X[0], ω_X^•) = 1`.** Clause (4) of [Stacks, Tag 0BS2] in degree zero
identifies this morphism group with the `k`-linear dual of `H⁰(X, 𝒪_X)`, which is
one-dimensional in Situation [Stacks, Tag 0B5D]; a space and its dual have the same dimension. -/
theorem finrank_hom_unit_dualizingComplex_eq_one :
    letI := Scheme.Modules.linearOverBase S.f
    letI : Functor.Linear S.k (globalSectionsOver S.f) :=
      globalSectionsOver_linear_linearOverBase S.f
    Module.finrank S.k ((derivedStructureSheaf S.X).obj ⟶
      (Stacks.Duality.dualizingComplexOverField S.f).obj) = 1 := by
  let := Scheme.Modules.linearOverBase S.f
  let : Functor.Linear S.k (globalSectionsOver S.f) := globalSectionsOver_linear_linearOverBase S.f
  have e := (Stacks.Duality.dualityLinearEquivZero S.f (derivedStructureSheaf S.X)).trans
    (Stacks.Duality.derivedCohomologyOverFieldDualLinearEquiv S.f
      (Stacks.Ample.unitModule S.X) 0 0 rfl)
  rw [e.finrank_eq, Subspace.dual_finrank_eq,
    finrank_cohomologyOverField_unit_zero_eq_one S.f]

/-- **`H¹(X, ω_X)` embeds `k`-linearly into `Hom_{D(𝒪_X)}(𝒪_X[0], ω_X^•)`.**

The group `H¹(X, ω_X)` is `Hom_{D(𝒪_X)}(𝒪_X[0], ω_X[0]⟦1⟧)` by
`AlgebraicGeometry.zExtOneLinearEquivCohomologyOverField`, and `ω_X[0]⟦1⟧` is the truncation
`τ^{≤ -1}(ω_X^•)` by `Stacks.Duality.singleShiftOneIsoTruncLE`; composing with the canonical map
`τ^{≤ -1}(ω_X^•) ⟶ ω_X^•` is injective because `𝒪_X[0]` lies in `D^{≤ 0}`, which is
`Stacks.Duality.eq_zero_of_comp_truncLEι_app_eq_zero`. -/
theorem exists_injective_firstCohomology_to_hom_dualizingComplex :
    letI := Scheme.Modules.linearOverBase S.f
    letI : Functor.Linear S.k (globalSectionsOver S.f) :=
      globalSectionsOver_linear_linearOverBase S.f
    ∃ Φ : cohomologyOverField S.k S.f (Stacks.Duality.dualizingSheafOverField S.f) 1 →ₗ[S.k]
      ((derivedStructureSheaf S.X).obj ⟶ (Stacks.Duality.dualizingComplexOverField S.f).obj),
      Function.Injective Φ := by
  let := Scheme.Modules.linearOverBase S.f
  let : Functor.Linear S.k (globalSectionsOver S.f) := globalSectionsOver_linear_linearOverBase S.f
  have hiso := Stacks.Duality.singleShiftOneIsoTruncLE S.f S.dimension_one.le
  let Ψ : Abelian.zExt (Stacks.Ample.unitModule S.X)
      (Stacks.Duality.dualizingSheafOverField S.f) (1 : ℤ) →ₗ[S.k]
      ((derivedStructureSheaf S.X).obj ⟶ (Stacks.Duality.dualizingComplexOverField S.f).obj) :=
    Linear.rightComp S.k ((derivedStructureSheaf S.X).obj)
      (hiso.hom ≫ (DerivedCategory.TStructure.t.truncLEι (-1)).app
        (Stacks.Duality.dualizingComplexOverField S.f).obj)
  have hΨ : Function.Injective Ψ := by
    refine (injective_iff_map_eq_zero Ψ).mpr fun g hg => ?_
    have hg' : (g ≫ hiso.hom) ≫ (DerivedCategory.TStructure.t.truncLEι (-1)).app
          (Stacks.Duality.dualizingComplexOverField S.f).obj = 0 :=
      (Category.assoc _ _ _).trans hg
    have hz := Stacks.Duality.eq_zero_of_comp_truncLEι_app_eq_zero
      DerivedCategory.TStructure.t (-1) 0 (by ring) _ hg'
    exact (cancel_mono hiso.hom).mp (hz.trans (Limits.zero_comp).symm)
  exact ⟨Ψ.comp ((zExtOneLinearEquivCohomologyOverField S.f
    (Stacks.Duality.dualizingSheafOverField S.f)).symm : _ →ₗ[S.k] _),
    hΨ.comp (zExtOneLinearEquivCohomologyOverField S.f
      (Stacks.Duality.dualizingSheafOverField S.f)).symm.injective⟩

/-- **`dim_k H¹(X, ω_X) ≤ 1`.** The `k`-linear embedding of
`exists_injective_firstCohomology_to_hom_dualizingComplex` lands in a one-dimensional space. -/
theorem finrank_cohomologyOverField_one_dualizingSheaf_le_one :
    Module.finrank S.k
      (cohomologyOverField S.k S.f (Stacks.Duality.dualizingSheafOverField S.f) 1) ≤ 1 := by
  let := Scheme.Modules.linearOverBase S.f
  let : Functor.Linear S.k (globalSectionsOver S.f) := globalSectionsOver_linear_linearOverBase S.f
  have := Module.finite_of_finrank_eq_succ (finrank_hom_unit_dualizingComplex_eq_one S)
  obtain ⟨Φ, hΦ⟩ := exists_injective_firstCohomology_to_hom_dualizingComplex S
  exact (LinearMap.finrank_le_finrank_of_injective hΦ).trans
    (finrank_hom_unit_dualizingComplex_eq_one S).le

/-- **`H¹(X, ω_X)` is finite-dimensional**, being embedded in a line. -/
theorem finiteDimensional_cohomologyOverField_one_dualizingSheaf :
    FiniteDimensional S.k
      (cohomologyOverField S.k S.f (Stacks.Duality.dualizingSheafOverField S.f) 1) := by
  let := Scheme.Modules.linearOverBase S.f
  let : Functor.Linear S.k (globalSectionsOver S.f) := globalSectionsOver_linear_linearOverBase S.f
  have := Module.finite_of_finrank_eq_succ (finrank_hom_unit_dualizingComplex_eq_one S)
  obtain ⟨Φ, hΦ⟩ := exists_injective_firstCohomology_to_hom_dualizingComplex S
  exact Module.Finite.of_injective Φ hΦ

/-! ### The lower bound -/

/-- **A `k`-vector space whose dual is trivial is trivial.** A nonzero vector of a vector space
carries a functional that does not vanish on it. -/
theorem subsingleton_of_subsingleton_dual {V : Type*} [AddCommGroup V] [Module S.k V]
    (h : Subsingleton (V →ₗ[S.k] S.k)) : Subsingleton V :=
  subsingleton_of_forall_eq 0 fun v =>
    (Module.forall_dual_apply_eq_zero_iff S.k v).mp fun φ => by
      rw [Subsingleton.elim φ 0, LinearMap.zero_apply]

/-- **`X` is not affine** in Situation [Stacks, Tag 0B5D]. An affine scheme is the spectrum of
its global functions, which here are the base field, so an affine `X` would be the spectrum of a
field and therefore of dimension zero — against `topologicalKrullDim X = 1`. -/
theorem not_isAffine : ¬ IsAffine S.X := by
  intro haff
  have h1 : topologicalKrullDim ↥S.X = topologicalKrullDim (PrimeSpectrum ↥Γ(S.X, ⊤)) :=
    IsHomeomorph.topologicalKrullDim_eq _ S.X.isoSpec.hom.homeomorph.isHomeomorph
  have hfield : IsField ↥Γ(S.X, ⊤) :=
    (CategoryTheory.Iso.commRingCatIsoToRingEquiv
      (asIso ((Scheme.ΓSpecIso (.of S.k)).inv ≫ S.f.appTop))).symm.toMulEquiv.isField
      (Field.toIsField S.k)
  have h2 : topologicalKrullDim (PrimeSpectrum ↥Γ(S.X, ⊤)) = 0 := by
    rw [PrimeSpectrum.topologicalKrullDim_eq_ringKrullDim]
    exact ringKrullDim_eq_zero_of_isField hfield
  rw [S.dimension_one, h2] at h1
  exact one_ne_zero h1

/-- **`H¹(X, ω_X) ≠ 0`.**

Were it zero, clause (5) of [Stacks, Tag 0BS2] at `ℱ = ω_X` would make `End(ω_X)` trivial, so
`ω_X` a zero object, and then clause (5) at an arbitrary quasi-coherent `ℱ` would make
`H¹(X, ℱ)` trivial for every quasi-coherent `ℱ`; by Serre's criterion
([Stacks, Tag 01XF]) `X` would then be affine, which `not_isAffine` excludes. -/
theorem not_subsingleton_cohomologyOverField_one_dualizingSheaf :
    ¬ Subsingleton
      (cohomologyOverField S.k S.f (Stacks.Duality.dualizingSheafOverField S.f) 1) := by
  intro hsub
  have hdual := firstCohomologyDuality_dualizingSheafOverField S
  have hωq := Stacks.Duality.isQuasicoherent_dualizingSheafOverField S.f
  have hdualsub : Subsingleton
      (cohomologyOverField S.k S.f (Stacks.Duality.dualizingSheafOverField S.f) 1 →ₗ[S.k] S.k) :=
    ⟨fun a b => LinearMap.ext fun x => by
      rw [Subsingleton.elim x 0, map_zero, map_zero]⟩
  have hEnd : Subsingleton (Stacks.Duality.dualizingSheafOverField S.f ⟶
      Stacks.Duality.dualizingSheafOverField S.f) :=
    (Equiv.subsingleton_congr
      (hdual.dual (Stacks.Duality.dualizingSheafOverField S.f) hωq).toEquiv).mpr hdualsub
  have hωzero : IsZero (Stacks.Duality.dualizingSheafOverField S.f) :=
    (IsZero.iff_id_eq_zero _).mpr (Subsingleton.elim _ _)
  have hvan : ∀ F : S.X.Modules, F.IsQuasicoherent →
      Subsingleton (cohomologyOverField S.k S.f F 1) := fun F hF =>
    subsingleton_of_subsingleton_dual S
      ((Equiv.subsingleton_congr (hdual.dual F hF).toEquiv).mp ⟨hωzero.eq_of_tgt⟩)
  have : CompactSpace S.X := QuasiCompact.compactSpace_of_compactSpace S.f
  have haff : IsAffine S.X :=
    Stacks.SerreCriterion.isAffine_of_forall_isZero_H1_ideal S.X fun I hI =>
      @ModuleCat.isZero_of_subsingleton _ _ _ (hvan (Subobject.underlying.obj I) hI)
  exact not_isAffine S haff

/-! ### `dim_k H¹(X, ω_X) = 1` -/

/-- **`dim_k H¹(X, ω_X) = 1`** in Situation [Stacks, Tag 0B5D], for the dualizing sheaf
`ω_X = H^{-1}(f^×(𝒪_{Spec k}))` of [Stacks, Tag 0BS2].

This is the equality that the proof of Lemma 53.5.1 of Section [Stacks, Tag 0B5B] reads off the
duality `H^i(X, ω_X^•) = Hom_k(H^{-i}(X, 𝒪_X), k)` at `i = 0`, and it is the hypothesis `hone`
of `AlgebraicGeometry.CohenMacaulayCurveSituation.nonempty_generatingSections_tensorSheaf`. The
upper bound is that duality — clause (4) of [Stacks, Tag 0BS2], read `k`-linearly — together
with `H⁰(X, 𝒪_X) = k`; the lower bound is clause (5) of [Stacks, Tag 0BS2] together with
Serre's criterion for affineness, which rules out the vanishing of `H¹(X, ω_X)` without
appealing to [Stacks, Tag 0BS3]. See the module documentation.

[Stacks, Tag 0B5B] (not registered here: this is not the whole statement of the tag): the equality
dim_k H^1(X, omega_X) = 1 that the proof of Lemma 53.5.1 of this section reads off the duality
H^i(X, omega^bullet) = Hom_k(H^(-i)(X, O_X), k) at i = 0, at the dualizing sheaf omega_X =
H^(-1)(f^x(O_Spec k)) of Tag 0BS2, with nothing carried beyond Situation 0B5D itself, which the
declaration takes as its argument S. The upper bound is clause (4) of Tag 0BS2 read k-linearly,
which is proved, together with H^0(X, O_X) = k of Situation 0B5D; the lower bound is clause (5) of
Tag 0BS2, also proved, together with Serre's criterion for affineness of Tag 01XF, and so does not
go through Tag 0BS3
-/
theorem finrank_cohomologyOverField_one_dualizingSheafOverField_eq_one :
    Module.finrank S.k
      (cohomologyOverField S.k S.f (Stacks.Duality.dualizingSheafOverField S.f) 1) = 1 := by
  have := finiteDimensional_cohomologyOverField_one_dualizingSheaf S
  have : Nontrivial
      (cohomologyOverField S.k S.f (Stacks.Duality.dualizingSheafOverField S.f) 1) :=
    not_subsingleton_iff_nontrivial.mp
      (not_subsingleton_cohomologyOverField_one_dualizingSheaf S)
  exact le_antisymm (finrank_cohomologyOverField_one_dualizingSheaf_le_one S) Module.finrank_pos

end AlgebraicGeometry.CohenMacaulayCurveSituation

end
