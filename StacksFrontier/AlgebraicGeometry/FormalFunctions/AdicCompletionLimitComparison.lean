module

public import StacksCore.Tactic.StacksAttribute
public import StacksFrontier.AlgebraicGeometry.FormalFunctions.IdealPowerQuotientCohomologyBound
public import StacksFrontier.AlgebraicGeometry.FormalGeometry.Completion.AdicQuotientMap
public import StacksFrontier.AlgebraicGeometry.TopDegreeBaseChange.CohomologyLinear
public import StacksFrontier.RingTheory.AdicCompletion.IntertwinedFiltration

/-!
# The theorem on formal functions

Let `A` be a ring, `I ⊆ A` an ideal, `f : X ⟶ Spec A` a morphism of schemes, `ℱ` a
quasi-coherent sheaf of modules on `X` and `p ≥ 0`. Write `𝓘 = I · 𝒪_X` for the ideal sheaf
`I` generates on `X`, and put

* `M = H^p(X, ℱ)`, an `A`-module through `A ⟶ Γ(X, 𝒪_X)`;
* `M n = H^p(X, ℱ / 𝓘 ^ n ℱ)`, the `n`-th term of the tower, with transition maps induced by
  the exponent-lowering maps `ℱ / 𝓘 ^ k ℱ ⟶ ℱ / 𝓘 ^ n ℱ`.

[Stacks, Tag 02OC] says that the maps `M / I ^ n M ⟶ M n` assemble into an isomorphism
`M ^∧_I ≅ lim_n M n`. That is `Stacks.Cohomology.FormalFunctions.formalFunctionsEquiv`, and
`Stacks.Cohomology.FormalFunctions.formalFunctionsEquiv_proj_of` says that it is *the* map
assembled from those projections: its `n`-th component takes the image of `x ∈ M` to the image
of `x` in `M n`.

Only the isomorphism of `A`-modules is proved here. [Stacks, Tag 02OC] also asserts that the
comparison is a homeomorphism for the limit topologies; that is not formalized, and neither
statement below claims it.

The source's proof is run abstractly in
`StacksFrontier/RingTheory/AdicCompletion/IntertwinedFiltration.lean`: with `K n = ker (M ⟶ M n)`,
the containments `I ^ n M ⊆ K n ⊆ I ^ (n - c) M` make the `K`-filtration cofinal in the `I`-adic
one, and the stabilization of the images of the transition maps identifies `lim_n M n` with
`lim_n M / K n`. This file supplies the four hypotheses of
`Stacks.IntertwinedFiltration.adicCompletionEquivTowerLimit` for that tower.

Two of them are the clauses of [Stacks, Tag 02OB] and are carried as the named hypotheses
`h02OB_ker` and `h02OB_range`, exactly as
`Stacks.Cohomology.FormalFunctions.exists_uniform_bound_cohomology_idealPowerQuotient` produces
them; that lemma is where the source's standing hypotheses — `A` Noetherian, `f` proper and `ℱ`
coherent — are used, and they are therefore not repeated here. The remaining two hypotheses are
proved: compatibility of the projections with the transitions is functoriality of `H ^ p`, and
`I ^ n M ⊆ K n` is the sentence "`I ^ n M ⊆ K n` because `N n` is killed by `I ^ n`" of the
source's proof, which is `pow_smul_top_le_ker_adicCohomologyProj` below.

## Main definitions

* `Stacks.Cohomology.FormalFunctions.adicCohomologyTower`,
  `adicCohomologyTowerMap` and `adicCohomologyProj` — the tower `n ↦ H^p(X, ℱ / 𝓘 ^ n ℱ)` of
  `A`-modules, its transition maps, and the maps to it from `H^p(X, ℱ)`.
* `Stacks.Cohomology.FormalFunctions.formalFunctionsEquiv` — the comparison isomorphism
  `H^p(X, ℱ) ^∧_I ≅ lim_n H^p(X, ℱ / 𝓘 ^ n ℱ)`.

## Main results

* `Stacks.Cohomology.FormalFunctions.smul_cohomologyOverBase_eq_zero` — `I ^ n` annihilates
  `H^p(X, ℱ / 𝓘 ^ n ℱ)`.
* `Stacks.Cohomology.FormalFunctions.pow_smul_top_le_ker_adicCohomologyProj` — hence
  `I ^ n H^p(X, ℱ) ⊆ ker (H^p(X, ℱ) ⟶ H^p(X, ℱ / 𝓘 ^ n ℱ))`.
* `Stacks.Cohomology.FormalFunctions.formalFunctionsEquiv_proj_of` — the comparison
  isomorphism is the one assembled from the projections.

## Implementation notes

The annihilation of `H^p(X, ℱ / 𝓘 ^ n ℱ)` by `I ^ n` is proved by moving the statement to the
sheaf: multiplication by `α ∈ I ^ n` is the zero endomorphism of `ℱ / 𝓘 ^ n ℱ`, and `H ^ p` is
`A`-linear by `Stacks.Cohomology.AffineBase.linear_rightDerived_moduleGlobalSections`, so `α`
acts as zero on cohomology. The sheaf-level vanishing is affine-local — it is
`Stacks.Algebraization.pow_smul_top_idealPowerQuotient_eq_bot` — and is spread to all opens
through the sheaf condition, because the affine opens form a basis.

The `A`-linear structure on `X.Modules` and the `A`-algebra structure on `Γ(X, 𝒪_X)` are not
global instances: both depend on the structure morphism `f` and not only on `X`. They are
therefore introduced by `let` where needed, with the type ascribed at `X.Modules` rather than at
`(Over.mk f).left.Modules` so that instance resolution recognizes them, as in
`StacksFrontier/AlgebraicGeometry/Perfect/DerivedEquivalence.lean`.

`LinearMap.range` and `LinearMap.ker` over `A` and over `Γ(X, 𝒪_X)` have the same carrier, since
restriction of scalars changes neither types nor maps. Clause (3) of [Stacks, Tag 02OB] is
stated at `Γ(X, 𝒪_X)` and is used here as an `A`-submodule identity through that definitional
coincidence, which is why `le_antisymm` with a membership argument suffices.

## References

* [Stacks Project, Tag 02OC](https://stacks.math.columbia.edu/tag/02OC)
* [Stacks Project, Tag 02OB](https://stacks.math.columbia.edu/tag/02OB)
-/

@[expose] public noncomputable section

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits Opposite
open scoped ModuleCat.Algebra

universe u

namespace Stacks.Cohomology.FormalFunctions

open Stacks.Cohomology.AffineBase Stacks.Algebraization Stacks.IntertwinedFiltration

variable (A : Type u) [CommRing A] {X : Scheme.{u}} (f : X ⟶ Spec (.of A)) (I : Ideal A)
  (F : X.Modules)

/-! ### `I ^ n` annihilates `ℱ / 𝓘 ^ n ℱ` -/

/-- The restriction to an affine open of a global function coming from `I ^ n` lies in the
`n`-th power of the ideal that `I · 𝒪_X` cuts out there: the restriction of `baseIdeal A I f`
generates that ideal, and restriction commutes with forming powers. -/
public lemma res_baseRingHom_mem_baseIdealSheaf_pow (n : ℕ) {α : A} (hα : α ∈ I ^ n)
    (U : X.Opens) (V : X.affineOpens) (hVU : (V : X.Opens) ≤ U) :
    (X.presheaf.map (homOfLE hVU).op).hom
        ((X.presheaf.map (homOfLE (le_top (a := U))).op).hom (baseRingHom A f α)) ∈
      (baseIdealSheaf A I f).ideal V ^ n := by
  have hres : (X.presheaf.map (homOfLE hVU).op).hom
        ((X.presheaf.map (homOfLE (le_top (a := U))).op).hom (baseRingHom A f α)) =
      (X.presheaf.map (homOfLE (le_top (a := (V : X.Opens)))).op).hom (baseRingHom A f α) := by
    rw [← CommRingCat.comp_apply, ← Functor.map_comp, ← op_comp]
    rfl
  rw [hres, baseIdealSheaf_ideal, ← Ideal.map_pow, ← baseIdeal_pow]
  exact Ideal.mem_map_of_mem _ (mem_baseIdeal A (I ^ n) f hα)

/-- A function whose restriction to every affine open lies in the `n`-th power of the ideal cut
out there by `I · 𝒪_X` kills every section of `ℱ / 𝓘 ^ n ℱ`.

Over an affine open this is `Stacks.Algebraization.pow_smul_top_idealPowerQuotient_eq_bot`; over
a general open it follows because the affine opens form a basis and the sections of a sheaf are
separated. -/
public lemma smul_sections_idealPowerQuotient_eq_zero [F.IsQuasicoherent] (n : ℕ) (U : X.Opens)
    (r : Γ(X, U))
    (hr : ∀ (V : X.affineOpens) (hVU : (V : X.Opens) ≤ U),
      (X.presheaf.map (homOfLE hVU).op).hom r ∈ (baseIdealSheaf A I f).ideal V ^ n)
    (s : Γ(idealPowerQuotient (baseIdealSheaf A I f) n F, U)) :
    r • s = 0 := by
  apply (Scheme.Modules.isSheaf (idealPowerQuotient (baseIdealSheaf A I f) n F)).section_ext
  intro x hx
  obtain ⟨_, ⟨V, hV, rfl⟩, hxV, hVU⟩ :=
    X.isBasis_affineOpens.exists_subset_of_mem_open hx U.isOpen
  have hVU' : V ≤ U := hVU
  refine ⟨V, hVU, hxV, ?_⟩
  rw [Scheme.Modules.map_smul, map_zero]
  refine (Submodule.mem_bot (↑Γ(X, V))).1 ?_
  rw [← pow_smul_top_idealPowerQuotient_eq_bot (baseIdealSheaf A I f) n F ⟨V, hV⟩]
  exact Submodule.smul_mem_smul (hr ⟨V, hV⟩ hVU') Submodule.mem_top

/-- **Multiplication by `α ∈ I ^ n` is the zero endomorphism of `ℱ / 𝓘 ^ n ℱ`.** The scalar
action of `A` on a sheaf of modules over a scheme over `Spec A` is multiplication by the image
of the scalar in the functions on each open, so this is
`smul_sections_idealPowerQuotient_eq_zero` open by open. -/
public lemma smul_id_idealPowerQuotient_eq_zero [F.IsQuasicoherent] (n : ℕ) {α : A}
    (hα : α ∈ I ^ n) :
    letI : Linear A X.Modules := AlgebraicGeometry.modulesLinear A (Over.mk f)
    α • 𝟙 (idealPowerQuotient (baseIdealSheaf A I f) n F) = 0 := by
  let _i : Linear A X.Modules := AlgebraicGeometry.modulesLinear A (Over.mk f)
  apply SheafOfModules.hom_ext
  apply PresheafOfModules.hom_ext
  intro U
  apply ModuleCat.hom_ext
  ext s
  change AlgebraicGeometry.baseRingToSections A (Over.mk f) U α • s = 0
  exact smul_sections_idealPowerQuotient_eq_zero A f I F n U.unop
    ((X.presheaf.map (homOfLE (le_top (a := U.unop))).op).hom (baseRingHom A f α))
    (fun V hVU => res_baseRingHom_mem_baseIdealSheaf_pow A f I n hα U.unop V hVU) s

/-- **`I ^ n` annihilates `H^p(X, ℱ / 𝓘 ^ n ℱ)`.** Multiplication by `α ∈ I ^ n` is the zero
endomorphism of the sheaf `ℱ / 𝓘 ^ n ℱ`, and cohomology of a scheme over `Spec A` is `A`-linear,
so `α` acts as zero on `H^p`.

This is the sentence "`I ^ n M ⊆ K n` because `N n` is killed by `I ^ n`" of the proof of
[Stacks, Tag 02OC]. -/
public lemma smul_cohomologyOverBase_eq_zero [F.IsQuasicoherent] (p n : ℕ) {α : A}
    (hα : α ∈ I ^ n)
    (y : cohomologyOverBase A f p (idealPowerQuotient (baseIdealSheaf A I f) n F)) :
    α • y = 0 := by
  let _i : Linear A X.Modules := AlgebraicGeometry.modulesLinear A (Over.mk f)
  let _a : Algebra A Γ(X, ⊤) := baseSectionsAlgebra A (Over.mk f)
  have hlin : Functor.Linear A ((moduleGlobalSections X).rightDerived p) :=
    linear_rightDerived_moduleGlobalSections A (Over.mk f) p
  have hz : ((moduleGlobalSections X).rightDerived p).map
      (α • 𝟙 (idealPowerQuotient (baseIdealSheaf A I f) n F)) = 0 := by
    rw [smul_id_idealPowerQuotient_eq_zero A f I F n hα, Functor.map_zero]
  rw [Functor.map_smul, CategoryTheory.Functor.map_id] at hz
  have hy := LinearMap.congr_fun (ModuleCat.hom_ext_iff.1 hz) y
  have hbridge : algebraMap A Γ(X, ⊤) α = baseRingHom A f α := by
    change (X.presheaf.map (homOfLE (le_top (a := (⊤ : X.Opens)))).op).hom (baseRingHom A f α) =
      baseRingHom A f α
    rw [show (homOfLE (le_top (a := (⊤ : X.Opens)))).op = 𝟙 (op (⊤ : X.Opens)) from rfl,
      CategoryTheory.Functor.map_id]
    rfl
  calc α • y = algebraMap A Γ(X, ⊤) α • y := by rw [hbridge]; rfl
    _ = 0 := hy

/-! ### The tower of cohomology modules of the adic quotients -/

/-- The `n`-th term `H^p(X, ℱ / 𝓘 ^ n ℱ)` of the tower, as an `A`-module. -/
public abbrev adicCohomologyTower (p n : ℕ) : Type u :=
  cohomologyOverBase A f p (idealPowerQuotient (baseIdealSheaf A I f) n F)

/-- The transition map `H^p(X, ℱ / 𝓘 ^ n ℱ) ⟶ H^p(X, ℱ / 𝓘 ^ m ℱ)` of the tower, for
`m ≤ n`: the cohomology of the exponent-lowering map. -/
public abbrev adicCohomologyTowerMap (p : ℕ) (m n : ℕ) (h : m ≤ n) :
    adicCohomologyTower A f I F p n →ₗ[A] adicCohomologyTower A f I F p m :=
  (cohomologyOverBaseMap A f p (idealPowerQuotientDrop (baseIdealSheaf A I f) h F)).hom

/-- The map `H^p(X, ℱ) ⟶ H^p(X, ℱ / 𝓘 ^ n ℱ)`, the cohomology of the quotient projection. -/
public abbrev adicCohomologyProj (p n : ℕ) :
    cohomologyOverBase A f p F →ₗ[A] adicCohomologyTower A f I F p n :=
  (cohomologyOverBaseMap A f p
    (cokernel.π (C := X.Modules) (idealPowerMultiple (baseIdealSheaf A I f) n F).ι)).hom

/-- The maps out of `H^p(X, ℱ)` are compatible with the transitions of the tower: the quotient
projections are, and `H ^ p` is a functor. -/
public lemma adicCohomologyTowerMap_comp_adicCohomologyProj (p : ℕ) (m n : ℕ) (h : m ≤ n) :
    (adicCohomologyTowerMap A f I F p m n h).comp (adicCohomologyProj A f I F p n) =
      adicCohomologyProj A f I F p m := by
  refine LinearMap.ext fun x => ?_
  have hcomp : ((moduleGlobalSections X).rightDerived p).map
        (cokernel.π (C := X.Modules) (idealPowerMultiple (baseIdealSheaf A I f) n F).ι) ≫
      ((moduleGlobalSections X).rightDerived p).map
        (idealPowerQuotientDrop (baseIdealSheaf A I f) h F) =
      ((moduleGlobalSections X).rightDerived p).map
        (cokernel.π (C := X.Modules) (idealPowerMultiple (baseIdealSheaf A I f) m F).ι) := by
    rw [← Functor.map_comp, idealPowerQuotientDrop_π]
  have hval := LinearMap.congr_fun (ModuleCat.hom_ext_iff.1 hcomp) x
  simp only [ModuleCat.hom_comp, LinearMap.coe_comp] at hval
  exact hval

/-- `I ^ n H^p(X, ℱ)` is contained in the kernel of `H^p(X, ℱ) ⟶ H^p(X, ℱ / 𝓘 ^ n ℱ)`, because
the target is annihilated by `I ^ n`. -/
public lemma pow_smul_top_le_ker_adicCohomologyProj [F.IsQuasicoherent] (p n : ℕ) :
    I ^ n • (⊤ : Submodule A (cohomologyOverBase A f p F)) ≤
      LinearMap.ker (adicCohomologyProj A f I F p n) := by
  refine Submodule.smul_le.2 fun α hα x _ => ?_
  rw [LinearMap.mem_ker, map_smul]
  exact smul_cohomologyOverBase_eq_zero A f I F p n hα _

/-! ### The theorem on formal functions -/

variable (p : ℕ) (c : ℕ)

/-- **Stacks Project, Tag 02OC**, granted [Stacks, Tag 02OB], and for the `A`-module
isomorphism only.

With `𝓘 = I · 𝒪_X`, the `I`-adic completion of `H^p(X, ℱ)` is the limit of the tower
`n ↦ H^p(X, ℱ / 𝓘 ^ n ℱ)`. The map is the one assembled from the projections
`H^p(X, ℱ) ⟶ H^p(X, ℱ / 𝓘 ^ n ℱ)`, which is the content of
`formalFunctionsEquiv_proj_of`. [Stacks, Tag 02OC] further asserts that the comparison is a
homeomorphism for the limit topologies; that is **not** proved here, and no statement in this
file claims it.

The two hypotheses are clauses (1) and (3) of [Stacks, Tag 02OB], for a fixed `c`, in the shape
`Stacks.Cohomology.FormalFunctions.exists_uniform_bound_cohomology_idealPowerQuotient` produces
them: `h02OB_ker` bounds the kernel of the `n`-th projection by `I ^ (n - c) H^p(X, ℱ)`, and
`h02OB_range` says that for `k ≥ n + c` the image of `H^p(X, ℱ / 𝓘 ^ k ℱ)` in
`H^p(X, ℱ / 𝓘 ^ n ℱ)` is the image of `H^p(X, ℱ)`. Clause (2) of that lemma, the
Mittag-Leffler condition, is not needed: in this formulation it is subsumed by clause (3). The
source's standing hypotheses — `A` Noetherian, `f` proper and `ℱ` coherent — are what make
[Stacks, Tag 02OB] true and are used nowhere else, so only quasi-coherence of `ℱ`, which the
annihilation argument needs, appears.

Everything else is `Stacks.IntertwinedFiltration.adicCompletionEquivTowerLimit`, the source's
own argument carried out abstractly. -/
@[stacks 02OC "the isomorphism of A-modules only, not the homeomorphism for the limit
topologies; granted Tag 02OB, whose clauses (1) and (3) are carried as the hypotheses
h02OB_ker and h02OB_range"]
public def formalFunctionsEquiv [F.IsQuasicoherent]
    (h02OB_ker : ∀ n : ℕ, c ≤ n →
      LinearMap.ker (adicCohomologyProj A f I F p n) ≤
        I ^ (n - c) • (⊤ : Submodule A (cohomologyOverBase A f p F)))
    (h02OB_range : ∀ n k : ℕ, (hk : n + c ≤ k) →
      LinearMap.range (((moduleGlobalSections X).rightDerived p).map
          (idealPowerQuotientDrop (baseIdealSheaf A I f)
            ((Nat.le_add_right n c).trans hk) F)).hom =
        LinearMap.range (((moduleGlobalSections X).rightDerived p).map
          (cokernel.π (C := X.Modules)
            (idealPowerMultiple (baseIdealSheaf A I f) n F).ι)).hom) :
    AdicCompletion I (cohomologyOverBase A f p F) ≃ₗ[A]
      towerLimit (adicCohomologyTower A f I F p) (adicCohomologyTowerMap A f I F p) :=
  adicCompletionEquivTowerLimit (adicCohomologyTower A f I F p)
    (adicCohomologyTowerMap A f I F p) (adicCohomologyProj A f I F p) I c
    (adicCohomologyTowerMap_comp_adicCohomologyProj A f I F p)
    (pow_smul_top_le_ker_adicCohomologyProj A f I F p) h02OB_ker
    fun n k _ hk =>
      le_antisymm (fun _ hx => (h02OB_range n k hk).le hx)
        (fun _ hx => (h02OB_range n k hk).ge hx)

/-- **The comparison isomorphism of [Stacks, Tag 02OC] is the canonical one**: its `n`-th
component carries the image in `H^p(X, ℱ) ^∧_I` of a class `x ∈ H^p(X, ℱ)` to the image of `x`
in `H^p(X, ℱ / 𝓘 ^ n ℱ)`. Together with `formalFunctionsEquiv` this says that the maps
`H^p(X, ℱ) / I ^ n H^p(X, ℱ) ⟶ H^p(X, ℱ / 𝓘 ^ n ℱ)` assemble into an isomorphism, rather than
merely that the two modules are isomorphic. -/
@[stacks 02OC "the identification of the isomorphism of formalFunctionsEquiv as the one
assembled from the projections; same hypotheses, and again nothing about the limit topologies"]
public lemma formalFunctionsEquiv_proj_of [F.IsQuasicoherent]
    (h02OB_ker : ∀ n : ℕ, c ≤ n →
      LinearMap.ker (adicCohomologyProj A f I F p n) ≤
        I ^ (n - c) • (⊤ : Submodule A (cohomologyOverBase A f p F)))
    (h02OB_range : ∀ n k : ℕ, (hk : n + c ≤ k) →
      LinearMap.range (((moduleGlobalSections X).rightDerived p).map
          (idealPowerQuotientDrop (baseIdealSheaf A I f)
            ((Nat.le_add_right n c).trans hk) F)).hom =
        LinearMap.range (((moduleGlobalSections X).rightDerived p).map
          (cokernel.π (C := X.Modules)
            (idealPowerMultiple (baseIdealSheaf A I f) n F).ι)).hom)
    (n : ℕ) (x : cohomologyOverBase A f p F) :
    towerLimit.proj n (formalFunctionsEquiv A f I F p c h02OB_ker h02OB_range
        (AdicCompletion.of I (cohomologyOverBase A f p F) x)) =
      adicCohomologyProj A f I F p n x :=
  rfl

end Stacks.Cohomology.FormalFunctions

end
