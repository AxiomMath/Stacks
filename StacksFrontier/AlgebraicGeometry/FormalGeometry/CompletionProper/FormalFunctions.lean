module

public import Mathlib.AlgebraicGeometry.Morphisms.Proper
public import StacksFrontier.AlgebraicGeometry.AffineCohomologyVanishing.AffineBase
public import StacksFrontier.AlgebraicGeometry.FormalGeometry.CompletionFunctor.FullyFaithful
public import StacksFrontier.AlgebraicGeometry.TopDegreeBaseChange.CohomologyLinear
public import StacksFrontier.RingTheory.AdicCompletion.Basic
public import Mathlib.RingTheory.AdicCompletion.Noetherian
public import StacksCore.Tactic.StacksAttribute

/-!
# The theorem on formal functions over a complete base

**Stacks 087U.** Let `A` be a Noetherian ring complete with respect to an ideal `J`, let
`f : X ⟶ Spec A` be proper and let `F` be a coherent sheaf on `X`. Then

  `Hᵖ(X, F) = limₙ Hᵖ(X, F / Jⁿ F)`

for every `p ≥ 0`.

This file constructs the comparison map for every `p` and proves that it is an isomorphism from
three inputs, which are exactly the ones the source cites and which are the only places where
properness is used there:

* the finiteness of `Hᵖ(X, F)` as an `A`-module, [Stacks, Tag 02O6]; and
* the two uniform Artin-Rees bounds of [Stacks, Tag 02OB] — one on the kernels of
  `Hᵖ(X, F) ⟶ Hᵖ(X, F / Jⁿ F)` and one saying that the image of that map is the stable image of
  the tower.

In this file all three enter the main theorems as hypotheses. The library does prove them for
a proper morphism, in later files: the finiteness by
`Stacks.Algebraization.moduleFinite_cohomologyOverBase` and the two bounds by
`Stacks.Cohomology.FormalFunctions.exists_uniform_bound_cohomology_idealPowerQuotient_of_02O8`
over the unconditional [Stacks, Tag 02O8]. With them discharged, the unconditional
[Stacks, Tag 087U] is
`Stacks.Algebraization.isIso_cohomologyToLimit_of_isProper_of_isAdicComplete`
(`StacksFrontier/AlgebraicGeometry/FormalGeometry/CompletionFunctor/FullyFaithfulComplete.lean`),
which carries the tag; the conditional statements here are untagged.

What the file does prove is the rest of the source's argument. The substantive part is the
completion step: `Hᵖ(X, F)` is a finite module over a Noetherian `J`-adically complete ring,
hence is itself `J`-adically complete ([Stacks, Tag 031B] together with Krull's intersection
theorem), so no completion is needed on the left-hand side and the comparison map is an
isomorphism as soon as the two uniform bounds make it injective and surjective. That argument is
isolated as a statement about towers of modules,
`Stacks.Algebraization.bijective_of_kernelBound_of_stableImage`, which mentions no geometry.

The other ingredient proved here is the annihilation that makes the tower an adic tower of
`A`-modules: a base scalar from `Jᵏ` kills every sheaf of modules killed by the ideal sheaf
`(J · 𝒪_X) ᵏ`, hence kills the cohomology of the terms of the completion, because cohomology is
an `A`-linear functor.

## Main definitions

* `Stacks.Algebraization.completionCohomologySystem` — the inverse system
  `n ↦ Hᵖ(X, F / 𝓙ⁿ⁺¹ F)` of cohomology modules of the terms of the completion of `F`.
* `Stacks.Algebraization.cohomologyToLimit` — the comparison map
  `Hᵖ(X, F) ⟶ limₙ Hᵖ(X, F / 𝓙ⁿ⁺¹ F)` of the theorem on formal functions.
* `Stacks.Algebraization.baseAlgebra` — the `A`-algebra structure on `Γ(X, 𝒪_X)` through which
  the cohomology modules of a scheme over `A` are `A`-modules.

## Main results

* `Stacks.Algebraization.cohomologyToLimit_zero_eq` and
  `Stacks.Algebraization.isIso_globalSectionsToLimit_of_isIso_cohomologyToLimit` — in degree zero
  the comparison is `Stacks.Algebraization.globalSectionsToLimit`, the comparison that
  `Stacks.Algebraization.fullyFaithful_completionFunctor` (Stacks 0883) takes as its hypothesis.
* `Stacks.Algebraization.bijective_of_kernelBound_of_stableImage` — the elementary criterion:
  a complete module maps bijectively onto the limit of a tower under a uniform kernel bound and a
  uniform stable-image bound.
* `Stacks.Algebraization.baseSmul_eq_zero_of_idealPowerMultiple_eq_bot` — a base scalar from
  `Jᵏ` annihilates a sheaf of modules killed by `(J · 𝒪_X) ᵏ`.
* `Stacks.Algebraization.isIso_cohomologyToLimit` — the comparison of Stacks 087U is an
  isomorphism for all `p ≥ 0`, given the finiteness of [Stacks, Tag 02O6] and the two uniform
  bounds of [Stacks, Tag 02OB] as hypotheses; the unconditional Stacks 087U, with these
  discharged, is `Stacks.Algebraization.isIso_cohomologyToLimit_of_isProper_of_isAdicComplete`.

## Implementation notes

The inverse system of the completion functor is zero-indexed: its term at `n` is `F / 𝓙ⁿ⁺¹ F`.
That is immaterial for the limit — the term at `n = 0` of the source's indexing is
`F / 𝓙⁰ F = 0` — but it is why the annihilation hypothesis of the elementary criterion is stated
with `Jⁿ⁺¹` rather than `Jⁿ`.

Cohomology is taken as `Functor.rightDerived` of
`Stacks.Cohomology.AffineBase.moduleGlobalSections`, the global sections of sheaves of modules
valued in `ModuleCat Γ(X, 𝒪_X)`, because that is the form in which this library has the
`A`-linearity of cohomology
(`Stacks.Cohomology.AffineBase.linear_rightDerived_moduleGlobalSections`)
and the identification of its zeroth term with global sections (`Functor.rightDerivedZeroIsoSelf`,
through `Stacks.Cohomology.AffineBase.moduleGlobalSections_preservesFiniteLimits`). The
`A`-module structure on the cohomology is the one coming from `baseAlgebra` and the scoped
instances of `ModuleCat.Algebra`; the `A`-linear structure on the sheaves of modules is
`AlgebraicGeometry.modulesLinear`, which is supplied with an explicit type ascription at the
spelling `X.Modules` rather than at `(Over.mk f).left.Modules`, since instance search does not
unfold `Over.mk`.

`AlgebraicGeometry.Scheme.Modules` is a `def` for `SheafOfModules X.ringCatSheaf`, so the two
spellings carry separate instances. Accordingly `Stacks.Algebraization.cohomologyToLimit_zero_eq`
and `isIso_globalSectionsToLimit_of_isIso_cohomologyToLimit` are chained in term mode with
`congrArg` and `Eq.trans`, and the `IsIso` instances they need are passed positionally: a `rw`
whose motive crosses that boundary is not type-correct at the transparency `rw` builds it at, and
instance search does not cross it either.

## References

* [Stacks Project, Tag 087U](https://stacks.math.columbia.edu/tag/087U)
* [Stacks Project, Tag 02OB](https://stacks.math.columbia.edu/tag/02OB)
* [Stacks Project, Tag 02OC](https://stacks.math.columbia.edu/tag/02OC)
* [Stacks Project, Tag 02O6](https://stacks.math.columbia.edu/tag/02O6)
* [Stacks Project, Tag 031B](https://stacks.math.columbia.edu/tag/031B)
-/

@[expose] public noncomputable section

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits Opposite TopologicalSpace
open scoped AlgebraicGeometry

universe u

namespace Stacks.Algebraization

section Comparison

variable {X : Scheme.{u}} [IsLocallyNoetherian X] (I : X.IdealSheafData)
  (F : AlgebraicGeometry.SheafOfModules.CoherentModules X.ringCatSheaf)

/-- The inverse system `n ↦ Hᵖ(X, F / Iⁿ⁺¹ F)` of cohomology modules of the terms of the
completion of `F`. -/
public abbrev completionCohomologySystem (p : ℕ) : ℕᵒᵖ ⥤ ModuleCat.{u} Γ(X, ⊤) :=
  ((completionFunctor X I).obj F).obj ⋙
    (Stacks.Cohomology.AffineBase.moduleGlobalSections X).rightDerived p

/-- The comparison map `Hᵖ(X, F) ⟶ limₙ Hᵖ(X, F / Iⁿ⁺¹ F)`. -/
public def cohomologyToLimit (p : ℕ) :
    ((Stacks.Cohomology.AffineBase.moduleGlobalSections X).rightDerived p).obj F.obj ⟶
      limit (completionCohomologySystem I F p) :=
  limit.lift _ (((Stacks.Cohomology.AffineBase.moduleGlobalSections X).rightDerived p).mapCone
    (completionCone X I F))

/-- The comparison map is normalized by the cohomology of the canonical projections. -/
public theorem cohomologyToLimit_π (p : ℕ) (n : ℕᵒᵖ) :
    cohomologyToLimit I F p ≫ limit.π (completionCohomologySystem I F p) n =
      ((Stacks.Cohomology.AffineBase.moduleGlobalSections X).rightDerived p).map
        (completionProjection X I F n.unop) :=
  limit.lift_π _ n

/-! ### Degree zero -/

/-- In degree zero the system of cohomology modules of the terms of the completion is the system
of their global sections. -/
public def completionCohomologySystemZeroIso :
    completionCohomologySystem I F 0 ≅
      Stacks.Coherent.globalSectionsSystem ((completionFunctor X I).obj F) :=
  Functor.isoWhiskerLeft ((completionFunctor X I).obj F).obj
    (Functor.rightDerivedZeroIsoSelf (Stacks.Cohomology.AffineBase.moduleGlobalSections X))

/-- **The comparison map in degree zero is the comparison of the theorem on formal functions in
degree zero.** Under the identification of `R⁰Γ` with `Γ` the map `cohomologyToLimit` at `p = 0`
is `Stacks.Algebraization.globalSectionsToLimit`. -/
public theorem cohomologyToLimit_zero_eq :
    cohomologyToLimit I F 0 ≫
        (HasLimit.isoOfNatIso (completionCohomologySystemZeroIso I F)).hom =
      (Functor.rightDerivedZeroIsoSelf
          (Stacks.Cohomology.AffineBase.moduleGlobalSections X)).hom.app F.obj ≫
        globalSectionsToLimit I F :=
  limit.hom_ext fun n =>
    (Category.assoc _ _ _).trans
      ((congrArg (fun k => cohomologyToLimit I F 0 ≫ k)
            (HasLimit.isoOfNatIso_hom_π (completionCohomologySystemZeroIso I F) n)).trans
        ((Category.assoc _ _ _).symm.trans
          ((congrArg (fun k => k ≫ (completionCohomologySystemZeroIso I F).hom.app n)
                (cohomologyToLimit_π I F 0 n)).trans
            (((Functor.rightDerivedZeroIsoSelf
                    (Stacks.Cohomology.AffineBase.moduleGlobalSections X)).hom.naturality
                  (completionProjection X I F n.unop)).trans
              ((congrArg (fun k => (Functor.rightDerivedZeroIsoSelf
                      (Stacks.Cohomology.AffineBase.moduleGlobalSections X)).hom.app F.obj ≫ k)
                  (globalSectionsToLimit_π I F n).symm).trans
                (Category.assoc _ _ _).symm)))))

/-- The degree-zero comparison of the theorem on formal functions is an isomorphism as soon as
`cohomologyToLimit` is one in degree zero. -/
public theorem isIso_globalSectionsToLimit_of_isIso_cohomologyToLimit
    (h : IsIso (cohomologyToLimit I F 0)) : IsIso (globalSectionsToLimit I F) := by
  have hf : IsIso ((Functor.rightDerivedZeroIsoSelf
      (Stacks.Cohomology.AffineBase.moduleGlobalSections X)).hom.app F.obj) :=
    ((Functor.rightDerivedZeroIsoSelf
      (Stacks.Cohomology.AffineBase.moduleGlobalSections X)).app F.obj).isIso_hom
  have hh : IsIso (cohomologyToLimit I F 0 ≫
      (HasLimit.isoOfNatIso (completionCohomologySystemZeroIso I F)).hom) :=
    ((@asIso _ _ _ _ _ h) ≪≫
      HasLimit.isoOfNatIso (completionCohomologySystemZeroIso I F)).isIso_hom
  exact @IsIso.of_isIso_fac_left _ _ _ _ _ _ _ _ hf hh (cohomologyToLimit_zero_eq I F).symm

end Comparison

/-! ### The elementary comparison criterion -/

/-- **The elementary criterion behind the theorem on formal functions.** Let `M` be an
`I`-adically complete module over a commutative ring `R`, let `(T n)` be a tower of `R`-modules
with transition maps `t`, let `L` be an `R`-module with compatible maps `π n : L ⟶ T n` that
separate its elements (for instance the inverse limit of the tower), and let `cm : M ⟶ L` be a
map compatible with maps `q n : M ⟶ T n`.

Then `cm` is bijective as soon as

* `Iⁿ⁺¹ M` is killed by `q n`;
* there is a single `k₁` with `ker (q (n + k₁)) ⊆ Iⁿ M` for every `n` — a uniform Artin-Rees
  bound on the kernels; and
* there is a single `k₂` such that the image of `q n` contains the image of the transition map
  `T (n + k₂) ⟶ T n` — a uniform stable-image bound.

This is the module-theoretic content of the passage from the uniform bounds of
[Stacks, Tag 02OB] to the comparison of [Stacks, Tag 087U]: injectivity is the Hausdorff
property applied to the kernel bound, and surjectivity is precompleteness applied to the
Cauchy sequence of partial lifts provided by the stable-image bound. -/
public theorem bijective_of_kernelBound_of_stableImage
    {R : Type*} [CommRing R] {Jd : Ideal R}
    {M : Type*} [AddCommGroup M] [Module R M] [IsAdicComplete Jd M]
    {L : Type*} [AddCommGroup L] [Module R L]
    {T : ℕ → Type*} [∀ n, AddCommGroup (T n)] [∀ n, Module R (T n)]
    (cm : M →ₗ[R] L) (π : ∀ n, L →ₗ[R] T n) (q : ∀ n, M →ₗ[R] T n)
    (t : ∀ {m n : ℕ}, m ≤ n → T n →ₗ[R] T m)
    (hq : ∀ (n : ℕ) (x : M), π n (cm x) = q n x)
    (hqt : ∀ {m n : ℕ} (h : m ≤ n) (x : M), t h (q n x) = q m x)
    (hπt : ∀ {m n : ℕ} (h : m ≤ n) (y : L), t h (π n y) = π m y)
    (hsep : ∀ y z : L, (∀ n, π n y = π n z) → y = z)
    (hkill : ∀ n : ℕ, Jd ^ (n + 1) • (⊤ : Submodule R M) ≤ LinearMap.ker (q n))
    (k₁ k₂ : ℕ)
    (hker : ∀ (n : ℕ) (x : M), q (n + k₁) x = 0 → x ∈ Jd ^ n • (⊤ : Submodule R M))
    (himg : ∀ (n : ℕ) (y : T (n + k₂)), ∃ x : M, q n x = t (Nat.le_add_right n k₂) y) :
    Function.Bijective cm := by
  refine ⟨fun x y hxy => ?_, fun y => ?_⟩
  · rw [← sub_eq_zero]
    refine IsHausdorff.haus (I := Jd) inferInstance (x - y) fun n => ?_
    rw [SModEq.sub_mem, sub_zero]
    refine hker n (x - y) ?_
    rw [map_sub, ← hq (n + k₁), ← hq (n + k₁), hxy, sub_self]
  · have hsol : ∀ n : ℕ, ∃ x : M, q n x = π n y := fun n => by
      obtain ⟨x, hx⟩ := himg n (π (n + k₂) y)
      exact ⟨x, hx.trans (hπt (Nat.le_add_right n k₂) y)⟩
    choose a ha using hsol
    have hqa : ∀ {m n : ℕ}, m ≤ n → q m (a n) = π m y := fun {m n} h => by
      rw [← hqt h (a n), ha n, hπt h y]
    have hdiff : ∀ {m n : ℕ}, m ≤ n → q m (a m - a n) = 0 := fun {m n} h => by
      rw [map_sub, ha m, hqa h, sub_self]
    have hcauchy : ∀ {m n : ℕ}, m ≤ n →
        (fun j => a (j + k₁)) m ≡ (fun j => a (j + k₁)) n [SMOD (Jd ^ m • ⊤ : Submodule R M)] :=
      fun {m n} h => by
        rw [SModEq.sub_mem]
        exact hker m _ (hdiff (Nat.add_le_add_right h k₁))
    obtain ⟨x, hx⟩ := IsPrecomplete.prec (I := Jd) inferInstance hcauchy
    refine ⟨x, hsep (cm x) y fun n => ?_⟩
    rw [hq n x]
    have h1 : a (n + 1 + k₁) - x ∈ Jd ^ (n + 1) • (⊤ : Submodule R M) := by
      have h := hx (n + 1)
      rwa [SModEq.sub_mem] at h
    have h2 : q n (a (n + 1 + k₁)) - q n x = 0 := by
      rw [← map_sub]
      exact LinearMap.mem_ker.mp (hkill n h1)
    exact (sub_eq_zero.mp h2).symm.trans (hqa (by omega))

/-! ### Base scalars and the ideal-power subsheaves -/

section BaseScalar

open Stacks.Cohomology.FormalFunctions

attribute [local instance] sectionsModuleΓ sectionsModuleΓSheaf sectionsSMulCommClassΓ

variable (A : Type u) [CommRing A] (J : Ideal A) {X : Scheme.{u}} (f : X ⟶ Spec (.of A))

/-- **The `A`-algebra structure on the global functions of a scheme over `A`.** It is through
this algebra map that the cohomology modules of `X` are `A`-modules. -/
public abbrev baseAlgebra : Algebra A Γ(X, ⊤) :=
  Stacks.Cohomology.AffineBase.baseSectionsAlgebra A (Over.mk f)

/-- Restriction carries the base scalar at an open to the base scalar at a smaller one. -/
public theorem baseRingToSections_restrict {U V : (Opens X)ᵒᵖ} (i : U ⟶ V) (a : A) :
    (X.ringCatSheaf.obj.map i).hom
        (AlgebraicGeometry.baseRingToSections A (Over.mk f) U a) =
      AlgebraicGeometry.baseRingToSections A (Over.mk f) V a :=
  (congrArg (fun g => RingCat.Hom.hom g
      (((Scheme.ΓSpecIso (.of A)).inv ≫ (Over.mk f).hom.appTop).hom a))
    (X.ringCatSheaf.obj.map_comp U.unop.leTop.op i)).symm

/-- A base scalar coming from `J ^ k` lies in the `k`-th power of the ideal sheaf `J · 𝒪_X` on
every affine open. -/
public theorem baseRingToSections_mem_ideal_pow {k : ℕ} {a : A} (ha : a ∈ J ^ k)
    (V : X.affineOpens) :
    AlgebraicGeometry.baseRingToSections A (Over.mk f) (op V.1) a ∈
      (baseIdealSheaf A J f).ideal V ^ k := by
  have hmem : ((Scheme.ΓSpecIso (.of A)).inv ≫ f.appTop).hom a ∈ baseIdeal A J f ^ k := by
    rw [baseIdeal, ← Ideal.map_pow]
    exact Ideal.mem_map_of_mem _ ha
  rw [baseIdealSheaf_ideal, ← Ideal.map_pow]
  exact Ideal.mem_map_of_mem _ hmem

/-- **A base scalar from `J ^ k` carries every section of `M` into the subsheaf
`(J · 𝒪_X) ^ k M`.** Membership is affine-local, and on an affine open the scalar is a section of
the `k`-th power of the ideal sheaf. -/
public theorem baseScalar_mem_idealPowerMultiple (M : X.Modules) (k : ℕ) {a : A}
    (ha : a ∈ J ^ k) (U : X.Opens) (x : M.val.obj (op U)) :
    AlgebraicGeometry.baseRingToSections A (Over.mk f) (op U) a • x ∈
      (idealPowerMultiple (baseIdealSheaf A J f) k M).toSubmodule.obj (op U) := by
  refine mem_submodule_of_affine _ U _ fun V i => ?_
  rw [M.val.map_smul i.op, baseRingToSections_restrict A f i.op a]
  exact (idealPowerMultiple_le_iff (baseIdealSheaf A J f) k M _).1 le_rfl V
    (Submodule.smul_mem_smul (baseRingToSections_mem_ideal_pow A J f ha V) Submodule.mem_top)

/-- **A base scalar from `J ^ k` annihilates a sheaf of modules killed by `(J · 𝒪_X) ^ k`.**
Multiplication by the scalar lands in the subsheaf `(J · 𝒪_X) ^ k M`, which is zero. -/
public theorem baseSmul_eq_zero_of_idealPowerMultiple_eq_bot (M : X.Modules) (k : ℕ) {a : A}
    (ha : a ∈ J ^ k) (hM : idealPowerMultiple (baseIdealSheaf A J f) k M = ⊥) :
    letI : Linear A X.Modules := AlgebraicGeometry.modulesLinear A (Over.mk f)
    a • 𝟙 M = 0 := by
  let _ : Linear A X.Modules := AlgebraicGeometry.modulesLinear A (Over.mk f)
  refine SheafOfModules.hom_ext (PresheafOfModules.hom_ext fun U => ModuleCat.hom_ext ?_)
  ext x
  have h := baseScalar_mem_idealPowerMultiple A J f M k ha U.unop x
  rw [hM] at h
  have hx : AlgebraicGeometry.baseRingToSections A (Over.mk f) (op U.unop) a • x = 0 :=
    (Submodule.mem_bot _).mp ((SheafOfModules.Submodule.bot_obj M (op U.unop)).le h)
  exact hx

/-! ### The theorem on formal functions over a complete Noetherian base -/

section Complete

open scoped ModuleCat.Algebra

/-- The comparison of [Stacks, Tag 087U], from the two uniform bounds of [Stacks, Tag 02OB] and
the finiteness of [Stacks, Tag 02O6], taken as hypotheses. The unconditional
[Stacks, Tag 087U] for a proper morphism, with these three discharged, is
`Stacks.Algebraization.isIso_cohomologyToLimit_of_isProper_of_isAdicComplete`, which carries
the tag.

Let `A` be a Noetherian ring complete with respect to an ideal `J`, let `X` be a locally
Noetherian scheme over `A` and let `F` be a coherent sheaf on `X`. Then for every `p ≥ 0` the
canonical map

  `Hᵖ(X, F) ⟶ limₙ Hᵖ(X, F / Jⁿ F)`

is an isomorphism, provided

* `hfin`: `Hᵖ(X, F)` is a finite `A`-module — this is [Stacks, Tag 02O6], the finiteness of
  the cohomology of a coherent sheaf along a proper morphism
  (for a proper `f`, `Stacks.Algebraization.moduleFinite_cohomologyOverBase` transferred along
  `Stacks.Cohomology.FormalFunctions.cohomologyBaseEquiv`);
* `hker`: there is a `c` with `ker (Hᵖ(X, F) ⟶ Hᵖ(X, F / Jⁿ⁺ᶜ F)) ⊆ Jⁿ Hᵖ(X, F)` for all `n`;
* `hstab`: there is a `c` such that the image of `Hᵖ(X, F) ⟶ Hᵖ(X, F / Jⁿ F)` contains the image
  of `Hᵖ(X, F / Jⁿ⁺ᶜ F) ⟶ Hᵖ(X, F / Jⁿ F)` for all `n`.

The last two are the uniform Artin-Rees bounds of [Stacks, Tag 02OB], read through the long
exact cohomology sequences of `0 → Jⁿ F → F → F / Jⁿ F → 0`; they are the two places where
properness of the structure morphism enters the source's argument, and for a proper `f` they
follow from
`Stacks.Cohomology.FormalFunctions.exists_uniform_bound_cohomology_idealPowerQuotient_of_02O8`.

What is proved here is everything else: the completion step of the source's proof — that no
completion is needed on the left because a finite module over a complete Noetherian ring is
itself complete — together with the derivation of the comparison from the two bounds. -/
public theorem isIso_cohomologyToLimit (A : Type u) [CommRing A] [IsNoetherianRing A]
    (J : Ideal A) [IsAdicComplete J A] {X : Scheme.{u}} [IsLocallyNoetherian X]
    (f : X ⟶ Spec (.of A))
    (F : AlgebraicGeometry.SheafOfModules.CoherentModules X.ringCatSheaf) (p : ℕ)
    (hfin : letI := baseAlgebra A f
      Module.Finite A
        ↥(((Stacks.Cohomology.AffineBase.moduleGlobalSections X).rightDerived p).obj F.obj))
    (hker : letI := baseAlgebra A f
      ∃ c : ℕ, ∀ (n : ℕ) (x : ↥(((Stacks.Cohomology.AffineBase.moduleGlobalSections
          X).rightDerived p).obj F.obj)),
        (((Stacks.Cohomology.AffineBase.moduleGlobalSections X).rightDerived p).map
            (completionProjection X
              (Stacks.Cohomology.FormalFunctions.baseIdealSheaf A J f) F (n + c))).hom x = 0 →
          x ∈ J ^ n • (⊤ : Submodule A ↥(((Stacks.Cohomology.AffineBase.moduleGlobalSections
            X).rightDerived p).obj F.obj)))
    (hstab : ∃ c : ℕ, ∀ (n : ℕ)
        (y : ↥((completionCohomologySystem
          (Stacks.Cohomology.FormalFunctions.baseIdealSheaf A J f) F p).obj (op (n + c)))),
        ∃ x : ↥(((Stacks.Cohomology.AffineBase.moduleGlobalSections X).rightDerived p).obj F.obj),
          (((Stacks.Cohomology.AffineBase.moduleGlobalSections X).rightDerived p).map
              (completionProjection X
                (Stacks.Cohomology.FormalFunctions.baseIdealSheaf A J f) F n)).hom x =
            ((completionCohomologySystem
                (Stacks.Cohomology.FormalFunctions.baseIdealSheaf A J f) F p).map
              (homOfLE (Nat.le_add_right n c)).op).hom y) :
    IsIso (cohomologyToLimit
      (Stacks.Cohomology.FormalFunctions.baseIdealSheaf A J f) F p) := by
  let _ := baseAlgebra A f
  let _ : Linear A X.Modules := AlgebraicGeometry.modulesLinear A (Over.mk f)
  have hlin : Functor.Linear A
      ((Stacks.Cohomology.AffineBase.moduleGlobalSections X).rightDerived p) :=
    Stacks.Cohomology.AffineBase.linear_rightDerived_moduleGlobalSections A (Over.mk f) p
  have hfin' : Module.Finite A
      ↥(((Stacks.Cohomology.AffineBase.moduleGlobalSections X).rightDerived p).obj F.obj) := hfin
  have hcompl : IsAdicComplete J
      ↥(((Stacks.Cohomology.AffineBase.moduleGlobalSections X).rightDerived p).obj F.obj) :=
    isAdicComplete_of_iInf_smul_eq_bot J
      (Ideal.iInf_pow_smul_eq_bot_of_le_jacobson J (IsAdicComplete.le_jacobson_bot J))
  obtain ⟨c₁, hc₁⟩ := hker
  obtain ⟨c₂, hc₂⟩ := hstab
  rw [ConcreteCategory.isIso_iff_bijective]
  refine bijective_of_kernelBound_of_stableImage (Jd := J)
    (LinearMap.restrictScalars A
      (cohomologyToLimit (Stacks.Cohomology.FormalFunctions.baseIdealSheaf A J f) F p).hom)
    (fun n => LinearMap.restrictScalars A
      (limit.π (completionCohomologySystem
        (Stacks.Cohomology.FormalFunctions.baseIdealSheaf A J f) F p) (op n)).hom)
    (fun n => LinearMap.restrictScalars A
      (((Stacks.Cohomology.AffineBase.moduleGlobalSections X).rightDerived p).map
        (completionProjection X
          (Stacks.Cohomology.FormalFunctions.baseIdealSheaf A J f) F n)).hom)
    (fun {m n} h => LinearMap.restrictScalars A
      ((completionCohomologySystem
        (Stacks.Cohomology.FormalFunctions.baseIdealSheaf A J f) F p).map (homOfLE h).op).hom)
    (fun n x => ConcreteCategory.congr_hom
      (cohomologyToLimit_π (Stacks.Cohomology.FormalFunctions.baseIdealSheaf A J f) F p (op n)) x)
    (fun {m n} h x => ?_) (fun {m n} h y => ConcreteCategory.congr_hom
      (limit.w (completionCohomologySystem
        (Stacks.Cohomology.FormalFunctions.baseIdealSheaf A J f) F p) (homOfLE h).op) y)
    (fun y z hyz => Concrete.limit_ext _ y z fun n => hyz n.unop) (fun n => ?_) c₁ c₂ hc₁ hc₂
  · exact ConcreteCategory.congr_hom
      ((((Stacks.Cohomology.AffineBase.moduleGlobalSections X).rightDerived p).map_comp
          (completionProjection X
            (Stacks.Cohomology.FormalFunctions.baseIdealSheaf A J f) F n)
          (((completionFunctor X
            (Stacks.Cohomology.FormalFunctions.baseIdealSheaf A J f)).obj F).obj.map
              (homOfLE h).op)).symm.trans
        (congrArg (fun k => ((Stacks.Cohomology.AffineBase.moduleGlobalSections
              X).rightDerived p).map k)
          (completionProjection_naturality_le X
            (Stacks.Cohomology.FormalFunctions.baseIdealSheaf A J f) F h))) x
  · refine Submodule.smul_le.mpr fun a ha x _ => ?_
    rw [LinearMap.mem_ker, map_smul]
    have hz : a • 𝟙 (((completionFunctor X
        (Stacks.Cohomology.FormalFunctions.baseIdealSheaf A J f)).obj F).obj.obj (op n)) = 0 :=
      baseSmul_eq_zero_of_idealPowerMultiple_eq_bot A J f _ (n + 1) ha
        (((completionFunctor X
          (Stacks.Cohomology.FormalFunctions.baseIdealSheaf A J f)).obj F).property.2.1 n)
    have h1 := (Functor.linear_iff A
      ((Stacks.Cohomology.AffineBase.moduleGlobalSections X).rightDerived p)).mp hlin
      (((completionFunctor X
        (Stacks.Cohomology.FormalFunctions.baseIdealSheaf A J f)).obj F).obj.obj (op n)) a
    rw [hz, Functor.map_zero] at h1
    have h4 := congrArg (fun k => ModuleCat.Hom.hom k
      ((LinearMap.restrictScalars A
        (((Stacks.Cohomology.AffineBase.moduleGlobalSections X).rightDerived p).map
          (completionProjection X
            (Stacks.Cohomology.FormalFunctions.baseIdealSheaf A J f) F n)).hom) x)) h1.symm
    simpa using h4

/-- The comparison of [Stacks, Tag 087U] for a proper morphism, from the two uniform bounds of
[Stacks, Tag 02OB] and the finiteness of [Stacks, Tag 02O6], taken as hypotheses. The
unconditional [Stacks, Tag 087U], with these three discharged, is
`Stacks.Algebraization.isIso_cohomologyToLimit_of_isProper_of_isAdicComplete`, which carries
the tag.

This is `Stacks.Algebraization.isIso_cohomologyToLimit` with the hypothesis
`IsLocallyNoetherian X` replaced by properness of `f`, which implies it over a Noetherian base.
The statement is then the source's verbatim: `A` Noetherian and `J`-adically complete,
`f : X ⟶ Spec A` proper, `F` coherent, and the conclusion for every `p ≥ 0`.

The three hypotheses are the ones the source cites and the only places properness is used there.
See
`Stacks.Algebraization.isIso_cohomologyToLimit` for what each of them says. -/
public theorem isIso_cohomologyToLimit_of_isProper (A : Type u) [CommRing A] [IsNoetherianRing A]
    (J : Ideal A) [IsAdicComplete J A] {X : Scheme.{u}} (f : X ⟶ Spec (.of A)) [IsProper f]
    (F : AlgebraicGeometry.SheafOfModules.CoherentModules X.ringCatSheaf) (p : ℕ)
    (hfin : letI : IsLocallyNoetherian X := LocallyOfFiniteType.isLocallyNoetherian f
      letI := baseAlgebra A f
      Module.Finite A
        ↥(((Stacks.Cohomology.AffineBase.moduleGlobalSections X).rightDerived p).obj F.obj))
    (hker : letI : IsLocallyNoetherian X := LocallyOfFiniteType.isLocallyNoetherian f
      letI := baseAlgebra A f
      ∃ c : ℕ, ∀ (n : ℕ) (x : ↥(((Stacks.Cohomology.AffineBase.moduleGlobalSections
          X).rightDerived p).obj F.obj)),
        (((Stacks.Cohomology.AffineBase.moduleGlobalSections X).rightDerived p).map
            (completionProjection X
              (Stacks.Cohomology.FormalFunctions.baseIdealSheaf A J f) F (n + c))).hom x = 0 →
          x ∈ J ^ n • (⊤ : Submodule A ↥(((Stacks.Cohomology.AffineBase.moduleGlobalSections
            X).rightDerived p).obj F.obj)))
    (hstab : letI : IsLocallyNoetherian X := LocallyOfFiniteType.isLocallyNoetherian f
      ∃ c : ℕ, ∀ (n : ℕ)
        (y : ↥((completionCohomologySystem
          (Stacks.Cohomology.FormalFunctions.baseIdealSheaf A J f) F p).obj (op (n + c)))),
        ∃ x : ↥(((Stacks.Cohomology.AffineBase.moduleGlobalSections X).rightDerived p).obj F.obj),
          (((Stacks.Cohomology.AffineBase.moduleGlobalSections X).rightDerived p).map
              (completionProjection X
                (Stacks.Cohomology.FormalFunctions.baseIdealSheaf A J f) F n)).hom x =
            ((completionCohomologySystem
                (Stacks.Cohomology.FormalFunctions.baseIdealSheaf A J f) F p).map
              (homOfLE (Nat.le_add_right n c)).op).hom y) :
    letI : IsLocallyNoetherian X := LocallyOfFiniteType.isLocallyNoetherian f
    IsIso (cohomologyToLimit
      (Stacks.Cohomology.FormalFunctions.baseIdealSheaf A J f) F p) := by
  let _ : IsLocallyNoetherian X := LocallyOfFiniteType.isLocallyNoetherian f
  exact isIso_cohomologyToLimit A J f F p hfin hker hstab

end Complete

end BaseScalar

end Stacks.Algebraization

end
