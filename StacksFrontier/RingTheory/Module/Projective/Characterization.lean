module

public import StacksCore.Tactic.StacksAttribute
public import Mathlib.Algebra.Order.Floor.Extended
public import Mathlib.Algebra.Order.Interval.Basic
public import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
public import Mathlib.Analysis.SpecialFunctions.Bernstein
public import Mathlib.Analysis.SpecialFunctions.Gamma.Basic
public import Mathlib.Analysis.SpecialFunctions.Trigonometric.DerivHyp
public import Mathlib.Combinatorics.Enumerative.DyckWord
public import Mathlib.Combinatorics.SimpleGraph.Triangle.Removal
public import Mathlib.Data.NNRat.Floor
public import Mathlib.Data.Nat.Choose.Multinomial
public import Mathlib.Geometry.Euclidean.Altitude
public import Mathlib.NumberTheory.Chebyshev
public import Mathlib.NumberTheory.Height.NumberField
public import Mathlib.NumberTheory.Height.Projectivization
public import Mathlib.NumberTheory.LucasLehmer
public import Mathlib.NumberTheory.SelbergSieve
public import Mathlib.RingTheory.Coalgebra.CoassocSimps
public import Mathlib.RingTheory.Radical.NatInt
public import Mathlib.Tactic.Echelon.Zsqrtd
public import Mathlib.Tactic.NormNum.Irrational
public import Mathlib.Tactic.NormNum.IsCoprime
public import Mathlib.Tactic.NormNum.IsSquare
public import Mathlib.Tactic.NormNum.LegendreSymbol
public import Mathlib.Tactic.NormNum.ModEq
public import Mathlib.Tactic.NormNum.NatFib
public import Mathlib.Tactic.NormNum.NatLog
public import Mathlib.Tactic.NormNum.NatSqrt
public import Mathlib.Tactic.NormNum.Ordinal
public import Mathlib.Tactic.NormNum.Parity
public import Mathlib.Tactic.NormNum.Prime
public import Mathlib.Tactic.NormNum.RealSqrt
public import Mathlib.Topology.Sheaves.Init
public import Mathlib.Algebra.Category.ModuleCat.Ext.HasExt
public import Mathlib.Algebra.Lie.OfAssociative
public import Mathlib.Algebra.Module.StablyFree.Basic
public import Mathlib.CategoryTheory.Abelian.Projective.Dimension

/-!
# Characterizations of projective modules

Let `R` be a ring and let `P` be an `R`-module. The following three conditions are equivalent
(Stacks tag 05CF, Lemma 10.77.2):

1. `P` is projective in the sense of the universal lifting property: for every surjective
   `R`-linear map `f : M ↠ N` and every `R`-linear map `g : P → N` there exists an `R`-linear
   map `h : P → M` with `f ∘ h = g`.
2. `P` is a direct summand of a free `R`-module: there exists a free `R`-module `F` together
   with `R`-linear maps `s : P → F` and `π : F → P` such that `π ∘ s = id_P`, i.e. `P` is a
   retract of a free module.
3. `Ext^1_R(P, M) = 0` for every `R`-module `M`.

## Conventions

The Stacks Project develops commutative algebra, but the equivalence is valid for any
(possibly noncommutative) ring `R` with left `R`-modules, so `R` is taken to be an arbitrary
`Ring`.

"Free" means isomorphic to a direct sum `⨁_{i ∈ I} R` of copies of `R` indexed by an
arbitrary (possibly infinite) set `I`; no finiteness hypothesis is imposed. This is
`Module.Free R F`.

The functor `Ext^1_R(P, -)` is taken in the category `ModuleCat R` of `R`-modules, which is
abelian with enough projectives and hence has `Ext` groups; `Ext^1_R(P, M)` is
`Abelian.Ext (ModuleCat.of R P) (ModuleCat.of R M) 1`. Since that is an additive group, the
vanishing `Ext^1 = 0` is expressed as the group being a `Subsingleton`.

The universal lifting property (condition 1) is taken as the definition of "projective". It
coincides with Mathlib's `Module.Projective`, as recorded by
`isProjectiveLifting_iff_projective`.

## Outline of the argument

* (1) ⇒ (2): pick a free `F ↠ P` and lift `id_P` to get a section.
* (2) ⇒ (3): `Ext^1(F, M) = 0` for free `F`, and `Ext^1(-, M)` is additive on direct sums, so
  `Ext^1(P, M)` is a summand of `0`.
* (3) ⇒ (1): the long exact `Ext` sequence shows any surjection can be lifted.

## Direct sums

That a direct sum of projective modules is projective (Stacks tag 065Q, Lemma 10.77.3) is
Mathlib's instance `Module.Projective R (Π₀ i, A i)`, so it is recorded here by an
`add_to_stacks` line rather than reproved.
-/

@[expose] public section

universe u

variable (R : Type u) [Ring R]

/-- Condition 1: `P` is *projective* via the universal lifting property. For
every surjective `R`-linear map `f : M → N` and every `R`-linear map
`g : P → N`, there exists an `R`-linear map `h : P → M` with `f ∘ h = g`; here `M` and `N`
range over `R`-modules in the universe of `P`. -/
def IsProjectiveLifting (P : Type u) [AddCommGroup P] [Module R P] : Prop :=
  ∀ {M N : Type u} [AddCommGroup M] [AddCommGroup N] [Module R M] [Module R N]
    (f : M →ₗ[R] N) (g : P →ₗ[R] N), Function.Surjective f →
      ∃ h : P →ₗ[R] M, f ∘ₗ h = g

/-- Condition 2: `P` is a *direct summand of a free `R`-module*. There exists a
free `R`-module `F` together with `R`-linear maps `s : P → F` (section) and
`π : F → P` (retraction) such that `π ∘ s = id_P`. -/
def IsDirectSummandOfFree (P : Type u) [AddCommGroup P] [Module R P] : Prop :=
  ∃ (F : Type u) (_ : AddCommGroup F) (_ : Module R F) (_ : Module.Free R F)
    (s : P →ₗ[R] F) (π : F →ₗ[R] P), π ∘ₗ s = LinearMap.id

open CategoryTheory in
/-- Condition 3: `Ext^1_R(P, M) = 0` for every `R`-module `M`, expressed via the
abelian-category `Ext` groups of `ModuleCat R`. Vanishing of the `Ext` group is
phrased as it being a `Subsingleton`. -/
def ExtOneVanishes (P : Type u) [AddCommGroup P] [Module R P] : Prop :=
  ∀ (M : Type u) [AddCommGroup M] [Module R M],
    Subsingleton (Abelian.Ext (ModuleCat.of R P) (ModuleCat.of R M) 1)

/-- The lifting-property formulation of projectivity (condition 1) coincides with Mathlib's
`Module.Projective`. -/
@[ega "0 19.5.6.4" "partial", sga "5 XV 3.Lemma3" "more general", sga "6 I 1.3" "more general"]
theorem isProjectiveLifting_iff_projective (P : Type u) [AddCommGroup P] [Module R P] :
    IsProjectiveLifting R P ↔ Module.Projective R P :=
  ⟨Module.Projective.of_lifting_property, fun _ _ _ _ _ _ _ f g hf ↦
    Module.projective_lifting_property f g hf⟩

/-- Theorem (Stacks Tag 05CF). For an `R`-module `P`, the three conditions
"`P` is projective (lifting property)", "`P` is a direct summand of a free
module", and "`Ext^1_R(P, M) = 0` for all `M`" are equivalent. -/
@[stacks 05CF, ega "0 17.2.1" "n = 0", sga "5 XV 3.Lemma3" "more general"]
theorem characterize_projective (P : Type u) [AddCommGroup P] [Module R P] :
    List.TFAE
      [IsProjectiveLifting R P, IsDirectSummandOfFree R P, ExtOneVanishes R P] := by
  tfae_have 1 → 2 := by
    intro h
    obtain ⟨s, hs⟩ := Module.projective_def'.mp ((isProjectiveLifting_iff_projective R P).mp h)
    exact ⟨P →₀ R, inferInstance, inferInstance, inferInstance, s,
      Finsupp.linearCombination R id, hs⟩
  tfae_have 2 → 3 := by
    rintro ⟨F, _, _, _, s, π, hsplit⟩ M _ _
    have := (IsProjective.iff_projective P).mp (Module.Projective.of_split s π hsplit)
    refine ⟨fun e e' => ?_⟩
    rw [CategoryTheory.Abelian.Ext.eq_zero_of_projective e,
      CategoryTheory.Abelian.Ext.eq_zero_of_projective e']
  tfae_have 3 → 1 := fun h ↦ (isProjectiveLifting_iff_projective R P).mpr <|
    (IsProjective.iff_projective P).mpr <|
      CategoryTheory.projective_iff_subsingleton_ext_one.mpr fun Y ↦ h Y
  tfae_finish

-- The former @[stacks 065Q] declaration is now the Mathlib instance.
add_to_stacks 065Q "a direct sum of projective modules is projective" Module.instProjectiveDFinsupp

