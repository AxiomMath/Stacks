module

public import StacksFrontier.AlgebraicGeometry.Algebraization.CompletedStalk
public import StacksFrontier.AlgebraicGeometry.FormalGeometry.ComparisonShortExact
public import StacksFrontier.AlgebraicGeometry.FormalGeometry.CompletionCriteria.MittagLefflerCriterion
public import StacksFrontier.RingTheory.LocalCohomology.HigherDegree.CohomologyOverBase
public import Mathlib.RingTheory.Regular.RegularSequence

/-!
# Algebraization under a regular-sequence hypothesis: the finiteness half

Fix an algebraization situation: a Noetherian ring `A` with ideals `I ⊆ 𝔞`, the affine scheme
`X = Spec(A)` and the open complement `U = X \ V(𝔞)`. Let `(F_n)` be a coherent `I`-adic system
on `U`. Stacks 0EJS proves that such a system extends canonically to `X` once `I` is generated
by a sequence that is regular on the completed stalks `F_y^∧` and `H⁰(U, F_1)`, `H¹(U, F_1)` are
finite `A`-modules; the proof verifies the three hypotheses (a), (b), (c) of the Mittag-Leffler
criterion Stacks 0EHH.

This file formalizes the part of that verification concerning condition (c), namely finiteness.
The source's short exact sequences

  `0 → I^(n+1) F_(n+1) → F_(n+1) → F_n → 0`

are produced here from the defining data of a coherent adic system, and taking sections on `U`
turns them into the inductive step that makes every `H⁰(U, F_n)` a finite `A`-module; condition
(c) of Stacks 0EHH, and hence canonical extension, follows from that.

## Main definitions

* `Stacks.Algebraization.idealPowerSub` — the subsheaf `I^(n+1) F_(n+1)`, the kernel of the
  transition map of the system.
* `Stacks.Algebraization.idealPowerShortComplex` — the sequence
  `0 → I^(n+1) F_(n+1) → F_(n+1) → F_(n+1)/I^(n+1) F_(n+1) → 0`.
* `Stacks.Algebraization.openSectionsFunctor` — global sections on `U`, as `A`-modules.
* `Stacks.Algebraization.idealPowerSections` — the `A`-module `H⁰(U, I^(n+1) F_(n+1))`.
* `Stacks.Algebraization.germOfBase` — the germ at a point of `U` of the function determined by
  an element of `A`.
* `Stacks.Algebraization.HasRegularSequenceOnCompletedStalks` — hypothesis (1) of Stacks 0EJS.
* `Stacks.Algebraization.HasFiniteLowDegreeCohomology` — hypothesis (2) of Stacks 0EJS.

## Main results

* `Stacks.Algebraization.idealPowerShortComplex_shortExact` — the sequence is short exact.
* `Stacks.Algebraization.ker_globalSectionsSystem_map_le_range` — a global section of `F_(n+1)`
  dying in `F_n` comes from `I^(n+1) F_(n+1)`.
* `Stacks.Algebraization.finite_globalSections_of_finite_idealPowerSections` — the source's
  induction: if `H⁰(U, F_1)` and every `H⁰(U, I^(n+1) F_(n+1))` are finite `A`-modules, then
  every `H⁰(U, F_n)` is a finite `A`-module.
* `Stacks.Algebraization.canonicallyExtends_of_finite_globalSections` — condition (c) of Stacks
  0EHH is implied by finiteness of all `H⁰(U, F_n)`, so the Mittag-Leffler and topology
  conditions alone then give canonical extension.
* `Stacks.Algebraization.canonicallyExtends_of_finite_idealPowerSections` — the two previous
  results combined.

## Implementation notes

The system is indexed by `ℕᵒᵖ` and is zero-indexed: term `n` is the source's `F_(n+1)`. So the
source's sequence `0 → IⁿF_(n+1) → F_(n+1) → F_n → 0` appears here as
`0 → I^(n+1)F_(n+1) → F_(n+1) → F_n → 0` between the terms at `n + 1` and `n`, which is the shape
the third clause of `Stacks.Coherent.IsCoherentAdicSystem` provides: the transition map is the
projection out of the quotient by `Stacks.Algebraization.idealPowerMultiple`. The isomorphism
identifying that quotient with the term at `n` is existentially quantified in that clause, so
`idealPowerShortComplex` uses the canonical cokernel and the isomorphism enters only inside
proofs.

Left exactness of sections is `Stacks.Algebraization.exists_app_eq_of_shortExact`, which holds
because evaluation of a sheaf of modules at an open preserves finite limits. The inductive step
then uses `Submodule.fg_of_fg_map_of_fg_inf_ker`: the image of `H⁰(U, F_(n+1))` in `H⁰(U, F_n)`
is finitely generated because `A` is Noetherian, and the kernel is finitely generated because it
sits inside the image of the finite module `H⁰(U, I^(n+1) F_(n+1))`.

What this file does **not** do is the rest of the proof of Stacks 0EJS, and the results below
carry qualifiers on their tags saying so. The source obtains finiteness of
`H⁰(U, I^(n+1)F_(n+1))` from the stalkwise direct-sum decomposition
`IⁿF_(n+1) = ⨁_{e₁ + ⋯ + e_d = n} F_1 · f₁^{e₁} ⋯ f_d^{e_d}`, which rests on quasi-regularity of
`f₁, …, f_d` on the completed stalks together with the identification of
`Stacks.Algebraization.completedStalk` with `F_y^∧` (Stacks 0EJE, not proved in this library).
Conditions (a) and (b) of Stacks 0EHH come in the source from Cohomology 0GYK and 0GYM, and they
are hypotheses below. The reason is not that those tags are unavailable in a usable category:
besides the models over `Stacks.Cohomology.QuotientTowers.ModuleSheaf` (sheaves of modules over
a fixed ring on a topological space) and over `SheafOfModules` on a site
(`Stacks.Cohomology.AdicInverseSystems`, Tags 0GYQ–0GYT, which does cover `𝒪_U`-modules), the
general-ideal Mittag-Leffler argument is available category-agnostically as
`Stacks.Cohomology.IdealBoundaries.isMittagLefflerCategorical_of_idealBoundaries`. What is
missing is its last hypothesis: that beyond some degree every boundary class is a sum of
boundary classes one step down pushed along the generators of `I`. That is finite generation of
`⨁ₙ H¹(U, IⁿF_(n+1))` as a graded `gr_I(A)`-module, which the source gets from the direct-sum
decomposition, and it is the only use the source makes of the degree-one half of its
hypothesis (2) below. The source's own hypotheses (1) and (2) are recorded as the
predicates `Stacks.Algebraization.HasRegularSequenceOnCompletedStalks` and
`Stacks.Algebraization.HasFiniteLowDegreeCohomology`; they are statements only, consumed by no
result here.

## References

* [Stacks Project, Tag 0EJS](https://stacks.math.columbia.edu/tag/0EJS)
* [Stacks Project, Tag 0EHH](https://stacks.math.columbia.edu/tag/0EHH)
* [Stacks Project, Tag 0EHC](https://stacks.math.columbia.edu/tag/0EHC)
-/

@[expose] public noncomputable section

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits Opposite
open scoped AlgebraicGeometry

universe u

namespace Stacks.Algebraization

attribute [local instance] AlgebraicGeometry.Scheme.Modules.submoduleCompleteLattice

variable (S : AlgebraizationSituation.{u})
  (F : Stacks.Coherent.CoherentAdicSystems (idealOnOpen S))

/-- The subsheaf `I^(n+1) F_(n+1)` of the term of index `n + 1` of a coherent adic system on the
open complement. It is the kernel of the transition map to the term of index `n`. -/
abbrev idealPowerSub (n : ℕ) :=
  idealPowerMultiple (idealOnOpen S) (n + 1) (F.obj.obj (op (n + 1)))

/-- The sequence `0 → I^(n+1) F_(n+1) → F_(n+1) → F_(n+1)/I^(n+1) F_(n+1) → 0`. Its third term
is identified with `F_n` by the defining data of a coherent adic system. -/
abbrev idealPowerShortComplex (n : ℕ) :=
  ShortComplex.mk (idealPowerSub S F n).ι (cokernel.π (idealPowerSub S F n).ι)
    (cokernel.condition _)

/-- **Stacks Project, Tag 0EJS (the short exact sequence of the proof).** The sequence
`0 → I^(n+1) F_(n+1) → F_(n+1) → F_(n+1)/I^(n+1) F_(n+1) → 0` is short exact. -/
theorem idealPowerShortComplex_shortExact (n : ℕ) :
    (idealPowerShortComplex S F n).ShortExact where
  exact := ShortComplex.exact_cokernel _
  mono_f := inferInstance
  epi_g := inferInstance

/-- Global sections on the open complement `U`, as a functor to `A`-modules. -/
abbrev openSectionsFunctor : S.U.toScheme.Modules ⥤ ModuleCat.{u} S.A :=
  _root_.SheafOfModules.evaluation S.U.toScheme.ringCatSheaf
      (op (⊤ : S.U.toScheme.Opens)) ⋙
    ModuleCat.restrictScalars (scalarMap S)

/-- The `A`-module `H⁰(U, I^(n+1) F_(n+1))` of global sections of the kernel of the transition
map. -/
abbrev idealPowerSections (n : ℕ) : ModuleCat.{u} S.A :=
  (openSectionsFunctor S).obj (idealPowerSub S F n).toSheafOfModules

/-- The inclusion `H⁰(U, I^(n+1) F_(n+1)) ⟶ H⁰(U, F_(n+1))` of `A`-modules. -/
abbrev idealPowerSectionsι (n : ℕ) :
    idealPowerSections S F n ⟶ (globalSectionsSystem S F).obj (op (n + 1)) :=
  (openSectionsFunctor S).map (idealPowerSub S F n).ι

/-- **Stacks Project, Tag 0EJS (left exactness of sections).** A global section of `F_(n+1)`
that dies in `F_n` is a section of `I^(n+1) F_(n+1)`. -/
theorem ker_globalSectionsSystem_map_le_range (n : ℕ) :
    LinearMap.ker ((globalSectionsSystem S F).map (homOfLE (Nat.le_succ n)).op).hom ≤
      LinearMap.range (idealPowerSectionsι S F n).hom := by
  obtain ⟨e, he⟩ := F.property.2.2 n
  intro y hy
  have hy0 : Scheme.Modules.Hom.app (F.obj.map (homOfLE (Nat.le_succ n)).op)
      (⊤ : S.U.toScheme.Opens) y = 0 := hy
  have hci : cokernel.π (idealPowerSub S F n).ι =
      F.obj.map (homOfLE (Nat.le_succ n)).op ≫ e.inv :=
    (Iso.eq_comp_inv e).mpr he
  have hsplit : Scheme.Modules.Hom.app (cokernel.π (idealPowerSub S F n).ι)
      (⊤ : S.U.toScheme.Opens) y =
      Scheme.Modules.Hom.app e.inv (⊤ : S.U.toScheme.Opens)
        (Scheme.Modules.Hom.app (F.obj.map (homOfLE (Nat.le_succ n)).op)
          (⊤ : S.U.toScheme.Opens) y) :=
    congrArg (fun φ => Scheme.Modules.Hom.app φ (⊤ : S.U.toScheme.Opens) y) hci
  have hcoker : Scheme.Modules.Hom.app (cokernel.π (idealPowerSub S F n).ι)
      (⊤ : S.U.toScheme.Opens) y = 0 := hsplit.trans (by rw [hy0]; exact map_zero _)
  obtain ⟨x, hx⟩ := exists_app_eq_of_shortExact (idealPowerShortComplex S F n)
    (idealPowerShortComplex_shortExact S F n) (⊤ : S.U.toScheme.Opens) y hcoker
  exact ⟨x, hx⟩

/-- **Stacks Project, Tag 0EJS (the induction of the proof).** If `H⁰(U, F_1)` is a finite
`A`-module and every `H⁰(U, I^(n+1) F_(n+1))` is a finite `A`-module, then `H⁰(U, F_n)` is a
finite `A`-module for every `n`.

This is the step "using the assumption of finiteness of `H⁰(U, F_1)` and induction, we first
conclude that `M_n = H⁰(U, F_n)` is a finite `A`-module for all `n`" of the source. The source
gets finiteness of `H⁰(U, I^(n+1) F_(n+1))` from the stalkwise direct-sum decomposition of
`I^(n+1) F_(n+1)` into copies of `F_1`, which is not available in this library; here it is a
hypothesis. -/
@[stacks 0EJS "the induction giving finiteness of every H⁰(U, Fₙ), with the direct-sum \
decomposition of Iⁿ F₍ₙ₊₁₎ replaced by the hypothesis that its sections are finite"]
theorem finite_globalSections_of_finite_idealPowerSections
    (h0 : Module.Finite S.A ((globalSectionsSystem S F).obj (op 0)))
    (hker : ∀ n, Module.Finite S.A (idealPowerSections S F n)) :
    ∀ n, Module.Finite S.A ((globalSectionsSystem S F).obj (op n)) := by
  intro n
  induction n with
  | zero => exact h0
  | succ n ih =>
    have hk := hker n
    have hrangefg : (LinearMap.range (idealPowerSectionsι S F n).hom).FG := by
      rw [← Submodule.map_top]
      exact (Module.finite_def.mp hk).map _
    have hrange : Module.Finite S.A (LinearMap.range (idealPowerSectionsι S F n).hom) :=
      Module.Finite.iff_fg.mpr hrangefg
    have hkerfg :
        (LinearMap.ker ((globalSectionsSystem S F).map (homOfLE (Nat.le_succ n)).op).hom).FG := by
      have hmc := Submodule.map_comap_eq_self
        (f := (LinearMap.range (idealPowerSectionsι S F n).hom).subtype)
        (q := LinearMap.ker ((globalSectionsSystem S F).map (homOfLE (Nat.le_succ n)).op).hom)
        (by rw [Submodule.range_subtype]; exact ker_globalSectionsSystem_map_le_range S F n)
      rw [← hmc]
      exact (IsNoetherian.noetherian _).map _
    refine Module.finite_def.mpr (Submodule.fg_of_fg_map_of_fg_inf_ker
      ((globalSectionsSystem S F).map (homOfLE (Nat.le_succ n)).op).hom ?_ ?_)
    · exact IsNoetherian.noetherian _
    · rwa [top_inf_eq]

/-- **Stacks Project, Tag 0EJS (condition (c) of Tag 0EHH).** Finiteness of every `H⁰(U, F_n)`
implies the finite-image condition (c) of the Mittag-Leffler criterion Stacks 0EHH, so together
with the Mittag-Leffler condition (a) and the topology condition (b) it gives canonical
extension.

The source derives (a) and (b) from Cohomology 0GYK and 0GYM applied to the graded module
`⨁_n H^p(U, IⁿF_(n+1))`; here they are hypotheses. -/
@[stacks 0EJS "the reduction to Tag 0EHH: condition (c) from finiteness of every H⁰(U, Fₙ), \
with conditions (a) and (b) as hypotheses"]
theorem canonicallyExtends_of_finite_globalSections
    (hML : IsMittagLefflerCategorical (globalSectionsSystem S F))
    (htop : (⨅ n : ℕ, TopologicalSpace.induced
      (fun x : limitGlobalSections S F =>
        (limit.π (globalSectionsSystem S F) (op n)).hom x) ⊥) =
        S.I.adicModuleTopology (limitGlobalSections S F))
    (hfin : ∀ n, Module.Finite S.A ((globalSectionsSystem S F).obj (op n))) :
    CanonicallyExtends S F := by
  refine canonicallyExtends_of_finite_limit_images S F hML htop fun n => ?_
  have := hfin n
  exact Module.Finite.iff_fg.mpr (IsNoetherian.noetherian _)

/-- **Stacks Project, Tag 0EJS (the finiteness half).** A coherent adic system on the open
complement extends canonically to `X` as soon as its system of global sections has
Mittag-Leffler, the limit topology on the module of compatible sections is the `I`-adic topology,
`H⁰(U, F_1)` is a finite `A`-module, and every `H⁰(U, I^(n+1) F_(n+1))` is a finite
`A`-module. -/
@[stacks 0EJS "the finiteness half: conditions (a), (b) of Tag 0EHH and finiteness of the \
sections of Iⁿ F₍ₙ₊₁₎ are hypotheses instead of consequences of the regular sequence"]
theorem canonicallyExtends_of_finite_idealPowerSections
    (hML : IsMittagLefflerCategorical (globalSectionsSystem S F))
    (htop : (⨅ n : ℕ, TopologicalSpace.induced
      (fun x : limitGlobalSections S F =>
        (limit.π (globalSectionsSystem S F) (op n)).hom x) ⊥) =
        S.I.adicModuleTopology (limitGlobalSections S F))
    (h0 : Module.Finite S.A ((globalSectionsSystem S F).obj (op 0)))
    (hker : ∀ n, Module.Finite S.A (idealPowerSections S F n)) :
    CanonicallyExtends S F :=
  canonicallyExtends_of_finite_globalSections S F hML htop
    (finite_globalSections_of_finite_idealPowerSections S F h0 hker)

/-! ### The hypotheses of Stacks 0EJS

The two predicates below are the source's hypotheses (1) and (2), written in this library's
vocabulary. They are statements only: no result in this file consumes them, because the
implication from them to the hypotheses of
`Stacks.Algebraization.canonicallyExtends_of_finite_idealPowerSections` is the part of the proof
of Stacks 0EJS that this library cannot yet carry out. -/

/-- The germ at a point `y` of `U` of the global function on `U` determined by an element of the
base ring `A`. This is the image of `a ∈ A` in the local ring `𝒪_{X,y}`. -/
def germOfBase (y : S.U.toScheme) (a : S.A) : S.U.toScheme.presheaf.stalk y :=
  (S.U.toScheme.presheaf.germ ⊤ y trivial).hom (scalarMap S a)

/-- **Stacks Project, Tag 0EJS, hypothesis (1).** There are `f₁, …, f_d ∈ I` such that at every
point `y` of `U ∩ Y` the ideal `I 𝒪_{X,y}` is generated by the germs of `f₁, …, f_d` and those
germs form an `F_y^∧`-regular sequence.

The locus `U ∩ Y` is the support of the ideal sheaf `I 𝒪_U`, and `F_y^∧` is
`Stacks.Algebraization.completedStalk`. The sequence is taken as a sequence of elements of the
local ring `𝒪_{X,y}` acting on `F_y^∧`, which is how the source's `f_i ∈ I ⊆ A` act. -/
@[stacks 0EJS "hypothesis (1), as a predicate; not used by any result in this file"]
def HasRegularSequenceOnCompletedStalks : Prop :=
  ∃ (d : ℕ) (f : Fin d → S.A), (∀ i, f i ∈ S.I) ∧
    ∀ y ∈ (idealOnOpen S).support,
      AlgebraicGeometry.IdealSheafData.stalk (idealOnOpen S) y =
          Ideal.span (Set.range fun i => germOfBase S y (f i)) ∧
        RingTheory.Sequence.IsRegular (completedStalk (idealOnOpen S) F y)
          (List.ofFn fun i => germOfBase S y (f i))

/-- **Stacks Project, Tag 0EJS, hypothesis (2).** `H⁰(U, F_1)` and `H¹(U, F_1)` are finite
`A`-modules.

Degree zero is the global-sections module of the system, and degree one is the first right
derived functor of sections over the base, `Stacks.LocalCohomology.cohomologyOverBase`. -/
@[stacks 0EJS "hypothesis (2), as a predicate; not used by any result in this file"]
def HasFiniteLowDegreeCohomology : Prop :=
  Module.Finite S.A ((globalSectionsSystem S F).obj (op 0)) ∧
    Module.Finite S.A
      (Stacks.LocalCohomology.cohomologyOverBase.{u, u} S.A S.U.ι (F.obj.obj (op 0)) 1)

end Stacks.Algebraization

end
