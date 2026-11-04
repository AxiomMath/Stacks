module

public import StacksCore.Tactic.StacksAttribute
public import StacksFrontier.AlgebraicGeometry.Spaces.ModuleSectionsWithSupport
public import StacksFrontier.AlgebraicGeometry.Spaces.SurjectiveRestrictionTopDegree
public import StacksFrontier.AlgebraicGeometry.Spaces.VanishingAboveTheDimension
public import StacksFrontier.AlgebraicGeometry.Spaces.VanishingAboveTheDimensionInduction

/-!
# Vanishing above the dimension on a quasi-compact quasi-separated algebraic space

Stacks 0A4R is the statement that on a quasi-compact quasi-separated algebraic space `X` of
dimension at most `d` the cohomology of a quasi-coherent module vanishes above degree `d`
(clause (1)), that the restriction map in degree `d` to a quasi-compact open subspace is onto
(clause (2)), and that the cohomology with support in a closed subspace with quasi-compact
complement vanishes above degree `d` (clause (3)).  This file states the three clauses.

The quasi-coherence hypothesis is load-bearing: the abelian-sheaf reading of clause (1) is
false.  Take `X = Spec ℝ` and `ℱ = ℤ/2` on `X_étale`.  Then `dim X = 0`, while
`H^q(X_étale, ℤ/2) = H^q(Gal(ℂ/ℝ), ℤ/2) = ℤ/2` is nonzero for every `q > 0`.

## Main results

* `AlgebraicGeometry.Space.isZero_rightDerived_globalSectionsFunctor_of_dimension_le` is
  **Stacks 0A4R, clause (1)**: for a quasi-compact quasi-separated algebraic space `X` with
  `dim X ≤ d` and a quasi-coherent `𝒪_X`-module `F`, `Hᑫ(X, F) = 0` for every `q > d`.
* `AlgebraicGeometry.Space.surjective_cohomologyRestriction_of_dimension_le` is
  **Stacks 0A4R, clause (2)**: `H^d(X, F) ⟶ H^d(U, F)` is onto for every quasi-compact open `U`.
* `AlgebraicGeometry.Space.isZero_rightDerived_globalSectionsAbRestrictionKer_of_dimension_le`
  is **Stacks 0A4R, clause (3)**: `H^q_Z(X, F) = 0` for `q > d` and every closed `Z` with
  quasi-compact complement.
* `AlgebraicGeometry.Space.isEmpty_points_of_dimension_le_bot`: a quasi-separated algebraic
  space of dimension `⊥` has no points.

## Implementation notes

The cohomology of a module on an algebraic space is the right derived functor of global
sections on the small étale site, with values in modules over the global functions; this is
the spelling of
`AlgebraicGeometry.Space.isZero_rightDerived_globalSectionsFunctor_of_isAffineSpace` and of
Stacks 0D2U.  The proof of clause (1) is not the source's: instead of the stratification of a
decent space and the excision of Stacks 0A4P it runs the induction principle of Stacks 08GP
along elementary distinguished squares, with the Mayer–Vietoris sequence of Stacks 08GW; see
`StacksFrontier/AlgebraicGeometry/Spaces/VanishingAboveTheDimensionInduction.lean`.  The inputs
are the same: the Zariski vanishing of Stacks 0A3G on quasi-compact opens of affine schemes,
and the invariance of the dimension under étale morphisms.

The dimension bound `d` lives in `WithBot ℕ∞`, where `AlgebraicGeometry.Space.dimension` takes
its values; this covers every integer `d` of the source, a negative bound forcing `X` to be
empty.  In clause (2) the bound is a natural number, `H^d` being indexed by `ℕ`.

Clauses (2) and (3) take the open subspace `U` (in clause (3), the complement of `Z`) as an
open immersion `j : U ⟶ X` from a quasi-compact algebraic space; the restriction map is
`AlgebraicGeometry.Space.cohomologyRestriction`, and `H^q_Z(X, -)` is the right derived functor
of `Γ_Z(X, -) = Ker(Γ(X, -) ⟶ Γ(U, (-)|_U))`,
`AlgebraicGeometry.Space.globalSectionsAbRestrictionKer`, both valued in abelian groups.
Clause (2) is proved along elementary distinguished squares
(`StacksFrontier/AlgebraicGeometry/Spaces/SurjectiveRestrictionTopDegree.lean`), and clause (3)
from (1) and (2) by the long exact sequence of the pair, as in the source.

## References

* [Stacks Project, Tag 04N6](https://stacks.math.columbia.edu/tag/04N6)
* [Stacks Project, Tag 08GP](https://stacks.math.columbia.edu/tag/08GP)
* [Stacks Project, Tag 08GW](https://stacks.math.columbia.edu/tag/08GW)
* [Stacks Project, Tag 0A3G](https://stacks.math.columbia.edu/tag/0A3G)
* [Stacks Project, Tag 0A4J](https://stacks.math.columbia.edu/tag/0A4J)
* [Stacks Project, Tag 0A4R](https://stacks.math.columbia.edu/tag/0A4R)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits Opposite TopologicalSpace
open scoped AlgebraicGeometry

universe u

namespace AlgebraicGeometry

namespace Space

attribute [local instance] pointTopology

/-! ### Clause (1) for a quasi-compact quasi-separated algebraic space -/

/-- An algebraic space whose dimension is `⊥` has no points: by Stacks 0A4J its dimension is
the Krull dimension of its point space, which is at least `0` on a nonempty space. -/
theorem isEmpty_points_of_dimension_le_bot (B : BigFppfSite.{u}) (S : Scheme.{u})
    (hS : B.Contains S) (X : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u) (hX : IsAlgebraicSpace B S hS X)
    (hqs : IsAbsolutelyQuasiSeparated B S hS B.contains_terminal X)
    (hdim : dimension B S hS X hX ≤ ⊥) : IsEmpty (points B S hS X) := by
  refine ⟨fun x => ?_⟩
  have hk : topologicalKrullDim (points B S hS X) ≤ ⊥ := by
    rw [topologicalKrullDim_points_eq_dimension_of_isDecentSpace B S hS hX
      (isDecentSpace_of_isAbsolutelyQuasiSeparated B S hS X hX hqs)]
    exact hdim
  have : Nonempty (TopologicalSpace.IrreducibleCloseds (points B S hS X)) :=
    ⟨⟨closure {x}, isIrreducible_singleton.closure, isClosed_closure⟩⟩
  have h0 : (0 : WithBot ℕ∞) ≤ ⊥ := Order.krullDim_nonneg.trans hk
  simp at h0

attribute [local instance 5000] SheafOfModules.instAbelian

attribute [local instance] hasInjectiveResolutions_modules enoughInjectives_modules

open Stacks.Cohomology.SiteModules in
/-- **Stacks 0A4R, clause (1).**  Let `S` be a scheme and `X` a quasi-compact quasi-separated
algebraic space over `S` with `dim X ≤ d`, and let `F` be a quasi-coherent `𝒪_X`-module.  Then
`Hᑫ(X, F) = 0` for every `q > d`.

The dimension bound `d` ranges over `WithBot ℕ∞`, where the dimension of an algebraic space
lives, so it covers every integer of the source: for `d = ⊤` there is nothing to prove, and a
negative `d` (in particular `d = ⊥`) forces `X` to have no points, so that every module on `X`
is zero.  For a natural number `d` this is the induction of Stacks 08GP along elementary
distinguished squares,
`AlgebraicGeometry.Space.isZero_rightDerived_globalSectionsAb_of_dimension_le`; the
cohomology is that of the module over the global functions, and it vanishes exactly when the
underlying abelian group does. -/
@[stacks 0A4R "part (1)"]
theorem isZero_rightDerived_globalSectionsFunctor_of_dimension_le (B : BigFppfSite.{u})
    (S : Scheme.{u}) (hS : B.Contains S) (X : AlgebraicSpaces B S hS)
    (hXqc : IsQuasiCompactSpace B S hS X.1)
    (hXqs : IsAbsolutelyQuasiSeparated B S hS B.contains_terminal X.1) (d : WithBot ℕ∞)
    (hdim : dimension B S hS X.1 X.2 ≤ d) (F : Modules.{u, u} B S hS X.1 X.2)
    (hF : F.IsQuasicoherentOnSite) (q : ℕ) (hq : d < q) :
    IsZero (((globalSectionsFunctor.{u + 1, u, u, u} (Stacks.SheafOfModules.Tensor.ringSheaf
      (smallEtaleRingedSite B S hS X.1 X.2).O)).rightDerived q).obj F) := by
  rw [← isZero_rightDerived_globalSectionsAb_iff]
  induction d using WithBot.recBotCoe with
  | bot =>
    exact isZero_rightDerived_globalSectionsAb_of_isEmpty_points B S hS X
      (isEmpty_points_of_dimension_le_bot B S hS X.1 X.2 hXqs hdim) F q
  | coe e =>
    induction e using WithTop.recTopCoe with
    | top => exact absurd hq (not_lt.2 (by exact_mod_cast le_top))
    | coe n =>
      exact isZero_rightDerived_globalSectionsAb_of_dimension_le B S hS n X hXqc hXqs hdim F hF q
        (by exact_mod_cast (WithBot.coe_lt_coe.1 hq : (n : ℕ∞) < q))

attribute [local instance] etaleModulePullback_additive
  preservesFiniteLimits_etaleModulePullback preservesFiniteColimits_etaleModulePullback
  smallEtaleRingedSite_hasSheafify_addCommGrpCat
  smallEtaleRingedSite_wEqualsLocallyBijective_addCommGrpCat

/-! ### Clause (2): surjectivity of restriction in degree `d` -/

/-- **Stacks 0A4R, clause (2).**  Let `S` be a scheme and `X` a quasi-compact quasi-separated
algebraic space over `S` with `dim X ≤ d`, and let `F` be a quasi-coherent `𝒪_X`-module.  Then
the restriction map `H^d(X, F) ⟶ H^d(U, F|_U)` is surjective for every quasi-compact open
subspace `U` of `X`.

The open subspace is given by an open immersion `j : U ⟶ X` from a quasi-compact algebraic
space, which covers every quasi-compact open subspace (through its inclusion) and every space
isomorphic to one; the restriction map is
`AlgebraicGeometry.Space.cohomologyRestriction`, the right derived map of
`Γ(X, -) ⟶ Γ(U, (-)|_U)`.  The bound `d` is a natural number: for a negative integer `d` the
source's statement is about `H^d`, which is zero.  The proof is
`AlgebraicGeometry.Space.epi_rightDerived_globalSectionsAbRestriction_of_dimension_le`, the
induction of Stacks 08GP with the Mayer–Vietoris sequence of Stacks 08GW in place of the
excision of Stacks 0A4P. -/
@[stacks 0A4R "part (2)"]
theorem surjective_cohomologyRestriction_of_dimension_le (B : BigFppfSite.{u})
    (S : Scheme.{u}) (hS : B.Contains S) (X : AlgebraicSpaces B S hS)
    (hXqc : IsQuasiCompactSpace B S hS X.1)
    (hXqs : IsAbsolutelyQuasiSeparated B S hS B.contains_terminal X.1) (d : ℕ)
    (hdim : dimension B S hS X.1 X.2 ≤ d) {U : AlgebraicSpaces B S hS} (j : U ⟶ X)
    (hj : IsOpenImmersion B S hS j.hom) (hUqc : IsQuasiCompactSpace B S hS U.1)
    (F : Modules.{u, u} B S hS X.1 X.2) (hF : F.IsQuasicoherentOnSite) :
    Function.Surjective
      (cohomologyRestriction B S hS j (isEtale_of_isOpenImmersion B S hS hj) F d) :=
  (AddCommGrpCat.epi_iff_surjective _).1 ((epi_cohomologyRestriction_iff B S hS j _ F d).2
    (epi_rightDerived_globalSectionsAbRestriction_of_dimension_le B S hS d X hXqc hXqs hdim j hj
      (isEtale_of_isOpenImmersion B S hS hj) hUqc F hF))

/-! ### Clause (3): vanishing of cohomology with support above the dimension -/

/-- **Stacks 0A4R, clause (3).**  Let `S` be a scheme and `X` a quasi-compact quasi-separated
algebraic space over `S` with `dim X ≤ d`, and let `F` be a quasi-coherent `𝒪_X`-module.  Then
`H^q_Z(X, F) = 0` for every `q > d` and every closed subspace `Z ⊆ X` whose complement is
quasi-compact.

The complement `U = X ∖ Z` is given by an open immersion `j : U ⟶ X` from a quasi-compact
algebraic space, and `H^q_Z(X, -)` is the `q`-th right derived functor of
`Γ_Z(X, -) = Ker(Γ(X, -) ⟶ Γ(U, (-)|_U))`,
`AlgebraicGeometry.Space.globalSectionsAbRestrictionKer`; this depends on `Z` only through its
open complement, which is how the source's `H^q_Z` depends on `Z`.  As in clause (1) the bound
`d` ranges over `WithBot ℕ∞`; a negative `d` forces `X` to have no points.  For a natural number
`d` the proof is the source's formal argument: in the long exact sequence of the pair
`H^{q-1}(X, F) ⟶ H^{q-1}(U, F) ⟶ H^q_Z(X, F) ⟶ H^q(X, F)` the last group vanishes by
clause (1), and the first map is onto, by clause (2) when `q - 1 = d` and because its target
vanishes by clause (1) on the quasi-compact quasi-separated space `U` when `q - 1 > d`. -/
@[stacks 0A4R "part (3)"]
theorem isZero_rightDerived_globalSectionsAbRestrictionKer_of_dimension_le (B : BigFppfSite.{u})
    (S : Scheme.{u}) (hS : B.Contains S) (X : AlgebraicSpaces B S hS)
    (hXqc : IsQuasiCompactSpace B S hS X.1)
    (hXqs : IsAbsolutelyQuasiSeparated B S hS B.contains_terminal X.1) (d : WithBot ℕ∞)
    (hdim : dimension B S hS X.1 X.2 ≤ d) {U : AlgebraicSpaces B S hS} (j : U ⟶ X)
    (hj : IsOpenImmersion B S hS j.hom) (hUqc : IsQuasiCompactSpace B S hS U.1)
    (F : Modules.{u, u} B S hS X.1 X.2) (hF : F.IsQuasicoherentOnSite) (q : ℕ) (hq : d < q) :
    IsZero (((globalSectionsAbRestrictionKer B S hS j
      (isEtale_of_isOpenImmersion B S hS hj)).rightDerived q).obj F) := by
  induction d using WithBot.recBotCoe with
  | bot =>
    exact Functor.map_isZero _ (isZero_modules_of_isEmpty_points B S hS X
      (isEmpty_points_of_dimension_le_bot B S hS X.1 X.2 hXqs hdim) F)
  | coe e =>
    induction e using WithTop.recTopCoe with
    | top => exact absurd hq (not_lt.2 (by exact_mod_cast le_top))
    | coe n =>
      have hnq : n < q := by exact_mod_cast (WithBot.coe_lt_coe.1 hq : (n : ℕ∞) < q)
      obtain ⟨m, rfl⟩ : ∃ m, q = m + 1 := ⟨q - 1, by omega⟩
      refine isZero_rightDerived_globalSectionsAbRestrictionKer_succ_of_epi B S hS j hj
        (isEtale_of_isOpenImmersion B S hS hj) F m
        (isZero_rightDerived_globalSectionsAb_of_dimension_le B S hS n X hXqc hXqs hdim F hF
          (m + 1) (by omega)) ?_
      rcases Nat.lt_or_ge n m with hnm | hnm
      · have hUqs : IsAbsolutelyQuasiSeparated B S hS B.contains_terminal U.1 :=
          isAbsolutelyQuasiSeparated_of_isQuasiSeparated B S hS B.contains_terminal U.2 hXqs
            (isQuasiSeparated_of_mono B S hS j.hom (mono_of_presheaf_isOpenImmersion hj))
        exact epi_rightDerived_globalSectionsAbRestriction_of_isZero B S hS j
          (isEtale_of_isOpenImmersion B S hS hj) F m
          (isZero_rightDerived_globalSectionsAb_of_dimension_le B S hS n U hUqc hUqs
            ((dimension_le_of_isEtale B S hS U.2 X.2 _
              (isEtale_of_isOpenImmersion B S hS hj)).trans hdim) _
            (isQuasicoherentOnSite_etaleModulePullback B S hS _
              (isEtale_of_isOpenImmersion B S hS hj) F hF) m hnm)
      · obtain rfl : m = n := by omega
        exact epi_rightDerived_globalSectionsAbRestriction_of_dimension_le B S hS m X hXqc hXqs
          hdim j hj (isEtale_of_isOpenImmersion B S hS hj) hUqc F hF

end Space

end AlgebraicGeometry

end
