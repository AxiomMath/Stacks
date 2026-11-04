module

public import StacksFrontier.AlgebraicGeometry.Cohomology.Coherent.QuasicoherentVanishing
public import StacksFrontier.AlgebraicGeometry.Duality.Lichtenbaum.NoProperComponent
public import StacksFrontier.AlgebraicGeometry.Duality.Lichtenbaum.ProperComponent
public import StacksFrontier.AlgebraicGeometry.Duality.Lichtenbaum.VarietyTopCohomology

/-!
# Lichtenbaum's theorem on the vanishing of top coherent cohomology

[Stacks, Tag 0G5F]: let `X` be a nonempty separated scheme of finite type over a field `k` and
let `d = dim X`. The following are equivalent:

1. `H^d(X, F) = 0` for all coherent `𝒪_X`-modules `F`,
2. `H^d(X, F) = 0` for all quasi-coherent `𝒪_X`-modules `F`, and
3. no irreducible component `X' ⊆ X` of dimension `d` is proper over `k`.

## Main results

* `Stacks.Duality.Lichtenbaum.isZero_cohomologyOverField_iff`: the `k`-vector space
  `H^d(X, F)` vanishes exactly when the underlying cohomology module does.
* `Stacks.Duality.Lichtenbaum.tfae_isZero_cohomologyOverField_of_lichtenbaum`: the three
  conditions are equivalent, given [Stacks, Tag 0G5E] as a hypothesis.
* `Stacks.Duality.Lichtenbaum.tfae_isZero_cohomologyOverField`: **[Stacks, Tag 0G5F]**, with
  that hypothesis discharged by
  `Stacks.Duality.Lichtenbaum.le_topologicalKrullDim_and_isProper_of_not_isZero_rightDerived`.

## Implementation notes

The three parts of the proof are, in the order of the source:
(1) ⇒ (3) is `Stacks.Duality.not_isProper_irreducibleComponent_of_forall_isZero_rightDerived`
(through [Stacks, Tag 0FVV] part (6)), (3) ⇒ (1) is
`Stacks.Duality.Lichtenbaum.isZero_rightDerived_of_forall_not_isProper_of_lichtenbaum` (through
[Stacks, Tag 01YF] and [Stacks, Tag 0G5E]), and (1) ⇔ (2) is
`AlgebraicGeometry.forall_isZero_cohomologyOverField_isCoherent_iff_isQuasicoherent` (through
[Stacks, Tag 01PG] and [Stacks, Tag 01FF]).

Cohomology is `AlgebraicGeometry.cohomologyOverField`, the `k`-vector space `H^d(X, F)` in which
[Stacks, Tag 0FVV] part (6) is stated. The dimension `d` is a natural number with
`topologicalKrullDim X = d`; such a `d` exists for every nonempty `X` of finite type over `k`
(`Stacks.Duality.Lichtenbaum.exists_topologicalKrullDim_eq_natCast`), and its existence forces
`X` to be nonempty, so the nonemptiness hypothesis of the source is not repeated. An irreducible
component `X'` is viewed, as in the source, as an integral closed subscheme through its reduced
induced structure `(Scheme.IdealSheafData.vanishingIdeal X').subscheme`, whose dimension is that
of `X'`.

## References

* [Stacks Project, Tag 0G5F](https://stacks.math.columbia.edu/tag/0G5F)
* [Stacks Project, Tag 0G5E](https://stacks.math.columbia.edu/tag/0G5E)
-/

@[expose] public section

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits Opposite TopologicalSpace

universe u

namespace Stacks.Duality.Lichtenbaum

/-- The `k`-vector space `Hⁿ(X, F)` vanishes exactly when the `Γ(X, 𝒪_X)`-module `Hⁿ(X, F)` does:
the former is the latter with its scalars restricted. -/
theorem isZero_cohomologyOverField_iff (k : Type u) [Field k] {X : Scheme.{u}}
    (f : X ⟶ Spec (.of k)) (F : X.Modules) (n : ℕ) :
    IsZero (cohomologyOverField k f F n) ↔
      IsZero (((moduleGlobalSections X).rightDerived n).obj F) := by
  simp only [ModuleCat.isZero_iff_subsingleton]
  rfl

/-- **[Stacks, Tag 0G5F], given [Stacks, Tag 0G5E].** For `X` separated of finite type over a
field `k` with `dim X = d`, vanishing of `H^d(X, F)` for all coherent `F`, vanishing of
`H^d(X, F)` for all quasi-coherent `F`, and the absence of a `d`-dimensional irreducible
component proper over `k` are equivalent, provided [Stacks, Tag 0G5E] holds in the form of the
hypothesis `lichtenbaum`. -/
theorem tfae_isZero_cohomologyOverField_of_lichtenbaum (k : Type u) [Field k] {X : Scheme.{u}}
    (f : X ⟶ Spec (.of k)) [IsSeparated f] [LocallyOfFiniteType f] [QuasiCompact f] (d : ℕ)
    (hd : topologicalKrullDim X = d)
    (lichtenbaum : ∀ (Z : Scheme.{u}) (g : Z ⟶ Spec (.of k)) [IsVariety k g] (G : Z.Modules)
      [G.IsCoherent], ¬ IsZero (((moduleGlobalSections Z).rightDerived d).obj G) →
        (d : WithBot ℕ∞) ≤ topologicalKrullDim Z ∧ (topologicalKrullDim Z = d → IsProper g)) :
    List.TFAE
      [∀ (F : X.Modules) [F.IsCoherent], IsZero (cohomologyOverField k f F d),
       ∀ (F : X.Modules) [F.IsQuasicoherent], IsZero (cohomologyOverField k f F d),
       ∀ Z : irreducibleComponents X,
        let C := Scheme.IdealSheafData.vanishingIdeal (X := X)
          ⟨Z.1, isClosed_of_mem_irreducibleComponents Z.1 Z.2⟩
        topologicalKrullDim C.subscheme = d → ¬ IsProper (C.subschemeι ≫ f)] := by
  have : IsNoetherian X := isNoetherian_of_locallyOfFiniteType f
  tfae_have 1 ↔ 2 := forall_isZero_cohomologyOverField_isCoherent_iff_isQuasicoherent k f d
  tfae_have 1 → 3 := fun h =>
    not_isProper_irreducibleComponent_of_forall_isZero_rightDerived k f d
      fun F _ => (isZero_cohomologyOverField_iff k f F d).mp (h F)
  tfae_have 3 → 1 := fun h F _ => (isZero_cohomologyOverField_iff k f F d).mpr
    (isZero_rightDerived_of_forall_not_isProper_of_lichtenbaum k f d hd lichtenbaum h F)
  tfae_finish

/-- **[Stacks, Tag 0G5F].** Let `X` be a separated scheme of finite type over a field `k`, of
dimension `d` (so `X` is nonempty). The following are equivalent:

1. `H^d(X, F) = 0` for all coherent `𝒪_X`-modules `F`,
2. `H^d(X, F) = 0` for all quasi-coherent `𝒪_X`-modules `F`, and
3. no irreducible component `X' ⊆ X` of dimension `d`, viewed as an integral closed subscheme
   through its reduced induced structure, is proper over `k`.

Here `H^d(X, F)` is the `k`-vector space `AlgebraicGeometry.cohomologyOverField k f F d`. -/
@[stacks 0G5F]
theorem tfae_isZero_cohomologyOverField (k : Type u) [Field k] {X : Scheme.{u}}
    (f : X ⟶ Spec (.of k)) [IsSeparated f] [LocallyOfFiniteType f] [QuasiCompact f] (d : ℕ)
    (hd : topologicalKrullDim X = d) :
    List.TFAE
      [∀ (F : X.Modules) [F.IsCoherent], IsZero (cohomologyOverField k f F d),
       ∀ (F : X.Modules) [F.IsQuasicoherent], IsZero (cohomologyOverField k f F d),
       ∀ Z : irreducibleComponents X,
        let C := Scheme.IdealSheafData.vanishingIdeal (X := X)
          ⟨Z.1, isClosed_of_mem_irreducibleComponents Z.1 Z.2⟩
        topologicalKrullDim C.subscheme = d → ¬ IsProper (C.subschemeι ≫ f)] :=
  tfae_isZero_cohomologyOverField_of_lichtenbaum k f d hd fun _ g _ G _ h =>
    le_topologicalKrullDim_and_isProper_of_not_isZero_rightDerived k g G d h

end Stacks.Duality.Lichtenbaum
