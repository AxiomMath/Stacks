module

public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.GroupHomology.PontryaginDualModules
public import StacksFrontier.Topology.Algebra.PontryaginDual.Torsion

/-!
# Duals of torsion discrete and of profinite compact `G`-modules

Let `G` be a topological group. The dual `M ↦ M^∧ = Hom_cont(M, S¹)` takes torsion discrete
`G`-modules to profinite compact `G`-modules, and profinite compact `G`-modules to torsion
discrete `G`-modules. On these modules the characters are `ℚ/ℤ`-valued: for `M` torsion discrete,
`M^∧ = Hom(M, ℚ/ℤ)`, and for `M` profinite, `M^∧ = Hom_cont(M, ℚ/ℤ)`, compatibly with the
contragredient actions `(g • χ)(m) = χ(g⁻¹ • m)`. These are the last assertions of the paragraph
"Trivial duality" of [Stacks, Tag 03VI]; the group-theoretic content is in
`StacksFrontier.Topology.Algebra.PontryaginDual.Torsion`.

## Main definitions

* `Stacks.GroupHomology.compactDualAddEquivCharacterModule`: for `M` a torsion discrete
  `G`-module, `M^∧ ≃ Hom(M, ℚ/ℤ)`.
* `Stacks.GroupHomology.discreteDualAddEquivLocallyConstantCharacters`: for `M` a profinite
  compact `G`-module, `M^∧ ≃ Hom_cont(M, ℚ/ℤ)`.

## Main results

* `Stacks.GroupHomology.isProfiniteTop_compactDual`: the dual of a torsion discrete `G`-module is
  profinite.
* `Stacks.GroupHomology.isAddTorsion_discreteDual`: the dual of a profinite compact `G`-module is
  torsion.
* `Stacks.GroupHomology.compactDualAddEquivCharacterModule_smul_apply`,
  `Stacks.GroupHomology.discreteDualAddEquivLocallyConstantCharacters_smul_apply`: the two
  identifications are equivariant for the contragredient actions.

## References

* [Stacks Project, Tag 03VI](https://stacks.math.columbia.edu/tag/03VI)
-/

@[expose] public noncomputable section

open CategoryTheory Opposite Stacks.GroupCohomology Stacks.Pontryagin Stacks.Chapter05.Tag_0BR1

universe u v

namespace Stacks.GroupHomology

variable (G : Type u) [Group G] [TopologicalSpace G] [IsTopologicalGroup G]

section Discrete

attribute [local instance] carrierAction carrierMulAction carrierTopology discreteTopology_carrier

/-- **The dual of a torsion discrete `G`-module is profinite**: compact, Hausdorff and totally
disconnected. -/
@[stacks 03VI "M ↦ M^∧ takes torsion discrete G-modules to profinite compact G-modules"]
theorem isProfiniteTop_compactDual (M : ContinuousGModule.{u, v} G)
    (hM : IsAddTorsion M.obj.obj.V) : IsProfiniteTop ((compactDual G).obj (op M)) :=
  isProfiniteTop_of_isTorsion (A := Multiplicative M.obj.obj.V)
    (isMulTorsion_multiplicative_iff.mpr hM)

/-- **The dual of a torsion discrete `G`-module is `Hom(M, ℚ/ℤ)`**: a character `χ` corresponds
to the homomorphism `m ↦ x` with `χ(m) = exp (2πix)`. -/
@[stacks 03VI "for M a torsion discrete G-module, M^∧ = Hom(M, Q/Z), compatibly with the action \
(compactDualAddEquivCharacterModule_smul_apply)"]
def compactDualAddEquivCharacterModule (M : ContinuousGModule.{u, v} G)
    (hM : IsAddTorsion M.obj.obj.V) :
    (compactDual G).obj (op M) ≃+ CharacterModule M.obj.obj.V :=
  addEquivCharacterModule (A := Multiplicative M.obj.obj.V)
    (isMulTorsion_multiplicative_iff.mpr hM)

/-- The value of `compactDualAddEquivCharacterModule M hM χ` at `m` is the `x ∈ ℚ/ℤ` with
`exp (2πix) = χ(m)`. -/
lemma ratCircleToCircle_compactDualAddEquivCharacterModule_apply (M : ContinuousGModule.{u, v} G)
    (hM : IsAddTorsion M.obj.obj.V) (χ : (compactDual G).obj (op M)) (m : M.obj.obj.V) :
    ratCircleToCircle (compactDualAddEquivCharacterModule G M hM χ m) =
      Additive.ofMul ((show AddPontryaginDual M.obj.obj.V from χ) m) :=
  ratCircleToCircle_addEquivCharacterModule_apply _ χ (Multiplicative.ofAdd m)

/-- The identification `M^∧ = Hom(M, ℚ/ℤ)` of a torsion discrete `G`-module is equivariant for
the contragredient actions: `(g • χ)(m) = χ(g⁻¹ • m)`. -/
lemma compactDualAddEquivCharacterModule_smul_apply (M : ContinuousGModule.{u, v} G)
    (hM : IsAddTorsion M.obj.obj.V) (g : G) (χ : (compactDual G).obj (op M))
    (m : M.obj.obj.V) :
    compactDualAddEquivCharacterModule G M hM (g • χ) m =
      compactDualAddEquivCharacterModule G M hM χ (g⁻¹ • m) := by
  apply ratCircleToCircle_injective
  exact (ratCircleToCircle_compactDualAddEquivCharacterModule_apply G M hM (g • χ) m).trans
    (ratCircleToCircle_compactDualAddEquivCharacterModule_apply G M hM χ (g⁻¹ • m)).symm

end Discrete

section Compact

omit [IsTopologicalGroup G] in
variable {G} in
/-- The multiplicative form of a profinite compact `G`-module is a profinite group. -/
lemma totallyDisconnectedSpace_multiplicative (M : CompactGModule.{u, v} G)
    [TotallyDisconnectedSpace M] : TotallyDisconnectedSpace (Multiplicative M) :=
  inferInstanceAs (TotallyDisconnectedSpace M)

attribute [local instance] totallyDisconnectedSpace_multiplicative

/-- **The dual of a profinite compact `G`-module is torsion** (and discrete, as the dual of any
compact module is). -/
@[stacks 03VI "M ↦ M^∧ takes profinite compact G-modules to torsion discrete G-modules"]
theorem isAddTorsion_discreteDual (M : CompactGModule.{u, v} G) [TotallyDisconnectedSpace M] :
    IsAddTorsion ((discreteDual G).obj (op M)).obj.obj.V := fun χ ↦ by
  let ψ : PontryaginDual (Multiplicative M) := Additive.toMul (show AddPontryaginDual M from χ)
  have h : IsOfFinAddOrder (Additive.ofMul ψ) :=
    isOfFinAddOrder_ofMul_iff.mpr ((discreteTopology_and_isTorsion (A := Multiplicative M)).2 ψ)
  exact h

/-- **The dual of a profinite compact `G`-module is `Hom_cont(M, ℚ/ℤ)`**, the characters with
values in `ℚ/ℤ` that are continuous for the discrete topology on `ℚ/ℤ`. -/
@[stacks 03VI "for M a profinite compact G-module, M^∧ = Hom_cont(M, Q/Z), compatibly with the \
action (discreteDualAddEquivLocallyConstantCharacters_smul_apply)"]
def discreteDualAddEquivLocallyConstantCharacters (M : CompactGModule.{u, v} G)
    [TotallyDisconnectedSpace M] :
    ((discreteDual G).obj (op M)).obj.obj.V ≃+ locallyConstantCharacters M :=
  addEquivLocallyConstantCharacters (A := Multiplicative M)

/-- The value of `discreteDualAddEquivLocallyConstantCharacters M χ` at `m` is the `x ∈ ℚ/ℤ`
with `exp (2πix) = χ(m)`. -/
lemma ratCircleToCircle_discreteDualAddEquivLocallyConstantCharacters_apply
    (M : CompactGModule.{u, v} G) [TotallyDisconnectedSpace M]
    (χ : ((discreteDual G).obj (op M)).obj.obj.V) (m : M) :
    ratCircleToCircle
        ((discreteDualAddEquivLocallyConstantCharacters G M χ : CharacterModule M) m) =
      Additive.ofMul ((show AddPontryaginDual M from χ) m) :=
  ratCircleToCircle_addEquivLocallyConstantCharacters_apply (A := Multiplicative M) χ
    (Multiplicative.ofAdd m)

/-- The identification `M^∧ = Hom_cont(M, ℚ/ℤ)` of a profinite compact `G`-module is equivariant
for the contragredient actions: `(g • χ)(m) = χ(g⁻¹ • m)`. -/
lemma discreteDualAddEquivLocallyConstantCharacters_smul_apply (M : CompactGModule.{u, v} G)
    [TotallyDisconnectedSpace M] (g : G) (χ : AddPontryaginDual M) (m : M) :
    (discreteDualAddEquivLocallyConstantCharacters G M (g • χ) : CharacterModule M) m =
      (discreteDualAddEquivLocallyConstantCharacters G M χ : CharacterModule M) (g⁻¹ • m) := by
  apply ratCircleToCircle_injective
  exact (ratCircleToCircle_discreteDualAddEquivLocallyConstantCharacters_apply G M (g • χ) m).trans
    (ratCircleToCircle_discreteDualAddEquivLocallyConstantCharacters_apply G M χ (g⁻¹ • m)).symm

end Compact

end Stacks.GroupHomology
