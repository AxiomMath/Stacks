module

public import Mathlib.FieldTheory.KrullTopology
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.BrauerGroups.CrossedProductSplit
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.GaloisCohomology.Hilbert90
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.GroupCohomology.Continuous
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.GroupCohomology.DiscreteModules
import StacksCore.Tactic.StacksAttribute

/-!
# The discrete Galois module of units, and degree two of Stacks 03R8 part (1) in cocycle form

Let `K` be a field and `Ω/K` a Galois extension. This file builds the discrete `Gal(Ω/K)`-module
`Ωˣ`, as an object of the category of Stacks 04JP in which this library's continuous group
cohomology (Stacks 04JR, `continuousGroupCohomology`) takes its coefficients, and proves that
when `Br(K) = 0` every locally constant `2`-cocycle of `Gal(Ω/K)` with values in `Ωˣ` is a
coboundary.

## Main definitions

* `Stacks.GaloisCohomology.unitsContinuousGModule`: the discrete `Gal(Ω/K)`-module
  `Additive Ωˣ`, with its Krull-topology continuity.

## Main results

* `Stacks.GaloisCohomology.isContinuous_ofMulDistribMulAction_units`: the action of `Gal(Ω/K)` on
  `Ωˣ` is continuous for the Krull topology, the stabiliser of a unit containing the open
  subgroup fixing the simple extension it generates.
* `Stacks.GaloisCohomology.isMulCoboundary₂_of_brauerGroup_eq_one`: if `Br(K) = 0`, every locally
  constant `2`-cocycle on `Gal(Ω/K)` with values in `Ωˣ` is a coboundary.
* `Stacks.GaloisCohomology.isZero_continuousGroupCohomology_units`: `H^q(Gal(Ω/K), Ωˣ) = 0` for
  every `q ≥ 1`, from the comparisons in degrees one and two and the vanishing in degrees `≥ 3`.

## Implementation notes

Everything is stated for a Galois extension `Ω/K` rather than for `Kˢᵉᵖ`. `SeparableClosure K`
unfolds to `separableClosure K (AlgebraicClosure K)`, and finding the action of `Gal(Ω/K)` on `Ωˣ`
through that unfolding exhausts the default instance-search budget; at a type variable `Ω` the
search is immediate.

The degree-two statement is `Stacks.GaloisCohomology.isMulCoboundary₂_of_forall_finiteGalois` fed
with `Stacks.GaloisCohomology.isMulCoboundary₂_of_brauer`, the crossed-product argument at each
finite Galois subextension: `Br(K) = 0` makes every relative Brauer group `Br(L/K)` vanish.

The proposition Stacks 03R8 itself, both parts, is
`Stacks.GaloisCohomology.isZero_continuousGroupCohomology_units_and_torsion_of_forall_brauer` in
`StacksFrontier.AlgebraicGeometry.EtaleCohomology.GaloisCohomology.SeparableClosureVanishing`. The
derived-functor vanishing of `H¹` and `H²` of `Ωˣ` is
`Stacks.GaloisCohomology.isZero_continuousGroupCohomology_units_one` and
`Stacks.GaloisCohomology.isZero_continuousGroupCohomology_units_two`.

`continuousGroupCohomology.{u, v}` takes coefficients in `ContinuousGModule.{u, max u v} G` for
`G : Type u`; with `K Ω : Type u` both `Gal(Ω/K)` and `Additive Ωˣ` live in `Type u`, so the
instantiation used downstream is `continuousGroupCohomology.{u, u}`.

## References

* [Stacks Project, Tag 03R8](https://stacks.math.columbia.edu/tag/03R8)
* [Stacks Project, Tag 04JP](https://stacks.math.columbia.edu/tag/04JP): the category of
  discrete `G`-modules, in which `unitsContinuousGModule` is built.
* [Stacks Project, Tag 04JR](https://stacks.math.columbia.edu/tag/04JR): continuous group
  cohomology.
* [Stacks Project, Tag 03R7](https://stacks.math.columbia.edu/tag/03R7): the identification of
  the Brauer group with `H^2`, of which the direction used in degree two is the
  crossed-product argument.
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits IntermediateField groupCohomology

attribute [local instance] HasDerivedCategory.standard

universe u

namespace Stacks.GaloisCohomology

/-- `ℤ`-modules are regarded as topological spaces with the discrete topology, which is what
makes continuity of an action of a topological group on them a meaningful condition. This is the
local instance of
`StacksFrontier.AlgebraicGeometry.EtaleCohomology.GroupCohomology.DiscreteModules`, repeated here
because it is local there. -/
local instance : HasForget₂ (ModuleCat.{u} ℤ) TopCat.{u} :=
  { forget₂ := forget (ModuleCat.{u} ℤ) ⋙ TopCat.discrete
    forget_comp := rfl }

variable (K Ω : Type u) [Field K] [Field Ω] [Algebra K Ω] [IsGalois K Ω]

/-! ### The discrete Galois module of units of a Galois extension -/

/-- **The action of `Gal(Ω/K)` on `Ωˣ` is continuous** for the Krull topology, `Ω/K` being
Galois. By the standard reformulation of continuity for a discrete module it is enough that each
stabiliser be open, and the stabiliser of a unit `u` contains the subgroup fixing the simple
extension `K⟮u⟯`, which is finite over `K` because `Ω/K` is algebraic and is therefore an open
subgroup of `Gal(Ω/K)`. -/
theorem isContinuous_ofMulDistribMulAction_units :
    (Stacks.GroupCohomology.actionOfRepresentation ℤ Gal(Ω/K) (Additive Ωˣ)
      (Representation.ofMulDistribMulAction Gal(Ω/K) Ωˣ)).IsContinuous := by
  rw [Stacks.GroupCohomology.isContinuous_actionOfRepresentation_iff]
  intro x
  obtain ⟨u, rfl⟩ : ∃ u : Ωˣ, Additive.ofMul u = x := ⟨x.toMul, rfl⟩
  have hfd : FiniteDimensional K K⟮(u : Ω)⟯ :=
    IntermediateField.adjoin.finiteDimensional (Algebra.IsIntegral.isIntegral (u : Ω))
  have hle : (K⟮(u : Ω)⟯).fixingSubgroup ≤ MulAction.stabilizer Gal(Ω/K) u := by
    intro g hg
    simp only [IntermediateField.mem_fixingSubgroup_iff] at hg
    have hga : g (u : Ω) = (u : Ω) :=
      hg (u : Ω) (IntermediateField.mem_adjoin_simple_self K (u : Ω))
    refine MulAction.mem_stabilizer_iff.mpr (Units.val_inj.mp ?_)
    simpa using hga
  have hset : {g : Gal(Ω/K) |
        Representation.ofMulDistribMulAction Gal(Ω/K) Ωˣ g (Additive.ofMul u) =
          Additive.ofMul u}
      = ((MulAction.stabilizer Gal(Ω/K) u : Subgroup Gal(Ω/K)) : Set Gal(Ω/K)) := by
    ext g
    simp only [SetLike.mem_coe, MulAction.mem_stabilizer_iff]
    exact ⟨fun h ↦ Additive.ofMul.injective h, fun h ↦ congrArg Additive.ofMul h⟩
  rw [hset]
  exact Subgroup.isOpen_mono hle (K⟮(u : Ω)⟯).fixingSubgroup_isOpen

/-- **Stacks Project, Tag 04JP at the units of a Galois extension.** The multiplicative group of
`Ω`, written additively, as a discrete `Gal(Ω/K)`-module. At `Ω = Kˢᵉᵖ` these are the
coefficients of part (1) of Stacks 03R8, and this is the object at which this library's
continuous group cohomology of Stacks 04JR evaluates to the groups
`H^q(Gal(Kˢᵉᵖ/K), (Kˢᵉᵖ)^*)`. -/
def unitsContinuousGModule : ContinuousGModule.{u, u} Gal(Ω/K) :=
  Stacks.GroupCohomology.ofRepresentation
    (Representation.ofMulDistribMulAction Gal(Ω/K) Ωˣ)
    (isContinuous_ofMulDistribMulAction_units K Ω)

/-! ### Degree two in cocycle form -/

/-- If `Br(K) = 0` then every locally constant `2`-cocycle on `Gal(Ω/K)` with values in `Ωˣ` is a
coboundary. At `Ω = Kˢᵉᵖ` this is the cocycle form of the degree-two case of part (1) of
Stacks 03R8, from the instance `K' = K` of that proposition's hypothesis: `Br(K) = 0` makes every
relative Brauer group `Br(L/K)` vanish, which is the premise of
`Stacks.GaloisCohomology.isMulCoboundary₂_of_brauer` at each finite Galois subextension `L` of
`Ω`. -/
theorem isMulCoboundary₂_of_brauerGroup_eq_one (hBr : ∀ y : BrauerGroup K, y = 1)
    (f : Gal(Ω/K) × Gal(Ω/K) → Ωˣ) (hloc : IsLocallyConstant f) (hf : IsMulCocycle₂ f) :
    IsMulCoboundary₂ f := by
  refine isMulCoboundary₂_of_forall_finiteGalois (fun L F hF ↦ ?_) f hloc hf
  exact isMulCoboundary₂_of_brauer (K := K) (L := L) (fun y _ ↦ hBr y) F hF

/-- Let `K` be a field with `Br(K) = 0` and let `Ω/K` be a Galois extension. Given, in degrees one
and two, that the vanishing of the cocycle quotient implies the vanishing of
`continuousGroupCohomology`, and given the vanishing in degrees `q ≥ 3`, the group
`H^q(Gal(Ω/K), Ωˣ)` vanishes for every `q ≥ 1`. The cocycle statements are Hilbert's theorem 90,
`Stacks.GaloisCohomology.isMulCoboundary₁_of_isLocallyConstant_of_isMulCocycle₁`, and
`Stacks.GaloisCohomology.isMulCoboundary₂_of_brauerGroup_eq_one`.

The comparison hypotheses in degrees one and two hold in this library: the conclusions they ask
for are `Stacks.GaloisCohomology.isZero_continuousGroupCohomology_units_one` and
`Stacks.GaloisCohomology.isZero_continuousGroupCohomology_units_two`. Part (1) of Stacks 03R8
with no extra hypothesis is
`Stacks.GaloisCohomology.isZero_continuousGroupCohomology_units_of_forall_brauer`. -/
theorem isZero_continuousGroupCohomology_units (hBr : ∀ y : BrauerGroup K, y = 1)
    (h03QU₁ : (∀ f : Gal(Ω/K) → Ωˣ, IsLocallyConstant f → IsMulCocycle₁ f →
          IsMulCoboundary₁ f) →
        IsZero (continuousGroupCohomology.{u, u} Gal(Ω/K) 1 (unitsContinuousGModule K Ω)))
    (h03QU₂ : (∀ f : Gal(Ω/K) × Gal(Ω/K) → Ωˣ, IsLocallyConstant f → IsMulCocycle₂ f →
          IsMulCoboundary₂ f) →
        IsZero (continuousGroupCohomology.{u, u} Gal(Ω/K) 2 (unitsContinuousGModule K Ω)))
    (hhigh : ∀ q : ℕ, 3 ≤ q →
      IsZero (continuousGroupCohomology.{u, u} Gal(Ω/K) q (unitsContinuousGModule K Ω)))
    (q : ℕ) (hq : 1 ≤ q) :
    IsZero (continuousGroupCohomology.{u, u} Gal(Ω/K) q (unitsContinuousGModule K Ω)) := by
  by_cases h1 : q = 1
  · subst h1
    exact h03QU₁ fun f hloc hf ↦ isMulCoboundary₁_of_isLocallyConstant_of_isMulCocycle₁ f hloc hf
  by_cases h2 : q = 2
  · subst h2
    exact h03QU₂ fun f hloc hf ↦ isMulCoboundary₂_of_brauerGroup_eq_one K Ω hBr f hloc hf
  exact hhigh q (by lia)

end Stacks.GaloisCohomology

end
