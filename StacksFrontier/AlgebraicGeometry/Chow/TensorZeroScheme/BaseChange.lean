module

public import StacksFrontier.AlgebraicGeometry.Chow.TensorZeroScheme.BranchFibreProduct
public import StacksFrontier.AlgebraicGeometry.Chow.TensorZeroScheme.WholeTag
public import StacksFrontier.AlgebraicGeometry.DeRham.LineBundle.InverseSituationBaseChange

/-!
# The construction of Tag 0F97 commutes with base change

Let `Y` be a scheme, let `L₁` and `L₂` be invertible `𝒪_Y`-modules, let `s` be a global section
of `L₁ ⊗_{𝒪_Y} L₂`, and let `g : Y' ⟶ Y` be an arbitrary morphism of schemes. Write `L₁' = g^*L₁`
and `L₂' = g^*L₂`, which are again invertible, and `s' = g^*s` for the base-changed section read
in `L₁' ⊗ L₂'` through the comparison of [Stacks, Tag 01CD].

This file proves that the ambient space of the construction of [Stacks, Tag 0F97] — the fibre
product `Tot(L₁^{⊗ -1}) ×_Y Tot(L₂^{⊗ -1})` of the two line bundles — commutes with the base
change: the canonical morphism from the ambient space of the base-changed data to the original
one sits in a cartesian square over `g`.

## Main definitions

* `Stacks.Chow.TensorZeroScheme.ambientBaseChange`: **the canonical morphism
  `Tot(L₁'^{⊗ -1}) ×_{Y'} Tot(L₂'^{⊗ -1}) ⟶ Tot(L₁^{⊗ -1}) ×_Y Tot(L₂^{⊗ -1})`** of ambient
  spaces.

## Main results

* `Stacks.Chow.TensorZeroScheme.ambientBaseChange_comp`: the canonical morphism lies over `g`.
* `Stacks.Chow.TensorZeroScheme.isPullback_ambientBaseChange`: **the ambient space commutes with
  arbitrary base change** — the square it sits in is cartesian, with no hypothesis on `g`.

## Implementation notes

The whole content is `Stacks.LineBundle.isPullback_totalSpaceBaseChange`, that the total space of
a single line bundle commutes with base change, applied to each of the two factors. The canonical
morphism is the lift into the fibre product of the two composites `pr_i ≫ β_i`, and the universal
property of the square is proved directly: the two line-bundle squares lift a point of the fibre
product together with a point of `Y'` agreeing over `Y` to a point of each of the two
base-changed line bundles over the same point of `Y'`, and those two points assemble into a point
of the new fibre product. Pasting would need the intermediate square

`Tot(L₁'^{⊗ -1}) ×_{Y'} Tot(L₂'^{⊗ -1}) ⟶ Tot(L₁^{⊗ -1}) ×_Y Tot(L₂^{⊗ -1})` over
`Tot(L₁'^{⊗ -1}) ⟶ Tot(L₁^{⊗ -1})`

to be known cartesian first, which is the same amount of work in a less direct form.

*The asymmetry of the fibre product.* `totalProj` is the first projection followed by the first
line bundle's structure morphism, so the second factor's comparison with `g` goes through
`Stacks.Chow.TensorZeroScheme.secondProj_comp`; that is the only place the asymmetry is visible.

*What is not here, and what no longer waits on it.* That the two fibre coordinates
`Stacks.Chow.TensorZeroScheme.coord₁` and `coord₂` correspond across the square — and hence that
the equation, the ideal sheaf `Stacks.Chow.TensorZeroScheme.spaceIdeal`, the structure morphism
`proj`, the two branches and the two sections of *this construction* do — is not proved.
Everything after the coordinates is bookkeeping: `Stacks.Divisors.zeroScheme_pullback` turns the
comparison of the equations into the comparison of the ideals,
`AlgebraicGeometry.isPullback_of_isClosedImmersion` turns that into the cartesian square for
`proj` once pasted with `isPullback_ambientBaseChange`, and
`Stacks.PullbackTensorIso.pullbackTensorSection_comp` handles the `q^*s` summand of the
equation.

**The base-change clause of [Stacks, Tag 0F97] does not depend on any of this.** It is
`Stacks.Chow.TensorZeroScheme.Decomposition.isStableUnderBaseChange`, proved for an arbitrary
diagram by transporting it: the clause pins its witness down to the fibre product, the inverse
images of `D₁` and `D₂` and the pullbacks of `s₁`, `s₂`, so the content is that the transported
data satisfies the tag's seven conditions, and no fibre coordinate appears. What the statement
below would add is the *finer* assertion that the canonically constructed diagram over `Y'`
coincides with the transport of the one over `Y`.

The one missing input for that finer assertion is that **the fibre coordinate of a line bundle
commutes with base change**: that `Stacks.LineBundle.fibreCoordinate Y' (g^*M)` is
`Stacks.LineBundle.fibreCoordinate Y M` pulled back along
`Stacks.LineBundle.totalSpaceBaseChange`.
`Stacks.LineBundle.totalSpaceHomEquiv_totalSpaceBaseChange` is that statement for the degree-one
inclusion `M^{⊗ -1} ⟶ q_* 𝒪_{L(M)}`, which is the datum the
fibre coordinate is built from, and the passage from the datum to the coordinate crosses four
identifications. The first of them, the pullback--pushforward adjunction producing
`Stacks.LineBundle.Situation.tautologicalFunctional` from the datum, is a mate-of-a-square
statement and is now done:
`Stacks.LineBundle.tautologicalFunctional_totalSpaceBaseChange` in
`StacksFrontier.AlgebraicGeometry.Chow.TensorZeroScheme.TautologicalFunctionalBaseChange`.

The other three are not. They are the duality
`Stacks.LineBundle.Situation.pullbackDuality` producing
`Stacks.LineBundle.Situation.tautologicalSection` from the functional, and the two dualization
isomorphisms `Stacks.LineBundle.Situation.pullbackInverseIso` and
`Stacks.LineBundle.lineBundlePullbackIso`, for which what is needed is the cocycle condition of
`Stacks.ProjBundleInverseBaseChange.pullbackTensorPowerNegOneIso` along a composite of
pullbacks. The two dualization isomorphisms are characterized by their duality pairings in
`StacksFrontier.AlgebraicGeometry.PullbackTensorIso.InvIsoPairing`, which is the handle that
cocycle condition would be proved through; what that handle still lacks is that the pullback
functor is *monoidal* for `Stacks.SheafInternalHom.monoidalCategory` with
`Stacks.ProjBundleInverseBaseChange.pullbackTensorIso` as its tensorator, since the pairing
identity of `Stacks.TensorPowers.TensorInverse.invIso_pairing` mentions the associator and both
unitors. `Stacks.PullbackSheafTensor.monoidal` is that statement at the ringed-space spelling of
the monoidal structure, and
`StacksFrontier.AlgebraicGeometry.PullbackTensorIso.MonoidalBridge` identifies every ingredient of
the two spellings — the monoidal structures, the pullback functors, the comparison of Tag 01CD
and the two unit comparisons, each on the nose — so that what is left of that bridge is the
transport of the three coherences across the re-seating of
`CategoryTheory.MonoidalCategory.reseat`.

*Two further handles, not yet joined up.*
`Stacks.TensorPowerPullback.pullbackIntPowIso` is a comparison `f^*(L^{⊗ n}) ≅ (f^*L)^{⊗ n}` for
every `n : ℤ` built from Tag 01CD alone, and
`Stacks.TensorPowerPullback.pullbackIntPowIso_coherentMulIso` is its compatibility with the
coherent multiplication of Tag 01CU. At `n = -1` it has *exactly* the type of
`Stacks.ProjBundleInverseBaseChange.pullbackTensorPowerNegOneIso` — this was checked — but the
two are not definitionally equal and nothing in the library relates them; proving them equal
through `Stacks.ProjBundleInverseBaseChange.eq_pullbackTensorPowerNegOneIso_of_pairing` would
put the ringed-space coherence API behind the cocycle condition.
Separately, the chain through the dualization isomorphisms can be bypassed altogether if the
fibre coordinate is instead pinned down by a *duality pairing against the tautological
functional*, taken with the pulled-back trivialization
`(Stacks.ProjBundleInverseBaseChange.pullbackTensorInverse q M _).mulIso'`, which mentions only
Tag 01CD and `q^*` of a fixed isomorphism on `Y`: that pairing crosses the square by
`Stacks.PullbackTensorIso.pullbackTensorSection_of_square` and the functional crosses it by
`Stacks.LineBundle.tautologicalFunctional_totalSpaceBaseChange`, both of which are available, so
on that route the only missing step is the identification of the fibre coordinate with the
pairing — a statement about a single scheme, with no base change in it.

## References

* [Stacks Project, Tag 0F97](https://stacks.math.columbia.edu/tag/0F97)
* [Stacks Project, Tag 01CD](https://stacks.math.columbia.edu/tag/01CD)
* [Stacks Project, Tag 01M2](https://stacks.math.columbia.edu/tag/01M2)
-/

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits Opposite
open Stacks.LineBundle (lineBundleProj lineBundleSpace totalSpaceBaseChange
  totalSpaceBaseChange_comp_lineBundleProj isPullback_totalSpaceBaseChange)

universe u

@[expose] public noncomputable section

namespace Stacks.Chow.TensorZeroScheme

variable (Y : Scheme.{u}) (L₁ L₂ : Y.Modules)
  [h₁ : AlgebraicGeometry.SheafOfModules.IsInvertible Y.sheaf.obj Y.ringCatSheaf.property L₁]
  [h₂ : AlgebraicGeometry.SheafOfModules.IsInvertible Y.sheaf.obj Y.ringCatSheaf.property L₂]

variable {Y' : Scheme.{u}} (g : Y' ⟶ Y)

include h₁ h₂ in
/-- The two composites `pr_i ≫ β_i` of a projection of the base-changed fibre product with the
canonical morphism of total spaces agree over `Y`, so together they define a morphism to the
original fibre product. -/
theorem ambientBaseChange_condition :
    (firstProj Y' ((Scheme.Modules.pullback g).obj L₁) ((Scheme.Modules.pullback g).obj L₂) ≫
        totalSpaceBaseChange g L₁) ≫ lineBundleProj Y L₁ =
      (secondProj Y' ((Scheme.Modules.pullback g).obj L₁)
          ((Scheme.Modules.pullback g).obj L₂) ≫ totalSpaceBaseChange g L₂) ≫
        lineBundleProj Y L₂ := by
  rw [Category.assoc, Category.assoc, totalSpaceBaseChange_comp_lineBundleProj,
    totalSpaceBaseChange_comp_lineBundleProj, ← Category.assoc, ← Category.assoc,
    secondProj_comp]
  rfl

include h₁ h₂ in
/-- **The canonical morphism of ambient spaces**: the lift into
`Tot(L₁^{⊗ -1}) ×_Y Tot(L₂^{⊗ -1})` of the two projections of the base-changed fibre product
followed by the canonical morphisms of total spaces. -/
def ambientBaseChange :
    totalSpace Y' ((Scheme.Modules.pullback g).obj L₁) ((Scheme.Modules.pullback g).obj L₂) ⟶
      totalSpace Y L₁ L₂ :=
  Limits.pullback.lift
    (firstProj Y' ((Scheme.Modules.pullback g).obj L₁) ((Scheme.Modules.pullback g).obj L₂) ≫
      totalSpaceBaseChange g L₁)
    (secondProj Y' ((Scheme.Modules.pullback g).obj L₁) ((Scheme.Modules.pullback g).obj L₂) ≫
      totalSpaceBaseChange g L₂)
    (ambientBaseChange_condition Y L₁ L₂ g)

include h₁ h₂ in
/-- The canonical morphism of ambient spaces, read through the first projection. -/
theorem ambientBaseChange_comp_firstProj :
    ambientBaseChange Y L₁ L₂ g ≫ firstProj Y L₁ L₂ =
      firstProj Y' ((Scheme.Modules.pullback g).obj L₁)
          ((Scheme.Modules.pullback g).obj L₂) ≫ totalSpaceBaseChange g L₁ :=
  Limits.pullback.lift_fst _ _ _

include h₁ h₂ in
/-- The canonical morphism of ambient spaces, read through the second projection. -/
theorem ambientBaseChange_comp_secondProj :
    ambientBaseChange Y L₁ L₂ g ≫ secondProj Y L₁ L₂ =
      secondProj Y' ((Scheme.Modules.pullback g).obj L₁)
          ((Scheme.Modules.pullback g).obj L₂) ≫ totalSpaceBaseChange g L₂ :=
  Limits.pullback.lift_snd _ _ _

include h₁ h₂ in
/-- **The canonical morphism of ambient spaces lies over `g`.** -/
theorem ambientBaseChange_comp :
    ambientBaseChange Y L₁ L₂ g ≫ totalProj Y L₁ L₂ =
      totalProj Y' ((Scheme.Modules.pullback g).obj L₁)
          ((Scheme.Modules.pullback g).obj L₂) ≫ g := by
  rw [totalProj, ← Category.assoc, ambientBaseChange_comp_firstProj, Category.assoc,
    totalSpaceBaseChange_comp_lineBundleProj, ← Category.assoc]
  rfl

/-- A point of a line bundle and a point of `Y'` agreeing over `Y` lift uniquely to a point of the
base-changed line bundle. -/
private theorem existsUnique_lift_lineBundle (L : Y.Modules)
    [AlgebraicGeometry.SheafOfModules.IsInvertible Y.sheaf.obj Y.ringCatSheaf.property L]
    {W : Scheme.{u}} (b : W ⟶ lineBundleSpace Y L) (a : W ⟶ Y')
    (hab : b ≫ lineBundleProj Y L = a ≫ g) :
    ∃! m : W ⟶ lineBundleSpace Y' ((Scheme.Modules.pullback g).obj L),
      m ≫ totalSpaceBaseChange g L = b ∧
        m ≫ lineBundleProj Y' ((Scheme.Modules.pullback g).obj L) = a :=
  let h := isPullback_totalSpaceBaseChange g L
  ⟨h.lift b a hab, ⟨h.lift_fst _ _ hab, h.lift_snd _ _ hab⟩, fun _ hm =>
    h.hom_ext (by rw [hm.1, h.lift_fst]) (by rw [hm.2, h.lift_snd])⟩

include h₁ h₂ in
/-- **A point of the ambient space and a point of `Y'` agreeing over `Y` lift uniquely to a point
of the base-changed ambient space.** -/
theorem existsUnique_lift_ambient {W : Scheme.{u}} (b : W ⟶ totalSpace Y L₁ L₂) (a : W ⟶ Y')
    (hab : b ≫ totalProj Y L₁ L₂ = a ≫ g) :
    ∃! m : W ⟶ totalSpace Y' ((Scheme.Modules.pullback g).obj L₁)
        ((Scheme.Modules.pullback g).obj L₂),
      m ≫ ambientBaseChange Y L₁ L₂ g = b ∧
        m ≫ totalProj Y' ((Scheme.Modules.pullback g).obj L₁)
          ((Scheme.Modules.pullback g).obj L₂) = a := by
  obtain ⟨m₁, ⟨hm₁, hm₁'⟩, hu₁⟩ := existsUnique_lift_lineBundle Y g L₁ (b ≫ firstProj Y L₁ L₂) a
    (by rw [Category.assoc]; exact hab)
  obtain ⟨m₂, ⟨hm₂, hm₂'⟩, hu₂⟩ := existsUnique_lift_lineBundle Y g L₂ (b ≫ secondProj Y L₁ L₂) a
    (by rw [Category.assoc, secondProj_comp]; exact hab)
  have key : ∀ k, k ≫ ambientBaseChange Y L₁ L₂ g = b →
      k ≫ totalProj Y' ((Scheme.Modules.pullback g).obj L₁)
        ((Scheme.Modules.pullback g).obj L₂) = a →
      k ≫ firstProj Y' ((Scheme.Modules.pullback g).obj L₁)
          ((Scheme.Modules.pullback g).obj L₂) = m₁ ∧
        k ≫ secondProj Y' ((Scheme.Modules.pullback g).obj L₁)
          ((Scheme.Modules.pullback g).obj L₂) = m₂ := fun k hb ha =>
    ⟨hu₁ _ ⟨by rw [Category.assoc, ← ambientBaseChange_comp_firstProj, ← Category.assoc, hb],
        by rw [Category.assoc]; exact ha⟩,
      hu₂ _ ⟨by rw [Category.assoc, ← ambientBaseChange_comp_secondProj, ← Category.assoc, hb],
        by rw [Category.assoc, secondProj_comp]; exact ha⟩⟩
  obtain ⟨M, hMf, hMs⟩ : ∃ M : W ⟶ totalSpace Y' ((Scheme.Modules.pullback g).obj L₁)
        ((Scheme.Modules.pullback g).obj L₂),
      M ≫ firstProj Y' ((Scheme.Modules.pullback g).obj L₁)
          ((Scheme.Modules.pullback g).obj L₂) = m₁ ∧
        M ≫ secondProj Y' ((Scheme.Modules.pullback g).obj L₁)
          ((Scheme.Modules.pullback g).obj L₂) = m₂ :=
    ⟨Limits.pullback.lift m₁ m₂ (hm₁'.trans hm₂'.symm), Limits.pullback.lift_fst _ _ _,
      Limits.pullback.lift_snd _ _ _⟩
  have hM : M ≫ totalProj Y' ((Scheme.Modules.pullback g).obj L₁)
      ((Scheme.Modules.pullback g).obj L₂) = a := by
    rw [totalProj, ← Category.assoc, hMf, hm₁']
  refine ⟨M, ⟨?_, hM⟩, fun m ⟨hb, ha⟩ => ?_⟩
  · refine totalSpace_hom_ext Y L₁ L₂ ?_ ?_
    · rw [Category.assoc, ambientBaseChange_comp_firstProj, ← Category.assoc, hMf, hm₁]
    · rw [Category.assoc, ambientBaseChange_comp_secondProj, ← Category.assoc, hMs, hm₂]
  · obtain ⟨h₁, h₂⟩ := key m hb ha
    exact totalSpace_hom_ext _ _ _ (h₁.trans hMf.symm) (h₂.trans hMs.symm)

include h₁ h₂ in
/-- **The ambient space of the construction of [Stacks, Tag 0F97] commutes with arbitrary base
change**: the square with sides the canonical morphism of ambient spaces, the two structure
morphisms and `g` is cartesian, with no hypothesis on `g`, `Y` or `Y'`. -/
theorem isPullback_ambientBaseChange :
    IsPullback (ambientBaseChange Y L₁ L₂ g)
      (totalProj Y' ((Scheme.Modules.pullback g).obj L₁) ((Scheme.Modules.pullback g).obj L₂))
      (totalProj Y L₁ L₂) g :=
  IsPullback.of_isLimit' ⟨ambientBaseChange_comp Y L₁ L₂ g⟩
    (PullbackCone.IsLimit.mk (ambientBaseChange_comp Y L₁ L₂ g)
      (fun c => (existsUnique_lift_ambient Y L₁ L₂ g c.fst c.snd c.condition).choose)
      (fun c => (existsUnique_lift_ambient Y L₁ L₂ g c.fst c.snd c.condition).choose_spec.1.1)
      (fun c => (existsUnique_lift_ambient Y L₁ L₂ g c.fst c.snd c.condition).choose_spec.1.2)
      (fun c m hb ha =>
        (existsUnique_lift_ambient Y L₁ L₂ g c.fst c.snd c.condition).choose_spec.2 m ⟨hb, ha⟩))

end Stacks.Chow.TensorZeroScheme

end
