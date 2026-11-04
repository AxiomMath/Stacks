module

public import StacksFrontier.AlgebraicGeometry.ProjBundleInverseBaseChange.Basic

/-!
# The evaluation normalisation of the comparison of two tensor inverses

`Stacks.TensorPowers.TensorInverse.invIso h k` is the five-step chain comparing the inverse
objects of two two-sided tensor inverses `h` and `k` of one object `L`. It was *constructed* in
`StacksFrontier.AlgebraicGeometry.ProjBundleInverseBaseChange.Basic` and nothing said how it
interacts with the four isomorphisms it is built from, so nothing could be said about where it
sends anything. **This file supplies that compatibility**, and reads it at the one place the
development uses the chain: `Stacks.ProjBundleInverseBaseChange.inverseQuotientBaseChangeIso`,
Tag 0B3V's base change of the inverse of an invertible module.

The compatibility is the triangle on the triple product `(h⁻¹ ⊗ L) ⊗ k⁻¹`. There are two ways to
contract it to a single factor: contract the left pair by the right trivialisation
`h.mulIso' : h⁻¹ ⊗ L ≅ 𝟙` and cancel the unit, landing in `k⁻¹`; or reassociate, contract the
right pair by the left trivialisation `k.mulIso : L ⊗ k⁻¹ ≅ 𝟙` and cancel the unit, landing in
`h⁻¹`. The two differ exactly by `invIso h k`:

`(h.mulIso' ▷ k⁻¹) ≫ λ ≫ (invIso h k)⁻¹ = α ≫ (h⁻¹ ◁ k.mulIso) ≫ ρ`.

## Main results

* `Stacks.TensorPowers.TensorInverse.invIso_hom_evaluation` and
  `Stacks.TensorPowers.TensorInverse.invIso_inv_evaluation`: **the comparison of two two-sided
  tensor inverses is compatible with the two trivialisations that build it**, in the forward and
  the backward direction.
* `Stacks.ProjBundleInverseBaseChange.inverseQuotientBaseChangeIso_evaluation`: that
  compatibility at Tag 0B3V's base change of the inverse, with both trivialisations written out:
  the pullback one through [Stacks, Tag 01CD] and the unit comparison, the target one through the
  given comparison `hL` of the two invertible modules.

## Route

There is less here than the name "monoidal algebra" suggests, and the measurement is worth
recording because it was not obvious in advance: the triangle is a *rearrangement of the
definition* of `invIso`, not a consequence of the coherence axioms. The chain's first three steps
`ρ⁻¹`, `h⁻¹ ◁ k.mulIso⁻¹`, `α⁻¹` form an isomorphism, and cancelling it against `invIso h k`
leaves the last two steps. So neither the pentagon nor the triangle identity is used, and in
particular no braiding and no symmetry is
involved; it holds in an arbitrary monoidal category. What the triangle buys is not depth but
*direction*: the definition reads `invIso` out of the trivialisations, while the triangle reads
the trivialisations against `invIso`, which is the form a computation on a section can use.

No normalisation of `invIso` beyond this one is claimed. Nothing here says that `invIso h h` is
the identity, or that `invIso` is transitive in its two arguments; both would need a relation
between `mulIso` and `mulIso'`, which `Stacks.TensorPowers.TensorInverse` does not carry — see
the module documentation of
`StacksFrontier.AlgebraicGeometry.TensorPowerAssoc.IntegerSucc`, which takes that relation as the
explicit hypothesis `hs`.

## Implementation notes

The scheme-level statement supplies both `Stacks.TensorPowers.TensorInverse` arguments
explicitly. Leaving either to unification exhausts the heartbeat budget inside
`isDefEq`: the two tensor inverses of `σ^*𝒪(1)` that
`Stacks.ProjBundleInverseBaseChange.inverseQuotientBaseChangeIso` is built from are large terms
over a `Scheme.Modules` restriction, and matching them up to definitional unfolding is
expensive. With both supplied, the only reduction left is the projection of a
structure instance, and the proof is the general triangle applied to them.

## Not done here

**The constraints are not read on a section here, but they are read on one now**, in
`StacksFrontier.AlgebraicGeometry.ProjBundleInverseBaseChange.Sections`. Turning the triangle into a
statement about a section of `(L')^{⊗ -1}` needs the left unitor, the right unitor and the
associator of `Stacks.SheafInternalHom.monoidalCategory` evaluated on a product section; all
three are in `StacksFrontier.Algebra.Category.ModuleCat.Sheaf.MonoidalLocalizedSections`, where the
associator and the two whiskerings transfer from `Stacks.SheafOfModules.monoidalCategory` by
`rfl`, the choice of unit object entering only the unitors, and the two unitors cross by
`CategoryTheory.Localization.Monoidal.rightUnitor_hom_eq_of_unitIso` and its left companion. The
four isomorphisms the triangle's two trivialisations are built from have section formulas too —
`Stacks.ProjBundleInverseBaseChange.negOneMulIso_hom_tensorSectionsAt` and its three companions.
`Stacks.ProjBundleInverseBaseChange.invIso_inv_val_app` is the triangle read against them: the
comparison carries `c` back to `a` as soon as two pairings against `g^*L` are `1`.

**The hypothesis `hw` of
`Stacks.ProjectiveBundleConormal.conormalCanonicalMap_val_app_tensorSectionsAt` is discharged, but
not here.** It asks that the section `(inverseTwistBaseChangeIso E Q e)⁻¹ w` of `σ^*𝒪(-1)` over
`W` be `AlgebraicGeometry.Scheme.Modules.pullbackSection` of a section `w₀` of `𝒪(-1)` over an
open `V` of `𝐏(ℰ)` with `V ≤ π⁻¹W` and `W ≤ σ⁻¹V`. The open is a parameter there precisely
because over the full preimage the hypothesis would be empty: `π_*𝒪(-1) = 0` once `ℰ` has rank at
least two, so the only `w₀` on `π⁻¹W` is `0` and `hw` would pin `w` to `0` instead of pinning the
comparison. On a chart of `𝐏(ℰ)` the twist is trivial and `w₀` exists, so the shape is
satisfiable. The comparison is read on a section by
`Stacks.ProjBundleInverseBaseChange.invIso_inv_val_app`, and
`Stacks.ProjBundleInverseBaseChange.inverseTwistBaseChangeIso_inv_val_app` supplies its two
pairing hypotheses with `a` taken to be the pullback of `w₀`; both live in
`StacksFrontier.AlgebraicGeometry.ProjBundleInverseBaseChange.Sections`.

## References

* [Stacks Project, Tag 0B3V](https://stacks.math.columbia.edu/tag/0B3V)
* [Stacks Project, Tag 01CU](https://stacks.math.columbia.edu/tag/01CU)
* [Stacks Project, Tag 01CD](https://stacks.math.columbia.edu/tag/01CD)
-/

@[expose] public noncomputable section

universe v u

open CategoryTheory MonoidalCategory Limits AlgebraicGeometry

namespace Stacks.TensorPowers

variable {C : Type u} [Category.{v} C] [MonoidalCategory C]

/-- **The comparison of two two-sided tensor inverses is compatible with the two trivialisations
that build it.** On the triple product `(h⁻¹ ⊗ L) ⊗ k⁻¹`, contracting the left pair by
`h.mulIso'` and cancelling the unit agrees, after `Stacks.TensorPowers.TensorInverse.invIso`,
with reassociating, contracting the right pair by `k.mulIso` and cancelling the unit.

This is the rearrangement of the definition of `invIso` that cancels its first three steps; it
uses no coherence axiom, and in particular no braiding. -/
public theorem TensorInverse.invIso_hom_evaluation {L : C} (h k : TensorInverse L) :
    (α_ h.inv L k.inv).hom ≫ h.inv ◁ k.mulIso.hom ≫ (ρ_ h.inv).hom ≫
        (TensorInverse.invIso h k).hom =
      h.mulIso'.hom ▷ k.inv ≫ (λ_ k.inv).hom := by
  simp [TensorInverse.invIso]

/-- **`Stacks.TensorPowers.TensorInverse.invIso_hom_evaluation` in the backward direction**: the
inverse of the comparison carries the contraction of the left pair by `h.mulIso'` to the
contraction of the right pair by `k.mulIso`. This is the direction a section of `k.inv` is read
through. -/
public theorem TensorInverse.invIso_inv_evaluation {L : C} (h k : TensorInverse L) :
    h.mulIso'.hom ▷ k.inv ≫ (λ_ k.inv).hom ≫ (TensorInverse.invIso h k).inv =
      (α_ h.inv L k.inv).hom ≫ h.inv ◁ k.mulIso.hom ≫ (ρ_ h.inv).hom := by
  simp [TensorInverse.invIso]

end Stacks.TensorPowers

namespace Stacks.ProjBundleInverseBaseChange

open Stacks.SheafOfModules.TensorSheafification Stacks.TensorPowers Stacks.SheafOfModules
open Stacks.SheafOfModules.TensorPower
open Stacks.SheafInternalHom (isSheaf_structureRingPresheaf)

attribute [local instance] Stacks.SheafInternalHom.monoidalCategory

section Scheme

variable {X X' : Scheme.{u}} (g : X' ⟶ X) (L : Mods X)
  [Stacks.SheafOfModules.IsInvertible X.presheaf (isSheaf_structureRingPresheaf X) L]

/-- **The evaluation normalisation of Tag 0B3V's base change of the inverse.** For
`g : X' ⟶ X`, an invertible `L` on `X`, an invertible `L'` on `X'` and a comparison
`hL : L' ≅ g^*L`, the comparison
`Stacks.ProjBundleInverseBaseChange.inverseQuotientBaseChangeIso` of `g^*(L^{⊗ -1})` with
`(L')^{⊗ -1}` is compatible with the two evaluation pairings against `g^*L` that define it:

* on the left, `g^*(L^{⊗ -1}) ⊗ g^*L ≅ 𝟙`, the pullback of the right trivialisation
  `Stacks.ProjBundleInverseBaseChange.negOneMulIso` of Tag 01CU through the comparison of
  [Stacks, Tag 01CD] and the pullback of the unit;
* on the right, `g^*L ⊗ (L')^{⊗ -1} ≅ 𝟙`, the left trivialisation
  `Stacks.ProjBundleInverseBaseChange.negOneMulIso'` of `L'` precomposed with `hL`.

This is `Stacks.TensorPowers.TensorInverse.invIso_inv_evaluation` at the two tensor inverses of
`g^*L` that the comparison is built from. It is the normalisation recorded as missing in the
"Not done here" of
`StacksFrontier.AlgebraicGeometry.ProjBundleInverseBaseChange.Basic`; what it does *not* yet do is
compute on a section, for which see this module's own "Not done here". -/
public theorem inverseQuotientBaseChangeIso_evaluation (L' : Mods X')
    [Stacks.SheafOfModules.IsInvertible X'.presheaf (isSheaf_structureRingPresheaf X') L']
    (hL : L' ≅ (pullbackFunctor g).obj L) :
    ((pullbackTensorIso g
            (tensorPower X.presheaf (isSheaf_structureRingPresheaf X) L (-1)) L).inv ≫
          (pullbackFunctor g).map
            (negOneMulIso X.presheaf (isSheaf_structureRingPresheaf X) L).hom ≫
          (pullbackUnitMonoidalIso g).hom) ▷
          tensorPower X'.presheaf (isSheaf_structureRingPresheaf X') L' (-1) ≫
        (λ_ (tensorPower X'.presheaf (isSheaf_structureRingPresheaf X') L' (-1))).hom ≫
          (inverseQuotientBaseChangeIso g L L' hL).inv =
      (α_ ((pullbackFunctor g).obj
            (tensorPower X.presheaf (isSheaf_structureRingPresheaf X) L (-1)))
          ((pullbackFunctor g).obj L)
          (tensorPower X'.presheaf (isSheaf_structureRingPresheaf X') L' (-1))).hom ≫
        (pullbackFunctor g).obj
            (tensorPower X.presheaf (isSheaf_structureRingPresheaf X) L (-1)) ◁
            (hL.inv ▷ tensorPower X'.presheaf (isSheaf_structureRingPresheaf X') L' (-1) ≫
              (negOneMulIso' X'.presheaf (isSheaf_structureRingPresheaf X') L').hom) ≫
          (ρ_ ((pullbackFunctor g).obj
            (tensorPower X.presheaf (isSheaf_structureRingPresheaf X) L (-1)))).hom :=
  TensorInverse.invIso_inv_evaluation
    (pullbackTensorInverse g L
      (negOneTensorInverse X.presheaf (isSheaf_structureRingPresheaf X) L))
    (TensorInverse.ofIso hL.symm
      (negOneTensorInverse X'.presheaf (isSheaf_structureRingPresheaf X') L'))

end Scheme

end Stacks.ProjBundleInverseBaseChange

end
