module

public import StacksFrontier.AlgebraicGeometry.Morphisms.Fibres.BertiniJacobianDivisor

/-!
# The Jacobian criterion for a divisor, globalised

`AlgebraicGeometry.smoothAt_zeroScheme_of_notMem_maximalSqSmul_of_perfectField` is the Jacobian
criterion at **one** point: over a perfect field, if `𝒪_{X,y}` is regular and the
germ of `s` at `y` avoids `𝔪_y²ℒ_y`, then `Z(s)` is smooth over `k` at the points of `Z(s)`
lying over `y`. Smoothness of a morphism is smoothness at every point of its source
(`InfinitesimalLifting.smooth_iff_forall_smoothAt`), so the criterion imposed at every point of
`|Z(s)|` gives smoothness of `Z(s)` over `k` outright. This module records that step, and its
form in the standing situation of the Bertini theorems, where the regularity obligation is
discharged rather than assumed: over **any** field a smooth `X` has regular local rings at all of
its points (`AlgebraicGeometry.isRegularLocalRing_stalk_of_smooth_over_field`), so the perfection
of `k` is the only hypothesis on the field that either statement below carries.

This is the step the Bertini part of [Stacks, Tag 0FH7] needs in order to read its
general-position conditions as smoothness of `H_v` on the whole of `X`: the smoothness conclusion
of [Stacks, Tag 0FD6] available for the linear system of sections vanishing on `Z` is a statement
about the open complement `X ∖ Z`, because that system does not generate `ℒ ^⊗ n` at the points
of `Z` and so hypothesis (2) of that tag fails for it there. What the two statements below supply
is the other direction of the trade: a hypothesis purely about germs, at every point of `|H_w|`,
yields smoothness of `H_w` over `k` on the whole of `X` with nothing assumed about `X ∖ Z`.

## Main results

* `AlgebraicGeometry.smooth_zeroScheme_of_forall_notMem_maximalSqSmul`: **the zero scheme of a
  section which nowhere vanishes to second order is smooth over a perfect field**,
  when every local ring of the ambient scheme is regular.
* `Stacks.Bertini.FamilyDivisors.smooth_divisor_of_forall_notMem_maximalSqSmul`: **the same for
  the divisor `H_w` of a vector of the linear system**, in the standing situation of
  [Stacks, Tag 0G47] with `X` smooth over a perfect field. Here the regularity of
  the local rings of `X` is not a hypothesis: it follows from the smoothness of `X` over `k`.

## Implementation notes

The section of the general statement is taken as an element `t` of `Γ(ℒ, ⊤)` rather than as a
`PresheafOfModules.sections`, which is the shape
`Stacks.Bertini.FamilyDivisors.divisor` is built at, and `t` is a *variable* so that the passage
to the `PresheafOfModules.sections` spelling the pointwise criterion is stated at can be made by
`subst` on `Stacks.SheafOfModules.sectionsOfTopOfRingSheaf_eval_top`. That is the same device
`AlgebraicGeometry.isRegularLocalRing_stalk_subscheme_of_eq_comap_zeroScheme` uses, and it is used
for the same reason: that equation is not a `rfl`, so rewriting with it inside a term whose type
mentions the ring sheaf of `X` does not typecheck, and no reducibility attribute on a ring-sheaf
spelling is wanted to make it.

`Stacks.Bertini.FamilyDivisors.divisor` is by definition the zero scheme of the section of the
vector, so the specialisation needs no transport; only the instance
`LocallyOfFiniteType (H_w ↪ X → Spec k)` is supplied by hand, as the composite of a closed
immersion with the structure morphism, because instance search does not find it in the presence
of the germ hypothesis.

The hypothesis is imposed at the points of `|H_w|` and not at every point of `X`. Off `|H_w|` it
holds for trivial reasons — the germ there generates the stalk — but only the points of `|H_w|`
are in the range of `Scheme.IdealSheafData.subschemeι`, so that is what the proof consumes and
what the statement asks for.

No `@[stacks]` attribute is attached: this is a step inside the proofs of [Stacks, Tag 0FD6] and
[Stacks, Tag 0FH7], asserted by neither tag.

## References

* [Stacks Project, Tag 0FD6](https://stacks.math.columbia.edu/tag/0FD6)
* [Stacks Project, Tag 0FH7](https://stacks.math.columbia.edu/tag/0FH7)
* [Stacks Project, Tag 0G47](https://stacks.math.columbia.edu/tag/0G47)
* [Stacks Project, Tag 01V5](https://stacks.math.columbia.edu/tag/01V5)
-/

@[expose] public noncomputable section

open AlgebraicGeometry CategoryTheory TopologicalSpace Opposite
open Stacks.ImmersionEvaluationSurjective

universe u

namespace AlgebraicGeometry

open Stacks.Divisors

variable {X : Scheme.{u}} (L : X.Modules)
  [SheafOfModules.IsInvertible X.sheaf.obj X.ringCatSheaf.property L]

/-- **The Jacobian criterion for a zero scheme, globalised.** Let `ℒ` be an invertible module on
a scheme `X` all of whose local rings are regular, let `t` be a global section of `ℒ`, and let the
zero scheme `Z(t)` be a scheme locally of finite type over a perfect field `k`. If
the germ of `t` at every point of the support of `Z(t)` avoids `𝔪_y²ℒ_y`, then `Z(t)` is smooth
over `k`.

A morphism is smooth exactly when it is smooth at every point of its source
(`InfinitesimalLifting.smooth_iff_forall_smoothAt`), and at a point `z` of `Z(t)` the point
`y = ι(z)` of `X` lies in the support, so the pointwise criterion
`AlgebraicGeometry.smoothAt_zeroScheme_of_notMem_maximalSqSmul_of_perfectField` applies there. -/
theorem smooth_zeroScheme_of_forall_notMem_maximalSqSmul {k : Type u} [Field k] [PerfectField k]
    (t : Γ(L, ⊤)) (g : (zeroScheme X L t).subscheme ⟶ Spec (.of k)) [LocallyOfFiniteType g]
    (hreg : ∀ y : X, IsRegularLocalRing (X.presheaf.stalk y))
    (ht : ∀ y : X, y ∈ (zeroScheme X L t).support →
      (L.presheaf.Γgerm y).hom t ∉ maximalSqSmul L y) :
    Smooth g := by
  obtain ⟨s, hs⟩ : ∃ s : L.sections, s.eval (op ⊤) = t :=
    ⟨Stacks.SheafOfModules.sectionsOfTopOfRingSheaf L t,
      Stacks.SheafOfModules.sectionsOfTopOfRingSheaf_eval_top L t⟩
  subst hs
  refine InfinitesimalLifting.smooth_of_forall_smoothAt _ fun z => ?_
  have := hreg ((zeroScheme X L (s.eval (op ⊤))).subschemeι z)
  refine smoothAt_zeroScheme_of_notMem_maximalSqSmul_of_perfectField L s g z (ht _ ?_)
  have hrange : (zeroScheme X L (s.eval (op ⊤))).subschemeι z ∈
      Set.range (zeroScheme X L (s.eval (op ⊤))).subschemeι := Set.mem_range_self z
  rwa [Scheme.IdealSheafData.range_subschemeι] at hrange

end AlgebraicGeometry

namespace Stacks.Bertini.FamilyDivisors

variable (D : FamilyDivisors.{u, u})

/-- **The divisor of a vector of the linear system whose section nowhere vanishes to second order
is smooth over the base field.** In the standing situation of [Stacks, Tag 0G47] with `X` smooth
over a perfect field `k`, if the germ of `ψ(w)` at every point of `|H_w|` avoids
`𝔪_y²ℒ_y`, then `H_w` is smooth over `k`.

This is the general-position criterion of the Bertini step of [Stacks, Tag 0FH7] in its global
form. The regularity of the local rings of `X`, which the ambient statement
`AlgebraicGeometry.smooth_zeroScheme_of_forall_notMem_maximalSqSmul` assumes, is here a
consequence of the hypotheses: a scheme smooth over any field has regular local rings at all of
its points (`AlgebraicGeometry.isRegularLocalRing_stalk_of_smooth_over_field`), and that step
needs nothing of the field. So the only input left is
the condition on the germs, which is the one the general-position opens of
`Stacks.Bertini.FamilyDivisors.exists_nonempty_opens_notMem_maximalSqSmul_constCoeffSection`
produce — there at a single closed point, and here needed at every point of `|H_w|`. Those opens
do need `k` algebraically closed, so the perfection assumed here is not the weakest hypothesis
under which the *conclusion* is reached in the Bertini argument; it is the weakest under which
this implication holds. -/
theorem smooth_divisor_of_forall_notMem_maximalSqSmul [PerfectField D.k] [Smooth D.toBase]
    (w : D.V)
    (hgerm : ∀ y : D.X, y ∈ D.divisorSet w →
      (D.L.presheaf.Γgerm y).hom (D.sectionOf w) ∉ maximalSqSmul D.L y) :
    Smooth ((D.divisor w).subschemeι ≫ D.toBase) := by
  have himm : LocallyOfFiniteType (D.divisor w).subschemeι := inferInstance
  have hbase : LocallyOfFiniteType D.toBase := inferInstance
  have : LocallyOfFiniteType
      ((Stacks.Divisors.zeroScheme D.X D.L (D.sectionOf w)).subschemeι ≫ D.toBase) :=
    MorphismProperty.IsStableUnderComposition.comp_mem _ _ himm hbase
  exact AlgebraicGeometry.smooth_zeroScheme_of_forall_notMem_maximalSqSmul D.L (D.sectionOf w)
    ((Stacks.Divisors.zeroScheme D.X D.L (D.sectionOf w)).subschemeι ≫ D.toBase)
    (AlgebraicGeometry.isRegularLocalRing_stalk_of_smooth_over_field D.toBase) hgerm

end Stacks.Bertini.FamilyDivisors

end
