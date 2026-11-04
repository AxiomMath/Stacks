module

public import StacksFrontier.AlgebraicGeometry.Divisors.ZeroSchemeFactorization
public import StacksFrontier.AlgebraicGeometry.Properties.ReducedClosedSubscheme

/-!
# A point with values in a field lies on a closed subscheme as soon as its image does

Let `K` be a field. The spectrum of `K` is a reduced scheme with exactly one point, so a
morphism `g : Spec K ⟶ X` factors through the closed subscheme cut out by an ideal sheaf `I` on
`X` precisely when the single point `g(⋆)` of its image lies in the support of `I`. This is the
scheme-theoretic content hiding behind the phrase "the point lies on the closed subscheme": for a
general source the set-theoretic condition is not enough, and what makes it enough here is that
`Spec K` is reduced, so that the factorization criterion of [Stacks, Tag 0356] applies.

Specializing the ideal sheaf to the zero scheme of a global section of an invertible module gives
the form the Bertini step of [Stacks, Tag 0FH7] needs: a `K`-valued point at which a section
vanishes factors through the divisor of that section. The hypothesis actually available there is
not the vanishing of the section at the one point but its vanishing on a closed subscheme `V(I)`
through which the point passes, which is why that is the hypothesis carried below.

## Main results

* `AlgebraicGeometry.Scheme.IdealSheafData.exists_lift_subschemeι_iff_mem_support`: a `K`-valued
  point factors through a closed subscheme exactly when the image of the point of `Spec K` lies
  in its support.
* `AlgebraicGeometry.exists_lift_zeroScheme_of_mem_support_of_pullbackGlobalSections_eq_zero`: a
  `K`-valued point of `V(I)` factors through the zero scheme of a section that vanishes on
  `V(I)`.

## Implementation notes

The point of `Spec K` is spelled `IsLocalRing.closedPoint K`, as elsewhere in the repository;
that it is the only one is `Unique (Spec (.of K))` for a field, so the inclusion of the range of
`g` in the support reduces to one membership. Nothing here is specific to the closed point: any
point of `Spec K` would do, and `Subsingleton.elim` is what says so.

That a section vanishing on `V(I)` has `V(I)` inside its divisor is the maximality half of
[Stacks, Tag 02OR], `AlgebraicGeometry.zeroScheme_isGreatest_vanishingClosedSubscheme`, read
through the order dual in which it is stated: geometric inclusion of closed subschemes is the
reverse of the order on ideal sheaves. Supports are then antitone in the ideal sheaf.

## References

* [Stacks Project, Tag 02OR](https://stacks.math.columbia.edu/tag/02OR)
* [Stacks Project, Tag 0356](https://stacks.math.columbia.edu/tag/0356)
-/

@[expose] public section

open CategoryTheory TopologicalSpace Opposite

universe u

namespace AlgebraicGeometry

/-- **A point with values in a field lies on a closed subscheme as soon as its image does.** A
morphism `g : Spec K ⟶ X` from the spectrum of a field factors through the closed subscheme cut
out by `I` exactly when the image of the point of `Spec K` lies in the support of `I`.

The spectrum of a field is reduced, so this is the factorization criterion of
[Stacks, Tag 0356], `exists_lift_subschemeι_iff_range_subset_support`, whose hypothesis is the
inclusion of the whole range of `g` in the support; the spectrum of a field has a single point,
so that inclusion is the one membership. -/
theorem Scheme.IdealSheafData.exists_lift_subschemeι_iff_mem_support {K : Type u} [Field K]
    {X : Scheme.{u}} (I : X.IdealSheafData) (g : Spec (.of K) ⟶ X) :
    (∃ h : Spec (.of K) ⟶ I.subscheme, h ≫ I.subschemeι = g) ↔
      g (IsLocalRing.closedPoint K) ∈ I.support := by
  rw [Scheme.IdealSheafData.exists_lift_subschemeι_iff_range_subset_support]
  refine ⟨fun h => h ⟨_, rfl⟩, fun h => ?_⟩
  rintro _ ⟨y, rfl⟩
  rw [Subsingleton.elim y (IsLocalRing.closedPoint K)]
  exact h

/-- **A point with values in a field at which a section vanishes factors through the divisor of
that section.** Let `L` be an invertible module on `X`, let `s` be a global section of `L` whose
restriction to the closed subscheme `V(I)` is zero, and let `g : Spec K ⟶ X` be a point with
values in a field whose image lies in the support of `I`. Then `g` factors through the zero
scheme of `s`.

The two steps are: `V(I)` lies inside the divisor of `s`, which is the maximality half of
[Stacks, Tag 02OR], so the support of `I` lies inside the support of the divisor; and a point
with values in a field whose image lies in that support factors through the divisor, which is
`Scheme.IdealSheafData.exists_lift_subschemeι_iff_mem_support`. -/
theorem exists_lift_zeroScheme_of_mem_support_of_pullbackGlobalSections_eq_zero
    {K : Type u} [Field K] (X : Scheme.{u}) (L : X.Modules)
    [SheafOfModules.IsInvertible X.sheaf.obj X.ringCatSheaf.property L] (s : Γ(L, ⊤))
    (I : X.IdealSheafData) (hs : pullbackGlobalSections I.subschemeι L s = 0)
    (g : Spec (.of K) ⟶ X) (hg : g (IsLocalRing.closedPoint K) ∈ I.support) :
    ∃ h : Spec (.of K) ⟶ (zeroScheme X L s).subscheme,
      h ≫ (zeroScheme X L s).subschemeι = g :=
  (Scheme.IdealSheafData.exists_lift_subschemeι_iff_mem_support _ g).mpr
    (Scheme.IdealSheafData.support_antitone
      (OrderDual.toDual_le_toDual.mp
        ((zeroScheme_isGreatest_vanishingClosedSubscheme X L s).2 hs)) hg)

end AlgebraicGeometry

end
