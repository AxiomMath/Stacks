module

public import StacksFrontier.AlgebraicGeometry.ComponentMultiplicity.ZeroDimensional
public import StacksFrontier.AlgebraicGeometry.EulerCharAdditivity.Basic
public import StacksFrontier.AlgebraicGeometry.EulerCharIso.Basic
public import StacksFrontier.AlgebraicGeometry.FundamentalGroup.AlgebraicClosureBaseChange
public import StacksFrontier.AlgebraicGeometry.Variety.Bertini.VanishingSystemTwoPoints
public import StacksFrontier.AlgebraicGeometry.Variety.NumericalIntersections.AsymptoticRiemannRoch

/-!
# The linear conditions imposed by two closed points are those imposed on the structure sheaf

The last hypothesis of the Bertini step of [Stacks, Tag 0FH7] not supplied by
`StacksFrontier.AlgebraicGeometry.Variety.Bertini.VanishingSystemTwoPoints` is the bound
`dim_k Γ(Z, ℒ ^⊗ n|_Z) ≤ m`, where `Z = V(I)` is the closed subscheme supported on the two
closed points. This file removes the twist from that dimension: on such a `Z` the restriction
`ℒ ^⊗ n|_Z` is **trivial**, so the dimension to be bounded is that of `Γ(Z, 𝒪_Z)`, with no module
left in it.

The reason is that `Z` is a *discrete* space. It is finite over `k`
(`Stacks.SectionsVanishingOnSubscheme.isFinite_subschemeι_comp_of_coe_support_eq_pair`), a scheme
finite over a field has discrete underlying space
(`AlgebraicGeometry.discreteTopology_of_isFinite_over_field`), and an invertible module on a
scheme with discrete space is isomorphic to the structure sheaf
(`Stacks.SheafOfModules.nonempty_iso_unit_of_discreteTopology`: every point is open, so clause 2
of [Stacks, Tag 0B8M] trivializes it at each point and the sections glue over the pairwise
disjoint cover by points). The dimension then transports along that isomorphism through degree-zero
cohomology.

## Main results

* `finrank_subschemeSections_eq_finrank_globalSections_of_coe_support_eq_pair`:
  **`dim_k Γ(Z, ℒ ^⊗ n|_Z) = dim_k Γ(Z, 𝒪_Z)`** for `Z` the closed subscheme cut out by an ideal
  sheaf whose support is two closed points, `X` proper over `k` and `ℒ` invertible.

## Implementation notes

**The chain of results, in order.** `Stacks.Bertini.finrank_globalSections_eq` moves the
left side into the `AlgebraicGeometry.globalSectionsOverField` spelling;
`AlgebraicGeometry.finrank_globalSectionsOverField` reads it as degree-zero cohomology;
`AlgebraicGeometry.finrank_cohomologyOverField_eq_of_iso` spends the trivialization; and
`AlgebraicGeometry.finrank_cohomologyOverField_zero_unit_eq_finrank_globalSections` brings the
structure-sheaf side back to `Γ(Z, ⊤)`.

**The `k`-algebra structure on `Γ(Z, 𝒪_Z)` is supplied inside the statement** as a `letI`, being
the one the structure morphism `Z ⟶ Spec k` induces and so depending on that morphism rather than
on the ring alone. It is the same spelling that
`AlgebraicGeometry.finrank_cohomologyOverField_zero_unit_eq_finrank_globalSections` and
`AlgebraicGeometry.finrank_globalSections_eq_finsum_finrank_stalk` use, so no transport is needed
between them and the right side can be fed straight to the sum-over-stalks formula.

**What this leaves owed.** `dim_k Γ(Z, 𝒪_Z) = 2` is now a statement about the structure sheaf
alone, for which `AlgebraicGeometry.finrank_globalSections_eq_finsum_finrank_stalk` expresses the
left side as `∑_{z ∈ Z} dim_k 𝒪_{Z,z}`. Each term is `1` when `Z` is reduced and `k` is
algebraically closed — `AlgebraicGeometry.length_stalk_eq_one_of_isMax` at a maximal point of a
reduced scheme, every point of a discrete space being maximal, and
`AlgebraicGeometry.finrank_residueField_of_isClosed` for the residue degree — and the index set
has at most two elements because the range of `Z ⟶ X` is `{x, x'}`. The remaining friction is that
those two results supply the `Algebra k` structure on the residue field in two different
spellings, `IsLocalRing.ResidueField.algebra` over the stalk's algebra against
`((Scheme.ΓSpecIso _).inv ≫ p.appTop ≫ Z.Γevaluation z).hom.toAlgebra`, and identifying them is
the one step not yet done.

**The invertibility spellings.** `Stacks.SheafOfModules.nonempty_iso_unit_of_discreteTopology`
asks for `Stacks.SheafOfModules.IsInvertible`, which
`Stacks.InvertibleBridge.stacksIsInvertible_of_algebraicGeometryIsInvertible` supplies from the
`AlgebraicGeometry.SheafOfModules.IsInvertible` form; and that form on the pullback is found by
instance search once the invertibility of `ℒ ^⊗ n` on `X` is passed as an explicit term, the
device used in `StacksFrontier.AlgebraicGeometry.Variety.Bertini.VanishingSystemFiniteness` and in
`Stacks.SectionsVanishingOnSubscheme.ambientFamilyDivisors`.

No `@[stacks]` attribute is attached: this is an input of the Bertini reduction of
[Stacks, Tag 0FH7], not a clause of any tag. The trivialization it rests on is registered against
[Stacks, Tag 0B8M].

## References

* [Stacks Project, Tag 0AYT](https://stacks.math.columbia.edu/tag/0AYT)
* [Stacks Project, Tag 0B8M](https://stacks.math.columbia.edu/tag/0B8M)
* [Stacks Project, Tag 0FD5](https://stacks.math.columbia.edu/tag/0FD5)
* [Stacks Project, Tag 0FH7](https://stacks.math.columbia.edu/tag/0FH7)
-/

@[expose] public noncomputable section

open CategoryTheory AlgebraicGeometry Opposite TopologicalSpace
open Stacks.Ample

universe u

attribute [local instance] HasDerivedCategory.standard

namespace Stacks.SectionsVanishingOnSubscheme

variable (k : Type u) [Field k] {X : Scheme.{u}} (f : X ⟶ Spec (.of k))

/-- **The twisted sections of the closed subscheme on two closed points have the same dimension
as its untwisted ones**: `dim_k Γ(Z, ℒ ^⊗ n|_Z) = dim_k Γ(Z, 𝒪_Z)`.

`Z` is finite over `k` by
`Stacks.SectionsVanishingOnSubscheme.isFinite_subschemeι_comp_of_coe_support_eq_pair`, hence
discrete, hence carries no nontrivial invertible module
(`Stacks.SheafOfModules.nonempty_iso_unit_of_discreteTopology`); the dimension transports along
that isomorphism through degree-zero cohomology. So the bound
`dim_k Γ(Z, ℒ ^⊗ n|_Z) ≤ m` that the Bertini step of [Stacks, Tag 0FH7] assumes is a statement
about the structure sheaf of `Z` alone. -/
theorem finrank_subschemeSections_eq_finrank_globalSections_of_coe_support_eq_pair [IsProper f]
    (I : X.IdealSheafData) {x x' : X} (hx : IsClosed ({x} : Set X))
    (hx' : IsClosed ({x'} : Set X)) (hZ : (I.support : Set X) = {x, x'})
    {L : X.Modules} [IsInvertibleModule X L] (n : ℤ) :
    letI : Algebra k Γ(I.subscheme, ⊤) :=
      ((Scheme.ΓSpecIso (.of k)).inv ≫ (I.subschemeι ≫ f).appTop).hom.toAlgebra
    Module.finrank k (subschemeSections k f I (L := L) n) =
      Module.finrank k Γ(I.subscheme, ⊤) := by
  have : IsFinite (I.subschemeι ≫ f) :=
    isFinite_subschemeι_comp_of_coe_support_eq_pair k f I hx hx' hZ
  have : DiscreteTopology (I.subscheme : Type u) :=
    AlgebraicGeometry.discreteTopology_of_isFinite_over_field k (I.subschemeι ≫ f)
  have : SheafOfModules.IsInvertible X.sheaf.obj X.ringCatSheaf.property
      (tensorPowModule X L n) := (inferInstance : IsInvertibleModule X (tensorPowModule X L n))
  have : Stacks.SheafOfModules.IsInvertible I.subscheme.presheaf I.subscheme.ringCatSheaf.2
      ((Scheme.Modules.pullback I.subschemeι).obj (tensorPowModule X L n)) :=
    Stacks.InvertibleBridge.stacksIsInvertible_of_algebraicGeometryIsInvertible
  obtain ⟨e⟩ := Stacks.SheafOfModules.nonempty_iso_unit_of_discreteTopology I.subscheme
    ((Scheme.Modules.pullback I.subschemeι).obj (tensorPowModule X L n))
  exact (Stacks.Bertini.finrank_globalSections_eq k (I.subschemeι ≫ f) _).trans
    ((AlgebraicGeometry.finrank_globalSectionsOverField k (I.subschemeι ≫ f) _).trans
      ((AlgebraicGeometry.finrank_cohomologyOverField_eq_of_iso k (I.subschemeι ≫ f) e 0).trans
        (AlgebraicGeometry.finrank_cohomologyOverField_zero_unit_eq_finrank_globalSections k
          (I.subschemeι ≫ f))))

end Stacks.SectionsVanishingOnSubscheme

end
