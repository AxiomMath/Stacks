module

public import StacksFrontier.Topology.Sheaves.Cohomology.DerivedPushforward.GlobalCupProductCanonicalInstances
public import StacksFrontier.Topology.Sheaves.Cohomology.DerivedPushforward.DerivedSectionsOnAPoint

/-!
# A non-degeneracy certificate for the Künneth map of Tag 0G49

Tag 0G49 is a *definition*, so it cannot be checked by `#print axioms`; what can be checked
instead is that the object it defines is not vacuous.  Two things are checked here.

*The binders are jointly instantiable.*  `kunnethMapOfSheavesCanonicalOnAPoint` forms the
parameterless map of Tag 0G49 with every binder instantiated — the base, the two spaces and
their fibre-product stand-in all the one-point ringed space `({*}, R)`, and all four structure
morphisms the identity.  Nothing is assumed beyond `CommRing R`.

*The witness is not degenerate.*  Satisfiability alone would prove nothing: a Künneth map over a
space with no cohomology is vacuous, which is how a constant sheaf at a terminal object once
passed for a witness elsewhere in this development.  `onePointRingedSpace R` over a **nontrivial**
`R` is a space this repository proves carries cohomology:
`Stacks.Cohomology.DerivedSectionsOnAPoint.not_forall_isZero_baseSections` says derived global
sections there do not vanish identically, witnessed by the sheaf attached to `R` itself in
degree zero.  So the map is formed over a base whose derived global sections — the functor
building both the source and the target of the map — are not identically zero.

*What this does not certify.*  It does not compute the source and target of the map at a named
pair `(ℱ, 𝒢)` and show both nonzero, nor that the map itself is nonzero.  Those are statements
about the content of the Section 0FKU cup product rather than about Tag 0G49, whose whole
assertion is that the map is canonical; the relevant non-vanishing input is
`Stacks.Cohomology.GlobalKunneth.IsGlobalCupProduct.ne_zero`, which needs the unitality of the
canonical cup product.

## References

* [Stacks Project, Tag 0G49](https://stacks.math.columbia.edu/tag/0G49)
-/

@[expose] public noncomputable section

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits Opposite TopologicalSpace
open RingedSpaceModuleAdjunction
open Stacks.Cohomology.DerivedSectionsLeray
open Stacks.Cohomology.DerivedAdjunctionOnRingedSpaces
open Stacks.DerivedTensor.RingedSite
open scoped CategoryTheory.Prod

universe u

namespace Stacks.Cohomology.GlobalKunneth

attribute [local instance] HasDerivedCategory.standard

open Stacks.Cohomology.DerivedSectionsOnAPoint in
/-- **Every binder of the parameterless Künneth map of Tag 0G49 instantiated at once**, over the
one-point ringed space `({*}, R)` with all four structure morphisms the identity.  Nothing is
assumed: there is no cup product to supply, which is the whole point of the discharge. -/
def kunnethMapOfSheavesCanonicalOnAPoint (R : Type u) [CommRing R]
    (F G : Modules (onePointRingedSpace R).sheaf) :=
  kunnethMapOfSheavesCanonical (S := onePointRingedSpace R) (𝟙 _) (𝟙 _) (𝟙 _) (𝟙 _) (𝟙 _)
    (Category.id_comp _) (Category.id_comp _) F G

open Stacks.Cohomology.DerivedSectionsOnAPoint in
/-- **The witness of `kunnethMapOfSheavesCanonicalOnAPoint` is not a space without cohomology.**
Over a nontrivial `R`, derived global sections on `({*}, R)` do not vanish identically, so the
base over which the map was formed is not one on which every instance of the map is a map
between zero objects. -/
theorem not_forall_isZero_baseSections_onePoint (R : Type u) [CommRing R] [Nontrivial R] :
    ¬ ∀ U : DerivedCategory
        (SheafOfModules.{u} (structureSheafRing (onePointRingedSpace R))),
      IsZero ((baseSections (onePointRingedSpace R)).obj U) :=
  Stacks.Cohomology.DerivedSectionsOnAPoint.not_forall_isZero_baseSections R

end Stacks.Cohomology.GlobalKunneth

end
