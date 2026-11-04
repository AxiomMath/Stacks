module

public import Mathlib.Algebra.Category.Grp.Abelian
public import Mathlib.CategoryTheory.Sites.Sheaf
public import StacksFrontier.CategoryTheory.Sites.Modules.GrothendieckAbelian
public import StacksFrontier.CategoryTheory.Sites.Cohomology.Cech.ComplexOfAFamily
public import StacksFrontier.CategoryTheory.Sites.Cohomology.Cech.DegreeZeroAndSheafCondition
public import StacksFrontier.CategoryTheory.Sites.Cohomology.Cech.InjectivePresheafVanishing
import StacksCore.Tactic.StacksAttribute

/-!
# Čech cohomology of a sheaf in degree zero

Let `C` be a site and let `E = {U_i → U}` be a covering of `C`. Stacks 03AW computes the
Čech cohomology of an *injective* abelian sheaf `I` with respect to `E`: it is `I(U)` in
degree zero and vanishes in positive degrees.

Both clauses are proved here. The degree-zero clause holds for an arbitrary abelian sheaf and
needs no injectivity: the sheaf condition for the covering `E` says exactly that the
restriction map from `I(U)` to the matching families on `E` is bijective, and by Stacks 03AN
the group of matching families is the degree-zero Čech cohomology group. The positive-degree
clause is injectivity alone: an injective abelian sheaf has injective underlying presheaf,
because sheafification is a left adjoint, and the Čech cohomology of an injective *presheaf*
vanishes in positive degrees by Stacks 03OR.

## Main results

* `Stacks.CechSite.cechCohomology_zero_iso`: the degree-zero Čech cohomology of an abelian
  sheaf for a covering of the site is its group of sections over the covered object.
* `Stacks.CechSite.cechCohomology_isZero_of_injective`: the Čech cohomology of an injective
  abelian sheaf vanishes in positive degrees.

## Implementation notes

A site is a `CategoryTheory.GrothendieckTopology`, and a covering family is a
`PreZeroHypercover` whose generated sieve belongs to the topology. The finite fibre products
needed to form the Čech complex are supplied as product instances in the over category, as
in Stacks 03AM. The coefficient universe contains the object, morphism and covering-index
universes, which is the small-site convention of the source.

The isomorphism is produced as `Nonempty (… ≅ …)` rather than as a chosen map, because the
source asserts only that the two groups agree and the comparison is the one induced by
restriction; its construction goes through `Stacks.CechSite.cechCohomologyZeroEquiv` of
Stacks 03AN.

The positive-degree clause does not need the identification of Čech cohomology with the right
derived functors of `H^0` (Stacks 03AU), which is how the source reaches it and which is not
formalized. Injectivity of the underlying presheaf suffices, so the clause follows from Stacks 03OR
directly. The tag therefore covers both clauses, one note each.

## References

* [Stacks Project, Tag 03AW](https://stacks.math.columbia.edu/tag/03AW)
* [Stacks Project, Tag 03AM](https://stacks.math.columbia.edu/tag/03AM)
* [Stacks Project, Tag 03AN](https://stacks.math.columbia.edu/tag/03AN)
-/

@[expose] public section

universe a w v u

namespace Stacks.CechSite

open CategoryTheory CategoryTheory.Limits Opposite

variable {C : Type u} [Category.{v} C] (J : GrothendieckTopology C) {U : C}
  (E : PreZeroHypercover.{w} U)
  [∀ (n : ℕ) (i : Fin (n + 1) → E.I₀), HasProduct (fun a ↦ Over.mk (E.f (i a)))]
  (hE : E.sieve₀ ∈ J U)
  (I : Sheaf J Ab.{max u v a w})

/-- **Stacks 03AW (positive degrees).** The Čech cohomology of an injective abelian sheaf for a
covering family vanishes in positive degrees.

Stated before `include hE` because the covering property plays no part: the vanishing is pure
injectivity, and carrying `hE` would make this strictly weaker than the source statement. -/
@[stacks 03AW "positive degrees"]
theorem cechCohomology_isZero_of_injective [Injective I] (p : ℕ) (hp : 0 < p) :
    IsZero (cechCohomology E I.obj p) := by
  have : Injective I.obj :=
    (sheafificationAdjunction J Ab.{max u v a w}).map_injective I inferInstance
  exact injective_presheaf_cechCohomology_isZero.{w, v, u, a} E I.obj p hp

include hE

/-- **Stacks 03AW (degree zero).** The degree-zero Čech cohomology of an abelian sheaf for a
covering family is its group of sections over the covered object. -/
@[stacks 03AW "degree zero"]
theorem cechCohomology_zero_iso :
    Nonempty (cechCohomology E I.obj 0 ≅ I.obj.obj (op U)) := by
  have hbij : Function.Bijective (cechRestriction E I.obj) :=
    cechRestriction_bijective_of_isSheaf J I.obj I.property E hE
  let eR := AddEquiv.ofBijective (cechRestriction E I.obj) hbij
  exact ⟨(cechCohomologyZeroEquiv E I.obj).trans eR.symm |>.toAddCommGrpIso⟩

end Stacks.CechSite

end
