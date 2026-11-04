module

public import StacksFrontier.Algebra.Category.ModuleCat.Sheaf.LargeModuleUniverseSeparator
public import StacksFrontier.RingTheory.LocalCohomology.LowDegree.ExactSequence
import StacksCore.Tactic.EgaSgaAttribute

/-!
# Cohomology on a scheme over a ring, as a module over that ring

Stacks 0DWR compares, in positive degrees, the cohomology of a module on `U = Spec A \ V(I)`
with the local cohomology of an `A`-module `M` with support in `V(I)`. Its left-hand side is the
`p`-th right derived functor of global sections of a sheaf of modules on the open subscheme `U`,
with scalars restricted to `A` along the structure morphism. The module lives in a universe `v`
independent of the universe `u` of the ring, so the sheaf of modules lives in `max u v` while
the scheme lives in `u`.

That object is exactly what this file defines, and the universes were the obstruction. A right
derived functor needs injective resolutions in the source category, and Mathlib gives
`SheafOfModules.{w} X.ringCatSheaf` for `X : Scheme.{u}` enough injectives only at `w = u`.
Two files supply them at `w = max u v`:
`StacksFrontier/Algebra/Category/ModuleCat/Sheaf/LargeModuleUniverse.lean` gives the abelian
structure and three of the four Grothendieck axioms there, and
`StacksFrontier/Algebra/Category/ModuleCat/Sheaf/SeparatorUnivLE.lean` gives the fourth, the
separator. `StacksFrontier/Algebra/Category/ModuleCat/Sheaf/LargeModuleUniverseSeparator.lean`
joins them and registers `Stacks.LargeModuleUniverse.enoughInjectives` as an instance, so the
definition below needs no hypothesis at all: the left-hand side of Stacks 0DWR at independent
universes is an unconditional definition.

At `v = u` it specialises to the ordinary one, which is the universe at which
`StacksFrontier/RingTheory/LocalCohomology/HigherDegree/CechSheafCohomology.lean` works
throughout.

## Main definitions

* `Stacks.LocalCohomology.cohomologyOverBase` — **sheaf cohomology on a scheme over `A`, with
  its canonical `A`-module structure**, in a module universe above the universe of the scheme.

## Implementation notes

The `A`-module structure is restriction of scalars along
`A ⟶ Γ(Spec A, ⊤) ⟶ Γ(X, ⊤)`, the second map being `f.appLE ⊤ ⊤`. That is the composite the
source uses, and it is the one for which the `Additive` instance on evaluation is available by
`rfl`.

No Stacks tag attribute is placed here: this is one object occurring in the statement of
Stacks 0DWR, not a covering set for it.

## References

* [Stacks Project, Tag 0DWR](https://stacks.math.columbia.edu/tag/0DWR)
-/

@[expose] public noncomputable section

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits Opposite

universe u v

namespace Stacks.LocalCohomology

/-- **Sheaf cohomology on a scheme over `A`, with its canonical `A`-module structure.** For
`f : X ⟶ Spec A` and a sheaf of modules `F` on `X` whose module universe `max u v` may exceed
the universe `u` of `X`, this is the `p`-th right derived functor of global sections of `F`,
with scalars restricted to `A` along `f`.

The injective resolutions come from `Stacks.LargeModuleUniverse.enoughInjectives`, which is an
instance at every module universe above the universe of the space; at `v = u` it is Mathlib's
own. -/
@[ega "0 12.1.2" "special case"]
def cohomologyOverBase (A : Type u) [CommRing A] {X : Scheme.{u}}
    (f : X ⟶ Spec (.of A)) (F : SheafOfModules.{max u v} X.ringCatSheaf) (p : ℕ) :
    ModuleCat.{max u v} A :=
  let E : SheafOfModules.{max u v} X.ringCatSheaf ⥤ ModuleCat.{max u v} Γ(X, ⊤) :=
    SheafOfModules.evaluation X.ringCatSheaf (op (⊤ : X.Opens))
  let : E.Additive := ⟨by intros; rfl⟩
  (ModuleCat.restrictScalars
    ((Scheme.ΓSpecIso (.of A)).inv ≫ f.appLE ⊤ ⊤ (by simp)).hom).obj
    ((E.rightDerived p).obj F)

end Stacks.LocalCohomology

end
