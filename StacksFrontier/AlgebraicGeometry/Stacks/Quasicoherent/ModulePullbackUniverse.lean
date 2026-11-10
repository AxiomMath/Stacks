module

public import StacksFrontier.AlgebraicGeometry.Stacks.Quasicoherent.ModulePullback
public import StacksFrontier.AlgebraicGeometry.Stacks.Quasicoherent.SectionUniverseLiftColimits
public import StacksFrontier.AlgebraicGeometry.Stacks.Quasicoherent.SectionUniverseLiftDescent

/-!
# The inverse image preserves quasi-coherence at every section universe (Stacks 06WH)

`AlgebraicGeometry.Stack.isQuasicoherentOnSite_modulePullback` is **Stacks 06WH** for modules
whose sections lie in a universe `max u v w m` containing the universes of the two fibred
categories.  The section universe of the modules on an algebraic stack is the universe `u` of
the schemes, which is below the universe `u + 1` of the objects of its fibred category.  This
file proves **Stacks 06WH** at every section universe.

The proof transports the single-universe statement along the universe lift of the sections.  The
lift
preserves and reflects quasi-coherence, and it commutes with the inverse image *definitionally*:
the inverse image is objectwise restriction with a transport of scalars, which leaves the
carriers of the sections unchanged.

## Main results

* `AlgebraicGeometry.Stack.isQuasicoherentOnSite_modulePullback_univ`: **Stacks 06WH** at an
  arbitrary section universe.

## References

* [Stacks Project, Tag 06WH](https://stacks.math.columbia.edu/tag/06WH)
-/

@[expose] public section

open CategoryTheory

universe u v w m

namespace AlgebraicGeometry.Stack

/-- **Stacks 06WH at an arbitrary section universe.**  The inverse image of a quasi-coherent
module along a 1-morphism of categories fibred in groupoids over the big fppf category of `S` is
quasi-coherent, whatever the universe of its sections.  The universe lift of the sections
preserves and reflects quasi-coherence and commutes with the inverse image on the nose, so this
is `AlgebraicGeometry.Stack.isQuasicoherentOnSite_modulePullback` read through the lift. -/
theorem isQuasicoherentOnSite_modulePullback_univ
    (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)
    {𝒳 𝒴 : Type v} [Category.{w} 𝒳] [Category.{w} 𝒴]
    (p : 𝒳 ⥤ BigFppfOver B S hS) (q : 𝒴 ⥤ BigFppfOver B S hS)
    (hp : p.IsFiberedInGroupoids) (hq : q.IsFiberedInGroupoids)
    (f : 𝒳 ⥤ 𝒴) (hf : f ⋙ q = p)
    (M : SheafOfModules.{m} (ringStructureSheafCore B S hS q hq B.topology le_rfl))
    (hM : M.IsQuasicoherentOnSite) :
    ((modulePullback.{u, v, w, m} B S hS p q hp hq f hf B.topology le_rfl).obj
      M).IsQuasicoherentOnSite := by
  have := SheafOfModules.isQuasicoherentOnSite_uliftForPresentation'.{v, w, u, m, max u v w} hM
  have h := isQuasicoherentOnSite_modulePullback.{u, v, w, m} B S hS p q hp hq f hf
    (SheafOfModules.uliftForPresentation.{v, w, u, m, max u v w} M)
  exact SheafOfModules.IsQuasicoherentOnSite.of_uliftForPresentation'.{v, w, u, m, max u v w} h

end AlgebraicGeometry.Stack
