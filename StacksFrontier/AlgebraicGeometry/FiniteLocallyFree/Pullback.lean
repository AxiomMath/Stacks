module

public import StacksFrontier.AlgebraicGeometry.Divisors.Norm.Basic

/-!
# Pullback of a finite locally free sheaf of modules

The pullback of a finite locally free sheaf of modules is finite locally free. This is the
rank-free companion of `Stacks.AlgebraicGeometry.ComponentDegrees.rankPullbackData`, which says
the same for a module of fixed rank `r`.

## Main results

* `AlgebraicGeometry.SheafOfModules.IsFiniteLocallyFree.pullback`: the statement for a morphism
  of sheaves of rings over a continuous map of spaces.
* `AlgebraicGeometry.SheafOfModules.IsFiniteLocallyFree.pullback_scheme`: the statement for the
  pullback of modules along a morphism of schemes.

## Implementation notes

Everything is read off `Stacks.Divisors.local_generators_pullback`, which transports local
generating data through a pullback and records that the index type and each local index type are
carried over unchanged. Local freeness is part of what it returns, so only the finiteness clause
is left, and that is exactly the statement that those local index types stay finite.

The transported data is taken from the existential rather than rebuilt here on purpose. Writing
the transported generating sections out — as the fixed-rank statement does — makes the ambient
module of each one a term that has to be identified with the restriction of the pullback by
unfolding, and that identification exhausts the elaborator's budget once the clause being
checked is finiteness of the index type rather than its cardinality. Read off the existential,
the data is opaque, the two index types are related by a propositional equation, and no
unfolding happens at all.
-/

@[expose] public section

open CategoryTheory TopologicalSpace

universe u

namespace AlgebraicGeometry.SheafOfModules.IsFiniteLocallyFree

/-- **The pullback of a finite locally free sheaf of modules is finite locally free.** -/
theorem pullback {X Y : TopCat.{u}} (f : X ⟶ Y)
    {S : Sheaf (Opens.grothendieckTopology Y) RingCat.{u}}
    {R : Sheaf (Opens.grothendieckTopology X) RingCat.{u}}
    (φ : S ⟶ ((Opens.map f).sheafPushforwardContinuous RingCat _ _).obj R)
    (M : _root_.SheafOfModules.{u} S)
    (h : IsFiniteLocallyFree.{u, u, u} M) :
    IsFiniteLocallyFree.{u, u, u} ((_root_.SheafOfModules.pullback φ).obj M) := by
  obtain ⟨q, hq, hfinite⟩ := h.exists_isFiniteLocallyFreeData
  obtain ⟨q', hq', e, -, hI⟩ := Stacks.Divisors.local_generators_pullback f φ M q hq
  refine ⟨q', hq', ⟨fun i => ?_⟩⟩
  have : Finite (q.generators (e i)).I := (hfinite.isFiniteType (e i)).finite
  exact ⟨Finite.of_equiv _ (Equiv.cast (hI i).symm)⟩

/-- **The pullback of a finite locally free module along a morphism of schemes is finite locally
free.** -/
theorem pullback_scheme {X Y : Scheme.{u}} (g : X ⟶ Y) (M : Y.Modules)
    (h : IsFiniteLocallyFree.{u, u, u} M) :
    IsFiniteLocallyFree.{u, u, u} ((Scheme.Modules.pullback g).obj M) :=
  pullback g.base g.toRingCatSheafHom M h

end AlgebraicGeometry.SheafOfModules.IsFiniteLocallyFree

end
