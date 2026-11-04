module

public import Mathlib.Algebra.Category.ModuleCat.Sheaf.Quasicoherent
public import Mathlib.AlgebraicGeometry.Modules.Sheaf
public import Mathlib.AlgebraicGeometry.Morphisms.Proper
public import StacksCore.Tactic.StacksAttribute
public import StacksFrontier.AlgebraicGeometry.Flatness.GrothendieckExistence.Basic
public import StacksFrontier.AlgebraicGeometry.RingedSpace.Flat
public import StacksFrontier.Topology.Sheaves.Modules.Support

/-!
# An existence situation for compatible flat modules with proper support

Let `(Aₙ)` be an inverse system of rings whose transition maps are surjective with locally
nilpotent kernels, let `A = lim Aₙ`, and let `X` be a separated scheme of finite presentation
over `Spec A`. Write `Xₙ = X ×_{Spec A} Spec Aₙ` for the base change at level `n`, a closed
subscheme of `X`. The module-level form of Grothendieck's existence theorem starts from a
compatible system `(Fₙ, φₙ)` of finitely presented quasi-coherent sheaves on the `Xₙ`, each
flat over `Spec Aₙ` and with proper support over `Spec Aₙ`, where `φₙ` exhibits `Fₙ` as the
pullback of `Fₙ₊₁`. This module records the standing data of that theorem.

## Main definitions

* `AlgebraicGeometry.GrothendieckExistence.ExistenceSituation`: the rings, the scheme and the
  compatible family of finitely presented flat sheaves with proper support.

## Implementation notes

The index `n : ℕ` stands for the level `n + 1` of the source, so that the inverse system is a
functor out of `ℕᵒᵖ` and its transitions are the images of `homOfLE (Nat.le_succ n)`.

The transition morphisms `Xₙ ⟶ Xₙ₊₁` between the base changes are recorded as data together
with the two equations saying that they commute with the projections to `X` and to the affine
bases; those two equations characterize them, by the universal property of the fibre product.

Proper support is recorded as the existence of a closed subscheme whose underlying set is the
support of the sheaf and whose structural morphism to the affine base at that level is proper.
The support is `AlgebraicGeometry.RingedSpace.ModuleSheaf.supp` of the repackaging of the sheaf
given by `AlgebraicGeometry.SheafOfModules.moduleSheafOfModules`.

## References

* [Stacks Project, Tag 0CTC](https://stacks.math.columbia.edu/tag/0CTC)
* [Stacks Project, Tag 0DIB](https://stacks.math.columbia.edu/tag/0DIB)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits Opposite

universe u

namespace AlgebraicGeometry.GrothendieckExistence

/-- The standing data of Grothendieck's existence theorem for modules: an inverse system of rings
with surjective, locally nilpotent transitions, a separated scheme of finite presentation over the
inverse-limit ring, and a compatible system of finitely presented sheaves on its base changes
which are flat over, and have proper support over, the affine base at their level. -/
@[stacks 0CTC]
structure ExistenceSituation where
  /-- The inverse system of rings. -/
  system : ℕᵒᵖ ⥤ CommRingCat.{u}
  /-- Its consecutive transition maps are surjective. -/
  transition_surjective (n : ℕ) :
    Function.Surjective (system.map (homOfLE (Nat.le_succ n)).op).hom
  /-- The kernels of those transition maps are locally nilpotent. -/
  transition_locallyNilpotent (n : ℕ) :
    (RingHom.ker (system.map (homOfLE (Nat.le_succ n)).op).hom).LocallyNilpotent
  /-- The scheme over the inverse-limit ring. -/
  X : Over (limitBase system)
  /-- The scheme is separated over the inverse-limit ring. -/
  [separated : IsSeparated X.hom]
  /-- The scheme is of finite presentation over the inverse-limit ring. -/
  finitePresentation : FinitePresentation X.hom
  /-- Each base change is a closed subscheme of the scheme. -/
  closedSchemeProjection (n : ℕ) : IsClosedImmersion (schemeProjection system X n)
  /-- The canonical inclusion of the base change at level `n` into the one at level `n + 1`. -/
  transitionScheme (n : ℕ) : schemeAt system X n ⟶ schemeAt system X (n + 1)
  /-- The transition morphism lies over the scheme. -/
  transition_fst (n : ℕ) :
    transitionScheme n ≫ schemeProjection system X (n + 1) = schemeProjection system X n
  /-- The transition morphism lies over the transition of affine bases. -/
  transition_snd (n : ℕ) :
    transitionScheme n ≫ pullback.snd X.hom (baseProjection system (n + 1)) =
      pullback.snd X.hom (baseProjection system n) ≫ baseTransition system n
  /-- The sheaf on the base change at level `n`. -/
  F (n : ℕ) : (schemeAt system X n).Modules
  /-- Each sheaf is of finite presentation. -/
  [finitelyPresented : ∀ n : ℕ, (F n).IsFinitePresentation]
  /-- Each sheaf is flat over the affine base at its level. -/
  flat (n : ℕ) :
    IsFlatOver (pullback.snd X.hom (baseProjection system n)).toLRSHom.toShHom (F n)
  /-- Each sheaf has proper support over the affine base at its level: its support is the
  underlying set of a closed subscheme which is proper over that base. -/
  properSupport (n : ℕ) :
    ∃ (Z : Scheme.{u}) (i : Z ⟶ schemeAt system X n), IsClosedImmersion i ∧
      Set.range i = RingedSpace.ModuleSheaf.supp
        (SheafOfModules.moduleSheafOfModules (F n)) ∧
      IsProper (i ≫ pullback.snd X.hom (baseProjection system n))
  /-- The comparison isomorphism: the pullback of the sheaf at level `n + 1` is the sheaf at
  level `n`. -/
  φ (n : ℕ) : (Scheme.Modules.pullback (transitionScheme n)).obj (F (n + 1)) ≅ F n

end AlgebraicGeometry.GrothendieckExistence

end
