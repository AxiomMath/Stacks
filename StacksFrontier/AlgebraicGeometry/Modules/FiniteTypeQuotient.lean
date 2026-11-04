module

public import Mathlib.AlgebraicGeometry.Modules.Sheaf
public import StacksFrontier.Algebra.Category.ModuleCat.Sheaf.FiniteTypeExtension

/-!
# A quotient of a module of finite type on a scheme is of finite type

If `p : M ⟶ N` is an epimorphism of modules on a scheme `X` and `M` is of finite type, then `N`
is of finite type. This is `Stacks.SheafOfModules.isFiniteType_of_epi`, stated at `X.Modules`.

## Main results

* `AlgebraicGeometry.Scheme.Modules.isFiniteType_of_epi`: a quotient of a module of finite type
  on a scheme is of finite type.
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits

universe u

namespace AlgebraicGeometry.Scheme.Modules

/-- A quotient of a module of finite type on a scheme is of finite type. The hypothesis and the
conclusion are transported between `X.Modules` and `SheafOfModules X.ringCatSheaf`, which are
definitionally equal but carry separate category instances. -/
theorem isFiniteType_of_epi {X : Scheme.{u}} {M N : X.Modules} (p : M ⟶ N) [Epi p]
    [M.IsFiniteType] : N.IsFiniteType := by
  let M' : _root_.SheafOfModules.{u} X.ringCatSheaf := M
  let N' : _root_.SheafOfModules.{u} X.ringCatSheaf := N
  let p' : M' ⟶ N' := p
  have hp' : Epi p' := by change Epi p; exact ‹Epi p›
  have hM' : _root_.SheafOfModules.IsFiniteType.{u, u, u} M' := ‹M.IsFiniteType›
  exact Stacks.SheafOfModules.isFiniteType_of_epi.{u, u, u} (M := M') (N := N') p' hM'

end AlgebraicGeometry.Scheme.Modules

end
