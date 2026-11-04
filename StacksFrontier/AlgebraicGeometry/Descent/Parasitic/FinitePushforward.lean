module

public import Mathlib.Algebra.Category.ModuleCat.Sheaf.Quasicoherent
public import Mathlib.AlgebraicGeometry.Modules.Sheaf
public import Mathlib.AlgebraicGeometry.Morphisms.Finite
public import StacksFrontier.Algebra.Module.FinitePresentationRel.Finite
public import StacksFrontier.AlgebraicGeometry.MoreMorphisms.RelativeFinitePresentation.FinitePushforward
public import StacksFrontier.AlgebraicGeometry.Morphisms.FinitePresentationPoint
public import StacksFrontier.AlgebraicGeometry.Morphisms.WeaklyEtale.RelativeFinitePresentation.Affine
public import StacksFrontier.AlgebraicGeometry.Morphisms.WeaklyEtale.RelativeFinitePresentation.FinitePresentation
public import StacksFrontier.AlgebraicGeometry.QcohLimits.RestrictScalars
public import StacksFrontier.Topology.Sheaves.Functors.Module.RingedSpace
public import StacksCore.Tactic.StacksAttribute

/-!
# Finite presentation of modules under a finite pushforward

A finite morphism is affine and its structure map on sections is a module-finite ring map, so
over an affine open of the target the sections of a module and of its direct image are the same
abelian group, read over two rings one of which is module-finite over the other. Finite
presentation relative to a base is insensitive to such a change of rings, so finite pushforward
preserves and reflects it; for a finite morphism of finite presentation the same holds for
absolute finite presentation.

## Main results

* `AlgebraicGeometry.isFinitelyPresentedRelative_modulePushforward_iff`: the relative statement
  `AlgebraicGeometry.isFinitelyPresentedRelative_pushforward_iff` with the direct image spelled
  as the pushforward of modules over the underlying morphism of ringed spaces.
* `AlgebraicGeometry.isFinitePresentation_iff_pushforward_isFinitePresentation`: for a finite
  morphism of finite presentation, a quasi-coherent module is of finite presentation if and
  only if its direct image is.

## References

* [Stacks Project, Tag 05B4](https://stacks.math.columbia.edu/tag/05B4)
* [Stacks Project, Tag 09T9](https://stacks.math.columbia.edu/tag/09T9)
-/

@[expose] public section

open CategoryTheory RingedSpaceModuleAdjunction

universe u

namespace AlgebraicGeometry

private theorem modulePushforward_toLRSHom_toShHom_eq {X Y : Scheme.{u}} (π : X ⟶ Y) :
    modulePushforward π.toLRSHom.toShHom = Scheme.Modules.pushforward π := by
  unfold modulePushforward Scheme.Modules.pushforward
  congr 1

/-- For a finite morphism `π : X ⟶ Y` of schemes locally of finite type over `S`, a
quasi-coherent module on `X` is finitely presented relative to `S` if and only if its direct image
is, the direct image being the pushforward of modules along the underlying morphism of ringed
spaces. -/
public theorem isFinitelyPresentedRelative_modulePushforward_iff
    {X Y S : Scheme.{u}} (π : X ⟶ Y) (f : X ⟶ S) (g : Y ⟶ S)
    (hπ : π ≫ g = f) [IsFinite π] [LocallyOfFiniteType f]
    [LocallyOfFiniteType g] (M : X.Modules) [M.IsQuasicoherent] :
    IsFinitelyPresentedRelative g ((modulePushforward π.toLRSHom.toShHom).obj M) ↔
      IsFinitelyPresentedRelative f M := by
  rw [modulePushforward_toLRSHom_toShHom_eq]
  exact isFinitelyPresentedRelative_pushforward_iff π f g hπ M

/-- A quasi-coherent module on the source of a finite morphism of finite presentation is
finitely presented if and only if its direct image is finitely presented. -/
@[stacks 05B4]
public theorem isFinitePresentation_iff_pushforward_isFinitePresentation
    {X Y : Scheme.{u}} (f : X ⟶ Y) [IsFinite f]
    (hf : FinitePresentation f) (F : X.Modules) [F.IsQuasicoherent] :
    F.IsFinitePresentation ↔
      ((Scheme.Modules.pushforward f).obj F).IsFinitePresentation := by
  let : LocallyOfFinitePresentation f := hf.1
  have hP :
      IsFinitelyPresentedRelative (CategoryStruct.id Y)
        ((Scheme.Modules.pushforward f).obj F) ↔
      IsFinitelyPresentedRelative f F := by
    simpa [modulePushforward_toLRSHom_toShHom_eq] using
      isFinitelyPresentedRelative_modulePushforward_iff f f (CategoryStruct.id Y) (by simp) F
  let : ((Scheme.Modules.pushforward f).obj F).IsQuasicoherent :=
    (Stacks.AlgebraicGeometry.QcohLimits.affine_isQuasicoherent_restrictScalars_iff f _).2
      (Stacks.AlgebraicGeometry.QcohLimits.affinePushforward_isQuasicoherent f F inferInstance)
  exact (isFinitelyPresentedRelative_iff_isFinitePresentation f F).symm.trans
    (hP.symm.trans (isFinitelyPresentedRelative_iff_isFinitePresentation
      (CategoryStruct.id Y) ((Scheme.Modules.pushforward f).obj F)))

end AlgebraicGeometry

end
