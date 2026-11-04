module

public import StacksFrontier.AlgebraicGeometry.Spaces.Perfect.FlatProperSupportRestriction
public import StacksFrontier.AlgebraicGeometry.Spaces.Perfect.TensorPullbackComplexEtaleRestriction
public import StacksFrontier.AlgebraicGeometry.Spaces.SmallEtaleDerivedModuleAdjunction
public import StacksFrontier.AlgebraicGeometry.Spaces.FlatModuleBaseChange
public import StacksFrontier.AlgebraicGeometry.Spaces.FlatModuleIso
public import StacksFrontier.AlgebraicGeometry.Spaces.ModulePullbackQuasicoherentFromChartDiagrams

/-!
# The pullback of modules along a morphism of small étale ringed topoi: zero, quasi-coherence and
flatness

For a morphism `g : X' ⟶ X` of algebraic spaces, the pullback of `𝒪_X`-modules along the
morphism of small étale ringed topoi of `g`
(`Stacks.Sheaves.RingedToposModules.RingedToposHom.pullbackModules`) is isomorphic to the
pullback `modulePullback` of Stacks 03LU, and so inherits from it:

* it carries zero modules to zero modules;
* it preserves quasi-coherence (Stacks 03GA);
* flatness over the base is preserved by base change (Stacks 05VV), at every geometric point;
* along an étale morphism, flatness over the base is preserved.

## Main results

* `AlgebraicGeometry.Space.isZero_smallEtalePullbackModules_obj`: the pullback of a zero module
  is zero.
* `AlgebraicGeometry.Space.isQuasicoherentOnSite_smallEtalePullbackModules_obj`: the pullback of
  a quasi-coherent module is quasi-coherent.
* `AlgebraicGeometry.Space.isFlatOverAtGeometricPoint_smallEtalePullbackModules_obj`: flatness
  over the base is preserved by base change, at every geometric point.
* `AlgebraicGeometry.Space.isFlatOver_smallEtalePullbackModules_obj_comp`: flatness over the base
  is preserved by restriction along an étale morphism.

## References

* [Stacks Project, Tag 03LU](https://stacks.math.columbia.edu/tag/03LU)
* [Stacks Project, Tag 03GA](https://stacks.math.columbia.edu/tag/03GA)
* [Stacks Project, Tag 05VV](https://stacks.math.columbia.edu/tag/05VV)
* [Stacks Project, Tag 08JR](https://stacks.math.columbia.edu/tag/08JR)
* [Stacks Project, Tag 0DKL](https://stacks.math.columbia.edu/tag/0DKL)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits

universe u

namespace AlgebraicGeometry.Space

attribute [-instance] Stacks.Cohomology.SiteModules.moduleSheavesAbelian

variable {B : BigFppfSite.{u}} {S : Scheme.{u}} {hS : B.Contains S}
  {X X' Y Y' : AlgebraicSpaces B S hS}

/-- The pullback of a zero module along a morphism of algebraic spaces is zero. -/
theorem isZero_smallEtalePullbackModules_obj (g : X' ⟶ X)
    {M : SheafOfModules.{u} (ringedToposStructureRingSheaf B S hS X)} (hM : IsZero M) :
    IsZero ((Stacks.Sheaves.RingedToposModules.RingedToposHom.pullbackModules
      (X := smallEtaleRingedTopos B S hS X') (Y := smallEtaleRingedTopos B S hS X)
        (smallEtaleRingedToposHom B S hS g).toModulesHom).obj M) := by
  have := modulePullback_additive (B := B) (S := S) (hS := hS) g
  exact ((modulePullback B S hS g).map_isZero hM).of_iso
    ((pullbackModulesIsoModulePullback B S hS g).app M)

/-- **Stacks 03GA**, for the pullback along the morphism of small étale ringed topoi: the pullback
of a quasi-coherent module is quasi-coherent. -/
theorem isQuasicoherentOnSite_smallEtalePullbackModules_obj (g : X' ⟶ X)
    (M : SheafOfModules.{u} (ringedToposStructureRingSheaf B S hS X))
    (hM : M.IsQuasicoherentOnSite) :
    ((Stacks.Sheaves.RingedToposModules.RingedToposHom.pullbackModules
      (X := smallEtaleRingedTopos B S hS X') (Y := smallEtaleRingedTopos B S hS X)
        (smallEtaleRingedToposHom B S hS g).toModulesHom).obj M).IsQuasicoherentOnSite :=
  SheafOfModules.IsQuasicoherentOnSite.of_iso
    ((pullbackModulesIsoModulePullback B S hS g).app M).symm
    (isQuasicoherentOnSite_modulePullback_of_isQuasicoherentOnSite B S hS g M hM)

/-- **Flatness over the base is preserved by base change** (Stacks 05VV), at every geometric point,
for the pullback along the morphism of small étale ringed topoi: if `M` is quasi-coherent and flat
over `Y` along `f`, then for a cartesian square `X' = X ×_Y Y'` the pullback `(g')^*M` is flat over
`Y'` along `f'` at every geometric point of `X'`. -/
theorem isFlatOverAtGeometricPoint_smallEtalePullbackModules_obj {g' : X' ⟶ X} {f' : X' ⟶ Y'}
    {f : X ⟶ Y} {g : Y' ⟶ Y} (hpb : IsPullback g' f' f g)
    (M : SheafOfModules.{u} (ringedToposStructureRingSheaf B S hS X))
    (hM : M.IsQuasicoherentOnSite) (hfl : IsFlatOver B S hS X.2 f.hom M)
    (x' : GeometricPoint B S hS X'.1) :
    IsFlatOverAtGeometricPoint B S hS f'
      ((Stacks.Sheaves.RingedToposModules.RingedToposHom.pullbackModules
        (X := smallEtaleRingedTopos B S hS X') (Y := smallEtaleRingedTopos B S hS X)
          (smallEtaleRingedToposHom B S hS g').toModulesHom).obj M) x' := by
  have h2 : ((modulePullback B S hS g').obj M).IsQuasicoherentOnSite :=
    isQuasicoherentOnSite_modulePullback_of_isQuasicoherentOnSite B S hS g' M hM
  exact (@isFlatOver_iff_forall_isFlatOverAtGeometricPoint B S hS _ _ f' _
    (isQuasicoherentOnSite_smallEtalePullbackModules_obj g' M hM)).1
    (IsFlatOver.of_iso B S hS X'.2 ((pullbackModulesIsoModulePullback B S hS g').app M).symm
      (@isFlatOver_modulePullback B S hS _ _ _ _ _ _ _ _ hpb M hM h2 hfl)) x'

/-- **Flatness over the base is preserved by restriction along an étale morphism**, for the
pullback along the morphism of small étale ringed topoi. -/
theorem isFlatOver_smallEtalePullbackModules_obj_comp (j : X' ⟶ X) (hj : IsEtale B S hS j.hom)
    (f : X ⟶ Y) (M : SheafOfModules.{u} (ringedToposStructureRingSheaf B S hS X))
    (hM : IsFlatOver B S hS X.2 f.hom M) :
    IsFlatOver B S hS X'.2 (j ≫ f).hom
      ((Stacks.Sheaves.RingedToposModules.RingedToposHom.pullbackModules
        (X := smallEtaleRingedTopos B S hS X') (Y := smallEtaleRingedTopos B S hS X)
          (smallEtaleRingedToposHom B S hS j).toModulesHom).obj M) :=
  IsFlatOver.of_iso B S hS X'.2 ((etaleModulePullbackIsoPullbackModules B S hS j hj).app M)
    (isFlatOver_etaleModulePullback_comp B S hS j hj f M hM)

end AlgebraicGeometry.Space

end
