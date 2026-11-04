module

public import StacksFrontier.Topology.Sheaves.Functors.Module.RingedSpace

/-!
# The pullback of a function is the function pulled back

Let `f : X ⟶ Y` be a morphism of ringed spaces. The pullback of sheaves of modules carries the
structure sheaf of `Y` to the structure sheaf of `X`, by
`RingedSpaceModuleAdjunction.modulePullbackObjUnitIso`. This file records what that
identification does on sections: the pullback of a section `r` of `𝒪_Y` over `V`, taken along
the unit of `f^* ⊣ f_*`, is carried to `f^♯ r`, the ordinary pullback of `r` as a function, a
section of `𝒪_X` over `f ⁻¹ V`.

This is the statement that the pullback of a *generator* of a trivialized invertible module is a
generator: if `θ : L ≅ 𝒪_Y`, then `f^* L ≅ 𝒪_X` by `(f^* θ) ≫ modulePullbackObjUnitIso`, and the
result below says that composite sends the pullback of `θ⁻¹ 1` to `f^♯ 1 = 1`.

## Main results

* `RingedSpaceModuleAdjunction.pullbackObjUnitToUnit_val_app_unit` — the identity above.

## Implementation notes

`CategoryTheory.SheafOfModules.pullbackObjUnitToUnit` is by definition the morphism adjoint to
`CategoryTheory.SheafOfModules.unitToPushforwardObjUnit`, which is `f^♯` read as a morphism of
sheaves of modules and whose component on a section is `f^♯` itself, by
`CategoryTheory.SheafOfModules.unitToPushforwardObjUnit_val_app_apply`, which is `rfl`. So the
content here is `CategoryTheory.Adjunction.homEquiv_unit` evaluated on a section: the adjunct of
a morphism is the unit followed by its pushforward, and pushforward along a continuous functor
is reindexing of sections, so the component of the pushforward at `V` is the component of the
morphism at `f ⁻¹ V`.

The statement is about `pullbackObjUnitToUnit` rather than about
`RingedSpaceModuleAdjunction.modulePullbackObjUnitIso`, whose `hom` it is: that isomorphism
exists only once `opensMap f` is known to be final, which is an extra hypothesis this identity
does not need, and the two agree by `rfl` where both are available.

`CategoryTheory.Functor.IsRightAdjoint` is a `Prop`, so the instance that
`RingedSpaceModuleAdjunction.modulePullbackPushforwardAdjunction` fixes by `letI` and the one
instance search finds here are equal by proof irrelevance; no transport is needed between the
two readings of the adjunction.

## References

* [Stacks Project, Tag 0096](https://stacks.math.columbia.edu/tag/0096)
-/

@[expose] public section

open CategoryTheory Opposite TopologicalSpace AlgebraicGeometry

universe u

namespace RingedSpaceModuleAdjunction

variable {X Y : RingedSpace.{u, u}} (f : X ⟶ Y)

/-- **The pullback of a function is the function pulled back.** The canonical morphism
`f^* 𝒪_Y ⟶ 𝒪_X` sends the pullback of a section `r` of `𝒪_Y` over `V`, taken along the unit of
`f^* ⊣ f_*`, to `f^♯ r` over `f ⁻¹ V`. -/
theorem pullbackObjUnitToUnit_val_app_unit (V : Opens Y.carrier)
    (r : (structureSheafRing Y).obj.obj (op V)) :
    (SheafOfModules.pullbackObjUnitToUnit (structureSheafHom f)).val.app
        (op ((opensMap f).obj V))
        (((modulePullbackPushforwardAdjunction f).unit.app
          (SheafOfModules.unit (structureSheafRing Y))).val.app (op V) r) =
      (structureSheafHom f).hom.app (op V) r := by
  have h := (SheafOfModules.pullbackPushforwardAdjunction (structureSheafHom f)).homEquiv_unit
    (f := SheafOfModules.pullbackObjUnitToUnit (structureSheafHom f))
  rw [SheafOfModules.pullbackPushforwardAdjunction_homEquiv_pullbackObjUnitToUnit] at h
  exact (congrArg (fun g => g.val.app (op V) r) h).symm

end RingedSpaceModuleAdjunction

end
