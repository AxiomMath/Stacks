module

public import StacksFrontier.Algebra.Category.ModuleCat.Sheaf.PullbackAlgebraIso
public import StacksFrontier.Algebra.Category.ModuleCat.Sheaf.PullbackUnitGenerators

/-!
# Transport of a global section along the pullback of sheaves of modules

Let `f : X ⟶ Y` be a morphism of ringed spaces and let `M` be a sheaf of `𝒪_Y`-modules. A global
section of `M` is described in two ways, and the two carry different notions of pullback:

* as an element of `M.sections`, a compatible family of local sections, whose image under `f^*` is
  taken by the unit of the adjunction `f^* ⊣ f_*` evaluated on sections, that is by
  `Stacks.RingedSpace.pullbackUnit`;
* as a morphism `𝒪_Y ⟶ M` out of the unit, which `f^*` carries to a morphism out of `f^*𝒪_Y` and
  so, through the comparison `f^*𝒪_Y ≅ 𝒪_X`, back to a morphism out of the unit, i.e. to a global
  section of `f^*M`. That is `Stacks.SheafOfModules.transportSection` for the pullback functor with
  the unitor `Stacks.PullbackAlgebra.pullbackUnitIso`.

The two pullbacks agree.

## Main results

* `Stacks.PullbackAlgebra.pullbackUnitIso_inv_app_one`: the comparison `f^*𝒪_Y ≅ 𝒪_X` carries the
  unit section of `𝒪_X` back to the pullback-unit image of the unit section of `𝒪_Y`.
* `Stacks.PullbackAlgebra.transportSection_eq_pullbackUnit`: the transport of a global section of
  `M` along the pullback is its pullback-unit image, over the inverse image of every open of `Y`;
  `Stacks.PullbackAlgebra.transportSection_val_top` is that over `X` itself.

## References

* [Stacks Project, Tag 0096](https://stacks.math.columbia.edu/tag/0096)
-/

@[expose] public noncomputable section

open CategoryTheory Opposite TopologicalSpace AlgebraicGeometry
open RingedSpaceModuleAdjunction Stacks.RingedSpace Stacks.SheafOfModules

universe u

namespace Stacks.PullbackAlgebra

variable {X Y : RingedSpace.{u, u}} (f : X ⟶ Y)

/-- The comparison `f^*𝒪_Y ≅ 𝒪_X` carries the unit section of `𝒪_X` back to the pullback-unit image
of the unit section of `𝒪_Y`. -/
theorem pullbackUnitIso_inv_app_one (U : (Opens Y.carrier)ᵒᵖ) :
    (pullbackUnitIso f).inv.val.app ((opensMap f).op.obj U)
        (1 : (structureSheafRing X).obj.obj ((opensMap f).op.obj U))
      = pullbackUnit f (SheafOfModules.unit (structureRingSheaf Y)) U
          (1 : (structureSheafRing Y).obj.obj U) := by
  have hsharp : sharp f U (1 : (structureSheafRing Y).obj.obj U)
      = (1 : (structureSheafRing X).obj.obj ((opensMap f).op.obj U)) := map_one _
  have hone := (pullbackUnitIso_hom_pullbackUnit f U
    (1 : (structureSheafRing Y).obj.obj U)).trans hsharp
  have hcancel := congrArg
    (fun k : (pullbackFunctor f).obj (SheafOfModules.unit (structureRingSheaf Y)) ⟶
        (pullbackFunctor f).obj (SheafOfModules.unit (structureRingSheaf Y)) ↦
      k.val.app ((opensMap f).op.obj U)
        (pullbackUnit f (SheafOfModules.unit (structureRingSheaf Y)) U
          (1 : (structureSheafRing Y).obj.obj U)))
    (pullbackUnitIso f).hom_inv_id
  exact (congrArg _ hone.symm).trans hcancel

/-- The transport of a global section along the pullback is its pullback-unit image: over the
inverse image of an open `U` of `Y`, the transport of `t` takes the value the unit of the
adjunction `f^* ⊣ f_*` gives to the value of `t` over `U`. -/
theorem transportSection_eq_pullbackUnit (M : SheafOfModules.{u} (structureRingSheaf Y))
    (t : M.sections) (U : (Opens Y.carrier)ᵒᵖ) :
    (transportSection (pullbackFunctor f) (pullbackUnitIso f).symm t).val
        ((opensMap f).op.obj U)
      = pullbackUnit f M U (t.val U) := by
  have hφ : (M.unitHomEquiv.symm t).val.app U (1 : (structureSheafRing Y).obj.obj U) = t.val U :=
    congrArg (fun s : M.sections ↦ s.val U) (M.unitHomEquiv.apply_symm_apply t)
  show ((pullbackFunctor f).map (M.unitHomEquiv.symm t)).val.app ((opensMap f).op.obj U)
      ((pullbackUnitIso f).inv.val.app ((opensMap f).op.obj U)
        (1 : (structureSheafRing X).obj.obj ((opensMap f).op.obj U)))
    = pullbackUnit f M U (t.val U)
  rw [pullbackUnitIso_inv_app_one]
  exact (pullbackUnit_naturality f (M.unitHomEquiv.symm t) U
    (1 : (structureSheafRing Y).obj.obj U)).trans (congrArg _ hφ)

/-- The transport of a global section along the pullback, over `X` itself: the inverse image of the
top open of `Y` is the top open of `X`. -/
theorem transportSection_val_top (M : SheafOfModules.{u} (structureRingSheaf Y))
    (t : M.sections) :
    (transportSection (pullbackFunctor f) (pullbackUnitIso f).symm t).val
        (op (⊤ : Opens X.carrier))
      = pullbackUnit f M (op (⊤ : Opens Y.carrier)) (t.val (op (⊤ : Opens Y.carrier))) :=
  transportSection_eq_pullbackUnit f M t (op (⊤ : Opens Y.carrier))

end Stacks.PullbackAlgebra

end
