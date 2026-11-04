module

public import StacksCore.Tactic.StacksAttribute
public import StacksFrontier.Algebra.Category.ModuleCat.Sheaf.EtaSheafPullback
public import StacksFrontier.Algebra.Category.ModuleCat.Sheaf.PullbackTensorCoherence

/-!
# The pullback comparison of Stacks 01CD is compatible with the ideal inclusion

Let `f : X ⟶ Y` be a morphism of ringed spaces, `I` an invertible sheaf of `𝒪_Y`-modules and
`ι : I ⟶ 𝒪_Y` an inclusion of it as an ideal. The sheaf-theoretic décalage of Tag 0GT6 is built
from the integer ideal powers `I^{⊗ n} ⊗ -` of
`StacksFrontier.Algebra.Category.ModuleCat.Sheaf.EtaSheaf` together with the transition maps
`Stacks.IdealTorsion.Eta.idealPowerIncl` that `ι` induces between consecutive powers. Comparing
a décalage on `Y` with a décalage on `X` needs the interchange
`f^*(I^{⊗ n} ⊗ M) ≅ (f^*I)^{⊗ n} ⊗ f^*M` of
`StacksFrontier.Algebra.Category.ModuleCat.Sheaf.EtaSheafPullback` *and* the compatibility of that
interchange with the transition maps. This file supplies the degree-`0` case of the latter,
which is the only degree in which anything has to be checked: the transport of
`StacksFrontier.CategoryTheory.Equivalence.PowIntertwinerSucc` lifts it to every integer degree.

## Main definitions

* `Stacks.IdealTorsion.Eta.pullbackIdealIncl`: **the pullback `f^*ι` of the ideal inclusion**,
  `f^*I ⟶ 𝒪_X`: the pullback of `ι` followed by the identification `f^*𝒪_Y ≅ 𝒪_X`.

## Main results

* `Stacks.IdealTorsion.Eta.map_idealPowerIncl_zero`: **the canonical comparison of Stacks 01CD
  is compatible with the degree-`0` ideal inclusion**,
  `f^*(ι ⊗ 1) = c_{M,I} ≫ ((f^*ι) ⊗ 1)`. The variant
  `comparisonBifunctorIso_app_hom_comp_idealPowerIncl_zero` states it with the comparison
  spelled through `Stacks.RingedSpace.comparisonBifunctorIso`, which is the form the transport
  of `Stacks.Equivalence.powIntertwineObj_incl` consumes.
* `Stacks.IdealTorsion.Eta.idealPowerIncl_zero_tmul`: **the degree-`0` ideal inclusion on a local
  pure tensor** is the scalar action of the ambient section represented by the ideal section.
* `Stacks.IdealTorsion.Eta.idealSection_pullbackIdealIncl`: the ambient section represented by
  `f^*ι` at a pullback-unit image is the image under `f^♯` of the one represented by `ι`.

## Implementation notes

**The route, and why it is the short one.** Both sides of the main identity are morphisms out of
the pullback `f^*(M ⊗ I)`, so `Stacks.PullbackTensorCoherence.pullback_tensor_hom_ext` reduces
the identity to the pullback-unit images of the local pure tensors — the adjunction `f^* ⊣ f_*`
turns a morphism out of a pullback into its adjoint transpose, whose source is a tensor product
sheaf, where `PresheafOfModules.tensorSheaf_hom_ext` applies. On those sections every morphism
involved already has a section formula:
`Stacks.PullbackTensorCoherence.pullbackTensorComparison_pullbackUnit` for the comparison of
Tag 01CD, `Stacks.PullbackAlgebra.pullbackUnitIso_hom_pullbackUnit` for the identification
`f^*𝒪_Y ≅ 𝒪_X`, and `Stacks.RingedSpace.pullbackUnit_smul` and `pullbackUnit_naturality` for
the pullback unit. The one formula that did not exist is the one for `idealPowerIncl` itself in
degree `0`, and that is `idealPowerIncl_zero_tmul` below.

Nothing here goes through a tensorator of a monoidal functor. In particular the identity is
*not* obtained from `Stacks.PullbackMonoidalSheaf.pullbackMonoidal`, whose tensorator is pinned
only to the presheaf-level comparison and is not known to agree with
`Stacks.RingedSpace.comparison`; it is obtained from the sheaf-level comparison directly, on
sections.

**Why degree `0` is the only degree that needs an argument.** `idealPowerIncl X I ι n M` is
`(powSuccIso _ n M).inv ≫ (ι ⊗ 1) ≫ (right unitor)`, and in degree `0` the successor comparison
is the identity, so the inclusion *is* `(ι ⊗ 1)` followed by the right unitor. That is the
hypothesis `ha` of `Stacks.Equivalence.powIntertwineObj_incl`, which lifts it to every integer
degree with no further input.

## References

* [Stacks Project, Tag 01CD](https://stacks.math.columbia.edu/tag/01CD)
* [Stacks Project, Tag 0B8L](https://stacks.math.columbia.edu/tag/0B8L)
* [Stacks Project, Tag 0GT6](https://stacks.math.columbia.edu/tag/0GT6)
-/

@[expose] public section

/- The spelling `(Stacks.SheafOfModules.Tensor.ringSheaf Z.sheaf)` of the structure sheaf of rings
is a composite of definitions that are not reducible, so instance search does not see through it
and the scalar action on sections of a sheaf of modules typed this way is not found. Making the
links locally unfoldable is what lets it be found; this is the same declaration, for the same
reason, as in `StacksFrontier.Algebra.Category.ModuleCat.Sheaf.EtaSheafPullback`. -/
attribute [local instance_reducible] TopCat.Sheaf CategoryTheory.sheafCompose
  AlgebraicGeometry.SheafedSpace.sheaf Stacks.SheafOfModules.TensorSheafification.structureSheaf

open AlgebraicGeometry CategoryTheory Opposite TopologicalSpace MonoidalCategory

open scoped TensorProduct

open RingedSpaceModuleAdjunction (opensMap modulePullbackObjUnitIso)

open Stacks.RingedSpace (pullbackFunctor comparisonBifunctorIso pullbackUnit pullbackUnit_smul
  pullbackUnit_naturality sharp structureRingSheaf)

open Stacks.PullbackTensorCoherence (tmul pullbackTensorComparison pullback_tensor_hom_ext
  pullbackTensorComparison_pullbackUnit)

universe u

namespace Stacks.IdealTorsion.Eta

/- The monoidal structure of Tag 01CA on sheaves of modules, which is the one the section
formulas of `StacksFrontier.Algebra.Category.ModuleCat.Sheaf.PullbackTensorCoherence` are stated
over. It is a `local instance` there for the same reason as here: it is deliberately not global,
since a second monoidal structure on the same category exists. -/
attribute [local instance] Stacks.PullbackGradedAlgebra.monoidalCategory

/-! ### The degree-`0` ideal inclusion on local sections -/

/-- **The degree-`0` ideal inclusion on a local pure tensor**, at the ascribed spelling
`Stacks.PullbackTensorCoherence.tmul` of the pure tensor, which is the one the section formulas
of Tag 01CA are stated at. This is `idealPowerIncl_zero_app_toTensorSheafSection` with the two
spellings of the pure tensor crossed by `:=`. -/
theorem idealPowerIncl_zero_tmul (Z : RingedSpace.{u})
    (I : SheafOfModules.{u} ((Stacks.SheafOfModules.Tensor.ringSheaf Z.sheaf)))
    (ι : I ⟶ SheafOfModules.unit ((Stacks.SheafOfModules.Tensor.ringSheaf Z.sheaf)))
    [Stacks.SheafOfModules.IsInvertible Z.sheaf.obj
      ((Stacks.SheafOfModules.Tensor.ringSheaf Z.sheaf)).property I]
    (M : SheafOfModules.{u} ((Stacks.SheafOfModules.Tensor.ringSheaf Z.sheaf)))
    (U : (Opens Z.carrier)ᵒᵖ)
    (m : M.val.obj U) (a : I.val.obj U) :
    (idealPowerIncl Z I ι 0 M).val.app U (tmul Z M I U m a) =
      (M.val.obj U).isModule.toSMul.smul (Stacks.IdealTorsion.idealSection Z ι U a) m :=
  idealPowerIncl_zero_app_toTensorSheafSection Z I ι M U.unop m a

/-! ### The pullback of the ideal inclusion -/

variable {X Y : RingedSpace.{u}} (f : X ⟶ Y)

/-- **The pullback of an ideal inclusion**, `f^*ι : f^*I ⟶ 𝒪_X`: the pullback of `ι` followed by
the identification `f^*𝒪_Y ≅ 𝒪_X` of `RingedSpaceModuleAdjunction.modulePullbackObjUnitIso`,
which is invertible because the inverse-image functor on opens is final. -/
noncomputable def pullbackIdealIncl
    (I : SheafOfModules.{u} ((Stacks.SheafOfModules.Tensor.ringSheaf Y.sheaf)))
    (ι : I ⟶ SheafOfModules.unit ((Stacks.SheafOfModules.Tensor.ringSheaf Y.sheaf))) :
    (pullbackFunctor f).obj I ⟶
      SheafOfModules.unit ((Stacks.SheafOfModules.Tensor.ringSheaf X.sheaf)) :=
  (pullbackFunctor f).map ι ≫ (modulePullbackObjUnitIso f).hom

/-- The ambient section represented by `f^*ι` at the pullback-unit image of a section `a` of `I`
is the image under `f^♯` of the ambient section represented by `ι` at `a`. -/
theorem idealSection_pullbackIdealIncl
    (I : SheafOfModules.{u} ((Stacks.SheafOfModules.Tensor.ringSheaf Y.sheaf)))
    (ι : I ⟶ SheafOfModules.unit ((Stacks.SheafOfModules.Tensor.ringSheaf Y.sheaf)))
    (U : (Opens Y.carrier)ᵒᵖ)
    (a : I.val.obj U) :
    Stacks.IdealTorsion.idealSection X (pullbackIdealIncl f I ι) ((opensMap f).op.obj U)
        (pullbackUnit f I U a) =
      sharp f U (Stacks.IdealTorsion.idealSection Y ι U a) :=
  (pullbackUnit_naturality f ι U a ▸
      Stacks.PullbackAlgebra.pullbackUnitIso_hom_pullbackUnit f U
        (Stacks.IdealTorsion.idealSection Y ι U a) :
    (modulePullbackObjUnitIso f).hom.val.app ((opensMap f).op.obj U)
        (((pullbackFunctor f).map ι).val.app ((opensMap f).op.obj U)
          (pullbackUnit f I U a)) =
      sharp f U (Stacks.IdealTorsion.idealSection Y ι U a))

/-! ### Compatibility of the comparison of Stacks 01CD with the ideal inclusion -/

/-- **The canonical comparison of Stacks 01CD is compatible with the degree-`0` ideal
inclusion.** Both sides are morphisms out of the pullback `f^*(M ⊗ I)`, hence determined by
their values on the pullback-unit images of the local pure tensors; there the left-hand side is
`f^♯(ι(a))` acting on the pullback-unit image of `m` by the section formula for the inclusion
and the semilinearity of the pullback unit, and the right-hand side is the same by the section
formulas for the comparison, for the identification `f^*𝒪_Y ≅ 𝒪_X` and for the inclusion on
`X`. -/
theorem map_idealPowerIncl_zero
    (I : SheafOfModules.{u} ((Stacks.SheafOfModules.Tensor.ringSheaf Y.sheaf)))
    (ι : I ⟶ SheafOfModules.unit ((Stacks.SheafOfModules.Tensor.ringSheaf Y.sheaf)))
    [Stacks.SheafOfModules.IsInvertible Y.sheaf.obj
      ((Stacks.SheafOfModules.Tensor.ringSheaf Y.sheaf)).property I]
    (M : SheafOfModules.{u} ((Stacks.SheafOfModules.Tensor.ringSheaf Y.sheaf))) :
    (pullbackFunctor f).map (idealPowerIncl Y I ι 0 M) =
      pullbackTensorComparison f M I ≫
        idealPowerIncl X ((pullbackFunctor f).obj I) (pullbackIdealIncl f I ι) 0
          ((pullbackFunctor f).obj M) :=
  pullback_tensor_hom_ext f (A := M) (B := I) (N := (pullbackFunctor f).obj M) fun U m a ↦ by
    -- Each side is computed to `f^♯(ι(a)) • η(m)` by a chain of ground equations; the goal is
    -- not type-correct at `implicit` transparency, so neither `rw` nor `simp` can be used on
    -- it and every step is a term.
    have hleft : ((pullbackFunctor f).map (idealPowerIncl Y I ι 0 M)).val.app
          ((opensMap f).op.obj U) (pullbackUnit f (M ⊗ I) U (tmul Y M I U m a)) =
        sharp f U (Stacks.IdealTorsion.idealSection Y ι U a) • pullbackUnit f M U m :=
      (pullbackUnit_naturality f (idealPowerIncl Y I ι 0 M) U (tmul Y M I U m a)).trans
        ((congrArg (pullbackUnit f M U) (idealPowerIncl_zero_tmul Y I ι M U m a)).trans
          (pullbackUnit_smul f M U (Stacks.IdealTorsion.idealSection Y ι U a) m))
    have hright : (pullbackTensorComparison f M I ≫
          idealPowerIncl X ((pullbackFunctor f).obj I) (pullbackIdealIncl f I ι) 0
            ((pullbackFunctor f).obj M)).val.app ((opensMap f).op.obj U)
          (pullbackUnit f (M ⊗ I) U (tmul Y M I U m a)) =
        sharp f U (Stacks.IdealTorsion.idealSection Y ι U a) • pullbackUnit f M U m :=
      (SheafOfModules.comp_val_app_apply _ _ _ _).trans
        ((congrArg ((idealPowerIncl X ((pullbackFunctor f).obj I) (pullbackIdealIncl f I ι) 0
                ((pullbackFunctor f).obj M)).val.app ((opensMap f).op.obj U))
              (pullbackTensorComparison_pullbackUnit f M I U m a)).trans
          ((idealPowerIncl_zero_tmul X ((pullbackFunctor f).obj I) (pullbackIdealIncl f I ι)
                ((pullbackFunctor f).obj M) ((opensMap f).op.obj U) (pullbackUnit f M U m)
                (pullbackUnit f I U a)).trans
            (congrArg (fun r ↦ r • pullbackUnit f M U m)
              (idealSection_pullbackIdealIncl f I ι U a))))
    exact hleft.trans hright.symm

/-- **The compatibility of Stacks 01CD with the degree-`0` ideal inclusion**, with the
comparison spelled through the isomorphism of bifunctors
`Stacks.RingedSpace.comparisonBifunctorIso` and the pullback of the ideal inclusion written out.
This is the form that the transport of `Stacks.Equivalence.powIntertwineObj_incl` consumes as its
hypothesis `ha`, and it is `map_idealPowerIncl_zero` with the two spellings of the comparison
crossed by `:=`. -/
theorem comparisonBifunctorIso_app_hom_comp_idealPowerIncl_zero
    (I : SheafOfModules.{u} ((Stacks.SheafOfModules.Tensor.ringSheaf Y.sheaf)))
    (ι : I ⟶ SheafOfModules.unit ((Stacks.SheafOfModules.Tensor.ringSheaf Y.sheaf)))
    [Stacks.SheafOfModules.IsInvertible Y.sheaf.obj
      ((Stacks.SheafOfModules.Tensor.ringSheaf Y.sheaf)).property I]
    (M : SheafOfModules.{u} ((Stacks.SheafOfModules.Tensor.ringSheaf Y.sheaf))) :
    (pullbackFunctor f).map (idealPowerIncl Y I ι 0 M) =
      ((comparisonBifunctorIso f).app (M, I)).hom ≫
        idealPowerIncl X ((pullbackFunctor f).obj I)
          ((pullbackFunctor f).map ι ≫ (modulePullbackObjUnitIso f).hom) 0
          ((pullbackFunctor f).obj M) :=
  map_idealPowerIncl_zero f I ι M

end Stacks.IdealTorsion.Eta

end
