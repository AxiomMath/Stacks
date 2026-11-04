module

public import StacksFrontier.AlgebraicGeometry.Descent.AssociatedModule.SmallEtaleOpenCoverQuasicoherence
public import StacksFrontier.AlgebraicGeometry.Descent.AssociatedModule.SmallEtaleMorphismBaseChange
public import StacksFrontier.AlgebraicGeometry.Topologies.Etale.SmallEtalePullbackSections

/-!
# The final object of the small étale site and the open `⊤`

The small étale site of a scheme `S` has two final objects: `S / S` with the identity structure
morphism, by `AlgebraicGeometry.SmallEtale.finalIsTerminal`, and the image of the open `⊤` of `S`
under the inclusion of the small Zariski site, by
`AlgebraicGeometry.SmallEtale.isTerminalOpensObjTop`. This file gives the isomorphism between them,
and describes the sections of the right adjoint `AlgebraicGeometry.SmallEtale.restrictModule` of
the associated-module functor: over an open `V` of `S` they are the sections over
`AlgebraicGeometry.SmallEtale.opensObj`, and over `⊤` they are the sections over the final object.

## Main definitions

* `AlgebraicGeometry.SmallEtale.finalIsoOpensObjTop`: the final object `S / S` of the small étale
  site is the open `⊤`.

## Main results

* `AlgebraicGeometry.SmallEtale.restrictModule_obj_presheaf_obj`: the sections of the restriction
  of a sheaf of modules over an open `V` are its sections over `V` as a small étale object.
* `AlgebraicGeometry.SmallEtale.restrictModuleSectionsTopIso`: the sections of the restriction over
  `⊤` are the sections over the final object.
* `AlgebraicGeometry.SmallEtale.finalToBaseChangeFinal_comp_baseChangeOpensIso_inv_app_top`: **the
  value of `AlgebraicGeometry.SmallEtale.baseChangeOpensIso` at `⊤`, against the canonical arrow to
  the base change of the final object.**

## References

* [Stacks Project, Tag 021D](https://stacks.math.columbia.edu/tag/021D)
* [Stacks Project, Tag 03DU](https://stacks.math.columbia.edu/tag/03DU)
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits Opposite

universe u

namespace AlgebraicGeometry.SmallEtale

variable (B : BigEtaleSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)

/-- **The final object of the small étale site of `S` is the open `⊤`.** The unique isomorphism
between the terminal objects `AlgebraicGeometry.SmallEtale.final`, the object `S / S` with identity
structure morphism, and `AlgebraicGeometry.SmallEtale.opensObj B S hS ⊤`. -/
public noncomputable def finalIsoOpensObjTop : final B S hS ≅ opensObj B S hS ⊤ :=
  (finalIsTerminal B S hS).uniqueUpToIso (isTerminalOpensObjTop B S hS)

/-- **Restriction along the inclusion of the small Zariski site does not move sections.** The
sections of `AlgebraicGeometry.SmallEtale.restrictModule` applied to `M` over an open `V` of `S`
are the sections of `M` over `V` read as a small étale object. -/
public theorem restrictModule_obj_presheaf_obj
    (M : SheafOfModules.{u} (structureSheaf B S hS)) (V : S.Opens) :
    ((restrictModule B S hS).obj M).presheaf.obj (op V) =
      M.val.presheaf.obj (op (opensObj B S hS V)) :=
  rfl

/-- **The sections of a restriction over `⊤` are the sections over the final object.** The
isomorphism is restriction along `AlgebraicGeometry.SmallEtale.finalIsoOpensObjTop`. -/
public noncomputable def restrictModuleSectionsTopIso
    (M : SheafOfModules.{u} (structureSheaf B S hS)) :
    ((restrictModule B S hS).obj M).presheaf.obj (op (⊤ : S.Opens)) ≅
      M.val.presheaf.obj (op (final B S hS)) :=
  M.val.presheaf.mapIso (finalIsoOpensObjTop B S hS).op

/-- The forward map of `AlgebraicGeometry.SmallEtale.restrictModuleSectionsTopIso` is restriction
along the isomorphism of the two final objects. -/
public theorem restrictModuleSectionsTopIso_hom
    (M : SheafOfModules.{u} (structureSheaf B S hS)) :
    (restrictModuleSectionsTopIso B S hS M).hom =
      M.val.presheaf.map (finalIsoOpensObjTop B S hS).hom.op :=
  rfl

section BaseChange

variable {X Y : B.Scheme} (a : X ⟶ Y)

/-- **The value of `AlgebraicGeometry.SmallEtale.baseChangeOpensIso` at `⊤`.** The canonical arrow
from the final object of the small étale site of `X` to the base change along `a` of the final
object of the small étale site of `Y`, followed by the identification of that base change with the
preimage of the open `⊤`, is the identification of the final object of the small étale site of `X`
with the open `⊤`. -/
public theorem finalToBaseChangeFinal_comp_baseChangeOpensIso_inv_app_top :
    (smallEtaleBaseChange_finalIsTerminal B a).from (final B X.obj X.property) ≫
        (smallEtaleBaseChange B a).map (finalIsoOpensObjTop B Y.obj Y.property).hom ≫
        (baseChangeOpensIso B a).inv.app ⊤ =
      (finalIsoOpensObjTop B X.obj X.property).hom :=
  Subsingleton.elim (h := subsingleton_hom_opensToSmallEtale B X.obj X.property _ _) _ _

end BaseChange

end AlgebraicGeometry.SmallEtale

end
