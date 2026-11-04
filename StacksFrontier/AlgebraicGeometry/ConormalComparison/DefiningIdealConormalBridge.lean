module

public import StacksFrontier.AlgebraicGeometry.Conormal.Stalk
public import StacksFrontier.AlgebraicGeometry.ConormalComparison.IdealSheafComparison
public import StacksFrontier.AlgebraicGeometry.ConormalComparison.SitesConormalComparison
public import StacksFrontier.AlgebraicGeometry.ConormalSheaf.Basic
public import StacksFrontier.Algebra.Category.ModuleCat.Sheaf.SubmoduleKer

/-!
# The submodule and the categorical ideal sheaf of an immersion agree

For an immersion `i : Z ⟶ X` of schemes the ideal sheaf of the canonical closed factor
`i.liftCoborder` is written in two ways here. One is the *sectionwise* kernel of
`𝒪_{i.coborderRange} ⟶ (i.liftCoborder)_* 𝒪_Z`, the ideal subsheaf
`Stacks.AlgebraicGeometry.RegularIdealSheaf.definingIdeal i`. The other is the *categorical*
kernel of the same morphism, `Stacks.Conormal.Sites.idealSheafLift i`. The two carry the same
sections, but they are different terms.

This file gives the isomorphism between them and transports it along the module pullback to an
isomorphism of the two conormal sheaves, together with its compatibility with the two inclusions
into the structure sheaf, both as an equation of morphisms and section by section, and with the
two canonical maps `ℐ ⟶ (i.liftCoborder)_* (ℐ/ℐ²)`.

## Main definitions

* `idealSheafBridge i`: the isomorphism `(definingIdeal i).toSheafOfModules ≅ idealSheafLift i`
  of sheaves of modules on `i.coborderRange`.
* `conormalSheafBridge i`: the isomorphism `RegularIdealSheaf.conormalSheaf i ≅
  Stacks.Conormal.conormalSheaf i` of sheaves of modules on `Z`.

## Main results

* `idealSheafBridge_hom_comp_idealIota` and `idealSheafBridge_inv_comp_ι`: `idealSheafBridge i`
  is compatible with the inclusion of the categorical kernel and with the inclusion of the
  submodule.
* `idealSection_idealSheafBridge_hom`: section by section, `idealSheafBridge i` changes nothing —
  the image of a section `s` of the defining ideal has `s.1` as its underlying section of
  `𝒪_{i.coborderRange}`.
* `conormalComparison_comp_conormalSheafBridge`: `conormalSheafBridge i` carries
  `RegularIdealSheaf.conormalComparison i` to the unit of the pullback-pushforward adjunction
  at `idealSheafLift i`.

## Implementation notes

`Stacks.AlgebraicGeometry.RegularIdealSheaf.kernelSubmodule` and
`SheafOfModules.Submodule.ker` are the same construction: the underlying family of submodules
is `LinearMap.ker` of the component of the morphism on both sides, and the remaining fields are
proofs. So `definingIdeal i` is definitionally `SheafOfModules.Submodule.ker` of the
structure-sheaf map, and `idealSheafBridge` is `SheafOfModules.Submodule.kerIsoKernel` at that
map.

## References

* [Stacks Project, Lemma 31.21.3 (Tag 063E)](https://stacks.math.columbia.edu/tag/063E)
* [Stacks Project, Definition 31.21.4 (Tag 063J)](https://stacks.math.columbia.edu/tag/063J)
* [Stacks Project, Lemma 25.11.3 (Tag 01R3)](https://stacks.math.columbia.edu/tag/01R3)
* [Stacks Project, Lemma 29.25.2 (Tag 01UZ)](https://stacks.math.columbia.edu/tag/01UZ)
-/

@[expose] public section

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits Opposite
open RingedSpaceModuleAdjunction

universe u

namespace Stacks.Conormal.DefiningIdealBridge

variable {Z X : Scheme.{u}} (i : Z ⟶ X) [IsImmersion i]

/-- **The two ideal sheaves of the closed factor of an immersion agree.** The sheaf of modules
attached to the ideal subsheaf `Stacks.AlgebraicGeometry.RegularIdealSheaf.definingIdeal i`,
whose sections over an open are the sections of `𝒪_{i.coborderRange}` killed by
`i.liftCoborder`, is the categorical kernel `Stacks.Conormal.Sites.idealSheafLift i` of the
same structure-sheaf map. -/
noncomputable def idealSheafBridge :
    (Stacks.AlgebraicGeometry.RegularIdealSheaf.definingIdeal i).toSheafOfModules ≅
      Stacks.Conormal.Sites.idealSheafLift i :=
  SheafOfModules.Submodule.kerIsoKernel
    (SheafOfModules.unitToPushforwardObjUnit
      (structureSheafHom i.liftCoborder.toLRSHom.toShHom))

/-- `idealSheafBridge i` is compatible with the two inclusions into `𝒪_{i.coborderRange}`:
composing it with the inclusion of the categorical kernel gives the inclusion of the defining
ideal. -/
@[reassoc]
theorem idealSheafBridge_hom_comp_idealIota :
    (idealSheafBridge i).hom ≫ Stacks.Conormal.Sites.idealIota i =
      (Stacks.AlgebraicGeometry.RegularIdealSheaf.definingIdeal i).ι :=
  SheafOfModules.Submodule.kerIsoKernel_hom_comp_ι _

/-- The inverse of `idealSheafBridge i` is compatible with the two inclusions in the other
direction. -/
@[reassoc]
theorem idealSheafBridge_inv_comp_ι :
    (idealSheafBridge i).inv ≫
        (Stacks.AlgebraicGeometry.RegularIdealSheaf.definingIdeal i).ι =
      Stacks.Conormal.Sites.idealIota i :=
  SheafOfModules.Submodule.kerIsoKernel_inv_comp_ι _

/-- **`idealSheafBridge i` changes no section.** A section `s` of the defining ideal sheaf over
an open `V` of `i.coborderRange` is a section of `𝒪_{i.coborderRange}` together with a proof
that it dies in `(i.liftCoborder)_* 𝒪_Z`; its image under `idealSheafBridge i` has exactly `s.1`
as its underlying section of the structure sheaf. -/
theorem idealSection_idealSheafBridge_hom (V : i.coborderRange.toScheme.Opens)
    (s : (Stacks.AlgebraicGeometry.RegularIdealSheaf.definingIdeal
      i).toSheafOfModules.val.obj (op V)) :
    Stacks.Conormal.idealSection i.liftCoborder V
        ((idealSheafBridge i).hom.val.app (op V) s) = s.1 :=
  congrArg (fun g => (g.val.app (op V)).hom s) (idealSheafBridge_hom_comp_idealIota i)

/-- **The two conormal sheaves of an immersion agree.** Both are the module pullback along
`i.liftCoborder` of an ideal sheaf of that closed factor, so this is `idealSheafBridge`
transported along that pullback. -/
noncomputable def conormalSheafBridge :
    Stacks.AlgebraicGeometry.RegularIdealSheaf.conormalSheaf i ≅
      Stacks.Conormal.conormalSheaf i :=
  (modulePullback i.liftCoborder.toLRSHom.toShHom).mapIso (idealSheafBridge i)

/-- **`conormalSheafBridge i` matches the two canonical maps out of the ideal sheaf.** The
square formed by `Stacks.AlgebraicGeometry.RegularIdealSheaf.conormalComparison i`, the unit of
`i.liftCoborder^* ⊣ (i.liftCoborder)_*` at `Stacks.Conormal.Sites.idealSheafLift i`,
`idealSheafBridge i` and the pushforward of `conormalSheafBridge i` commutes. -/
theorem conormalComparison_comp_conormalSheafBridge :
    Stacks.AlgebraicGeometry.RegularIdealSheaf.conormalComparison i ≫
        (modulePushforward i.liftCoborder.toLRSHom.toShHom).map
          (conormalSheafBridge i).hom =
      (idealSheafBridge i).hom ≫
        (modulePullbackPushforwardAdjunction i.liftCoborder.toLRSHom.toShHom).unit.app
          (Stacks.Conormal.Sites.idealSheafLift i) :=
  ((modulePullbackPushforwardAdjunction i.liftCoborder.toLRSHom.toShHom).unit.naturality
    (idealSheafBridge i).hom).symm

end Stacks.Conormal.DefiningIdealBridge

end
