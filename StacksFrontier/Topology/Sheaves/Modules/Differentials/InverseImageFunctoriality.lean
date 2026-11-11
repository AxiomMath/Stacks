module

public import StacksFrontier.Algebra.Category.ModuleCat.Sheaf.DifferentialsFunctorial
public import StacksFrontier.Topology.Sheaves.Modules.Differentials.Functoriality
import StacksCore.Tactic.StacksAttribute

/-!
# The inverse-image description of the canonical map of differentials

For a commutative square of ringed spaces
```
  X' --f--> X
  |h'       |h
  v         v
  S' --g--> S
```
Stacks Tag 08RU builds a map `f⁻¹Ω_{X/S} ⟶ Ω_{X'/S'}` of `f⁻¹𝒪_X`-modules from the
identification `f⁻¹Ω_{X/S} ≅ Ω_{f⁻¹𝒪_X/f⁻¹h⁻¹𝒪_S}` of Tag 08RR and the functoriality of
Tag 08RS for the square of sheaves of rings
```
  f⁻¹h⁻¹𝒪_S ---> f⁻¹𝒪_X
      |             |
      v             v
  h'⁻¹𝒪_{S'} --->  𝒪_{X'}
```
and states that it corresponds, under `f^*Ω_{X/S} = f⁻¹Ω_{X/S} ⊗ 𝒪_{X'}`, to the canonical
map `c_f : f^*Ω_{X/S} ⟶ Ω_{X'/S'}`. This file builds that map independently of `c_f` and
proves the agreement.

## Main definitions

* `AlgebraicGeometry.SheafOfModules.inverseImageRingsDifferentialMap`: the map of Tag 08RS for
  the square of sheaves of rings.
* `AlgebraicGeometry.SheafOfModules.inverseImageDifferentialMapOfFunctoriality`: the morphism
  `f⁻¹Ω_{X/S} ⟶ Ω_{X'/S'}` built from Tags 08RR and 08RS.

## Main results

* `AlgebraicGeometry.SheafOfModules.inverseImageDifferentialMapOfFunctoriality_d`: that
  morphism sends the inverse image of `d a` to `d (f^♯ a)`.
* `AlgebraicGeometry.SheafOfModules.inverseImageToPullback_comp_differentialMap`: the
  tensor-unit map `f⁻¹Ω_{X/S} ⟶ f^*Ω_{X/S}` followed by `c_f` is that morphism.

## Implementation notes

The map of Tag 08RS, `Stacks.Sheaves.DifferentialsFunctorial.differentialMap`, is stated for
the sheafified sectionwise differentials, while Tag 08RR and `c_f` use the corepresenting ones;
the two are identified by `moduleOfDifferentialsIsoSectionwise`, compatibly with the universal
derivations. The agreement is proved through the universal property of `f⁻¹Ω_{X/S}`
(`inverseImageDerivation_isUniversal` together with the bijectivity
`isInverseImageDerivationComparison`): a morphism out of it is determined by its values on the
inverse images of the differentials `d a`, and both sides send these to `d (f^♯ a)`.

## References

* [Stacks Project, Tag 08RU](https://stacks.math.columbia.edu/tag/08RU)
* [Stacks Project, Tag 08RR](https://stacks.math.columbia.edu/tag/08RR)
* [Stacks Project, Tag 08RS](https://stacks.math.columbia.edu/tag/08RS)
-/

@[expose] public section

open CategoryTheory TopologicalSpace

open Stacks.Sheaves.RingedSpaceDifferentials (inverseImageStructureMap)

universe u

namespace AlgebraicGeometry.SheafOfModules

/-- A morphism out of the inverse image `p⁻¹Ω_{O₂/O₁}` of a module of differentials is
determined by its values on the inverse-image sections of the differentials `d b` of local
sections `b` of `O₂`. -/
private theorem inverseImageDifferentials_hom_ext {Y Z : TopCat.{u}} (p : Y ⟶ Z)
    {O₁ O₂ : TopCat.Sheaf CommRingCat.{u} Z} (phi : O₁ ⟶ O₂)
    {F : _root_.SheafOfModules.{u}
      (underlyingRingSheaf ((TopCat.Sheaf.pullback CommRingCat.{u} p).obj O₂))}
    {m₁ m₂ : inverseImageModule p O₂ (moduleOfDifferentials.{u, u, u} phi) ⟶ F}
    (hm : ∀ (U : (Opens Z)ᵒᵖ) (b : O₂.obj.obj U),
      (m₁.val.app ((opensMap p).op.obj U)).hom
          (((inverseImageModuleUnit p O₂ (moduleOfDifferentials.{u, u, u} phi)).val.app U).hom
            ((universalDerivation.{u, u, u} phi).d b)) =
        (m₂.val.app ((opensMap p).op.obj U)).hom
          (((inverseImageModuleUnit p O₂ (moduleOfDifferentials.{u, u, u} phi)).val.app U).hom
            ((universalDerivation.{u, u, u} phi).d b))) :
    m₁ = m₂ := by
  let δ := (inverseImageDerivation p (universalDerivation.{u, u, u} phi)).val
  have hδ : δ.postcomp m₁.val = δ.postcomp m₂.val := by
    apply (isInverseImageDerivationComparison p phi F).1
    rw [pushforwardInverseImageDerivation_postcomp, pushforwardInverseImageDerivation_postcomp,
      pushforwardInverseImageDerivation_inverseImageDerivation]
    ext U b
    exact hm U b
  exact (inverseImageDerivation_isUniversal p phi F (δ.postcomp m₁.val)).unique rfl hδ.symm

/-- The map of Tag 08RS for the square of sheaves of commutative rings on `X'`
```
  f⁻¹h⁻¹𝒪_S ---> f⁻¹𝒪_X
      |             |
      v             v
  h'⁻¹𝒪_{S'} --->  𝒪_{X'}
```
attached to a commutative square of ringed spaces: the canonical map
`Ω_{f⁻¹𝒪_X/f⁻¹h⁻¹𝒪_S} ⟶ Ω_{X'/S'}` of `f⁻¹𝒪_X`-modules. It is
`Stacks.Sheaves.DifferentialsFunctorial.differentialMap`, read on the corepresenting modules of
differentials through `moduleOfDifferentialsIsoSectionwise`. -/
noncomputable def inverseImageRingsDifferentialMap {X' X S' S : RingedSpace.{u, u}}
    (f : X' ⟶ X) (h : X ⟶ S) (h' : X' ⟶ S') (g : S' ⟶ S) (hcomm : f ≫ h = h' ≫ g) :
    moduleOfDifferentials.{u, u, u}
        ((TopCat.Sheaf.pullback CommRingCat f.hom.base).map (inverseImageStructureMap h)) ⟶
      inverseImageDifferentialTarget f h' :=
  (moduleOfDifferentialsIsoSectionwise.{u, u}
      ((TopCat.Sheaf.pullback CommRingCat f.hom.base).map (inverseImageStructureMap h))).hom ≫
    Stacks.Sheaves.DifferentialsFunctorial.differentialMap
      (C := Opens X'.carrier) (J := Opens.grothendieckTopology X'.carrier)
      ((TopCat.Sheaf.pullback CommRingCat f.hom.base).map (inverseImageStructureMap h))
      (inverseImageStructureMap h') (inverseImageStructureMap f)
      (inverseImageBaseChangeMap f h h' g hcomm) (inverseImageBaseChangeMap_comm f h h' g hcomm) ≫
    (_root_.SheafOfModules.restrictScalars (inverseImageStructureRingMap f)).map
      (moduleOfDifferentialsIsoSectionwise.{u, u} (inverseImageStructureMap h')).inv

/-- The inverse of the comparison with the sectionwise differentials sends the sectionwise
differential of a local section to its universal differential. -/
private theorem moduleOfDifferentialsIsoSectionwise_inv_d {Z : TopCat.{u}}
    {O₁ O₂ : TopCat.Sheaf CommRingCat.{u} Z} (phi : O₁ ⟶ O₂) {U : (Opens Z)ᵒᵖ}
    (a : O₂.obj.obj U) :
    ((moduleOfDifferentialsIsoSectionwise.{u, u} phi).inv.val.app U).hom
        ((sectionwiseDerivation.{u, u} phi).d a) =
      (universalDerivation.{u, u, u} phi).d a := by
  rw [← PresheafOfModulesOfCommRing.Derivation.congr_d
    (moduleOfDifferentialsIsoSectionwise_compatible.{u, u} phi) a]
  exact congrArg (fun m : moduleOfDifferentials.{u, u, u} phi ⟶
      moduleOfDifferentials.{u, u, u} phi =>
        (m.val.app U).hom ((universalDerivation.{u, u, u} phi).d a))
    (moduleOfDifferentialsIsoSectionwise.{u, u} phi).hom_inv_id

/-- The structural map `f⁻¹𝒪_X ⟶ 𝒪_{X'}` sends the inverse-image section of a local section
`b` of `𝒪_X` to `f^♯ b`. -/
private theorem inverseImageStructureMap_app_inverseImageRingHom {X' X : RingedSpace.{u, u}}
    (f : X' ⟶ X) (U : (Opens X.carrier)ᵒᵖ) (b : X.presheaf.obj U) :
    ((inverseImageStructureMap f).hom.app ((opensMap f.hom.base).op.obj U)).hom
        (((inverseImageRingHom f.hom.base X.sheaf).hom.app U).hom b) =
      (f.hom.c.app U).hom b :=
  congrArg (fun m => (m.hom.app U).hom b) (inverseImageRingHom_comp_structureSheafHom f)

/-- The map of Tag 08RS for the square of rings sends the differential of the inverse-image
section of a local section `b` of `𝒪_X` to `d (f^♯ b)`. -/
private theorem inverseImageRingsDifferentialMap_d {X' X S' S : RingedSpace.{u, u}}
    (f : X' ⟶ X) (h : X ⟶ S) (h' : X' ⟶ S') (g : S' ⟶ S) (hcomm : f ≫ h = h' ≫ g)
    (U : (Opens X.carrier)ᵒᵖ) (b : X.presheaf.obj U) :
    ((inverseImageRingsDifferentialMap f h h' g hcomm).val.app
        ((opensMap f.hom.base).op.obj U)).hom
      ((universalDerivation.{u, u, u}
          ((TopCat.Sheaf.pullback CommRingCat f.hom.base).map (inverseImageStructureMap h))).d
        (((inverseImageRingHom f.hom.base X.sheaf).hom.app U).hom b)) =
      (universalDerivation (inverseImageStructureMap h')).d ((f.hom.c.app U).hom b) := by
  let ι := (TopCat.Sheaf.pullback CommRingCat f.hom.base).map (inverseImageStructureMap h)
  let x := ((inverseImageRingHom f.hom.base X.sheaf).hom.app U).hom b
  have h1 : ((moduleOfDifferentialsIsoSectionwise.{u, u} ι).hom.val.app
        ((opensMap f.hom.base).op.obj U)).hom ((universalDerivation.{u, u, u} ι).d x) =
      (sectionwiseDerivation.{u, u} ι).d x :=
    PresheafOfModulesOfCommRing.Derivation.congr_d
      (moduleOfDifferentialsIsoSectionwise_compatible ι) x
  have h2 := Stacks.Sheaves.DifferentialsFunctorial.differentialMap_comp_d
    (C := Opens X'.carrier) (J := Opens.grothendieckTopology X'.carrier) ι
    (inverseImageStructureMap h') (inverseImageStructureMap f)
    (inverseImageBaseChangeMap f h h' g hcomm) (inverseImageBaseChangeMap_comm f h h' g hcomm) x
  have h3 := moduleOfDifferentialsIsoSectionwise_inv_d (inverseImageStructureMap h')
    (((inverseImageStructureMap f).hom.app ((opensMap f.hom.base).op.obj U)).hom x)
  show ((moduleOfDifferentialsIsoSectionwise.{u, u} (inverseImageStructureMap h')).inv.val.app
      ((opensMap f.hom.base).op.obj U)).hom
        (((Stacks.Sheaves.DifferentialsFunctorial.differentialMap
          (C := Opens X'.carrier) (J := Opens.grothendieckTopology X'.carrier) ι
          (inverseImageStructureMap h') (inverseImageStructureMap f)
          (inverseImageBaseChangeMap f h h' g hcomm)
          (inverseImageBaseChangeMap_comm f h h' g hcomm)).val.app
            ((opensMap f.hom.base).op.obj U)).hom
          (((moduleOfDifferentialsIsoSectionwise.{u, u} ι).hom.val.app
            ((opensMap f.hom.base).op.obj U)).hom ((universalDerivation.{u, u, u} ι).d x))) = _
  rw [h1]
  exact (congrArg _ h2).trans (h3.trans (congrArg _
    (inverseImageStructureMap_app_inverseImageRingHom f U b)))

/-- **Tag 08RU, the map `f⁻¹Ω_{X/S} ⟶ Ω_{X'/S'}` built from Tags 08RR and 08RS.** For a
commutative square of ringed spaces
```
  X' --f--> X
  |h'       |h
  v         v
  S' --g--> S
```
this is the identification `f⁻¹Ω_{X/S} ≅ Ω_{f⁻¹𝒪_X/f⁻¹h⁻¹𝒪_S}` of Tag 08RR
(`pullbackDifferentialsIso`), followed by the map of Tag 08RS
(`inverseImageRingsDifferentialMap`) for the square of sheaves of rings
`f⁻¹h⁻¹𝒪_S ⟶ h'⁻¹𝒪_{S'}`, `f⁻¹𝒪_X ⟶ 𝒪_{X'}`. It is a map of `f⁻¹𝒪_X`-modules, the target
carrying its scalars restricted along `f⁻¹𝒪_X ⟶ 𝒪_{X'}`, and it is constructed without
reference to the canonical map `c_f = differentialMap`. -/
@[stacks 08RU "the map f^{-1}Omega_{X/S} -> Omega_{X'/S'} from 08RR and 08RS"]
noncomputable def inverseImageDifferentialMapOfFunctoriality {X' X S' S : RingedSpace.{u, u}}
    (f : X' ⟶ X) (h : X ⟶ S) (h' : X' ⟶ S') (g : S' ⟶ S) (hcomm : f ≫ h = h' ≫ g) :
    inverseImageModule f.hom.base X.sheaf
      (moduleOfDifferentials (inverseImageStructureMap h)) ⟶
        inverseImageDifferentialTarget f h' :=
  (pullbackDifferentialsIso f.hom.base (inverseImageStructureMap h)).hom ≫
    inverseImageRingsDifferentialMap f h h' g hcomm

/-- The map built from Tags 08RR and 08RS sends the inverse image of the differential `d a` of
a local section `a` of `𝒪_X` to `d (f^♯ a)`. -/
theorem inverseImageDifferentialMapOfFunctoriality_d {X' X S' S : RingedSpace.{u, u}}
    (f : X' ⟶ X) (h : X ⟶ S) (h' : X' ⟶ S') (g : S' ⟶ S) (hcomm : f ≫ h = h' ≫ g)
    (U : (Opens X.carrier)ᵒᵖ) (a : X.presheaf.obj U) :
    ((inverseImageDifferentialMapOfFunctoriality f h h' g hcomm).val.app
        ((opensMap f.hom.base).op.obj U)).hom
      (((inverseImageModuleUnit f.hom.base X.sheaf
          (moduleOfDifferentials (inverseImageStructureMap h))).val.app U).hom
        ((universalDerivation (inverseImageStructureMap h)).d a)) =
      (universalDerivation (inverseImageStructureMap h')).d ((f.hom.c.app U).hom a) := by
  have hδ := (inverseImageDerivation f.hom.base
    (universalDerivation.{u, u, u} (inverseImageStructureMap h))).property U a
  have hiso := PresheafOfModulesOfCommRing.Derivation.congr_d
    (pullbackDifferentialsIso_compatible f.hom.base (inverseImageStructureMap h))
    (((inverseImageRingHom f.hom.base X.sheaf).hom.app U).hom a)
  show ((inverseImageRingsDifferentialMap f h h' g hcomm).val.app
      ((opensMap f.hom.base).op.obj U)).hom
    (((pullbackDifferentialsIso f.hom.base (inverseImageStructureMap h)).hom.val.app
      ((opensMap f.hom.base).op.obj U)).hom
        (((inverseImageModuleUnit f.hom.base X.sheaf
          (moduleOfDifferentials (inverseImageStructureMap h))).val.app U).hom
        ((universalDerivation (inverseImageStructureMap h)).d a))) = _
  rw [← hδ]
  exact (congrArg _ hiso).trans (inverseImageRingsDifferentialMap_d f h h' g hcomm U a)

/-- **Tag 08RU, agreement of the inverse-image map with `c_f`.** Under the identification
`f^*Ω_{X/S} = f⁻¹Ω_{X/S} ⊗ 𝒪_{X'}`, the canonical map `c_f = differentialMap` corresponds to
the map `f⁻¹Ω_{X/S} ⟶ Ω_{X'/S'}` built from Tags 08RR and 08RS: the composite
`f⁻¹Ω_{X/S} ⟶ f^*Ω_{X/S} ⟶ Ω_{X'/S'}` of the tensor-unit map with `c_f` is
`inverseImageDifferentialMapOfFunctoriality`. The proof is by the universal property of
`f⁻¹Ω_{X/S}`: both maps send the inverse image of `d a` to `d (f^♯ a)`. -/
@[stacks 08RU "agreement of the 08RR/08RS map with c_f under f^*Omega = f^{-1}Omega ⊗ O_{X'}"]
theorem inverseImageToPullback_comp_differentialMap {X' X S' S : RingedSpace.{u, u}}
    (f : X' ⟶ X) (h : X ⟶ S) (h' : X' ⟶ S') (g : S' ⟶ S) (hcomm : f ≫ h = h' ≫ g) :
    inverseImageToPullback f (moduleOfDifferentials (inverseImageStructureMap h)) ≫
        (_root_.SheafOfModules.restrictScalars (inverseImageStructureRingMap f)).map
          (differentialMap f h h' g hcomm) =
      inverseImageDifferentialMapOfFunctoriality f h h' g hcomm := by
  refine inverseImageDifferentials_hom_ext f.hom.base (inverseImageStructureMap h) ?_
  intro U a
  refine Eq.trans ?_ (inverseImageDifferentialMapOfFunctoriality_d f h h' g hcomm U a).symm
  let Ω := moduleOfDifferentials (inverseImageStructureMap h)
  let Ω' := moduleOfDifferentials (inverseImageStructureMap h')
  let adj := RingedSpaceModuleAdjunction.modulePullbackPushforwardAdjunction f
  have ht := (Classical.choose_spec (existsUnique_inverseImageToPullback f Ω)).1 U.unop
    ((universalDerivation (inverseImageStructureMap h)).d a)
  have hc := (Classical.choose_spec (existsUnique_differentialMap f h h' g hcomm)).1 U.unop a
  have hu : RingedSpaceModuleAdjunction.homEquiv f Ω' Ω (differentialMap f h h' g hcomm) =
      adj.unit.app Ω ≫ (RingedSpaceModuleAdjunction.modulePushforward f).map
        (differentialMap f h h' g hcomm) :=
    Adjunction.homEquiv_unit adj Ω Ω' (differentialMap f h h' g hcomm)
  change ((RingedSpaceModuleAdjunction.homEquiv f Ω' Ω
    (differentialMap f h h' g hcomm)).val.app (.op U.unop)).hom
      ((universalDerivation (inverseImageStructureMap h)).d a) = _ at hc
  rw [hu] at hc
  show ((differentialMap f h h' g hcomm).val.app ((opensMap f.hom.base).op.obj U)).hom
    (((inverseImageToPullback f Ω).val.app (.op ((Opens.map f.hom.base).obj U.unop))).hom
      (((inverseImageModuleUnit f.hom.base X.sheaf Ω).val.app (.op U.unop)).hom
        ((universalDerivation (inverseImageStructureMap h)).d a))) = _
  rw [show inverseImageToPullback f Ω = Classical.choose
    (existsUnique_inverseImageToPullback f Ω) from rfl, ht]
  exact hc

end AlgebraicGeometry.SheafOfModules
