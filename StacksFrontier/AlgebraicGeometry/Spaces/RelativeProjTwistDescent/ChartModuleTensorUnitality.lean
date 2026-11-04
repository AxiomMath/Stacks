module

public import
    StacksFrontier.AlgebraicGeometry.Spaces.RelativeProjTwistDescent.ChartModuleTensorCoherence
public import StacksFrontier.AlgebraicGeometry.Spaces.RelativeProjTwistDescent.ChartModuleUnitPullback

/-!
# The tensor identification of Stacks 03DX (2) on a representable is compatible with the unitors

For quasi-coherent modules on the scheme underlying an object `U` of the big fppf site,
`AlgebraicGeometry.Space.representedQuasicoherentSchemeTensorIso` identifies the module attached
by Stacks 03DX (2) to `M ⊗ N` with the tensor product of the attached modules, and
`AlgebraicGeometry.Space.representedQuasicoherentSchemeUnitIso` identifies the module attached
to `𝒪_U` with `𝒪_{yoneda U}`.  This file proves that, together, they are compatible with the left
unitors: on the scheme that of the tensor product sheaf of Tag 01CA, on `yoneda.obj U` that of
the monoidal structure `AlgebraicGeometry.Space.modulesMonoidalCategory`.

## Main definitions

* `AlgebraicGeometry.Space.quasicoherentLeftUnitor`: the left unitor of the tensor product sheaf
  of Tag 01CA, from the quasi-coherent tensor product `𝒪_U ⊗ M` to `M`.

## Main results

* `Stacks.SheafOfModules.pullbackTensorIsoTransport_comp_leftUnitality_of_iso`: the left unit
  coherence of a composite of two comparisons of Stacks 03EL, with the identification of the
  units given as an isomorphism together with its expression as a composite.
* `AlgebraicGeometry.Space.representedQuasicoherentSchemeTensorIso_leftUnitality`: **the tensor
  identification of Stacks 03DX (2) is compatible with the left unitors.**

## Implementation notes

The unit identification is a composite of two isomorphisms whose first factor is the image of an
isomorphism under the comparison of Stacks 04M0.  Equating its underlying morphism with the
composite of the underlying morphisms exhausts the heartbeat budget, while the equation between
isomorphisms holds by `rfl` at once; so the generic coherence takes that equation between
isomorphisms, and the instance supplies it by
`AlgebraicGeometry.Space.representedQuasicoherentSchemeUnitIso_eq`, as
`AlgebraicGeometry.Space.representedQuasicoherentSchemeTensorIso_associativity` supplies its
tensor identifications by `representedQuasicoherentSchemeTensorIso_eq`.

## References

* [Stacks Project, Tag 01CA](https://stacks.math.columbia.edu/tag/01CA)
* [Stacks Project, Tag 03DX](https://stacks.math.columbia.edu/tag/03DX)
* [Stacks Project, Tag 03EL](https://stacks.math.columbia.edu/tag/03EL)
* [Stacks Project, Tag 084D](https://stacks.math.columbia.edu/tag/084D)
-/

@[expose] public noncomputable section

open CategoryTheory MonoidalCategory

namespace Stacks.SheafOfModules

universe w₁ w₂ w₃ v₁ v₂ v₃ u₁ u₂ u₃

attribute [local instance] Strict.monoidalUnderlyingRingSheaf Strict.braidedUnderlyingRingSheaf

variable {X₁ : AlgebraicGeometry.RingedTopos.{v₁, u₁, w₁}}
    {X₂ : AlgebraicGeometry.RingedTopos.{v₂, u₂, w₂}}
    {X₃ : AlgebraicGeometry.RingedTopos.{v₃, u₃, w₃}}
  [X₁.J.HasSheafCompose (forget₂ CommRingCat.{w₁} RingCat.{w₁})]
  [X₂.J.HasSheafCompose (forget₂ CommRingCat.{w₂} RingCat.{w₂})]
  [X₃.J.HasSheafCompose (forget₂ CommRingCat.{w₃} RingCat.{w₃})]
  [X₁.J.HasSheafCompose (forget RingCat.{w₁})] [X₂.J.HasSheafCompose (forget RingCat.{w₂})]
  [X₃.J.HasSheafCompose (forget RingCat.{w₃})]
  [X₁.J.HasSheafCompose (forget AddCommGrpCat.{w₁})]
  [X₂.J.HasSheafCompose (forget AddCommGrpCat.{w₂})]
  [X₃.J.HasSheafCompose (forget AddCommGrpCat.{w₃})]
  [HasWeakSheafify X₁.J AddCommGrpCat.{w₁}] [X₁.J.WEqualsLocallyBijective AddCommGrpCat.{w₁}]
  [HasWeakSheafify X₂.J AddCommGrpCat.{w₂}] [X₂.J.WEqualsLocallyBijective AddCommGrpCat.{w₂}]
  [HasWeakSheafify X₃.J AddCommGrpCat.{w₃}] [X₃.J.WEqualsLocallyBijective AddCommGrpCat.{w₃}]
  (f₁ : Stacks.Sheaves.RingedToposModules.RingedToposHom X₂ X₁)
  {L₁ : _root_.SheafOfModules.{w₁} (Tensor.ringSheaf X₁.O) ⥤
    _root_.SheafOfModules.{w₂} (Tensor.ringSheaf X₂.O)}
  (α₁ : f₁.pullbackModules ≅ L₁)
  (f₂ : Stacks.Sheaves.RingedToposModules.RingedToposHom X₃ X₂)
  {L₂ : _root_.SheafOfModules.{w₂} (Tensor.ringSheaf X₂.O) ⥤
    _root_.SheafOfModules.{w₃} (Tensor.ringSheaf X₃.O)}
  (α₂ : f₂.pullbackModules ≅ L₂)

/-- **Two comparisons of Stacks 03EL read through identifications of pullbacks, composed, are
compatible with the left unitors**, with the identification of the units given as an
isomorphism `ε` together with its expression as the composite of the two identifications
`Stacks.SheafOfModules.pullbackUnitIsoTransport`.  This is
`Stacks.SheafOfModules.pullbackTensorIsoTransport_comp_leftUnitality` with that expression taken
between isomorphisms, the form in which an instance can supply it by `rfl`. -/
theorem pullbackTensorIsoTransport_comp_leftUnitality_of_iso
    (M : _root_.SheafOfModules.{w₁} (Tensor.ringSheaf X₁.O))
    (μ : L₂.obj (L₁.obj (𝟙_ _ ⊗ M)) ≅ MonoidalCategoryStruct.tensorObj
      (self := (monoidalCategory X₃.O.obj (TensorEncodings.isSheaf_structureRingPresheaf
          X₃.O)).toMonoidalCategoryStruct) (L₂.obj (L₁.obj (𝟙_ _))) (L₂.obj (L₁.obj M)))
    (hμ : μ = L₂.mapIso (pullbackTensorIsoTransport f₁ α₁ (𝟙_ _) M) ≪≫
      pullbackTensorIsoTransport f₂ α₂ (L₁.obj (𝟙_ _)) (L₁.obj M) ≪≫
      (tensorObjIso X₃.O.obj (TensorEncodings.isSheaf_structureRingPresheaf X₃.O) _ _).symm)
    (ε : L₂.obj (L₁.obj (𝟙_ _)) ≅ _root_.SheafOfModules.unit (Tensor.ringSheaf X₃.O))
    (hε : ε = L₂.mapIso (pullbackUnitIsoTransport f₁ α₁) ≪≫ pullbackUnitIsoTransport f₂ α₂)
    (e₀ : L₂.obj (L₁.obj (𝟙_ _ ⊗ M)) ⟶ L₂.obj (L₁.obj M))
    (he₀ : e₀ = L₂.map (L₁.map (λ_ M).hom)) :
    e₀ = μ.hom ≫ MonoidalCategoryStruct.whiskerRight (self := (monoidalCategory X₃.O.obj
        (TensorEncodings.isSheaf_structureRingPresheaf X₃.O)).toMonoidalCategoryStruct) ε.hom
          (L₂.obj (L₁.obj M)) ≫
      (MonoidalCategoryStruct.leftUnitor (self := (monoidalCategory X₃.O.obj
          (TensorEncodings.isSheaf_structureRingPresheaf X₃.O)).toMonoidalCategoryStruct) (L₂.obj
              (L₁.obj M))).hom :=
  pullbackTensorIsoTransport_comp_leftUnitality f₁ α₁ f₂ α₂ M μ hμ ε.hom
    (by rw [hε]; rfl) e₀ he₀

end Stacks.SheafOfModules

universe u

namespace AlgebraicGeometry.Space

attribute [local instance] modulesMonoidalCategory

variable (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S) (U : BigFppfOver B S hS)

/-- **The left unitor of the tensor product sheaf of Tag 01CA**, from the quasi-coherent tensor
product of the structure sheaf with a quasi-coherent module `M` on the scheme underlying `U`. -/
abbrev quasicoherentLeftUnitor
    (M : (SheafOfModules.isQuasicoherent
      ((BigFppfOver.toScheme B S hS).obj U).ringCatSheaf).FullSubcategory) :
    quasicoherentTensorObj B S hS U (quasicoherentUnitObj B S hS U) M ≅ M :=
  ObjectProperty.isoMk _ (MonoidalCategoryStruct.leftUnitor (self :=
      ((Stacks.SheafOfModules.Strict.monoidalUnderlyingRingSheaf ((BigFppfOver.toScheme B S hS).obj
          U).zariskiRingedSite.toRingedTopos.O).toMonoidalCategoryStruct)) M.obj)

section Irreducible

attribute [local irreducible] Stacks.SheafOfModules.Tensor.sheafTensor
  Stacks.SheafOfModules.pullbackTensorIso

/-- **The tensor identification of Stacks 03DX (2) on a representable is compatible with the left
unitors**, the units being matched by
`AlgebraicGeometry.Space.representedQuasicoherentSchemeUnitIso`: for a quasi-coherent module `M`
on the scheme underlying `U`, the module attached to the left unitor `𝒪_U ⊗ M ≅ M` is the
identification `(𝒪_U ⊗ M)_{yoneda U} ≅ 𝒪_{yoneda U} ⊗ M_{yoneda U}` followed by the left unitor
of `𝒪_{yoneda U}`-modules. -/
theorem representedQuasicoherentSchemeTensorIso_leftUnitality
    (M : (SheafOfModules.isQuasicoherent
      ((BigFppfOver.toScheme B S hS).obj U).ringCatSheaf).FullSubcategory) :
    ((representedQuasicoherentSchemeEquivalence B S hS U).functor.map
        (quasicoherentLeftUnitor B S hS U M).hom).hom =
      (representedQuasicoherentSchemeTensorIso B S hS U (quasicoherentUnitObj B S hS U) M).hom ≫
        MonoidalCategoryStruct.whiskerRight (C := Modules.{u, u} B S hS (yoneda.obj U)
            (AlgebraicGeometry.isAlgebraicSpace_yoneda B S hS U))
          (representedQuasicoherentSchemeUnitIso B S hS U).hom
          ((representedQuasicoherentSchemeEquivalence B S hS U).functor.obj M).obj ≫
        (MonoidalCategoryStruct.leftUnitor (C := Modules.{u, u} B S hS (yoneda.obj U)
            (AlgebraicGeometry.isAlgebraicSpace_yoneda B S hS U))
          ((representedQuasicoherentSchemeEquivalence B S hS U).functor.obj M).obj).hom := by
  refine Stacks.SheafOfModules.pullbackTensorIsoTransport_comp_leftUnitality_of_iso
      (_root_.AlgebraicGeometry.SmallEtale.toZariskiRingedToposModulesHom (associatedBigEtaleSite B)
      ((BigFppfOver.toScheme B S hS).obj U) U.left.property)
    (_root_.AlgebraicGeometry.SmallEtale.pullbackModulesToZariskiIso (associatedBigEtaleSite B)
      ((BigFppfOver.toScheme B S hS).obj U) U.left.property)
    (Stacks.SheafOfModules.reindexRingedToposModulesHom (SmallEtale.topology B S hS (yoneda.obj U))
      (representedSmallEtaleEquivalence B S hS U) (representedSchemeCommRingStructureSheaf B S hS
          U))
    (Stacks.SheafOfModules.pullbackModulesReindexIso (SmallEtale.topology B S hS (yoneda.obj U))
      (representedSmallEtaleEquivalence B S hS U) (representedSchemeCommRingStructureSheaf B S hS
          U))
    M.obj _ ?_ _ ?_ _ ?_
  · exact representedQuasicoherentSchemeTensorIso_eq B S hS U (quasicoherentUnitObj B S hS U) M
  · exact representedQuasicoherentSchemeUnitIso_eq B S hS U
  · exact representedQuasicoherentSchemeEquivalence_functor_map_hom B S hS U _

end Irreducible

end AlgebraicGeometry.Space

end
