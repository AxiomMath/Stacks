module

public import StacksFrontier.AlgebraicGeometry.Stacks.CoherentCompactQuasicoherent
public import StacksFrontier.AlgebraicGeometry.Stacks.CoherentExtensionLocallyNoetherian
public import StacksFrontier.AlgebraicGeometry.Stacks.Quasicoherent.QuasicoherentMonoidal
public import StacksFrontier.AlgebraicGeometry.Stacks.SubcategoryModuleLowerShriek
public import StacksFrontier.AlgebraicGeometry.Stacks.Quasicoherent.InternalHom
public import StacksFrontier.AlgebraicGeometry.Topologies.FinitePresentationCokernelOnSite
public import StacksFrontier.Algebra.Category.ModuleCat.Sheaf.TensorFinitePresentationOnSite
public import StacksFrontier.Algebra.Category.ModuleCat.Sheaf.MonoidalTensorColimits

/-!
# `Coh(𝒪_𝒳)` inside `QCoh(𝒪_𝒳)`: finite colimits, tensor products, and filtered colimits

Let `𝒳` be a locally Noetherian algebraic stack. The proof of Stacks 0GRJ applies Stacks 0FWY to
the inclusion `Coh(𝒪_𝒳) ⊆ QCoh(𝒪_𝒳)` and uses, beyond compactness (Stacks 0GQZ) and generation
(Stacks 0GRF), that coherent modules form a monoidal subcategory of `QCoh(𝒪_𝒳)` closed under
finite coproducts and cokernels, and that "colimits of modules commute with taking tensor
products". This file proves those three inputs.

## Main results

* `AlgebraicGeometry.Stack.coherentQuasicoherent_isClosedUnderColimitsOfShape_pair`,
  `AlgebraicGeometry.Stack.coherentQuasicoherent_isClosedUnderColimitsOfShape_empty` and
  `AlgebraicGeometry.Stack.coherentQuasicoherent_isClosedUnderColimitsOfShape_parallelPair`:
  `Coh(𝒪_𝒳)` is closed in `QCoh(𝒪_𝒳)` under binary coproducts, the empty colimit and
  coequalizers.
* `AlgebraicGeometry.Stack.coherentQuasicoherent_isMonoidal`: `Coh(𝒪_𝒳)` is a monoidal
  subcategory of `QCoh(𝒪_𝒳)`.
* `AlgebraicGeometry.Stack.preservesColimitsOfSize_quasicoherentTensorLeft` and
  `AlgebraicGeometry.Stack.preservesColimitsOfSize_quasicoherentTensorRight`: tensoring in
  `QCoh(𝒪_𝒳)` with a fixed quasi-coherent module commutes with all small colimits.

## Implementation notes

Colimits in `QCoh(𝒪_𝒳)` are computed in `Mod(𝒪_𝒳)`
(`AlgebraicGeometry.FibredSite.preservesColimitsOfSize_quasicoherentInclusion'`, Stacks 06WV(3)),
so each closure statement is one about modules on the fppf site of `𝒳`. On a locally Noetherian
algebraic stack coherence is finite presentation on that site
(`AlgebraicGeometry.Stack.isCoherent_iff_isCoherentModule`), and the three closure properties of
finite presentation used are site-level: extensions
(`Stacks.SheafOfModules.isFinitePresentationOnSite_X₂_of_kernel_cokernel`), cokernels
(`Stacks.SheafOfModules.isFinitePresentationOnSite_cokernel_of_isColimit`) and tensor products
(`Stacks.SheafOfModules.TensorLocalProperties.tensorSheaf_isFinitePresentationOnSite`).

## References

* [Stacks Project, Tag 0GRJ](https://stacks.math.columbia.edu/tag/0GRJ)
* [Stacks Project, Tag 0GR9](https://stacks.math.columbia.edu/tag/0GR9)
* [Stacks Project, Tag 06WV](https://stacks.math.columbia.edu/tag/06WV)
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits MonoidalCategory

universe u w w'

namespace AlgebraicGeometry.Stack

variable (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)
  (𝒳 : AlgebraicStacks.{u, w} B S hS)

section ModuleLevel

variable (h𝒳 : HasPropertyOnSomeSchemeAtlas B S hS
  (fun T : Scheme.{u} ↦ IsLocallyNoetherian T) 𝒳)

include h𝒳

/-- On a locally Noetherian algebraic stack a module of finite presentation on the fppf site is
coherent. -/
theorem isCoherent_of_isFinitePresentationOnSite
    {M : SheafOfModules.{u} (ringStructureSheafCore B S hS 𝒳.val.val.p
      𝒳.val.isFiberedInGroupoids B.topology le_rfl)}
    (hM : M.IsFinitePresentationOnSite) : IsCoherent B S hS 𝒳 M :=
  (isCoherent_iff_isCoherentModule B S hS 𝒳 h𝒳 M).mpr hM

/-- On a locally Noetherian algebraic stack coherence is invariant under isomorphism. -/
theorem isCoherent_of_iso
    {M N : SheafOfModules.{u} (ringStructureSheafCore B S hS 𝒳.val.val.p
      𝒳.val.isFiberedInGroupoids B.topology le_rfl)}
    (e : M ≅ N) (hM : IsCoherent B S hS 𝒳 M) : IsCoherent B S hS 𝒳 N :=
  isCoherent_of_isFinitePresentationOnSite B S hS 𝒳 h𝒳
    (SheafOfModules.IsFinitePresentationOnSite.of_iso e hM.2)

/-- A zero `𝒪_𝒳`-module on a locally Noetherian algebraic stack is coherent. -/
theorem isCoherent_of_isZero
    {Z : SheafOfModules.{u} (ringStructureSheafCore B S hS 𝒳.val.val.p
      𝒳.val.isFiberedInGroupoids B.topology le_rfl)}
    (hZ : IsZero Z) : IsCoherent B S hS 𝒳 Z :=
  isCoherent_of_isFinitePresentationOnSite B S hS 𝒳 h𝒳
    (Stacks.SheafOfModules.isFinitePresentationOnSite_of_isZero hZ)

/-- **Stacks 0GR9, part (1), for coherence in the sense of Stacks 0GR6.** On a locally
Noetherian algebraic stack a cokernel of a map of coherent `𝒪_𝒳`-modules is coherent. -/
theorem isCoherent_of_isColimit_cokernelCofork
    {F₁ F₂ F₃ : SheafOfModules.{u} (ringStructureSheafCore B S hS 𝒳.val.val.p
      𝒳.val.isFiberedInGroupoids B.topology le_rfl)}
    {φ : F₁ ⟶ F₂} {ψ : F₂ ⟶ F₃} (hz : φ ≫ ψ = 0) (hψ : IsColimit (CokernelCofork.ofπ ψ hz))
    (h₁ : IsCoherent B S hS 𝒳 F₁) (h₂ : IsCoherent B S hS 𝒳 F₂) :
    IsCoherent B S hS 𝒳 F₃ :=
  isCoherent_of_isFinitePresentationOnSite B S hS 𝒳 h𝒳
    (Stacks.SheafOfModules.isFinitePresentationOnSite_cokernel_of_isColimit hz hψ h₁.2 h₂.2)

end ModuleLevel

section QuasicoherentColimits

/-- The inclusion of `QCoh(𝒪_𝒳)` into all `𝒪_𝒳`-modules preserves colimits indexed by small
categories in the lowest universe. -/
theorem preservesColimitsOfShape_quasicoherentι (K : Type) [SmallCategory K] :
    PreservesColimitsOfShape K
      (SheafOfModules.isQuasicoherentOnSite.{u + 1, u, u, u}
        (FibredSite.ringStructureSheafCore B S hS 𝒳.val.val.p 𝒳.val.isFiberedInGroupoids
          .fppf)).ι :=
  have := FibredSite.preservesColimitsOfSize_quasicoherentInclusion' B S hS 𝒳.val.val.p
    𝒳.val.isFiberedInGroupoids
  have : PreservesColimitsOfSize.{0, 0}
      (SheafOfModules.isQuasicoherentOnSite.{u + 1, u, u, u}
        (FibredSite.ringStructureSheafCore B S hS 𝒳.val.val.p 𝒳.val.isFiberedInGroupoids
          .fppf)).ι :=
    preservesColimitsOfSize_shrink.{0, u, 0, u} _
  inferInstance

variable (h𝒳 : HasPropertyOnSomeSchemeAtlas B S hS
  (fun T : Scheme.{u} ↦ IsLocallyNoetherian T) 𝒳)

include h𝒳

/-- **Coherent modules are closed under binary coproducts in `QCoh(𝒪_𝒳)`.** The coproduct is
computed in `Mod(𝒪_𝒳)`, where it is a biproduct, hence an extension of one summand by the other,
and coherence is closed under extensions (Stacks 0GRA). -/
theorem coherentQuasicoherent_isClosedUnderColimitsOfShape_pair :
    (coherentQuasicoherent B S hS 𝒳).IsClosedUnderColimitsOfShape (Discrete WalkingPair) where
  colimitsOfShape_le := by
    rintro X ⟨h⟩
    have := preservesColimitsOfShape_quasicoherentι B S hS 𝒳 (Discrete WalkingPair)
    let ι := (SheafOfModules.isQuasicoherentOnSite.{u + 1, u, u, u}
      (FibredSite.ringStructureSheafCore B S hS 𝒳.val.val.p 𝒳.val.isFiberedInGroupoids .fppf)).ι
    have hc : IsColimit (ι.mapCocone (Cocone.mk _ h.ι)) := isColimitOfPreserves ι h.isColimit
    have ht := (IsColimit.precomposeInvEquiv (diagramIsoPair (h.diag ⋙ ι)) _).symm hc
    have hb := binaryBiconeIsBilimitOfColimitCoconeOfIsColimit ht
    let c := BinaryBicone.ofColimitCocone ht
    exact isCoherent_X₂_of_kernel_cokernel B S hS 𝒳 h𝒳 c.inl_snd
      (c.isLimitSndKernelFork hb.isLimit) (c.isColimitInlCokernelCofork hb.isColimit)
      (h.prop_diag_obj ⟨WalkingPair.left⟩) (h.prop_diag_obj ⟨WalkingPair.right⟩)

/-- **Coherent modules are closed under the empty colimit in `QCoh(𝒪_𝒳)`**: the zero module is
coherent. -/
theorem coherentQuasicoherent_isClosedUnderColimitsOfShape_empty :
    (coherentQuasicoherent B S hS 𝒳).IsClosedUnderColimitsOfShape (Discrete PEmpty.{1}) where
  colimitsOfShape_le := by
    rintro X ⟨h⟩
    let ι := (SheafOfModules.isQuasicoherentOnSite.{u + 1, u, u, u}
      (FibredSite.ringStructureSheafCore B S hS 𝒳.val.val.p 𝒳.val.isFiberedInGroupoids .fppf)).ι
    have : PreservesColimit h.diag ι :=
      (preservesColimitsOfShape_quasicoherentι B S hS 𝒳 (Discrete PEmpty.{1})).preservesColimit
    have hc : IsColimit (ι.mapCocone (Cocone.mk _ h.ι)) := isColimitOfPreserves ι h.isColimit
    exact isCoherent_of_isZero B S hS 𝒳 h𝒳
      ((IsZero.iff_id_eq_zero _).mpr (hc.hom_ext fun j ↦ PEmpty.elim j.as))

/-- **Coherent modules are closed under coequalizers in `QCoh(𝒪_𝒳)`.** The coequalizer of
`f, g` is computed in `Mod(𝒪_𝒳)`, where it is a cokernel of `f - g`, and a cokernel of a map of
coherent modules is coherent (Stacks 0GR9, part (1)). -/
theorem coherentQuasicoherent_isClosedUnderColimitsOfShape_parallelPair :
    (coherentQuasicoherent B S hS 𝒳).IsClosedUnderColimitsOfShape WalkingParallelPair where
  colimitsOfShape_le := by
    rintro X ⟨h⟩
    have := preservesColimitsOfShape_quasicoherentι B S hS 𝒳 WalkingParallelPair
    let ι := (SheafOfModules.isQuasicoherentOnSite.{u + 1, u, u, u}
      (FibredSite.ringStructureSheafCore B S hS 𝒳.val.val.p 𝒳.val.isFiberedInGroupoids .fppf)).ι
    let c' := (Cocone.precompose (diagramIsoParallelPair (h.diag ⋙ ι)).inv).obj
      (ι.mapCocone (Cocone.mk _ h.ι))
    have hc' : IsColimit c' := (IsColimit.precomposeInvEquiv (diagramIsoParallelPair (h.diag ⋙ ι))
      _).symm (isColimitOfPreserves ι h.isColimit)
    exact isCoherent_of_isColimit_cokernelCofork B S hS 𝒳 h𝒳
      (Preadditive.cokernelCoforkOfCofork c').condition
      (Preadditive.isColimitCokernelCoforkOfCofork hc')
      (h.prop_diag_obj WalkingParallelPair.zero) (h.prop_diag_obj WalkingParallelPair.one)

end QuasicoherentColimits

section Monoidal

attribute [local instance] FibredSite.monoidalCategoryQuasicoherentModules

/-- **The tensor product of two `𝒪_𝒳`-modules of finite presentation is of finite
presentation**, for the monoidal structure of `QCoh(𝒪_𝒳)` on the fppf site of `𝒳`. -/
theorem isFinitePresentationOnSite_quasicoherentTensorObj
    (F G : FibredSite.quasicoherentModules.{u, u + 1, u, u} B S hS 𝒳.val.val.p
      𝒳.val.isFiberedInGroupoids)
    (hF : F.obj.IsFinitePresentationOnSite) (hG : G.obj.IsFinitePresentationOnSite) :
    (F ⊗ G).obj.IsFinitePresentationOnSite := by
  have i1 := FibredSite.hasSheafCompose_associatedTopology B S hS 𝒳.val.val.p
    𝒳.val.isFiberedInGroupoids .fppf
  have i2 := FibredSite.hasWeakSheafify_associatedTopology B S hS 𝒳.val.val.p
    (.fppf : SiteKind)
  have i3 := FibredSite.wEqualsLocallyBijective_associatedTopology B S hS 𝒳.val.val.p
    (.fppf : SiteKind)
  have h := @Stacks.SheafOfModules.TensorLocalProperties.tensorSheaf_isFinitePresentationOnSite
    (FibredSite.ringedSite B S hS 𝒳.val.val.p 𝒳.val.isFiberedInGroupoids .fppf) i1 i2 i3
    F.obj G.obj hF hG
  exact SheafOfModules.IsFinitePresentationOnSite.of_iso
    (Stacks.SheafOfModules.tensorObjIso
      (FibredSite.structureSheaf B S hS 𝒳.val.val.p 𝒳.val.isFiberedInGroupoids .fppf).obj
      (FibredSite.structureRingPresheaf_isSheaf B S hS 𝒳.val.val.p 𝒳.val.isFiberedInGroupoids
        .fppf) F.obj G.obj).symm h

variable (h𝒳 : HasPropertyOnSomeSchemeAtlas B S hS
  (fun T : Scheme.{u} ↦ IsLocallyNoetherian T) 𝒳)

include h𝒳 in
/-- **Coherent modules form a monoidal subcategory of `QCoh(𝒪_𝒳)`** on a locally Noetherian
algebraic stack: `𝒪_𝒳` is coherent (Stacks 0GR7) and the tensor product of two coherent modules
is coherent. -/
theorem coherentQuasicoherent_isMonoidal : (coherentQuasicoherent B S hS 𝒳).IsMonoidal where
  prop_unit := isCoherent_unit B S hS 𝒳 h𝒳
  prop_tensor F G hF hG := isCoherent_of_isFinitePresentationOnSite B S hS 𝒳 h𝒳
    (isFinitePresentationOnSite_quasicoherentTensorObj B S hS 𝒳 F G hF.2 hG.2)

/-- Tensoring on the left in `QCoh(𝒪_𝒳)` is computed in `Mod(𝒪_𝒳)`. -/
noncomputable def quasicoherentTensorLeftCompιIso
    (F : FibredSite.quasicoherentModules.{u, u + 1, u, u} B S hS 𝒳.val.val.p
      𝒳.val.isFiberedInGroupoids) :
    letI := FibredSite.monoidalCategory B S hS 𝒳.val.val.p 𝒳.val.isFiberedInGroupoids .fppf
    tensorLeft F ⋙ (SheafOfModules.isQuasicoherentOnSite.{u + 1, u, u, u}
        (FibredSite.ringStructureSheafCore B S hS 𝒳.val.val.p 𝒳.val.isFiberedInGroupoids
          .fppf)).ι ≅
      (SheafOfModules.isQuasicoherentOnSite.{u + 1, u, u, u}
        (FibredSite.ringStructureSheafCore B S hS 𝒳.val.val.p 𝒳.val.isFiberedInGroupoids
          .fppf)).ι ⋙ tensorLeft F.obj :=
  NatIso.ofComponents (fun _ ↦ Iso.refl _) (fun _ ↦ by simp)

/-- Tensoring on the right in `QCoh(𝒪_𝒳)` is computed in `Mod(𝒪_𝒳)`. -/
noncomputable def quasicoherentTensorRightCompιIso
    (F : FibredSite.quasicoherentModules.{u, u + 1, u, u} B S hS 𝒳.val.val.p
      𝒳.val.isFiberedInGroupoids) :
    letI := FibredSite.monoidalCategory B S hS 𝒳.val.val.p 𝒳.val.isFiberedInGroupoids .fppf
    tensorRight F ⋙ (SheafOfModules.isQuasicoherentOnSite.{u + 1, u, u, u}
        (FibredSite.ringStructureSheafCore B S hS 𝒳.val.val.p 𝒳.val.isFiberedInGroupoids
          .fppf)).ι ≅
      (SheafOfModules.isQuasicoherentOnSite.{u + 1, u, u, u}
        (FibredSite.ringStructureSheafCore B S hS 𝒳.val.val.p 𝒳.val.isFiberedInGroupoids
          .fppf)).ι ⋙ tensorRight F.obj :=
  NatIso.ofComponents (fun _ ↦ Iso.refl _) (fun _ ↦ by simp)

/-- **Tensoring on the left in `QCoh(𝒪_𝒳)` commutes with all small colimits** ("colimits of
modules commute with taking tensor products", in the proof of Stacks 0GRJ). The inclusion of
`QCoh(𝒪_𝒳)` into `Mod(𝒪_𝒳)` preserves colimits and, being fully faithful, reflects them, and
tensoring in `Mod(𝒪_𝒳)` commutes with colimits
(`Stacks.SheafOfModules.preservesColimitsOfSize_tensorLeft`). -/
theorem preservesColimitsOfSize_quasicoherentTensorLeft
    (F : FibredSite.quasicoherentModules.{u, u + 1, u, u} B S hS 𝒳.val.val.p
      𝒳.val.isFiberedInGroupoids) :
    PreservesColimitsOfSize.{u, u} (tensorLeft F) := by
  let := FibredSite.monoidalCategory B S hS 𝒳.val.val.p 𝒳.val.isFiberedInGroupoids .fppf
  have := FibredSite.preservesColimitsOfSize_quasicoherentInclusion' B S hS 𝒳.val.val.p
    𝒳.val.isFiberedInGroupoids
  have i1 := FibredSite.hasSheafCompose_associatedTopology B S hS 𝒳.val.val.p
    𝒳.val.isFiberedInGroupoids .fppf
  have i2 := FibredSite.hasWeakSheafify_associatedTopology B S hS 𝒳.val.val.p
    (.fppf : SiteKind)
  have i3 := FibredSite.wEqualsLocallyBijective_associatedTopology B S hS 𝒳.val.val.p
    (.fppf : SiteKind)
  have : PreservesColimitsOfSize.{u, u} (tensorLeft F.obj) :=
    Stacks.SheafOfModules.preservesColimitsOfSize_tensorLeft
      (FibredSite.structureSheaf B S hS 𝒳.val.val.p 𝒳.val.isFiberedInGroupoids .fppf).obj
      (FibredSite.structureRingPresheaf_isSheaf B S hS 𝒳.val.val.p 𝒳.val.isFiberedInGroupoids
        .fppf) F.obj
  have : PreservesColimitsOfSize.{u, u} (tensorLeft F ⋙
      (SheafOfModules.isQuasicoherentOnSite.{u + 1, u, u, u}
        (FibredSite.ringStructureSheafCore B S hS 𝒳.val.val.p 𝒳.val.isFiberedInGroupoids
          .fppf)).ι) :=
    preservesColimits_of_natIso (quasicoherentTensorLeftCompιIso B S hS 𝒳 F).symm
  exact preservesColimits_of_reflects_of_preserves _
    (SheafOfModules.isQuasicoherentOnSite.{u + 1, u, u, u}
      (FibredSite.ringStructureSheafCore B S hS 𝒳.val.val.p 𝒳.val.isFiberedInGroupoids .fppf)).ι

/-- **Tensoring on the right in `QCoh(𝒪_𝒳)` commutes with all small colimits.** -/
theorem preservesColimitsOfSize_quasicoherentTensorRight
    (F : FibredSite.quasicoherentModules.{u, u + 1, u, u} B S hS 𝒳.val.val.p
      𝒳.val.isFiberedInGroupoids) :
    PreservesColimitsOfSize.{u, u} (tensorRight F) := by
  let := FibredSite.monoidalCategory B S hS 𝒳.val.val.p 𝒳.val.isFiberedInGroupoids .fppf
  have := FibredSite.preservesColimitsOfSize_quasicoherentInclusion' B S hS 𝒳.val.val.p
    𝒳.val.isFiberedInGroupoids
  have i1 := FibredSite.hasSheafCompose_associatedTopology B S hS 𝒳.val.val.p
    𝒳.val.isFiberedInGroupoids .fppf
  have i2 := FibredSite.hasWeakSheafify_associatedTopology B S hS 𝒳.val.val.p
    (.fppf : SiteKind)
  have i3 := FibredSite.wEqualsLocallyBijective_associatedTopology B S hS 𝒳.val.val.p
    (.fppf : SiteKind)
  have : PreservesColimitsOfSize.{u, u} (tensorRight F.obj) :=
    Stacks.SheafOfModules.preservesColimitsOfSize_tensorRight
      (FibredSite.structureSheaf B S hS 𝒳.val.val.p 𝒳.val.isFiberedInGroupoids .fppf).obj
      (FibredSite.structureRingPresheaf_isSheaf B S hS 𝒳.val.val.p 𝒳.val.isFiberedInGroupoids
        .fppf) F.obj
  have : PreservesColimitsOfSize.{u, u} (tensorRight F ⋙
      (SheafOfModules.isQuasicoherentOnSite.{u + 1, u, u, u}
        (FibredSite.ringStructureSheafCore B S hS 𝒳.val.val.p 𝒳.val.isFiberedInGroupoids
          .fppf)).ι) :=
    preservesColimits_of_natIso (quasicoherentTensorRightCompιIso B S hS 𝒳 F).symm
  exact preservesColimits_of_reflects_of_preserves _
    (SheafOfModules.isQuasicoherentOnSite.{u + 1, u, u, u}
      (FibredSite.ringStructureSheafCore B S hS 𝒳.val.val.p 𝒳.val.isFiberedInGroupoids .fppf)).ι

end Monoidal

end AlgebraicGeometry.Stack

end
