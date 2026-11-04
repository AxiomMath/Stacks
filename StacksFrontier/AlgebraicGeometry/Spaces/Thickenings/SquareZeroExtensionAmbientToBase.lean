module

public import StacksFrontier.AlgebraicGeometry.Spaces.Thickenings.SquareZeroExtensionAmbientImmersion

/-!
# The structure morphism from the ambient space of a square-zero extension to the base

For a square-zero extension `E` of `f : X ⟶ Y` with a charted presentation `C`, the thickened
presenting chart and the thickened relation chart map to the presenting scheme and the relation
scheme of `Y`, compatibly with the source and target maps. These maps descend to a morphism from
the ambient algebraic space `X'` to `Y`, and the composite `X ⟶ X' ⟶ Y` is `f`.

## Main definitions

* `ambUToBase`: The morphism from the thickened presenting chart to the presenting scheme of `Y`.
* `ambRToBase`: The morphism from the thickened relation chart to the relation scheme of `Y`.

## Main results

* `hom_ext_of_presentation`: Two morphisms from an algebraic space to an fppf sheaf agreeing on a
  surjective étale atlas are equal.
* `exists_ambientToBase`: There is a morphism `X' ⟶ Y` whose composite with the quotient map is
  the map of the thickened presenting chart to `Y`.
* `ambientMap_comp_toBase`: The composite `X ⟶ X' ⟶ Y` is `f`.
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits Opposite TopologicalSpace Stacks.Groupoids

universe u

namespace AlgebraicGeometry.Space

namespace SquareZeroExtension

variable {B : BigFppfSite.{u}} {S : Scheme.{u}} {hS : B.Contains S}
  {X Y : AlgebraicSpaces B S hS} {f : X ⟶ Y} (E : SquareZeroExtension B S hS f)
  (C : ChartedPresentation B S hS f)
  (hcU : B.Contains (chartThickening B S hS E (presentationChart C.P)))
  (hcR : B.Contains (chartThickening B S hS E (presentationRelationChart C.P)))

/-- The thickened relation source map followed by the map of the thickened presenting chart to
the presenting scheme of `Y` equals the map of the thickened relation chart to the relation scheme
of `Y` followed by the relation source map of `Y`. -/
theorem chartThickeningMap_source_comp_chartMapGen :
    chartThickeningMap B S hS E (presentationRelationSourceHom C.P) ≫
        chartMapGen B S hS E C.diagram =
      chartMapGen B S hS E C.relationDiagram ≫
        chartSchemeMap (presentationRelationSourceHom C.Q) :=
  (chartThickeningMap_comp_chartMapGen B S hS E C.diagram
    (presentationRelationSourceHom C.P)).trans ((chartMapGen_mk_congr B S hS E
      (U := presentationRelationChart C.P) (V := presentationChart C.Q)
      (g' := C.β ≫ (SmallEtale.toOver B S hS Y.1).map (presentationRelationSourceHom C.Q))
      _ (ChartDiagram.postcomp' B S hS C.relationDiagram
        (presentationRelationSourceHom C.Q)).comm C.β_source.symm).trans
      (chartMapGen_postcomp B S hS E C.relationDiagram (presentationRelationSourceHom C.Q)))

/-- The thickened relation target map followed by the map of the thickened presenting chart to
the presenting scheme of `Y` equals the map of the thickened relation chart to the relation scheme
of `Y` followed by the relation target map of `Y`. -/
theorem chartThickeningMap_target_comp_chartMapGen :
    chartThickeningMap B S hS E (presentationRelationTargetHom C.P) ≫
        chartMapGen B S hS E C.diagram =
      chartMapGen B S hS E C.relationDiagram ≫
        chartSchemeMap (presentationRelationTargetHom C.Q) :=
  (chartThickeningMap_comp_chartMapGen B S hS E C.diagram
    (presentationRelationTargetHom C.P)).trans ((chartMapGen_mk_congr B S hS E
      (U := presentationRelationChart C.P) (V := presentationChart C.Q)
      (g' := C.β ≫ (SmallEtale.toOver B S hS Y.1).map (presentationRelationTargetHom C.Q))
      _ (ChartDiagram.postcomp' B S hS C.relationDiagram
        (presentationRelationTargetHom C.Q)).comm C.β_target.symm).trans
      (chartMapGen_postcomp B S hS E C.relationDiagram (presentationRelationTargetHom C.Q)))

/-- The thickened presenting chart maps to the presenting scheme of the target. -/
def ambUToBase : ambU E C hcU ⟶ C.Q.U :=
  Over.homMk (ObjectProperty.homMk (chartMapGen B S hS E C.diagram))
    (by apply ObjectProperty.hom_ext; rfl)

/-- The underlying morphism of schemes of `ambUToBase E C hcU` is `chartMapGen B S hS E C.diagram`.
-/
theorem toScheme_map_ambUToBase :
    (BigFppfOver.toScheme B S hS).map (ambUToBase E C hcU) = chartMapGen B S hS E C.diagram :=
  rfl

/-- The thickened relation chart maps to the relation scheme of the target. -/
def ambRToBase : ambR E C hcR ⟶ C.Q.R :=
  Over.homMk (ObjectProperty.homMk (chartMapGen B S hS E C.relationDiagram)) (by
    apply ObjectProperty.hom_ext
    change chartMapGen B S hS E C.relationDiagram ≫ B.inclusion.map C.Q.R.hom =
      relationThickeningToBase E C
    have hQ : chartSchemeMap (presentationRelationSourceHom C.Q) ≫ B.inclusion.map C.Q.U.hom =
        B.inclusion.map C.Q.R.hom :=
      (B.inclusion.map_comp _ _).symm.trans (congrArg B.inclusion.map (Over.w C.Q.source))
    exact (congrArg (chartMapGen B S hS E C.relationDiagram ≫ ·) hQ).symm.trans
      ((Category.assoc _ _ _).symm.trans ((congrArg (· ≫ B.inclusion.map C.Q.U.hom)
        (chartThickeningMap_source_comp_chartMapGen E C)).symm.trans (Category.assoc _ _ _))))

/-- The maps of the thickened charts to the charts of `Y` commute with the source maps. -/
theorem ambSource_comp_ambUToBase :
    ambSource E C hcU hcR ≫ ambUToBase E C hcU = ambRToBase E C hcR ≫ C.Q.source :=
  BigFppfOver.map_toScheme_injective B S hS
    (((BigFppfOver.toScheme B S hS).map_comp _ _).trans
      ((chartThickeningMap_source_comp_chartMapGen E C).trans
        ((BigFppfOver.toScheme B S hS).map_comp (ambRToBase E C hcR) C.Q.source).symm))

/-- The maps of the thickened charts to the charts of `Y` commute with the target maps. -/
theorem ambTarget_comp_ambUToBase :
    ambTarget E C hcU hcR ≫ ambUToBase E C hcU = ambRToBase E C hcR ≫ C.Q.target :=
  BigFppfOver.map_toScheme_injective B S hS
    (((BigFppfOver.toScheme B S hS).map_comp _ _).trans
      ((chartThickeningMap_target_comp_chartMapGen E C).trans
        ((BigFppfOver.toScheme B S hS).map_comp (ambRToBase E C hcR) C.Q.target).symm))

/-- The inclusion of the presenting chart of `X` into its thickening, followed by the map to the
presenting scheme of `Y`, is `C.α`. -/
theorem incU_comp_ambUToBase : incU E C hcU ≫ ambUToBase E C hcU = C.α :=
  BigFppfOver.map_toScheme_injective B S hS
    (((BigFppfOver.toScheme B S hS).map_comp _ _).trans
      (chartImmersion_comp_chartMapGen B S hS E C.diagram))

attribute [local instance] hasSheafify_bigFppfOver

/-- Two morphisms out of an algebraic space into an fppf sheaf agree as soon as they agree on a
surjective étale atlas. -/
theorem hom_ext_of_presentation {F : AlgebraicSpaces B S hS} (P : Presentation B S hS F.1 F.2)
    {G : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u} (hG : Presheaf.IsSheaf (BigFppfOver.topology B S hS) G)
    {a b : F.1 ⟶ G} (h : P.toSpace ≫ a = P.toSpace ≫ b) : a = b := by
  obtain ⟨hRsh, hUsh, ⟨hc⟩⟩ := isCoequalizer_of_surjectiveEtale B S hS P.toSpace
    P.source P.target P.isPullback.flip F.2 P.surjective P.etale
  exact congrArg (·.hom)
    (Cofork.IsColimit.hom_ext hc (W := ⟨G, hG⟩) (k := ⟨a⟩) (l := ⟨b⟩) (Sheaf.hom_ext h))

/-- **The structure morphism `X' ⟶ Y` exists**: the composite of the map of the thickened
presenting chart to the presenting scheme of `Y` with the atlas of `Y` descends along the
quotient map. -/
theorem exists_ambientToBase :
    ∃ ψ : (ambient E C hcU hcR).1 ⟶ Y.1,
      ambQuot E C hcU hcR ≫ ψ = yoneda.map (ambUToBase E C hcU) ≫ C.Q.toSpace := by
  obtain ⟨hRsh, hUsh, ⟨hc⟩⟩ := isCoequalizer_of_surjectiveEtale B S hS (ambQuot E C hcU hcR)
    (ambSource E C hcU hcR) (ambTarget E C hcU hcR) (ambQuot_isPullback E C hcU hcR).flip
    (ambient E C hcU hcR).2 (quotientMap_surjective_unconditional B S hS _ _)
    (quotientMap_etale_unconditional B S hS _ _)
  let g : (⟨yoneda.obj (ambU E C hcU), hUsh⟩ : Sheaf (BigFppfOver.topology B S hS) (Type u)) ⟶
      ⟨Y.1, Y.2.isSheaf⟩ := ⟨yoneda.map (ambUToBase E C hcU) ≫ C.Q.toSpace⟩
  have hw : (⟨yoneda.map (ambSource E C hcU hcR)⟩ : (⟨yoneda.obj (ambR E C hcR), hRsh⟩ :
      Sheaf (BigFppfOver.topology B S hS) (Type u)) ⟶ ⟨yoneda.obj (ambU E C hcU), hUsh⟩) ≫ g =
      (⟨yoneda.map (ambTarget E C hcU hcR)⟩ : (⟨yoneda.obj (ambR E C hcR), hRsh⟩ :
      Sheaf (BigFppfOver.topology B S hS) (Type u)) ⟶ ⟨yoneda.obj (ambU E C hcU), hUsh⟩) ≫ g := by
    apply Sheaf.hom_ext
    show yoneda.map (ambSource E C hcU hcR) ≫ yoneda.map (ambUToBase E C hcU) ≫
        C.Q.toSpace =
      yoneda.map (ambTarget E C hcU hcR) ≫ yoneda.map (ambUToBase E C hcU) ≫ C.Q.toSpace
    rw [← Functor.map_comp_assoc, ← Functor.map_comp_assoc, ambSource_comp_ambUToBase,
      ambTarget_comp_ambUToBase, Functor.map_comp_assoc, Functor.map_comp_assoc, C.Q.isPullback.w]
  exact ⟨(hc.desc (Cofork.ofπ g hw)).hom,
    congrArg (·.hom) (hc.fac (Cofork.ofπ g hw) WalkingParallelPair.one)⟩

variable {E C hcU hcR} (i : X ⟶ ambient E C hcU hcR)
  (hi : C.P.toSpace ≫ i.hom = yoneda.map (incU E C hcU) ≫ ambQuot E C hcU hcR)
  (p : ambient E C hcU hcR ⟶ Y)
  (hp : ambQuot E C hcU hcR ≫ p.hom = yoneda.map (ambUToBase E C hcU) ≫ C.Q.toSpace)

include hi hp in
/-- **The ambient space lies over the base**: `X ⟶ X' ⟶ Y` is `f`. -/
theorem ambientMap_comp_toBase : i ≫ p = f := by
  refine ObjectProperty.hom_ext _ (hom_ext_of_presentation C.P Y.2.isSheaf ?_)
  show C.P.toSpace ≫ i.hom ≫ p.hom = C.P.toSpace ≫ f.hom
  rw [← Category.assoc, hi, Category.assoc, hp, ← Category.assoc, ← Functor.map_comp,
    incU_comp_ambUToBase, C.comm]

end SquareZeroExtension

end AlgebraicGeometry.Space

end
