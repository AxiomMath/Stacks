module

public import StacksFrontier.AlgebraicGeometry.Spaces.Topologies.BigFppfModuleUnit
public import StacksFrontier.AlgebraicGeometry.Spaces.Topologies.BigFppfPushforwardQuasicoherent
public import StacksFrontier.AlgebraicGeometry.Spaces.Topologies.BigFppfQuasicoherentHomologyCohomology

/-!
# The counit of `a_X^* ⊣ a_{X,*}` on quasi-coherent modules

Let `a_X : ((Spaces/X)_fppf, 𝒪) ⟶ (X_{spaces,étale}, 𝒪_X)` be the morphism of Stacks 0DGM. For a
quasi-coherent `𝒪`-module `H` on `(Spaces/X)_fppf` the counit `a_X^*a_{X,*}H ⟶ H` is an
isomorphism. With the unit of Stacks 0DGN (6) and the quasi-coherence of `a_{X,*}H` this is part
(5) of Stacks 0DGN: `a_X^*` and `a_{X,*}` are inverse equivalences between quasi-coherent modules
on `(X_{spaces,étale}, 𝒪_X)` and on `((Spaces/X)_fppf, 𝒪)`.

## Main results

* `AlgebraicGeometry.BigFppfSpaceSite.isCoverDense_isAffineOverAffineEtale`: the affine schemes
  over affine objects of the spaces-étale site cover `(Spaces/X)_fppf`.
* `AlgebraicGeometry.BigFppfSpaceSite.isIso_counit_app_of_isQuasicoherentOnSite`: **the counit
  `a_X^*a_{X,*}H ⟶ H` is an isomorphism** for a quasi-coherent `H`.

## References

* [Stacks Project, Tag 0DGN](https://stacks.math.columbia.edu/tag/0DGN)
* [Stacks Project, Tag 03DX](https://stacks.math.columbia.edu/tag/03DX)
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits Opposite

universe u

namespace AlgebraicGeometry.BigFppfSpaceSite

variable {S : Scheme.{u}} {T : BigFppfSpaceSite S} {X : T.Spaces}

variable (T X) in
/-- The objects of `(Spaces/X)_fppf` represented by an affine scheme and mapping to an object of
the spaces-étale site of `X` represented by an affine scheme. -/
def IsAffineOverAffineEtale : ObjectProperty (BigFppfSpaceOver T X) :=
  fun Y ↦ BigFppfSpaceOver.IsAffineSchemeOver T X Y ∧
    ∃ W : Space.SpacesEtale T.schemeSite S T.scheme_mem X,
      Space.SpacesEtale.IsAffineScheme T.schemeSite S T.scheme_mem X W ∧
        Nonempty (Y ⟶ (Space.SpacesEtale.inclusion T.schemeSite S T.scheme_mem X).obj W)

/-- **The objects of `(Spaces/X)_fppf` represented by an affine scheme over an affine étale object
of `X` are cover-dense.** -/
instance isCoverDense_isAffineOverAffineEtale :
    (IsAffineOverAffineEtale T X).ι.IsCoverDense (BigFppfSpaceOver.topology T X) where
  is_cover Z := by
    have := (spacesEtaleInclusion_isMorphismOfSites T X).isContinuous
    have hcp := CoverPreserving.of_isContinuous
      (Space.SpacesEtale.inclusion T.schemeSite S T.scheme_mem X)
      (Space.SpacesEtale.topology T.schemeSite S T.scheme_mem X) (BigFppfSpaceOver.topology T X)
    have h₁ := GrothendieckTopology.pullback_stable _ ((Over.mkIdTerminal (X := X)).from Z)
      (hcp.cover_preserve (Space.SpacesEtale.generate_affineSchemePresieve_mem T.schemeSite S
        T.scheme_mem X (Space.SpacesEtale.final T.schemeSite S T.scheme_mem X)))
    refine GrothendieckTopology.superset_covering _ ?_
      ((BigFppfSpaceOver.topology T X).bind_covering h₁
        (fun Y _ _ ↦ BigFppfSpaceOver.generate_affineSchemePresieve_mem T Y))
    rintro Z'' _ ⟨Y, h, f, hf, hh, rfl⟩
    obtain ⟨W, a, b, ⟨W₀, a₁, a₂, hW₀, rfl⟩, hb⟩ := hf
    obtain ⟨A, h₁, h₂, hA, rfl⟩ := hh
    exact ⟨⟨⟨A, hA, W₀, hW₀, ⟨h₂ ≫ b ≫
      (Space.SpacesEtale.inclusion T.schemeSite S T.scheme_mem X).map a₁⟩⟩, h₁, h₂ ≫ f,
      (Category.assoc _ _ _).symm⟩⟩

/-- **The counit `a_X^*a_{X,*}H ⟶ H` is invertible on sections over an affine scheme mapping to an
affine object of the spaces-étale site**, for a quasi-coherent `H`. -/
theorem isIso_counit_val_app_of_isAffineOverAffineEtale
    (H : SheafOfModules.{u + 1} (Stacks.SheafOfModules.Tensor.ringSheaf (bigFppfRingedSite T X).O))
    [H.IsQuasicoherentOnSite]
    (Y : BigFppfSpaceOver T X) (hY : IsAffineOverAffineEtale T X Y) :
    IsIso (((fppfToSpacesEtaleRingedSiteHom
      T X).toRingedToposSiteHom.pullbackPushforwardAdjunctionTopos.counit.app H).val.app
        (op Y)) := by
  let f := fppfToSpacesEtaleRingedSiteHom T X
  let adj := f.toRingedToposSiteHom.pullbackPushforwardAdjunctionTopos
  let G := f.toRingedToposSiteHom.pushforwardTopos.obj H
  have : G.IsQuasicoherentOnSite := isQuasicoherentOnSite_pushforward_of_isQuasicoherentOnSite H
  have hη : IsIso (adj.unit.app G) := isIso_unit_app_of_isQuasicoherentOnSite G
  let ε := adj.counit.app H
  have hF : IsIso (f.toRingedToposSiteHom.pushforwardTopos.map ε) := by
    have : IsIso (adj.unit.app G ≫ f.toRingedToposSiteHom.pushforwardTopos.map ε) := by
      rw [adj.right_triangle_components H]
      infer_instance
    exact IsIso.of_isIso_comp_left (adj.unit.app G) _
  obtain ⟨⟨Y₀, hY₀, ⟨eY⟩⟩, W, ⟨V₀, hV₀, ⟨e⟩⟩, ⟨g⟩⟩ := hY
  let U : BigFppfSpaceOver T X := (Space.SpacesEtale.inclusion T.schemeSite S T.scheme_mem X).obj W
  have hU : IsIso (ε.val.app (op U)) :=
    Stacks.AlgebraicGeometry.QcohRestrictEquiv.isIso_val_app_of_isIso_pushforward_val_app
      f.toRingedToposSiteHom.fSharpRing ε (op W)
      (Functor.map_isIso (SheafOfModules.evaluation _ (op W))
        (f.toRingedToposSiteHom.pushforwardTopos.map ε))
  let T₀ : BigFppfSpaceOver T X := (AffineSchemesOver.toOver T U).obj
    (AffineSchemesOver.ofIso V₀ hV₀ e)
  have hT₀ : IsIso (ε.val.app (op T₀)) :=
    Stacks.AlgebraicGeometry.QcohRestrictEquiv.isIso_val_app_of_iso ε
      (Over.isoMk (f := T₀) (g := U) e rfl).symm hU
  let Ŷ : AffineSchemesOver T U := ⟨CostructuredArrow.mk (eY.hom ≫ g.left), hY₀⟩
  let k : Ŷ ⟶ AffineSchemesOver.ofIso V₀ hV₀ e :=
    (AffineSchemesOver.isTerminalOfIso V₀ hV₀ e).from Ŷ
  let P := f.toRingedToposSiteHom.pullbackTopos.obj G
  have cP := (AffineSchemesOver.isIso_restrictionBaseChange_affineRestriction_iff P k).1
    (AffineSchemesOver.isIso_restrictionBaseChange_of_locallyPresented (U := U) V₀ hV₀ e P
      (generate_hasGlobalPresentation_pullback_mem G) k)
  have cH := (AffineSchemesOver.isIso_restrictionBaseChange_affineRestriction_iff H k).1
    (AffineSchemesOver.isIso_restrictionBaseChange_of_locallyPresented (U := U) V₀ hV₀ e H
      (generate_hasGlobalPresentation_mem_of_isQuasicoherentOnSite H) k)
  let m := (Over.forget U).map ((AffineSchemesOver.toSlice T U).map k)
  have hnat := Stacks.PresheafOfModules.restrictionBaseChange_naturality.{_, _, u + 1, u + 1}
    (R := Stacks.TerminalBaseChange.commPresheaf (bigFppfRingSheaf T X).obj) ε.val m.op
  have hL := @IsIso.comp_isIso _ _ _ _ _ _ _
    ((ModuleCat.extendScalars
      ((Stacks.TerminalBaseChange.commPresheaf (bigFppfRingSheaf T X).obj).map m.op).hom).mapIso
        (@asIso _ _ _ _ (ε.val.app (op T₀)) hT₀)).isIso_hom cH
  have hR := (congrArg IsIso hnat).mp hL
  have hY' : IsIso (ε.val.app (op ((AffineSchemesOver.toOver T U).obj Ŷ))) :=
    @IsIso.of_isIso_comp_left _ _ _ _ _ _ _ cP hR
  exact Stacks.AlgebraicGeometry.QcohRestrictEquiv.isIso_val_app_of_iso ε
    (Over.isoMk (f := Y) (g := (AffineSchemesOver.toOver T U).obj Ŷ) eY.symm
      (by
        show eY.inv ≫ (eY.hom ≫ g.left) ≫ U.hom = Y.hom
        rw [Category.assoc, eY.inv_hom_id_assoc, Over.w g])).symm hY'

/-- **Stacks 0DGN (5), the counit: `a_X^*a_{X,*}H ⟶ H` is an isomorphism** for a quasi-coherent
`𝒪`-module `H` on `(Spaces/X)_fppf`. -/
theorem isIso_counit_app_of_isQuasicoherentOnSite
    (H : SheafOfModules.{u + 1} (Stacks.SheafOfModules.Tensor.ringSheaf (bigFppfRingedSite T X).O))
    [H.IsQuasicoherentOnSite] :
    IsIso ((fppfToSpacesEtaleRingedSiteHom
      T X).toRingedToposSiteHom.pullbackPushforwardAdjunctionTopos.counit.app H) :=
  Stacks.AlgebraicGeometry.QcohRestrictEquiv.isIso_of_isIso_val_app_of_isCoverDense
    (IsAffineOverAffineEtale T X).ι _
    (fun Y ↦ isIso_counit_val_app_of_isAffineOverAffineEtale H Y.obj Y.property)

end AlgebraicGeometry.BigFppfSpaceSite

end
