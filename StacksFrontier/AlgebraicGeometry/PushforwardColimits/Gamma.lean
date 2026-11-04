module

public import StacksFrontier.AlgebraicGeometry.AffineBaseChange.Basic
public import StacksFrontier.AlgebraicGeometry.AffineQcohPushforward.Colimits

/-!
# Global sections and direct images on spectra commute with colimits of quasi-coherent modules

Let `R` be a commutative ring.  Taking global sections of an `𝒪_{Spec R}`-module is a right
adjoint, so there is no reason for it to commute with colimits; on *quasi-coherent* modules it
does, because `AlgebraicGeometry.tildeEquiv` identifies them with `ModuleCat R` and the global
section functor with the inverse of that equivalence.  This file proves that, and deduces that
the direct image along a morphism of spectra commutes with colimits of quasi-coherent modules.

The second statement is the affine input for the fact that the direct image along an affine
morphism of schemes commutes with coproducts, which is what the equivalence assertion of Stacks
Tag 01SB needs at free modules.

## Main results

* `Stacks.AlgebraicGeometry.PushforwardColimits.isIso_map_colimit_post`: the piece of general
  category theory used throughout.  If `G` preserves the colimit of `D ⋙ F` and `F ⋙ G`
  preserves the colimit of `D`, then `G` carries the colimit comparison morphism of `D` and `F`
  to an isomorphism.  This is how a statement about `F` is extracted from statements about `G`
  and `F ⋙ G`.
* `Stacks.AlgebraicGeometry.PushforwardColimits.preservesColimit_moduleSpecΓFunctor`: on a
  spectrum, `AlgebraicGeometry.moduleSpecΓFunctor` preserves the colimit of a diagram of
  quasi-coherent modules.
* `Stacks.AlgebraicGeometry.PushforwardColimits.preservesColimit_pushforward_specMap`: the
  direct image along `Spec.map φ` preserves the colimit of a diagram of quasi-coherent modules.

## Implementation notes

The proof that global sections preserve such a colimit is the one used for
`Stacks.AlgebraicGeometry.QuasicoherentColimits.isQuasicoherent_of_isColimit_spec`: a diagram
`D` of quasi-coherent modules is isomorphic to `E ⋙ tilde.functor R`, where
`E = D ⋙ tildeEquiv.inverse` is a diagram of `R`-modules, and on a diagram of that form the
colimit may be computed in `ModuleCat R`, where `tilde.functor R ⋙ moduleSpecΓFunctor` is the
identity up to `AlgebraicGeometry.tilde.toTildeΓNatIso`.

For the direct image the comparison of global sections is already available: by
`Stacks.AlgebraicGeometry.SectionsColimit.pullbackSectionsIso` the composite
`Scheme.Modules.pushforward (Spec.map φ) ⋙ moduleSpecΓFunctor` is isomorphic to
`moduleSpecΓFunctor ⋙ ModuleCat.restrictScalars φ`, and restriction of scalars for modules over
a ring is a left adjoint.  So both hypotheses of `isIso_map_colimit_post` hold with
`G = moduleSpecΓFunctor`, and the resulting invertibility on global sections is upgraded to
invertibility by `Stacks.AlgebraicGeometry.AffineBaseChange.isIso_of_isIso_moduleSpecΓ`, whose
two quasi-coherence hypotheses are the closure of quasi-coherence under colimits and under
direct images along morphisms of spectra.

## References

* [Stacks Project, Tag 01SB](https://stacks.math.columbia.edu/tag/01SB)
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits TopologicalSpace Opposite
open AlgebraicGeometry

universe v₂ u₂ u

noncomputable section

namespace Stacks.AlgebraicGeometry.PushforwardColimits

/-! ### A cancellation lemma for colimit comparison morphisms -/

section Cancellation

variable {K : Type u₂} [Category.{v₂} K] {C₁ : Type*} [Category C₁] {C₂ : Type*} [Category C₂]
  {C₃ : Type*} [Category C₃]

/-- If `G` preserves the colimit of `D ⋙ F` and `F ⋙ G` preserves the colimit of `D`, then the
image under `G` of the colimit comparison morphism `colimit (D ⋙ F) ⟶ F.obj (colimit D)` is
invertible.  Both of the two comparison morphisms in
`CategoryTheory.Limits.colimit.post_post` are then invertible, and the statement is the
cancellation of the first from the composite. -/
theorem isIso_map_colimit_post (D : K ⥤ C₁) (F : C₁ ⥤ C₂) (G : C₂ ⥤ C₃)
    [HasColimit D] [HasColimit (D ⋙ F)] [HasColimit ((D ⋙ F) ⋙ G)]
    [PreservesColimit (D ⋙ F) G] [PreservesColimit D (F ⋙ G)] :
    IsIso (G.map (colimit.post D F)) := by
  have h : IsIso (colimit.post (D ⋙ F) G ≫ G.map (colimit.post D F)) := by
    rw [colimit.post_post D F G]
    infer_instance
  exact IsIso.of_isIso_comp_left (colimit.post (D ⋙ F) G) _

end Cancellation

/-! ### Global sections on a spectrum -/

variable {K : Type u₂} [Category.{v₂} K]

/-- **On a spectrum the global section functor preserves colimits of quasi-coherent modules.**
The diagram is isomorphic to a diagram of the form `E ⋙ tilde.functor R`, and
`tilde.functor R ⋙ moduleSpecΓFunctor` is isomorphic to the identity. -/
theorem preservesColimit_moduleSpecΓFunctor (R : CommRingCat.{u})
    [HasColimitsOfShape K (ModuleCat.{u} R)] {D : K ⥤ (Spec R).Modules}
    (hD : ∀ k, (D.obj k).IsQuasicoherent) :
    PreservesColimit D (moduleSpecΓFunctor (R := R)) := by
  let P := SheafOfModules.isQuasicoherent (Spec R).ringCatSheaf
  let D' : K ⥤ P.FullSubcategory := P.lift D hD
  let E : K ⥤ ModuleCat.{u} R := D' ⋙ (tildeEquiv (R := R)).inverse
  have iso : D ≅ E ⋙ tilde.functor R :=
    Functor.isoWhiskerRight
      (Functor.isoWhiskerLeft D' (tildeEquiv (R := R)).counitIso.symm) P.ι
  have hcomp : PreservesColimit E (tilde.functor R ⋙ moduleSpecΓFunctor (R := R)) :=
    preservesColimit_of_natIso E tilde.toTildeΓNatIso
  have key : PreservesColimit (E ⋙ tilde.functor R) (moduleSpecΓFunctor (R := R)) :=
    preservesColimit_of_preserves_colimit_cocone
      (isColimitOfPreserves (tilde.functor R) (colimit.isColimit E))
      (isColimitOfPreserves (tilde.functor R ⋙ moduleSpecΓFunctor (R := R))
        (colimit.isColimit E))
  exact preservesColimit_of_iso_diagram _ iso.symm

/-! ### Direct image along a morphism of spectra -/

variable [HasColimitsOfShape K AddCommGrpCat.{u}]
  [∀ R : CommRingCat.{u}, HasColimitsOfShape K (ModuleCat.{u} R)]

/-- **Direct image along a morphism of spectra preserves colimits of quasi-coherent modules.**
Both hypotheses of `isIso_map_colimit_post` hold for `G = moduleSpecΓFunctor`, by
`preservesColimit_moduleSpecΓFunctor` and by the identification
`Stacks.AlgebraicGeometry.SectionsColimit.pullbackSectionsIso` of the global sections of a direct
image with the global sections with scalars restricted. -/
theorem preservesColimit_pushforward_specMap {R T : CommRingCat.{u}} (φ : R ⟶ T)
    [HasColimitsOfShape K ((Spec R).Modules)] [HasColimitsOfShape K ((Spec T).Modules)]
    {D : K ⥤ (Spec T).Modules} (hD : ∀ k, (D.obj k).IsQuasicoherent) :
    PreservesColimit D (Scheme.Modules.pushforward (Spec.map φ)) := by
  have hDF : ∀ k, ((D ⋙ Scheme.Modules.pushforward (Spec.map φ)).obj k).IsQuasicoherent :=
    fun k ↦
      have := hD k
      AffinePushforward.isQuasicoherent_pushforward_specMap φ (D.obj k)
  have h1 : PreservesColimit (D ⋙ Scheme.Modules.pushforward (Spec.map φ))
      (moduleSpecΓFunctor (R := R)) :=
    preservesColimit_moduleSpecΓFunctor R hDF
  have hΓT : PreservesColimit D (moduleSpecΓFunctor (R := T)) :=
    preservesColimit_moduleSpecΓFunctor T hD
  have hrs : PreservesColimit D (SectionsColimit.sectionsRestrictScalars φ) :=
    inferInstanceAs (PreservesColimit D
      (moduleSpecΓFunctor (R := T) ⋙ ModuleCat.restrictScalars φ.hom))
  have h2 : PreservesColimit D
      (Scheme.Modules.pushforward (Spec.map φ) ⋙ moduleSpecΓFunctor (R := R)) :=
    preservesColimit_of_natIso D (SectionsColimit.pullbackSectionsIso φ).symm
  have hqc1 : (colimit (D ⋙ Scheme.Modules.pushforward (Spec.map φ))).IsQuasicoherent :=
    QuasicoherentColimits.isQuasicoherent_colimit _ hDF
  have hqc2 : (((Scheme.Modules.pushforward (Spec.map φ))).obj (colimit D)).IsQuasicoherent :=
    have := QuasicoherentColimits.isQuasicoherent_colimit D hD
    AffinePushforward.isQuasicoherent_pushforward_specMap φ (colimit D)
  have hcM : HasColimit ((D ⋙ Scheme.Modules.pushforward (Spec.map φ)) ⋙
      moduleSpecΓFunctor (R := R)) := HasColimitsOfShape.has_colimit _
  have hpost : IsIso (moduleSpecΓFunctor.map
      (colimit.post D (Scheme.Modules.pushforward (Spec.map φ)))) :=
    isIso_map_colimit_post D (Scheme.Modules.pushforward (Spec.map φ))
      (moduleSpecΓFunctor (R := R))
  have hiso : IsIso (colimit.post D (Scheme.Modules.pushforward (Spec.map φ))) :=
    @AffineBaseChange.isIso_of_isIso_moduleSpecΓ _ _ _ hqc1 hqc2 _ hpost
  exact preservesColimit_of_isIso_post (Scheme.Modules.pushforward (Spec.map φ)) D

end Stacks.AlgebraicGeometry.PushforwardColimits

end

end
