module

public import StacksFrontier.AlgebraicGeometry.Cohomology.InjectiveQcoh.InjectiveQcohSpace
public import StacksFrontier.AlgebraicGeometry.Spaces.ModulePushforwardAbelianSheaf
public import StacksFrontier.AlgebraicGeometry.Spaces.QuasicoherentCoherator
public import StacksFrontier.AlgebraicGeometry.Spaces.SmallEtaleCohomologyFilteredColimits
public import StacksFrontier.CategoryTheory.Sites.Cohomology.Acyclicity.PushforwardOfAnInjective
public import StacksFrontier.CategoryTheory.Sites.Modules.SliceRestrictionColimits
public import StacksFrontier.CategoryTheory.Sites.UniverseLiftColimits
public import StacksFrontier.CategoryTheory.Sites.UniverseLiftDerived
public import StacksFrontier.CategoryTheory.Sites.UniverseLiftInjective
import StacksCore.Tactic.EgaSgaAttribute

/-!
# Filtered colimits and the direct image of quasi-coherent modules

Let `f : X ⟶ Y` be a quasi-compact and quasi-separated morphism of algebraic spaces over a
scheme `S`, with representable underlying morphism.  The direct image `f_*` of Stacks 03LU
preserves filtered colimits of `𝒪_X`-modules, and therefore so does its restriction
`QCoh(𝒪_X) ⥤ QCoh(𝒪_Y)` to the quasi-coherent modules of Stacks 03G9.

This is the degree-zero case of Stacks 07U6, read for modules at the universe `u` of the
structure rings: the abelian sheaf underlying `f_*𝓕` is the direct image of the abelian sheaf
underlying `𝓕`, the forgetful functor to abelian sheaves preserves and reflects colimits, and
quasi-coherence is closed under colimits, so both passages are transparent to colimits.

## Main results

* `AlgebraicGeometry.Space.preservesColimit_smallEtaleAbelianPushforward_of_qcqs`: the direct
  image of abelian sheaves on the small étale sites, at the universe of the structure rings,
  preserves a filtered colimit.
* `AlgebraicGeometry.Space.preservesFilteredColimitsOfSize_modulePushforward_of_qcqs`: the
  direct image of `𝒪_X`-modules preserves filtered colimits.
* `AlgebraicGeometry.Space.preservesFilteredColimitsOfSize_chartQuasicoherentPushforward` and
  its specialisation to a morphism whose source is a scheme,
  `...preservesFilteredColimitsOfSize_chartQuasicoherentPushforward_schemeSpace`: the direct
  image of quasi-coherent modules preserves filtered colimits.

## Implementation notes

Stacks 07U6 in the form
`AlgebraicGeometry.Space.isIso_colimit_post_rightDerived_smallEtaleAbelianPushforward` is about
abelian sheaves with sections at the universe `u + 1` of the objects of the small étale site,
whereas an `𝒪_X`-module at the universe `u` of the structure rings has its underlying
abelian sheaf at `u`.  The two are reconciled by the universe lift
`Stacks.Sheaves.UniverseLift.uliftSheafFunctor`, which commutes with restriction along a
continuous functor on the nose, preserves colimits indexed at `u`, and is fully faithful, hence
reflects them.  This is why the direct image is taken in the site-level form
`AlgebraicGeometry.Space.smallEtaleAbelianPushforward` — restriction along base change of étale
scheme charts, Stacks 03G2, part (4) — rather than in the topos-level form Stacks 07U6 is stated
with; the two are identified by `abelianPushforwardSmallEtaleIso` below.

Representability of `f` is what makes that base change of scheme charts exist, and it is the one
hypothesis here beyond those of Stacks 07U6; for a morphism whose source is a scheme it is
automatic, by the representability of the diagonal of an algebraic space.

## References

* [Stacks Project, Tag 07U6](https://stacks.math.columbia.edu/tag/07U6)
* [Stacks Project, Tag 073E](https://stacks.math.columbia.edu/tag/073E)
* [Stacks Project, Tag 03LU](https://stacks.math.columbia.edu/tag/03LU)
* [Stacks Project, Tag 03M1](https://stacks.math.columbia.edu/tag/03M1)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits
open Stacks.Topos.AbelianPushforward
open Stacks.Sheaves.UniverseLift

universe u

namespace AlgebraicGeometry.Space

variable (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)
variable {X Y : AlgebraicSpaces B S hS}

/-- The direct image of abelian sheaves along the morphism of small étale topoi of Stacks 03G2,
part (3), is restriction along base change of étale scheme charts.  Both have the same underlying
direct image of sheaves of sets, by Stacks 03G2, part (4). -/
private def abelianPushforwardSmallEtaleIso (f : X ⟶ Y)
    (hf : yoneda.relativelyRepresentable f.hom) :
    abelianPushforward (SmallEtale.topology B S hS X.1) (smallToposMorphism B S hS f) ≅
      smallEtaleAbelianPushforward.{u + 1} B S hS f hf :=
  letI := (smallBaseChange_isMorphismOfSites B S hS f hf).toIsContinuous
  Stacks.Cohomology.abelianSheafNatIsoOfUnderlying (SmallEtale.topology B S hS Y.1) _ _
    (abelianPushforward_forgetIso _ _ ≪≫
      Functor.isoWhiskerLeft _ (smallBaseChange_topos B S hS f hf))

/-- **Stacks 07U6 in degree zero**, for abelian sheaves with sections at the universe of the
objects of the small étale site.  The direct image along a quasi-compact and quasi-separated
morphism with representable underlying morphism preserves a filtered colimit, the degree-zero
higher direct image being the direct image itself. -/
@[sga "4 VI 8.5.11" "special case"]
private theorem preservesColimit_smallEtaleAbelianPushforward_uliftCoefficients
    (hZ : B.Contains (⊤_ Scheme.{u})) (f : X ⟶ Y)
    (hf : yoneda.relativelyRepresentable f.hom)
    (hqc : IsQuasiCompact B S hS f.hom) (hqs : IsQuasiSeparated B S hS f.hom)
    {I : Type u} [SmallCategory I] [IsFiltered I]
    (F : I ⥤ Sheaf (SmallEtale.topology B S hS X.1) AddCommGrpCat.{u + 1}) :
    PreservesColimit F (smallEtaleAbelianPushforward.{u + 1} B S hS f hf) := by
  have h := isIso_colimit_post_rightDerived_smallEtaleAbelianPushforward B S hS hZ f hqc hqs 0 F
  have h1 : PreservesColimit F
      ((abelianPushforward (SmallEtale.topology B S hS X.1)
        (smallToposMorphism B S hS f)).rightDerived 0) := preservesColimit_of_isIso_post _ _
  have h2 : PreservesColimit F
      (abelianPushforward (SmallEtale.topology B S hS X.1) (smallToposMorphism B S hS f)) :=
    preservesColimit_of_natIso F (Functor.rightDerivedZeroIsoSelf _)
  exact preservesColimit_of_natIso F (abelianPushforwardSmallEtaleIso B S hS f hf)

/-- **Stacks 07U6 in degree zero**, for abelian sheaves with sections at the universe of the
structure rings: the direct image of abelian sheaves on the small étale sites along a
quasi-compact and quasi-separated morphism with representable underlying morphism preserves a
filtered colimit.

The universe lift of abelian sheaves commutes with restriction along the base change of étale
scheme charts, preserves the colimit and reflects it, being fully faithful, so this follows from
the same statement one universe up. -/
theorem preservesColimit_smallEtaleAbelianPushforward_of_qcqs
    (hZ : B.Contains (⊤_ Scheme.{u})) (f : X ⟶ Y)
    (hf : yoneda.relativelyRepresentable f.hom)
    (hqc : IsQuasiCompact B S hS f.hom) (hqs : IsQuasiSeparated B S hS f.hom)
    {I : Type u} [SmallCategory I] [IsFiltered I]
    (A : I ⥤ Sheaf (SmallEtale.topology B S hS X.1) AddCommGrpCat.{u}) :
    PreservesColimit A (smallEtaleAbelianPushforward.{u} B S hS f hf) := by
  let := (smallBaseChange_isMorphismOfSites B S hS f hf).toIsContinuous
  have hLX : PreservesColimitsOfSize.{u, u}
      (uliftSheafFunctor.{u + 1, u} (SmallEtale.topology B S hS X.1)) :=
    sheafCompose_uliftFunctor_preservesColimits.{_, _, u, u + 1}
  have hLY : PreservesColimitsOfSize.{u, u}
      (uliftSheafFunctor.{u + 1, u} (SmallEtale.topology B S hS Y.1)) :=
    sheafCompose_uliftFunctor_preservesColimits.{_, _, u, u + 1}
  let : PreservesColimit A
      (uliftSheafFunctor.{u + 1, u} (SmallEtale.topology B S hS X.1) ⋙
        smallEtaleAbelianPushforward.{u + 1} B S hS f hf) := by
    refine ⟨fun {c} hc => ⟨?_⟩⟩
    let := preservesColimit_smallEtaleAbelianPushforward_uliftCoefficients B S hS hZ f hf hqc hqs
      (A ⋙ uliftSheafFunctor.{u + 1, u} (SmallEtale.topology B S hS X.1))
    exact isColimitOfPreserves (smallEtaleAbelianPushforward.{u + 1} B S hS f hf)
      (isColimitOfPreserves (uliftSheafFunctor.{u + 1, u}
        (SmallEtale.topology B S hS X.1)) hc)
  let : PreservesColimit A
      (smallEtaleAbelianPushforward.{u} B S hS f hf ⋙
        uliftSheafFunctor.{u + 1, u} (SmallEtale.topology B S hS Y.1)) :=
    preservesColimit_of_natIso A
      (sheafPushforwardContinuousULiftIso (SmallEtale.topology B S hS Y.1)
        (SmallEtale.topology B S hS X.1) (smallBaseChange B S hS f hf)).symm
  let : (uliftSheafFunctor.{u + 1, u}
      (SmallEtale.topology B S hS Y.1)).ReflectsIsomorphisms :=
    (fullyFaithfulUliftSheafFunctor (SmallEtale.topology B S hS Y.1)).reflectsIsomorphisms
  let : ReflectsColimitsOfShape I
      (uliftSheafFunctor.{u + 1, u} (SmallEtale.topology B S hS Y.1)) :=
    reflectsColimitsOfShape_of_reflectsIsomorphisms
  refine ⟨fun {c} hc => ?_⟩
  exact (show ReflectsColimitsOfShape I (uliftSheafFunctor.{u + 1, u}
      (SmallEtale.topology B S hS Y.1)) from inferInstance).reflectsColimit.reflects
    (isColimitOfPreserves (smallEtaleAbelianPushforward.{u} B S hS f hf ⋙
      uliftSheafFunctor.{u + 1, u} (SmallEtale.topology B S hS Y.1)) hc)

/-- **The direct image of `𝒪_X`-modules along a quasi-compact and quasi-separated morphism with
representable underlying morphism preserves filtered colimits.**  This is Stacks 07U6 in degree
zero, read on modules.

The abelian sheaf underlying `f_*𝓕` is the direct image of the one underlying `𝓕`
(`AlgebraicGeometry.Space.modulePushforwardCompToSheafIso`), and the forgetful functor to abelian
sheaves both preserves and reflects colimits. -/
@[sga "4 VI 8.5.11" "special case"]
theorem preservesFilteredColimitsOfSize_modulePushforward_of_qcqs
    (hZ : B.Contains (⊤_ Scheme.{u})) (f : X ⟶ Y)
    (hf : yoneda.relativelyRepresentable f.hom)
    (hqc : IsQuasiCompact B S hS f.hom) (hqs : IsQuasiSeparated B S hS f.hom) :
    PreservesFilteredColimitsOfSize.{u, u} (modulePushforward B S hS f) := by
  refine ⟨fun I _ _ => ?_⟩
  let : PreservesColimitsOfShape I
      (SheafOfModules.toSheaf.{u} (structureRingSheaf B S hS X)) :=
    Stacks.SheafOfModules.preservesColimits_toSheaf.preservesColimitsOfShape
  let : ReflectsColimitsOfShape I
      (SheafOfModules.toSheaf.{u} (structureRingSheaf B S hS Y)) :=
    Stacks.SheafOfModules.reflectsColimits_toSheaf.reflectsColimitsOfShape
  have hcomp : PreservesColimitsOfShape I
      (SheafOfModules.toSheaf.{u} (structureRingSheaf B S hS X) ⋙
        smallEtaleAbelianPushforward.{u} B S hS f hf) := by
    refine ⟨fun {D} => ⟨fun {c} hc => ⟨?_⟩⟩⟩
    let := preservesColimit_smallEtaleAbelianPushforward_of_qcqs B S hS hZ f hf hqc hqs
      (D ⋙ SheafOfModules.toSheaf.{u} (structureRingSheaf B S hS X))
    exact isColimitOfPreserves (smallEtaleAbelianPushforward.{u} B S hS f hf)
      (isColimitOfPreserves (SheafOfModules.toSheaf.{u} (structureRingSheaf B S hS X)) hc)
  let : PreservesColimitsOfShape I (modulePushforward B S hS f ⋙
      SheafOfModules.toSheaf.{u} (structureRingSheaf B S hS Y)) :=
    (preservesColimitsOfShape_iff_of_natIso
      (modulePushforwardCompToSheafIso B S hS f hf)).mpr hcomp
  refine ⟨fun {D} => ⟨fun {c} hc => ?_⟩⟩
  exact (show ReflectsColimitsOfShape I
      (SheafOfModules.toSheaf.{u} (structureRingSheaf B S hS Y)) from
    inferInstance).reflectsColimit.reflects
      (isColimitOfPreserves (modulePushforward B S hS f ⋙
        SheafOfModules.toSheaf.{u} (structureRingSheaf B S hS Y)) hc)

/-- **The direct image of quasi-coherent modules along a quasi-compact and quasi-separated
morphism with representable underlying morphism preserves filtered colimits.**  This is
Stacks 07U6 in degree zero, read in `QCoh` of Stacks 03G9.

Quasi-coherence is closed under colimits of any shape by the colimit clause of Stacks 03M1, so
the inclusion of `QCoh(𝒪)` into the `𝒪`-modules creates — in particular preserves and reflects —
them, and the statement is the one for all modules. -/
theorem preservesFilteredColimitsOfSize_chartQuasicoherentPushforward
    (hZ : B.Contains (⊤_ Scheme.{u})) (j : Y ⟶ X)
    (hj : yoneda.relativelyRepresentable j.hom)
    (hqc : IsQuasiCompact B S hS j.hom) (hqs : IsQuasiSeparated B S hS j.hom)
    (hqcoh : ∀ M : QuasicoherentSheaves.{u, u} B S hS Y.1 Y.2,
      ((modulePushforward B S hS j).obj M.obj).IsQuasicoherentOnSite) :
    PreservesFilteredColimitsOfSize.{u, u}
      (chartQuasicoherentPushforward B S hS j hqcoh) := by
  refine ⟨fun I _ _ => ?_⟩
  let : PreservesColimitsOfShape I (modulePushforward B S hS j) :=
    (preservesFilteredColimitsOfSize_modulePushforward_of_qcqs B S hS hZ j hj hqc
      hqs).preserves_filtered_colimits I
  let := isClosedUnderColimitsOfShape_quasicoherentSheaves_schemeUniverse B S hS Y.1 Y.2 I
  let := isClosedUnderColimitsOfShape_quasicoherentSheaves_schemeUniverse B S hS X.1 X.2 I
  let : PreservesColimitsOfShape I (SheafOfModules.isQuasicoherentOnSite.{u + 1, u, u, u}
      (Stacks.SheafOfModules.Tensor.ringSheaf
        (smallEtaleRingedSite B S hS Y.1 Y.2).O)).ι :=
    preservesColimitOfShape_of_createsColimitsOfShape_and_hasColimitsOfShape _
  let : PreservesColimitsOfShape I (chartQuasicoherentPushforward B S hS j hqcoh ⋙
      (SheafOfModules.isQuasicoherentOnSite.{u + 1, u, u, u}
        (Stacks.SheafOfModules.Tensor.ringSheaf
          (smallEtaleRingedSite B S hS X.1 X.2).O)).ι) :=
    (preservesColimitsOfShape_iff_of_natIso
      (ObjectProperty.liftCompιIso _ _ hqcoh)).mpr inferInstance
  refine ⟨fun {D} => ⟨fun {c} hc => ?_⟩⟩
  exact (show ReflectsColimitsOfShape I (SheafOfModules.isQuasicoherentOnSite.{u + 1, u, u, u}
      (Stacks.SheafOfModules.Tensor.ringSheaf
        (smallEtaleRingedSite B S hS X.1 X.2).O)).ι from
    inferInstance).reflectsColimit.reflects
      (isColimitOfPreserves (chartQuasicoherentPushforward B S hS j hqcoh ⋙
        (SheafOfModules.isQuasicoherentOnSite.{u + 1, u, u, u}
          (Stacks.SheafOfModules.Tensor.ringSheaf
            (smallEtaleRingedSite B S hS X.1 X.2).O)).ι) hc)

/-- **Stacks 07U6 in degree zero, read in `QCoh` along a morphism whose source is a scheme.**
For a quasi-compact and quasi-separated morphism `j : U ⟶ X` from the algebraic space of a
scheme, the direct image of quasi-coherent modules preserves filtered colimits.

Representability of `j` is automatic: the diagonal of the algebraic space `X` is representable,
and `j` has representable source. -/
theorem preservesFilteredColimitsOfSize_chartQuasicoherentPushforward_schemeSpace
    (hZ : B.Contains (⊤_ Scheme.{u})) (U : BigFppfOver B S hS) (j : schemeSpace U ⟶ X)
    (hqc : IsQuasiCompact B S hS j.hom) (hqs : IsQuasiSeparated B S hS j.hom)
    (hqcoh : ∀ M : QuasicoherentSheaves.{u, u} B S hS
        (schemeSpace U).1 (schemeSpace U).2,
      ((modulePushforward B S hS j).obj M.obj).IsQuasicoherentOnSite) :
    PreservesFilteredColimitsOfSize.{u, u}
      (chartQuasicoherentPushforward B S hS j hqcoh) :=
  preservesFilteredColimitsOfSize_chartQuasicoherentPushforward B S hS hZ j
    (X.2.diagonal_representable.of_diag j.hom) hqc hqs hqcoh

end AlgebraicGeometry.Space

end
