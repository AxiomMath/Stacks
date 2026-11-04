module

public import StacksFrontier.Algebra.Homology.DerivedCategory.ProjectiveHomologySplitting
public import StacksFrontier.Algebra.Homology.RestrictScalarsHomology
public import StacksFrontier.AlgebraicGeometry.Curves.VanishingResults.TorsionFreeGlobalGeneration
public import StacksFrontier.AlgebraicGeometry.Duality.ProperOverField.DualizingComplex
public import StacksFrontier.AlgebraicGeometry.Duality.RelativeDualizing.DerivedStalkModel
public import StacksFrontier.RingTheory.Dualizing.ConcentratedDualizingModule
public import StacksFrontier.RingTheory.Dualizing.OverField
public import StacksFrontier.RingTheory.Dualizing.ResidueFieldShift
import StacksCore.Tactic.StacksAttribute

/-!
# The dualizing sheaf of an integral proper curve has rank one, and Tag 0B5G

In Situation [Stacks, Tag 0B5D] — a field `k` and a proper one-dimensional `k`-scheme `X` with
`H⁰(X, 𝒪_X) = k` — assume `X` integral and let `ω_X = H^{-1}(f^×(𝒪_{Spec k}))` be the dualizing
sheaf of [Stacks, Tag 0BS2]. This file proves that the stalk of `ω_X` at the generic point is a
one-dimensional vector space over the function field, and with it [Stacks, Tag 0B5G]: an extension
`0 ⟶ ω_X ⟶ ℱ ⟶ 𝒬 ⟶ 0` of coherent modules with `ℱ` torsion free, `dim Supp 𝒬 ≤ 0` and
`dim_k H⁰(X, 𝒬) ≥ 2` has `ℱ` globally generated.

## Main results

The elided prefix is `AlgebraicGeometry.CohenMacaulayCurveSituation`.

* `isSimpleModule_genericStalk_dualizingSheafOverField`: the generic stalk of `ω_X` is a simple
  module over the function field.
* `nonempty_generatingSections_of_isTorsionFree`: **[Stacks, Tag 0B5G]**.

## Implementation notes

The rank-one statement is the input the source's proof uses when it says that `ℱ' ⊆ ℱ` is an
inclusion of rank one sheaves and that a nonzero endomorphism of a torsion-free rank one sheaf is
an automorphism; it comes from the local theory of the dualizing complex, which is why the proof
of [Stacks, Tag 0B5G] cites [Stacks, Tags 0FVV, 0AWF, 0A7R]. The global argument is in
`StacksFrontier/AlgebraicGeometry/Curves/VanishingResults/TorsionFreeGlobalGeneration.lean`.

The derived stalk at the generic point is `Stacks.Duality.derivedStalkOfComplex`, computed on a
representative of `ω_X^•`; the module categories over local rings carry the standard model of
their derived category, the one `Dualizing.IsNormalizedDualizingComplex` is stated at, introduced
inside the proof.

"Globally generated" is Mathlib's `SheafOfModules.GeneratingSections`, a family of global sections
whose map from the free module is an epimorphism; the family used is all of `Γ(X, ℱ)`, i.e.
`AlgebraicGeometry.globalSectionsHom ℱ` is an epimorphism. The source's `dim(Supp(𝒬)) = 0` is
weakened to `dim(Supp(𝒬)) ≤ 0`, the torsion freeness of `ℱ` is
`Stacks.AlgebraicGeometry.ReflexiveModules.IsTorsionFree` ([Stacks, Tag 0AVR]).

## References

* [Stacks Project, Tag 0B5G](https://stacks.math.columbia.edu/tag/0B5G)
* [Stacks Project, Tag 0FVV](https://stacks.math.columbia.edu/tag/0FVV)
* [Stacks Project, Tag 0AWF](https://stacks.math.columbia.edu/tag/0AWF)
* [Stacks Project, Tag 0A7R](https://stacks.math.columbia.edu/tag/0A7R)
* [Stacks Project, Tag 0BS2](https://stacks.math.columbia.edu/tag/0BS2)
-/

-- This file uses the locally small derived-category models below, which are not
-- global instances (see `StacksFrontier.Homology.DerivedCategory.LocallySmall`):
-- `D(R)` for `R`-modules.
-- `D(R)` for sheaves of modules on a small site.
-- `D(𝒪_X)` for a scheme.
attribute [local instance] ModuleCat.hasDerivedCategory
attribute [local instance] SheafOfModules.hasDerivedCategory
attribute [local instance] AlgebraicGeometry.Scheme.Modules.hasDerivedCategory

@[expose] public noncomputable section

universe u

open CategoryTheory CategoryTheory.Limits

namespace AlgebraicGeometry

namespace CohenMacaulayCurveSituation

variable (S : CohenMacaulayCurveSituation.{u})

/-- **On an integral `X`, the generic stalk of `ω_X` is one-dimensional over the function
field**: `ω_X` has rank one.

`ω_X^• = f^×(𝒪_{Spec k})` is a dualizing complex ([Stacks, Tag 0FVV]), so its derived stalk at
the generic point `η` is, up to the shift of [Stacks, Tag 0AWF], a normalized dualizing complex
over the field `𝒪_{X,η}`, hence a simple object of `D(𝒪_{X,η})` with bounded cohomology, hence a
shift of `𝒪_{X,η}` placed in degree zero (the field case of [Stacks, Tag 0A7R]). The stalk of
`ω_X = H^{-1}(ω_X^•)` at `η` is the degree `-1` cohomology of that derived stalk, because the stalk
functor is exact; it is therefore either `0` or `𝒪_{X,η}`, and it is not `0` because `ω_X` is a
nonzero module with no submodule supported in dimension zero (clause (2) of [Stacks, Tag 0BS2]). -/
public theorem isSimpleModule_genericStalk_dualizingSheafOverField [IsIntegral S.X] :
    IsSimpleModule S.X.functionField
      ((genericStalkFunctor S.X).obj (Stacks.Duality.dualizingSheafOverField S.f)) := by
  let : IsLocallyNoetherian S.X := LocallyOfFiniteType.isLocallyNoetherian S.f
  have hω : Stacks.Duality.IsDualizingComplex (Stacks.Duality.dualizingComplexOverField S.f).obj :=
    Stacks.Duality.isDualizingComplex_relativeDualizingComplex_of_isProper S.f
  have hωc : (Stacks.Duality.dualizingSheafOverField S.f).IsCoherent :=
    Stacks.Duality.isCoherent_homology_of_isDualizingComplex hω (-1)
  have hne : ¬ IsZero ((genericStalkFunctor S.X).obj
      (Stacks.Duality.dualizingSheafOverField S.f)) := by
    rw [← genericPoint_mem_supp_iff]
    by_contra hη
    exact not_isZero_dualizingSheafOverField S
      (Stacks.Duality.isZero_of_mono_dualizingSheafOverField_of_supp_dim_le_zero S.f
        (le_of_eq S.dimension_one) _ (𝟙 _) inferInstance hωc
        ((topologicalKrullDim_supp_le_zero_iff hωc).mpr hη))
  obtain ⟨E, ⟨eE⟩⟩ : ∃ E : CochainComplex S.X.Modules ℤ,
      Nonempty (DerivedCategory.Q.obj E ≅ (Stacks.Duality.dualizingComplexOverField S.f).obj) :=
    ⟨_, ⟨DerivedCategory.Q.objObjPreimageIso _⟩⟩
  let := HasDerivedCategory.standard (ModuleCat.{u} (S.X.presheaf.stalk (genericPoint S.X)))
  have h0AWF :=
    ((Stacks.Duality.isUniversallyCatenary_and_isDimensionFunction_associatedShiftFunction
      hω).2.1 (genericPoint S.X) E ⟨eE⟩ _).mpr rfl
  set δ := Stacks.Duality.associatedShiftFunction (Stacks.Duality.dualizingComplexOverField S.f).obj
    (genericPoint S.X)
  set D := Stacks.Duality.derivedStalkOfComplex (genericPoint S.X) E
  have hdual : Dualizing.IsDualizingComplex (D⟦-δ⟧) := h0AWF.1
  have : Simple (D⟦-δ⟧) := Dualizing.simple_of_isDualizingComplex_field.{u, u} _ hdual
  obtain ⟨a, b, I, hge, hle, _, ⟨eI⟩⟩ := hdual.finiteInjectiveDimension
  have := hge
  have := hle
  have : (D⟦-δ⟧).IsGE a := DerivedCategory.TStructure.t.isGE_of_iso eI.symm a
  have : (D⟦-δ⟧).IsLE b := DerivedCategory.TStructure.t.isLE_of_iso eI.symm b
  obtain ⟨n, ⟨en⟩⟩ := Dualizing.simple_bounded_iso_shift_field.{u, u} (D⟦-δ⟧) a b
  have e1 : (genericStalkFunctor S.X).obj (Stacks.Duality.dualizingSheafOverField S.f) ≅
      (DerivedCategory.homologyFunctor
        (ModuleCat.{u} (S.X.presheaf.stalk (genericPoint S.X))) (-1)).obj D :=
    (genericStalkFunctor S.X).mapIso
        ((DerivedCategory.homologyFunctor S.X.Modules (-1)).mapIso eE.symm ≪≫
          (DerivedCategory.homologyFunctorFactors S.X.Modules (-1)).app E) ≪≫
      (Stacks.Homology.RestrictScalars.mapHomologicalComplexHomologyIso
        (genericStalkFunctor S.X) E (-1)).symm ≪≫
      ((DerivedCategory.homologyFunctorFactors _ (-1)).app _).symm
  have e2 : (DerivedCategory.homologyFunctor
        (ModuleCat.{u} (S.X.presheaf.stalk (genericPoint S.X))) (-1)).obj D ≅
      (DerivedCategory.homologyFunctor _ (n + (-1 + δ))).obj
        ((DerivedCategory.singleFunctor
          (ModuleCat.{u} (S.X.presheaf.stalk (genericPoint S.X))) 0).obj
            (ModuleCat.of _ (ULift.{u} (S.X.presheaf.stalk (genericPoint S.X))))) :=
    (Dualizing.homologyShiftObjIsoOfEq D (-δ) (-1 + δ) (-1) (by ring)).symm ≪≫
      (DerivedCategory.homologyFunctor _ (-1 + δ)).mapIso en ≪≫
      Dualizing.homologyShiftObjIsoOfEq _ n (-1 + δ) (n + (-1 + δ)) rfl
  by_cases hdeg : n + (-1 + δ) = 0
  · have e3 := eqToIso (congrArg (fun i => (DerivedCategory.homologyFunctor
        (ModuleCat.{u} (S.X.presheaf.stalk (genericPoint S.X))) i).obj
          ((DerivedCategory.singleFunctor
            (ModuleCat.{u} (S.X.presheaf.stalk (genericPoint S.X))) 0).obj
              (ModuleCat.of _ (ULift.{u} (S.X.presheaf.stalk (genericPoint S.X)))))) hdeg) ≪≫
      (DerivedCategory.singleFunctorCompHomologyFunctorIso _ 0).app _
    have hV : IsSimpleModule S.X.functionField (ULift.{u} S.X.functionField) :=
      IsSimpleModule.congr (ULift.moduleEquiv (R := S.X.functionField))
    exact @IsSimpleModule.congr _ _ _ _ _ _ _ _ (e1 ≪≫ e2 ≪≫ e3).toLinearEquiv hV
  · exact absurd ((DerivedCategory.Plus.isZero_homologyFunctor_singleFunctor_obj _ hdeg).of_iso
      (e1 ≪≫ e2)) hne

variable {S}

/-- `ℱ` is generated by its global sections, `globalSectionsHom` read as Mathlib's
`SheafOfModules.GeneratingSections`. -/
public theorem nonempty_generatingSections_of_epi_globalSectionsHom {X : Scheme.{u}}
    {F : X.Modules} (h : Epi (globalSectionsHom F)) :
    Nonempty (F : SheafOfModules X.ringCatSheaf).GeneratingSections :=
  ⟨{ I := F.sections, s := fun s => s, epi := h }⟩

/-- **Stacks Project, Tag 0B5G.** In Situation [Stacks, Tag 0B5D] assume that `X` is integral,
let `ω_X = H^{-1}(f^×(𝒪_{Spec k}))` be the dualizing sheaf of [Stacks, Tag 0BS2], and let
`0 ⟶ ω_X ⟶ ℱ ⟶ 𝒬 ⟶ 0` be a short exact sequence of coherent `𝒪_X`-modules with `ℱ` torsion free
([Stacks, Tag 0AVR]), `dim Supp 𝒬 ≤ 0` and `dim_k H⁰(X, 𝒬) ≥ 2`. Then `ℱ` is globally generated.

The generic stalk of `ω_X` is one-dimensional over the function field
(`isSimpleModule_genericStalk_dualizingSheafOverField`, from [Stacks, Tags 0FVV, 0AWF, 0A7R]),
and `epi_globalSectionsHom_of_isSimpleModule_genericStalk` runs the source's argument from there:
[Stacks, Tag 0B5F], the duality of clause (5) of [Stacks, Tag 0BS2], and the finiteness of
[Stacks, Tag 02O6]. -/
@[stacks 0B5G]
public theorem nonempty_generatingSections_of_isTorsionFree [IsIntegral S.X] {F Q : S.X.Modules}
    (hFc : F.IsCoherent) (hQc : Q.IsCoherent)
    (α : Stacks.Duality.dualizingSheafOverField S.f ⟶ F) (β : F ⟶ Q) (hαβ : α ≫ β = 0)
    (hS : (ShortComplex.mk α β hαβ).ShortExact)
    (hTF : Stacks.AlgebraicGeometry.ReflexiveModules.IsTorsionFree F)
    (hQdim : topologicalKrullDim (SheafOfModules.supp Q) ≤ 0)
    (htwo : 2 ≤ Module.finrank S.k (cohomologyOverField S.k S.f Q 0)) :
    Nonempty (F : SheafOfModules S.X.ringCatSheaf).GeneratingSections := by
  have : IsLocallyNoetherian S.X := LocallyOfFiniteType.isLocallyNoetherian S.f
  have hFq := Stacks.AlgebraicGeometry.CoherentTFAE.isQuasicoherent_isFiniteType_of_isCoherent F
  have hQq := (Stacks.AlgebraicGeometry.CoherentTFAE.isQuasicoherent_isFiniteType_of_isCoherent
    Q).1
  exact nonempty_generatingSections_of_epi_globalSectionsHom
    (epi_globalSectionsHom_of_isSimpleModule_genericStalk
      (isSimpleModule_genericStalk_dualizingSheafOverField S) hFq.1 hFq.2 hQq α β hαβ hS hTF
      hQdim htwo)

end CohenMacaulayCurveSituation

end AlgebraicGeometry

end
