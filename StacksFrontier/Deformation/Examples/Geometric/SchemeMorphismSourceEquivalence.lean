module

public import StacksFrontier.AlgebraicGeometry.BaseAdicFiltration.ReductionIdealSheaf
public import StacksFrontier.Deformation.Examples.Geometric.SchemeMorphismSourceTower
public import StacksFrontier.Deformation.Examples.Geometric.SpecialFibreCartesian

/-!
# The source-forgetful functor is an equivalence

Let `f : X ⟶ Y` be a morphism of schemes over the residue field `k` with `f_*𝒪_X = 𝒪_Y` and
`R¹f_*𝒪_X = 0`. Then the functor forgetting the target of a deformation of `f` is an equivalence
onto the deformations of `X`.

## Main results

* `Deformation.Examples.exists_pushforwardTarget_isPullback_of_specialFibre`: a flat deformation
  `U` of `X` is the source of a morphism `g : U ⟶ V` to a flat family `V` with special fibre `Y`,
  both special-fibre squares being cartesian.
* `Deformation.Examples.schemeMorphismSourceForgetful_essSurj_of_specialFibre`: the
  source-forgetful functor is essentially surjective.
* `Deformation.Examples.schemeMorphismSourceForgetful_isEquivalence_of_specialFibre`: the
  source-forgetful functor is an equivalence.

## References

* [Stacks Project, Tag 0E3X](https://stacks.math.columbia.edu/tag/0E3X)
* [Stacks Project, Tag 0DY7](https://stacks.math.columbia.edu/tag/0DY7)
* [Stacks Project, Tag 0E3T](https://stacks.math.columbia.edu/tag/0E3T)
-/

@[expose] public noncomputable section

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits

universe u

namespace Deformation.Examples

variable {Λ k : Type u} [CommRing Λ] [Field k] [Algebra Λ k]

/-- Let `p : U ⟶ Spec A` be a flat family over an object of `𝒞_Λ` whose special fibre is cut
out by `i_X : X ⟶ U`, and let `f : X ⟶ Y` be a morphism over the residue field with
`f_*𝒪_X = 𝒪_Y` and `R¹f_*𝒪_X = 0`. Then there are a flat family `pV : V ⟶ Spec A` and a
morphism `g : U ⟶ V` over `Spec A`, together with a closed immersion `i_Y : Y ⟶ V` exhibiting `Y`
as the special fibre of `V` cartesianly, such that `X` is the fibre product of `Y` and `U` over
`V`. -/
theorem exists_pushforwardTarget_isPullback_of_specialFibre
    {A : ArtinianLocalAlgCat.{u, u, u} Λ k} {U X Y : Scheme.{u}}
    (p : U ⟶ baseSpec A) [AlgebraicGeometry.Flat p]
    {iX : X ⟶ U} {qX : X ⟶ baseSpec (residueFieldBase Λ k)}
    (hcart : IsPullback iX qX p (residueSpecMap A))
    (fXY : X ⟶ Y) (qY : Y ⟶ baseSpec (residueFieldBase Λ k)) (hf : fXY ≫ qY = qX)
    (h0 : IsIso (C := Y.Modules) (Scheme.Modules.unitToPushforwardUnit fXY))
    (hR : IsZero (((Scheme.Modules.pushforward fXY).rightDerived 1).obj
      (SheafOfModules.unit X.ringCatSheaf))) :
    ∃ (V : Scheme.{u}) (pV : V ⟶ baseSpec A) (g : U ⟶ V) (iY : Y ⟶ V),
      AlgebraicGeometry.Flat pV ∧ g ≫ pV = p ∧
        IsPullback iY qY pV (residueSpecMap A) ∧ IsPullback fXY iX iY g := by
  have : IsClosedImmersion iX :=
    MorphismProperty.IsStableUnderBaseChange.of_isPullback (P := @IsClosedImmersion)
      hcart.flip (residueSpecMap_isClosedImmersion A)
  have hkm : iX.ker =
      Stacks.BaseAdicFiltration.baseIdeal p (IsLocalRing.maximalIdeal A) :=
    ker_eq_baseIdeal_of_isPullback p hcart
  have hcomm : iX ≫ p = fXY ≫ (qY ≫ residueSpecMap A) := by
    rw [← Category.assoc, hf, hcart.w]
  obtain ⟨V, pV, g, iY, hgc, hgp, hiYt, hiYq, hsq⟩ :=
    exists_pushforwardTarget_of_specialFibre p iX hkm fXY (qY ≫ residueSpecMap A) hcomm h0 hR
  have : IsClosedImmersion iY := hiYt.1
  obtain ⟨hflat, hkY⟩ :=
    Stacks.BaseAdicFiltration.flat_and_ker_eq_baseIdeal_of_specialFibre p pV iX iY fXY g
      hgp (Scheme.isIso_unitToPushforwardUnit_of_isIso_c g hgc) hkm hsq h0 hR
  have htgt : IsPullback iY qY pV (residueSpecMap A) :=
    isPullback_of_ker_eq_baseIdeal_of_eq pV iY qY hiYq rfl hkY
  refine ⟨V, pV, g, iY, hflat, hgp, htgt, IsPullback.of_right ?_ hsq.symm htgt.flip⟩
  rw [hf, hgp]
  exact hcart.flip

section SourceForgetful

variable {X Y : Scheme.{u}} (f : X ⟶ Y)
  (pX : X ⟶ baseSpec (residueFieldBase Λ k)) (pY : Y ⟶ baseSpec (residueFieldBase Λ k))
  (hf : f ≫ pY = pX)

/-- If `f_*𝒪_X = 𝒪_Y` and `R¹f_*𝒪_X = 0`, every deformation of `X` is the source of a
deformation of `f`: the source-forgetful functor is essentially surjective. -/
theorem schemeMorphismSourceForgetful_essSurj_of_specialFibre
    (h0 : IsIso (C := Y.Modules) (Scheme.Modules.unitToPushforwardUnit f))
    (hR : IsZero (((Scheme.Modules.pushforward f).rightDerived 1).obj
      (SheafOfModules.unit X.ringCatSheaf))) :
    (schemeMorphismSourceForgetful f pX pY hf).EssSurj where
  mem_essImage S := by
    have := S.flat
    obtain ⟨V, pV, g, iY, hflat, hgp, htgt, hsrc⟩ :=
      exists_pushforwardTarget_isPullback_of_specialFibre S.toBase S.specialCartesian f pY hf
        h0 hR
    have htgt' : IsPullback iY pY pV
        (baseSpecMap ((isTerminal_residueFieldBase (Λ := Λ) (k := k)).from S.base)) := by
      rw [baseSpecMap_eq_residueSpecMap]
      exact htgt
    exact ⟨Over.mk
      ({ base := (isTerminal_residueFieldBase (Λ := Λ) (k := k)).from S.base
         source := S.specialMap
         target := iY
         source_pullback := hsrc
         target_pullback := htgt' } :
        ({ base := S.base
           source := S.scheme
           target := V
           morphism := g
           sourceToBase := S.toBase
           targetToBase := pV
           over_base := hgp
           source_flat := S.flat
           target_flat := hflat } : SchemeMorphismFamily.{u, u} Λ k) ⟶
          schemeMorphismFamilySpecialFiber f pX pY hf), ⟨Iso.refl _⟩⟩

/-- Let `f : X ⟶ Y` be a morphism of schemes over the residue field `k` such that the canonical
map `𝒪_Y ⟶ f_*𝒪_X` is an isomorphism and `R¹f_*𝒪_X` vanishes. Then the functor forgetting the
target of a deformation of `f` is an equivalence from the deformation category of `f` to the
deformation category of `X`. -/
@[stacks 0E3X]
theorem schemeMorphismSourceForgetful_isEquivalence_of_specialFibre
    (h0 : IsIso (C := Y.Modules) (Scheme.Modules.unitToPushforwardUnit f))
    (hR : IsZero (((Scheme.Modules.pushforward f).rightDerived 1).obj
      (SheafOfModules.unit X.ringCatSheaf))) :
    (schemeMorphismSourceForgetful f pX pY hf).IsEquivalence where
  faithful := schemeMorphismSourceForgetful_faithful_of_specialFibre f pX pY hf h0 hR
  full := schemeMorphismSourceForgetful_full_of_specialFibre f pX pY hf h0 hR
  essSurj := schemeMorphismSourceForgetful_essSurj_of_specialFibre f pX pY hf h0 hR

end SourceForgetful

end Deformation.Examples

end
