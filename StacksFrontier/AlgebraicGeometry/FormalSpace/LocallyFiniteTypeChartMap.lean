module

public import StacksFrontier.AlgebraicGeometry.FormalSpace.RepresentableFormalSpectrumTaut
public import StacksFrontier.AlgebraicGeometry.FormalSpace.SpectrumFiniteType
public import StacksFrontier.RingTheory.Rig.FiniteType

/-!
# The chart homomorphism of a morphism locally of finite type

Let `S` be a scheme contained in a big fppf site `B` and let `φ : A ⟶ C` be a continuous
homomorphism of Noetherian adic topological rings over `S` whose formal spectra are affine formal
algebraic spaces. If `Spf φ : Spf C ⟶ Spf A` is locally of finite type, then `φ` is adic and
topologically of finite type, in the form `Rig.FiniteTypeAdicAlgebraForEveryIdeal φ` of
condition (6) of Stacks 0GBW.

## Main results

* `FormalSpace.finiteType_quotientMap_of_isLocallyOfFiniteType_formalSpectrumMap`: the stage half
  of the implication (1) ⟹ (2) of Stacks 0ANT for a formal spectrum map which is only locally of
  finite type.
* `FormalSpace.finiteTypeAdicAlgebraForEveryIdeal_of_isLocallyOfFiniteType`: the statement above.

## Implementation notes

Tautness of `φ` is the implication (1) ⟹ (3) of Stacks 0AN5 for affine formal spectra,
`isTaut_of_isRepresentableByAlgebraicSpacesULift_formalSpectrumMap_of_isAffine`, applied to the
representability that local finite type includes. For a taut `φ` each stage of `Spf φ` over a
quotient stage `Spec (A ⧸ I)` is the morphism `Spec (C ⧸ J(I)) ⟶ Spec (A ⧸ I)` with `J(I)` the
closure of `φ(I) C`, which is a base change of `Spf φ` and hence locally of finite type; this is
the argument of `finiteType_quotientMap_of_isFiniteType_formalSpectrumMap`, which reads only the
local finite type half of its hypothesis. Then Stacks 0ANT and Stacks 0GBW conclude.

## References

* [Stacks Project, Tag 0AN5](https://stacks.math.columbia.edu/tag/0AN5)
* [Stacks Project, Tag 0ANT](https://stacks.math.columbia.edu/tag/0ANT)
* [Stacks Project, Tag 0GBW](https://stacks.math.columbia.edu/tag/0GBW)
* [Stacks Project, Tag 0GC0](https://stacks.math.columbia.edu/tag/0GC0)
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits

namespace AlgebraicGeometry.FormalSpace

universe u

variable {B : BigFppfSite.{u}} {S : Scheme.{u}} {hS : B.Contains S}
  {A C : Type u} [CommRing A] [TopologicalSpace A] [IsTopologicalRing A]
  [IsLinearTopology A A] [CommRing C] [TopologicalSpace C] [IsTopologicalRing C]
  [IsLinearTopology C C]

/-- **Stacks 0ANT, the stage half of (1) ⟹ (2), for a morphism locally of finite type.** Let
`φ : A ⟶ C` be a taut continuous homomorphism of weakly admissible topological rings over `S`.
If `Spf (φ)` is locally of finite type, then for every weak ideal of definition `I` of `A` the
induced ring map `A ⧸ I → C ⧸ J(I)`, with `J(I)` the closure of `φ(I)C`, is of finite type. -/
theorem finiteType_quotientMap_of_isLocallyOfFiniteType_formalSpectrumMap
    (hA : TopologicalRing.IsWeaklyAdmissible A) (hC : TopologicalRing.IsWeaklyAdmissible C)
    (D : QuotientSystem B S hS A) (E : QuotientSystem B S hS C) (f : ContinuousHom D E)
    (hf : RingHom.IsTaut f.toRingHom)
    (hLFT : IsLocallyOfFiniteType B S hS (formalSpectrumMap hA f))
    (I : Ideal A) (hI : TopologicalRing.IsWeakIdealOfDefinition I) :
    (Ideal.quotientMap (Ideal.closure (I.map f.toRingHom)) f.toRingHom
      (Ideal.map_le_iff_le_comap.mp subset_closure)).FiniteType := by
  obtain ⟨hrep, hprop⟩ := hLFT
  obtain ⟨⟨Kv, hKw⟩, hKeq, hIK, hsq⟩ :=
    isPullback_formalSpectrumMap_stage_of_isTaut B S hS hA hC D E f hf ⟨I, hI⟩
  subst hKeq
  set G := sheafToPresheaf (BigFppfOver.topology B S hS) (Type (u + 1)) with hG
  set k := (BigAffineFppf.inclusion B S hS).map
    (f.stageMap ⟨I, hI⟩ ⟨Ideal.closure (I.map f.toRingHom), hKw⟩ hIK) with hk
  have hright := hsq.map G
  have hleft : IsPullback (sheafifiedYonedaObjIso B S hS _).hom ((uliftYoneda.{u + 1}).map k)
      (G.map ((Sheaf.sheafifiedYoneda (BigFppfOver.topology B S hS)).map k))
      (sheafifiedYonedaObjIso B S hS _).hom :=
    IsPullback.of_horiz_isIso ⟨(sheafifiedYonedaObjIso_naturality B S hS k).symm⟩
  have hpaste := hleft.paste_horiz hright
  have hlft : Space.IsLocallyOfFiniteTypeULift.{u + 1} B S hS
      (pullback.fst ((sheafifiedYonedaObjIso B S hS
          ((BigAffineFppf.inclusion B S hS).obj (D.stage ⟨I, hI⟩))).hom ≫
        G.map (formalSpectrumInclusion D ⟨I, hI⟩)) (G.map (formalSpectrumMap hA f))) :=
    hprop _ _
  have hchart := Space.holdsOnEveryEtaleChartULift_precomp B S hS
    (@AlgebraicGeometry.LocallyOfFiniteType.{u}) hpaste.flip.isoPullback.hom _ hlft
  have hchart' : Space.HoldsOnEveryEtaleChartULift.{u + 1} B S hS
      (@AlgebraicGeometry.LocallyOfFiniteType.{u}) ((uliftYoneda.{u + 1}).map k) := by
    rw [← hpaste.flip.isoPullback_hom_fst]
    exact hchart
  have hk' := prop_of_holdsOnEveryEtaleChartULift B S hS k hchart'
  rw [hk] at hk'
  exact AlgebraicGeometry.HasRingHomProperty.Spec_iff.mp
    (show AlgebraicGeometry.LocallyOfFiniteType (Spec.map (CommRingCat.ofHom
      (Ideal.quotientMap (Ideal.closure (I.map f.toRingHom)) f.toRingHom hIK))) from hk')

/-- **The chart homomorphism of a morphism locally of finite type is adic and topologically of
finite type.** Let `φ : A ⟶ C` be a continuous homomorphism of Noetherian adic topological rings
over `S` whose formal spectra are affine formal algebraic spaces over `S`. If `Spf (φ)` is
locally of finite type then `φ` satisfies condition (6) of Stacks 0GBW: for every ideal of
definition `I` of `A`, the ideal `I C` defines the topology of `C`, `C` is `I C`-adically
complete and `C ⧸ I C` is of finite type over `A ⧸ I`.

This is the implication from condition (4) to condition (1) of Stacks 0GC0 read on a single
chart square, with nothing assumed beyond the chart: tautness comes from Stacks 0AN5 and finite
type modulo the weak ideals of definition from the stages of `Spf (φ)`. -/
theorem finiteTypeAdicAlgebraForEveryIdeal_of_isLocallyOfFiniteType
    [IsNoetherianRing A] [IsNoetherianRing C]
    (hA : TopologicalRing.IsAdic A) (hC : TopologicalRing.IsAdic C)
    (D : QuotientSystem B S hS A) (E : QuotientSystem B S hS C)
    (hDaff : IsAffineFormalAlgebraicSpace B S hS (formalSpectrum D))
    (hEaff : IsAffineFormalAlgebraicSpace B S hS (formalSpectrum E))
    (f : ContinuousHom D E)
    (hLFT : IsLocallyOfFiniteType B S hS
      (formalSpectrumMap (Rig.weaklyAdmissible_of_isAdicRing hA) f)) :
    Rig.FiniteTypeAdicAlgebraForEveryIdeal f.toRingHom := by
  have htaut : RingHom.IsTaut f.toRingHom :=
    isTaut_of_isRepresentableByAlgebraicSpacesULift_formalSpectrumMap_of_isAffine B S hS
      (Rig.weaklyAdmissible_of_isAdicRing hA) (Rig.weaklyAdmissible_of_isAdicRing hC) D E hDaff
      hEaff f
      hLFT.1
  have htft : TopologicalRing.IsTopologicallyOfFiniteType f.toRingHom :=
    TopologicalRing.isTopologicallyOfFiniteType_of_finiteTypeModuloEveryWeakIdeal
      f.toRingHom (Rig.weaklyAdmissible_of_isAdicRing hA).1 ⟨htaut, fun I hI ↦
        finiteType_quotientMap_of_isLocallyOfFiniteType_formalSpectrumMap
          (Rig.weaklyAdmissible_of_isAdicRing hA) (Rig.weaklyAdmissible_of_isAdicRing hC) D E f
          htaut hLFT I hI⟩
  obtain ⟨I, hI, -⟩ := hA.1
  obtain ⟨J, hJ, -⟩ := hC.1
  have h := Rig.adicFiniteType_tfae f.toRingHom f.continuous hA hC
    ⟨I, hI, Ideal.fg_of_isNoetherianRing I⟩ ⟨J, hJ, Ideal.fg_of_isNoetherianRing J⟩
  exact (h.out 2 6).mp
    (show RingHom.IsTaut f.toRingHom ∧ TopologicalRing.IsTopologicallyOfFiniteType f.toRingHom
      from ⟨htaut, htft⟩)

end AlgebraicGeometry.FormalSpace

end
