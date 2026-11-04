module

public import StacksFrontier.AlgebraicGeometry.FormalSpace.FiniteTypeRefined
public import StacksFrontier.AlgebraicGeometry.FormalSpace.SpectrumFiniteType
public import StacksFrontier.AlgebraicGeometry.FormalSpace.TautRepresentability
public import StacksFrontier.Topology.Algebra.AdicTopology.FiniteTypeRefined

/-!
# Finite type morphisms of formal spectra: the stage quotients

## Main results

* `finiteType_quotientMap_of_isLocallyOfFiniteType_formalSpectrumMap`: for a taut continuous
  homomorphism `φ : A → C` of weakly admissible topological rings with `Spf (φ)` locally of
  finite type, the induced map `A ⧸ I → C ⧸ J(I)` is of finite type for every weak ideal of
  definition `I`.
-/
@[expose] public section

open CategoryTheory CategoryTheory.Limits

namespace TopologicalRing

section Algebra

universe u v

variable {A : Type u} [CommRing A] [TopologicalSpace A]
  {B : Type v} [CommRing B] [TopologicalSpace B] [IsTopologicalRing B]

end Algebra

end TopologicalRing

namespace AlgebraicGeometry.FormalSpace

section Geometry

universe u

variable (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)

variable {B S hS}
variable {A C : Type u} [CommRing A] [TopologicalSpace A] [IsTopologicalRing A]
  [IsLinearTopology A A] [CommRing C] [TopologicalSpace C] [IsTopologicalRing C]
  [IsLinearTopology C C]

/-- Let `φ : A ⟶ C` be a taut continuous homomorphism of weakly admissible topological rings over
`S`. If `Spf (φ)` is locally of finite type, then for every weak ideal of definition `I` of `A` the
induced ring map `A ⧸ I → C ⧸ J(I)`, with `J(I)` the closure of `φ(I)C`, is of finite type. -/
theorem finiteType_quotientMap_of_isLocallyOfFiniteType_formalSpectrumMap
    (hA : TopologicalRing.IsWeaklyAdmissible A) (hC : TopologicalRing.IsWeaklyAdmissible C)
    (D : QuotientSystem B S hS A) (E : QuotientSystem B S hS C) (f : ContinuousHom D E)
    (hf : RingHom.IsTaut f.toRingHom)
    (hFT : IsLocallyOfFiniteType B S hS (formalSpectrumMap hA f))
    (I : Ideal A) (hI : TopologicalRing.IsWeakIdealOfDefinition I) :
    (Ideal.quotientMap (Ideal.closure (I.map f.toRingHom)) f.toRingHom
      (Ideal.map_le_iff_le_comap.mp subset_closure)).FiniteType := by
  obtain ⟨hrep, hprop⟩ := hFT
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

end Geometry

end AlgebraicGeometry.FormalSpace

end
