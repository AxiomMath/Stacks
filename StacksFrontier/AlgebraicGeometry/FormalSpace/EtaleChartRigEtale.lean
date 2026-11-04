module

public import Mathlib.AlgebraicGeometry.Morphisms.Etale
public import StacksCore.Tactic.StacksAttribute
public import StacksFrontier.AlgebraicGeometry.FormalSpace.LocalProperty
public import StacksFrontier.AlgebraicGeometry.FormalSpace.SpectrumFiniteType
public import StacksFrontier.RingTheory.NaiveCotangent.PresentationHomology
public import StacksFrontier.RingTheory.Rig.RigEtaleLifting
public import StacksFrontier.RingTheory.Rig.RigEtaleLocality
public import StacksFrontier.RingTheory.Rig.RigEtaleTFAE
public import StacksFrontier.RingTheory.Rig.RigSmoothTower
public import StacksFrontier.Topology.Algebra.AdicTopology.CompletionQuotient
public import StacksFrontier.Topology.Algebra.AdicTopology.NoetherianNilradical

/-!
# The chart homomorphism of a representable étale map is rig-étale

Let `φ : A ⟶ C` be a continuous homomorphism of adic Noetherian topological rings. If `φ` is
taut and the ring maps `A ⧸ I → C ⧸ IC` it induces on the quotients by the weak ideals of
definition `I` of `A` are étale, then `φ` is rig-étale (Definition 0GCV): it is adic of
topologically finite type, and condition (4) of Stacks 0AJU holds with exponent `0`, the naive
cotangent complexes of the étale ring maps `A ⧸ Iⁿ → C ⧸ IⁿC` having no homology at all.

Over a site of the big fppf topology, both hypotheses hold as soon as `Spf φ` is representable
by algebraic spaces and étale: tautness is the implication (1) ⟹ (3) of Stacks 0AN5, and
étaleness of the quotient maps is read off the cartesian square formed by `Spf φ` and the
stages `Spec (A ⧸ I)`, `Spec (C ⧸ IC)` of the two formal spectra.

## Main results

* `Rig.isRigEtale_of_etale_quotientMap`: the ring statement above.
* `AlgebraicGeometry.FormalSpace.etale_quotientMap_of_isRepresentableEtale_formalSpectrumMap`:
  the stage maps of a taut homomorphism whose formal spectrum map is representable étale are
  étale.

## References

* [Stacks Project, Tag 0AJU](https://stacks.math.columbia.edu/tag/0AJU)
* [Stacks Project, Tag 0AN5](https://stacks.math.columbia.edu/tag/0AN5)
* [Stacks Project, Tag 0GBW](https://stacks.math.columbia.edu/tag/0GBW)
* [Stacks Project, Tag 0GCV](https://stacks.math.columbia.edu/tag/0GCV)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits

universe u

namespace Rig

/-- The naive cotangent complex of an étale algebra has no homology. -/
theorem subsingleton_homology_naiveCotangentComplex_of_etale {R S : Type u} [CommRing R]
    [CommRing S] [Algebra R S] [Algebra.Etale R S] :
    Subsingleton ((Algebra.naiveCotangentComplex R S).homology 1) ∧
      Subsingleton ((Algebra.naiveCotangentComplex R S).homology 0) := by
  let P := Algebra.Generators.self R S
  have : Subsingleton (LinearMap.ker P.toExtension.cotangentComplex) :=
    (P.equivH1Cotangent.trans (Algebra.Extension.h1CotangentEquivKer _)).symm.subsingleton
  have : Subsingleton
      (P.toExtension.CotangentSpace ⧸ LinearMap.range P.toExtension.cotangentComplex) :=
    (Algebra.Extension.quotRangeCotangentComplexEquivKaehler P.toExtension).subsingleton
  exact ⟨(NaiveCotangent.naiveCotangentComplexHomologyOneEquiv P).subsingleton,
    (NaiveCotangent.naiveCotangentComplexHomologyZeroEquiv P).subsingleton⟩

variable {A C : Type u}
  [CommRing A] [TopologicalSpace A] [IsTopologicalRing A] [IsLinearTopology A A]
    [IsNoetherianRing A]
  [CommRing C] [TopologicalSpace C] [IsTopologicalRing C] [IsLinearTopology C C]
    [IsNoetherianRing C]

/-- **A taut homomorphism of adic Noetherian rings which is étale on all quotient stages is
rig-étale.** Let `φ : A → C` be a continuous taut homomorphism of adic Noetherian topological
rings such that for every weak ideal of definition `I` of `A` the induced ring map
`A ⧸ I → C ⧸ J(I)` is étale, `J(I)` being the closure of `IC`. Then `φ` is rig-étale.

Every ideal of the adic Noetherian ring `C` is closed, so `J(I) = IC`. Tautness makes `φ` adic
(Stacks 0APU), and étaleness of the quotient map makes it of finite type, so `φ` is adic of
topologically finite type by Stacks 0GBW. Condition (4) of Stacks 0AJU then holds with exponent
`0`: for an ideal of definition `I` the maps `A ⧸ Iⁿ → C ⧸ IⁿC` are étale, so their naive
cotangent complexes have no homology. -/
theorem isRigEtale_of_etale_quotientMap (hA : TopologicalRing.IsAdic A)
    (hC : TopologicalRing.IsAdic C) (φ : A →+* C) (hφ : Continuous φ)
    (htaut : RingHom.IsTaut φ)
    (het : ∀ I : Ideal A, TopologicalRing.IsWeakIdealOfDefinition I →
      (Ideal.quotientMap (Ideal.closure (I.map φ)) φ
        (Ideal.map_le_iff_le_comap.mp subset_closure)).Etale) :
    RingHom.IsRigEtale φ := by
  have hcl : ∀ J : Ideal C, Ideal.closure J = J := by
    obtain ⟨⟨K, -, hKadic⟩, hT2, hCompl⟩ := hC
    let _ : UniformSpace C := IsTopologicalAddGroup.rightUniformSpace C
    have _ : IsUniformAddGroup C := isUniformAddGroup_of_addCommGroup
    have _ : CompleteSpace C := hCompl
    have _ : T2Space C := hT2
    exact fun J ↦ SetLike.coe_injective
      (TopologicalRing.isClosed_ideal_of_isAdic_of_isNoetherianRing hKadic J).closure_eq
  have het' (I : Ideal A) (hI : TopologicalRing.IsWeakIdealOfDefinition I) :
      (Ideal.quotientMap (I.map φ) φ Ideal.le_comap_map).Etale := by
    convert het I hI using 3 <;> exact (hcl _).symm
  obtain ⟨IA, hIA, hIAfg⟩ := exists_idealOfDefinition_fg hA inferInstance
  have hIAadic := idealOfDefinition_isAdic_of_isAdicRing hA IA hIA
  have hft : FiniteTypeAdicAlgebraForEveryIdeal φ := by
    have hT2 : T2Space C := hC.2.1
    have hCompl : @CompleteSpace C (IsTopologicalAddGroup.rightUniformSpace C) := hC.2.2
    obtain ⟨I, hIadic, hImap⟩ := RingHom.isAdic_of_isTaut φ hφ htaut ⟨IA, hIAfg, hIAadic⟩
    have hI : TopologicalRing.IsIdealOfDefinition I :=
      TopologicalRing.isIdealOfDefinition_of_isAdic hIadic
    have hIw : TopologicalRing.IsWeakIdealOfDefinition I := by
      simpa using TopologicalRing.isWeakIdealOfDefinition_pow_of_isAdic hIadic 0
    have h3 : FiniteTypeModuloSomeIdealOfDefinition φ := by
      refine ⟨⟨I, hI, hImap⟩, I, hI, ?_⟩
      let := (Ideal.quotientMap (I.map φ) φ Ideal.le_comap_map).toAlgebra
      have : Algebra.Etale (A ⧸ I) (C ⧸ I.map φ) := het' I hIw
      exact (inferInstance : Algebra.FiniteType (A ⧸ I) (C ⧸ I.map φ))
    exact ((adicFiniteType_tfae φ hφ hA hC ⟨IA, hIA, hIAfg⟩
      (exists_idealOfDefinition_fg hC inferInstance)).out 3 6).mp h3
  refine RingHom.isRigEtale_of_isRigEtaleOver hft IA hIA
    (isRigEtaleOver_of_isRigEtale φ hft IA hIA ?_)
  obtain ⟨P⟩ := nonempty_completedPolynomialPresentation hIAfg (adicFiniteTypeAlgebra φ hft IA hIA)
  refine ((tfae_isRigEtale (adicFiniteTypeAlgebra φ hft IA hIA) P).out 4 1).mp ?_
  refine ⟨0, fun n hn a _ ↦ ?_⟩
  obtain ⟨m, rfl⟩ : ∃ m, n = m + 1 := ⟨n - 1, by omega⟩
  have hE : Algebra.Etale (A ⧸ IA ^ (m + 1))
      ((adicFiniteTypeAlgebra φ hft IA hIA).carrier ⧸
        (IA ^ (m + 1)).map (algebraMap A (adicFiniteTypeAlgebra φ hft IA hIA).carrier)) := by
    rw [← RingHom.etale_algebraMap]
    exact het' _ (TopologicalRing.isWeakIdealOfDefinition_pow_of_isAdic hIAadic m)
  obtain ⟨h1, h0⟩ := subsingleton_homology_naiveCotangentComplex_of_etale
    (R := A ⧸ IA ^ (m + 1)) (S := (adicFiniteTypeAlgebra φ hft IA hIA).carrier ⧸
        (IA ^ (m + 1)).map (algebraMap A (adicFiniteTypeAlgebra φ hft IA hIA).carrier))
  constructor <;> exact Module.mem_annihilator.mpr fun _ ↦ Subsingleton.elim _ _

end Rig

namespace AlgebraicGeometry.FormalSpace

variable {B : BigFppfSite.{u}} {S : Scheme.{u}} {hS : B.Contains S}
variable {A C : Type u} [CommRing A] [TopologicalSpace A] [IsTopologicalRing A]
  [IsLinearTopology A A] [CommRing C] [TopologicalSpace C] [IsTopologicalRing C]
  [IsLinearTopology C C]

/-- **The stage maps of a representable étale map of formal spectra are étale.** Let
`φ : A ⟶ C` be a taut continuous homomorphism of weakly admissible topological rings over `S`
whose formal spectrum map `Spf φ` is representable by algebraic spaces and étale. Then for every
weak ideal of definition `I` of `A` the ring map `A ⧸ I → C ⧸ J(I)`, `J(I)` the closure of
`φ(I)C`, is étale.

Tautness makes the square formed by the two stages and `Spf φ` cartesian, so the stage map is a
base change of `Spf φ` along a scheme-valued point and is étale; it is a morphism of affine
schemes, so this is étaleness of the ring map. This is the étale analogue of the stage half of
Stacks 0GCG. -/
theorem etale_quotientMap_of_isRepresentableEtale_formalSpectrumMap
    (hA : TopologicalRing.IsWeaklyAdmissible A) (hC : TopologicalRing.IsWeaklyAdmissible C)
    (D : QuotientSystem B S hS A) (E : QuotientSystem B S hS C) (f : ContinuousHom D E)
    (hf : RingHom.IsTaut f.toRingHom)
    (het : IsRepresentableEtale B S hS (formalSpectrumMap hA f))
    (I : Ideal A) (hI : TopologicalRing.IsWeakIdealOfDefinition I) :
    (Ideal.quotientMap (Ideal.closure (I.map f.toRingHom)) f.toRingHom
      (Ideal.map_le_iff_le_comap.mp subset_closure)).Etale := by
  obtain ⟨_, hprop⟩ := het
  obtain ⟨⟨Kv, hKw⟩, rfl, hIK, hsq⟩ :=
    isPullback_formalSpectrumMap_stage_of_isTaut B S hS hA hC D E f hf ⟨I, hI⟩
  set G := sheafToPresheaf (BigFppfOver.topology B S hS) (Type (u + 1))
  set k := (BigAffineFppf.inclusion B S hS).map
    (f.stageMap ⟨I, hI⟩ ⟨Ideal.closure (I.map f.toRingHom), hKw⟩ hIK)
  have hleft : IsPullback (sheafifiedYonedaObjIso B S hS _).hom ((uliftYoneda.{u + 1}).map k)
      (G.map ((Sheaf.sheafifiedYoneda (BigFppfOver.topology B S hS)).map k))
      (sheafifiedYonedaObjIso B S hS _).hom :=
    IsPullback.of_horiz_isIso ⟨(sheafifiedYonedaObjIso_naturality B S hS k).symm⟩
  have hpaste := hleft.paste_horiz (hsq.map G)
  have het2 : Space.IsEtaleULift.{u + 1} B S hS ((uliftYoneda.{u + 1}).map k) := by
    rw [← hpaste.flip.isoPullback_hom_fst]
    exact isEtaleULift_precomp_iso B S hS hpaste.flip.isoPullback _ (hprop _ _)
  exact HasRingHomProperty.Spec_iff.mp
    (show AlgebraicGeometry.Etale (Spec.map (CommRingCat.ofHom
      (Ideal.quotientMap (Ideal.closure (I.map f.toRingHom)) f.toRingHom hIK))) from
      (Space.isEtaleULift_uliftYoneda_map_iff B S hS k).mp het2)

end AlgebraicGeometry.FormalSpace

end
