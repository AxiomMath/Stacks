module

public import StacksFrontier.AlgebraicGeometry.FormalSpace.AffineRigEtaleAlgebraization
public import StacksFrontier.AlgebraicGeometry.FormalSpace.RepresentableFormalSpectrumTaut
public import StacksFrontier.AlgebraicGeometry.FormalSpace.RigEtaleLocalCharacterization
public import StacksFrontier.AlgebraicGeometry.FormalSpace.RigSurjectiveClosedImmersionCharts
public import StacksFrontier.AlgebraicGeometry.FormalSpace.RigSurjectiveFaithfullyFlat
public import StacksFrontier.AlgebraicGeometry.FormalSpace.SpectrumFullyFaithful
public import StacksFrontier.AlgebraicGeometry.FormalSpace.TautStageBaseChange
public import StacksFrontier.Topology.Algebra.AdicTopology.CompletedTensorProduct.QuotientSurjection
import StacksFrontier.RingTheory.AdicCompletion.NoetherianRing
import StacksCore.Tactic.EgaSgaAttribute

/-!
# Morphisms from the completion of an affine scheme to a formal spectrum

Let `S` be a scheme contained in a big fppf site `B`, let `V = Spec R` be a Noetherian affine
scheme of the site and `I ⊆ R` an ideal. By Stacks 0GBA (2) the completion `V_{/V(I)}` is the
formal spectrum of the `I`-adic completion `R^∧`, presented by
`AlgebraicGeometry.FormalSpace.adicQuotientSystem`. A morphism `G : V_{/V(I)} ⟶ Spf C₀` to the
formal spectrum of an adic ring which is representable by algebraic spaces is therefore, by
Stacks 0AN0, the formal spectrum map of a continuous homomorphism `C₀ → R^∧` over `S`, and that
homomorphism is taut.

## Main results

* `AlgebraicGeometry.FormalSpace.adicCompletion_closure_eq`: with its `I`-adic topology, every
  ideal of the completion of a Noetherian ring is closed.
* `AlgebraicGeometry.FormalSpace.exists_continuousHom_completionComparison`: the statement
  above.

## References

* [Stacks Project, Tag 0GBA](https://stacks.math.columbia.edu/tag/0GBA)
* [Stacks Project, Tag 0AN0](https://stacks.math.columbia.edu/tag/0AN0)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits Opposite

universe u

namespace AlgebraicGeometry.FormalSpace

/-! ### The adic topology on a completion -/

section AdicTopology

/-- With its `I`-adic module topology, the `I`-adic completion of `A` for a finitely generated
`I` is an adic, weakly admissible, linearly topologized topological ring, its topology being the
`IA^∧`-adic one. -/
private theorem adicCompletion_isAdic_of_isNoetherianRing {A : Type u} [CommRing A]
    [IsNoetherianRing A] (I : Ideal A) :
    letI : TopologicalSpace (AdicCompletion I A) := I.adicModuleTopology (AdicCompletion I A)
    ∃ (_ : IsTopologicalRing (AdicCompletion I A))
      (_ : IsLinearTopology (AdicCompletion I A) (AdicCompletion I A)),
      _root_.IsAdic (I.map (algebraMap A (AdicCompletion I A))) ∧
        TopologicalRing.IsAdic (AdicCompletion I A) ∧
          TopologicalRing.IsWeaklyAdmissible (AdicCompletion I A) := by
  have hI : I.FG := I.fg_of_isNoetherianRing
  have hmod : I.adicModuleTopology (AdicCompletion I A) =
      (I.map (algebraMap A (AdicCompletion I A))).adicTopology := by
    let : TopologicalSpace A := I.adicTopology
    apply IsTopologicalAddGroup.ext
    · infer_instance
    · infer_instance
    ext U
    rw [(I.ringFilterBasis.moduleFilterBasis
      (I.adic_module_basis (AdicCompletion I A))).toAddGroupFilterBasis.nhds_zero_hasBasis.mem_iff,
      (I.map (algebraMap A (AdicCompletion I A))).hasBasis_nhds_zero_adic.mem_iff]
    constructor
    · rintro ⟨-, ⟨n, rfl⟩, hn⟩
      refine ⟨n, trivial, ?_⟩
      simpa [Ideal.smul_top_eq_map, Ideal.map_pow] using hn
    · rintro ⟨n, -, hn⟩
      refine ⟨_, ⟨n, rfl⟩, ?_⟩
      simpa [Ideal.smul_top_eq_map, Ideal.map_pow] using hn
  rw [hmod]
  let J := I.map (algebraMap A (AdicCompletion I A))
  let : TopologicalSpace (AdicCompletion I A) := J.adicTopology
  have hJ : _root_.IsAdic J := rfl
  let : IsLinearTopology (AdicCompletion I A) (AdicCompletion I A) := J.isLinearTopology
  let : UniformSpace (AdicCompletion I A) := IsTopologicalAddGroup.rightUniformSpace _
  let : IsUniformAddGroup (AdicCompletion I A) := isUniformAddGroup_of_addCommGroup
  have hc := hJ.isAdicComplete_iff.mp (AdicCompletion.isAdicComplete_self I hI)
  exact ⟨inferInstance, inferInstance, hJ,
    ⟨⟨J, TopologicalRing.isIdealOfDefinition_of_isAdic hJ, hJ⟩, hc.2, hc.1⟩,
    TopologicalRing.isWeaklyAdmissible_of_isAdic hJ (AdicCompletion.isAdicComplete_self I hI)⟩

/-- The `I`-adic completion is a topological ring for its `I`-adic module topology. -/
theorem adicCompletion_isTopologicalRing {A : Type u} [CommRing A] [IsNoetherianRing A]
    (I : Ideal A) :
    letI : TopologicalSpace (AdicCompletion I A) := I.adicModuleTopology (AdicCompletion I A)
    IsTopologicalRing (AdicCompletion I A) :=
  (adicCompletion_isAdic_of_isNoetherianRing I).fst

/-- The `I`-adic topology of the `I`-adic completion is linear. -/
theorem adicCompletion_isLinearTopology {A : Type u} [CommRing A] [IsNoetherianRing A]
    (I : Ideal A) :
    letI : TopologicalSpace (AdicCompletion I A) := I.adicModuleTopology (AdicCompletion I A)
    IsLinearTopology (AdicCompletion I A) (AdicCompletion I A) :=
  (adicCompletion_isAdic_of_isNoetherianRing I).snd.fst

/-- In the `I`-adic completion of a Noetherian ring, with its `I`-adic topology, every ideal is
closed. -/
@[sga "3 VIIB 5.5.2" "partial"]
theorem adicCompletion_closure_eq {A : Type u} [CommRing A] [IsNoetherianRing A] (I : Ideal A)
    (𝔞 : Ideal (AdicCompletion I A)) :
    letI : TopologicalSpace (AdicCompletion I A) := I.adicModuleTopology (AdicCompletion I A)
    haveI := adicCompletion_isTopologicalRing I
    𝔞.closure = 𝔞 := by
  let : TopologicalSpace (AdicCompletion I A) := I.adicModuleTopology (AdicCompletion I A)
  have := adicCompletion_isTopologicalRing I
  obtain ⟨_, _, hJ, ⟨-, hT2, hcomp⟩, -⟩ := adicCompletion_isAdic_of_isNoetherianRing I
  let : UniformSpace (AdicCompletion I A) := IsTopologicalAddGroup.rightUniformSpace _
  have : IsUniformAddGroup (AdicCompletion I A) := isUniformAddGroup_of_addCommGroup
  have : CompleteSpace (AdicCompletion I A) := hcomp
  have : T2Space (AdicCompletion I A) := hT2
  have : IsNoetherianRing (AdicCompletion I A) := Stacks.AdicCompletion.NoetherianRing.solution I
  exact Ideal.closure_eq_of_isAdic_of_isNoetherianRing hJ 𝔞

end AdicTopology

/-! ### The dictionary -/

variable (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)

/-- **A representable morphism from the completion of a Noetherian affine scheme to a formal
spectrum is the formal spectrum map of a taut continuous homomorphism.** For `V = Spec R` and
`G : V_{/V(I)} ⟶ Spf C₀` representable by algebraic spaces, with `C₀` adic, there is a continuous
homomorphism `φ : C₀ → R^∧` over `S`, taut, with `Spf φ` equal to `G` precomposed with the
comparison isomorphism `Spf (R^∧) ≅ V_{/V(I)}` of Stacks 0GBA (2). -/
theorem exists_continuousHom_completionComparison {R : Type u} [CommRing R] [IsNoetherianRing R]
    (hR : B.Contains (Spec (.of R))) (s : Spec (.of R) ⟶ S) (I : Ideal R)
    {C₀ : Type u} [CommRing C₀] [TopologicalSpace C₀] [IsTopologicalRing C₀]
    [IsLinearTopology C₀ C₀] (hC₀ : TopologicalRing.IsAdic C₀) (E : QuotientSystem B S hS C₀)
    (G : Space.completionSheaf B S hS (yoneda.obj (affineOver B S hS hR s))
      (zeroLocusPoints B S hS hR s I) ⟶ formalSpectrum E)
    (hG : Space.IsRepresentableByAlgebraicSpacesULift.{u + 1} B S hS G.hom) :
    letI : TopologicalSpace (AdicCompletion I R) := I.adicModuleTopology (AdicCompletion I R)
    haveI := adicCompletion_isTopologicalRing I
    haveI := adicCompletion_isLinearTopology I
    ∃ φ : ContinuousHom E (adicQuotientSystem B S hS hR s I I.fg_of_isNoetherianRing),
      RingHom.IsTaut φ.toRingHom ∧
      ∃ _hwA : TopologicalRing.IsWeaklyAdmissible (AdicCompletion I R),
      formalSpectrumMap hC₀.isWeaklyAdmissible φ =
        completionComparison B S hS hR s I
          (adicQuotientSystem B S hS hR s I I.fg_of_isNoetherianRing)
          (quotientSystemCompatible_adicQuotientSystem B S hS hR s I I.fg_of_isNoetherianRing) ≫
          G := by
  let : TopologicalSpace (AdicCompletion I R) := I.adicModuleTopology (AdicCompletion I R)
  have hI : I.FG := I.fg_of_isNoetherianRing
  have := adicCompletion_isTopologicalRing I
  have := adicCompletion_isLinearTopology I
  obtain ⟨_, _, _, haA, hwA⟩ := adicCompletion_isAdic_of_isNoetherianRing I
  let D := adicQuotientSystem B S hS hR s I hI
  have := isIso_completionComparison_adicQuotientSystem B S hS hR s I hI
  let cmp := completionComparison B S hS hR s I D
    (quotientSystemCompatible_adicQuotientSystem B S hS hR s I hI)
  obtain ⟨φ, hφ, -⟩ :=
    existsUnique_continuousHom_formalSpectrumMap_eq hC₀.isWeaklyAdmissible hwA (cmp ≫ G)
  refine ⟨φ, ?_, hwA, hφ⟩
  have hrep : Space.IsRepresentableByAlgebraicSpacesULift.{u + 1} B S hS
      (formalSpectrumMap hC₀.isWeaklyAdmissible φ).hom := by
    rw [hφ]
    refine Space.isRepresentableByAlgebraicSpacesULift_of_isPullback B S hS cmp.hom
      (cmp ≫ G).hom G.hom (𝟙 _) ?_ hG
    have : IsIso cmp.hom := inferInstanceAs (IsIso ((sheafToPresheaf _ _).map cmp))
    exact IsPullback.of_horiz_isIso ⟨by simp⟩
  exact isTaut_of_isRepresentableByAlgebraicSpacesULift_formalSpectrumMap B S hS
    hC₀.isWeaklyAdmissible hwA E D
    (hasLargeSite_of_mk_lt_cutoff E (mk_lt_cutoff_of_quotientSystem_of_isAdic B S hS hC₀ E))
    (hasLargeSite_of_mk_lt_cutoff D (mk_lt_cutoff_of_quotientSystem_of_isAdic B S hS haA D))
    φ hrep

end AlgebraicGeometry.FormalSpace
