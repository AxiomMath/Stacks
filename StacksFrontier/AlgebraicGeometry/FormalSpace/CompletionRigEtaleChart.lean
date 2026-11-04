module

public import StacksFrontier.AlgebraicGeometry.FormalSpace.CompletionChartSquare
public import StacksFrontier.RingTheory.Rig.RigEtaleAdicCompletionAscent
public import StacksFrontier.RingTheory.Rig.RigEtaleArrowAlgebraization

/-!
# The map of adic completions of a finite type algebra étale off `V(I)` is rig-étale

Let `φ : A → A'` be a finite type homomorphism of Noetherian rings, `I ⊆ A` an ideal, and assume
`Spec A' → Spec A` étale over `Spec A ∖ V(I)`. Then the induced map `A^∧ → (A')^∧` of `I`-adic
completions, with their adic topologies, is a rig-étale arrow of `WAdm^{Noeth}` in the sense of
**Stacks 0GCV**.

This is the affine case of **Stacks 0AR2**: "By Lemma 0ALQ we see that `(A')^∧` is rig-étale over
`(A, I)` which in turn means that `A^∧ → (A')^∧` is rig-étale". Part (1) of Stacks 0ALQ is
`Rig.isRigEtale_adicCompletionObj_of_isEtaleOutside`, and the passage from rig-étaleness over
`(A, I)` to rig-étaleness over `(A^∧, IA^∧)` is
`Rig.isRigEtaleOver_adicCompletion_of_isRigEtaleOver`.

## Main results

* `AlgebraicGeometry.FormalSpace.isRigEtaleHom_adicCompletionMap_of_isEtaleOutside`: the affine
  case of Stacks 0AR2.

## References

* [Stacks Project, Tag 0ALQ](https://stacks.math.columbia.edu/tag/0ALQ)
* [Stacks Project, Tag 0AR2](https://stacks.math.columbia.edu/tag/0AR2)
* [Stacks Project, Tag 0GCV](https://stacks.math.columbia.edu/tag/0GCV)
-/

@[expose] public noncomputable section

universe u

namespace AlgebraicGeometry.FormalSpace

attribute [local instance] adicCompletionModuleTopology
  isTopologicalRing_adicCompletionModuleTopology isLinearTopology_adicCompletionModuleTopology

variable {A A' : Type u} [CommRing A] [CommRing A'] [IsNoetherianRing A] [IsNoetherianRing A']

/-- **The map of adic completions of a finite type algebra is adic of topologically finite type**
(condition (6) of Stacks 0GBW), as soon as its target is of finite type modulo the extension of
`IÂ` and complete for it. For a homomorphism `φ : A → A'` of Noetherian rings and an ideal `I ⊆ A`,
`IÂ` is an ideal of definition of `Â` whose extension to `(A')^∧` defines the `I A'`-adic topology;
condition (5) of Stacks 0GBW at `IÂ` is then the finite type hypothesis. -/
theorem finiteTypeAdicAlgebraForEveryIdeal_adicCompletionMap (φ : A →+* A') (I : Ideal A)
    (hc : letI : Algebra (AdicCompletion I A) (AdicCompletion (I.map φ) A') :=
        (adicCompletionMap φ I (I.map φ) le_rfl).toAlgebra
      IsAdicComplete ((I.map (algebraMap A (AdicCompletion I A))).map
        (algebraMap (AdicCompletion I A) (AdicCompletion (I.map φ) A')))
        (AdicCompletion (I.map φ) A'))
    (hf : letI : Algebra (AdicCompletion I A) (AdicCompletion (I.map φ) A') :=
        (adicCompletionMap φ I (I.map φ) le_rfl).toAlgebra
      Algebra.FiniteType (AdicCompletion I A ⧸ I.map (algebraMap A (AdicCompletion I A)))
        (AdicCompletion (I.map φ) A' ⧸ (I.map (algebraMap A (AdicCompletion I A))).map
          (algebraMap (AdicCompletion I A) (AdicCompletion (I.map φ) A')))) :
    Rig.FiniteTypeAdicAlgebraForEveryIdeal (adicCompletionMap φ I (I.map φ) le_rfl) := by
  set α := algebraMap A (AdicCompletion I A) with hα
  set g := adicCompletionMap φ I (I.map φ) le_rfl with hg
  have hI : I.FG := IsNoetherian.noetherian I
  have hI' : (I.map φ).FG := IsNoetherian.noetherian _
  have hdef : TopologicalRing.IsIdealOfDefinition (I.map α) :=
    isIdealOfDefinition_map_adicModuleTopology I hI
  have hmapeq : (I.map α).map g = (I.map φ).map (algebraMap A' (AdicCompletion (I.map φ) A')) := by
    rw [Ideal.map_map, Ideal.map_map, adicCompletionMap_comp_algebraMap]
  have hadic : _root_.IsAdic ((I.map α).map g) := by
    rw [hmapeq]
    exact isAdic_map_adicModuleTopology (I.map φ) hI'
  have hAadic : TopologicalRing.IsAdic (AdicCompletion I A) :=
    isAdic_adicModuleTopology I hI
  have hA'adic : TopologicalRing.IsAdic (AdicCompletion (I.map φ) A') :=
    isAdic_adicModuleTopology (I.map φ) hI'
  have hcont : Continuous g := continuous_adicCompletionMap φ I (I.map φ) le_rfl
  have hf2 : (Ideal.quotientMap ((I.map α).map g) g Ideal.le_comap_map).FiniteType := by
    let : Algebra (AdicCompletion I A) (AdicCompletion (I.map φ) A') := g.toAlgebra
    have h := RingHom.finiteType_algebraMap.mpr hf
    have heq : Ideal.quotientMap ((I.map α).map g) g Ideal.le_comap_map =
        algebraMap (AdicCompletion I A ⧸ I.map α)
          (AdicCompletion (I.map φ) A' ⧸ (I.map α).map (algebraMap _ _)) :=
      Ideal.Quotient.ringHom_ext (RingHom.ext fun _ ↦ rfl)
    rw [heq]
    exact h
  have h5 : Rig.FiniteTypeAdicAlgebraForSomeIdeal g := ⟨I.map α, hdef, hadic, hc, hf2⟩
  exact ((Rig.adicFiniteType_tfae g hcont hAadic hA'adic
    (Rig.exists_idealOfDefinition_fg hAadic inferInstance)
    (Rig.exists_idealOfDefinition_fg hA'adic inferInstance)).out 5 6).mp h5

/-- **The affine case of Stacks 0AR2.** For a finite type homomorphism `φ : A → A'` of Noetherian
rings and an ideal `I ⊆ A` such that `Spec A' → Spec A` is étale over `Spec A ∖ V(I)`, the induced
map of `I`-adic completions `A^∧ → (A')^∧` is a rig-étale arrow of `WAdm^{Noeth}`. -/
theorem isRigEtaleHom_adicCompletionMap_of_isEtaleOutside (φ : A →+* A') (I : Ideal A)
    (hft : φ.FiniteType)
    (hφ : letI : Algebra A A' := φ.toAlgebra; Rig.IsEtaleOutside I A') :
    TopologicalRing.IsRigEtaleHom (adicCompletionMap φ I (I.map φ) le_rfl) := by
  intro _ _ _ _
  let : Algebra A A' := φ.toAlgebra
  have : Algebra.FiniteType A A' := hft
  set α := algebraMap A (AdicCompletion I A) with hα
  set g := adicCompletionMap φ I (I.map φ) le_rfl with hg
  -- rig-étaleness over the non-complete base, by part (1) of Stacks 0ALQ
  have h0 := Rig.isRigEtale_adicCompletionObj_of_isEtaleOutside I (B := A') hφ
  have hcomp : g.comp α = algebraMap A (Rig.adicCompletionObj I (B := A')).carrier := by
    rw [hg, adicCompletionMap_comp_algebraMap]
    rfl
  have hover : Rig.IsRigEtaleOver (g.comp α) I := by
    rw [hcomp]
    exact ⟨(Rig.adicCompletionObj I (B := A')).isAdicallyComplete,
      (Rig.adicCompletionObj I (B := A')).property.2, h0⟩
  have hover' := Rig.isRigEtaleOver_adicCompletion_of_isRigEtaleOver g hover
  -- the finite type data, for the ideal of definition `IA^∧`
  obtain ⟨hc, hf, -⟩ := id hover'
  have hft' := finiteTypeAdicAlgebraForEveryIdeal_adicCompletionMap φ I hc hf
  exact ⟨continuous_adicCompletionMap φ I (I.map φ) le_rfl, hft', I.map α,
    isIdealOfDefinition_map_adicModuleTopology I (IsNoetherian.noetherian I), hover'⟩

end AlgebraicGeometry.FormalSpace

end
