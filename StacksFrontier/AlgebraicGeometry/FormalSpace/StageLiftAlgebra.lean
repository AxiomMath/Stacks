module

public import StacksFrontier.AlgebraicGeometry.FormalSpace.StageBaseChangeModelPullback
public import StacksFrontier.RingTheory.Etale.Lifting

/-!
# The chosen étale lift of the stage model at a fixed weak ideal of definition

Let `R` be a topological ring presenting an affine formal algebraic space `Spf R` over `S`, let
`v : V ⟶ Spf R` be a morphism from an affine formal algebraic space which is representable by
algebraic spaces and étale, and let `J₀ ⊆ R` be a weak ideal of definition. The coordinate ring
`Ā_{J₀}` of the chosen affine model of `Spec (R ⧸ J₀) ×_{Spf R} V`
(`AlgebraicGeometry.FormalSpace.stageBaseChangeRing`) is an étale `R ⧸ J₀`-algebra. By **Stacks
04D1** it lifts to an étale `R`-algebra `A` with `A ⧸ J₀A ≅ Ā_{J₀}`; we choose such a lift.

## Main definitions

* `AlgebraicGeometry.FormalSpace.algebraStageBaseChangeRing`: the `R ⧸ J`-algebra structure on
  the coordinate ring of the chosen model given by
  `AlgebraicGeometry.FormalSpace.stageBaseChangeRingHom`.
* `AlgebraicGeometry.FormalSpace.stageLiftAlgebra`: the chosen étale `R`-algebra lifting
  `Ā_{J₀}`.
* `AlgebraicGeometry.FormalSpace.stageLiftAlgebraEquiv`: the identification
  `A ⧸ J₀A ≅ Ā_{J₀}`.

## Main results

* `AlgebraicGeometry.FormalSpace.etaleAlgebra_stageBaseChangeRing`: the stage model is étale
  over the stage, as an algebra.
* `AlgebraicGeometry.FormalSpace.exists_stageLiftAlgebra`: Stacks 04D1 applied to the stage
  model at `J₀`.
* `AlgebraicGeometry.FormalSpace.stageLiftAlgebraEquiv_comp_quotientMap`: the identification
  `A ⧸ J₀A ≅ Ā_{J₀}` commutes with the structure maps out of `R ⧸ J₀`.

## References

* [Stacks Project, Tag 0AN8](https://stacks.math.columbia.edu/tag/0AN8)
* [Stacks Project, Tag 04D1](https://stacks.math.columbia.edu/tag/04D1)
-/

@[expose] public section

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits

universe u

namespace AlgebraicGeometry.FormalSpace

attribute [local instance] sheaf_hasColimits

variable {𝔅 : BigFppfSite.{u}} {S : Scheme.{u}} {hS : 𝔅.Contains S}
  {R : Type u} [CommRing R] [TopologicalSpace R] (D : QuotientSystem 𝔅 S hS R)
  {V : FppfSheaf 𝔅 S hS} (v : V ⟶ formalSpectrum D)
  (hY : IsAffineFormalAlgebraicSpace 𝔅 S hS (formalSpectrum D))
  (hV : IsAffineFormalAlgebraicSpace 𝔅 S hS V) (hv : IsRepresentableEtale 𝔅 S hS v)

/-- The coordinate ring of the chosen affine model of `Spec (R ⧸ J) ×_{Spf R} V` as an
`R ⧸ J`-algebra, through the ring map
`AlgebraicGeometry.FormalSpace.stageBaseChangeRingHom`. -/
noncomputable instance algebraStageBaseChangeRing (J : WeakIdeals R) :
    Algebra (R ⧸ (OrderDual.ofDual J).1) (stageBaseChangeRing D v hY hV hv J) :=
  (stageBaseChangeRingHom D v hY hV hv J).toAlgebra

/-- The structure map of the `R ⧸ J`-algebra `stageBaseChangeRing D v hY hV hv J` is
`AlgebraicGeometry.FormalSpace.stageBaseChangeRingHom`. -/
theorem algebraMap_stageBaseChangeRing (J : WeakIdeals R) :
    algebraMap (R ⧸ (OrderDual.ofDual J).1) (stageBaseChangeRing D v hY hV hv J) =
      stageBaseChangeRingHom D v hY hV hv J := rfl

/-- **The chosen affine model of `Spec (R ⧸ J) ×_{Spf R} V` is an étale `R ⧸ J`-algebra.** -/
instance etaleAlgebra_stageBaseChangeRing (J : WeakIdeals R) :
    Algebra.Etale (R ⧸ (OrderDual.ofDual J).1) (stageBaseChangeRing D v hY hV hv J) :=
  etale_stageBaseChangeRingHom D v hY hV hv J

/-- **Stacks 04D1 applied to the stage model at `J₀`**: there is an étale `R`-algebra `A`
together with an isomorphism `A ⧸ J₀A ≅ Ā_{J₀}` compatible with the structure maps out of
`R ⧸ J₀`. -/
theorem exists_stageLiftAlgebra (J₀ : TopologicalRing.WeakIdealOfDefinitionIndex R) :
    ∃ (A : Type u) (_ : CommRing A) (_ : Algebra R A), Algebra.Etale R A ∧
      ∃ e : (A ⧸ J₀.1.map (algebraMap R A)) ≃+*
          stageBaseChangeRing D v hY hV hv (OrderDual.toDual J₀),
        e.toRingHom.comp (Ideal.quotientMap (J₀.1.map (algebraMap R A)) (algebraMap R A)
              Ideal.le_comap_map) =
          stageBaseChangeRingHom D v hY hV hv (OrderDual.toDual J₀) := by
  classical
  let instAlg : Algebra (R ⧸ J₀.1)
      (stageBaseChangeRing D v hY hV hv (OrderDual.toDual J₀)) :=
    (stageBaseChangeRingHom D v hY hV hv (OrderDual.toDual J₀)).toAlgebra
  let instEt : Algebra.Etale (R ⧸ J₀.1)
      (stageBaseChangeRing D v hY hV hv (OrderDual.toDual J₀)) :=
    etale_stageBaseChangeRingHom D v hY hV hv (OrderDual.toDual J₀)
  let instBase : Algebra R (stageBaseChangeRing D v hY hV hv (OrderDual.toDual J₀)) :=
    ((stageBaseChangeRingHom D v hY hV hv (OrderDual.toDual J₀)).comp
      (Ideal.Quotient.mk J₀.1)).toAlgebra
  have : IsScalarTower R (R ⧸ J₀.1)
      (stageBaseChangeRing D v hY hV hv (OrderDual.toDual J₀)) :=
    .of_algebraMap_eq fun _ ↦ rfl
  have hsurj : Function.Surjective (algebraMap R (R ⧸ J₀.1)) := by
    rw [Ideal.Quotient.algebraMap_eq]
    exact Ideal.Quotient.mk_surjective
  obtain ⟨A, _, _, hA, ψ, hψ, hker⟩ := etale_lift_along_surjection R (R ⧸ J₀.1)
    (stageBaseChangeRing D v hY hV hv (OrderDual.toDual J₀)) hsurj
  have hker' : RingHom.ker
      (ψ : A →+* stageBaseChangeRing D v hY hV hv (OrderDual.toDual J₀)) =
      J₀.1.map (algebraMap R A) := by
    rw [hker, Ideal.Quotient.algebraMap_eq, Ideal.mk_ker]
  refine ⟨A, inferInstance, inferInstance, hA,
    (Ideal.quotEquivOfEq hker'.symm).trans (RingHom.quotientKerEquivOfSurjective hψ), ?_⟩
  refine Ideal.Quotient.ringHom_ext (RingHom.ext fun r ↦ ?_)
  show ((Ideal.quotEquivOfEq hker'.symm).trans (RingHom.quotientKerEquivOfSurjective hψ))
      (Ideal.quotientMap (J₀.1.map (algebraMap R A)) (algebraMap R A) Ideal.le_comap_map
        (Ideal.Quotient.mk J₀.1 r)) = _
  rw [Ideal.quotientMap_mk, RingEquiv.trans_apply, Ideal.quotEquivOfEq_mk]
  exact (RingHom.quotientKerEquivOfSurjective_apply_mk _ _).trans (ψ.commutes r)

/-- **The chosen étale `R`-algebra `A` lifting the stage model `Ā_{J₀}` at `J₀`.** -/
noncomputable def stageLiftAlgebra (J₀ : TopologicalRing.WeakIdealOfDefinitionIndex R) :
    Type u :=
  (exists_stageLiftAlgebra D v hY hV hv J₀).choose

/-- The commutative ring structure on the chosen lift
`AlgebraicGeometry.FormalSpace.stageLiftAlgebra`. -/
noncomputable instance commRing_stageLiftAlgebra
    (J₀ : TopologicalRing.WeakIdealOfDefinitionIndex R) :
    CommRing (stageLiftAlgebra D v hY hV hv J₀) :=
  (exists_stageLiftAlgebra D v hY hV hv J₀).choose_spec.choose

/-- The `R`-algebra structure on the chosen lift
`AlgebraicGeometry.FormalSpace.stageLiftAlgebra`. -/
noncomputable instance algebra_stageLiftAlgebra
    (J₀ : TopologicalRing.WeakIdealOfDefinitionIndex R) :
    Algebra R (stageLiftAlgebra D v hY hV hv J₀) :=
  (exists_stageLiftAlgebra D v hY hV hv J₀).choose_spec.choose_spec.choose

/-- **The chosen lift is an étale `R`-algebra.** -/
instance etale_stageLiftAlgebra (J₀ : TopologicalRing.WeakIdealOfDefinitionIndex R) :
    Algebra.Etale R (stageLiftAlgebra D v hY hV hv J₀) :=
  (exists_stageLiftAlgebra D v hY hV hv J₀).choose_spec.choose_spec.choose_spec.1

/-- **The reduction of the chosen étale lift modulo `J₀` is the stage model at `J₀`**:
`A ⧸ J₀A ≅ Ā_{J₀}`. -/
noncomputable def stageLiftAlgebraEquiv
    (J₀ : TopologicalRing.WeakIdealOfDefinitionIndex R) :
    (stageLiftAlgebra D v hY hV hv J₀ ⧸
        J₀.1.map (algebraMap R (stageLiftAlgebra D v hY hV hv J₀))) ≃+*
      stageBaseChangeRing D v hY hV hv (OrderDual.toDual J₀) :=
  (exists_stageLiftAlgebra D v hY hV hv J₀).choose_spec.choose_spec.choose_spec.2.choose

/-- The identification `A ⧸ J₀A ≅ Ā_{J₀}` is compatible with the two structure maps out of
`R ⧸ J₀`. -/
theorem stageLiftAlgebraEquiv_comp_quotientMap
    (J₀ : TopologicalRing.WeakIdealOfDefinitionIndex R) :
    (stageLiftAlgebraEquiv D v hY hV hv J₀).toRingHom.comp
        (Ideal.quotientMap (J₀.1.map (algebraMap R (stageLiftAlgebra D v hY hV hv J₀)))
          (algebraMap R (stageLiftAlgebra D v hY hV hv J₀)) Ideal.le_comap_map) =
      stageBaseChangeRingHom D v hY hV hv (OrderDual.toDual J₀) :=
  (exists_stageLiftAlgebra D v hY hV hv J₀).choose_spec.choose_spec.choose_spec.2.choose_spec

end AlgebraicGeometry.FormalSpace

end
