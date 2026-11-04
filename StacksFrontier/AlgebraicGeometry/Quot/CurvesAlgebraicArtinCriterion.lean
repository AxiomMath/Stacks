module

public import StacksFrontier.AlgebraicGeometry.Quot.C1590Private.CurvesArtinInputs
public import StacksFrontier.AlgebraicGeometry.Quot.C1590Private.CurvesSizeBounded
public import StacksFrontier.AlgebraicGeometry.Quot.CurveDeformationsFiniteDimensional
public import StacksFrontier.AlgebraicGeometry.Quot.CurvesFormalEffectiveUnconditional
public import StacksFrontier.AlgebraicGeometry.Quot.CurvesLimitPreservingUnconditional
public import StacksFrontier.AlgebraicGeometry.Quot.CurvesRimSchlessingerArtin
public import StacksFrontier.AlgebraicGeometry.Quot.CurvesStack
public import StacksFrontier.AlgebraicGeometry.Spaces.Pushouts.EtaleChartLifts
public import StacksFrontier.AlgebraicGeometry.Stacks.ArtinCriterion
public import StacksFrontier.AlgebraicGeometry.Stacks.StructureSheaf
public import StacksFrontier.RingTheory.GRing.EssFiniteType

/-!
# Artin's criterion for the stack of curves (towards Stacks 0D5A)

**Stacks 0D5A** says that the stack `Curves` of families of curves is algebraic. Its proof in the
source is Artin's criterion (**Stacks 07Y4**,
`AlgebraicGeometry.Stack.isAlgebraicStack_of_artinAxioms`) applied to `Curves` over `Spec(ℤ)`.

This file applies the criterion. The hypotheses of Stacks 07Y4 that are proved in the library are
discharged here:

* `Spec(ℤ)` is locally Noetherian;
* axiom [-1], the set-theoretic bound of Stacks 07Y3, is
  `AlgebraicGeometry.C1590Private.isSizeBounded_curvesFiberedCategory`;
* axiom [0], the étale stack condition, is the fppf stack condition of Stacks 0D52
  (`AlgebraicGeometry.curvesProjectionOver_isStack`) read for the coarser étale topology;
* axiom [1], limit preservation, is Stacks 0D55,
  `AlgebraicGeometry.isLimitPreserving_curvesFiberedCategory_unconditional`;
* axiom [2], condition (RS), is Stacks 0D56 through the lift of étale charts across thickenings,
  `AlgebraicGeometry.satisfiesRS_curves_of_hasEtaleChartLifts` and
  `AlgebraicGeometry.Space.hasEtaleChartLifts`;
* axiom [3], the tangent-space half, is Stacks 0D57
  (`AlgebraicGeometry.CurveDeformation.finiteDimensional_predeformation`), in
  `AlgebraicGeometry.C1590Private.hasFiniteDimensionalTangentSpaces_curvesFiberedCategory`;
* effectivity of formal objects is Stacks 0D58, `AlgebraicGeometry.curvesFormalObject_isEffective`;
* the local rings of `Spec(ℤ)` are G-rings (Stacks 07PX and Stacks 07PV).

The remaining hypotheses of Stacks 07Y4 are the arguments of
`AlgebraicGeometry.curvesFiberedCategory_isAlgebraicStack_of_artinInputs`, each in exactly the
form in which Stacks 07Y4 asks for it: the diagonal (Stacks 0D53) and openness of versality
(Stacks 0D59).

No declaration here carries a Stacks tag.

## References

* [Stacks Project, Tag 0D5A](https://stacks.math.columbia.edu/tag/0D5A)
* [Stacks Project, Tag 07Y4](https://stacks.math.columbia.edu/tag/07Y4)
* [Stacks Project, Tag 0D57](https://stacks.math.columbia.edu/tag/0D57)
-/

@[expose] public noncomputable section

open CategoryTheory Deformation Deformation.Artin

universe u z

namespace AlgebraicGeometry

variable (B : BigFppfSite.{u}) (hZ : B.Contains integerBase)

/-- The base `Spec(ℤ)` of the absolute stack of curves is locally Noetherian. -/
private theorem isLocallyNoetherian_integerBase' : IsLocallyNoetherian (integerBase.{u}) :=
  isLocallyNoetherian_Spec.mpr (isNoetherianRing_of_ringEquiv ℤ ULift.ringEquiv.symm)

/-- An algebra whose structure map is surjective is of finite type. -/
private theorem finiteType_of_surjective_algebraMap {R A : Type*} [CommRing R] [CommRing A]
    [Algebra R A] (h : Function.Surjective (algebraMap R A)) : Algebra.FiniteType R A :=
  RingHom.finiteType_algebraMap.mp (RingHom.FiniteType.of_surjective _ h)

/-- Every local ring of `Spec(ℤ)` is a G-ring: it is a localization of `ULift ℤ`, which is of
finite type over the G-ring `ℤ` (Stacks 07PX), and an algebra essentially of finite type over a
G-ring is a G-ring (Stacks 07PV). -/
private theorem isGRing_stalk_integerBase' (s : (integerBase.{u} : Scheme.{u})) :
    IsGRing ((integerBase.{u} : Scheme.{u}).presheaf.stalk s) := by
  have hsurj : Function.Surjective (algebraMap ℤ (ULift.{u} ℤ)) := by
    intro x
    refine ⟨(ULift.ringEquiv : ULift.{u} ℤ ≃+* ℤ) x, ?_⟩
    apply (ULift.ringEquiv : ULift.{u} ℤ ≃+* ℤ).injective
    simp
  have : Algebra.FiniteType ℤ (ULift.{u} ℤ) := finiteType_of_surjective_algebraMap hsurj
  have hZG : IsGRing (ULift.{u} ℤ) := isGRing_of_essFiniteType isGRing_basic_examples.{0, 0}.2.2.1
  have hU : IsAffineOpen (⊤ : (integerBase.{u} : Scheme.{u}).Opens) := isAffineOpen_top _
  have hΓ : IsGRing Γ((integerBase.{u} : Scheme.{u}), ⊤) := by
    let e := (Scheme.ΓSpecIso (CommRingCat.of (ULift.{u} ℤ))).commRingCatIsoToRingEquiv.symm
    let : Algebra (ULift.{u} ℤ) Γ((integerBase.{u} : Scheme.{u}), ⊤) := e.toRingHom.toAlgebra
    have : Algebra.FiniteType (ULift.{u} ℤ) Γ((integerBase.{u} : Scheme.{u}), ⊤) :=
      finiteType_of_surjective_algebraMap e.surjective
    exact isGRing_of_essFiniteType hZG
  let x : (⊤ : (integerBase.{u} : Scheme.{u}).Opens) := ⟨s, trivial⟩
  let : Algebra Γ((integerBase.{u} : Scheme.{u}), ⊤)
      ((integerBase.{u} : Scheme.{u}).presheaf.stalk (x : (integerBase.{u} : Scheme.{u}))) :=
    TopCat.Presheaf.algebra_section_stalk (integerBase.{u} : Scheme.{u}).presheaf x
  have : IsLocalization.AtPrime
      ((integerBase.{u} : Scheme.{u}).presheaf.stalk (x : (integerBase.{u} : Scheme.{u})))
      (hU.primeIdealOf x).asIdeal :=
    hU.isLocalization_stalk x
  have : Algebra.EssFiniteType Γ((integerBase.{u} : Scheme.{u}), ⊤)
      ((integerBase.{u} : Scheme.{u}).presheaf.stalk (x : (integerBase.{u} : Scheme.{u}))) :=
    Algebra.EssFiniteType.of_isLocalization _ (hU.primeIdealOf x).asIdeal.primeCompl
  exact isGRing_of_essFiniteType hΓ

/-- **Artin's criterion for `Curves`, on the inputs of Section 99.15 of the source.** The stack
`Curves` of families of curves is an algebraic stack as soon as its diagonal is representable by
algebraic spaces (Stacks 0D53) and it satisfies openness of versality (Stacks 0D59).

Each argument is the corresponding hypothesis of Stacks 07Y4
(`AlgebraicGeometry.Stack.isAlgebraicStack_of_artinAxioms`) for `Curves` over `Spec(ℤ)`, verbatim.
The other hypotheses of Stacks 07Y4 are proved: `Spec(ℤ)` is locally Noetherian, axiom [-1] is
`AlgebraicGeometry.C1590Private.isSizeBounded_curvesFiberedCategory`, axiom [0] is Stacks 0D52
for the coarser étale topology, axiom [1] is Stacks 0D55, (RS) is Stacks 0D56, axiom [3] is
Stacks 0D57
(`AlgebraicGeometry.C1590Private.hasFiniteDimensionalTangentSpaces_curvesFiberedCategory`),
formal objects are effective by Stacks 0D58 and the local rings of `Spec(ℤ)` are G-rings. -/
theorem curvesFiberedCategory_isAlgebraicStack_of_artinInputs
    (hdiag : Stack.HasRepresentableDiagonal B integerBase hZ (curvesFiberedCategory B hZ))
    (hopen : ∀ U : Over integerBase, LocallyOfFiniteType U.hom →
      ∀ (y : (curvesFiberedCategory B hZ).val.obj)
        (hy : ((curvesFiberedCategory B hZ).val.p ⋙ Over.post B.inclusion).obj y = U)
        (u : U.left),
        AlgebraicGeometry.IsFiniteTypePoint u →
        Deformation.Artin.IsVersalAt U ((curvesFiberedCategory B hZ).val.p ⋙ Over.post B.inclusion)
          u y hy →
        ∃ V : U.left.Opens, u ∈ V.1 ∧
          ∀ u' : U.left, u' ∈ V.1 →
            AlgebraicGeometry.IsFiniteTypePoint u' →
            Deformation.Artin.IsVersalAt U
              ((curvesFiberedCategory B hZ).val.p ⋙ Over.post B.inclusion) u' y hy) :
    Stack.IsAlgebraicStack.{u, z, u + 1, u + 1} B integerBase hZ
      (curvesFiberedCategory B hZ).val := by
  have := isLocallyNoetherian_integerBase'.{u}
  exact Stack.isAlgebraicStack_of_artinAxioms.{u, u + 1, u + 1, z} B integerBase hZ
    (curvesFiberedCategory B hZ)
    hdiag (C1590Private.isSizeBounded_curvesFiberedCategory B hZ)
    (((curvesProjectionOver_isStack B hZ).isStackInGroupoids
      (curvesFiberedCategory B hZ).property).of_le
        (fun _ _ hS => Stack.etaleTopology_le_topology B _ hS))
    (isLimitPreserving_curvesFiberedCategory_unconditional B hZ)
    (satisfiesRS_curves_of_hasEtaleChartLifts B hZ (Space.hasEtaleChartLifts B integerBase hZ))
    (C1590Private.hasFiniteDimensionalTangentSpaces_curvesFiberedCategory B hZ)
    (curvesFormalObject_isEffective B hZ) hopen
    (fun s _ => isGRing_stalk_integerBase' s)

end AlgebraicGeometry

end
