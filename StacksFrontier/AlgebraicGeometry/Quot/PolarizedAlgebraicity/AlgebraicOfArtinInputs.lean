module

public import StacksFrontier.AlgebraicGeometry.FundamentalGroup.FiniteEtaleProperHenselianLimit
public import StacksFrontier.AlgebraicGeometry.Quot.PolarizedAlgebraicity.QuasiSeparatedOfAlgebraic
public import StacksFrontier.AlgebraicGeometry.Quot.PolarizedAlgebraicity.RimSchlessinger
public import StacksFrontier.AlgebraicGeometry.Quot.PolarizedDeformationFiniteDimensional
public import StacksFrontier.AlgebraicGeometry.Quot.PolarizedDiagonal
public import StacksFrontier.AlgebraicGeometry.Quot.PolarizedFormalEffective
public import StacksFrontier.AlgebraicGeometry.Quot.PolarizedLimitPreservingProof
public import StacksFrontier.AlgebraicGeometry.Quot.PolarizedSizeBounded
public import StacksFrontier.AlgebraicGeometry.Quot.PolarizedStackRepresentable
public import StacksFrontier.AlgebraicGeometry.Stacks.ArtinCriterion
public import StacksFrontier.AlgebraicGeometry.Stacks.ArtinCriterionTangentSpaces

/-!
# Artin's criterion for `𝒫olarized`

Artin's criterion `AlgebraicGeometry.Stack.isAlgebraicStack_of_artinAxioms` applied to the stack
`𝒫olarized` of polarized proper schemes over `Spec(ℤ)`: the representability of the diagonal,
limit preservation, condition (RS), the effectivity of formal objects and the conditions on the
base hold for `𝒫olarized`, and the remaining inputs are taken as hypotheses.

## Main results

* `isGRing_stalk_specULiftInt`: the local rings of `Spec(ℤ)` are G-rings.
* `isAlgebraicStack_polarized_of_artinInputs`: `𝒫olarized` is an algebraic stack,
  assuming axiom [-1], the fppf stack condition, finite dimensional tangent spaces and
  openness of versality.
* `isAlgebraicStack_polarized_of_isOpenVersality`: `𝒫olarized` is an algebraic stack, assuming
  openness of versality.
* `isQuasiSeparated_and_isLocallyOfFinitePresentation_polarized_of_isOpenVersality`:
  assuming openness of versality, `𝒫olarized → Spec(ℤ)` is quasi-separated and locally of finite
  presentation.

## References

* [Stacks Project, Tag 0D4X](https://stacks.math.columbia.edu/tag/0D4X)
* [Stacks Project, Tag 07Y4](https://stacks.math.columbia.edu/tag/07Y4)
* [Stacks Project, Tag 07PX](https://stacks.math.columbia.edu/tag/07PX)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits

universe u z

namespace AlgebraicGeometry.PolarizedAlgebraicity

/-- **The local rings of `Spec(ℤ)` are G-rings.** -/
theorem isGRing_stalk_specULiftInt (s : Spec (CommRingCat.of (ULift.{u} ℤ))) :
    IsGRing ((Spec (CommRingCat.of (ULift.{u} ℤ))).presheaf.stalk s) :=
  have : IsIso (terminal.from (Spec (CommRingCat.of (ULift.{u} ℤ)))) :=
    isIso_of_isTerminal specULiftZIsTerminal.{u} terminalIsTerminal _
  isGRing_stalk_of_locallyOfFiniteType_terminal s

variable (B : BigFppfSite.{u}) (hZ : B.Contains (Spec (CommRingCat.of (ULift.{u} ℤ))))

/-- **Artin's criterion for `𝒫olarized` over `Spec(ℤ)`, from its four remaining inputs.** If
`𝒫olarized` satisfies axiom [-1] (`hsize`), is an fppf stack (`hfppf`), has finite dimensional
tangent spaces (`htangent`) and satisfies openness of versality (`hopen`), then it is an algebraic
stack. -/
theorem isAlgebraicStack_polarized_of_artinInputs
    (hsize : Stack.IsSizeBounded B _ hZ
      (polarizedStackUnconditional B hZ (isTerminal_obj_specULiftZ B hZ)))
    (hfppf : (polarizedStackUnconditional B hZ (isTerminal_obj_specULiftZ B hZ)).val.p.IsStack
      (BigFppfOver.topology B _ hZ))
    (htangent : Stack.HasFiniteDimensionalTangentSpaces B _ hZ
      (polarizedStackUnconditional B hZ (isTerminal_obj_specULiftZ B hZ)))
    (hopen : ∀ U : Over (Spec (CommRingCat.of (ULift.{u} ℤ))), LocallyOfFiniteType U.hom →
      ∀ (y : (polarizedStackUnconditional B hZ (isTerminal_obj_specULiftZ B hZ)).val.obj)
        (hy : ((polarizedStackUnconditional B hZ (isTerminal_obj_specULiftZ B hZ)).val.p ⋙
          Over.post B.inclusion).obj y = U) (u : U.left),
        AlgebraicGeometry.IsFiniteTypePoint u →
        Deformation.Artin.IsVersalAt U
          ((polarizedStackUnconditional B hZ (isTerminal_obj_specULiftZ B hZ)).val.p ⋙
            Over.post B.inclusion) u y hy →
        ∃ V : U.left.Opens, u ∈ V.1 ∧
          ∀ u' : U.left, u' ∈ V.1 →
            AlgebraicGeometry.IsFiniteTypePoint u' →
            Deformation.Artin.IsVersalAt U
              ((polarizedStackUnconditional B hZ (isTerminal_obj_specULiftZ B hZ)).val.p ⋙
                Over.post B.inclusion) u' y hy) :
    Stack.IsAlgebraicStack.{u, z, u, u + 1} B _ hZ
      (polarizedStackUnconditional B hZ (isTerminal_obj_specULiftZ B hZ)).val :=
  let : (polarizedStackUnconditional B hZ (isTerminal_obj_specULiftZ B hZ)).val.p.IsFibered :=
    (polarizedStackUnconditional B hZ (isTerminal_obj_specULiftZ B hZ)).property.isFibered
  have : IsNoetherianRing (ULift.{u} ℤ) := isNoetherianRing_of_ringEquiv ℤ ULift.ringEquiv.symm
  Stack.isAlgebraicStack_of_artinAxioms.{u, u, u + 1, z} B _ hZ
    (polarizedStackUnconditional B hZ (isTerminal_obj_specULiftZ B hZ))
    (hasRepresentableDiagonal_polarizedStackUnconditional B hZ (isTerminal_obj_specULiftZ B hZ))
    hsize
    ((hfppf.isStackInGroupoids
      (polarizedStackUnconditional B hZ (isTerminal_obj_specULiftZ B hZ)).property).of_le
      (fun _ _ h => Stack.etaleTopology_le_topology B _ h))
    (isLimitPreservingPolarizedUnconditional B hZ (isTerminal_obj_specULiftZ B hZ))
    (satisfiesRS_polarizedSliceProjection B hZ (isTerminal_obj_specULiftZ B hZ))
    htangent
    (fun ξ => polarizedFormalObject_isEffective B hZ ξ)
    hopen
    (fun s _ => isGRing_stalk_specULiftInt s)

/-- **Artin's criterion for `𝒫olarized` over `Spec(ℤ)`, from openness of versality.** If
`𝒫olarized` satisfies openness of versality (`hopen`), it is an algebraic stack. -/
theorem isAlgebraicStack_polarized_of_isOpenVersality
    (hopen : ∀ U : Over (Spec (CommRingCat.of (ULift.{u} ℤ))), LocallyOfFiniteType U.hom →
      ∀ (y : (polarizedStackUnconditional B hZ (isTerminal_obj_specULiftZ B hZ)).val.obj)
        (hy : ((polarizedStackUnconditional B hZ (isTerminal_obj_specULiftZ B hZ)).val.p ⋙
          Over.post B.inclusion).obj y = U) (u : U.left),
        AlgebraicGeometry.IsFiniteTypePoint u →
        Deformation.Artin.IsVersalAt U
          ((polarizedStackUnconditional B hZ (isTerminal_obj_specULiftZ B hZ)).val.p ⋙
            Over.post B.inclusion) u y hy →
        ∃ V : U.left.Opens, u ∈ V.1 ∧
          ∀ u' : U.left, u' ∈ V.1 →
            AlgebraicGeometry.IsFiniteTypePoint u' →
            Deformation.Artin.IsVersalAt U
              ((polarizedStackUnconditional B hZ (isTerminal_obj_specULiftZ B hZ)).val.p ⋙
                Over.post B.inclusion) u' y hy) :
    Stack.IsAlgebraicStack.{u, z, u, u + 1} B _ hZ
      (polarizedStackUnconditional B hZ (isTerminal_obj_specULiftZ B hZ)).val :=
  isAlgebraicStack_polarized_of_artinInputs B hZ
    (isSizeBounded_polarizedStackUnconditional B hZ)
    (polarizedStackUnconditional_isStack B hZ)
    (Stack.hasFiniteDimensionalTangentSpaces_of_isFiniteDimensionalDeformationCategory B _ hZ _
      (fun _ _ _ _ _ iΛ x₀ hx₀ hlft hqc =>
        PolarizedDeformation.isFiniteDimensionalDeformationCategory_predeformationCategory B hZ
          (isTerminal_obj_specULiftZ B hZ) iΛ x₀ hx₀ ⟨hlft, hqc⟩))
    hopen

/-- If `𝒫olarized` satisfies openness of versality (`hopen`), then `𝒫olarized → Spec(ℤ)` is
quasi-separated and locally of finite presentation, `𝒫olarized` being an algebraic stack by
`isAlgebraicStack_polarized_of_isOpenVersality`. -/
theorem isQuasiSeparated_and_isLocallyOfFinitePresentation_polarized_of_isOpenVersality
    (hopen : ∀ U : Over (Spec (CommRingCat.of (ULift.{u} ℤ))), LocallyOfFiniteType U.hom →
      ∀ (y : (polarizedStackUnconditional B hZ (isTerminal_obj_specULiftZ B hZ)).val.obj)
        (hy : ((polarizedStackUnconditional B hZ (isTerminal_obj_specULiftZ B hZ)).val.p ⋙
          Over.post B.inclusion).obj y = U) (u : U.left),
        AlgebraicGeometry.IsFiniteTypePoint u →
        Deformation.Artin.IsVersalAt U
          ((polarizedStackUnconditional B hZ (isTerminal_obj_specULiftZ B hZ)).val.p ⋙
            Over.post B.inclusion) u y hy →
        ∃ V : U.left.Opens, u ∈ V.1 ∧
          ∀ u' : U.left, u' ∈ V.1 →
            AlgebraicGeometry.IsFiniteTypePoint u' →
            Deformation.Artin.IsVersalAt U
              ((polarizedStackUnconditional B hZ (isTerminal_obj_specULiftZ B hZ)).val.p ⋙
                Over.post B.inclusion) u' y hy) :
    Stack.AlgebraicStacks.IsQuasiSeparated B _ hZ
        (Stack.structureMorphism B _ hZ (polarizedAlgebraicStackOf.{u, u + 1} B hZ
          (isTerminal_obj_specULiftZ B hZ)
          (isAlgebraicStack_polarized_of_isOpenVersality B hZ hopen))) ∧
      Stack.AlgebraicStacks.IsLocallyOfFinitePresentation B _ hZ
        (Stack.structureMorphism B _ hZ (polarizedAlgebraicStackOf.{u, u + 1} B hZ
          (isTerminal_obj_specULiftZ B hZ)
          (isAlgebraicStack_polarized_of_isOpenVersality B hZ hopen))) :=
  isQuasiSeparated_and_isLocallyOfFinitePresentation_polarizedAlgebraicStackOf B hZ
    (isTerminal_obj_specULiftZ B hZ) _

end AlgebraicGeometry.PolarizedAlgebraicity

end
