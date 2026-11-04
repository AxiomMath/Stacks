module

public import StacksFrontier.AlgebraicGeometry.Curves.ContractingRationalBridges.TerminalBaseChange
public import StacksFrontier.AlgebraicGeometry.Curves.ContractingRationalTails.TerminalBaseChange
public import StacksFrontier.AlgebraicGeometry.Curves.NodalFamilyCriterion
public import StacksFrontier.AlgebraicGeometry.Quot.StableCurveFamilies
import StacksFrontier.AlgebraicGeometry.Quot.StableReduction.FamilyCriterion.FieldExtensionFibreBaseChange

/-!
# The fibres of a family of nodal curves over field-valued points

Let `p : Y ⟶ S` be proper and at-worst-nodal of relative dimension one, and suppose that every
fibre `Y_s` over `κ(s)` has `H⁰(Y_s, 𝒪) = κ(s)`, genus at least two, no rational tail and no
rational bridge. Then for every field `K` and every morphism `Spec K ⟶ S`, the fibre product
`Y ×_S Spec K` over `K` has genus at least two, no rational tail and no rational bridge: it is the
base change of `Y_s` along the field extension `κ(s) ⟶ K`, where `s` is the image point, and the
three conditions are invariant under extension of the ground field (Stacks 0E3L, 0E3Q).

## Main results

* `AlgebraicGeometry.hasGenusTwoNoRationalTailNoRationalBridge_of_isPullback`.
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits

universe u

namespace AlgebraicGeometry

/-- **The fibre conditions of a stable family hold at every field-valued point.** -/
theorem hasGenusTwoNoRationalTailNoRationalBridge_of_isPullback {Y S V : Scheme.{u}}
    (p : Y ⟶ S) [IsProper p] (hnodal : IsAtWorstNodalOfRelativeDimensionOne p)
    (hfib : ∀ s : S,
      IsIso ((Scheme.ΓSpecIso (S.residueField s)).inv ≫ (p.fiberToSpecResidueField s).appTop) ∧
        HasGenusTwoNoRationalTailNoRationalBridge (S.residueField s) (p.fiberToSpecResidueField s))
    (K : Type u) [Field K] (a : Spec (.of K) ⟶ S) {v : V ⟶ Spec (.of K)} {q : V ⟶ Y}
    (hsq : IsPullback q v p a) :
    HasGenusTwoNoRationalTailNoRationalBridge K v := by
  obtain ⟨⟨s, φ⟩, rfl⟩ := (Scheme.SpecToEquivOfField K S).symm.surjective a
  obtain ⟨hglob, hX⟩ := hfib s
  let : Algebra (S.residueField s) K := φ.hom.toAlgebra
  let fX := p.fiberToSpecResidueField s
  have : IsIso ((Scheme.ΓSpecIso (.of (S.residueField s))).inv ≫ fX.appTop) := hglob
  have : IsProper fX := MorphismProperty.of_isPullback
    (IsPullback.of_hasPullback p (S.fromSpecResidueField s)) inferInstance
  have hsq' : IsPullback (pullback.lift q (v ≫ Spec.map φ) (by simpa using hsq.w)) v fX
      (Spec.map (CommRingCat.ofHom (algebraMap (S.residueField s) K))) :=
    IsPullback.of_right (by rw [pullback.lift_fst]; exact hsq) (pullback.lift_snd _ _ _)
      (IsPullback.of_hasPullback p (S.fromSpecResidueField s))
  have : ConnectedSpace (p.fiber s) := connectedSpace_of_isIso_globalSections (S.residueField s) fX
  obtain ⟨-, hdim, hnod⟩ :=
    ((Stacks.Curves.hasAtWorstNodalFibresOfDimensionOne_iff p).mpr hnodal).2.2 s inferInstance
  exact hasGenusTwoNoRationalTailNoRationalBridge_of_isPullback_specMapAlgebraMap
    (S.residueField s) K fX hdim hnod hX hsq'

end AlgebraicGeometry

end
