module

public import StacksFrontier.AlgebraicGeometry.Quot.C1590Private.CurvesFormalEffective
public import StacksFrontier.AlgebraicGeometry.Quot.C1590Private.CurvesLimitPreserving
public import StacksFrontier.AlgebraicGeometry.Quot.C1590Private.CurvesOpenVersality
public import StacksFrontier.AlgebraicGeometry.Quot.C1590Private.CurvesRSStar
public import StacksFrontier.AlgebraicGeometry.Quot.C1590Private.CurvesSizeBounded
public import StacksFrontier.AlgebraicGeometry.Quot.C1590Private.SpecialTowerCurvesEffective
public import StacksFrontier.AlgebraicGeometry.Quot.C1590Private.SpecialTowerOpenVersality
public import StacksFrontier.AlgebraicGeometry.Quot.CurveDeformationsFiniteDimensional
public import StacksFrontier.AlgebraicGeometry.Quot.CurvesStack
public import StacksFrontier.AlgebraicGeometry.Stacks.ArtinCriterion
public import StacksFrontier.RingTheory.GRing.EssFiniteType
public import StacksFrontier.RingTheory.Jacobson.Examples

/-!
# Artin's criterion for the stack of curves (towards Stacks 0D5A)

Stacks 0D5A — the stack `Curves` of families of curves is algebraic — is proved in the source by
Artin's criterion (Stacks 07Y4), `AlgebraicGeometry.Stack.isAlgebraicStack_of_artinAxioms`,
applied to `Curves` over `Spec(ℤ)`. This file supplies the hypotheses of the criterion that are
not deformation-theoretic, reads the ones the library proves in the form the criterion consumes,
and applies the criterion.

* The base `Spec(ℤ)` is locally Noetherian: an instance of the library.
* Axiom [-1]: `AlgebraicGeometry.C1590Private.isSizeBounded_curvesFiberedCategory`.
* Axiom [0], that `Curves` is a stack in groupoids for the big étale topology over `Spec(ℤ)`:
  the fppf stack condition of Stacks 0D52, `AlgebraicGeometry.curvesProjectionOver_isStack`,
  read for the coarser étale topology.
* Axiom [1], limit preservation (Stacks 0D55):
  `AlgebraicGeometry.C1590Private.isLimitPreserving_curvesFiberedCategory`.
* Axiom [2], condition (RS), from condition (RS*) (Stacks 0D56):
  `AlgebraicGeometry.C1590Private.satisfiesRSStar_curves`.
* The tangent-space half of axiom [3]: part (1) of Stacks 0D57, which the library proves for
  every field, read in the form of the criterion.
* Openness of versality (Stacks 0D59), from Artin's criterion Stacks 0CXU with condition (4)
  for special towers (`AlgebraicGeometry.C1590Private.specialTowerOpenVersality`), over the
  Jacobson base `Spec(ℤ)`:
  `AlgebraicGeometry.C1590Private.hasOpenVersality_curvesFiberedCategory_of_inputs`.
* The G-ring condition: every local ring of `Spec(ℤ)` is a G-ring, by Stacks 07PX for `ℤ` and
  Stacks 07PV along the essentially finite type maps `ℤ → Γ(Spec ℤ) → 𝒪_{Spec ℤ, s}`.

## Main results

* `AlgebraicGeometry.C1590Private.isGRing_stalk_integerBase`: the G-ring condition.
* `AlgebraicGeometry.C1590Private.curvesFiberedCategory_isStackInGroupoids_etale`: axiom [0].
* `AlgebraicGeometry.C1590Private.hasFiniteDimensionalTangentSpaces_curvesFiberedCategory`:
  Artin's axiom [3] in the form the criterion asks for, from part (1) of Stacks 0D57.
* `AlgebraicGeometry.C1590Private.hasOpenVersality_curvesFiberedCategory_of_inputs`: openness of
  versality for `Curves`, from Stacks 0CXU for special towers.
* `AlgebraicGeometry.C1590Private.isAlgebraicStack_curvesFiberedCategory_of_artinInputs`:
  Artin's criterion for `Curves`, on the three inputs of the source's proof not yet available
  here: the diagonal (Stacks 0D53), effectivity of formal objects (Stacks 0D58), and the
  effectivity of special towers of square-zero thickenings (the case of condition (4) of
  Stacks 0CXU that its proof uses, established in the proof of Stacks 0D3X).
* `AlgebraicGeometry.C1590Private.isAlgebraicStack_curvesFiberedCategory_of_diagonal`: the same
  with effectivity of formal objects supplied (Stacks 0D58,
  `AlgebraicGeometry.C1590Private.isEffective_curvesFormalObject`), on the diagonal and the
  special-tower effectivity alone.
* `AlgebraicGeometry.C1590Private.isAlgebraicStack_curvesFiberedCategory`: the stack of curves is
  algebraic (Stacks 0D5A), with the diagonal (Stacks 0D53) and the special-tower effectivity
  supplied.

## Implementation notes

Nothing here carries a `stacks` attribute: the last declaration takes results the source proves
as arguments, and is only the shape in which they are assembled.

## References

* [Stacks Project, Tag 0D5A](https://stacks.math.columbia.edu/tag/0D5A)
* [Stacks Project, Tag 07Y4](https://stacks.math.columbia.edu/tag/07Y4)
* [Stacks Project, Tag 0D52](https://stacks.math.columbia.edu/tag/0D52)
* [Stacks Project, Tag 0D57](https://stacks.math.columbia.edu/tag/0D57)
* [Stacks Project, Tag 0D59](https://stacks.math.columbia.edu/tag/0D59)
* [Stacks Project, Tag 07PV](https://stacks.math.columbia.edu/tag/07PV)
* [Stacks Project, Tag 07PX](https://stacks.math.columbia.edu/tag/07PX)
-/

@[expose] public section

open CategoryTheory

universe u w

namespace AlgebraicGeometry.C1590Private

/-! ### The G-ring condition at `Spec(ℤ)` -/

/-- The integers raised to the universe `u` form a G-ring: they are of finite type over `ℤ`,
which is a G-ring (Stacks 07PX), and finite type algebras over G-rings are G-rings
(Stacks 07PV). -/
theorem isGRing_uliftInt : IsGRing (ULift.{u} ℤ) := by
  have : Algebra.FiniteType ℤ (ULift.{u} ℤ) :=
    Algebra.FiniteType.of_surjective (Algebra.ofId ℤ (ULift.{u} ℤ))
      (fun x => ⟨x.down, by ext; simp⟩)
  exact isGRing_basic_examples.{0, u}.2.2.2.2 ℤ (ULift.{u} ℤ) isGRing_basic_examples.{0, 0}.2.2.1

/-- **The G-ring condition of Artin's criterion at `Spec(ℤ)`**: every local ring of the base
`Spec(ℤ)` of the absolute stack of curves is a G-ring, at every point and not only at the finite
type ones. The global sections of `Spec(ℤ)` are a finite type algebra over `ℤ` (they are
isomorphic to it), and a local ring of an affine scheme is a localization of its global
sections, hence essentially of finite type over them (Stacks 07PV). -/
theorem isGRing_stalk_integerBase (s : integerBase.{u}) :
    IsGRing (integerBase.{u}.presheaf.stalk s) := by
  let e := Scheme.ΓSpecIso (CommRingCat.of (ULift.{u} ℤ))
  let : Algebra (ULift.{u} ℤ) Γ(integerBase.{u}, ⊤) := e.inv.hom.toAlgebra
  have : Algebra.FiniteType (ULift.{u} ℤ) Γ(integerBase.{u}, ⊤) :=
    Algebra.FiniteType.of_surjective (Algebra.ofId _ _)
      (fun y => ⟨e.hom.hom y, by
        show e.inv.hom (e.hom.hom y) = y
        rw [← CommRingCat.comp_apply, e.hom_inv_id, CommRingCat.id_apply]⟩)
  have hΓ : IsGRing Γ(integerBase.{u}, ⊤) :=
    isGRing_basic_examples.{u, u}.2.2.2.2 _ _ isGRing_uliftInt
  let := integerBase.{u}.presheaf.algebra_section_stalk (U := ⊤) ⟨s, trivial⟩
  have := (isAffineOpen_top integerBase.{u}).isLocalization_stalk ⟨s, trivial⟩
  have : Algebra.EssFiniteType Γ(integerBase.{u}, ⊤) (integerBase.{u}.presheaf.stalk s) :=
    Algebra.EssFiniteType.of_isLocalization _
      ((isAffineOpen_top integerBase.{u}).primeIdealOf ⟨s, trivial⟩).asIdeal.primeCompl
  exact isGRing_of_essFiniteType hΓ

/-! ### Axiom [0] -/

variable (B : BigFppfSite.{u}) (hZ : B.Contains integerBase)

/-- **Axiom [0] of Artin's axioms for `Curves`**: the category of families of curves is a stack
in groupoids for the localization at `Spec(ℤ)` of the big étale topology. This is Stacks 0D52
(`AlgebraicGeometry.curvesProjectionOver_isStack`, the fppf stack condition) read for the
coarser étale topology (`AlgebraicGeometry.Stack.etaleTopology_le_topology`). -/
theorem curvesFiberedCategory_isStackInGroupoids_etale :
    (curvesFiberedCategory B hZ).val.p.IsStackInGroupoids.{u + 1}
      ((AlgebraicGeometry.etaleTopology B).over (B.obj hZ)) :=
  ((curvesProjectionOver_isStack B hZ).isStackInGroupoids
    (curvesFiberedCategory B hZ).property).of_le
    (fun _ _ hS => Stack.etaleTopology_le_topology B _ hS)

/-! ### The tangent spaces -/

/-- **Axiom [3] for `Curves`, in the form Artin's criterion consumes it**: the tangent space of
the predeformation category of a family of curves over a finite type field is finite
dimensional. This is part (1) of Stacks 0D57,
`AlgebraicGeometry.CurveDeformation.finiteDimensional_predeformation`, which holds for every
field and every `Λ`, read at the local ring of `Spec(ℤ)` at the image point. -/
theorem hasFiniteDimensionalTangentSpaces_curvesFiberedCategory :
    Stack.HasFiniteDimensionalTangentSpaces B integerBase hZ (curvesFiberedCategory B hZ) := by
  intro k _ i₀ x₀ hx₀ _ _ s _ Λ _ _ _ iΛ _ hbase hx D hD
  exact (CurveDeformation.finiteDimensional_predeformation (B := B) (hZ := hZ)
    (Λ := Λ) (k := k) (iΛ := iΛ) x₀ (hx₀.trans (congrArg Over.mk hbase.symm))).choose_spec.1

/-! ### Openness of versality for `Curves` -/

/-- **Openness of versality for `Curves`, from Artin's criterion (Stacks 0CXU).** Given the
diagonal `hdiag` (Stacks 0D53), condition (RS*) `hRS` (Stacks 0D56), limit preservation
`hlimit` (Stacks 0D55) and the effectivity `hspecial` of special towers of square-zero
thickenings on lift classes for the small model (the case of condition (4) of Stacks 0CXU that
its proof uses, established in the proof of Stacks 0D3X), versality is open for `Curves`: an
object over a scheme locally of finite type over `Spec(ℤ)` which is versal at a finite type
point is versal at every finite type point of a neighbourhood. The base `Spec(ℤ)` is Jacobson,
as the special-tower form of Stacks 0CXU asks. -/
theorem hasOpenVersality_curvesFiberedCategory_of_inputs
    (hdiag : Stack.HasRepresentableDiagonal B integerBase hZ (curvesFiberedCategory B hZ))
    (hRS : Deformation.Artin.SatisfiesRSStar B integerBase hZ (curvesFiberedCategory B hZ).val.p
      (curvesFiberedCategory B hZ).property)
    (hlimit : Deformation.Artin.IsLimitPreserving.{u, u, u, u + 1, u + 1} B integerBase hZ
      (curvesFiberedCategory B hZ))
    (hspecial : IsSpecialSquareZeroTowerEffectiveOnClasses B integerBase hZ
      (curvesSmall B hZ).val.p (curvesSmall B hZ).isFiberedInGroupoids) :
    Deformation.Artin.HasOpenVersality
      ((curvesFiberedCategory B hZ).val.p ⋙ Over.post B.inclusion) := by
  have : IsJacobsonRing (ULift.{u} ℤ) :=
    (isJacobsonRing_iso (ULift.ringEquiv : ULift.{u} ℤ ≃+* ℤ)).mpr int_isJacobsonRing
  exact Deformation.Artin.hasOpenVersality_of_equivalenceOver (curvesSmallEquivalenceOver B hZ).symm
    (specialTowerOpenVersality B integerBase hZ (curvesSmall B hZ)
      (hasRepresentableDiagonal_curvesSmall B hZ hdiag)
      (satisfiesRSStar_of_equivalenceOver B integerBase hZ (curvesFiberedCategory B hZ).property
        (curvesSmall B hZ).isFiberedInGroupoids hRS (curvesSmallEquivalenceOver B hZ))
      (Stack.isLimitPreserving_of_equivalenceOver B integerBase hZ (curvesSmall B hZ)
        (curvesFiberedCategory B hZ) (curvesSmallEquivalenceOver B hZ).symm hlimit)
      hspecial)

/-! ### Artin's criterion for `Curves` -/

/-- **Artin's criterion (Stacks 07Y4) for the stack of curves**, on the three inputs of the
source's proof of Stacks 0D5A that are not yet available here: the diagonal `hdiag`
(Stacks 0D53), effectivity of formal objects `heffective` (Stacks 0D58), and `hspecial`, the
effectivity on lift classes of special towers of square-zero thickenings for the small model of
`Curves`, which is the case of condition (4) of Stacks 0CXU that its proof uses, established in
the proof of Stacks 0D3X. Every other
hypothesis of the criterion is supplied: axioms [-1], [0], [1] (Stacks 0D55), [2] (Stacks 0D56),
the tangent spaces (Stacks 0D57), openness of versality (Stacks 0D59, from Stacks 0CXU on
`hdiag`, (RS*), limit preservation and `hspecial`), the Noetherian base and the G-ring
condition. -/
theorem isAlgebraicStack_curvesFiberedCategory_of_artinInputs
    (hdiag : Stack.HasRepresentableDiagonal B integerBase hZ (curvesFiberedCategory B hZ))
    (heffective : ∀ ξ : Deformation.Artin.FormalObject B integerBase hZ
        (curvesFiberedCategory B hZ).val.p,
      Deformation.Artin.FormalObject.IsEffective B integerBase hZ
        (curvesFiberedCategory B hZ).val.p (curvesFiberedCategory B hZ).property ξ)
    (hspecial : IsSpecialSquareZeroTowerEffectiveOnClasses B integerBase hZ
      (curvesSmall B hZ).val.p (curvesSmall B hZ).isFiberedInGroupoids) :
    Stack.IsAlgebraicStack.{u, w} B integerBase hZ (curvesFiberedCategory B hZ).val :=
  Stack.isAlgebraicStack_of_artinAxioms.{u, u + 1, u, w} B integerBase hZ
    (curvesFiberedCategory B hZ) hdiag (isSizeBounded_curvesFiberedCategory B hZ)
    (curvesFiberedCategory_isStackInGroupoids_etale B hZ)
    (isLimitPreserving_curvesFiberedCategory B hZ)
    (Deformation.Artin.satisfiesRS_of_satisfiesRSStar B integerBase hZ _ _
      (satisfiesRSStar_curves B hZ))
    (hasFiniteDimensionalTangentSpaces_curvesFiberedCategory B hZ) heffective
    (hasOpenVersality_curvesFiberedCategory_of_inputs B hZ hdiag (satisfiesRSStar_curves B hZ)
      (isLimitPreserving_curvesFiberedCategory B hZ) hspecial)
    (fun s _ => isGRing_stalk_integerBase s)

/-- **Artin's criterion (Stacks 07Y4) for the stack of curves, on the diagonal and the tower
effectivity alone**: the criterion
`AlgebraicGeometry.C1590Private.isAlgebraicStack_curvesFiberedCategory_of_artinInputs` with
effectivity of formal objects supplied by Stacks 0D58
(`AlgebraicGeometry.C1590Private.isEffective_curvesFormalObject`). The remaining inputs are the
diagonal `hdiag` (Stacks 0D53) and `hspecial`, condition (4) of Stacks 0CXU for special towers
for the small model of `Curves`, established in the proof of Stacks 0D3X. -/
theorem isAlgebraicStack_curvesFiberedCategory_of_diagonal
    (hdiag : Stack.HasRepresentableDiagonal B integerBase hZ (curvesFiberedCategory B hZ))
    (hspecial : IsSpecialSquareZeroTowerEffectiveOnClasses B integerBase hZ
      (curvesSmall B hZ).val.p (curvesSmall B hZ).isFiberedInGroupoids) :
    Stack.IsAlgebraicStack.{u, w} B integerBase hZ (curvesFiberedCategory B hZ).val :=
  isAlgebraicStack_curvesFiberedCategory_of_artinInputs B hZ hdiag
    (isEffective_curvesFormalObject B hZ) hspecial

/-- **The stack of curves is algebraic** (Stacks 0D5A): Artin's criterion
`AlgebraicGeometry.C1590Private.isAlgebraicStack_curvesFiberedCategory_of_diagonal`, with the
diagonal from Stacks 0D53
(`AlgebraicGeometry.C1590Private.hasRepresentableDiagonal_curvesFiberedCategory`) and the
effectivity of special towers from the proof of Stacks 0D3X
(`AlgebraicGeometry.C1590Private.isSpecialSquareZeroTowerEffectiveOnClasses_curvesSmall`). -/
theorem isAlgebraicStack_curvesFiberedCategory :
    Stack.IsAlgebraicStack.{u, w} B integerBase hZ (curvesFiberedCategory B hZ).val :=
  isAlgebraicStack_curvesFiberedCategory_of_diagonal B hZ
    (hasRepresentableDiagonal_curvesFiberedCategory B hZ)
    (isSpecialSquareZeroTowerEffectiveOnClasses_curvesSmall B hZ)

end AlgebraicGeometry.C1590Private

end
