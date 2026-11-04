module

public import StacksFrontier.AlgebraicGeometry.Morphisms.FiniteType.SpecField
public import StacksFrontier.AlgebraicGeometry.Quot.CoherentStackInfFinite
public import StacksFrontier.AlgebraicGeometry.Quot.CoherentStackLimitPreserving
public import StacksFrontier.AlgebraicGeometry.Stacks.ArtinCriterion
public import StacksFrontier.Deformation.Artin.Predeformation.PresentationChange

/-!
# The tangent spaces of `Coh_{X/Y}` in the form Artin's criterion consumes

Stacks 08W8
(`CoherentSituation.finiteDimensional_tangentSpace_and_infinitesimalAutomorphisms_cohDef`)
is stated in the convention of Section 07T2: the predeformation category of a point `x₀` of
`Coh_{X/Y}` over `Spec k` is formed over `𝒞_Λ` for an affine open `Spec Λ ⊆ S` through which
`Spec k ⟶ S` factors with `Λ → k` finite. The tangent-space hypothesis of Artin's criterion,
`AlgebraicGeometry.Stack.HasFiniteDimensionalTangentSpaces`, asks instead for the tangent space of
the predeformation category formed at the presentation of the point by the local ring `𝒪_{S,s}`.

This file feeds the first into the second. Such an affine open exists by Stacks 01TA
(`AlgebraicGeometry.finiteType_specField_tfae`), and the tangent space does not depend on the
presentation of the point
(`Deformation.Artin.finiteDimensional_artinianTangentSpace_of_presentation`).

## Main results

* `AlgebraicGeometry.Space.CoherentSituation.hasFiniteDimensionalTangentSpaces`: over a locally
  Noetherian base, with `Y` locally of finite presentation over `S`, `Coh_{X/Y}` satisfies the
  tangent-space hypothesis of Artin's criterion.

## Implementation notes

The hypothesis `AlgebraicGeometry.Stack.HasFiniteDimensionalTangentSpaces` quantifies over a type
`Λ` equal to `𝒪_{S,s}` together with arbitrary ring and algebra structures on it, and over a map
`Spec Λ ⟶ S` heterogeneously equal to the canonical one. Those two equalities do not determine the
ring structure, so the proof does not use them: the presentation-independence of the tangent
space needs only that both presentations factor the same point.

## References

* [Stacks Project, Tag 08W8](https://stacks.math.columbia.edu/tag/08W8)
* [Stacks Project, Tag 01TA](https://stacks.math.columbia.edu/tag/01TA)
* [Stacks Project, Tag 07Y4](https://stacks.math.columbia.edu/tag/07Y4)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits Opposite Deformation Deformation.Artin

universe u

namespace AlgebraicGeometry.Space.CoherentSituation

variable {B : BigFppfSite.{u}} {S : Scheme.{u}} {hS : B.Contains S}
  (D : CoherentSituation B S hS)

attribute [local instance] cohCategory predefCategory

/-- **The tangent spaces of `Coh_{X/Y}` are finite-dimensional, in the form Artin's criterion
consumes.** Over a locally Noetherian base `S`, with `Y` locally of finite presentation over `S`,
for every field `k` of finite type over `S` and every object `x₀` of `Coh_{X/Y}` over `Spec k`, the
tangent space of the predeformation category of `x₀` formed at any presentation of the point is a
finite-dimensional `k`-vector space for its canonical structure.

This is Stacks 08W8 at an affine open `Spec Λ ⊆ S` through which `Spec k ⟶ S` factors with
`Λ → k` finite (such an open exists by Stacks 01TA), carried to the given presentation by
`Deformation.Artin.finiteDimensional_artinianTangentSpace_of_presentation`. -/
theorem hasFiniteDimensionalTangentSpaces [IsLocallyNoetherian S]
    (hlfp : IsLocallyOfFinitePresentation B S hS (terminal.from D.Y.1)) :
    Stack.HasFiniteDimensionalTangentSpaces B S hS D.coherentCFG := by
  intro k _ i₀ x₀ hx₀ hlft hqc s _ Λ _ _ _ iΛ _ hbase
  dsimp only
  intro hD
  obtain ⟨U, hU, hfin⟩ := ((finiteType_specField_tfae i₀).out 2 3).mp hlft
  let φ : Γ(S, U.1) ⟶ CommRingCat.of k := i₀.appLE U ⊤ hU ≫ (Scheme.ΓSpecIso (.of k)).hom
  let : Algebra Γ(S, U.1) k := φ.hom.toAlgebra
  have : Module.Finite Γ(S, U.1) k := hfin
  let iU : Spec (.of Γ(S, U.1)) ⟶ S := U.2.fromSpec
  have hfac : Spec.map (CommRingCat.ofHom (algebraMap Γ(S, U.1) k)) ≫ iU = i₀ := by
    show Spec.map φ ≫ U.2.fromSpec = i₀
    rw [Spec.map_comp, Category.assoc, U.2.SpecMap_appLE_fromSpec i₀ (isAffineOpen_top _),
      IsAffineOpen.fromSpec_top, Scheme.isoSpec_Spec]
    simp
  have hU₀ : D.cohQ.obj x₀ = Over.mk (Spec.map (CommRingCat.ofHom (algebraMap Γ(S, U.1) k)) ≫ iU) :=
    hx₀.trans (congrArg Over.mk hfac.symm)
  have hfinite : LocallyOfFiniteType (Spec.map (CommRingCat.ofHom (algebraMap Γ(S, U.1) k)) ≫ iU) ∧
      QuasiCompact (Spec.map (CommRingCat.ofHom (algebraMap Γ(S, U.1) k)) ≫ iU) :=
    hfac ▸ ⟨hlft, hqc⟩
  obtain ⟨hp, hT, -⟩ :=
    D.finiteDimensional_tangentSpace_and_infinitesimalAutomorphisms_cohDef iU x₀ hU₀ hlfp
      (IsAffineOpen.isOpenImmersion_fromSpec U.2) hfinite
  exact finiteDimensional_artinianTangentSpace_of_isDeformationCategory_of_presentation
    (D.cohDef iU x₀ hU₀)
    (predeformationCategory iΛ (D.coherentCFG.val.p ⋙ Over.post B.inclusion) x₀
      (hx₀.trans (congrArg Over.mk hbase.symm))) hp hD hT

end AlgebraicGeometry.Space.CoherentSituation

end
