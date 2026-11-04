module

public import StacksFrontier.Algebra.Homology.HomotopyCategory.HomComplexAdjunction
public import StacksFrontier.CategoryTheory.Sites.Simplicial.AugmentationResolutionConeVanishing

/-!
# The vanishing on the base site from a lower shriek along the augmentation

Let `S` be a simplicial-site situation (Stacks 09WE) and `a` an augmentation of `S` towards a
site `(D, K)` (Stacks 0D6Z). The statement

`CategoryTheory.SimplicialSiteSituation.Augmentation.InverseImageAcyclicAgainstResolutionCone`

speaks about Hom complexes *on the total site*, into the inverse image `a⁻¹M` of a K-injective
complex `M`; and `a⁻¹M` is not K-injective there, which is why the statement is not a formality.
This module removes the total site from it. Suppose the inverse image `a⁻¹` on abelian sheaves
has a left adjoint `a_!` — for the simplicial site of a simplicial semi-representable object this
is Stacks 09WM, part (2), namely
`CategoryTheory.SimplicialSemiRepresentable.augmentationAbelianLowerShriekAdjunction`. Then

`Hom(Z(𝒢), a⁻¹M) ≅ Hom(a_!Z(𝒢), M)`

degreewise and compatibly with the differentials, by `CochainComplex.homComplexAdjIso`; the
right-hand side is a Hom complex on `(D, K)` into a K-injective complex, so it is acyclic as soon
as `a_!Z(𝒢)` is. So the whole statement follows from

**`a_!` carries the augmentation of the resolution of Stacks 0D78 to a quasi-isomorphism**,

a statement about complexes of abelian sheaves on the base site alone: no Hom complexes, no
K-injectivity, and no complex on the total site. Transposed along `a_! ⊣ a⁻¹`, the image
`a_!(g_{p!}a_p⁻¹𝒢)` is `a_{p!}a_p⁻¹𝒢`, so the hypothesis says that

`… ⟶ a_{1!}a_1⁻¹𝒢 ⟶ a_{0!}a_0⁻¹𝒢 ⟶ a_!a⁻¹𝒢 ⟶ 0`

is exact — the Čech resolution of `𝒢` along the hypercovering, with `a_!a⁻¹𝒢` in place of `𝒢`
(the two agree when the counit is invertible, and in any case `a_!a⁻¹𝒢` is the degree-zero
homology of the Čech complex because `a_!` is right exact). That is the step of the source's
proof of Stacks 0D8G which reads: *since `ℤ_U^#` is a flat sheaf of `ℤ`-modules,
`s(ℤ_{F(K)}^#) ⊗_ℤ ℤ_U^# ⟶ ℤ_U^#` is a quasi-isomorphism*, i.e. Stacks 01GE with coefficients.

## Main results

* `CategoryTheory.SimplicialSiteSituation.Augmentation`
  `.inverseImageAcyclicAgainstResolutionCone_of_quasiIso_lowerShriek`: **the reduction.**
* `CategoryTheory.SimplicialSiteSituation.Augmentation`
  `.inverseImageAcyclicAgainstResolutionCone_of_acyclic_lowerShriek`: the same with the
  hypothesis phrased as acyclicity of the `a_!`-image of the cone.

## Implementation notes

The left adjoint is a hypothesis rather than a construction: a general augmentation of a
simplicial-site situation has no `a_!`, the inverse image along it being only an inverse image of
a morphism of topoi, whereas the inverse image along the augmentation of a simplicial
semi-representable object is restriction along the localization functor of the total site and so
has one. Taking the adjunction as data keeps this module free of the semi-representable
hypotheses and lets a caller supply whichever adjunction it has.

Additivity of `a_!` is an instance argument and additivity of `a⁻¹` is then
`CategoryTheory.Adjunction.right_adjoint_additive`, so no additivity instance for the inverse
image of a morphism of topoi is needed.

## References

* [Stacks Project, Tag 0D8G](https://stacks.math.columbia.edu/tag/0D8G)
* [Stacks Project, Tag 0D78](https://stacks.math.columbia.edu/tag/0D78)
* [Stacks Project, Tag 09WM](https://stacks.math.columbia.edu/tag/09WM)
* [Stacks Project, Tag 01GE](https://stacks.math.columbia.edu/tag/01GE)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits

universe u

namespace CategoryTheory.SimplicialSiteSituation.Augmentation

attribute [local instance] HasDerivedCategory.standard

variable (S : SimplicialSiteSituation.{u}) (D : Cat.{u, u}) (K : GrothendieckTopology D)
  (a : Augmentation S D K)

/-- **The vanishing on the base site from acyclicity of the `a_!`-image of the cone.** Granted a
left adjoint `a_!` of the inverse image `a⁻¹` on abelian sheaves, the statement
`CategoryTheory.SimplicialSiteSituation.Augmentation.InverseImageAcyclicAgainstResolutionCone`
follows from acyclicity of the image under `a_!` of the cone of the augmentation of the
resolution of Stacks 0D78.

The Hom complex out of that cone into `a⁻¹M` is the Hom complex out of its `a_!`-image into `M`,
and `M` is K-injective. -/
theorem inverseImageAcyclicAgainstResolutionCone_of_acyclic_lowerShriek
    {L : Sheaf S.totalTopology Ab.{u} ⥤ Sheaf K Ab.{u}}
    (adj : L ⊣ totalInverseImageAb S D K a) [L.Additive]
    (h : ∀ G : Sheaf K Ab.{u}, ((L.mapHomologicalComplex (ComplexShape.up ℤ)).obj
      (CochainComplex.mappingCone (resolutionCochainAug S D K a G))).Acyclic) :
    InverseImageAcyclicAgainstResolutionCone S D K a := by
  have := adj.right_adjoint_additive
  intro G M hM
  have := hM
  intro i
  exact (CochainComplex.acyclic_homComplex_of_isKInjective _ M (h G) i).of_iso
    (CochainComplex.homComplexAdjIso adj _ M)

/-- **The vanishing on the base site from one quasi-isomorphism on it.** Granted a left adjoint
`a_!` of the inverse image `a⁻¹` on abelian sheaves, the statement
`CategoryTheory.SimplicialSiteSituation.Augmentation.InverseImageAcyclicAgainstResolutionCone`
follows from the single statement that `a_!` carries the augmentation of the resolution of
Stacks 0D78 to a quasi-isomorphism, that is that

`… ⟶ a_{1!}a_1⁻¹𝒢 ⟶ a_{0!}a_0⁻¹𝒢 ⟶ a_!a⁻¹𝒢 ⟶ 0`

is exact — the Čech resolution of the hypercovering, which is Stacks 01GE with coefficients. -/
theorem inverseImageAcyclicAgainstResolutionCone_of_quasiIso_lowerShriek
    {L : Sheaf S.totalTopology Ab.{u} ⥤ Sheaf K Ab.{u}}
    (adj : L ⊣ totalInverseImageAb S D K a) [L.Additive]
    (h : ∀ G : Sheaf K Ab.{u}, QuasiIso ((L.mapHomologicalComplex (ComplexShape.up ℤ)).map
      (resolutionCochainAug S D K a G))) :
    InverseImageAcyclicAgainstResolutionCone S D K a :=
  inverseImageAcyclicAgainstResolutionCone_of_acyclic_lowerShriek S D K a adj fun G i =>
    (((CochainComplex.KFlatBifunctor.quasiIso_iff_acyclic_mappingCone _).mp (h G)) i).of_iso
      (CochainComplex.mappingCone.mapHomologicalComplexIso
        (resolutionCochainAug S D K a G) L).symm

end CategoryTheory.SimplicialSiteSituation.Augmentation

end
