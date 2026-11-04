module

public import StacksFrontier.Algebra.Homology.HomotopyCategory.HomComplexVanishing
public import StacksFrontier.CategoryTheory.Sites.Simplicial.AugmentationPushforwardAcyclic
public import StacksFrontier.CategoryTheory.Sites.Simplicial.AugmentationResolutionQuasiIso
public import StacksFrontier.CategoryTheory.Sites.Simplicial.HomComplexResolution

/-!
# `InverseImageComputesDerivedPushforward` from one vanishing on the base site

Let `S` be a simplicial-site situation (Stacks 09WE) and `a` an augmentation of `S` towards a
site `(D, K)` (Stacks 0D6Z). The resolution of Stacks 0D78 of `a⁻¹𝒢` is a quasi-isomorphism, so
its cone `Z(𝒢)` is an acyclic complex of abelian sheaves on the total site; this module shows
that the predicate
`CategoryTheory.SimplicialSiteSituation.Augmentation.InverseImageComputesDerivedPushforward`
follows from the single statement

`Hom(Z(𝒢), a⁻¹M)` is acyclic for every abelian sheaf `𝒢` on `(D, K)` and every K-injective
complex `M` of abelian sheaves on `(D, K)`,

together with the preservation of K-injectivity by the component inverse images (Stacks 0D88 in
the hypercovering case). Nothing else is assumed: no boundedness, no injectivity of the terms,
and no hypothesis on the coefficients.

## What that statement is

`Hom(Z(𝒢), a⁻¹M)` is the complex whose terms are the groups
`Hom(g_{p!}(a_p⁻¹𝒢), a⁻¹M^q) = Hom(a_p⁻¹𝒢, a_p⁻¹M^q)` together with `Hom(a⁻¹𝒢, a⁻¹M^q)`, so its
acyclicity says that the complex

`… ⟶ a_{1!}a_1⁻¹𝒢 ⟶ a_{0!}a_0⁻¹𝒢 ⟶ 𝒢 ⟶ 0`

of abelian sheaves on `(D, K)` — the image of the resolution of Stacks 0D78 under the left
adjoint of `a⁻¹` — is acyclic, tested against the K-injective complex `M`. That complex is the
Čech resolution of `𝒢` along the hypercovering, and its exactness is the step of the source's
proof of Stacks 0D8G which reads: *since `ℤ_U^#` is a flat sheaf of `ℤ`-modules,
`s(ℤ_{F(K)}^#) ⊗_ℤ ℤ_U^# ⟶ ℤ_U^#` is a quasi-isomorphism*. With `𝒢 = ℤ^#` it is Stacks 01GE,
which this library has as
`CategoryTheory.SimplicialObject.Augmented.quasiIso_freeAbelianSheafResolutionAugmentation`; with
general `𝒢` it is 01GE with coefficients.

The quantifier over `𝒢` can be restricted:
`StacksFrontier/CategoryTheory/Sites/Simplicial/AugmentationResolutionConeFreeYoneda.lean`
re-runs the reduction below with `𝒢` restricted to the free abelian sheaves `ℤ_V^♯` on the
representables — enough, because those detect acyclicity — and at those coefficients 01GE is
`Stacks.CategoryTheory.Hypercovering.quasiIso_freeAbelianSheafResolutionAugmentation_prodConst`
(Stacks 01GE for a hypercovering of a presheaf, multiplied by any presheaf of sets, with no
hypothesis on the multiplier).

## Main definitions

* `CategoryTheory.SimplicialSiteSituation.Augmentation.resolutionCochainAug`: the augmentation of
  the resolution of Stacks 0D78, as a morphism of cochain complexes with the resolution placed in
  non-positive degrees.
* `CategoryTheory.SimplicialSiteSituation.Augmentation.InverseImageAcyclicAgainstResolutionCone`:
  the statement above.

## Main results

* `CategoryTheory.SimplicialSiteSituation.Augmentation.acyclic_mappingCone_resolutionCochainAug`:
  the cone of that augmentation is acyclic.
* `CategoryTheory.SimplicialSiteSituation.Augmentation`
  `.acyclic_coyonedaComplex_mappingCone_of_vanishing`: the Hom complex out of `a⁻¹𝒢` into the cone
  of a K-injective resolution of `a⁻¹I` is acyclic.
* `CategoryTheory.SimplicialSiteSituation.Augmentation`
  `.inverseImageComputesDerivedPushforward_of_vanishing`: **the reduction.**

## Implementation notes

The three moves on Hom complexes are
`CochainComplex.acyclic_homComplex_of_isKInjective`,
`CochainComplex.acyclic_homComplex_mappingCone` and
`CochainComplex.acyclic_homComplex_of_mappingCone`; the last is the one that consumes the cone of
the augmentation of Stacks 0D78, and what it is applied to in the other variable is
`CategoryTheory.SimplicialSiteSituation.Augmentation.acyclic_homComplex_resolution`, the Hom
complex out of the resolution itself.

The route does *not* go through
`CategoryTheory.SimplicialSiteSituation.Augmentation`
`.inverseImageComputesDerivedPushforward_of_acyclic_coyonedaComplex`, whose hypothesis asks for
the Hom-complex acyclicity at *every* acyclic complex with K-injective restrictions. Here the
complex is the cone of a chosen K-injective resolution, and that it is a cone is what the second
move needs; so the cone is built here and the criterion
`.inverseImageComputesDerivedPushforward_of_quasiIso` is applied directly. The K-injectivity of
the restrictions of that cone is proved exactly as it is there.

## References

* [Stacks Project, Tag 0D8G](https://stacks.math.columbia.edu/tag/0D8G)
* [Stacks Project, Tag 0D78](https://stacks.math.columbia.edu/tag/0D78)
* [Stacks Project, Tag 0D88](https://stacks.math.columbia.edu/tag/0D88)
* [Stacks Project, Tag 01GE](https://stacks.math.columbia.edu/tag/01GE)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits

universe u

namespace CategoryTheory.SimplicialSiteSituation.Augmentation

attribute [local instance] HasDerivedCategory.standard

variable (S : SimplicialSiteSituation.{u}) (D : Cat.{u, u}) (K : GrothendieckTopology D)
  (a : Augmentation S D K)

/-- The augmentation of the resolution of Stacks 0D78, as a morphism of cochain complexes with
the resolution placed in non-positive degrees. -/
def resolutionCochainAug (G : Sheaf K Ab.{u}) :
    (resolutionComplex S D K a G).extend ComplexShape.embeddingDownNat ⟶
      (CochainComplex.singleFunctor (Sheaf S.totalTopology Ab.{u}) 0).obj
        ((totalInverseImageAb S D K a).obj G) :=
  CochainComplex.resolutionCochainAugmentation (resolutionComplex S D K a G)
    ((totalInverseImageAb S D K a).obj G) (resolutionChainAugmentation S D K a G)

/-- **The cone of the augmentation of Stacks 0D78 is acyclic**, that augmentation being a
quasi-isomorphism. -/
theorem acyclic_mappingCone_resolutionCochainAug (G : Sheaf K Ab.{u}) :
    (CochainComplex.mappingCone (resolutionCochainAug S D K a G)).Acyclic := by
  have : QuasiIso (resolutionCochainAug S D K a G) := by
    dsimp only [resolutionCochainAug]
    infer_instance
  exact (CochainComplex.KFlatBifunctor.quasiIso_iff_acyclic_mappingCone
    (resolutionCochainAug S D K a G)).mp this

/-- **The vanishing on the base site.** For every abelian sheaf `𝒢` on the
augmentation site and every K-injective complex `M` of abelian sheaves on it, the Hom complex out
of the cone of the augmentation of Stacks 0D78 of `a⁻¹𝒢`, into `a⁻¹M`, is acyclic.

Transposed along the adjunction `a⁻¹ ⊣ a_*` degreewise, this is the acyclicity, tested against
`M`, of the complex `… ⟶ a_{1!}a_1⁻¹𝒢 ⟶ a_{0!}a_0⁻¹𝒢 ⟶ 𝒢 ⟶ 0` on the augmentation site: the
Čech resolution of `𝒢` along the hypercovering. -/
def InverseImageAcyclicAgainstResolutionCone : Prop :=
  ∀ (G : Sheaf K Ab.{u}) (M : CochainComplex (Sheaf K Ab.{u}) ℤ), M.IsKInjective →
    (CochainComplex.HomComplex (CochainComplex.mappingCone (resolutionCochainAug S D K a G))
      (((totalInverseImageAb S D K a).mapHomologicalComplex (ComplexShape.up ℤ)).obj M)).Acyclic

/-- **The Hom complex out of `a⁻¹𝒢` into the cone of a K-injective resolution of `a⁻¹I` is
acyclic**, granted the vanishing of
`CategoryTheory.SimplicialSiteSituation.Augmentation.InverseImageAcyclicAgainstResolutionCone`.

The Hom complex out of the resolution of Stacks 0D78 into that cone is acyclic by
`CategoryTheory.SimplicialSiteSituation.Augmentation.acyclic_homComplex_resolution`, and the Hom
complex out of the cone of the augmentation of that resolution is acyclic because the cone of the
resolution of `a⁻¹I` is one: the Hom complexes into `a⁻¹I` and into the K-injective complex `J`
are both acyclic. -/
theorem acyclic_coyonedaComplex_mappingCone_of_vanishing
    (hgap : InverseImageAcyclicAgainstResolutionCone S D K a) (G : Sheaf K Ab.{u})
    (I : CochainComplex (Sheaf K Ab.{u}) ℤ) (hI : I.IsKInjective)
    {J : CochainComplex (Sheaf S.totalTopology Ab.{u}) ℤ} (hJ : J.IsKInjective)
    (q : (((totalInverseImageAb S D K a).mapHomologicalComplex (ComplexShape.up ℤ)).obj I) ⟶ J)
    (hWac : (CochainComplex.mappingCone q).Acyclic)
    (hWp : ∀ p : SimplexCategory, CochainComplex.IsKInjective
      (((restrictAb S p).mapHomologicalComplex (ComplexShape.up ℤ)).obj
        (CochainComplex.mappingCone q))) :
    (CochainComplex.coyonedaComplex ((totalInverseImageAb S D K a).obj G)
      (CochainComplex.mappingCone q)).Acyclic := by
  have := hJ
  -- the Hom complex out of the cone of the augmentation of Stacks 0D78, into the cone of `q`
  have hcone : (CochainComplex.HomComplex
      (CochainComplex.mappingCone (resolutionCochainAug S D K a G))
      (CochainComplex.mappingCone q)).Acyclic :=
    CochainComplex.acyclic_homComplex_mappingCone _ q (hgap G I hI)
      (CochainComplex.acyclic_homComplex_of_isKInjective _ J
        (acyclic_mappingCone_resolutionCochainAug S D K a G))
  -- the Hom complex out of the resolution itself, into the cone of `q`
  have hres := acyclic_homComplex_resolution S D K a G (CochainComplex.mappingCone q) hWac hWp
  have hsingle := CochainComplex.acyclic_homComplex_of_mappingCone
    (resolutionCochainAug S D K a G) (CochainComplex.mappingCone q) hres hcone
  exact fun i => CochainComplex.exactAt_coyonedaComplex_of_homComplex _ _ i (hsingle i)

/-- **`InverseImageComputesDerivedPushforward` from the one statement on the base site.** For a
K-injective complex `I` of abelian sheaves on `(D, K)`, the inverse image `a⁻¹I` computes
`R a_*`, granted that the component inverse images of a K-injective complex restrict to
K-injective complexes (Stacks 0D88 in the hypercovering case) and granted
`CategoryTheory.SimplicialSiteSituation.Augmentation.InverseImageAcyclicAgainstResolutionCone`. -/
theorem inverseImageComputesDerivedPushforward_of_vanishing
    (hrestr : ∀ (p : SimplexCategory) (I : CochainComplex (Sheaf K Ab.{u}) ℤ),
      I.IsKInjective → CochainComplex.IsKInjective
        (((restrictAb S p).mapHomologicalComplex (ComplexShape.up ℤ)).obj
          (((totalInverseImageAb S D K a).mapHomologicalComplex (ComplexShape.up ℤ)).obj I)))
    (hgap : InverseImageAcyclicAgainstResolutionCone S D K a) :
    InverseImageComputesDerivedPushforward S D K a := by
  refine inverseImageComputesDerivedPushforward_of_quasiIso S D K a fun I hI => ?_
  obtain ⟨J, q, hJ, hq⟩ := exists_kInjective_resolution_total S
    (((totalInverseImageAb S D K a).mapHomologicalComplex (ComplexShape.up ℤ)).obj I)
  refine ⟨J, hJ, q, hq, ?_⟩
  have hWac : (CochainComplex.mappingCone q).Acyclic :=
    (CochainComplex.KFlatBifunctor.quasiIso_iff_acyclic_mappingCone q).mp hq
  have hWp : ∀ p : SimplexCategory, CochainComplex.IsKInjective
      (((restrictAb S p).mapHomologicalComplex (ComplexShape.up ℤ)).obj
        (CochainComplex.mappingCone q)) := by
    intro p
    have h1 := hrestr p I hI
    have h2 : CochainComplex.IsKInjective
        (((restrictAb S p).mapHomologicalComplex (ComplexShape.up ℤ)).obj J) := by
      have := hJ
      exact isKInjective_componentRestriction S p J
    have h3 : CochainComplex.IsKInjective (CochainComplex.mappingCone
        (((restrictAb S p).mapHomologicalComplex (ComplexShape.up ℤ)).map q)) :=
      CochainComplex.isKInjective_mappingCone _
    exact CochainComplex.isKInjective_of_iso
      (CochainComplex.mappingCone.mapHomologicalComplexIso q (restrictAb S p)).symm
  have hac := acyclic_abelianTotalPushforward_of_acyclic_coyonedaComplex S D K a
    (CochainComplex.mappingCone q) fun G =>
      acyclic_coyonedaComplex_mappingCone_of_vanishing S D K a hgap G I hI hJ q hWac hWp
  rw [CochainComplex.KFlatBifunctor.quasiIso_iff_acyclic_mappingCone]
  exact fun i => (hac i).of_iso
    (CochainComplex.mappingCone.mapHomologicalComplexIso q (abelianTotalPushforward S D K a))

end CategoryTheory.SimplicialSiteSituation.Augmentation

end
