module

public import StacksFrontier.CategoryTheory.Sites.AbelianSheafFreeYonedaAcyclic
public import StacksFrontier.CategoryTheory.Sites.Simplicial.AugmentationResolutionConeLowerShriek

/-!
# The one vanishing on the base site, needed only at the free abelian sheaves on representables

Let `S` be a simplicial-site situation (Stacks 09WE) and `a` an augmentation of `S` towards a
site `(D, K)` (Stacks 0D6Z). The statement
`CategoryTheory.SimplicialSiteSituation.Augmentation.InverseImageAcyclicAgainstResolutionCone`,
which is the one input of
`CategoryTheory.SimplicialSiteSituation.Augmentation.InverseImageComputesDerivedPushforward` left
by `.inverseImageComputesDerivedPushforward_of_vanishing`, quantifies over *every* abelian sheaf
`𝒢` on `(D, K)`. It need not. The quantifier enters only through
`.acyclic_abelianTotalPushforward_of_acyclic_coyonedaComplex`, where it detects acyclicity of a
complex of abelian sheaves by the Hom complexes out of objects; and for abelian sheaves the free
abelian sheaves `ℤ_V^♯` on the representables already detect acyclicity, by
`CategoryTheory.Sheaf.acyclic_of_acyclic_coyonedaComplex_freeYoneda`.

This module therefore re-runs the reduction with `𝒢` restricted to the sheaves `ℤ_V^♯`, `V` an
object of `(D, K)`. That matters because `ℤ_V^♯` is the one coefficient case in which the Čech
resolution of the hypercovering is again a complex of free abelian sheaves on presheaves of
sets — `ℤ_{K_p}^♯ ⊗ ℤ_V^♯ = ℤ_{K_p × h_V}^♯` — so that Stacks 01GE applies to it directly,
base-changed along `h_V`, rather than being needed with general coefficients.

## Main definitions

* `CategoryTheory.SimplicialSiteSituation.Augmentation`
  `.InverseImageAcyclicAgainstResolutionConeFreeYoneda`: the restricted statement.

## Main results

* `CategoryTheory.SimplicialSiteSituation.Augmentation`
  `.acyclic_abelianTotalPushforward_of_acyclic_coyonedaComplex_freeYoneda`: the direct image of a
  complex along the total augmentation is acyclic as soon as the Hom complexes out of the inverse
  images of the `ℤ_V^♯` are.
* `CategoryTheory.SimplicialSiteSituation.Augmentation`
  `.inverseImageComputesDerivedPushforward_of_vanishing_freeYoneda`: **the reduction, from the
  restricted statement.**
* `CategoryTheory.SimplicialSiteSituation.Augmentation`
  `.inverseImageAcyclicAgainstResolutionConeFreeYoneda_of_quasiIso_lowerShriek`: the restricted
  statement from the restricted lower-shriek quasi-isomorphism.

## Implementation notes

The two intermediate steps of the unrestricted chain,
`.acyclic_coyonedaComplex_mappingCone_of_vanishing` and
`.inverseImageAcyclicAgainstResolutionCone_of_acyclic_lowerShriek`, use their hypothesis at a
single abelian sheaf at a time; they are repeated here in that single-sheaf form,
`.acyclic_coyonedaComplex_mappingCone_of_acyclic_homComplex` and
`.acyclic_homComplex_mappingCone_resolutionCochainAug_of_quasiIso_lowerShriek`, which is what lets
the restricted quantifier be carried through. Nothing else in the chain sees the quantifier.

## References

* [Stacks Project, Tag 0D8G](https://stacks.math.columbia.edu/tag/0D8G)
* [Stacks Project, Tag 0D78](https://stacks.math.columbia.edu/tag/0D78)
* [Stacks Project, Tag 0D88](https://stacks.math.columbia.edu/tag/0D88)
* [Stacks Project, Tag 01GE](https://stacks.math.columbia.edu/tag/01GE)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits Opposite Stacks.Cohomology.CohomologyPresheaf

universe u

namespace CategoryTheory.SimplicialSiteSituation.Augmentation

attribute [local instance] HasDerivedCategory.standard

variable (S : SimplicialSiteSituation.{u}) (D : Cat.{u, u}) (K : GrothendieckTopology D)
  (a : Augmentation S D K)

/-- A functor carries a morphism to a quasi-isomorphism iff it carries its cone to an acyclic
complex. -/
private theorem quasiIso_map_iff_acyclic_obj_mappingCone
    {C E : Type*} [Category C] [Category E] [Abelian C] [Abelian E] (F : C ⥤ E) [F.Additive]
    {X Y : CochainComplex C ℤ} (g : X ⟶ Y) :
    QuasiIso ((F.mapHomologicalComplex (ComplexShape.up ℤ)).map g) ↔
      ((F.mapHomologicalComplex (ComplexShape.up ℤ)).obj
        (CochainComplex.mappingCone g)).Acyclic := by
  rw [CochainComplex.KFlatBifunctor.quasiIso_iff_acyclic_mappingCone]
  exact ⟨fun h i => (h i).of_iso (CochainComplex.mappingCone.mapHomologicalComplexIso g F).symm,
    fun h i => (h i).of_iso (CochainComplex.mappingCone.mapHomologicalComplexIso g F)⟩

/-- **The direct image of a complex along the total augmentation is acyclic as soon as the Hom
complexes out of the inverse images of the free abelian sheaves on the representables are.** This
is `.acyclic_abelianTotalPushforward_of_acyclic_coyonedaComplex` with the abelian sheaf restricted
to the sheaves `ℤ_V^♯`, which already detect acyclicity. -/
theorem acyclic_abelianTotalPushforward_of_acyclic_coyonedaComplex_freeYoneda
    (W : CochainComplex (Sheaf S.totalTopology Ab.{u}) ℤ)
    (h : ∀ V : D, (CochainComplex.coyonedaComplex ((totalInverseImageAb S D K a).obj
      (freeYonedaSheaf K V)) W).Acyclic) :
    (((abelianTotalPushforward S D K a).mapHomologicalComplex
      (ComplexShape.up ℤ)).obj W).Acyclic :=
  Sheaf.acyclic_of_acyclic_coyonedaComplex_freeYoneda K _ fun V i =>
    (h V i).of_iso (CochainComplex.coyonedaComplexAdjIso (abelianTotalAdjunction S D K a)
      (freeYonedaSheaf K V) W)

/-- **The Hom complex out of `a⁻¹𝒢` into the cone of a K-injective resolution of `a⁻¹I` is
acyclic**, granted the vanishing at the single abelian sheaf `𝒢`. This is
`.acyclic_coyonedaComplex_mappingCone_of_vanishing` with its hypothesis taken at the one `𝒢` and
the one `I` it is used at. -/
theorem acyclic_coyonedaComplex_mappingCone_of_acyclic_homComplex (G : Sheaf K Ab.{u})
    (I : CochainComplex (Sheaf K Ab.{u}) ℤ) (_hI : I.IsKInjective)
    {J : CochainComplex (Sheaf S.totalTopology Ab.{u}) ℤ} (hJ : J.IsKInjective)
    (q : (((totalInverseImageAb S D K a).mapHomologicalComplex (ComplexShape.up ℤ)).obj I) ⟶ J)
    (hWac : (CochainComplex.mappingCone q).Acyclic)
    (hWp : ∀ p : SimplexCategory, CochainComplex.IsKInjective
      (((restrictAb S p).mapHomologicalComplex (ComplexShape.up ℤ)).obj
        (CochainComplex.mappingCone q)))
    (hgapG : (CochainComplex.HomComplex
      (CochainComplex.mappingCone (resolutionCochainAug S D K a G))
      (((totalInverseImageAb S D K a).mapHomologicalComplex (ComplexShape.up ℤ)).obj I)).Acyclic) :
    (CochainComplex.coyonedaComplex ((totalInverseImageAb S D K a).obj G)
      (CochainComplex.mappingCone q)).Acyclic := by
  have := hJ
  -- the Hom complex out of the cone of the augmentation of Stacks 0D78, into the cone of `q`
  have hcone : (CochainComplex.HomComplex
      (CochainComplex.mappingCone (resolutionCochainAug S D K a G))
      (CochainComplex.mappingCone q)).Acyclic :=
    CochainComplex.acyclic_homComplex_mappingCone _ q hgapG
      (CochainComplex.acyclic_homComplex_of_isKInjective _ J
        (acyclic_mappingCone_resolutionCochainAug S D K a G))
  -- the Hom complex out of the resolution itself, into the cone of `q`
  have hres := acyclic_homComplex_resolution S D K a G (CochainComplex.mappingCone q) hWac hWp
  have hsingle := CochainComplex.acyclic_homComplex_of_mappingCone
    (resolutionCochainAug S D K a G) (CochainComplex.mappingCone q) hres hcone
  exact fun i => CochainComplex.exactAt_coyonedaComplex_of_homComplex _ _ i (hsingle i)

/-- **The one statement this library does not have, needed only at the free abelian sheaves on
the representables.** For every object `V` of the augmentation site and every K-injective complex
`M` of abelian sheaves on it, the Hom complex out of the cone of the augmentation of
Stacks 0D78 of `a⁻¹ℤ_V^♯`, into `a⁻¹M`, is acyclic.

This is
`CategoryTheory.SimplicialSiteSituation.Augmentation.InverseImageAcyclicAgainstResolutionCone`
with the abelian sheaf `𝒢` restricted to the sheaves `ℤ_V^♯`; it is a weaker statement and it
suffices. -/
def InverseImageAcyclicAgainstResolutionConeFreeYoneda : Prop :=
  ∀ (V : D) (M : CochainComplex (Sheaf K Ab.{u}) ℤ), M.IsKInjective →
    (CochainComplex.HomComplex (CochainComplex.mappingCone
        (resolutionCochainAug S D K a (freeYonedaSheaf K V)))
      (((totalInverseImageAb S D K a).mapHomologicalComplex (ComplexShape.up ℤ)).obj M)).Acyclic

/-- **`InverseImageComputesDerivedPushforward` from the one statement on the base site, taken
only at the free abelian sheaves on the representables.** This is
`.inverseImageComputesDerivedPushforward_of_vanishing` with the weaker hypothesis
`InverseImageAcyclicAgainstResolutionConeFreeYoneda` in place of
`InverseImageAcyclicAgainstResolutionCone`.

The first hypothesis is that `a⁻¹` of a K-injective complex restricts to a K-injective complex on
every component; for the simplicial site of a hypercovering it is Stacks 0D88. -/
theorem inverseImageComputesDerivedPushforward_of_vanishing_freeYoneda
    (hrestr : ∀ (p : SimplexCategory) (I : CochainComplex (Sheaf K Ab.{u}) ℤ),
      I.IsKInjective → CochainComplex.IsKInjective
        (((restrictAb S p).mapHomologicalComplex (ComplexShape.up ℤ)).obj
          (((totalInverseImageAb S D K a).mapHomologicalComplex (ComplexShape.up ℤ)).obj I)))
    (hgap : InverseImageAcyclicAgainstResolutionConeFreeYoneda S D K a) :
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
  have hac := acyclic_abelianTotalPushforward_of_acyclic_coyonedaComplex_freeYoneda S D K a
    (CochainComplex.mappingCone q) fun V =>
      acyclic_coyonedaComplex_mappingCone_of_acyclic_homComplex S D K a _ I hI hJ q hWac hWp
        (hgap V I hI)
  exact (quasiIso_map_iff_acyclic_obj_mappingCone _ q).2 hac

/-- **The vanishing at one abelian sheaf from one quasi-isomorphism on the base site.** Granted a
left adjoint `a_!` of the inverse image `a⁻¹` on abelian sheaves, the Hom complex out of the cone
of the augmentation of Stacks 0D78 of `a⁻¹𝒢` into `a⁻¹M` is acyclic as soon as `a_!` carries that
augmentation to a quasi-isomorphism: the Hom complex out of the cone is the Hom complex out of its
`a_!`-image, and `M` is K-injective.

This is the per-sheaf core of
`.inverseImageAcyclicAgainstResolutionCone_of_quasiIso_lowerShriek`. -/
theorem acyclic_homComplex_mappingCone_resolutionCochainAug_of_quasiIso_lowerShriek
    {L : Sheaf S.totalTopology Ab.{u} ⥤ Sheaf K Ab.{u}}
    (adj : L ⊣ totalInverseImageAb S D K a) [L.Additive] (G : Sheaf K Ab.{u})
    (h : QuasiIso ((L.mapHomologicalComplex (ComplexShape.up ℤ)).map
      (resolutionCochainAug S D K a G)))
    (M : CochainComplex (Sheaf K Ab.{u}) ℤ) (hM : M.IsKInjective) :
    (CochainComplex.HomComplex (CochainComplex.mappingCone (resolutionCochainAug S D K a G))
        (((totalInverseImageAb S D K a).mapHomologicalComplex
          (ComplexShape.up ℤ)).obj M)).Acyclic := by
  have := adj.right_adjoint_additive
  have := hM
  have hLac := (quasiIso_map_iff_acyclic_obj_mappingCone L _).1 h
  intro i
  exact (CochainComplex.acyclic_homComplex_of_isKInjective _ M hLac i).of_iso
    (CochainComplex.homComplexAdjIso adj _ M)

/-- **The restricted vanishing on the base site from one quasi-isomorphism per object of the
site.** Granted a left adjoint `a_!` of the inverse image `a⁻¹` on abelian sheaves, the statement
`InverseImageAcyclicAgainstResolutionConeFreeYoneda` follows from the statement that `a_!` carries
the augmentation of the resolution of Stacks 0D78 of `a⁻¹ℤ_V^♯` to a quasi-isomorphism, for every
object `V` of the augmentation site. -/
theorem inverseImageAcyclicAgainstResolutionConeFreeYoneda_of_quasiIso_lowerShriek
    {L : Sheaf S.totalTopology Ab.{u} ⥤ Sheaf K Ab.{u}}
    (adj : L ⊣ totalInverseImageAb S D K a) [L.Additive]
    (h : ∀ V : D, QuasiIso ((L.mapHomologicalComplex (ComplexShape.up ℤ)).map
      (resolutionCochainAug S D K a (freeYonedaSheaf K V)))) :
    InverseImageAcyclicAgainstResolutionConeFreeYoneda S D K a :=
  fun V M hM => acyclic_homComplex_mappingCone_resolutionCochainAug_of_quasiIso_lowerShriek
    S D K a adj _ (h V) M hM

end CategoryTheory.SimplicialSiteSituation.Augmentation

end
