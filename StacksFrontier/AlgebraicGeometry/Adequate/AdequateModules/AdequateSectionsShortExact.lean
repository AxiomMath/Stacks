module

public import StacksFrontier.AlgebraicGeometry.Adequate.AdequateModules.AdequateCechExactness
public import StacksFrontier.AlgebraicGeometry.Adequate.AdequateModules.AdequatorVanishing
public import StacksFrontier.AlgebraicGeometry.Adequate.AdequateModules.BigSiteFpqcFromAffineSingletons
public import StacksFrontier.AlgebraicGeometry.Adequate.AdequateModules.TopologyIndependence
public import StacksFrontier.AlgebraicGeometry.Spaces.Coproduct
public import StacksFrontier.AlgebraicGeometry.Topologies.BigSites.OverSliceContinuity
public import StacksFrontier.AlgebraicGeometry.Topologies.StandardCoveringDisjointUnion
public import StacksFrontier.CategoryTheory.Sites.Cohomology.Cech.CoproductRefinement
public import StacksFrontier.CategoryTheory.Sites.Cohomology.Cech.FirstVanishingAndSections
public import StacksFrontier.CategoryTheory.Sites.FunctorialInjectiveEmbeddings

/-!
# The affine sections of a short exact sequence with adequate outer terms

Let `S` be a scheme, `B` a chosen big `τ`-site over `S` and

`0 ⟶ 𝓕₁ ⟶ 𝓕₂ ⟶ 𝓕₃ ⟶ 0`

a short exact sequence of `𝒪`-modules on the site whose outer terms are adequate. The step of
the source's proof of [Stacks, Tag 06VQ] (3) that this module supplies is that the induced
sequence of affine-section functors `F_{𝓕ᵢ, A}` is again short exact, for every affine scheme
`Spec A` over `S` belonging to the site. The middle term is *not* assumed adequate — proving
that it is, which is [Stacks, Tag 06VQ] (3) itself, is what the statement proved here is
consumed for.

The source reads the exactness off the vanishing of `H¹` on affines of [Stacks, Tag 06VM]. The
route taken here is the same mathematics in its Čech form, which avoids derived functors
altogether: [Stacks, Tag 03F8] turns the vanishing of the *first Čech* cohomology of `𝓕₁` on a
cofinal system of coverings of an object into surjectivity of `𝓕₂ ⟶ 𝓕₃` on sections over that
object. Cofinality of the finite affine coverings among the covering sieves of an affine object
is `Stacks.Adequate.BigSite.affineCovCofinal`, and the Čech vanishing on such a covering is
obtained here from [Stacks, Tag 06VL] — `Stacks.Adequate.affineCechExactness_of_isAdequate` —
together with [Stacks, Tag 03FI] part (3).

## Main results

* `Stacks.Adequate.adequateSectionsShortExact` — **the step of [Stacks, Tag 06VQ] (3)**:
  `Stacks.Adequate.AdequateSectionsShortExact` holds for every chosen big site, with no
  hypothesis. It is consumed by `Stacks.Adequate.adequate_isClosedUnderExtensions'` and
  `Stacks.Adequate.adequate_isWeakSerreClass'`, the closure statements at every value
  universe.
* `Stacks.Adequate.BigSite.surjective_sections_of_isAdequate` — the content of the above: the
  sections over an affine object of the site of a short exact sequence of abelian sheaves whose
  first term is adequate are surjective.
* `Stacks.Adequate.BigSite.isZero_cechCohomology_of_finite_affine_covering` —
  **[Stacks, Tag 06VL] read on a finite affine covering**: the positive-degree Čech cohomology
  of an adequate `𝒪`-module vanishes on a finite affine covering of an object of the site, with
  no hypothesis beyond the data of the covering. This is the unconditional form of
  `Stacks.Adequate.BigSite.cechCohomology_isZero_of_isAdequate`, whose two Čech inputs are now
  both available.
* `Stacks.Adequate.BigSite.preservesFiniteProducts_sheaf` — an abelian sheaf on the site carries
  a finite disjoint union to the product of its values, because the extensive topology of the
  site is coarser than its own topology
  (`Stacks.Adequate.BigSite.extensiveTopology_le_topology`, with
  `Stacks.Adequate.BigSite.hasFiniteCoproducts_category` and
  `Stacks.Adequate.BigSite.finitaryExtensive_category`, all in
  `StacksFrontier/AlgebraicGeometry/Adequate/AdequateModules/DisjointUnionCech.lean`).

## Implementation notes

*The typeclass assumptions.* `HasSheafify B.topology AddCommGrpCat.{max u m}`,
`B.topology.WEqualsLocallyBijective AddCommGrpCat.{max u m}` and
`EnoughInjectives (Sheaf B.topology AddCommGrpCat.{max u m})` are instances on every chosen big
site, consequences of its essential smallness at the value universe
(`Stacks.Adequate.BigSite.essentiallySmall_category_max`): they are
`Stacks.Adequate.BigSite.hasSheafify_addCommGrpCat`,
`Stacks.Adequate.BigSite.wEqualsLocallyBijective_addCommGrpCat` and
`Stacks.Adequate.BigSite.enoughInjectives_sheaf_addCommGrpCat`.

*Why the extensive topology appears.* [Stacks, Tag 03FI] part (3) — the identification of the
Čech complex of a finite family with the Čech complex of the single morphism from its disjoint
union — is available abstractly as
`Stacks.CechSite.isIso_cechComplexMap_of_preservesFiniteProducts`, which asks the ambient
category to be finitary extensive and the coefficient presheaf to preserve finite products. For
a chosen big site both are available: the site has finite coproducts and is finitary extensive
(`Stacks.Adequate.BigSite.hasFiniteCoproducts_category`,
`Stacks.Adequate.BigSite.finitaryExtensive_category`), and an abelian sheaf preserves finite
products because the extensive topology of the site is coarser than the site's topology
(`Stacks.Adequate.BigSite.extensiveTopology_le_topology`).

*The derived-functor route.* [Stacks, Tag 06VM] (3) in this library,
`Stacks.Adequate.BigSite.isZero_rightDerived_sections_of_isAdequate`, carries no hypothesis,
and `Stacks.Adequate.shortExact_affineSections_of_isAdequate` reads the same exactness off it,
needing only the first term adequate. The Čech route taken here is independent of it: it needs
neither `EnoughInjectives` nor a choice of derived category.

*Why not the affine-section exactness of [Stacks, Tag 06ZJ].*
`Stacks.Adequate.preservesFiniteColimits_affineSections` is exactness of the affine-section
functor *restricted to the adequate modules*, at the affine base and at `m = u`. It cannot
discharge the statement proved here, which quantifies over short exact sequences of all
`𝒪`-modules with only the outer terms adequate: its whole purpose is to prove adequacy of the
middle term.

## References

* [Stacks Project, Tag 06VQ](https://stacks.math.columbia.edu/tag/06VQ)
* [Stacks Project, Tag 06VM](https://stacks.math.columbia.edu/tag/06VM)
* [Stacks Project, Tag 06VL](https://stacks.math.columbia.edu/tag/06VL)
* [Stacks Project, Tag 03F8](https://stacks.math.columbia.edu/tag/03F8)
* [Stacks Project, Tag 03FI](https://stacks.math.columbia.edu/tag/03FI)
-/

@[expose] public section

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits Opposite Cardinal

universe u m

namespace Stacks.Adequate

/-! ### Finite disjoint unions in a chosen big site -/

/-- The cutoff category of schemes is closed under finite coproducts. -/
private theorem schemeSizeBelow_closedUnderFiniteCoproducts (κ : Cardinal.{u}) (hκ : ℵ₀ < κ)
    (hcof : ℵ₀ < κ.ord.cof) (J : Type) [Finite J] :
    (schemeSizeBelow κ).IsClosedUnderColimitsOfShape (Discrete J) :=
  have := schemeSizeBelow_isClosedUnderColimitsOfShape_discrete hκ hcof
    (ι := ULift.{u} J) (by simp)
  (ObjectProperty.isClosedUnderColimitsOfShape_iff_of_equivalence _
    (Discrete.equivalence (Equiv.ulift.{u} (α := J)))).1 inferInstance

variable {τ : CoveringTopology} {S : Scheme.{u}}

/-- The canonical functor from a chosen big site to all schemes preserves finite
coproducts. -/
private theorem preservesColimitsOfShape_toScheme (B : BigSite τ S) (α : Type) [Finite α] :
    PreservesColimitsOfShape (Discrete α)
      (Over.forget (⟨S, B.base_mem⟩ : SchemeBelow B.cutoff) ⋙
        ObjectProperty.ι (schemeSizeBelow B.cutoff)) :=
  have := schemeSizeBelow_closedUnderFiniteCoproducts B.cutoff B.aleph0_lt_cutoff
    (BigSite.aleph0_lt_cutoff_cof B) α
  inferInstance

/-- **An abelian sheaf on a chosen big site takes finite disjoint unions to products.** The
extensive topology is coarser than the site's topology, so the sheaf is in particular an
extensive sheaf. -/
public theorem BigSite.preservesFiniteProducts_sheaf (B : BigSite τ S)
    (F : Sheaf B.topology AddCommGrpCat.{max u m}) : PreservesFiniteProducts F.obj :=
  let := B.finitaryExtensive_category
  (Presheaf.isSheaf_iff_preservesFiniteProducts F.obj).mp
    (Presheaf.IsSheaf.of_le B.extensiveTopology_le_topology F.property)

/-- **The disjoint union of a finite affine covering of an object of the site is an affine
object of the site, and the induced morphism from it is flat and surjective.** -/
private theorem isAffine_and_flat_and_surjective_sigmaDesc (B : BigSite τ S) {U : B.category}
    {I : Type} [Finite I] (X : I → B.category) [HasCoproduct X] (f : ∀ i, X i ⟶ U)
    (haff : ∀ i, IsAffine (X i).left.obj)
    (hprop : ∀ i, coveringMorphismProperty τ (B.toOver.map (f i)).left)
    (hsurj : ∀ x : U.left.obj, ∃ i, x ∈ Set.range (B.toOver.map (f i)).left) :
    IsAffine (∐ X).left.obj ∧ Flat (B.toOver.map (Sigma.desc f)).left ∧
      Surjective (B.toOver.map (Sigma.desc f)).left := by
  let : PreservesColimitsOfShape (Discrete I) (B.toOver ⋙ Over.forget S) :=
    preservesColimitsOfShape_toScheme B I
  set G : B.category ⥤ Scheme.{u} := B.toOver ⋙ Over.forget S
  let : ∀ i, IsAffine (G.obj (X i)) := haff
  set e : G.obj (∐ X) ≅ ∐ (fun i => G.obj (X i)) := PreservesCoproduct.iso G X
  have hg : G.map (Sigma.desc f) = e.hom ≫ Sigma.desc (fun i => G.map (f i)) :=
    e.inv_comp_eq.mp (sigmaComparison_map_desc G X _ f)
  have : IsZariskiLocalAtSource (@Flat : MorphismProperty Scheme.{u}) :=
    HasRingHomProperty.instIsZariskiLocalAtSource (P := @Flat) (Q := RingHom.Flat)
  have : Flat (Sigma.desc (fun i => G.map (f i))) := IsZariskiLocalAtSource.sigmaDesc fun i =>
    (coveringMorphismProperty_le_flat_inf_locallyOfFinitePresentation τ _ (hprop i)).1
  have : Surjective (Sigma.desc (fun i => G.map (f i))) := by
    refine ⟨fun x => ?_⟩
    obtain ⟨i, y, hy⟩ := hsurj x
    exact ⟨Sigma.ι (fun i => G.obj (X i)) i y, by rwa [← Scheme.Hom.comp_apply, Sigma.ι_desc]⟩
  refine ⟨?_, ?_, ?_⟩
  · show IsAffine (G.obj (∐ X))
    exact IsAffine.of_isIso e.hom
  · show Flat (G.map (Sigma.desc f))
    rw [hg]
    infer_instance
  · show Surjective (G.map (Sigma.desc f))
    rw [hg]
    infer_instance

/-! ### Čech vanishing on a finite affine covering -/

/-- **The positive-degree Čech cohomology of an adequate `𝒪`-module vanishes on a finite
affine covering of an object of the site**, with no hypothesis beyond the data of the
covering. The covering is replaced by the one-member family given by the morphism from the
disjoint union of its members, which is a flat surjective morphism of affine objects of the
site; [Stacks, Tag 06VL] kills the Čech cohomology of that family, and
[Stacks, Tag 03FI] part (3) identifies the two Čech complexes, the identification being
available because an abelian sheaf on the site takes finite disjoint unions to products. -/
public theorem BigSite.isZero_cechCohomology_of_finite_affine_covering (B : BigSite τ S)
    (F : SheafOfModules.{max u m} B.structureSheaf) (hF : IsAdequate B F) {U : B.category}
    (E : PreZeroHypercover.{0} U) (hU : IsAffine U.left.obj) (hfin : Finite E.I₀)
    (haff : ∀ i, IsAffine (E.X i).left.obj)
    (hprop : ∀ i, coveringMorphismProperty τ (B.toOver.map (E.f i)).left)
    (hsurj : ∀ x : U.left.obj, ∃ i, x ∈ Set.range (B.toOver.map (E.f i)).left)
    (k : ℕ) (hk : 0 < k) :
    letI : HasFiniteLimits B.category := B.hasFiniteLimits_category
    IsZero (Stacks.CechSite.cechCohomology E
      ((SheafOfModules.toSheaf B.structureSheaf).obj F).obj k) := by
  let : HasFiniteLimits B.category := B.hasFiniteLimits_category
  let := hfin
  let := B.hasFiniteCoproducts_category
  let := B.finitaryExtensive_category
  let := B.preservesFiniteProducts_sheaf.{u, m}
    ((SheafOfModules.toSheaf B.structureSheaf).obj F)
  obtain ⟨haffsum, hflat, hsurjsum⟩ :=
    isAffine_and_flat_and_surjective_sigmaDesc B E.X E.f haff hprop hsurj
  let := hflat
  let := hsurjsum
  refine (affineCechExactness_of_isAdequate.{u, m} B F hF (Sigma.desc E.f) hU haffsum
    hflat hsurjsum k hk).of_iso ?_
  exact (HomologicalComplex.homologyMapIso
    (@asIso _ _ _ _ _ (Stacks.CechSite.isIso_cechComplexMap_of_preservesFiniteProducts E
      ((SheafOfModules.toSheaf B.structureSheaf).obj F).obj)) k).symm

/-! ### Surjectivity of the sections of a short exact sequence on affines -/

/-- **The sections over an affine object of a short exact sequence of abelian sheaves whose
first term is adequate are surjective.** This is [Stacks, Tag 03F8] applied to the collection
of finite affine coverings of the object, which is cofinal among its covering sieves by
`Stacks.Adequate.BigSite.affineCovCofinal` and on which the first Čech cohomology of an
adequate module vanishes by
`Stacks.Adequate.BigSite.isZero_cechCohomology_of_finite_affine_covering`. -/
public theorem BigSite.surjective_sections_of_isAdequate (B : BigSite τ S)
    (T : ShortComplex (SheafOfModules.{max u m} B.structureSheaf))
    (hT : haveI := B.hasSheafify_addCommGrpCat.{u, m}
      haveI := B.wEqualsLocallyBijective_addCommGrpCat.{u, m}
      (T.map (SheafOfModules.toSheaf B.structureSheaf)).ShortExact)
    (h₁ : IsAdequate B T.X₁) (U : B.category) (hU : IsAffine U.left.obj) :
    Function.Surjective (T.g.val.app (op U)) := by
  let : HasFiniteLimits B.category := B.hasFiniteLimits_category
  let := B.hasSheafify_addCommGrpCat.{u, m}
  let := B.wEqualsLocallyBijective_addCommGrpCat.{u, m}
  refine Stacks.CechSite.surjective_on_sections_of_isZero_cechCohomology.{0, u, u + 1, max u m}
    B.topology _ hT U
    { E : PreZeroHypercover.{0} U | ∃ h : E.sieve₀ ∈ B.topology U,
        (⟨E, h⟩ : { E : PreZeroHypercover.{0} U // E.sieve₀ ∈ B.topology U }) ∈
          B.affineCov U }
    (fun E hE => hE.choose) ?_ (fun _ _ _ _ => inferInstance) ?_
  · intro R hR
    obtain ⟨E, hE, hle⟩ := B.affineCovCofinal U hU R hR
    exact ⟨E.1, ⟨E.2, hE⟩, hle⟩
  · rintro E ⟨hmem, hcov⟩
    exact B.isZero_cechCohomology_of_finite_affine_covering.{u, m} T.X₁ h₁ E hU hcov.2.1
      hcov.2.2.1 hcov.2.2.2.1 hcov.2.2.2.2 1 one_pos

/-! ### The affine sections of a short exact sequence with adequate outer terms -/

/-- **The step of [Stacks, Tag 06VQ] (3), with no hypothesis.** For every short exact sequence
of `𝒪`-modules on a chosen big `τ`-site over `S` whose outer terms are adequate, and every
affine scheme `Spec A` over `S` belonging to the site, the induced sequence of affine-section
functors is short exact. The middle term is not assumed adequate; proving that it is, which is
[Stacks, Tag 06VQ] (3), is what this statement is consumed for, by
`Stacks.Adequate.adequate_isClosedUnderExtensions'`.

The affine-section functor is left exact with no hypothesis
(`Stacks.Adequate.preservesFiniteLimits_affineSectionsFunctor`), which gives the monomorphism
and the exactness in the middle; the epimorphism is
`Stacks.Adequate.BigSite.surjective_sections_of_isAdequate` applied at each algebra of the site,
whose spectrum is an affine object. -/
public theorem adequateSectionsShortExact (B : BigSite τ S) :
    AdequateSectionsShortExact.{u, m} B := by
  let := B.hasSheafify_addCommGrpCat.{u, m}
  let := B.wEqualsLocallyBijective_addCommGrpCat.{u, m}
  intro T hT h₁ _h₃ A f _hA
  have hEpi : Epi ((affineSectionsFunctor.{u, max u m} B A f).map T.g) :=
    PresheafOfModules.epi_of_surjective fun X => B.surjective_sections_of_isAdequate.{u, m} T
      ((ShortExact.shortExact_map_iff (SheafOfModules.toSheaf B.structureSheaf)).2 hT) h₁
      ((affineSpecOver B A f).obj X.unop) (inferInstanceAs (IsAffine (Spec _)))
  have hexact := (Functor.preservesFiniteLimits_iff_forall_exact_map_and_mono
    (affineSectionsFunctor.{u, max u m} B A f)).1 inferInstance T hT
  exact ShortComplex.ShortExact.mk' hexact.1 hexact.2 hEpi

end Stacks.Adequate

end

