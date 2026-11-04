module

public import StacksFrontier.AlgebraicGeometry.Adequate.AdequateModules.AdequateCechExactness
public import StacksFrontier.AlgebraicGeometry.Adequate.AdequateModules.AffineCoveringCofinality
public import StacksFrontier.AlgebraicGeometry.Adequate.AdequateModules.DisjointUnionCech
public import StacksFrontier.CategoryTheory.Sites.FunctorialInjectiveEmbeddings

/-!
# The higher cohomology of an adequate module vanishes on affine objects

Let `S` be a scheme and let `𝓕` be an adequate `𝒪`-module on a chosen big `τ`-site
`(Sch/S)_τ` over `S`, for `τ` any of the five topologies `Zar`, `étale`, `smooth`, `syntomic`,
`fppf`. Then `H^q(U, 𝓕) = 0` for every `q > 0` and every affine scheme `U` over `S` belonging to
the site. This is **[Stacks, Tag 06VM] (3)**, with no hypothesis.

## Main results

* `Stacks.Adequate.BigSite.hasSheafify_addCommGrpCat`,
  `Stacks.Adequate.BigSite.wEqualsLocallyBijective_addCommGrpCat` and
  `Stacks.Adequate.BigSite.enoughInjectives_sheaf_addCommGrpCat` — abelian sheaves on a chosen
  big site, at every coefficient universe above the universe of its schemes, admit
  sheafification, whose weak equivalences are the locally bijective maps, and have enough
  injectives. Both are consequences of the essential smallness
  of the site, [Stacks, Tag 000J], and the second is [Stacks, Tag 01DP].
* `Stacks.Adequate.BigSite.cechCohomology_isZero_of_isAdequate` — the positive-degree Čech
  cohomology of an adequate `𝒪`-module vanishes on a finite affine covering of an affine object
  of the site.
* `Stacks.Adequate.BigSite.isZero_rightDerived_sections_of_isAdequate` —
  **[Stacks, Tag 06VM] (3)**.

## Implementation notes

The proof is the source's: the Čech criterion of [Stacks, Tag 03F9], in the form
`Stacks.Adequate.cechCriterion_of_essentiallySmall`, applied to the affine objects of the site
and to the finite affine `τ`-coverings `Stacks.Adequate.BigSite.affineCov` of those objects. Its
three inputs are now all theorems:

* cofinality of the finite affine coverings, [Stacks, Tag 03XA], is
  `Stacks.Adequate.BigSite.affineCovCofinal`;
* the replacement of a finite covering `{Uᵢ → U}` by the one-member family `{∐ Uᵢ → U}`,
  [Stacks, Tag 03FI] (3), is `Stacks.Adequate.BigSite.coproductCechComparison`;
* the vanishing of the higher Čech cohomology of an adequate module along a flat surjective
  morphism of affines, [Stacks, Tag 06VL], is
  `Stacks.Adequate.affineCechExactness_of_isAdequate`.

Cohomology over `U` is the right derived functor of sections over `U` on abelian sheaves on the
site, applied to the abelian sheaf underlying `𝓕`; this is the source's definition of
`H^q(U, 𝓕)`. The instances it needs — sheafification and enough injectives for abelian sheaves on
the site — are proved here rather than assumed.

## References

* [Stacks Project, Tag 06VM](https://stacks.math.columbia.edu/tag/06VM)
* [Stacks Project, Tag 03F9](https://stacks.math.columbia.edu/tag/03F9)
* [Stacks Project, Tag 03FI](https://stacks.math.columbia.edu/tag/03FI)
* [Stacks Project, Tag 06VL](https://stacks.math.columbia.edu/tag/06VL)
* [Stacks Project, Tag 03XA](https://stacks.math.columbia.edu/tag/03XA)
* [Stacks Project, Tag 01DP](https://stacks.math.columbia.edu/tag/01DP)
-/

@[expose] public section

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits Opposite

universe u m

namespace Stacks.Adequate

variable {τ : CoveringTopology} {S : Scheme.{u}}

/-! ### Sheafification and injectives on a chosen big site -/

/-- A chosen big site is essentially small at every universe above the universe of its
schemes. -/
public theorem BigSite.essentiallySmall_category_max (B : BigSite τ S) :
    EssentiallySmall.{max u m} B.category := by
  have := B.essentiallySmall_category
  exact (essentiallySmall_iff _).2 ⟨small_lift _, inferInstance⟩

/-- **Abelian presheaves on a chosen big site admit sheafification**, at every coefficient
universe above the universe of its schemes: the site is essentially small. -/
public instance BigSite.hasSheafify_addCommGrpCat (B : BigSite τ S) :
    HasSheafify B.topology AddCommGrpCat.{max u m} :=
  have := B.essentiallySmall_category_max.{u, m}
  hasSheafifyEssentiallySmallSite _ _

/-- **Sheafification of abelian presheaves on a chosen big site inverts exactly the locally
bijective maps**, at every coefficient universe above the universe of its schemes: this holds on
a small model of the site and transports along the dense inclusion of that model. -/
public instance BigSite.wEqualsLocallyBijective_addCommGrpCat (B : BigSite τ S) :
    B.topology.WEqualsLocallyBijective AddCommGrpCat.{max u m} :=
  have := B.essentiallySmall_category_max.{u, m}
  GrothendieckTopology.WEqualsLocallyBijective.ofEssentiallySmall.{u, _, u + 1, _, max u m}
    B.topology

/-- **Abelian sheaves on a chosen big site have enough injectives**, at every coefficient
universe above the universe of its schemes. This is [Stacks, Tag 01DP] on the site, which is
essentially small. -/
public instance BigSite.enoughInjectives_sheaf_addCommGrpCat (B : BigSite τ S) :
    EnoughInjectives (Sheaf B.topology AddCommGrpCat.{max u m}) :=
  have := B.essentiallySmall_category_max.{u, m}
  Sheaf.enoughInjectives_addCommGrpCat B.topology

/-! ### Čech vanishing on a finite affine covering -/

/-- **The positive-degree Čech cohomology of an adequate `𝒪`-module vanishes on a finite affine
covering of an affine object of the site.** This is the hypothesis `hCech` of
[Stacks, Tag 03F9] at the finite affine coverings. The covering is replaced by the one-member
family given by the morphism from the disjoint union of its members, which is a surjective flat
morphism of affine objects ([Stacks, Tag 03FI] (3)), and [Stacks, Tag 06VL] kills the Čech
cohomology of that family. -/
public theorem BigSite.cechCohomology_isZero_of_isAdequate (B : BigSite τ S)
    (F : SheafOfModules.{max u m} B.structureSheaf) (hF : IsAdequate B F) {U : B.category}
    (E : { E : PreZeroHypercover.{0} U // E.sieve₀ ∈ B.topology U })
    (hE : E ∈ B.affineCov U) (k : ℕ) (hk : 0 < k) :
    letI : HasFiniteLimits B.category := B.hasFiniteLimits_category
    IsZero (Stacks.CechSite.cechCohomology E.1
      ((SheafOfModules.toSheaf B.structureSheaf).obj F).obj k) := by
  let : HasFiniteLimits B.category := B.hasFiniteLimits_category
  have hfin : Finite E.1.I₀ := hE.2.1
  obtain ⟨Y, f, hY, hflat, hsurj, hmap⟩ :=
    B.exists_affine_coproduct_morphism E.1 hE.2.2.1 hE.2.2.2.1 hE.2.2.2.2
  exact (affineCechExactness_of_isAdequate.{u, m} B F hF f hE.1 hY hflat hsurj k hk).of_iso
    (B.coproductCechComparison.{u, m} F E.1 hfin Y f hmap k).some

/-! ### Assertion (3) -/

/-- **[Stacks, Tag 06VM] (3).** Let `𝓕` be an adequate `𝒪`-module on a chosen big `τ`-site
`(Sch/S)_τ` over a scheme `S`. For every affine scheme `U` over `S` belonging to the site,
`H^q(U, 𝓕) = 0` for all `q > 0`, where `H^q(U, −)` is the `q`-th right derived functor of
sections over `U` on abelian sheaves on the site, applied to the abelian sheaf underlying `𝓕`.

This is [Stacks, Tag 03F9] at the collection of affine objects of the site and the collection
of finite affine `τ`-coverings of those objects: the objects occurring in such a covering are
affine by `Stacks.Adequate.BigSite.isAffine_product_of_mem_affineCov`, the coverings are
cofinal by `Stacks.Adequate.BigSite.affineCovCofinal`, and the Čech cohomology of an adequate
module vanishes on them by `Stacks.Adequate.BigSite.cechCohomology_isZero_of_isAdequate`. -/
@[stacks 06VM "(3): for an adequate 𝒪-module F on (Sch/S)_τ and every affine scheme U over S,
H^q(U, F) = 0 for all q > 0; cohomology is the right derived functor of sections over U of the
abelian sheaf underlying F"]
public theorem BigSite.isZero_rightDerived_sections_of_isAdequate (B : BigSite τ S)
    (F : SheafOfModules.{max u m} B.structureSheaf) (hF : IsAdequate B F)
    (U : B.category) [IsAffine U.left.obj] (q : ℕ) (hq : 0 < q) :
    IsZero ((((sheafSections B.topology AddCommGrpCat.{max u m}).obj (op U)).rightDerived q).obj
      ((SheafOfModules.toSheaf B.structureSheaf).obj F)) := by
  let : HasFiniteLimits B.category := B.hasFiniteLimits_category
  let : EssentiallySmall.{max u m} B.category := B.essentiallySmall_category_max.{u, m}
  exact cechCriterion_of_essentiallySmall B.topology B.affineObjects
    (fun θ hX ↦ B.mem_affineObjects_of_iso θ hX) B.affineCov
    (fun E E' θ hE ↦ B.mem_affineCov_of_iso E E' θ hE)
    (fun {V} E hE ↦ ⟨hE.1, hE.2.2.1, B.isAffine_product_of_mem_affineCov E hE⟩)
    B.affineCovCofinal ((SheafOfModules.toSheaf B.structureSheaf).obj F)
    (fun E hE k hk ↦ B.cechCohomology_isZero_of_isAdequate F hF E hE k hk)
    U (inferInstanceAs (IsAffine U.left.obj)) q hq

end Stacks.Adequate

end
