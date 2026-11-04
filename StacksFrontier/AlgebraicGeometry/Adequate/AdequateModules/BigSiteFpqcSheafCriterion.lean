module

public import StacksFrontier.AlgebraicGeometry.Adequate.AdequateModules.AffineCohomologyVanishing
public import StacksFrontier.AlgebraicGeometry.Adequate.AdequateModules.CechAmitsurDifferentials
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.FpqcTopology.SheafCriterion
public import StacksFrontier.AlgebraicGeometry.Topologies.Fpqc.ComapSheafCondition

/-!
# The fpqc sheaf criterion on a chosen big site

[Stacks, Tag 03O1] reduces the fpqc sheaf condition to the Zariski sheaf condition together with
descent along a single faithfully flat morphism of affines. It is available as
`Stacks.EtaleCohomology.isSheaf_fpqc_iff_zariski_and_affine_singleton`, but only for presheaves on
*all* schemes over `S`. The final paragraph of [Stacks, Tag 06VL] needs it for a module on a
chosen big site, which is defined only on the schemes below the site's cardinal cutoff. This
module supplies that form.

## The form proved, and why

`Stacks.Adequate.isSheaf_fpqc_of_exists_extension` is the criterion: a presheaf on a chosen big
site which is, up to isomorphism, the restriction along `Stacks.Adequate.BigSite.toOver` of a
presheaf on the schemes over `S` satisfying the two conditions of [Stacks, Tag 03O1] satisfies
the sheaf condition for every fpqc covering family of the site. Together with
`Stacks.Adequate.isSheaf_fppf_of_isSheaf_fpqc` it gives both of the sheaf conclusions the final
paragraph of [Stacks, Tag 06VL] asserts side by side.

The hypothesis is an extension of the presheaf to the whole slice, and that is deliberate. Of the
three routes to a subsite form of the criterion, the extension is the only one that is not
blocked:

* *Generalising* [Stacks, Tag 03O1] so that its proof runs over a subsite is not available. Its
  proof reduces to Mathlib's `AlgebraicGeometry.isSheaf_type_propQCTopology_iff`, Tag 022H, which
  is stated and proved for `Scheme.{u}` and quantifies over all of it; the reduction it performs
  manipulates affine covers, finite coproducts and quasi-compact refinements of arbitrary
  schemes. Generalising it is a change to Mathlib, not to this library.
* *Proving a separate statement* intrinsic to the site means redoing that reduction inside the
  site. The repository does exactly this for two other topologies — see
  `AlgebraicGeometry.isSheaf_iff_zariski_and_properSurjective` for ph and
  `AlgebraicGeometry.BigHOver.isSheaf_iff_zariski_and_affineFlatProperFP_and_generatorSquares` for
  the h topology — and each costs about a thousand lines.
* *Extending* and descending is the route taken. The descent half is unconditional and proved:
  `Stacks.Adequate.isSheaf_fpqc_restriction` is one application of
  `AlgebraicGeometry.isSheaf_fpqcComap_of_isSheaf_fpqcOver`, whose hypotheses are that the site
  has fibre products and that its canonical functor preserves them — both supplied here. So the
  extension does preserve the covering families, which is the thing to check first.

## Main definitions

* `Stacks.Adequate.zariskiPrecoverageOn` — the Zariski covering families of a chosen big site,
  the Zariski companion of `Stacks.Adequate.fpqcPrecoverageOn`. Without it the
  criterion cannot be stated: the only Grothendieck topologies the library had on `B.category`
  were `B.topology` itself and the hypothesis data `Stacks.Adequate.BigSite.Coarsening`.
* `Stacks.Adequate.IsAffineSingletonSheaf` — descent along a flat surjective morphism between
  affines *of the site*, stated with exactly the hypotheses of
  `Stacks.Adequate.sieve_generate_singleton_mem_fpqc`.
* `Stacks.Adequate.BigSite.fullyFaithfulToOver` — the canonical functor of the site is fully
  faithful, being `CategoryTheory.Over.post` of a full subcategory inclusion.

## Main results

* `Stacks.Adequate.isSheaf_fpqcPrecoverageOn_iff` — the fpqc sheaf condition on the site is the
  sheaf condition for its fpqc covering families, no saturation to inspect.
* `Stacks.Adequate.isSheaf_fpqc_restriction` — restriction of an fpqc sheaf on the schemes over
  `S` to the site is a sheaf for the fpqc topology of the site.
* `Stacks.Adequate.isSheaf_fpqc_restriction_of_zariski_and_affine_singleton`,
  `Stacks.Adequate.isSheaf_fpqc_of_exists_extension` — **the big-site form of [Stacks, Tag
  03O1]**, and
  `Stacks.Adequate.isSheaf_fppf_restriction_of_zariski_and_affine_singleton`,
  `Stacks.Adequate.isSheaf_fppf_of_exists_extension` — its fppf consequence.
* `Stacks.Adequate.isSheaf_zariski_of_isSheaf_fpqc`,
  `Stacks.Adequate.isAffineSingletonSheaf_of_isSheaf_fpqc` — the converse direction, which holds
  intrinsically on the site: an fpqc sheaf of the site satisfies both conditions of the
  criterion.

## Implementation notes

`Stacks.Adequate.fpqcPrecoverageOn` is by definition
`Scheme.fpqcPrecoverage.comap (B.toOver ⋙ Over.forget S)`, which is literally the shape the
general lemmas of `StacksFrontier.AlgebraicGeometry.Topologies.Fpqc.ComapSheafCondition` are stated
at, so both of them apply to a chosen big site with no bridging. Their two instance hypotheses
are discharged by `Stacks.Adequate.BigSite.hasPullbacks_category`, from
`Stacks.Adequate.BigSite.hasFiniteLimits_category`, and by
`Stacks.Adequate.BigSite.preservesPullbacks_toOver`, which is
`CategoryTheory.Limits.preservesLimitsOfShape_of_reflects_of_preserves` applied to the composite
with the slice projection; that composite is `Over.forget _ ⋙ (schemeSizeBelow B.cutoff).ι` by
`CategoryTheory.Over.post_forget_eq_forget_comp`, and the inclusion preserves fibre products
because `AlgebraicGeometry.schemeSizeBelow` is closed under them, Tag 021U.

**The criterion is not needed for a presented module.** The extension hypothesis is an
obstruction only for a presheaf given abstractly. The presheaf of
`Stacks.Adequate.BigSite.associatedModule` is *by definition* the restriction along
`Stacks.Adequate.BigSite.toOver` of the presheaf of [Stacks, Tag 03DS] on all schemes over `S`,
and that presheaf is an fpqc sheaf by [Stacks, Tag 03DT], so
`Stacks.Adequate.isSheaf_fpqc_restriction` alone gives the fpqc sheaf condition — without the
Zariski condition, without the affine singleton condition, and without this criterion. The same
holds for a kernel of a map of associated modules, `Presheaf.IsSheaf` being closed under limits.
Both are in
`StacksFrontier/AlgebraicGeometry/Adequate/AdequateModules/AssociatedModuleFpqcSheaf.lean`. What
that does not reach is a module given only as satisfying `Stacks.Adequate.IsAdequate`: adequacy
constrains the affine-section *functors* and supplies no presentation of the sheaf, and the
implication from adequacy to a presentation is the converse of [Stacks, Tag 06VK], which needs
the quasi-inverse of [Stacks, Tag 06ZJ].

**What is not proved, and the measurement.** The criterion is not available with the extension
removed, that is, for an arbitrary presheaf of the site. The repository has the machinery of
[Stacks, Tag 0EUW] to build an extension —
`AlgebraicGeometry.ExtendingFunctors.extension`, with
`AlgebraicGeometry.ExtendingFunctors.isZariskiSheaf_extension` for the first of the two
conditions and `AlgebraicGeometry.ExtendingFunctors.nonempty_restrictionIso` identifying its
restriction with the given functor — and the second condition is where it stops. [Stacks, Tag
03O1] demands descent along `Spec T ⟶ Spec R` for *every* pair of rings, including rings above
the cutoff, and the only route to such a statement for an extension is the one
[Stacks, Tag 0GDW] uses for the five standard topologies: write the affine as a directed limit
of affines of finite presentation over an affine open of `S` (Tag 00QN), descend the covering to
a finite stage (Tag 049N) and pass to the filtered colimit. A faithfully flat morphism of affines
is *not* of finite presentation, so it does not descend to a stage, and that step has no fpqc
analogue — which is also why the Stacks Project builds no big fpqc site and why the paragraph of
Tag 06VL this serves says "details omitted". A naive extension does not repair this: the right
Kan extension along `B.toOver` is a Zariski sheaf whenever the given presheaf is, but its value
at an affine above the cutoff is a limit over the small schemes lying over it, and the base
change of a small algebra along a large one leaves the site, so the descent datum it would need
is not there.

## References

* [Stacks Project, Tag 06VL](https://stacks.math.columbia.edu/tag/06VL)
* [Stacks Project, Tag 03O1](https://stacks.math.columbia.edu/tag/03O1)
* [Stacks Project, Tag 022H](https://stacks.math.columbia.edu/tag/022H)
* [Stacks Project, Tag 0EUW](https://stacks.math.columbia.edu/tag/0EUW)
* [Stacks Project, Tag 0GDW](https://stacks.math.columbia.edu/tag/0GDW)
-/

@[expose] public section

open AlgebraicGeometry CategoryTheory Limits Opposite

universe w v u

namespace Stacks.Adequate

variable {τ : CoveringTopology} {S : Scheme.{u}}

/-- The Zariski covering families of a chosen big site: the families of the site whose images
are Zariski covering families of schemes. -/
public abbrev zariskiPrecoverageOn (B : BigSite τ S) : Precoverage B.category :=
  Scheme.zariskiPrecoverage.{u}.comap (B.toOver ⋙ Over.forget S)

/-- A Zariski covering family of the site is an fpqc covering family of the site. -/
public theorem zariskiPrecoverageOn_le_fpqcPrecoverageOn (B : BigSite τ S) :
    zariskiPrecoverageOn B ≤ fpqcPrecoverageOn B := fun _ _ hR =>
  Scheme.zariskiPrecoverage_le_fpqcPrecoverage _ hR

/-- The canonical functor from a chosen big site to the schemes over `S` is fully faithful: it is
`Over.post` of the inclusion of a full subcategory of schemes. -/
public def BigSite.fullyFaithfulToOver (B : BigSite τ S) : B.toOver.FullyFaithful :=
  Functor.FullyFaithful.over _ _ (schemeSizeBelow B.cutoff).fullyFaithfulι

/-- The canonical functor from a chosen big site to the schemes over `S` is full. -/
public instance BigSite.full_toOver (B : BigSite τ S) : B.toOver.Full :=
  B.fullyFaithfulToOver.full

/-- The canonical functor from a chosen big site to the schemes over `S` is faithful. -/
public instance BigSite.faithful_toOver (B : BigSite τ S) : B.toOver.Faithful :=
  B.fullyFaithfulToOver.faithful

/-- The underlying-scheme functor of a chosen big site preserves fibre products: it is the
forgetful functor of an over category followed by the inclusion of the small schemes. -/
public instance BigSite.preservesPullbacks_toOver_comp_forget (B : BigSite τ S) :
    PreservesLimitsOfShape WalkingCospan (B.toOver ⋙ Over.forget S) := by
  have h₂ : PreservesLimitsOfShape WalkingCospan (schemeBelowInclusion B.cutoff) := by
    dsimp [schemeBelowInclusion, SchemeBelow]
    infer_instance
  change PreservesLimitsOfShape WalkingCospan
    (Over.forget (⟨S, B.base_mem⟩ : SchemeBelow B.cutoff) ⋙ schemeBelowInclusion B.cutoff)
  apply comp_preservesLimitsOfShape

/-- The canonical functor from a chosen big site to the schemes over `S` preserves fibre
products, since its composite with the forgetful functor does and that functor reflects them. -/
public instance BigSite.preservesPullbacks_toOver (B : BigSite τ S) :
    PreservesLimitsOfShape WalkingCospan B.toOver :=
  preservesLimitsOfShape_of_reflects_of_preserves _ (Over.forget S)

/-- **Descent along a flat surjective morphism between affines of the site.** This is the second
condition of the big-site form of [Stacks, Tag 03O1]: the sheaf condition for the singleton
presieve of a morphism of the site whose underlying morphism of schemes is a faithfully flat
morphism of affines. It is the condition that [Stacks, Tag 06VL] supplies through the exactness
of the extended Čech complex. -/
public def IsAffineSingletonSheaf (B : BigSite τ S) (P : B.categoryᵒᵖ ⥤ Type v) : Prop :=
  ∀ {X T : B.category} (g : X ⟶ T), IsAffine ((B.toOver.obj X).left) →
    IsAffine ((B.toOver.obj T).left) → Flat ((B.toOver.map g).left) →
      Surjective ((B.toOver.map g).left) → Presieve.IsSheafFor P (Presieve.singleton g)

/-- A chosen big site has fibre products, since it has finite limits. -/
public instance BigSite.hasPullbacks_category (B : BigSite τ S) : HasPullbacks B.category := by
  have : HasFiniteLimits B.category := B.hasFiniteLimits_category
  infer_instance

/-- **The fpqc sheaf condition on a chosen big site is the sheaf condition for its fpqc covering
families.** The covering families of the site are stable under base change and the site has fibre
products, so no saturation of the generated topology has to be inspected. -/
public theorem isSheaf_fpqcPrecoverageOn_iff (B : BigSite τ S) (P : B.categoryᵒᵖ ⥤ Type v) :
    Presheaf.IsSheaf (fpqcPrecoverageOn B).toGrothendieck P ↔
      ∀ ⦃X : B.category⦄ (R : Presieve X), R ∈ fpqcPrecoverageOn B X →
        Presieve.IsSheafFor P R :=
  AlgebraicGeometry.isSheaf_fpqcComap_iff B.toOver P

/-- **Restriction of an fpqc sheaf on the schemes over `S` to a chosen big site.** The canonical
functor of the site preserves fibre products, so it is continuous for the fpqc topology of the
site and the fpqc topology induced on the schemes over `S`. -/
public theorem isSheaf_fpqc_restriction (B : BigSite τ S) {A : Type*} [Category A]
    (Φ : (Over S)ᵒᵖ ⥤ A) (hΦ : Presheaf.IsSheaf (Scheme.fpqcTopology.over S) Φ) :
    Presheaf.IsSheaf (fpqcPrecoverageOn B).toGrothendieck (B.toOver.op ⋙ Φ) :=
  AlgebraicGeometry.isSheaf_fpqcComap_of_isSheaf_fpqcOver B.toOver Φ hΦ

/-- **[Stacks, Tag 03O1] on a chosen big site.** A presheaf on the schemes over `S` which is a
Zariski sheaf and satisfies the singleton sheaf condition for every faithfully flat morphism of
affines over `S` restricts to a presheaf on a chosen big site over `S` satisfying the sheaf
condition for every fpqc covering family of the site.

The two hypotheses are exactly those of
`Stacks.EtaleCohomology.isSheaf_fpqc_iff_zariski_and_affine_singleton`, which is the criterion
for presheaves on all of `Sch/S`; the conclusion is the condition on the site, which is what the
final paragraph of [Stacks, Tag 06VL] asserts. -/
public theorem isSheaf_fpqc_restriction_of_zariski_and_affine_singleton (B : BigSite τ S)
    (Φ : (Over S)ᵒᵖ ⥤ Type v)
    (hZar : Presheaf.IsSheaf (Scheme.zariskiTopology.over S) Φ)
    (hAff : ∀ {R T : CommRingCat.{u}} (f : R ⟶ T) (g : Spec R ⟶ S)
      [Flat (Spec.map f)] [Surjective (Spec.map f)],
      Presieve.IsSheafFor Φ (Presieve.singleton (Over.homMk (Spec.map f) rfl :
        Over.mk (Spec.map f ≫ g) ⟶ Over.mk g))) :
    Presheaf.IsSheaf (fpqcPrecoverageOn B).toGrothendieck (B.toOver.op ⋙ Φ) :=
  isSheaf_fpqc_restriction B Φ
    ((Stacks.EtaleCohomology.isSheaf_fpqc_iff_zariski_and_affine_singleton S Φ).2 ⟨hZar, hAff⟩)

/-- **The fppf conclusion of [Stacks, Tag 06VL] for a restricted presheaf.** Composing the
big-site form of [Stacks, Tag 03O1] with
`Stacks.Adequate.isSheaf_fppf_of_isSheaf_fpqc` gives the second of the two sheaf conclusions the
final paragraph of the source asserts side by side. -/
public theorem isSheaf_fppf_restriction_of_zariski_and_affine_singleton (B : BigSite τ S)
    (Φ : (Over S)ᵒᵖ ⥤ Type v)
    (hZar : Presheaf.IsSheaf (Scheme.zariskiTopology.over S) Φ)
    (hAff : ∀ {R T : CommRingCat.{u}} (f : R ⟶ T) (g : Spec R ⟶ S)
      [Flat (Spec.map f)] [Surjective (Spec.map f)],
      Presieve.IsSheafFor Φ (Presieve.singleton (Over.homMk (Spec.map f) rfl :
        Over.mk (Spec.map f ≫ g) ⟶ Over.mk g))) :
    Presheaf.IsSheaf (fppfPrecoverageOn B).toGrothendieck (B.toOver.op ⋙ Φ) :=
  isSheaf_fppf_of_isSheaf_fpqc B _
    (isSheaf_fpqc_restriction_of_zariski_and_affine_singleton B Φ hZar hAff)

/-- **[Stacks, Tag 03O1] on a chosen big site, stated for a presheaf of the site.** A presheaf on
a chosen big site over `S` which is the restriction, up to isomorphism, of a presheaf on the
schemes over `S` satisfying the two conditions of [Stacks, Tag 03O1] satisfies the sheaf
condition for every fpqc covering family of the site.

This is the form in which the final paragraph of [Stacks, Tag 06VL] uses the criterion: its
hypothesis is intrinsic to the presheaf of the site apart from the single datum of an extension,
and the fpqc conclusion is the one the source asserts. -/
public theorem isSheaf_fpqc_of_exists_extension (B : BigSite τ S) (P : B.categoryᵒᵖ ⥤ Type v)
    (Φ : (Over S)ᵒᵖ ⥤ Type v) (e : B.toOver.op ⋙ Φ ≅ P)
    (hZar : Presheaf.IsSheaf (Scheme.zariskiTopology.over S) Φ)
    (hAff : ∀ {R T : CommRingCat.{u}} (f : R ⟶ T) (g : Spec R ⟶ S)
      [Flat (Spec.map f)] [Surjective (Spec.map f)],
      Presieve.IsSheafFor Φ (Presieve.singleton (Over.homMk (Spec.map f) rfl :
        Over.mk (Spec.map f ≫ g) ⟶ Over.mk g))) :
    Presheaf.IsSheaf (fpqcPrecoverageOn B).toGrothendieck P :=
  (Presheaf.isSheaf_of_iso_iff e).1
    (isSheaf_fpqc_restriction_of_zariski_and_affine_singleton B Φ hZar hAff)

/-- The fppf conclusion of [Stacks, Tag 06VL] for a presheaf of the site admitting an
extension. -/
public theorem isSheaf_fppf_of_exists_extension (B : BigSite τ S) (P : B.categoryᵒᵖ ⥤ Type v)
    (Φ : (Over S)ᵒᵖ ⥤ Type v) (e : B.toOver.op ⋙ Φ ≅ P)
    (hZar : Presheaf.IsSheaf (Scheme.zariskiTopology.over S) Φ)
    (hAff : ∀ {R T : CommRingCat.{u}} (f : R ⟶ T) (g : Spec R ⟶ S)
      [Flat (Spec.map f)] [Surjective (Spec.map f)],
      Presieve.IsSheafFor Φ (Presieve.singleton (Over.homMk (Spec.map f) rfl :
        Over.mk (Spec.map f ≫ g) ⟶ Over.mk g))) :
    Presheaf.IsSheaf (fppfPrecoverageOn B).toGrothendieck P :=
  isSheaf_fppf_of_isSheaf_fpqc B _
    (isSheaf_fpqc_of_exists_extension B P Φ e hZar hAff)

/-- A presheaf on a chosen big site satisfying the sheaf condition for the fpqc covering families
of the site satisfies it for the Zariski covering families, since the latter are among the
former. -/
public theorem isSheaf_zariski_of_isSheaf_fpqc (B : BigSite τ S) {Z : Type*} [Category Z]
    (P : B.categoryᵒᵖ ⥤ Z)
    (h : Presheaf.IsSheaf (fpqcPrecoverageOn B).toGrothendieck P) :
    Presheaf.IsSheaf (zariskiPrecoverageOn B).toGrothendieck P :=
  h.of_le (Precoverage.toGrothendieck_mono (zariskiPrecoverageOn_le_fpqcPrecoverageOn B))

/-- A presheaf on a chosen big site satisfying the sheaf condition for the fpqc covering families
of the site descends along every flat surjective morphism between affines of the site, such a
morphism being an fpqc covering of the site. -/
public theorem isAffineSingletonSheaf_of_isSheaf_fpqc (B : BigSite τ S)
    (P : B.categoryᵒᵖ ⥤ Type v)
    (h : Presieve.IsSheaf (fpqcPrecoverageOn B).toGrothendieck P) :
    IsAffineSingletonSheaf B P := by
  intro X T g hX hT hflat hsurj
  exact (Presieve.isSheafFor_iff_generate _).2
    (h _ (sieve_generate_singleton_mem_fpqc B g hX hT hflat hsurj))

end Stacks.Adequate

end
