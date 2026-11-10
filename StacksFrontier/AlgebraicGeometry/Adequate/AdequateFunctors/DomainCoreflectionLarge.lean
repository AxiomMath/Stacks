module

public import StacksFrontier.AlgebraicGeometry.Adequate.AdequateFunctors.DomainCoreflection

/-!
# The site-local family of linearly adequate functors at an independent value universe

`AdequateFunctor.ofLinearPresentationSite` and the two theorems about it in
`StacksFrontier.AlgebraicGeometry.Adequate.AdequateFunctors.DomainCoreflection` take their values
in the universe `u` of the algebras of the site. The same constructions and proofs work with the
value universe a free parameter `max u m` above `u`, and that is the generality in which
[Stacks, Tag 06ZU] is stated, so the three are repeated here at that universe. Taking `m := u`
recovers the forms of that module.

## Main definitions

* `AdequateFunctor.ofLinearPresentationSite_large` — the linearly adequate functor on the
  algebras of the site presented by a map of finite free modules, at value universe `max u m`.

## Main results

* `AdequateFunctor.exists_iso_ofLinearPresentationSite_large` — every linearly adequate functor
  there is isomorphic to a member of that family.
* `AdequateFunctor.isSeparating_ofLinearPresentationSite_large` — the family is separating.

## References

* [Stacks Project, Tag 06UX](https://stacks.math.columbia.edu/tag/06UX)
* [Stacks Project, Tag 06Z6](https://stacks.math.columbia.edu/tag/06Z6)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry

universe u m

namespace AdequateFunctor

section Site

variable (A : Type u) [CommRing A] (κ : Cardinal.{u})

/-- The linearly adequate functor on the algebras of a site presented by a map of finite free
`A`-modules, as an object of the category of adequate functors there.

The value universe is `max u m` with `m` free, so that the family is available at every value
universe above the universe `u` of the algebras; `m := u` recovers the values in `u` itself. -/
public def ofLinearPresentationSite_large (d : LinearPresentation.{u, max u m} A) :
    (adequateOn.{max u m, u}
      (siteAlgebraInclusion.{u, u} A (schemeSizeBelow κ))).FullSubcategory :=
  ⟨kernel ((moduleExtensionFunctorOn.{max u m, u}
      (siteAlgebraInclusion.{u, u} A (schemeSizeBelow κ))).map d.2.2),
    ⟨_, _, d.2.2, ⟨presheafOfModulesUliftIso.{u, max u m}
      (algebraRingDiagramOn.{u} (siteAlgebraInclusion.{u, u} A (schemeSizeBelow κ))) _⟩⟩⟩

variable {A κ}

/-- Every linearly adequate functor on the algebras of a site is isomorphic to one of the family
`AdequateFunctor.ofLinearPresentationSite_large`: its presenting morphism of finite free module
extensions comes from a map of modules, by fullness of extension of scalars on the site. -/
public theorem exists_iso_ofLinearPresentationSite_large (hA : (Spec (CommRingCat.of A)).size < κ)
    {F : ModuleValuedFunctorOn.{max u m, u}
      (siteAlgebraInclusion.{u, u} A (schemeSizeBelow κ))}
    (hF : IsLinearlyAdequate (siteAlgebraInclusion.{u, u} A (schemeSizeBelow κ)) F) :
    ∃ d : LinearPresentation.{u, max u m} A,
      Nonempty (F ≅ (ofLinearPresentationSite_large.{u, m} A κ d).obj) := by
  obtain ⟨n, k, f, ⟨e⟩⟩ := hF
  let hfull := fullyFaithfulModuleExtensionFunctorOn.{max u m}
    (BaseAlgebraObject.siteOfSpecMem (schemeSizeBelow κ) hA)
  exact ⟨⟨n, k, hfull.preimage f⟩, ⟨(presheafOfModulesUliftIso.{u, max u m}
    (algebraRingDiagramOn.{u} (siteAlgebraInclusion.{u, u} A (schemeSizeBelow κ))) F).symm ≪≫
      e ≪≫ kernelIsoOfEq (hfull.map_preimage f).symm⟩⟩

/-- The linearly adequate functors form a separating family for the adequate functors on the
algebras of a site: by [Stacks, Tag 06UX] there, every adequate functor is a pointwise quotient
of a direct sum of linearly adequate functors, and each summand is isomorphic to one of the
chosen family. -/
public theorem isSeparating_ofLinearPresentationSite_large
    (hA : (Spec (CommRingCat.of A)).size < κ) :
    (ObjectProperty.ofObj (ofLinearPresentationSite_large.{u, m} A κ)).IsSeparating := by
  classical
  intro X Y f g hfg
  apply ObjectProperty.hom_ext
  let R := algebraRingDiagramOn.{u} (siteAlgebraInclusion.{u, u} A (schemeSizeBelow κ))
  obtain ⟨J, L, hL, cover, hcover⟩ :=
    exists_coproduct_linearlyAdequate_surjective_on.{max u m, u}
      (siteAlgebraInclusion.{u, u} A (schemeSizeBelow κ)) X.obj X.property
  let eX : (presheafOfModulesUliftFunctor.{u, max u m} R).obj X.obj ≅ X.obj :=
    presheafOfModulesUliftIso.{u, max u m} R X.obj
  let cover' : (∐ L) ⟶ X.obj := cover ≫ eX.hom
  have hcover' : ∀ Z, Function.Surjective (cover'.app Z) := by
    intro Z y
    obtain ⟨z, hz⟩ := (ModuleCat.epi_iff_surjective _).mp
      (inferInstance : Epi (eX.hom.app Z)) y
    obtain ⟨x, hx⟩ := hcover Z z
    exact ⟨x, by simp [cover', hx, hz]⟩
  have : Epi cover' := PresheafOfModules.epi_of_surjective hcover'
  rw [← cancel_epi cover']
  apply colimit.hom_ext
  intro i
  obtain ⟨i⟩ := i
  obtain ⟨d, ⟨e⟩⟩ := exists_iso_ofLinearPresentationSite_large.{u, m} hA (hL i)
  let h₀ : ofLinearPresentationSite_large.{u, m} A κ d ⟶ X :=
    ObjectProperty.homMk (X := ofLinearPresentationSite_large.{u, m} A κ d) (Y := X)
      (e.inv ≫ Sigma.ι L i ≫ cover')
  have key := hfg (ofLinearPresentationSite_large.{u, m} A κ d) (ObjectProperty.ofObj_apply _ d) h₀
  have key' : (e.inv ≫ Sigma.ι L i ≫ cover') ≫ f.hom =
      (e.inv ≫ Sigma.ι L i ≫ cover') ≫ g.hom := congrArg InducedCategory.Hom.hom key
  change Sigma.ι L i ≫ cover' ≫ f.hom = Sigma.ι L i ≫ cover' ≫ g.hom
  rw [← cancel_epi e.inv]
  simpa using key'

end Site

end AdequateFunctor

end
