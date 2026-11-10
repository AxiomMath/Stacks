module

public import Mathlib.Algebra.Algebra.TransferInstance
public import Mathlib.CategoryTheory.Abelian.Subcategory
public import Mathlib.CategoryTheory.Abelian.Subobject
public import Mathlib.CategoryTheory.Adjunction.AdjointFunctorTheorems
public import StacksFrontier.Algebra.Category.ModuleCat.Presheaf.LocallySmall
public import StacksFrontier.AlgebraicGeometry.Adequate.AdequateModules.AffineAdequateColimits
public import StacksFrontier.AlgebraicGeometry.Adequate.AdequateFunctors.DomainCoproduct
public import StacksFrontier.AlgebraicGeometry.Adequate.AdequateFunctors.DomainFiniteProducts
public import StacksFrontier.AlgebraicGeometry.Adequate.HigherExtsBase.Coreflection
public import StacksFrontier.AlgebraicGeometry.Size.Cutoff

/-!
# The adequate functors on the algebras of a site are coreflective

Let `A` be a ring and `κ` an uncountable strong prelimit cardinal with `Spec A` of size below
`κ`. The inclusion `i` of the adequate module-valued functors on the `A`-algebras whose spectra
have size below `κ` — the algebras of a big site with cutoff `κ` — into all module-valued
functors on those algebras has a right adjoint `Q`. This is the construction of
[Stacks, Tag 06Z6] over the algebras of the site.

## Main definitions

* `AdequateFunctor.ofLinearPresentationSite` — the linearly adequate functor on the algebras of
  the site presented by a map of finite free modules, as an adequate functor.
* `AdequateFunctor.adequateCoreflectionSite` — the functor `Q`.
* `AdequateFunctor.adequateCoreflectionSiteAdjunction` — the adjunction `i ⊣ Q`.

## Main results

* `AdequateFunctor.essentiallySmall_algebraInSite` — the algebras of a site form an essentially
  small property of the commutative `A`-algebras.
* `AdequateFunctor.locallySmall_moduleValuedFunctorOn_site` — the module-valued functors on the
  algebras of a site are locally small.
* `AdequateFunctor.isSeparating_ofLinearPresentationSite` — the linearly adequate functors
  separate the adequate functors on the algebras of a site.
* `AdequateFunctor.isLeftAdjoint_adequateOn_site` — the inclusion of the adequate functors on the
  algebras of a site has a right adjoint.

## References

* [Stacks Project, Tag 06Z6](https://stacks.math.columbia.edu/tag/06Z6)
* [Stacks Project, Tag 06UX](https://stacks.math.columbia.edu/tag/06UX)
* [Stacks Project, Tag 06V4](https://stacks.math.columbia.edu/tag/06V4)
* [Stacks Project, Tag 06ZS](https://stacks.math.columbia.edu/tag/06ZS)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry

universe u

namespace AdequateFunctor

/-! ### Smallness of the algebras of a site -/

/-- The `A`-algebras whose spectra have size below `κ` form an essentially small property of
the commutative `A`-algebras. -/
public theorem essentiallySmall_algebraInSite (A : Type u) [CommRing A] (κ : Cardinal.{u}) :
    ObjectProperty.EssentiallySmall.{u} (algebraInSite.{u, u} A (schemeSizeBelow κ)) := by
  classical
  let model (p : Σ T : Set κ.out, Σ r : CommRing T, let _ := r; Algebra A T) :
      CommAlgCat.{u} A :=
    let _ := p.2.1
    let _ := p.2.2
    CommAlgCat.of A p.1
  refine ⟨ObjectProperty.ofObj model, inferInstance, fun R hR ↦ ?_⟩
  have hRκ : Cardinal.mk R < κ :=
    lt_of_le_of_lt ((le_max_right _ _).trans (Scheme.size_Spec (CommRingCat.of R)).ge) hR
  obtain ⟨f⟩ : Nonempty (R ↪ κ.out) := hRκ.le.trans_eq (Cardinal.mk_out κ).symm
  let e : R ≃ Set.range f := Equiv.ofInjective f f.injective
  let : CommRing (Set.range f) := e.symm.commRing
  let : Algebra A (Set.range f) := e.symm.algebra A
  exact ⟨model ⟨Set.range f, inferInstance, inferInstance⟩, ObjectProperty.ofObj_apply model _,
    ⟨CommAlgCat.isoMk (e.symm.algEquiv A).symm⟩⟩

section Site

variable (A : Type u) [CommRing A] (κ : Cardinal.{u})

/-- The module-valued functors on the algebras of a site, with values in the universe `u` of the
algebras, are locally small at `u`. -/
public theorem locallySmall_moduleValuedFunctorOn_site :
    LocallySmall.{u} (ModuleValuedFunctorOn.{u, u}
      (siteAlgebraInclusion.{u, u} A (schemeSizeBelow κ))) :=
  have := essentiallySmall_algebraInSite A κ
  PresheafOfModules.locallySmall_of_essentiallySmall.{u} _

/-- The linearly adequate functor on the algebras of a site presented by a map of finite free
`A`-modules, as an object of the category of adequate functors there. -/
public def ofLinearPresentationSite (d : LinearPresentation.{u, u} A) :
    (adequateOn.{u, u} (siteAlgebraInclusion.{u, u} A (schemeSizeBelow κ))).FullSubcategory :=
  ⟨kernel ((moduleExtensionFunctorOn.{u, u}
      (siteAlgebraInclusion.{u, u} A (schemeSizeBelow κ))).map d.2.2),
    ⟨_, _, d.2.2, ⟨presheafOfModulesUliftIso.{u, u}
      (algebraRingDiagramOn.{u} (siteAlgebraInclusion.{u, u} A (schemeSizeBelow κ))) _⟩⟩⟩

variable {A κ}

/-- Every linearly adequate functor on the algebras of a site is isomorphic to one of the family
`AdequateFunctor.ofLinearPresentationSite`. -/
public theorem exists_iso_ofLinearPresentationSite (hA : (Spec (CommRingCat.of A)).size < κ)
    {F : ModuleValuedFunctorOn.{u, u} (siteAlgebraInclusion.{u, u} A (schemeSizeBelow κ))}
    (hF : IsLinearlyAdequate (siteAlgebraInclusion.{u, u} A (schemeSizeBelow κ)) F) :
    ∃ d : LinearPresentation.{u, u} A, Nonempty (F ≅ (ofLinearPresentationSite A κ d).obj) := by
  obtain ⟨n, m, f, ⟨e⟩⟩ := hF
  let hfull := fullyFaithfulModuleExtensionFunctorOn.{u}
    (BaseAlgebraObject.siteOfSpecMem (schemeSizeBelow κ) hA)
  exact ⟨⟨n, m, hfull.preimage f⟩, ⟨(presheafOfModulesUliftIso.{u, u}
    (algebraRingDiagramOn.{u} (siteAlgebraInclusion.{u, u} A (schemeSizeBelow κ))) F).symm ≪≫
      e ≪≫ kernelIsoOfEq (hfull.map_preimage f).symm⟩⟩

/-- The linearly adequate functors form a separating family for the adequate functors on the
algebras of a site. -/
public theorem isSeparating_ofLinearPresentationSite (hA : (Spec (CommRingCat.of A)).size < κ) :
    (ObjectProperty.ofObj (ofLinearPresentationSite A κ)).IsSeparating := by
  classical
  intro X Y f g hfg
  apply ObjectProperty.hom_ext
  let R := algebraRingDiagramOn.{u} (siteAlgebraInclusion.{u, u} A (schemeSizeBelow κ))
  obtain ⟨J, L, hL, cover, hcover⟩ := exists_coproduct_linearlyAdequate_surjective_on.{u, u}
    (siteAlgebraInclusion.{u, u} A (schemeSizeBelow κ)) X.obj X.property
  let eX : (presheafOfModulesUliftFunctor.{u, u} R).obj X.obj ≅ X.obj :=
    presheafOfModulesUliftIso.{u, u} R X.obj
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
  rintro ⟨i⟩
  obtain ⟨d, ⟨e⟩⟩ := exists_iso_ofLinearPresentationSite hA (hL i)
  let h₀ : ofLinearPresentationSite A κ d ⟶ X :=
    ObjectProperty.homMk (X := ofLinearPresentationSite A κ d) (Y := X)
      (e.inv ≫ Sigma.ι L i ≫ cover')
  have key : (e.inv ≫ Sigma.ι L i ≫ cover') ≫ f.hom = (e.inv ≫ Sigma.ι L i ≫ cover') ≫ g.hom :=
    congrArg InducedCategory.Hom.hom (hfg _ (ObjectProperty.ofObj_apply _ d) h₀)
  change Sigma.ι L i ≫ cover' ≫ f.hom = Sigma.ι L i ≫ cover' ≫ g.hom
  rw [← cancel_epi e.inv]
  simpa using key

variable (hκ : Cardinal.aleph0 < κ) (hsl : Cardinal.IsStrongPrelimit κ)
  (hA : (Spec (CommRingCat.of A)).size < κ)

include hκ hsl hA in
/-- Adequacy on the algebras of a site is closed under colimits of every shape in the universe
`u`. -/
public theorem adequateOn_isClosedUnderColimitsOfShape_site (J : Type u) [Category.{u} J] :
    ObjectProperty.IsClosedUnderColimitsOfShape
      (adequateOn.{u, u} (siteAlgebraInclusion.{u, u} A (schemeSizeBelow κ))) J where
  colimitsOfShape_le := by
    rintro X ⟨p⟩
    exact IsAdequate.of_iso (isAdequate_colimit_site.{u} hκ hsl A hA p.diag p.prop_diag_obj)
      (IsColimit.coconePointUniqueUpToIso p.isColimit (colimit.isColimit p.diag))

include hκ hsl hA in
/-- Adequacy on the algebras of a site is closed under kernels. -/
public theorem adequateOn_isClosedUnderKernels_site :
    ObjectProperty.IsClosedUnderKernels
      (adequateOn.{u, u} (siteAlgebraInclusion.{u, u} A (schemeSizeBelow κ))) where
  kernels_le := by
    rintro _ ⟨φ, k, hk, hF, hG⟩
    exact (adequateOn.{u, u} (siteAlgebraInclusion.{u, u} A (schemeSizeBelow κ))).prop_of_iso
      (IsLimit.conePointUniqueUpToIso (limit.isLimit (parallelPair φ 0)) hk)
      (isAdequate_kernel_site.{u} hκ hsl A hA φ hF hG)

include hκ hsl hA in
/-- Adequacy on the algebras of a site is closed under cokernels. -/
public theorem adequateOn_isClosedUnderCokernels_site :
    ObjectProperty.IsClosedUnderCokernels
      (adequateOn.{u, u} (siteAlgebraInclusion.{u, u} A (schemeSizeBelow κ))) where
  cokernels_le := by
    rintro _ ⟨φ, k, hk, hF, hG⟩
    exact (adequateOn.{u, u} (siteAlgebraInclusion.{u, u} A (schemeSizeBelow κ))).prop_of_iso
      (IsColimit.coconePointUniqueUpToIso (colimit.isColimit (parallelPair φ 0)) hk)
      (isAdequate_cokernel_site.{u} hκ hsl A hA φ hF hG)

include hκ hsl hA in
/-- The inclusion of the adequate functors into all module-valued functors on the algebras of a
site has a right adjoint. -/
public theorem isLeftAdjoint_adequateOn_site :
    (adequateOn.{u, u} (siteAlgebraInclusion.{u, u} A (schemeSizeBelow κ))).ι.IsLeftAdjoint := by
  let P := adequateOn.{u, u} (siteAlgebraInclusion.{u, u} A (schemeSizeBelow κ))
  have : LocallySmall.{u} (ModuleValuedFunctorOn.{u, u}
      (siteAlgebraInclusion.{u, u} A (schemeSizeBelow κ))) :=
    locallySmall_moduleValuedFunctorOn_site A κ
  have hsep := isSeparating_ofLinearPresentationSite hA
  have : P.IsClosedUnderKernels := adequateOn_isClosedUnderKernels_site hκ hsl hA
  have : P.IsClosedUnderCokernels := adequateOn_isClosedUnderCokernels_site hκ hsl hA
  have : WellPowered.{u} P.FullSubcategory := wellPowered_of_isDetecting hsep.isDetecting
  have : HasColimitsOfSize.{u, u} P.FullSubcategory := ⟨fun J _ ↦
    have := adequateOn_isClosedUnderColimitsOfShape_site hκ hsl hA J; inferInstance⟩
  have : PreservesColimitsOfSize.{u, u} P.ι := ⟨fun {J} _ ↦
    have := adequateOn_isClosedUnderColimitsOfShape_site hκ hsl hA J; inferInstance⟩
  exact isLeftAdjoint_of_preservesColimits_of_isSeparating hsep _

/-- **The construction of [Stacks, Tag 06Z6] over the algebras of a site.** The functor `Q`,
right adjoint to the inclusion of the adequate module-valued functors on the algebras of a site
into all module-valued functors on them. -/
public def adequateCoreflectionSite :
    ModuleValuedFunctorOn.{u, u} (siteAlgebraInclusion.{u, u} A (schemeSizeBelow κ)) ⥤
      (adequateOn.{u, u} (siteAlgebraInclusion.{u, u} A (schemeSizeBelow κ))).FullSubcategory :=
  have := isLeftAdjoint_adequateOn_site hκ hsl hA
  (adequateOn.{u, u} (siteAlgebraInclusion.{u, u} A (schemeSizeBelow κ))).ι.rightAdjoint

/-- The functor `Q` of [Stacks, Tag 06Z6] over the algebras of a site is a right adjoint to the
inclusion `i` of the adequate module-valued functors. -/
public def adequateCoreflectionSiteAdjunction :
    (adequateOn.{u, u} (siteAlgebraInclusion.{u, u} A (schemeSizeBelow κ))).ι ⊣
      adequateCoreflectionSite hκ hsl hA :=
  have := isLeftAdjoint_adequateOn_site hκ hsl hA
  Adjunction.ofIsLeftAdjoint _

end Site

end AdequateFunctor

end
