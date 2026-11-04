module

public import Mathlib.Algebra.Homology.DerivedCategory.Ext.ExactSequences
public import Mathlib.CategoryTheory.Abelian.Exact
public import StacksFrontier.AlgebraicGeometry.Adequate.AdequateModules.AbelianUnconditional
public import StacksFrontier.AlgebraicGeometry.Adequate.AdequateModules.AdequateSeparatingFamily
public import StacksFrontier.AlgebraicGeometry.Adequate.AdequateModules.BigSiteModuleInjectives
public import StacksFrontier.AlgebraicGeometry.Adequate.AdequateModules.AffineSectionsAcyclicUnconditional
public import StacksFrontier.AlgebraicGeometry.Adequate.AdequateModules.AffineSectionsInjectivesSmall
public import StacksFrontier.AlgebraicGeometry.Adequate.AdequateModules.AffineExtensionsSplitting
public import StacksFrontier.Algebra.Homology.DerivedCategory.Ext.Basic
public import StacksFrontier.CategoryTheory.Sites.Cohomology.ModulesOnACategory.PullbackOfModules
public import StacksFrontier.Topology.Sheaves.Cohomology.Vanishing.NoetherianSpaces

/-!
# Vanishing of the higher right derived functors of the adequator of Tag 06ZS

Let `U = Spec A` be affine and let `B` be a chosen big `τ`-site over `U`. This file reduces the
vanishing `R^p A(𝓕) = 0` (`p > 0`, `𝓕` adequate) for the adequator
`Stacks.Adequate.affineAdequator` of [Stacks, Tag 06ZS] to a statement purely about module-valued
functors on the `A`-algebras of the site: the vanishing of the positive-degree extension groups,
in that category, from the affine sections of the members of a separating family of `Adeq(𝒪)`
into the affine sections of `𝓕`.

The argument is the source's proof of [Stacks, Tag 06ZU], run through the homological core
`Stacks.Adequate.isZero_rightDerived_of_coreflection` with every input other than the extension
groups discharged:

* the affine-section functor `j` is fully faithful,
  `Stacks.Adequate.fullyFaithfulAffineSectionsFunctor`;
* it preserves injective objects, `Stacks.Adequate.preservesInjectiveObjects_affineSectionsFunctor`
  ([Stacks, Tag 03FB] on the affine subsite);
* it is right acyclic at every adequate module,
  `Stacks.Adequate.affineSectionsAcyclic_of_isAdequate` ([Stacks, Tags 06YK and 06VM]);
* `Adeq(𝒪)` has the separating family `Stacks.Adequate.adequateSeparatingFamily` carried from the
  linearly adequate functors on the algebras of the site along the identification of
  [Stacks, Tag 06ZJ].

## Main definitions

* `Stacks.Adequate.siteModuleFunctors` — the module-valued functors on the `A`-algebras of the
  site, the target of the affine-section functor.

## Main results

* `Stacks.Adequate.subsingleton_ext_succ_kernel` — positive-degree `Ext` into a kernel, by
  dimension shifting.
* `Stacks.Adequate.isZero_rightDerived_affineAdequator_of_subsingleton_ext` — `R^p A(𝓕) = 0`
  from the vanishing of the degree-`p` extension groups along the separating family.
* `Stacks.Adequate.isZero_rightDerived_affineAdequator_of_site` — `R^p A(𝓕) = 0` from the
  vanishing of the positive-degree extension groups from linearly adequate into adequate
  functors on the algebras of the site.
* `Stacks.Adequate.subsingleton_ext_one_siteModuleFunctors` — [Stacks, Tag 06V7] on the algebras
  of the site: `Ext¹` from a linearly adequate functor into an adequate one vanishes.
* `Stacks.Adequate.subsingleton_ext_siteModuleFunctors_of_moduleExtension` — positive-degree
  `Ext` from a linearly adequate functor into adequate functors vanishes as soon as it does into
  the extensions of scalars of `A`-modules.

## References

* [Stacks Project, Tag 06ZU](https://stacks.math.columbia.edu/tag/06ZU)
* [Stacks Project, Tag 06ZS](https://stacks.math.columbia.edu/tag/06ZS)
* [Stacks Project, Tag 03FB](https://stacks.math.columbia.edu/tag/03FB)
-/

@[expose] public noncomputable section

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits

attribute [-instance] Stacks.Cohomology.SiteModules.moduleSheavesAbelian
  Stacks.Cohomology.SiteModules.moduleSheavesGrothendieck
  Stacks.Cohomology.SiteModules.moduleSheavesEnoughInjectives

universe w u

namespace Stacks.Adequate

section DimensionShift

variable {C : Type*} [Category* C] [Abelian C] [HasExt.{w} C]

/-- **`Ext^{n+1}` into the sub-object of a short exact sequence vanishes** as soon as it vanishes
into the quotient in degree `n` and into the middle term in degree `n + 1`: this is the covariant
long exact sequence `Ext^n(L, S.X₃) ⟶ Ext^{n+1}(L, S.X₁) ⟶ Ext^{n+1}(L, S.X₂)`. -/
public theorem subsingleton_ext_succ_X₁_of_shortExact (L : C) {S : ShortComplex C}
    (hS : S.ShortExact) (n : ℕ) (h₃ : Subsingleton (Abelian.Ext.{w} L S.X₃ n))
    (h₂ : Subsingleton (Abelian.Ext.{w} L S.X₂ (n + 1))) :
    Subsingleton (Abelian.Ext.{w} L S.X₁ (n + 1)) := by
  refine subsingleton_of_forall_eq 0 fun x => ?_
  obtain ⟨x₃, hx₃⟩ := Abelian.Ext.covariant_sequence_exact₁ L hS x (h₂.elim _ 0) (n₀ := n) rfl
  rw [← hx₃, h₃.elim x₃ 0, Abelian.Ext.zero_comp]

/-- **Positive-degree `Ext` into a kernel, by dimension shifting.** For `f : X ⟶ Y`, the
positive-degree extension groups from `L` into `ker f` vanish if they vanish into `X`, `Y` and
`coker f`, and if `Ext¹` from `L` vanishes into `ker f` and into the image `ker (coker f)`. The two
short exact sequences are `0 → ker f → X → im f → 0` and `0 → im f → Y → coker f → 0`. -/
public theorem subsingleton_ext_succ_kernel (L : C) {X Y : C} (f : X ⟶ Y)
    (hX : ∀ q : ℕ, Subsingleton (Abelian.Ext.{w} L X (q + 1)))
    (hY : ∀ q : ℕ, Subsingleton (Abelian.Ext.{w} L Y (q + 1)))
    (hC : ∀ q : ℕ, Subsingleton (Abelian.Ext.{w} L (cokernel f) (q + 1)))
    (hker : Subsingleton (Abelian.Ext.{w} L (kernel f) 1))
    (him : Subsingleton (Abelian.Ext.{w} L (kernel (cokernel.π f)) 1)) (q : ℕ) :
    Subsingleton (Abelian.Ext.{w} L (kernel f) (q + 1)) := by
  have hS₂ : (ShortComplex.mk (kernel.ι (cokernel.π f)) (cokernel.π f)
      (kernel.condition _)).ShortExact :=
    { exact := ShortComplex.exact_kernel (cokernel.π f) }
  have hw : kernel.ι f ≫ Abelian.factorThruImage f = 0 := by
    rw [← cancel_mono (Abelian.image.ι f), Category.assoc, Abelian.image.fac, kernel.condition,
      zero_comp]
  have hS₁ : (ShortComplex.mk (kernel.ι f) (Abelian.factorThruImage f) hw).ShortExact :=
    { exact := ShortComplex.exact_of_f_is_kernel _
        (isKernelOfComp (Abelian.image.ι f) f (kernelIsKernel f) hw (Abelian.image.fac f)) }
  have him' : ∀ k : ℕ, Subsingleton (Abelian.Ext.{w} L (kernel (cokernel.π f)) (k + 1)) := by
    rintro (_ | k)
    · exact him
    · exact subsingleton_ext_succ_X₁_of_shortExact L hS₂ (k + 1) (hC k) (hY (k + 1))
  cases q with
  | zero => exact hker
  | succ q => exact subsingleton_ext_succ_X₁_of_shortExact L hS₁ (q + 1) (him' q) (hX (q + 1))

end DimensionShift

variable {τ : CoveringTopology} {A : CommRingCat.{u}} (B : BigSite τ (Spec A))

/-- The module-valued functors on the `A`-algebras of the site, at the universe `u` of the site:
the target of the affine-section functor `Stacks.Adequate.affineSectionsFunctor`. -/
public abbrev siteModuleFunctors : Type (u + 1) :=
  AdequateFunctor.ModuleValuedFunctorOn.{u}
    (AdequateFunctor.siteAlgebraInclusion A (schemeSizeBelow B.cutoff))

/-- **`R^p A(𝓕) = 0` from extension vanishing along a separating family.** For `U = Spec A`
affine, an adequate `𝒪`-module `𝓕` and `p > 0`, the `p`-th right derived functor of the
adequator of [Stacks, Tag 06ZS] vanishes at `𝓕` as soon as, in the module-valued functors on the
`A`-algebras of the site, the degree-`p` extension groups from the affine sections of the members
of the separating family `Stacks.Adequate.adequateSeparatingFamily` into the affine sections of
`𝓕` vanish. -/
public theorem isZero_rightDerived_affineAdequator_of_subsingleton_ext
    [HasExt.{w} (siteModuleFunctors B)]
    (F : (adequate.{u, u} B).FullSubcategory) (p : ℕ) (hp : 0 < p)
    (hExt : ∀ L : (adequate.{u, u} B).FullSubcategory,
      adequateSeparatingFamily.{u, u} B (adequateComparisonEquivalence B) L →
      Subsingleton (Abelian.Ext.{w} (C := siteModuleFunctors B)
        ((affineSectionsFunctor.{u, u} B A (𝟙 (Spec A))).obj L.obj)
        ((affineSectionsFunctor.{u, u} B A (𝟙 (Spec A))).obj F.obj) p)) :
    letI := adequate_isClosedUnderKernels.{u, u} B
    letI := adequate_isClosedUnderCokernels.{u, u} B
    letI := adequate_isClosedUnderFiniteProducts.{u, u} B
    letI : Abelian (adequate.{u, u} B).FullSubcategory := abelian_adequate B
    letI : (affineAdequator B).Additive :=
      (affineAdequatorAdjunction B).right_adjoint_additive
    IsZero (((affineAdequator B).rightDerived p).obj F.obj) := by
  let := adequate_isClosedUnderKernels.{u, u} B
  let := adequate_isClosedUnderCokernels.{u, u} B
  let := adequate_isClosedUnderFiniteProducts.{u, u} B
  let : Abelian (adequate.{u, u} B).FullSubcategory := abelian_adequate B
  let : (affineAdequator B).Additive :=
    (affineAdequatorAdjunction B).right_adjoint_additive
  have := preservesInjectiveObjects_affineSectionsFunctor.{u, u} B
  have : (affineSectionsFunctor.{u, u} B A (𝟙 (Spec A))).Full :=
    (fullyFaithfulAffineSectionsFunctor B).full
  have : (affineSectionsFunctor.{u, u} B A (𝟙 (Spec A))).Faithful :=
    (fullyFaithfulAffineSectionsFunctor B).faithful
  exact isZero_rightDerived_of_coreflection.{w} (adequate.{u, u} B).ι (affineAdequator B)
    (affineAdequatorAdjunction B) (affineSectionsFunctor.{u, u} B A (𝟙 (Spec A)))
    (adequateSeparatingFamily.{u, u} B (adequateComparisonEquivalence B))
    (isSeparating_adequateSeparatingFamily.{u, u} B (adequateComparisonEquivalence B)) F.obj
    (affineSectionsAcyclic_of_isAdequate.{u, u} B A (𝟙 (Spec A)) F.obj F.property) p hp hExt

/-- The affine sections of a member of the separating family
`Stacks.Adequate.adequateSeparatingFamily` are a linearly adequate module-valued functor on the
`A`-algebras of the site: the member is the image under the identification of
[Stacks, Tag 06ZJ] of a linearly adequate functor presented by a map of finite free modules. -/
public theorem isLinearlyAdequate_affineSections_of_adequateSeparatingFamily
    {L : (adequate.{u, u} B).FullSubcategory}
    (hL : adequateSeparatingFamily.{u, u} B (adequateComparisonEquivalence B) L) :
    AdequateFunctor.IsLinearlyAdequate
      (AdequateFunctor.siteAlgebraInclusion A (schemeSizeBelow B.cutoff))
      ((affineSectionsFunctor.{u, u} B A (𝟙 (Spec A))).obj L.obj) := by
  obtain ⟨X, ⟨d⟩⟩ := hL
  let E := adequateComparisonEquivalence B
  let e : (affineSectionsFunctor.{u, u} B A (𝟙 (Spec A))).obj (E.inverse.obj
      (AdequateFunctor.ofLinearPresentationSite_large.{u, u} (A : Type u) B.cutoff d)).obj ≅
      (AdequateFunctor.ofLinearPresentationSite_large.{u, u} (A : Type u) B.cutoff d).obj :=
    (adequateOn.{u, u} A (schemeSizeBelow B.cutoff)).ι.mapIso (E.counitIso.app _)
  refine AdequateFunctor.IsLinearlyAdequate.of_iso ?_ e
  exact ⟨d.1, d.2.1, (AdequateFunctor.moduleExtensionFunctorOn.{u, u}
      (AdequateFunctor.siteAlgebraInclusion A (schemeSizeBelow B.cutoff))).map d.2.2,
    ⟨AdequateFunctor.presheafOfModulesUliftIso.{u, u} _ _⟩⟩

/-- **`R^p A(𝓕) = 0` from extension vanishing on the algebras of the site.** For `U = Spec A`
affine, an adequate `𝒪`-module `𝓕` and `p > 0`, the `p`-th right derived functor of the
adequator of [Stacks, Tag 06ZS] vanishes at `𝓕` as soon as, in the module-valued functors on
the `A`-algebras of the site, the positive-degree extension groups from linearly adequate
functors into adequate functors vanish. -/
public theorem isZero_rightDerived_affineAdequator_of_site
    [HasExt.{w} (siteModuleFunctors B)]
    (hS : ∀ X Y : siteModuleFunctors B,
      AdequateFunctor.IsLinearlyAdequate
        (AdequateFunctor.siteAlgebraInclusion A (schemeSizeBelow B.cutoff)) X →
      AdequateFunctor.IsAdequate
        (AdequateFunctor.siteAlgebraInclusion A (schemeSizeBelow B.cutoff)) Y →
      ∀ p : ℕ, 0 < p → Subsingleton (Abelian.Ext.{w} (C := siteModuleFunctors B) X Y p))
    (F : (adequate.{u, u} B).FullSubcategory) (p : ℕ) (hp : 0 < p) :
    letI := adequate_isClosedUnderKernels.{u, u} B
    letI := adequate_isClosedUnderCokernels.{u, u} B
    letI := adequate_isClosedUnderFiniteProducts.{u, u} B
    letI : Abelian (adequate.{u, u} B).FullSubcategory := abelian_adequate B
    letI : (affineAdequator B).Additive :=
      (affineAdequatorAdjunction B).right_adjoint_additive
    IsZero (((affineAdequator B).rightDerived p).obj F.obj) :=
  isZero_rightDerived_affineAdequator_of_subsingleton_ext.{w} B F p hp fun _ hL =>
    hS _ _ (isLinearlyAdequate_affineSections_of_adequateSeparatingFamily B hL)
      ((adequateComparison.{u, u} B).obj F).property p hp

/-- **[Stacks, Tag 06V7] on the algebras of the site, as `Ext¹`-vanishing.** The degree-one
extension group from a linearly adequate module-valued functor on the `A`-algebras of the site
into an adequate one vanishes: a class is the class of an extension, and the extension splits. -/
public theorem subsingleton_ext_one_siteModuleFunctors [HasExt.{w} (siteModuleFunctors B)]
    (X Y : siteModuleFunctors B)
    (hX : AdequateFunctor.IsLinearlyAdequate
      (AdequateFunctor.siteAlgebraInclusion A (schemeSizeBelow B.cutoff)) X)
    (hY : AdequateFunctor.IsAdequate
      (AdequateFunctor.siteAlgebraInclusion A (schemeSizeBelow B.cutoff)) Y) :
    Subsingleton (Abelian.Ext.{w} (C := siteModuleFunctors B) X Y 1) := by
  have hsplit : AdequateFunctor.LinearlyAdequateSplitting.{u, u}
      (AdequateFunctor.siteAlgebraInclusion A (schemeSizeBelow B.cutoff)) :=
    AdequateFunctor.linearlyAdequateSplitting_site.{u}
    (BigSite.aleph0_lt_cutoff_of_affine B) B.cutoff_isStrongPrelimit (A : Type u) B.base_mem
  refine subsingleton_of_forall_eq 0 fun x => ?_
  obtain ⟨E, i, p, hw, hS, rfl⟩ :=
    (Abelian.Ext.extClass_surjective_and_eq_iff_iso_and_baerSum (siteModuleFunctors B) X Y).1 x
  obtain ⟨r, hr⟩ := hsplit i p hw hS hY hX
  calc hS.extClass = hS.extClass.comp (Abelian.Ext.mk₀ (𝟙 Y)) (add_zero 1) := by simp
    _ = hS.extClass.comp (Abelian.Ext.mk₀ (i ≫ r)) (add_zero 1) := by rw [hr]
    _ = 0 := by
      rw [← Abelian.Ext.mk₀_comp_mk₀]
      exact hS.extClass_comp_assoc _

/-- Extension of scalars to the module-valued functors on the `A`-algebras of the site is right
exact: it is extension of scalars to all algebras followed by restriction to the site, and both
preserve finite colimits. -/
public instance preservesFiniteColimits_moduleExtensionFunctorOn_site :
    PreservesFiniteColimits (AdequateFunctor.moduleExtensionFunctorOn.{u, u}
      (AdequateFunctor.siteAlgebraInclusion A (schemeSizeBelow B.cutoff))) :=
  comp_preservesFiniteColimits _ _

/-- **Positive-degree `Ext` on the algebras of the site, from the module extensions.** In the
module-valued functors on the `A`-algebras of the site, the positive-degree extension groups from
a linearly adequate functor `X` into an adequate functor vanish as soon as those from `X` into
the extension of scalars of every `A`-module do. An adequate functor is the kernel of a map
`M̲ ⟶ N̲` of module extensions, whose image and kernel are adequate, so dimension shifting along
`0 → ker → M̲ → im → 0` and `0 → im → N̲ → coker → 0` reduces to `Ext¹` into adequate functors,
which is [Stacks, Tag 06V7] on the site, and to `Ext` into `M̲`, `N̲` and `coker` itself, a module
extension because extension of scalars is right exact. -/
public theorem subsingleton_ext_siteModuleFunctors_of_moduleExtension
    [HasExt.{w} (siteModuleFunctors B)]
    (X : siteModuleFunctors B)
    (hX : AdequateFunctor.IsLinearlyAdequate
      (AdequateFunctor.siteAlgebraInclusion A (schemeSizeBelow B.cutoff)) X)
    (hcore : ∀ (M : ModuleCat.{u} A) (q : ℕ),
      Subsingleton (Abelian.Ext.{w} (C := siteModuleFunctors B) X
        ((AdequateFunctor.moduleExtensionFunctorOn.{u, u}
          (AdequateFunctor.siteAlgebraInclusion A (schemeSizeBelow B.cutoff))).obj M) (q + 1)))
    (Y : siteModuleFunctors B)
    (hY : AdequateFunctor.IsAdequate
      (AdequateFunctor.siteAlgebraInclusion A (schemeSizeBelow B.cutoff)) Y) (q : ℕ) :
    Subsingleton (Abelian.Ext.{w} (C := siteModuleFunctors B) X Y (q + 1)) := by
  let ι := AdequateFunctor.siteAlgebraInclusion (A : Type u) (schemeSizeBelow B.cutoff)
  let E := AdequateFunctor.moduleExtensionFunctorOn.{u, u} ι
  obtain ⟨M, N, f, ⟨e⟩⟩ := hY
  let eY : Y ≅ kernel (E.map f) :=
    (AdequateFunctor.presheafOfModulesUliftIso.{u, u} _ Y).symm ≪≫ e
  let c : cokernel (E.map f) ≅ E.obj (cokernel f) := (PreservesCokernel.iso E f).symm
  have hc : cokernel.π (E.map f) ≫ c.hom = E.map (cokernel.π f) := by simp [c]
  have hker : AdequateFunctor.IsAdequate ι (kernel (E.map f)) :=
    ⟨M, N, f, ⟨AdequateFunctor.presheafOfModulesUliftIso.{u, u} _ _⟩⟩
  have him : AdequateFunctor.IsAdequate ι (kernel (cokernel.π (E.map f))) :=
    ⟨N, cokernel f, cokernel.π f, ⟨AdequateFunctor.presheafOfModulesUliftIso.{u, u} _ _ ≪≫
      (kernelCompMono (cokernel.π (E.map f)) c.hom).symm ≪≫ kernelIsoOfEq hc⟩⟩
  exact Stacks.CohomologyVanishing.subsingleton_ext_of_iso_target eY.symm (q + 1)
    (subsingleton_ext_succ_kernel X (E.map f) (hcore M) (hcore N)
      (fun k => Stacks.CohomologyVanishing.subsingleton_ext_of_iso_target c.symm (k + 1)
        (hcore (cokernel f) k))
      (subsingleton_ext_one_siteModuleFunctors B X _ hX hker)
      (subsingleton_ext_one_siteModuleFunctors B X _ hX him) q)

end Stacks.Adequate

end
