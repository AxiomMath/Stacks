module

public import StacksFrontier.AlgebraicGeometry.Adequate.AdequateFunctors.DomainCoproduct
public import StacksFrontier.AlgebraicGeometry.Adequate.AdequateFunctors.DomainCokernels
public import StacksFrontier.AlgebraicGeometry.Adequate.AdequateFunctors.Extensions
public import StacksFrontier.AlgebraicGeometry.Adequate.AdequateModules.AffineAdequateColimits
public import StacksFrontier.AlgebraicGeometry.Adequate.AdequateModules.AffineSectionExactness

/-!
# Tag 06V8 on a restricted domain of algebras

[Stacks, Tag 06V8] — adequate module-valued functors are closed under extensions — is proved for
the full domain of commutative `A`-algebras as `AdequateFunctor.isAdequate_of_shortExact`. This
file carries the *argument* to a domain `ι : C ⥤ CommAlgCat A`, and then to the algebras of a
site, leaving exactly one input open: the splitting property of [Stacks, Tag 06V7] on that
domain.

That proof goes through unchanged. A coproduct of linearly adequate functors covers the
target by [Stacks, Tag 06UX] on the domain; the splitting property lifts the covering one
summand at a time through the epimorphism, and the assembled lift splits the pullback of the
extension along the covering, exhibiting that pullback as the biproduct of the kernel term with
the covering coproduct. The middle term is then the cokernel of the kernel of the pullback's
other projection, and both of those are adequate, so [Stacks, Tag 06V2] on the domain finishes.

## Main definitions

* `AdequateFunctor.LinearlyAdequateSplitting` — [Stacks, Tag 06V7] on a domain of algebras: an
  extension of a linearly adequate module-valued functor by an adequate one splits. This is the
  one input of 06V8 that the library does not yet have on a restricted domain, and it is taken
  as an explicit hypothesis, as `AdequateFunctor.isAdequate_of_descent_on` takes closure under
  kernels.

## Main results

* `AdequateFunctor.isAdequate_of_isLinearlyAdequate_on` — a linearly adequate module-valued
  functor on a domain of algebras with a base object is adequate.
* `AdequateFunctor.isAdequate_of_shortExact_on` — [Stacks, Tag 06V8] on a restricted domain of
  algebras, given a base algebra object, the lifting property of [Stacks, Tag 06V0] there, and
  the splitting property of [Stacks, Tag 06V7] there.
* `AdequateFunctor.isAdequate_of_shortExact_site` — the same over the algebras of a site, where
  the first two of those inputs are discharged.
* `Stacks.Adequate.affineAdequateExtensions_of_linearlyAdequateSplitting` —
  `Stacks.Adequate.AffineAdequateExtensions` holds as soon as [Stacks, Tag 06V7] holds on the
  algebras of the site, at the full universe generality `.{u, m}` of that property.

## Implementation notes

No `@[stacks]` attribute is placed here: the tagged statement of 06V8 is
`AdequateFunctor.isAdequate_of_shortExact`, over all commutative algebras, and these are that
statement transported to a restricted domain, not further parts of the tag's covering set. This
is the same convention as `AdequateFunctor.isAdequate_kernel_on` for 06V3 and
`AdequateFunctor.isAdequate_cokernel_on` for 06V2.

Two ingredients of that proof have no analogue on a restricted domain and are supplied
here. `AdequateFunctor.isAdequate_of_isLinearlyAdequate_on` replaces
`AdequateFunctor.IsLinearlyAdequate.isAdequate`, reading the presenting map of finite free module
extensions off as a map of modules by fullness of extension of scalars, which is why it needs a
base algebra object. `AdequateFunctor.isAdequate_coproduct_on` replaces
`AdequateFunctor.isAdequate_coproduct`, by the same manoeuvre as
`AdequateFunctor.exists_coproduct_linearlyAdequate_surjective_on`: each summand is the
restriction of an adequate functor on all algebras by
`AdequateFunctor.IsAdequate.exists_extension`, legitimate here because adequacy of the summands
is a hypothesis, and reindexing preserves coproducts.

Unlike kernels and cokernels, the universe generality is not inherited. The library's 06V8 and its
engine `AdequateFunctor.exists_retraction_of_shortExact` are stated only on the single-universe
diagonal `ModuleValuedFunctor.{u, u} A`, because the weight-space decomposition of
[Stacks, Tag 06UZ] and the lifting criterion of [Stacks, Tag 06V5] are proved for
`AdequateFunctor.Laurent.ModuleValuedFunctor`, which pins the value universe to the universe of
the base ring. An affine-section functor needs the value universe `max u m`, so neither the
domain nor the universe of `AdequateFunctor.LinearlyAdequateSplitting` is reachable by
instantiating the existing statement.

## References

* [Stacks Project, Tag 06UX](https://stacks.math.columbia.edu/tag/06UX)
* [Stacks Project, Tag 06V0](https://stacks.math.columbia.edu/tag/06V0)
* [Stacks Project, Tag 06V2](https://stacks.math.columbia.edu/tag/06V2)
* [Stacks Project, Tag 06V7](https://stacks.math.columbia.edu/tag/06V7)
* [Stacks Project, Tag 06V8](https://stacks.math.columbia.edu/tag/06V8)
-/

@[expose] public noncomputable section

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits

universe w v u m u₁ v₁

namespace AdequateFunctor

section Domain

variable {A : Type u} [CommRing A] {C : Type u₁} [Category.{v₁} C]

/-- A linearly adequate module-valued functor on a domain of algebras with a base object is
adequate: fullness of extension of scalars reads the presenting map of finite free module
extensions off as a map of modules. -/
public theorem isAdequate_of_isLinearlyAdequate_on {ι : C ⥤ CommAlgCat.{max u v} A}
    (b : BaseAlgebraObject.{v} ι) {F : ModuleValuedFunctorOn.{max u v w, v} ι}
    (hF : IsLinearlyAdequate.{max u v w, v} ι F) :
    IsAdequate.{max u v w, v} ι F := by
  obtain ⟨n, m, f, ⟨e⟩⟩ := hF
  exact ⟨_, _, moduleHomOfExtensionNatTransOn.{max u v w} b f,
    ⟨e ≪≫ kernelIsoOfEq (moduleExtension_natTransOn_eq_map.{max u v w} b f)⟩⟩


/-- Splitting of an extension of a linearly adequate module-valued functor by an adequate one on
a domain of algebras: [Stacks, Tag 06V7] on that domain. -/
public abbrev LinearlyAdequateSplitting (ι : C ⥤ CommAlgCat.{max u v} A) : Prop :=
  ∀ {F E L : ModuleValuedFunctorOn.{max u v w, v} ι}
    (i : F ⟶ E) (p : E ⟶ L) (hip : i ≫ p = 0),
    (ShortComplex.mk i p hip).ShortExact →
    IsAdequate.{max u v w, v} ι F → IsLinearlyAdequate.{max u v w, v} ι L →
    ∃ r : E ⟶ F, i ≫ r = 𝟙 F

/-- **Stacks Lemma 06V8 on a restricted domain of algebras.** The middle term of a short exact
sequence of module-valued functors on a domain of algebras whose outer terms are adequate is
adequate, given a base algebra object, the lifting property of [Stacks, Tag 06V0] on that
domain, and the splitting property of [Stacks, Tag 06V7] there.

The proof of 06V8 over all algebras goes through unchanged. A coproduct of linearly adequate
functors covers the target by [Stacks, Tag 06UX] on the domain; the splitting property lifts the
covering one summand at a time through the epimorphism, and the assembled lift splits the pullback
of the extension along the covering, exhibiting that pullback as a biproduct. The middle term is
then the cokernel of the kernel of the pullback's other projection, and both of those are adequate,
so [Stacks, Tag 06V2] on the domain finishes. -/
public theorem isAdequate_of_shortExact_on {ι : C ⥤ CommAlgCat.{max u v} A}
    (b : BaseAlgebraObject.{v} ι) (hlift : FiniteFreeKernelLifting.{w, v} ι)
    (hsplit : LinearlyAdequateSplitting.{w, v} ι)
    (S : ShortComplex (ModuleValuedFunctorOn.{max u v w, v} ι)) (hS : S.ShortExact)
    (h₁ : IsAdequate.{max u v w, v} ι S.X₁) (h₃ : IsAdequate.{max u v w, v} ι S.X₃) :
    IsAdequate.{max u v w, v} ι S.X₂ := by
  classical
  have := hS.mono_f
  have := hS.epi_g
  obtain ⟨J, L, hL, cover₀, hcover₀⟩ :=
    exists_coproduct_linearlyAdequate_surjective_on.{max u v w} ι S.X₃ h₃
  obtain ⟨cover, hcover⟩ : ∃ cover : (∐ L) ⟶ S.X₃, Epi cover :=
    ⟨cover₀ ≫ (presheafOfModulesUliftIso.{max u v, max u v w}
        (algebraRingDiagramOn.{v} ι) S.X₃).hom,
      have : Epi cover₀ := PresheafOfModules.epi_of_surjective hcover₀
      epi_comp _ _⟩
  have := hcover
  have hLad : ∀ j, IsAdequate.{max u v w, v} ι (L j) := fun j =>
    isAdequate_of_isLinearlyAdequate_on.{w} b (hL j)
  have hLsum : IsAdequate.{max u v w, v} ι (∐ L) := isAdequate_coproduct_on.{w} L hLad
  have hkerCover : IsAdequate.{max u v w, v} ι (kernel cover) :=
    isAdequate_kernel_on.{w} b hlift cover hLsum h₃
  have hlifts : ∀ j, ∃ s : L j ⟶ S.X₂, s ≫ S.g = Sigma.ι L j ≫ cover := by
    intro j
    obtain ⟨jj, hj, hjSE⟩ := exists_shortExact_pullback hS (Sigma.ι L j ≫ cover)
    obtain ⟨r, hr⟩ := hsplit jj _ hj hjSE h₁ (hL j)
    have spl := ShortComplex.Splitting.ofExactOfRetraction _ hjSE.exact r hr hjSE.epi_g
    refine ⟨spl.s ≫ pullback.fst S.g (Sigma.ι L j ≫ cover), ?_⟩
    rw [Category.assoc, pullback.condition, ← Category.assoc, spl.s_g, Category.id_comp]
  choose s hs using hlifts
  have hsec : Sigma.desc s ≫ S.g = cover := by
    refine Sigma.hom_ext _ _ fun j => ?_
    rw [← Category.assoc, Sigma.ι_comp_desc]
    exact hs j
  obtain ⟨j, hj, hjSE⟩ := exists_shortExact_pullback hS cover
  obtain ⟨σ, hσ⟩ : ∃ σ : (∐ L) ⟶ pullback S.g cover, σ ≫ pullback.snd S.g cover = 𝟙 _ :=
    ⟨pullback.lift (Sigma.desc s) (𝟙 (∐ L)) (by rw [hsec, Category.id_comp]),
      pullback.lift_snd _ _ _⟩
  have splP := ShortComplex.Splitting.ofExactOfSection _ hjSE.exact σ hσ hjSE.mono_f
  have hPad : IsAdequate.{max u v w, v} ι (pullback S.g cover) :=
    (IsAdequate.biprod ι h₁ hLsum).of_iso splP.isoBinaryBiproduct
  have sq : IsPullback (pullback.fst S.g cover) (pullback.snd S.g cover) S.g cover :=
    IsPullback.of_hasPullback S.g cover
  have hkerfst : IsAdequate.{max u v w, v} ι (kernel (pullback.fst S.g cover)) :=
    hkerCover.of_iso (have := isIso_kernel_map_of_isPullback sq; asIso (kernel.map
      (pullback.fst S.g cover) cover (pullback.snd S.g cover) S.g sq.w))
  have hfinal : (ShortComplex.mk (kernel.ι (pullback.fst S.g cover)) (pullback.fst S.g cover)
      (kernel.condition _)).ShortExact :=
    ShortComplex.ShortExact.mk'
      (ShortComplex.exact_of_f_is_kernel _ (kernelIsKernel _)) inferInstance inferInstance
  exact (isAdequate_cokernel_on.{w} b hlift
    (kernel.ι (pullback.fst S.g cover)) hkerfst hPad).of_iso
    (IsColimit.coconePointUniqueUpToIso (cokernelIsCokernel _) hfinal.gIsCokernel).symm

end Domain

/-! ### Tag 06V8 over the algebras of a site -/

section Site

variable {κ : Cardinal.{u}} (hκ : Cardinal.aleph0 < κ) (hsl : Cardinal.IsStrongPrelimit κ)

include hκ hsl in
/-- **Stacks Lemma 06V8 over the algebras of a site**, given the splitting property of
[Stacks, Tag 06V7] there. The two generic inputs of
`AdequateFunctor.isAdequate_of_shortExact_on` are discharged exactly as for kernels and
cokernels: the base ring as an object of the site,
`AdequateFunctor.BaseAlgebraObject.siteOfSpecMem`, and the lifting property of
[Stacks, Tag 06V0] there, `AdequateFunctor.finiteFreeKernelLifting_site`. The splitting
property remains a hypothesis. -/
public theorem isAdequate_of_shortExact_site (A : Type u) [CommRing A]
    (hA : (Spec (CommRingCat.of A)).size < κ)
    (hsplit : LinearlyAdequateSplitting.{w, u}
      (siteAlgebraInclusion.{u, u} A (schemeSizeBelow κ)))
    (T : ShortComplex (ModuleValuedFunctorOn.{max u w, u}
      (siteAlgebraInclusion.{u, u} A (schemeSizeBelow κ))))
    (hT : T.ShortExact)
    (h₁ : IsAdequate (siteAlgebraInclusion.{u, u} A (schemeSizeBelow κ)) T.X₁)
    (h₃ : IsAdequate (siteAlgebraInclusion.{u, u} A (schemeSizeBelow κ)) T.X₃) :
    IsAdequate (siteAlgebraInclusion.{u, u} A (schemeSizeBelow κ)) T.X₂ :=
  isAdequate_of_shortExact_on.{w, u} (BaseAlgebraObject.siteOfSpecMem (schemeSizeBelow κ) hA)
    (finiteFreeKernelLifting_site.{w} hκ hsl A hA) hsplit T hT h₁ h₃

end Site

end AdequateFunctor

namespace Stacks.Adequate

variable {τ : CoveringTopology} {S : Scheme.{u}} (B : BigSite τ S)

/-- `Stacks.Adequate.AffineAdequateExtensions` holds as soon as [Stacks, Tag 06V7] holds on the
algebras of the site, at the full universe generality of the property: adequacy of module-valued
functors on the algebras of the site over an affine scheme of the site is then closed under
extensions.

This is `AdequateFunctor.isAdequate_of_shortExact_site`, whose two unconditional inputs are the
same as those of `Stacks.Adequate.affineAdequateKernels` and
`Stacks.Adequate.affineAdequateCokernels` — the base ring as an object of the site and the
lifting property of [Stacks, Tag 06V0] there, carried by the two unconditional clauses of
[Stacks, Tag 000R] (9) together with the cutoff's being an uncountable strong prelimit. -/
public theorem affineAdequateExtensions_of_linearlyAdequateSplitting
    (hsplit : ∀ (A : CommRingCat.{u}), schemeSizeBelow B.cutoff (Spec A) →
      AdequateFunctor.LinearlyAdequateSplitting.{m, u}
        (AdequateFunctor.siteAlgebraInclusion A (schemeSizeBelow B.cutoff))) :
    AffineAdequateExtensions.{u, m} B := fun A hA T hT h₁ h₃ ↦
  AdequateFunctor.isAdequate_of_shortExact_site.{m}
    (lt_of_le_of_lt (Scheme.aleph0_le_size (Spec A)) hA)
    B.cutoff_isStrongPrelimit A hA (hsplit A hA) T hT h₁ h₃

end Stacks.Adequate

end
