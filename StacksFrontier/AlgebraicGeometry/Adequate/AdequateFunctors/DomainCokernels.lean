module

public import StacksFrontier.AlgebraicGeometry.Adequate.AdequateFunctors.DomainKernels
public import StacksCore.CategoryTheory.Abelian.CommSq

/-!
# Cokernels of adequate functors on a restricted domain of algebras

[Stacks, Tag 06V2] — adequate module-valued functors are closed under cokernels — holds for the
full domain of commutative `A`-algebras as `AdequateFunctor.isAdequate_cokernel`. This file
carries it to a domain `ι : C ⥤ CommAlgCat A` with a base algebra object on which the lifting
property of [Stacks, Tag 06V0] holds, and then to the algebras of a site, where both inputs are
available.

The proof is that of 06V2. A mono `iG : G ↪ E M` is read off a kernel presentation of the
target; [Stacks, Tag 06V1] makes `Coker(φ ≫ iG)` adequate, so that cokernel too embeds in a
module extension, `iW : Coker(φ ≫ iG) ↪ E N`; the third isomorphism theorem's mono
`Coker φ ⟶ Coker(φ ≫ iG)` composed with `iW` is then a mono `q : Coker φ ↪ E N`, and
`ψ = π ≫ q : G ⟶ E N` factors as an epi onto `Coker φ` followed by `q`. One more application of
06V1 embeds `Coker ψ` in a module extension `E P`, and `Coker φ` is the kernel of the composite
`fQ : E N ↠ Coker ψ ↪ E P`, being the image of `ψ`. Fullness of extension of scalars on the
domain reads `fQ` off as a map of modules, which is the kernel presentation wanted.

Only two steps of that argument are not generic, and both are available on a restricted domain:
06V1 there is `AdequateFunctor.isAdequate_cokernel_to_moduleExtension_on`, and fullness is
`AdequateFunctor.full_moduleExtensionFunctorOn`, used through
`AdequateFunctor.moduleHomOfExtensionNatTransOn`. The values of the functors are taken in a
universe already containing the ring and algebra universes, so
`AdequateFunctor.presheafOfModulesUliftIso` erases the universe lift of
`AdequateFunctor.IsKernelPresentation`.

## Main results

* `AdequateFunctor.exists_mono_to_moduleExtension_on` — an adequate module-valued functor on a
  domain of algebras embeds into the module extension of a module.
* `AdequateFunctor.isAdequate_cokernel_on` — [Stacks, Tag 06V2] on a restricted domain of
  algebras, given a base algebra object and the lifting property of [Stacks, Tag 06V0] there.
* `AdequateFunctor.isAdequate_cokernel_site` — [Stacks, Tag 06V2] over the algebras of a site.

## Implementation notes

The lifting property of [Stacks, Tag 06V0] over the algebras of a site is
`AdequateFunctor.finiteFreeKernelLifting_site`.

## References

* [Stacks Project, Tag 06V0](https://stacks.math.columbia.edu/tag/06V0)
* [Stacks Project, Tag 06V1](https://stacks.math.columbia.edu/tag/06V1)
* [Stacks Project, Tag 06V2](https://stacks.math.columbia.edu/tag/06V2)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry

universe w v u u₁ v₁

namespace AdequateFunctor

section Domain

variable {A : Type u} [CommRing A] {C : Type u₁} [Category.{v₁} C]

/-- An adequate module-valued functor on a domain of algebras embeds into the module extension of
a module: the source of any kernel presentation of it does, the mono being the kernel
inclusion. -/
public theorem exists_mono_to_moduleExtension_on {ι : C ⥤ CommAlgCat.{max u v} A}
    {F : ModuleValuedFunctorOn.{max u v w, v} ι} (hF : IsAdequate.{max u v w, v} ι F) :
    ∃ (M : ModuleCat.{max u v w} A)
      (i : F ⟶ (moduleExtensionFunctorOn.{max u v w, v} ι).obj M), Mono i := by
  obtain ⟨M, N, f, ⟨e⟩⟩ := hF
  refine ⟨M, (presheafOfModulesUliftIso.{max u v, max u v w}
    (algebraRingDiagramOn.{v} ι) F).symm.hom ≫ e.hom ≫
    kernel.ι ((moduleExtensionFunctorOn.{max u v w, v} ι).map f), inferInstance⟩

/-- [Stacks, Tag 06V2] on a restricted domain of algebras: the cokernel of a morphism of
adequate module-valued functors on a domain of algebras is adequate, given a base algebra object
and the lifting property of [Stacks, Tag 06V0] on that domain. -/
public theorem isAdequate_cokernel_on {ι : C ⥤ CommAlgCat.{max u v} A}
    (b : BaseAlgebraObject.{v} ι) (hlift : FiniteFreeKernelLifting.{w, v} ι)
    {F G : ModuleValuedFunctorOn.{max u v w, v} ι} (φ : F ⟶ G)
    (hF : IsAdequate.{max u v w, v} ι F) (hG : IsAdequate.{max u v w, v} ι G) :
    IsAdequate.{max u v w, v} ι (cokernel φ) := by
  classical
  let E := moduleExtensionFunctorOn.{max u v w, v} ι
  obtain ⟨M, iG, hiG⟩ := exists_mono_to_moduleExtension_on.{w} hG
  let ψ₁ : F ⟶ E.obj M := φ ≫ iG
  obtain ⟨Nn, iW, hiW⟩ := exists_mono_to_moduleExtension_on.{w}
    (isAdequate_cokernel_to_moduleExtension_on b hlift F M ψ₁ hF)
  let a : cokernel φ ⟶ cokernel ψ₁ := cokernel.map φ ψ₁ (𝟙 _) iG (by simp [ψ₁])
  let q : cokernel φ ⟶ E.obj Nn := a ≫ iW
  have : Mono q := by dsimp only [q, a, ψ₁]; infer_instance
  let ψ : G ⟶ E.obj Nn := cokernel.π φ ≫ q
  obtain ⟨P, m, hm⟩ := exists_mono_to_moduleExtension_on.{w}
    (isAdequate_cokernel_to_moduleExtension_on b hlift G Nn ψ hG)
  let fQ : E.obj Nn ⟶ E.obj P := cokernel.π ψ ≫ m
  let fac : StrongEpiMonoFactorisation ψ :=
    StrongEpiMonoFactorisation.mk
      (MonoFactorisation.mk (cokernel φ) q (cokernel.π φ) (by simp [ψ, q]))
  have hKImg : IsLimit (KernelFork.ofι (f := fQ) (Abelian.image.ι ψ)
      (by simp [Abelian.image, fQ])) := by
    refine Fork.IsLimit.mk _ (fun s => kernel.lift (cokernel.π ψ) s.ι ?_) ?_ ?_
    · exact (cancel_mono m).1 (by simp [fQ, Category.assoc])
    · intro s; simp [Abelian.image, fQ]
    · intro s k hk
      exact (cancel_mono (Abelian.image.ι ψ)).1 (by simpa [Abelian.image] using hk)
  let eK : cokernel φ ≅ kernel fQ :=
    (IsImage.isoExt fac.toMonoIsImage
      (Abelian.imageStrongEpiMonoFactorisation ψ).toMonoIsImage).trans <|
      IsLimit.conePointUniqueUpToIso
      (s := KernelFork.ofι (Abelian.image.ι ψ) (by simp [Abelian.image, fQ]))
      (t := KernelFork.ofι (kernel.ι fQ) (kernel.condition fQ))
      hKImg (kernelIsKernel fQ)
  refine ⟨Nn, P, moduleHomOfExtensionNatTransOn.{max u v w} b fQ, ⟨?_⟩⟩
  exact presheafOfModulesUliftIso.{max u v, max u v w} (algebraRingDiagramOn.{v} ι)
    (cokernel φ) ≪≫ eK ≪≫
    kernelIsoOfEq (moduleExtension_natTransOn_eq_map.{max u v w} b fQ)

end Domain

/-! ### Cokernels over the algebras of a site -/

section Site

variable {κ : Cardinal.{u}} (hκ : Cardinal.aleph0 < κ) (hsl : Cardinal.IsStrongPrelimit κ)

include hκ hsl in
/-- [Stacks, Tag 06V2] over the algebras of a site: the cokernel of a morphism of adequate
module-valued functors on the algebras whose spectra have size below the cutoff is adequate. -/
public theorem isAdequate_cokernel_site (A : Type u) [CommRing A]
    (hA : (Spec (CommRingCat.of A)).size < κ)
    {F G : ModuleValuedFunctorOn.{max u w, u}
      (siteAlgebraInclusion.{u, u} A (schemeSizeBelow κ))}
    (φ : F ⟶ G)
    (hF : IsAdequate (siteAlgebraInclusion.{u, u} A (schemeSizeBelow κ)) F)
    (hG : IsAdequate (siteAlgebraInclusion.{u, u} A (schemeSizeBelow κ)) G) :
    IsAdequate (siteAlgebraInclusion.{u, u} A (schemeSizeBelow κ)) (cokernel φ) :=
  isAdequate_cokernel_on.{w, u} (BaseAlgebraObject.siteOfSpecMem (schemeSizeBelow κ) hA)
    (finiteFreeKernelLifting_site.{w} hκ hsl A hA) φ hF hG

end Site

end AdequateFunctor

end
