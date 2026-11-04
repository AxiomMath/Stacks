module

public import StacksFrontier.AlgebraicGeometry.Adequate.AdequateFunctors.CokernelToExtension
public import StacksFrontier.AlgebraicGeometry.Adequate.AdequateFunctors.DomainCoproduct
public import StacksFrontier.AlgebraicGeometry.Adequate.AdequateFunctors.DomainFullness

/-!
# Cokernels into module extensions on a restricted domain of algebras

[Stacks, Tag 06V1] — the cokernel of a morphism from an adequate module-valued functor to the
functor of a module is adequate — is proved for the full domain of commutative `A`-algebras as
`AdequateFunctor.isAdequate_cokernel_to_moduleExtension`. On a restricted domain
`ι : C ⥤ CommAlgCat A` the obstruction is the usual one: a morphism defined only on the domain
need not be the restriction of a morphism on all algebras.

For a morphism that *is* such a restriction there is no obstruction at all, and this file records
that case. Reindexing preserves cokernels, because colimits of presheaves of modules are computed
objectwise, so the cokernel of a restricted morphism is the restriction of the cokernel;
`AdequateFunctor.isAdequate_cokernel_to_moduleExtension` makes that cokernel adequate on all
algebras, and `AdequateFunctor.IsAdequate.restrictDomain` brings adequacy back to the domain.

That case is `AdequateFunctor.isAdequate_cokernel_restrictDomain`, and it is already the whole
of 06V1 for the morphism `Ker(E δ) ⟶ E M` assembled from two maps of *modules* `δ` and `g`:
reindexing preserves the kernel, so both factors are restrictions. That is
`AdequateFunctor.isAdequate_cokernel_kernelComp_restrictDomain`.

An *arbitrary* morphism out of an adequate functor is then reduced to that one, which is 06V1 on
a restricted domain in full and is what a restricted-domain [Stacks, Tag 06V3] needs. The
reduction is the front half of the proof of
`AdequateFunctor.isAdequate_cokernel_to_moduleExtension`: [Stacks, Tag 06UX] on the domain covers
the source by linearly adequate functors, [Stacks, Tag 06V0] on the domain extends each piece's
morphism into `E M` along the piece's presenting kernel, and fullness of extension of scalars
reads those extensions off as maps of modules. Their sum is the `g` above, the sum of the
presenting maps is the `δ`, and the covering morphism is identified with `Ker(E δ) ⟶ E M`.

## Main results

* `AdequateFunctor.isAdequate_cokernel_restrictDomain` — the cokernel of the restriction of a
  morphism from an adequate functor to a module extension is adequate on the domain.
* `AdequateFunctor.isAdequate_cokernel_kernelComp_restrictDomain` — the same for the morphism
  `Ker(E δ) ⟶ E P` assembled from two maps of modules.
* `AdequateFunctor.isAdequate_cokernel_to_moduleExtension_on` — [Stacks, Tag 06V1] on a
  restricted domain for an arbitrary morphism, given a base algebra object and the lifting
  property of [Stacks, Tag 06V0] on the domain.

## Implementation notes

No `@[stacks]` attribute is placed here: the tagged statement of 06V1 is
`AdequateFunctor.isAdequate_cokernel_to_moduleExtension`, over all commutative algebras, and
these are that statement transported to a restricted domain, not further parts of the tag's
covering set.

The lifting property of 06V0 is taken as the hypothesis
`AdequateFunctor.FiniteFreeKernelLifting` rather than extracted from a chosen domain, so that
nothing here depends on a set-theoretic cutoff; over the algebras of a site it is
`AdequateFunctor.exists_lift_from_finite_free_kernel_site`.

Three typeclass inputs of the front half are stated for the full domain of algebras in
`StacksFrontier/AlgebraicGeometry/Adequate/AdequateFunctors/CokernelToExtension.lean` and are not
found by instance synthesis on a restricted domain: extension of scalars preserving coproducts, the
module-valued functors having exact coproducts, and coproducts preserving finite limits. The first
two are `AdequateFunctor.moduleExtension_preservesCoproduct` and
`AdequateFunctor.toPresheaf_reflectsIsomorphisms` of that file, stated with the domain generic and
applied directly, and the third follows from the second by
`HasExactColimitsOfShape.preservesFiniteLimits`. Reindexing preserves colimits of every shape by
`AdequateFunctor.pushforward₀_preservesColimitsOfShape`, which is what reduces the first to
extension of scalars on *all* algebras preserving coproducts.

## References

* [Stacks Project, Tag 06V1](https://stacks.math.columbia.edu/tag/06V1)
* [Stacks Project, Tag 06V3](https://stacks.math.columbia.edu/tag/06V3)
* [Stacks Project, Tag 06Z3](https://stacks.math.columbia.edu/tag/06Z3)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits

universe w v u u₁ v₁

namespace AdequateFunctor

/-- Reindexing a presheaf of modules preserves the cokernel of a morphism. -/
public theorem pushforward₀_preservesColimit_parallelPair
    {A : Type u} [CommRing A] {C : Type u₁} [Category.{v₁} C]
    (ι : C ⥤ CommAlgCat.{max u v} A)
    {F G : ModuleValuedFunctor.{max u v w, v} A} (c : F ⟶ G) :
    PreservesColimit (parallelPair c 0)
      (restrictDomain.{max u v w, v} ι (𝟭 (CommAlgCat.{max u v} A))) :=
  (pushforward₀_preservesColimitsOfShape.{max u v w} ι.op (algebraRingDiagram.{v} A)
    WalkingParallelPair).preservesColimit

/-- The cokernel of the restriction to a domain of algebras of a morphism from an adequate
module-valued functor to the functor of a module is adequate on that domain: this is
[Stacks, Tag 06V1] for a morphism restricted from all algebras.

Reindexing preserves the cokernel, so the cokernel of the restriction is the restriction of the
cokernel, which [Stacks, Tag 06V1] makes adequate on all algebras. -/
public theorem isAdequate_cokernel_restrictDomain
    {A : Type u} [CommRing A] {C : Type u₁} [Category.{v₁} C]
    (ι : C ⥤ CommAlgCat.{max u v} A)
    (F : ModuleValuedFunctor.{max u v w, v} A) (M : ModuleCat.{max u v w} A)
    (c : F ⟶ moduleExtension.{max u v w, v} A M)
    (hF : IsAdequate.{max u v w, v} (𝟭 _) F) :
    IsAdequate.{max u v w, v} ι
      (cokernel ((restrictDomain.{max u v w, v} ι (𝟭 (CommAlgCat.{max u v} A))).map c)) := by
  let R := restrictDomain.{max u v w, v} ι (𝟭 (CommAlgCat.{max u v} A))
  have : PreservesColimit (parallelPair c 0) R :=
    pushforward₀_preservesColimit_parallelPair.{max u v w} ι c
  have hfull : IsAdequate.{max u v w, v} (𝟭 _) (cokernel c) :=
    isAdequate_cokernel_to_moduleExtension A F M c hF
  exact (IsAdequate.restrictDomain.{max u v w} ι (𝟭 _) (cokernel c) hfull).of_iso
    (PreservesCokernel.iso R c).symm

/-! ### The front half: Tag 06V1 on a restricted domain for an arbitrary morphism -/

section FrontHalf

variable {A : Type u} [CommRing A] {C : Type u₁} [Category.{v₁} C]

/-- The cokernel of the morphism `Ker(E δ) ⟶ E P` assembled from two maps of modules
`δ : M ⟶ N` and `g : M ⟶ P` is adequate on any domain of algebras.

Both `kernel.ι (E δ)` and `E g` are restrictions of their counterparts over all algebras —
reindexing preserves the kernel — so the composite is a restriction, and
`AdequateFunctor.isAdequate_cokernel_restrictDomain` applies: its source `Ker(E δ)` is adequate
over all algebras by its own kernel presentation, and its target is a module extension. -/
public theorem isAdequate_cokernel_kernelComp_restrictDomain (ι : C ⥤ CommAlgCat.{max u v} A)
    {Mm Nn Pp : ModuleCat.{max u v w} A} (δ : Mm ⟶ Nn) (g : Mm ⟶ Pp) :
    IsAdequate.{max u v w, v} ι
      (cokernel (kernel.ι ((moduleExtensionFunctorOn.{max u v w, v} ι).map δ) ≫
        (moduleExtensionFunctorOn.{max u v w, v} ι).map g)) := by
  let Ef := moduleExtensionFunctor.{max u v w, v} A
  let R := restrictDomain.{max u v w, v} ι (𝟭 (CommAlgCat.{max u v} A))
  let c : kernel (Ef.map δ) ⟶ Ef.obj Pp := kernel.ι (Ef.map δ) ≫ Ef.map g
  have hF : IsAdequate.{max u v w, v} (𝟭 _) (kernel (Ef.map δ)) :=
    ⟨Mm, Nn, δ, ⟨presheafOfModulesUliftIso (algebraRingDiagram.{v} A) _⟩⟩
  have h := isAdequate_cokernel_restrictDomain ι (kernel (Ef.map δ)) Pp c hF
  refine h.of_iso ?_
  have : PreservesLimit (parallelPair (Ef.map δ) 0) R :=
    pushforward₀_preservesLimit_parallelPair ι.op (algebraRingDiagram.{v} A) (Ef.map δ)
  let e : R.obj (kernel (Ef.map δ)) ≅
      kernel ((moduleExtensionFunctorOn.{max u v w, v} ι).map δ) :=
    PreservesKernel.iso R (Ef.map δ)
  -- Supply the cokernel explicitly; instance search for it is expensive.
  have : HasCokernel (R.map c) := HasCokernels.has_colimit _
  refine cokernel.mapIso _ (R.map c) e.symm (Iso.refl _) ?_
  have hι : e.hom ≫ kernel.ι ((moduleExtensionFunctorOn.{max u v w, v} ι).map δ) =
      R.map (kernel.ι (Ef.map δ)) := by
    show kernelComparison (Ef.map δ) R ≫ _ = _
    exact kernelComparison_comp_ι (Ef.map δ) R
  have hc : R.map c = e.hom ≫ kernel.ι ((moduleExtensionFunctorOn.{max u v w, v} ι).map δ) ≫
      (moduleExtensionFunctorOn.{max u v w, v} ι).map g := by
    show R.map (kernel.ι (Ef.map δ) ≫ Ef.map g) = _
    rw [Functor.map_comp, ← hι, Category.assoc]
    rfl
  rw [hc]
  simp only [Iso.refl_hom, Category.comp_id, Iso.symm_hom]
  rw [← Category.assoc, Iso.inv_hom_id, Category.id_comp]


/-- The lifting property of [Stacks, Tag 06V0] on a domain of algebras, as a hypothesis: every
morphism from the kernel of a map of finite free module extensions on the domain into a module
extension on the domain extends along that kernel's inclusion.

Over the algebras of a site this is `AdequateFunctor.exists_lift_from_finite_free_kernel_site`;
in general it is `AdequateFunctor.exists_lift_from_finite_free_kernel_on`, whose three inputs
constrain the domain. It is taken as a hypothesis here so that the proof of [Stacks, Tag 06V1]
below is about a domain of algebras and not about a set-theoretic cutoff. -/
public abbrev FiniteFreeKernelLifting (ι : C ⥤ CommAlgCat.{max u v} A) : Prop :=
  ∀ (M : ModuleCat.{max u v w} A) (n m : ℕ) (L : ModuleValuedFunctorOn.{max u v w, v} ι)
    (i : L ⟶ (moduleExtensionFunctorOn.{max u v w, v} ι).obj
      (finiteFreeModule.{max u v w} A n))
    (d : (moduleExtensionFunctorOn.{max u v w, v} ι).obj (finiteFreeModule.{max u v w} A n) ⟶
      (moduleExtensionFunctorOn.{max u v w, v} ι).obj (finiteFreeModule.{max u v w} A m))
    (φ : L ⟶ (moduleExtensionFunctorOn.{max u v w, v} ι).obj M), Mono i →
    ∀ hd : i ≫ d = 0, (ShortComplex.mk i d hd).Exact →
      ∃ ψ : (moduleExtensionFunctorOn.{max u v w, v} ι).obj
          (finiteFreeModule.{max u v w} A n) ⟶
        (moduleExtensionFunctorOn.{max u v w, v} ι).obj M, i ≫ ψ = φ


/-- [Stacks, Tag 06V1] on a restricted domain of algebras: the cokernel of an *arbitrary*
morphism from an adequate module-valued functor on a domain of algebras to the functor of a
module is adequate, given a base algebra object and the lifting property of
[Stacks, Tag 06V0] on that domain.

This is the proof of `AdequateFunctor.isAdequate_cokernel_to_moduleExtension` carried across the
domain restriction. [Stacks, Tag 06UX] on the domain covers the source by linearly adequate
functors; the lifting property extends each piece's morphism into `E M` along the piece's
presenting kernel; fullness of extension of scalars reads those extensions off as maps of modules
`g₀ j`. Their sum `g` and the sum `δ` of the presenting maps identify the covering morphism with
`Ker(E δ) ⟶ E M`, at which point `AdequateFunctor.isAdequate_cokernel_kernelComp_restrictDomain`
finishes, the covering morphism being epi.

No `@[stacks]` attribute is placed here: the tagged statement of 06V1 is
`AdequateFunctor.isAdequate_cokernel_to_moduleExtension`, over all commutative algebras, and
this is that statement transported to a restricted domain. -/
public theorem isAdequate_cokernel_to_moduleExtension_on {ι : C ⥤ CommAlgCat.{max u v} A}
    (b : BaseAlgebraObject.{v} ι)
    (hlift : FiniteFreeKernelLifting.{w, v} ι)
    (F : ModuleValuedFunctorOn.{max u v w, v} ι) (M : ModuleCat.{max u v w} A)
    (φ : F ⟶ (moduleExtensionFunctorOn.{max u v w, v} ι).obj M)
    (hF : IsAdequate.{max u v w, v} ι F) :
    IsAdequate.{max u v w, v} ι (cokernel φ) := by
  classical
  let R := algebraRingDiagramOn.{v} ι
  let E := moduleExtensionFunctorOn.{max u v w, v} ι
  let Cc := ModuleValuedFunctorOn.{max u v w, v} ι
  obtain ⟨J, L, hL, ⟨cover, hcover⟩⟩ :=
    exists_coproduct_linearlyAdequate_surjective_on ι F hF
  let eF := presheafOfModulesUliftIso.{max u v, max u v w} R F
  let cover' : (∐ L) ⟶ F := cover ≫ eF.hom
  have hcover' : ∀ X, Function.Surjective (cover'.app X) := by
    intro X y
    obtain ⟨z, hz⟩ := (ModuleCat.epi_iff_surjective _).mp
      (inferInstance : Epi (eF.hom.app X)) y
    obtain ⟨x, hx⟩ := hcover X z
    exact ⟨x, by simp [cover', hx, hz]⟩
  have hcoverEpi : Epi cover' := PresheafOfModules.epi_of_surjective hcover'
  -- the presenting maps of the covering pieces, read off as maps of modules by fullness
  choose n m gp hgp using hL
  let e0 (j : J) := Classical.choice (hgp j)
  let f (j : J) : finiteFreeModule.{max u v w} A (n j) ⟶ finiteFreeModule.{max u v w} A (m j) :=
    moduleHomOfExtensionNatTransOn b (gp j)
  have hf (j : J) : gp j = E.map (f j) := moduleExtension_natTransOn_eq_map b (gp j)
  let e (j : J) : L j ≅ kernel (E.map (f j)) :=
    (presheafOfModulesUliftIso.{max u v, max u v w} R (L j)).symm ≪≫ e0 j ≪≫
      kernelIsoOfEq (hf j)
  let ii (j : J) : L j ⟶ E.obj (finiteFreeModule.{max u v w} A (n j)) :=
    (e j).hom ≫ kernel.ι (E.map (f j))
  have hi (j : J) : ii j ≫ E.map (f j) = 0 := by simp [ii]
  have hker_i (j : J) : IsLimit (KernelFork.ofι (ii j) (hi j)) :=
    kernel.isoKernel (E.map (f j)) (ii j) (e j) (by simp [ii])
  have hmono_i (j : J) : Mono (ii j) := mono_of_isLimit_fork (hker_i j)
  have hexact_i (j : J) : (ShortComplex.mk (ii j) (E.map (f j)) (hi j)).Exact :=
    ShortComplex.exact_of_f_is_kernel _ (hker_i j)
  -- Tag 06V0 on the domain lifts each piece's morphism into `E M`
  choose ψ hψ using fun j => hlift M (n j) (m j) (L j) (ii j) (E.map (f j))
    (Sigma.ι L j ≫ cover' ≫ φ) (hmono_i j) (hi j) (hexact_i j)
  let g₀ (j : J) : finiteFreeModule.{max u v w} A (n j) ⟶ M :=
    moduleHomOfExtensionNatTransOn b (ψ j)
  let P : ModuleCat.{max u v w} A := ∐ fun j => finiteFreeModule.{max u v w} A (n j)
  let Qq : ModuleCat.{max u v w} A := ∐ fun j => finiteFreeModule.{max u v w} A (m j)
  let g : P ⟶ M := Sigma.desc fun j => g₀ j
  let D := Discrete.functor (fun j => finiteFreeModule.{max u v w} A (n j)) ⋙ E
  let G := Discrete.functor (fun j => finiteFreeModule.{max u v w} A (m j)) ⋙ E
  let α : D ⟶ G := Discrete.natTrans fun j => E.map (f j.as)
  let eH : Discrete.functor L ≅ kernel α := Discrete.natIso fun j =>
    let ev := (evaluation (Discrete J) Cc).obj j
    let eEv := PreservesKernel.iso ev α
    e j.as ≪≫ eEv.symm
  let δ : P ⟶ Qq := Sigma.desc fun j => f j ≫
    Sigma.ι (fun j => finiteFreeModule.{max u v w} A (m j)) j
  have hpres (N : J → ModuleCat.{max u v w} A) : PreservesColimit (Discrete.functor N) E := by
    show PreservesColimit (Discrete.functor N)
      (moduleExtensionFunctor.{max u v w, v} A ⋙
        PresheafOfModules.pushforward₀ ι.op (algebraRingDiagram.{v} A))
    have h1 := moduleExtension_preservesCoproduct.{u, v, w} (A := A) N
    have h2 := pushforward₀_preservesColimitsOfShape.{max u v w} ι.op
      (algebraRingDiagram.{v} A) (Discrete J)
    infer_instance
  let eP : colimit D ≅ E.obj P :=
    (preservesColimitIso E
      (Discrete.functor (fun j => finiteFreeModule.{max u v w} A (n j)))).symm
  let eQ : colimit G ≅ E.obj Qq :=
    (preservesColimitIso E
      (Discrete.functor (fun j => finiteFreeModule.{max u v w} A (m j)))).symm
  have hιP (j : Discrete J) : colimit.ι D j ≫ eP.hom =
      E.map (Sigma.ι (fun k => finiteFreeModule.{max u v w} A (n k)) j.as) :=
    ι_preservesColimitIso_inv E (Discrete.functor fun k => finiteFreeModule.{max u v w} A (n k)) j
  have hιQ (j : Discrete J) : colimit.ι G j ≫ eQ.hom =
      E.map (Sigma.ι (fun k => finiteFreeModule.{max u v w} A (m k)) j.as) :=
    ι_preservesColimitIso_inv E (Discrete.functor fun k => finiteFreeModule.{max u v w} A (m k)) j
  have hcompat : colim.map α ≫ eQ.hom = eP.hom ≫ E.map δ := by
    apply colimit.hom_ext
    intro j
    have hcol : colimit.ι D j ≫ colim.map α = α.app j ≫ colimit.ι G j := ι_colimMap α j
    rw [reassoc_of% hcol, hιQ, reassoc_of% hιP]
    show E.map (f j.as) ≫ _ = _
    rw [← E.map_comp, ← E.map_comp]
    simp [δ]
  have : HasExactColimitsOfShape (Discrete J) Cc := by
    have : (PresheafOfModules.toPresheaf R).ReflectsIsomorphisms :=
      toPresheaf_reflectsIsomorphisms
    exact HasExactColimitsOfShape.domain_of_functor (Discrete J)
      (PresheafOfModules.toPresheaf R)
  have : PreservesFiniteLimits (colim (J := Discrete J) (C := Cc)) :=
    HasExactColimitsOfShape.preservesFiniteLimits
  have : PreservesLimit (parallelPair α 0) (colim (J := Discrete J) (C := Cc)) := inferInstance
  let eK := (colim.mapIso eH) ≪≫
    PreservesKernel.iso (colim (J := Discrete J) (C := Cc)) α ≪≫
      kernel.mapIso (colim.map α) (E.map δ) eP eQ hcompat
  have hcoverMap : cover' ≫ φ = eK.hom ≫ kernel.ι (E.map δ) ≫ E.map g := by
    apply colimit.hom_ext
    intro j
    have he : colimit.ι (Discrete.functor L) j ≫ eK.hom ≫ kernel.ι (E.map δ) =
        ii j.as ≫ E.map (Sigma.ι (fun k => finiteFreeModule.{max u v w} A (n k)) j.as) := by
      have hη : colimit.ι (Discrete.functor L) j ≫ colim.map eH.hom =
          eH.hom.app j ≫ colimit.ι (kernel α) j := colimit.ι_map eH.hom j
      show colimit.ι (Discrete.functor L) j ≫ colim.map eH.hom ≫
        (PreservesKernel.iso colim α).hom ≫
        (kernel.mapIso (colimMap α) (E.map δ) eP eQ hcompat).hom ≫
        kernel.ι (E.map δ) = _
      rw [← Category.assoc, hη]
      have hmap : (kernel.mapIso (colimMap α) (E.map δ) eP eQ hcompat).hom ≫
          kernel.ι (E.map δ) = kernel.ι (colim.map α) ≫ eP.hom := by
        simp [kernel.mapIso, kernel.map]
      have hcmp : (PreservesKernel.iso colim α).hom ≫
          (kernel.mapIso (colimMap α) (E.map δ) eP eQ hcompat).hom ≫
          kernel.ι (E.map δ) = colim.map (kernel.ι α) ≫ eP.hom := by
        rw [hmap, ← Category.assoc, PreservesKernel.iso_hom, kernelComparison_comp_ι]
      have hNat : colimit.ι (kernel α) j ≫ colim.map (kernel.ι α) =
          (kernel.ι α).app j ≫ colimit.ι D j := colimit.ι_map (kernel.ι α) j
      have hηj : eH.hom.app j ≫ (kernel.ι α).app j =
          (e j.as).hom ≫ kernel.ι (E.map (f j.as)) := by
        let ev := (evaluation (Discrete J) Cc).obj j
        show (e j.as).hom ≫ (PreservesKernel.iso ev α).inv ≫
            ev.map (kernel.ι α) = _
        rw [PreservesKernel.iso_inv_ι]
        rfl
      rw [hcmp, Category.assoc, reassoc_of% hNat, hιP j, reassoc_of% hηj]
      simp [ii]
    rw [reassoc_of% he]
    show Sigma.ι L j.as ≫ cover' ≫ φ = _
    rw [← hψ j.as, moduleExtension_natTransOn_eq_map b (ψ j.as), ← E.map_comp]
    congr 2
    simp [g, g₀]
  -- the target morphism is built from maps of modules, hence a restriction
  let v := kernel.ι (E.map δ) ≫ E.map g
  have : HasCokernel v := HasCokernels.has_colimit v
  have hV : IsAdequate.{max u v w, v} ι (cokernel v) :=
    isAdequate_cokernel_kernelComp_restrictDomain ι δ g
  let eDomain := cokernel.mapIso (cover' ≫ φ) v eK (Iso.refl _) (by simpa [v] using hcoverMap)
  exact hV.of_iso ((cokernelEpiComp cover' φ).symm ≪≫ eDomain)

end FrontHalf

end AdequateFunctor

end
