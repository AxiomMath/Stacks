module

public import StacksFrontier.AlgebraicGeometry.Adequate.AdequateFunctors.DomainFiniteProducts

/-!
# Kernels of adequate functors on a restricted domain, given an extension

[Stacks, Tag 06V3], closure of adequacy under kernels, is stated for module-valued functors on
all commutative `A`-algebras. This file reduces that closure property, on any domain
`ι : C ⥤ CommAlgCat A`, to a single input: the lifting property of [Stacks, Tag 06V0] on that
domain.

Precisely: let `a : M₁ ⟶ N₁` and `b : M₂ ⟶ N₂` be maps of modules, presenting two adequate
functors as `ker (E a)` and `ker (E b)` for `E` the extension of scalars to the domain, and let
`ψ : ker (E a) ⟶ ker (E b)`. The composite `ker (E a) ⟶ ker (E b) ↪ E M₂` is a map out of a
kernel into a module extension; *if* it extends along the mono `ker (E a) ↪ E M₁`, then by
fullness of `E` (`AdequateFunctor.full_moduleExtensionFunctorOn`) the extension is `E t` for a
map of modules `t : M₁ ⟶ M₂`, and then `ker ψ` is the kernel of `E (biprod.lift a t)` — a kernel
presentation, so `ker ψ` is adequate.

So [Stacks, Tag 06V3] on a restricted domain rests on producing that extension. When `M₁` and
`N₁` are finite free — that is, when the source is *linearly* adequate — the extension is
[Stacks, Tag 06V0] on the domain, which is available over the algebras of a site as
`AdequateFunctor.exists_lift_from_finite_free_kernel_site`; nothing set-theoretic stands in the
way there, the auxiliary algebras of 06V0 belonging to the site by
`AlgebraicGeometry.size_lt_cutoff_spec_symmetricAlgebra` and
`AdequateFunctor.size_lt_of_spec_laurentPolynomial`. For a general adequate source the extension
is *not* reducible to 06V0: 06V0 lifts only along a map of finite free module extensions. See the
implementation notes of
`StacksFrontier/AlgebraicGeometry/Adequate/AdequateModules/AffineSectionExactness.lean`
for what the general case needs instead.

## Main results

* `AdequateFunctor.isAdequate_kernel_of_moduleExtensionLift` — the kernel of a morphism between
  two kernels of base-changed maps of modules is adequate, given a map of modules extending the
  induced map into the second presenting module.

## Implementation notes

The hypothesis is stated as the commuting square `kernel.ι (E a) ≫ E t = ψ ≫ kernel.ι (E b)`
rather than as an abstract extension, so that the map of modules `t` is part of the data. That is
what fullness of `E` supplies on a domain with a base algebra object, and it is what makes
`biprod.lift a t` available as the presenting map; stating the hypothesis with an extension
`ker (E a) ⟶ E M₂` instead would leave `t` to be produced again at every use.

No `@[stacks]` attribute is placed here: this is a reduction of 06V3 on a restricted domain to
06V0 on that domain, not a proof of either tag.

## References

* [Stacks Project, Tag 06V0](https://stacks.math.columbia.edu/tag/06V0)
* [Stacks Project, Tag 06V3](https://stacks.math.columbia.edu/tag/06V3)
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits

universe w v u u₁ v₁

namespace AdequateFunctor

/-- The kernel of a morphism between two kernels of base-changed maps of modules is adequate,
given a map of modules whose base change extends the induced map into the second presenting
module. The presenting map of the kernel is the pair consisting of the first presenting map and
that extension. -/
public lemma isAdequate_kernel_of_moduleExtensionLift
    {A : Type u} [CommRing A] {C : Type u₁} [Category.{v₁} C]
    (ι : C ⥤ CommAlgCat.{max u v} A)
    {M₁ N₁ M₂ N₂ : ModuleCat.{max u v w} A} (a : M₁ ⟶ N₁) (b : M₂ ⟶ N₂)
    {ψ : kernel ((moduleExtensionFunctorOn.{max u v w} ι).map a) ⟶
      kernel ((moduleExtensionFunctorOn.{max u v w} ι).map b)}
    (t : M₁ ⟶ M₂)
    (hsq : kernel.ι ((moduleExtensionFunctorOn.{max u v w} ι).map a) ≫
        (moduleExtensionFunctorOn.{max u v w} ι).map t =
      ψ ≫ kernel.ι ((moduleExtensionFunctorOn.{max u v w} ι).map b)) :
    IsAdequate.{max u v w, v} ι (kernel ψ) := by
  let E := moduleExtensionFunctorOn.{max u v w} ι
  have : PreservesBinaryBiproducts E := moduleExtensionFunctorOn_preservesBinaryBiproducts ι
  let g := Limits.biprod.lift (E.map a) (E.map t)
  have hzero : (kernel.ι ψ ≫ kernel.ι (E.map a)) ≫ g = 0 := by
    apply Limits.biprod.hom_ext
    · rw [Category.assoc, Limits.biprod.lift_fst, zero_comp, Category.assoc,
        kernel.condition, comp_zero]
    · rw [Category.assoc, Limits.biprod.lift_snd, zero_comp, Category.assoc, hsq,
        ← Category.assoc, kernel.condition, zero_comp]
  have hs (s : Fork g 0) : s.ι ≫ g = 0 := by simp
  have hfst (s : Fork g 0) : s.ι ≫ E.map a = 0 := by
    rw [← Limits.biprod.lift_fst (E.map a) (E.map t), ← Category.assoc, hs, zero_comp]
  have hsnd (s : Fork g 0) : s.ι ≫ E.map t = 0 := by
    rw [← Limits.biprod.lift_snd (E.map a) (E.map t), ← Category.assoc, hs, zero_comp]
  have hkψ (s : Fork g 0) : kernel.lift (E.map a) s.ι (hfst s) ≫ ψ = 0 := by
    refine (cancel_mono (kernel.ι (E.map b))).1 ?_
    rw [Category.assoc, ← hsq, ← Category.assoc, kernel.lift_ι, hsnd s, zero_comp]
  have hlift (s : Fork g 0) :
      kernel.lift ψ (kernel.lift (E.map a) s.ι (hfst s)) (hkψ s) ≫
        kernel.ι ψ ≫ kernel.ι (E.map a) = s.ι := by
    rw [← Category.assoc, kernel.lift_ι, kernel.lift_ι]
  have hlim : IsLimit (KernelFork.ofι (kernel.ι ψ ≫ kernel.ι (E.map a)) hzero) := by
    refine Fork.IsLimit.mk _
      (fun s => kernel.lift ψ (kernel.lift (E.map a) s.ι (hfst s)) (hkψ s)) hlift
      (fun s m hm => ?_)
    refine (cancel_mono (kernel.ι ψ ≫ kernel.ι (E.map a))).1 ?_
    exact hm.trans (hlift s).symm
  refine ⟨M₁, N₁ ⊞ M₂, Limits.biprod.lift a t, ⟨?_⟩⟩
  have e₁ : kernel ψ ≅ kernel g :=
    hlim.conePointUniqueUpToIso (limit.isLimit (parallelPair g 0))
  have e₂ : kernel (E.map (Limits.biprod.lift a t)) ≅ kernel g :=
    kernel.mapIso (E.map (Limits.biprod.lift a t)) g (Iso.refl _) (E.mapBiprod N₁ M₂)
      (by rw [Iso.refl_hom, Category.id_comp]
          exact Limits.biprod.map_lift_mapBiprod E N₁ M₂ a t)
  exact (presheafOfModulesUliftIso.{max u v, max u v w}
    (algebraRingDiagramOn ι) (kernel ψ)) ≪≫ e₁ ≪≫ e₂.symm

end AdequateFunctor

end
