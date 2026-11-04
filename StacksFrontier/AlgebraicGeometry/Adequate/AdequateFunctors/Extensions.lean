module

public import Mathlib.CategoryTheory.Limits.Shapes.Pullback.IsPullback.Kernels
public import StacksCore.Tactic.StacksAttribute
public import StacksFrontier.Algebra.Module.Adequate.Colimit
public import StacksFrontier.Algebra.Module.Adequate.Splitting
public import StacksFrontier.AlgebraicGeometry.Adequate.AdequateFunctors.Cokernels
public import StacksFrontier.AlgebraicGeometry.Adequate.HigherExtsBase.Biproducts

/-!
# Extensions of adequate functors

Let `A` be a ring. The adequate module-valued functors on `Alg_A` are closed under extensions:
if `0 → F → G → H → 0` is a short exact sequence of module-valued functors whose outer terms are
adequate, then so is the middle term. Together with closure under kernels ([Stacks, Tag 06V3])
and cokernels ([Stacks, Tag 06V2]) this exhibits the adequate functors as a weak Serre
subcategory of all module-valued functors.

## Main results

* `AdequateFunctor.isAdequate_of_shortExact` is closure under extensions.
* `AdequateFunctor.IsLinearlyAdequate.isAdequate` records that a linearly adequate functor is
  adequate.

## Implementation notes

The argument follows the source. Choose a surjection `∐ L i → H` from a direct sum of linearly
adequate functors ([Stacks, Tag 06UX]). Pulling the extension back along a single summand
`L i → H` gives an extension of a linearly adequate functor by `F`, which splits
([Stacks, Tag 06V7]); the resulting sections assemble into a lift `∐ L i → G` of the surjection,
which splits the pullback `G ×_H (∐ L i)`. That pullback is therefore the biproduct of `F` and
`∐ L i`, hence adequate. Finally `G` is the cokernel of the kernel of the epimorphism
`G ×_H (∐ L i) → G`, and that kernel is the kernel of `∐ L i → H` because kernels of parallel
edges of a pullback square agree; both terms are adequate, so `G` is adequate by
[Stacks, Tag 06V2].

The first reduction of the source, to the case where `F` is the functor of an `A`-module, is not
needed here: `AdequateFunctor.exists_retraction_of_shortExact` already splits an extension of a
linearly adequate functor by an arbitrary adequate functor, which is the content of
[Stacks, Remark 06V7].

The value universe and the universe of the algebra carriers are both the universe of the base
ring, as in `AdequateFunctor.exists_retraction_of_shortExact`.

## References

* [Stacks Project, Tag 06V8](https://stacks.math.columbia.edu/tag/06V8)
* [Stacks Project, Tag 06V7](https://stacks.math.columbia.edu/tag/06V7)
* [Stacks Project, Tag 06UX](https://stacks.math.columbia.edu/tag/06UX)
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits

universe u₁ v₁ u v w

namespace AdequateFunctor

/-- A linearly adequate functor is adequate: a presentation by a map of finite free modules is in
particular a presentation by a map of modules. -/
public lemma IsLinearlyAdequate.isAdequate {A : Type u} [CommRing A]
    {F : ModuleValuedFunctor.{w, v} A} (hF : IsLinearlyAdequate (𝟭 _) F) :
    IsAdequate (𝟭 _) F := by
  obtain ⟨n, m, f, h⟩ := (isLinearlyAdequate_iff_exists_module_map F).mp hF
  exact ⟨_, _, f, h⟩

/-- The kernels of the two parallel edges of a pullback square are isomorphic. -/
private lemma exists_iso_kernel_of_isPullback {C : Type u₁} [Category.{v₁} C] [Abelian C]
    {X₁ X₂ X₃ X₄ : C} {t : X₁ ⟶ X₂} {l : X₁ ⟶ X₃} {r : X₂ ⟶ X₄} {b : X₃ ⟶ X₄}
    (sq : IsPullback t l r b) :
    ∃ ε : kernel t ≅ kernel b, ε.hom ≫ kernel.ι b = kernel.ι t ≫ l :=
  have := isIso_kernel_map_of_isPullback sq
  ⟨asIso (kernel.map t b l r sq.w), kernel.lift_ι _ _ _⟩

/-- The pullback of a short exact sequence `0 → X₁ → X₂ → X₃ → 0` along a morphism `p : L ⟶ X₃`
is a short exact sequence `0 → X₁ → X₂ ×_{X₃} L → L → 0`. The first map is the one induced by
`X₁ ⟶ X₂` and the zero morphism, and the second is the projection to `L`. -/
public lemma exists_shortExact_pullback {C : Type u₁} [Category.{v₁} C] [Abelian C]
    {S : ShortComplex C} (hS : S.ShortExact) {L : C} (p : L ⟶ S.X₃) :
    ∃ (j : S.X₁ ⟶ pullback S.g p) (hj : j ≫ pullback.snd S.g p = 0),
      (ShortComplex.mk j (pullback.snd S.g p) hj).ShortExact := by
  have := hS.mono_f
  have := hS.epi_g
  have hw : S.f ≫ S.g = 0 ≫ p := by rw [S.zero, zero_comp]
  refine ⟨pullback.lift S.f 0 hw, pullback.lift_snd _ _ _, ?_⟩
  have sq : IsPullback (pullback.fst S.g p) (pullback.snd S.g p) S.g p :=
    IsPullback.of_hasPullback S.g p
  obtain ⟨ε, hε⟩ := exists_iso_kernel_of_isPullback sq.flip
  obtain ⟨α, hα⟩ : ∃ α : S.X₁ ≅ kernel S.g, α.hom ≫ kernel.ι S.g = S.f :=
    ⟨IsLimit.conePointUniqueUpToIso hS.fIsKernel (limit.isLimit (parallelPair S.g 0)), by simp⟩
  have hβ : (α ≪≫ ε.symm).hom ≫ kernel.ι (pullback.snd S.g p) = pullback.lift S.f 0 hw := by
    refine pullback.hom_ext ?_ ?_
    · rw [Category.assoc, ← hε, pullback.lift_fst]
      simpa only [Iso.trans_hom, Iso.symm_hom, Category.assoc, Iso.inv_hom_id_assoc] using hα
    · rw [pullback.lift_snd, Category.assoc, kernel.condition, comp_zero]
  have : Mono (pullback.lift S.f 0 hw ≫ pullback.fst S.g p) := by
    rwa [pullback.lift_fst]
  exact ShortComplex.ShortExact.mk'
    (ShortComplex.exact_of_f_is_kernel _
      (kernel.isoKernel (pullback.snd S.g p) _ (α ≪≫ ε.symm) hβ))
    (mono_of_mono _ (pullback.fst S.g p)) inferInstance

/-- **Stacks Lemma 06V8.** Let `A` be a ring and let `0 → F → G → H → 0` be a short exact
sequence of module-valued functors on `Alg_A`. If `F` and `H` are adequate, so is `G`. -/
@[stacks 06V8]
public lemma isAdequate_of_shortExact {A : Type u} [CommRing A]
    (S : ShortComplex (ModuleValuedFunctor.{u, u} A)) (hS : S.ShortExact)
    (h₁ : IsAdequate (𝟭 _) S.X₁) (h₃ : IsAdequate (𝟭 _) S.X₃) :
    IsAdequate (𝟭 _) S.X₂ := by
  have := hS.mono_f
  have := hS.epi_g
  obtain ⟨ι, L, hL, cover₀, hcover₀⟩ :=
    exists_coproduct_linearlyAdequate_surjective S.X₃ h₃
  obtain ⟨cover, hcover⟩ : ∃ cover : (∐ L) ⟶ S.X₃, Epi cover :=
    ⟨cover₀ ≫ (presheafOfModulesUliftIso.{u, u} (algebraRingDiagram.{u} A) S.X₃).hom,
      have : Epi cover₀ := PresheafOfModules.epi_of_surjective hcover₀
      epi_comp _ _⟩
  have := hcover
  have hLsum : IsAdequate (𝟭 _) (∐ L) :=
    isAdequate_coproduct L fun i => IsLinearlyAdequate.isAdequate (hL i)
  have hkerCover : IsAdequate (𝟭 _) (kernel cover) := isAdequate_kernel cover hLsum h₃
  -- Lift the surjection through `S.g`, one linearly adequate summand at a time.
  have hlift : ∀ i, ∃ s : L i ⟶ S.X₂, s ≫ S.g = Sigma.ι L i ≫ cover := by
    intro i
    obtain ⟨j, hj, hjSE⟩ := exists_shortExact_pullback hS (Sigma.ι L i ≫ cover)
    obtain ⟨r, hr⟩ := exists_retraction_of_shortExact j _ hj hjSE h₁ (hL i)
    have spl := ShortComplex.Splitting.ofExactOfRetraction _ hjSE.exact r hr hjSE.epi_g
    refine ⟨spl.s ≫ pullback.fst S.g (Sigma.ι L i ≫ cover), ?_⟩
    rw [Category.assoc, pullback.condition, ← Category.assoc, spl.s_g, Category.id_comp]
  choose s hs using hlift
  have hsec : Sigma.desc s ≫ S.g = cover := by
    refine Sigma.hom_ext _ _ fun i => ?_
    rw [← Category.assoc, Sigma.ι_desc, hs i]
  -- The lift splits the pullback of the extension along the surjection.
  obtain ⟨j, hj, hjSE⟩ := exists_shortExact_pullback hS cover
  obtain ⟨σ, hσ⟩ : ∃ σ : (∐ L) ⟶ pullback S.g cover, σ ≫ pullback.snd S.g cover = 𝟙 _ :=
    ⟨pullback.lift (Sigma.desc s) (𝟙 (∐ L)) (by rw [hsec, Category.id_comp]),
      pullback.lift_snd _ _ _⟩
  have splP := ShortComplex.Splitting.ofExactOfSection _ hjSE.exact σ hσ hjSE.mono_f
  have hPad : IsAdequate (𝟭 _) (pullback S.g cover) :=
    (isAdequate_biprod A h₁ hLsum).of_iso splP.isoBinaryBiproduct
  -- `S.X₂` is the cokernel of the kernel of the projection out of that pullback.
  have sq : IsPullback (pullback.fst S.g cover) (pullback.snd S.g cover) S.g cover :=
    IsPullback.of_hasPullback S.g cover
  obtain ⟨ε, -⟩ := exists_iso_kernel_of_isPullback sq
  have hkerfst : IsAdequate (𝟭 _) (kernel (pullback.fst S.g cover)) := hkerCover.of_iso ε
  have hfinal : (ShortComplex.mk (kernel.ι (pullback.fst S.g cover)) (pullback.fst S.g cover)
      (kernel.condition _)).ShortExact :=
    ShortComplex.ShortExact.mk'
      (ShortComplex.exact_of_f_is_kernel _ (kernelIsKernel _)) inferInstance inferInstance
  exact (isAdequate_cokernel (kernel.ι (pullback.fst S.g cover)) hkerfst hPad).of_iso
    (IsColimit.coconePointUniqueUpToIso (cokernelIsCokernel _) hfinal.gIsCokernel).symm

end AdequateFunctor

end
