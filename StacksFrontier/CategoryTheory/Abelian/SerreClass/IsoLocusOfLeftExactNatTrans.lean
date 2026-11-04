module

public import StacksFrontier.CategoryTheory.Abelian.SerreClass.IsoLocusOfNatTrans

/-!
# Where a natural transformation of left exact functors is invertible

`CategoryTheory.ObjectProperty.isWeakSerreClass_isoLocus` treats a family of natural
transformations `c i : T i ⟶ R i` with `R i` exact and `T i` right exact. This file treats the
case where both `T i` and `R i` are only left exact, but carry every short exact sequence whose
first term lies in a weak Serre subcategory `Q` to a sequence whose last map is an epimorphism.

Such functors are exact on short exact sequences of objects of `Q` and preserve the cokernels of
morphisms between objects of `Q`; hence the objects of `Q` at which every `c i` is invertible
again form a weak Serre subcategory.

## Main results

* `CategoryTheory.ObjectProperty.isColimitMapCokernelCofork_of_epi`: such a functor preserves the
  cokernel of a morphism between objects of `Q`.
* `CategoryTheory.ObjectProperty.isWeakSerreClass_isoLocus_of_epi`: the weak Serre property of the
  locus where a family of natural transformations between such functors is invertible.
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits

universe v₁ v₂ u₁ u₂ w

namespace CategoryTheory.ObjectProperty

variable {𝒜 : Type u₁} [Category.{v₁} 𝒜] [Abelian 𝒜] {ℬ : Type u₂} [Category.{v₂} ℬ] [Abelian ℬ]
  (Q : ObjectProperty 𝒜) [Q.IsWeakSerreClass]

section LeftExact

variable (F : 𝒜 ⥤ ℬ) [F.PreservesZeroMorphisms] [PreservesFiniteLimits F]
  (hF : ∀ S : ShortComplex 𝒜, S.ShortExact → Q S.X₁ → Epi (F.map S.g))

omit [Q.IsWeakSerreClass] in
include hF in
/-- A left exact functor which carries the short exact sequences with first term in `Q` to
sequences with epimorphic last map carries them to short exact sequences. -/
theorem shortExact_map_of_epi {S : ShortComplex 𝒜} (hS : S.ShortExact) (h₁ : Q S.X₁) :
    (S.map F).ShortExact := by
  have hmono := hS.mono_f
  have : Mono (S.map F).f := F.map_mono S.f
  have : Epi (S.map F).g := hF S hS h₁
  exact ⟨ShortComplex.Exact.map_of_mono_of_preservesKernel hS.exact F hmono inferInstance⟩

include hF in
/-- **Such a functor preserves the cokernel of a morphism between objects of `Q`.** The cokernel
of `f` is the cokernel of the inclusion of its image, which lies in `Q`, so the image sequence is
carried to a short exact sequence; and `F` carries the epimorphism onto the image, whose kernel
lies in `Q`, to an epimorphism. -/
noncomputable def isColimitMapCokernelCofork_of_epi {X Y : 𝒜} {f : X ⟶ Y} (hX : Q X) (hY : Q Y)
    {k : CokernelCofork f} (hk : IsColimit k) : IsColimit (k.map F) := by
  have hI : Q (Abelian.image f) := Q.prop_kernel _ hY (Q.prop_cokernel f hX hY)
  let S₂ : ShortComplex 𝒜 := ShortComplex.mk (Abelian.image.ι f) (cokernel.π f)
    (kernel.condition (cokernel.π f))
  have hS₂ : S₂.ShortExact :=
    { exact := ShortComplex.exact_of_f_is_kernel S₂ (kernelIsKernel (cokernel.π f))
      mono_f := inferInstanceAs (Mono (kernel.ι (cokernel.π f)))
      epi_g := inferInstanceAs (Epi (cokernel.π f)) }
  have hFS₂ := shortExact_map_of_epi Q F hF hS₂ hI
  let S₁ : ShortComplex 𝒜 := ShortComplex.mk (kernel.ι (Abelian.factorThruImage f))
    (Abelian.factorThruImage f) (kernel.condition _)
  have hS₁ : S₁.ShortExact :=
    { exact := ShortComplex.exact_of_f_is_kernel S₁ (kernelIsKernel _)
      mono_f := inferInstanceAs (Mono (kernel.ι _))
      epi_g := inferInstanceAs (Epi (Abelian.factorThruImage f)) }
  have hK : Q S₁.X₁ := Q.prop_kernel _ hX hI
  haveI : Epi (F.map (Abelian.factorThruImage f)) := hF S₁ hS₁ hK
  have hc₂ : IsColimit (CokernelCofork.ofπ (F.map (cokernel.π f)) (S₂.map F).zero) :=
    hFS₂.gIsCokernel
  have hc : IsColimit (CokernelCofork.ofπ (F.map (cokernel.π f))
      (by rw [← F.map_comp, cokernel.condition, F.map_zero]) : CokernelCofork (F.map f)) :=
    isCokernelEpiComp hc₂ (F.map (Abelian.factorThruImage f))
      (by
        change F.map f = F.map (Abelian.factorThruImage f) ≫ F.map (Abelian.image.ι f)
        rw [← F.map_comp, Abelian.image.fac])
  let e : k.pt ≅ cokernel f := hk.coconePointUniqueUpToIso (colimit.isColimit _)
  refine IsColimit.ofIsoColimit hc (Cofork.ext (F.mapIso e).symm ?_)
  change F.map (cokernel.π f) ≫ F.map e.inv = F.map k.π
  rw [← F.map_comp]
  congr 1
  exact hk.comp_coconePointUniqueUpToIso_inv (colimit.isColimit _) WalkingParallelPair.one

end LeftExact

variable {ι : Type w} {𝒞 : ι → Type u₂} [∀ i, Category.{v₂} (𝒞 i)] [∀ i, Abelian (𝒞 i)]
  (T R : ∀ i, 𝒜 ⥤ 𝒞 i) [∀ i, (T i).PreservesZeroMorphisms] [∀ i, PreservesFiniteLimits (T i)]
  [∀ i, (R i).PreservesZeroMorphisms] [∀ i, PreservesFiniteLimits (R i)]
  (c : ∀ i, T i ⟶ R i)

/-- **The locus where a family of natural transformations of left exact functors, exact on the
short exact sequences with first term in `Q`, is invertible is a weak Serre subcategory.** -/
theorem isWeakSerreClass_isoLocus_of_epi
    (hT : ∀ i (S : ShortComplex 𝒜), S.ShortExact → Q S.X₁ → Epi ((T i).map S.g))
    (hR : ∀ i (S : ShortComplex 𝒜), S.ShortExact → Q S.X₁ → Epi ((R i).map S.g)) :
    (isoLocus Q c).IsWeakSerreClass where
  exists_zero := by
    obtain ⟨Z, hZ, hQZ⟩ := Q.exists_prop_of_containsZero
    refine ⟨Z, hZ, hQZ, fun i => ?_⟩
    have h₁ : IsZero ((T i).obj Z) := (T i).map_isZero hZ
    have h₂ : IsZero ((R i).obj Z) := (R i).map_isZero hZ
    exact ⟨⟨h₂.to_ _, h₁.eq_of_src _ _, h₂.eq_of_src _ _⟩⟩
  of_iso := by
    rintro X X' e ⟨hX, hc⟩
    refine ⟨Q.prop_of_iso e hX, fun i => ?_⟩
    have : (c i).app X' = (T i).map e.inv ≫ (c i).app X ≫ (R i).map e.hom := by
      rw [← Category.assoc, (c i).naturality e.inv, Category.assoc, ← (R i).map_comp,
        e.inv_hom_id, (R i).map_id, Category.comp_id]
    rw [this]
    have := hc i
    infer_instance
  kernels_le := by
    rintro _ ⟨f, k, hk, ⟨hX, hcX⟩, ⟨hY, hcY⟩⟩
    refine ⟨Q.prop_of_isLimit_kernelFork hk hX hY, fun i => ?_⟩
    have := hcX i
    have := hcY i
    exact isIso_of_isLimit_kernelForks
      ((KernelFork.isLimitMapConeEquiv _ (T i)) (isLimitOfPreserves (T i) hk))
      ((KernelFork.isLimitMapConeEquiv _ (R i)) (isLimitOfPreserves (R i) hk)) ((c i).app _)
      ((c i).app _) ((c i).naturality f) ((c i).app k.pt) ((c i).naturality k.ι).symm
  cokernels_le := by
    rintro _ ⟨f, k, hk, ⟨hX, hcX⟩, ⟨hY, hcY⟩⟩
    refine ⟨Q.prop_of_isColimit_cokernelCofork hk hX hY, fun i => ?_⟩
    have := hcX i
    have := hcY i
    exact isIso_of_isColimit_cokernelCoforks
      (isColimitMapCokernelCofork_of_epi Q (T i) (hT i) hX hY hk)
      (isColimitMapCokernelCofork_of_epi Q (R i) (hR i) hX hY hk) ((c i).app _) ((c i).app _)
      ((c i).naturality f) ((c i).app k.pt) ((c i).naturality k.π)
  prop_X₂_of_shortExact := by
    rintro S hS ⟨h₁, hc₁⟩ ⟨h₃, hc₃⟩
    have h₂ : Q S.X₂ := Q.prop_X₂_of_shortExact hS h₁ h₃
    refine ⟨h₂, fun i => ?_⟩
    let φ : S.map (T i) ⟶ S.map (R i) := ShortComplex.homMk ((c i).app _) ((c i).app _)
      ((c i).app _) ((c i).naturality S.f).symm ((c i).naturality S.g).symm
    have : IsIso φ.τ₁ := hc₁ i
    have : IsIso φ.τ₃ := hc₃ i
    exact ShortComplex.isIso₂_of_shortExact_of_isIso₁₃ φ
      (shortExact_map_of_epi Q (T i) (hT i) hS h₁) (shortExact_map_of_epi Q (R i) (hR i) hS h₁)

end CategoryTheory.ObjectProperty
