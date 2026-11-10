module

public import StacksCore.CategoryTheory.Abelian.SerreClass.Weak

/-!
# Where a natural transformation of half-exact functors is invertible

Let `T R : 𝒜 ⥤ ℬ` be functors between abelian categories with `R` exact and `T` right exact, and
let `Q` be a weak Serre subcategory of `𝒜` such that `T` carries monomorphisms between objects
of `Q` to monomorphisms. Then `T` is exact on `Q`, and for a family of natural transformations
`c i : T i ⟶ R i` of such pairs, with codomains `𝒞 i` allowed to depend on `i`, the objects of `Q`
at which every `c i` is invertible form again a weak Serre subcategory of `𝒜`.

This is the shape of the argument of Stacks 0764 (2) and Stacks 0771 (2) for the flat base
change property: `R` is a restriction functor to a small étale site, `T` is a restriction
followed by the pullback `f_{small}^*` along a flat morphism of schemes, `Q` is the class of
locally quasi-coherent modules, and `c` is the comparison map `c_φ` of Stacks 06WC; exactness of
the restriction and of `f_{small}^*` on quasi-coherent modules and the five lemma give the
result.

## Main results

* `CategoryTheory.isIso_of_isLimit_kernelForks` and
  `CategoryTheory.isIso_of_isColimit_cokernelCoforks`:
  a map between limit kernel forks (colimit cokernel coforks) over an isomorphism of arrows is
  an isomorphism.
* `CategoryTheory.ObjectProperty.isWeakSerreClass_isoLocus`: the weak Serre property of the
  locus where a family of natural transformations is invertible.
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits

universe v₁ v₂ u₁ u₂ w

namespace CategoryTheory

variable {C : Type u₁} [Category.{v₁} C] [HasZeroMorphisms C]

/-- A map between limit kernel forks of two arrows, compatible with an isomorphism on the
sources and a monomorphism on the targets, is an isomorphism. -/
theorem isIso_of_isLimit_kernelForks {X Y X' Y' : C} {f : X ⟶ Y} {f' : X' ⟶ Y'}
    {k : KernelFork f} {k' : KernelFork f'} (hk : IsLimit k) (hk' : IsLimit k')
    (a : X ⟶ X') (b : Y ⟶ Y') [IsIso a] [Mono b] (hab : f ≫ b = a ≫ f')
    (t : k.pt ⟶ k'.pt) (ht : t ≫ k'.ι = k.ι ≫ a) : IsIso t := by
  have hz : (k'.ι ≫ inv a) ≫ f = 0 := by
    rw [← cancel_mono b, Category.assoc, Category.assoc, hab, IsIso.inv_hom_id_assoc,
      KernelFork.condition, zero_comp]
  let s : k'.pt ⟶ k.pt := hk.lift (KernelFork.ofι (k'.ι ≫ inv a) hz)
  have hs : s ≫ k.ι = k'.ι ≫ inv a := hk.fac _ WalkingParallelPair.zero
  refine ⟨s, ?_, ?_⟩
  · refine Fork.IsLimit.hom_ext hk ?_
    simp only [Category.assoc, Category.id_comp]
    show t ≫ s ≫ k.ι = k.ι
    rw [hs, ← Category.assoc, ht, Category.assoc, IsIso.hom_inv_id, Category.comp_id]
  · refine Fork.IsLimit.hom_ext hk' ?_
    simp only [Category.assoc, Category.id_comp]
    show s ≫ t ≫ k'.ι = k'.ι
    rw [ht, ← Category.assoc, hs, Category.assoc, IsIso.inv_hom_id, Category.comp_id]

/-- A map between colimit cokernel coforks of two arrows, compatible with an epimorphism on the
sources and an isomorphism on the targets, is an isomorphism. -/
theorem isIso_of_isColimit_cokernelCoforks {X Y X' Y' : C} {f : X ⟶ Y} {f' : X' ⟶ Y'}
    {k : CokernelCofork f} {k' : CokernelCofork f'} (hk : IsColimit k) (hk' : IsColimit k')
    (a : X ⟶ X') (b : Y ⟶ Y') [Epi a] [IsIso b] (hab : f ≫ b = a ≫ f')
    (t : k.pt ⟶ k'.pt) (ht : k.π ≫ t = b ≫ k'.π) : IsIso t := by
  have hz : f' ≫ (inv b ≫ k.π) = 0 := by
    rw [← cancel_epi a, ← Category.assoc, ← hab, Category.assoc, IsIso.hom_inv_id_assoc,
      CokernelCofork.condition, comp_zero]
  let s : k'.pt ⟶ k.pt := hk'.desc (CokernelCofork.ofπ (inv b ≫ k.π) hz)
  have hs : k'.π ≫ s = inv b ≫ k.π := hk'.fac _ WalkingParallelPair.one
  refine ⟨s, ?_, ?_⟩
  · refine Cofork.IsColimit.hom_ext hk ?_
    show k.π ≫ t ≫ s = k.π ≫ 𝟙 _
    rw [← Category.assoc, ht, Category.assoc, hs, IsIso.hom_inv_id_assoc, Category.comp_id]
  · refine Cofork.IsColimit.hom_ext hk' ?_
    show k'.π ≫ s ≫ t = k'.π ≫ 𝟙 _
    rw [← Category.assoc, hs, Category.assoc, ht, IsIso.inv_hom_id_assoc, Category.comp_id]

end CategoryTheory

namespace CategoryTheory.ObjectProperty

variable {𝒜 : Type u₁} [Category.{v₁} 𝒜] [Abelian 𝒜] {ℬ : Type u₂} [Category.{v₂} ℬ] [Abelian ℬ]
  (Q : ObjectProperty 𝒜) [Q.IsWeakSerreClass]

section HalfExact

variable (T : 𝒜 ⥤ ℬ) [T.PreservesZeroMorphisms] [PreservesFiniteColimits T]
  (hT : ∀ ⦃X Y : 𝒜⦄ (f : X ⟶ Y), Q X → Q Y → Mono f → Mono (T.map f))

include hT in
/-- **A right exact functor which preserves monomorphisms between objects of a weak Serre
subcategory preserves the kernels of morphisms between them.** The kernel of `f` is the kernel
of the epimorphism onto the image of `f`, which lies in the subcategory; right exactness gives
the cokernel sequence, preservation of monomorphisms its left end, and the image inclusion is a
monomorphism between objects of the subcategory. -/
noncomputable def isLimitMapKernelFork {X Y : 𝒜} {f : X ⟶ Y} (hX : Q X) (hY : Q Y)
    {k : KernelFork f} (hk : IsLimit k) :
    IsLimit (k.map T) := by
  have : Mono k.ι := Fork.IsLimit.mono hk
  let S : ShortComplex 𝒜 := ShortComplex.mk k.ι f k.condition
  have hS : S.Exact := ShortComplex.exact_of_f_is_kernel S
    (IsLimit.ofIsoLimit hk (Fork.isoForkOfι k))
  have hz : k.ι ≫ Abelian.factorThruImage f = 0 := by
    rw [← cancel_mono (Abelian.image.ι f), Category.assoc, Abelian.image.fac, zero_comp]
    exact k.condition
  let S' : ShortComplex 𝒜 := ShortComplex.mk k.ι (Abelian.factorThruImage f) hz
  let ψ : S' ⟶ S := ShortComplex.homMk (𝟙 _) (𝟙 _) (Abelian.image.ι f) (by simp [S, S'])
    (by simp [S, S'])
  have : Epi ψ.τ₁ := inferInstanceAs (Epi (𝟙 _))
  have : IsIso ψ.τ₂ := inferInstanceAs (IsIso (𝟙 _))
  have : Mono ψ.τ₃ := inferInstanceAs (Mono (Abelian.image.ι f))
  have hS' : S'.Exact := (ShortComplex.exact_iff_of_epi_of_isIso_of_mono ψ).2 hS
  have : Mono S'.f := inferInstanceAs (Mono k.ι)
  have : Epi S'.g := inferInstanceAs (Epi (Abelian.factorThruImage f))
  have hTS' : (S'.map T).Exact := ShortComplex.exact_of_g_is_cokernel _
    ((CokernelCofork.isColimitMapCoconeEquiv _ T)
      (isColimitOfPreserves T (ShortComplex.ShortExact.mk hS').gIsCokernel))
  have : Mono (T.map (Abelian.image.ι f)) :=
    hT _ (Q.prop_kernel _ hY (Q.prop_cokernel f hX hY)) hY inferInstance
  let ψT : S'.map T ⟶ S.map T := ShortComplex.homMk (𝟙 _) (𝟙 _) (T.map (Abelian.image.ι f))
    (by simp [S, S']) (by
      change 𝟙 _ ≫ T.map f = T.map (Abelian.factorThruImage f) ≫ T.map (Abelian.image.ι f)
      rw [← T.map_comp, Abelian.image.fac, Category.id_comp])
  have : Epi ψT.τ₁ := inferInstanceAs (Epi (𝟙 _))
  have : IsIso ψT.τ₂ := inferInstanceAs (IsIso (𝟙 _))
  have : Mono ψT.τ₃ := inferInstanceAs (Mono (T.map (Abelian.image.ι f)))
  have hTS : (S.map T).Exact := (ShortComplex.exact_iff_of_epi_of_isIso_of_mono ψT).1 hTS'
  have : Mono (S.map T).f := hT k.ι (Q.prop_of_isLimit_kernelFork hk hX hY) hX inferInstance
  exact IsLimit.ofIsoLimit hTS.fIsKernel (Fork.ext (Iso.refl _) (by simp [S]))

omit [Q.IsWeakSerreClass] in
include hT in
/-- A right exact functor which preserves monomorphisms between objects of a weak Serre
subcategory carries a short exact sequence of objects of it to a short exact sequence. -/
theorem shortExact_map {S : ShortComplex 𝒜} (hS : S.ShortExact) (h₁ : Q S.X₁) (h₂ : Q S.X₂) :
    (S.map T).ShortExact := by
  have : Mono (S.map T).f := hT S.f h₁ h₂ hS.mono_f
  have := hS.epi_g
  have : Epi (S.map T).g := inferInstanceAs (Epi (T.map S.g))
  exact ⟨ShortComplex.exact_of_g_is_cokernel _
    ((CokernelCofork.isColimitMapCoconeEquiv _ T) (isColimitOfPreserves T hS.gIsCokernel))⟩

end HalfExact

variable {ι : Type w} {𝒞 : ι → Type u₂} [∀ i, Category.{v₂} (𝒞 i)] [∀ i, Abelian (𝒞 i)]
  (T R : ∀ i, 𝒜 ⥤ 𝒞 i) [∀ i, (T i).PreservesZeroMorphisms]
  [∀ i, PreservesFiniteColimits (T i)] [∀ i, (R i).PreservesZeroMorphisms]
  [∀ i, PreservesFiniteLimits (R i)] [∀ i, PreservesFiniteColimits (R i)]
  (c : ∀ i, T i ⟶ R i)
  (hT : ∀ i ⦃X Y : 𝒜⦄ (f : X ⟶ Y), Q X → Q Y → Mono f → Mono ((T i).map f))

/-- The objects of `Q` at which every component of a family of natural transformations is an
isomorphism. -/
abbrev isoLocus {T R : ∀ i, 𝒜 ⥤ 𝒞 i} (c : ∀ i, T i ⟶ R i) : ObjectProperty 𝒜 :=
  fun X => Q X ∧ ∀ i, IsIso ((c i).app X)

include hT in
/-- **The locus where a family of natural transformations of half-exact functors is invertible
is a weak Serre subcategory.** For each `i`, `R i` is exact, `T i` is right exact and preserves
monomorphisms between objects of the weak Serre subcategory `Q`; the objects of `Q` at which
every `c i` is an isomorphism are closed under isomorphisms, kernels, cokernels and extensions,
and contain a zero object. -/
theorem isWeakSerreClass_isoLocus : (isoLocus Q c).IsWeakSerreClass where
  exists_zero := by
    obtain ⟨Z, hZ, hQZ⟩ := Q.exists_prop_of_containsZero
    refine ⟨Z, hZ, hQZ, fun i => ?_⟩
    have h₂ : IsZero ((R i).obj Z) := (R i).map_isZero hZ
    exact ⟨⟨h₂.to_ _, ((T i).map_isZero hZ).eq_of_src _ _, h₂.eq_of_src _ _⟩⟩
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
    exact isIso_of_isLimit_kernelForks (isLimitMapKernelFork Q (T i) (hT i) hX hY hk)
      ((KernelFork.isLimitMapConeEquiv _ (R i)) (isLimitOfPreserves (R i) hk))
      ((c i).app _) ((c i).app _)
      ((c i).naturality f) ((c i).app k.pt) ((c i).naturality k.ι).symm
  cokernels_le := by
    rintro _ ⟨f, k, hk, ⟨hX, hcX⟩, ⟨hY, hcY⟩⟩
    refine ⟨Q.prop_of_isColimit_cokernelCofork hk hX hY, fun i => ?_⟩
    have := hcX i
    have := hcY i
    exact isIso_of_isColimit_cokernelCoforks
      ((CokernelCofork.isColimitMapCoconeEquiv _ (T i)) (isColimitOfPreserves (T i) hk))
      ((CokernelCofork.isColimitMapCoconeEquiv _ (R i)) (isColimitOfPreserves (R i) hk))
      ((c i).app _) ((c i).app _)
      ((c i).naturality f) ((c i).app k.pt) ((c i).naturality k.π)
  prop_X₂_of_shortExact := by
    rintro S hS ⟨h₁, hc₁⟩ ⟨h₃, hc₃⟩
    have h₂ : Q S.X₂ := Q.prop_X₂_of_shortExact hS h₁ h₃
    refine ⟨h₂, fun i => ?_⟩
    let φ : S.map (T i) ⟶ S.map (R i) := ShortComplex.homMk ((c i).app _) ((c i).app _)
      ((c i).app _) ((c i).naturality S.f).symm ((c i).naturality S.g).symm
    have : IsIso φ.τ₁ := hc₁ i
    have : IsIso φ.τ₃ := hc₃ i
    exact ShortComplex.isIso₂_of_shortExact_of_isIso₁₃ φ (shortExact_map Q (T i) (hT i) hS h₁ h₂)
      (hS.map_of_exact (R i))

end CategoryTheory.ObjectProperty
