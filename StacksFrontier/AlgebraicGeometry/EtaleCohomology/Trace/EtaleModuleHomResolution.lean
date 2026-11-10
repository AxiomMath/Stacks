module

public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.Trace.EtaleModuleHomPullback
public import Mathlib.Algebra.Homology.HomologySequence
public import Mathlib.Algebra.Homology.HomologicalComplexAbelian

/-!
# `Hom_R(N, -)` on an injective resolution of a locally injective sheaf

Let `A` be a commutative ring, `R` a left Noetherian `A`-algebra and `F'` a sheaf of `R`-modules on
the small étale site of a scheme which is *locally injective*: for every injective map `N₁ → N₂` of
finite `R`-modules, `Hom_R(N₂, F') → Hom_R(N₁, F')` is an epimorphism of sheaves. Let
`F' → I⁰ → I¹ → ⋯` be an injective resolution. Then for every finite `R`-module `N` the complex
`Hom_R(N, I)` is exact in positive degrees: the sheaves `Ext^q_R(N, F')` vanish for `q > 0`.

## Main results

* `Stacks.EtaleCohomology.exactAt_homSheaf_free`: exactness of `Hom_R(R^k, -)` on complexes.
* `Stacks.EtaleCohomology.exactAt_homSheaf_of_locallyInjective`: `Hom_R(N, I)` is exact in
  positive degrees for an injective resolution `I` of a locally injective sheaf.

## References

* [Stacks Project, Tag 03UG](https://stacks.math.columbia.edu/tag/03UG)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits Opposite
open AlgebraicGeometry AlgebraicGeometry.Scheme

universe u

namespace Stacks.EtaleCohomology

attribute [local instance] moduleCat_hasLimitsOfSize

variable {A : Type} [CommRing A] {R : Type} [Ring R] [Algebra A R]

/-- The functor `Hom_R(N, -)` on sheaves of `R`-modules, valued in sheaves of `A`-modules. -/
abbrev homSheaf (A : Type) [CommRing A] [Algebra A R] (N : ModuleCat.{u + 1} R) (Y : Scheme.{u}) :
    EtaleModules.{u, 0} R Y ⥤ EtaleModules.{u, 0} A Y :=
  sheafCompose Y.smallEtaleTopology (homFunctor N (centralScalars (A := A) N))

/-- The functor `Hom_R(N, -)` on sheaves is additive. -/
instance homSheaf_additive (N : ModuleCat.{u + 1} R) (Y : Scheme.{u}) :
    (homSheaf A N Y).Additive where
  map_add {F G f g} := by
    apply Sheaf.hom_ext
    ext W : 2
    exact (homFunctor N (centralScalars (A := A) N)).map_add

/-- The transformation `Hom_R(N₂, -) ⟶ Hom_R(N₁, -)` induced by `v : N₁ ⟶ N₂`. -/
abbrev homSheafPrecomp {N₁ N₂ : ModuleCat.{u + 1} R} (v : N₁ ⟶ N₂) (Y : Scheme.{u}) :
    homSheaf A N₂ Y ⟶ homSheaf A N₁ Y :=
  sheafCompose_map Y.smallEtaleTopology (homFunctorPrecomp (A := A) v)

/-- The map `Hom_R(N₂, K) ⟶ Hom_R(N₁, K)` of complexes induced by `v : N₁ ⟶ N₂`. -/
abbrev homSheafPrecompC {N₁ N₂ : ModuleCat.{u + 1} R} (v : N₁ ⟶ N₂) (Y : Scheme.{u})
    (K : CochainComplex (EtaleModules.{u, 0} R Y) ℤ) :
    ((homSheaf A N₂ Y).mapHomologicalComplex (ComplexShape.up ℤ)).obj K ⟶
      ((homSheaf A N₁ Y).mapHomologicalComplex (ComplexShape.up ℤ)).obj K :=
  (NatTrans.mapHomologicalComplex (homSheafPrecomp (A := A) v Y) (ComplexShape.up ℤ)).app K

/-- Restriction of scalars is exact on complexes. -/
lemma exactAt_restrictScalars_mapHomologicalComplex {Y : Scheme.{u}}
    (K : CochainComplex (EtaleModules.{u, 0} R Y) ℤ) (q : ℤ) (hK : K.ExactAt q) :
    (((etaleModuleRestrictScalars (algebraMap A R) Y).mapHomologicalComplex
      (ComplexShape.up ℤ)).obj K).ExactAt q := by
  rw [HomologicalComplex.exactAt_iff_isZero_homology] at hK ⊢
  exact ((etaleModuleRestrictScalars (algebraMap A R) Y).map_isZero hK).of_iso
    ((K.sc q).mapHomologyIso (etaleModuleRestrictScalars (algebraMap A R) Y))

/-- **`Hom_R(R^k, -)` is exact on complexes.** -/
lemma exactAt_homSheaf_free {Y : Scheme.{u}} (K : CochainComplex (EtaleModules.{u, 0} R Y) ℤ)
    (q : ℤ) (hK : K.ExactAt q) (k : ℕ) :
    (((homSheaf A (freeModuleU.{u} R k) Y).mapHomologicalComplex (ComplexShape.up ℤ)).obj K).ExactAt
      q := by
  have hreg : IsZero ((((homSheaf A (regularModuleU.{u} R) Y).mapHomologicalComplex
      (ComplexShape.up ℤ)).obj K).homology q) := by
    have h := exactAt_restrictScalars_mapHomologicalComplex (A := A) K q hK
    rw [HomologicalComplex.exactAt_iff_isZero_homology] at h
    exact h.of_iso (HomologicalComplex.homologyMapIso
      ((NatIso.mapHomologicalComplex (sheafComposeIso Y homFunctorRegularIso)
        (ComplexShape.up ℤ)).app K) q)
  have hsum0 : ∀ G : EtaleModules.{u, 0} R Y,
      ∑ j, (homSheafPrecomp (A := A) (freeModuleι k j) Y).app G ≫
        (homSheafPrecomp (A := A) (freeModuleπ k j) Y).app G = 𝟙 _ := fun G =>
    show ∑ j, homPrecompApp (A := A) (freeModuleι k j) G ≫
        homPrecompApp (freeModuleπ k j) G = 𝟙 _ by
      simp only [← homPrecompApp_comp, ← homPrecompApp_sum, sum_freeModuleπ_comp_ι,
        homPrecompApp_id]
  have hsum : ∑ j, homSheafPrecompC (A := A) (freeModuleι k j) Y K ≫
      homSheafPrecompC (A := A) (freeModuleπ k j) Y K = 𝟙 _ := by
    ext q' : 1
    rw [← HomologicalComplex.Hom.fAddMonoidHom_apply, map_sum]
    exact hsum0 (K.X q')
  rw [HomologicalComplex.exactAt_iff_isZero_homology, IsZero.iff_id_eq_zero,
    ← HomologicalComplex.homologyMap_id, ← hsum]
  change (HomologicalComplex.homologyFunctor _ _ q).map _ = 0
  rw [Functor.map_sum]
  refine Finset.sum_eq_zero fun j _ => ?_
  rw [Functor.map_comp, hreg.eq_of_tgt ((HomologicalComplex.homologyFunctor _ _ q).map
    (homSheafPrecompC (A := A) (freeModuleι k j) Y K)) 0]
  exact zero_comp

/-- `Hom_R(N, -)` preserves finite limits of sheaves. -/
lemma preservesFiniteLimits_homSheaf (N : ModuleCat.{u + 1} R) (Y : Scheme.{u}) :
    PreservesFiniteLimits (homSheaf A N Y) := by
  have : PreservesFiniteLimits ((Functor.whiskeringRight Y.Etaleᵒᵖ (ModuleCat.{u + 1} R)
      (ModuleCat.{u + 1} A)).obj (homFunctor N (centralScalars (A := A) N))) :=
    ⟨fun _ _ _ => inferInstance⟩
  have : PreservesFiniteLimits (homSheaf A N Y ⋙ sheafToPresheaf Y.smallEtaleTopology
      (ModuleCat.{u + 1} A)) := by
    change PreservesFiniteLimits (sheafToPresheaf Y.smallEtaleTopology (ModuleCat.{u + 1} R) ⋙
      (Functor.whiskeringRight Y.Etaleᵒᵖ (ModuleCat.{u + 1} R) (ModuleCat.{u + 1} A)).obj
        (homFunctor N (centralScalars (A := A) N)))
    infer_instance
  exact preservesFiniteLimits_of_reflects_of_preserves _
    (sheafToPresheaf Y.smallEtaleTopology (ModuleCat.{u + 1} A))

/-- **`Hom_R(M, F')` is the sheaf of `0`-cycles of `Hom_R(M, I)`**, for `ι₀ : F' ⟶ I⁰` a kernel of
`I⁰ → I¹`. -/
def homSheafCyclesZeroIso {Y : Scheme.{u}} (F' : EtaleModules.{u, 0} R Y)
    (I : CochainComplex (EtaleModules.{u, 0} R Y) ℤ) (ι₀ : F' ⟶ I.X 0) (w : ι₀ ≫ I.d 0 1 = 0)
    (hι₀ : IsLimit (KernelFork.ofι ι₀ w)) (M : ModuleCat.{u + 1} R) :
    (homSheaf A M Y).obj F' ≅
      (((homSheaf A M Y).mapHomologicalComplex (ComplexShape.up ℤ)).obj I).cycles 0 :=
  haveI := preservesFiniteLimits_homSheaf (A := A) M Y
  IsLimit.conePointUniqueUpToIso (KernelFork.mapIsLimit _ hι₀ (homSheaf A M Y))
    ((((homSheaf A M Y).mapHomologicalComplex (ComplexShape.up ℤ)).obj I).cyclesIsKernel 0 1
      (by simp))

/-- `homSheafCyclesZeroIso` followed by the inclusion of the `0`-cycles is `Hom_R(M, ι₀)`. -/
lemma homSheafCyclesZeroIso_hom_iCycles {Y : Scheme.{u}} (F' : EtaleModules.{u, 0} R Y)
    (I : CochainComplex (EtaleModules.{u, 0} R Y) ℤ) (ι₀ : F' ⟶ I.X 0) (w : ι₀ ≫ I.d 0 1 = 0)
    (hι₀ : IsLimit (KernelFork.ofι ι₀ w)) (M : ModuleCat.{u + 1} R) :
    (homSheafCyclesZeroIso (A := A) F' I ι₀ w hι₀ M).hom ≫
        (((homSheaf A M Y).mapHomologicalComplex (ComplexShape.up ℤ)).obj I).iCycles 0 =
      (homSheaf A M Y).map ι₀ :=
  have := preservesFiniteLimits_homSheaf (A := A) M Y
  IsLimit.conePointUniqueUpToIso_hom_comp (KernelFork.mapIsLimit _ hι₀ (homSheaf A M Y))
    ((((homSheaf A M Y).mapHomologicalComplex (ComplexShape.up ℤ)).obj I).cyclesIsKernel 0 1
      (by simp)) WalkingParallelPair.zero

/-- The dimension-shifting short exact sequence `0 → Hom_R(N, I) → Hom_R(R^k, I) → Hom_R(K, I) → 0`
of complexes, for `R^k → N` surjective with kernel `K`, `I` a complex of injective sheaves. -/
lemma exists_shortExact_homSheafPrecompC [IsNoetherianRing R] {Y : Scheme.{u}}
    (I : CochainComplex (EtaleModules.{u, 0} R Y) ℤ) (hI : ∀ q, Injective (I.X q))
    (N : ModuleCat.{u + 1} R) [Module.Finite R N] : ∃ (k : ℕ)
      (g : freeModuleU.{u} R k ⟶ N) (_ : Epi g),
      Module.Finite R ↑(kernel g : ModuleCat.{u + 1} R) ∧
      (ShortComplex.mk (homSheafPrecompC (A := A) g Y I)
        (homSheafPrecompC (A := A) (kernel.ι g) Y I) (by
          ext q : 1
          apply Sheaf.hom_ext
          ext U f
          change kernel.ι g ≫ g ≫ (show N ⟶ (I.X q).obj.obj U from f) = 0
          rw [kernel.condition_assoc, zero_comp])).ShortExact := by
  obtain ⟨k, π, hπ⟩ := Module.Finite.exists_fin' R N
  let g : freeModuleU.{u} R k ⟶ N := ModuleCat.ofHom (π ∘ₗ
    (LinearEquiv.piCongrRight fun _ : Fin k => ULift.moduleEquiv (R := R) (M := R)).toLinearMap)
  have hg : Epi g := (ModuleCat.epi_iff_surjective _).2 (hπ.comp (LinearEquiv.surjective _))
  have : IsNoetherian R (freeModuleU.{u} R k) := inferInstance
  refine ⟨k, g, hg, Module.Finite.of_injective (kernel.ι g).hom
    ((ModuleCat.mono_iff_injective _).1 inferInstance), ?_⟩
  let SR : ShortComplex (ModuleCat.{u + 1} R) := ShortComplex.mk (kernel.ι g) g (kernel.condition g)
  have hSR : SR.ShortExact := { exact := ShortComplex.exact_of_f_is_kernel _ (kernelIsKernel g) }
  refine HomologicalComplex.shortExact_of_degreewise_shortExact _ fun q => ?_
  exact shortExact_etaleModuleHom_of_injective (A := A) SR hSR (I.X q)
    (fun V => @injective_obj_obj_of_injective _ _ _ (I.X q) (hI q) V)

/-- **`H⁰(Hom_R(-, I))` on an injection of modules is an epimorphism** for a resolution `I` of a
locally injective sheaf `F'`: it is `Hom_R(N₂, F') → Hom_R(N₁, F')`. -/
lemma epi_homologyMap_zero_homSheafPrecompC {Y : Scheme.{u}} (F' : EtaleModules.{u, 0} R Y)
    (hF' : ∀ {N₁ N₂ : ModuleCat.{u + 1} R} [Module.Finite R N₁] [Module.Finite R N₂]
      (v : N₁ ⟶ N₂) [Mono v], Epi ((homSheafPrecomp (A := A) v Y).app F'))
    (I : CochainComplex (EtaleModules.{u, 0} R Y) ℤ) [I.IsStrictlyGE 0]
    (ι₀ : F' ⟶ I.X 0) (w : ι₀ ≫ I.d 0 1 = 0) (hι₀ : IsLimit (KernelFork.ofι ι₀ w))
    {M₁ M₂ : ModuleCat.{u + 1} R} [Module.Finite R M₁] [Module.Finite R M₂] (v : M₁ ⟶ M₂)
    [Mono v] : Epi (HomologicalComplex.homologyMap (homSheafPrecompC (A := A) v Y I) 0) := by
  let Z := fun (M : ModuleCat.{u + 1} R) =>
    ((homSheaf A M Y).mapHomologicalComplex (ComplexShape.up ℤ)).obj I
  let e := fun (M : ModuleCat.{u + 1} R) => homSheafCyclesZeroIso (A := A) F' I ι₀ w hι₀ M
  have he : ∀ M, (e M).hom ≫ (Z M).iCycles 0 = (homSheaf A M Y).map ι₀ :=
    homSheafCyclesZeroIso_hom_iCycles (A := A) F' I ι₀ w hι₀
  have hπiso : ∀ M, IsIso ((Z M).homologyπ 0) := fun M =>
    (Z M).isIso_homologyπ (-1) 0 (by simp)
      (((homSheaf A M Y).map_isZero (I.isZero_of_isStrictlyGE 0 (-1) (by lia))).eq_of_src _ _)
  have hc : (e M₂).hom ≫ HomologicalComplex.cyclesMap (homSheafPrecompC (A := A) v Y I) 0 =
      (homSheafPrecomp (A := A) v Y).app F' ≫ (e M₁).hom := by
    rw [← cancel_mono ((Z M₁).iCycles 0), Category.assoc, HomologicalComplex.cyclesMap_i,
      ← Category.assoc, he, Category.assoc, he]
    exact ((homSheafPrecomp (A := A) v Y).naturality ι₀).symm
  have hcm : HomologicalComplex.cyclesMap (homSheafPrecompC (A := A) v Y I) 0 =
      (e M₂).inv ≫ (homSheafPrecomp (A := A) v Y).app F' ≫ (e M₁).hom := by
    rw [← hc, Iso.inv_hom_id_assoc]
  have := hF' v
  have := hπiso M₁
  have := hπiso M₂
  have hh := HomologicalComplex.homologyπ_naturality (homSheafPrecompC (A := A) v Y I) 0
  have : HomologicalComplex.homologyMap (homSheafPrecompC (A := A) v Y I) 0 =
      inv ((Z M₂).homologyπ 0) ≫ HomologicalComplex.cyclesMap
        (homSheafPrecompC (A := A) v Y I) 0 ≫ (Z M₁).homologyπ 0 := by
    rw [← hh, IsIso.inv_hom_id_assoc]
  rw [this, hcm]
  infer_instance

/-- **The sheaves `Ext^q_R(N, F')` vanish for `q > 0`** when `F'` is locally injective: for an
injective resolution `F' → I`, the complex `Hom_R(N, I)` is exact in positive degrees, for every
finite `R`-module `N`. -/
theorem exactAt_homSheaf_of_locallyInjective [IsNoetherianRing R] {Y : Scheme.{u}}
    (F' : EtaleModules.{u, 0} R Y)
    (hF' : ∀ {N₁ N₂ : ModuleCat.{u + 1} R} [Module.Finite R N₁] [Module.Finite R N₂]
      (v : N₁ ⟶ N₂) [Mono v], Epi ((homSheafPrecomp (A := A) v Y).app F'))
    (I : CochainComplex (EtaleModules.{u, 0} R Y) ℤ) [I.IsStrictlyGE 0]
    (hI : ∀ q, Injective (I.X q)) (ι₀ : F' ⟶ I.X 0) (w : ι₀ ≫ I.d 0 1 = 0)
    (hι₀ : IsLimit (KernelFork.ofι ι₀ w)) (hexact : ∀ q : ℤ, 1 ≤ q → I.ExactAt q) :
    ∀ (q : ℕ) (N : ModuleCat.{u + 1} R) [Module.Finite R N],
      (((homSheaf A N Y).mapHomologicalComplex (ComplexShape.up ℤ)).obj I).ExactAt (q + 1) := by
  have hsetup := exists_shortExact_homSheafPrecompC (A := A) I hI
  have hH0 := fun {M₁ M₂ : ModuleCat.{u + 1} R} [Module.Finite R M₁] [Module.Finite R M₂]
      (v : M₁ ⟶ M₂) [Mono v] =>
    epi_homologyMap_zero_homSheafPrecompC (A := A) F' hF' I ι₀ w hι₀ v
  intro q
  induction q with
  | zero =>
    intro N _
    obtain ⟨k, g, hg, hK, hSc⟩ := hsetup N
    have h01 : ((0 : ℕ) : ℤ) + 1 = 1 := by simp
    rw [h01]
    have hF1 := exactAt_homSheaf_free (A := A) I 1 (hexact 1 le_rfl) k
    rw [HomologicalComplex.exactAt_iff_isZero_homology] at hF1 ⊢
    have hδepi : Epi (hSc.δ 0 1 (by simp)) :=
      (hSc.homology_exact₁ 0 1 (by simp)).epi_f (hF1.eq_of_tgt _ _)
    have := hK
    have hE := hH0 (kernel.ι g)
    have hc := hSc.comp_δ 0 1 (by simp)
    have hδ0 : hSc.δ 0 1 (by simp) = 0 := by
      rw [← cancel_epi
        (HomologicalComplex.homologyMap (homSheafPrecompC (A := A) (kernel.ι g) Y I) 0), comp_zero]
      exact hc
    rw [IsZero.iff_id_eq_zero, ← cancel_epi (hSc.δ 0 1 rfl), hδ0]
    simp
  | succ q ih =>
    intro N _
    obtain ⟨k, g, hg, hK, hSc⟩ := hsetup N
    have hq : ((q + 1 : ℕ) : ℤ) + 1 = ((q : ℤ) + 1) + 1 := by push_cast; ring
    rw [hq]
    have hF := exactAt_homSheaf_free (A := A) I ((q : ℤ) + 1 + 1) (hexact _ (by lia)) k
    have hKq := ih (kernel g : ModuleCat.{u + 1} R)
    rw [HomologicalComplex.exactAt_iff_isZero_homology] at hF hKq ⊢
    exact (hSc.homology_exact₁ ((q : ℤ) + 1) ((q : ℤ) + 1 + 1) (by simp)).isZero_X₂_iff.2
      ⟨hKq.eq_of_src _ _, hF.eq_of_tgt _ _⟩

end Stacks.EtaleCohomology
