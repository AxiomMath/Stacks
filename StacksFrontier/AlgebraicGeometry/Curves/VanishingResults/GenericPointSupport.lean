module

public import StacksFrontier.Algebra.Category.ModuleCat.Sheaf.StalkEpiMono
public import StacksFrontier.Algebra.Category.ModuleCat.Sheaf.ULiftUnit
public import StacksFrontier.AlgebraicGeometry.AmplePowers.ModuleStalk
public import StacksFrontier.AlgebraicGeometry.Curves.VanishingResults.DualizingSheafClauseFive
public import StacksFrontier.AlgebraicGeometry.Curves.VanishingResults.DualizingSheafHom
public import StacksFrontier.AlgebraicGeometry.Curves.VanishingResults.GlobalSectionsGeneration
public import StacksFrontier.AlgebraicGeometry.Divisors.Reflexive.HullExtensionUniqueness
public import StacksFrontier.AlgebraicGeometry.Divisors.Reflexive.SpanRestrictInvertible
public import StacksFrontier.AlgebraicGeometry.Divisors.TorsionFree.Submodule
public import StacksFrontier.Topology.Dimension.NowhereDense

/-!
# Modules on an integral curve read off at the generic point

Let `X` be an integral scheme of dimension at most one with generic point `η`. A module of finite
type whose stalk at `η` vanishes is supported in dimension zero: its support is closed and misses
`η`, hence is nowhere dense, hence has dimension at most `dim X - 1`.

On an integral curve `X` in Situation [Stacks, Tag 0B5D] this gives the step of
[Stacks, Tag 0E3A] and [Stacks, Tag 0E3C] that the source compresses into "since `ℱ` is torsion
free, this map is injective": a nonzero map `ℱ ⟶ ω_X` out of a coherent submodule `ℱ` of an
invertible module is a monomorphism.

## Main results

* `AlgebraicGeometry.topologicalKrullDim_supp_le_zero_of_genericPoint_notMem`: a module of finite
  type on an integral scheme of dimension at most one whose stalk at the generic point vanishes
  has support of dimension at most zero.
* `AlgebraicGeometry.genericPoint_notMem_supp_cokernel_of_genericPoint_mem_supp`: for a map
  `ψ : 𝒦 ⟶ ℱ` with `ℱ` a submodule of an invertible module, if `ψ` is injective at `η` and `𝒦` is
  nonzero at `η` then the cokernel of `ψ` vanishes at `η`.
* `AlgebraicGeometry.CohenMacaulayCurveSituation.mono_of_ne_zero_of_mono`: in Situation
  [Stacks, Tag 0B5D] with `X` integral, a nonzero map from a coherent submodule of an invertible
  module to the dualizing sheaf is a monomorphism.

## The argument for `mono_of_ne_zero_of_mono`

Let `φ : ℱ ⟶ ω_X` be nonzero, `ℱ ⊆ ℒ` with `ℒ` invertible, and `𝒦 = ker φ`. The stalk `ℒ_η` is a
line over the function field, so either `𝒦_η = 0` or `𝒦_η = ℱ_η`.

* If `𝒦_η = ℱ_η`, the coimage `𝒞 = ℱ / 𝒦` vanishes at `η`, so it is a coherent module supported in
  dimension zero and `H¹(X, 𝒞) = 0`. Clause (5) of [Stacks, Tag 0BS2] identifies
  `Hom(𝒞, ω_X)` with the dual of `H¹(X, 𝒞)`, so the monomorphism `𝒞 ⟶ ω_X` through which `φ`
  factors is zero, and so is `φ`.
* If `𝒦_η = 0`, then `𝒦` is a torsion-free module (a submodule of `ℒ`, which is torsion free) whose
  sections all have zero germ at `η`; the germ at `η` is injective on the sections of a
  torsion-free quasi-coherent module, so `𝒦 = 0`.

## References

* [Stacks Project, Tag 0E3A](https://stacks.math.columbia.edu/tag/0E3A)
* [Stacks Project, Tag 0E3C](https://stacks.math.columbia.edu/tag/0E3C)
* [Stacks Project, Tag 0BS2](https://stacks.math.columbia.edu/tag/0BS2)
* [Stacks Project, Tag 0AVR](https://stacks.math.columbia.edu/tag/0AVR)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits TopologicalSpace Opposite
open Stacks.ModuleStalk

universe u

namespace AlgebraicGeometry

variable {X : Scheme.{u}}

/-- **A monomorphism of `𝒪_X`-modules is injective on sections over every open.** -/
theorem Scheme.Modules.injective_app_of_mono {M N : X.Modules} (j : M ⟶ N) [Mono j] (U : X.Opens) :
    Function.Injective (j.app U) :=
  @Stacks.SheafOfModules.injective_app_of_mono _ _ _ X.ringCatSheaf M N j
    ⟨fun g₁ g₂ hg => (inferInstance : Mono j).right_cancellation g₁ g₂ hg⟩ (op U)

/-- A monomorphism of `𝒪_X`-modules is injective on stalks. -/
private theorem injective_mapFun_of_mono {M N : X.Modules} (j : M ⟶ N) [Mono j] (x : X) :
    Function.Injective (mapFun j x) :=
  TopCat.Presheaf.stalkFunctor_map_injective_of_app_injective (f := j.mapPresheaf)
    (fun U => Scheme.Modules.injective_app_of_mono j U) x

/-- **A module of finite type on an integral scheme of dimension at most one which vanishes at the
generic point is supported in dimension zero.** Its support is closed and misses the generic
point, so it is nowhere dense, and a nowhere dense closed subset of a Noetherian space has
dimension at most one less than the space. -/
theorem topologicalKrullDim_supp_le_zero_of_genericPoint_notMem [IsIntegral X]
    [NoetherianSpace X] (hdim : topologicalKrullDim X ≤ 1) (M : X.Modules) (hM : M.IsFiniteType)
    (h : genericPoint X ∉ SheafOfModules.supp M) :
    topologicalKrullDim (SheafOfModules.supp M) ≤ 0 := by
  have := hM
  have hcl : IsClosed (SheafOfModules.supp M) := SheafOfModules.isClosed_supp M
  have hnd : IsNowhereDense (SheafOfModules.supp M) := by
    rw [IsNowhereDense, hcl.closure_eq, interior_eq_empty_iff_dense_compl]
    exact hcl.isOpen_compl.dense ⟨genericPoint X, h⟩
  have h1 := le_trans (hnd.topologicalKrullDim_add_one_le hcl) hdim
  rcases eq_or_ne (topologicalKrullDim (SheafOfModules.supp M)) ⊥ with hb | hb
  · exact hb.trans_le bot_le
  obtain ⟨n, hn⟩ := WithBot.ne_bot_iff_exists.mp hb
  rw [← hn] at h1 ⊢
  have h2 : n + 1 ≤ 1 := by exact_mod_cast h1
  have hn0 : n < 1 := by
    rcases eq_or_ne n ⊤ with rfl | hne
    · simp at h2
    · exact (ENat.add_one_le_iff hne).mp h2
  exact_mod_cast (Order.lt_one_iff.mp hn0).le

/-- **A section with zero germ at the generic point vanishes on a torsion-free submodule of an
invertible module.** The germ at the generic point of an integral scheme is injective on the
sections of a torsion-free quasi-coherent module, and every nonempty open contains the generic
point; so a module of this kind with zero stalk at the generic point is zero. -/
theorem isZero_of_mono_of_genericPoint_notMem [IsIntegral X] [IsLocallyNoetherian X]
    {K L : X.Modules} [SheafOfModules.IsInvertible X.presheaf X.ringCatSheaf.2 L]
    [K.IsQuasicoherent] (j : K ⟶ L) [Mono j] (h : genericPoint X ∉ SheafOfModules.supp K) :
    IsZero K := by
  have htf : Stacks.AlgebraicGeometry.ReflexiveModules.IsTorsionFree K :=
    Stacks.AlgebraicGeometry.ReflexiveModules.isTorsionFree_of_injective_app j
      (fun U => Scheme.Modules.injective_app_of_mono j U)
      (Stacks.AlgebraicGeometry.ReflexiveModules.isTorsionFree_of_isInvertibleModule L)
  refine Stacks.AlgebraicGeometry.DevissageNoetherian.isZero_of_supp_eq_empty K ?_
  refine Set.eq_empty_iff_forall_notMem.mpr fun x hx => ?_
  obtain ⟨a, ha⟩ := hx
  obtain ⟨U, hxU, t, rfl⟩ := TopCat.Presheaf.exists_germ_eq _ a
  have hηU : genericPoint X ∈ U :=
    ((genericPoint_spec X).mem_open_set_iff U.isOpen).mpr ⟨x, trivial, hxU⟩
  have hη0 : (K.presheaf.germ U (genericPoint X) hηU).hom t = 0 := by
    by_contra hne
    exact h ⟨_, hne⟩
  have ht : t = 0 :=
    injective_generic_germ_of_isTorsionFree K htf hηU (hη0.trans (map_zero _).symm)
  exact ha (by rw [ht, map_zero])

/-- **A map into a submodule of an invertible module, injective and nonzero at the generic point,
has cokernel vanishing there.** For `ψ : 𝒦 ⟶ ℱ` and `ι : ℱ ⟶ ℒ` with `ι` a monomorphism and `ℒ`
invertible on an integral scheme, the stalk `ℒ_η` is a line over the function field; if the
image of `𝒦_η` in it is nonzero it is all of `ℒ_η`, so `ℱ_η` is the image of `𝒦_η` and the
cokernel of `ψ` has zero stalk at `η`. -/
theorem genericPoint_notMem_supp_cokernel_of_genericPoint_mem_supp [IsIntegral X]
    [IsLocallyNoetherian X] {K F L : X.Modules}
    [SheafOfModules.IsInvertible X.presheaf X.ringCatSheaf.2 L] (ψ : K ⟶ F) (ι : F ⟶ L)
    [Mono ι] (hK : ∃ a : TopCat.Presheaf.stalk (C := Ab.{u}) K.presheaf (genericPoint X),
      mapFun (ψ ≫ ι) (genericPoint X) a ≠ 0) :
    genericPoint X ∉ SheafOfModules.supp (cokernel ψ) := by
  let : Field (X.presheaf.stalk (genericPoint X)) := inferInstanceAs (Field X.functionField)
  obtain ⟨a, ha⟩ := hK
  have hrank :=
    Stacks.AlgebraicGeometry.ReflexiveModules.finrank_stalk_genericPoint_eq_one_of_isInvertible L
  have hspan := (finrank_eq_one_iff_of_nonzero' _ ha).mp hrank
  rintro ⟨c, hc⟩
  obtain ⟨b, rfl⟩ := @Stacks.SheafOfModules.StalkEpiMono.stalk_surjective_of_epi _
    X.ringCatSheaf _ _ (cokernel.π ψ)
    ⟨fun g₁ g₂ hg => (inferInstance : Epi (cokernel.π ψ)).left_cancellation g₁ g₂ hg⟩
    (genericPoint X) c
  obtain ⟨r, hr⟩ := hspan (mapFun ι (genericPoint X) b)
  have hb : b = mapFun ψ (genericPoint X) (r • a) :=
    injective_mapFun_of_mono ι _ (by rw [← hr, mapFun_smul, mapFun_smul, ← mapFun_comp])
  apply hc
  change mapFun (cokernel.π ψ) (genericPoint X) b = 0
  rw [hb, ← mapFun_comp, cokernel.condition]
  obtain ⟨U, hxU, t, ht⟩ := TopCat.Presheaf.exists_germ_eq _ (r • a)
  rw [← ht, mapFun_germ]
  simp

namespace CohenMacaulayCurveSituation

variable {S : CohenMacaulayCurveSituation.{u}}

/-- **A nonzero map from a coherent submodule of an invertible module to the dualizing sheaf is a
monomorphism**, in Situation [Stacks, Tag 0B5D] with `X` integral. This is the step "since `ℱ` is
torsion free, this map is injective" of the proofs of [Stacks, Tag 0E3A] and [Stacks, Tag 0E3C].

The coimage of `φ` vanishes at the generic point unless the kernel does. In the first case the
coimage is supported in dimension zero, so it has no first cohomology and, by clause (5) of
[Stacks, Tag 0BS2], no nonzero map to `ω_X`, forcing `φ = 0`; in the second the kernel is a
torsion-free module vanishing at the generic point, hence zero. -/
theorem mono_of_ne_zero_of_mono [IsIntegral S.X] {F L : S.X.Modules}
    [SheafOfModules.IsInvertible S.X.presheaf S.X.ringCatSheaf.2 L] (ι : F ⟶ L) [Mono ι]
    (hFc : F.IsCoherent) (φ : F ⟶ Stacks.Duality.dualizingSheafOverField S.f) (hφ : φ ≠ 0) :
    Mono φ := by
  have : IsLocallyNoetherian S.X := LocallyOfFiniteType.isLocallyNoetherian S.f
  have : IsNoetherian S.X := isNoetherian_of_locallyOfFiniteType S.f
  have hdim : topologicalKrullDim S.X ≤ 1 := S.dimension_one.le
  have hFq : F.IsQuasicoherent := isQuasicoherent_of_isCoherent F
  have hωq := Stacks.Duality.isQuasicoherent_dualizingSheafOverField S.f
  have hKc : (kernel φ).IsCoherent :=
    Stacks.AlgebraicGeometry.CoherentOfFiniteType.isCoherent_of_mono_of_isQuasicoherent hFc
      (kernel.ι φ)
  have hKq : (kernel φ).IsQuasicoherent := isQuasicoherent_of_isCoherent _
  refine Preadditive.mono_of_kernel_zero ?_
  by_cases hη : genericPoint S.X ∈ SheafOfModules.supp (kernel φ)
  · exfalso
    obtain ⟨a, ha⟩ := hη
    have hC := genericPoint_notMem_supp_cokernel_of_genericPoint_mem_supp (kernel.ι φ) ι
      ⟨a, fun h0 => ha (injective_mapFun_of_mono (kernel.ι φ ≫ ι) _ (h0.trans (map_zero _).symm))⟩
    have hCc : (cokernel (kernel.ι φ)).IsCoherent :=
      Stacks.AlgebraicGeometry.CoherentOfFiniteType.isCoherent_of_epi_of_isQuasicoherent hFc
        (cokernel.π (kernel.ι φ))
    have hCdim := topologicalKrullDim_supp_le_zero_of_genericPoint_notMem hdim _
      (@_root_.SheafOfModules.IsCoherent.isFiniteType _ _ _ _ hCc) hC
    have hzero : Abelian.factorThruCoimage φ = 0 := by
      refine (Stacks.Duality.homDualizingSheafAddEquiv S.f hdim _
        (isQuasicoherent_of_isCoherent _)).injective ?_
      rw [map_zero]
      exact (S.isZero_firstCohomology_of_supp_dim_le_zero hCc hCdim).eq_of_src _ _
    exact hφ (by rw [← Abelian.coimage.fac φ, hzero, comp_zero])
  · exact (isZero_of_mono_of_genericPoint_notMem (kernel.ι φ ≫ ι) hη).eq_of_src _ _

end CohenMacaulayCurveSituation

end AlgebraicGeometry

end
