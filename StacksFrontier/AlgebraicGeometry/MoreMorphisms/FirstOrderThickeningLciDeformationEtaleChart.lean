module

public import StacksFrontier.AlgebraicGeometry.AffineQcohPushforward.Colimits
public import StacksFrontier.AlgebraicGeometry.Conormal.RestrictSquareMap
public import StacksFrontier.AlgebraicGeometry.Conormal.SquareFlatIso
public import StacksFrontier.AlgebraicGeometry.Flatness.FlatteningFunctors.FlatPullbackStalk
public import StacksFrontier.AlgebraicGeometry.Modules.FiniteLocallyFreeDescent.Fpqc
public import StacksFrontier.AlgebraicGeometry.MoreMorphisms.FirstOrderThickeningLciDeformation

/-!
# Deforming a cover through an étale chart of the target

This file proves the scheme-level heart of [Stacks Project, Tag 06D8] in the form its proof for
algebraic spaces needs. The target `X'` there is an algebraic space, so the conormal sequence
`0 → i^*𝒞_{X/X'} → 𝒞_{Z/X'} → 𝒞_{Z/X} → 0` cannot be written on `Z` directly. It *can* be
written after pulling back along an étale chart. The statement below takes as input:

* a first-order thickening `j : Z ⟶ W` of the affine scheme `Z`, together with `g : W ⟶ U'`.
  In the application `W` is the universal first-order thickening of `Z` over `X'`;
* a surjective étale `a : Z_V ⟶ Z` and an étale `b : W_V ⟶ W` with `Z_V = Z ×_W W_V`, such
  that `Z_V ⊆ W_V` is a scheme-level universal first-order thickening of `Z_V` over a flat
  `V' ⟶ U'`, through a local complete intersection `f_V : Z_V ⟶ X_V` into
  `X_V = U ×_{U'} V'`.

It concludes as Tag 06D8 does. There is a first-order thickening `Z ⊆ Z'` inside `W` with
`Z' ⟶ U'` finite locally free of degree `d` and `Z = U ×_{U'} Z'`.

The conormal map `φ : q^*𝒞_{U/U'} ⟶ 𝒞_{Z/W}` of the square `(Z ⊆ W) → (U ⊆ U')` plays the role
of the source's first arrow. By the composition law of [Stacks Project, Tag 04G2], its pullback
along `a` is the conormal map of the composite square `(Z_V ⊆ W_V) → (U ⊆ U')`. The same map
also factors through `(X_V ⊆ V')`. There the first factor is invertible by flat base change
([Stacks Project, Tag 0473]), and the second is the first arrow of the sequence of
[Stacks Project, Tag 06BA]: a monomorphism with finite locally free cokernel
([Stacks Project, Tag 06B9]). Monomorphy descends along the flat surjective `a` stalkwise, and
finite local freeness of the cokernel descends by [Stacks Project, Tag 05B2]. So `φ` is a split
monomorphism on the affine `Z`, and
`Stacks.Thickenings.exists_isFirstOrderThickening_isFiniteLocallyFreeOfRank_of_splitting` applies
with `X = U` and `X' = U'`.

## Main results

* `AlgebraicGeometry.Scheme.Modules.mono_of_mono_pullback_of_surjective`: monomorphy of a map of
  modules descends along a flat surjective morphism.
* `AlgebraicGeometry.Scheme.Modules.isFiniteLocallyFree_cokernel_of_pullback`: finite local
  freeness of a cokernel of quasi-coherent modules descends along a surjective étale morphism.
* `Stacks.Thickenings.exists_finiteLocallyFreeOfRank_deformation_of_etaleChart`: the deformation.

## References

* [Stacks Project, Tag 06D8](https://stacks.math.columbia.edu/tag/06D8)
* [Stacks Project, Tag 0473](https://stacks.math.columbia.edu/tag/0473)
* [Stacks Project, Tag 04G2](https://stacks.math.columbia.edu/tag/04G2)
* [Stacks Project, Tag 05B2](https://stacks.math.columbia.edu/tag/05B2)
* [Stacks Project, Tag 06B9](https://stacks.math.columbia.edu/tag/06B9)
* [Stacks Project, Tag 06BA](https://stacks.math.columbia.edu/tag/06BA)
-/

@[expose] public noncomputable section

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits
open RingedSpaceModuleAdjunction
open Stacks.Immersion

universe u

namespace AlgebraicGeometry.Scheme.Modules

variable {Z ZV : Scheme.{u}} (a : ZV ⟶ Z)

/-- **Monomorphy of a map of modules descends along a flat surjective morphism.** Monomorphy is
stalkwise, the stalk of the pullback at `z'` is injective exactly when the stalk of the map at
`a z'` is, and every point of `Z` is such an image. -/
theorem mono_of_mono_pullback_of_surjective [Flat a] [Surjective a] {M N : Z.Modules}
    (φ : M ⟶ N) (h : Mono ((Scheme.Modules.pullback a).map φ)) : Mono φ := by
  refine (SheafOfModules.mono_iff_injective_stalkMap _).2 fun z ↦ ?_
  obtain ⟨z', rfl⟩ := a.surjective z
  exact (injective_stalkMap_modulePullback_iff a φ z').1
    ((SheafOfModules.mono_iff_injective_stalkMap _).1 h z')

/-- A surjective étale morphism is, on its own, an fpqc covering of its target. -/
theorem singleton_mem_fpqcPrecoverage [Etale a] [Surjective a] :
    Presieve.singleton a ∈ Scheme.fpqcPrecoverage Z := by
  have hE : Presieve.singleton a ∈ Scheme.precoverage @Etale Z :=
    (Scheme.singleton_mem_precoverage_iff (P := @Etale) a).2 ⟨a.surjective, inferInstance⟩
  exact ⟨Scheme.precoverage_le_qcPrecoverage_of_isOpenMap
    (fun _ _ f (_ : Etale f) ↦ f.isOpenMap) _ hE,
    (Scheme.singleton_mem_precoverage_iff (P := @Flat) a).2 ⟨a.surjective, inferInstance⟩⟩

/-- **Finite local freeness of a cokernel descends along a surjective étale morphism.** Pullback
is a left adjoint, so it carries the cokernel of `φ` to the cokernel of the pullback of `φ`, and
[Stacks Project, Tag 05B2] descends finite local freeness along the one-member fpqc covering
`{a}`. -/
theorem isFiniteLocallyFree_cokernel_of_pullback [Etale a] [Surjective a] {M N : Z.Modules}
    [M.IsQuasicoherent] [N.IsQuasicoherent] (φ : M ⟶ N)
    (h : SheafOfModules.IsFiniteLocallyFree.{u, u, u}
      (cokernel ((Scheme.Modules.pullback a).map φ))) :
    SheafOfModules.IsFiniteLocallyFree.{u, u, u} (cokernel φ) := by
  let 𝒰 : Z.Cover.{u} Scheme.fpqcPrecoverage :=
    Precoverage.ZeroHypercover.singleton a (singleton_mem_fpqcPrecoverage a)
  exact isFiniteLocallyFree_of_pullback_fpqcCover (cokernel φ) 𝒰 fun _ ↦
    @SheafOfModules.IsFiniteLocallyFree.of_iso _ _ _
      (PreservesCokernel.iso (Scheme.Modules.pullback a) φ).symm h

/-- **A monomorphism of quasi-coherent modules on an affine scheme with finite locally free
cokernel is split.** -/
theorem nonempty_splitting_of_mono_of_isFiniteLocallyFree_cokernel [IsAffine Z] {M N : Z.Modules}
    [M.IsQuasicoherent] [N.IsQuasicoherent] (φ : M ⟶ N) [Mono φ]
    (h : SheafOfModules.IsFiniteLocallyFree.{u, u, u} (cokernel φ)) :
    Nonempty (ShortComplex.mk φ (cokernel.π φ) (cokernel.condition φ)).Splitting :=
  @nonempty_splitting_of_shortExact_of_isFiniteLocallyFree Z _ _
    { exact := ShortComplex.exact_of_g_is_cokernel _ (cokernelIsCokernel φ)
      mono_f := ‹Mono φ›
      epi_g := inferInstanceAs (Epi (cokernel.π φ)) }
    (inferInstanceAs N.IsQuasicoherent) (inferInstanceAs (cokernel φ).IsQuasicoherent) h

end AlgebraicGeometry.Scheme.Modules

namespace Stacks.Thickenings

/-- **The third term of the sequence of [Stacks Project, Tag 06BA] at a self thickening is finite
locally free.** For a formally unramified local complete intersection morphism `f` into a
first-order thickening `i : X ⟶ X'`, the third term `𝒞_{Z/X}` of the conormal sequence of
`Z ⟶ X ⟶ X'` is finite locally free. The term is the conormal sheaf of the relative universal
first-order thickening, which agrees with `Stacks.Thickenings.universalConormalSheaf` by
[Stacks Project, Tag 0473]. That sheaf is finite locally free by [Stacks Project, Tag 06B9]. -/
theorem isFiniteLocallyFree_transitivityConormalShortComplex_X₃_self {Z X X' : Scheme.{u}}
    (f : Z ⟶ X) [FormallyUnramified f] (hlci : IsLocalCompleteIntersectionMorphism f)
    (i : X ⟶ X') (hi : IsFirstOrderThickening i) (tZ : UniversalFirstOrderThickening (f ≫ i)) :
    SheafOfModules.IsFiniteLocallyFree.{u, u, u}
      (transitivityConormalShortComplex f i tZ (selfUniversalFirstOrderThickening i hi)).X₃ := by
  have hcan : IsIso (UniversalFirstOrderThickening.canonicalMap
      (relativeThickening f i tZ (selfUniversalFirstOrderThickening i hi))
      (universalFirstOrderThickening f)) :=
    ⟨UniversalFirstOrderThickening.canonicalMap _ _,
      UniversalFirstOrderThickening.canonicalMap_comp_canonicalMap _ _,
      UniversalFirstOrderThickening.canonicalMap_comp_canonicalMap _ _⟩
  have hsqrel : IsPullback
      (relativeThickening f i tZ (selfUniversalFirstOrderThickening i hi)).inclusion (𝟙 Z)
      (UniversalFirstOrderThickening.canonicalMap
        (relativeThickening f i tZ (selfUniversalFirstOrderThickening i hi))
        (universalFirstOrderThickening f))
      (universalFirstOrderThickening f).inclusion :=
    IsPullback.of_vert_isIso_mono (CommSq.mk (by
      rw [Category.id_comp, UniversalFirstOrderThickening.canonicalMap_inclusion]))
  have e : universalConormalSheaf f ≅ (transitivityConormalShortComplex f i tZ
      (selfUniversalFirstOrderThickening i hi)).X₃ :=
    ((modulePullbackId Z.toLocallyRingedSpace.toRingedSpace).app
        (universalConormalSheaf f)).symm ≪≫
      @asIso _ _ _ _ _ (isIso_immersionConormalSheafMap_of_flat
        (relativeThickening f i tZ (selfUniversalFirstOrderThickening i hi)).inclusion
        (universalFirstOrderThickening f).inclusion (𝟙 Z)
        (UniversalFirstOrderThickening.canonicalMap
          (relativeThickening f i tZ (selfUniversalFirstOrderThickening i hi))
          (universalFirstOrderThickening f)) hsqrel)
  exact @SheafOfModules.IsFiniteLocallyFree.of_iso Z _ _ e
    (AlgebraicGeometry.isFiniteLocallyFree_universalConormalSheaf_of_isLocalCompleteIntersection
      f hlci)

/-- The morphism `Z' ⟶ X'` of [Stacks Project, Tag 06AE], part (1), into a self thickening is
the structure morphism of `Z'`. -/
theorem transitivityMap_self {Z X X' : Scheme.{u}} (f : Z ⟶ X) (i : X ⟶ X')
    (hi : IsFirstOrderThickening i) (tZ : UniversalFirstOrderThickening (f ≫ i)) :
    transitivityMap f i tZ (selfUniversalFirstOrderThickening i hi) = tZ.toBase :=
  (Category.comp_id _).symm.trans
    (transitivityMap_comp_toBase f i tZ (selfUniversalFirstOrderThickening i hi))

/-- In an abelian category, if `E ≫ E' ≫ ψ = (c ≫ φ) ≫ m` with `E`, `E'`, `c`, `m` invertible and
`ψ` a monomorphism, then `φ` is a monomorphism and its cokernel is that of `ψ`. -/
theorem mono_and_nonempty_cokernelIso_of_comp_eq {C : Type*} [Category C] [Abelian C]
    {A A' B B' D' D : C} (E : A ⟶ B) (E' : B ⟶ B') (ψ : B' ⟶ D) (c : A ⟶ A') (φ : A' ⟶ D')
    (m : D' ⟶ D) (h : E ≫ E' ≫ ψ = (c ≫ φ) ≫ m) (hE : IsIso E) (hE' : IsIso E') (hc : IsIso c)
    (hm : IsIso m) (hψ : Mono ψ) :
    Mono φ ∧ Nonempty (cokernel φ ≅ cokernel ψ) := by
  have hφ : φ = inv c ≫ E ≫ E' ≫ ψ ≫ inv m := by
    rw [reassoc_of% h]
    simp
  refine ⟨?_, ⟨(cokernelCompIsIso φ m).symm ≪≫ (cokernelEpiComp c (φ ≫ m)).symm ≪≫
    cokernelIsoOfEq (by rw [h, Category.assoc]) ≪≫ cokernelEpiComp E (E' ≫ ψ) ≪≫
      cokernelEpiComp E' ψ⟩⟩
  rw [hφ]
  infer_instance

/-- **[Stacks Project, Tag 06D8] through an étale chart of the target.**

Let `iU : U ⟶ U'` be a first-order thickening, `q : Z ⟶ U` finite locally free of degree `d`
with `Z` affine, `j : Z ⟶ W` a first-order thickening and `g : W ⟶ U'` with `j ≫ g = q ≫ iU`.
Suppose that after a surjective étale `a : Z_V ⟶ Z`, with `Z_V = Z ×_W W_V` for an étale
`b : W_V ⟶ W`, the thickening `Z_V ⊆ W_V` is a universal first-order thickening of
`Z_V ⟶ X_V ⊆ V'` over `V'`, where `pV : V' ⟶ U'` is flat, `X_V = U ×_{U'} V'`, and
`f_V : Z_V ⟶ X_V` is a formally unramified local complete intersection morphism compatible with
`q` and `g`.

Then `j` factors as a first-order thickening `Z ⟶ Z'` followed by a closed immersion
`Z' ⟶ W`, with `Z' ⟶ U'` finite locally free of degree `d` and `Z = U ×_{U'} Z'`. -/
theorem exists_finiteLocallyFreeOfRank_deformation_of_etaleChart
    {U U' Z W ZV WV XV V' : Scheme.{u}} (iU : U ⟶ U') (hiU : IsFirstOrderThickening iU)
    (q : Z ⟶ U) (d : ℕ) (hq : Stacks.Morphisms.IsFiniteLocallyFreeOfRank q d) [IsAffine Z]
    (j : Z ⟶ W) (hj : IsFirstOrderThickening j) (g : W ⟶ U') (hjg : j ≫ g = q ≫ iU)
    (a : ZV ⟶ Z) [Etale a] [Surjective a] (b : WV ⟶ W) [Etale b] (jV : ZV ⟶ WV)
    (hsq : IsPullback jV a b j)
    (pV : V' ⟶ U') [Flat pV] (iV : XV ⟶ V') (qV : XV ⟶ U) (hX : IsPullback iV qV pV iU)
    (fV : ZV ⟶ XV) [FormallyUnramified fV] (hlci : IsLocalCompleteIntersectionMorphism fV)
    (hfV : fV ≫ qV = a ≫ q) (gV : WV ⟶ V')
    (hUniv : IsUniversalFirstOrderThickening (fV ≫ iV) jV gV) (hgV : gV ≫ pV = b ≫ g) :
    ∃ (Z' : Scheme.{u}) (iZ : Z ⟶ Z') (k : Z' ⟶ W), IsFirstOrderThickening iZ ∧
      IsClosedImmersion k ∧ iZ ≫ k = j ∧
      Stacks.Morphisms.IsFiniteLocallyFreeOfRank (k ≫ g) d ∧
      IsPullback iZ q (k ≫ g) iU := by
  have := hiU.1
  have := hj.1
  have hiV : IsFirstOrderThickening iV := isFirstOrderThickening_of_isPullback hX hiU
  have := hiV.1
  have := hUniv.isFirstOrderThickening.1
  let tZ : UniversalFirstOrderThickening (fV ≫ iV) := ⟨WV, jV, gV, hUniv⟩
  let tY := selfUniversalFirstOrderThickening iV hiV
  -- The conormal map `φ : q^*𝒞_{U/U'} ⟶ 𝒞_{Z/W}` and the three maps it is compared with.
  set φ := immersionConormalSheafMap j iU q g (toShHom_square hjg)
  have hcommV : jV ≫ gV = fV ≫ iV := hUniv.inclusion_toBase
  have hψeq : transitivityConormalLeftMap fV iV tZ tY =
      immersionConormalSheafMap jV iV fV gV (toShHom_square hcommV) :=
    (immersionConormalSheafMap_congr jV iV (rfl : fV = fV)
      (transitivityMap_self fV iV hiV tZ).symm (toShHom_square hcommV)
      (toShHom_square (inclusion_comp_transitivityMap fV iV tZ tY).symm)).trans rfl
  have hSE := transitivityConormalShortComplex_shortExact fV iV tZ tY hlci
  have hcokT : SheafOfModules.IsFiniteLocallyFree.{u, u, u}
      (cokernel (transitivityConormalLeftMap fV iV tZ tY)) :=
    @SheafOfModules.IsFiniteLocallyFree.of_iso _ _ _
      (hSE.gIsCokernel.coconePointUniqueUpToIso (colimit.isColimit _))
      (isFiniteLocallyFree_transitivityConormalShortComplex_X₃_self fV hlci iV hiV tZ)
  -- The two factorizations of the conormal map of the composite square.
  have hχ := isIso_immersionConormalSheafMap_of_flat iV iU qV pV hX
  have hψ₁ := isIso_immersionConormalSheafMap_of_flat jV j a b hsq
  have hL := immersionConormalSheafMap_comp jV j iU a b hsq.w q g hjg
  rw [immersionConormalSheafMap_congr jV iU hfV hgV
    (toShHom_square (square_comp hcommV hX.w)) (toShHom_square (square_comp hsq.w hjg)),
    immersionConormalSheafMap_comp jV iV iU fV gV hcommV qV pV hX.w] at hL
  simp only [← Category.assoc] at hL
  rw [← hψeq] at hL
  obtain ⟨hmono, ⟨e⟩⟩ := mono_and_nonempty_cokernelIso_of_comp_eq _ _ _ _ _ _ hL
    (by infer_instance) (IsIso.comp_isIso'
        (Iso.isIso_hom ((modulePullbackComp _ _).app _)) (Functor.map_isIso _ _))
    (Iso.isIso_hom ((modulePullbackComp _ _).app _)) hψ₁
    (mono_transitivityConormalLeftMap fV iV tZ tY hlci)
  have hqc₁ :
      ((modulePullback q.toLRSHom.toShHom).obj (immersionConormalSheaf iU)).IsQuasicoherent :=
    AlgebraicGeometry.SheafOfModules.modulePullback_isQuasicoherent _ _
  have hqc₂ : (immersionConormalSheaf j).IsQuasicoherent :=
    Stacks.Conormal.conormalSheaf_isQuasicoherent j
  have hφcok : SheafOfModules.IsFiniteLocallyFree.{u, u, u} (cokernel φ) :=
    @Scheme.Modules.isFiniteLocallyFree_cokernel_of_pullback _ _ a _ _ _ _ hqc₁ hqc₂ φ
      (@SheafOfModules.IsFiniteLocallyFree.of_iso _ _ _ e.symm hcokT)
  -- The sequence `0 → q^*𝒞_{U/U'} → 𝒞_{Z/W} → coker φ → 0` splits on the affine `Z`.
  obtain ⟨σ⟩ :=
    @Scheme.Modules.nonempty_splitting_of_mono_of_isFiniteLocallyFree_cokernel _ _ _ _ hqc₁ hqc₂
      φ (Scheme.Modules.mono_of_mono_pullback_of_surjective a φ hmono) hφcok
  obtain ⟨Z', iZ, k, hiZ, hk, hik, hfl, hpb⟩ :=
    exists_isFirstOrderThickening_isFiniteLocallyFreeOfRank_of_splitting j hj.2 iU hiU.2 iU
      hiU.2 q g hjg (𝟙 U) (𝟙 U') (IsPullback.of_vert_isIso ⟨by simp⟩) d (by rwa [Category.comp_id])
      (@Stacks.AlgebraicGeometry.QuasicoherentColimits.isQuasicoherent_cokernel _ _ _ φ hqc₁ hqc₂)
      (cokernel.π φ) (cokernel.condition φ) σ
  exact ⟨Z', iZ, k, hiZ, hk, hik, by simpa using hfl, by simpa using hpb⟩

end Stacks.Thickenings
