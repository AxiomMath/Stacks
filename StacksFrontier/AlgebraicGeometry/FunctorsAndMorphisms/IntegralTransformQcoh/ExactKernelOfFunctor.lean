module

public import StacksFrontier.AlgebraicGeometry.FunctorsAndMorphisms.IntegralTransformQcoh.KernelFlatnessGlued
public import StacksFrontier.AlgebraicGeometry.AffineExtend.Induction
public import Mathlib.CategoryTheory.Limits.Shapes.FiniteMultiequalizer
public import StacksFrontier.AlgebraicGeometry.TopDegreeBaseChange.DerivedFunctorAdditive
public import StacksFrontier.AlgebraicGeometry.DerivedCoherent.SerreClass

/-!
# The kernel of an exact functor on quasi-coherent modules

Let `R` be a ring, let `X` and `Y` be schemes over `R` with `X` quasi-compact and with affine
diagonal, and let `F : QCoh(𝒪_X) ⥤ QCoh(𝒪_Y)` be an `R`-linear exact functor commuting with
arbitrary direct sums.  Tag 0GPA attaches to `F` a quasi-coherent kernel `K` on `X ×_R Y` and a
natural transformation `t : F ⟶ F_K` which is an isomorphism on direct images from affine
schemes.  This file proves, for such `F`, the following part of the direction (1) ⇒ (2) of
Tag 0FZH.

* `t` is an isomorphism.
* The kernel satisfies condition (2)(b) of Tag 0FZH: for a kernel `K` flat over `X` whose
  integral transform is exact, the integrand `pr_1^*G ⊗ K` has no positive higher direct images
  along `pr_2`.

## Main results

* `AlgebraicGeometry.isLimitCechMultifork`: the Čech multifork of an open cover is a limit.
* `AlgebraicGeometry.isIso_kernelTransform_of_preservesFiniteLimits`: the transformation
  `t : F ⟶ F_K` of Tag 0GPA is an isomorphism when `F` is left exact.
* `AlgebraicGeometry.isZero_rightDerived_integralTransformIntegrand_of_exactFunctor`: for a
  kernel `K` flat over `X` with exact integral transform, the integrand `pr_1^*G ⊗ K` has no
  positive higher direct images along the second projection.

## References

* [Stacks Project, Tag 0FZH](https://stacks.math.columbia.edu/tag/0FZH)
* [Stacks Project, Tag 0GPA](https://stacks.math.columbia.edu/tag/0GPA)
* [Stacks Project, Tag 0FZG](https://stacks.math.columbia.edu/tag/0FZG)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits
open AlgebraicGeometry

universe u

namespace AlgebraicGeometry

attribute [local instance] Abelian.hasFiniteBiproducts

section Cech

variable (R : Type u) [CommRing R] (X : Over (Spec (.of R)))
  [CompactSpace X.left] [QuasiSeparatedSpace X.left]
  {ι : Type u} (U : ι → X.left.Opens) [∀ i, QuasiCompact (U i).ι] [∀ i, QuasiSeparated (U i).ι]
  [∀ i j, QuasiCompact (U i ⊓ U j).ι] [∀ i j, QuasiSeparated (U i ⊓ U j).ι]

/-- **The Čech multifork of an open cover is a limit** in the quasi-coherent modules. -/
def isLimitCechMultifork (hU : TopologicalSpace.IsOpenCover U)
    (G : Scheme.QuasicoherentModules X.left) : IsLimit (cechMultifork U G) :=
  isLimitOfReflects (SheafOfModules.isQuasicoherent X.left.ringCatSheaf).ι
    (isLimitOfIsLimitRestrict _ U hU fun k =>
      isLimitMapConeRestrictCechMultifork R X U k (𝟭 _) G)

omit [CompactSpace X.left] [QuasiSeparatedSpace X.left] in
/-- **The Čech map `G ⟶ ⊕ (U_i)_*(G|_{U_i})` of an open cover is a monomorphism**, for the
direct sum over any finite family of indices exhausting the cover. -/
theorem mono_biproduct_lift_cechUnit {κ : Type} [Finite κ] (σ : κ → ι)
    (hσ : Function.Surjective σ) (hU : TopologicalSpace.IsOpenCover U)
    (G : Scheme.QuasicoherentModules X.left) :
    Mono (biproduct.lift fun k => (cechUnit (U (σ k))).app G) := by
  refine ⟨fun a b hab => (isLimitCechMultifork R X U hU G).hom_ext ?_⟩
  have hl : ∀ i, a ≫ (cechUnit (U i)).app G = b ≫ (cechUnit (U i)).app G := fun i => by
    obtain ⟨k, rfl⟩ := hσ i
    simpa using congrArg (· ≫ biproduct.π (fun k => (cechObj (U (σ k))).obj G) k) hab
  rintro (i | p)
  · exact hl i
  · exact comp_eq_comp_of_comp_eq_comp (hl p.1) ((cechMultifork U G).w (multicospanFst p))

end Cech

/-! ### The comparison transformation is an isomorphism -/

section Transform

variable (R : Type u) [CommRing R] (X Y : Over (Spec (.of R)))
  (F : Scheme.QuasicoherentModules X.left ⥤ Scheme.QuasicoherentModules Y.left)
  [CompactSpace X.left] [IsAffineHom (pullback.diagonal (terminal.from X.left))]

attribute [local instance] isAffineHom_ι_affineOpens isAffineHom_ι_affineOpens_inf

omit [IsAffineHom (pullback.diagonal (terminal.from X.left))] in
/-- A quasi-compact scheme has a finite cover by affine opens, indexed by a finite set of
affine opens. -/
theorem isOpenCover_finset_affineOpens :
    ∃ s : Finset X.left.affineOpens,
      TopologicalSpace.IsOpenCover fun i : s => ((i : X.left.affineOpens) : X.left.Opens) := by
  obtain ⟨s, hs⟩ :=
    Stacks.AlgebraicGeometry.Tag01PFAffineExtend.exists_finset_affineOpens_iSup_eq_top (X := X.left)
  exact ⟨s, by rw [TopologicalSpace.IsOpenCover, ← hs, iSup_subtype']⟩

/-- **The transformation `t : F ⟶ F_K` of Tag 0GPA is an isomorphism as soon as `F` carries the
Čech multiforks of one finite affine open cover of `X` to limits.** -/
theorem isIso_kernelTransform_of_isLimit
    (hF : affineOpenRightExactLinearCoproductFunctor R X Y F) (s : Finset X.left.affineOpens)
    (hs : TopologicalSpace.IsOpenCover fun i : s => ((i : X.left.affineOpens) : X.left.Opens))
    (hlim : ∀ G : Scheme.QuasicoherentModules X.left, IsLimit (F.mapCone
      (cechMultifork (fun i : s => ((i : X.left.affineOpens) : X.left.Opens)) G))) :
    IsIso (kernelTransform R X Y F hF) := by
  let V : s → X.left.Opens := fun i => ((i : X.left.affineOpens) : X.left.Opens)
  refine (NatTrans.isIso_iff_isIso_app _).mpr fun G => isIso_app_pt_of_isLimit
    (kernelTransform R X Y F hF) (cechMultifork V G) (hlim G)
    (isLimitIntegralTransformCechMultifork R X Y (openKernelSystem R X Y F hF).glued V hs G) ?_
  rintro (i | p)
  · exact isIso_kernelTransform_app_pushforward R X Y F hF i.1 _
  · exact isIso_kernelTransform_app_pushforward R X Y F hF
      ⟨V p.1 ⊓ V p.2, IsAffineOpen.inf p.1.1.2 p.2.1.2⟩ _

/-- **The transformation `t : F ⟶ F_K` of Tag 0GPA is an isomorphism when `F` is left exact.** -/
theorem isIso_kernelTransform_of_preservesFiniteLimits
    (hF : affineOpenRightExactLinearCoproductFunctor R X Y F) [PreservesFiniteLimits F] :
    IsIso (kernelTransform R X Y F hF) := by
  classical
  obtain ⟨s, hs⟩ := isOpenCover_finset_affineOpens R X
  let V : s → X.left.Opens := fun i => ((i : X.left.affineOpens) : X.left.Opens)
  have : Fintype (MulticospanShape.prod s).L := inferInstanceAs (Fintype s)
  have : Fintype (MulticospanShape.prod s).R := inferInstanceAs (Fintype (s × s))
  have : DecidableEq (MulticospanShape.prod s).L := inferInstanceAs (DecidableEq s)
  have : DecidableEq (MulticospanShape.prod s).R := inferInstanceAs (DecidableEq (s × s))
  exact isIso_kernelTransform_of_isLimit R X Y F hF s hs fun G =>
    isLimitOfPreserves F (isLimitCechMultifork R X V hs G)

end Transform

/-! ### Vanishing of the higher direct images of the integrand -/

section Vanishing

variable (R : Type u) [CommRing R] (X Y : Over (Spec (.of R)))

/-- **The relative Leray spectral sequence collapses at an affine first leg**:  for `i` affine
and `M` quasi-coherent, `R ⁿ g_*(i_* M)` vanishes as soon as `R ⁿ (i ≫ g)_* M` does. -/
theorem isZero_rightDerived_pushforward_pushforward_of_comp_eq {A B C : Scheme.{u}} (i : A ⟶ B)
    [IsAffineHom i] (g : B ⟶ C) (p : A ⟶ C) (hp : i ≫ g = p) (M : A.Modules)
    [M.IsQuasicoherent] (n : ℕ)
    (h : IsZero (((Scheme.Modules.pushforward p).rightDerived n).obj M)) :
    IsZero (((Scheme.Modules.pushforward g).rightDerived n).obj
      ((Scheme.Modules.pushforward i).obj M)) := by
  let : HasDerivedCategory.{u + 1} B.Modules := HasDerivedCategory.standard _
  let : HasDerivedCategory.{u + 1} C.Modules := HasDerivedCategory.standard _
  subst hp
  exact IsZero.of_iso h (Stacks.AcyclicCollapse.objIso (Scheme.Modules.pushforward i)
    (Scheme.Modules.pushforward g)
    (fun I hI =>
      Stacks.AlgebraicGeometry.RelativeCechAcyclic.rightAcyclic_pushforward_obj_injective i g I hI)
    (fun m hm => Stacks.AffineHigherDirectImage.isZero_rightDerived_pushforward i M m hm) n).symm

variable [CompactSpace X.left] [IsAffineHom (pullback.diagonal (terminal.from X.left))]

attribute [local instance] isAffineHom_ι_affineOpens isAffineHom_ι_affineOpens_inf
  isAffineHom_left_of_isAffine_left

omit [CompactSpace X.left] in
/-- **The integrand of a direct image from an affine open has no higher direct images.**  For an
affine open `U` of `X` and a quasi-coherent `N` on `U`, the integrand of a kernel `K` at
`(U ↪ X)_* N` has no positive higher direct images along the second projection. -/
theorem isZero_rightDerived_integralTransformIntegrand_pushforward
    (K : Scheme.QuasicoherentModules (pullback X.hom Y.hom)) (U : X.left.affineOpens)
    (N : Scheme.QuasicoherentModules (U : X.left.Opens).toScheme) (q : ℕ) (hq : 0 < q) :
    IsZero (((Scheme.Modules.pushforward (pullback.snd X.hom Y.hom)).rightDerived q).obj
      ((integralTransformIntegrand R X Y K).obj
        ((quasicoherentPushforward (U : X.left.Opens).ι).obj N))) := by
  have : IsAffine (openSubOver R X (U : X.left.Opens)).left := U.2
  have : ((integralTransformIntegrand R (openSubOver R X (U : X.left.Opens)) Y
      (sourceChangeKernel R X (openSubOver R X (U : X.left.Opens)) Y
        (openSubOverHom R X (U : X.left.Opens)) K)).obj N).IsQuasicoherent :=
    isQuasicoherent_tensorLeftFunctor_pullback R (openSubOver R X (U : X.left.Opens)) Y
      (sourceChangeKernel R X (openSubOver R X (U : X.left.Opens)) Y
        (openSubOverHom R X (U : X.left.Opens)) K) N
  have : IsAffineHom (pullback.snd (openSubOver R X (U : X.left.Opens)).hom Y.hom) :=
    MorphismProperty.IsStableUnderBaseChange.of_isPullback (IsPullback.of_hasPullback _ _)
      inferInstance
  refine IsZero.of_iso ?_ (((Scheme.Modules.pushforward (pullback.snd X.hom Y.hom)).rightDerived
    q).mapIso (integralTransformIntegrandSourceChangeObjIso R X
      (openSubOver R X (U : X.left.Opens)) Y (openSubOverHom R X (U : X.left.Opens)) K N))
  exact isZero_rightDerived_pushforward_pushforward_of_comp_eq _ _ _
    (sourceChangeMap_comp_snd R X _ Y _) _ q
    (Stacks.AffineHigherDirectImage.isZero_rightDerived_pushforward _ _ q hq)

/-- **Condition (2)(b) of Tag 0FZH for a kernel flat over `X` with exact integral transform.**
For a quasi-coherent kernel `K` flat over `X` whose integral transform `F_K` is exact, the
integrand `pr_1^*G ⊗ K` has no positive higher direct images along the second projection, for
every quasi-coherent `G` on `X`. -/
theorem isZero_rightDerived_integralTransformIntegrand_of_exactFunctor
    (K : Scheme.QuasicoherentModules (pullback X.hom Y.hom))
    (hK : IsFlatOver (pullback.fst X.hom Y.hom).toLRSHom.toShHom K.obj)
    (hE : exactFunctor _ _ (quasicoherentIntegralTransform R X Y K))
    (G : Scheme.QuasicoherentModules X.left) (q : ℕ) (hq : 0 < q) :
    IsZero (((Scheme.Modules.pushforward (pullback.snd X.hom Y.hom)).rightDerived q).obj
      ((integralTransformIntegrand R X Y K).obj G)) := by
  classical
  obtain ⟨s, hs⟩ := isOpenCover_finset_affineOpens R X
  let V : s → X.left.Opens := fun i => ((i : X.left.affineOpens) : X.left.Opens)
  let e := Fintype.equivFin s
  have hIex := exactFunctor_integralTransformIntegrand R X Y K hK
  have hIlim : PreservesFiniteLimits (integralTransformIntegrand R X Y K) :=
    ((exactFunctor_iff _).mp hIex).1
  have hIcolim : PreservesFiniteColimits (integralTransformIntegrand R X Y K) :=
    ((exactFunctor_iff _).mp hIex).2
  have : (integralTransformIntegrand R X Y K).PreservesZeroMorphisms :=
    preservesZeroMorphisms_integralTransformIntegrand R X Y K hK
  have : (integralTransformIntegrand R X Y K).Additive :=
    Functor.additive_of_preserves_binary_products (integralTransformIntegrand R X Y K)
  have hS : ∀ G : Scheme.QuasicoherentModules X.left,
      (ShortComplex.mk (biproduct.lift fun i => (cechUnit (V (e.symm i))).app G)
        (cokernel.π (biproduct.lift fun i => (cechUnit (V (e.symm i))).app G))
        (cokernel.condition _)).ShortExact := fun G =>
    have := mono_biproduct_lift_cechUnit R X V e.symm e.symm.surjective hs G
    { exact := ShortComplex.exact_of_g_is_cokernel _ (cokernelIsCokernel _) }
  have hmid : ∀ (G : Scheme.QuasicoherentModules X.left) (n : ℕ), 0 < n →
      IsZero (((Scheme.Modules.pushforward (pullback.snd X.hom Y.hom)).rightDerived n).obj
        ((integralTransformIntegrand R X Y K).obj
          (⨁ fun i => (cechObj (V (e.symm i))).obj G))) := by
    intro G n hn
    have hΦ : (integralTransformIntegrand R X Y K ⋙
        (Scheme.Modules.pushforward (pullback.snd X.hom Y.hom)).rightDerived n).Additive :=
      inferInstance
    refine IsZero.of_iso ?_ ((integralTransformIntegrand R X Y K ⋙
      (Scheme.Modules.pushforward (pullback.snd X.hom Y.hom)).rightDerived n).mapBiproduct
        fun i => (cechObj (V (e.symm i))).obj G)
    rw [IsZero.iff_id_eq_zero]
    exact biproduct.hom_ext _ _ fun j => IsZero.eq_of_tgt
      (isZero_rightDerived_integralTransformIntegrand_pushforward R X Y K (e.symm j).1 _ n hn) _ _
  have hone : ∀ G : Scheme.QuasicoherentModules X.left,
      IsZero (((Scheme.Modules.pushforward (pullback.snd X.hom Y.hom)).rightDerived 1).obj
        ((integralTransformIntegrand R X Y K).obj G)) := by
    intro G
    have hSI := (hS G).map_of_exact (integralTransformIntegrand R X Y K)
    refine Stacks.Cohomology.RightDerivedDelta.isZero_rightDerived_succ_X₁_of_epi hSI
      (Scheme.Modules.pushforward (pullback.snd X.hom Y.hom)) 0 ?_ (hmid G 1 Nat.one_pos)
    have hepi : Epi ((Scheme.Modules.pushforward (pullback.snd X.hom Y.hom)).map
        ((integralTransformIntegrand R X Y K).map
          (cokernel.π (biproduct.lift fun i => (cechUnit (V (e.symm i))).app G)))) := by
      have hc : PreservesFiniteColimits (quasicoherentIntegralTransformData R X Y K).functor :=
        ((exactFunctor_iff _).mp hE).2
      have h2 : PreservesFiniteColimits ((quasicoherentIntegralTransformData R X Y K).functor ⋙
          ObjectProperty.ι (SheafOfModules.isQuasicoherent Y.left.ringCatSheaf)) :=
        @comp_preservesFiniteColimits _ _ _ _ _ _ _ _ hc inferInstance
      have h3 : PreservesFiniteColimits (integralTransformFormula R X Y K.obj) :=
        @preservesFiniteColimits_of_natIso _ _ _ _ _ _
          (quasicoherentIntegralTransformData R X Y K).comparison h2
      exact Functor.map_epi (integralTransformFormula R X Y K.obj)
        (cokernel.π (biproduct.lift fun i => (cechUnit (V (e.symm i))).app G))
    have hnat := (Scheme.Modules.pushforward
      (pullback.snd X.hom Y.hom)).rightDerivedZeroIsoSelf.inv.naturality
        ((integralTransformIntegrand R X Y K).map
          (cokernel.π (biproduct.lift fun i => (cechUnit (V (e.symm i))).app G)))
    change Epi (((Scheme.Modules.pushforward (pullback.snd X.hom Y.hom)).rightDerived 0).map
      ((integralTransformIntegrand R X Y K).map
        (cokernel.π (biproduct.lift fun i => (cechUnit (V (e.symm i))).app G))))
    exact @epi_of_epi_fac _ _ _ _ _ _ _ _ (epi_comp' hepi (IsIso.epi_of_iso _)) hnat.symm
  have hall : ∀ n : ℕ, ∀ G : Scheme.QuasicoherentModules X.left,
      IsZero (((Scheme.Modules.pushforward (pullback.snd X.hom Y.hom)).rightDerived (n + 1)).obj
        ((integralTransformIntegrand R X Y K).obj G)) := by
    intro n
    induction n with
    | zero => exact hone
    | succ n ih =>
      intro G
      exact Stacks.Cohomology.RightDerivedDelta.isZero_rightDerived_succ_X₁
        ((hS G).map_of_exact (integralTransformIntegrand R X Y K))
        (Scheme.Modules.pushforward (pullback.snd X.hom Y.hom)) (n + 1)
        (ih (cokernel (biproduct.lift fun i => (cechUnit (V (e.symm i))).app G)))
        (hmid G (n + 2) (Nat.succ_pos _))
  obtain ⟨n, rfl⟩ := Nat.exists_eq_add_of_lt hq
  simpa using hall n G

end Vanishing

end AlgebraicGeometry

end
