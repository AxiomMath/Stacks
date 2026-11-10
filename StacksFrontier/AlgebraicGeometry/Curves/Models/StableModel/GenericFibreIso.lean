module

public import StacksFrontier.AlgebraicGeometry.Curves.Models.StableModel.FibreMaps
public import StacksFrontier.AlgebraicGeometry.Curves.StableContraction.StableModel
public import StacksFrontier.AlgebraicGeometry.Curves.Models.StableModel.QuasiFinitePoint
public import StacksFrontier.AlgebraicGeometry.Curves.Models.RegularModelSurface
public import StacksFrontier.AlgebraicGeometry.Curves.Models.SpecialFiberComponentProperCurve
public import StacksFrontier.AlgebraicGeometry.Variety.Curve.ContractedDegree
public import StacksFrontier.AlgebraicGeometry.MoreMorphisms.SteinFactorization.FlatBaseChange
public import StacksFrontier.AlgebraicGeometry.Perfect.ProperFlatFamily.UniversalDirectImage
public import StacksFrontier.AlgebraicGeometry.BirationalCurveFinite.Basic
public import StacksFrontier.AlgebraicGeometry.Models.Basic

/-!
# The contraction is an isomorphism on generic fibres

In the situation of [Stacks, Tag 0C61] let `c : X ⟶ Y` be a proper morphism over `Spec R` with
`𝒪_Y = c_*𝒪_X`, and suppose that on special fibres `c_k = h ∘ c₀` with `c₀ : X_k ⟶ Y₀` a stable
contraction ([Stacks, Tag 0E7Q]) and `h` finite. Then `c` is an isomorphism on generic fibres.

A generic point `ζ` of a component of `X_k` lying over a generic point of `Y₀` is isolated in its
fibre under `c₀` (proper maps send closed points to closed points, so that fibre consists of
generic points of components), hence `c_k`, and so `c`, is quasi-finite at `ζ`. The quasi-finite
locus of `c` is open, so it contains the generic point of the integral scheme `X`, which is the
generic point of `X_K = C`. So `c_K : C ⟶ Y_K` is not constant, hence finite (`C` is an irreducible
proper curve), and a finite morphism with `𝒪 = c_*𝒪` is an isomorphism.

## Main results

* `Stacks.Models.RegularProperModelSituation.isIso_genericFiberMap`.
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry

universe u

namespace Stacks.Models.RegularProperModelSituation

variable (S : RegularProperModelSituation.{u})

/-- **The contraction is an isomorphism on generic fibres.** -/
theorem isIso_genericFiberMap
    {Y₀ : Scheme.{u}} {g₀ : Y₀ ⟶ Spec (.of S.k)} {c₀ : S.specialFiber ⟶ Y₀}
    (hc₀ : Stacks.Curves.StableModel.IsStableContraction S.specialFiberToSpec g₀ c₀)
    {Y : Scheme.{u}} (pY : Y ⟶ Spec (.of S.R)) (c : S.X ⟶ Y) (hc : c ≫ pY = S.X_to_R)
    [IsProper c] (hO : IsIso (SheafOfModules.unitToPushforwardObjUnit c.toRingCatSheafHom))
    (h : Y₀ ⟶ pullback pY (Spec.map (CommRingCat.ofHom (algebraMap S.R S.k)))) [IsFinite h]
    (hh : c₀ ≫ h = S.specialFiberMap pY c hc) :
    IsIso (S.genericFiberMap pY c hc) := by
  have hιK : IsOpenImmersion (Spec.map (CommRingCat.ofHom (algebraMap S.R S.K))) :=
    genericFiberSpec_isOpenImmersion
  have hιk : IsClosedImmersion (Spec.map (CommRingCat.ofHom (algebraMap S.R S.k))) :=
    IsClosedImmersion.spec_of_surjective _ S.surjective_algebraMap_residueField
  have : IsProper g₀ := hc₀.isProper
  have : IsProper (c₀ ≫ g₀) := by rw [hc₀.comp_eq]; infer_instance
  have : IsProper c₀ := IsProper.of_comp c₀ g₀
  -- the generic fibre square is cartesian
  have hsq : IsPullback (pullback.fst S.X_to_R (Spec.map (CommRingCat.ofHom (algebraMap S.R S.K))))
      (S.genericFiberMap pY c hc) c
      (pullback.fst pY (Spec.map (CommRingCat.ofHom (algebraMap S.R S.K)))) := by
    refine IsPullback.of_bot ?_ (S.genericFiberMap_fst pY c hc).symm
      (IsPullback.of_hasPullback pY _)
    rw [S.genericFiberMap_snd, hc]
    exact IsPullback.of_hasPullback _ _
  -- a point of `X_k` at which `c₀` is quasi-finite
  obtain ⟨y₀, hy₀⟩ : ∃ y : Y₀, ¬ IsClosed ({y} : Set Y₀) := by
    by_contra! H
    have : T1Space Y₀ := ⟨H⟩
    have := Stacks.Topology.Dimension.topologicalKrullDim_le_zero_of_quasiSober_of_t1Space
      (S := Y₀)
    rw [hc₀.topologicalKrullDim_eq] at this
    exact absurd this (by decide)
  have hsurj₀ : Function.Surjective c₀ := (c₀.surjective_of_isIso_app
    (Stacks.Curves.DualizingPullback.isIso_app_of_isIso_unitToPushforwardObjUnit c₀
      hc₀.isIso_unitToPushforwardObjUnit)).surj
  obtain ⟨ζ, rfl⟩ := hsurj₀ y₀
  have hq₀ : c₀.QuasiFiniteAt ζ := by
    have : IsNoetherian S.specialFiber := S.isNoetherian_specialFiber
    exact c₀.quasiFiniteAt_of_finite_preimage_singleton
      (finite_preimage_singleton_of_not_isClosed_singleton
        (S.topologicalKrullDim_specialFiber ⟨ζ⟩).le c₀.isClosedMap hy₀)
  have hqk : (S.specialFiberMap pY c hc).QuasiFiniteAt ζ := by
    rw [← hh]
    exact Scheme.Hom.quasiFiniteAt_comp_iff.mpr hq₀
  -- hence `c` is quasi-finite at the image of `ζ`
  have hqX : c.QuasiFiniteAt (S.specialFiberι ζ) := by
    have : LocallyOfFiniteType (S.specialFiberMap pY c hc) := by rw [← hh]; infer_instance
    obtain ⟨U', hU', hζU', hinj⟩ := Scheme.Hom.quasiFiniteAt_iff_exists_isOpen.mp hqk
    obtain ⟨U, hU, rfl⟩ := S.specialFiberι.isClosedEmbedding.isInducing.isOpen_iff.mp hU'
    refine Scheme.Hom.quasiFiniteAt_iff_exists_isOpen.mpr ⟨U, hU, hζU', fun x hxU hcx ↦ ?_⟩
    have hxr : x ∈ Set.range S.specialFiberι := by
      rw [Scheme.Pullback.range_fst]
      have h1 : S.X_to_R x = S.X_to_R (S.specialFiberι ζ) := by
        rw [← hc, Scheme.Hom.comp_apply, Scheme.Hom.comp_apply, hcx]
      change S.X_to_R x ∈ Set.range (Spec.map (CommRingCat.ofHom (algebraMap S.R S.k)))
      rw [h1, ← Scheme.Hom.comp_apply, pullback.condition, Scheme.Hom.comp_apply]
      exact ⟨_, rfl⟩
    obtain ⟨z, rfl⟩ := hxr
    have hz : z = ζ := hinj z hxU (by
      apply Scheme.Hom.isClosedEmbedding
        (pullback.fst pY (Spec.map (CommRingCat.ofHom (algebraMap S.R S.k)))) |>.injective
      rw [← Scheme.Hom.comp_apply, ← Scheme.Hom.comp_apply, S.specialFiberMap_fst,
        Scheme.Hom.comp_apply, Scheme.Hom.comp_apply, hcx])
    rw [hz]
  -- the quasi-finite locus of `c` meets the generic fibre
  have : IsIntegral S.X := S.toRegularModelSituation.isIntegral_X
  have : IsNoetherian S.X := S.isIntegralRegularSurface.isNoetherian
  have hneK : Nonempty S.genericFiber :=
    ⟨S.genericFiberIso.hom (Nonempty.some inferInstance)⟩
  have hfst := Scheme.Hom.isOpenEmbedding
    (pullback.fst S.X_to_R (Spec.map (CommRingCat.ofHom (algebraMap S.R S.K))))
  obtain ⟨_, -, hqU, ⟨p, rfl⟩⟩ := PreirreducibleSpace.isPreirreducible_univ (X := S.X) _ _
    c.isOpen_quasiFiniteAt hfst.isOpen_range
    ⟨_, trivial, hqX⟩ ⟨_, trivial, ⟨Nonempty.some hneK, rfl⟩⟩
  have hqK : (S.genericFiberMap pY c hc).QuasiFiniteAt p :=
    (RingHom.QuasiFinite.respectsIso.arrow_mk_iso_iff (Scheme.stalkMapIsoOfIsPullback hsq p)).mp
      hqU
  -- the generic fibre is an irreducible Noetherian curve
  have : IsProper (S.genericFiberMap pY c hc) :=
    MorphismProperty.of_isPullback (P := @IsProper) hsq inferInstance
  have : IsIntegral S.genericFiber :=
    isIntegral_of_isOpenImmersion (pullback.fst _ _)
  have : TopologicalSpace.NoetherianSpace S.genericFiber :=
    hfst.isInducing.noetherianSpace
  have hdimK : topologicalKrullDim S.genericFiber = 1 := by
    rw [← IsHomeomorph.topologicalKrullDim_eq _ S.genericFiberIso.hom.homeomorph.isHomeomorph]
    exact IsCurve.topologicalKrullDim_eq_one (f := S.C_to_K)
  -- so `c_K` is not constant, hence finite
  have hnc : ¬ (Set.range (S.genericFiberMap pY c hc).base).Subsingleton := by
    intro hsub
    have hcl := Scheme.Hom.isClopen_singleton_of_quasiFiniteAt_of_forall_eq hqK
      (fun x' ↦ hsub ⟨x', rfl⟩ ⟨p, rfl⟩)
    have huniv := hcl.eq_univ ⟨p, rfl⟩
    have : Subsingleton S.genericFiber :=
      Set.subsingleton_univ_iff.mp (huniv ▸ Set.subsingleton_singleton)
    have := topologicalKrullDim_zero_of_discreteTopology
      S.genericFiber
    rw [hdimK] at this
    exact absurd this (by decide)
  have := (S.genericFiberMap pY c hc).isFinite_of_not_subsingleton_range hdimK.le hnc
  -- `𝒪 = c_*𝒪` survives the flat base change to the generic fibre
  have hcc : IsIso c.c :=
    (Stacks.AlgebraicGeometry.ProperFlatFamilyUnit.isIso_c_iff_isIso_unitToPushforwardObjUnit
      c).mpr hO
  have hcK : IsIso (S.genericFiberMap pY c hc).c :=
    Stacks.AlgebraicGeometry.isIso_c_of_isPullback_of_flat hsq hcc
  have happ := (Stacks.AlgebraicGeometry.ProperFlatFamilyUnit.isIso_c_iff_isIso_app _).mp hcK
  -- a finite morphism with `𝒪 = c_*𝒪` is an isomorphism
  exact (MorphismProperty.isomorphisms.iff _).mp
    (IsZariskiLocalAtTarget.of_iSup_eq_top (P := MorphismProperty.isomorphisms Scheme)
      (f := S.genericFiberMap pY c hc)
      (fun W : (pullback pY (Spec.map (CommRingCat.ofHom (algebraMap S.R S.K)))).affineOpens ↦
        (W : (pullback pY (Spec.map (CommRingCat.ofHom (algebraMap S.R S.K)))).Opens))
      (iSup_affineOpens_eq_top _) fun W ↦
        (MorphismProperty.isomorphisms.iff _).mpr
          ((isIso_morphismRestrict_iff_isIso_app _ W.2).mpr (happ W)))

end Stacks.Models.RegularProperModelSituation

end
