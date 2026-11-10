module

public import StacksFrontier.AlgebraicGeometry.Spaces.ProperGlobalSections.ArtinRees
public import StacksFrontier.AlgebraicGeometry.Spaces.IdealPushforwardAffineComparison
public import StacksFrontier.AlgebraicGeometry.Spaces.ModulePushforwardChartComparison

/-!
# Direct images and the ideal `I · 𝒪`

For a representable morphism `f : Y ⟶ X` of algebraic spaces over `Spec A` and an ideal
`I ⊆ A`, the pullback of `I · 𝒪_X` lies in `I · 𝒪_Y`. Consequently the direct image of a module
annihilated by a power of `I · 𝒪_Y` is annihilated by the same power of `I · 𝒪_X`, and the
Artin-Rees property of global sections passes to direct images.

## Main definitions

* `AlgebraicGeometry.Space.baseIdealComap`: the sections of `𝒪_X` whose pullback lies in
  `I · 𝒪_Y`.

## Main results

* `AlgebraicGeometry.Space.isPowAnnihilated_modulePushforward`: the direct image of a module
  annihilated by `(I · 𝒪_Y)^k` is annihilated by `(I · 𝒪_X)^k`.
* `AlgebraicGeometry.Space.HasSectionsArtinRees.modulePushforward`: the Artin-Rees property of
  global sections passes to direct images along representable morphisms.
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits Opposite

universe u

namespace AlgebraicGeometry.Space

open Stacks.SheafOfModules.Tensor (ringSheaf)
open Stacks.Cohomology.SiteModules

variable (A : Type u) [CommRing A] {B : BigFppfSite.{u}} {hA : B.Contains (Spec (.of A))}

section Pullback

variable {X Y : AlgebraicSpaces B (Spec (.of A)) hA} (f : Y ⟶ X)
  (hf : yoneda.relativelyRepresentable f.hom)

/-- The structure map of a representable morphism carries the constants of `A` to the
constants. -/
theorem chartIdealPullbackHom_chartBaseRingHom (Q : SmallEtale B (Spec (.of A)) hA X.1) (a : A) :
    chartIdealPullbackHom B (Spec (.of A)) hA f hf Q (chartBaseRingHom A X Q a) =
      chartBaseRingHom A Y ((smallBaseChange B (Spec (.of A)) hA f hf).obj Q) a :=
  Γ_map_algebraMap_siteObj A (hf.snd Q.1.hom) a

/-- The sections of `𝒪_X` whose pullback along a representable `f : Y ⟶ X` lies in `I · 𝒪_Y`. -/
def baseIdealComap (I : Ideal A) :
    (SheafOfModules.unit (smallEtaleRingSheaf B (Spec (.of A)) hA X.1 X.2)).Submodule where
  obj V := Ideal.comap (chartIdealPullbackHom B (Spec (.of A)) hA f hf V.unop)
    ((baseIdealSheaf A Y I).obj (op ((smallBaseChange B (Spec (.of A)) hA f hf).obj V.unop)))
  map {V V'} g s hs := by
    change chartIdealPullbackHom B (Spec (.of A)) hA f hf V'.unop
      (chartSectionsRestrict B (Spec (.of A)) hA X g.unop s) ∈
        (baseIdealSheaf A Y I).obj (op ((smallBaseChange B (Spec (.of A)) hA f hf).obj V'.unop))
    have h := chartIdealPullbackHom_restrict B (Spec (.of A)) hA f hf g.unop s
    have hm :=
      (baseIdealSheaf A Y I).map ((smallBaseChange B (Spec (.of A)) hA f hf).map g.unop).op hs
    exact h ▸ hm
  isSheaf V s hs := by
    let s' : chartSectionsRing B (Spec (.of A)) hA X V.unop := s
    let t : chartSectionsRing B (Spec (.of A)) hA Y
        ((smallBaseChange B (Spec (.of A)) hA f hf).obj V.unop) :=
      chartIdealPullbackHom B (Spec (.of A)) hA f hf V.unop s'
    change t ∈
      (baseIdealSheaf A Y I).obj (op ((smallBaseChange B (Spec (.of A)) hA f hf).obj V.unop))
    refine (baseIdealSheaf A Y I).isSheaf (X := op ((smallBaseChange B (Spec (.of A)) hA f hf).obj
      V.unop)) t ((SmallEtale.topology B (Spec (.of A)) hA Y.1).superset_covering ?_
      ((coverPreserving_smallBaseChange B (Spec (.of A)) hA f hf).cover_preserve hs))
    rintro W k ⟨V'', g, h, hg, rfl⟩
    have hg' : chartIdealPullbackHom B (Spec (.of A)) hA f hf V''
        (chartSectionsRestrict B (Spec (.of A)) hA X g s') ∈
        (baseIdealSheaf A Y I).obj (op ((smallBaseChange B (Spec (.of A)) hA f hf).obj V'')) := hg
    have e := chartIdealPullbackHom_restrict B (Spec (.of A)) hA f hf g s'
    have hm := (baseIdealSheaf A Y I).map h.op (e ▸ hg')
    change chartSectionsRestrict B (Spec (.of A)) hA Y
      (h ≫ (smallBaseChange B (Spec (.of A)) hA f hf).map g) t ∈ _
    rw [chartSectionsRestrict_comp, RingHom.comp_apply]
    exact hm

/-- **The pullback of `I · 𝒪_X` along a representable morphism lies in `I · 𝒪_Y`.** -/
theorem map_chartIdealPullbackHom_baseIdealSheaf_le (I : Ideal A)
    (V : SmallEtale B (Spec (.of A)) hA X.1) :
    Ideal.map (chartIdealPullbackHom B (Spec (.of A)) hA f hf V)
        ((baseIdealSheaf A X I).obj (op V)) ≤
      (baseIdealSheaf A Y I).obj (op ((smallBaseChange B (Spec (.of A)) hA f hf).obj V)) := by
  have hle : baseIdealSheaf A X I ≤ baseIdealComap A f hf I := by
    refine Stacks.SheafOfModules.sheafifySubmodule_le fun W a ha => ?_
    change chartIdealPullbackHom B (Spec (.of A)) hA f hf W.unop a ∈
      (baseIdealSheaf A Y I).obj (op ((smallBaseChange B (Spec (.of A)) hA f hf).obj W.unop))
    refine le_baseIdealSheaf A Y I _ ?_
    have : Ideal.map (chartIdealPullbackHom B (Spec (.of A)) hA f hf W.unop)
        (Ideal.map (chartBaseRingHom A X W.unop) I) =
        Ideal.map
          (chartBaseRingHom A Y ((smallBaseChange B (Spec (.of A)) hA f hf).obj W.unop)) I := by
      rw [Ideal.map_map]
      exact congrArg (Ideal.map · I) (RingHom.ext fun a =>
        chartIdealPullbackHom_chartBaseRingHom A f hf W.unop a)
    exact this ▸ Ideal.mem_map_of_mem _ ha
  exact Ideal.map_le_iff_le_comap.2 fun a ha => hle (op V) ha

/-- The pullback of the `k`-th power of the sections of `I · 𝒪_X` along a representable
morphism lies in the `k`-th power of the sections of `I · 𝒪_Y`. -/
theorem pow_map_chartIdealPullbackHom_baseIdealSheaf_le (I : Ideal A) (k : ℕ)
    (V : SmallEtale B (Spec (.of A)) hA X.1) :
    Ideal.map (chartIdealPullbackHom B (Spec (.of A)) hA f hf V)
        (chartSectionsIdeal B (Spec (.of A)) hA X (baseIdealSheaf A X I) V ^ k) ≤
      chartSectionsIdeal B (Spec (.of A)) hA Y (baseIdealSheaf A Y I)
        ((smallBaseChange B (Spec (.of A)) hA f hf).obj V) ^ k := by
  rw [Ideal.map_pow]
  exact Ideal.pow_right_mono (map_chartIdealPullbackHom_baseIdealSheaf_le A f hf I V) k

/-- **The direct image along a representable morphism of a module annihilated by a power of
`I · 𝒪_Y` is annihilated by the same power of `I · 𝒪_X`.** -/
theorem isPowAnnihilated_smallBaseChangeModulePushforward (I : Ideal A) (k : ℕ)
    (Q : Modules.{u, u} B (Spec (.of A)) hA Y.1 Y.2)
    (hQ : IsPowAnnihilated B (Spec (.of A)) hA Y.1 Y.2 (baseIdealSheaf A Y I) k Q) :
    IsPowAnnihilated B (Spec (.of A)) hA X.1 X.2 (baseIdealSheaf A X I) k
      ((smallBaseChangeModulePushforward B (Spec (.of A)) hA f hf).obj Q) := by
  intro U r hr x
  have h := pow_map_chartIdealPullbackHom_baseIdealSheaf_le A f hf I k U
    (Ideal.mem_map_of_mem _ hr)
  exact hQ _ _ h x

include hf in
/-- **The direct image `modulePushforward f` of a module annihilated by a power of `I · 𝒪_Y` is
annihilated by the same power of `I · 𝒪_X`**, for a representable morphism `f : Y ⟶ X`. -/
theorem isPowAnnihilated_modulePushforward (I : Ideal A) (k : ℕ)
    (Q : Modules.{u, u} B (Spec (.of A)) hA Y.1 Y.2)
    (hQ : IsPowAnnihilated B (Spec (.of A)) hA Y.1 Y.2 (baseIdealSheaf A Y I) k Q) :
    IsPowAnnihilated B (Spec (.of A)) hA X.1 X.2 (baseIdealSheaf A X I) k
      ((modulePushforward B (Spec (.of A)) hA f).obj Q) :=
  @isPowAnnihilated_of_epi B (Spec (.of A)) hA X.1 X.2 (baseIdealSheaf A X I) k _ _
    ((modulePushforwardChartIso B (Spec (.of A)) hA f hf).app Q).inv
    (IsIso.epi_of_iso _)
    (isPowAnnihilated_smallBaseChangeModulePushforward A f hf I k Q hQ)

end Pullback

section Sections

variable {X Y : AlgebraicSpaces B (Spec (.of A)) hA} (f : Y ⟶ X)

/-- The identification of global sections of a direct image is the component at `N` of
`globalSectionsPushforwardIsoSite`. -/
theorem sectionsOverBasePushforwardIso_hom_apply (N : Modules.{u, u} B (Spec (.of A)) hA Y.1 Y.2)
    (s : (sectionsOverBase A B hA X.1 X.2).obj ((modulePushforward B (Spec (.of A)) hA f).obj N)) :
    (sectionsOverBasePushforwardIso A f N).hom s =
      ((globalSectionsPushforwardIsoSite B (Spec (.of A)) hA f).hom.app N).hom s := rfl

/-- The identification of global sections of a direct image is natural in the module. -/
theorem sectionsOverBasePushforwardIso_hom_naturality
    {N N' : Modules.{u, u} B (Spec (.of A)) hA Y.1 Y.2} (h : N ⟶ N')
    (s : (sectionsOverBase A B hA X.1 X.2).obj ((modulePushforward B (Spec (.of A)) hA f).obj N)) :
    (sectionsOverBasePushforwardIso A f N').hom
        ((sectionsOverBase A B hA X.1 X.2).map
          ((modulePushforward B (Spec (.of A)) hA f).map h) s) =
      (sectionsOverBase A B hA Y.1 Y.2).map h ((sectionsOverBasePushforwardIso A f N).hom s) := by
  rw [sectionsOverBasePushforwardIso_hom_apply, sectionsOverBasePushforwardIso_hom_apply]
  exact congrArg (fun φ => φ.hom s)
    ((globalSectionsPushforwardIsoSite B (Spec (.of A)) hA f).hom.naturality h)

attribute [local instance 5000] SheafOfModules.instAbelian in
/-- **Global sections of a direct image dying modulo `(I · 𝒪_X)ⁿ` die modulo `(I · 𝒪_Y)ⁿ`**, for a
representable morphism `f : Y ⟶ X`. -/
theorem sectionsOverBasePushforwardIso_hom_mem_sectionsKer
    (hf : yoneda.relativelyRepresentable f.hom) (I : Ideal A) (n : ℕ)
    (N : Modules.{u, u} B (Spec (.of A)) hA Y.1 Y.2)
    {s : (sectionsOverBase A B hA X.1 X.2).obj ((modulePushforward B (Spec (.of A)) hA f).obj N)}
    (hs : s ∈ sectionsKer A X (baseIdealSheaf A X I) n
      ((modulePushforward B (Spec (.of A)) hA f).obj N)) :
    (sectionsOverBasePushforwardIso A f N).hom s ∈ sectionsKer A Y (baseIdealSheaf A Y I) n N := by
  let πY := cokernel.π (idealPowerMultiple B (Spec (.of A)) hA Y.1 Y.2 (baseIdealSheaf A Y I) n N).ι
  have hz : (idealPowerMultiple B (Spec (.of A)) hA X.1 X.2 (baseIdealSheaf A X I) n
      ((modulePushforward B (Spec (.of A)) hA f).obj N)).ι ≫
        (modulePushforward B (Spec (.of A)) hA f).map πY = 0 :=
    idealPowerMultiple_ι_comp_eq_zero_of_eq_bot B (Spec (.of A)) hA X.1 X.2 _ n _
      ((idealPowerMultiple_eq_bot_iff B (Spec (.of A)) hA X.1 X.2 _ n _).2
        (isPowAnnihilated_modulePushforward A f hf I n _
          (isPowAnnihilated_idealPowerQuotient B (Spec (.of A)) hA Y.1 Y.2 _ n N)))
  have hfac := cokernel.π_desc _ ((modulePushforward B (Spec (.of A)) hA f).map πY) hz
  have h0 : (sectionsOverBase A B hA X.1 X.2).map
      ((modulePushforward B (Spec (.of A)) hA f).map πY) s = 0 := by
    rw [← hfac, Functor.map_comp]
    change ((sectionsOverBase A B hA X.1 X.2).map _).hom
      (((sectionsOverBase A B hA X.1 X.2).map _).hom s) = 0
    rw [show ((sectionsOverBase A B hA X.1 X.2).map (cokernel.π (idealPowerMultiple B (Spec (.of A))
      hA X.1 X.2 (baseIdealSheaf A X I) n ((modulePushforward B (Spec (.of A)) hA f).obj N)).ι)).hom
        s = 0 from hs, map_zero]
  have h1 := sectionsOverBasePushforwardIso_hom_naturality A f πY s
  rw [h0, map_zero] at h1
  exact h1.symm

/-- **The Artin-Rees property passes to direct images along representable morphisms.** -/
theorem HasSectionsArtinRees.modulePushforward (hf : yoneda.relativelyRepresentable f.hom)
    (I : Ideal A) (N : Modules.{u, u} B (Spec (.of A)) hA Y.1 Y.2)
    (h : HasSectionsArtinRees A Y (baseIdealSheaf A Y I) I N) :
    HasSectionsArtinRees A X (baseIdealSheaf A X I) I
      ((modulePushforward B (Spec (.of A)) hA f).obj N) := by
  intro m
  obtain ⟨n, hn⟩ := h m
  refine ⟨n, fun s hs => ?_⟩
  let e := (sectionsOverBasePushforwardIso A f N).toLinearEquiv
  have h1 := hn (sectionsOverBasePushforwardIso_hom_mem_sectionsKer A f hf I n N hs)
  have h2 := Submodule.mem_map_of_mem (f := e.symm.toLinearMap) h1
  rw [Submodule.map_smul'', Submodule.map_top, LinearEquiv.range] at h2
  have h3 : e.symm.toLinearMap ((sectionsOverBasePushforwardIso A f N).hom s) = s :=
    e.symm_apply_apply s
  rwa [h3] at h2

end Sections

end AlgebraicGeometry.Space
