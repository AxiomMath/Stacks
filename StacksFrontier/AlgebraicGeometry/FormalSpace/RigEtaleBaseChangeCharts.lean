module

public import StacksFrontier.AlgebraicGeometry.FormalSpace.AdicMorphismCharts
public import StacksFrontier.AlgebraicGeometry.FormalSpace.AdicMorphismConverse
public import StacksFrontier.AlgebraicGeometry.FormalSpace.FormalSpectrumCompletedTensorProduct
public import StacksFrontier.AlgebraicGeometry.FormalSpace.PullbackChartCover
public import StacksFrontier.AlgebraicGeometry.FormalSpace.RigEtaleAdicMonomorphism
public import StacksFrontier.AlgebraicGeometry.FormalSpace.RigEtaleCompositionCharts
public import StacksFrontier.RingTheory.Rig.RigSmoothStability
import all StacksFrontier.AlgebraicGeometry.FormalSpace.PullbackChartCover
import StacksCore.Tactic.StacksAttribute

/-!
# Base change of rig-étale morphisms of formal algebraic spaces

Let `S` be a scheme contained in a big fppf site `B` and let `f : X ⟶ Y` and `g : Z ⟶ Y` be
morphisms of locally Noetherian formal algebraic spaces over `S`. **Stacks 0GD1** says that if
`f` is rig-étale and `g` is adic, then the base change `X ×_Y Z ⟶ Z` is rig-étale. **Stacks
0GH4** deduces that if `g ∘ f` is rig-étale and `g` is an adic monomorphism then `f` is
rig-étale.

## Main results

* `FormalSpace.isAdicOnEveryAffineEtaleDiagramNoetherian_of_isAdicMorphism`: an adic morphism
  (Definition 0AQ3) has every Noetherian presentation of its chart maps adic.
* `FormalSpace.correspondsToRigEtaleMap_pullback_snd_of_isNoetherian`: the base change of a
  rig-étale chart map of Noetherian affine formal algebraic spaces by an adic one corresponds to
  a rig-étale map of Noetherian adic rings.
* `FormalSpace.correspondsToRigEtaleMapAfterSourceCover_pullback_snd`: condition (4) of
  Stacks 0GCZ for `X ×_Y Z ⟶ Z`.
* `FormalSpace.isRigEtale_pullback_snd_of_isLocallyNoetherian`: the base change of a rig-étale
  morphism by an adic morphism is rig-étale.
* `FormalSpace.isRigEtale_of_comp_of_isAdicMorphism_of_mono_of_isLocallyNoetherian`: if `g ∘ f`
  is rig-étale and `g` is an adic monomorphism, then `f` is rig-étale.

## References

* [Stacks Project, Tag 0GD1](https://stacks.math.columbia.edu/tag/0GD1)
* [Stacks Project, Tag 0GH4](https://stacks.math.columbia.edu/tag/0GH4)
* [Stacks Project, Tag 0GCW](https://stacks.math.columbia.edu/tag/0GCW)
* [Stacks Project, Tag 0GCZ](https://stacks.math.columbia.edu/tag/0GCZ)
* [Stacks Project, Tag 0GBD](https://stacks.math.columbia.edu/tag/0GBD)
* [Stacks Project, Tag 0AN3](https://stacks.math.columbia.edu/tag/0AN3)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits TopologicalRing

universe u

namespace AlgebraicGeometry.FormalSpace

variable (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)

attribute [local instance] Algebra.TensorProduct.rightAlgebra

/-- A Noetherian adic topological ring lies in `WAdm^{adic*}`: its ideals of definition are
finitely generated. -/
theorem isCountablyAdicStar_of_isNoetherianAdic {R : Type u} [CommRing R] [TopologicalSpace R]
    [IsTopologicalRing R] [IsLinearTopology R R] (hR : IsNoetherianAdic R) :
    IsCountablyAdicStar R := by
  have : IsNoetherianRing R := hR.2
  obtain ⟨I, hI, -⟩ := hR.1.1
  exact isCountablyAdicStar_of_isAdicStar ⟨hR.1, I, hI, Ideal.fg_of_isNoetherianRing I⟩

/-- An adic morphism in the sense of Definition 0AQ3 has every presentation of its chart maps
by Noetherian adic rings adic. -/
theorem isAdicOnEveryAffineEtaleDiagramNoetherian_of_isAdicMorphism {X Y : FppfSheaf B S hS}
    (f : X ⟶ Y) (hf : IsAdicMorphism B S hS f) :
    IsAdicOnEveryAffineEtaleDiagramNoetherian B S hS f := by
  intro U V a b t hU hV ha hb hsq A R _ _ _ _ _ _ _ _ hCA hCR hA D E eU eV g hg
  exact isAdicOnEveryAffineEtaleDiagram_of_isAdicMorphism' B S hS f hf U V a b t hU hV ha hb hsq
    A R (isCountablyAdicStar_of_isNoetherianAdic hCA) (isCountablyAdicStar_of_isNoetherianAdic hCR)
    hA D E eU eV g hg

/-- Let `t₁ : U ⟶ V` and `t₂ : W ⟶ V` be morphisms of Noetherian affine formal algebraic spaces,
all of whose Noetherian presentations are rig-étale, respectively adic. Then `U ×_V W ⟶ W`
corresponds to a rig-étale map in `WAdm^{Noeth}`. -/
theorem correspondsToRigEtaleMap_pullback_snd_of_isNoetherian {U V W : FppfSheaf B S hS}
    (t₁ : U ⟶ V) (t₂ : W ⟶ V) (hU : IsNoetherian B S hS U) (hV : IsNoetherian B S hS V)
    (hW : IsNoetherian B S hS W)
    (h₁ : HasPropertyOnAffineChartMap B S hS IsNoetherianAdic IsRigEtaleHom t₁)
    (h₂ : HasPropertyOnAffineChartMap B S hS
      (fun R ↦ TopologicalRing.IsAdic R ∧ IsNoetherianRing R)
      (fun {R₁ R₂ : Type u} [CommRing R₁] [TopologicalSpace R₁] [IsTopologicalRing R₁]
        [CommRing R₂] [TopologicalSpace R₂] [IsTopologicalRing R₂] (φ : R₁ →+* R₂) ↦
        RingHom.IsAdic φ) t₂) :
    CorrespondsToRigEtaleMap B S hS (pullback.snd t₁ t₂) := by
  obtain ⟨A, _, _, _, _, DA, hCA, ⟨eU⟩⟩ := exists_iso_formalSpectrum_of_isNoetherian B S hS hU
  obtain ⟨B₀, _, _, _, _, DB, hCB, ⟨eV⟩⟩ := exists_iso_formalSpectrum_of_isNoetherian B S hS hV
  obtain ⟨C, _, _, _, _, DC, hCC, ⟨eW⟩⟩ := exists_iso_formalSpectrum_of_isNoetherian B S hS hW
  have hAw := hCA.1.isWeaklyAdmissible
  have hBw := hCB.1.isWeaklyAdmissible
  have hCw := hCC.1.isWeaklyAdmissible
  obtain ⟨φ₁, hφ₁, -⟩ := existsUnique_continuousHom_formalSpectrumMap_eq hBw hAw
    (eU.inv ≫ t₁ ≫ eV.hom)
  obtain ⟨φ₂, hφ₂, -⟩ := existsUnique_continuousHom_formalSpectrumMap_eq hBw hCw
    (eW.inv ≫ t₂ ≫ eV.hom)
  have ht₁ : t₁ = eU.hom ≫ formalSpectrumMap hBw φ₁ ≫ eV.inv := by simp [hφ₁]
  have ht₂ : t₂ = eW.hom ≫ formalSpectrumMap hBw φ₂ ≫ eV.inv := by simp [hφ₂]
  have hP : IsRigEtaleHom φ₁.toRingHom := h₁ B₀ A hCB hCA hBw DB DA eU eV φ₁ ht₁
  have hQ : RingHom.IsAdic φ₂.toRingHom := h₂ B₀ C hCB hCC hBw DB DC eW eV φ₂ ht₂
  let : Algebra B₀ A := φ₁.toRingHom.toAlgebra
  let : Algebra B₀ C := φ₂.toRingHom.toAlgebra
  have : IsNoetherianRing A := hCA.2
  have : IsNoetherianRing B₀ := hCB.2
  have : IsNoetherianRing C := hCC.2
  obtain ⟨hTadic, hTnoeth, hTrig⟩ := rigEtale_completedTensorProduct_of_isAdic hCB.1 hCA.1 hCC.1
    φ₁.continuous φ₂.continuous hP hQ
  obtain ⟨-, hpb⟩ := isPullback_formalSpectrumMap_completedTensor B₀ hAw hCw DA DC hBw φ₁ φ₂
    rfl rfl
  have hpb' : IsPullback
      (formalSpectrumMap hAw (completedTensorLeftHom B₀ hAw hCw DA DC) ≫ eU.inv)
      (formalSpectrumMap hCw (completedTensorRightHom B₀ hAw hCw DA DC hBw φ₁ φ₂ rfl rfl) ≫
        eW.inv) t₁ t₂ :=
    IsPullback.of_iso hpb (Iso.refl _) eU.symm eW.symm eV.symm (by simp) (by simp)
      (by rw [ht₁]; simp) (by rw [ht₂]; simp)
  have halg : (completedTensorRight B₀ A C) =
      algebraMap C (TopologicalRing.CompletedTensorProduct (R := B₀) (M := A) (N := C)) :=
    RingHom.ext fun _ ↦ rfl
  refine ⟨C, _, inferInstance, inferInstance, inferInstance, inferInstance, inferInstance,
    inferInstance, inferInstance, inferInstance, hCC, ⟨hTadic, hTnoeth⟩, hCw, DC,
    completedTensorQuotientSystem B₀ hAw hCw DA DC, hpb'.isoPullback.symm, eW,
    completedTensorRightHom B₀ hAw hCw DA DC hBw φ₁ φ₂ rfl rfl, ?_, ?_⟩
  · exact (Iso.eq_inv_comp _).mpr hpb'.isoPullback_hom_snd
  · change RingHom.IsRigEtaleArrow (completedTensorRight B₀ A C)
    rwa [halg]

/-- Let `f : X ⟶ Y` and `g : Z ⟶ Y` be morphisms of locally Noetherian formal algebraic spaces
with `f` rig-étale and `g` adic. Then `X ×_Y Z ⟶ Z` satisfies condition (4) of Stacks 0GCZ, on
the covering of `X ×_Y Z` by the fibre products `Uⱼᵢ ×_{Vⱼ} Wⱼₖ` of charts of Stacks 0GBD. -/
theorem correspondsToRigEtaleMapAfterSourceCover_pullback_snd {X Y Z : FppfSheaf B S hS}
    (f : X ⟶ Y) (g : Z ⟶ Y) (hX : IsLocallyNoetherian B S hS X)
    (hY : IsLocallyNoetherian B S hS Y) (hZ : IsLocallyNoetherian B S hS Z)
    (hf : IsRigEtale B S hS f) (hg : IsAdicMorphism B S hS g) :
    CorrespondsToRigEtaleMapAfterSourceCover B S hS (pullback.snd f g) := by
  let : HasColimitsOfSize.{u + 1, u + 1} (FppfSheaf B S hS) := Sheaf.instHasColimitsOfSize
  obtain ⟨J, V, v, hV⟩ := exists_isAffineEtaleCover_of_isRepresentableEtale B S hS hY (𝟙 Y)
    (isRepresentableEtale_of_isIso B S hS _)
  choose I U a hU using fun j ↦ exists_isAffineEtaleCover_of_isRepresentableEtale B S hS hX
    (pullback.snd (v j) f) (isRepresentableEtale_pullback_snd B S hS (v j) f (hV.2.1 j))
  choose K W b hW using fun j ↦ exists_isAffineEtaleCover_of_isRepresentableEtale B S hS hZ
    (pullback.snd (v j) g) (isRepresentableEtale_pullback_snd B S hS (v j) g (hV.2.1 j))
  have hf5 := (isRigEtale_iff_hasPropertyOnEveryAffineEtaleDiagram B S hS f).mp hf
  have hg5 := isAdicOnEveryAffineEtaleDiagramNoetherian_of_isAdicMorphism B S hS g hg
  let r : (x : Σ j, I j) → pullback (a x.1 x.2 ≫ pullback.snd (v x.1) f) (pullback.fst f g) ⟶
      pullback f g := fun x ↦ pullback.snd _ _
  have hr : Sheaf.IsLocallySurjective (Sigma.desc r) :=
    Sheaf.isLocallySurjective_sigmaDesc_pullback_snd (pullback.fst f g)
      (fun x : Σ j, I j ↦ a x.1 x.2 ≫ pullback.snd (v x.1) f)
      (isLocallySurjective_sigmaDesc_comp_sigma B S hS (fun j ↦ pullback.snd (v j) f)
        (Sheaf.isLocallySurjective_sigmaDesc_pullback_snd f v hV.2.2)
        (fun x : Σ j, I j ↦ a x.1 x.2) (fun j ↦ (hU j).2.2))
  let q : ∀ (x : Σ j, I j) (k : K x.1),
      pullback (a x.1 x.2 ≫ pullback.fst (v x.1) f) (b x.1 k ≫ pullback.fst (v x.1) g) ⟶
        pullback (a x.1 x.2 ≫ pullback.snd (v x.1) f) (pullback.fst f g) :=
    fun x k ↦ chartLift B S hS f g (v x.1) (a x.1 x.2) (b x.1 k)
  have hq : ∀ x : Σ j, I j, Sheaf.IsLocallySurjective (Sigma.desc fun k : K x.1 ↦ q x k) := by
    intro x
    let sq := fun k : K x.1 ↦ isPullback_chartLift B S hS f g (v x.1) (a x.1 x.2) (b x.1 k)
    have hsnd := Sheaf.isLocallySurjective_sigmaDesc_pullback_snd
      (chartCompare B S hS f g (v x.1) (a x.1 x.2)) (fun k : K x.1 ↦ b x.1 k) (hW x.1).2.2
    have hfac : (Sigma.desc fun k : K x.1 ↦ q x k) =
        (Sigma.mapIso fun k : K x.1 ↦ (sq k).isoPullback).hom ≫
          Sigma.desc fun k : K x.1 ↦ pullback.snd (b x.1 k)
            (chartCompare B S hS f g (v x.1) (a x.1 x.2)) := by
      refine Sigma.hom_ext _ _ fun k ↦ ?_
      rw [Sigma.ι_comp_desc, Sigma.ι_mapIso_hom_assoc, Sigma.ι_comp_desc,
        IsPullback.isoPullback_hom_snd]
    rw [hfac]
    infer_instance
  have hcov := isLocallySurjective_sigmaDesc_comp_sigma B S hS r hr
    (fun y : Σ x : Σ j, I j, K x.1 ↦ q y.1 y.2) hq
  have hqr : ∀ y : Σ x : Σ j, I j, K x.1, q y.1 y.2 ≫ r y.1 =
      chartPullbackMap B S hS f g (v y.1.1) (a y.1.1 y.1.2) (b y.1.1 y.2) := fun y ↦
    chartLift_comp_snd B S hS f g (v y.1.1) (a y.1.1 y.1.2) (b y.1.1 y.2)
  have hcomp : ∀ {T P : FppfSheaf B S hS} (k : T ⟶ Y) (j : J) (c : P ⟶ pullback (v j) k),
      IsRepresentableEtale B S hS c → IsRepresentableEtale B S hS (c ≫ pullback.snd (v j) k) :=
    fun k j _ hc ↦ hc.comp B S hS (isRepresentableEtale_pullback_snd B S hS (v j) k (hV.2.1 j))
  have hcorr : ∀ y : Σ x : Σ j, I j, K x.1, CorrespondsToRigEtaleMap B S hS
      (pullback.snd (a y.1.1 y.1.2 ≫ pullback.fst (v y.1.1) f)
        (b y.1.1 y.2 ≫ pullback.fst (v y.1.1) g)) := by
    rintro ⟨⟨j, i⟩, k⟩
    have hUa := hcomp f j _ ((hU j).2.1 i)
    have hWb := hcomp g j _ ((hW j).2.1 k)
    exact correspondsToRigEtaleMap_pullback_snd_of_isNoetherian B S hS _ _
      (isNoetherian_of_isLocallyNoetherian_of_isRepresentableEtale B S hS hX _ ((hU j).1 i) hUa)
      (isNoetherian_of_isLocallyNoetherian_of_isRepresentableEtale B S hS hY _ (hV.1 j)
        (hV.2.1 j))
      (isNoetherian_of_isLocallyNoetherian_of_isRepresentableEtale B S hS hZ _ ((hW j).1 k) hWb)
      (hf5 _ _ _ (v j) _ ((hU j).1 i) (hV.1 j) hUa (hV.2.1 j)
        (by simp only [Category.assoc, pullback.condition]))
      (hg5 _ _ _ (v j) _ ((hW j).1 k) (hV.1 j) hWb (hV.2.1 j)
        (by simp only [Category.assoc, pullback.condition]))
  refine ⟨Σ x : Σ j, I j, K x.1, _, fun y ↦ q y.1 y.2 ≫ r y.1, ⟨fun y ↦ ?_, fun y ↦ ?_, hcov⟩,
    fun y ↦ ⟨W y.1.1 y.2, b y.1.1 y.2 ≫ pullback.snd (v y.1.1) g, pullback.snd _ _,
      (hW y.1.1).1 y.2, hcomp g _ _ ((hW y.1.1).2.1 y.2), ?_, hcorr y⟩⟩
  · obtain ⟨A, R, _, _, _, _, _, _, _, _, -, hCR, -, -, E, eU, -⟩ := hcorr y
    exact isAffineFormalAlgebraicSpace_of_iso_formalSpectrum_of_isAdic B S hS hCR.1 E eU
  · beta_reduce
    rw [hqr]
    exact isRepresentableEtale_chartPullbackMap B S hS f g (v y.1.1) (a y.1.1 y.1.2)
      (b y.1.1 y.2) (hV.2.1 y.1.1) ((hU y.1.1).2.1 y.1.2) ((hW y.1.1).2.1 y.2)
  · beta_reduce
    rw [hqr]
    exact chartPullbackMap_comp_snd B S hS f g (v y.1.1) (a y.1.1 y.1.2) (b y.1.1 y.2)

/-- **Stacks 0GD1.** Let `f : X ⟶ Y` and `g : Z ⟶ Y` be morphisms of locally Noetherian formal
algebraic spaces over `S`. If `f` is rig-étale and `g` is adic, then the base change
`X ×_Y Z ⟶ Z` is rig-étale.

The hypotheses are those of the source: `IsLocallyNoetherian` is Stacks 0AKY, `IsRigEtale` is
Definition 0AQM and `IsAdicMorphism` is Definition 0AQ3. As in the source, the proof reduces by
condition (4) of Stacks 0GCZ to the ring-level statement Stacks 0GCW on the fibre products of
charts of Stacks 0GBD. -/
@[stacks 0GD1]
theorem isRigEtale_pullback_snd_of_isLocallyNoetherian {X Y Z : FppfSheaf B S hS}
    (f : X ⟶ Y) (g : Z ⟶ Y) (hX : IsLocallyNoetherian B S hS X)
    (hY : IsLocallyNoetherian B S hS Y) (hZ : IsLocallyNoetherian B S hS Z)
    (hf : IsRigEtale B S hS f) (hg : IsAdicMorphism B S hS g) :
    IsRigEtale B S hS (pullback.snd f g) :=
  (isRigEtale_iff_hasPropertyOnEveryAffineEtaleDiagram B S hS _).mpr
    (hasPropertyOnEveryAffineEtaleDiagram_of_correspondsToRigEtaleMapAfterSourceCover B S hS _
      (correspondsToRigEtaleMapAfterSourceCover_pullback_snd B S hS f g hX hY hZ hf hg))

/-- **Stacks 0GH4.** Let `f : X ⟶ Y` and `g : Y ⟶ Z` be morphisms of locally Noetherian formal
algebraic spaces over `S`. If `g ∘ f` is rig-étale and `g` is an adic monomorphism, then `f` is
rig-étale: as `g` is a monomorphism, `f` is the base change of `g ∘ f` by `g`, so Stacks 0GD1
applies. -/
@[stacks 0GH4]
theorem isRigEtale_of_comp_of_isAdicMorphism_of_mono_of_isLocallyNoetherian
    {X Y Z : FppfSheaf B S hS} (f : X ⟶ Y) (g : Y ⟶ Z) (hX : IsLocallyNoetherian B S hS X)
    (hY : IsLocallyNoetherian B S hS Y) (hZ : IsLocallyNoetherian B S hS Z)
    (hfg : IsRigEtale B S hS (f ≫ g)) (hgadic : IsAdicMorphism B S hS g) (hgmono : Mono g) :
    IsRigEtale B S hS f := by
  have hpb : IsPullback (𝟙 X) f (f ≫ g) g := isPullback_id_of_mono B S hS f g hgmono
  have h := isRigEtale_iso_hom_comp B S hS hpb.isoPullback (pullback.snd (f ≫ g) g)
    (isRigEtale_pullback_snd_of_isLocallyNoetherian B S hS (f ≫ g) g hX hZ hY hfg hgadic)
  rwa [hpb.isoPullback_hom_snd] at h

end AlgebraicGeometry.FormalSpace

end
