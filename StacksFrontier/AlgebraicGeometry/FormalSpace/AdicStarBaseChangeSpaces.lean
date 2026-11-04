module

public import StacksFrontier.AlgebraicGeometry.FormalSpace.ChartPullbackAtlasCover
public import StacksFrontier.AlgebraicGeometry.FormalSpace.CompletedTensorChartBaseChange
public import StacksFrontier.AlgebraicGeometry.FormalSpace.CountablyIndexedPullbackProperty
public import StacksFrontier.AlgebraicGeometry.FormalSpace.LocalPropertyBaseChangeClass
public import StacksFrontier.AlgebraicGeometry.FormalSpace.LocalPropertySourceCover
public import StacksFrontier.AlgebraicGeometry.FormalSpace.TypeTransferRefined
public import StacksFrontier.AlgebraicGeometry.FormalSpace.WeakIdealPresentation

/-!
# The 0GBD variant for locally adic\* formal algebraic spaces

Let `S` be a scheme contained in a big fppf site `B`. The second half of **Remark 87.21.8
(Stacks 0GBE)** asserts the analogue of **Lemma 87.21.7 (Stacks 0GBD)** for morphisms between
locally adic\* formal algebraic spaces: if `P` is a local property of morphisms of
`WAdm^{adic*}` stable under base change, `f : X ⟶ Y` and `g : Z ⟶ Y` are morphisms of locally
adic\* formal algebraic spaces over `S`, and `f` satisfies the equivalent conditions of Stacks
0ANG for `P`, then so does `pr₂ : X ×_Y Z ⟶ Z`.

This file builds the covering of `X ×_Y Z` used in the proof of Stacks 0GBD out of the
hypotheses that `X`, `Y` and `Z` are locally adic\*.

## Main results

* `AlgebraicGeometry.FormalSpace.isChartOfClass_of_isAdicStar`: an adic\* affine formal
  algebraic space is a chart of the class `WAdm^{adic*}`.
* `AlgebraicGeometry.FormalSpace.exists_spfPresentation_of_isAdicStar`: an adic\* affine
  formal algebraic space is presented by a ring of `WAdm^{adic*}`.
* `AlgebraicGeometry.FormalSpace.isAdicStar_pullback_of_isAdicStar`: the affine case of Stacks
  0GBB (4), from clause (3) of Stacks 0AN3 and Lemma 87.4.12 (Stacks 0GB4).
* `AlgebraicGeometry.FormalSpace.exists_isAdicStar_affineEtaleCover_pullback`: adic\* charts of
  `V ×_Y X` for `X` locally adic\*.
* `AlgebraicGeometry.FormalSpace.hasBaseChangeCoverOverPullbackSnd_of_isLocallyAdicStar`: the
  geometric input of the chart argument of Stacks 0GBD, for `X`, `Y` locally adic\* and `Z` a
  formal algebraic space.
* `AlgebraicGeometry.FormalSpace.isLocallyAdicStar_pullback_of_representableEtaleOverAffine`:
  Stacks 0GBB (4).
* `AlgebraicGeometry.FormalSpace.hasPropertyAfterSourceCover_pullback_snd_of_isLocallyAdicStar` and
  `AlgebraicGeometry.FormalSpace.hasPropertyAfterTargetCover_pullback_snd_of_isLocallyAdicStar`:
  conditions (3) and (2) of Stacks 0ANG for `pr₂ : X ×_Y Z ⟶ Z`.

All of these are stated at the étale case of Stacks 0AJH, as `hEt`
(`AlgebraicGeometry.FormalSpace.RepresentableEtaleOverAffineIsFormal`), which enters only
through Stacks 0AJ3 for a fibre product of two affine formal algebraic spaces over a formal
algebraic space with one leg representable étale.

## References

* [Stacks Project, Tag 0GBE](https://stacks.math.columbia.edu/tag/0GBE)
* [Stacks Project, Tag 0GBD](https://stacks.math.columbia.edu/tag/0GBD)
* [Stacks Project, Tag 0AKX](https://stacks.math.columbia.edu/tag/0AKX)
* [Stacks Project, Tag 0AJ3](https://stacks.math.columbia.edu/tag/0AJ3)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits

namespace AlgebraicGeometry.FormalSpace

universe u

variable (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)

/-- An adic\* affine formal algebraic space is a chart of the class `WAdm^{adic*}`: its
presenting ring is adic with a finitely generated ideal of definition, and the weak-ideal
colimit presentation identifies the space with the formal spectrum of that ring. -/
theorem isChartOfClass_of_isAdicStar {X : FppfSheaf B S hS} (hX : IsAdicStar B S hS X) :
    IsChartOfClass B S hS TopologicalRing.IsAdicStar X := by
  obtain ⟨-, A, i₁, i₂, i₃, i₄, ⟨-, ⟨pres⟩⟩, hadic, hI⟩ := hX
  exact ⟨A, i₁, i₂, i₃, i₄, ⟨hadic, hI⟩, pres.quotientSystem, ⟨pres.formalSpectrumIso⟩⟩

/-- An adic\* affine formal algebraic space is presented by a ring of `WAdm^{adic*}`: its
presenting ring, through the weak-ideal colimit presentation. This is the shape in which the
covering arguments of Stacks 0GBI and 0GBM consume the charts of a locally adic\* formal
algebraic space. -/
theorem exists_spfPresentation_of_isAdicStar (V : FppfSheaf B S hS)
    (hV : IsAdicStar B S hS V) :
    ∃ PV : SpfPresentation B S hS V, TopologicalRing.IsAdicStar PV.ring := by
  obtain ⟨-, A, i₁, i₂, i₃, i₄, ⟨-, ⟨pres⟩⟩, hadic, hI⟩ := hV
  exact ⟨⟨A, pres.quotientSystem, ⟨pres.formalSpectrumIso⟩⟩, hadic, hI⟩

section

attribute [local instance] Algebra.TensorProduct.rightAlgebra

/-- **The affine case of Stacks 0GBB, clause (4).** The fibre product of two adic\* affine formal
algebraic spaces over a third is adic\*: by clause (3) of Stacks 0AN3 it is the formal spectrum
of the completed tensor product of the three presenting rings, which is adic with a finitely
generated ideal of definition by Lemma 87.4.12 (Stacks 0GB4). -/
theorem isAdicStar_pullback_of_isAdicStar {U V W : FppfSheaf B S hS} (t : U ⟶ V) (s : W ⟶ V)
    (hU : IsAdicStar B S hS U) (hV : IsAdicStar B S hS V) (hW : IsAdicStar B S hS W) :
    IsAdicStar B S hS (pullback t s) := by
  obtain ⟨⟨hVaff, -⟩, A₀, i₀a, i₀b, i₀c, i₀d, ⟨h₀, ⟨P₀⟩⟩, hadic₀, hI₀⟩ := hV
  obtain ⟨⟨hUaff, -⟩, A₁, i₁a, i₁b, i₁c, i₁d, ⟨h₁, ⟨P₁⟩⟩, hadic₁, hI₁⟩ := hU
  obtain ⟨⟨hWaff, -⟩, A, ia, ib, ic, id, ⟨hA, ⟨P⟩⟩, hadic, hI⟩ := hW
  obtain ⟨c₁, hc₁map, -⟩ := existsUnique_continuousHom_formalSpectrumMap_eq h₀ h₁
    (P₁.formalSpectrumIso.inv ≫ t ≫ P₀.formalSpectrumIso.hom)
  obtain ⟨c, hcmap, -⟩ := existsUnique_continuousHom_formalSpectrumMap_eq h₀ hA
    (P.formalSpectrumIso.inv ≫ s ≫ P₀.formalSpectrumIso.hom)
  let : Algebra A₀ A₁ := c₁.toRingHom.toAlgebra
  let : Algebra A₀ A := c.toRingHom.toAlgebra
  obtain ⟨DT, -, -, eT, -, -, -, -⟩ :=
    exists_quotientSystem_iso_pullback_completedTensorProduct_of_isWeaklyAdmissible B S hS h₀ h₁
      hA P₀.quotientSystem P₁.quotientSystem P.quotientSystem c₁ c rfl rfl
  have hsq₁ : t ≫ P₀.formalSpectrumIso.hom =
      P₁.formalSpectrumIso.hom ≫ formalSpectrumMap h₀ c₁ := by
    rw [hc₁map, Iso.hom_inv_id_assoc]
  have hsq : s ≫ P₀.formalSpectrumIso.hom = P.formalSpectrumIso.hom ≫ formalSpectrumMap h₀ c := by
    rw [hcmap, Iso.hom_inv_id_assoc]
  have hpb : IsPullback (pullback.fst t s ≫ P₁.formalSpectrumIso.hom)
      (pullback.snd t s ≫ P.formalSpectrumIso.hom) (formalSpectrumMap h₀ c₁)
      (formalSpectrumMap h₀ c) :=
    (IsPullback.of_hasPullback t s).of_iso (Iso.refl _) P₁.formalSpectrumIso P.formalSpectrumIso
      P₀.formalSpectrumIso (by simp) (by simp) hsq₁ hsq
  have hT : TopologicalRing.IsWeaklyAdmissible (TopologicalRing.CompletedTensorProduct
      (R := A₀) (M := A₁) (N := A)) :=
    TopologicalRing.completedTensorProduct_isWeaklyAdmissible (B := A₀) h₁.1 hA.1
  have hpres : IsPresentingRing B S hS (TopologicalRing.CompletedTensorProduct
      (R := A₀) (M := A₁) (N := A)) (pullback t s) :=
    ⟨hT, ⟨DT.weakIdealColimitPresentation.ofIso (hpb.isoPullback ≪≫ eT)⟩⟩
  have hset : SatisfiesSetTheoreticCondition B S hS (pullback t s) :=
    satisfiesSetTheoreticCondition_pullback_of_hasRepresentableRelativeProducts B S hS t s
      (hasRepresentableRelativeProducts_of_isAffineFormalAlgebraicSpace B S hS hVaff)
      (hasRepresentableRelativeProducts_of_isAffineFormalAlgebraicSpace B S hS hUaff)
      (hasRepresentableRelativeProducts_of_isAffineFormalAlgebraicSpace B S hS hWaff)
      hUaff.1 hWaff.1
  obtain ⟨hTadic, hTfg⟩ := TopologicalRing.isAdicStar_completedTensorProduct
    (A₀ := A₀) ⟨hadic₁, hI₁⟩ ⟨hadic, hI⟩ c₁.continuous c.continuous
  exact ⟨(hasAllSurjectivePresentations_of_exists_weaklyAdmissible B S hS hset
      ⟨_, inferInstance, inferInstance, inferInstance, inferInstance, hpres.1, hpres.2⟩
      ).hasSomeSurjectivePresentation,
    _, _, _, _, _, hpres, hTadic, hTfg⟩

end

/-- A ring of `WAdm^{adic*}` is weakly admissible, as an adic ring. -/
private theorem isWeaklyAdmissible_of_isAdicStar (R : Type u) [CommRing R] [TopologicalSpace R]
    [IsTopologicalRing R] [IsLinearTopology R R] (h : TopologicalRing.IsAdicStar R) :
    TopologicalRing.IsWeaklyAdmissible R :=
  Rig.weaklyAdmissible_of_isAdicRing h.1

/-- The chart fibre products `Uⱼᵢ ×_{Vⱼ} Wⱼₖ` form an affine étale cover of `X ×_Y Z`, mapping by
the chart base change maps. -/
private theorem isAffineEtaleCover_chartPullback {X Y Z : FppfSheaf B S hS} (f : X ⟶ Y)
    (g : Z ⟶ Y) {J : Type (u + 1)} {V : J → FppfSheaf B S hS} (v : ∀ j, V j ⟶ Y)
    {I K : J → Type (u + 1)} {U : ∀ j, I j → FppfSheaf B S hS}
    {W : ∀ j, K j → FppfSheaf B S hS} (a : ∀ j i, U j i ⟶ pullback (v j) f)
    (b : ∀ j k, W j k ⟶ pullback (v j) g) (hV : IsAffineEtaleCover B S hS V v)
    (hU : ∀ j, IsAffineEtaleCover B S hS (U j) (a j))
    (hW : ∀ j, IsAffineEtaleCover B S hS (W j) (b j)) :
    IsAffineEtaleCover B S hS
      (fun p : Σ j, I j × K j ↦ pullback (a p.1 p.2.1 ≫ pullback.fst (v p.1) f)
        (b p.1 p.2.2 ≫ pullback.fst (v p.1) g))
      fun p ↦ chartPullbackMap B S hS f g (v p.1) (a p.1 p.2.1) (b p.1 p.2.2) := by
  let : HasColimitsOfSize.{u + 1, u + 1} (FppfSheaf B S hS) := Sheaf.instHasColimitsOfSize
  refine ⟨fun p ↦ ?_, fun p ↦ ?_,
    isLocallySurjective_sigmaDesc_chartPullbackMap B S hS f g v hV.2.2 a (fun j ↦ (hU j).2.2) b
      fun j ↦ (hW j).2.2⟩
  · exact isAffineFormalAlgebraicSpace_pullback B S hS _ _
      (hasRepresentableRelativeProducts_of_isAffineFormalAlgebraicSpace B S hS (hV.1 p.1))
      (IsAffineFormalAlgebraicSpace.isSeparated B S hS (hV.1 p.1))
      ((hU p.1).1 p.2.1) ((hW p.1).1 p.2.2)
  · exact isRepresentableEtale_chartPullbackMap B S hS f g (v p.1) (a p.1 p.2.1)
      (b p.1 p.2.2) (hV.2.1 p.1) ((hU p.1).2.1 p.2.1) ((hW p.1).2.1 p.2.2)

/-- **Adic\* charts of the fibre product of a chart with a locally adic\* space.** If `X` admits
an atlas as in Definition 0AIM by adic\* affine formal algebraic spaces and `v : V ⟶ Y` is
representable étale, then `V ×_Y X` has an affine étale covering
by adic\* affine formal algebraic spaces: the covering of
`exists_affineEtaleCover_pullback_of_atlas`, each member of which maps representably to a member
of the atlas of `X` and so is adic\* by Stacks 0AKQ (4), through Stacks 0AKN and clause (5) of
Stacks 0AKP. -/
theorem exists_isAdicStar_affineEtaleCover_pullback
    (hEt : RepresentableEtaleOverAffineIsFormal B S hS)
    {X Y V : FppfSheaf B S hS} (f : X ⟶ Y) (v : V ⟶ Y)
    (hX : HasAffineEtaleAtlasWithProperty B S hS X (IsAdicStar B S hS))
    (hv : IsRepresentableEtale B S hS v) :
    ∃ (I : Type (u + 1)) (U : I → FppfSheaf B S hS) (a : ∀ i, U i ⟶ pullback v f),
      IsAffineEtaleCover B S hS U a ∧ ∀ i, IsAdicStar B S hS (U i) := by
  obtain ⟨M, Xm, x, hXaff, hXet, hXsurj, hXadic⟩ := hX
  obtain ⟨I, U, a, ι, r, hU, hr, -⟩ := exists_affineEtaleCover_pullback_of_atlas B S hS hEt f v
    hv x ⟨hXaff, hXet, hXsurj⟩
  exact ⟨I, U, a, hU, fun i ↦ isAdicStar_of_isRepresentable' B S hS (r i)
    (hU.1 i) (hXaff (ι i)) (hr i).1 (hXadic (ι i))⟩

/-- **The covering of Stacks 0GBD for locally adic\* formal algebraic spaces.** Let
`f : X ⟶ Y` and `g : Z ⟶ Y` be morphisms of fppf sheaves with `X` and `Y` locally adic\* and
`Z` a formal algebraic space. Then `X ×_Y Z` has the covering of the proof of Stacks 0GBD by
fibre products of charts `Uⱼᵢ ×_{Vⱼ} Wⱼₖ`, each mapping to `Z` through a chart `Wⱼₖ` by a chart
base change of `f` along `g` at the class `WAdm^{adic*}`.

The charts `Vⱼ` are the members of an adic\* atlas of `Y`, the charts `Uⱼᵢ` of `Vⱼ ×_Y X` those
of `exists_isAdicStar_affineEtaleCover_pullback`, and the charts `Wⱼₖ` of `Vⱼ ×_Y Z`, which need
no property, those of `exists_affineEtaleCover_pullback_of_isFormalAlgebraicSpace`. The only
input not proved here is the étale case of Stacks 0AJH, as `hEt`, and it enters only through
Stacks 0AJ3 for a fibre product of two affine formal algebraic spaces over `Y`, one leg
representable étale. -/
theorem hasBaseChangeCoverOverPullbackSnd_of_isLocallyAdicStar
    (hEt : RepresentableEtaleOverAffineIsFormal B S hS)
    {X Y Z : FppfSheaf B S hS} (f : X ⟶ Y) (g : Z ⟶ Y)
    (hX : IsLocallyAdicStar B S hS X) (hY : IsLocallyAdicStar B S hS Y)
    (hZ : IsFormalAlgebraicSpace B S hS Z) :
    HasBaseChangeCoverOverPullbackSndOn B S hS TopologicalRing.IsAdicStar f g := by
  obtain ⟨J, V, v, hVaff, hVet, hVsurj, hVadic⟩ := hY.2
  choose I U a hU hUadic using fun j ↦ exists_isAdicStar_affineEtaleCover_pullback B S hS
    hEt f (v j) hX.2 (hVet j)
  choose K W b hW using fun j ↦ exists_affineEtaleCover_pullback_of_isFormalAlgebraicSpace B S
    hS hEt g (v j) hZ (hVet j)
  exact hasBaseChangeCoverOverPullbackSnd_of_chartPresentations B S hS
    TopologicalRing.IsAdicStar
    (isWeaklyAdmissible_of_isAdicStar) f g V v
    ⟨hVaff, hVet, hVsurj⟩ U a hU W b hW (fun j ↦ isChartOfClass_of_isAdicStar B S hS (hVadic j))
    fun j i ↦ isChartOfClass_of_isAdicStar B S hS (hUadic j i)

/-- **Stacks 0GBB, clause (4), at the étale case of Stacks 0AJH.** If `X`, `Y` and `Z` are
locally adic\* formal algebraic spaces, then so is `X ×_Y Z`.

The atlas is the one of the proof of Stacks 0GBB: the chart fibre products `Uⱼᵢ ×_{Vⱼ} Wⱼₖ` of an
adic\* atlas `{Vⱼ ⟶ Y}` with adic\* coverings of `Vⱼ ×_Y X` and of `Vⱼ ×_Y Z`
(`exists_isAdicStar_affineEtaleCover_pullback`), which are adic\* by
`isAdicStar_pullback_of_isAdicStar`. That `X ×_Y Z` is a formal algebraic space is
`isFormalAlgebraicSpace_pullback_of_chartCovers`. -/
theorem isLocallyAdicStar_pullback_of_representableEtaleOverAffine
    (hEt : RepresentableEtaleOverAffineIsFormal B S hS)
    {X Y Z : FppfSheaf B S hS} (f : X ⟶ Y) (g : Z ⟶ Y)
    (hX : IsLocallyAdicStar B S hS X) (hY : IsLocallyAdicStar B S hS Y)
    (hZ : IsLocallyAdicStar B S hS Z) :
    IsLocallyAdicStar B S hS (pullback f g) := by
  let : HasColimitsOfSize.{u + 1, u + 1} (FppfSheaf B S hS) := Sheaf.instHasColimitsOfSize
  obtain ⟨J, V, v, hVaff, hVet, hVsurj, hVadic⟩ := hY.2
  have hV : IsAffineEtaleCover B S hS V v := ⟨hVaff, hVet, hVsurj⟩
  choose I U a hU hUadic using fun j ↦ exists_isAdicStar_affineEtaleCover_pullback B S hS
    hEt f (v j) hX.2 (hVet j)
  choose K W b hW hWadic using fun j ↦ exists_isAdicStar_affineEtaleCover_pullback B S hS
    hEt g (v j) hZ.2 (hVet j)
  have hc := isAffineEtaleCover_chartPullback B S hS f g v a b hV hU hW
  exact ⟨isFormalAlgebraicSpace_pullback_of_chartCovers B S hS f g hX.1 hY.1 hZ.1 V v hV U a hU
    W b hW, _, _, _, hc.1, hc.2.1, hc.2.2, fun p ↦
      isAdicStar_pullback_of_isAdicStar B S hS _ _ (hUadic p.1 p.2.1) (hVadic p.1)
        (hWadic p.1 p.2.2)⟩

/-- **The 0GBD variant for locally adic\* formal algebraic spaces, condition (3) of Stacks 0ANG
for `pr₂`, at the étale case of Stacks 0AJH.** Let `P` be a local property of morphisms of
`WAdm^{adic*}` stable under base change, invariant under isomorphism of targets, and let
`f : X ⟶ Y`, `g : Z ⟶ Y` be morphisms of formal algebraic spaces with `X` and `Y` locally
adic\*. If `f` satisfies condition (1) of Stacks 0ANG for `P`, then `pr₂ : X ×_Y Z ⟶ Z` satisfies
condition (3).

This is the chart argument `hasPropertyAfterSourceCover_pullback_snd_of_stableBaseChangeAdicStar`
run on the covering `hasBaseChangeCoverOverPullbackSnd_of_isLocallyAdicStar`. -/
theorem hasPropertyAfterSourceCover_pullback_snd_of_isLocallyAdicStar
    (hEt : RepresentableEtaleOverAffineIsFormal B S hS)
    (P : ∀ {R₁ R₂ : Type u} [CommRing R₁] [TopologicalSpace R₁] [IsTopologicalRing R₁]
      [CommRing R₂] [TopologicalSpace R₂] [IsTopologicalRing R₂], (R₁ →+* R₂) → Prop)
    (hP : TopologicalRing.PropertyIsStableUnderBaseChangeAdicStar.{u} P)
    (hiso : PropertyIsInvariantUnderTargetIsoOn.{u} TopologicalRing.IsAdicStar P)
    {X Y Z : FppfSheaf B S hS} (f : X ⟶ Y) (g : Z ⟶ Y)
    (hX : IsLocallyAdicStar B S hS X) (hY : IsLocallyAdicStar B S hS Y)
    (hZ : IsFormalAlgebraicSpace B S hS Z)
    (hf : HasPropertyOnEveryAffineEtaleDiagram B S hS TopologicalRing.IsAdicStar P f) :
    HasPropertyAfterSourceCover B S hS TopologicalRing.IsAdicStar P (pullback.snd f g) :=
  hasPropertyAfterSourceCover_pullback_snd_of_stableBaseChangeAdicStar B S hS P hP hiso f g
    (hasBaseChangeCoverOverPullbackSnd_of_isLocallyAdicStar B S hS hEt f g hX hY hZ) hf

/-- **The 0GBD variant for locally adic\* formal algebraic spaces, condition (2) of Stacks 0ANG
for `pr₂`, at the étale case of Stacks 0AJH.** Under the hypotheses of
`hasPropertyAfterSourceCover_pullback_snd_of_isLocallyAdicStar`, `pr₂ : X ×_Y Z ⟶ Z` satisfies
condition (2): the charts `Wⱼₖ ⟶ Z` of the covering of Stacks 0GBD cover `Z`, and the chart
fibre products `Uⱼᵢ ×_{Vⱼ} Wⱼₖ` cover `Wⱼₖ ×_Z (X ×_Y Z)` by maps with `P`
(`hasPropertyAfterTargetCover_pullback_snd_of_chartPresentations`). -/
theorem hasPropertyAfterTargetCover_pullback_snd_of_isLocallyAdicStar
    (hEt : RepresentableEtaleOverAffineIsFormal B S hS)
    (P : ∀ {R₁ R₂ : Type u} [CommRing R₁] [TopologicalSpace R₁] [IsTopologicalRing R₁]
      [CommRing R₂] [TopologicalSpace R₂] [IsTopologicalRing R₂], (R₁ →+* R₂) → Prop)
    (hP : TopologicalRing.PropertyIsStableUnderBaseChangeAdicStar.{u} P)
    (hiso : PropertyIsInvariantUnderTargetIsoOn.{u} TopologicalRing.IsAdicStar P)
    {X Y Z : FppfSheaf B S hS} (f : X ⟶ Y) (g : Z ⟶ Y)
    (hX : IsLocallyAdicStar B S hS X) (hY : IsLocallyAdicStar B S hS Y)
    (hZ : IsFormalAlgebraicSpace B S hS Z)
    (hf : HasPropertyOnEveryAffineEtaleDiagram B S hS TopologicalRing.IsAdicStar P f) :
    HasPropertyAfterTargetCover B S hS TopologicalRing.IsAdicStar P (pullback.snd f g) := by
  obtain ⟨J, V, v, hVaff, hVet, hVsurj, hVadic⟩ := hY.2
  choose I U a hU hUadic using fun j ↦ exists_isAdicStar_affineEtaleCover_pullback B S hS
    hEt f (v j) hX.2 (hVet j)
  choose K W b hW using fun j ↦ exists_affineEtaleCover_pullback_of_isFormalAlgebraicSpace B S
    hS hEt g (v j) hZ (hVet j)
  exact hasPropertyAfterTargetCover_pullback_snd_of_chartPresentations B S hS
    TopologicalRing.IsAdicStar
    (isWeaklyAdmissible_of_isAdicStar) P (fun _ ↦ True)
    (completedTensorBaseChangeAxiom_of_stableBaseChangeAdicStar P hP) hiso f g V v
    ⟨hVaff, hVet, hVsurj⟩ U a hU W b hW (fun j ↦ isChartOfClass_of_isAdicStar B S hS (hVadic j))
    (fun j i ↦ isChartOfClass_of_isAdicStar B S hS (hUadic j i)) hf
    (hasPropertyOnEveryAffineEtaleDiagram_true B S hS _ g)

/-- **The 0GBD variant for locally adic\* formal algebraic spaces, condition (3) of Stacks 0ANG
for `pr₂` with charts of the class.** Under the hypotheses of
`hasPropertyAfterSourceCover_pullback_snd_of_isLocallyAdicStar`, and with `Z` locally adic\*,
`pr₂ : X ×_Y Z ⟶ Z` satisfies condition (3) on a covering whose members and target charts are
adic\*: the chart fibre products `Uⱼᵢ ×_{Vⱼ} Wⱼₖ`, adic\* by `isAdicStar_pullback_of_isAdicStar`,
mapping to the adic\* charts `Wⱼₖ` of `Vⱼ ×_Y Z`. This is the form of condition (3) from which
the implication (3) ⟹ (1) of Stacks 0ANG,
`hasPropertyOnEveryAffineEtaleDiagram_of_afterSourceCover_of_isLocal`, starts. -/
theorem hasPropertyAfterSourceCoverOfClass_pullback_snd_of_isLocallyAdicStar
    (hEt : RepresentableEtaleOverAffineIsFormal B S hS)
    (P : ∀ {R₁ R₂ : Type u} [CommRing R₁] [TopologicalSpace R₁] [IsTopologicalRing R₁]
      [CommRing R₂] [TopologicalSpace R₂] [IsTopologicalRing R₂], (R₁ →+* R₂) → Prop)
    (hP : TopologicalRing.PropertyIsStableUnderBaseChangeAdicStar.{u} P)
    (hiso : PropertyIsInvariantUnderTargetIsoOn.{u} TopologicalRing.IsAdicStar P)
    {X Y Z : FppfSheaf B S hS} (f : X ⟶ Y) (g : Z ⟶ Y)
    (hX : IsLocallyAdicStar B S hS X) (hY : IsLocallyAdicStar B S hS Y)
    (hZ : IsLocallyAdicStar B S hS Z)
    (hf : HasPropertyOnEveryAffineEtaleDiagram B S hS TopologicalRing.IsAdicStar P f) :
    HasPropertyAfterSourceCoverOfClass B S hS TopologicalRing.IsAdicStar P (pullback.snd f g) := by
  let : HasColimitsOfSize.{u + 1, u + 1} (FppfSheaf B S hS) := Sheaf.instHasColimitsOfSize
  obtain ⟨J, V, v, hVaff, hVet, hVsurj, hVadic⟩ := hY.2
  have hV : IsAffineEtaleCover B S hS V v := ⟨hVaff, hVet, hVsurj⟩
  choose I U a hU hUadic using fun j ↦ exists_isAdicStar_affineEtaleCover_pullback B S hS
    hEt f (v j) hX.2 (hVet j)
  choose K W b hW hWadic using fun j ↦ exists_isAdicStar_affineEtaleCover_pullback B S hS
    hEt g (v j) hZ.2 (hVet j)
  have hCwa : ∀ (R : Type u) [CommRing R] [TopologicalSpace R] [IsTopologicalRing R]
      [IsLinearTopology R R], TopologicalRing.IsAdicStar R → TopologicalRing.IsWeaklyAdmissible R :=
    fun R _ _ _ _ h ↦ Rig.weaklyAdmissible_of_isAdicRing h.1
  refine ⟨_, _, _, isAffineEtaleCover_chartPullback B S hS f g v a b hV hU hW, fun p ↦
    ⟨W p.1 p.2.2, b p.1 p.2.2 ≫ pullback.snd (v p.1) g,
      pullback.snd (a p.1 p.2.1 ≫ pullback.fst (v p.1) f) (b p.1 p.2.2 ≫ pullback.fst (v p.1) g),
      (hW p.1).1 p.2.2, IsRepresentableEtale.comp B S hS ((hW p.1).2.1 p.2.2)
        (isRepresentableEtale_pullback_snd B S hS (v p.1) g (hVet p.1)),
      chartPullbackMap_comp_snd B S hS f g (v p.1) (a p.1 p.2.1) (b p.1 p.2.2),
      isChartOfClass_of_isAdicStar B S hS (isAdicStar_pullback_of_isAdicStar B S hS _ _
        (hUadic p.1 p.2.1) (hVadic p.1) (hWadic p.1 p.2.2)),
      isChartOfClass_of_isAdicStar B S hS (hWadic p.1 p.2.2), ?_⟩⟩
  · exact hasPropertyOnAffineChartMap_of_isChartBaseChangeOn B S hS TopologicalRing.IsAdicStar P
      (fun _ ↦ True) (completedTensorBaseChangeAxiom_of_stableBaseChangeAdicStar P hP) hiso f g hf
      (hasPropertyOnEveryAffineEtaleDiagram_true B S hS _ g) _
      (isChartBaseChangeOf_chartPullback B S hS TopologicalRing.IsAdicStar hCwa f g V v hV U a hU
        W b hW (fun j ↦ isChartOfClass_of_isAdicStar B S hS (hVadic j))
        (fun j i ↦ isChartOfClass_of_isAdicStar B S hS (hUadic j i)) p.1 p.2.1 p.2.2)

end AlgebraicGeometry.FormalSpace

end
