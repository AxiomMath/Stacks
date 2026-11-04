module

public import StacksCore.Tactic.StacksAttribute
public import StacksFrontier.AlgebraicGeometry.FormalSpace.AdicStarBaseChange
public import StacksFrontier.AlgebraicGeometry.FormalSpace.CompletedTensorFibreProduct
public import StacksFrontier.AlgebraicGeometry.FormalSpace.LocalPropertyBaseChangeClass
public import StacksFrontier.AlgebraicGeometry.FormalSpace.PullbackChartBaseChange

/-!
# The chart maps of a fibre product of charts, from clause (3) of Stacks 0AN3

Let `S` be a scheme contained in a big fppf site `B`. The chart argument of **Stacks 0GBD** is
run on the covering of `X ×_Y Z` by the fibre products `Uⱼᵢ ×_{Vⱼ} Wⱼₖ` of charts, and it needs
of that covering one ring-level fact: that the chart ring of `Uⱼᵢ ×_{Vⱼ} Wⱼₖ` is the completed
tensor product of the chart rings of `Uⱼᵢ` and `Wⱼₖ` over that of `Vⱼ`, compatibly with the
projection to `Wⱼₖ`. That is clause (3) of **Stacks 0AN3**, and in
`StacksFrontier/AlgebraicGeometry/FormalSpace/LocalPropertyBaseChange.lean` it is packaged as
`AlgebraicGeometry.FormalSpace.IsChartBaseChangeOn` and carried as a hypothesis — `hAN3` at the
`WAdm^count` site of Stacks 0GBD and the `IsChartBaseChangeOn` clause of
`AlgebraicGeometry.FormalSpace.HasBaseChangeCoverOverPullbackSndOn` at the `WAdm^{adic*}` site of
Stacks 0GBE.

This file discharges it from
`AlgebraicGeometry.FormalSpace.exists_continuous_ringEquiv_completedTensorProduct_pullback`,
which is clause (3) of Stacks 0AN3 read on chart rings. What is left over is exactly the input
that clause carries: presentations of the two charts `Vⱼ` and `Uⱼᵢ` as formal spectra of rings
of the class, recorded as `AlgebraicGeometry.FormalSpace.IsChartOfClass`. For a locally
countably indexed or locally adic\* formal algebraic space, which is what Stacks 0GBD and
Stacks 0GBE assume of `X`, `Y` and `Z`, those presentations are what the McQuillan criterion of
Stacks 0AIC supplies; being an affine formal algebraic space does not supply them, and
`AlgebraicGeometry.FormalSpace.IsAffineEtaleCover` asserts no more than that.

Note that `IsChartBaseChangeOn` quantifies over *every* presentation of the fibre product of
charts and of the chart of `Z`, and asks for a weakly admissible ring only of the latter. The
class is therefore required here to consist of weakly admissible rings, `hCwa`; both
`TopologicalRing.IsCountablyWeaklyAdmissible` and `TopologicalRing.IsAdicStar` do.

## Main definitions

* `AlgebraicGeometry.FormalSpace.IsChartOfClass`: an fppf sheaf is the formal spectrum of a
  topological ring of a given class over `S`.

## Main results

* `AlgebraicGeometry.FormalSpace.isChartBaseChangeOf_chartPullback`: `hAN3` of the chart
  argument of **Stacks 0GBD**, from clause (3) of Stacks 0AN3 and presentations of the charts.
* `AlgebraicGeometry.FormalSpace.hasBaseChangeCoverOverPullbackSnd_of_chartPresentations`: the
  geometric input of Stacks 0GBD with its ring-level clause discharged.
* `hasPropertyAfterSourceCover_pullback_snd_countablyIndexed_of_charts`, in the namespace
  `AlgebraicGeometry.FormalSpace`: **Stacks 0GBD** with `hAN3` removed.
* `hasPropertyOnEveryAffineEtaleDiagram_pullback_snd_adicStar_of_charts`, in the same
  namespace: **Stacks 0GBE**, second half, with the ring-level half of `hcover` removed.

## References

* [Stacks Project, Tag 0AN3](https://stacks.math.columbia.edu/tag/0AN3)
* [Stacks Project, Tag 0GBD](https://stacks.math.columbia.edu/tag/0GBD)
* [Stacks Project, Tag 0GBE](https://stacks.math.columbia.edu/tag/0GBE)
* [Stacks Project, Tag 0ANG](https://stacks.math.columbia.edu/tag/0ANG)
* [Stacks Project, Tag 0AIC](https://stacks.math.columbia.edu/tag/0AIC)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits
open scoped TensorProduct

namespace AlgebraicGeometry.FormalSpace

universe u

variable (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)

section

attribute [local instance] Algebra.TensorProduct.rightAlgebra

/-- An fppf sheaf is a *chart of the class `C`* when it is the formal spectrum of a topological
ring of the class `C` over `S`. This is the data that conditions (1) and (3) of Stacks 0ANG
quantify over, read on a single chart: a presentation of it as a formal spectrum, with its ring
in the class. For the charts of a locally countably indexed formal algebraic space it is Stacks
0AIC through Stacks 0AIS; it is not a consequence of being an affine formal algebraic space. -/
abbrev IsChartOfClass
    (C : ∀ (R : Type u) [CommRing R] [TopologicalSpace R] [IsTopologicalRing R]
      [IsLinearTopology R R], Prop)
    (X : FppfSheaf B S hS) : Prop :=
  ∃ (A : Type u) (_ : CommRing A) (_ : TopologicalSpace A) (_ : IsTopologicalRing A)
      (_ : IsLinearTopology A A),
    letI : CommRing A := ‹CommRing A›
    letI : TopologicalSpace A := ‹TopologicalSpace A›
    letI : IsTopologicalRing A := ‹IsTopologicalRing A›
    letI : IsLinearTopology A A := ‹IsLinearTopology A A›
    C A ∧ ∃ D : QuotientSystem B S hS A, Nonempty (X ≅ formalSpectrum D)

/-- Given an étale chart square over `f` presented by rings `A₀`, `A₁`, the map of charts is the
formal spectrum of a continuous ring map, which is an affine étale chart map of `f`. -/
private theorem exists_continuousHom_isAffineEtaleChartMap
    {X Y V U : FppfSheaf B S hS} (f : X ⟶ Y) (v : V ⟶ Y) (a : U ⟶ X) (t : U ⟶ V)
    (hUaff : IsAffineFormalAlgebraicSpace B S hS U)
    (hVaff : IsAffineFormalAlgebraicSpace B S hS V)
    (ha : IsRepresentableEtale B S hS a) (hv : IsRepresentableEtale B S hS v)
    (hsq : a ≫ f = t ≫ v) {A₀ A₁ : Type u}
    [CommRing A₀] [TopologicalSpace A₀] [IsTopologicalRing A₀] [IsLinearTopology A₀ A₀]
    [CommRing A₁] [TopologicalSpace A₁] [IsTopologicalRing A₁] [IsLinearTopology A₁ A₁]
    (h₀ : TopologicalRing.IsWeaklyAdmissible A₀) (h₁ : TopologicalRing.IsWeaklyAdmissible A₁)
    (D₀ : QuotientSystem B S hS A₀) (D₁ : QuotientSystem B S hS A₁)
    (eV : V ≅ formalSpectrum D₀) (eU : U ≅ formalSpectrum D₁) :
    ∃ c : ContinuousHom D₀ D₁, t ≫ eV.hom = eU.hom ≫ formalSpectrumMap h₀ c ∧
      IsAffineEtaleChartMap B S hS f c.toRingHom := by
  obtain ⟨c, hcmap, -⟩ := existsUnique_continuousHom_formalSpectrumMap_eq h₀ h₁
    (eU.inv ≫ t ≫ eV.hom)
  have hsq' : t ≫ eV.hom = eU.hom ≫ formalSpectrumMap h₀ c := by
    rw [hcmap, Iso.hom_inv_id_assoc]
  exact ⟨c, hsq', U, V, a, v, t, hUaff, hVaff, ha, hv, hsq, h₀, D₀, D₁, eU, eV, c,
    by rw [← Category.assoc, ← hsq', Category.assoc, Iso.hom_inv_id, Category.comp_id], rfl⟩

/-- **Stacks 0AN3, clause (3), in the shape the chart argument of Stacks 0GBD consumes it.**
Given a chart `Vⱼ ⟶ Y` and charts `Uⱼᵢ ⟶ X`, `Wⱼₖ ⟶ Z` over it, with presentations of `Vⱼ` and
`Uⱼᵢ` by rings of the class, the second projection of `Uⱼᵢ ×_{Vⱼ} Wⱼₖ` is a chart base change of
`f` along `g`: for every presentation of that fibre product and of `Wⱼₖ`, its chart ring is the
completed tensor product of the chart rings of `Uⱼᵢ` and `Wⱼₖ` over that of `Vⱼ`, compatibly
with the projection. -/
theorem isChartBaseChangeOf_pullback_snd_of_chartPresentations
    (C : ∀ (R : Type u) [CommRing R] [TopologicalSpace R] [IsTopologicalRing R]
      [IsLinearTopology R R], Prop)
    (hCwa : ∀ (R : Type u) [CommRing R] [TopologicalSpace R] [IsTopologicalRing R]
      [IsLinearTopology R R], C R → TopologicalRing.IsWeaklyAdmissible R)
    {X Y Z : FppfSheaf B S hS} (f : X ⟶ Y) (g : Z ⟶ Y)
    {V UX WZ : FppfSheaf B S hS}
    (v : V ⟶ Y) (aX : UX ⟶ X) (tX : UX ⟶ V) (bZ : WZ ⟶ Z) (tZ : WZ ⟶ V)
    (hUXaff : IsAffineFormalAlgebraicSpace B S hS UX)
    (hVaff : IsAffineFormalAlgebraicSpace B S hS V)
    (hWZaff : IsAffineFormalAlgebraicSpace B S hS WZ)
    (haX : IsRepresentableEtale B S hS aX) (hv : IsRepresentableEtale B S hS v)
    (hbZ : IsRepresentableEtale B S hS bZ)
    (hsqX : aX ≫ f = tX ≫ v) (hsqZ : bZ ≫ g = tZ ≫ v)
    {A₀ A₁ : Type u}
    [CommRing A₀] [TopologicalSpace A₀] [IsTopologicalRing A₀] [IsLinearTopology A₀ A₀]
    [CommRing A₁] [TopologicalSpace A₁] [IsTopologicalRing A₁] [IsLinearTopology A₁ A₁]
    (hCA₀ : C A₀) (hCA₁ : C A₁)
    (h₀ : TopologicalRing.IsWeaklyAdmissible A₀)
    (h₁ : TopologicalRing.IsWeaklyAdmissible A₁)
    (D₀ : QuotientSystem B S hS A₀) (D₁ : QuotientSystem B S hS A₁)
    (eV : V ≅ formalSpectrum D₀) (eUX : UX ≅ formalSpectrum D₁) :
    IsChartBaseChangeOn B S hS C f g (pullback.snd tX tZ) := by
  intro A R _ _ _ _ _ _ _ _ hCA hCR hA D E eP eW φ hφ Goal cont
  have hR : TopologicalRing.IsWeaklyAdmissible R := hCwa R hCR
  obtain ⟨c₁, hsq1, hcm₁⟩ := exists_continuousHom_isAffineEtaleChartMap B S hS f v aX tX hUXaff
    hVaff haX hv hsqX h₀ h₁ D₀ D₁ eV eUX
  obtain ⟨c, hsq2, hcm⟩ := exists_continuousHom_isAffineEtaleChartMap B S hS g v bZ tZ hWZaff
    hVaff hbZ hv hsqZ h₀ hA D₀ D eV eW
  let : Algebra A₀ A₁ := c₁.toRingHom.toAlgebra
  let : Algebra A₀ A := c.toRingHom.toAlgebra
  have hc₁alg : c₁.toRingHom = algebraMap A₀ A₁ := rfl
  have hcalg : c.toRingHom = algebraMap A₀ A := rfl
  have hpb : IsPullback (pullback.fst tX tZ ≫ eUX.hom) (pullback.snd tX tZ ≫ eW.hom)
      (formalSpectrumMap h₀ c₁) (formalSpectrumMap h₀ c) :=
    (IsPullback.of_hasPullback tX tZ).of_iso (Iso.refl _) eUX eW eV (by simp)
      (by simp) (by simp [hsq1]) (by simp [hsq2])
  set epres : pullback (formalSpectrumMap h₀ c₁) (formalSpectrumMap h₀ c) ≅ formalSpectrum E :=
    hpb.isoPullback.symm ≪≫ eP with hepres
  obtain ⟨ε, hεc, hεsc, hcompat⟩ :=
    exists_continuous_ringEquiv_completedTensorProduct_pullback
      B S hS h₀ h₁ hA D₀ D₁ D c₁ c hc₁alg hcalg hR E epres
  obtain ⟨a₁, ha₁, -⟩ := existsUnique_continuousHom_formalSpectrumMap_eq h₁ hR
    (epres.inv ≫ pullback.fst (formalSpectrumMap h₀ c₁) (formalSpectrumMap h₀ c))
  have hsnd : formalSpectrumMap hA φ =
      epres.inv ≫ pullback.snd (formalSpectrumMap h₀ c₁) (formalSpectrumMap h₀ c) := by
    rw [hepres]
    simp only [Iso.trans_inv, Iso.symm_inv, Category.assoc, IsPullback.isoPullback_hom_snd]
    rw [hφ]
    simp
  obtain ⟨-, hlast⟩ := hcompat a₁ φ ha₁ hsnd
  exact cont A₀ A₁ ε hCA₀ hCA₁ c₁.continuous c.continuous hcm₁ hcm hεc hεsc hlast

/-- **Stacks 0AN3, clause (3)** in the shape the chart argument of Stacks 0GBD consumes it, with
the two chart presentations packaged as `IsChartOfClass`. -/
theorem isChartBaseChangeOf_pullback_snd_of_isChartOfClass
    (C : ∀ (R : Type u) [CommRing R] [TopologicalSpace R] [IsTopologicalRing R]
      [IsLinearTopology R R], Prop)
    (hCwa : ∀ (R : Type u) [CommRing R] [TopologicalSpace R] [IsTopologicalRing R]
      [IsLinearTopology R R], C R → TopologicalRing.IsWeaklyAdmissible R)
    {X Y Z : FppfSheaf B S hS} (f : X ⟶ Y) (g : Z ⟶ Y)
    {V UX WZ : FppfSheaf B S hS}
    (v : V ⟶ Y) (aX : UX ⟶ X) (tX : UX ⟶ V) (bZ : WZ ⟶ Z) (tZ : WZ ⟶ V)
    (hUXaff : IsAffineFormalAlgebraicSpace B S hS UX)
    (hVaff : IsAffineFormalAlgebraicSpace B S hS V)
    (hWZaff : IsAffineFormalAlgebraicSpace B S hS WZ)
    (haX : IsRepresentableEtale B S hS aX) (hv : IsRepresentableEtale B S hS v)
    (hbZ : IsRepresentableEtale B S hS bZ)
    (hsqX : aX ≫ f = tX ≫ v) (hsqZ : bZ ≫ g = tZ ≫ v)
    (hVch : IsChartOfClass B S hS C V) (hUXch : IsChartOfClass B S hS C UX) :
    IsChartBaseChangeOn B S hS C f g (pullback.snd tX tZ) := by
  obtain ⟨A₀, j0a, j0b, j0c, j0d, hCA₀, D₀, ⟨eV⟩⟩ := hVch
  obtain ⟨A₁, j1a, j1b, j1c, j1d, hCA₁, D₁, ⟨eUX⟩⟩ := hUXch
  let : CommRing A₀ := j0a
  let : TopologicalSpace A₀ := j0b
  let : IsTopologicalRing A₀ := j0c
  let : IsLinearTopology A₀ A₀ := j0d
  let : CommRing A₁ := j1a
  let : TopologicalSpace A₁ := j1b
  let : IsTopologicalRing A₁ := j1c
  let : IsLinearTopology A₁ A₁ := j1d
  exact isChartBaseChangeOf_pullback_snd_of_chartPresentations B S hS C hCwa f g v aX tX bZ tZ
    hUXaff hVaff hWZaff haX hv hbZ hsqX hsqZ hCA₀ hCA₁ (hCwa A₀ hCA₀) (hCwa A₁ hCA₁) D₀ D₁ eV eUX

/-- The chart maps of the covering of `X ×_Y Z` by the fibre products of charts are chart base
changes of `f` along `g`: this is `hAN3` of the chart argument of **Stacks 0GBD**, discharged
from clause (3) of Stacks 0AN3 together with presentations of the charts `Vⱼ` and `Uⱼᵢ`. -/
theorem isChartBaseChangeOf_chartPullback
    (C : ∀ (R : Type u) [CommRing R] [TopologicalSpace R] [IsTopologicalRing R]
      [IsLinearTopology R R], Prop)
    (hCwa : ∀ (R : Type u) [CommRing R] [TopologicalSpace R] [IsTopologicalRing R]
      [IsLinearTopology R R], C R → TopologicalRing.IsWeaklyAdmissible R)
    {X Y Z : FppfSheaf B S hS} (f : X ⟶ Y) (g : Z ⟶ Y)
    {J : Type (u + 1)} (V : J → FppfSheaf B S hS) (v : ∀ j, V j ⟶ Y)
    (hV : IsAffineEtaleCover B S hS V v)
    {I : J → Type (u + 1)} (U : ∀ j, I j → FppfSheaf B S hS)
    (a : ∀ j i, U j i ⟶ pullback (v j) f) (hU : ∀ j, IsAffineEtaleCover B S hS (U j) (a j))
    {K : J → Type (u + 1)} (W : ∀ j, K j → FppfSheaf B S hS)
    (b : ∀ j k, W j k ⟶ pullback (v j) g) (hW : ∀ j, IsAffineEtaleCover B S hS (W j) (b j))
    (hVch : ∀ j, IsChartOfClass B S hS C (V j))
    (hUch : ∀ j i, IsChartOfClass B S hS C (U j i))
    (j : J) (i : I j) (k : K j) :
    IsChartBaseChangeOn B S hS C f g
      (pullback.snd (a j i ≫ pullback.fst (v j) f) (b j k ≫ pullback.fst (v j) g)) := by
  refine isChartBaseChangeOf_pullback_snd_of_isChartOfClass B S hS C hCwa f g (v j)
    (a j i ≫ pullback.snd (v j) f) (a j i ≫ pullback.fst (v j) f)
    (b j k ≫ pullback.snd (v j) g) (b j k ≫ pullback.fst (v j) g)
    ((hU j).1 i) (hV.1 j) ((hW j).1 k)
    (IsRepresentableEtale.comp B S hS ((hU j).2.1 i)
      (isRepresentableEtale_pullback_snd B S hS (v j) f (hV.2.1 j)))
    (hV.2.1 j)
    (IsRepresentableEtale.comp B S hS ((hW j).2.1 k)
      (isRepresentableEtale_pullback_snd B S hS (v j) g (hV.2.1 j)))
    ?_ ?_ (hVch j) (hUch j i)
  · rw [Category.assoc, Category.assoc, ← pullback.condition]
  · rw [Category.assoc, Category.assoc, ← pullback.condition]

/-- The geometric input of the chart argument of **Stacks 0GBD** on the covering of `X ×_Y Z` by
the fibre products of charts, with its ring-level clause discharged: what is assumed is the
covering clauses together with presentations of the charts `Vⱼ` and `Uⱼᵢ` by rings of the class,
and clause (3) of Stacks 0AN3 supplies the rest. -/
theorem hasBaseChangeCoverOverPullbackSnd_of_chartPresentations
    (C : ∀ (R : Type u) [CommRing R] [TopologicalSpace R] [IsTopologicalRing R]
      [IsLinearTopology R R], Prop)
    (hCwa : ∀ (R : Type u) [CommRing R] [TopologicalSpace R] [IsTopologicalRing R]
      [IsLinearTopology R R], C R → TopologicalRing.IsWeaklyAdmissible R)
    {X Y Z : FppfSheaf B S hS} (f : X ⟶ Y) (g : Z ⟶ Y)
    {J : Type (u + 1)} (V : J → FppfSheaf B S hS) (v : ∀ j, V j ⟶ Y)
    (hV : IsAffineEtaleCover B S hS V v)
    {I : J → Type (u + 1)} (U : ∀ j, I j → FppfSheaf B S hS)
    (a : ∀ j i, U j i ⟶ pullback (v j) f) (hU : ∀ j, IsAffineEtaleCover B S hS (U j) (a j))
    {K : J → Type (u + 1)} (W : ∀ j, K j → FppfSheaf B S hS)
    (b : ∀ j k, W j k ⟶ pullback (v j) g) (hW : ∀ j, IsAffineEtaleCover B S hS (W j) (b j))
    (hVch : ∀ j, IsChartOfClass B S hS C (V j))
    (hUch : ∀ j i, IsChartOfClass B S hS C (U j i)) :
    HasBaseChangeCoverOverPullbackSndOn B S hS C f g :=
  hasBaseChangeCoverOverPullbackSnd_of_chartFibreProducts B S hS C f g V v hV U a hU W b hW
    (isChartBaseChangeOf_chartPullback B S hS C hCwa f g V v hV U a hU W b hW hVch hUch)

/-- **Stacks 0GBD**, condition (3) of Stacks 0ANG for `pr₂ : X ×_Y Z ⟶ Z` at the class
`WAdm^count`, with `hAN3` discharged. Beside
`AlgebraicGeometry.FormalSpace.hasPropertyAfterSourceCover_pullback_snd_countablyIndexed`, which
carries clause (3) of Stacks 0AN3 as the hypothesis `hAN3`, this version proves that clause and
asks instead for presentations of the charts `Vⱼ` and `Uⱼᵢ` as formal spectra of countably
indexed weakly admissible rings — which is the source's own hypothesis that `X`, `Y` and `Z` be
locally countably indexed, read on the charts the proof constructs. The invariance `hiso` is
still carried, for the reason recorded in
`StacksFrontier/AlgebraicGeometry/FormalSpace/LocalPropertyBaseChange.lean`.

It carries no tag: Stacks 0GBD is
`AlgebraicGeometry.FormalSpace.hasProperty_pullback_snd_of_isLocallyCountablyIndexed`, which
needs none of the inputs taken here as hypotheses. -/
theorem hasPropertyAfterSourceCover_pullback_snd_countablyIndexed_of_charts
    (P : ∀ {R₁ R₂ : Type u} [CommRing R₁] [TopologicalSpace R₁] [IsTopologicalRing R₁]
      [CommRing R₂] [TopologicalSpace R₂] [IsTopologicalRing R₂], (R₁ →+* R₂) → Prop)
    (hP : TopologicalRing.IsStableUnderBaseChange.{u} P)
    (hiso : PropertyIsInvariantUnderTargetIsoOn.{u}
      TopologicalRing.IsCountablyWeaklyAdmissible P)
    {X Y Z : FppfSheaf B S hS} (f : X ⟶ Y) (g : Z ⟶ Y)
    {J : Type (u + 1)} (V : J → FppfSheaf B S hS) (v : ∀ j, V j ⟶ Y)
    (hV : IsAffineEtaleCover B S hS V v)
    {I : J → Type (u + 1)} (U : ∀ j, I j → FppfSheaf B S hS)
    (a : ∀ j i, U j i ⟶ pullback (v j) f) (hU : ∀ j, IsAffineEtaleCover B S hS (U j) (a j))
    {K : J → Type (u + 1)} (W : ∀ j, K j → FppfSheaf B S hS)
    (b : ∀ j k, W j k ⟶ pullback (v j) g) (hW : ∀ j, IsAffineEtaleCover B S hS (W j) (b j))
    (hVch : ∀ j, IsChartOfClass B S hS TopologicalRing.IsCountablyWeaklyAdmissible (V j))
    (hUch : ∀ j i, IsChartOfClass B S hS TopologicalRing.IsCountablyWeaklyAdmissible (U j i))
    (hf : HasPropertyOnEveryAffineEtaleDiagram B S hS
      TopologicalRing.IsCountablyWeaklyAdmissible P f) :
    HasPropertyAfterSourceCover B S hS TopologicalRing.IsCountablyWeaklyAdmissible P
      (pullback.snd f g) :=
  hasPropertyAfterSourceCover_pullback_snd_countablyIndexed B S hS P hP hiso f g V v hV U a hU
    W b hW
    (isChartBaseChangeOf_chartPullback B S hS TopologicalRing.IsCountablyWeaklyAdmissible
      (by intro R _ _ _ _ h; exact h.1) f g V v hV U a hU W b hW hVch hUch) hf

/-- The chart argument of the second half of Stacks 0GBE, in the form of condition (1) of Stacks
0ANG for the second projection, with the ring-level half of `hcover` discharged. Beside
`AlgebraicGeometry.FormalSpace.hasPropertyOnEveryAffineEtaleDiagram_pullback_snd_adicStar`, which
carries the whole of `hcover`, this version asks for the covering clauses of Stacks 0GBD and for
presentations of the charts `Vⱼ` and `Uⱼᵢ` as formal spectra of adic\* rings, and proves the
identification of the chart ring of a fibre product of charts with the completed tensor product.
The hypotheses `h31` and `hiso` are unchanged. -/
theorem hasPropertyOnEveryAffineEtaleDiagram_pullback_snd_adicStar_of_charts
    (P : ∀ {R₁ R₂ : Type u} [CommRing R₁] [TopologicalSpace R₁] [IsTopologicalRing R₁]
      [CommRing R₂] [TopologicalSpace R₂] [IsTopologicalRing R₂], (R₁ →+* R₂) → Prop)
    (hP : TopologicalRing.AdicStarPropertyIsStableUnderBaseChange.{u} P)
    (hiso : PropertyIsInvariantUnderTargetIsoOn.{u} TopologicalRing.IsAdicStar P)
    (h31 : SourceCoverImpliesEveryAffineEtaleDiagram B S hS TopologicalRing.IsAdicStar P)
    {X Y Z : FppfSheaf B S hS} (f : X ⟶ Y) (g : Z ⟶ Y)
    {J : Type (u + 1)} (V : J → FppfSheaf B S hS) (v : ∀ j, V j ⟶ Y)
    (hV : IsAffineEtaleCover B S hS V v)
    {I : J → Type (u + 1)} (U : ∀ j, I j → FppfSheaf B S hS)
    (a : ∀ j i, U j i ⟶ pullback (v j) f) (hU : ∀ j, IsAffineEtaleCover B S hS (U j) (a j))
    {K : J → Type (u + 1)} (W : ∀ j, K j → FppfSheaf B S hS)
    (b : ∀ j k, W j k ⟶ pullback (v j) g) (hW : ∀ j, IsAffineEtaleCover B S hS (W j) (b j))
    (hVch : ∀ j, IsChartOfClass B S hS TopologicalRing.IsAdicStar (V j))
    (hUch : ∀ j i, IsChartOfClass B S hS TopologicalRing.IsAdicStar (U j i))
    (hf : HasPropertyOnEveryAffineEtaleDiagram B S hS TopologicalRing.IsAdicStar P f) :
    HasPropertyOnEveryAffineEtaleDiagram B S hS TopologicalRing.IsAdicStar P
      (pullback.snd f g) :=
  hasPropertyOnEveryAffineEtaleDiagram_pullback_snd_adicStar B S hS P hP hiso h31 f g
    (hasBaseChangeCoverOverPullbackSnd_of_chartPresentations B S hS
      TopologicalRing.IsAdicStar
      (by intro R _ _ _ _ h; exact Rig.weaklyAdmissible_of_isAdicRing h.1) f g
      V v hV U a hU W b hW hVch hUch) hf

/-- The chart argument of the second half of Stacks 0GBE, condition (1) of Stacks 0ANG for the
second projection with the ring-level half of `hcover` discharged, from the source's hypothesis on
`P`.

This is `hasPropertyOnEveryAffineEtaleDiagram_pullback_snd_adicStar_of_charts` with the
hypothesis on `P` read at the source's class of rings:
`TopologicalRing.PropertyIsStableUnderBaseChangeAdicStar`, the remark's two clauses taken over
`WAdm^{adic*}` itself rather than over the class `∃ I : Ideal R, I.FG ∧ _root_.IsAdic I`; the
two hypotheses are equivalent, by `TopologicalRing.adicStarPropertyIsStableUnderBaseChange_iff`,
and the chart argument is unchanged. -/
theorem hasPropertyOnEveryAffineEtaleDiagram_pullback_snd_of_charts_stableBaseChangeAdicStar
    (P : ∀ {R₁ R₂ : Type u} [CommRing R₁] [TopologicalSpace R₁] [IsTopologicalRing R₁]
      [CommRing R₂] [TopologicalSpace R₂] [IsTopologicalRing R₂], (R₁ →+* R₂) → Prop)
    (hP : TopologicalRing.PropertyIsStableUnderBaseChangeAdicStar.{u} P)
    (hiso : PropertyIsInvariantUnderTargetIsoOn.{u} TopologicalRing.IsAdicStar P)
    (h31 : SourceCoverImpliesEveryAffineEtaleDiagram B S hS TopologicalRing.IsAdicStar P)
    {X Y Z : FppfSheaf B S hS} (f : X ⟶ Y) (g : Z ⟶ Y)
    {J : Type (u + 1)} (V : J → FppfSheaf B S hS) (v : ∀ j, V j ⟶ Y)
    (hV : IsAffineEtaleCover B S hS V v)
    {I : J → Type (u + 1)} (U : ∀ j, I j → FppfSheaf B S hS)
    (a : ∀ j i, U j i ⟶ pullback (v j) f) (hU : ∀ j, IsAffineEtaleCover B S hS (U j) (a j))
    {K : J → Type (u + 1)} (W : ∀ j, K j → FppfSheaf B S hS)
    (b : ∀ j k, W j k ⟶ pullback (v j) g) (hW : ∀ j, IsAffineEtaleCover B S hS (W j) (b j))
    (hVch : ∀ j, IsChartOfClass B S hS TopologicalRing.IsAdicStar (V j))
    (hUch : ∀ j i, IsChartOfClass B S hS TopologicalRing.IsAdicStar (U j i))
    (hf : HasPropertyOnEveryAffineEtaleDiagram B S hS TopologicalRing.IsAdicStar P f) :
    HasPropertyOnEveryAffineEtaleDiagram B S hS TopologicalRing.IsAdicStar P
      (pullback.snd f g) :=
  hasPropertyOnEveryAffineEtaleDiagram_pullback_snd_of_stableBaseChangeAdicStar B S hS P hP hiso
    h31 f g
    (hasBaseChangeCoverOverPullbackSnd_of_chartPresentations B S hS
      TopologicalRing.IsAdicStar
      (by intro R _ _ _ _ h; exact Rig.weaklyAdmissible_of_isAdicRing h.1) f g
      V v hV U a hU W b hW hVch hUch) hf

end

end AlgebraicGeometry.FormalSpace
end
