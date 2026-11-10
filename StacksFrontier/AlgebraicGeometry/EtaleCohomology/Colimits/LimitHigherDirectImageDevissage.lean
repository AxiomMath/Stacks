module

public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.BaseChangeHigher.ConnectingMapPasting
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.Colimits.LimitHigherDirectImageColimit
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.Colimits.SmallEtaleColimitPresentationAdjointForm
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.Colimits.SmallEtaleDevissage
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.Colimits.SmallEtaleInjectiveSystems
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.Colimits.SmallEtalePresentedSystem

/-!
# The dimension shift of Stacks 0EYM

Let `(X_i, f_{i'i})` and `(S_i, h_{i'i})` be inverse systems of schemes, `g_i : X_i ⟶ S_i` a
morphism of the first into the second, `cX` a cone over the first and `cS` a limit cone over the
second, and `g : X ⟶ S` the limit morphism. For a presented system `E` — a system of abelian
sheaves `(F_i)` on the `X_i` in the sense of [Stacks, Tag 0EZL] with a sheaf
`𝓕 = colim f_i^{-1}F_i` on `X` — and a degree `p`, `IsHigherDirectImageColimit` is the colimit
assertion `R^p g_* 𝓕 = colim_i h_i^{-1} R^p g_{i, *} F_i` of [Stacks, Tag 0EYM].

This file carries out the dimension shift of the source's first proof: if the assertion holds in
degree `p` for the middle and the quotient system of a dévissage
`0 ⟶ E ⟶ G ⟶ Q ⟶ 0` of `E` into a system of injective sheaves, and if `R^{p+1}` of the middle
system vanishes at every level and on the limit, then the assertion holds in degree `p + 1` for
`E`.

The argument is the source's "by the long exact sequence of cohomology", made explicit. On the
limit, `R^p g_* 𝓠 ⟶ R^{p+1} g_* 𝓕` is the cokernel of `R^p g_* 𝓖 ⟶ R^p g_* 𝓠`. At a level the
connecting morphism `h_i^{-1}R^p g_{i, *}Q_i ⟶ h_i^{-1}R^{p+1} g_{i, *}F_i` is an epimorphism
killing the image of `G_i`. The two compatibilities that make the argument go through are
`Stacks.EtaleCohomology.higherBaseChangeδSource_comp_map` — the cocone maps commute with the two
connecting morphisms — and `Stacks.EtaleCohomology.higherBaseChangeδSource_paste` — the
connecting morphisms at the levels commute with the transition maps.

## Main results

* `Stacks.EtaleCohomology.LimitHigherDirectImage.devissageLegHom`,
  `Stacks.EtaleCohomology.LimitHigherDirectImage.devissageTransitionHom` — the legs and the
  transitions of a dévissage as morphisms of short exact sequences.
* `Stacks.EtaleCohomology.LimitHigherDirectImage.isHigherDirectImageColimit_succ_of_devissage` —
  **the dimension shift.**

## Implementation notes

The presented systems are those of `Stacks.EtaleCohomology.SmallEtaleLimitCohomology`, whose
legs are maps out of the constructed inverse image; `transportLeg` reads them as maps out of
`Stacks.EtaleCohomology.smallEtalePullbackAb`, which is what the maps of [Stacks, Tag 0EYM] are
built from.

## References

* [Stacks Project, Tag 0EYM](https://stacks.math.columbia.edu/tag/0EYM)
* [Stacks Project, Tag 0EXZ](https://stacks.math.columbia.edu/tag/0EXZ)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits
open AlgebraicGeometry AlgebraicGeometry.Scheme
open Stacks.EtaleCohomology.SmallEtaleLimitCohomology

universe v u

namespace Stacks.EtaleCohomology

-- forced by `Stacks.EtaleCohomology.higherBaseChangeMapAb`
-- (`BaseChangeHigher/BaseChangeCondition.lean:154`)
attribute [local instance] HasDerivedCategory.standard

/-- **`higherBaseChangeδSource_paste` with the composite base named.** The composite `u₂ ≫ u₁`
is given as a morphism `u` together with an equation, and the composition comparison of the
inverse images is `Stacks.EtaleCohomology.smallEtalePullbackAbComp'`. -/
theorem higherBaseChangeδSource_paste_named {X₀ X₁ S₀ S₁ S₂ : Scheme.{u}} (g₀ : X₀ ⟶ S₀)
    (g₁ : X₁ ⟶ S₁) (u₁ : S₁ ⟶ S₀) (v₁ : X₁ ⟶ X₀) (w₁ : g₁ ≫ u₁ = v₁ ≫ g₀) (u₂ : S₂ ⟶ S₁)
    (u : S₂ ⟶ S₀) (hu : u = u₂ ≫ u₁) (q : ℕ)
    {E : ShortComplex (Sheaf (smallEtaleTopology X₀) Ab.{u + 1})} (hE : E.ShortExact)
    {E' : ShortComplex (Sheaf (smallEtaleTopology X₁) Ab.{u + 1})} (hE' : E'.ShortExact)
    (σ : E.map (smallEtalePullbackAb v₁) ⟶ E') :
    (smallEtalePullbackAbComp' u₂ u₁ u hu).inv.app
          (((smallEtalePushforwardAb g₀).rightDerived q).obj E.X₃) ≫
        (smallEtalePullbackAb u₂).map ((higherBaseChangeMapAb u₁ g₀ g₁ v₁ w₁ q).app E.X₃ ≫
          ((smallEtalePushforwardAb g₁).rightDerived q).map σ.τ₃) ≫
        higherBaseChangeδSource u₂ g₁ q hE' =
      higherBaseChangeδSource u g₀ q hE ≫
        (smallEtalePullbackAbComp' u₂ u₁ u hu).inv.app
          (((smallEtalePushforwardAb g₀).rightDerived (q + 1)).obj E.X₁) ≫
        (smallEtalePullbackAb u₂).map ((higherBaseChangeMapAb u₁ g₀ g₁ v₁ w₁ (q + 1)).app E.X₁ ≫
          ((smallEtalePushforwardAb g₁).rightDerived (q + 1)).map σ.τ₁) := by
  subst hu
  simpa [smallEtalePullbackAbComp'] using
    higherBaseChangeδSource_paste g₀ g₁ u₁ v₁ w₁ u₂ q hE hE' σ

namespace LimitHigherDirectImage

variable {I : Type v} [Preorder I] {DX DS : Iᵒᵖ ⥤ Scheme.{u}} (γ : DX ⟶ DS)
  [∀ i : Iᵒᵖ, HasSheafify (smallEtaleTopology (DX.obj i)) AddCommGrpCat.{u + 1}]
  [∀ i : Iᵒᵖ, HasExt.{u + 1} (Sheaf (smallEtaleTopology (DX.obj i)) AddCommGrpCat.{u + 1})]
  (cX : Cone DX) [HasSheafify (smallEtaleTopology cX.pt) AddCommGrpCat.{u + 1}]
  [HasExt.{u + 1} (Sheaf (smallEtaleTopology cX.pt) AddCommGrpCat.{u + 1})]
  (cS : Cone DS) (hcS : IsLimit cS)

/-! ### The legs and the transitions of a dévissage -/

section Devissage

variable {cX} {E : PresentedSystem (c := cX) IsColimitPresentation} (d : Devissage E)

/-- The legs of a dévissage, read out of `smallEtalePullbackAb`, form a morphism from the inverse
image of the short exact sequence at a level to the short exact sequence on the limit. -/
def devissageLegHom (i : Iᵒᵖ) :
    (d.S i).map (smallEtalePullbackAb (cX.π.app i)) ⟶ d.T where
  τ₁ := transportLeg E.sys E.sheaf E.ι i
  τ₂ := transportLeg d.mid.sys d.mid.sheaf d.mid.ι i
  τ₃ := transportLeg d.quot.sys d.quot.sheaf d.quot.ι i
  comm₁₂ :=
    (Category.assoc _ _ _).trans ((congrArg
      (fun z => (inverseImageIsoPullbackAb (conePi cX i)).hom.app (E.sys.obj i) ≫ z)
      (d.ι_f i).symm).trans ((Category.assoc _ _ _).symm.trans ((congrArg
        (fun z => z ≫ d.mid.ι i)
        ((inverseImageIsoPullbackAb (conePi cX i)).hom.naturality (d.f i)).symm).trans
        (Category.assoc _ _ _))))
  comm₂₃ :=
    (Category.assoc _ _ _).trans ((congrArg
      (fun z => (inverseImageIsoPullbackAb (conePi cX i)).hom.app (d.mid.sys.obj i) ≫ z)
      (d.ι_g i).symm).trans ((Category.assoc _ _ _).symm.trans ((congrArg
        (fun z => z ≫ d.quot.ι i)
        ((inverseImageIsoPullbackAb (conePi cX i)).hom.naturality (d.g i)).symm).trans
        (Category.assoc _ _ _))))

omit [∀ i : Iᵒᵖ, HasExt.{u + 1} (Sheaf (smallEtaleTopology (DX.obj i)) AddCommGrpCat.{u + 1})] in
/-- A morphism of systems in the vocabulary of `systemTransitionMap`, read in the vocabulary of
the transition maps of the systems themselves. -/
theorem map_comp_of_systemTransitionMap {F F' : EtaleSheafSystem DX AddCommGrpCat.{u + 1}}
    {i j : Iᵒᵖ} (a : i ⟶ j) (α : F.obj j ⟶ F'.obj j) (β : F.obj i ⟶ F'.obj i)
    (h : (etaleAbelianInverseImage.{u, u + 1} (DX.map a)).map α ≫ systemTransitionMap F' a =
      systemTransitionMap F a ≫ β) :
    (systemPullback DX AddCommGrpCat.{u + 1} a).map α ≫ F'.map a = F.map a ≫ β := by
  rw [← cancel_epi ((systemPullbackIsoInverseImage DX a).inv.app (F.obj j)), ← Category.assoc,
    ← (systemPullbackIsoInverseImage DX a).inv.naturality α]
  exact h

/-- The transitions of a dévissage form a morphism from the inverse image of the short exact
sequence at a level to the short exact sequence at a later level. -/
def devissageTransitionHom {i j : Iᵒᵖ} (a : i ⟶ j) :
    (d.S j).map (smallEtalePullbackAb (DX.map a)) ⟶ d.S i where
  τ₁ := E.sys.map a
  τ₂ := d.mid.sys.map a
  τ₃ := d.quot.sys.map a
  comm₁₂ := (map_comp_of_systemTransitionMap a (d.f j) (d.f i) (d.map_f a)).symm
  comm₂₃ := (map_comp_of_systemTransitionMap a (d.g j) (d.g i) (d.map_g a)).symm

end Devissage

/-! ### The connecting morphisms of a dévissage -/

section Connecting

variable {cX} {E : PresentedSystem (c := cX) IsColimitPresentation} (d : Devissage E) (p : ℕ)

/-- **The connecting morphisms at the levels commute with the transition maps** of the
higher direct image systems of the quotient and of the system itself. -/
theorem devissage_δSource_transition {i j : Iᵒᵖ} (a : i ⟶ j) :
    (conePullbackComp cS a).inv.app
          (((smallEtalePushforwardAb (γ.app j)).rightDerived p).obj (d.quot.sys.obj j)) ≫
        (smallEtalePullbackAb (cS.π.app i)).map (transitionMap γ p d.quot.sys a) ≫
        higherBaseChangeδSource (cS.π.app i) (γ.app i) p (d.shortExact i) =
      higherBaseChangeδSource (cS.π.app j) (γ.app j) p (d.shortExact j) ≫
        (conePullbackComp cS a).inv.app
          (((smallEtalePushforwardAb (γ.app j)).rightDerived (p + 1)).obj (E.sys.obj j)) ≫
        (smallEtalePullbackAb (cS.π.app i)).map (transitionMap γ (p + 1) E.sys a) := by
  rw [conePullbackComp_eq]
  exact higherBaseChangeδSource_paste_named (γ.app j) (γ.app i) (DS.map a)
    (DX.map a) (transition_comm γ a) (cS.π.app i) (cS.π.app j) (cS.w a).symm p
    (d.shortExact j) (d.shortExact i) (devissageTransitionHom d a)

/-- **The cocone maps commute with the connecting morphisms** at the levels and on the limit. -/
theorem devissage_δSource_projection (i : Iᵒᵖ) :
    higherBaseChangeδSource (cS.π.app i) (γ.app i) p (d.shortExact i) ≫
        projectionMap γ cX cS hcS (p + 1) E.sheaf E.sys (transportLeg E.sys E.sheaf E.ι) i =
      projectionMap γ cX cS hcS p d.quot.sheaf d.quot.sys
          (transportLeg d.quot.sys d.quot.sheaf d.quot.ι) i ≫
        directImageTriangleδ (limitMorphism γ cX cS hcS) p d.shortExact' :=
  higherBaseChangeδSource_comp_map (cS.π.app i) (γ.app i) (limitMorphism γ cX cS hcS)
    (cX.π.app i) (limitMorphism_comp_π γ cX cS hcS i) p (d.shortExact i) d.shortExact'
    (devissageLegHom d i)

/-- The connecting morphism at a level kills the image of the middle system. -/
theorem devissage_map_g_comp_δSource (i : Iᵒᵖ) :
    (smallEtalePullbackAb (cS.π.app i)).map
        (((smallEtalePushforwardAb (γ.app i)).rightDerived p).map (d.g i)) ≫
      higherBaseChangeδSource (cS.π.app i) (γ.app i) p (d.shortExact i) = 0 :=
  higherBaseChangeSource_map_g_comp_δSource (cS.π.app i) (γ.app i) p (d.shortExact i)

end Connecting

/-! ### The dimension shift -/

/-- **The dimension shift of [Stacks, Tag 0EYM].** Let `E` be a presented system with a
dévissage `0 ⟶ E ⟶ G ⟶ Q ⟶ 0`. If the colimit assertion holds in degree `p` for `G` and for
`Q`, and if `R^{p+1}` of `G` vanishes at every level and on the limit, then the colimit assertion
holds in degree `p + 1` for `E`. -/
theorem isHigherDirectImageColimit_succ_of_devissage
    {E : PresentedSystem (c := cX) IsColimitPresentation} (d : Devissage E) (p : ℕ)
    (hmid : IsHigherDirectImageColimit γ p cX cS hcS d.mid.sheaf d.mid.sys
      (transportLeg d.mid.sys d.mid.sheaf d.mid.ι))
    (hquot : IsHigherDirectImageColimit γ p cX cS hcS d.quot.sheaf d.quot.sys
      (transportLeg d.quot.sys d.quot.sheaf d.quot.ι))
    (hvan : IsZero (((smallEtalePushforwardAb (limitMorphism γ cX cS hcS)).rightDerived
      (p + 1)).obj d.mid.sheaf))
    (hlev : ∀ i : Iᵒᵖ, IsZero (((smallEtalePushforwardAb (γ.app i)).rightDerived (p + 1)).obj
      (d.mid.sys.obj i))) :
    IsHigherDirectImageColimit γ (p + 1) cX cS hcS E.sheaf E.sys
      (transportLeg E.sys E.sheaf E.ι) := by
  intro 𝒢 τ hτ
  have hDepi : ∀ i : Iᵒᵖ, Epi (higherBaseChangeδSource (cS.π.app i) (γ.app i) p
      (d.shortExact i)) := fun i =>
    epi_higherBaseChangeδSource (cS.π.app i) (γ.app i) p (d.shortExact i)
      (Functor.map_isZero (smallEtalePullbackAb (cS.π.app i)) (hlev i))
  have hσ : ∀ {i j : Iᵒᵖ} (a : i ⟶ j),
      (conePullbackComp cS a).inv.app
          (((smallEtalePushforwardAb (γ.app j)).rightDerived p).obj (d.quot.sys.obj j)) ≫
        (smallEtalePullbackAb (cS.π.app i)).map (transitionMap γ p d.quot.sys a) ≫
          higherBaseChangeδSource (cS.π.app i) (γ.app i) p (d.shortExact i) ≫ τ i =
      higherBaseChangeδSource (cS.π.app j) (γ.app j) p (d.shortExact j) ≫ τ j := by
    intro i j a
    have h := congrArg (fun z => z ≫ τ i) (devissage_δSource_transition γ cS d p a)
    simp only [Category.assoc] at h
    rw [h, hτ a]
  obtain ⟨χ', hχ', huq⟩ := hquot 𝒢
    (fun i => higherBaseChangeδSource (cS.π.app i) (γ.app i) p (d.shortExact i) ≫ τ i) hσ
  have hkill : ((smallEtalePushforwardAb (limitMorphism γ cX cS hcS)).rightDerived p).map d.ψ ≫
      χ' = 0 := by
    obtain ⟨χ₀, -, hu₀⟩ := hmid 𝒢 (fun _ => 0) (fun _ => by simp)
    refine (hu₀ _ fun i => ?_).trans (hu₀ 0 fun _ => comp_zero).symm
    have hnat := projectionMap_naturality γ cX cS hcS p d.mid.sheaf
      (transportLeg d.mid.sys d.mid.sheaf d.mid.ι) (transportLeg d.quot.sys d.quot.sheaf d.quot.ι)
      d.g d.ψ (fun i => ((devissageLegHom d i).comm₂₃).symm) i
    rw [← Category.assoc, ← hnat, Category.assoc, hχ' i, ← Category.assoc,
      devissage_map_g_comp_δSource γ cS d p i, zero_comp]
  have hex := exact_directImage_map_g_δ (limitMorphism γ cX cS hcS) p d.shortExact'
  have hepi := epi_directImageTriangleδ (limitMorphism γ cX cS hcS) p d.shortExact' hvan
  have hcok := hex.gIsCokernel
  have hχ := hcok.fac (CokernelCofork.ofπ χ' hkill) WalkingParallelPair.one
  have hdesc := fun i => (congrArg (fun z => projectionMap γ cX cS hcS p d.quot.sheaf d.quot.sys
    (transportLeg d.quot.sys d.quot.sheaf d.quot.ι) i ≫ z) hχ).trans (hχ' i)
  refine ⟨hcok.desc (CokernelCofork.ofπ χ' hkill), fun i => ?_, fun χ₂ hχ₂ => ?_⟩
  · rw [← cancel_epi (higherBaseChangeδSource (cS.π.app i) (γ.app i) p (d.shortExact i)),
      ← Category.assoc, devissage_δSource_projection γ cS hcS d p i, Category.assoc]
    exact hdesc i
  · rw [← cancel_epi (directImageTriangleδ (limitMorphism γ cX cS hcS) p d.shortExact')]
    refine (huq _ fun i => ?_).trans (huq _ hdesc).symm
    rw [← Category.assoc, ← devissage_δSource_projection γ cS hcS d p i, Category.assoc,
      hχ₂ i]

/-- **The dimension shift of [Stacks, Tag 0EYM], run in every degree.** If the colimit assertion
holds in degree `0` for every presented system, and if the higher direct images along `g` of the
sheaf presenting a system of injective sheaves vanish in positive degrees, then the colimit
assertion holds in every degree for every presented system.

The dévissage is [Stacks, Tag 0EXZ] on the small étale sites,
`Stacks.EtaleCohomology.SmallEtaleLimitCohomology.hasPointwiseInjectiveEmbeddings`, and the
vanishing at the levels is that of the higher right derived functors on injective objects. -/
theorem isHigherDirectImageColimit_of_degreeZero_of_vanishing [IsDirected I (· ≤ ·)]
    [Nonempty I] [UnivLE.{v, u + 1}]
    (H0 : ∀ E : PresentedSystem (c := cX) IsColimitPresentation,
      IsHigherDirectImageColimit γ 0 cX cS hcS E.sheaf E.sys (transportLeg E.sys E.sheaf E.ι))
    (HV : ∀ E : PresentedSystem (c := cX) IsColimitPresentation,
      (∀ i : Iᵒᵖ, Injective (E.sys.obj i)) → ∀ q : ℕ,
        IsZero (((smallEtalePushforwardAb (limitMorphism γ cX cS hcS)).rightDerived (q + 1)).obj
          E.sheaf))
    (p : ℕ) (E : PresentedSystem (c := cX) IsColimitPresentation) :
    IsHigherDirectImageColimit γ p cX cS hcS E.sheaf E.sys (transportLeg E.sys E.sheaf E.ι) := by
  induction p generalizing E with
  | zero => exact H0 E
  | succ p ih =>
    obtain ⟨d⟩ := nonempty_devissage (hasPointwiseInjectiveEmbeddings DX) E
    exact isHigherDirectImageColimit_succ_of_devissage γ cX cS hcS d p (ih d.mid) (ih d.quot)
      (HV d.mid d.injective p) (fun i =>
        have := d.injective i
        (smallEtalePushforwardAb (γ.app i)).isZero_rightDerived_obj_injective_succ p _)

end LimitHigherDirectImage

end Stacks.EtaleCohomology

end
