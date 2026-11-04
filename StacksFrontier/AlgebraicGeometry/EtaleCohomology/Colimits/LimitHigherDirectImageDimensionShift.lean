module

public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.BaseChangeHigher.ConnectingMapDeltaFunctor
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.Colimits.InjectiveSheafSystems
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.Colimits.LimitHigherDirectImageCocycle
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.Colimits.LimitHigherDirectImageColimit
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.Colimits.SystemPullbackDiagram
public import StacksFrontier.CategoryTheory.Limits.SystemColimit

/-!
# Higher direct images along a limit: the dimension shift

This file carries out the inductive step of the first proof of [Stacks, Tag 0EYM]. Let
`0 ⟶ (ℱ_i) ⟶ (𝒢_i) ⟶ (𝒬_i) ⟶ 0` be a short exact sequence of systems of abelian sheaves on an
inverse system of schemes `(X_i)`, with every `𝒢_i` injective, and let
`0 ⟶ ℱ ⟶ 𝒢 ⟶ 𝒬 ⟶ 0` be a short exact sequence on the limit `X` whose terms present the colimits
of the three systems, compatibly with the two maps. If `R^{p+1}g_*𝒢 = 0`, and if the colimit
assertion of [Stacks, Tag 0EYM] holds in degree `p` for the systems `(𝒢_i)` and `(𝒬_i)`, then it
holds in degree `p + 1` for `(ℱ_i)`.

The argument is the source's: in degree `p + 1` the higher direct images of `ℱ_i`, pulled back
to the limit of the bases, are the cokernels of `h_i^{-1}R^p g_{i,*}𝒢_i ⟶ h_i^{-1}R^p g_{i,*}𝒬_i`
under the connecting morphisms, the higher direct images of the injective `𝒢_i` vanishing; the
same holds for `R^{p+1}g_*ℱ` by the vanishing of `R^{p+1}g_*𝒢`; and cokernels commute with
colimits (`CategoryTheory.Limits.IsSystemColimit.of_cokernel`). What makes the colimits of the
three rows comparable is that the base change maps commute with the connecting morphisms,
`Stacks.EtaleCohomology.higherBaseChangeMapAb_comp_δ`.

## Main definitions

* `Stacks.EtaleCohomology.LimitHigherDirectImage.higherDirectImageDiagramMap` — the maps
  `h_{i'}^{-1}R^p g_{i',*}ℱ_{i'} ⟶ h_i^{-1}R^p g_{i,*}ℱ_i` of the diagram whose colimit [Stacks,
  Tag 0EYM] computes.

## Main results

* `Stacks.EtaleCohomology.LimitHigherDirectImage.isPullbackColimitPresentation_iff_isSystemColimit`
  — the colimit presentation `𝓕 = colim_i f_i^{-1}F_i` is an instance of
  `CategoryTheory.Limits.IsSystemColimit`, so that its API applies to it.
* `Stacks.EtaleCohomology.LimitHigherDirectImage.isHigherDirectImageColimit_iff_isSystemColimit`
  — the colimit assertion of [Stacks, Tag 0EYM] is an instance of
  `CategoryTheory.Limits.IsSystemColimit`, so that its API applies to it.
* `Stacks.EtaleCohomology.EtaleSheafSystem.pullbackDiagramMap_comp` — the maps of the diagram of
  inverse images of a system compose.
* `Stacks.EtaleCohomology.LimitHigherDirectImage.projectionMap_comp_δ` and
  `Stacks.EtaleCohomology.LimitHigherDirectImage.higherDirectImageDiagramMap_comp_δ` — the cocone
  and diagram maps of [Stacks, Tag 0EYM] commute with the connecting morphisms.

## References

* [Stacks Project, Tag 0EYM](https://stacks.math.columbia.edu/tag/0EYM)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits
open AlgebraicGeometry AlgebraicGeometry.Scheme

universe v u

namespace Stacks.EtaleCohomology

section PullbackDiagram

variable {I : Type v} [Preorder I] {D : Iᵒᵖ ⥤ Scheme.{u}}

private theorem coneDirectImageCompAb_hom_cocycle (c : Cone D) {i j k : Iᵒᵖ} (a : i ⟶ j)
    (b : j ⟶ k) (Y : Sheaf (smallEtaleTopology c.pt) Ab.{u + 1}) :
    (systemPushforward D Ab.{u + 1} b).map ((coneDirectImageCompAb c a).hom.app Y) ≫
        (coneDirectImageCompAb c b).hom.app Y =
      (systemPushforwardComp D Ab.{u + 1} a b).hom.app
          ((smallEtalePushforwardAb (c.π.app i)).obj Y) ≫
        (coneDirectImageCompAb c (a ≫ b)).hom.app Y := by
  have h := congrArg (fun z => NatTrans.app (Iso.hom z) Y)
    (smallEtalePushforwardComp'_assoc (c.π.app i) (D.map a) (D.map b) (c.π.app j) (c.w a).symm
      (D.map (a ≫ b)) (D.map_comp a b) (c.π.app k) (c.w b).symm (c.w (a ≫ b)).symm Ab.{u + 1})
  simp only [Iso.trans_hom, NatTrans.comp_app, Functor.isoWhiskerRight_hom,
    Functor.isoWhiskerLeft_hom, Functor.whiskerRight_app, Functor.whiskerLeft_app,
    Functor.associator_hom_app, Category.id_comp] at h
  exact h

/-- **The maps of the diagram of inverse images of a system compose**: the cocycle condition of
the system, transported to the limit through the comparisons of inverse images along the
projections. -/
theorem EtaleSheafSystem.pullbackDiagramMap_comp (F : EtaleSheafSystem D Ab.{u + 1}) (c : Cone D)
    {i j k : Iᵒᵖ} (a : i ⟶ j) (b : j ⟶ k) :
    F.pullbackDiagramMap c (i := i) (j := k) (a ≫ b) =
      F.pullbackDiagramMap c (i := j) (j := k) b ≫ F.pullbackDiagramMap c (i := i) (j := j) a := by
  rw [F.pullbackDiagramMap_eq c a, F.pullbackDiagramMap_comp_homEquiv_symm c b,
    F.pullbackDiagramMap_eq c (a ≫ b), F.transition_comp a b]
  congr 1
  simp only [Category.assoc, Functor.map_comp]
  congr 2
  rw [← (systemPushforwardComp D Ab.{u + 1} a b).hom.naturality_assoc]
  congr 1
  exact (coneDirectImageCompAb_hom_cocycle c a b _).symm

end PullbackDiagram

end Stacks.EtaleCohomology

namespace Stacks.EtaleCohomology.LimitHigherDirectImage

section Definitions

variable {I : Type v} [Preorder I] {DX DS : Iᵒᵖ ⥤ Scheme.{u}} (γ : DX ⟶ DS) (p : ℕ)
  (cX : Cone DX) (cS : Cone DS) (hcS : IsLimit cS)
  (𝓕 : Sheaf (smallEtaleTopology cX.pt) Ab.{u + 1})

/-- The map `h_{i'}^{-1}R^p g_{i',*}ℱ_{i'} ⟶ h_i^{-1}R^p g_{i,*}ℱ_i` of the diagram of
[Stacks, Tag 0EYM], for `i ⟶ j` in `Iᵒᵖ`: the comparison of inverse images along
`h_j = h_i ≫ h_{ij}` followed by the inverse image of the transition map `ψ_{ij}`. -/
def higherDirectImageDiagramMap (F : EtaleSheafSystem DX Ab.{u + 1}) {i j : Iᵒᵖ} (a : i ⟶ j) :
    (smallEtalePullbackAb (cS.π.app j)).obj
        (((smallEtalePushforwardAb (γ.app j)).rightDerived p).obj (F.obj j)) ⟶
      (smallEtalePullbackAb (cS.π.app i)).obj
        (((smallEtalePushforwardAb (γ.app i)).rightDerived p).obj (F.obj i)) :=
  (conePullbackComp cS a).inv.app
      (((smallEtalePushforwardAb (γ.app j)).rightDerived p).obj (F.obj j)) ≫
    (smallEtalePullbackAb (cS.π.app i)).map (transitionMap γ p F a)

variable {γ p cX cS hcS 𝓕}

/-- The colimit presentation `𝓕 = colim_i f_i^{-1}F_i` of
`Stacks.EtaleCohomology.LimitHigherDirectImage.IsPullbackColimitPresentation` is an instance of
`CategoryTheory.Limits.IsSystemColimit`, so that the API of the latter applies to it. -/
theorem isPullbackColimitPresentation_iff_isSystemColimit {F : EtaleSheafSystem DX Ab.{u + 1}}
    {ι : ∀ i : Iᵒᵖ, (smallEtalePullbackAb (cX.π.app i)).obj (F.obj i) ⟶ 𝓕} :
    IsPullbackColimitPresentation cX 𝓕 F ι ↔
      IsSystemColimit (fun i => (smallEtalePullbackAb (cX.π.app i)).obj (F.obj i))
        (fun {i j} a => (conePullbackComp cX a).inv.app (F.obj j) ≫
          (smallEtalePullbackAb (cX.π.app i)).map (F.map a)) 𝓕 ι := by
  simp only [IsSystemColimit, IsPullbackColimitPresentation, Category.assoc]

alias ⟨IsPullbackColimitPresentation.isSystemColimit,
  IsPullbackColimitPresentation.of_isSystemColimit⟩ :=
  isPullbackColimitPresentation_iff_isSystemColimit

/-- The colimit assertion of [Stacks, Tag 0EYM],
`Stacks.EtaleCohomology.LimitHigherDirectImage.IsHigherDirectImageColimit`, is an instance of
`CategoryTheory.Limits.IsSystemColimit` for the diagram of the maps
`Stacks.EtaleCohomology.LimitHigherDirectImage.higherDirectImageDiagramMap`, so that the API of
the latter applies to it. -/
theorem isHigherDirectImageColimit_iff_isSystemColimit {F : EtaleSheafSystem DX Ab.{u + 1}}
    {ι : ∀ i : Iᵒᵖ, (smallEtalePullbackAb (cX.π.app i)).obj (F.obj i) ⟶ 𝓕} :
    IsHigherDirectImageColimit γ p cX cS hcS 𝓕 F ι ↔
      IsSystemColimit (fun i => (smallEtalePullbackAb (cS.π.app i)).obj
          (((smallEtalePushforwardAb (γ.app i)).rightDerived p).obj (F.obj i)))
        (fun a => higherDirectImageDiagramMap γ p cS F a)
        (((smallEtalePushforwardAb (limitMorphism γ cX cS hcS)).rightDerived p).obj 𝓕)
        (projectionMap γ cX cS hcS p 𝓕 F ι) := by
  simp only [IsSystemColimit, IsHigherDirectImageColimit, higherDirectImageDiagramMap,
    Category.assoc]

alias ⟨IsHigherDirectImageColimit.isSystemColimit, IsHigherDirectImageColimit.of_isSystemColimit⟩ :=
  isHigherDirectImageColimit_iff_isSystemColimit

end Definitions

section Step

attribute [local instance] HasDerivedCategory.standard

variable {I : Type v} [Preorder I] {DX DS : Iᵒᵖ ⥤ Scheme.{u}} (γ : DX ⟶ DS) (p : ℕ)
  (cX : Cone DX) (cS : Cone DS) (hcS : IsLimit cS)

variable {F G Q : EtaleSheafSystem DX Ab.{u + 1}} (α : ∀ i, F.obj i ⟶ G.obj i)
  (β : ∀ i, G.obj i ⟶ Q.obj i) (hαβ : ∀ i, α i ≫ β i = 0)
  (hE : ∀ i, (ShortComplex.mk (α i) (β i) (hαβ i)).ShortExact)
  {𝓕 𝓖 𝓠 : Sheaf (smallEtaleTopology cX.pt) Ab.{u + 1}}
  (ιF : ∀ i, (smallEtalePullbackAb (cX.π.app i)).obj (F.obj i) ⟶ 𝓕)
  (ιG : ∀ i, (smallEtalePullbackAb (cX.π.app i)).obj (G.obj i) ⟶ 𝓖)
  (ιQ : ∀ i, (smallEtalePullbackAb (cX.π.app i)).obj (Q.obj i) ⟶ 𝓠)
  (u : 𝓕 ⟶ 𝓖) (v : 𝓖 ⟶ 𝓠) (huv : u ≫ v = 0) (hlim : (ShortComplex.mk u v huv).ShortExact)
  (hu : ∀ i, (smallEtalePullbackAb (cX.π.app i)).map (α i) ≫ ιG i = ιF i ≫ u)
  (hv : ∀ i, (smallEtalePullbackAb (cX.π.app i)).map (β i) ≫ ιQ i = ιG i ≫ v)

private theorem reassoc_chain {𝒳 : Type*} [Category* 𝒳] {o₀ o₁ o₂ o₃ o₄ o₅ : 𝒳}
    {b : o₀ ⟶ o₁} {r : o₁ ⟶ o₂} {δ : o₂ ⟶ o₃} {x : o₀ ⟶ o₄} {b' : o₄ ⟶ o₅} {r' : o₅ ⟶ o₃}
    (key : b ≫ r ≫ δ = x ≫ b' ≫ r') : (b ≫ r) ≫ δ = x ≫ (b' ≫ r') := by
  rw [Category.assoc, key]

private theorem projectionMap_eq (H : EtaleSheafSystem DX Ab.{u + 1})
    {𝓗 : Sheaf (smallEtaleTopology cX.pt) Ab.{u + 1}}
    (ιH : ∀ i, (smallEtalePullbackAb (cX.π.app i)).obj (H.obj i) ⟶ 𝓗) (q : ℕ) (i : Iᵒᵖ) :
    projectionMap γ cX cS hcS q 𝓗 H ιH i =
      (higherBaseChangeMapAb (cS.π.app i) (γ.app i) (limitMorphism γ cX cS hcS) (cX.π.app i)
          (limitMorphism_comp_π γ cX cS hcS i) q).app (H.obj i) ≫
        ((smallEtalePushforwardAb (limitMorphism γ cX cS hcS)).rightDerived q).map (ιH i) :=
  rfl

include hu hv in
/-- The map of short complexes from the inverse image of a level of a short exact sequence of
systems to the short exact sequence on the limit presenting the colimits. -/
def limitShortComplexHom (i : Iᵒᵖ) :
    (ShortComplex.mk (α i) (β i) (hαβ i)).map (smallEtalePullbackAb (cX.π.app i)) ⟶
      ShortComplex.mk u v huv where
  τ₁ := ιF i
  τ₂ := ιG i
  τ₃ := ιQ i
  comm₁₂ := (hu i).symm
  comm₂₃ := (hv i).symm

include hu hv in
private theorem projection_key (i : Iᵒᵖ) :
    (higherBaseChangeMapAb (cS.π.app i) (γ.app i) (limitMorphism γ cX cS hcS) (cX.π.app i)
          (limitMorphism_comp_π γ cX cS hcS i) p).app (ShortComplex.mk (α i) (β i) (hαβ i)).X₃ ≫
        ((smallEtalePushforwardAb (limitMorphism γ cX cS hcS)).rightDerived p).map
          (limitShortComplexHom cX α β hαβ ιF ιG ιQ u v huv hu hv i).τ₃ ≫
        (Stacks.DerivedIndexing.rightDerivedDeltaFunctorOfEnoughInjectives
          (smallEtalePushforwardAb (limitMorphism γ cX cS hcS))).δ hlim p =
      (smallEtalePullbackAb (cS.π.app i)).map
          ((Stacks.DerivedIndexing.rightDerivedDeltaFunctorOfEnoughInjectives
            (smallEtalePushforwardAb (γ.app i))).δ (hE i) p) ≫
        (higherBaseChangeMapAb (cS.π.app i) (γ.app i) (limitMorphism γ cX cS hcS) (cX.π.app i)
          (limitMorphism_comp_π γ cX cS hcS i) (p + 1)).app
            (ShortComplex.mk (α i) (β i) (hαβ i)).X₁ ≫
        ((smallEtalePushforwardAb (limitMorphism γ cX cS hcS)).rightDerived (p + 1)).map
          (limitShortComplexHom cX α β hαβ ιF ιG ιQ u v huv hu hv i).τ₁ :=
  higherBaseChangeMapAb_comp_δ (cS.π.app i) (γ.app i) (limitMorphism γ cX cS hcS)
    (cX.π.app i) (limitMorphism_comp_π γ cX cS hcS i) p (hE i) hlim
    (limitShortComplexHom cX α β hαβ ιF ιG ιQ u v huv hu hv i)

include hu hv in
/-- **The cocone maps commute with the connecting morphisms.** For the projection square of the
level `i`, the base change map followed by the maps presenting the colimits commutes with the
connecting morphism of `g_{i,*}` at the level, pulled back to the limit of the bases, and with
the connecting morphism of `g_*` on the limit. -/
theorem projectionMap_comp_δ (i : Iᵒᵖ) :
    projectionMap γ cX cS hcS p 𝓠 Q ιQ i ≫
        (Stacks.DerivedIndexing.rightDerivedDeltaFunctorOfEnoughInjectives
          (smallEtalePushforwardAb (limitMorphism γ cX cS hcS))).δ hlim p =
      (smallEtalePullbackAb (cS.π.app i)).map
          ((Stacks.DerivedIndexing.rightDerivedDeltaFunctorOfEnoughInjectives
            (smallEtalePushforwardAb (γ.app i))).δ (hE i) p) ≫
        projectionMap γ cX cS hcS (p + 1) 𝓕 F ιF i := by
  rw [projectionMap_eq, projectionMap_eq]
  exact reassoc_chain (projection_key γ p cX cS hcS α β hαβ hE ιF ιG ιQ u v huv hlim hu hv i)

private theorem transitionMap_eq' (H : EtaleSheafSystem DX Ab.{u + 1}) (q : ℕ) {i j : Iᵒᵖ}
    (a : i ⟶ j) :
    transitionMap γ q H a =
      (higherBaseChangeMapAb (DS.map a) (γ.app j) (γ.app i) (DX.map a) (transition_comm γ a)
          q).app (H.obj j) ≫
        ((smallEtalePushforwardAb (γ.app i)).rightDerived q).map (H.map a) :=
  rfl

variable {α β} in
/-- The map of short complexes from the inverse image of a level of a short exact sequence of
systems to a later level. -/
def transitionShortComplexHom
    (hα : ∀ {i j : Iᵒᵖ} (a : i ⟶ j),
      (systemPullback DX Ab.{u + 1} a).map (α j) ≫ G.map a = F.map a ≫ α i)
    (hβ : ∀ {i j : Iᵒᵖ} (a : i ⟶ j),
      (systemPullback DX Ab.{u + 1} a).map (β j) ≫ Q.map a = G.map a ≫ β i)
    {i j : Iᵒᵖ} (a : i ⟶ j) :
    (ShortComplex.mk (α j) (β j) (hαβ j)).map (systemPullback DX Ab.{u + 1} a) ⟶
      ShortComplex.mk (α i) (β i) (hαβ i) where
  τ₁ := F.map a
  τ₂ := G.map a
  τ₃ := Q.map a
  comm₁₂ := (hα a).symm
  comm₂₃ := (hβ a).symm

variable {α β} in
private theorem transition_key
    (hα : ∀ {i j : Iᵒᵖ} (a : i ⟶ j),
      (systemPullback DX Ab.{u + 1} a).map (α j) ≫ G.map a = F.map a ≫ α i)
    (hβ : ∀ {i j : Iᵒᵖ} (a : i ⟶ j),
      (systemPullback DX Ab.{u + 1} a).map (β j) ≫ Q.map a = G.map a ≫ β i)
    {i j : Iᵒᵖ} (a : i ⟶ j) :
    (higherBaseChangeMapAb (DS.map a) (γ.app j) (γ.app i) (DX.map a) (transition_comm γ a)
          p).app (ShortComplex.mk (α j) (β j) (hαβ j)).X₃ ≫
        ((smallEtalePushforwardAb (γ.app i)).rightDerived p).map
          (transitionShortComplexHom hαβ hα hβ a).τ₃ ≫
        (Stacks.DerivedIndexing.rightDerivedDeltaFunctorOfEnoughInjectives
          (smallEtalePushforwardAb (γ.app i))).δ (hE i) p =
      (smallEtalePullbackAb (DS.map a)).map
          ((Stacks.DerivedIndexing.rightDerivedDeltaFunctorOfEnoughInjectives
            (smallEtalePushforwardAb (γ.app j))).δ (hE j) p) ≫
        (higherBaseChangeMapAb (DS.map a) (γ.app j) (γ.app i) (DX.map a) (transition_comm γ a)
          (p + 1)).app (ShortComplex.mk (α j) (β j) (hαβ j)).X₁ ≫
        ((smallEtalePushforwardAb (γ.app i)).rightDerived (p + 1)).map
          (transitionShortComplexHom hαβ hα hβ a).τ₁ :=
  higherBaseChangeMapAb_comp_δ (DS.map a) (γ.app j) (γ.app i) (DX.map a) (transition_comm γ a) p
    (hE j) (hE i) (transitionShortComplexHom hαβ hα hβ a)

private theorem diagram_chain {𝒴 𝒳 : Type*} [Category* 𝒴] [Category* 𝒳] (L : 𝒴 ⥤ 𝒳)
    {y₀ y₁ y₂ y₃ y₄ y₅ : 𝒴} {x₀ x₁ : 𝒳}
    {c₀ : x₀ ⟶ L.obj y₀} {b : y₀ ⟶ y₁} {r : y₁ ⟶ y₂} {δ : y₂ ⟶ y₃}
    {δ' : x₀ ⟶ x₁} {c₁ : x₁ ⟶ L.obj y₄} {M : y₀ ⟶ y₄} {b' : y₄ ⟶ y₅} {r' : y₅ ⟶ y₃}
    (key : b ≫ r ≫ δ = M ≫ b' ≫ r') (hn : c₀ ≫ L.map M = δ' ≫ c₁) :
    (c₀ ≫ L.map (b ≫ r)) ≫ L.map δ = δ' ≫ (c₁ ≫ L.map (b' ≫ r')) := by
  rw [Category.assoc, ← L.map_comp, Category.assoc, key, L.map_comp, ← Category.assoc, hn,
    Category.assoc]

private theorem higherDirectImageDiagramMap_eq (H : EtaleSheafSystem DX Ab.{u + 1}) (q : ℕ)
    {i j : Iᵒᵖ} (a : i ⟶ j) :
    higherDirectImageDiagramMap γ q cS H a =
      (conePullbackComp cS a).inv.app
          (((smallEtalePushforwardAb (γ.app j)).rightDerived q).obj (H.obj j)) ≫
        (smallEtalePullbackAb (cS.π.app i)).map (transitionMap γ q H a) :=
  rfl

variable {α β} in
/-- **The transition maps commute with the connecting morphisms**, for a short exact sequence of
systems: the maps of the diagram of [Stacks, Tag 0EYM] in degrees `p` and `p + 1` commute with
the connecting morphisms of the higher direct images at the levels, pulled back to the limit of
the bases. -/
theorem higherDirectImageDiagramMap_comp_δ
    (hα : ∀ {i j : Iᵒᵖ} (a : i ⟶ j),
      (systemPullback DX Ab.{u + 1} a).map (α j) ≫ G.map a = F.map a ≫ α i)
    (hβ : ∀ {i j : Iᵒᵖ} (a : i ⟶ j),
      (systemPullback DX Ab.{u + 1} a).map (β j) ≫ Q.map a = G.map a ≫ β i)
    {i j : Iᵒᵖ} (a : i ⟶ j) :
    higherDirectImageDiagramMap γ p cS Q (i := i) (j := j) a ≫
        (smallEtalePullbackAb (cS.π.app i)).map
          ((Stacks.DerivedIndexing.rightDerivedDeltaFunctorOfEnoughInjectives
            (smallEtalePushforwardAb (γ.app i))).δ (hE i) p) =
      (smallEtalePullbackAb (cS.π.app j)).map
          ((Stacks.DerivedIndexing.rightDerivedDeltaFunctorOfEnoughInjectives
            (smallEtalePushforwardAb (γ.app j))).δ (hE j) p) ≫
        higherDirectImageDiagramMap γ (p + 1) cS F (i := i) (j := j) a := by
  rw [higherDirectImageDiagramMap_eq, higherDirectImageDiagramMap_eq, transitionMap_eq',
    transitionMap_eq']
  exact diagram_chain (smallEtalePullbackAb (cS.π.app i))
    (transition_key γ p hαβ hE hα hβ a)
    ((conePullbackComp cS a).inv.naturality
      ((Stacks.DerivedIndexing.rightDerivedDeltaFunctorOfEnoughInjectives
        (smallEtalePushforwardAb (γ.app j))).δ (hE j) p)).symm

end Step

end Stacks.EtaleCohomology.LimitHigherDirectImage
