module

public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.DerivedLowerShriek.CompositionIsoAssociativity
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.DerivedLowerShriek.OpenImmersionBaseChange

import StacksCore.Tactic.StacksAttribute

/-!
# The isomorphisms of [Stacks, Tag 0F7J] are independent of the compactification of `g`

Let `f : X ⟶ Y` and `g : Y ⟶ Z` be separated morphisms of finite type of quasi-compact and
quasi-separated schemes. The isomorphism `R(g ∘ f)_! ≅ Rg_! ∘ Rf_!` of [Stacks, Tag 0F7J]
(`Stacks.EtaleCohomology.derivedLowerShriekCompIso`) is built from a compactification of `g`;
along the comparisons of [Stacks, Tag 0F7I] it does not depend on it. This is the part of the
proof of [Stacks, Tag 0F7J] which shows independence of the compactification `Ȳ` of `Y`.

## Main results

* `Stacks.EtaleCohomology.derivedLowerShriekCompIso_hom_app_of_hom`: along a morphism of
  compactifications of `g`.
* `Stacks.EtaleCohomology.derivedLowerShriekCompIso_hom_app_second`: for two arbitrary
  compactifications of `g`.
* `Stacks.EtaleCohomology.derivedLowerShriekCompIso_assoc`: **Stacks 0F7K**, the associativity of
  these isomorphisms.
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits
open AlgebraicGeometry AlgebraicGeometry.Scheme

universe u

/-! ### The compactifications of the comparison along a morphism of compactifications of `g` -/

namespace AlgebraicGeometry.CompactificationOf.SecondSlot

variable {X Y Z : Scheme.{u}} {f : X ⟶ Y} {g : Y ⟶ Z} {jG jG' : CompactificationOf (Over.mk g)}
  (ψ : jG ⟶ jG') (jX : CompactificationOf (Over.mk (f ≫ jG.immersion)))

/-- `X ⟶ X̄ ⟶ Ȳ ⟶ Ȳ'`, through `ψ̄`, is `X ⟶ Y ⟶ Ȳ'`. -/
lemma immersion_toBase_map :
    jX.immersion ≫ (jX.toBase ≫ Hom.map ψ) = f ≫ jG'.immersion :=
  (Category.assoc _ _ _).symm.trans ((eq_whisker (immersion_toBase jX) _).trans
    ((Category.assoc _ _ _).trans (whisker_eq f (immersion_comp_map ψ))))

/-- `X̄` as a compactification of `X` over `Ȳ'`, through `ψ̄ : Ȳ ⟶ Ȳ'`. -/
abbrev pushX : CompactificationOf (Over.mk (f ≫ jG'.immersion)) :=
  ofFactor jX.immersion (jX.toBase ≫ Hom.map ψ) (f ≫ jG'.immersion) (immersion_toBase_map ψ jX)

/-- The morphism `X̄ ×_Ȳ Y ⟶ X̄ ×_Ȳ' Y`. -/
abbrev rmap : (restrictBase jG jX).space ⟶ (restrictBase jG' (pushX ψ jX)).space :=
  pullback.lift (restrictBaseι jG jX) (pullback.snd jX.toBase jG.immersion)
    ((Category.assoc _ _ _).symm.trans ((eq_whisker pullback.condition _).trans
      ((Category.assoc _ _ _).trans (whisker_eq _ (immersion_comp_map ψ)))))

/-- `rmap ψ jX` commutes with the projections to `X̄`. -/
lemma rmap_fst : rmap ψ jX ≫ restrictBaseι jG' (pushX ψ jX) = restrictBaseι jG jX :=
  pullback.lift_fst _ _ _

/-- `rmap ψ jX` commutes with the projections to `Y`. -/
lemma rmap_snd : rmap ψ jX ≫ (restrictBase jG' (pushX ψ jX)).toBase =
    (restrictBase jG jX).toBase :=
  pullback.lift_snd _ _ _

/-- `rmap ψ jX` commutes with the open immersions of `X`. -/
lemma immersion_rmap :
    (restrictBase jG jX).immersion ≫ rmap ψ jX = (restrictBase jG' (pushX ψ jX)).immersion := by
  refine pullback.hom_ext ?_ ?_
  · exact (Category.assoc _ _ _).trans ((whisker_eq _ (rmap_fst ψ jX)).trans
      ((restrictBase_immersion_restrictBaseι jG jX).trans
        (restrictBase_immersion_restrictBaseι jG' (pushX ψ jX)).symm))
  · exact (Category.assoc _ _ _).trans ((whisker_eq _ (rmap_snd ψ jX)).trans
      ((baseChangeImmersion_snd (isPullback_id_comp_immersion jG) jX).trans
        (baseChangeImmersion_snd (isPullback_id_comp_immersion jG') (pushX ψ jX)).symm))

/-- The comparison `X̄ ×_Ȳ Y ⟶ X̄ ×_Ȳ' Y` of compactifications of `f`. -/
def r : restrictBase jG jX ⟶ restrictBase jG' (pushX ψ jX) :=
  homOfSpaceMap _ _ (rmap ψ jX) (immersion_rmap ψ jX) (rmap_snd ψ jX)

include ψ in
/-- The structure morphism `X̄ ⟶ Ȳ`, from the ambient scheme of `overBar jG' (pushX ψ jX)`. -/
abbrev fbar' : (overBar jG' (pushX ψ jX)).space ⟶ jG.space := jX.toBase

/-- `fbar' ψ jX` is proper, being the structure morphism of `jX`. -/
instance isProper_fbar' : IsProper (fbar' ψ jX) := (inferInstance : IsProper jX.toBase)

/-- `X̄`, with the open immersion of `X̄ ×_Ȳ' Y`, as a compactification of `X` over `Ȳ`. -/
abbrev k₂ : CompactificationOf (Over.mk (f ≫ jG.immersion)) :=
  ofFactor (overBar jG' (pushX ψ jX)).immersion (fbar' ψ jX) (f ≫ jG.immersion)
    ((eq_whisker (restrictBase_immersion_restrictBaseι jG' (pushX ψ jX)) _).trans
      (immersion_toBase jX))

/-- The comparison `overBar jG jX ⟶ k₂` (the identity of `X̄`). -/
def c₀' : overBar jG jX ⟶ k₂ ψ jX :=
  homOfSpaceMap _ _ (𝟙 _)
    ((Category.comp_id _).trans ((restrictBase_immersion_restrictBaseι jG jX).trans
      (restrictBase_immersion_restrictBaseι jG' (pushX ψ jX)).symm))
    (Category.id_comp _)

/-- `overBar jG jX` read over `Ȳ'`. -/
abbrev k₁ : CompactificationOf (Over.mk (f ≫ jG'.immersion)) :=
  ofFactor (overBar jG jX).immersion ((overBar jG jX).toBase ≫ Hom.map ψ) (f ≫ jG'.immersion)
    ((eq_whisker (restrictBase_immersion_restrictBaseι jG jX) _).trans
      (immersion_toBase_map ψ jX))

/-- The comparison `k₁ ⟶ overBar jG' (pushX ψ jX)` over `Ȳ'`, read from `c₀'` over `Ȳ`. -/
abbrev c₀ : k₁ ψ jX ⟶ overBar jG' (pushX ψ jX) :=
  ofFactorHom (Hom.map ψ) (f ≫ jG'.immersion) (c₀' ψ jX)
    ((overBar jG jX).toBase ≫ Hom.map ψ) rfl ((k₂ ψ jX).toBase ≫ Hom.map ψ) rfl
    (immersion_toBase (k₁ ψ jX)) (immersion_toBase (overBar jG' (pushX ψ jX)))

include ψ in
/-- The structure morphism `X̄ ⟶ Z` of `compOver jG jX`, from the ambient scheme of `k₁`. -/
abbrev bbar : (k₁ ψ jX).space ⟶ Z := jX.toBase ≫ jG.toBase

/-- `bbar ψ jX` is proper, as a composite of proper morphisms. -/
instance isProper_bbar : IsProper (bbar ψ jX) := (inferInstance : IsProper (jX.toBase ≫ jG.toBase))

/-- `X̄ ⟶ Ȳ ⟶ Z` is the structure morphism `X̄ ⟶ Ȳ'` of `k₁` followed by `Ȳ' ⟶ Z`. -/
lemma toBase_comp_map : bbar ψ jX = (k₁ ψ jX).toBase ≫ jG'.toBase :=
  (whisker_eq _ (map_comp_toBase ψ).symm).trans (Category.assoc _ _ _).symm

/-- The comparison `compOver jG jX ⟶ compOver jG' (pushX ψ jX)` over `Z` (the identity of `X̄`),
read from `c₀` over `Ȳ'`. -/
abbrev c : compOver jG jX ⟶ compOver jG' (pushX ψ jX) :=
  ofFactorHom jG'.toBase (f ≫ g) (c₀ ψ jX) (bbar ψ jX) (toBase_comp_map ψ jX)
    ((overBar jG' (pushX ψ jX)).toBase ≫ jG'.toBase) rfl (immersion_toBase (compOver jG jX))
    (immersion_toBase (compOver jG' (pushX ψ jX)))

end AlgebraicGeometry.CompactificationOf.SecondSlot

namespace Stacks.EtaleCohomology

attribute [local instance] HasDerivedCategory.standard

variable (Λ : Type) [Ring Λ]

/-! ### The unit `𝟭 ⟶ R(𝟙_Y)_*` -/

section Unit

variable (Y : Scheme.{u})

/-- `R(𝟙_Y)_*` is fully faithful, being isomorphic to the identity. -/
def etaleModuleDerivedDirectImageIdFullyFaithful :
    (etaleModuleDerivedDirectImage.{u, 0} Λ (𝟙 Y)).FullyFaithful :=
  (Functor.FullyFaithful.id _).ofIso
    (Functor.rightDerivedFunctorPlusIdIsoOf (etaleModuleDirectImage.{u, 0} Λ (𝟙 Y))
      (Functor.sheafPushforwardContinuousId' (smallEtaleBaseChangeId Y) _ _ :
        etaleModuleDirectImage.{u, 0} Λ (𝟙 Y) ≅ 𝟭 _)).symm

/-- The unit `N ⟶ R(𝟙_Y)_* N`, characterized by `R(𝟙_Y)_*` of it being the composition
isomorphism `R(𝟙_Y)_* ≅ R(𝟙_Y)_* ∘ R(𝟙_Y)_*`. -/
def etaleModuleDerivedDirectImageIdUnit :
    𝟭 (DerivedCategory.Plus (EtaleModules.{u, 0} Λ Y)) ⟶
      etaleModuleDerivedDirectImage.{u, 0} Λ (𝟙 Y) where
  app N := (etaleModuleDerivedDirectImageIdFullyFaithful Λ Y).preimage
    ((etaleModuleDerivedDirectImageComp.{u, 0} Λ (𝟙 Y) (𝟙 Y) (𝟙 Y)
      (Category.comp_id _).symm).hom.app N)
  naturality N N' x := by
    apply (etaleModuleDerivedDirectImageIdFullyFaithful Λ Y).map_injective
    simp only [Functor.id_map, Functor.map_comp, Functor.FullyFaithful.map_preimage]
    exact (etaleModuleDerivedDirectImageComp.{u, 0} Λ (𝟙 Y) (𝟙 Y) (𝟙 Y)
      (Category.comp_id _).symm).hom.naturality x

/-- `R(𝟙_Y)_*` of the unit `N ⟶ R(𝟙_Y)_* N` is the composition isomorphism at `N`. -/
lemma map_etaleModuleDerivedDirectImageIdUnit_app
    (N : DerivedCategory.Plus (EtaleModules.{u, 0} Λ Y)) :
    (etaleModuleDerivedDirectImage.{u, 0} Λ (𝟙 Y)).map
        ((etaleModuleDerivedDirectImageIdUnit Λ Y).app N) =
      (etaleModuleDerivedDirectImageComp.{u, 0} Λ (𝟙 Y) (𝟙 Y) (𝟙 Y)
        (Category.comp_id _).symm).hom.app N :=
  (etaleModuleDerivedDirectImageIdFullyFaithful Λ Y).map_preimage _

/-- The unit `N ⟶ R(𝟙_Y)_* N` is an isomorphism, `R(𝟙_Y)_*` being fully faithful. -/
instance isIso_etaleModuleDerivedDirectImageIdUnit_app
    (N : DerivedCategory.Plus (EtaleModules.{u, 0} Λ Y)) :
    IsIso ((etaleModuleDerivedDirectImageIdUnit Λ Y).app N) := by
  have : IsIso ((etaleModuleDerivedDirectImage.{u, 0} Λ (𝟙 Y)).map
      ((etaleModuleDerivedDirectImageIdUnit Λ Y).app N)) := by
    rw [map_etaleModuleDerivedDirectImageIdUnit_app]; infer_instance
  exact (etaleModuleDerivedDirectImageIdFullyFaithful Λ Y).isIso_of_isIso_map _

/-- **The right unit law of the composition of derived direct images**: `R p_* ≅ R(𝟙_Y)_* ∘ Rp_*`
is the unit at `Rp_*`. -/
lemma etaleModuleDerivedDirectImageComp_id_right_hom_app {A : Scheme.{u}} (p : A ⟶ Y)
    (h : p = p ≫ 𝟙 Y) (N : DerivedCategory.Plus (EtaleModules.{u, 0} Λ A)) :
    (etaleModuleDerivedDirectImageComp.{u, 0} Λ p (𝟙 Y) p h).hom.app N =
      (etaleModuleDerivedDirectImageIdUnit Λ Y).app
        ((etaleModuleDerivedDirectImage.{u, 0} Λ p).obj N) := by
  apply (etaleModuleDerivedDirectImageIdFullyFaithful Λ Y).map_injective
  have A := congrArg (fun t => NatTrans.app t N) (etaleModuleDerivedDirectImageComp_assoc Λ p
    (𝟙 Y) (𝟙 Y) p h (𝟙 Y) (Category.comp_id _).symm p h h)
  simp only [NatTrans.comp_app, Functor.whiskerRight_app, Functor.whiskerLeft_app] at A
  rw [map_etaleModuleDerivedDirectImageIdUnit_app]
  exact (cancel_epi _).mp A

/-- The trivial compactification `Y ⟶ Y ⟶ Y` of `𝟙_Y`. -/
abbrev trivialIdCompactification : CompactificationOf (Over.mk (𝟙 Y)) :=
  @CompactificationOf.ofFactor _ _ (Over.mk (𝟙 Y)) _ (𝟙 Y) (inferInstanceAs (IsOpenImmersion (𝟙 Y)))
    (𝟙 Y) (inferInstanceAs (IsProper (𝟙 Y))) (𝟙 Y) (Category.id_comp _)

/-- **The map of [Stacks, Tag 0F7G] along the identity of the trivial compactification** is the
unit of `R(𝟙_Y)_*`, at a torsion object. -/
lemma derivedRefinementComparison_id_trivial_app
    (N : DerivedCategory.Plus (EtaleModules.{u, 0} Λ Y)) (hN : isTorsionPlus.{u, 0} Λ Y N) :
    (derivedRefinementComparison Λ (𝟙 (trivialIdCompactification Y))).app N =
      (etaleModuleDerivedDirectImageIdUnit Λ Y).app
        ((etaleModuleDerivedExtensionByZero.{u, 0} Λ
          (trivialIdCompactification Y).immersion).obj N) := by
  have h := derivedLowerShriekHom_id_app Λ (trivialIdCompactification Y) N hN
  rw [derivedLowerShriekHom_app] at h
  let BC := derivedBaseComparison Λ (𝟙 (trivialIdCompactification Y))
  have hb : BC = (etaleModuleDerivedDirectImageComp.{u, 0} Λ (𝟙 Y) (𝟙 Y) (𝟙 Y)
      (Category.comp_id _).symm).hom :=
    (etaleModuleDerivedDirectImageComp_hom_eq Λ _ _ _ _).symm
  have hi : (inv BC).app ((etaleModuleDerivedExtensionByZero.{u, 0} Λ
      (trivialIdCompactification Y).immersion).obj N) ≫ BC.app _ = 𝟙 _ :=
    NatTrans.congr_app (IsIso.inv_hom_id BC) _
  have h2 : (etaleModuleDerivedDirectImage.{u, 0} Λ (trivialIdCompactification Y).toBase).map
      ((derivedRefinementComparison Λ (𝟙 (trivialIdCompactification Y))).app N) =
      BC.app ((etaleModuleDerivedExtensionByZero.{u, 0} Λ
        (trivialIdCompactification Y).immersion).obj N) :=
    ((Category.comp_id _).symm.trans (whisker_eq _ hi.symm)).trans
      ((Category.assoc _ _ _).symm.trans ((eq_whisker h _).trans (Category.id_comp _)))
  exact (etaleModuleDerivedDirectImageIdFullyFaithful Λ Y).map_injective
    (h2.trans ((NatTrans.congr_app hb _).trans
      (map_etaleModuleDerivedDirectImageIdUnit_app Λ Y _).symm))

end Unit

/-! ### Restrictions of the map of [Stacks, Tag 0F7G] and of identity cubes -/

section Restrict

/-- The cancellation pattern of `Stacks.EtaleCohomology.derivedLowerShriekBaseChangeCube_id_app`,
over plain objects. -/
lemma idcube_chain {𝒞 : Type*} [Category* 𝒞] {A B A' B' B'' : 𝒞} (C : A ⟶ B) [IsIso C]
    (x : A ⟶ A') (xinv : A' ⟶ A) (DC : A' ⟶ B') (C₂ : B' ⟶ B'') (y : B'' ⟶ B) (yinv : B ⟶ B'')
    (z : B' ⟶ B) (zinv : B ⟶ B') (hp : C = x ≫ DC ≫ C₂ ≫ y) (hn : DC ≫ z = xinv ≫ C)
    (hx : x ≫ xinv = 𝟙 _) (_hz : zinv ≫ z = 𝟙 _) (hz' : z ≫ zinv = 𝟙 _) (hy : y ≫ yinv = 𝟙 _) :
    C₂ = z ≫ yinv := by
  have h1 : x ≫ DC = C ≫ zinv := by
    calc x ≫ DC = x ≫ DC ≫ z ≫ zinv := by rw [hz', Category.comp_id]
      _ = C ≫ zinv := by rw [reassoc_of% hn, reassoc_of% hx]
  have h2 : C ≫ zinv ≫ C₂ ≫ y = C ≫ 𝟙 _ := by
    rw [Category.comp_id]
    conv_rhs => rw [hp]
    rw [← reassoc_of% h1]
  calc C₂ = (z ≫ zinv) ≫ C₂ ≫ (y ≫ yinv) := by rw [hz', hy, Category.id_comp, Category.comp_id]
    _ = z ≫ (zinv ≫ C₂ ≫ y) ≫ yinv := by simp only [Category.assoc]
    _ = z ≫ yinv := by rw [(cancel_epi C).mp h2, Category.id_comp]

variable {X Y : Scheme.{u}} {f : X ⟶ Y} (k : CompactificationOf (Over.mk f))

/-- **The base change map of the identity cube of a compactification** is the identity, read
through `(𝟙)^{-1} ≅ 𝟭`, at objects of the form `(𝟙_X)^{-1} N`. -/
theorem derivedLowerShriekBaseChangeCube_id_app (hc : IsPullback (𝟙 X) k.immersion k.immersion
    (𝟙 k.space)) (w : k.toBase ≫ 𝟙 Y = 𝟙 k.space ≫ k.toBase)
    (N : DerivedCategory.Plus (EtaleModules.{u, 0} Λ X)) :
    (derivedLowerShriekBaseChangeCube Λ k k (𝟙 k.space) hc w).app
        ((etaleModuleDerivedInverseImagePlus.{u, 0} Λ (𝟙 X)).obj N) =
      (etaleModuleDerivedInverseImagePlusIdIso Λ Y).hom.app
          ((derivedLowerShriek.{u, 0} f k Λ).obj
            ((etaleModuleDerivedInverseImagePlus.{u, 0} Λ (𝟙 X)).obj N)) ≫
        (derivedLowerShriek.{u, 0} f k Λ).map
          ((etaleModuleDerivedInverseImagePlusIdIso Λ X).inv.app
            ((etaleModuleDerivedInverseImagePlus.{u, 0} Λ (𝟙 X)).obj N)) := by
  let ιX := etaleModuleDerivedInverseImagePlusIdIso Λ X
  let ιY := etaleModuleDerivedInverseImagePlusIdIso Λ Y
  let C := derivedLowerShriekBaseChangeCube Λ k k (𝟙 k.space) hc w
  have sq : IsPullback (𝟙 k.space) k.toBase k.toBase (𝟙 Y) := IsPullback.of_horiz_isIso ⟨rfl⟩
  have hC : IsIso (C.app N) := by
    have := isIso_etaleModuleDerivedBaseChange_of_isOpenImmersion Λ k.toBase sq
      ((etaleModuleDerivedExtensionByZero.{u, 0} Λ k.immersion).obj N)
    dsimp only [C, derivedLowerShriekBaseChangeCube, NatTrans.comp_app, Functor.whiskerLeft_app,
      Functor.whiskerRight_app]
    infer_instance
  have P := NatTrans.congr_app (derivedLowerShriekBaseChangeCube_paste Λ k k k (𝟙 k.space)
    (𝟙 k.space) hc hc w w w) N
  simp only [NatTrans.comp_app, Functor.whiskerRight_app, Functor.whiskerLeft_app,
    Functor.associator_hom_app, Functor.associator_inv_app, Category.id_comp,
    Category.comp_id] at P
  have e1 := etaleModuleDerivedInverseImagePlusCompIso_id_left_hom_app Λ (𝟙 Y)
    ((derivedLowerShriek.{u, 0} f k Λ).obj N)
  have e2 := etaleModuleDerivedInverseImagePlusCompIso_id_left_hom_app Λ (𝟙 X) N
  have hn := ιY.hom.naturality (C.app N)
  simp only [Functor.id_map] at hn
  refine idcube_chain (C.app N) _ (ιY.hom.app _) _ _ _
    ((derivedLowerShriek.{u, 0} f k Λ).map (ιX.inv.app _)) (ιY.hom.app _) (ιY.inv.app _) P hn ?_
    (Iso.inv_hom_id_app _ _) (Iso.hom_inv_id_app _ _) ?_
  · rw [← e1]; exact Iso.inv_hom_id_app _ _
  · exact ((Functor.map_comp _ _ _).symm.trans (congrArg (derivedLowerShriek.{u, 0} f k Λ).map
      ((eq_whisker e2 _).trans (Iso.hom_inv_id_app _ _)))).trans
      (CategoryTheory.Functor.map_id _ _)

end Restrict


/-! ### The map of [Stacks, Tag 0F7G] for a morphism of compactifications of `g`, over `Y` -/

section RestrictTheta

variable {Y Z : Scheme.{u}} {g : Y ⟶ Z} {jG jG' : CompactificationOf (Over.mk g)} (ψ : jG ⟶ jG')

/-- The square of `𝟙_Y` and the open immersion `Y ⟶ Ȳ` of a compactification of `g`, taken
twice, is a pullback, the immersion being a monomorphism. -/
lemma isPullback_id_id_immersion (j : CompactificationOf (Over.mk g)) :
    IsPullback (𝟙 Y) (trivialIdCompactification Y).immersion j.immersion j.immersion :=
  (mono_iff_isPullback j.immersion).1 inferInstance

/-- The identity of the trivial compactification of `𝟙_Y` followed by `i' : Y ⟶ Ȳ'` is
`i : Y ⟶ Ȳ` followed by `ψ̄`. -/
lemma immersion_comp_map_id_trivial :
    CompactificationOf.Hom.map (𝟙 (trivialIdCompactification Y)) ≫ jG'.immersion =
      jG.immersion ≫ CompactificationOf.Hom.map ψ :=
  (Category.id_comp _).trans (CompactificationOf.immersion_comp_map ψ).symm

/-- **The map `θ : i'_! ⟶ Rψ̄_* i_!` of [Stacks, Tag 0F7G] restricted to `Y`**: its inverse image
along `i' : Y ⟶ Ȳ'` followed by the base change map of `ψ̄` along `i'` and `i` is the map of
[Stacks, Tag 0F7G] for the identity of the trivial compactification of `𝟙_Y`, read through the
isomorphisms of [Stacks, Tag 03S6]. -/
theorem derivedRefinementComparison_restrict (N : DerivedCategory.Plus (EtaleModules.{u, 0} Λ Y)) :
    (etaleModuleDerivedInverseImagePlus.{u, 0} Λ jG'.immersion).map
        ((derivedRefinementComparison Λ ψ).app N) ≫
      (etaleModuleDerivedBaseChange.{u, 0} Λ (CompactificationOf.Hom.map ψ)
          (CompactificationOf.Hom.map (𝟙 (trivialIdCompactification Y))) jG'.immersion
          jG.immersion (immersion_comp_map_id_trivial ψ)).app
        ((etaleModuleDerivedExtensionByZero.{u, 0} Λ jG.immersion).obj N) ≫
      (etaleModuleDerivedDirectImage.{u, 0} Λ
          (CompactificationOf.Hom.map (𝟙 (trivialIdCompactification Y)))).map
        ((etaleModuleDerivedExtensionByZeroCubeIso Λ (isPullback_id_id_immersion jG)).inv.app N) =
    (etaleModuleDerivedExtensionByZeroCubeIso Λ (isPullback_id_id_immersion jG')).inv.app N ≫
      (derivedRefinementComparison Λ (𝟙 (trivialIdCompactification Y))).app
        ((etaleModuleDerivedInverseImagePlus.{u, 0} Λ (𝟙 Y)).obj N) := by
  have h := NatTrans.congr_app (derivedRefinementComparison_baseChange Λ ψ
    (𝟙 (trivialIdCompactification Y)) jG.immersion jG'.immersion
    (isPullback_id_id_immersion jG) (isPullback_id_id_immersion jG')
    (immersion_comp_map_id_trivial ψ)
    (etaleModuleRefinementComparison_baseChange Λ (CompactificationOf.immersion_comp_map ψ)
      (CompactificationOf.immersion_comp_map (𝟙 (trivialIdCompactification Y)))
      (isPullback_id_id_immersion jG) (isPullback_id_id_immersion jG')
      (immersion_comp_map_id_trivial ψ))) N
  simp only [NatTrans.comp_app, Functor.whiskerRight_app, Functor.whiskerLeft_app,
    Functor.associator_hom_app, Functor.associator_inv_app, Category.id_comp,
    Category.comp_id] at h
  exact h

/-- The cancellation pattern of
`Stacks.EtaleCohomology.derivedRefinementComparison_restrict_counit`, over plain objects. -/
lemma restrict_theta_chain {𝒞 : Type*} [Category* 𝒞] (F : 𝒞 ⥤ 𝒞) {s0 s1 p m n : 𝒞}
    (a : s0 ⟶ s1) (b : s1 ⟶ F.obj p) (c : p ⟶ m) (d : s0 ⟶ m) (t : m ⟶ F.obj m) (X : m ⟶ n)
    (uM : m ⟶ F.obj m) (uN : n ⟶ F.obj n) (ei : p ⟶ n) (ei' : s0 ⟶ n)
    (R1 : a ≫ b ≫ F.map c = d ≫ t) (Ei : ei = c ≫ X) (Ei' : ei' = d ≫ X) (Jb : t = uM)
    (un : X ≫ uN = uM ≫ F.map X) :
    a ≫ b ≫ F.map ei = ei' ≫ uN := by
  subst Ei Ei' Jb
  rw [F.map_comp, ← Category.assoc b, ← Category.assoc a, R1, Category.assoc, ← un,
    Category.assoc]

/-- **The map of [Stacks, Tag 0F7G] restricted to `Y`, through the counits**: the inverse image
along `i'` of `θ : i'_! ⟶ Rψ̄_* i_!`, followed by the base change map of `ψ̄` and the counit of
`i_!`, is the counit of `i'_!` followed by the unit of `R(𝟙_Y)_*`. -/
theorem derivedRefinementComparison_restrict_counit
    (N : DerivedCategory.Plus (EtaleModules.{u, 0} Λ Y)) (hN : isTorsionPlus.{u, 0} Λ Y N) :
    (etaleModuleDerivedInverseImagePlus.{u, 0} Λ jG'.immersion).map
        ((derivedRefinementComparison Λ ψ).app N) ≫
      (etaleModuleDerivedBaseChange.{u, 0} Λ (CompactificationOf.Hom.map ψ)
          (CompactificationOf.Hom.map (𝟙 (trivialIdCompactification Y))) jG'.immersion
          jG.immersion (immersion_comp_map_id_trivial ψ)).app
        ((etaleModuleDerivedExtensionByZero.{u, 0} Λ jG.immersion).obj N) ≫
      (etaleModuleDerivedDirectImage.{u, 0} Λ (𝟙 Y)).map
        ((etaleModuleDerivedExtensionByZeroCompInverseImagePlusIso Λ jG.immersion).hom.app N) =
    (etaleModuleDerivedExtensionByZeroCompInverseImagePlusIso Λ jG'.immersion).hom.app N ≫
      (etaleModuleDerivedDirectImageIdUnit Λ Y).app N := by
  have R1 := derivedRefinementComparison_restrict Λ ψ N
  have hD : isTorsionPlus.{u, 0} Λ Y ((etaleModuleDerivedInverseImagePlus.{u, 0} Λ (𝟙 Y)).obj N) :=
    isTorsionPlus_etaleModuleDerivedInverseImagePlus_obj Λ (𝟙 Y) N hN
  have Jb := derivedRefinementComparison_id_trivial_app Λ Y _ hD
  have Ei := etaleModuleDerivedExtensionByZeroCompInverseImagePlusIso_hom_app_eq_cube Λ
    jG.immersion (isPullback_id_id_immersion jG) N
  have Ei' := etaleModuleDerivedExtensionByZeroCompInverseImagePlusIso_hom_app_eq_cube Λ
    jG'.immersion (isPullback_id_id_immersion jG') N
  have un := (etaleModuleDerivedDirectImageIdUnit Λ Y).naturality
    ((etaleModuleDerivedInverseImagePlusIdIso Λ Y).inv.app
        ((etaleModuleDerivedExtensionByZero.{u, 0} Λ (𝟙 Y)).obj
          ((etaleModuleDerivedInverseImagePlus.{u, 0} Λ (𝟙 Y)).obj N)) ≫
      (etaleModuleDerivedExtensionByZeroCompInverseImagePlusIso Λ (𝟙 Y)).hom.app
        ((etaleModuleDerivedInverseImagePlus.{u, 0} Λ (𝟙 Y)).obj N) ≫
      (etaleModuleDerivedInverseImagePlusIdIso Λ Y).hom.app N)
  simp only [Functor.id_map] at un
  exact restrict_theta_chain (etaleModuleDerivedDirectImage.{u, 0} Λ (𝟙 Y)) _ _ _ _ _ _ _ _ _ _
    R1 Ei Ei' Jb un

end RestrictTheta

/-! ### The comparison over `Y` along a morphism of compactifications of `g` -/

section SecondSlotY

open CompactificationOf CompactificationOf.SecondSlot

variable {X Y Z : Scheme.{u}} {f : X ⟶ Y} {g : Y ⟶ Z} {jG jG' : CompactificationOf (Over.mk g)}
  (ψ : jG ⟶ jG') (jX : CompactificationOf (Over.mk (f ≫ jG.immersion)))

/-- The open immersions of `overBar jG jX` and `overBar jG' (pushX ψ jX)` agree, both being
that of `jX`. -/
lemma overBar_immersion_eq :
    (overBar jG jX).immersion = (overBar jG' (pushX ψ jX)).immersion :=
  (restrictBase_immersion_restrictBaseι jG jX).trans
    (restrictBase_immersion_restrictBaseι jG' (pushX ψ jX)).symm

/-- `X = X ×_{X̄ ×_Ȳ' Y} (X̄ ×_Ȳ Y)`. -/
theorem isPullback_rmap : IsPullback (𝟙 X) (restrictBase jG jX).immersion
    (restrictBase jG' (pushX ψ jX)).immersion (rmap ψ jX) := by
  have s := isPullback_restrictBase_overBar jG jX
  rw [← rmap_fst ψ jX, overBar_immersion_eq ψ jX, ← Category.comp_id (𝟙 X)] at s
  exact IsPullback.of_right s ((Category.id_comp _).trans (immersion_rmap ψ jX).symm)
    (isPullback_restrictBase_overBar jG' (pushX ψ jX))

/-- `rmap ψ jX` commutes with the projections to `Y`, as a square with `𝟙_Y`. -/
lemma rmap_w : (restrictBase jG jX).toBase ≫ 𝟙 Y =
    rmap ψ jX ≫ (restrictBase jG' (pushX ψ jX)).toBase :=
  (Category.comp_id _).trans (rmap_snd ψ jX).symm

/-- `X̄ ×_Ȳ Y ⟶ Y ⟶ Ȳ'` is `X̄ ×_Ȳ Y ⟶ X̄ ×_Ȳ' Y ⟶ X̄ ⟶ Ȳ'`. -/
lemma rmap_w₃ : (restrictBase jG jX).toBase ≫ (𝟙 Y ≫ jG'.immersion) =
    (rmap ψ jX ≫ restrictBaseι jG' (pushX ψ jX)) ≫ (overBar jG' (pushX ψ jX)).toBase := by
  calc (restrictBase jG jX).toBase ≫ (𝟙 Y ≫ jG'.immersion)
      = (rmap ψ jX ≫ (restrictBase jG' (pushX ψ jX)).toBase) ≫ jG'.immersion := by
        rw [Category.id_comp, rmap_snd]
    _ = rmap ψ jX ≫ (restrictBaseι jG' (pushX ψ jX) ≫ (pushX ψ jX).toBase) := by
        rw [Category.assoc]; exact whisker_eq _ pullback.condition.symm
    _ = _ := (Category.assoc _ _ _).symm

/-- The cancellation pattern of `Stacks.EtaleCohomology.secondSlot_cube_rmap`, over plain
objects. -/
lemma secondSlot_cube_chain {𝒞 : Type*} [Category* 𝒞] {a0 a1 a2 b0 b1 b3 b4 b5 b6 : 𝒞}
    (c3 : a0 ⟶ b0) (ci : a0 ⟶ a1) (Dc' : a1 ⟶ a2) (cR : a2 ⟶ b3) (Rch : b3 ⟶ b0)
    (ιi : a0 ⟶ a1) (DHr : a2 ⟶ b4) (IdC : b4 ⟶ b3) (ιRb : b4 ⟶ b0) (RιinvDK : b0 ⟶ b3)
    (RιDK : b3 ⟶ b0) (c' : a0 ⟶ b1) (ιinvRb' : b1 ⟶ a2) (Hr : b1 ⟶ b0)
    (RιK : b0 ⟶ b5) (Rb'ιK : b1 ⟶ b6) (HrK : b6 ⟶ b5)
    (P : c3 = ci ≫ Dc' ≫ cR ≫ Rch) (hci : ci = ιi) (hcR : DHr ≫ IdC = cR)
    (hId : IdC = ιRb ≫ RιinvDK) (hRch : Rch = RιDK) (n1 : ιi ≫ Dc' = c' ≫ ιinvRb')
    (n2 : ιinvRb' ≫ DHr ≫ ιRb = Hr) (inv1 : RιinvDK ≫ RιDK = 𝟙 _)
    (n3 : Hr ≫ RιK = Rb'ιK ≫ HrK) :
    c3 ≫ RιK = c' ≫ Rb'ιK ≫ HrK := by
  subst P hci hRch hcR hId
  simp only [Category.assoc]
  rw [reassoc_of% inv1, reassoc_of% n1, reassoc_of% n2, n3]

/-- **The base change map of `X̄ ⟶ Ȳ'` along `Y ⟶ Ȳ'`, through `X̄ ×_Ȳ Y`**, is that through
`X̄ ×_Ȳ' Y` followed by the comparison of [Stacks, Tag 0F7I] along `X̄ ×_Ȳ Y ⟶ X̄ ×_Ȳ' Y`. -/
theorem secondSlot_cube_rmap (K : (isTorsionPlus.{u, 0} Λ X).FullSubcategory) :
    (derivedLowerShriekBaseChangeCube Λ (overBar jG' (pushX ψ jX)) (restrictBase jG jX)
        (rmap ψ jX ≫ restrictBaseι jG' (pushX ψ jX))
        ((isPullback_rmap ψ jX).paste_horiz (isPullback_restrictBase_overBar jG' (pushX ψ jX)))
        (rmap_w₃ ψ jX)).app K.obj ≫
      (derivedLowerShriek.{u, 0} f (restrictBase jG jX) Λ).map
        ((etaleModuleDerivedInverseImagePlusIdIso Λ X).hom.app K.obj) =
    (derivedLowerShriekBaseChangeCube Λ (overBar jG' (pushX ψ jX)) (restrictBase jG' (pushX ψ jX))
        (restrictBaseι jG' (pushX ψ jX)) (isPullback_restrictBase_overBar jG' (pushX ψ jX))
        pullback.condition.symm).app K.obj ≫
      (derivedLowerShriek.{u, 0} f (restrictBase jG' (pushX ψ jX)) Λ).map
        ((etaleModuleDerivedInverseImagePlusIdIso Λ X).hom.app K.obj) ≫
      (derivedLowerShriekHom Λ (r ψ jX)).app K.obj := by
  let ιX := etaleModuleDerivedInverseImagePlusIdIso Λ X
  let ιY := etaleModuleDerivedInverseImagePlusIdIso Λ Y
  have hK1 : isTorsionPlus.{u, 0} Λ X
      ((etaleModuleDerivedInverseImagePlus.{u, 0} Λ (𝟙 X)).obj K.obj) :=
    isTorsionPlus_etaleModuleDerivedInverseImagePlus_obj Λ (𝟙 X) K.obj K.property
  have hK2 : isTorsionPlus.{u, 0} Λ X ((etaleModuleDerivedInverseImagePlus.{u, 0} Λ (𝟙 X)).obj
      ((etaleModuleDerivedInverseImagePlus.{u, 0} Λ (𝟙 X)).obj K.obj)) :=
    isTorsionPlus_etaleModuleDerivedInverseImagePlus_obj Λ (𝟙 X) _ hK1
  have hcid : IsPullback (𝟙 X) (restrictBase jG jX).immersion (restrictBase jG jX).immersion
      (𝟙 _) := IsPullback.of_horiz_isIso ⟨rfl⟩
  have P := NatTrans.congr_app (derivedLowerShriekBaseChangeCube_paste Λ
    (overBar jG' (pushX ψ jX)) (restrictBase jG' (pushX ψ jX)) (restrictBase jG jX)
    (restrictBaseι jG' (pushX ψ jX)) (rmap ψ jX) (isPullback_restrictBase_overBar jG' (pushX ψ jX))
    (isPullback_rmap ψ jX) pullback.condition.symm (rmap_w ψ jX) (rmap_w₃ ψ jX)) K.obj
  simp only [NatTrans.comp_app, Functor.whiskerRight_app, Functor.whiskerLeft_app,
    Functor.associator_hom_app, Functor.associator_inv_app, Category.id_comp] at P
  have Nr := NatTrans.congr_app (derivedLowerShriekBaseChangeCube_naturality Λ (r ψ jX)
    (𝟙 (restrictBase jG jX)) (𝟙 _) (rmap ψ jX) hcid (isPullback_rmap ψ jX) rfl
    ((Category.comp_id _).trans (Category.id_comp _).symm) (rmap_w ψ jX))
    ((etaleModuleDerivedInverseImagePlus.{u, 0} Λ (𝟙 X)).obj K.obj)
  simp only [NatTrans.comp_app, Functor.whiskerRight_app, Functor.whiskerLeft_app] at Nr
  have Nr' := Nr.trans ((whisker_eq _ (derivedLowerShriekHom_id_app Λ _ _ hK2)).trans
    (Category.comp_id _))
  have e1 := etaleModuleDerivedInverseImagePlusCompIso_id_left_hom_app Λ jG'.immersion
    ((derivedLowerShriek.{u, 0} (f ≫ jG'.immersion) (overBar jG' (pushX ψ jX)) Λ).obj K.obj)
  have e2 := etaleModuleDerivedInverseImagePlusCompIso_id_left_hom_app Λ (𝟙 X) K.obj
  have n1 := ιY.inv.naturality ((derivedLowerShriekBaseChangeCube Λ (overBar jG' (pushX ψ jX))
    (restrictBase jG' (pushX ψ jX)) (restrictBaseι jG' (pushX ψ jX))
    (isPullback_restrictBase_overBar jG' (pushX ψ jX)) pullback.condition.symm).app K.obj)
  simp only [Functor.id_map] at n1
  have n2 := ιY.hom.naturality ((derivedLowerShriekHom Λ (r ψ jX)).app
    ((etaleModuleDerivedInverseImagePlus.{u, 0} Λ (𝟙 X)).obj K.obj))
  simp only [Functor.id_map] at n2
  have n2' : ιY.inv.app _ ≫ (etaleModuleDerivedInverseImagePlus.{u, 0} Λ (𝟙 Y)).map
      ((derivedLowerShriekHom Λ (r ψ jX)).app
        ((etaleModuleDerivedInverseImagePlus.{u, 0} Λ (𝟙 X)).obj K.obj)) ≫ ιY.hom.app _ =
      (derivedLowerShriekHom Λ (r ψ jX)).app
        ((etaleModuleDerivedInverseImagePlus.{u, 0} Λ (𝟙 X)).obj K.obj) := by
    rw [n2, Iso.inv_hom_id_app_assoc]
  have n3 := (derivedLowerShriekHom Λ (r ψ jX)).naturality (ιX.hom.app K.obj)
  have inv1 := (Functor.map_comp _ _ _).symm.trans
    ((congrArg (derivedLowerShriek.{u, 0} f (restrictBase jG jX) Λ).map
      (Iso.inv_hom_id_app ιX ((etaleModuleDerivedInverseImagePlus.{u, 0} Λ (𝟙 X)).obj
        K.obj))).trans (CategoryTheory.Functor.map_id _ _))
  refine secondSlot_cube_chain _ _ _ _ _ (ιY.inv.app _) _ _ (ιY.hom.app _) _ _ _ (ιY.inv.app _)
    _ _ _ _ P ?_ Nr' (derivedLowerShriekBaseChangeCube_id_app Λ (restrictBase jG jX) hcid
      ((Category.comp_id _).trans (Category.id_comp _).symm) K.obj) ?_ n1.symm n2' inv1 n3.symm
  · exact congrArg Iso.inv (Iso.ext (α := (etaleModuleDerivedInverseImagePlusCompIso Λ (𝟙 Y)
      jG'.immersion).app _) (β := ιY.app _) e1)
  · exact congrArg (derivedLowerShriek.{u, 0} f (restrictBase jG jX) Λ).map e2

/-- The cancellation pattern of `Stacks.EtaleCohomology.secondSlot_Ybar`, over plain objects. -/
lemma secondSlot_Ybar_chain {𝒞 : Type*} [Category* 𝒞] (F : 𝒞 ⥤ 𝒞)
    {s0 s1 s2 s3 t1 e0 e1 n0 n1 m0 m1 p0 p1 q0 : 𝒞}
    (dΨ' : s0 ⟶ s1) (dθ : s1 ⟶ s2) (dRr : s2 ⟶ s3) (pbB : s3 ⟶ F.obj e0) (εB : e0 ⟶ n0)
    (pbB' : s2 ⟶ F.obj e1) (dEr : e1 ⟶ e0) (εB' : e1 ⟶ n1) (Hr : n1 ⟶ n0) (ε'B' : s1 ⟶ n1)
    (uB' : n1 ⟶ F.obj n1) (uB : n0 ⟶ F.obj n0) (cX' : s0 ⟶ m1) (R'ι : m1 ⟶ n1)
    (de : s0 ⟶ t1) (dRy : t1 ⟶ s3) (pbM : t1 ⟶ F.obj p0) (dy : p0 ⟶ e0) (dc : p0 ⟶ p1)
    (dΨ : p1 ⟶ e0) (cX : p1 ⟶ m0) (Rι : m0 ⟶ n0) (cX₂ : p0 ⟶ m0) (pbf : p0 ⟶ q0)
    (RcI : q0 ⟶ m0) (pb3 : s0 ⟶ q0) (E2 : q0 ⟶ F.obj q0) (uq : q0 ⟶ F.obj q0) (cX₃ : s0 ⟶ m0)
    (nat1 : dRr ≫ pbB = pbB' ≫ F.map dEr) (natε : dEr ≫ εB = εB' ≫ Hr)
    (Rσ' : dθ ≫ pbB' ≫ F.map εB' = ε'B' ≫ uB') (un : uB' ≫ F.map Hr = Hr ≫ uB)
    (rc' : dΨ' ≫ ε'B' = cX' ≫ R'ι)
    (nat3 : dRy ≫ pbB = pbM ≫ F.map dy) (hdy : dy = dc ≫ dΨ) (rc : dΨ ≫ εB = cX ≫ Rι)
    (nc : dc ≫ cX = cX₂) (hcX₂ : cX₂ = pbf ≫ RcI) (V : de ≫ pbM ≫ F.map pbf = pb3 ≫ E2)
    (Jc : E2 = uq) (un2 : uq ≫ F.map (RcI ≫ Rι) = (RcI ≫ Rι) ≫ uB) (hcX₃ : cX₃ = pb3 ≫ RcI)
    (D : cX₃ ≫ Rι = cX' ≫ R'ι ≫ Hr) (DL : s0 ⟶ s3) (DR : s0 ⟶ s3) (hLm : DL = de ≫ dRy)
    (hRm : DR = dΨ' ≫ dθ ≫ dRr) :
    DL ≫ pbB ≫ F.map εB = DR ≫ pbB ≫ F.map εB := by
  subst hLm hRm
  have hR : (dΨ' ≫ dθ ≫ dRr) ≫ pbB ≫ F.map εB = cX' ≫ R'ι ≫ Hr ≫ uB := by
    simp only [Category.assoc]
    rw [reassoc_of% nat1, ← F.map_comp, natε, F.map_comp, reassoc_of% Rσ', un, reassoc_of% rc']
  have hL : (de ≫ dRy) ≫ pbB ≫ F.map εB = cX₃ ≫ Rι ≫ uB := by
    calc (de ≫ dRy) ≫ pbB ≫ F.map εB = de ≫ pbM ≫ F.map (pbf ≫ RcI ≫ Rι) := by
          simp only [Category.assoc]
          rw [reassoc_of% nat3, ← F.map_comp, hdy, Category.assoc, rc, reassoc_of% nc, hcX₂,
            Category.assoc]
      _ = (de ≫ pbM ≫ F.map pbf) ≫ F.map (RcI ≫ Rι) := by
          simp only [F.map_comp, Category.assoc]
      _ = cX₃ ≫ Rι ≫ uB := by
          rw [V, Jc, Category.assoc, un2, hcX₃]
          simp only [Category.assoc]
  rw [hL, hR, reassoc_of% D]

/-- **The comparison over `Ȳ'` along a morphism `ψ : jG ⟶ jG'` of compactifications of `g`**:
in `D⁺(Ȳ')`, `Rψ̄_*` of the isomorphism `Ψ : R(f ≫ i)_! ≅ i_! Rf_!` for `Y ⊂ Ȳ` agrees with `Ψ`
for `Y ⊂ Ȳ'` followed by the map `i'_! ⟶ Rψ̄_* i_!` of [Stacks, Tag 0F7G], read through the
comparisons of [Stacks, Tag 0F7I]. -/
theorem secondSlot_Ybar (K : (isTorsionPlus.{u, 0} Λ X).FullSubcategory) :
    (etaleModuleDerivedDirectImageComp.{u, 0} Λ jX.toBase (Hom.map ψ) (jX.toBase ≫ Hom.map ψ)
        rfl).hom.app ((etaleModuleDerivedExtensionByZero.{u, 0} Λ
          (overBar jG' (pushX ψ jX)).immersion).obj K.obj) ≫
      (etaleModuleDerivedDirectImage.{u, 0} Λ (Hom.map ψ)).map
        ((derivedLowerShriekHom Λ (c₀' ψ jX)).app K.obj ≫
          (derivedLowerShriekRestrictBaseIso Λ jG jX).hom.app K) =
    (derivedLowerShriekRestrictBaseIso Λ jG' (pushX ψ jX)).hom.app K ≫
      (derivedRefinementComparison Λ ψ).app
        ((derivedLowerShriek.{u, 0} f (restrictBase jG' (pushX ψ jX)) Λ).obj K.obj) ≫
      (etaleModuleDerivedDirectImage.{u, 0} Λ (Hom.map ψ)).map
        ((etaleModuleDerivedExtensionByZero.{u, 0} Λ jG.immersion).map
          ((derivedLowerShriekHom Λ (r ψ jX)).app K.obj)) := by
  let B := (derivedLowerShriek.{u, 0} f (restrictBase jG jX) Λ).obj K.obj
  let B' := (derivedLowerShriek.{u, 0} f (restrictBase jG' (pushX ψ jX)) Λ).obj K.obj
  let M' : DerivedCategory.Plus (EtaleModules.{u, 0} Λ jX.space) :=
    (etaleModuleDerivedExtensionByZero.{u, 0} Λ (overBar jG' (pushX ψ jX)).immersion).obj K.obj
  let D' := etaleModuleDerivedInverseImagePlus.{u, 0} Λ jG'.immersion
  let ε := etaleModuleDerivedExtensionByZeroCompInverseImagePlusIso Λ jG.immersion
  let u := etaleModuleDerivedDirectImageIdUnit Λ Y
  let Hr := (derivedLowerShriekHom Λ (r ψ jX)).app K.obj
  let PB := etaleModuleDerivedBaseChange.{u, 0} Λ (Hom.map ψ)
    (Hom.map (𝟙 (trivialIdCompactification Y))) jG'.immersion jG.immersion
    (immersion_comp_map_id_trivial ψ)
  have hB : isTorsionPlus.{u, 0} Λ Y B :=
    isTorsionPlus_derivedLowerShriek_obj Λ f _ K.obj K.property
  have hB' : isTorsionPlus.{u, 0} Λ Y B' :=
    isTorsionPlus_derivedLowerShriek_obj Λ f _ K.obj K.property
  have hK1 : isTorsionPlus.{u, 0} Λ X
      ((etaleModuleDerivedInverseImagePlus.{u, 0} Λ (𝟙 X)).obj K.obj) :=
    isTorsionPlus_etaleModuleDerivedInverseImagePlus_obj Λ (𝟙 X) K.obj K.property
  -- the restriction map is invertible
  have RσB := derivedRefinementComparison_restrict_counit Λ ψ B hB
  have hθB := isIso_derivedRefinementComparison_app Λ ψ B hB
  have hI : IsIso (D'.map ((derivedRefinementComparison Λ ψ).app B) ≫
      (PB.app ((etaleModuleDerivedExtensionByZero.{u, 0} Λ jG.immersion).obj B) ≫
        (etaleModuleDerivedDirectImage.{u, 0} Λ (𝟙 Y)).map (ε.hom.app B))) :=
    (congrArg IsIso RσB).mpr inferInstance
  let σ := PB.app ((etaleModuleDerivedExtensionByZero.{u, 0} Λ jG.immersion).obj B) ≫
      (etaleModuleDerivedDirectImage.{u, 0} Λ (𝟙 Y)).map (ε.hom.app B)
  have hσ : IsIso σ :=
    @IsIso.of_isIso_comp_left _ _ _ _ _ (D'.map ((derivedRefinementComparison Λ ψ).app B)) _
      (Functor.map_isIso _ _) hI
  -- the right side
  have nat1 := PB.naturality ((etaleModuleDerivedExtensionByZero.{u, 0} Λ jG.immersion).map Hr)
  simp only [Functor.comp_map] at nat1
  have natε := ε.hom.naturality Hr
  simp only [Functor.comp_map, Functor.id_map] at natε
  have Rσ' := derivedRefinementComparison_restrict_counit Λ ψ B' hB'
  have un := u.naturality Hr
  simp only [Functor.id_map] at un
  have rc' := derivedLowerShriekRestrictBaseIso_restrict_cube Λ jG' (pushX ψ jX) K
  -- the left side
  have nat3 := PB.naturality ((derivedLowerShriekHom Λ (c₀' ψ jX)).app K.obj ≫
    (derivedLowerShriekRestrictBaseIso Λ jG jX).hom.app K)
  simp only [Functor.comp_map] at nat3
  have rc := derivedLowerShriekRestrictBaseIso_restrict_cube Λ jG jX K
  have hc₂ : IsPullback (𝟙 X) (restrictBase jG jX).immersion (k₂ ψ jX).immersion
      (rmap ψ jX ≫ restrictBaseι jG' (pushX ψ jX)) :=
    (isPullback_rmap ψ jX).paste_horiz (isPullback_restrictBase_overBar jG' (pushX ψ jX))
  have w₂ : (restrictBase jG jX).toBase ≫ jG.immersion =
      (rmap ψ jX ≫ restrictBaseι jG' (pushX ψ jX)) ≫ (k₂ ψ jX).toBase :=
    pullback.condition.symm.trans (eq_whisker (rmap_fst ψ jX).symm _)
  have nc := NatTrans.congr_app (derivedLowerShriekBaseChangeCube_naturality Λ (c₀' ψ jX)
    (𝟙 (restrictBase jG jX)) (restrictBaseι jG jX) (rmap ψ jX ≫ restrictBaseι jG' (pushX ψ jX))
    (isPullback_restrictBase_overBar jG jX) hc₂
    ((Category.id_comp _).trans ((rmap_fst ψ jX).trans (Category.comp_id _).symm))
    pullback.condition.symm w₂) K.obj
  simp only [NatTrans.comp_app, Functor.whiskerRight_app, Functor.whiskerLeft_app] at nc
  have hcX₂ : (derivedLowerShriekBaseChangeCube Λ (k₂ ψ jX) (restrictBase jG jX)
      (rmap ψ jX ≫ restrictBaseι jG' (pushX ψ jX)) hc₂ w₂).app K.obj =
      (etaleModuleDerivedBaseChange.{u, 0} Λ jX.toBase (restrictBase jG jX).toBase jG.immersion
        (rmap ψ jX ≫ restrictBaseι jG' (pushX ψ jX)) w₂).app M' ≫
      (etaleModuleDerivedDirectImage.{u, 0} Λ (restrictBase jG jX).toBase).map
        ((etaleModuleDerivedExtensionByZeroCubeIso Λ hc₂).inv.app K.obj) := rfl
  have hcX₃ : (derivedLowerShriekBaseChangeCube Λ (overBar jG' (pushX ψ jX)) (restrictBase jG jX)
      (rmap ψ jX ≫ restrictBaseι jG' (pushX ψ jX))
      ((isPullback_rmap ψ jX).paste_horiz (isPullback_restrictBase_overBar jG' (pushX ψ jX)))
      (rmap_w₃ ψ jX)).app K.obj =
      (etaleModuleDerivedBaseChange.{u, 0} Λ (jX.toBase ≫ Hom.map ψ) (restrictBase jG jX).toBase
        jG'.immersion (rmap ψ jX ≫ restrictBaseι jG' (pushX ψ jX)) (rmap_w₃ ψ jX)).app M' ≫
      (etaleModuleDerivedDirectImage.{u, 0} Λ (restrictBase jG jX).toBase).map
        ((etaleModuleDerivedExtensionByZeroCubeIso Λ hc₂).inv.app K.obj) := rfl
  have nc' := nc.trans ((whisker_eq _ (derivedLowerShriekHom_id_app Λ _ _ hK1)).trans
    (Category.comp_id _))
  have V := congrArg (fun t => NatTrans.app t M')
    (etaleModuleDerivedBaseChange_comp Λ jX.toBase (Hom.map ψ)
      (jX.toBase ≫ Hom.map ψ) rfl (restrictBase jG jX).toBase
      (𝟙 Y) (restrictBase jG jX).toBase
      (Category.comp_id _).symm (rmap ψ jX ≫ restrictBaseι jG' (pushX ψ jX)) jG.immersion
      jG'.immersion w₂ ((Category.id_comp _).trans (immersion_comp_map ψ).symm) (rmap_w₃ ψ jX))
  simp only [NatTrans.comp_app, Functor.whiskerLeft_app, Functor.whiskerRight_app,
    Functor.associator_hom_app, Functor.associator_inv_app, Category.id_comp,
    Category.comp_id] at V
  have Jc := etaleModuleDerivedDirectImageComp_id_right_hom_app Λ Y (restrictBase jG jX).toBase
    (Category.comp_id _).symm ((etaleModuleDerivedInverseImagePlus.{u, 0} Λ
      (rmap ψ jX ≫ restrictBaseι jG' (pushX ψ jX))).obj M')
  have un2 := u.naturality ((etaleModuleDerivedDirectImage.{u, 0} Λ
      (restrictBase jG jX).toBase).map ((etaleModuleDerivedExtensionByZeroCubeIso Λ hc₂).inv.app
        K.obj) ≫ (derivedLowerShriek.{u, 0} f (restrictBase jG jX) Λ).map
      ((etaleModuleDerivedInverseImagePlusIdIso Λ X).hom.app K.obj))
  simp only [Functor.id_map] at un2
  refine (cancel_epi ((derivedLowerShriekRestrictBaseIso Λ jG' (pushX ψ jX)).inv.app K)).mp ?_
  refine eq_of_etaleModuleDerivedInverseImagePlus_map_eq_of_source Λ jG'.immersion _ _ ?_
  refine (D'.map_comp _ _).trans ((whisker_eq _ ?_).trans (D'.map_comp _ _).symm)
  have hσm : Mono σ := @IsIso.mono_of_iso _ _ _ _ σ hσ
  refine (cancel_mono σ).mp ?_
  exact secondSlot_Ybar_chain (etaleModuleDerivedDirectImage.{u, 0} Λ (𝟙 Y)) _ _ _ _ _ _ _ _ _ _
    _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ nat1 natε Rσ' un.symm rc' nat3 (Functor.map_comp _ _ _)
    rc nc' hcX₂ V.symm Jc un2.symm hcX₃ (secondSlot_cube_rmap Λ ψ jX K) _ _ (D'.map_comp _ _)
    ((D'.map_comp _ _).trans (whisker_eq _ (D'.map_comp _ _)))


/-- The cancellation pattern of `Stacks.EtaleCohomology.secondSlot_core`, over plain objects. -/
lemma secondSlot_core_chain {C C' D : Type*} [Category* C] [Category* C'] [Category* D]
    (G : C' ⥤ D) (P : C ⥤ C') (Rg : C ⥤ D) {d0 d1 : D} {a0 a1 a2 : C'} {c0 c1 c2 c3 : C}
    (HcK : d0 ⟶ d1) (COK : d1 ⟶ Rg.obj c2) (CO'K : d0 ⟶ G.obj a2) (HψB' : G.obj a2 ⟶ Rg.obj c3)
    (RHr : Rg.obj c3 ⟶ Rg.obj c2) (e₂₁ : d0 ⟶ G.obj a0) (Hc0 : a0 ⟶ a1) (e₂₄inv : G.obj a1 ⟶ d1)
    (e₂₄ : d1 ⟶ G.obj a1) (e₂₂ : a0 ⟶ P.obj c0) (Hc₀' : c0 ⟶ c1) (e₂₃inv : P.obj c1 ⟶ a1)
    (e₂₃ : a1 ⟶ P.obj c1) (e₂₅ : d1 ⟶ Rg.obj c1) (Ψ : c1 ⟶ c2) (e₂₁' : d0 ⟶ G.obj a0)
    (Ψ' : a0 ⟶ a2) (θ : a2 ⟶ P.obj c3) (invBC3 : G.obj (P.obj c3) ⟶ Rg.obj c3)
    (BCc3 : Rg.obj c3 ⟶ G.obj (P.obj c3)) (BCc1 : Rg.obj c1 ⟶ G.obj (P.obj c1))
    (BCc2 : Rg.obj c2 ⟶ G.obj (P.obj c2)) [Mono BCc2] (ir : c3 ⟶ c2)
    (HP1 : HcK = e₂₁ ≫ G.map Hc0 ≫ e₂₄inv) (HP2 : Hc0 = e₂₂ ≫ P.map Hc₀' ≫ e₂₃inv)
    (hCO : COK = e₂₅ ≫ Rg.map Ψ) (hCO' : CO'K = e₂₁' ≫ G.map Ψ')
    (hHψ : HψB' = G.map θ ≫ invBC3) (hRHr : RHr = Rg.map ir)
    (nBC1 : Rg.map ir ≫ BCc2 = BCc3 ≫ G.map (P.map ir))
    (nBC2 : Rg.map Ψ ≫ BCc2 = BCc1 ≫ G.map (P.map Ψ)) (A : e₂₄ ≫ G.map e₂₃ = e₂₅ ≫ BCc1)
    (i1 : e₂₃inv ≫ e₂₃ = 𝟙 _) (i2 : e₂₄inv ≫ e₂₄ = 𝟙 _) (i3 : invBC3 ≫ BCc3 = 𝟙 _)
    (Ω : e₂₂ ≫ P.map (Hc₀' ≫ Ψ) = Ψ' ≫ θ ≫ P.map ir) (he : e₂₁ = e₂₁') :
    HcK ≫ COK = CO'K ≫ HψB' ≫ RHr := by
  subst HP1 HP2 hCO hCO' hHψ hRHr he
  refine (cancel_mono BCc2).mp ?_
  have hL : (e₂₁ ≫ G.map (e₂₂ ≫ P.map Hc₀' ≫ e₂₃inv) ≫ e₂₄inv) ≫ (e₂₅ ≫ Rg.map Ψ) ≫ BCc2 =
      e₂₁ ≫ G.map (e₂₂ ≫ P.map (Hc₀' ≫ Ψ)) := by
    simp only [Category.assoc]
    rw [nBC2, ← reassoc_of% A, reassoc_of% i2, ← G.map_comp, ← G.map_comp]
    congr 2
    simp only [Category.assoc, reassoc_of% i1, P.map_comp]
  have hR : (e₂₁ ≫ G.map Ψ') ≫ (G.map θ ≫ invBC3) ≫ Rg.map ir ≫ BCc2 =
      e₂₁ ≫ G.map (Ψ' ≫ θ ≫ P.map ir) := by
    simp only [Category.assoc, G.map_comp]
    rw [nBC1, reassoc_of% i3]
  rw [Category.assoc, hL, Ω, Category.assoc, Category.assoc, ← hR]
  simp only [Category.assoc]

/-- **The comparison over `Z` along a morphism `ψ : jG ⟶ jG'` of compactifications of `g`**: the
isomorphism of [Stacks, Tag 0F7J] through `jG` and `X̄`, read through the comparisons of
[Stacks, Tag 0F7I], is that through `jG'` and `X̄` followed by the comparison
`Rg_!^{jG'} ⟶ Rg_!^{jG}` along `ψ`. -/
theorem secondSlot_core (K : (isTorsionPlus.{u, 0} Λ X).FullSubcategory) :
    (derivedLowerShriekHom Λ (c ψ jX)).app K.obj ≫
        (derivedLowerShriekCompOverIso Λ f g jG jX).hom.app K =
      (derivedLowerShriekCompOverIso Λ f g jG' (pushX ψ jX)).hom.app K ≫
        (derivedLowerShriekHom Λ ψ).app
          ((derivedLowerShriek.{u, 0} f (restrictBase jG' (pushX ψ jX)) Λ).obj K.obj) ≫
        (derivedLowerShriek.{u, 0} g jG Λ).map ((derivedLowerShriekHom Λ (r ψ jX)).app K.obj) := by
  let M : DerivedCategory.Plus (EtaleModules.{u, 0} Λ jX.space) :=
    (etaleModuleDerivedExtensionByZero.{u, 0} Λ (overBar jG jX).immersion).obj K.obj
  let BC := derivedBaseComparison Λ ψ
  have : IsIso (BC.app ((etaleModuleDerivedExtensionByZero.{u, 0} Λ jG.immersion).obj
      ((derivedLowerShriek.{u, 0} f (restrictBase jG jX) Λ).obj K.obj))) := inferInstance
  have hBC : BC = (etaleModuleDerivedDirectImageComp.{u, 0} Λ (Hom.map ψ) jG'.toBase jG.toBase
      (map_comp_toBase ψ).symm).hom :=
    (etaleModuleDerivedDirectImageComp_hom_eq Λ _ _ _ _).symm
  have nBC1 := BC.naturality ((etaleModuleDerivedExtensionByZero.{u, 0} Λ jG.immersion).map
    ((derivedLowerShriekHom Λ (r ψ jX)).app K.obj))
  have nBC2 := BC.naturality ((derivedLowerShriekRestrictBaseIso Λ jG jX).hom.app K)
  simp only [Functor.comp_map] at nBC1 nBC2
  have A := congrArg (fun t => NatTrans.app t M) (etaleModuleDerivedDirectImageComp_assoc Λ
    jX.toBase (Hom.map ψ) jG'.toBase (jX.toBase ≫ Hom.map ψ) rfl jG.toBase
    (map_comp_toBase ψ).symm (jX.toBase ≫ jG.toBase) (toBase_comp_map ψ jX) rfl)
  simp only [NatTrans.comp_app, Functor.whiskerRight_app, Functor.whiskerLeft_app] at A
  rw [← hBC] at A
  exact secondSlot_core_chain (etaleModuleDerivedDirectImage.{u, 0} Λ jG'.toBase)
    (etaleModuleDerivedDirectImage.{u, 0} Λ (Hom.map ψ))
    (etaleModuleDerivedDirectImage.{u, 0} Λ jG.toBase) _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _
    _ _ (derivedLowerShriekHom_ofFactorHom Λ _ _ _ _ _ _ _ _ _ _)
    (derivedLowerShriekHom_ofFactorHom Λ _ _ _ _ _ _ _ _ _ _)
    (derivedLowerShriekCompOverIso_hom_app Λ jG jX K)
    (derivedLowerShriekCompOverIso_hom_app Λ jG' (pushX ψ jX) K)
    (derivedLowerShriekHom_app Λ ψ _) rfl nBC1 nBC2 A (Iso.inv_hom_id_app _ _)
    (Iso.inv_hom_id_app _ _) (NatTrans.congr_app (IsIso.inv_hom_id BC) _)
    (secondSlot_Ybar Λ ψ jX K) rfl


end SecondSlotY

/-! ### Independence of the compactification of `g` -/

section Independence

open CompactificationOf CompactificationOf.SecondSlot

/-- A default-priority copy of `quasiCompact_of_compactSpace`, whose low-priority original times
out when the instance is needed in the proofs below. -/
private instance quasiCompact_of_compactSpace_aux {A B : Scheme.{u}} (p : A ⟶ B) [CompactSpace A]
    [QuasiSeparatedSpace B] : QuasiCompact p :=
  quasiCompact_of_compactSpace p

/-- Two comparisons of [Stacks, Tag 0F7I], the second along a morphism of compactifications. -/
lemma derivedLowerShriekCompactificationIso_hom_app_of_hom_comp {X Y : Scheme.{u}} (f : X ⟶ Y)
    [CompactSpace Y] [QuasiSeparatedSpace Y] [IsSeparated f] [LocallyOfFiniteType f]
    [QuasiCompact f] (K : (isTorsionPlus.{u, 0} Λ X).FullSubcategory)
    {j k l : CompactificationOf (Over.mk f)} (ψ : l ⟶ k) :
    (derivedLowerShriekCompactificationIso f j l Λ).hom.app K =
      (derivedLowerShriekCompactificationIso f j k Λ).hom.app K ≫
        (derivedLowerShriekHom Λ ψ).app K.obj := by
  rw [← derivedLowerShriekCompactificationIso_trans f Λ j k l,
    derivedLowerShriekCompactificationIso_of_hom f Λ ψ]
  rfl

/-- The comparison of [Stacks, Tag 0F7I] through a compactification dominating both. -/
lemma derivedLowerShriekCompactificationIso_hom_app_span {X Y : Scheme.{u}} (f : X ⟶ Y)
    [CompactSpace Y] [QuasiSeparatedSpace Y] [IsSeparated f] [LocallyOfFiniteType f]
    [QuasiCompact f] (K : (isTorsionPlus.{u, 0} Λ X).FullSubcategory)
    {j k m : CompactificationOf (Over.mk f)} (ψ₁ : m ⟶ j) (ψ₂ : m ⟶ k) :
    (derivedLowerShriekCompactificationIso f j k Λ).hom.app K =
      (derivedLowerShriekHom Λ ψ₁).app K.obj ≫ (derivedLowerShriekHomIso Λ ψ₂).inv.app K := by
  rw [← derivedLowerShriekCompactificationIso_trans f Λ j m k,
    derivedLowerShriekCompactificationIso_of_hom f Λ ψ₁,
    ← derivedLowerShriekCompactificationIso_symm Λ f k m,
    derivedLowerShriekCompactificationIso_of_hom f Λ ψ₂]
  rfl

/-- The cancellation pattern of `Stacks.EtaleCohomology.derivedLowerShriekCompIso_hom_app_of_hom`,
over plain objects. -/
lemma secondSlot_hom_chain {C D : Type*} [Category* C] [Category* D] (R R' : C ⥤ D)
    (Hψ : R' ⟶ R) {d0 d1 d1' : D} {b B' bf : C} (CIG : d0 ⟶ R.obj bf) (CIG' : d0 ⟶ R'.obj bf)
    (Ijco : d0 ⟶ d1) (Ijco' : d0 ⟶ d1') (Hc : d1' ⟶ d1) (CO : d1 ⟶ R.obj b)
    (CO' : d1' ⟶ R'.obj B') (Irb : b ⟶ bf) (Irb' : B' ⟶ bf) (Hr : B' ⟶ b)
    (hL : CIG = Ijco ≫ CO ≫ R.map Irb) (hR : CIG' = Ijco' ≫ CO' ≫ R'.map Irb')
    (i1 : Ijco = Ijco' ≫ Hc) (i2 : Irb' = Hr ≫ Irb)
    (core : Hc ≫ CO = CO' ≫ Hψ.app B' ≫ R.map Hr) :
    CIG = CIG' ≫ Hψ.app bf := by
  subst hL hR i1 i2
  simp only [Category.assoc, R'.map_comp]
  rw [Hψ.naturality Irb, reassoc_of% (Hψ.naturality Hr), reassoc_of% core]

/-- The cancellation pattern of `Stacks.EtaleCohomology.derivedLowerShriekCompIso_hom_app_second`,
over plain objects. -/
lemma span_chain {𝒞 : Type*} [Category* 𝒞] {A B C D : 𝒞} (a : A ⟶ D) (b : A ⟶ B) (m : A ⟶ C)
    (x : B ⟶ C) (y : D ⟶ C) (yinv : C ⟶ D) (h1 : m = b ≫ x) (h2 : m = a ≫ y)
    (hy : y ≫ yinv = 𝟙 _) : a = b ≫ x ≫ yinv := by
  rw [← reassoc_of% h1, h2, Category.assoc, hy, Category.comp_id]

variable {X Y Z : Scheme.{u}} (f : X ⟶ Y) (g : Y ⟶ Z) [CompactSpace X] [QuasiSeparatedSpace X]
  [CompactSpace Y] [QuasiSeparatedSpace Y] [CompactSpace Z] [QuasiSeparatedSpace Z]
  [IsSeparated f] [LocallyOfFiniteType f] [IsSeparated g] [LocallyOfFiniteType g]

/-- **The isomorphism of [Stacks, Tag 0F7J] along a morphism of compactifications of `g`**: for
`ψ : jG ⟶ jG'`, the isomorphism through `jG` is that through `jG'` followed by the comparison
`Rg_!^{jG'} ⟶ Rg_!^{jG}` of [Stacks, Tag 0F7I]. -/
theorem derivedLowerShriekCompIso_hom_app_of_hom (jf : CompactificationOf (Over.mk f))
    {jG jG' : CompactificationOf (Over.mk g)} (ψ : jG ⟶ jG')
    (j : CompactificationOf (Over.mk (f ≫ g))) (K : (isTorsionPlus.{u, 0} Λ X).FullSubcategory) :
    (derivedLowerShriekCompIso Λ f g jf jG j).hom.app K =
      (derivedLowerShriekCompIso Λ f g jf jG' j).hom.app K ≫
        (derivedLowerShriekHom Λ ψ).app ((derivedLowerShriek.{u, 0} f jf Λ).obj K.obj) := by
  obtain ⟨jX⟩ := nonempty_compactificationOf_comp_immersion f g jG
  have hL := derivedLowerShriekCompIso_hom_app_eq Λ f g jf jG j jX K
  have hR := derivedLowerShriekCompIso_hom_app_eq Λ f g jf jG' j (pushX ψ jX) K
  have i1 := derivedLowerShriekCompactificationIso_hom_app_of_hom_comp Λ (f ≫ g) K
    (j := j) (c ψ jX)
  have i2 := derivedLowerShriekCompactificationIso_hom_app_of_hom_source Λ f K (l := jf) (r ψ jX)
  exact secondSlot_hom_chain (derivedLowerShriek.{u, 0} g jG Λ) (derivedLowerShriek.{u, 0} g jG' Λ)
    (derivedLowerShriekHom Λ ψ) _ _ _ _ _ _ _ _ _ _ hL hR i1 i2 (secondSlot_core Λ ψ jX K)

/-- **The isomorphism of [Stacks, Tag 0F7J] does not depend on the compactification of `g`**: for
two compactifications `jG` and `jG'` of `g`, the isomorphisms through them correspond under the
comparison `Rg_!^{jG} ≅ Rg_!^{jG'}` of [Stacks, Tag 0F7I]. -/
theorem derivedLowerShriekCompIso_hom_app_second (jf : CompactificationOf (Over.mk f))
    (jG jG' : CompactificationOf (Over.mk g)) (j : CompactificationOf (Over.mk (f ≫ g)))
    (K : (isTorsionPlus.{u, 0} Λ X).FullSubcategory) :
    haveI : QuasiCompact g := quasiCompact_of_compactSpace g
    (derivedLowerShriekCompIso Λ f g jf jG' j).hom.app K =
      (derivedLowerShriekCompIso Λ f g jf jG j).hom.app K ≫
        (derivedLowerShriekCompactificationIso g jG jG' Λ).hom.app
          ⟨(derivedLowerShriek.{u, 0} f jf Λ).obj K.obj,
            isTorsionPlus_derivedLowerShriek_obj Λ f jf K.obj K.property⟩ := by
  let ψ₁ := IsCofiltered.minToLeft jG jG'
  let ψ₂ := IsCofiltered.minToRight jG jG'
  have h1 := derivedLowerShriekCompIso_hom_app_of_hom Λ f g jf ψ₁ j K
  have h2 := derivedLowerShriekCompIso_hom_app_of_hom Λ f g jf ψ₂ j K
  have hs := derivedLowerShriekCompactificationIso_hom_app_span Λ g
    ⟨_, isTorsionPlus_derivedLowerShriek_obj Λ f jf K.obj K.property⟩ ψ₁ ψ₂
  have hy := Iso.hom_inv_id_app (derivedLowerShriekHomIso Λ ψ₂)
    ⟨_, isTorsionPlus_derivedLowerShriek_obj Λ f jf K.obj K.property⟩
  rw [derivedLowerShriekHomIso_hom_app] at hy
  rw [hs]
  exact span_chain _ _ _ _ _ _ h1 h2 hy

/-- **The isomorphism of [Stacks, Tag 0F7J] along the comparisons of [Stacks, Tag 0F7I] for
`g ∘ f`.** -/
theorem derivedLowerShriekCompIso_hom_app_third (jf : CompactificationOf (Over.mk f))
    (jg : CompactificationOf (Over.mk g)) (j j' : CompactificationOf (Over.mk (f ≫ g)))
    (K : (isTorsionPlus.{u, 0} Λ X).FullSubcategory) :
    haveI : QuasiCompact (f ≫ g) := quasiCompact_of_compactSpace _
    (derivedLowerShriekCompIso Λ f g jf jg j').hom.app K =
      (derivedLowerShriekCompactificationIso (f ≫ g) j' j Λ).hom.app K ≫
        (derivedLowerShriekCompIso Λ f g jf jg j).hom.app K := by
  obtain ⟨jX⟩ := nonempty_compactificationOf_comp_immersion f g jg
  rw [derivedLowerShriekCompIso_hom_app_eq Λ f g jf jg j' jX K,
    derivedLowerShriekCompIso_hom_app_eq Λ f g jf jg j jX K,
    ← derivedLowerShriekCompactificationIso_trans (f ≫ g) Λ j' j, Iso.trans_hom,
    NatTrans.comp_app, Category.assoc]

/-- **The isomorphism of [Stacks, Tag 0F7J] along the comparisons of [Stacks, Tag 0F7I] for
`f`.** -/
theorem derivedLowerShriekCompIso_hom_app_first (jf jf' : CompactificationOf (Over.mk f))
    (jg : CompactificationOf (Over.mk g)) (j : CompactificationOf (Over.mk (f ≫ g)))
    (K : (isTorsionPlus.{u, 0} Λ X).FullSubcategory) :
    haveI : QuasiCompact f := quasiCompact_of_compactSpace f
    (derivedLowerShriekCompIso Λ f g jf' jg j).hom.app K =
      (derivedLowerShriekCompIso Λ f g jf jg j).hom.app K ≫
        (derivedLowerShriek.{u, 0} g jg Λ).map
          ((derivedLowerShriekCompactificationIso f jf jf' Λ).hom.app K) := by
  obtain ⟨jX⟩ := nonempty_compactificationOf_comp_immersion f g jg
  rw [derivedLowerShriekCompIso_hom_app_eq Λ f g jf' jg j jX K,
    derivedLowerShriekCompIso_hom_app_eq Λ f g jf jg j jX K,
    ← derivedLowerShriekCompactificationIso_trans f Λ _ jf jf']
  simp only [Iso.trans_hom, NatTrans.comp_app, Functor.map_comp, Category.assoc]

end Independence

/-! ### [Stacks, Tag 0F7K] -/

section Associativity

open CompactificationOf.Tower

/-- The assembly of `Stacks.EtaleCohomology.derivedLowerShriekCompIso_assoc`, over plain
objects. -/
lemma assoc_final_chain {𝒞 𝒟 : Type*} [Category* 𝒞] [Category* 𝒟] (Rh : 𝒞 ⥤ 𝒟)
    {d0 e e₀ : 𝒟} {c b b₀ : 𝒞} (A : d0 ⟶ e) (A₀ : d0 ⟶ e₀) (I1 : e₀ ⟶ e) (I2 : e ⟶ e₀)
    (CIb : e ⟶ Rh.obj b) (CIbm : e₀ ⟶ Rh.obj b) (CIb₀ : e₀ ⟶ Rh.obj b₀) (Ig : b₀ ⟶ b)
    (CIc : d0 ⟶ Rh.obj c) (CId : c ⟶ b) (CId₀ : c ⟶ b₀)
    (S1 : A = A₀ ≫ I1) (T3 : CIb = I2 ≫ CIbm) (F1 : CIbm = CIb₀ ≫ Rh.map Ig)
    (S2 : CId = CId₀ ≫ Ig) (T : A₀ ≫ CIb₀ = CIc ≫ Rh.map CId₀) (II : I1 ≫ I2 = 𝟙 _) :
    A ≫ CIb = CIc ≫ Rh.map CId := by
  subst S1 T3 F1 S2
  simp only [Category.assoc]
  rw [reassoc_of% II, reassoc_of% T, Rh.map_comp]

variable {X Y Z T : Scheme.{u}} (f : X ⟶ Y) (g : Y ⟶ Z) (h : Z ⟶ T) [CompactSpace X]
  [QuasiSeparatedSpace X] [CompactSpace Y] [QuasiSeparatedSpace Y] [CompactSpace Z]
  [QuasiSeparatedSpace Z] [CompactSpace T] [QuasiSeparatedSpace T] [IsSeparated f]
  [LocallyOfFiniteType f] [IsSeparated g] [LocallyOfFiniteType g] [IsSeparated h]
  [LocallyOfFiniteType h]

/-- **Stacks Project, Tag 0F7K.** Let `f : X ⟶ Y`, `g : Y ⟶ Z` and `h : Z ⟶ T` be separated
morphisms of finite type of quasi-compact and quasi-separated schemes, and let `Λ` be a ring. Then
the two isomorphisms `R(h ∘ g ∘ f)_! ≅ Rh_! ∘ Rg_! ∘ Rf_!` on `D⁺_tors(X_étale, Λ)` built from the
isomorphisms of [Stacks, Tag 0F7J] (`Stacks.EtaleCohomology.derivedLowerShriekCompIso`) agree:
through `R(h ∘ g)_! ∘ Rf_!` and through `Rh_! ∘ R(g ∘ f)_!`. Each of `Rf_!`, `Rg_!`, `Rh_!`,
`R(g ∘ f)_!`, `R(h ∘ g)_!` and `R(h ∘ g ∘ f)_!` is computed through an arbitrary compactification.

The proof follows [Stacks, Tag 0F7K]: choosing a compactification `Ȳ` of `Y` over the
compactification `Z̄` of `Z` (and of `X` over `Ȳ`) the statement is
`Stacks.EtaleCohomology.derivedLowerShriekCompIso_assoc_of_tower`, and the isomorphisms of
[Stacks, Tag 0F7J] do not depend on the compactifications
(`Stacks.EtaleCohomology.derivedLowerShriekCompIso_hom_app_second` and its first and third slot
companions). -/
@[stacks 0F7K]
theorem derivedLowerShriekCompIso_assoc (jf : CompactificationOf (Over.mk f))
    (jg : CompactificationOf (Over.mk g)) (jh : CompactificationOf (Over.mk h))
    (jfg : CompactificationOf (Over.mk (f ≫ g))) (jgh : CompactificationOf (Over.mk (g ≫ h)))
    (jfgh : CompactificationOf (Over.mk (f ≫ g ≫ h)))
    (K : (isTorsionPlus.{u, 0} Λ X).FullSubcategory) :
    (derivedLowerShriekCompIso Λ f (g ≫ h) jf jgh jfgh).hom.app K ≫
        (derivedLowerShriekCompIso Λ g h jg jh jgh).hom.app
          ⟨(derivedLowerShriek.{u, 0} f jf Λ).obj K.obj,
            isTorsionPlus_derivedLowerShriek_obj Λ f jf K.obj K.property⟩ =
      (derivedLowerShriekCompIso Λ (f ≫ g) h jfg jh jfgh).hom.app K ≫
        (derivedLowerShriek.{u, 0} h jh Λ).map
          ((derivedLowerShriekCompIso Λ f g jf jg jfg).hom.app K) := by
  obtain ⟨jY⟩ := nonempty_compactificationOf_comp_immersion g h jh
  let N : (isTorsionPlus.{u, 0} Λ Y).FullSubcategory :=
    ⟨(derivedLowerShriek.{u, 0} f jf Λ).obj K.obj,
      isTorsionPlus_derivedLowerShriek_obj Λ f jf K.obj K.property⟩
  let jgh₀ := CompactificationOf.compOver jh jY
  let jg₀ := CompactificationOf.restrictBase jh jY
  have S1 := derivedLowerShriekCompIso_hom_app_second Λ f (g ≫ h) jf jgh₀ jgh jfgh K
  have S2 := derivedLowerShriekCompIso_hom_app_second Λ f g jf jg₀ jg jfg K
  have T3 := derivedLowerShriekCompIso_hom_app_third Λ g h jg jh jgh₀ jgh N
  have F1 := derivedLowerShriekCompIso_hom_app_first Λ g h jg₀ jg jh jgh₀ N
  have II : (derivedLowerShriekCompactificationIso (g ≫ h) jgh₀ jgh Λ).hom.app N ≫
      (derivedLowerShriekCompactificationIso (g ≫ h) jgh jgh₀ Λ).hom.app N = 𝟙 _ := by
    rw [← NatTrans.comp_app, ← Iso.trans_hom, derivedLowerShriekCompactificationIso_trans,
      derivedLowerShriekCompactificationIso_self]
    rfl
  exact assoc_final_chain (derivedLowerShriek.{u, 0} h jh Λ) _ _ _ _ _ _ _ _ _ _ _ S1 T3 F1 S2
    (derivedLowerShriekCompIso_assoc_of_tower Λ f g h jf jfg jfgh jh jY K) II

end Associativity

end Stacks.EtaleCohomology

end
