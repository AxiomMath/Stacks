module

public import
  StacksFrontier.AlgebraicGeometry.EtaleCohomology.DerivedLowerShriek.ExtensionByZeroRestrict
public import
  StacksFrontier.AlgebraicGeometry.EtaleCohomology.DerivedLowerShriek.BaseChangeCubeComposition
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.DerivedLowerShriek.InverseImageTorsion
public import
  StacksFrontier.AlgebraicGeometry.EtaleCohomology.DerivedLowerShriek.CompositionIsoNaturality
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.DerivedLowerShriek.ExtensionByZeroCounitBaseChange
public import
  StacksFrontier.AlgebraicGeometry.EtaleCohomology.DerivedLowerShriek.InverseImageCompIdRight

/-!
# The isomorphism `Rf̄_* (b ∘ a)_! ≅ i_! Rf'_* a_!` and base change

For a compactification `i : Y ⟶ Ȳ` of `g` and a compactification `X ⟶ X̄` of `X` over `Ȳ`, the
isomorphism `Ψ : Rf̄_* (b ∘ a)_! ≅ i_! Rf'_* a_!` of the proof of [Stacks, Tag 0F7J] is compatible
with the base change maps of cubes along a base change `Z' ⟶ Z`. This is the core of the
compatibility of the base change isomorphisms of [Stacks, Tag 0F7L] with composition.

## Main results

* `Stacks.EtaleCohomology.derivedLowerShriekRestrictBaseIso_baseChange`.

## Implementation notes

The final comparison is carried out over abstract functors
(`Stacks.EtaleCohomology.restrictBase_baseChange_abstract`): over the concrete functors of étale
sheaves the kernel would have to unfold them to compare differently spelled objects.
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits
open AlgebraicGeometry AlgebraicGeometry.Scheme

universe u

namespace AlgebraicGeometry.CompactificationOf

variable {X Y Z X' Y' Z' : Scheme.{u}} {f : X ⟶ Y} {g : Y ⟶ Z} {h : Z' ⟶ Z} {hY : Y' ⟶ Y}
  {g' : Y' ⟶ Z'} {hX : X' ⟶ X} {f' : X' ⟶ Y'}
  (sqg : IsPullback hY g' g h) (sqf : IsPullback hX f' f hY)
  (jg : CompactificationOf (Over.mk g)) (jX : CompactificationOf (Over.mk (f ≫ jg.immersion)))

include sqf in
/-- The square `X' ⟶ Ȳ'` over `X ⟶ Ȳ`, for `Ȳ' = Ȳ ×_Z Z'`. -/
theorem isPullback_comp_immersion_baseChange :
    IsPullback hX (f' ≫ (jg.baseChange sqg).immersion) (f ≫ jg.immersion)
      (pullback.fst jg.toBase h) :=
  sqf.paste_vert (isPullback_baseChange sqg jg)

/-- The base change `X ⟶ X̄ ×_Ȳ Ȳ'` of the compactification `jX` of `X` over `Ȳ`. -/
abbrev compImmersionBaseChange :
    CompactificationOf (Over.mk (f' ≫ (jg.baseChange sqg).immersion)) :=
  jX.baseChange (isPullback_comp_immersion_baseChange sqg sqf jg)

/-- The projection `X̄ ×_Ȳ Ȳ' ⟶ X̄`. -/
abbrev compImmersionBaseChangeι :
    (compImmersionBaseChange sqg sqf jg jX).space ⟶ jX.space :=
  pullback.fst jX.toBase (pullback.fst jg.toBase h)

/-- The cube of the compactifications `overBar` over the square `X' ⟶ X`. -/
theorem isPullback_overBar_baseChange :
    IsPullback hX (overBar (jg.baseChange sqg) (compImmersionBaseChange sqg sqf jg jX)).immersion
      (overBar jg jX).immersion (compImmersionBaseChangeι sqg sqf jg jX) := by
  have h := isPullback_baseChange (isPullback_comp_immersion_baseChange sqg sqf jg) jX
  rw [← restrictBase_immersion_restrictBaseι jg jX] at h
  rw [← restrictBase_immersion_restrictBaseι (jg.baseChange sqg)
    (compImmersionBaseChange sqg sqf jg jX)] at h
  exact h

/-- The structure morphisms `X̄ ×_Ȳ Ȳ' ⟶ Ȳ'` and `X̄ ⟶ Ȳ` of `overBar` commute with the
projections `X̄ ×_Ȳ Ȳ' ⟶ X̄` and `Ȳ' ⟶ Ȳ`. -/
theorem overBar_baseChange_toBase_comm :
    (overBar (jg.baseChange sqg) (compImmersionBaseChange sqg sqf jg jX)).toBase ≫
        pullback.fst jg.toBase h =
      compImmersionBaseChangeι sqg sqf jg jX ≫ (overBar jg jX).toBase :=
  pullback.condition.symm

/-- The comparison `X̄★ ×_{Ȳ'} Y' ⟶ X̄ ×_Ȳ Y` of the spaces of `restrictBase`. -/
def restrictBaseBaseChangeι :
    (restrictBase (jg.baseChange sqg) (compImmersionBaseChange sqg sqf jg jX)).space ⟶
      (restrictBase jg jX).space :=
  pullback.lift (pullback.fst _ _ ≫ compImmersionBaseChangeι sqg sqf jg jX)
    (pullback.snd _ _ ≫ hY) (by
      have h0 : compImmersionBaseChangeι sqg sqf jg jX ≫ jX.toBase =
          (compImmersionBaseChange sqg sqf jg jX).toBase ≫ pullback.fst jg.toBase h :=
        pullback.condition
      have h1 := pullback.condition (f := (compImmersionBaseChange sqg sqf jg jX).toBase)
        (g := (jg.baseChange sqg).immersion)
      have h2 := (isPullback_baseChange sqg jg).w
      exact (Category.assoc _ _ _).trans ((congrArg (fun z => _ ≫ z) h0).trans
        ((Category.assoc _ _ _).symm.trans ((congrArg (fun z => z ≫ _) h1).trans
          ((Category.assoc _ _ _).trans ((congrArg (fun z => _ ≫ z) h2.symm).trans
            (Category.assoc _ _ _).symm))))))

/-- The first component of `restrictBaseBaseChangeι`: its composite with the projection to `X̄`
is the projection to `X̄ ×_Ȳ Ȳ'` followed by `X̄ ×_Ȳ Ȳ' ⟶ X̄`. -/
@[reassoc (attr := simp)]
lemma restrictBaseBaseChangeι_fst :
    restrictBaseBaseChangeι sqg sqf jg jX ≫ pullback.fst jX.toBase jg.immersion =
      pullback.fst _ _ ≫ compImmersionBaseChangeι sqg sqf jg jX :=
  pullback.lift_fst _ _ _

/-- The second component of `restrictBaseBaseChangeι`: its composite with the projection to `Y`
is the projection to `Y'` followed by `Y' ⟶ Y`. -/
@[reassoc (attr := simp)]
lemma restrictBaseBaseChangeι_snd :
    restrictBaseBaseChangeι sqg sqf jg jX ≫ pullback.snd jX.toBase jg.immersion =
      pullback.snd _ _ ≫ hY :=
  pullback.lift_snd _ _ _

/-- The structure morphisms `X̄★ ×_{Ȳ'} Y' ⟶ Y'` and `X̄ ×_Ȳ Y ⟶ Y` of `restrictBase` commute
with `restrictBaseBaseChangeι` and `Y' ⟶ Y`. -/
theorem restrictBase_baseChange_toBase_comm :
    (restrictBase (jg.baseChange sqg) (compImmersionBaseChange sqg sqf jg jX)).toBase ≫ hY =
      restrictBaseBaseChangeι sqg sqf jg jX ≫ (restrictBase jg jX).toBase :=
  (restrictBaseBaseChangeι_snd sqg sqf jg jX).symm

/-- `X̄★ ×_{Ȳ'} Y'` is `(X̄ ×_Ȳ Y) ×_Y Y'`. -/
theorem isPullback_restrictBaseBaseChangeι :
    IsPullback (restrictBaseBaseChangeι sqg sqf jg jX)
      (restrictBase (jg.baseChange sqg) (compImmersionBaseChange sqg sqf jg jX)).toBase
      (restrictBase jg jX).toBase hY := by
  have tbig := (IsPullback.of_hasPullback (compImmersionBaseChange sqg sqf jg jX).toBase
    (jg.baseChange sqg).immersion).paste_horiz
      (IsPullback.of_hasPullback jX.toBase (pullback.fst jg.toBase h))
  have e1 : pullback.fst _ _ ≫ compImmersionBaseChangeι sqg sqf jg jX =
      restrictBaseBaseChangeι sqg sqf jg jX ≫ pullback.fst jX.toBase jg.immersion :=
    (restrictBaseBaseChangeι_fst sqg sqf jg jX).symm
  have e2 := (isPullback_baseChange sqg jg).w
  rw [e1, ← e2] at tbig
  exact IsPullback.of_right tbig (restrictBaseBaseChangeι_snd sqg sqf jg jX)
    (IsPullback.of_hasPullback jX.toBase jg.immersion)

/-- The cube of the compactifications `restrictBase` over the square `X' ⟶ X`. -/
theorem isPullback_restrictBase_baseChange :
    IsPullback hX
      (restrictBase (jg.baseChange sqg) (compImmersionBaseChange sqg sqf jg jX)).immersion
      (restrictBase jg jX).immersion (restrictBaseBaseChangeι sqg sqf jg jX) := by
  refine IsPullback.of_bot ?_ ?_ (isPullback_restrictBaseBaseChangeι sqg sqf jg jX)
  · rw [immersion_toBase, immersion_toBase]
    exact sqf
  · apply pullback.hom_ext
    · have h1 := (isPullback_baseChange (isPullback_comp_immersion_baseChange sqg sqf jg) jX).w
      have h2 := baseChangeImmersion_fst (isPullback_id_comp_immersion jg) jX
      have h3 := baseChangeImmersion_fst (isPullback_id_comp_immersion (jg.baseChange sqg))
        (compImmersionBaseChange sqg sqf jg jX)
      have h4 := restrictBaseBaseChangeι_fst sqg sqf jg jX
      rw [Category.id_comp] at h2 h3
      change (hX ≫ baseChangeImmersion (isPullback_id_comp_immersion jg) jX) ≫ _ =
        (baseChangeImmersion (isPullback_id_comp_immersion (jg.baseChange sqg))
          (compImmersionBaseChange sqg sqf jg jX) ≫ _) ≫ _
      exact (congrArg (fun z => hX ≫ z) h2).trans (h1.trans
        (((congrArg (fun z => z ≫ compImmersionBaseChangeι sqg sqf jg jX) h3).symm.trans
          (Category.assoc _ _ _)).trans ((congrArg (fun z => _ ≫ z) h4.symm).trans
            (Category.assoc _ _ _).symm)))
    · have h2 := baseChangeImmersion_snd (isPullback_id_comp_immersion jg) jX
      have h3 := baseChangeImmersion_snd (isPullback_id_comp_immersion (jg.baseChange sqg))
        (compImmersionBaseChange sqg sqf jg jX)
      have h4 := restrictBaseBaseChangeι_snd sqg sqf jg jX
      change (hX ≫ baseChangeImmersion (isPullback_id_comp_immersion jg) jX) ≫ _ =
        (baseChangeImmersion (isPullback_id_comp_immersion (jg.baseChange sqg))
          (compImmersionBaseChange sqg sqf jg jX) ≫ _) ≫ _
      exact (congrArg (fun z => hX ≫ z) h2).trans (sqf.w.trans
        (((congrArg (fun z => z ≫ hY) h3).symm.trans
          (Category.assoc _ _ _)).trans ((congrArg (fun z => _ ≫ z) h4.symm).trans
            (Category.assoc _ _ _).symm)))

end AlgebraicGeometry.CompactificationOf

namespace Stacks.EtaleCohomology

attribute [local instance] HasDerivedCategory.standard

attribute [local instance high] CompactificationOf.etale_restrictBaseι
  CompactificationOf.etale_overBar_immersion

attribute [local instance] etaleModuleInverseImage_preservesFiniteLimits
  etaleModuleInverseImage_preservesFiniteColimits

variable (Λ : Type) [Ring Λ] {X Y Z X' Y' Z' : Scheme.{u}} {f : X ⟶ Y} {g : Y ⟶ Z} {h : Z' ⟶ Z}
  {hY : Y' ⟶ Y} {g' : Y' ⟶ Z'} {hX : X' ⟶ X} {f' : X' ⟶ Y'}
  (sqg : IsPullback hY g' g h) (sqf : IsPullback hX f' f hY)
  (jg : CompactificationOf (Over.mk g)) (jX : CompactificationOf (Over.mk (f ≫ jg.immersion)))

section Transport

variable {X Y X' Y' : Scheme.{u}} {f : X ⟶ Y} {f' : X' ⟶ Y'}

/-- The composition isomorphism of derived inverse images through an equality of morphisms. -/
lemma mapDerivedCategoryPlusCompIsoh_trans_eqToIso_inv {W V Vb : Scheme.{u}} {c : V ⟶ Vb}
    {g : W ⟶ V} {k₁ k₂ : W ⟶ Vb} (h : k₁ = k₂)
    (e : etaleModuleInverseImage.{u, 0} Λ c ⋙ etaleModuleInverseImage.{u, 0} Λ g ≅
      etaleModuleInverseImage.{u, 0} Λ k₁) :
    (Functor.mapDerivedCategoryPlusCompIsoh
        (e ≪≫ eqToIso (congrArg (fun m => etaleModuleInverseImage.{u, 0} Λ m) h))).inv =
      eqToHom (congrArg (fun m => etaleModuleDerivedInverseImagePlus.{u, 0} Λ m) h.symm) ≫
        (Functor.mapDerivedCategoryPlusCompIsoh e).inv := by
  subst h
  simp only [eqToIso_refl, Iso.trans_refl, eqToHom_refl, Category.id_comp]

omit [Ring Λ] in
/-- Cancelling a monomorphism and an isomorphism through a functor, over plain objects. -/
lemma map_eq_map_inv_comp_of_map_comp_eq {C D : Type*} [Category* C] [Category* D] (G : C ⥤ D)
    {S T U : C} {V : D} (σ : S ≅ T) (a : T ⟶ U) (r : S ⟶ U) (e : G.obj U ⟶ V) [Mono e]
    (h : G.map (σ.hom ≫ a) ≫ e = G.map r ≫ e) : G.map a = G.map (σ.inv ≫ r) := by
  have h' := (cancel_mono e).1 h
  rw [Functor.map_comp, ← h', Functor.map_comp, ← Category.assoc, ← Functor.map_comp,
    Iso.inv_hom_id, CategoryTheory.Functor.map_id, Category.id_comp]

omit [Ring Λ] in
/-- Concluding from the cancelled form, over plain objects. -/
lemma comp_eq_of_eq_inv_comp {C : Type*} [Category* C] {S T T' U : C} (a₁ : S ⟶ T) (a₂ : T ⟶ T')
    (σ : S ≅ T') (hσ : σ.hom = a₁ ≫ a₂) (a₃ : T' ⟶ U) (r : S ⟶ U) (h : a₃ = σ.inv ≫ r) :
    a₁ ≫ a₂ ≫ a₃ = r := by
  rw [h, ← Category.assoc, ← hσ, Iso.hom_inv_id_assoc]

omit [Ring Λ] in
/-- The chain of the left-hand side in `derivedLowerShriekRestrictBaseIso_baseChange`, over plain
objects. -/
lemma t0_left_chain {C : Type*} [Category* C]
    {P₀ P₁ P₂ P₃ Q N R₁ R₃ S₁ S₂ : C} (m : P₀ ⟶ P₃)
    (a1 : P₀ ⟶ P₁) (a2 : P₁ ⟶ P₂) (a3 : P₂ ⟶ P₃) (εQ : P₃ ⟶ Q) (εN : P₂ ⟶ N)
    (bcf : N ⟶ Q) (gg : P₁ ⟶ R₁) (eps : R₁ ⟶ N) (gg₀ : P₀ ⟶ R₃)
    (psi : R₃ ⟶ R₁) (bc1 : R₃ ⟶ S₁) (th : S₁ ⟶ N) (bcf' : S₁ ⟶ S₂) {thx : S₂ ⟶ Q}
    (hm : m = (a1 ≫ a2) ≫ a3)
    (n1 : a3 ≫ εQ = εN ≫ bcf) (u : a2 ≫ εN = gg ≫ eps)
    (nt : a1 ≫ gg = gg₀ ≫ psi) (rc : psi ≫ eps = bc1 ≫ th)
    (nb : th ≫ bcf = bcf' ≫ thx) :
    m ≫ εQ = gg₀ ≫ bc1 ≫ bcf' ≫ thx := by
  rw [hm, Category.assoc, Category.assoc, n1, reassoc_of% u, reassoc_of% nt, reassoc_of% rc, nb]

/-- The comparisons along `𝟙 ≫ c` and `c ≫ 𝟙` through `(𝟙)^{-1} ≅ 𝟭` agree. -/
lemma etaleModuleDerivedInverseImagePlusCompIso_id_right_left {W V : Scheme.{u}} (c : W ⟶ V)
    (N : DerivedCategory.Plus (EtaleModules.{u, 0} Λ V)) :
    (etaleModuleDerivedInverseImagePlusCompIso Λ c (𝟙 V)).inv.app N ≫
        (etaleModuleDerivedInverseImagePlus.{u, 0} Λ c).map
          ((etaleModuleDerivedInverseImagePlusIdIso Λ V).hom.app N) =
      (eqToHom (congrArg (fun m => etaleModuleDerivedInverseImagePlus.{u, 0} Λ m)
          (show c ≫ 𝟙 V = 𝟙 W ≫ c by simp))).app N ≫
        (etaleModuleDerivedInverseImagePlusCompIso Λ (𝟙 W) c).inv.app N ≫
        (etaleModuleDerivedInverseImagePlusIdIso Λ W).hom.app
          ((etaleModuleDerivedInverseImagePlus.{u, 0} Λ c).obj N) := by
  rw [← etaleModuleDerivedInverseImagePlusCompIso_id_right_hom_app,
    ← etaleModuleDerivedInverseImagePlusCompIso_id_comp_hom_app]
  refine (Iso.inv_hom_id_app _ _).trans ?_
  refine Eq.trans ?_ (whisker_eq _ (Iso.inv_hom_id_app _ _)).symm
  simp only [eqToHom_app]
  rfl

end Transport

section Abstract

omit [Ring Λ]

variable {CX CX' CY CY' CYb CYb' : Type*} [Category* CX] [Category* CX'] [Category* CY]
  [Category* CY'] [Category* CYb] [Category* CYb']

/-- **The glueing in `derivedLowerShriekRestrictBaseIso_baseChange`, over abstract functors.** -/
theorem restrictBase_baseChange_abstract
    {F : CX ⥤ CYb} {Fs : CX' ⥤ CYb'} {G : CX ⥤ CY} {Gs : CX' ⥤ CY'} {Dhb : CYb ⥤ CYb'}
    {Di' : CYb' ⥤ CY'} {Di : CYb ⥤ CY} {DhY : CY ⥤ CY'} {DhX : CX ⥤ CX'} {D1X : CX ⥤ CX}
    {D1X' : CX' ⥤ CX'} {Dk1 Dk2 : CYb ⥤ CY'} {Dg1 Dg2 : CX ⥤ CX'}
    (BC0 : F ⋙ Dhb ⟶ DhX ⋙ Fs) (BC2 : Fs ⋙ Di' ⟶ D1X' ⋙ Gs) (BC1 : F ⋙ Di ⟶ D1X ⋙ G)
    (BCf : G ⋙ DhY ⟶ DhX ⋙ Gs) (BCbig : F ⋙ Dk2 ⟶ Dg2 ⋙ Gs)
    (Dg : Dhb ⋙ Di' ≅ Dk1) (Dh : Di ⋙ DhY ≅ Dk2) (DX1 : DhX ⋙ D1X' ≅ Dg1)
    (DX2 : D1X ⋙ DhX ≅ Dg2) (hk : Dk2 = Dk1) (hk' : Dg1 = Dg2) (θ : D1X ≅ 𝟭 CX)
    (θ' : D1X' ≅ 𝟭 CX') (SC : Dhb ⋙ Di' ⟶ Di ⋙ DhY)
    (eqBig : BCbig = Functor.whiskerLeft F (eqToHom hk) ≫ Functor.whiskerLeft F Dg.inv ≫
      (Functor.associator _ _ _).inv ≫ Functor.whiskerRight BC0 Di' ≫
      (Functor.associator _ _ _).hom ≫ Functor.whiskerLeft DhX BC2 ≫
      (Functor.associator _ _ _).inv ≫ Functor.whiskerRight DX1.hom Gs ≫
      Functor.whiskerRight (eqToHom hk') Gs)
    (P2 : BCbig = Functor.whiskerLeft F Dh.inv ≫ (Functor.associator _ _ _).inv ≫
      Functor.whiskerRight BC1 DhY ≫ (Functor.associator _ _ _).hom ≫
      Functor.whiskerLeft D1X BCf ≫ (Functor.associator _ _ _).inv ≫
      Functor.whiskerRight DX2.hom Gs)
    (hSC : SC = Dg.hom ≫ eqToHom hk.symm ≫ Dh.inv)
    (hX : ∀ N, DX2.inv.app N ≫ DhX.map (θ.hom.app N) =
      (eqToHom hk'.symm).app N ≫ DX1.inv.app N ≫ θ'.hom.app (DhX.obj N))
    (K : CX) :
    SC.app (F.obj K) ≫ DhY.map (BC1.app K) ≫ BCf.app (D1X.obj K) ≫ Gs.map (DhX.map (θ.hom.app K)) =
      Di'.map (BC0.app K) ≫ BC2.app (DhX.obj K) ≫ Gs.map (θ'.hom.app (DhX.obj K)) := by
  subst hk hk'
  have h := NatTrans.congr_app (eqBig.symm.trans P2) K
  simp only [NatTrans.comp_app, Functor.whiskerLeft_app, Functor.whiskerRight_app,
    Functor.associator_hom_app, Functor.associator_inv_app, Category.id_comp, eqToHom_refl,
    NatTrans.id_app, CategoryTheory.Functor.map_id] at h
  have hXK := hX K
  simp only [eqToHom_refl, NatTrans.id_app, Category.id_comp] at hXK
  rw [hSC]
  simp only [NatTrans.comp_app, eqToHom_refl, Category.id_comp, Category.assoc]
  -- solve for `DhY.map (BC1.app K) ≫ BCf.app _` from `h`
  have h' : Dh.inv.app (F.obj K) ≫ DhY.map (BC1.app K) ≫ BCf.app (D1X.obj K) =
      Dg.inv.app (F.obj K) ≫ Di'.map (BC0.app K) ≫ BC2.app (DhX.obj K) ≫
        Gs.map (DX1.hom.app K) ≫ Gs.map (DX2.inv.app K) := by
    rw [← cancel_mono (Gs.map (DX2.hom.app K))]
    simp only [Category.assoc, ← Functor.map_comp, Iso.inv_hom_id_app, Category.comp_id]
    simpa only [Category.id_comp, Category.comp_id, Functor.comp_obj] using h.symm
  rw [reassoc_of% h']
  simp only [Iso.hom_inv_id_app_assoc]
  congr 2
  simp only [← Functor.map_comp]
  congr 1
  rw [hXK, Iso.hom_inv_id_app_assoc]

end Abstract

section PasteOfEq

variable {X Y X' Y' X'' Y'' : Scheme.{u}} {f : X ⟶ Y} {f' : X' ⟶ Y'} {f'' : X'' ⟶ Y''}
  {g₁ : Y' ⟶ Y} {g₁' : X' ⟶ X} {g₂ : Y'' ⟶ Y'} {g₂' : X'' ⟶ X'}

/-- `Stacks.EtaleCohomology.derivedLowerShriekBaseChangeCube_paste` for a cube whose data are only
equal to the composites. -/
theorem derivedLowerShriekBaseChangeCube_paste_of_eq (j : CompactificationOf (Over.mk f))
    (j' : CompactificationOf (Over.mk f')) (j'' : CompactificationOf (Over.mk f''))
    (φ₁ : j'.space ⟶ j.space) (φ₂ : j''.space ⟶ j'.space)
    (hc₁ : IsPullback g₁' j'.immersion j.immersion φ₁)
    (hc₂ : IsPullback g₂' j''.immersion j'.immersion φ₂)
    (w₁ : j'.toBase ≫ g₁ = φ₁ ≫ j.toBase) (w₂ : j''.toBase ≫ g₂ = φ₂ ≫ j'.toBase)
    {g₁₂ : Y'' ⟶ Y} (hg : g₂ ≫ g₁ = g₁₂) {g₁₂' : X'' ⟶ X} (hg' : g₂' ≫ g₁' = g₁₂')
    {φ₁₂ : j''.space ⟶ j.space} (hφ : φ₂ ≫ φ₁ = φ₁₂)
    (hc : IsPullback g₁₂' j''.immersion j.immersion φ₁₂) (w : j''.toBase ≫ g₁₂ = φ₁₂ ≫ j.toBase) :
    derivedLowerShriekBaseChangeCube Λ j j'' φ₁₂ hc w =
      Functor.whiskerLeft (derivedLowerShriek.{u, 0} f j Λ)
          (eqToHom (congrArg (fun m => etaleModuleDerivedInverseImagePlus.{u, 0} Λ m) hg.symm)) ≫
        Functor.whiskerLeft (derivedLowerShriek.{u, 0} f j Λ)
          (Functor.mapDerivedCategoryPlusCompIsoh
            (etaleModuleInverseImageCompIso.{u, 0} Λ g₂ g₁).symm).inv ≫
        (Functor.associator _ _ _).inv ≫
        Functor.whiskerRight (derivedLowerShriekBaseChangeCube Λ j j' φ₁ hc₁ w₁)
          (etaleModuleDerivedInverseImagePlus.{u, 0} Λ g₂) ≫
        (Functor.associator _ _ _).hom ≫
        Functor.whiskerLeft (etaleModuleDerivedInverseImagePlus.{u, 0} Λ g₁')
          (derivedLowerShriekBaseChangeCube Λ j' j'' φ₂ hc₂ w₂) ≫
        (Functor.associator _ _ _).inv ≫
        Functor.whiskerRight (Functor.mapDerivedCategoryPlusCompIsoh
            (etaleModuleInverseImageCompIso.{u, 0} Λ g₂' g₁').symm).hom
          (derivedLowerShriek.{u, 0} f'' j'' Λ) ≫
        Functor.whiskerRight
          (eqToHom (congrArg (fun m => etaleModuleDerivedInverseImagePlus.{u, 0} Λ m) hg'))
          (derivedLowerShriek.{u, 0} f'' j'' Λ) := by
  subst hg hg' hφ
  simp only [eqToHom_refl, Functor.whiskerLeft_id', Functor.whiskerRight_id', Category.id_comp,
    Category.comp_id]
  exact derivedLowerShriekBaseChangeCube_paste Λ j j' j'' φ₁ φ₂ hc₁ hc₂ w₁ w₂ w

end PasteOfEq

open CompactificationOf in
/-- **`Ψ : R(f ≫ i)_! ≅ i_! Rf_!` is compatible with base change** along `Z' ⟶ Z`: the base change
map of the cube of `overBar` followed by `Ψ` of the base change is `Ψ` followed by the base change
map of `i_!` and `i_!` of the base change map of the cube of `restrictBase`. -/
theorem derivedLowerShriekRestrictBaseIso_baseChange
    (K : (isTorsionPlus.{u, 0} Λ X).FullSubcategory) :
    (etaleModuleDerivedInverseImagePlus.{u, 0} Λ (pullback.fst jg.toBase h)).map
        ((derivedLowerShriekRestrictBaseIso Λ jg jX).hom.app K) ≫
      (etaleModuleDerivedExtensionByZeroCubeIso Λ (isPullback_baseChange sqg jg)).inv.app
        ((derivedLowerShriek.{u, 0} f (restrictBase jg jX) Λ).obj K.obj) ≫
      (etaleModuleDerivedExtensionByZero.{u, 0} Λ (jg.baseChange sqg).immersion).map
        ((derivedLowerShriekBaseChangeCube Λ (restrictBase jg jX)
          (restrictBase (jg.baseChange sqg) (compImmersionBaseChange sqg sqf jg jX))
          (restrictBaseBaseChangeι sqg sqf jg jX) (isPullback_restrictBase_baseChange sqg sqf jg jX)
          (restrictBase_baseChange_toBase_comm sqg sqf jg jX)).app K.obj) =
    (derivedLowerShriekBaseChangeCube Λ (overBar jg jX)
        (overBar (jg.baseChange sqg) (compImmersionBaseChange sqg sqf jg jX))
        (compImmersionBaseChangeι sqg sqf jg jX) (isPullback_overBar_baseChange sqg sqf jg jX)
        (overBar_baseChange_toBase_comm sqg sqf jg jX)).app K.obj ≫
      (derivedLowerShriekRestrictBaseIso Λ (jg.baseChange sqg)
        (compImmersionBaseChange sqg sqf jg jX)).hom.app
          ⟨(etaleModuleDerivedInverseImagePlus.{u, 0} Λ hX).obj K.obj,
            isTorsionPlus_etaleModuleDerivedInverseImagePlus_obj Λ hX K.obj K.property⟩ := by
  have T0 : (etaleModuleDerivedInverseImagePlus.{u, 0} Λ (jg.baseChange sqg).immersion).map
        (((etaleModuleDerivedInverseImagePlus.{u, 0} Λ (pullback.fst jg.toBase h)).map
            ((derivedLowerShriekRestrictBaseIso Λ jg jX).hom.app K) ≫
          (etaleModuleDerivedExtensionByZeroCubeIso Λ (isPullback_baseChange sqg jg)).inv.app
            ((derivedLowerShriek.{u, 0} f (restrictBase jg jX) Λ).obj K.obj)) ≫
          (etaleModuleDerivedExtensionByZero.{u, 0} Λ (jg.baseChange sqg).immersion).map
            ((derivedLowerShriekBaseChangeCube Λ (restrictBase jg jX)
              (restrictBase (jg.baseChange sqg) (compImmersionBaseChange sqg sqf jg jX))
              (restrictBaseBaseChangeι sqg sqf jg jX)
              (isPullback_restrictBase_baseChange sqg sqf jg jX)
              (restrictBase_baseChange_toBase_comm sqg sqf jg jX)).app K.obj)) ≫
      (etaleModuleDerivedExtensionByZeroCompInverseImagePlusIso Λ
        (jg.baseChange sqg).immersion).hom.app _ =
      (etaleModuleDerivedInverseImagePlus.{u, 0} Λ (jg.baseChange sqg).immersion).map
        ((derivedLowerShriekBaseChangeCube Λ (overBar jg jX)
            (overBar (jg.baseChange sqg) (compImmersionBaseChange sqg sqf jg jX))
            (compImmersionBaseChangeι sqg sqf jg jX) (isPullback_overBar_baseChange sqg sqf jg jX)
            (overBar_baseChange_toBase_comm sqg sqf jg jX)).app K.obj ≫
          (derivedLowerShriekRestrictBaseIso Λ (jg.baseChange sqg)
            (compImmersionBaseChange sqg sqf jg jX)).hom.app
              ⟨(etaleModuleDerivedInverseImagePlus.{u, 0} Λ hX).obj K.obj,
                isTorsionPlus_etaleModuleDerivedInverseImagePlus_obj Λ hX K.obj K.property⟩) ≫
      (etaleModuleDerivedExtensionByZeroCompInverseImagePlusIso Λ
        (jg.baseChange sqg).immersion).hom.app _ := by
    let M := (derivedLowerShriek.{u, 0} f (restrictBase jg jX) Λ).obj K.obj
    have u0 := etaleModuleDerivedExtensionByZeroCubeIso_inv_counit_app Λ
      (isPullback_baseChange sqg jg) M
    have n1 := (etaleModuleDerivedExtensionByZeroCompInverseImagePlusIso Λ
      (jg.baseChange sqg).immersion).hom.naturality
        ((derivedLowerShriekBaseChangeCube Λ (restrictBase jg jX)
          (restrictBase (jg.baseChange sqg) (compImmersionBaseChange sqg sqf jg jX))
          (restrictBaseBaseChangeι sqg sqf jg jX)
          (isPullback_restrictBase_baseChange sqg sqf jg jX)
          (restrictBase_baseChange_toBase_comm sqg sqf jg jX)).app K.obj)
    simp only [Functor.comp_map, Functor.id_map] at n1
    have nt : (etaleModuleDerivedInverseImagePlus.{u, 0} Λ (jg.baseChange sqg).immersion).map
          ((etaleModuleDerivedInverseImagePlus.{u, 0} Λ (pullback.fst jg.toBase h)).map
            ((derivedLowerShriekRestrictBaseIso Λ jg jX).hom.app K)) ≫
        (etaleModuleDerivedInverseImagePlusSquareComparison Λ (isPullback_baseChange sqg jg)).app
          ((etaleModuleDerivedExtensionByZero.{u, 0} Λ jg.immersion).obj M) =
        (etaleModuleDerivedInverseImagePlusSquareComparison Λ (isPullback_baseChange sqg jg)).app
          ((derivedLowerShriek.{u, 0} (f ≫ jg.immersion) (overBar jg jX) Λ).obj K.obj) ≫
        (etaleModuleDerivedInverseImagePlus.{u, 0} Λ hY).map
          ((etaleModuleDerivedInverseImagePlus.{u, 0} Λ jg.immersion).map
            ((derivedLowerShriekRestrictBaseIso Λ jg jX).hom.app K)) :=
      (etaleModuleDerivedInverseImagePlusSquareComparison Λ
        (isPullback_baseChange sqg jg)).naturality
        ((derivedLowerShriekRestrictBaseIso Λ jg jX).hom.app K)
    have rc := congrArg (fun z => (etaleModuleDerivedInverseImagePlus.{u, 0} Λ hY).map z)
      (derivedLowerShriekRestrictBaseIso_restrict_cube Λ jg jX K)
    simp only [Functor.map_comp] at rc
    have nb := (derivedLowerShriekBaseChangeCube Λ (restrictBase jg jX)
          (restrictBase (jg.baseChange sqg) (compImmersionBaseChange sqg sqf jg jX))
          (restrictBaseBaseChangeι sqg sqf jg jX)
          (isPullback_restrictBase_baseChange sqg sqf jg jX)
          (restrictBase_baseChange_toBase_comm sqg sqf jg jX)).naturality
      ((etaleModuleDerivedInverseImagePlusIdIso Λ X).hom.app K.obj)
    simp only [Functor.comp_map] at nb
    have hL := t0_left_chain _
      ((etaleModuleDerivedInverseImagePlus.{u, 0} Λ (jg.baseChange sqg).immersion).map
          ((etaleModuleDerivedInverseImagePlus.{u, 0} Λ (pullback.fst jg.toBase h)).map
            ((derivedLowerShriekRestrictBaseIso Λ jg jX).hom.app K)))
      _ _ _ _ _ _ _
      ((etaleModuleDerivedInverseImagePlusSquareComparison Λ (isPullback_baseChange sqg jg)).app
          ((derivedLowerShriek.{u, 0} (f ≫ jg.immersion) (overBar jg jX) Λ).obj K.obj))
      ((etaleModuleDerivedInverseImagePlus.{u, 0} Λ hY).map
          ((etaleModuleDerivedInverseImagePlus.{u, 0} Λ jg.immersion).map
            ((derivedLowerShriekRestrictBaseIso Λ jg jX).hom.app K)))
      _ _ _
      ((Functor.map_comp _ _ _).trans (congrArg (fun z => z ≫ _) (Functor.map_comp _ _ _)))
      n1 u0 nt rc nb
    have w12a : (restrictBase (jg.baseChange sqg) (compImmersionBaseChange sqg sqf jg jX)).toBase ≫
        (hY ≫ jg.immersion) =
        (restrictBaseBaseChangeι sqg sqf jg jX ≫ restrictBaseι jg jX) ≫ (overBar jg jX).toBase :=
      (Category.assoc _ _ _).symm.trans ((congrArg (fun z => z ≫ _)
        (restrictBase_baseChange_toBase_comm sqg sqf jg jX)).trans ((Category.assoc _ _ _).trans
          ((congrArg (fun z => _ ≫ z) pullback.condition.symm).trans (Category.assoc _ _ _).symm)))
    have P2 := derivedLowerShriekBaseChangeCube_paste Λ (overBar jg jX)
      (restrictBase jg jX)
      (restrictBase (jg.baseChange sqg) (compImmersionBaseChange sqg sqf jg jX))
      (restrictBaseι jg jX) (restrictBaseBaseChangeι sqg sqf jg jX)
      (isPullback_restrictBase_overBar jg jX) (isPullback_restrictBase_baseChange sqg sqf jg jX)
      pullback.condition.symm (restrictBase_baseChange_toBase_comm sqg sqf jg jX) w12a
    have w12b : (restrictBase (jg.baseChange sqg) (compImmersionBaseChange sqg sqf jg jX)).toBase ≫
        ((jg.baseChange sqg).immersion ≫ pullback.fst jg.toBase h) =
        (restrictBaseι (jg.baseChange sqg) (compImmersionBaseChange sqg sqf jg jX) ≫
          compImmersionBaseChangeι sqg sqf jg jX) ≫ (overBar jg jX).toBase :=
      (Category.assoc _ _ _).symm.trans ((congrArg (fun z => z ≫ _) pullback.condition.symm).trans
        ((Category.assoc _ _ _).trans ((congrArg (fun z => _ ≫ z)
          (overBar_baseChange_toBase_comm sqg sqf jg jX)).trans (Category.assoc _ _ _).symm)))
    have eqBig := derivedLowerShriekBaseChangeCube_paste_of_eq Λ (g₁ := pullback.fst jg.toBase h)
      (g₁' := hX) (g₂ := (jg.baseChange sqg).immersion) (g₂' := 𝟙 X') (overBar jg jX)
      (overBar (jg.baseChange sqg) (compImmersionBaseChange sqg sqf jg jX))
      (restrictBase (jg.baseChange sqg) (compImmersionBaseChange sqg sqf jg jX))
      (compImmersionBaseChangeι sqg sqf jg jX)
      (restrictBaseι (jg.baseChange sqg) (compImmersionBaseChange sqg sqf jg jX))
      (isPullback_overBar_baseChange sqg sqf jg jX)
      (isPullback_restrictBase_overBar (jg.baseChange sqg) (compImmersionBaseChange sqg sqf jg jX))
      (overBar_baseChange_toBase_comm sqg sqf jg jX) pullback.condition.symm
      (by exact (isPullback_baseChange sqg jg).w.symm) (by simp)
      (by exact (restrictBaseBaseChangeι_fst sqg sqf jg jX).symm)
      ((isPullback_restrictBase_baseChange sqg sqf jg jX).paste_horiz
        (isPullback_restrictBase_overBar jg jX)) w12a
    have hSC : etaleModuleDerivedInverseImagePlusSquareComparison Λ (isPullback_baseChange sqg jg) =
        (etaleModuleDerivedInverseImagePlusCompIso Λ (jg.baseChange sqg).immersion
            (pullback.fst jg.toBase h)).hom ≫
        eqToHom (congrArg (fun m => etaleModuleDerivedInverseImagePlus.{u, 0} Λ m)
          (isPullback_baseChange sqg jg).w.symm) ≫
        (etaleModuleDerivedInverseImagePlusCompIso Λ hY jg.immersion).inv := by
      simp only [etaleModuleDerivedInverseImagePlusSquareComparison]
      rw [mapDerivedCategoryPlusCompIsoh_trans_eqToIso_inv Λ (isPullback_baseChange sqg jg).w]
    have rc2 := derivedLowerShriekRestrictBaseIso_restrict_cube Λ (jg.baseChange sqg)
      (compImmersionBaseChange sqg sqf jg jX)
      ⟨(etaleModuleDerivedInverseImagePlus.{u, 0} Λ hX).obj K.obj,
        isTorsionPlus_etaleModuleDerivedInverseImagePlus_obj Λ hX K.obj K.property⟩
    have hR := (congrArg (fun z => z ≫ _) (Functor.map_comp
      (etaleModuleDerivedInverseImagePlus.{u, 0} Λ (jg.baseChange sqg).immersion)
      ((derivedLowerShriekBaseChangeCube Λ (overBar jg jX)
          (overBar (jg.baseChange sqg) (compImmersionBaseChange sqg sqf jg jX))
          (compImmersionBaseChangeι sqg sqf jg jX) (isPullback_overBar_baseChange sqg sqf jg jX)
          (overBar_baseChange_toBase_comm sqg sqf jg jX)).app K.obj)
      ((derivedLowerShriekRestrictBaseIso Λ (jg.baseChange sqg)
          (compImmersionBaseChange sqg sqf jg jX)).hom.app
            ⟨(etaleModuleDerivedInverseImagePlus.{u, 0} Λ hX).obj K.obj,
              isTorsionPlus_etaleModuleDerivedInverseImagePlus_obj Λ hX K.obj K.property⟩))).trans
      ((Category.assoc _ _ _).trans (whisker_eq _ rc2))
    exact hL.trans ((restrictBase_baseChange_abstract _ _ _ _ _ _ _ _ _ _ _
      (etaleModuleDerivedInverseImagePlusIdIso Λ X) (etaleModuleDerivedInverseImagePlusIdIso Λ X')
      _ eqBig P2 hSC (etaleModuleDerivedInverseImagePlusCompIso_id_right_left Λ hX) K.obj).trans
        hR.symm)
  let σ := (etaleModuleDerivedInverseImagePlus.{u, 0} Λ (pullback.fst jg.toBase h)).mapIso
      ((derivedLowerShriekRestrictBaseIso Λ jg jX).app K) ≪≫
    ((etaleModuleDerivedExtensionByZeroCubeIso Λ (isPullback_baseChange sqg jg)).app
      ((derivedLowerShriek.{u, 0} f (restrictBase jg jX) Λ).obj K.obj)).symm
  refine comp_eq_of_eq_inv_comp _ _ σ rfl _ _
    (eq_of_etaleModuleDerivedInverseImagePlus_map_eq_of_source Λ (jg.baseChange sqg).immersion _ _
      (map_eq_map_inv_comp_of_map_comp_eq _ σ _ _
        ((etaleModuleDerivedExtensionByZeroCompInverseImagePlusIso Λ
          (jg.baseChange sqg).immersion).hom.app _) ?_))
  exact T0

end Stacks.EtaleCohomology
