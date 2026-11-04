module

public import StacksFrontier.AlgebraicGeometry.Stacks.RelativePropertyDescent

/-!
# Descent of relative properties along a jointly covering family (Stacks 045D)

A representable 1-morphism of categories fibred in groupoids over the big fppf site has a relative
property stable under base change and fppf local at the target as soon as its base changes along
the members of a jointly covering family have it: the family form of
`AlgebraicGeometry.Stack.hasRelativeProperty_of_baseChange`.

## Main results

* `AlgebraicGeometry.Stack.hasRelativeProperty_of_baseChange_family`
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits Opposite CategoryTheory.OverShriek
open CategoryTheory.PresheafOfCategories

namespace AlgebraicGeometry.Stack

universe u v w t

/-- A representable 1-morphism `f : 𝒳 ⟶ 𝒴` has a relative property `P` (stable under base change
and fppf local at the target) as soon as every object of `𝒴` lifts locally to one of a family
`g i : 𝒵 i ⟶ 𝒴` along whose members the base changes of `f` have `P`. -/
theorem hasRelativeProperty_of_baseChange_family
    (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)
    (𝒳 𝒴 : CatFiberedInGroupoids.{u, max u v, u + 1, max (max (u + 1) w) v}
      (BigFppfOver B S hS)) {J : Type*}
    (𝒵 : J → CatFiberedInGroupoids.{u, max u v, u + 1, max (max (u + 1) w) v}
      (BigFppfOver B S hS))
    (P : MorphismProperty (AlgebraicSpaces B S hS))
    [P.IsStableUnderBaseChange]
    [P.IsLocalAtTarget (Space.Topology.fppf.precoverage.{u, max u t} B S hS)]
    (f : 𝒳 ⟶ 𝒴) (g : ∀ i, 𝒵 i ⟶ 𝒴)
    (D : ∀ i, Bicategory.TwoCommSq (g i) f)
    (hD : ∀ i, Bicategory.IsTwoFibreProduct (D i))
    (hf : IsRepresentableByAlgebraicSpaces B S hS f.hom)
    (hg : ∀ (U : BigFppfOver B S hS) (y : 𝒴.val.p.Fiber U),
      ∃ R ∈ BigFppfOver.topology B S hS U,
        ∀ ⦃V : BigFppfOver B S hS⦄ ⦃k : V ⟶ U⦄, R.arrows k →
          ∃ (i : J) (z : (𝒵 i).val.obj) (φ : (CatFiberedInGroupoids.homFunctor (g i)).obj z ⟶ y.1),
            𝒴.val.p.IsHomLift k φ)
    (hP : ∀ i, HasRelativeProperty B S hS P (D i).fst
      (isRepresentableByAlgebraicSpaces_baseChange.{u, v, w} B S hS 𝒳 𝒴 (𝒵 i) f (g i) (D i) (hD i)
        hf)) :
    HasRelativeProperty B S hS P f hf := by
  classical
  have : P.IsLocalAtTarget (Space.Topology.fppf.precoverage.{u, u} B S hS) :=
    .of_le (Space.Topology.precoverage_le_precoverage_max .fppf B S hS)
  intro U y hy F hF hE
  obtain ⟨E⟩ := hE
  have hUid : (Over.map U.hom).obj (Over.mk (𝟙 U.left)) = U :=
    StacksRepresentableCFG.forget_obj_iteratedSliceBackward_id U
  have hy₀ : 𝒴.val.p.obj (y.obj (Over.mk (𝟙 U.left))) = U :=
    (Functor.congr_obj hy (Over.mk (𝟙 U.left))).trans hUid
  obtain ⟨R, hR, hlift⟩ := hg U ⟨y.obj (Over.mk (𝟙 U.left)), hy₀⟩
  obtain ⟨I, W, m, hmem, hflat, hlfp, hsurj⟩ :=
    exists_family_of_mem_topology B S hS (U := U) hR
  choose ι hι using hsurj
  let V' : (B.inclusion.obj U.left) → BigFppfOver B S hS :=
    fun x => Over.mk (m (ι x) ≫ U.hom)
  let k' : ∀ x, V' x ⟶ U := fun x => Over.homMk (m (ι x))
  have hcov := Space.ofArrows_yoneda_mem_fppfPrecoverage.{u, u} B S hS (U := U) V' k'
    (fun x => hflat (ι x)) (fun x => hlfp (ι x)) (fun x => by
      obtain ⟨z, hz⟩ := hι x
      exact ⟨x, z, hz⟩)
  refine (Space.prop_relocalizeToYoneda_iff B S hS P U F hF).1 ?_
  refine (MorphismProperty.IsLocalAtTarget.iff_of_forall_pullbackSnd
    (P := P) (K := Space.Topology.fppf.precoverage.{u, u} B S hS) hcov).2 ?_
  intro T q hpb hq
  obtain ⟨x⟩ := hq
  have hFx : IsAlgebraicSpace B (W (ι x)).1 (W (ι x)).2
      ((relocalizeRestrict (m (ι x))).obj F) :=
    isAlgebraicSpace_relocalizeRestrict B (W (ι x)).1 U.left.1 (W (ι x)).2 U.left.2
      (m (ι x)) F hF
  have hΛF := Space.isAlgebraicSpace_relocalizePresheaf B S hS U F hF
  have hΛFx := Space.isAlgebraicSpace_relocalizePresheaf B S hS (V' x)
    ((relocalizeRestrict (m (ι x))).obj F) hFx
  have hc := OverShriek.isPullback_relocalizeRestrictMap U.hom (m (ι x)) F
  have hsq : IsPullback
      (ObjectProperty.homMk (relocalizeRestrictMap U.hom (m (ι x)) F) :
        (⟨_, hΛFx⟩ : AlgebraicSpaces B S hS) ⟶ ⟨_, hΛF⟩)
      (ObjectProperty.homMk
          (relocalizeToYoneda (m (ι x) ≫ U.hom) ((relocalizeRestrict (m (ι x))).obj F)) :
        (⟨_, hΛFx⟩ : AlgebraicSpaces B S hS) ⟶
          ⟨yoneda.obj (V' x), isAlgebraicSpace_yoneda B S hS (V' x)⟩)
      (ObjectProperty.homMk (relocalizeToYoneda U.hom F) :
        (⟨_, hΛF⟩ : AlgebraicSpaces B S hS) ⟶
          ⟨yoneda.obj U, isAlgebraicSpace_yoneda B S hS U⟩)
      (ObjectProperty.homMk (yoneda.map (k' x))) :=
    IsPullback.of_map_of_faithful (ObjectProperty.ι _) hc
  rw [← P.cancel_left_of_respectsIso hsq.isoPullback.hom, hsq.isoPullback_hom_snd]
  refine (Space.prop_relocalizeToYoneda_iff B S hS P (V' x) _ hFx).2 ?_
  obtain ⟨j, z, φ, hφ⟩ := hlift (hmem (ι x))
  have hz₀ : (𝒵 j).val.p.obj z = V' x :=
    (Functor.congr_obj (g j).hom.w z).symm.trans
      (CategoryTheory.IsHomLift.domain_eq 𝒴.val.p (k' x) φ)
  obtain ⟨zp, hzp, ξ, hξ⟩ :=
    StacksRepresentableCFG.exists_pointOverMap_of_obj (𝒵 j).val.p (𝒵 j).property (V' x) z hz₀
  have hVid : (Over.map (V' x).hom).obj (Over.mk (𝟙 (V' x).left)) = V' x :=
    StacksRepresentableCFG.forget_obj_iteratedSliceBackward_id (V' x)
  have hu₁ : (zp ⋙ CatFiberedInGroupoids.homFunctor (g j)) ⋙ 𝒴.val.p
      = Over.map (V' x).hom := by
    rw [Functor.assoc, (g j).hom.w, hzp]
  have hu₂ : (Over.map (m (ι x)) ⋙ y) ⋙ 𝒴.val.p = Over.map (V' x).hom := by
    rw [Functor.assoc, hy, ← Over.mapComp_eq]
    rfl
  have hid₂ : 𝒴.val.p.obj
      ((Over.map (m (ι x)) ⋙ y).obj (Over.mk (𝟙 (V' x).left))) = V' x :=
    (Functor.congr_obj hu₂ (Over.mk (𝟙 (V' x).left))).trans hVid
  have hξ' : 𝒴.val.p.IsHomLift (𝟙 (V' x))
      ((CatFiberedInGroupoids.homFunctor (g j)).map ξ.hom) := by
    have _ := hξ
    exact Functor.isHomLift_map_of_comp_eq (g j).hom.w (𝟙 (V' x)) ξ.hom
  have hψ₁ : 𝒴.val.p.IsHomLift (𝟙 (V' x) ≫ k' x)
      ((CatFiberedInGroupoids.homFunctor (g j)).map ξ.hom ≫ φ) := by
    have _ := hξ'
    have _ := hφ
    exact CategoryTheory.IsHomLift.comp 𝒴.val.p (𝟙 (V' x)) (k' x) _ _
  have hσ : 𝒴.val.p.IsHomLift (k' x)
      (y.map (StacksRepresentableCFG.toTautological
        ((Over.map (m (ι x))).obj (Over.mk (𝟙 (V' x).left))))) := by
    refine CategoryTheory.IsHomLift.of_fac' _ (k' x) _
      hid₂ hy₀ ?_
    have hcg := Functor.congr_hom hy (StacksRepresentableCFG.toTautological
      ((Over.map (m (ι x))).obj (Over.mk (𝟙 (V' x).left))))
    rw [show 𝒴.val.p.map (y.map (StacksRepresentableCFG.toTautological
        ((Over.map (m (ι x))).obj (Over.mk (𝟙 (V' x).left)))))
      = (y ⋙ 𝒴.val.p).map (StacksRepresentableCFG.toTautological
        ((Over.map (m (ι x))).obj (Over.mk (𝟙 (V' x).left)))) from rfl, hcg]
    refine Over.OverMorphism.ext ?_
    simp [k']
  obtain ⟨θ, hθ⟩ : ∃ θ : (zp ⋙ CatFiberedInGroupoids.homFunctor (g j)).obj
        (Over.mk (𝟙 (V' x).left)) ≅
        (Over.map (m (ι x)) ⋙ y).obj (Over.mk (𝟙 (V' x).left)),
      𝒴.val.p.IsHomLift
        (𝟙 ((Over.map (V' x).hom).obj (Over.mk (𝟙 (V' x).left)))) θ.hom := by
    have _ := hσ
    have _ := hψ₁
    have _ : 𝒴.val.p.IsHomLift (𝟙 (V' x))
        (𝟙 ((Over.map (m (ι x)) ⋙ y).obj (Over.mk (𝟙 (V' x).left)))) :=
      CategoryTheory.IsHomLift.id hid₂
    have hiso := 𝒴.property.isHomLift_twoStepLiftIso_hom (𝟙 (V' x)) (k' x)
      (y.map (StacksRepresentableCFG.toTautological
        ((Over.map (m (ι x))).obj (Over.mk (𝟙 (V' x).left)))))
      (𝟙 ((Over.map (m (ι x)) ⋙ y).obj (Over.mk (𝟙 (V' x).left))))
      ((CatFiberedInGroupoids.homFunctor (g j)).map ξ.hom ≫ φ)
    refine ⟨(𝒴.property.twoStepLiftIso (𝟙 (V' x)) (k' x)
      (y.map (StacksRepresentableCFG.toTautological
        ((Over.map (m (ι x))).obj (Over.mk (𝟙 (V' x).left)))))
      (𝟙 ((Over.map (m (ι x)) ⋙ y).obj (Over.mk (𝟙 (V' x).left))))
      ((CatFiberedInGroupoids.homFunctor (g j)).map ξ.hom ≫ φ)).symm, ?_⟩
    rw [hVid]
    have _ := hiso
    exact CategoryTheory.IsHomLift.lift_id_inv 𝒴.val.p (V' x) _
  obtain ⟨α, hα⟩ := StacksRepresentableCFG.exists_natIso_of_iso_at_id (V' x).hom
    (zp ⋙ CatFiberedInGroupoids.homFunctor (g j)) (Over.map (m (ι x)) ⋙ y) hu₁ hu₂
    𝒴.property θ hθ
  obtain ⟨E1⟩ := nonempty_baseChangeEquivalenceOver.{u, v, w} B S hS 𝒳 𝒴 (𝒵 j) f (g j) (D j) (hD j)
    (V' x) zp hzp
  obtain ⟨E3⟩ := nonempty_equivalenceOver_relocalizeRestrict U.hom (m (ι x)) F y
    (CatFiberedInGroupoids.homFunctor f) hy f.hom.w 𝒳.property 𝒴.property E
  exact hP j (V' x) zp hzp _ hFx
    ⟨E1.trans ((TwoFibreProductOver.reindexEquivalenceOver α hα).trans E3)⟩

end AlgebraicGeometry.Stack

end
