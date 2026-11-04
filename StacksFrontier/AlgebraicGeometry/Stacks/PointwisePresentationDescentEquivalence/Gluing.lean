module

public import StacksFrontier.AlgebraicGeometry.Stacks.PointwisePresentationDescentEquivalence.Cocycle

/-!
# The descent datum of a quasi-coherent module on a groupoid, and its gluing

Given a quasi-coherent module `(𝒢, α)` on the groupoid `(U, R, s, t, c)`, the descent datum
`(M, β)` on the pointwise groupoid fibration `[U/_pR]` attached to it, and the quasi-coherent
module on `[U/_pR]` glued from it, with the comparison lemmas used to compute its image under the
descent functor.

## Main definitions

* `AlgebraicGeometry.Stack.pointwiseDatumOfQuasicoherent`: the descent datum `(M, β)` attached
  to a quasi-coherent module on the groupoid.
* `AlgebraicGeometry.Stack.pointwiseSheafOfQuasicoherent`: the quasi-coherent module on
  `[U/_pR]` glued from it.
-/

@[expose] public noncomputable section

open CategoryTheory Opposite

universe u v w

namespace AlgebraicGeometry.Stack

variable {C : BigFppfSite.{u}} {S : Scheme.{u}} {hS : C.Contains S}

/-! ### The descent datum of a quasi-coherent module on the groupoid -/

section Datum

variable {A : AlgebraicSpaces C S hS} (G : GroupoidInAlgebraicSpaces C S hS A)
  (M : FibredSite.quasicoherentModules.{u, u + 1, u, u} C S hS (spaceProj G.objects)
    (isFiberedInGroupoids_spaceProj G.objects))
  (α : (Space.modulePullback C S hS G.target).obj (selfChartRestriction M.obj) ⟶
    (Space.modulePullback C S hS G.source).obj (selfChartRestriction M.obj))

/-- The descent morphism attached to the transition `α`, as a morphism `t^*M ⟶ s^*M` of the
modules of the descent datum (`AlgebraicGeometry.Stack.PointwiseDescentDatum`). -/
def descentDatumMorphism : (targetPullback G).obj M.obj ⟶ (sourcePullback G).obj M.obj :=
  descentMorphismOfTransition G.target G.source M α

/-- The component of the descent morphism, in the spelling of the fppf site of `𝒮_R`. -/
theorem descComp_descentDatumMorphism (T : BigFppfOver C S hS) (r : G.arrows.obj.obj (op T)) :
    descComp (descentDatumMorphism G M α) T r =
      ((PresheafOfModules.toPresheaf (spaceRing G.arrows).obj).map
        (descentMorphismOfTransition G.target G.source M α).val).app
          (op (⟨T, ⟨r⟩⟩ : spaceCat G.arrows)) := rfl

open GroupoidInAlgebraicSpaces in
/-- **The unit condition, module-level**: if the transition `α` satisfies the unit condition, the
inverse image along the unit `e : U ⟶ R` of its descent morphism is the
transport `e^*t^*M = e^*s^*M`. -/
theorem spacePullback_identityArrow_map_descentMorphism
    (hu : Space.groupoidPullbackTransition C S hS G
        (Space.etaleRestrictedModuleInverseImage C S hS (spaceProj G.objects) (spaceProj G.objects)
          (isFiberedInGroupoids_spaceProj G.objects) (isFiberedInGroupoids_spaceProj G.objects)
          (spacePresentation G.objects) (𝟭 _) (isFibredOneMorphism_spaceId G.objects)
          (spaceEtale M.obj)) α (identityArrow G) =
      Space.pullbackTransport (selfChartRestriction M.obj)
        ((identityArrow_comp_target G).trans (identityArrow_comp_source G).symm)) :
    (spacePullback (identityArrow G)).map (descentMorphismOfTransition G.target G.source M α) =
      eqToHom (spacePullback_comp_obj_eq _ _ _ M.obj
        ((identityArrow_comp_target G).trans (identityArrow_comp_source G).symm)) := by
  have : IsIso (compComparison (identityArrow G) G.target M.obj) :=
    (inferInstance : IsIso (spaceEtaleInverseImageComparison (identityArrow G ≫ G.target) M.obj))
  apply eq_of_selfChartRestrictionMap_eq
    (P₁ := spaceQuasicoherentPullback (spaceQuasicoherentPullback M G.target) (identityArrow G))
    (P₂ := spaceQuasicoherentPullback (spaceQuasicoherentPullback M G.source) (identityArrow G))
  rw [Space.groupoidPullbackTransition, Iso.app_inv, Iso.app_hom] at hu
  rw [selfChartRestrictionMap_spacePullback_map_eq_eqToHom G.target G.source M.obj _ α
    (descentMorphismOfTransition_spec G.target G.source M α) _ _ hu,
    selfChartRestrictionMap_eqToHom]

open GroupoidInAlgebraicSpaces in
/-- **The unit condition of the descent morphism**, pointwise. -/
theorem descComp_descentMorphism_identity
    (hu : Space.groupoidPullbackTransition C S hS G
        (Space.etaleRestrictedModuleInverseImage C S hS (spaceProj G.objects) (spaceProj G.objects)
          (isFiberedInGroupoids_spaceProj G.objects) (isFiberedInGroupoids_spaceProj G.objects)
          (spacePresentation G.objects) (𝟭 _) (isFibredOneMorphism_spaceId G.objects)
          (spaceEtale M.obj)) α (identityArrow G) =
      Space.pullbackTransport (selfChartRestriction M.obj)
        ((identityArrow_comp_target G).trans (identityArrow_comp_source G).symm))
    (T : BigFppfOver C S hS) (a : G.objects.obj.obj (op T)) :
    descComp (descentDatumMorphism G M α) T (G.toGroupoidInFunctors.identity (op T) a) =
      ptTransport M.obj ((source_identity G T a).trans (target_identity G T a).symm) := by
  have hm : (stackPullback (identityArrow G)).map (descentDatumMorphism G M α) =
      eqToHom (spacePullback_comp_obj_eq _ _ _ M.obj
        ((identityArrow_comp_target G).trans (identityArrow_comp_source G).symm) :
          (stackPullback (identityArrow G)).obj ((targetPullback G).obj M.obj) =
            (stackPullback (identityArrow G)).obj ((sourcePullback G).obj M.obj)) :=
    spacePullback_identityArrow_map_descentMorphism G M α hu
  have h := toPresheaf_map_val_app_of_modulePullback_map_eq_eqToHom _ _ _ _ _ _
    (descentDatumMorphism G M α) _ hm (objPt G T a)
  have hW : (spaceFunctor (identityArrow G)).obj (objPt G T a) =
      (⟨T, ⟨G.toGroupoidInFunctors.identity (op T) a⟩⟩ : spaceCat G.arrows) :=
    (spaceFunctor_obj_mk (identityArrow G) T a).trans
      (congrArg (fun r => (⟨T, ⟨r⟩⟩ : spaceCat G.arrows)) (identityArrow_hom_app G (op T) a))
  refine (descComp_eq_eqToHom_comp (descentDatumMorphism G M α) T _ _ hW).trans ?_
  rw [h]
  refine Eq.trans ?_ (ptTransport_eq_eqToHom _ _).symm
  exact eqToHom_comp_eqToHom_comp_eqToHom _ _ _ _

/-- `nestedComparison_comp_restrictionMap` for the descent morphism, with the reindexed
transition. -/
theorem nestedComparison_comp_restrictionMap_descent {X : AlgebraicSpaces C S hS}
    (k : X ⟶ G.arrows) :
    nestedComparison k G.target M.obj ≫
        selfChartRestrictionMap (M := (spacePullback k).obj ((spacePullback G.target).obj M.obj))
          (M' := (spacePullback k).obj ((spacePullback G.source).obj M.obj))
          ((spacePullback k).map (descentMorphismOfTransition G.target G.source M α)) =
      Space.groupoidPullbackTransition C S hS G
        (Space.etaleRestrictedModuleInverseImage C S hS (spaceProj G.objects) (spaceProj G.objects)
          (isFiberedInGroupoids_spaceProj G.objects) (isFiberedInGroupoids_spaceProj G.objects)
          (spacePresentation G.objects) (𝟭 _) (isFibredOneMorphism_spaceId G.objects)
          (spaceEtale M.obj)) α k ≫ nestedComparison k G.source M.obj :=
  nestedComparison_comp_restrictionMap _ _ M.obj _ α
    (descentMorphismOfTransition_spec G.target G.source M α) k

open GroupoidInAlgebraicSpaces in
/-- **The cocycle condition, module-level**: if the transition `α` satisfies the cocycle
condition, the inverse image along the composition `c` of its descent morphism is
the composite of its inverse images along the two projections, through the transports. -/
theorem spacePullback_comp_map_descentMorphism
    (hc : Space.groupoidPullbackTransition C S hS G
        (Space.etaleRestrictedModuleInverseImage C S hS (spaceProj G.objects) (spaceProj G.objects)
          (isFiberedInGroupoids_spaceProj G.objects) (isFiberedInGroupoids_spaceProj G.objects)
          (spacePresentation G.objects) (𝟭 _) (isFibredOneMorphism_spaceId G.objects)
          (spaceEtale M.obj)) α G.comp =
      Space.groupoidTransitionComposite C S hS G
        (Space.etaleRestrictedModuleInverseImage C S hS (spaceProj G.objects) (spaceProj G.objects)
          (isFiberedInGroupoids_spaceProj G.objects) (isFiberedInGroupoids_spaceProj G.objects)
          (spacePresentation G.objects) (𝟭 _) (isFibredOneMorphism_spaceId G.objects)
          (spaceEtale M.obj)) α) :
    (spacePullback G.comp).map (descentMorphismOfTransition G.target G.source M α) =
      eqToHom (spacePullback_comp_obj_eq _ _ _ M.obj (comp_comp_target G)) ≫
        (spacePullback (firstArrow G)).map (descentMorphismOfTransition G.target G.source M α) ≫
          eqToHom (spacePullback_comp_obj_eq _ _ _ M.obj (firstArrow_comp_source G)) ≫
            (spacePullback (secondArrow G)).map
              (descentMorphismOfTransition G.target G.source M α) ≫
              eqToHom (spacePullback_comp_obj_eq _ _ _ M.obj (comp_comp_source G).symm) := by
  have : IsIso (compComparison G.comp G.target M.obj) :=
    (inferInstance : IsIso (spaceEtaleInverseImageComparison (G.comp ≫ G.target) M.obj))
  refine eq_of_selfChartRestrictionMap_eq'
    (N₁ := (spacePullback G.comp).obj ((spacePullback G.target).obj M.obj))
    (N₂ := (spacePullback G.comp).obj ((spacePullback G.source).obj M.obj))
    (spaceQuasicoherentPullback (spaceQuasicoherentPullback M G.target) G.comp).property
    (spaceQuasicoherentPullback (spaceQuasicoherentPullback M G.source) G.comp).property ?_
  rw [selfChartRestrictionMap_comp, selfChartRestrictionMap_comp, selfChartRestrictionMap_comp,
    selfChartRestrictionMap_comp, selfChartRestrictionMap_eqToHom, selfChartRestrictionMap_eqToHom,
    selfChartRestrictionMap_eqToHom]
  have hΦ : IsIso (nestedComparison G.comp G.target M.obj) := inferInstance
  have key := cocycle_of_comparisons G
    (Space.etaleRestrictedModuleInverseImage C S hS (spaceProj G.objects) (spaceProj G.objects)
      (isFiberedInGroupoids_spaceProj G.objects) (isFiberedInGroupoids_spaceProj G.objects)
      (spacePresentation G.objects) (𝟭 _) (isFibredOneMorphism_spaceId G.objects)
      (spaceEtale M.obj)) α hc _ _ _ _ _ _ _ _ _ _ _ _ hΦ
    (nestedComparison_comp_restrictionMap_descent G M α G.comp)
    (nestedComparison_comp_restrictionMap_descent G M α (firstArrow G))
    (nestedComparison_comp_restrictionMap_descent G M α (secondArrow G))
    (pullbackTransport_comp_nestedComparison (comp_comp_target G) M.obj)
    (pullbackTransport_comp_nestedComparison (firstArrow_comp_source G) M.obj)
    (pullbackTransport_comp_nestedComparison (comp_comp_source G).symm M.obj)
  exact key

open GroupoidInAlgebraicSpaces in
/-- **The cocycle condition of the descent morphism**, pointwise. -/
theorem descComp_descentMorphism_compose
    (hc : Space.groupoidPullbackTransition C S hS G
        (Space.etaleRestrictedModuleInverseImage C S hS (spaceProj G.objects) (spaceProj G.objects)
          (isFiberedInGroupoids_spaceProj G.objects) (isFiberedInGroupoids_spaceProj G.objects)
          (spacePresentation G.objects) (𝟭 _) (isFibredOneMorphism_spaceId G.objects)
          (spaceEtale M.obj)) α G.comp =
      Space.groupoidTransitionComposite C S hS G
        (Space.etaleRestrictedModuleInverseImage C S hS (spaceProj G.objects) (spaceProj G.objects)
          (isFiberedInGroupoids_spaceProj G.objects) (isFiberedInGroupoids_spaceProj G.objects)
          (spacePresentation G.objects) (𝟭 _) (isFibredOneMorphism_spaceId G.objects)
          (spaceEtale M.obj)) α)
    (T : BigFppfOver C S hS) (a b : G.arrows.obj.obj (op T))
    (h : G.source.hom.app (op T) a = G.target.hom.app (op T) b) :
    descComp (descentDatumMorphism G M α) T (G.toGroupoidInFunctors.compose (op T) a b h) =
      ptTransport M.obj (target_compose G T a b h).symm ≫
        descComp (descentDatumMorphism G M α) T a ≫
        ptTransport M.obj h.symm ≫ descComp (descentDatumMorphism G M α) T b ≫
          ptTransport M.obj (source_compose G T a b h) :=
  descComp_compose_of_spacePullback_map_eq G M.obj _
    (spacePullback_comp_map_descentMorphism G M α hc) T a b h

end Datum


/-! ### Transport of a transition along an isomorphism -/

section TransitionTransport

variable {A : AlgebraicSpaces C S hS} {G : GroupoidInAlgebraicSpaces C S hS A}
  {F' : Space.Modules.{u, u} C S hS G.objects.1 G.objects.2}
  (Q : Space.QuasicoherentModule C S hS G) (e : F' ≅ Q.F.obj)

/-- The transition of `Q` transported to `F'` along `e : F' ≅ Q.F`. -/
def transportedTransition :
    (Space.modulePullback C S hS G.target).obj F' ⟶ (Space.modulePullback C S hS G.source).obj F' :=
  (Space.modulePullback C S hS G.target).map e.hom ≫ Q.alpha ≫
    (Space.modulePullback C S hS G.source).map e.inv

/-- `e` intertwines the transported transition with the transition of `Q`. -/
theorem transportedTransition_comm :
    transportedTransition Q e ≫ (Space.modulePullback C S hS G.source).map e.hom =
      (Space.modulePullback C S hS G.target).map e.hom ≫ Q.alpha := by
  rw [transportedTransition, Category.assoc, Category.assoc, ← CategoryTheory.Functor.map_comp,
    e.inv_hom_id, CategoryTheory.Functor.map_id, Category.comp_id]

open GroupoidInAlgebraicSpaces in
/-- The transported transition satisfies the unit condition. -/
theorem transportedTransition_unit :
    Space.groupoidPullbackTransition C S hS G F' (transportedTransition Q e) (identityArrow G) =
      Space.pullbackTransport F'
        ((identityArrow_comp_target G).trans (identityArrow_comp_source G).symm) := by
  have n := Space.groupoidPullbackTransition_naturality C S hS G e.hom
    (transportedTransition_comm Q e) (identityArrow G)
  rw [Q.unit, Space.pullbackTransport_naturality] at n
  exact (((Space.modulePullback C S hS (identityArrow G ≫ G.source)).mapIso e).cancel_iso_hom_right
    _ _).1 n.symm

open GroupoidInAlgebraicSpaces in
/-- The transported transition satisfies the cocycle condition. -/
theorem transportedTransition_cocycle :
    Space.groupoidPullbackTransition C S hS G F' (transportedTransition Q e) G.comp =
      Space.groupoidTransitionComposite C S hS G F' (transportedTransition Q e) := by
  have n₁ := Space.groupoidPullbackTransition_naturality C S hS G e.hom
    (transportedTransition_comm Q e) G.comp
  have n₂ := Space.groupoidTransitionComposite_naturality C S hS G e.hom
    (transportedTransition_comm Q e)
  rw [Q.cocycle, n₂] at n₁
  exact (((Space.modulePullback C S hS (G.comp ≫ G.source)).mapIso e).cancel_iso_hom_right
    _ _).1 n₁.symm

end TransitionTransport

/-! ### The descent datum of a quasi-coherent module on the groupoid -/

section DatumOfQuasicoherent

variable {A : AlgebraicSpaces C S hS} (G : GroupoidInAlgebraicSpaces C S hS A)
  (Q : Space.QuasicoherentModule C S hS G)

/-- A quasi-coherent module on `𝒮_U` whose restriction to `U_étale` is `Q.F`. -/
def chartPreimage : FibredSite.quasicoherentModules.{u, u + 1, u, u} C S hS (spaceProj G.objects)
    (isFiberedInGroupoids_spaceProj G.objects) :=
  (spaceQuasicoherentRestriction G.objects).objPreimage Q.F

/-- The identification of the restriction of `chartPreimage G Q` to `U_étale` with `Q.F`. -/
def chartPreimageIso : Space.etaleRestrictedModuleInverseImage C S hS (spaceProj G.objects)
        (spaceProj G.objects) (isFiberedInGroupoids_spaceProj G.objects)
        (isFiberedInGroupoids_spaceProj G.objects) (spacePresentation G.objects) (𝟭 _)
        (isFibredOneMorphism_spaceId G.objects) (spaceEtale (chartPreimage G Q).obj) ≅ Q.F.obj :=
  (ObjectProperty.ι _).mapIso ((spaceQuasicoherentRestriction G.objects).objObjPreimageIso Q.F)

/-- The transition of `Q`, transported to the restriction of `chartPreimage G Q`. -/
def chartTransition :
    (Space.modulePullback C S hS G.target).obj
      (Space.etaleRestrictedModuleInverseImage C S hS (spaceProj G.objects)
        (spaceProj G.objects) (isFiberedInGroupoids_spaceProj G.objects)
        (isFiberedInGroupoids_spaceProj G.objects) (spacePresentation G.objects) (𝟭 _)
        (isFibredOneMorphism_spaceId G.objects) (spaceEtale (chartPreimage G Q).obj)) ⟶
      (Space.modulePullback C S hS G.source).obj
        (Space.etaleRestrictedModuleInverseImage C S hS (spaceProj G.objects)
          (spaceProj G.objects) (isFiberedInGroupoids_spaceProj G.objects)
          (isFiberedInGroupoids_spaceProj G.objects) (spacePresentation G.objects) (𝟭 _)
          (isFibredOneMorphism_spaceId G.objects) (spaceEtale (chartPreimage G Q).obj)) :=
  transportedTransition Q (chartPreimageIso G Q)

/-- **The pointwise descent datum of a quasi-coherent module on the groupoid.** -/
def pointwiseDatumOfQuasicoherent : PointwiseDescentDatum G where
  M := (chartPreimage G Q).obj
  β := descentDatumMorphism G (chartPreimage G Q) (chartTransition G Q)
  unit := descComp_descentMorphism_identity G (chartPreimage G Q) (chartTransition G Q)
    (transportedTransition_unit Q (chartPreimageIso G Q))
  cocycle := descComp_descentMorphism_compose G (chartPreimage G Q) (chartTransition G Q)
    (transportedTransition_cocycle Q (chartPreimageIso G Q))

/-- The glued module of the descent datum of `Q` is quasi-coherent. -/
theorem isQuasicoherentOnSite_pointwiseDatumOfQuasicoherent_sheaf :
    (pointwiseDatumOfQuasicoherent G Q).sheaf.IsQuasicoherentOnSite :=
  (isQuasicoherentOnSite_objectRestriction_iff _).1
    (SheafOfModules.IsQuasicoherentOnSite.of_iso
      (pointwiseDatumOfQuasicoherent G Q).sheafRestrictionIso.symm (chartPreimage G Q).property)

/-- **The quasi-coherent module on the pointwise groupoid fibration glued from `Q`.** -/
def pointwiseSheafOfQuasicoherent : FibredSite.quasicoherentModules.{u, u + 1, u, u} C S hS
    (presheafOfGroupoids (evaluationGroupoidFunctor G.toGroupoidInFunctors)).p
    (isFiberedInGroupoids_presheafOfGroupoids _) :=
  ⟨(pointwiseDatumOfQuasicoherent G Q).sheaf,
    isQuasicoherentOnSite_pointwiseDatumOfQuasicoherent_sheaf G Q⟩

end DatumOfQuasicoherent

end AlgebraicGeometry.Stack


namespace AlgebraicGeometry.Space

universe v₁ w₁ v₂ w₂ v₃ w₃

section WhiskerRightUnitor

variable (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)
  {U V : AlgebraicSpaces B S hS}
  {𝒰 : Type v₁} [Category.{w₁} 𝒰] {𝒱 : Type v₂} [Category.{w₂} 𝒱]
  {𝒳 : Type v₃} [Category.{w₃} 𝒳]
  (p : 𝒰 ⥤ BigFppfOver B S hS) (q : 𝒱 ⥤ BigFppfOver B S hS) (r : 𝒳 ⥤ BigFppfOver B S hS)
  (hp : p.IsFiberedInGroupoids) (hq : q.IsFiberedInGroupoids) (hr : r.IsFiberedInGroupoids)
  (eU : StacksRepresentableCFG.EquivalenceOver p
    (presheafOfCategories (U.1 ⋙ typeToCat)).p)
  (eV : StacksRepresentableCFG.EquivalenceOver q
    (presheafOfCategories (V.1 ⋙ typeToCat)).p)

/-- **The comparison map of the triangle `a ⋙ 𝟭 = a` whiskered by `K`** is the comparison map of
the strictly commuting triangle `a ⋙ (K ⋙ 𝟭) = a ⋙ (K ⋙ 𝟭)`. -/
theorem comparisonAlgebraicSpacesModules_whiskerTriangleIso_rightUnitor (a : 𝒰 ⥤ 𝒱) (K : 𝒱 ⥤ 𝒳)
    (aSpace : U ⟶ V) (hf : p.IsFibredOneMorphism r (a ⋙ K))
    (hg : q.IsFibredOneMorphism r (𝟭 _ ⋙ K)) (hf' : p.IsFibredOneMorphism r (a ⋙ (K ⋙ 𝟭 _)))
    (hg' : q.IsFibredOneMorphism r (K ⋙ 𝟭 _))
    (ha : schemeChartFunctor B S hS U.1 p eU ⋙ a ≅
      CostructuredArrow.map aSpace.hom ⋙ schemeChartFunctor B S hS V.1 q eV)
    (hφ : ∀ X : 𝒰, r.IsHomLift (𝟙 (r.obj ((a ⋙ K).obj X)))
      ((whiskerTriangleIso K a a (𝟭 _) (Functor.rightUnitor a)).inv.app X))
    (hφ' : ∀ X : 𝒰, r.IsHomLift (𝟙 (r.obj ((a ⋙ (K ⋙ 𝟭 _)).obj X)))
      ((Iso.refl (a ⋙ (K ⋙ 𝟭 _))).inv.app X))
    (hab : ∀ Z : CostructuredArrow yoneda U.1,
      q.IsHomLift (𝟙 (q.obj (a.obj ((schemeChartFunctor B S hS U.1 p eU).obj Z))))
        (ha.hom.app Z))
    (ℱ : inheritedEtaleModules B S hS r hr) :
    comparisonAlgebraicSpacesModules B S hS p q r hp hq eU eV a (a ⋙ K) (𝟭 _ ⋙ K) hf hg
        (whiskerTriangleIso K a a (𝟭 _) (Functor.rightUnitor a)) aSpace ha hr hφ hab ℱ =
      comparisonAlgebraicSpacesModules B S hS p q r hp hq eU eV a (a ⋙ (K ⋙ 𝟭 _)) (K ⋙ 𝟭 _)
        hf' hg' (Iso.refl _) aSpace ha hr hφ' hab ℱ :=
  comparisonAlgebraicSpacesModules_congr B S hS p q r hp hq hr eU eV (a ⋙ K) (𝟭 _ ⋙ K) hf hg
    aSpace a a (whiskerTriangleIso K a a (𝟭 _) (Functor.rightUnitor a)) (Iso.refl _) ha ha hφ hφ'
    hab hab ℱ (fun d => by simp [comparisonMorphism])

end WhiskerRightUnitor

end AlgebraicGeometry.Space

namespace AlgebraicGeometry.Stack

variable {C : BigFppfSite.{u}} {S : Scheme.{u}} {hS : C.Contains S}

section PullbackRightUnitor

universe v₁ w₁

variable {𝒳 : Type v₁} [Category.{w₁} 𝒳] {p : 𝒳 ⥤ BigFppfOver C S hS}
  (hp : p.IsFiberedInGroupoids) {X Y : AlgebraicSpaces C S hS}

/-- **The comparison map along `k` of `K^*N` is the comparison map along `k` of `N` for the
1-morphism `K ⋙ 𝟭`**, through the identifications of
`AlgebraicGeometry.Stack.pullbackRestrictionIso`. -/
theorem spaceEtaleInverseImageComparison_pullbackFunctor (k : X ⟶ Y) (K : spaceCat Y ⥤ 𝒳)
    (hK : K ⋙ p = spaceProj Y)
    (hfK : (spaceProj X).IsFibredOneMorphism p (spaceFunctor k ⋙ K))
    (hgK : (spaceProj Y).IsFibredOneMorphism p (𝟭 _ ⋙ K))
    (hf' : (spaceProj X).IsFibredOneMorphism p (spaceFunctor k ⋙ (K ⋙ 𝟭 _)))
    (hg' : (spaceProj Y).IsFibredOneMorphism p (K ⋙ 𝟭 _))
    (hφ' : ∀ W : spaceCat X, p.IsHomLift (𝟙 (p.obj ((spaceFunctor k ⋙ (K ⋙ 𝟭 _)).obj W)))
      ((Iso.refl (spaceFunctor k ⋙ (K ⋙ 𝟭 _))).inv.app W))
    (N : SheafOfModules.{u} (Stack.ringStructureSheafCore C S hS p hp C.topology le_rfl)) :
    Space.comparisonAlgebraicSpacesModules C S hS (spaceProj X) (spaceProj Y)
        (spaceProj Y) (isFiberedInGroupoids_spaceProj X) (isFiberedInGroupoids_spaceProj Y)
        (spacePresentation X) (spacePresentation Y) (spaceFunctor k)
        (spaceFunctor k) (𝟭 _) (isFibredOneMorphism_spaceFunctor _)
        (isFibredOneMorphism_spaceId _) (Functor.rightUnitor _) k
        (spaceFunctorChartIso k) (isFiberedInGroupoids_spaceProj Y)
        (isHomLift_spaceRightUnitor_inv_app k)
        (isHomLift_spaceFunctorChartIso_hom_app k)
        (Space.stackEtale C S hS _ (isFiberedInGroupoids_spaceProj Y)
          ((Stack.modulePullback C S hS (spaceProj Y) p (isFiberedInGroupoids_spaceProj Y)
            hp K hK C.topology le_rfl).obj N)) ≫
      (pullbackRestrictionIso (spaceProj Y) (isFiberedInGroupoids_spaceProj Y) K hK hp (spaceProj X)
        (isFiberedInGroupoids_spaceProj X) (spacePresentation X) (spaceFunctor k)
        (isFibredOneMorphism_spaceFunctor k) hfK N).hom =
    (Space.modulePullback C S hS k).map (pullbackRestrictionIso (spaceProj Y)
        (isFiberedInGroupoids_spaceProj Y) K hK hp (spaceProj Y) (isFiberedInGroupoids_spaceProj Y)
        (spacePresentation Y) (𝟭 _) (isFibredOneMorphism_spaceId Y) hgK N).hom ≫
      Space.comparisonAlgebraicSpacesModules C S hS (spaceProj X) (spaceProj Y) p
        (isFiberedInGroupoids_spaceProj X) (isFiberedInGroupoids_spaceProj Y)
        (spacePresentation X) (spacePresentation Y) (spaceFunctor k)
        (spaceFunctor k ⋙ (K ⋙ 𝟭 _)) (K ⋙ 𝟭 _) hf' hg' (Iso.refl _) k (spaceFunctorChartIso k) hp
        hφ' (isHomLift_spaceFunctorChartIso_hom_app k) (Space.stackEtale C S hS p hp N) := by
  have hφ := fun W => Space.isHomLift_whiskerTriangleIso_inv_app C S hS _ _ K
    (isFibredOneMorphism_pullbackFunctor _ _ hK hp) _ _ _ _
    (isHomLift_spaceRightUnitor_inv_app k) W
  have h1 := comparisonAlgebraicSpacesModules_pullbackFunctor (spaceProj Y)
    (isFiberedInGroupoids_spaceProj Y) K hK hp (spaceProj X)
    (isFiberedInGroupoids_spaceProj X) (spacePresentation X) (spaceProj Y)
    (isFiberedInGroupoids_spaceProj Y) (spacePresentation Y)
    (spaceFunctor k) (spaceFunctor k) (𝟭 _) (isFibredOneMorphism_spaceFunctor _)
    (isFibredOneMorphism_spaceId _) hfK hgK (Functor.rightUnitor _) k
    (spaceFunctorChartIso k) (isHomLift_spaceRightUnitor_inv_app k)
    (isHomLift_spaceFunctorChartIso_hom_app k) hφ N
  have h2 := Space.comparisonAlgebraicSpacesModules_whiskerTriangleIso_rightUnitor C S hS
    (spaceProj X) (spaceProj Y) p (isFiberedInGroupoids_spaceProj X)
    (isFiberedInGroupoids_spaceProj Y) hp (spacePresentation X) (spacePresentation Y)
    (spaceFunctor k) K k hfK hgK hf' hg' (spaceFunctorChartIso k)
    hφ hφ'
    (isHomLift_spaceFunctorChartIso_hom_app k) (Space.stackEtale C S hS p hp N)
  exact h1.trans (congrArg (fun c => _ ≫ c) h2)

/-- `pullbackRestrictionIso` along `k`, with the target read along `k ⋙ (K ⋙ 𝟭)`. -/
def pullbackRestrictionIsoComp (k : X ⟶ Y) (K : spaceCat Y ⥤ 𝒳) (hK : K ⋙ p = spaceProj Y)
    (hf' : (spaceProj X).IsFibredOneMorphism p (spaceFunctor k ⋙ (K ⋙ 𝟭 _)))
    (N : SheafOfModules.{u} (Stack.ringStructureSheafCore C S hS p hp C.topology le_rfl)) :
    Space.etaleRestrictedModuleInverseImage C S hS (spaceProj X) (spaceProj Y)
        (isFiberedInGroupoids_spaceProj X) (isFiberedInGroupoids_spaceProj Y)
        (spacePresentation X) (spaceFunctor k) (isFibredOneMorphism_spaceFunctor k)
        (Space.stackEtale C S hS _ (isFiberedInGroupoids_spaceProj Y)
          ((Stack.modulePullback C S hS (spaceProj Y) p (isFiberedInGroupoids_spaceProj Y)
            hp K hK C.topology le_rfl).obj N)) ≅
      Space.etaleRestrictedModuleInverseImage C S hS (spaceProj X) p
        (isFiberedInGroupoids_spaceProj X) hp (spacePresentation X)
        (spaceFunctor k ⋙ (K ⋙ 𝟭 _)) hf' (Space.stackEtale C S hS p hp N) :=
  pullbackRestrictionIso (spaceProj Y) (isFiberedInGroupoids_spaceProj Y) K hK hp (spaceProj X)
    (isFiberedInGroupoids_spaceProj X) (spacePresentation X) (spaceFunctor k)
    (isFibredOneMorphism_spaceFunctor k) hf' N

/-- `pullbackRestrictionIso` along `𝟭`, with the target read along `K ⋙ 𝟭`. -/
def pullbackRestrictionIsoSelf (K : spaceCat Y ⥤ 𝒳) (hK : K ⋙ p = spaceProj Y)
    (hg' : (spaceProj Y).IsFibredOneMorphism p (K ⋙ 𝟭 _))
    (N : SheafOfModules.{u} (Stack.ringStructureSheafCore C S hS p hp C.topology le_rfl)) :
    Space.etaleRestrictedModuleInverseImage C S hS (spaceProj Y) (spaceProj Y)
        (isFiberedInGroupoids_spaceProj Y) (isFiberedInGroupoids_spaceProj Y)
        (spacePresentation Y) (𝟭 _) (isFibredOneMorphism_spaceId Y)
        (Space.stackEtale C S hS _ (isFiberedInGroupoids_spaceProj Y)
          ((Stack.modulePullback C S hS (spaceProj Y) p (isFiberedInGroupoids_spaceProj Y)
            hp K hK C.topology le_rfl).obj N)) ≅
      Space.etaleRestrictedModuleInverseImage C S hS (spaceProj Y) p
        (isFiberedInGroupoids_spaceProj Y) hp (spacePresentation Y)
        (K ⋙ 𝟭 _) hg' (Space.stackEtale C S hS p hp N) :=
  pullbackRestrictionIso (spaceProj Y) (isFiberedInGroupoids_spaceProj Y) K hK hp (spaceProj Y)
    (isFiberedInGroupoids_spaceProj Y) (spacePresentation Y) (𝟭 _)
    (isFibredOneMorphism_spaceId Y) hg' N

/-- `spaceEtaleInverseImageComparison_pullbackFunctor`, with the identifications read along
`K ⋙ 𝟭`. -/
theorem spaceEtaleInverseImageComparison_comp_pullbackRestrictionIsoComp (k : X ⟶ Y)
    (K : spaceCat Y ⥤ 𝒳)
    (hK : K ⋙ p = spaceProj Y)
    (hf' : (spaceProj X).IsFibredOneMorphism p (spaceFunctor k ⋙ (K ⋙ 𝟭 _)))
    (hg' : (spaceProj Y).IsFibredOneMorphism p (K ⋙ 𝟭 _))
    (hφ' : ∀ W : spaceCat X, p.IsHomLift (𝟙 (p.obj ((spaceFunctor k ⋙ (K ⋙ 𝟭 _)).obj W)))
      ((Iso.refl (spaceFunctor k ⋙ (K ⋙ 𝟭 _))).inv.app W))
    (N : SheafOfModules.{u} (Stack.ringStructureSheafCore C S hS p hp C.topology le_rfl)) :
    Space.comparisonAlgebraicSpacesModules C S hS (spaceProj X) (spaceProj Y)
        (spaceProj Y) (isFiberedInGroupoids_spaceProj X) (isFiberedInGroupoids_spaceProj Y)
        (spacePresentation X) (spacePresentation Y) (spaceFunctor k)
        (spaceFunctor k) (𝟭 _) (isFibredOneMorphism_spaceFunctor _)
        (isFibredOneMorphism_spaceId _) (Functor.rightUnitor _) k
        (spaceFunctorChartIso k) (isFiberedInGroupoids_spaceProj Y)
        (isHomLift_spaceRightUnitor_inv_app k)
        (isHomLift_spaceFunctorChartIso_hom_app k)
        (Space.stackEtale C S hS _ (isFiberedInGroupoids_spaceProj Y)
          ((Stack.modulePullback C S hS (spaceProj Y) p (isFiberedInGroupoids_spaceProj Y)
            hp K hK C.topology le_rfl).obj N)) ≫
      (pullbackRestrictionIsoComp hp k K hK hf' N).hom =
    (Space.modulePullback C S hS k).map (pullbackRestrictionIsoSelf hp K hK hg' N).hom ≫
      Space.comparisonAlgebraicSpacesModules C S hS (spaceProj X) (spaceProj Y) p
        (isFiberedInGroupoids_spaceProj X) (isFiberedInGroupoids_spaceProj Y)
        (spacePresentation X) (spacePresentation Y) (spaceFunctor k)
        (spaceFunctor k ⋙ (K ⋙ 𝟭 _)) (K ⋙ 𝟭 _) hf' hg' (Iso.refl _) k (spaceFunctorChartIso k) hp
        hφ' (isHomLift_spaceFunctorChartIso_hom_app k) (Space.stackEtale C S hS p hp N) :=
  spaceEtaleInverseImageComparison_pullbackFunctor hp k K hK hf' hg' hf' hg' hφ' N

end PullbackRightUnitor

section Gluing

variable {A : AlgebraicSpaces C S hS} (G : GroupoidInAlgebraicSpaces C S hS A)

/-- `k ⋙ ι` is a fibred 1-morphism, for the inclusion `ι` of the object space into the
pointwise groupoid fibration. -/
theorem isFibredOneMorphism_spaceFunctor_comp_pointwiseObjectInclusion {X : AlgebraicSpaces C S hS}
    (k : X ⟶ G.objects) :
    (spaceProj X).IsFibredOneMorphism
      (presheafOfGroupoids (evaluationGroupoidFunctor G.toGroupoidInFunctors)).p
      (spaceFunctor k ⋙ pointwiseObjectInclusion G) :=
  (isFiberedInGroupoids_presheafOfGroupoids _).isFibredOneMorphism (by
    rw [Functor.assoc, pointwiseObjectInclusion_comp_p]
    exact spaceFunctor_comp_spaceProj k)

/-- `𝟭 ⋙ ι` is a fibred 1-morphism, for the inclusion `ι` of the object space into the
pointwise groupoid fibration. -/
theorem isFibredOneMorphism_id_comp_pointwiseObjectInclusion :
    (spaceProj G.objects).IsFibredOneMorphism
      (presheafOfGroupoids (evaluationGroupoidFunctor G.toGroupoidInFunctors)).p
      (𝟭 _ ⋙ pointwiseObjectInclusion G) :=
  (isFiberedInGroupoids_presheafOfGroupoids _).isFibredOneMorphism
    (pointwiseObjectInclusion_comp_p G)

/-- The target map `t : R ⟶ U` followed by the object map of the pointwise presentation is a
fibred 1-morphism. -/
theorem isFibredOneMorphism_target_comp_pointwisePresentationObject :
    (spaceProj G.arrows).IsFibredOneMorphism
      (presheafOfGroupoids (evaluationGroupoidFunctor G.toGroupoidInFunctors)).p
      (spaceFunctor G.target ⋙ pointwisePresentationObject (𝟭 (PointwiseFibration G))) :=
  (isFiberedInGroupoids_presheafOfGroupoids _).isFibredOneMorphism (by
    rw [Functor.assoc, pointwisePresentationObject_comp _ (pointwiseFibration_id_comp G)]
    exact spaceFunctor_comp_spaceProj G.target)

/-- The components of the identity of `t ⋙ pointwisePresentationObject 𝟭` lie over identities. -/
theorem isHomLift_target_comp_pointwisePresentationObject_refl (W : spaceCat G.arrows) :
    (presheafOfGroupoids (evaluationGroupoidFunctor G.toGroupoidInFunctors)).p.IsHomLift
      (𝟙 ((presheafOfGroupoids (evaluationGroupoidFunctor G.toGroupoidInFunctors)).p.obj
        ((spaceFunctor G.target ⋙ pointwisePresentationObject (𝟭 (PointwiseFibration G))).obj W)))
      ((Iso.refl (spaceFunctor G.target ⋙ pointwisePresentationObject
        (𝟭 (PointwiseFibration G)))).inv.app W) :=
  Space.isHomLift_iso_refl_inv_app C S hS _ _ W

/-- `k^*(ι^*N)|_{X_étale} ≅ (k ⋙ ι)^*N|_{X_étale}`, with identity components, for the inclusion
`ι` of the object space into the pointwise groupoid fibration. -/
abbrev objectRestrictionPullbackIso {X : AlgebraicSpaces C S hS} (k : X ⟶ G.objects)
    (hf : (spaceProj X).IsFibredOneMorphism
      (presheafOfGroupoids (evaluationGroupoidFunctor G.toGroupoidInFunctors)).p
      (spaceFunctor k ⋙ pointwisePresentationObject (𝟭 (PointwiseFibration G))))
    (N : SheafOfModules.{u} (pointwiseRing G)) :=
  pullbackRestrictionIsoComp (isFiberedInGroupoids_presheafOfGroupoids _) k
    (pointwiseObjectInclusion G) (pointwiseObjectInclusion_comp_p G) hf N

/-- `(ι^*N)|_{U_étale} ≅ ι^*N|_{U_étale}`, with identity components. -/
abbrev objectRestrictionSelfIso (N : SheafOfModules.{u} (pointwiseRing G)) :=
  pullbackRestrictionIsoSelf (isFiberedInGroupoids_presheafOfGroupoids _)
    (pointwiseObjectInclusion G) (pointwiseObjectInclusion_comp_p G)
    (isFibredOneMorphism_pointwisePresentationObject (𝟭 _) (pointwiseFibration_id_comp G)
      (isFiberedInGroupoids_presheafOfGroupoids _)) N

/-- **The comparison map through the source of a module on the pointwise groupoid fibration is
the comparison map along `s` of its restriction to the object space.** -/
theorem pointwisePresentationSourceComparison_objectRestriction
    (N : SheafOfModules.{u} (pointwiseRing G)) :
    spaceEtaleInverseImageComparison G.source
        ((objectRestriction G).obj N : SheafOfModules.{u} (spaceRing G.objects)) ≫
      (objectRestrictionPullbackIso G G.source
        (isFibredOneMorphism_pointwisePresentationSource (𝟭 _) (pointwiseFibration_id_comp G)
          (isFiberedInGroupoids_presheafOfGroupoids _)) N).hom =
    (Space.modulePullback C S hS G.source).map (objectRestrictionSelfIso G N).hom ≫
      pointwisePresentationSourceComparison (𝟭 (PointwiseFibration G))
        (pointwiseFibration_id_comp G)
        (Space.stackEtale C S hS _ (isFiberedInGroupoids_presheafOfGroupoids _) N) :=
  spaceEtaleInverseImageComparison_comp_pullbackRestrictionIsoComp
    (isFiberedInGroupoids_presheafOfGroupoids _)
    G.source (pointwiseObjectInclusion G) (pointwiseObjectInclusion_comp_p G) _ _
    (isHomLift_pointwisePresentationSource_refl (𝟭 _)) N

/-- **The comparison map through the target of a module on the pointwise groupoid fibration,
before restriction along the canonical 2-morphism, is the comparison map along `t` of its
restriction to the object space.** -/
theorem targetComparison_objectRestriction (N : SheafOfModules.{u} (pointwiseRing G)) :
    spaceEtaleInverseImageComparison G.target
        ((objectRestriction G).obj N : SheafOfModules.{u} (spaceRing G.objects)) ≫
      (objectRestrictionPullbackIso G G.target
        (isFibredOneMorphism_target_comp_pointwisePresentationObject G) N).hom =
    (Space.modulePullback C S hS G.target).map (objectRestrictionSelfIso G N).hom ≫
      Space.comparisonAlgebraicSpacesModules C S hS (spaceProj G.arrows) (spaceProj G.objects) _
        (isFiberedInGroupoids_arrows G) (isFiberedInGroupoids_objects G)
        (spacePresentation G.arrows) (spacePresentation G.objects) (spaceFunctor G.target)
        (spaceFunctor G.target ⋙ pointwisePresentationObject (𝟭 (PointwiseFibration G)))
        (pointwisePresentationObject (𝟭 (PointwiseFibration G)))
        (isFibredOneMorphism_target_comp_pointwisePresentationObject G)
        (isFibredOneMorphism_pointwisePresentationObject (𝟭 _) (pointwiseFibration_id_comp G)
          (isFiberedInGroupoids_presheafOfGroupoids _))
        (Iso.refl _) G.target (spaceFunctorChartIso G.target)
        (isFiberedInGroupoids_presheafOfGroupoids _)
        (isHomLift_target_comp_pointwisePresentationObject_refl G) (isHomLift_targetChartIso G)
        (Space.stackEtale C S hS _ (isFiberedInGroupoids_presheafOfGroupoids _) N) :=
  spaceEtaleInverseImageComparison_comp_pullbackRestrictionIsoComp
    (isFiberedInGroupoids_presheafOfGroupoids _)
    G.target (pointwiseObjectInclusion G) (pointwiseObjectInclusion_comp_p G) _ _
    (isHomLift_target_comp_pointwisePresentationObject_refl G) N

/-- The comparison map through the target of the pointwise groupoid fibration is the comparison
map of the strictly commuting triangle through the target, followed by restriction along the
canonical 2-morphism. -/
theorem pointwisePresentationTargetComparison_eq_comp_twoMorphism
    (ℱ : Space.inheritedEtaleModules.{u, u + 1, u, u} C S hS
      (presheafOfGroupoids (evaluationGroupoidFunctor G.toGroupoidInFunctors)).p
      (isFiberedInGroupoids_presheafOfGroupoids _)) :
    pointwisePresentationTargetComparison (𝟭 (PointwiseFibration G)) (pointwiseFibration_id_comp G)
        ℱ =
      Space.comparisonAlgebraicSpacesModules C S hS (spaceProj G.arrows) (spaceProj G.objects) _
        (isFiberedInGroupoids_arrows G) (isFiberedInGroupoids_objects G)
        (spacePresentation G.arrows) (spacePresentation G.objects) (spaceFunctor G.target)
        (spaceFunctor G.target ⋙ pointwisePresentationObject (𝟭 (PointwiseFibration G)))
        (pointwisePresentationObject (𝟭 (PointwiseFibration G)))
        (isFibredOneMorphism_target_comp_pointwisePresentationObject G)
        (isFibredOneMorphism_pointwisePresentationObject (𝟭 _) (pointwiseFibration_id_comp G)
          (isFiberedInGroupoids_presheafOfGroupoids _))
        (Iso.refl _) G.target (spaceFunctorChartIso G.target)
        (isFiberedInGroupoids_presheafOfGroupoids _)
        (isHomLift_target_comp_pointwisePresentationObject_refl G) (isHomLift_targetChartIso G) ℱ ≫
      Space.etaleRestrictedModuleInverseImageTwoMorphism C S hS (spaceProj G.arrows) _
        (isFiberedInGroupoids_arrows G) (isFiberedInGroupoids_presheafOfGroupoids _)
        (spacePresentation G.arrows)
        (spaceFunctor G.target ⋙ pointwisePresentationObject (𝟭 (PointwiseFibration G)))
        (pointwisePresentationSource (𝟭 (PointwiseFibration G)))
        (isFibredOneMorphism_target_comp_pointwisePresentationObject G)
        (isFibredOneMorphism_pointwisePresentationSource (𝟭 _) (pointwiseFibration_id_comp G)
          (isFiberedInGroupoids_presheafOfGroupoids _))
        (pointwisePresentationTwoArrow (𝟭 (PointwiseFibration G)))
        (isHomLift_pointwisePresentationTwoArrow_app (𝟭 _) (pointwiseFibration_id_comp G)) ℱ :=
  Space.comparisonAlgebraicSpacesModules_twoMorphism C S hS (spaceProj G.arrows)
    (spaceProj G.objects) _ (isFiberedInGroupoids_arrows G) (isFiberedInGroupoids_objects G)
    (isFiberedInGroupoids_presheafOfGroupoids _) (spacePresentation G.arrows)
    (spacePresentation G.objects)
    (spaceFunctor G.target ⋙ pointwisePresentationObject (𝟭 (PointwiseFibration G)))
    (pointwisePresentationSource (𝟭 (PointwiseFibration G)))
    (isFibredOneMorphism_target_comp_pointwisePresentationObject G)
    (isFibredOneMorphism_pointwisePresentationSource (𝟭 _) (pointwiseFibration_id_comp G)
      (isFiberedInGroupoids_presheafOfGroupoids _))
    (pointwisePresentationTwoArrow (𝟭 (PointwiseFibration G)))
    (isHomLift_pointwisePresentationTwoArrow_app (𝟭 _) (pointwiseFibration_id_comp G))
    (spaceFunctor G.target) (pointwisePresentationObject (𝟭 (PointwiseFibration G)))
    (isFibredOneMorphism_pointwisePresentationObject (𝟭 _) (pointwiseFibration_id_comp G)
      (isFiberedInGroupoids_presheafOfGroupoids _))
    (Iso.refl _) (pointwisePresentationTwoIso (𝟭 (PointwiseFibration G))) G.target
    (spaceFunctorChartIso G.target) (isHomLift_target_comp_pointwisePresentationObject_refl G)
    (isHomLift_pointwisePresentationTwoIso_inv_app (𝟭 _) (pointwiseFibration_id_comp G))
    (isHomLift_targetChartIso G) (IsIso.inv_hom_id _) ℱ

/-- The descent morphism of a descent datum on sections: restriction of sections of the glued
module along the canonical 2-morphism. -/
theorem PointwiseDescentDatum.β_val_app (D : PointwiseDescentDatum G) (T : BigFppfOver C S hS)
    (r : G.arrows.obj.obj (op T))
    (y : D.M.val.presheaf.obj (op (objPt G T (G.target.hom.app (op T) r)))) :
    D.β.val.app (op ⟨T, ⟨r⟩⟩) y = D.sheaf.val.presheaf.map (vertHom G T r rfl rfl).op y :=
  (ConcreteCategory.congr_hom (descComp_restrictionTransition_sheaf D T r) y).symm

/-- **The descent morphism of a descent datum, restricted to `R_étale`, is restriction of sections
of the glued module along the canonical 2-morphism.** -/
theorem twoMorphism_pointwiseDescentDatum_sheaf (D : PointwiseDescentDatum G) :
    Space.etaleRestrictedModuleInverseImageTwoMorphism C S hS (spaceProj G.arrows) _
        (isFiberedInGroupoids_arrows G) (isFiberedInGroupoids_presheafOfGroupoids _)
        (spacePresentation G.arrows)
        (spaceFunctor G.target ⋙ pointwisePresentationObject (𝟭 (PointwiseFibration G)))
        (pointwisePresentationSource (𝟭 (PointwiseFibration G)))
        (isFibredOneMorphism_target_comp_pointwisePresentationObject G)
        (isFibredOneMorphism_pointwisePresentationSource (𝟭 _) (pointwiseFibration_id_comp G)
          (isFiberedInGroupoids_presheafOfGroupoids _))
        (pointwisePresentationTwoArrow (𝟭 (PointwiseFibration G)))
        (isHomLift_pointwisePresentationTwoArrow_app (𝟭 _) (pointwiseFibration_id_comp G))
        (Space.stackEtale C S hS _ (isFiberedInGroupoids_presheafOfGroupoids _) D.sheaf) ≫
      (objectRestrictionPullbackIso G G.source
        (isFibredOneMorphism_pointwisePresentationSource (𝟭 _) (pointwiseFibration_id_comp G)
          (isFiberedInGroupoids_presheafOfGroupoids _)) D.sheaf).inv ≫
        spaceEtaleInverseImageMap G.source
          (D.sheafRestrictionIso.hom : (objectRestriction G).obj D.sheaf ⟶ D.M) =
    (objectRestrictionPullbackIso G G.target
        (isFibredOneMorphism_target_comp_pointwisePresentationObject G) D.sheaf).inv ≫
      spaceEtaleInverseImageMap G.target
          (D.sheafRestrictionIso.hom : (objectRestriction G).obj D.sheaf ⟶ D.M) ≫
        (spacePullbackSelfIso G.target (D.M : SheafOfModules.{u} (spaceRing G.objects))).inv ≫
          selfChartRestrictionMap (D.β : (spacePullback G.target).obj D.M ⟶
            (spacePullback G.source).obj D.M) ≫
            (spacePullbackSelfIso G.source
              (D.M : SheafOfModules.{u} (spaceRing G.objects))).hom := by
  ext W x
  exact (PointwiseDescentDatum.β_val_app G D _ _ x).symm

end Gluing

end AlgebraicGeometry.Stack

end
