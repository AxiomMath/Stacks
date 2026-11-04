module

public import StacksFrontier.AlgebraicGeometry.Stacks.PointwisePresentationDescentEquivalence.Gluing

/-!
# The descent functor of a pointwise groupoid presentation is an equivalence

The image under the descent functor of the module glued from a quasi-coherent module on the
groupoid is that module, so the descent functor `QCoh(𝒪_{[U/_pR]}) ⥤ QCoh(U, R, s, t, c)` is an
equivalence, and so is the descent functor of every fully faithful 1-morphism `F : [U/_pR] ⥤ 𝒳`
which covers `𝒳`.

## Main definitions

* `AlgebraicGeometry.Stack.pointwiseIdDescentFunctorObjIso`: the image under the descent functor
  of the glued module is the given module on the groupoid.

## Main results

* `AlgebraicGeometry.Stack.isEquivalence_pointwiseQuasicoherentDescentFunctor_id`: the descent
  functor of `[U/_pR]` is an equivalence.
* `AlgebraicGeometry.Stack.isEquivalence_pointwiseQuasicoherentDescentFunctor`: the descent
  functor of a fully faithful 1-morphism `F : [U/_pR] ⥤ 𝒳` covering `𝒳` is an equivalence.
-/

@[expose] public noncomputable section

open CategoryTheory Opposite

universe u v w

namespace AlgebraicGeometry.Stack

variable {C : BigFppfSite.{u}} {S : Scheme.{u}} {hS : C.Contains S}

/-- A diagram chase: under the given commuting squares and one-sided inverses,
`A ≫ sΨ' ≫ sσ ≫ se = (tΨ' ≫ tσ ≫ te) ≫ Qα`. -/
theorem comp_eq_of_comparisons {𝒞 : Type*} [Category 𝒞]
    {tF sF Ps Pt tU sU Cs Ct Cs' Ct' St Ss tM sM tQ sQ : 𝒞}
    (A : tF ⟶ sF) (cs : sF ⟶ Ps) (ct : tF ⟶ Ps) (c't : tF ⟶ Pt) (tw : Pt ⟶ Ps)
    (tΨ : tU ⟶ tF) (tΨ' : tF ⟶ tU) (sΨ : sU ⟶ sF) (sΨ' : sF ⟶ sU)
    (ccs : sU ⟶ Cs) (cct : tU ⟶ Ct) (Ψs : Cs ⟶ Ps) (Ψs' : Ps ⟶ Cs) (Ψt : Ct ⟶ Pt)
    (Ψt' : Pt ⟶ Ct) (σs : Cs ⟶ Cs') (σt : Ct ⟶ Ct') (tσ : tU ⟶ tM) (sσ : sU ⟶ sM)
    (ccs' : sM ⟶ Cs') (cct' : tM ⟶ Ct') (Jt : Ct' ⟶ St) (Bβ : St ⟶ Ss) (Js : Ss ⟶ Cs')
    (α' : tM ⟶ sM) (te : tM ⟶ tQ) (se : sM ⟶ sQ) (Qα : tQ ⟶ sQ)
    (hA : A ≫ cs = ct) (hT : ct = c't ≫ tw)
    (hKS : ccs ≫ Ψs = sΨ ≫ cs) (hKT : cct ≫ Ψt = tΨ ≫ c't)
    (hsΨ : sΨ' ≫ sΨ = 𝟙 _) (htΨ : tΨ' ≫ tΨ = 𝟙 _) (hΨs : Ψs ≫ Ψs' = 𝟙 _) (hΨt : Ψt ≫ Ψt' = 𝟙 _)
    (hKB : tw ≫ Ψs' ≫ σs = Ψt' ≫ σt ≫ Jt ≫ Bβ ≫ Js)
    (hns : ccs ≫ σs = sσ ≫ ccs') (hnt : cct ≫ σt = tσ ≫ cct')
    (hβ : cct' ≫ Jt ≫ Bβ ≫ Js = α' ≫ ccs') (hα : α' ≫ se = te ≫ Qα) (hiso : IsIso ccs') :
    A ≫ sΨ' ≫ sσ ≫ se = (tΨ' ≫ tσ ≫ te) ≫ Qα := by
  have hs : sΨ' ≫ ccs = cs ≫ Ψs' := by
    rw [← Category.comp_id (sΨ' ≫ ccs), ← hΨs, Category.assoc, ← Category.assoc ccs, hKS,
      ← Category.assoc, ← Category.assoc, hsΨ, Category.id_comp]
  have ht : tΨ' ≫ cct = c't ≫ Ψt' := by
    rw [← Category.comp_id (tΨ' ≫ cct), ← hΨt, Category.assoc, ← Category.assoc cct, hKT,
      ← Category.assoc, ← Category.assoc, htΨ, Category.id_comp]
  have key : A ≫ sΨ' ≫ sσ = tΨ' ≫ tσ ≫ α' := by
    rw [← cancel_mono ccs']
    simp only [Category.assoc]
    rw [← hns, reassoc_of% hs, reassoc_of% hA, hT, Category.assoc, hKB, ← hβ, ← reassoc_of% hnt,
      reassoc_of% ht]
  rw [Category.assoc, Category.assoc, ← hα, ← reassoc_of% key]



section GluingIso

/-- `ψ ↦ ψ|_{Y_étale}` preserves identities. -/
theorem selfChartRestrictionMap_id {Y : AlgebraicSpaces C S hS}
    (M : SheafOfModules.{u} (spaceRing Y)) :
    selfChartRestrictionMap (M := M) (M' := M) (𝟙 M) = 𝟙 _ := by
  simp only [selfChartRestrictionMap, Space.etaleRestrictedModuleInverseImageMap,
    CategoryTheory.Functor.map_id]
  exact CategoryTheory.Functor.map_id _ _

/-- `ψ ↦ ψ|_{Y_étale}` on isomorphisms. -/
def selfChartRestrictionIso {Y : AlgebraicSpaces C S hS} {M M' : SheafOfModules.{u} (spaceRing Y)}
    (e : M ≅ M') : selfChartRestriction M ≅ selfChartRestriction M' where
  hom := selfChartRestrictionMap e.hom
  inv := selfChartRestrictionMap e.inv
  hom_inv_id := by rw [← selfChartRestrictionMap_comp, e.hom_inv_id, selfChartRestrictionMap_id]
  inv_hom_id := by rw [← selfChartRestrictionMap_comp, e.inv_hom_id, selfChartRestrictionMap_id]

variable {A : AlgebraicSpaces C S hS} (G : GroupoidInAlgebraicSpaces C S hS A)
  (Q : Space.QuasicoherentModule C S hS G)

/-- The descent functor of the pointwise groupoid fibration. -/
abbrev pointwiseIdDescentFunctor :=
  pointwiseQuasicoherentDescentFunctor (𝟭 (PointwiseFibration G)) (pointwiseFibration_id_comp G)
    (isFiberedInGroupoids_presheafOfGroupoids _)

/-- The restriction to the object space of the glued module of `Q` is `chartPreimage G Q`. -/
abbrev gluedSheafRestrictionIso : @Iso (SheafOfModules.{u} (spaceRing G.objects)) _
    ((objectRestriction G).obj (pointwiseDatumOfQuasicoherent G Q).sheaf)
    (chartPreimage G Q).obj :=
  (pointwiseDatumOfQuasicoherent G Q).sheafRestrictionIso

/-- The identification of the underlying module of the descent datum of the glued module with
`Q.F`. -/
def gluedRestrictionIso :
    ((pointwiseIdDescentFunctor G).obj (pointwiseSheafOfQuasicoherent G Q)).F.obj ≅ Q.F.obj :=
  (objectRestrictionSelfIso G (pointwiseDatumOfQuasicoherent G Q).sheaf).symm ≪≫
    selfChartRestrictionIso (gluedSheafRestrictionIso G Q) ≪≫ chartPreimageIso G Q

/-- The restriction of the glued module of `Q` along the 2-arrow of the pointwise presentation
is, through the identifications with `chartPreimage G Q`, the descent morphism of
`chartTransition G Q`. -/
theorem twoMorphism_gluedSheaf :
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
        (Space.stackEtale C S hS _ (isFiberedInGroupoids_presheafOfGroupoids _)
          (pointwiseDatumOfQuasicoherent G Q).sheaf) ≫
      (objectRestrictionPullbackIso G G.source
        (isFibredOneMorphism_pointwisePresentationSource (𝟭 _) (pointwiseFibration_id_comp G)
          (isFiberedInGroupoids_presheafOfGroupoids _))
        (pointwiseDatumOfQuasicoherent G Q).sheaf).inv ≫
        spaceEtaleInverseImageMap G.source
          ((pointwiseDatumOfQuasicoherent G Q).sheafRestrictionIso.hom :
            (objectRestriction G).obj (pointwiseDatumOfQuasicoherent G Q).sheaf ⟶
              (chartPreimage G Q).obj) =
    (objectRestrictionPullbackIso G G.target
        (isFibredOneMorphism_target_comp_pointwisePresentationObject G)
          (pointwiseDatumOfQuasicoherent G Q).sheaf).inv ≫
      spaceEtaleInverseImageMap G.target
          ((pointwiseDatumOfQuasicoherent G Q).sheafRestrictionIso.hom :
            (objectRestriction G).obj (pointwiseDatumOfQuasicoherent G Q).sheaf ⟶
              (chartPreimage G Q).obj) ≫
        (spacePullbackSelfIso G.target (chartPreimage G Q).obj).inv ≫
          selfChartRestrictionMap (descentMorphismOfTransition G.target G.source (chartPreimage G Q)
            (chartTransition G Q)) ≫
            (spacePullbackSelfIso G.source (chartPreimage G Q).obj).hom :=
  twoMorphism_pointwiseDescentDatum_sheaf G (pointwiseDatumOfQuasicoherent G Q)

/-- `chartPreimageIso G Q` intertwines `chartTransition G Q` with the transition of `Q`. -/
theorem chartTransition_comm :
    chartTransition G Q ≫ (Space.modulePullback C S hS G.source).map (chartPreimageIso G Q).hom =
      (Space.modulePullback C S hS G.target).map (chartPreimageIso G Q).hom ≫ Q.alpha :=
  transportedTransition_comm Q (chartPreimageIso G Q)

/-- **The identification of `gluedRestrictionIso` is compatible with the transitions.** -/
theorem gluedRestrictionIso_comm :
    ((pointwiseIdDescentFunctor G).obj (pointwiseSheafOfQuasicoherent G Q)).alpha ≫
        (Space.modulePullback C S hS G.source).map (gluedRestrictionIso G Q).hom =
      (Space.modulePullback C S hS G.target).map (gluedRestrictionIso G Q).hom ≫ Q.alpha := by
  have : IsIso (pointwisePresentationSourceComparison (𝟭 (PointwiseFibration G))
      (pointwiseFibration_id_comp G)
      (Space.stackEtale C S hS _ (isFiberedInGroupoids_presheafOfGroupoids _)
        (pointwiseDatumOfQuasicoherent G Q).sheaf)) :=
    (isPointwiseDescentAdmissible_of_quasicoherent (𝟭 (PointwiseFibration G))
      (pointwiseFibration_id_comp G) (pointwiseSheafOfQuasicoherent G Q)).2.1
  have hA := pointwisePresentationTransition_comp (𝟭 (PointwiseFibration G))
    (pointwiseFibration_id_comp G)
    (Space.stackEtale C S hS _ (isFiberedInGroupoids_presheafOfGroupoids _)
      (pointwiseDatumOfQuasicoherent G Q).sheaf)
  have hs : (Space.modulePullback C S hS G.source).map (gluedRestrictionIso G Q).hom =
      (Space.modulePullback C S hS G.source).map
          (objectRestrictionSelfIso G (pointwiseDatumOfQuasicoherent G Q).sheaf).inv ≫
        (Space.modulePullback C S hS G.source).map
          (selfChartRestrictionMap (gluedSheafRestrictionIso G Q).hom) ≫
          (Space.modulePullback C S hS G.source).map (chartPreimageIso G Q).hom :=
    ((Space.modulePullback C S hS G.source).map_comp _ _).trans
      (congrArg _ ((Space.modulePullback C S hS G.source).map_comp _ _))
  have ht : (Space.modulePullback C S hS G.target).map (gluedRestrictionIso G Q).hom =
      (Space.modulePullback C S hS G.target).map
          (objectRestrictionSelfIso G (pointwiseDatumOfQuasicoherent G Q).sheaf).inv ≫
        (Space.modulePullback C S hS G.target).map
          (selfChartRestrictionMap (gluedSheafRestrictionIso G Q).hom) ≫
          (Space.modulePullback C S hS G.target).map (chartPreimageIso G Q).hom :=
    ((Space.modulePullback C S hS G.target).map_comp _ _).trans
      (congrArg _ ((Space.modulePullback C S hS G.target).map_comp _ _))
  rw [hs, ht]
  exact comp_eq_of_comparisons _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ hA
    (pointwisePresentationTargetComparison_eq_comp_twoMorphism G _)
    (pointwisePresentationSourceComparison_objectRestriction G _)
    (targetComparison_objectRestriction G _)
    ((Space.modulePullback C S hS G.source).mapIso
      (objectRestrictionSelfIso G (pointwiseDatumOfQuasicoherent G Q).sheaf)).inv_hom_id
    ((Space.modulePullback C S hS G.target).mapIso
      (objectRestrictionSelfIso G (pointwiseDatumOfQuasicoherent G Q).sheaf)).inv_hom_id
    (Iso.hom_inv_id _) (Iso.hom_inv_id _)
    (twoMorphism_gluedSheaf G Q)
    (spaceEtaleInverseImageComparison_naturality G.source (gluedSheafRestrictionIso G Q).hom)
    (spaceEtaleInverseImageComparison_naturality G.target (gluedSheafRestrictionIso G Q).hom)
    (descentMorphismOfTransition_spec G.target G.source (chartPreimage G Q) (chartTransition G Q))
    (chartTransition_comm G Q)
    (inferInstance : IsIso (spaceEtaleInverseImageComparison G.source (chartPreimage G Q).obj))

/-- **Every quasi-coherent module on the groupoid is the descent datum of a quasi-coherent module
on the pointwise groupoid fibration.** -/
def pointwiseIdDescentFunctorObjIso :
    (pointwiseIdDescentFunctor G).obj (pointwiseSheafOfQuasicoherent G Q) ≅ Q :=
  quasicoherentModuleIsoMk ⟨(gluedRestrictionIso G Q).hom, gluedRestrictionIso_comm G Q⟩
    (Iso.isIso_hom _)

end GluingIso

section Equivalence

variable {A : AlgebraicSpaces C S hS} (G : GroupoidInAlgebraicSpaces C S hS A)

/-- The descent functor of the pointwise groupoid fibration is essentially surjective. -/
instance : (pointwiseIdDescentFunctor G).EssSurj where
  mem_essImage Q := ⟨pointwiseSheafOfQuasicoherent G Q, ⟨pointwiseIdDescentFunctorObjIso G Q⟩⟩

/-- The identity of the pointwise groupoid fibration covers its target. -/
theorem pointwiseFibration_id_covers (y : PointwiseFibration G) :
    ∃ (I : Type u) (x : I → PointwiseFibration G)
      (g : ∀ i, (𝟭 (PointwiseFibration G)).obj (x i) ⟶ y),
      Sieve.ofArrows _ g ∈ BigFppfOver.associatedTopology C S hS
        (presheafOfGroupoids (evaluationGroupoidFunctor G.toGroupoidInFunctors)).p .fppf y := by
  refine ⟨PUnit, fun _ => y, fun _ => 𝟙 y, ?_⟩
  have h : Sieve.ofArrows (fun _ : PUnit => y) (fun _ => 𝟙 y) = ⊤ :=
    (Sieve.id_mem_iff_eq_top).1 (Sieve.ofArrows_mk _ _ PUnit.unit)
  exact h ▸ GrothendieckTopology.top_mem _ _

/-- **The descent functor of the pointwise groupoid fibration is an equivalence**:
`QCoh(𝒪_P) ≌ QCoh(U, R, s, t, c)`, `N ↦ (ι^*N|_{U_étale}, c_t ≫ c_s⁻¹)`. -/
theorem isEquivalence_pointwiseQuasicoherentDescentFunctor_id :
    (pointwiseQuasicoherentDescentFunctor (𝟭 (PointwiseFibration G)) (pointwiseFibration_id_comp G)
      (isFiberedInGroupoids_presheafOfGroupoids _)).IsEquivalence :=
  have := faithful_pointwiseQuasicoherentDescentFunctor (𝟭 (PointwiseFibration G))
    (pointwiseFibration_id_comp G) (isFiberedInGroupoids_presheafOfGroupoids _)
    (pointwiseFibration_id_covers G)
  have := full_pointwiseQuasicoherentDescentFunctor (𝟭 (PointwiseFibration G))
    (pointwiseFibration_id_comp G) (isFiberedInGroupoids_presheafOfGroupoids _)
    (pointwiseFibration_id_covers G)
  { }

variable {G} {𝒳 : Type v} [Category.{w} 𝒳] {p : 𝒳 ⥤ BigFppfOver C S hS}
  (F : PointwiseFibration G ⥤ 𝒳)
  (hF : F ⋙ p = (presheafOfGroupoids (evaluationGroupoidFunctor G.toGroupoidInFunctors)).p)
  (hp : p.IsFiberedInGroupoids)

include hF in
/-- **The descent functor of a fully faithful pointwise presentation covering its target is
essentially surjective.** -/
theorem essSurj_pointwiseQuasicoherentDescentFunctor [F.Full] [F.Faithful]
    (hloc : ∀ y : 𝒳, ∃ (I : Type u) (x : I → PointwiseFibration G) (g : ∀ i, F.obj (x i) ⟶ y),
      Sieve.ofArrows _ g ∈ BigFppfOver.associatedTopology C S hS p .fppf y) :
    (pointwiseQuasicoherentDescentFunctor F hF hp).EssSurj where
  mem_essImage Q := by
    have hE := isEquivalence_quasicoherentPullback'_of_full_of_faithful.{u, u + 1, u, u, v, w}
      C S hS _ p (isFiberedInGroupoids_presheafOfGroupoids _) hp F hF hloc
    obtain ⟨N, ⟨eN⟩⟩ := Functor.EssSurj.mem_essImage
      (F := pointwiseQuasicoherentDescentFunctor (𝟭 (PointwiseFibration G))
        (pointwiseFibration_id_comp G) (isFiberedInGroupoids_presheafOfGroupoids _)) Q
    obtain ⟨ℱ, ⟨eℱ⟩⟩ := Functor.EssSurj.mem_essImage
      (F := quasicoherentPullback'.{u, u + 1, u, u, v, w} C S hS _ p
        (isFiberedInGroupoids_presheafOfGroupoids _) hp F hF) N
    exact ⟨ℱ, ⟨(pointwiseQuasicoherentDescentFunctorPullbackIso F hF hp ℱ).symm ≪≫
      (pointwiseQuasicoherentDescentFunctor (𝟭 (PointwiseFibration G))
        (pointwiseFibration_id_comp G) (isFiberedInGroupoids_presheafOfGroupoids _)).mapIso
          eℱ ≪≫ eN⟩⟩

include hF in
/-- **The descent functor of a fully faithful pointwise presentation covering its target is an
equivalence**: `QCoh(𝒪_𝒳) ≌ QCoh(U, R, s, t, c)`, `ℱ ↦ (x^*ℱ|_{U_étale}, c_t ≫ c_s⁻¹)`. -/
theorem isEquivalence_pointwiseQuasicoherentDescentFunctor [F.Full] [F.Faithful]
    (hloc : ∀ y : 𝒳, ∃ (I : Type u) (x : I → PointwiseFibration G) (g : ∀ i, F.obj (x i) ⟶ y),
      Sieve.ofArrows _ g ∈ BigFppfOver.associatedTopology C S hS p .fppf y) :
    (pointwiseQuasicoherentDescentFunctor F hF hp).IsEquivalence :=
  have := faithful_pointwiseQuasicoherentDescentFunctor F hF hp hloc
  have := full_pointwiseQuasicoherentDescentFunctor F hF hp hloc
  have := essSurj_pointwiseQuasicoherentDescentFunctor F hF hp hloc
  { }

end Equivalence


end AlgebraicGeometry.Stack

end
