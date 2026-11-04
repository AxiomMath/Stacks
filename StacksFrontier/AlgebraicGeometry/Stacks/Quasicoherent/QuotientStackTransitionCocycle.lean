module

public import StacksFrontier.AlgebraicGeometry.Spaces.Groupoids.EquivariantQuasicoherentPullback
public import StacksFrontier.AlgebraicGeometry.Spaces.Groupoids.QuotientStackSquares.TwoArrowCocycle
public import StacksFrontier.AlgebraicGeometry.Stacks.Quasicoherent.QuotientStackTransitionTwisted
public import StacksFrontier.AlgebraicGeometry.Stacks.Quasicoherent.QuotientStackTransitionUnit

/-!
# The cocycle condition for the transition morphism of Stacks 06WT

Let `G = (U, R, s, t, c)` be a groupoid in algebraic spaces, `ℱ` a quasi-coherent module on the
quotient stack `[U/R]`, and `α : t^*𝒢 ⟶ s^*𝒢` the transition morphism of `𝒢 = x^*ℱ|_{U_étale}`
(`AlgebraicGeometry.Stack.quotientStackTransition`). This file proves the cocycle condition of
Stacks 0441 for `(𝒢, α)` over the space `R ×_{s, U, t} R` of composable pairs of arrows, a
consequence of the cocycle identity of Stacks 044T for the 2-morphism of Stacks 044S.

## Main results

* `AlgebraicGeometry.Stack.groupoidPullbackTransition_quotientStackTransition_comp`: the cocycle
  condition.

## References

* [Stacks Project, Tag 06WT](https://stacks.math.columbia.edu/tag/06WT)
* [Stacks Project, Tag 0441](https://stacks.math.columbia.edu/tag/0441)
* [Stacks Project, Tag 044T](https://stacks.math.columbia.edu/tag/044T)
-/

@[expose] public section

open CategoryTheory Opposite AlgebraicGeometry.GroupoidInAlgebraicSpaces

universe u

namespace AlgebraicGeometry.Stack

variable {C : BigFppfSite.{u}} {S : Scheme.{u}} {hS : C.Contains S}

/-- Two composites of 1-morphisms attached to maps of presheaves (Stacks 0458) agree when the
composites of the maps agree. -/
theorem associatedMap_toFunctor_comp_eq {F₁ F₂ F₂' F₃ : (BigFppfOver C S hS)ᵒᵖ ⥤ Type u}
    (x : F₁ ⟶ F₂) (y : F₂ ⟶ F₃) (x' : F₁ ⟶ F₂') (y' : F₂' ⟶ F₃) (h : x ≫ y = x' ≫ y') :
    (associatedMap C S hS x).1.hom.toFunctor ⋙ (associatedMap C S hS y).1.hom.toFunctor =
      (associatedMap C S hS x').1.hom.toFunctor ⋙ (associatedMap C S hS y').1.hom.toFunctor := by
  have e1 := congrArg (fun k => k.hom.toFunctor) (associatedMap_comp C S hS x y)
  have e2 := congrArg (fun k => k.hom.toFunctor) (associatedMap_comp C S hS x' y')
  exact e1.symm.trans ((congrArg (fun k => (associatedMap C S hS k).1.hom.toFunctor) h).trans e2)

/-- A transport followed by a morphism of the category fibred in sets attached to a presheaf is
determined by its base. -/
theorem fibredCategory_eqToHom_comp_eq {F : (BigFppfOver C S hS)ᵒᵖ ⥤ Type u}
    {X X' Y : (fibredCategory C S hS F).val.obj} (h : X = X') (m : X' ⟶ Y) (m' : X ⟶ Y)
    (hb : eqToHom (congrArg Pseudofunctor.CoGrothendieck.base h) ≫ m.base = m'.base) :
    eqToHom h ≫ m = m' :=
  fibredCategory_hom_ext _ _ ((congrArg (· ≫ m.base) (fibredCategory_eqToHom_base h)).trans hb)

/-- A 2-morphism of based functors through a transport, componentwise. -/
theorem _root_.CategoryTheory.BasedNatTrans.eqToHom_toNatTrans_app {𝒮 : Type*} [Category 𝒮]
    {𝒳 𝒴 : BasedCategory 𝒮} {F₁ F₂ : 𝒳 ⥤ᵇ 𝒴} (h : F₁ = F₂) (X : 𝒳.obj) :
    (eqToHom h).toNatTrans.app X = eqToHom (congrArg (fun K : 𝒳 ⥤ᵇ 𝒴 => K.toFunctor.obj X) h) := by
  cases h
  rfl

/-- A composite of 2-morphisms of based functors, componentwise. -/
theorem _root_.CategoryTheory.BasedNatTrans.comp_toNatTrans_app {𝒮 : Type*} [Category 𝒮]
    {𝒳 𝒴 : BasedCategory 𝒮} {F₁ F₂ F₃ : 𝒳 ⥤ᵇ 𝒴} (η : F₁ ⟶ F₂) (θ : F₂ ⟶ F₃) (X : 𝒳.obj) :
    (η ≫ θ).toNatTrans.app X = η.toNatTrans.app X ≫ θ.toNatTrans.app X :=
  rfl

/-- A transport between images under a functor, followed by the image of a morphism, is the image
of a transport followed by that morphism. -/
theorem _root_.CategoryTheory.Functor.eqToHom_comp_map_eq {𝒜 ℬ : Type*} [Category 𝒜] [Category ℬ]
    (Φ : 𝒜 ⥤ ℬ) {a a' b : 𝒜} (e : Φ.obj a = Φ.obj a') (h : a = a') (m : a' ⟶ b) :
    eqToHom e ≫ Φ.map m = Φ.map (eqToHom h ≫ m) := by
  subst h
  simp

/-- In any category, if `X = T₁ ≫ (g₁ ≫ T₀ ≫ g₂) ≫ T₂`, `T₂ ≫ D = S₂`, `g₂ ≫ S₂ = T₂'`,
`T₀ ≫ T₂' = S₁` and `g₁ ≫ S₁ = T₁'`, then `X ≫ D = T₁ ≫ T₁'`. -/
theorem _root_.CategoryTheory.comp_eq_of_five_factors {𝒞 : Type*} [Category 𝒞]
    {X₁ X₂ X₃ X₄ X₅ X₆ H : 𝒞} {X : X₁ ⟶ X₆} {T₁ : X₁ ⟶ X₂} {g₁ : X₂ ⟶ X₃} {T₀ : X₃ ⟶ X₄}
    {g₂ : X₄ ⟶ X₅} {T₂ : X₅ ⟶ X₆} {D : X₆ ⟶ H} {S₂ : X₅ ⟶ H} {T₂' : X₄ ⟶ H} {S₁ : X₃ ⟶ H}
    {T₁' : X₂ ⟶ H} (hX : X = T₁ ≫ (g₁ ≫ T₀ ≫ g₂) ≫ T₂) (hA : T₂ ≫ D = S₂)
    (h₂ : g₂ ≫ S₂ = T₂') (hB : T₀ ≫ T₂' = S₁) (h₁ : g₁ ≫ S₁ = T₁') :
    X ≫ D = T₁ ≫ T₁' := by
  subst hX
  simp only [Category.assoc]
  rw [hA, h₂, hB, h₁]

/-- Two composites of the shape of Stacks 044T agree when their last factors do, after the last
transport. -/
theorem _root_.CategoryTheory.eqToHom_comp_comp_comp_comp_eq {𝒞 : Type*} [Category 𝒞]
    {A A' Y Y' D D' E : 𝒞} (σ₂ : A' ⟶ Y) (σ₁ : Y' ⟶ D) (m : D' ⟶ E) (m' : D ⟶ E)
    (e₁ e₁' : A = A') (e₂ e₂' : Y = Y') (e₃ : D = D') (hm : eqToHom e₃ ≫ m = m') :
    (eqToHom e₁ ≫ σ₂ ≫ eqToHom e₂ ≫ σ₁ ≫ eqToHom e₃) ≫ m =
      eqToHom e₁' ≫ σ₂ ≫ eqToHom e₂' ≫ σ₁ ≫ m' := by
  subst hm
  simp only [Category.assoc]

variable {B : AlgebraicSpaces C S hS} (G : GroupoidInAlgebraicSpaces C S hS B)

/-- The source of the second arrow of a composable pair is the source of the composite, as
1-morphisms `𝒮_{R ×_U R} ⟶ 𝒮_U`. -/
theorem cocycleLegEq₂ : reindexLeg G (secondArrow G) ⋙ quotientStackSourceLeg G =
    reindexLeg G G.comp ⋙ quotientStackSourceLeg G :=
  associatedMap_toFunctor_comp_eq _ _ _ _ (congrArg (fun k => k.hom) (comp_comp_source G)).symm

/-- The source of the first arrow of a composable pair is the target of the second. -/
theorem cocycleLegEq₁ : reindexLeg G (firstArrow G) ⋙ quotientStackSourceLeg G =
    reindexLeg G (secondArrow G) ⋙ quotientStackTargetLeg G :=
  associatedMap_toFunctor_comp_eq _ _ _ _ (congrArg (fun k => k.hom) (firstArrow_comp_source G))

/-- The target of the composite of a composable pair is the target of its first arrow. -/
theorem cocycleLegEq₀ : reindexLeg G G.comp ⋙ quotientStackTargetLeg G =
    reindexLeg G (firstArrow G) ⋙ quotientStackTargetLeg G :=
  associatedMap_toFunctor_comp_eq _ _ _ _ (congrArg (fun k => k.hom) (comp_comp_target G))

/-- The common target `x ∘ s ∘ c : 𝒮_{R ×_U R} ⟶ [U/R]` of the comparison maps. -/
noncomputable abbrev cocycleTarget :
    (fibredCategory C S hS (AlgebraicSpaces.fiberProduct C S hS G.source G.target).obj).val.obj ⥤
      (quotientStack G).obj :=
  reindexLeg G G.comp ⋙ (quotientStackSourceLeg G ⋙ quotientStackProj G)

/-- The 2-isomorphism `x ∘ s ∘ p₂ ≅ x ∘ s ∘ c` given by the equality of the two legs. -/
noncomputable abbrev cocycleSecondIso :
    reindexLeg G (secondArrow G) ⋙ (quotientStackSourceLeg G ⋙ quotientStackProj G) ≅
      cocycleTarget G :=
  Functor.isoWhiskerRight (eqToIso (cocycleLegEq₂ G)) (quotientStackProj G)

/-- The image under the projection to `[U/R]` of the components of the inverse of an `eqToIso` of
functors lies over identities. -/
private theorem isHomLift_quotientStackProj_map_eqToIso_inv {𝒥 : Type*} [Category 𝒥]
    {K₁ K₂ : 𝒥 ⥤ (fibredCategory C S hS G.objects.obj).val.obj} (e : K₁ = K₂) (X : 𝒥) :
    (quotientStack G).p.IsHomLift (𝟙 ((quotientStack G).p.obj ((K₂ ⋙ quotientStackProj G).obj X)))
      ((quotientStackProj G).map ((eqToIso e).inv.app X)) := by
  rw [eqToIso.inv, eqToHom_app, eqToHom_map]
  exact IsHomLift.eqToHom_domain_lift_id _ rfl

/-- The components of `cocycleSecondIso` lie over identities. -/
theorem isHomLift_cocycleSecondIso
    (X : (fibredCategory C S hS
      (AlgebraicSpaces.fiberProduct C S hS G.source G.target).obj).val.obj) :
    (quotientStack G).p.IsHomLift (𝟙 ((quotientStack G).p.obj ((cocycleTarget G).obj X)))
      ((cocycleSecondIso G).inv.app X) := by
  exact isHomLift_quotientStackProj_map_eqToIso_inv G (cocycleLegEq₂ G) X

/-- The 2-isomorphism `x ∘ s ∘ p₁ ≅ x ∘ s ∘ c`: the equality of the source of `p₁` with the
target of `p₂`, the inverse of the 2-morphism of Stacks 044S whiskered by `p₂`, and
`cocycleSecondIso`. -/
noncomputable abbrev cocycleFirstIso :
    reindexLeg G (firstArrow G) ⋙ (quotientStackSourceLeg G ⋙ quotientStackProj G) ≅
      cocycleTarget G :=
  Functor.isoWhiskerRight (eqToIso (cocycleLegEq₁ G)) (quotientStackProj G) ≪≫
    twistedTargetIso G (secondArrow G) (cocycleTarget G) (cocycleSecondIso G)

/-- The components of `cocycleFirstIso` lie over identities. -/
theorem isHomLift_cocycleFirstIso
    (X : (fibredCategory C S hS
      (AlgebraicSpaces.fiberProduct C S hS G.source G.target).obj).val.obj) :
    (quotientStack G).p.IsHomLift (𝟙 ((quotientStack G).p.obj ((cocycleTarget G).obj X)))
      ((cocycleFirstIso G).inv.app X) := by
  have := isHomLift_twistedTargetIso G (secondArrow G) (cocycleTarget G) (cocycleSecondIso G)
    (isHomLift_cocycleSecondIso G) X
  have := isHomLift_quotientStackProj_map_eqToIso_inv G (cocycleLegEq₁ G) X
  exact IsHomLift.comp_lift_id_right' (p := (quotientStack G).p) _
    ((twistedTargetIso G (secondArrow G) (cocycleTarget G) (cocycleSecondIso G)).inv.app X)
    ((quotientStack G).p.obj (((reindexLeg G (secondArrow G) ⋙ quotientStackTargetLeg G) ⋙
        quotientStackProj G).obj X))
    ((quotientStackProj G).map ((eqToIso (cocycleLegEq₁ G)).inv.app X))

variable (F : QuotientStackModules G) (hF : F.IsQuasicoherentOnSite)

/-- The comparison map `(c ≫ s)^*𝒢 ⟶ (x ∘ s ∘ c)^*ℱ`. -/
noncomputable abbrev cocycleCompSource :=
  twistedSourceComparison G G.comp (cocycleTarget G)
    (isFibredOneMorphism_reindexSourceProj G G.comp) (Iso.refl _) (fun _ => IsHomLift.id rfl) F

/-- The comparison map `(c ≫ t)^*𝒢 ⟶ (x ∘ s ∘ c)^*ℱ`. -/
noncomputable abbrev cocycleCompTarget :=
  twistedTargetComparison G G.comp (cocycleTarget G)
    (isFibredOneMorphism_reindexSourceProj G G.comp) (Iso.refl _) (fun _ => IsHomLift.id rfl) F

/-- The comparison map `(p₂ ≫ s)^*𝒢 ⟶ (x ∘ s ∘ c)^*ℱ`. -/
noncomputable abbrev cocycleSecondSource :=
  twistedSourceComparison G (secondArrow G) (cocycleTarget G)
    (isFibredOneMorphism_reindexSourceProj G G.comp) (cocycleSecondIso G)
    (isHomLift_cocycleSecondIso G) F

/-- The comparison map `(p₂ ≫ t)^*𝒢 ⟶ (x ∘ s ∘ c)^*ℱ`. -/
noncomputable abbrev cocycleSecondTarget :=
  twistedTargetComparison G (secondArrow G) (cocycleTarget G)
    (isFibredOneMorphism_reindexSourceProj G G.comp) (cocycleSecondIso G)
    (isHomLift_cocycleSecondIso G) F

/-- The comparison map `(p₁ ≫ s)^*𝒢 ⟶ (x ∘ s ∘ c)^*ℱ`. -/
noncomputable abbrev cocycleFirstSource :=
  twistedSourceComparison G (firstArrow G) (cocycleTarget G)
    (isFibredOneMorphism_reindexSourceProj G G.comp) (cocycleFirstIso G)
    (isHomLift_cocycleFirstIso G) F

/-- The comparison map `(p₁ ≫ t)^*𝒢 ⟶ (x ∘ s ∘ c)^*ℱ`. -/
noncomputable abbrev cocycleFirstTarget :=
  twistedTargetComparison G (firstArrow G) (cocycleTarget G)
    (isFibredOneMorphism_reindexSourceProj G G.comp) (cocycleFirstIso G)
    (isHomLift_cocycleFirstIso G) F

/-- The transport along `p₂ ≫ s = c ≫ s` followed by the comparison through `s ∘ c` is the
comparison through `s ∘ p₂`. -/
theorem pullbackTransport_comp_cocycleCompSource :
    Space.pullbackTransport _ (comp_comp_source G).symm ≫ cocycleCompSource G F =
      cocycleSecondSource G F :=
  Space.pullbackTransport_comp_comparisonAlgebraicSpacesModules C S hS _ _ _ _ _ _ _ _ _ _ _ _ _
    _ _ _ _ _ _ _ _ _ _ _ (comp_comp_source G).symm (fun d => by
      simp only [Space.comparisonMorphism, Space.comparisonChartHom, reindexSourceChartIso,
        Iso.refl_hom, Iso.refl_inv, NatTrans.id_app, Category.id_comp,
        Functor.isoWhiskerRight_inv, Functor.whiskerRight_app, eqToIso.inv, eqToHom_app]
      rw [← Functor.map_comp]
      refine congrArg (quotientStackProj G).map (fibredCategory_eqToHom_comp_eq _ _ _ ?_)
      exact (congrArg (· ≫ _) (eqToHom_refl _ _)).trans ((Category.id_comp _).trans rfl)) _

/-- The transport along `p₁ ≫ s = p₂ ≫ t` followed by the comparison through `t ∘ p₂` is the
comparison through `s ∘ p₁`. -/
theorem pullbackTransport_comp_cocycleSecondTarget :
    Space.pullbackTransport _ (firstArrow_comp_source G) ≫ cocycleSecondTarget G F =
      cocycleFirstSource G F :=
  Space.pullbackTransport_comp_comparisonAlgebraicSpacesModules C S hS _ _ _ _ _ _ _ _ _ _ _ _ _
    _ _ _ _ _ _ _ _ _ _ _ (firstArrow_comp_source G) (fun d => by
      simp only [Space.comparisonMorphism, Space.comparisonChartHom, reindexSourceChartIso,
        reindexTargetChartIso, Iso.refl_hom, NatTrans.id_app,
        Iso.trans_inv, NatTrans.comp_app, Category.assoc,
        Functor.isoWhiskerRight_inv, Functor.whiskerRight_app, eqToIso.inv, eqToHom_app]
      congr 2
      rw [← Functor.map_comp]
      refine congrArg (quotientStackProj G).map (fibredCategory_eqToHom_comp_eq _ _ _ ?_)
      exact (congrArg (· ≫ _) (eqToHom_refl _ _)).trans ((Category.id_comp _).trans rfl)) _

/-- **Stacks 044T, componentwise**: at a point of `R ×_U R` the 2-morphism of Stacks 044S at the
composite is the composite of its values at the two factors, up to the transports between the
endpoints. -/
theorem quotientStackTwoArrowNat_app_comp
    (X : (fibredCategory C S hS
      (AlgebraicSpaces.fiberProduct C S hS G.source G.target).obj).val.obj) :
    ∃ (e₁ : ((reindexLeg G G.comp ⋙ quotientStackSourceLeg G) ⋙ quotientStackProj G).obj X =
        ((reindexLeg G (secondArrow G) ⋙ quotientStackSourceLeg G) ⋙ quotientStackProj G).obj X)
      (e₂ : ((reindexLeg G (secondArrow G) ⋙ quotientStackTargetLeg G) ⋙
          quotientStackProj G).obj X =
        ((reindexLeg G (firstArrow G) ⋙ quotientStackSourceLeg G) ⋙ quotientStackProj G).obj X)
      (e₃ : ((reindexLeg G (firstArrow G) ⋙ quotientStackTargetLeg G) ⋙
          quotientStackProj G).obj X =
        ((reindexLeg G G.comp ⋙ quotientStackTargetLeg G) ⋙ quotientStackProj G).obj X),
      (quotientStackTwoArrowNat G).app ((reindexLeg G G.comp).obj X) =
        eqToHom e₁ ≫ (quotientStackTwoArrowNat G).app ((reindexLeg G (secondArrow G)).obj X) ≫
          eqToHom e₂ ≫ (quotientStackTwoArrowNat G).app ((reindexLeg G (firstArrow G)).obj X) ≫
            eqToHom e₃ := by
  have h := congrArg (fun η => η.toNatTrans.app X) (quotientStackTwoArrow_cocycle G)
  dsimp only at h
  refine ⟨congrArg (fun K => K.toFunctor.obj X) (quotientStackTwoArrow_source_comp_eq G),
    congrArg (fun K => K.toFunctor.obj X) (quotientStackTwoArrow_middle_comp_eq G),
    congrArg (fun K => K.toFunctor.obj X) (quotientStackTwoArrow_target_comp_eq G), h.trans ?_⟩
  refine (BasedNatTrans.comp_toNatTrans_app _ _ X).trans ?_
  refine congrArg₂ (· ≫ ·) (BasedNatTrans.eqToHom_toNatTrans_app _ X) ?_
  refine (BasedNatTrans.comp_toNatTrans_app _ _ X).trans ?_
  refine congrArg₂ (· ≫ ·) rfl ?_
  refine (BasedNatTrans.comp_toNatTrans_app _ _ X).trans ?_
  refine congrArg₂ (· ≫ ·) (BasedNatTrans.eqToHom_toNatTrans_app _ X) ?_
  refine (BasedNatTrans.comp_toNatTrans_app _ _ X).trans ?_
  exact congrArg₂ (· ≫ ·) rfl (BasedNatTrans.eqToHom_toNatTrans_app _ X)

/-- The transport along `c ≫ t = p₁ ≫ t` followed by the comparison through `t ∘ p₁` is the
comparison through `t ∘ c`. -/
theorem pullbackTransport_comp_cocycleFirstTarget :
    Space.pullbackTransport _ (comp_comp_target G) ≫ cocycleFirstTarget G F =
      cocycleCompTarget G F :=
  Space.pullbackTransport_comp_comparisonAlgebraicSpacesModules C S hS _ _ _ _ _ _ _ _ _ _ _ _ _
    _ _ _ _ _ _ _ _ _ _ _ (comp_comp_target G) (fun d => by
      obtain ⟨e₁, e₂, e₃, hE⟩ := quotientStackTwoArrowNat_app_comp G
        ((Space.restrictionFunctor C S hS
          (AlgebraicSpaces.fiberProduct C S hS G.source G.target).obj
          (fibredCategory C S hS (AlgebraicSpaces.fiberProduct C S hS G.source G.target).obj).val.p
          (StacksRepresentableCFG.EquivalenceOver.refl (fibredCategory C S hS
            (AlgebraicSpaces.fiberProduct C S hS G.source G.target).obj).val.p)).obj d.U)
      simp only [Space.comparisonMorphism, Space.comparisonChartHom, reindexTargetChartIso,
        Iso.refl_hom, Iso.refl_inv, NatTrans.id_app, Category.id_comp,
        Iso.trans_inv, NatTrans.comp_app, Category.assoc,
        Functor.isoWhiskerRight_inv, Functor.whiskerRight_app, eqToIso.inv, eqToHom_app,
        Functor.isoWhiskerLeft_inv, Functor.whiskerLeft_app, quotientStackTwoArrowIso,
        Iso.symm_inv, asIso_hom, eqToHom_map]
      rw [hE]
      refine eqToHom_comp_comp_comp_comp_eq _ _ _ _ _ _ _ _ _ ?_
      refine ((quotientStackProj G).eqToHom_comp_map_eq _ ?_ _).trans ?_
      · exact Functor.congr_obj (cocycleLegEq₀ G).symm _
      refine congrArg (quotientStackProj G).map (fibredCategory_eqToHom_comp_eq _ _ _ ?_)
      exact (congrArg (· ≫ _) (eqToHom_refl _ _)).trans ((Category.id_comp _).trans rfl)) _

include hF in
/-- **The comparison map through `s ∘ a`, into any target, is an isomorphism** for a
quasi-coherent module on `[U/R]`. -/
theorem isIso_twistedSourceComparison {P : AlgebraicSpaces C S hS} (a : P ⟶ G.arrows)
    (π : (fibredCategory C S hS P.obj).val.obj ⥤ (quotientStack G).obj)
    (hπ : (fibredCategory C S hS P.obj).val.p.IsFibredOneMorphism (quotientStack G).p π)
    (ψ : reindexLeg G a ⋙ (quotientStackSourceLeg G ⋙ quotientStackProj G) ≅ π)
    (hψ : ∀ X, (quotientStack G).p.IsHomLift (𝟙 ((quotientStack G).p.obj (π.obj X)))
      (ψ.inv.app X)) :
    IsIso (twistedSourceComparison G a π hπ ψ hψ F) :=
  Space.isIso_comparisonAlgebraicSpacesModules C S hS _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _
    (fun _ _ k hx hy => bijective_restrictionBaseChange_fibredRings_of_isQuasicoherentOnSite C S hS
      (quotientStack G).p (isFiberedInGroupoids_quotientStack G) F hF k hx hy)
    (isQuasicoherentOnSite_quotientStackObjectRestriction G F hF)

include hF in
/-- The right-hand side of the cocycle condition followed by the comparison through `s ∘ c`,
moved past the comparison maps of `p₂` and of `p₁`. -/
theorem groupoidTransitionComposite_comp_cocycleCompSource :
    Space.groupoidTransitionComposite C S hS G _ (quotientStackTransition G F hF) ≫
        cocycleCompSource G F =
      Space.pullbackTransport _ (comp_comp_target G) ≫ cocycleFirstTarget G F := by
  have e1 := groupoidPullbackTransition_quotientStackTransition_twisted G (firstArrow G)
    (cocycleTarget G) (isFibredOneMorphism_reindexSourceProj G G.comp) (cocycleFirstIso G)
    (isHomLift_cocycleFirstIso G) F hF
  have e2 := groupoidPullbackTransition_quotientStackTransition_twisted G (secondArrow G)
    (cocycleTarget G) (isFibredOneMorphism_reindexSourceProj G G.comp) (cocycleSecondIso G)
    (isHomLift_cocycleSecondIso G) F hF
  refine comp_eq_of_five_factors ?_ (pullbackTransport_comp_cocycleCompSource G F) e2
    (pullbackTransport_comp_cocycleSecondTarget G F) e1
  rw [Space.groupoidTransitionComposite_eq, Space.transitionComposite_eq_comp,
    ← Space.transitionReindex_eq_modulePullbackReindex,
    ← Space.transitionReindex_eq_modulePullbackReindex,
    ← Space.groupoidPullbackTransition_eq_transitionReindex,
    ← Space.groupoidPullbackTransition_eq_transitionReindex]

include hF in
/-- The right-hand side of the cocycle condition followed by the comparison through `s ∘ c` is
the comparison through `t ∘ c`. -/
theorem groupoidTransitionComposite_comp_cocycleCompSource_eq :
    Space.groupoidTransitionComposite C S hS G _ (quotientStackTransition G F hF) ≫
      cocycleCompSource G F = cocycleCompTarget G F :=
  (groupoidTransitionComposite_comp_cocycleCompSource G F hF).trans
    (pullbackTransport_comp_cocycleFirstTarget G F)

include hF in
/-- **The cocycle condition of Stacks 0441 for the transition morphism of Stacks 06WT**: the
reindexing of `α` along the composition `c : R ×_{s, U, t} R ⟶ R` is the composite of its
reindexings along the two projections, read through the three endpoint equations. -/
theorem groupoidPullbackTransition_quotientStackTransition_comp :
    Space.groupoidPullbackTransition C S hS G _ (quotientStackTransition G F hF) G.comp =
      Space.groupoidTransitionComposite C S hS G _ (quotientStackTransition G F hF) := by
  have := isIso_twistedSourceComparison G F hF G.comp (cocycleTarget G)
    (isFibredOneMorphism_reindexSourceProj G G.comp) (Iso.refl _) (fun _ => IsHomLift.id rfl)
  exact (Iso.cancel_iso_hom_right _ _ (asIso (cocycleCompSource G F))).1
    ((groupoidPullbackTransition_quotientStackTransition_twisted G G.comp (cocycleTarget G)
      (isFibredOneMorphism_reindexSourceProj G G.comp) (Iso.refl _)
      (fun _ => IsHomLift.id rfl) F hF).trans
      (groupoidTransitionComposite_comp_cocycleCompSource_eq G F hF).symm)

end AlgebraicGeometry.Stack

end
