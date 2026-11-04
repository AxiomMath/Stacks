module

public import StacksFrontier.AlgebraicGeometry.Spaces.Thickenings.EtaleToposThickeningHom

/-!
# The étale topos of a thickening with a retraction

Let `i : X ⟶ X'` be a thickening of algebraic spaces and `q : X' ⟶ X` a retraction of it,
`i ≫ q = 𝟙 X`. In the proof of Stacks 0DLL this is `X₀ ⟶ X_V ⟶ X₀`, the second map being the
base change along `Spec k[V] ⟶ Spec k` given by the second component `z` of a point of the fibre.
Base change of étale scheme charts along `q` followed by base change along `i` is the identity of
the small étale site of `X` (`AlgebraicGeometry.Space.smallBaseChangeRetractionIso`), so
restriction of sheaves along chart base change along `q` is an inverse of the Comparison Lemma
equivalence of
`AlgebraicGeometry.Space.isEquivalence_sheafPushforward_smallBaseChange_of_isThickeningHom`.
`AlgebraicGeometry.Space.thickeningRetractionEquivalence` is that equivalence with its unit chosen
to be the one of the charts, so that a morphism into a restricted sheaf is computed on the charts
of `X` (`AlgebraicGeometry.Space.thickeningRetractionEquivalence_homEquiv_symm`).

Nothing here is registered.

## References

* [Stacks Project, Tag 05ZM](https://stacks.math.columbia.edu/tag/05ZM)
* [Stacks Project, Tag 0DLL](https://stacks.math.columbia.edu/tag/0DLL)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits Opposite

universe w' w u

namespace AlgebraicGeometry.Space

variable (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)

variable {X X' : AlgebraicSpaces B S hS}

section Retraction

variable (i : X ⟶ X') (q : X' ⟶ X) (h : i ≫ q = 𝟙 X)
  (hi : yoneda.relativelyRepresentable i.hom) (hq : yoneda.relativelyRepresentable q.hom)

include h in
/-- If `i ≫ q = 𝟙 X`, then the underlying morphisms of presheaves satisfy
`i.hom ≫ q.hom = 𝟙 X.1`. -/
theorem retraction_hom_comp : i.hom ≫ q.hom = 𝟙 X.1 :=
  congrArg (fun t : X ⟶ X => t.hom) h

/-- The chart map `(U ×_X X') ×_{X'} X ⟶ U`: the two cartesian projections. -/
noncomputable def smallBaseChangeRetractionHom (U : SmallEtale B S hS X.1) :
    (smallBaseChange B S hS q hq ⋙ smallBaseChange B S hS i hi).obj U ⟶ U :=
  ObjectProperty.homMk (CostructuredArrow.homMk
    (hi.snd (hq.fst U.1.hom) ≫ hq.snd U.1.hom) (by
      change yoneda.map (hi.snd (hq.fst U.1.hom) ≫ hq.snd U.1.hom) ≫ U.1.hom =
        hi.fst (hq.fst U.1.hom)
      rw [yoneda.map_comp, Category.assoc, ← hq.w U.1.hom, ← Category.assoc, ← hi.w,
        Category.assoc, retraction_hom_comp B S hS i q h, Category.comp_id]))

/-- The chart map `U ⟶ (U ×_X X') ×_{X'} X`: the section of the two cartesian projections. -/
noncomputable def smallBaseChangeRetractionInv (U : SmallEtale B S hS X.1) :
    U ⟶ (smallBaseChange B S hS q hq ⋙ smallBaseChange B S hS i hi).obj U :=
  ObjectProperty.homMk (CostructuredArrow.homMk
    (hi.lift U.1.hom (hq.lift (U.1.hom ≫ i.hom) (𝟙 U.1.left) (by
        rw [Category.assoc, retraction_hom_comp B S hS i q h, Category.comp_id,
          CategoryTheory.Functor.map_id, Category.id_comp])) (by
        change U.1.hom ≫ i.hom = yoneda.map _ ≫ hq.fst U.1.hom
        rw [hq.lift_fst]))
    (hi.lift_fst _ _ _))

/-- `smallBaseChangeRetractionInv` followed by `smallBaseChangeRetractionHom` is the identity
of `U`. -/
theorem smallBaseChangeRetractionInv_hom (U : SmallEtale B S hS X.1) :
    smallBaseChangeRetractionInv B S hS i q h hi hq U ≫
      smallBaseChangeRetractionHom B S hS i q h hi hq U = 𝟙 U := by
  refine ObjectProperty.hom_ext _ (CostructuredArrow.hom_ext _ _ ?_)
  exact (Category.assoc _ _ _).symm.trans
    ((congrArg (· ≫ hq.snd U.1.hom) (hi.lift_snd _ _ _)).trans (hq.lift_snd _ _ _))

/-- `smallBaseChangeRetractionHom` followed by `smallBaseChangeRetractionInv` is the identity
of `(U ×_X X') ×_{X'} X`. -/
theorem smallBaseChangeRetractionHom_inv (U : SmallEtale B S hS X.1) :
    smallBaseChangeRetractionHom B S hS i q h hi hq U ≫
      smallBaseChangeRetractionInv B S hS i q h hi hq U = 𝟙 _ := by
  refine ObjectProperty.hom_ext _ (CostructuredArrow.hom_ext _ _ ?_)
  have hw : yoneda.map (hi.snd (hq.fst U.1.hom) ≫ hq.snd U.1.hom) ≫ U.1.hom =
      hi.fst (hq.fst U.1.hom) :=
    (smallBaseChangeRetractionHom B S hS i q h hi hq U).hom.w
  let a : hi.pullback (hq.fst U.1.hom) ⟶ hq.pullback U.1.hom := hi.snd (hq.fst U.1.hom)
  let b : hq.pullback U.1.hom ⟶ U.1.left := hq.snd U.1.hom
  let l : U.1.left ⟶ hi.pullback (hq.fst U.1.hom) :=
    (smallBaseChangeRetractionInv B S hS i q h hi hq U).hom.left
  change (a ≫ b) ≫ l = 𝟙 _
  have hl₁ : yoneda.map l ≫ hi.fst (hq.fst U.1.hom) = U.1.hom := hi.lift_fst _ _ _
  have hw' : yoneda.map a ≫ yoneda.map b ≫ U.1.hom = hi.fst (hq.fst U.1.hom) := by
    rw [← Category.assoc, ← yoneda.map_comp]
    exact hw
  have hiw : hi.fst (hq.fst U.1.hom) ≫ i.hom = yoneda.map a ≫ hq.fst U.1.hom := hi.w _
  have hm : l ≫ a ≫ b = 𝟙 _ :=
    congrArg (fun f => f.hom.left) (smallBaseChangeRetractionInv_hom B S hS i q h hi hq U)
  refine hi.hom_ext ?_ ?_
  · rw [yoneda.map_comp, Category.assoc, hl₁, CategoryTheory.Functor.map_id, Category.id_comp]
    exact hw
  · rw [Category.assoc, Category.id_comp]
    refine hq.hom_ext ?_ ?_
    · simp only [yoneda.map_comp, Category.assoc]
      rw [← hiw, ← Category.assoc (yoneda.map l), hl₁, reassoc_of% hw']
    · simp only [Category.assoc]
      rw [hm, Category.comp_id]

/-- **Base change of charts along a retraction and then along the section is the identity.** For
`i : X ⟶ X'` and `q : X' ⟶ X` with `i ≫ q = 𝟙 X`, the two cartesian projections
`(U ×_X X') ×_{X'} X ⟶ U ×_X X' ⟶ U` identify the iterated base change of an étale chart `U` of
`X` with `U`. -/
noncomputable def smallBaseChangeRetractionIso :
    smallBaseChange B S hS q hq ⋙ smallBaseChange B S hS i hi ≅ 𝟭 (SmallEtale B S hS X.1) :=
  NatIso.ofComponents
    (fun U ↦
      { hom := smallBaseChangeRetractionHom B S hS i q h hi hq U
        inv := smallBaseChangeRetractionInv B S hS i q h hi hq U
        hom_inv_id := smallBaseChangeRetractionHom_inv B S hS i q h hi hq U
        inv_hom_id := smallBaseChangeRetractionInv_hom B S hS i q h hi hq U })
    (fun {U U'} k ↦ by
      refine ObjectProperty.hom_ext _ ?_
      refine CostructuredArrow.hom_ext _ _ ?_
      have h1 := smallBaseChange_map_snd B S hS i hi ((smallBaseChange B S hS q hq).map k)
      have h2 := smallBaseChange_map_snd B S hS q hq k
      exact (Category.assoc _ _ _).symm.trans ((congrArg (· ≫ hq.snd U'.1.hom) h1).trans
        ((Category.assoc _ _ _).trans ((congrArg (hi.snd _ ≫ ·) h2).trans
          (Category.assoc _ _ _).symm))))

/-- The component of `smallBaseChangeRetractionIso` at `U` is the composite of the two
cartesian projections `(U ×_X X') ×_{X'} X ⟶ U ×_X X' ⟶ U`. -/
theorem smallBaseChangeRetractionIso_hom_app_left (U : SmallEtale B S hS X.1) :
    ((smallBaseChangeRetractionIso B S hS i q h hi hq).hom.app U).hom.left =
      hi.snd (hq.fst U.1.hom) ≫ hq.snd U.1.hom := rfl

/-- The inverse component of `smallBaseChangeRetractionIso` at `U` is the morphism
`U ⟶ (U ×_X X') ×_{X'} X` induced by `U ⟶ X ⟶ X'` and the identity of `U`. -/
theorem smallBaseChangeRetractionIso_inv_app_left (U : SmallEtale B S hS X.1) :
    ((smallBaseChangeRetractionIso B S hS i q h hi hq).inv.app U).hom.left =
      hi.lift U.1.hom (hq.lift (U.1.hom ≫ i.hom) (𝟙 U.1.left) (by
        rw [Category.assoc, retraction_hom_comp B S hS i q h, Category.comp_id,
          CategoryTheory.Functor.map_id, Category.id_comp])) (by
        change U.1.hom ≫ i.hom = yoneda.map _ ≫ hq.fst U.1.hom
        rw [hq.lift_fst]) := rfl

end Retraction

variable {i : X ⟶ X'} (hi : IsThickeningHom B S hS i) {q : X' ⟶ X} (h : i ≫ q = 𝟙 X)
  (hq : yoneda.relativelyRepresentable q.hom)

include hi in
/-- Base change of étale scheme charts along a retraction of a thickening is continuous. -/
theorem isContinuous_smallBaseChange_retraction :
    (smallBaseChange B S hS q hq).IsContinuous (SmallEtale.topology B S hS X.1)
      (SmallEtale.topology B S hS X'.1) :=
  isContinuous_smallBaseChange B S hS q hq

/-- **Restriction along chart base change along `i` and then along `q` is the identity**, on
sheaves with values in any category: the two restrictions compose to restriction along
`AlgebraicGeometry.Space.smallBaseChangeRetractionIso`. -/
noncomputable def sheafPushforwardRetractionIso (A : Type w) [Category.{w'} A] :
    letI := smallBaseChange_isDenseSubsite_of_isThickeningHom B S hS hi
    letI := isContinuous_smallBaseChange B S hS q hq
    (smallBaseChange B S hS i hi.isClosedImmersion.rep).sheafPushforwardContinuous A
        (SmallEtale.topology B S hS X'.1) (SmallEtale.topology B S hS X.1) ⋙
      (smallBaseChange B S hS q hq).sheafPushforwardContinuous A
        (SmallEtale.topology B S hS X.1) (SmallEtale.topology B S hS X'.1) ≅ 𝟭 _ :=
  letI := smallBaseChange_isDenseSubsite_of_isThickeningHom B S hS hi
  letI := isContinuous_smallBaseChange B S hS q hq
  letI := Functor.isContinuous_comp (smallBaseChange B S hS q hq)
    (smallBaseChange B S hS i hi.isClosedImmersion.rep) (SmallEtale.topology B S hS X.1)
    (SmallEtale.topology B S hS X'.1) (SmallEtale.topology B S hS X.1)
  Functor.sheafPushforwardContinuousComp _ _ _ _ _ _ ≪≫
    Functor.sheafPushforwardContinuousId'
      (smallBaseChangeRetractionIso B S hS i q h hi.isClosedImmersion.rep hq) _ _

/-- **The Comparison Lemma equivalence of a thickening with a retraction**, with functor the
restriction along chart base change along `i`, inverse the restriction along chart base change
along `q`, and unit `AlgebraicGeometry.Space.sheafPushforwardRetractionIso`. -/
noncomputable def thickeningRetractionEquivalence (A : Type w) [Category.{w'} A]
    [HasLimitsOfSize.{u, u} A] :
    Sheaf (SmallEtale.topology B S hS X.1) A ≌ Sheaf (SmallEtale.topology B S hS X'.1) A :=
  letI := smallBaseChange_isDenseSubsite_of_isThickeningHom B S hS hi
  letI := isContinuous_smallBaseChange B S hS q hq
  letI := isEquivalence_sheafPushforward_smallBaseChange_of_isThickeningHom B S hS hi A
  letI G := (smallBaseChange B S hS i hi.isClosedImmersion.rep).sheafPushforwardContinuous A
    (SmallEtale.topology B S hS X'.1) (SmallEtale.topology B S hS X.1)
  letI F := (smallBaseChange B S hS q hq).sheafPushforwardContinuous A
    (SmallEtale.topology B S hS X.1) (SmallEtale.topology B S hS X'.1)
  letI E := G.asEquivalence
  letI ε := sheafPushforwardRetractionIso B S hS hi h hq A
  (CategoryTheory.Equivalence.mk F G
    (E.counitIso.symm ≪≫ Functor.isoWhiskerRight
      ((Functor.rightUnitor _).symm ≪≫ Functor.isoWhiskerLeft E.inverse ε.symm ≪≫
        (Functor.associator _ _ _).symm ≪≫ Functor.isoWhiskerRight E.counitIso F ≪≫
        Functor.leftUnitor F) G)
    (sheafPushforwardRetractionIso B S hS hi h hq A)).symm

/-- The functor of `thickeningRetractionEquivalence` is restriction along chart base change
along `i`. -/
theorem thickeningRetractionEquivalence_functor (A : Type w) [Category.{w'} A]
    [HasLimitsOfSize.{u, u} A] :
    letI := smallBaseChange_isDenseSubsite_of_isThickeningHom B S hS hi
    (thickeningRetractionEquivalence B S hS hi h hq A).functor =
      (smallBaseChange B S hS i hi.isClosedImmersion.rep).sheafPushforwardContinuous A
        (SmallEtale.topology B S hS X'.1) (SmallEtale.topology B S hS X.1) := rfl

/-- The inverse of `thickeningRetractionEquivalence` is restriction along chart base change
along `q`. -/
theorem thickeningRetractionEquivalence_inverse (A : Type w) [Category.{w'} A]
    [HasLimitsOfSize.{u, u} A] :
    letI := isContinuous_smallBaseChange B S hS q hq
    (thickeningRetractionEquivalence B S hS hi h hq A).inverse =
      (smallBaseChange B S hS q hq).sheafPushforwardContinuous A
        (SmallEtale.topology B S hS X.1) (SmallEtale.topology B S hS X'.1) := rfl

/-- The unit of `thickeningRetractionEquivalence` is the inverse of
`sheafPushforwardRetractionIso`. -/
theorem thickeningRetractionEquivalence_unitIso (A : Type w) [Category.{w'} A]
    [HasLimitsOfSize.{u, u} A] :
    (thickeningRetractionEquivalence B S hS hi h hq A).unitIso =
      (sheafPushforwardRetractionIso B S hS hi h hq A).symm := rfl

/-- **A morphism into a restricted sheaf, read on the charts of `X`.** Under the equivalence
`AlgebraicGeometry.Space.thickeningRetractionEquivalence`, a morphism `P ⟶ i_* R` of sheaves on
`X'` corresponds to the morphism `q^* P ⟶ q^* i_* R ⟶ R` on `X` obtained by restricting along
chart base change along `q` and composing with the chart identification
`AlgebraicGeometry.Space.sheafPushforwardRetractionIso`. -/
theorem thickeningRetractionEquivalence_homEquiv_symm (A : Type w) [Category.{w'} A]
    [HasLimitsOfSize.{u, u} A] (P : Sheaf (SmallEtale.topology B S hS X'.1) A)
    (R : Sheaf (SmallEtale.topology B S hS X.1) A)
    (x : P ⟶ (thickeningRetractionEquivalence B S hS hi h hq A).functor.obj R) :
    ((thickeningRetractionEquivalence B S hS hi h hq A).symm.toAdjunction.homEquiv P R).symm x =
      (thickeningRetractionEquivalence B S hS hi h hq A).inverse.map x ≫
        (sheafPushforwardRetractionIso B S hS hi h hq A).hom.app R := by
  rw [Adjunction.homEquiv_counit]
  rfl

end AlgebraicGeometry.Space

end
