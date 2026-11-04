module

public import StacksFrontier.CategoryTheory.Sites.Localization.Relocalize
public import StacksFrontier.CategoryTheory.Sites.Localization.RelocalizationTriangle
public import StacksFrontier.CategoryTheory.Sites.Localization.ToposComparison

/-!
# Stacks 04IL (1) carries the counit of `j_{V!} ⊣ j_V^{-1}` to that of `j_{U!} ⊣ j_U^{-1}`

Let `(C, J)` be a site and `f : V ⟶ U` a morphism of `C`.  Stacks 04IL (1)
(`CategoryTheory.OverShriek.inverseImageCompSheafFunctorToOverIso`) identifies the inverse image
`j^{-1}` of the relocalization functor `j = Over.map f`, read through Stacks 00Y1's equivalence
`Φ_U : Sh(C/U) ≌ Sh(C)/h_U^#` and its companion at `V`, with base change along
`h_f^# : h_V^# ⟶ h_U^#`.  This file identifies what that comparison does to the two localization
counits: evaluated at a restricted sheaf `j_U^{-1}A`, read through `Over.forget h_V^#` and
followed by Stacks 00Y1's identification of the sheaf underlying `Φ_V T` with `j_{V!}T` and the
counit `ε^V` of `j_{V!} ⊣ j_V^{-1}`, it is the first projection of the base change followed by the
same identification at `U` and the counit `ε^U` of `j_{U!} ⊣ j_U^{-1}`.

## Main results

* `CategoryTheory.OverShriek.shriek_unitIso_inv_app`: the lower shriek of the inverse unit of
  Stacks 00Y1, evaluated.
* `CategoryTheory.OverShriek.left_shriekCompSheafFunctorToOverIso_hom_app_comp`: Stacks 04IL (2),
  read through `Over.forget h_U^#` and Stacks 00Y1, is Stacks 03EH's `leftAdjointIso`.
* `CategoryTheory.OverShriek.shriek_inverseCompShriekRelocalizeIso_hom_app_comp`: the same
  statement with the two equivalences of Stacks 00Y1 unwound, which is the form the transposed
  Stacks 04IL (1) needs.
* `CategoryTheory.OverShriek.left_inverseImageCompSheafFunctorToOverIso_inv_app_comp_counit`:
  Stacks 04IL (1) carries `ε^V` to the first projection followed by `ε^U`.

## Implementation notes

The comparison of Stacks 04IL (1) is an `Adjunction.rightAdjointUniq`, and
`CategoryTheory.OverShriek.homEquiv_symm_inverseImageCompSheafFunctorToOverIso_inv_app` records
the transpose it prescribes.  Pushing that transpose along `j_{U!}` and following it with `ε^U`
turns the left-hand side into the counit of `j_{V!} ⊣ j_V^{-1}` and the right-hand side into the
first projection, provided one knows that the composite of Stacks 04IL (2) with Stacks 00Y1's
identifications at `U` and at `V` is the comparison `j_{V!} ≅ j_{U!} ∘ j_!` of Stacks 03EH — which
is `left_shriekCompSheafFunctorToOverIso_hom_app_comp` below, and is the one non-formal input.

That input is proved where Stacks 04IL (2) is proved, namely at the level of presheaves.  Both
`j_! ⋙ Φ_U ⋙ Over.forget h_U^#` and `j_{V!}` are left adjoint to `j_V^{-1}`, so by uniqueness of a
left adjoint it is enough to see that each factor of the chain defining Stacks 04IL (2) becomes,
after `Over.forget h_U^#`, the canonical comparison of two left adjoints: for the presheaf level
statement (2) because it holds by construction, for `relocalizeSheafifyIso` because it is itself an
`Adjunction.leftAdjointUniq`, and for `sheafifyCompFunctorToOverIso` because Stacks 03CD
(`sheafifyNatIso`) identifies the two.  `natTrans_ext_of_comp_counit` is what turns "the two
comparisons agree on counits" into "they are equal", and is also what identifies Stacks 03EH's
`leftAdjointIso` — a `leftAdjointUniq` of a transported adjunction — with the `leftAdjointUniq` of
the two adjunctions in play, without unfolding the transport.
-/

@[expose] public section

open CategoryTheory Opposite Limits MonoidalCategory CartesianMonoidalCategory

universe v u

namespace CategoryTheory

/-- **Two natural transformations of left adjoints which agree on counits are equal.**  If
`adj₁ : L₁ ⊣ R₁` and `adj₂ : L₂ ⊣ R₂`, a natural transformation `θ : L₁ ⟶ L₂` is determined by the
composites `θ.app (R₂ Y) ≫ adj₂.counit.app Y`: those composites are, through the transposition
`adj₁.homEquiv`, the components of the conjugate transformation `R₂ ⟶ R₁`, and conjugation
(`CategoryTheory.conjugateEquiv`) is a bijection. -/
theorem natTrans_ext_of_comp_counit {D E : Type*} [Category D] [Category E]
    {L₁ L₂ : D ⥤ E} {R₁ R₂ : E ⥤ D} (adj₁ : L₁ ⊣ R₁) (adj₂ : L₂ ⊣ R₂) {θ θ' : L₁ ⟶ L₂}
    (h : ∀ Y, θ.app (R₂.obj Y) ≫ adj₂.counit.app Y =
      θ'.app (R₂.obj Y) ≫ adj₂.counit.app Y) :
    θ = θ' := by
  refine (conjugateEquiv adj₂ adj₁).injective (NatTrans.ext (funext fun Y => ?_))
  refine (adj₁.homEquiv _ Y).symm.injective ?_
  rw [Adjunction.homEquiv_counit, Adjunction.homEquiv_counit,
    conjugateEquiv_counit adj₂ adj₁ θ Y, conjugateEquiv_counit adj₂ adj₁ θ' Y]
  exact h Y

end CategoryTheory

namespace CategoryTheory.OverShriek

noncomputable section

section Congr

variable {D : Type*} [Category D]

/-- Congruence in the first factor of a composite, with the second factor an argument rather than
part of a `congrArg` motive: a step of a long computation can then be applied with the surrounding
factors left to unification. -/
private theorem compRightOfEq {W X Y : D} {g g' : W ⟶ X} (e : g = g') (h : X ⟶ Y) :
    g ≫ h = g' ≫ h :=
  congrArg (fun z => z ≫ h) e

/-- Congruence in the second factor of a composite, with the first factor an argument. -/
private theorem compLeftOfEq {W X Y : D} (g : W ⟶ X) {h h' : X ⟶ Y} (e : h = h') :
    g ≫ h = g ≫ h' :=
  congrArg (fun z => g ≫ z) e

/-- A functor applied to a factored morphism, followed by a morphism, with the composite
reassociated. -/
private theorem map_comp_eq_of_eq {E : Type*} [Category E] (F : D ⥤ E) {X Y Z : D} {W : E}
    {g : X ⟶ Z} {a : X ⟶ Y} {b : Y ⟶ Z} (e : g = a ≫ b) (h : F.obj Z ⟶ W) :
    F.map g ≫ h = F.map a ≫ F.map b ≫ h := by
  rw [e, F.map_comp, Category.assoc]

end Congr

section WhiskerCongr

variable {A B E : Type*} [Category A] [Category B] [Category E]

private theorem whiskerRightOfEq {F G : A ⥤ B} {α β : F ⟶ G} (e : α = β) (H : B ⥤ E) :
    Functor.whiskerRight α H = Functor.whiskerRight β H :=
  congrArg (fun z => Functor.whiskerRight z H) e

private theorem whiskerLeftOfEq (H : A ⥤ B) {F G : B ⥤ E} {α β : F ⟶ G} (e : α = β) :
    Functor.whiskerLeft H α = Functor.whiskerLeft H β :=
  congrArg (fun z => Functor.whiskerLeft H z) e

end WhiskerCongr

section AdjunctionAlgebra

variable {A B D : Type*} [Category A] [Category B] [Category D]

/-- Whiskering a comparison of two left adjoints on the right is the comparison of the
composed adjunctions. -/
private theorem leftAdjointUniq_whiskerRight {L L' : A ⥤ B} {R : B ⥤ A} {F : B ⥤ D} {G : D ⥤ B}
    (a : L ⊣ R) (b : L' ⊣ R) (c : F ⊣ G) :
    Functor.whiskerRight (a.leftAdjointUniq b).hom F =
      ((a.comp c).leftAdjointUniq (b.comp c)).hom := by
  refine (conjugateEquiv (b.comp c) (a.comp c)).injective ?_
  refine Eq.trans (conjugateEquiv_whiskerRight b a c (a.leftAdjointUniq b).hom) ?_
  simp [Adjunction.leftAdjointUniq]

/-- Whiskering a comparison of two left adjoints on the left is the comparison of the
composed adjunctions. -/
private theorem leftAdjointUniq_whiskerLeft {L L' : B ⥤ D} {R : D ⥤ B} {F : A ⥤ B} {G : B ⥤ A}
    (a : L ⊣ R) (b : L' ⊣ R) (c : F ⊣ G) :
    Functor.whiskerLeft F (a.leftAdjointUniq b).hom =
      ((c.comp a).leftAdjointUniq (c.comp b)).hom := by
  refine (conjugateEquiv (c.comp b) (c.comp a)).injective ?_
  refine Eq.trans (conjugateEquiv_whiskerLeft b a c (a.leftAdjointUniq b).hom) ?_
  simp [Adjunction.leftAdjointUniq]

end AdjunctionAlgebra

section AdjunctionAssoc

variable {A₀ A₁ A₂ A₃ : Type*} [Category A₀] [Category A₁] [Category A₂] [Category A₃]

/-- Composition of adjunctions is associative. -/
private theorem adjunction_comp_assoc {L₁ : A₀ ⥤ A₁} {R₁ : A₁ ⥤ A₀} {L₂ : A₁ ⥤ A₂}
    {R₂ : A₂ ⥤ A₁} {L₃ : A₂ ⥤ A₃} {R₃ : A₃ ⥤ A₂}
    (a₁ : L₁ ⊣ R₁) (a₂ : L₂ ⊣ R₂) (a₃ : L₃ ⊣ R₃) :
    (a₁.comp a₂).comp a₃ = a₁.comp (a₂.comp a₃) := by
  refine Adjunction.ext (NatTrans.ext (funext fun X => ?_))
  simp [Adjunction.comp_unit_app, Functor.map_comp]

end AdjunctionAssoc

section OneObject

variable {C : Type u} [Category.{v} C] {U : C} (J : GrothendieckTopology C)
  [HasWeakSheafify J (Type v)] [J.WEqualsLocallyBijective (Type v)]
  [HasWeakSheafify (J.over U) (Type v)]
  [((Over.forget U).sheafPushforwardContinuous (Type v) (J.over U) J).IsRightAdjoint]

/-- **The lower shriek of the inverse unit of Stacks 00Y1.**  Applying `j_{U!}` to the inverse
unit of the equivalence `Φ_U` of Stacks 00Y1 gives
`CategoryTheory.OverShriek.inverseCompShriekIso` at `Φ_U T` followed by Stacks 00Y1's
identification of the sheaf underlying `Φ_U T` with `j_{U!}T`.

This is `CategoryTheory.OverShriek.inverseCompShriekIso_hom_app` together with the naturality of
that identification and the triangle identity of the equivalence. -/
theorem shriek_unitIso_inv_app (T : Sheaf (J.over U) (Type v)) :
    ((Over.forget U).sheafPullback (Type v) (J.over U) J).map
        ((sheafEquivalence (U := U) J).unitIso.inv.app T) =
      (inverseCompShriekIso (U := U) J).hom.app ((sheafFunctorToOver (U := U) J).obj T) ≫
        (sheafFunctorToOverForgetIso (U := U) J).hom.app T := by
  refine (Iso.cancel_iso_hom_left
    ((sheafFunctorToOverForgetIso (U := U) J).app
      ((sheafEquivalence (U := U) J).inverse.obj
        ((sheafFunctorToOver (U := U) J).obj T))) _ _).1 ?_
  refine Eq.trans ((sheafFunctorToOverForgetIso (U := U) J).hom.naturality
    ((sheafEquivalence (U := U) J).unitIso.inv.app T)).symm ?_
  refine Eq.trans ?_ (Category.assoc _ _ _)
  refine compRightOfEq ?_ _
  refine Eq.trans ?_ (compLeftOfEq _ (inverseCompShriekIso_hom_app J
    ((sheafFunctorToOver (U := U) J).obj T))).symm
  refine Eq.trans ?_ (Category.assoc _ _ _)
  refine Eq.trans ?_ (compRightOfEq
    ((sheafFunctorToOverForgetIso (U := U) J).hom_inv_id_app _).symm _)
  refine Eq.trans ?_ (Category.id_comp _).symm
  exact (congrArg (Over.forget ((presheafToSheaf J (Type v)).obj (yoneda.obj U))).map
    ((sheafEquivalence (U := U) J).counit_app_functor T)).symm

/-- `CategoryTheory.OverShriek.shriek_unitIso_inv_app` read in the other direction: the lower
shriek of the unit of Stacks 00Y1, followed by
`CategoryTheory.OverShriek.inverseCompShriekIso`, inverts Stacks 00Y1's identification of the
sheaf underlying `Φ_U T` with `j_{U!}T`. -/
theorem shriek_unitIso_hom_app_comp (T : Sheaf (J.over U) (Type v)) :
    ((Over.forget U).sheafPullback (Type v) (J.over U) J).map
          ((sheafEquivalence (U := U) J).unitIso.hom.app T) ≫
        (inverseCompShriekIso (U := U) J).hom.app ((sheafFunctorToOver (U := U) J).obj T) =
      (sheafFunctorToOverForgetIso (U := U) J).inv.app T := by
  refine ((sheafFunctorToOverForgetIso (U := U) J).app T).comp_hom_eq_id.1 ?_
  refine Eq.trans (Category.assoc _ _ _) ?_
  refine Eq.trans (compLeftOfEq _ (shriek_unitIso_inv_app J T).symm) ?_
  refine Eq.trans
    (((Over.forget U).sheafPullback (Type v) (J.over U) J).map_comp _ _).symm ?_
  refine Eq.trans (congrArg ((Over.forget U).sheafPullback (Type v) (J.over U) J).map
    ((sheafEquivalence (U := U) J).unitIso.hom_inv_id_app T)) ?_
  exact CategoryTheory.Functor.map_id _ _

end OneObject

section TwoObjects

variable {C : Type u} [Category.{v} C] {U V : C} (f : V ⟶ U) (J : GrothendieckTopology C)
  [HasWeakSheafify J (Type v)] [J.WEqualsLocallyBijective (Type v)]
  [HasWeakSheafify (J.over U) (Type v)]
  [((Over.forget U).sheafPushforwardContinuous (Type v) (J.over U) J).IsRightAdjoint]
  [HasWeakSheafify (J.over V) (Type v)]
  [((Over.forget V).sheafPushforwardContinuous (Type v) (J.over V) J).IsRightAdjoint]
  [((Over.map f).sheafPushforwardContinuous (Type v) (J.over V) (J.over U)).IsRightAdjoint]

omit [HasWeakSheafify J (Type v)] [J.WEqualsLocallyBijective (Type v)]
  [HasWeakSheafify (J.over U) (Type v)] [HasWeakSheafify (J.over V) (Type v)] in
/-- **Stacks 03EH's comparison carries one localization counit to the other.**  The counit of
`(j_! ∘ j_{U!}) ⊣ j_V^{-1}` is the inverse of Stacks 03EH's comparison `j_{V!} ≅ j_{U!} ∘ j_!`
followed by the counit of `j_{V!} ⊣ j_V^{-1}`.

This is `leftAdjointIso_hom_app_comp_map_comp_counit` at the identity. -/
theorem counit_comp_eq_leftAdjointIso_inv_app_comp (A : Sheaf J (Type v)) :
    (((Over.map f).sheafAdjunctionContinuous (Type v) (J.over V) (J.over U)).comp
          ((Over.forget U).sheafAdjunctionContinuous (Type v) (J.over U) J)).counit.app A =
      (leftAdjointIso J f (Type v)).inv.app ((J.overPullback (Type v) V).obj A) ≫
        ((Over.forget V).sheafAdjunctionContinuous (Type v) (J.over V) J).counit.app A := by
  have h2 : ((Over.forget V).sheafAdjunctionContinuous (Type v) (J.over V) J).counit.app A =
      (leftAdjointIso J f (Type v)).hom.app ((J.overPullback (Type v) V).obj A) ≫
        (((Over.map f).sheafAdjunctionContinuous (Type v) (J.over V) (J.over U)).comp
          ((Over.forget U).sheafAdjunctionContinuous (Type v) (J.over U) J)).counit.app A := by
    refine Eq.trans (Eq.trans (Category.id_comp _).symm
      (compRightOfEq (CategoryTheory.Functor.map_id _ _).symm _)) ?_
    refine Eq.trans (leftAdjointIso_hom_app_comp_map_comp_counit J f (Type v)
      (T := (J.overPullback (Type v) V).obj A) (Z := A) (𝟙 _)) ?_
    refine compLeftOfEq _ ?_
    exact Eq.trans (compRightOfEq (CategoryTheory.Functor.map_id _ _) _) (Category.id_comp _)
  refine Eq.trans ?_ (compLeftOfEq _ h2).symm
  refine Eq.trans ?_ (Category.assoc _ _ _)
  refine Eq.trans (Category.id_comp _).symm ?_
  exact compRightOfEq ((leftAdjointIso J f (Type v)).inv_hom_id_app _).symm _

/-! ### Reading the chain defining Stacks 04IL (2) through `Over.forget` -/

/-- **Stacks 04IL (2) at the presheaf level, read through `Over.forget h_U`, is canonical.**
Both `Λ ⋙ j_{U!}^{PSh}` and `j_{V!}^{PSh}` are left adjoint to restriction along `Over.forget V`,
and the presheaf level statement (2) — which holds by construction — is their canonical
comparison. -/
private theorem presheafRelocalizationForgetIso_homEquiv (G : (Over V)ᵒᵖ ⥤ Type v) :
    ((relocalizeAdjunction f).comp (presheafAdjunction (U := U))).homEquiv G _
        ((Functor.whiskerRight (relocalizePresheafFunctorToOverIso f).hom
          (Over.forget (yoneda.obj U))).app G) =
      (presheafAdjunction (U := V)).unit.app G := by
  ext W s
  rfl

private theorem presheafRelocalizationForgetIso_eq_canonical :
    Functor.whiskerRight (relocalizePresheafFunctorToOverIso f).hom
        (Over.forget (yoneda.obj U)) =
      (((relocalizeAdjunction f).comp (presheafAdjunction (U := U))).leftAdjointUniq
        (presheafAdjunction (U := V))).hom :=
  NatTrans.ext (funext fun G =>
    (((relocalizeAdjunction f).comp (presheafAdjunction (U := U))).homEquiv G _).injective
      (Eq.trans (presheafRelocalizationForgetIso_homEquiv f G)
        (Adjunction.homEquiv_leftAdjointUniq_hom_app _ _ G).symm))

omit [J.WEqualsLocallyBijective (Type v)] in
/-- Sheafifying the sheafification map and reading Stacks 00Y1 at `U` inverts Stacks 03CD. -/
private theorem comp_sheafFunctorToOverForgetIso_hom (P : (Over U)ᵒᵖ ⥤ Type v) :
    (presheafFunctor (U := U) ⋙ presheafToSheaf J (Type v)).map
          ((sheafificationAdjunction (J.over U) (Type v)).unit.app P) ≫
        (sheafFunctorToOverForgetIso (U := U) J).hom.app
          ((presheafToSheaf (J.over U) (Type v)).obj P) =
      (sheafifyNatIso (U := U) J).inv.app P := by
  change _ ≫ ((sheafifyNatIso (U := U) J).inv.app _ ≫
    ((Over.forget U).sheafPullback (Type v) (J.over U) J).map
      ((sheafificationAdjunction (J.over U) (Type v)).counit.app _)) = _
  refine Eq.trans (Category.assoc _ _ _).symm ?_
  refine Eq.trans (compRightOfEq ((sheafifyNatIso (U := U) J).inv.naturality _) _) ?_
  refine Eq.trans (Category.assoc _ _ _) (Eq.trans (compLeftOfEq _ ?_) (Category.comp_id _))
  refine Eq.trans (CategoryTheory.Functor.map_comp
    ((Over.forget U).sheafPullback (Type v) (J.over U) J) _ _).symm ?_
  refine Eq.trans (congrArg ((Over.forget U).sheafPullback (Type v) (J.over U) J).map
    ((sheafificationAdjunction (J.over U) (Type v)).left_triangle_components P)) ?_
  exact CategoryTheory.Functor.map_id _ _

omit [J.WEqualsLocallyBijective (Type v)] in
/-- **Stacks 04IL's bookkeeping isomorphism, read through `Over.forget h_U^#`.**  Stacks 00Y1 at
`U` followed by Stacks 03CD. -/
private theorem sheafifyCompFunctorToOverIso_forget :
    Functor.whiskerRight (sheafifyCompFunctorToOverIso (U := U) J).hom
        (Over.forget ((presheafToSheaf J (Type v)).obj (yoneda.obj U))) =
      Functor.whiskerLeft (presheafToSheaf (J.over U) (Type v))
          (sheafFunctorToOverForgetIso (U := U) J).hom ≫
        (sheafifyNatIso (U := U) J).hom := by
  refine NatTrans.ext (funext fun P => ?_)
  refine ((Iso.hom_comp_eq_id ((Over.forget
    ((presheafToSheaf J (Type v)).obj (yoneda.obj U))).mapIso
      ((asIso (sheafifyCompFunctorToOverHom (U := U) J)).app P))).1 ?_).symm
  refine Eq.trans (Category.assoc _ _ _).symm ?_
  refine Eq.trans (compRightOfEq (comp_sheafFunctorToOverForgetIso_hom J P) _) ?_
  exact (sheafifyNatIso (U := U) J).inv_hom_id_app P

omit [HasWeakSheafify J (Type v)] [J.WEqualsLocallyBijective (Type v)]
  [HasWeakSheafify (J.over U) (Type v)]
  [((Over.forget U).sheafPushforwardContinuous (Type v) (J.over U) J).IsRightAdjoint]
  [((Over.forget V).sheafPushforwardContinuous (Type v) (J.over V) J).IsRightAdjoint] in
/-- Transporting the sheafified relocalization adjunction along
`Functor.sheafPushforwardContinuousCompSheafToPresheafIso` — which is the identity — leaves it
alone. -/
private theorem ofNatIsoRight_sheafPushforwardContinuousComp :
    ((sheafificationAdjunction (J.over V) (Type v)).comp
          ((Over.map f).sheafAdjunctionContinuous (Type v) (J.over V) (J.over U))).ofNatIsoRight
        ((Over.map f).sheafPushforwardContinuousCompSheafToPresheafIso (Type v)
          (J.over V) (J.over U)) =
      (sheafificationAdjunction (J.over V) (Type v)).comp
        ((Over.map f).sheafAdjunctionContinuous (Type v) (J.over V) (J.over U)) := by
  refine Adjunction.ext ?_
  exact Eq.trans (compLeftOfEq _ (Functor.whiskerLeft_id' _)) (Category.comp_id _)

omit [HasWeakSheafify J (Type v)] [J.WEqualsLocallyBijective (Type v)]
  [((Over.forget U).sheafPushforwardContinuous (Type v) (J.over U) J).IsRightAdjoint]
  [((Over.forget V).sheafPushforwardContinuous (Type v) (J.over V) J).IsRightAdjoint] in
/-- Stacks 04IL's sheafification comparison, inverted, is the canonical comparison of the two
left adjoints it compares. -/
private theorem relocalizeSheafifyIso_inv_aux :
    (relocalizeSheafifyIso f J).inv =
      (Adjunction.leftAdjointUniq
        (((sheafificationAdjunction (J.over V) (Type v)).comp
            ((Over.map f).sheafAdjunctionContinuous (Type v) (J.over V) (J.over U))).ofNatIsoRight
          ((Over.map f).sheafPushforwardContinuousCompSheafToPresheafIso (Type v)
            (J.over V) (J.over U)))
        ((relocalizeAdjunction f).comp (sheafificationAdjunction (J.over U) (Type v)))).hom :=
  NatTrans.ext (funext fun G => Adjunction.leftAdjointUniq_inv_app _ _ G)

omit [HasWeakSheafify J (Type v)] [J.WEqualsLocallyBijective (Type v)]
  [((Over.forget U).sheafPushforwardContinuous (Type v) (J.over U) J).IsRightAdjoint]
  [((Over.forget V).sheafPushforwardContinuous (Type v) (J.over V) J).IsRightAdjoint] in
private theorem relocalizeSheafifyIso_inv :
    (relocalizeSheafifyIso f J).inv =
      (Adjunction.leftAdjointUniq
        ((sheafificationAdjunction (J.over V) (Type v)).comp
          ((Over.map f).sheafAdjunctionContinuous (Type v) (J.over V) (J.over U)))
        ((relocalizeAdjunction f).comp (sheafificationAdjunction (J.over U) (Type v)))).hom :=
  Eq.trans (relocalizeSheafifyIso_inv_aux f J)
    (congrArg (fun z => (Adjunction.leftAdjointUniq z
        ((relocalizeAdjunction f).comp (sheafificationAdjunction (J.over U) (Type v)))).hom)
      (ofNatIsoRight_sheafPushforwardContinuousComp f J))

omit [HasWeakSheafify J (Type v)] [J.WEqualsLocallyBijective (Type v)]
  [((Over.forget V).sheafPushforwardContinuous (Type v) (J.over V) J).IsRightAdjoint] in
private theorem relocalizeSheafifyIso_inv_whiskerRight :
    Functor.whiskerRight (relocalizeSheafifyIso f J).inv
        ((Over.forget U).sheafPullback (Type v) (J.over U) J) =
      (Adjunction.leftAdjointUniq
        (((sheafificationAdjunction (J.over V) (Type v)).comp
            ((Over.map f).sheafAdjunctionContinuous (Type v) (J.over V) (J.over U))).comp
          ((Over.forget U).sheafAdjunctionContinuous (Type v) (J.over U) J))
        (((relocalizeAdjunction f).comp (sheafificationAdjunction (J.over U) (Type v))).comp
          ((Over.forget U).sheafAdjunctionContinuous (Type v) (J.over U) J))).hom :=
  Eq.trans (whiskerRightOfEq (relocalizeSheafifyIso_inv f J) _)
    (leftAdjointUniq_whiskerRight _ _
      ((Over.forget U).sheafAdjunctionContinuous (Type v) (J.over U) J))

omit [J.WEqualsLocallyBijective (Type v)]
  [((Over.forget V).sheafPushforwardContinuous (Type v) (J.over V) J).IsRightAdjoint] in
/-- The three comparisons which make up Stacks 04IL (2) after Stacks 00Y1 has been split off
compose to the single canonical comparison of left adjoints. -/
private theorem relocalizeInner_leftAdjointUniq :
    Functor.whiskerRight (relocalizeSheafifyIso f J).inv
          ((Over.forget U).sheafPullback (Type v) (J.over U) J) ≫
        Functor.whiskerLeft (relocalizePresheafFunctor f) (sheafifyNatIso (U := U) J).hom ≫
          Functor.whiskerRight (Functor.whiskerRight
            (relocalizePresheafFunctorToOverIso f).hom (Over.forget (yoneda.obj U)))
            (presheafToSheaf J (Type v)) =
      (Adjunction.leftAdjointUniq
        (((sheafificationAdjunction (J.over V) (Type v)).comp
            ((Over.map f).sheafAdjunctionContinuous (Type v) (J.over V) (J.over U))).comp
          ((Over.forget U).sheafAdjunctionContinuous (Type v) (J.over U) J))
        ((presheafAdjunction (U := V)).comp (sheafificationAdjunction J (Type v)))).hom := by
  have hb := adjunction_comp_assoc (relocalizeAdjunction f)
    (sheafificationAdjunction (J.over U) (Type v))
    ((Over.forget U).sheafAdjunctionContinuous (Type v) (J.over U) J)
  have hc := (adjunction_comp_assoc (relocalizeAdjunction f) (presheafAdjunction (U := U))
    (sheafificationAdjunction J (Type v))).symm
  have h2 : Functor.whiskerLeft (relocalizePresheafFunctor f) (sheafifyNatIso (U := U) J).hom =
      (Adjunction.leftAdjointUniq
        (((relocalizeAdjunction f).comp (sheafificationAdjunction (J.over U) (Type v))).comp
          ((Over.forget U).sheafAdjunctionContinuous (Type v) (J.over U) J))
        (((relocalizeAdjunction f).comp (presheafAdjunction (U := U))).comp
          (sheafificationAdjunction J (Type v)))).hom := by
    refine Eq.trans (leftAdjointUniq_whiskerLeft
      ((sheafificationAdjunction (J.over U) (Type v)).comp
        ((Over.forget U).sheafAdjunctionContinuous (Type v) (J.over U) J))
      ((presheafAdjunction (U := U)).comp (sheafificationAdjunction J (Type v)))
      (relocalizeAdjunction f)) ?_
    refine Eq.trans (congrArg (fun z => (Adjunction.leftAdjointUniq z
      ((relocalizeAdjunction f).comp
        ((presheafAdjunction (U := U)).comp (sheafificationAdjunction J (Type v))))).hom)
      hb.symm) ?_
    exact congrArg (fun z => (Adjunction.leftAdjointUniq
      (((relocalizeAdjunction f).comp (sheafificationAdjunction (J.over U) (Type v))).comp
        ((Over.forget U).sheafAdjunctionContinuous (Type v) (J.over U) J)) z).hom) hc
  have h3 : Functor.whiskerRight (Functor.whiskerRight
        (relocalizePresheafFunctorToOverIso f).hom (Over.forget (yoneda.obj U)))
      (presheafToSheaf J (Type v)) =
      (Adjunction.leftAdjointUniq
        (((relocalizeAdjunction f).comp (presheafAdjunction (U := U))).comp
          (sheafificationAdjunction J (Type v)))
        ((presheafAdjunction (U := V)).comp (sheafificationAdjunction J (Type v)))).hom :=
    Eq.trans (whiskerRightOfEq (presheafRelocalizationForgetIso_eq_canonical f) _)
      (leftAdjointUniq_whiskerRight _ _ (sheafificationAdjunction J (Type v)))
  refine Eq.trans (compRightOfEq (relocalizeSheafifyIso_inv_whiskerRight f J) _) ?_
  refine Eq.trans (compLeftOfEq _ (compRightOfEq h2 _)) ?_
  refine Eq.trans (compLeftOfEq _ (compLeftOfEq _ h3)) ?_
  refine Eq.trans (Category.assoc _ _ _).symm ?_
  refine Eq.trans (compRightOfEq (Adjunction.leftAdjointUniq_trans _ _ _) _) ?_
  exact Adjunction.leftAdjointUniq_trans _ _ _

omit [J.WEqualsLocallyBijective (Type v)] [HasWeakSheafify (J.over U) (Type v)]
  [((Over.forget U).sheafPushforwardContinuous (Type v) (J.over U) J).IsRightAdjoint]
  [HasWeakSheafify (J.over V) (Type v)]
  [((Over.forget V).sheafPushforwardContinuous (Type v) (J.over V) J).IsRightAdjoint]
  [((Over.map f).sheafPushforwardContinuous (Type v) (J.over V) (J.over U)).IsRightAdjoint] in
/-- The structural maps to `h_U^#` of the two descriptions of `Λ G` agree on the nose, so the
comparison `Over.mapCompPostIso` is the identity on underlying sheaves. -/
private theorem mapCompPost_forget_eq_id :
    Functor.whiskerRight (Functor.whiskerLeft (presheafFunctorToOver (U := V))
        (Over.mapCompPostIso (presheafToSheaf J (Type v)) (yoneda.map f)).hom)
      (Over.forget ((presheafToSheaf J (Type v)).obj (yoneda.obj U))) = 𝟙 _ :=
  NatTrans.ext (funext fun _ => rfl)

omit [J.WEqualsLocallyBijective (Type v)]
  [((Over.forget V).sheafPushforwardContinuous (Type v) (J.over V) J).IsRightAdjoint] in
/-- **Stacks 04IL (2) before the final bookkeeping, read through `Over.forget h_U^#`.**  It is
Stacks 00Y1 at `U` followed by the canonical comparison of left adjoints. -/
private theorem relocalizeInnerIso_forget :
    Functor.whiskerRight (relocalizeInnerIso f J).hom
        (Over.forget ((presheafToSheaf J (Type v)).obj (yoneda.obj U))) =
      Functor.whiskerLeft (presheafToSheaf (J.over V) (Type v) ⋙
            (Over.map f).sheafPullback (Type v) (J.over V) (J.over U))
          (sheafFunctorToOverForgetIso (U := U) J).hom ≫
        (Adjunction.leftAdjointUniq
          (((sheafificationAdjunction (J.over V) (Type v)).comp
              ((Over.map f).sheafAdjunctionContinuous (Type v) (J.over V) (J.over U))).comp
            ((Over.forget U).sheafAdjunctionContinuous (Type v) (J.over U) J))
          ((presheafAdjunction (U := V)).comp (sheafificationAdjunction J (Type v)))).hom := by
  have hw2 : Functor.whiskerRight (Functor.whiskerLeft (relocalizePresheafFunctor f)
          (sheafifyCompFunctorToOverIso (U := U) J).hom)
        (Over.forget ((presheafToSheaf J (Type v)).obj (yoneda.obj U))) =
      Functor.whiskerLeft (relocalizePresheafFunctor f ⋙ presheafToSheaf (J.over U) (Type v))
          (sheafFunctorToOverForgetIso (U := U) J).hom ≫
        Functor.whiskerLeft (relocalizePresheafFunctor f) (sheafifyNatIso (U := U) J).hom :=
    Eq.trans (whiskerLeftOfEq _ (sheafifyCompFunctorToOverIso_forget J))
      (Functor.whiskerLeft_comp _ _ _)
  refine Eq.trans (Functor.whiskerRight_comp _ _ _) ?_
  refine Eq.trans (compLeftOfEq _ (Functor.whiskerRight_comp _ _ _)) ?_
  refine Eq.trans (compLeftOfEq _ (compLeftOfEq _ (Functor.whiskerRight_comp _ _ _))) ?_
  refine Eq.trans (compLeftOfEq _ (compLeftOfEq _
    (Eq.trans (compLeftOfEq _ (mapCompPost_forget_eq_id f J)) (Category.comp_id _)))) ?_
  refine Eq.trans (compLeftOfEq _ (compRightOfEq hw2 _)) ?_
  refine Eq.trans (compLeftOfEq _ (Category.assoc _ _ _)) ?_
  refine Eq.trans (Category.assoc _ _ _).symm ?_
  refine Eq.trans (compRightOfEq (Functor.whiskerLeft_comp_whiskerRight
    (relocalizeSheafifyIso f J).inv (sheafFunctorToOverForgetIso (U := U) J).hom).symm _) ?_
  refine Eq.trans (Category.assoc _ _ _) ?_
  exact compLeftOfEq _ (relocalizeInner_leftAdjointUniq f J)

omit [HasWeakSheafify J (Type v)] [J.WEqualsLocallyBijective (Type v)]
  [HasWeakSheafify (J.over U) (Type v)] [HasWeakSheafify (J.over V) (Type v)] in
/-- **Stacks 03EH's comparison is the canonical comparison of left adjoints.**  Both
`j_{V!}` and `j_! ⋙ j_{U!}` are left adjoint to `j_V^{-1}`, and the inverse of
`leftAdjointIso` is their canonical comparison: the two agree on counits, by
`counit_comp_eq_leftAdjointIso_inv_app_comp`. -/
private theorem leftAdjointIso_inv_eq_leftAdjointUniq :
    (leftAdjointIso J f (Type v)).inv =
      (Adjunction.leftAdjointUniq
        (((Over.map f).sheafAdjunctionContinuous (Type v) (J.over V) (J.over U)).comp
          ((Over.forget U).sheafAdjunctionContinuous (Type v) (J.over U) J))
        ((Over.forget V).sheafAdjunctionContinuous (Type v) (J.over V) J)).hom :=
  CategoryTheory.natTrans_ext_of_comp_counit
    (((Over.map f).sheafAdjunctionContinuous (Type v) (J.over V) (J.over U)).comp
      ((Over.forget U).sheafAdjunctionContinuous (Type v) (J.over U) J))
    ((Over.forget V).sheafAdjunctionContinuous (Type v) (J.over V) J)
    (fun Y => Eq.trans (counit_comp_eq_leftAdjointIso_inv_app_comp f J Y).symm
      (Adjunction.leftAdjointUniq_hom_app_counit _ _ Y).symm)

omit [HasWeakSheafify J (Type v)] [J.WEqualsLocallyBijective (Type v)]
  [HasWeakSheafify (J.over U) (Type v)] in
/-- The inverted sheafification counit of Stacks 04IL (2) is absorbed by the naturality of the
canonical comparison `j_! ⋙ j_{U!} ⟶ j_{V!}`. -/
private theorem counit_whisker_leftAdjointUniq_app (G : Sheaf (J.over V) (Type v)) :
    ((Over.map f).sheafPullback (Type v) (J.over V) (J.over U) ⋙
          (Over.forget U).sheafPullback (Type v) (J.over U) J).map
        ((asIso (sheafificationAdjunction (J.over V) (Type v)).counit).inv.app G) ≫
      ((Adjunction.leftAdjointUniq
            (((Over.map f).sheafAdjunctionContinuous (Type v) (J.over V) (J.over U)).comp
              ((Over.forget U).sheafAdjunctionContinuous (Type v) (J.over U) J))
            ((Over.forget V).sheafAdjunctionContinuous (Type v) (J.over V) J)).hom.app
          ((sheafToPresheaf (J.over V) (Type v) ⋙
            presheafToSheaf (J.over V) (Type v)).obj G) ≫
        ((Over.forget V).sheafPullback (Type v) (J.over V) J).map
          ((sheafificationAdjunction (J.over V) (Type v)).counit.app G)) =
      (Adjunction.leftAdjointUniq
        (((Over.map f).sheafAdjunctionContinuous (Type v) (J.over V) (J.over U)).comp
          ((Over.forget U).sheafAdjunctionContinuous (Type v) (J.over U) J))
        ((Over.forget V).sheafAdjunctionContinuous (Type v) (J.over V) J)).hom.app G := by
  refine Eq.trans (compLeftOfEq _ ((Adjunction.leftAdjointUniq
    (((Over.map f).sheafAdjunctionContinuous (Type v) (J.over V) (J.over U)).comp
      ((Over.forget U).sheafAdjunctionContinuous (Type v) (J.over U) J))
    ((Over.forget V).sheafAdjunctionContinuous (Type v) (J.over V) J)).hom.naturality
      ((sheafificationAdjunction (J.over V) (Type v)).counit.app G)).symm) ?_
  refine Eq.trans (Category.assoc _ _ _).symm ?_
  refine Eq.trans (compRightOfEq (CategoryTheory.Functor.map_comp
    ((Over.map f).sheafPullback (Type v) (J.over V) (J.over U) ⋙
      (Over.forget U).sheafPullback (Type v) (J.over U) J) _ _).symm _) ?_
  refine Eq.trans (compRightOfEq (congrArg
    ((Over.map f).sheafPullback (Type v) (J.over V) (J.over U) ⋙
      (Over.forget U).sheafPullback (Type v) (J.over U) J).map
    ((asIso (sheafificationAdjunction (J.over V) (Type v)).counit).inv_hom_id_app G)) _) ?_
  exact Eq.trans (compRightOfEq (CategoryTheory.Functor.map_id _ _) _) (Category.id_comp _)

omit [J.WEqualsLocallyBijective (Type v)] [HasWeakSheafify (J.over U) (Type v)] in
/-- Stacks 03CD at `V`, inverted, turns the comparison of Stacks 04IL (2) into Stacks 03EH's. -/
private theorem leftAdjointUniq_comp_sheafifyNatIso_inv :
    (Adjunction.leftAdjointUniq
          (((sheafificationAdjunction (J.over V) (Type v)).comp
              ((Over.map f).sheafAdjunctionContinuous (Type v) (J.over V) (J.over U))).comp
            ((Over.forget U).sheafAdjunctionContinuous (Type v) (J.over U) J))
          ((presheafAdjunction (U := V)).comp (sheafificationAdjunction J (Type v)))).hom ≫
        (sheafifyNatIso (U := V) J).inv =
      Functor.whiskerLeft (presheafToSheaf (J.over V) (Type v))
        (Adjunction.leftAdjointUniq
          (((Over.map f).sheafAdjunctionContinuous (Type v) (J.over V) (J.over U)).comp
            ((Over.forget U).sheafAdjunctionContinuous (Type v) (J.over U) J))
          ((Over.forget V).sheafAdjunctionContinuous (Type v) (J.over V) J)).hom := by
  have hnatV : (sheafifyNatIso (U := V) J).inv =
      (Adjunction.leftAdjointUniq
        ((presheafAdjunction (U := V)).comp (sheafificationAdjunction J (Type v)))
        ((sheafificationAdjunction (J.over V) (Type v)).comp
          ((Over.forget V).sheafAdjunctionContinuous (Type v) (J.over V) J))).hom :=
    NatTrans.ext (funext fun G => Adjunction.leftAdjointUniq_inv_app _ _ G)
  refine Eq.trans (compLeftOfEq _ hnatV) ?_
  refine Eq.trans (Adjunction.leftAdjointUniq_trans _ _ _) ?_
  refine Eq.trans (congrArg (fun z => (Adjunction.leftAdjointUniq z
      ((sheafificationAdjunction (J.over V) (Type v)).comp
        ((Over.forget V).sheafAdjunctionContinuous (Type v) (J.over V) J))).hom)
    (adjunction_comp_assoc (sheafificationAdjunction (J.over V) (Type v))
      ((Over.map f).sheafAdjunctionContinuous (Type v) (J.over V) (J.over U))
      ((Over.forget U).sheafAdjunctionContinuous (Type v) (J.over U) J))) ?_
  exact (leftAdjointUniq_whiskerLeft _ _ (sheafificationAdjunction (J.over V) (Type v))).symm

omit [J.WEqualsLocallyBijective (Type v)] [HasWeakSheafify (J.over U) (Type v)] in
/-- The inverted sheafification counit, Stacks 04IL (2)'s canonical comparison and Stacks 00Y1 at
`V` compose to Stacks 03EH's canonical comparison. -/
private theorem shriek_counit_whisker :
    Functor.whiskerRight (Functor.whiskerRight
            (asIso (sheafificationAdjunction (J.over V) (Type v)).counit).inv
            ((Over.map f).sheafPullback (Type v) (J.over V) (J.over U)))
          ((Over.forget U).sheafPullback (Type v) (J.over U) J) ≫
        (Functor.whiskerLeft (sheafToPresheaf (J.over V) (Type v))
            (Adjunction.leftAdjointUniq
              (((sheafificationAdjunction (J.over V) (Type v)).comp
                  ((Over.map f).sheafAdjunctionContinuous (Type v) (J.over V) (J.over U))).comp
                ((Over.forget U).sheafAdjunctionContinuous (Type v) (J.over U) J))
              ((presheafAdjunction (U := V)).comp (sheafificationAdjunction J (Type v)))).hom ≫
          (sheafFunctorToOverForgetIso (U := V) J).hom) =
      (Adjunction.leftAdjointUniq
        (((Over.map f).sheafAdjunctionContinuous (Type v) (J.over V) (J.over U)).comp
          ((Over.forget U).sheafAdjunctionContinuous (Type v) (J.over U) J))
        ((Over.forget V).sheafAdjunctionContinuous (Type v) (J.over V) J)).hom := by
  have hbracket : Functor.whiskerLeft (sheafToPresheaf (J.over V) (Type v))
          (Adjunction.leftAdjointUniq
            (((sheafificationAdjunction (J.over V) (Type v)).comp
                ((Over.map f).sheafAdjunctionContinuous (Type v) (J.over V) (J.over U))).comp
              ((Over.forget U).sheafAdjunctionContinuous (Type v) (J.over U) J))
            ((presheafAdjunction (U := V)).comp (sheafificationAdjunction J (Type v)))).hom ≫
        (sheafFunctorToOverForgetIso (U := V) J).hom =
      Functor.whiskerLeft (sheafToPresheaf (J.over V) (Type v) ⋙
            presheafToSheaf (J.over V) (Type v))
          (Adjunction.leftAdjointUniq
            (((Over.map f).sheafAdjunctionContinuous (Type v) (J.over V) (J.over U)).comp
              ((Over.forget U).sheafAdjunctionContinuous (Type v) (J.over U) J))
            ((Over.forget V).sheafAdjunctionContinuous (Type v) (J.over V) J)).hom ≫
        Functor.whiskerRight (sheafificationAdjunction (J.over V) (Type v)).counit
          ((Over.forget V).sheafPullback (Type v) (J.over V) J) := by
    refine Eq.trans (Category.assoc _ _ _).symm ?_
    refine compRightOfEq ?_ _
    exact Eq.trans (Functor.whiskerLeft_comp _ _ _).symm
      (whiskerLeftOfEq _ (leftAdjointUniq_comp_sheafifyNatIso_inv f J))
  refine Eq.trans (compLeftOfEq _ hbracket) ?_
  exact NatTrans.ext (funext fun G => counit_whisker_leftAdjointUniq_app f J G)

omit [J.WEqualsLocallyBijective (Type v)] in
/-- **Stacks 04IL (2), read through `Over.forget h_U^#` and Stacks 00Y1, is Stacks 03EH.**
This is the target as an identity of natural transformations. -/
private theorem shriekCompSheafFunctorToOverIso_forget :
    Functor.whiskerRight (shriekCompSheafFunctorToOverIso f J).hom
          (Over.forget ((presheafToSheaf J (Type v)).obj (yoneda.obj U))) ≫
        (sheafFunctorToOverForgetIso (U := V) J).hom =
      Functor.whiskerLeft ((Over.map f).sheafPullback (Type v) (J.over V) (J.over U))
          (sheafFunctorToOverForgetIso (U := U) J).hom ≫
        (Adjunction.leftAdjointUniq
          (((Over.map f).sheafAdjunctionContinuous (Type v) (J.over V) (J.over U)).comp
            ((Over.forget U).sheafAdjunctionContinuous (Type v) (J.over U) J))
          ((Over.forget V).sheafAdjunctionContinuous (Type v) (J.over V) J)).hom := by
  have hid : Functor.whiskerRight
        (Functor.leftUnitor ((Over.map f).sheafPullback (Type v) (J.over V) (J.over U) ⋙
          sheafFunctorToOver (U := U) J)).inv
        (Over.forget ((presheafToSheaf J (Type v)).obj (yoneda.obj U))) = 𝟙 _ :=
    NatTrans.ext (funext fun _ => rfl)
  have hwB : Functor.whiskerRight (Functor.whiskerLeft (sheafToPresheaf (J.over V) (Type v))
          (relocalizeInnerIso f J).hom)
        (Over.forget ((presheafToSheaf J (Type v)).obj (yoneda.obj U))) =
      Functor.whiskerLeft (sheafToPresheaf (J.over V) (Type v) ⋙
            (presheafToSheaf (J.over V) (Type v) ⋙
              (Over.map f).sheafPullback (Type v) (J.over V) (J.over U)))
          (sheafFunctorToOverForgetIso (U := U) J).hom ≫
        Functor.whiskerLeft (sheafToPresheaf (J.over V) (Type v))
          (Adjunction.leftAdjointUniq
            (((sheafificationAdjunction (J.over V) (Type v)).comp
                ((Over.map f).sheafAdjunctionContinuous (Type v) (J.over V) (J.over U))).comp
              ((Over.forget U).sheafAdjunctionContinuous (Type v) (J.over U) J))
            ((presheafAdjunction (U := V)).comp (sheafificationAdjunction J (Type v)))).hom :=
    Eq.trans (whiskerLeftOfEq _ (relocalizeInnerIso_forget f J))
      (Functor.whiskerLeft_comp _ _ _)
  refine Eq.trans (compRightOfEq (Functor.whiskerRight_comp _ _ _) _) ?_
  refine Eq.trans (compRightOfEq (compLeftOfEq _ (Functor.whiskerRight_comp _ _ _)) _) ?_
  refine Eq.trans (compRightOfEq
    (Eq.trans (compRightOfEq hid _) (Category.id_comp _)) _) ?_
  refine Eq.trans (compRightOfEq (compLeftOfEq _ hwB) _) ?_
  refine Eq.trans (compRightOfEq (Category.assoc _ _ _).symm _) ?_
  refine Eq.trans (Category.assoc _ _ _) ?_
  refine Eq.trans (compRightOfEq (Functor.whiskerLeft_comp_whiskerRight
    (Functor.whiskerRight (asIso (sheafificationAdjunction (J.over V) (Type v)).counit).inv
      ((Over.map f).sheafPullback (Type v) (J.over V) (J.over U)))
    (sheafFunctorToOverForgetIso (U := U) J).hom).symm _) ?_
  refine Eq.trans (Category.assoc _ _ _) ?_
  exact compLeftOfEq _ (shriek_counit_whisker f J)

omit [J.WEqualsLocallyBijective (Type v)] in
/-- **Stacks 04IL (2), read through `Over.forget h_U^#` and Stacks 00Y1, is Stacks 03EH.**  The
comparison `j_! ⋙ Φ_U ≅ Φ_V ⋙ Over.map h_f^#` of Stacks 04IL (2), read on underlying sheaves and
followed by Stacks 00Y1's identification of the sheaf underlying `Φ_V T` with `j_{V!}T`, is
Stacks 00Y1's identification of the sheaf underlying `Φ_U(j_!T)` with `j_{U!}j_!T` followed by the
comparison `j_{V!} ≅ j_{U!} ∘ j_!` of Stacks 03EH.

Both sides are isomorphisms of two left adjoints of `j_V^{-1}`; this says that they are *the*
comparison of those two left adjoints. -/
theorem left_shriekCompSheafFunctorToOverIso_hom_app_comp
    (T : Sheaf (J.over V) (Type v)) :
    ((shriekCompSheafFunctorToOverIso f J).hom.app T).left ≫
        (sheafFunctorToOverForgetIso (U := V) J).hom.app T =
      (sheafFunctorToOverForgetIso (U := U) J).hom.app
          (((Over.map f).sheafPullback (Type v) (J.over V) (J.over U)).obj T) ≫
        (leftAdjointIso J f (Type v)).inv.app T :=
  Eq.trans (congrFun (congrArg NatTrans.app (shriekCompSheafFunctorToOverIso_forget f J)) T)
    (compLeftOfEq _ (congrFun (congrArg NatTrans.app
      (leftAdjointIso_inv_eq_leftAdjointUniq f J)) T).symm)

omit [J.WEqualsLocallyBijective (Type v)] in
/-- `left_shriekCompSheafFunctorToOverIso_hom_app_comp` with the two identifications of
Stacks 00Y1 moved to the other side. -/
theorem forgetIso_inv_app_comp_left_shriekCompSheafFunctorToOverIso_hom_app
    (T : Sheaf (J.over V) (Type v)) :
    (sheafFunctorToOverForgetIso (U := U) J).inv.app
          (((Over.map f).sheafPullback (Type v) (J.over V) (J.over U)).obj T) ≫
        ((shriekCompSheafFunctorToOverIso f J).hom.app T).left =
      (leftAdjointIso J f (Type v)).inv.app T ≫
        (sheafFunctorToOverForgetIso (U := V) J).inv.app T := by
  refine Eq.trans (compLeftOfEq _ (Category.comp_id _).symm) ?_
  refine Eq.trans (compLeftOfEq _ (compLeftOfEq _
    ((sheafFunctorToOverForgetIso (U := V) J).hom_inv_id_app T).symm)) ?_
  refine Eq.trans (compLeftOfEq _ (Category.assoc _ _ _).symm) ?_
  refine Eq.trans (compLeftOfEq _ (compRightOfEq
    (left_shriekCompSheafFunctorToOverIso_hom_app_comp f J T) _)) ?_
  refine Eq.trans (compLeftOfEq _ (Category.assoc _ _ _)) ?_
  refine Eq.trans (Category.assoc _ _ _).symm ?_
  refine Eq.trans (compRightOfEq
    ((sheafFunctorToOverForgetIso (U := U) J).inv_hom_id_app _) _) ?_
  exact Category.id_comp _

/-- **Stacks 04IL (1), transposed, read through the two lower shrieks.**  The comparison
`Φ_V^{-1} ⋙ j_! ≅ Over.map h_f^# ⋙ Φ_U^{-1}` of
`CategoryTheory.OverShriek.inverseCompShriekRelocalizeIso`, pushed along `j_{U!}` and followed by
`CategoryTheory.OverShriek.inverseCompShriekIso` at `U`, is Stacks 03EH's comparison followed by
`CategoryTheory.OverShriek.inverseCompShriekIso` at `V`.

Both sides are isomorphisms `j_{U!}j_!Φ_V^{-1}H ≅ H` for `H` an object of `Sh(C)/h_V^#`; this is
`left_shriekCompSheafFunctorToOverIso_hom_app_comp` with the two equivalences unwound. -/
theorem shriek_inverseCompShriekRelocalizeIso_hom_app_comp
    (H : Over ((presheafToSheaf J (Type v)).obj (yoneda.obj V))) :
    ((Over.forget U).sheafPullback (Type v) (J.over U) J).map
          ((inverseCompShriekRelocalizeIso f J).hom.app H) ≫
        (inverseCompShriekIso (U := U) J).hom.app
          ((Over.map ((presheafToSheaf J (Type v)).map (yoneda.map f))).obj H) =
      (leftAdjointIso J f (Type v)).inv.app
          ((sheafEquivalence (U := V) J).inverse.obj H) ≫
        (inverseCompShriekIso (U := V) J).hom.app H := by
  have hcomp : (inverseCompShriekRelocalizeIso f J).hom.app H =
      (sheafEquivalence (U := U) J).unitIso.hom.app
          (((Over.map f).sheafPullback (Type v) (J.over V) (J.over U)).obj
            ((sheafEquivalence (U := V) J).inverse.obj H)) ≫
        (sheafEquivalence (U := U) J).inverse.map
          ((shriekCompSheafFunctorToOverIso f J).hom.app
              ((sheafEquivalence (U := V) J).inverse.obj H) ≫
            (Over.map ((presheafToSheaf J (Type v)).map (yoneda.map f))).map
              ((sheafEquivalence (U := V) J).counitIso.hom.app H)) := by
    refine Eq.trans (Category.id_comp _) (compLeftOfEq _ ?_)
    refine Eq.trans ?_ (CategoryTheory.Functor.map_comp
      (sheafEquivalence (U := U) J).inverse _ _).symm
    refine compLeftOfEq _ ?_
    refine Eq.trans (compLeftOfEq _ (CategoryTheory.Functor.map_id
      (sheafEquivalence (U := U) J).inverse _)) ?_
    exact Category.comp_id _
  refine Eq.trans (map_comp_eq_of_eq _ hcomp _) ?_
  refine Eq.trans (compLeftOfEq _ ((inverseCompShriekIso (U := U) J).hom.naturality _)) ?_
  refine Eq.trans (Category.assoc _ _ _).symm ?_
  refine Eq.trans (compRightOfEq (shriek_unitIso_hom_app_comp J _) _) ?_
  refine Eq.trans (compLeftOfEq _
    ((Over.forget ((presheafToSheaf J (Type v)).obj (yoneda.obj U))).map_comp _ _)) ?_
  refine Eq.trans (Category.assoc _ _ _).symm ?_
  refine Eq.trans (compRightOfEq
    (forgetIso_inv_app_comp_left_shriekCompSheafFunctorToOverIso_hom_app f J _) _) ?_
  refine Eq.trans (Category.assoc _ _ _) ?_
  exact compLeftOfEq _ (inverseCompShriekIso_hom_app J H).symm

omit [HasWeakSheafify (J.over U) (Type v)] in
/-- **The counit of `Φ_V^{-1} ⋙ j_! ⊣ j^{-1} ⋙ Φ_V`, pushed along `j_{U!}`.**  Followed by the
counit `ε^U`, it is Stacks 03EH's comparison followed by Stacks 00Y1's two identifications at `V`
and the counit `ε^V`.

This is `counit_comp_eq_leftAdjointIso_inv_app_comp` with the inverse unit of Stacks 00Y1
evaluated by `shriek_unitIso_inv_app`. -/
theorem shriek_relocalizeCounit_comp_counit (A : Sheaf J (Type v)) :
    ((Over.forget U).sheafPullback (Type v) (J.over U) J).map
          (((sheafEquivalence (U := V) J).symm.toAdjunction.comp
              ((Over.map f).sheafAdjunctionContinuous (Type v) (J.over V) (J.over U))).counit.app
            ((J.overPullback (Type v) U).obj A)) ≫
        ((Over.forget U).sheafAdjunctionContinuous (Type v) (J.over U) J).counit.app A =
      (leftAdjointIso J f (Type v)).inv.app
          ((sheafEquivalence (U := V) J).inverse.obj
            ((sheafFunctorToOver (U := V) J).obj ((J.overPullback (Type v) V).obj A))) ≫
        (inverseCompShriekIso (U := V) J).hom.app
            ((sheafFunctorToOver (U := V) J).obj ((J.overPullback (Type v) V).obj A)) ≫
          (sheafFunctorToOverForgetIso (U := V) J).hom.app ((J.overPullback (Type v) V).obj A) ≫
            ((Over.forget V).sheafAdjunctionContinuous (Type v) (J.over V) J).counit.app A := by
  refine Eq.trans (map_comp_eq_of_eq _ (Adjunction.comp_counit_app _ _ _) _) ?_
  refine Eq.trans (compLeftOfEq _ (counit_comp_eq_leftAdjointIso_inv_app_comp f J A)) ?_
  refine Eq.trans (Category.assoc _ _ _).symm ?_
  refine Eq.trans (compRightOfEq ((leftAdjointIso J f (Type v)).inv.naturality _) _) ?_
  refine Eq.trans (Category.assoc _ _ _) ?_
  refine compLeftOfEq _ ?_
  refine Eq.trans (compRightOfEq (shriek_unitIso_inv_app J _) _) ?_
  exact Category.assoc _ _ _

omit [HasWeakSheafify (J.over U) (Type v)] in
/-- `shriek_relocalizeCounit_comp_counit` with a morphism of `Sh(C)/h_V^#` absorbed: this is the
shape the transpose of Stacks 04IL (1) takes once it has been pushed along `j_{U!}` and followed
by `ε^U`. -/
theorem shriek_map_comp_relocalizeCounit_comp_counit (A : Sheaf J (Type v))
    {P : Over ((presheafToSheaf J (Type v)).obj (yoneda.obj V))}
    (m : P ⟶ (sheafFunctorToOver (U := V) J).obj ((J.overPullback (Type v) V).obj A)) :
    ((Over.forget U).sheafPullback (Type v) (J.over U) J).map
          (((sheafEquivalence (U := V) J).inverse ⋙
              (Over.map f).sheafPullback (Type v) (J.over V) (J.over U)).map m ≫
            ((sheafEquivalence (U := V) J).symm.toAdjunction.comp
              ((Over.map f).sheafAdjunctionContinuous (Type v) (J.over V)
                (J.over U))).counit.app ((J.overPullback (Type v) U).obj A)) ≫
        ((Over.forget U).sheafAdjunctionContinuous (Type v) (J.over U) J).counit.app A =
      (leftAdjointIso J f (Type v)).inv.app ((sheafEquivalence (U := V) J).inverse.obj P) ≫
        (inverseCompShriekIso (U := V) J).hom.app P ≫
          m.left ≫
            (sheafFunctorToOverForgetIso (U := V) J).hom.app
                ((J.overPullback (Type v) V).obj A) ≫
              ((Over.forget V).sheafAdjunctionContinuous (Type v) (J.over V) J).counit.app A := by
  refine Eq.trans (map_comp_eq_of_eq _ rfl _) ?_
  refine Eq.trans (compLeftOfEq _ (shriek_relocalizeCounit_comp_counit f J A)) ?_
  refine Eq.trans (Category.assoc _ _ _).symm ?_
  refine Eq.trans (compRightOfEq ((leftAdjointIso J f (Type v)).inv.naturality
    ((sheafEquivalence (U := V) J).inverse.map m)) _) ?_
  refine Eq.trans (Category.assoc _ _ _) ?_
  refine compLeftOfEq _ ?_
  refine Eq.trans (Category.assoc _ _ _).symm ?_
  refine Eq.trans (compRightOfEq ((inverseCompShriekIso (U := V) J).hom.naturality m) _) ?_
  exact Category.assoc _ _ _

omit [HasWeakSheafify (J.over V) (Type v)]
  [((Over.forget V).sheafPushforwardContinuous (Type v) (J.over V) J).IsRightAdjoint]
  [((Over.map f).sheafPushforwardContinuous (Type v) (J.over V) (J.over U)).IsRightAdjoint] in
/-- **The counit of `Over.map h_f^# ⋙ Φ_U^{-1} ⊣ Φ_U ⋙ Over.pullback h_f^#`, pushed along
`j_{U!}`.**  Followed by the counit `ε^U`, it is
`CategoryTheory.OverShriek.inverseCompShriekIso` at `U` followed by the first projection of the
base change and Stacks 00Y1's identification at `U` and `ε^U`. -/
theorem shriek_mapPullbackCounit_comp_counit (A : Sheaf J (Type v)) :
    ((Over.forget U).sheafPullback (Type v) (J.over U) J).map
          (((Over.mapPullbackAdj ((presheafToSheaf J (Type v)).map (yoneda.map f))).comp
              (sheafEquivalence (U := U) J).symm.toAdjunction).counit.app
            ((J.overPullback (Type v) U).obj A)) ≫
        ((Over.forget U).sheafAdjunctionContinuous (Type v) (J.over U) J).counit.app A =
      (inverseCompShriekIso (U := U) J).hom.app
          ((Over.map ((presheafToSheaf J (Type v)).map (yoneda.map f))).obj
            ((sheafFunctorToOver (U := U) J ⋙
              Over.pullback ((presheafToSheaf J (Type v)).map
                (yoneda.map f))).obj ((J.overPullback (Type v) U).obj A))) ≫
        pullback.fst
            ((sheafFunctorToOver (U := U) J).obj ((J.overPullback (Type v) U).obj A)).hom
            ((presheafToSheaf J (Type v)).map (yoneda.map f)) ≫
          (sheafFunctorToOverForgetIso (U := U) J).hom.app ((J.overPullback (Type v) U).obj A) ≫
            ((Over.forget U).sheafAdjunctionContinuous (Type v) (J.over U) J).counit.app A := by
  have hpsi : (Over.forget ((presheafToSheaf J (Type v)).obj (yoneda.obj U))).map
        ((Over.mapPullbackAdj ((presheafToSheaf J (Type v)).map (yoneda.map f))).counit.app
          ((sheafFunctorToOver (U := U) J).obj ((J.overPullback (Type v) U).obj A))) =
      pullback.fst
        ((sheafFunctorToOver (U := U) J).obj ((J.overPullback (Type v) U).obj A)).hom
        ((presheafToSheaf J (Type v)).map (yoneda.map f)) := by
    simp
  refine Eq.trans (map_comp_eq_of_eq _ (Adjunction.comp_counit_app _ _ _) _) ?_
  refine Eq.trans (compLeftOfEq _ (compRightOfEq (shriek_unitIso_inv_app J _) _)) ?_
  refine Eq.trans (compLeftOfEq _ (Category.assoc _ _ _)) ?_
  refine Eq.trans (Category.assoc _ _ _).symm ?_
  refine Eq.trans (compRightOfEq ((inverseCompShriekIso (U := U) J).hom.naturality _) _) ?_
  refine Eq.trans (Category.assoc _ _ _) ?_
  exact compLeftOfEq _ (compRightOfEq hpsi _)

/-- **Stacks 04IL (1) carries the counit of `j_{V!} ⊣ j_V^{-1}` to that of
`j_{U!} ⊣ j_U^{-1}`.**  The inverse of Stacks 04IL (1) at a restricted sheaf `j_U^{-1}A`, read
through `Over.forget h_V^#` and followed by Stacks 00Y1's identification at `V` and the counit
`ε^V`, is the first projection of the base change along `h_f^#` followed by Stacks 00Y1's
identification at `U` and the counit `ε^U`.

The two counits belong to two different localizations of the site, and Stacks 04IL (1) is what
relates them. -/
@[stacks 04IL "(1) carries the counit of j_{V!} to the counit of j_{U!}"]
theorem left_inverseImageCompSheafFunctorToOverIso_inv_app_comp_counit
    (A : Sheaf J (Type v)) :
    ((inverseImageCompSheafFunctorToOverIso f J).inv.app
            ((J.overPullback (Type v) U).obj A)).left ≫
        (sheafFunctorToOverForgetIso (U := V) J).hom.app ((J.overPullback (Type v) V).obj A) ≫
          ((Over.forget V).sheafAdjunctionContinuous (Type v) (J.over V) J).counit.app A =
      pullback.fst
            ((sheafFunctorToOver (U := U) J).obj ((J.overPullback (Type v) U).obj A)).hom
            ((presheafToSheaf J (Type v)).map (yoneda.map f)) ≫
          (sheafFunctorToOverForgetIso (U := U) J).hom.app ((J.overPullback (Type v) U).obj A) ≫
            ((Over.forget U).sheafAdjunctionContinuous (Type v) (J.over U) J).counit.app A := by
  have H1 : ((sheafEquivalence (U := V) J).inverse ⋙
          (Over.map f).sheafPullback (Type v) (J.over V) (J.over U)).map
            ((inverseImageCompSheafFunctorToOverIso f J).inv.app
              ((J.overPullback (Type v) U).obj A)) ≫
          ((sheafEquivalence (U := V) J).symm.toAdjunction.comp
            ((Over.map f).sheafAdjunctionContinuous (Type v) (J.over V) (J.over U))).counit.app
              ((J.overPullback (Type v) U).obj A) =
        (inverseCompShriekRelocalizeIso f J).hom.app
            ((sheafFunctorToOver (U := U) J ⋙
              Over.pullback ((presheafToSheaf J (Type v)).map (yoneda.map f))).obj
                ((J.overPullback (Type v) U).obj A)) ≫
          ((Over.mapPullbackAdj ((presheafToSheaf J (Type v)).map (yoneda.map f))).comp
            (sheafEquivalence (U := U) J).symm.toAdjunction).counit.app
              ((J.overPullback (Type v) U).obj A) :=
    homEquiv_symm_inverseImageCompSheafFunctorToOverIso_inv_app f J _
  refine (Iso.cancel_iso_hom_left
    ((leftAdjointIso J f (Type v)).symm.app
        ((sheafEquivalence (U := V) J).inverse.obj
          ((sheafFunctorToOver (U := U) J ⋙
            Over.pullback ((presheafToSheaf J (Type v)).map (yoneda.map f))).obj
              ((J.overPullback (Type v) U).obj A))) ≪≫
      (inverseCompShriekIso (U := V) J).app
        ((sheafFunctorToOver (U := U) J ⋙
          Over.pullback ((presheafToSheaf J (Type v)).map (yoneda.map f))).obj
            ((J.overPullback (Type v) U).obj A))) _ _).1 ?_
  refine Eq.trans (Category.assoc _ _ _) ?_
  refine Eq.trans (shriek_map_comp_relocalizeCounit_comp_counit f J A
    ((inverseImageCompSheafFunctorToOverIso f J).inv.app
      ((J.overPullback (Type v) U).obj A))).symm ?_
  refine Eq.trans (map_comp_eq_of_eq _ H1 _) ?_
  refine Eq.trans (compLeftOfEq _ (shriek_mapPullbackCounit_comp_counit f J A)) ?_
  refine Eq.trans (Category.assoc _ _ _).symm ?_
  exact compRightOfEq (shriek_inverseCompShriekRelocalizeIso_hom_app_comp f J _) _

end TwoObjects

end

end CategoryTheory.OverShriek
