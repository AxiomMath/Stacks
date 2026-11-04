module

public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.Constructible.LimitCategory.StageRealization
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.Restriction.CoefficientEquivalence
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.PullbackStalk.CompGerm

/-!
# The limit assertions of Stacks 09YU along an equivalence of coefficient categories

Let `e : A ≌ A'` be an equivalence of coefficient categories and `Ψ` postcomposition with
`e.functor`, from sheaves with values in `A` to sheaves with values in `A'` on the small étale
sites of a big étale site. Inverse image commutes with `Ψ`
(`CategoryTheory.Sheaf.sheafPullbackCoefficientIso`). This file shows that the faithfulness and
fullness assertions of the limit comparison pass from `A'` to `A`, for classes of sheaves `P` on
`A` and `P'` on `A'` with `Ψ` carrying `P` into `P'`.

Fullness involves the canonical comparisons of iterated inverse images, which are not compared
directly: a realization is read on the stage through the adjunctions
(`AlgebraicGeometry.unit_comp_map_smallEtaleStageRealization`) as a factorization through the leg
of sections, and the legs on the two coefficient categories correspond by
`CategoryTheory.Adjunction.unitCharacterized_transport`, whose only inputs are unit equations.

## Main results

* `AlgebraicGeometry.unit_comp_map_coefficientPullbackIso` — the unit equation of the comparison
  of inverse images with `Ψ`.
* `AlgebraicGeometry.smallEtaleStageLeg_coefficient` — the comparison of the legs.
* `AlgebraicGeometry.smallEtaleStagesFaithful_of_coefficientEquivalence` and
  `AlgebraicGeometry.smallEtaleStagesFull_of_coefficientEquivalence` — the transfers.
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits Opposite

universe t v t' v' u iu

namespace AlgebraicGeometry

variable (B : BigEtaleSite.{u}) {A : Type t} [Category.{v} A] {A' : Type t'} [Category.{v'} A']
  [∀ (S T : B.Scheme) (f : T ⟶ S),
    ((smallEtaleBaseChange B f).sheafPushforwardContinuous A
      (SmallEtale.topology B S.obj S.property)
      (SmallEtale.topology B T.obj T.property)).IsRightAdjoint]
  [∀ (S T : B.Scheme) (f : T ⟶ S),
    ((smallEtaleBaseChange B f).sheafPushforwardContinuous A'
      (SmallEtale.topology B S.obj S.property)
      (SmallEtale.topology B T.obj T.property)).IsRightAdjoint]
  (e : A ≌ A')
  [∀ S : B.Scheme, (SmallEtale.topology B S.obj S.property).HasSheafCompose e.functor]
  [∀ S : B.Scheme, (SmallEtale.topology B S.obj S.property).HasSheafCompose e.inverse]

/-- The change of coefficients along `e`, on sheaves on the small étale site of `S`. -/
abbrev coefficientChange (S : B.Scheme) :
    Sheaf (SmallEtale.topology B S.obj S.property) A ⥤
      Sheaf (SmallEtale.topology B S.obj S.property) A' :=
  sheafCompose _ e.functor

/-- **Inverse image commutes with the change of coefficients**, in the direction
`f⁻¹(ΨH) ⟶ Ψ(f⁻¹H)`. -/
abbrev coefficientPullbackIso {S T : B.Scheme} (f : T ⟶ S)
    (H : Sheaf (SmallEtale.topology B S.obj S.property) A) :
    (smallEtaleSheafPullback B A' f).obj ((coefficientChange B e S).obj H) ≅
      (coefficientChange B e T).obj ((smallEtaleSheafPullback B A f).obj H) :=
  ((Sheaf.sheafPullbackCoefficientIso (smallEtaleBaseChange B f)
    (SmallEtale.topology B S.obj S.property) (SmallEtale.topology B T.obj T.property) e).app H).symm

/-- **The unit equation of the comparison of inverse images with the change of coefficients.** -/
theorem unit_comp_map_coefficientPullbackIso {S T : B.Scheme} (f : T ⟶ S)
    (H : Sheaf (SmallEtale.topology B S.obj S.property) A) :
    (smallEtaleSheafAdjunction B A' f).unit.app ((coefficientChange B e S).obj H) ≫
        (smallEtaleSheafPushforward B A' f).map (coefficientPullbackIso B e f H).hom =
      (coefficientChange B e S).map ((smallEtaleSheafAdjunction B A f).unit.app H) ≫ 𝟙 _ := by
  let EJ := Sheaf.coefficientEquivalence (SmallEtale.topology B S.obj S.property) e
  let EK := Sheaf.coefficientEquivalence (SmallEtale.topology B T.obj T.property) e
  let adj1 := (smallEtaleSheafAdjunction B A f).comp EK.toAdjunction
  let adj2 : EJ.functor ⋙ smallEtaleSheafPullback B A' f ⊣
      EK.inverse ⋙ smallEtaleSheafPushforward B A f :=
    (EJ.toAdjunction.comp (smallEtaleSheafAdjunction B A' f)).ofNatIsoRight (Iso.refl _)
  have h2 : adj2.unit.app H = EJ.unit.app H ≫
      EJ.inverse.map ((smallEtaleSheafAdjunction B A' f).unit.app (EJ.functor.obj H)) := by
    have h := Adjunction.homEquiv_ofNatIsoRight_apply
      (EJ.toAdjunction.comp (smallEtaleSheafAdjunction B A' f))
      (Iso.refl (smallEtaleSheafPushforward B A' f ⋙ EJ.inverse))
      (𝟙 ((EJ.functor ⋙ smallEtaleSheafPullback B A' f).obj H))
    rw [Adjunction.homEquiv_id, Adjunction.homEquiv_id] at h
    refine h.trans ?_
    simp [Adjunction.comp_unit_app]
  have hadj1 : adj1.unit.app H = (smallEtaleSheafAdjunction B A f).unit.app H ≫
      (smallEtaleSheafPushforward B A f).map
        (EK.unit.app ((smallEtaleSheafPullback B A f).obj H)) := by
    simp [adj1, Adjunction.comp_unit_app]
  have key := Adjunction.unit_leftAdjointUniq_hom_app adj2 adj1 H
  rw [h2, hadj1] at key
  have hiso : (coefficientPullbackIso B e f H).hom = (adj2.leftAdjointUniq adj1).hom.app H :=
    Adjunction.leftAdjointUniq_inv_app adj1 adj2 H
  rw [hiso, Category.comp_id]
  apply EJ.inverse.map_injective
  refine (Iso.cancel_iso_hom_left (EJ.unitIso.app H) _ _).mp ?_
  have hnat := EJ.unit.naturality ((smallEtaleSheafAdjunction B A f).unit.app H)
  have hu : (smallEtaleSheafPushforward B A f).map
      (EK.unit.app ((smallEtaleSheafPullback B A f).obj H)) =
      EJ.unit.app
        ((smallEtaleSheafPushforward B A f).obj ((smallEtaleSheafPullback B A f).obj H)) := rfl
  refine (congrArg _ (Functor.map_comp _ _ _)).trans ?_
  refine (Category.assoc _ _ _).symm.trans ?_
  refine key.trans ?_
  rw [hu]
  exact hnat

/-- The change of coefficients commutes with direct image on the nose. -/
abbrev coefficientPushforwardHom {S T : B.Scheme} (f : T ⟶ S) :
    smallEtaleSheafPushforward B A f ⋙ coefficientChange B e S ⟶
      coefficientChange B e T ⋙ smallEtaleSheafPushforward B A' f :=
  𝟙 _

omit [∀ S : B.Scheme, (SmallEtale.topology B S.obj S.property).HasSheafCompose e.inverse] in
/-- The comparisons of direct images along a composite are compatible with the change of
coefficients. -/
theorem coefficientChange_pushforwardComp_compat {X Y Z : B.Scheme} (f : X ⟶ Y) (g : Y ⟶ Z)
    (h : X ⟶ Z) (e' : f ≫ g = h) (K : Sheaf (SmallEtale.topology B X.obj X.property) A) :
    (coefficientChange B e Z).map ((smallEtalePushforwardCompHom B A f g h e').app K) ≫
      (coefficientPushforwardHom B e g).app ((smallEtaleSheafPushforward B A f).obj K) ≫
      (smallEtaleSheafPushforward B A' g).map ((coefficientPushforwardHom B e f).app K) =
    (coefficientPushforwardHom B e h).app K ≫
      (smallEtalePushforwardCompHom B A' f g h e').app ((coefficientChange B e X).obj K) := by
  have hc' : (coefficientChange B e Z).map ((smallEtalePushforwardCompHom B A f g h e').app K) =
      (smallEtalePushforwardCompHom B A' f g h e').app ((coefficientChange B e X).obj K) := by
    refine Sheaf.hom_ext (NatTrans.ext (funext fun U => ?_))
    induction U with | op V => ?_
    exact (congrArg e.functor.map
      (AlgebraicGeometry.sheafPushforwardContinuousComp'_inv_app_hom_app B f g h e' A K V)).trans
      (AlgebraicGeometry.sheafPushforwardContinuousComp'_inv_app_hom_app B f g h e' A'
        ((coefficientChange B e X).obj K) V).symm
  have hid : (smallEtaleSheafPushforward B A' g).map ((coefficientPushforwardHom B e f).app K) =
      𝟙 _ := (smallEtaleSheafPushforward B A' g).map_id _
  rw [hid]
  exact ((congrArg (_ ≫ ·) (Category.comp_id _)).trans (Category.comp_id _)).trans
    (hc'.trans (Category.id_comp _).symm)

/-- **The legs of sections before and after the change of coefficients agree.** -/
theorem smallEtaleStageLeg_coefficient {X Y Z : B.Scheme} (f : X ⟶ Y) (g : Y ⟶ Z) (h : X ⟶ Z)
    (e' : f ≫ g = h) (G : Sheaf (SmallEtale.topology B Z.obj Z.property) A) :
    (coefficientPullbackIso B e g G).hom ≫
        (coefficientChange B e Y).map (smallEtaleStageLeg B A f g h e' G) ≫
        (coefficientPushforwardHom B e f).app ((smallEtaleSheafPullback B A h).obj G) =
      smallEtaleStageLeg B A' f g h e' ((coefficientChange B e Z).obj G) ≫
        (smallEtaleSheafPushforward B A' f).map (coefficientPullbackIso B e h G).hom :=
  Adjunction.unitCharacterized_transport (smallEtaleSheafAdjunction B A' g)
    (smallEtaleSheafAdjunction B A' h) (smallEtalePushforwardCompHom B A' f g h e')
    (smallEtaleSheafAdjunction B A g) (smallEtaleSheafAdjunction B A h)
    (smallEtalePushforwardCompHom B A f g h e')
    (coefficientChange B e Z) (coefficientChange B e Y) (coefficientChange B e X)
    (coefficientPushforwardHom B e g) (coefficientPushforwardHom B e h)
    (coefficientPushforwardHom B e f)
    (smallEtaleStageLeg B A' f g h e') (unit_comp_map_smallEtaleStageLeg B A' f g h e')
    (smallEtaleStageLeg B A f g h e') (unit_comp_map_smallEtaleStageLeg B A f g h e')
    (fun H => (coefficientPullbackIso B e g H).hom) (unit_comp_map_coefficientPullbackIso B e g)
    (fun H => (coefficientPullbackIso B e h H).hom) (unit_comp_map_coefficientPullbackIso B e h)
    (coefficientChange_pushforwardComp_compat B e f g h e') G

/-- The comparison of inverse images with the change of coefficients is natural. -/
@[reassoc]
theorem coefficientPullbackIso_hom_naturality {S T : B.Scheme} (f : T ⟶ S)
    {H H' : Sheaf (SmallEtale.topology B S.obj S.property) A} (x : H ⟶ H') :
    (smallEtaleSheafPullback B A' f).map ((coefficientChange B e S).map x) ≫
        (coefficientPullbackIso B e f H').hom =
      (coefficientPullbackIso B e f H).hom ≫
        (coefficientChange B e T).map ((smallEtaleSheafPullback B A f).map x) :=
  ((Sheaf.sheafPullbackCoefficientIso (smallEtaleBaseChange B f)
    (SmallEtale.topology B S.obj S.property) (SmallEtale.topology B T.obj T.property)
      e).inv.naturality x)

omit [∀ (S T : B.Scheme) (f : T ⟶ S),
      ((smallEtaleBaseChange B f).sheafPushforwardContinuous A
        (SmallEtale.topology B S.obj S.property)
        (SmallEtale.topology B T.obj T.property)).IsRightAdjoint]
  [∀ (S T : B.Scheme) (f : T ⟶ S),
      ((smallEtaleBaseChange B f).sheafPushforwardContinuous A'
        (SmallEtale.topology B S.obj S.property)
        (SmallEtale.topology B T.obj T.property)).IsRightAdjoint] in
/-- The change of coefficients is faithful. -/
theorem coefficientChange_map_injective (S : B.Scheme)
    {H H' : Sheaf (SmallEtale.topology B S.obj S.property) A} {x y : H ⟶ H'}
    (h : (coefficientChange B e S).map x = (coefficientChange B e S).map y) : x = y :=
  (Sheaf.coefficientEquivalence (SmallEtale.topology B S.obj S.property) e).functor.map_injective h

omit [∀ (S T : B.Scheme) (f : T ⟶ S),
      ((smallEtaleBaseChange B f).sheafPushforwardContinuous A
        (SmallEtale.topology B S.obj S.property)
        (SmallEtale.topology B T.obj T.property)).IsRightAdjoint]
  [∀ (S T : B.Scheme) (f : T ⟶ S),
      ((smallEtaleBaseChange B f).sheafPushforwardContinuous A'
        (SmallEtale.topology B S.obj S.property)
        (SmallEtale.topology B T.obj T.property)).IsRightAdjoint]
  [∀ S : B.Scheme, (SmallEtale.topology B S.obj S.property).HasSheafCompose e.inverse] in
/-- The change of coefficients commutes with direct image on the nose. -/
theorem coefficientChange_map_pushforward {S T : B.Scheme} (f : T ⟶ S)
    {K K' : Sheaf (SmallEtale.topology B T.obj T.property) A} (x : K ⟶ K') :
    (coefficientChange B e S).map ((smallEtaleSheafPushforward B A f).map x) =
      (smallEtaleSheafPushforward B A' f).map ((coefficientChange B e T).map x) :=
  rfl

/-- The unit equation of `AlgebraicGeometry.unit_comp_map_coefficientPullbackIso`, read as the
image of the unit under the change of coefficients. -/
theorem coefficientChange_map_unit {S T : B.Scheme} (f : T ⟶ S)
    (H : Sheaf (SmallEtale.topology B S.obj S.property) A) :
    (coefficientChange B e S).map ((smallEtaleSheafAdjunction B A f).unit.app H) =
      (smallEtaleSheafAdjunction B A' f).unit.app ((coefficientChange B e S).obj H) ≫
        (smallEtaleSheafPushforward B A' f).map (coefficientPullbackIso B e f H).hom :=
  ((unit_comp_map_coefficientPullbackIso B e f H).trans (Category.comp_id _)).symm

omit [∀ S : B.Scheme, (SmallEtale.topology B S.obj S.property).HasSheafCompose e.inverse] in
/-- The comparison of direct images along a composite, after the change of coefficients. -/
theorem coefficientChange_map_pushforwardCompHom {X Y Z : B.Scheme} (f : X ⟶ Y) (g : Y ⟶ Z)
    (h : X ⟶ Z) (e' : f ≫ g = h) (K : Sheaf (SmallEtale.topology B X.obj X.property) A) :
    (coefficientChange B e Z).map ((smallEtalePushforwardCompHom B A f g h e').app K) =
      (smallEtalePushforwardCompHom B A' f g h e').app ((coefficientChange B e X).obj K) := by
  have := coefficientChange_pushforwardComp_compat B e f g h e' K
  have hid : (smallEtaleSheafPushforward B A' g).map ((coefficientPushforwardHom B e f).app K) =
      𝟙 _ := (smallEtaleSheafPushforward B A' g).map_id _
  rw [hid] at this
  exact ((congrArg (_ ≫ ·) (Category.comp_id _)).trans (Category.comp_id _)).symm.trans
    (this.trans (Category.id_comp _))

/-- The comparison of the legs, without the identity comparison of direct images. -/
theorem smallEtaleStageLeg_coefficient' {X Y Z : B.Scheme} (f : X ⟶ Y) (g : Y ⟶ Z) (h : X ⟶ Z)
    (e' : f ≫ g = h) (G : Sheaf (SmallEtale.topology B Z.obj Z.property) A) :
    (coefficientPullbackIso B e g G).hom ≫
        (coefficientChange B e Y).map (smallEtaleStageLeg B A f g h e' G) =
      smallEtaleStageLeg B A' f g h e' ((coefficientChange B e Z).obj G) ≫
        (smallEtaleSheafPushforward B A' f).map (coefficientPullbackIso B e h G).hom :=
  (congrArg (_ ≫ ·) (Category.comp_id _)).symm.trans (smallEtaleStageLeg_coefficient B e f g h e' G)

variable {I : Type iu} [Preorder I] (Dg : Iᵒᵖ ⥤ B.Scheme) (c : Cone (Dg ⋙ B.inclusion))
  (hX : B.Contains c.pt)

/-- **Faithfulness passes along an equivalence of coefficient categories.** -/
theorem smallEtaleStagesFaithful_of_coefficientEquivalence {P : SmallEtaleSheafProperty B A}
    {P' : SmallEtaleSheafProperty B A'}
    (hPP' : ∀ (X : B.Scheme) (F : Sheaf (SmallEtale.topology B X.obj X.property) A),
      P X F → P' X ((coefficientChange B e X).obj F))
    (h : SmallEtaleStagesFaithful B A' Dg c hX P') :
    SmallEtaleStagesFaithful B A Dg c hX P := by
  intro i F G hF hG a b hab
  have hab' : (smallEtaleStageProjection B A' Dg c hX i).map ((coefficientChange B e _).map a) =
      (smallEtaleStageProjection B A' Dg c hX i).map ((coefficientChange B e _).map b) := by
    rw [← cancel_mono (coefficientPullbackIso B e (coneStageHom B Dg c hX i) G).hom,
      coefficientPullbackIso_hom_naturality, coefficientPullbackIso_hom_naturality]
    exact congrArg (fun z => _ ≫ (coefficientChange B e _).map z) hab
  obtain ⟨j, hij, hj⟩ := h i _ _ (hPP' _ F hF) (hPP' _ G hG) _ _ hab'
  refine ⟨j, hij, coefficientChange_map_injective B e _ ?_⟩
  rw [← cancel_epi (coefficientPullbackIso B e (systemStageHom B Dg hij) F).hom,
    ← coefficientPullbackIso_hom_naturality, ← coefficientPullbackIso_hom_naturality]
  exact congrArg (· ≫ _) hj

/-- **Fullness passes along an equivalence of coefficient categories.** -/
theorem smallEtaleStagesFull_of_coefficientEquivalence {P : SmallEtaleSheafProperty B A}
    {P' : SmallEtaleSheafProperty B A'}
    (hPP' : ∀ (X : B.Scheme) (F : Sheaf (SmallEtale.topology B X.obj X.property) A),
      P X F → P' X ((coefficientChange B e X).obj F))
    (h : SmallEtaleStagesFull B A' Dg c hX P') :
    SmallEtaleStagesFull B A Dg c hX P := by
  intro i F G hF hG a
  let pi := coneStageHom B Dg c hX i
  let a' := (coefficientPullbackIso B e pi F).hom ≫ (coefficientChange B e _).map a ≫
    (coefficientPullbackIso B e pi G).inv
  obtain ⟨j, hij, b', hb'⟩ := h i _ _ (hPP' _ F hF) (hPP' _ G hG) a'
  let g := systemStageHom B Dg hij
  let pj := coneStageHom B Dg c hX j
  let ee := coneStageHom_comp B Dg c hX hij
  let b := (Sheaf.coefficientEquivalence _ e).fullyFaithfulFunctor.preimage
    ((coefficientPullbackIso B e g F).inv ≫ b' ≫ (coefficientPullbackIso B e g G).hom)
  have hb : (coefficientChange B e _).map b =
      (coefficientPullbackIso B e g F).inv ≫ b' ≫ (coefficientPullbackIso B e g G).hom :=
    (Sheaf.coefficientEquivalence _ e).fullyFaithfulFunctor.map_preimage _
  refine ⟨j, hij, b, ?_⟩
  rw [smallEtaleStageComparison_eq, smallEtaleStageComparison_eq] at hb' ⊢
  have hb'' := unit_comp_map_smallEtaleStageRealization B A' pj g pi ee b'
  rw [hb'] at hb''
  apply ((smallEtaleSheafAdjunction B A pi).homEquiv _ _).injective
  rw [Adjunction.homEquiv_unit, Adjunction.homEquiv_unit]
  rw [← cancel_mono ((smallEtalePushforwardCompHom B A pj g pi ee).app
    ((smallEtaleSheafPullback B A pi).obj G)), Category.assoc,
    unit_comp_map_smallEtaleStageRealization B A pj g pi ee b]
  apply coefficientChange_map_injective B e _
  simp only [Functor.map_comp, coefficientChange_map_pushforward, coefficientChange_map_unit,
    coefficientChange_map_pushforwardCompHom, hb, Category.assoc]
  have hL : ((smallEtaleSheafAdjunction B A' g).unit.app ((coefficientChange B e _).obj F) ≫
        (smallEtaleSheafPushforward B A' g).map (coefficientPullbackIso B e g F).hom) ≫
      ((smallEtaleSheafPushforward B A' g).map (coefficientPullbackIso B e g F).inv ≫
        (smallEtaleSheafPushforward B A' g).map b' ≫
        (smallEtaleSheafPushforward B A' g).map (coefficientPullbackIso B e g G).hom) ≫
      (smallEtaleSheafPushforward B A' g).map
        ((coefficientChange B e _).map (smallEtaleStageLeg B A pj g pi ee G)) =
      ((smallEtaleSheafAdjunction B A' g).unit.app ((coefficientChange B e _).obj F) ≫
        (smallEtaleSheafPushforward B A' g).map b') ≫
      (smallEtaleSheafPushforward B A' g).map
        (smallEtaleStageLeg B A' pj g pi ee ((coefficientChange B e _).obj G)) ≫
      (smallEtaleSheafPushforward B A' g).map ((smallEtaleSheafPushforward B A' pj).map
        (coefficientPullbackIso B e pi G).hom) := by
    have hleg := congrArg (smallEtaleSheafPushforward B A' g).map
      (smallEtaleStageLeg_coefficient' B e pj g pi ee G)
    simp only [Functor.map_comp] at hleg
    simp only [Category.assoc]
    rw [← Functor.map_comp_assoc (smallEtaleSheafPushforward B A' g)
      (coefficientPullbackIso B e g F).hom, Iso.hom_inv_id, CategoryTheory.Functor.map_id,
      Category.id_comp, hleg]
    exact congrArg (fun z => (smallEtaleSheafAdjunction B A' g).unit.app
      ((coefficientChange B e _).obj F) ≫ (smallEtaleSheafPushforward B A' g).map b' ≫ z)
      ((smallEtaleSheafPushforward B A' g).map_comp _ _)
  refine hL.trans ?_
  have hcn := (smallEtalePushforwardCompHom B A' pj g pi ee).naturality
    (coefficientPullbackIso B e pi G).hom
  have ha' : (coefficientPullbackIso B e pi F).hom ≫ (coefficientChange B e _).map a =
      a' ≫ (coefficientPullbackIso B e pi G).hom := by
    simp only [Iso.symm_hom, Iso.app_inv, Iso.symm_inv, Iso.app_hom, Category.assoc,
      Iso.hom_inv_id_app, Functor.comp_obj, NatIso.cancel_natIso_inv_left, a']
    exact (Category.comp_id _).symm
  have key : (smallEtaleSheafAdjunction B A' pi).unit.app ((coefficientChange B e _).obj F) ≫
      (smallEtaleSheafPushforward B A' pi).map ((coefficientPullbackIso B e pi F).hom ≫
        (coefficientChange B e _).map a) ≫
      (smallEtalePushforwardCompHom B A' pj g pi ee).app
        ((coefficientChange B e _).obj ((smallEtaleSheafPullback B A pi).obj G)) =
      ((smallEtaleSheafAdjunction B A' pi).unit.app ((coefficientChange B e _).obj F) ≫
        (smallEtaleSheafPushforward B A' pi).map a' ≫
        (smallEtalePushforwardCompHom B A' pj g pi ee).app
          ((smallEtaleSheafPullback B A' pi).obj ((coefficientChange B e _).obj G))) ≫
      (smallEtaleSheafPushforward B A' pj ⋙ smallEtaleSheafPushforward B A' g).map
        (coefficientPullbackIso B e pi G).hom := by
    rw [ha', Functor.map_comp]
    simp only [Category.assoc]
    rw [hcn]
  have key2 := key.trans (congrArg (· ≫ (smallEtaleSheafPushforward B A' pj ⋙
    smallEtaleSheafPushforward B A' g).map (coefficientPullbackIso B e pi G).hom) hb'')
  have k3 := key2.symm
  simp only [Category.assoc, Functor.map_comp, Functor.comp_map] at k3
  exact (Category.assoc _ _ _).trans (k3.trans (Category.assoc _ _ _).symm)

end AlgebraicGeometry
