module

public import StacksFrontier.AlgebraicGeometry.Quot.ComplexesStackCechDescentSpacesEtaleAugmentationCoherent
public import StacksFrontier.AlgebraicGeometry.Spaces.SimplicialSmallEtaleDegreeTransition
public import StacksFrontier.CategoryTheory.Functor.KanExtension.RanBaseChange

/-!
# The 2-morphism identity behind the derived transitions of a pullback along an augmentation

Let `X` be a simplicial algebraic space with an augmentation `a : X ⟶ Z`, `e` the comparison of
`X_{spaces,étale}` with the total site of its strict components, `b = a ∘ e⁻¹`, `g_k` the component
morphisms, `r_k` the realizations of the strict components and `d_k` the inclusions of the degrees.
This file proves
`AlgebraicGeometry.Space.SimplicialSpacesEtaleSite.StrictAugmentationTwoMorphismCoherent`: the
2-morphism `t_φ : g_n ⟶ g_m ∘ f_φ` of Stacks 04IC, with `b` appended and `r_n` prepended, is
the composite of the 2-isomorphisms of Stacks 0DE7 through `a_n` and `a_m ∘ X(φ)`. With
`strictAugmentationTransitionCoherent_of_twoMorphism`
this gives `StrictAugmentationTransitionCoherent` (Stacks 0D7H (4) made explicit).

The proof goes through the *degree transition* `δ_φ : d_n ⟶ d_m ∘ X(φ)` on direct images
(`AlgebraicGeometry.Space.SimplicialSpacesEtaleSite.degreeTransitionOfSquareOp`), the base change
of right Kan extensions along the cross-degree arrows `(φ, pr₁) : (n, V ×_{X_m} X_n) ⟶ (m, V)`:

* `AlgebraicGeometry.RingedToposHom.TwoIso.whiskerLeft_whiskerRight_t_eq_of_degreeTransition`
  reduces the identity, for arbitrary morphisms of ringed topoi, to two identities: `δ` against
  `e ∘ d_k ≅ g_k ∘ r_k` and `t_φ`, and `δ` against `a ∘ d_k ≅ a_k`; the middle step is the
  naturality of `b ∘ e ≅ a`.
* `AlgebraicGeometry.Space.SimplicialSpacesEtaleSite.strictDegreeTwoIso_comp_degreeTransition`
  and `.degreeTransition_comp_augmentationDegreeTwoIso` are those two identities. Every factor is
  a base change of right Kan extensions, a counit, or a restriction, and both are checked after
  the counit of a right Kan extension (`CategoryTheory.ranBaseChange_comp_transition_eq`,
  `CategoryTheory.ranBaseChange_comp_degreeSquare_eq`), where they become identities of arrows of
  `X_{spaces,étale}`. The 2-morphism `t_φ` enters through
  `CategoryTheory.SimplicialSiteSituation.componentPushforwardTransition_app_eq_homEquiv`: it is
  the transpose of the direct-image transition of Stacks 09WF followed by a counit.

Nothing here is registered.

## Implementation notes

Equations between composites whose factors are only definitionally composable (a right Kan
extension read at `c(d_k V)`, against one read at `V`) are assembled in term mode with
`Eq.trans` and `congrArg`, since `rw` checks its motive at the `implicit` transparency.

## References

* [Stacks Project, Tag 0D7H](https://stacks.math.columbia.edu/tag/0D7H)
* [Stacks Project, Tag 0DE7](https://stacks.math.columbia.edu/tag/0DE7)
* [Stacks Project, Tag 04IC](https://stacks.math.columbia.edu/tag/04IC)
* [Stacks Project, Tag 09WF](https://stacks.math.columbia.edu/tag/09WF)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits Opposite

namespace AlgebraicGeometry.RingedToposHom.TwoIso

universe vE uE wE vE' uE' wE' vC uC wC vC' uC' wC' vT uT wT vR uR wR vW uW wW

variable {E : RingedTopos.{vE, uE, wE}} {E' : RingedTopos.{vE', uE', wE'}}
  {C : RingedTopos.{vC, uC, wC}} {C' : RingedTopos.{vC', uC', wC'}}
  {T : RingedTopos.{vT, uT, wT}} {R : RingedTopos.{vR, uR, wR}} {W : RingedTopos.{vW, uW, wW}}
  [E.J.HasSheafCompose (forget RingCat.{wE})] [E'.J.HasSheafCompose (forget RingCat.{wE'})]
  [C.J.HasSheafCompose (forget RingCat.{wC})] [C'.J.HasSheafCompose (forget RingCat.{wC'})]
  [T.J.HasSheafCompose (forget RingCat.{wT})] [R.J.HasSheafCompose (forget RingCat.{wR})]
  [W.J.HasSheafCompose (forget RingCat.{wW})]
  [E.J.HasSheafCompose (forget₂ CommRingCat.{wE} RingCat.{wE})]
  [E'.J.HasSheafCompose (forget₂ CommRingCat.{wE'} RingCat.{wE'})]
  [C.J.HasSheafCompose (forget₂ CommRingCat.{wC} RingCat.{wC})]
  [C'.J.HasSheafCompose (forget₂ CommRingCat.{wC'} RingCat.{wC'})]
  [T.J.HasSheafCompose (forget₂ CommRingCat.{wT} RingCat.{wT})]
  [R.J.HasSheafCompose (forget₂ CommRingCat.{wR} RingCat.{wR})]
  [W.J.HasSheafCompose (forget₂ CommRingCat.{wW} RingCat.{wW})]

attribute [local implicit_reducible] AlgebraicGeometry.RingedToposHom.comp MorphismOfTopoi.comp

/-- **The 2-morphism identity from a degree transition.** For morphisms of ringed topoi with
`sD : e ∘ d ≅ g ∘ r`, `sA : b ∘ e ≅ a`, `aD : a ∘ d ≅ a_n` (and their degree-`m` versions),
`τ : f ∘ r ≅ r' ∘ x`, `κ : a_m ∘ x ≅ a_n` and a 2-morphism `t : g ⟶ g' ∘ f`, the whiskered
`b t r` is the composite of the 2-isomorphisms through `a_n` as soon as some transition
`δ : d_* ⟶ x_* ⋙ d'_*` is compatible with `t` through `sD`, `sD'` and with `aD`, `aD'`, `κ`. -/
theorem whiskerLeft_whiskerRight_t_eq_of_degreeTransition
    {r : RingedToposHom E C} {r' : RingedToposHom E' C'} {f : RingedToposHom C C'}
    {x : RingedToposHom E E'} {g : RingedToposHom C T} {g' : RingedToposHom C' T}
    {b : RingedToposHom T W} {e : RingedToposHom R T} {d : RingedToposHom E R}
    {d' : RingedToposHom E' R} {a : RingedToposHom R W} {an : RingedToposHom E W}
    {am : RingedToposHom E' W}
    (t : TwoMorphism g (g'.comp f)) (sD : TwoIso (e.comp d) (g.comp r))
    (sD' : TwoIso (e.comp d') (g'.comp r')) (sA : TwoIso (b.comp e) a)
    (aD : TwoIso (a.comp d) an) (aD' : TwoIso (a.comp d') am)
    (τ : TwoIso (f.comp r) (r'.comp x)) (κ : TwoIso (am.comp x) an)
    (δ : d.toToposHom.pushforward ⟶ x.toToposHom.pushforward ⋙ d'.toToposHom.pushforward)
    (hI : sD.e.hom ≫ Functor.whiskerLeft r.toToposHom.pushforward t.t ≫
        (Functor.associator r.toToposHom.pushforward f.toToposHom.pushforward
          g'.toToposHom.pushforward).inv ≫
        Functor.whiskerRight τ.e.hom g'.toToposHom.pushforward ≫
        (Functor.associator x.toToposHom.pushforward r'.toToposHom.pushforward
          g'.toToposHom.pushforward).hom =
      Functor.whiskerRight δ e.toToposHom.pushforward ≫
        (Functor.associator x.toToposHom.pushforward d'.toToposHom.pushforward
          e.toToposHom.pushforward).hom ≫
        Functor.whiskerLeft x.toToposHom.pushforward sD'.e.hom)
    (hII : Functor.whiskerRight δ a.toToposHom.pushforward ≫
        (Functor.associator x.toToposHom.pushforward d'.toToposHom.pushforward
          a.toToposHom.pushforward).hom ≫
        Functor.whiskerLeft x.toToposHom.pushforward aD'.e.hom ≫ κ.e.hom = aD.e.hom) :
    Functor.whiskerLeft r.toToposHom.pushforward (t.whiskerRight b).t =
      ((associator r g b).symm.trans ((degreeAugmentationTwoIso sD sA aD).trans
        (realizedTransitionTwoIso τ (degreeAugmentationTwoIso sD' sA aD') κ).symm)).e.hom := by
  have key : Functor.whiskerLeft r.toToposHom.pushforward (t.whiskerRight b).t ≫
      (realizedTransitionTwoIso τ (degreeAugmentationTwoIso sD' sA aD') κ).e.hom =
      (associator r g b).e.inv ≫ (degreeAugmentationTwoIso sD sA aD).e.hom := by
    ext M : 2
    have hI' := NatTrans.congr_app hI M
    have hII' := NatTrans.congr_app hII M
    have hA := sA.e.hom.naturality (δ.app M)
    dsimp only [NatTrans.comp_app, Functor.whiskerLeft_app, Functor.whiskerRight_app,
      Functor.associator_hom_app, Functor.associator_inv_app, Functor.comp_map,
      RingedToposHom.comp, MorphismOfTopoi.comp, Functor.comp_obj]
      at hI' hII' hA
    dsimp only [realizedTransitionTwoIso, degreeAugmentationTwoIso, TwoIso.trans, TwoIso.symm,
      TwoIso.whiskerRight, TwoIso.whiskerLeft, TwoIso.associator, TwoMorphism.whiskerRight_t,
      Iso.trans_hom, Iso.trans_inv, Iso.symm_hom, Iso.symm_inv, NatTrans.comp_app,
      Functor.isoWhiskerRight_hom, Functor.isoWhiskerRight_inv, Functor.isoWhiskerLeft_hom,
      Functor.isoWhiskerLeft_inv, Functor.whiskerRight_app, Functor.whiskerLeft_app,
      Functor.associator_hom_app, Functor.associator_inv_app, Functor.comp_obj,
      RingedToposHom.comp, MorphismOfTopoi.comp, Functor.comp_map]
    simp only [Category.id_comp, Category.comp_id, CategoryTheory.Functor.map_id,
      Category.assoc] at hI' hII' ⊢
    have hA' : b.toToposHom.pushforward.map (e.toToposHom.pushforward.map (δ.app M)) ≫
        sA.e.hom.app (d'.toToposHom.pushforward.obj (x.toToposHom.pushforward.obj M)) =
        sA.e.hom.app (d.toToposHom.pushforward.obj M) ≫ a.toToposHom.pushforward.map (δ.app M) :=
      sA.e.hom.naturality (δ.app M)
    have h1 : t.t.app (r.toToposHom.pushforward.obj M) ≫
        g'.toToposHom.pushforward.map (τ.e.hom.app M) ≫
          sD'.e.inv.app (x.toToposHom.pushforward.obj M) =
        sD.e.inv.app M ≫ e.toToposHom.pushforward.map (δ.app M) := by
      rw [← cancel_epi (sD.e.hom.app M), Iso.hom_inv_id_app_assoc, reassoc_of% hI',
        Iso.hom_inv_id_app]
      exact Category.comp_id _
    rw [← CategoryTheory.Functor.map_comp_assoc, ← CategoryTheory.Functor.map_comp_assoc,
      Category.assoc, h1,
      CategoryTheory.Functor.map_comp_assoc, reassoc_of% hA', hII']
  show _ = (associator r g b).e.inv ≫ (degreeAugmentationTwoIso sD sA aD).e.hom ≫
    (realizedTransitionTwoIso τ (degreeAugmentationTwoIso sD' sA aD') κ).e.inv
  rw [← Category.assoc, ← key, Category.assoc, Iso.hom_inv_id, Category.comp_id]

end AlgebraicGeometry.RingedToposHom.TwoIso

namespace CategoryTheory

open _root_.CategoryTheory.Functor

section Pasting

variable {A : Type*} [Category* A] {Cm Cn T Xm Xn R : Type*} [Category* Cm] [Category* Cn]
  [Category* T] [Category* Xm] [Category* Xn] [Category* R]
  {ιm : Cm ⥤ T} {ιn : Cn ⥤ T} {u : Cm ⥤ Cn} {rm : Cm ⥤ Xm} {rn : Cn ⥤ Xn} {E : T ⥤ R}
  {δm : Xm ⥤ R} {δn : Xn ⥤ R} {β : Xm ⥤ Xn}
  [∀ F : Cmᵒᵖ ⥤ A, ιm.op.HasRightKanExtension F] [∀ F : Cnᵒᵖ ⥤ A, ιn.op.HasRightKanExtension F]
  [∀ F : Xmᵒᵖ ⥤ A, δm.op.HasRightKanExtension F] [∀ F : Xnᵒᵖ ⥤ A, δn.op.HasRightKanExtension F]

/-- The base change of right Kan extensions along `(δm, β, wβ)`, against an arrow `k` of the base
and the counit of `δm`. -/
private theorem ranBaseChange_mk_naturality_comp_ranCounit (wβ : β ⋙ δn ⟶ δm) (P : Xnᵒᵖ ⥤ A)
    {y : R} {z : Xm} (k : δm.obj z ⟶ y) :
    ((TwoSquare.mk δm.op β.op (𝟭 _) δn.op (NatTrans.op wβ)).ranBaseChange.app P).app (op y) ≫
        (δm.op.ran.obj (β.op ⋙ P)).map k.op ≫ (δm.op.ranCounit.app (β.op ⋙ P)).app (op z) =
      (δn.op.ran.obj P).map k.op ≫ (δn.op.ran.obj P).map (wβ.app z).op ≫
        (δn.op.ranCounit.app P).app (op (β.obj z)) := by
  have h := ((TwoSquare.mk δm.op β.op (𝟭 _) δn.op (NatTrans.op wβ)).ranBaseChange.app P).naturality
    k.op
  exact ((reassoc_of% h) _).symm.trans (congrArg _ (TwoSquare.ranBaseChange_app_app_ranCounit
    (TwoSquare.mk δm.op β.op (𝟭 _) δn.op (NatTrans.op wβ)) P (op z)))

/-- **Pasting a transition against two base changes of right Kan extensions.** -/
theorem ranBaseChange_comp_transition_eq (wm : TwoSquare rm ιm δm E) (wn : TwoSquare rn ιn δn E)
    (w' : u ⋙ ιn ⟶ ιm) (wβ : β ⋙ δn ⟶ δm) (ρ' : rm ⋙ β ⟶ u ⋙ rn) (P : Xnᵒᵖ ⥤ A)
    (tP : ιn.op.ran.obj (rn.op ⋙ P) ⟶ ιm.op.ran.obj (u.op ⋙ rn.op ⋙ P))
    (ht : tP = (ιm.op.ranAdjunction A).homEquiv _ _
      (Functor.whiskerRight (NatTrans.op w') (ιn.op.ran.obj (rn.op ⋙ P)) ≫
        Functor.whiskerLeft u.op ((ιn.op.ranAdjunction A).counit.app (rn.op ⋙ P))))
    (τP : u.op ⋙ rn.op ⋙ P ⟶ rm.op ⋙ β.op ⋙ P)
    (hτ : ∀ V, τP.app V = P.map (ρ'.app V.unop).op)
    (hsite : ∀ V : Cm, δn.map (ρ'.app V) ≫ wn.app (u.obj V) ≫ E.map (w'.app V) =
      wβ.app (rm.obj V) ≫ wm.app V) :
    wn.op.ranBaseChange.app P ≫ tP ≫ ιm.op.ran.map τP =
      Functor.whiskerLeft E.op
          ((TwoSquare.mk δm.op β.op (𝟭 _) δn.op (NatTrans.op wβ)).ranBaseChange.app P) ≫
        wm.op.ranBaseChange.app (β.op ⋙ P) := by
  refine Functor.hom_ext_of_isRightKanExtension _ (ιm.op.ranCounit.app (rm.op ⋙ β.op ⋙ P)) _ _ ?_
  ext V
  have h1 : tP.app (op (ιm.obj V.unop)) ≫ (ιm.op.ranCounit.app (u.op ⋙ rn.op ⋙ P)).app V =
      (ιn.op.ran.obj (rn.op ⋙ P)).map (w'.app V.unop).op ≫
        (ιn.op.ranCounit.app (rn.op ⋙ P)).app (op (u.obj V.unop)) := by
    have h : ((ιm.op.ranAdjunction A).homEquiv _ _).symm tP =
        Functor.whiskerRight (NatTrans.op w') (ιn.op.ran.obj (rn.op ⋙ P)) ≫
          Functor.whiskerLeft u.op ((ιn.op.ranAdjunction A).counit.app (rn.op ⋙ P)) := by
      rw [ht]
      exact Equiv.symm_apply_apply _ _
    simp only [Adjunction.homEquiv_counit, ranAdjunction_counit] at h
    have h' := NatTrans.congr_app h V
    simpa using h'
  have h2 : (wn.op.ranBaseChange.app P).app (op (ιn.obj (u.obj V.unop))) ≫
      (ιn.op.ranCounit.app (rn.op ⋙ P)).app (op (u.obj V.unop)) =
      (δn.op.ran.obj P).map (wn.app (u.obj V.unop)).op ≫
        (δn.op.ranCounit.app P).app (op (rn.obj (u.obj V.unop))) :=
    TwoSquare.ranBaseChange_app_app_ranCounit wn.op P (op (u.obj V.unop))
  have h3 : (δn.op.ran.obj P).map (E.map (w'.app V.unop)).op ≫
      (wn.op.ranBaseChange.app P).app (op (ιn.obj (u.obj V.unop))) =
      (wn.op.ranBaseChange.app P).app (op (ιm.obj V.unop)) ≫
        (ιn.op.ran.obj (rn.op ⋙ P)).map (w'.app V.unop).op :=
    (wn.op.ranBaseChange.app P).naturality (w'.app V.unop).op
  have h4 : (δn.op.ran.obj P).map (δn.map (ρ'.app V.unop)).op ≫
      (δn.op.ranCounit.app P).app (op (β.obj (rm.obj V.unop))) =
      (δn.op.ranCounit.app P).app (op (rn.obj (u.obj V.unop))) ≫ P.map (ρ'.app V.unop).op :=
    (δn.op.ranCounit.app P).naturality (ρ'.app V.unop).op
  have h5 : (wm.op.ranBaseChange.app (β.op ⋙ P)).app (op (ιm.obj V.unop)) ≫
      (ιm.op.ranCounit.app (rm.op ⋙ β.op ⋙ P)).app V =
      (δm.op.ran.obj (β.op ⋙ P)).map (wm.app V.unop).op ≫
        (δm.op.ranCounit.app (β.op ⋙ P)).app (op (rm.obj V.unop)) :=
    TwoSquare.ranBaseChange_app_app_ranCounit wm.op (β.op ⋙ P) V
  have h8 : (ιm.op.ran.map τP).app (op (ιm.obj V.unop)) ≫
      (ιm.op.ranCounit.app (rm.op ⋙ β.op ⋙ P)).app V =
      (ιm.op.ranCounit.app (u.op ⋙ rn.op ⋙ P)).app V ≫ τP.app V :=
    AlgebraicGeometry.Space.SimplicialSpacesEtaleSite.ran_map_app_ranCounit_app ιm.op τP V
  have hs := congrArg Quiver.Hom.op (hsite V.unop)
  simp only [op_comp, Category.assoc] at hs
  simp only [NatTrans.comp_app, Functor.whiskerLeft_app, Category.assoc]
  dsimp only [Functor.op_obj]
  rw [h8, reassoc_of% h1, ← reassoc_of% h3, reassoc_of% h2, hτ, ← h4, h5,
    ranBaseChange_mk_naturality_comp_ranCounit wβ P (y := E.obj (ιm.obj V.unop))
      (wm.app V.unop)]
  simp only [← Functor.map_comp_assoc]
  rw [hs]

omit [∀ F : Cmᵒᵖ ⥤ A, ιm.op.HasRightKanExtension F]
  [∀ F : Cnᵒᵖ ⥤ A, ιn.op.HasRightKanExtension F] in
/-- **Pasting the degree transition against two degree squares of base change**, read at an
object of the base. -/
theorem ranBaseChange_comp_degreeSquare_eq {R' Z : Type*} [Category* R'] [Category* Z]
    {Pa : R' ⥤ R} {δZm δZn : Z ⥤ R'} {dPm : Z ⥤ Xm} {dPn : Z ⥤ Xn} {βm : Z ⥤ Xm} {βn : Z ⥤ Xn}
    [∀ F : Zᵒᵖ ⥤ A, δZm.op.HasRightKanExtension F] [∀ F : Zᵒᵖ ⥤ A, δZn.op.HasRightKanExtension F]
    (dsqm : TwoSquare dPm δZm δm Pa) (dsqn : TwoSquare dPn δZn δn Pa) (wβ : β ⋙ δn ⟶ δm)
    (im : βm ⟶ dPm) (iN : βn ⟶ dPn) (q : βn ⟶ βm ⋙ β) (P : Xnᵒᵖ ⥤ A) (V : Z)
    (ψ : δZn.obj V ⟶ δZm.obj V)
    (hsite : δn.map (q.app V) ≫ δn.map (β.map (im.app V)) ≫ wβ.app (dPm.obj V) ≫ dsqm.app V =
      δn.map (iN.app V) ≫ dsqn.app V ≫ Pa.map ψ) :
    ((TwoSquare.mk δm.op β.op (𝟭 _) δn.op (NatTrans.op wβ)).ranBaseChange.app P).app
        (op (Pa.obj (δZm.obj V))) ≫
      (dsqm.op.ranBaseChange.app (β.op ⋙ P)).app (op (δZm.obj V)) ≫
      (δZm.op.ran.map (Functor.whiskerRight (NatTrans.op im) (β.op ⋙ P))).app (op (δZm.obj V)) ≫
      (δZm.op.ranCounit.app (βm.op ⋙ β.op ⋙ P)).app (op V) ≫ P.map (q.app V).op =
    (δn.op.ran.obj P).map (Pa.map ψ).op ≫ (dsqn.op.ranBaseChange.app P).app (op (δZn.obj V)) ≫
      (δZn.op.ran.map (Functor.whiskerRight (NatTrans.op iN) P)).app (op (δZn.obj V)) ≫
      (δZn.op.ranCounit.app (βn.op ⋙ P)).app (op V) := by
  have g1 : (δZm.op.ran.map (Functor.whiskerRight (NatTrans.op im) (β.op ⋙ P))).app
        (op (δZm.obj V)) ≫ (δZm.op.ranCounit.app (βm.op ⋙ β.op ⋙ P)).app (op V) =
      (δZm.op.ranCounit.app (dPm.op ⋙ β.op ⋙ P)).app (op V) ≫
        P.map (β.map (im.app V)).op :=
    AlgebraicGeometry.Space.SimplicialSpacesEtaleSite.ran_map_app_ranCounit_app δZm.op _ (op V)
  have g2 : (dsqm.op.ranBaseChange.app (β.op ⋙ P)).app (op (δZm.obj V)) ≫
      (δZm.op.ranCounit.app (dPm.op ⋙ β.op ⋙ P)).app (op V) =
      (δm.op.ran.obj (β.op ⋙ P)).map (dsqm.app V).op ≫
        (δm.op.ranCounit.app (β.op ⋙ P)).app (op (dPm.obj V)) :=
    TwoSquare.ranBaseChange_app_app_ranCounit dsqm.op (β.op ⋙ P) (op V)
  have g5 : (δn.op.ran.obj P).map (δn.map (β.map (im.app V))).op ≫
      (δn.op.ranCounit.app P).app (op (β.obj (βm.obj V))) =
      (δn.op.ranCounit.app P).app (op (β.obj (dPm.obj V))) ≫ P.map (β.map (im.app V)).op :=
    (δn.op.ranCounit.app P).naturality (β.map (im.app V)).op
  have g6 : (δn.op.ran.obj P).map (δn.map (q.app V)).op ≫
      (δn.op.ranCounit.app P).app (op (βn.obj V)) =
      (δn.op.ranCounit.app P).app (op (β.obj (βm.obj V))) ≫ P.map (q.app V).op :=
    (δn.op.ranCounit.app P).naturality (q.app V).op
  have h1 : (δZn.op.ran.map (Functor.whiskerRight (NatTrans.op iN) P)).app (op (δZn.obj V)) ≫
      (δZn.op.ranCounit.app (βn.op ⋙ P)).app (op V) =
      (δZn.op.ranCounit.app (dPn.op ⋙ P)).app (op V) ≫ P.map (iN.app V).op :=
    AlgebraicGeometry.Space.SimplicialSpacesEtaleSite.ran_map_app_ranCounit_app δZn.op _ (op V)
  have h2 : (dsqn.op.ranBaseChange.app P).app (op (δZn.obj V)) ≫
      (δZn.op.ranCounit.app (dPn.op ⋙ P)).app (op V) =
      (δn.op.ran.obj P).map (dsqn.app V).op ≫ (δn.op.ranCounit.app P).app (op (dPn.obj V)) :=
    TwoSquare.ranBaseChange_app_app_ranCounit dsqn.op P (op V)
  have h5 : (δn.op.ran.obj P).map (δn.map (iN.app V)).op ≫
      (δn.op.ranCounit.app P).app (op (βn.obj V)) =
      (δn.op.ranCounit.app P).app (op (dPn.obj V)) ≫ P.map (iN.app V).op :=
    (δn.op.ranCounit.app P).naturality (iN.app V).op
  have hs := congrArg Quiver.Hom.op hsite
  simp only [op_comp, Category.assoc] at hs
  have hR : (δn.op.ran.obj P).map (Pa.map ψ).op ≫
      (dsqn.op.ranBaseChange.app P).app (op (δZn.obj V)) ≫
      (δZn.op.ran.map (Functor.whiskerRight (NatTrans.op iN) P)).app (op (δZn.obj V)) ≫
      (δZn.op.ranCounit.app (βn.op ⋙ P)).app (op V) =
      (δn.op.ran.obj P).map (Pa.map ψ).op ≫ (δn.op.ran.obj P).map (dsqn.app V).op ≫
        (δn.op.ran.obj P).map (δn.map (iN.app V)).op ≫
          (δn.op.ranCounit.app P).app (op (βn.obj V)) :=
    congrArg (_ ≫ ·) ((congrArg (_ ≫ ·) h1).trans ((Category.assoc _ _ _).symm.trans
      ((congrArg (· ≫ _) h2).trans ((Category.assoc _ _ _).trans (congrArg (_ ≫ ·) h5.symm)))))
  have hM : (δn.op.ran.obj P).map (dsqm.app V).op ≫ (δn.op.ran.obj P).map (wβ.app (dPm.obj V)).op ≫
      (δn.op.ran.obj P).map (δn.map (β.map (im.app V))).op ≫
        (δn.op.ran.obj P).map (δn.map (q.app V)).op ≫
          (δn.op.ranCounit.app P).app (op (βn.obj V)) =
      (δn.op.ran.obj P).map (Pa.map ψ).op ≫ (δn.op.ran.obj P).map (dsqn.app V).op ≫
        (δn.op.ran.obj P).map (δn.map (iN.app V)).op ≫
          (δn.op.ranCounit.app P).app (op (βn.obj V)) := by
    have h := congrArg (fun k => (δn.op.ran.obj P).map k ≫
      (δn.op.ranCounit.app P).app (op (βn.obj V))) hs
    simpa only [Functor.map_comp, Category.assoc] using h
  refine Eq.trans ?_ (hM.trans hR.symm)
  rw [reassoc_of% g1, reassoc_of% g2,
    reassoc_of% (ranBaseChange_mk_naturality_comp_ranCounit wβ P (dsqm.app V)),
    ← reassoc_of% g5, ← g6]

omit [∀ F : Cmᵒᵖ ⥤ A, ιm.op.HasRightKanExtension F]
  [∀ F : Cnᵒᵖ ⥤ A, ιn.op.HasRightKanExtension F]
  [∀ F : Xmᵒᵖ ⥤ A, δm.op.HasRightKanExtension F] [∀ F : Xnᵒᵖ ⥤ A, δn.op.HasRightKanExtension F] in
/-- Moving two counit projections to the front of a composite. -/
theorem comp_comp_comp_eq_of_ranCounitProjections {X₀ X₁ X₂ X₃ X₄ Y₀ Y₁ Y₁' Y₂ : A}
    {f : X₀ ⟶ X₁} {g : X₁ ⟶ X₂}
    {k : X₂ ⟶ X₃} {l : X₃ ⟶ X₄} {π : X₀ ⟶ Y₀} {π₂ : X₁ ⟶ Y₁} {πm : X₂ ⟶ Y₂} {a : Y₀ ⟶ Y₁}
    {b₁ : Y₁ ⟶ Y₁'} {b₂ : Y₁' ⟶ Y₂} {c : Y₂ ⟶ X₃} (hk : k = πm ≫ c) (h₁ : g ≫ πm = π₂ ≫ b₁ ≫ b₂)
    (h₂ : f ≫ π₂ = π ≫ a) : f ≫ ((g ≫ k) ≫ l) = π ≫ a ≫ b₁ ≫ b₂ ≫ c ≫ l := by
  rw [hk]
  simp only [Category.assoc]
  rw [reassoc_of% h₁, reassoc_of% h₂]

omit [∀ F : Cmᵒᵖ ⥤ A, ιm.op.HasRightKanExtension F]
  [∀ F : Cnᵒᵖ ⥤ A, ιn.op.HasRightKanExtension F]
  [∀ F : Xmᵒᵖ ⥤ A, δm.op.HasRightKanExtension F] [∀ F : Xnᵒᵖ ⥤ A, δn.op.HasRightKanExtension F] in
/-- Moving a counit projection to the front of a composite, through a change of projection. -/
theorem comp_eq_of_ranCounitProjections {X₀ X₁ X₂ Y₀ Y₁ Y₁' W : A} {f : X₀ ⟶ X₁}
    {k : X₁ ⟶ X₂} {πn' : X₁ ⟶ Y₁}
    {c : Y₁ ⟶ X₂} {πn : X₀ ⟶ Y₀} {d₁ : Y₀ ⟶ Y₁'} {d₂ : Y₁' ⟶ Y₁} {π : X₀ ⟶ W} {q : W ⟶ Y₀}
    (hk : k = πn' ≫ c) (h₃ : f ≫ πn' = πn ≫ d₁ ≫ d₂) (hψ : πn = π ≫ q) :
    f ≫ k = π ≫ q ≫ d₁ ≫ d₂ ≫ c := by
  rw [hk, reassoc_of% h₃, hψ]
  simp only [Category.assoc]

end Pasting

end CategoryTheory

namespace CategoryTheory.SimplicialSiteSituation

universe u

variable (S : SimplicialSiteSituation.{u})

/-- **The 2-morphism `g_n ⟶ g_m ∘ f_φ` through restriction.** The component of
`componentPushforwardTransition` at `G` is the transpose, along restriction against right Kan
extension in degree `m`, of the direct-image transition of Stacks 09WF at `g_{n,*}G` followed by
the counit in degree `n`. -/
theorem componentPushforwardTransition_app_eq_homEquiv {m n : SimplexCategory} (φ : m ⟶ n)
    (G : Sheaf (S.componentTopology n) (Type u)) :
    (S.componentPushforwardTransition φ).app G =
      ((componentFunctor S m).sheafAdjunctionCocontinuous (Type u) (S.componentTopology m)
          S.totalTopology).homEquiv _ _
        ((S.restrictTransition φ).app ((componentMorphism S n).pushforward.obj G) ≫
          (S.transitionMorphism φ).pushforward.map
            (((componentFunctor S n).sheafAdjunctionCocontinuous (Type u) (S.componentTopology n)
              S.totalTopology).counit.app G)) := by
  have h := Stacks.CategoryTheory.homEquiv_conjugate' (componentMorphism S n).adj
    ((componentMorphism S m).comp (S.transitionMorphism φ)).adj
    (S.componentInverseImageTransition φ) ((componentMorphism S n).adj.counit.app G)
  have hc : (componentMorphism S n).adj.homEquiv _ _ ((componentMorphism S n).adj.counit.app G) =
      𝟙 _ := by
    rw [Adjunction.homEquiv_unit]
    exact (componentMorphism S n).adj.right_triangle_components G
  rw [hc, Category.id_comp] at h
  simp only [Functor.id_obj] at h
  rw [show S.componentPushforwardTransition φ = conjugateEquiv (componentMorphism S n).adj
    ((componentMorphism S m).comp (S.transitionMorphism φ)).adj
    (S.componentInverseImageTransition φ) from rfl, ← h]
  have hα : (S.componentInverseImageTransition φ).app ((componentMorphism S n).pushforward.obj G) =
      (S.transitionMorphism φ).inverseImage.map
        ((S.componentRingedTopos_setRestrictionIso m).hom.app
          ((componentMorphism S n).pushforward.obj G)) ≫
        (S.fiberTransition φ).app ((componentMorphism S n).pushforward.obj G) ≫
          (S.componentRingedTopos_setRestrictionIso n).inv.app
            ((componentMorphism S n).pushforward.obj G) := rfl
  have hn : (S.componentRingedTopos_setRestrictionIso n).inv.app
        ((componentMorphism S n).pushforward.obj G) ≫ (componentMorphism S n).adj.counit.app G =
      ((componentFunctor S n).sheafAdjunctionCocontinuous (Type u) (S.componentTopology n)
        S.totalTopology).counit.app G :=
    Adjunction.leftAdjointUniq_hom_app_counit _ _ G
  have hm : ∀ {Y : Sheaf (S.componentTopology m) (Type u)}
      (k : ((componentFunctor S m).sheafPushforwardContinuous (Type u) (S.componentTopology m)
        S.totalTopology).obj ((componentMorphism S n).pushforward.obj G) ⟶ Y),
      (componentMorphism S m).adj.homEquiv ((componentMorphism S n).pushforward.obj G) Y
        ((S.componentRingedTopos_setRestrictionIso m).hom.app
          ((componentMorphism S n).pushforward.obj G) ≫ k) =
      ((componentFunctor S m).sheafAdjunctionCocontinuous (Type u) (S.componentTopology m)
        S.totalTopology).homEquiv _ Y k := by
    intro Y k
    rw [Adjunction.homEquiv_naturality_right]
    refine (congrArg (· ≫ _) (Adjunction.homEquiv_leftAdjointUniq_hom_app _ _ _)).trans ?_
    exact (Adjunction.homEquiv_unit _ _ _ _).symm
  refine (Adjunction.comp_homEquiv_apply (componentMorphism S m).adj
    (S.transitionMorphism φ).adj _).trans ?_
  rw [hα]
  refine (congrArg ((componentMorphism S m).adj.homEquiv _ _) ?_).trans (hm _)
  exact (congrArg ((S.transitionMorphism φ).adj.homEquiv _ _)
      ((Category.assoc _ _ _).trans (congrArg (_ ≫ ·) (Category.assoc _ _ _)))).trans
    ((Adjunction.homEquiv_naturality_left _ _ _).trans (congrArg (_ ≫ ·)
      ((Adjunction.homEquiv_naturality_right _ _ _).trans
        (congrArg₂ (· ≫ ·) (S.fiberTransition_adj φ _)
          (congrArg (S.transitionMorphism φ).pushforward.map hn)))))

/-- The direct image along the component morphism of ringed topoi is right Kan extension, on
underlying presheaves. -/
theorem componentRingedToposHom_pushforward_map_hom (O : Sheaf S.totalTopology CommRingCat.{u})
    (k : SimplexCategory) {F G : Sheaf (S.componentTopology k) (Type u)} (h : F ⟶ G) :
    ((S.componentRingedToposHom O k).toToposHom.pushforward.map h).hom =
      (componentFunctor S k).op.ran.map h.hom :=
  rfl

/-- `componentRingedTwoMorphism` on underlying presheaves, in case (A): the transpose, along right
Kan extension in degree `m`, of the cross-fibre arrows `(φ, 𝟙)` followed by the counit in degree
`n`. -/
theorem componentRingedTwoMorphism_t_app_hom (C : SimplicialSite.{u})
    (O : Sheaf C.situation.totalTopology CommRingCat.{u}) {m n : SimplexCategory} (φ : m ⟶ n)
    (G : Sheaf (C.situation.componentTopology n) (Type u)) :
    ((C.situation.componentRingedTwoMorphism O φ).t.app G).hom =
      ((componentFunctor C.situation m).op.ranAdjunction (Type u)).homEquiv _ _
        (Functor.whiskerRight (NatTrans.op (continuousInclusionTransition C φ))
            ((componentFunctor C.situation n).op.ran.obj G.obj) ≫
          Functor.whiskerLeft (C.underlying.map φ).toFunctor.op
            (((componentFunctor C.situation n).op.ranAdjunction (Type u)).counit.app G.obj)) := by
  rw [show (C.situation.componentRingedTwoMorphism O φ).t =
      C.situation.componentPushforwardTransition φ from rfl,
    componentPushforwardTransition_app_eq_homEquiv,
    Functor.sheafAdjunctionCocontinuous_homEquiv_apply_hom]
  refine congrArg _ ((ObjectProperty.FullSubcategory.comp_hom _ _ _).trans ?_)
  exact congrArg₂ (· ≫ ·) rfl (congrArg (Functor.whiskerLeft (C.underlying.map φ).toFunctor.op)
    (Functor.sheafAdjunctionCocontinuous_counit_app_hom _ _ _ _ G))

end CategoryTheory.SimplicialSiteSituation


namespace AlgebraicGeometry.Space.SimplicialSpacesEtaleSite

universe u

variable {B : BigFppfSite.{u}} {S : Scheme.{u}} {hS : B.Contains S}
  {X : SimplicialObject (AlgebraicSpaces B S hS)}

attribute [local implicit_reducible] AlgebraicGeometry.RingedToposHom.comp MorphismOfTopoi.comp

/-- The cross-degree arrows `(φ, pr₁) : (n, V ×_{X_m} X_n) ⟶ (m, V)` of `X_{spaces,étale}`. -/
def degreeTransitionNatTrans {m n : SimplexCategory} (φ : m ⟶ n) :
    (spacesBaseChange B S hS (X.map φ.op)).functor ⋙ degreeInclusion X n ⟶
      degreeInclusion X m where
  app V := ⟨φ, (spacesBaseChange B S hS (X.map φ.op)).projection.app V,
    ((spacesBaseChange B S hS (X.map φ.op)).isPullback V).w⟩
  naturality _V _W g := Hom.ext ((Category.comp_id φ).trans (Category.id_comp φ).symm)
    ((spacesBaseChange B S hS (X.map φ.op)).projection.naturality g)

/-- The square of right Kan extensions behind the degree transition. -/
abbrev degreeTransitionSquareOp {m n : SimplexCategory} (φ : m ⟶ n) :
    TwoSquare (degreeInclusion X m).op (spacesBaseChange B S hS (X.map φ.op)).functor.op
      (𝟭 _) (degreeInclusion X n).op :=
  TwoSquare.mk _ _ _ _ (NatTrans.op (degreeTransitionNatTrans φ))

/-- **The degree transition** `d_n ⟶ d_m ∘ X(φ)` on direct images of sheaves of sets: the base
change of right Kan extensions along the cross-degree arrows. -/
def degreeTransitionOfSquareOp {m n : SimplexCategory} (φ : m ⟶ n) :
    (degreeRingedToposHom X n).toToposHom.pushforward ⟶
      (spacesEtaleRingedToposHom (X.map φ.op)).toToposHom.pushforward ⋙
        (degreeRingedToposHom X m).toToposHom.pushforward where
  app F := ObjectProperty.homMk ((degreeTransitionSquareOp φ).ranBaseChange.app F.obj)
  naturality _F _G f := Sheaf.hom_ext ((degreeTransitionSquareOp φ).ranBaseChange.naturality f.hom)

/-- On underlying presheaves, the degree transition is the base change of right Kan extensions
along the cross-degree arrows. -/
theorem degreeTransitionOfSquareOp_app_hom {m n : SimplexCategory} (φ : m ⟶ n)
    (F : Sheaf (SpacesEtale.topology B S hS (X.obj (op n))) (Type (u + 1))) :
    ((degreeTransitionOfSquareOp φ).app F).hom =
      (degreeTransitionSquareOp φ).ranBaseChange.app F.obj :=
  rfl

/-- On underlying presheaves, `strictDegreeTwoIso` is the base change of right Kan extensions
along the square of the realization. -/
theorem strictDegreeTwoIso_e_hom_app_hom (k : SimplexCategory)
    (F : Sheaf (SpacesEtale.topology B S hS (X.obj (op k))) (Type (u + 1))) :
    ((strictDegreeTwoIso X k).e.hom.app F).hom =
      (componentRealizeSquare X k).op.ranBaseChange.app F.obj :=
  Stacks.Sites.CocontinuousExchange.sheafIsoOfTwoSquare_inv_app_hom_andMorphismsTwoSquare _ _ _ _ _
    (componentRealizeSquare X k) F

/-- The direct image along the comparison with the strict total site is restriction, on
underlying presheaves. -/
theorem strictRingedToposHom_pushforward_map_hom {F G : Sheaf (topology X) (Type (u + 1))}
    (f : F ⟶ G) :
    ((strictRingedToposHom X).toToposHom.pushforward.map f).hom =
      Functor.whiskerLeft (componentTotalComparison X).op f.hom :=
  rfl

/-- On underlying presheaves, `strictComponentTransitionTwoIso` is restriction along the
realization of `u_φ`. -/
theorem strictComponentTransitionTwoIso_e_hom_app_hom {m n : SimplexCategory} (φ : m ⟶ n)
    (F : Sheaf (SpacesEtale.topology B S hS (X.obj (op n))) (Type (u + 1))) :
    ((strictComponentTransitionTwoIso X φ).e.hom.app F).hom =
      Functor.whiskerRight (NatTrans.op (componentStrictTransitionRealizeIso X φ).inv) F.obj :=
  rfl

/-- The square of the realizations, the transition `u_φ`, the cross-fibre arrows and the
cross-degree arrows commutes in `X_{spaces,étale}`. -/
theorem degreeTransitionNatTrans_pasting {m n : SimplexCategory} (φ : m ⟶ n)
    (V : (strictSituation X).component m) :
    (degreeInclusion X n).map ((componentStrictTransitionRealizeIso X φ).inv.app V) ≫
        (componentRealizeSquare X n).app ((componentStrictTransition X φ).obj V) ≫
        (componentTotalComparison X).map
          ((SimplicialSiteSituation.continuousInclusionTransition (strictSimplicialSite X) φ).app
            V) =
      (degreeTransitionNatTrans φ).app ((componentRealize X m).obj V) ≫
        (componentRealizeSquare X m).app V := by
  have hr : ∀ (k : SimplexCategory) (x : (strictSituation X).component k),
      (componentRealizeSquare X k).app x =
        𝟙 ((degreeInclusion X k).obj ((componentRealize X k).obj x)) := fun _ _ => rfl
  refine Hom.ext ?_ ?_
  · simp only [comp_base, hr]
    rfl
  · simp only [comp_hom, hr]
    show StrictObj.transitionRealizeInv φ V ≫ (𝟙 _ ≫ StrictObj.transitionProj φ V) =
      pullback.fst _ _
    rw [Category.id_comp]
    exact (Category.assoc _ _ _).symm.trans ((congrArg (· ≫ _)
      (StrictObj.transitionRealizeInv_hom φ V)).trans (Category.id_comp _))

/-- **The degree transition against the strict components** (Stacks 0DE7 and 04IC). -/
theorem strictDegreeTwoIso_comp_degreeTransition {m n : SimplexCategory} (φ : m ⟶ n) :
    (strictDegreeTwoIso X n).e.hom ≫
        Functor.whiskerLeft (strictComponentRingedToposHom X n).toToposHom.pushforward
          ((strictSituation X).componentRingedTwoMorphism (strictStructureSheaf X) φ).t ≫
        (Functor.associator (strictComponentRingedToposHom X n).toToposHom.pushforward
          ((strictSituation X).transitionRingedToposHom (strictStructureSheaf X)
            φ).toToposHom.pushforward
          ((strictSituation X).componentRingedToposHom (strictStructureSheaf X)
            m).toToposHom.pushforward).inv ≫
        Functor.whiskerRight (strictComponentTransitionTwoIso X φ).e.hom
          ((strictSituation X).componentRingedToposHom (strictStructureSheaf X)
            m).toToposHom.pushforward ≫
        (Functor.associator (spacesEtaleRingedToposHom (X.map φ.op)).toToposHom.pushforward
          (strictComponentRingedToposHom X m).toToposHom.pushforward
          ((strictSituation X).componentRingedToposHom (strictStructureSheaf X)
            m).toToposHom.pushforward).hom =
      Functor.whiskerRight (degreeTransitionOfSquareOp φ)
        (strictRingedToposHom X).toToposHom.pushforward ≫
        (Functor.associator (spacesEtaleRingedToposHom (X.map φ.op)).toToposHom.pushforward
          (degreeRingedToposHom X m).toToposHom.pushforward
          (strictRingedToposHom X).toToposHom.pushforward).hom ≫
        Functor.whiskerLeft (spacesEtaleRingedToposHom (X.map φ.op)).toToposHom.pushforward
          (strictDegreeTwoIso X m).e.hom := by
  refine NatTrans.ext (funext fun F => ?_)
  dsimp only [NatTrans.comp_app, Functor.whiskerLeft_app, Functor.whiskerRight_app,
    Functor.associator_hom_app, Functor.associator_inv_app, RingedToposHom.comp,
    MorphismOfTopoi.comp, Functor.comp_obj, Functor.comp_map]
  simp only [Category.id_comp, Category.comp_id]
  refine Sheaf.hom_ext ?_
  simp only [ObjectProperty.FullSubcategory.comp_hom]
  have e1 := strictDegreeTwoIso_e_hom_app_hom n F
  have e2 := strictDegreeTwoIso_e_hom_app_hom m
    ((spacesEtaleRingedToposHom (X.map φ.op)).toToposHom.pushforward.obj F)
  have e3 := SimplicialSiteSituation.componentRingedTwoMorphism_t_app_hom (strictSimplicialSite X)
    (strictStructureSheaf X) φ ((strictComponentRingedToposHom X n).toToposHom.pushforward.obj F)
  have e4 := SimplicialSiteSituation.componentRingedToposHom_pushforward_map_hom
    (strictSituation X) (strictStructureSheaf X) m
    ((strictComponentTransitionTwoIso X φ).e.hom.app F)
  have e5 := strictComponentTransitionTwoIso_e_hom_app_hom φ F
  have e6 := strictRingedToposHom_pushforward_map_hom ((degreeTransitionOfSquareOp φ).app F)
  have e7 := degreeTransitionOfSquareOp_app_hom φ F
  have key := CategoryTheory.ranBaseChange_comp_transition_eq (A := Type (u + 1))
    (componentRealizeSquare X m) (componentRealizeSquare X n)
    (SimplicialSiteSituation.continuousInclusionTransition (strictSimplicialSite X) φ)
    (degreeTransitionNatTrans φ) (componentStrictTransitionRealizeIso X φ).inv F.obj _ e3
    (Functor.whiskerRight (NatTrans.op (componentStrictTransitionRealizeIso X φ).inv) F.obj)
    (fun _ => rfl) (degreeTransitionNatTrans_pasting φ)
  exact (congrArg₂ (· ≫ ·) e1 (congrArg₂ (· ≫ ·) rfl (e4.trans (congrArg _ e5)))).trans
    (key.trans (congrArg₂ (· ≫ ·) (e6.trans (congrArg _ e7)).symm e2.symm))

section Augmentation

variable {Z : AlgebraicSpaces B S hS} (a : X ⟶ (Functor.const _).obj Z)

/-- The 2-isomorphism of an equality of morphisms of algebraic spaces, on underlying presheaves:
restriction along the equality of the base-change functors. -/
theorem ofEq_spacesEtaleRingedToposHom_e_hom_app_hom {Z₁ Z₂ : AlgebraicSpaces B S hS}
    {f₁ f₂ : Z₁ ⟶ Z₂} (h : f₁ = f₂) (F : Sheaf (SpacesEtale.topology B S hS Z₁) (Type (u + 1))) :
    ((RingedToposHom.TwoIso.ofEq
        (congrArg (fun g => spacesEtaleRingedToposHom (Z₂ := Z₂) g) h)).e.hom.app F).hom =
      Functor.whiskerRight
        (NatTrans.op (eqToHom (congrArg (fun g => (spacesBaseChange B S hS g).functor) h.symm)))
        F.obj := by
  subst h
  ext V
  simp [RingedToposHom.TwoIso.ofEq, RingedToposHom.TwoIso.refl]
  rfl

/-- On underlying presheaves, the triangle 2-isomorphism `a_m ∘ X(φ) ≅ a_n` is restriction along
the comparison of iterated base changes. -/
theorem strictAugmentationTriangleTwoIso_e_hom_app_hom {m n : SimplexCategory} (φ : m ⟶ n)
    (hk : X.map φ.op ≫ a.app (op m) = a.app (op n))
    (F : Sheaf (SpacesEtale.topology B S hS (X.obj (op n))) (Type (u + 1))) :
    ((strictAugmentationTriangleTwoIso a φ hk).e.hom.app F).hom =
      Functor.whiskerRight (NatTrans.op
        (eqToHom (congrArg (fun g => (spacesBaseChange B S hS g).functor) hk.symm) ≫
          (spacesBaseChange_comp B S hS (X.map φ.op) (a.app (op m))).inv)) F.obj := by
  show (((spacesEtaleRingedToposHomCompTwoIsoSpacesEtaleRingedToposHomComp (Z := Z) (X.map φ.op)
      (a.app (op m))).e.inv.app F) ≫ ((RingedToposHom.TwoIso.ofEq
        (congrArg (fun g => spacesEtaleRingedToposHom (Z₂ := Z) g) hk)).e.hom.app F)).hom = _
  rw [ObjectProperty.FullSubcategory.comp_hom, ofEq_spacesEtaleRingedToposHom_e_hom_app_hom hk F,
    NatTrans.op_comp, Functor.whiskerRight_comp]
  rfl

/-- The direct image along the augmentation is restriction along base change followed by right
Kan extension along forgetting the degree, on underlying presheaves. -/
theorem augmentationRingedToposHom_pushforward_map_hom {F G : Sheaf (topology X) (Type (u + 1))}
    (f : F ⟶ G) :
    ((augmentationRingedToposHom a).toToposHom.pushforward.map f).hom =
      (constForget Z).op.ran.map (Functor.whiskerLeft (pullbackFunctor a).op f.hom) :=
  rfl

/-- On underlying presheaves, `augmentationDegreeTwoIso` is the base change of right Kan
extensions along the degree square, right Kan extension along forgetting the degree, and the
identification `constDegreePushforwardIso`. -/
theorem augmentationDegreeTwoIso_e_hom_app_hom (k : SimplexCategory)
    (G : Sheaf (SpacesEtale.topology B S hS (X.obj (op k))) (Type (u + 1))) :
    ((augmentationDegreeTwoIso a k).e.hom.app G).hom =
      (constForget Z).op.ran.map
          ((degreeExchangeSquare a k).op.ranBaseChange.app G.obj ≫
            (degreeInclusion ((Functor.const _).obj Z) k).op.ran.map
              (Functor.whiskerRight (NatTrans.op (spacesBaseChangeIso a k).hom) G.obj)) ≫
        ((constDegreePushforwardIso Z k).hom.app
          ((spacesEtaleRingedToposHom (a.app (op k))).toToposHom.pushforward.obj G)).hom :=
  rfl

/-- On underlying presheaves, `constDegreePushforwardIso` is the counit of right Kan extension
along forgetting the degree, then the counit along the inclusion of the degree. -/
theorem constDegreePushforwardIso_hom_app_hom_app (Z : AlgebraicSpaces B S hS)
    (k : SimplexCategory)
    (Y : Sheaf (SpacesEtale.topology B S hS Z) (Type (u + 1))) (V : (SpacesEtale B S hS Z)ᵒᵖ) :
    ((constDegreePushforwardIso Z k).hom.app Y).hom.app V =
      ((constForget Z).op.ranCounit.app
          ((degreeInclusion ((Functor.const _).obj Z) k).op.ran.obj Y.obj)).app
        (op ((degreeInclusion ((Functor.const _).obj Z) k).obj V.unop)) ≫
        ((degreeInclusion ((Functor.const _).obj Z) k).op.ranCounit.app Y.obj).app V := by
  have h := conjugateEquiv_counit (constDegreeAdj Z k) Adjunction.id
    (NatIso.ofComponents (fun F ↦ Iso.refl F) (fun _ ↦ rfl) :
      𝟭 _ ≅ (constToposHom Z).inverseImage ⋙
        (degreeToposHom ((Functor.const _).obj Z) k).inverseImage).hom Y
  have h' : (constDegreePushforwardIso Z k).hom.app Y = (constDegreeAdj Z k).counit.app Y :=
    (Category.comp_id _).symm.trans (h.trans (Category.id_comp _))
  rw [h', constDegreeAdj, Adjunction.comp_counit_app, ObjectProperty.FullSubcategory.comp_hom,
    NatTrans.comp_app]
  dsimp only [constToposHom, degreeToposHom, Functor.morphismOfTopoiOfCocontinuous]
  rw [Functor.sheafPushforwardContinuous_map_hom_app,
    Functor.sheafAdjunctionCocontinuous_counit_app_hom,
    Functor.sheafAdjunctionCocontinuous_counit_app_hom, Functor.ranAdjunction_counit,
    Functor.ranAdjunction_counit]
  rfl

/-- The counit of right Kan extension along forgetting the degree, read in degrees `n` and `m`
of an object `V`, differ by `(φ, 𝟙)`. -/
theorem ranCounit_constForget_app_degree {m n : SimplexCategory} (φ : m ⟶ n)
    (Q : (SimplicialSpacesEtaleSite B S hS ((Functor.const _).obj Z))ᵒᵖ ⥤ Type (u + 1))
    (V : SpacesEtale B S hS Z) :
    ((constForget Z).op.ranCounit.app Q).app
        (op ((degreeInclusion ((Functor.const _).obj Z) n).obj V)) =
      ((constForget Z).op.ranCounit.app Q).app
          (op ((degreeInclusion ((Functor.const _).obj Z) m).obj V)) ≫
        Q.map (constDegreeTransitionHom Z φ V).op := by
  have h := ((constForget Z).op.ranCounit.app Q).naturality (constDegreeTransitionHom Z φ V).op
  have e : ((constForget Z).op ⋙ (constForget Z).op.ran.obj Q).map
      (constDegreeTransitionHom Z φ V).op = 𝟙 _ :=
    (congrArg (fun (k : V ⟶ V) => ((constForget Z).op.ran.obj Q).map k.op)
      (constForget_map_constDegreeTransitionHom φ V)).trans
        (((constForget Z).op.ran.obj Q).map_id _)
  exact (Category.id_comp _).symm.trans ((congrArg (· ≫ _) e.symm).trans h)

/-- The base changes along `a_n`, along `X(φ) ≫ a_m` and along `a_m` then `X(φ)`. -/
abbrev augmentationTransitionBaseChange {m n : SimplexCategory} (φ : m ⟶ n)
    (hk : X.map φ.op ≫ a.app (op m) = a.app (op n)) :
    (spacesBaseChange B S hS (a.app (op n))).functor ⟶
      (spacesBaseChange B S hS (a.app (op m))).functor ⋙
        (spacesBaseChange B S hS (X.map φ.op)).functor :=
  eqToHom (congrArg (fun g => (spacesBaseChange B S hS g).functor) hk.symm) ≫
    (spacesBaseChange_comp B S hS (X.map φ.op) (a.app (op m))).inv

/-- The base change along an equality, read against the first projection. -/
theorem eqToHom_spacesBaseChange_app_hom_left_fst {Y₁ Y₂ : AlgebraicSpaces B S hS}
    {k₁ k₂ : Y₁ ⟶ Y₂} (h : k₁ = k₂) (W : SpacesEtale B S hS Y₂) :
    ((eqToHom (congrArg (fun g => (spacesBaseChange B S hS g).functor) h)).app W).hom.left ≫
        pullback.fst W.1.hom k₂ = pullback.fst W.1.hom k₁ := by
  subst h
  exact Category.id_comp _

/-- The base change along an equality, read against the second projection. -/
theorem eqToHom_spacesBaseChange_app_hom_left_snd {Y₁ Y₂ : AlgebraicSpaces B S hS}
    {k₁ k₂ : Y₁ ⟶ Y₂} (h : k₁ = k₂) (W : SpacesEtale B S hS Y₂) :
    ((eqToHom (congrArg (fun g => (spacesBaseChange B S hS g).functor) h)).app W).hom.left ≫
        pullback.snd W.1.hom k₂ = pullback.snd W.1.hom k₁ := by
  subst h
  exact Category.id_comp _

/-- The comparison of base changes of `augmentationTransitionBaseChange`, against the
projections of `V ×_Z X_m`. -/
theorem augmentationTransitionBaseChange_hom_left {m n : SimplexCategory} (φ : m ⟶ n)
    (hk : X.map φ.op ≫ a.app (op m) = a.app (op n)) (V : SpacesEtale B S hS Z) :
    ((augmentationTransitionBaseChange a φ hk).app V).hom.left ≫
        ((spacesBaseChange B S hS (X.map φ.op)).functor.map
          ((spacesBaseChangeIso a m).hom.app V)).hom.left ≫
        pullback.fst ((degreePullback a m).obj V).1.hom (X.map φ.op) =
      pullback.map V.1.hom (a.app (op n)) V.1.hom (a.app (op m)) (𝟙 _) (X.map φ.op) (𝟙 Z)
        ((Category.comp_id _).trans (Category.id_comp _).symm)
        ((Category.comp_id _).trans hk.symm) := by
  have p1 : ((spacesBaseChange B S hS (X.map φ.op)).functor.map
        ((spacesBaseChangeIso a m).hom.app V)).hom.left ≫
        (spacesBaseChange B S hS (X.map φ.op)).projection.app ((degreePullback a m).obj V) =
      (spacesBaseChange B S hS (X.map φ.op)).projection.app
          ((spacesBaseChange B S hS (a.app (op m))).functor.obj V) ≫
        ((spacesBaseChangeIso a m).hom.app V).hom.left :=
    (spacesBaseChange B S hS (X.map φ.op)).projection.naturality
      ((spacesBaseChangeIso a m).hom.app V)
  have p2 := spacesBaseChange_comp_projection B S hS (X.map φ.op) (a.app (op m)) V
  have p2' : ((spacesBaseChange_comp B S hS (X.map φ.op) (a.app (op m))).inv.app V).hom.left ≫
      ((spacesBaseChange B S hS (X.map φ.op)).projection.app
          ((spacesBaseChange B S hS (a.app (op m))).functor.obj V) ≫
        (spacesBaseChange B S hS (a.app (op m))).projection.app V) =
      (spacesBaseChange B S hS (X.map φ.op ≫ a.app (op m))).projection.app V := by
    rw [← p2, ← Category.assoc]
    have e := congrArg (fun t => t.hom.left)
      ((spacesBaseChange_comp B S hS (X.map φ.op) (a.app (op m))).inv_hom_id_app V)
    exact (congrArg (· ≫ _) e).trans (Category.id_comp _)
  have p3 := eqToHom_spacesBaseChange_app_hom_left_fst hk.symm V
  have p4 := eqToHom_spacesBaseChange_app_hom_left_snd hk.symm V
  have w1 := Over.w ((spacesBaseChange_comp B S hS (X.map φ.op) (a.app (op m))).inv.app V).hom
  have w2 := Over.w ((spacesBaseChange B S hS (X.map φ.op)).functor.map
    ((spacesBaseChangeIso a m).hom.app V)).hom
  have w3 := ((spacesBaseChange B S hS (X.map φ.op)).isPullback ((degreePullback a m).obj V)).w
  have L : ((eqToHom (congrArg (fun g => (spacesBaseChange B S hS g).functor) hk.symm)).app
        V).hom.left ≫
      ((spacesBaseChange_comp B S hS (X.map φ.op) (a.app (op m))).inv.app V).hom.left ≫
        ((spacesBaseChange B S hS (X.map φ.op)).functor.map
          ((spacesBaseChangeIso a m).hom.app V)).hom.left ≫
          (spacesBaseChange B S hS (X.map φ.op)).projection.app ((degreePullback a m).obj V) ≫
            (spacesBaseChange B S hS (a.app (op m))).projection.app V =
      pullback.fst V.1.hom (a.app (op n)) :=
    (congrArg (_ ≫ ·) (congrArg (_ ≫ ·) ((reassoc_of% p1) _))).trans
      ((congrArg (_ ≫ ·) p2').trans p3)
  have Ls : ((eqToHom (congrArg (fun g => (spacesBaseChange B S hS g).functor) hk.symm)).app
        V).hom.left ≫
      ((spacesBaseChange_comp B S hS (X.map φ.op) (a.app (op m))).inv.app V).hom.left ≫
        ((spacesBaseChange B S hS (X.map φ.op)).functor.map
          ((spacesBaseChangeIso a m).hom.app V)).hom.left ≫
          (spacesBaseChange B S hS (X.map φ.op)).projection.app ((degreePullback a m).obj V) ≫
            ((degreePullback a m).obj V).1.hom =
      pullback.snd V.1.hom (a.app (op n)) ≫ X.map φ.op :=
    (congrArg (_ ≫ ·) (congrArg (_ ≫ ·) (congrArg (_ ≫ ·) w3))).trans
      ((congrArg (_ ≫ ·) (congrArg (_ ≫ ·) ((reassoc_of% w2) _))).trans
        ((congrArg (_ ≫ ·) ((reassoc_of% w1) _)).trans ((reassoc_of% p4) _)))
  refine pullback.hom_ext ?_ ?_
  · exact (Category.assoc _ _ _).trans ((congrArg (_ ≫ ·) (Category.assoc _ _ _)).trans
      ((Category.assoc _ _ _).trans (L.trans ((pullback.lift_fst _ _ _).trans
        (Category.comp_id _)).symm)))
  · exact (Category.assoc _ _ _).trans ((congrArg (_ ≫ ·) (Category.assoc _ _ _)).trans
      ((Category.assoc _ _ _).trans (Ls.trans (pullback.lift_snd _ _ _).symm)))

/-- The cross-degree arrows, the degree squares of base change and `(φ, 𝟙)` commute in
`X_{spaces,étale}`. -/
theorem degreeTransitionNatTrans_degreeSquare {m n : SimplexCategory} (φ : m ⟶ n)
    (hk : X.map φ.op ≫ a.app (op m) = a.app (op n)) (V : SpacesEtale B S hS Z) :
    (degreeInclusion X n).map ((augmentationTransitionBaseChange a φ hk).app V) ≫
        (degreeInclusion X n).map ((spacesBaseChange B S hS (X.map φ.op)).functor.map
          ((spacesBaseChangeIso a m).hom.app V)) ≫
        (degreeTransitionNatTrans φ).app ((degreePullback a m).obj V) ≫
        (degreeExchangeSquare a m).app V =
      (degreeInclusion X n).map ((spacesBaseChangeIso a n).hom.app V) ≫
        (degreeExchangeSquare a n).app V ≫
          (pullbackFunctor a).map (constDegreeTransitionHom Z φ V) := by
  have hid : ∀ (k : SimplexCategory) (W : SpacesEtale B S hS Z),
      (spacesBaseChangeIso a k).hom.app W = 𝟙 _ := fun _ _ => rfl
  refine Hom.ext rfl ?_
  exact augmentationTransitionBaseChange_hom_left a φ hk V

/-- The degree transition against the augmentation, on underlying presheaves. -/
theorem degreeTransition_comp_augmentationDegree_hom {m n : SimplexCategory} (φ : m ⟶ n)
    (hk : X.map φ.op ≫ a.app (op m) = a.app (op n))
    (F : Sheaf (SpacesEtale.topology B S hS (X.obj (op n))) (Type (u + 1))) :
    (constForget Z).op.ran.map (Functor.whiskerLeft (pullbackFunctor a).op
        ((degreeTransitionSquareOp φ).ranBaseChange.app F.obj)) ≫
      ((constForget Z).op.ran.map
          ((degreeExchangeSquare a m).op.ranBaseChange.app
              ((spacesBaseChange B S hS (X.map φ.op)).functor.op ⋙ F.obj) ≫
            (degreeInclusion ((Functor.const _).obj Z) m).op.ran.map
              (Functor.whiskerRight (NatTrans.op (spacesBaseChangeIso a m).hom)
                ((spacesBaseChange B S hS (X.map φ.op)).functor.op ⋙ F.obj))) ≫
        ((constDegreePushforwardIso Z m).hom.app
          ((spacesEtaleRingedToposHom (a.app (op m))).toToposHom.pushforward.obj
            ((spacesEtaleRingedToposHom (X.map φ.op)).toToposHom.pushforward.obj F))).hom) ≫
      Functor.whiskerRight (NatTrans.op
        (eqToHom (congrArg (fun g => (spacesBaseChange B S hS g).functor) hk.symm) ≫
          (spacesBaseChange_comp B S hS (X.map φ.op) (a.app (op m))).inv)) F.obj =
    (constForget Z).op.ran.map
        ((degreeExchangeSquare a n).op.ranBaseChange.app F.obj ≫
          (degreeInclusion ((Functor.const _).obj Z) n).op.ran.map
            (Functor.whiskerRight (NatTrans.op (spacesBaseChangeIso a n).hom) F.obj)) ≫
      ((constDegreePushforwardIso Z n).hom.app
        ((spacesEtaleRingedToposHom (a.app (op n))).toToposHom.pushforward.obj F)).hom := by
  refine NatTrans.ext (funext fun V => ?_)
  have kM := constDegreePushforwardIso_hom_app_hom_app Z m
    ((spacesEtaleRingedToposHom (a.app (op m))).toToposHom.pushforward.obj
      ((spacesEtaleRingedToposHom (X.map φ.op)).toToposHom.pushforward.obj F)) V
  have kN := constDegreePushforwardIso_hom_app_hom_app Z n
    ((spacesEtaleRingedToposHom (a.app (op n))).toToposHom.pushforward.obj F) V
  have f1 := ran_map_app_ranCounit_app (constForget Z).op
    ((degreeExchangeSquare a m).op.ranBaseChange.app
        ((spacesBaseChange B S hS (X.map φ.op)).functor.op ⋙ F.obj) ≫
      (degreeInclusion ((Functor.const _).obj Z) m).op.ran.map
        (Functor.whiskerRight (NatTrans.op (spacesBaseChangeIso a m).hom)
          ((spacesBaseChange B S hS (X.map φ.op)).functor.op ⋙ F.obj)))
    (op ((degreeInclusion ((Functor.const _).obj Z) m).obj V.unop))
  have f2 := ran_map_app_ranCounit_app (constForget Z).op
    (Functor.whiskerLeft (pullbackFunctor a).op
      ((degreeTransitionSquareOp φ).ranBaseChange.app F.obj))
    (op ((degreeInclusion ((Functor.const _).obj Z) m).obj V.unop))
  have f3 := ran_map_app_ranCounit_app (constForget Z).op
    ((degreeExchangeSquare a n).op.ranBaseChange.app F.obj ≫
      (degreeInclusion ((Functor.const _).obj Z) n).op.ran.map
        (Functor.whiskerRight (NatTrans.op (spacesBaseChangeIso a n).hom) F.obj))
    (op ((degreeInclusion ((Functor.const _).obj Z) n).obj V.unop))
  have fψ := ranCounit_constForget_app_degree φ
    ((pullbackFunctor a).op ⋙ (degreeInclusion X n).op.ran.obj F.obj) V.unop
  have key := CategoryTheory.ranBaseChange_comp_degreeSquare_eq (A := Type (u + 1))
    (degreeExchangeSquare a m) (degreeExchangeSquare a n) (degreeTransitionNatTrans φ)
    (spacesBaseChangeIso a m).hom (spacesBaseChangeIso a n).hom
    (augmentationTransitionBaseChange a φ hk) F.obj V.unop (constDegreeTransitionHom Z φ V.unop)
    (degreeTransitionNatTrans_degreeSquare a φ hk V.unop)
  exact (CategoryTheory.comp_comp_comp_eq_of_ranCounitProjections kM f1 f2).trans
    ((congrArg (_ ≫ ·) key).trans
      (CategoryTheory.comp_eq_of_ranCounitProjections kN f3 fψ).symm)

/-- **The degree transition against the augmentation** (Stacks 0DE7). -/
theorem degreeTransition_comp_augmentationDegreeTwoIso {m n : SimplexCategory} (φ : m ⟶ n)
    (hk : X.map φ.op ≫ a.app (op m) = a.app (op n)) :
    Functor.whiskerRight (degreeTransitionOfSquareOp φ)
        (augmentationRingedToposHom a).toToposHom.pushforward ≫
        (Functor.associator (spacesEtaleRingedToposHom (X.map φ.op)).toToposHom.pushforward
          (degreeRingedToposHom X m).toToposHom.pushforward
          (augmentationRingedToposHom a).toToposHom.pushforward).hom ≫
        Functor.whiskerLeft (spacesEtaleRingedToposHom (X.map φ.op)).toToposHom.pushforward
          (augmentationDegreeTwoIso a m).e.hom ≫ (strictAugmentationTriangleTwoIso a φ hk).e.hom =
      (augmentationDegreeTwoIso a n).e.hom := by
  refine NatTrans.ext (funext fun F => ?_)
  dsimp only [NatTrans.comp_app, Functor.whiskerLeft_app, Functor.whiskerRight_app,
    Functor.associator_hom_app, Functor.associator_inv_app, RingedToposHom.comp,
    MorphismOfTopoi.comp, Functor.comp_obj, Functor.comp_map]
  simp only [Category.id_comp]
  refine Sheaf.hom_ext ?_
  simp only [ObjectProperty.FullSubcategory.comp_hom]
  have e1 := augmentationRingedToposHom_pushforward_map_hom a ((degreeTransitionOfSquareOp φ).app F)
  have e2 := augmentationDegreeTwoIso_e_hom_app_hom a m
    ((spacesEtaleRingedToposHom (X.map φ.op)).toToposHom.pushforward.obj F)
  have e3 := strictAugmentationTriangleTwoIso_e_hom_app_hom a φ hk F
  have e4 := augmentationDegreeTwoIso_e_hom_app_hom a n F
  have e5 := degreeTransitionOfSquareOp_app_hom φ F
  exact (congrArg₂ (· ≫ ·) (e1.trans (congrArg _ (congrArg _ e5))) (congrArg₂ (· ≫ ·) e2 e3)).trans
    ((degreeTransition_comp_augmentationDegree_hom a φ hk F).trans e4.symm)

/-- **The 2-morphism identity behind Stacks 0D7H (4)**: the 2-morphism `t_φ : g_n ⟶ g_m ∘ f_φ`
of Stacks 04IC, with the augmentation `b` appended and the realization `r_n` prepended, is the
composite of the 2-isomorphisms of Stacks 0DE7 through `a_n` and `a_m ∘ X(φ)`. Both are compared
with the degree transition `d_n ⟶ d_m ∘ X(φ)`. -/
theorem strictAugmentationTwoMorphismCoherent : StrictAugmentationTwoMorphismCoherent a := by
  intro m n φ hk
  exact RingedToposHom.TwoIso.whiskerLeft_whiskerRight_t_eq_of_degreeTransition.{u + 1, u + 1,
    u + 1, u + 1, u + 1, u + 1, u + 1, u + 1, u + 1, u + 1, u + 1, u + 1, u + 1, u + 1, u + 1,
    u + 1, u + 1, u + 1, u + 1, u + 1, u + 1}
    ((strictSituation X).componentRingedTwoMorphism (strictStructureSheaf X) φ)
    (strictDegreeTwoIso X n) (strictDegreeTwoIso X m) (strictAugmentationTwoIso a)
    (augmentationDegreeTwoIso a n) (augmentationDegreeTwoIso a m)
    (strictComponentTransitionTwoIso X φ) (strictAugmentationTriangleTwoIso a φ hk)
    (degreeTransitionOfSquareOp φ) (strictDegreeTwoIso_comp_degreeTransition φ)
    (degreeTransition_comp_augmentationDegreeTwoIso a φ hk)

end Augmentation

variable (B S hS) in
/-- **Stacks 0D7H (4) made explicit, through the strict components** (internal): for every
augmentation `a : X ⟶ Z`, the derived transitions of `Lb^*M` realize to the composition
isomorphisms `La_n^*M ≅ LX(φ)^* La_m^*M` of Stacks 0D6D. -/
theorem strictAugmentationTransitionCoherent :
    ∀ (X : SimplicialObject (AlgebraicSpaces B S hS)) (Z : AlgebraicSpaces B S hS)
      (a : X ⟶ (Functor.const _).obj Z), StrictAugmentationTransitionCoherent X a :=
  fun _ _ a => strictAugmentationTransitionCoherent_of_twoMorphism
    (strictAugmentationTwoMorphismCoherent a)

end AlgebraicGeometry.Space.SimplicialSpacesEtaleSite

end
