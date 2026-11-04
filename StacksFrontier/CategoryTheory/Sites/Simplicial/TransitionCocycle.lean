module

public import StacksFrontier.CategoryTheory.Sites.Simplicial.RestrictTransition
public import StacksFrontier.CategoryTheory.Sites.Simplicial.Sheaves

/-!
# Pseudofunctoriality of the restriction transitions of a simplicial site

Let `S` be a simplicial-site situation and `F` a sheaf on its total site. Restricting `F` to the
components and comparing across a simplex map gives the transitions `restrictTransition` on
direct images and `fiberTransition` on inverse images. This file proves that those transitions
are pseudofunctorial: the transition of an identity simplex map is the canonical identification,
and the transition of a composite is the composite of the transitions, compared by the canonical
compositor.

## Main results

* `CategoryTheory.SimplicialSiteSituation.restrictTransition_id` and
  `.restrictTransition_comp`: the unit and cocycle laws for the direct-image transition.
* `CategoryTheory.SimplicialSiteSituation.fiberTransition_id` and `.fiberTransition_comp`: the
  unit and cocycle laws for the inverse-image transition.
* `CategoryTheory.Grothendieck.id_eq_mk`, `.ιNatTrans_id_app`,
  `.ιNatTrans_app_comp_ιNatTrans_app`, `.whiskerRight_op_ιNatTrans_id` and
  `.whiskerRight_op_ιNatTrans_comp`: the same two laws for the Cartesian lifts of a covariant
  Grothendieck construction, both as arrows of the total category and after restricting a
  presheaf along them.
* `CategoryTheory.Pseudofunctor.CoGrothendieck.ιNatTrans_app_comp_ιNatTrans_app`: the cocycle
  law for the Cartesian lifts of a contravariant Grothendieck construction.

## Implementation notes

Specialized to a simplicial site, intermediate terms mix two definitionally equal but
syntactically different spellings of a direct image (`Functor.sheafPushforwardCocontinuous` and
the right Kan extension `Functor.ran` underlying it), and a goal containing both is not
type-correct at `implicit` transparency, so neither `rw` nor `simp` applies to it. The lemmas are
therefore stated for an arbitrary pseudofunctor, resp. for an arbitrary pair of cocontinuous site
functors, and the comparisons are assembled with `Eq.trans` and `congrArg`.

## References

* [Stacks Project, Tag 09WE](https://stacks.math.columbia.edu/tag/09WE)
* [Stacks Project, Tag 09WF](https://stacks.math.columbia.edu/tag/09WF)
-/

@[expose] public section

open CategoryTheory CategoryTheory.Functor CategoryTheory.Pseudofunctor Opposite

universe v₁ u₁ v₂ u₂ u

namespace CategoryTheory.Grothendieck

variable {𝒞 : Type u₁} [Category.{v₁} 𝒞] {G : 𝒞 ⥤ Cat.{v₂, u₂}}

attribute [local implicit_reducible] Grothendieck.ι

/-- The identity arrow of a fibre of a Grothendieck construction, written out. -/
theorem id_eq_mk (X : 𝒞) (d : G.obj X) :
    𝟙 ((ι G X).obj d) =
      ⟨𝟙 X, (eqToIso (congrArg Cat.Hom.toFunctor (G.map_id X))).hom.app d⟩ := by
  refine Grothendieck.ext _ _ rfl ?_
  simp only [ι, Cat.Hom.id_toFunctor, eqToIso.hom, id_base, id_fiber, eqToHom_app, id_obj]
  exact eqToHom_trans _ _

/-- The Cartesian lifts of two composable arrows compose to the Cartesian lift of the
composite, up to the identification of `G(f ≫ g)` with `G(f) ⋙ G(g)`. -/
theorem ιNatTrans_app_comp_ιNatTrans_app {X Y Z : 𝒞} (f : X ⟶ Y) (g : Y ⟶ Z) (d : G.obj X) :
    (ιNatTrans (F := G) f).app d ≫ (ιNatTrans (F := G) g).app ((G.map f).toFunctor.obj d) =
      ⟨f ≫ g, (eqToIso (congrArg Cat.Hom.toFunctor (G.map_comp f g))).hom.app d⟩ := by
  refine Grothendieck.ext _ _ rfl ?_
  simp only [ι, comp_obj, Cat.Hom.comp_toFunctor, eqToIso.hom, ιNatTrans, comp_base, comp_fiber,
    map_id, Category.comp_id, eqToHom_app]
  exact eqToHom_trans _ _

/-- The Cartesian lift of an identity arrow is the canonical identification of the fibre with
its image under the identity transition functor. -/
theorem ιNatTrans_id_app (X : 𝒞) (d : G.obj X) :
    (ιNatTrans (F := G) (𝟙 X)).app d = eqToHom (by simp) := by
  refine Grothendieck.ext _ _ ?_ ?_
  · simp only [ιNatTrans_app_base, base_eqToHom]
    exact (eqToHom_refl X _).symm
  · simp only [ιNatTrans_app_fiber, fiber_eqToHom]
    exact (Category.comp_id _).trans rfl

/-- Restricting a presheaf on the total category along the Cartesian lifts of an identity arrow
gives the canonical identification: the unit law for the Cartesian lifts, read on sections. -/
theorem whiskerRight_op_ιNatTrans_id {E : Type*} [Category E] (X : 𝒞)
    (P : (Grothendieck G)ᵒᵖ ⥤ E) :
    Functor.whiskerRight (NatTrans.op (ιNatTrans (F := G) (𝟙 X))) P =
      eqToHom (by simp [Functor.id_comp]) := by
  apply NatTrans.ext
  funext d
  obtain ⟨d⟩ := d
  simp only [Functor.whiskerRight_app, NatTrans.op_app, ιNatTrans_id_app, eqToHom_app]
  rw [eqToHom_op, eqToHom_map]

/-- Restricting a presheaf on the total category along the Cartesian lifts of two composable
arrows is restricting along the Cartesian lifts of the composite, up to the identification of
`G(a ≫ b)` with `G(a) ⋙ G(b)`: the cocycle law for the Cartesian lifts, read on sections. -/
theorem whiskerRight_op_ιNatTrans_comp {E : Type*} [Category E] {X Y Z : 𝒞}
    (a : X ⟶ Y) (b : Y ⟶ Z) (P : (Grothendieck G)ᵒᵖ ⥤ E) :
    eqToHom (show (G.map (a ≫ b)).toFunctor.op ⋙ (ι G Z).op ⋙ P =
        (G.map a).toFunctor.op ⋙ (G.map b).toFunctor.op ⋙ (ι G Z).op ⋙ P by
          rw [G.map_comp]; rfl) ≫
      (Functor.whiskerLeft (G.map a).toFunctor.op
          (Functor.whiskerRight (NatTrans.op (ιNatTrans (F := G) b)) P) ≫
        Functor.whiskerRight (NatTrans.op (ιNatTrans (F := G) a)) P) =
      Functor.whiskerRight (NatTrans.op (ιNatTrans (F := G) (a ≫ b))) P := by
  apply NatTrans.ext
  funext d
  obtain ⟨d⟩ := d
  simp only [NatTrans.comp_app, eqToHom_app, Functor.whiskerLeft_app, Functor.whiskerRight_app,
    NatTrans.op_app, Functor.op_obj, unop_op]
  rw [← P.map_comp, ← op_comp, ιNatTrans_app_comp_ιNatTrans_app,
    ← ιNatTrans_app_comp_ι_map, op_comp, P.map_comp]
  simp only [eqToIso.hom, eqToHom_app, eqToHom_map, eqToHom_op, eqToHom_trans_assoc,
    eqToHom_refl, Category.id_comp]

end CategoryTheory.Grothendieck

namespace CategoryTheory.Pseudofunctor.CoGrothendieck

variable {𝒮 : Type u₁} [Category.{v₁} 𝒮]
  (F : Pseudofunctor (LocallyDiscrete 𝒮ᵒᵖ) Cat.{v₂, u₂})

attribute [local implicit_reducible] ι Quiver.Hom.toLoc

/-- The Cartesian lifts of two composable arrows compose to the Cartesian lift of the composite,
up to the compositor of the pseudofunctor.

This is the contravariant counterpart of
`CategoryTheory.Grothendieck.ιNatTrans_app_comp_ιNatTrans_app`. -/
theorem ιNatTrans_app_comp_ιNatTrans_app {R S T : 𝒮} (f : R ⟶ S) (g : S ⟶ T)
    (a : F.obj ⟨op T⟩) :
    (ι F R).map ((F.mapComp g.op.toLoc f.op.toLoc).hom.toNatTrans.app a) ≫
        (ιNatTrans F f).app ((F.map g.op.toLoc).toFunctor.obj a) ≫
        (ιNatTrans F g).app a =
      (ιNatTrans F (f ≫ g)).app a := by
  rw [← Category.assoc, ι_map_comp_ιNatTrans_app]
  refine Hom.ext _ _ ?_ ?_
  · simp [ιNatTrans]
  · simp only [ιNatTrans, ι, categoryStruct_comp_fiber, comp_obj, Functor.map_id,
      Category.id_comp]
    simp [← Cat.Hom₂.comp_app]

end CategoryTheory.Pseudofunctor.CoGrothendieck

namespace CategoryTheory.SimplicialSiteSituation

attribute [local implicit_reducible] CoGrothendieck.ι Quiver.Hom.toLoc
  SimplicialSite.totalPseudofunctor Functor.toPseudofunctor' pseudofunctorOfIsLocallyDiscrete

/-- A strict pseudofunctor out of a locally discrete bicategory sends an identity arrow to an
identity. -/
private theorem toPseudofunctor'_map_id {I B : Type*} [Category I] [Bicategory B]
    [Bicategory.Strict B] (P : I ⥤ B) (X : I) :
    P.toPseudofunctor'.map (𝟙 (⟨X⟩ : LocallyDiscrete I)) = 𝟙 (P.obj X) :=
  P.map_id X

section AdjunctionComparisons

variable {A : Type u₁} [Category.{v₁} A] {B : Type u₂} [Category.{v₂} B]

/-- Transposing along an adjunction and then comparing with a second right adjoint of the same
functor is transposing along that second adjunction. -/
private theorem homEquiv_comp_rightAdjointUniq_hom {L : A ⥤ B} {R R' : B ⥤ A}
    (adj : L ⊣ R) (adj' : L ⊣ R') {X : A} {Y : B} (g : L.obj X ⟶ Y) :
    adj.homEquiv X Y g ≫ (Adjunction.rightAdjointUniq adj adj').hom.app Y =
      adj'.homEquiv X Y g := by
  rw [Adjunction.homEquiv_unit, Adjunction.homEquiv_unit, Category.assoc,
    (Adjunction.rightAdjointUniq adj adj').hom.naturality g, ← Category.assoc,
    Adjunction.unit_rightAdjointUniq_hom_app]

/-- The inverse form of `homEquiv_comp_rightAdjointUniq_hom`. -/
private theorem homEquiv_comp_rightAdjointUniq_inv {L : A ⥤ B} {R R' : B ⥤ A}
    (adj : L ⊣ R) (adj' : L ⊣ R') {X : A} {Y : B} (g : L.obj X ⟶ Y) :
    adj'.homEquiv X Y g ≫ (Adjunction.rightAdjointUniq adj adj').inv.app Y =
      adj.homEquiv X Y g := by
  rw [← homEquiv_comp_rightAdjointUniq_hom adj adj' g, Category.assoc, Iso.hom_inv_id_app,
    Category.comp_id]

/-- Transposing along the identity adjunction does nothing. -/
private theorem homEquiv_id_apply {X Y : A} (g : X ⟶ Y) :
    (Adjunction.id (C := A)).homEquiv X Y g = g := by
  rw [Adjunction.homEquiv_unit]
  simp

end AdjunctionComparisons

section DirectImageComparisons

/-- The comparison attached to a reflexivity proof is the identity. -/
private theorem cocontinuousPushforwardIsoOfEq_rfl {Cc : Type u} [Category.{u} Cc]
    {Dd : Type u} [Category.{u} Dd] (J : GrothendieckTopology Cc) (K : GrothendieckTopology Dd)
    {P : Cc ⥤ Dd} [P.IsCocontinuous J K] :
    cocontinuousPushforwardIsoOfEq J K (rfl : P = P) = Iso.refl _ := rfl

/-- Transposing along a Kan-extension adjunction and then transporting the direct image along
an equality of site functors is transposing the transported map. -/
private theorem homEquiv_comp_cocontinuousPushforwardIsoOfEq {Cc : Type u} [Category.{u} Cc]
    {Dd : Type u} [Category.{u} Dd] (J : GrothendieckTopology Cc) (K : GrothendieckTopology Dd)
    {P Q : Cc ⥤ Dd} (h : P = Q) [P.IsCocontinuous J K] [Q.IsCocontinuous J K]
    (Aa : Ddᵒᵖ ⥤ Type u) (Y : Sheaf J (Type u)) (σ : P.op ⋙ Aa ⟶ Y.obj) :
    (P.op.ranAdjunction (Type u)).homEquiv Aa Y.obj σ ≫
        ((cocontinuousPushforwardIsoOfEq J K h).hom.app Y).hom =
      (Q.op.ranAdjunction (Type u)).homEquiv Aa Y.obj (eqToHom (by subst h; rfl) ≫ σ) := by
  cases h
  rw [cocontinuousPushforwardIsoOfEq_rfl, eqToHom_refl, Category.id_comp]
  exact Category.comp_id _

/-- On underlying presheaves, the direct-image compositor of two cocontinuous site functors is
the right Kan extension compositor. -/
private theorem sheafPushforwardCocontinuousCompIso_inv_app_hom
    {Cc : Type u} [SmallCategory Cc] {Dd : Type u} [SmallCategory Dd]
    {Ee : Type u} [SmallCategory Ee] (J : GrothendieckTopology Cc)
    (K : GrothendieckTopology Dd) (L : GrothendieckTopology Ee)
    (a : Cc ⥤ Dd) (b : Dd ⥤ Ee) [a.IsCocontinuous J K] [b.IsCocontinuous K L]
    (X : Sheaf J (Type u)) :
    ((sheafPushforwardCocontinuousCompIso J K L a b).inv.app X).hom =
      (ranOpCompIso a b).inv.app X.obj :=
  (sheafToPresheaf L (Type u)).map_preimage _

/-- The unit law for a direct-image transition that is a Kan-extension transpose: if the
transposed map is the canonical identification, then the transition is inverse to the canonical
identification of the direct image along the identity site functor with the identity. -/
private theorem transpose_comp_pushforwardId {Cc : Type u} [Category.{u} Cc]
    (J : GrothendieckTopology Cc) {w : Cc ⥤ Cc} (hw : w = 𝟭 Cc) [w.IsCocontinuous J J]
    (X : Sheaf J (Type u)) (T : X ⟶ (w.sheafPushforwardCocontinuous (Type u) J J).obj X)
    (σ : w.op ⋙ X.obj ⟶ X.obj)
    (hT : T.hom = (w.op.ranAdjunction (Type u)).homEquiv X.obj X.obj σ)
    (hσ : σ = eqToHom (show w.op ⋙ X.obj = X.obj by subst hw; rfl)) :
    T ≫ (cocontinuousPushforwardIsoOfEq J J hw ≪≫
        Adjunction.rightAdjointUniq
          (((𝟭 Cc).sheafAdjunctionCocontinuous (Type u) J J).ofNatIsoLeft
            (Functor.sheafPushforwardContinuousId (Type u) J))
          Adjunction.id).hom.app X = 𝟙 X := by
  set adjX := ((𝟭 Cc).sheafAdjunctionCocontinuous (Type u) J J).ofNatIsoLeft
    (Functor.sheafPushforwardContinuousId (Type u) J) with hadjX
  have step : T ≫ (cocontinuousPushforwardIsoOfEq J J hw).hom.app X =
      adjX.homEquiv X X (𝟙 X) := by
    refine Sheaf.hom_ext ?_
    refine Eq.trans (congrArg
      (fun t => t ≫ ((cocontinuousPushforwardIsoOfEq J J hw).hom.app X).hom) hT) ?_
    refine Eq.trans (homEquiv_comp_cocontinuousPushforwardIsoOfEq J J hw X.obj X σ) ?_
    rw [hσ, eqToHom_trans, hadjX, Adjunction.homEquiv_ofNatIsoLeft_apply,
      Functor.sheafAdjunctionCocontinuous_homEquiv_apply_hom]
    congr 1
  rw [Iso.trans_hom, NatTrans.comp_app, ← Category.assoc, step,
    homEquiv_comp_rightAdjointUniq_hom, homEquiv_id_apply]

/-- The cocycle law for direct-image transitions that are Kan-extension transposes: if the
transposed maps satisfy the cocycle law for the Cartesian lifts, then the transitions compose to
the transition of the composite, compared by the direct-image compositor. -/
private theorem transpose_comp_pushforwardCompSymm
    {Cl : Type u} [SmallCategory Cl] {Cm : Type u} [SmallCategory Cm]
    {Cn : Type u} [SmallCategory Cn] (Jl : GrothendieckTopology Cl)
    (Jm : GrothendieckTopology Cm) (Jn : GrothendieckTopology Cn)
    {wφ : Cn ⥤ Cm} {wψ : Cm ⥤ Cl} {wc : Cn ⥤ Cl} (h : wφ ⋙ wψ = wc)
    [wφ.IsCocontinuous Jn Jm] [wψ.IsCocontinuous Jm Jl] [wc.IsCocontinuous Jn Jl]
    [(wφ ⋙ wψ).IsCocontinuous Jn Jl]
    (Xl : Sheaf Jl (Type u)) (Xm : Sheaf Jm (Type u)) (Xn : Sheaf Jn (Type u))
    (σψ : wψ.op ⋙ Xl.obj ⟶ Xm.obj) (σφ : wφ.op ⋙ Xm.obj ⟶ Xn.obj)
    (σc : wc.op ⋙ Xl.obj ⟶ Xn.obj)
    (hσ : eqToHom (show wc.op ⋙ Xl.obj = wφ.op ⋙ wψ.op ⋙ Xl.obj by subst h; rfl) ≫
      (Functor.whiskerLeft wφ.op σψ ≫ σφ) = σc) :
    (⟨(wψ.op.ranAdjunction (Type u)).homEquiv Xl.obj Xm.obj σψ⟩ :
          Xl ⟶ (wψ.sheafPushforwardCocontinuous (Type u) Jm Jl).obj Xm) ≫
        (wψ.sheafPushforwardCocontinuous (Type u) Jm Jl).map
          (⟨(wφ.op.ranAdjunction (Type u)).homEquiv Xm.obj Xn.obj σφ⟩ :
            Xm ⟶ (wφ.sheafPushforwardCocontinuous (Type u) Jn Jm).obj Xn) ≫
        ((sheafPushforwardCocontinuousCompIso Jn Jm Jl wφ wψ).symm ≪≫
          cocontinuousPushforwardIsoOfEq Jn Jl h).hom.app Xn =
      (⟨(wc.op.ranAdjunction (Type u)).homEquiv Xl.obj Xn.obj σc⟩ :
        Xl ⟶ (wc.sheafPushforwardCocontinuous (Type u) Jn Jl).obj Xn) := by
  refine Sheaf.hom_ext ?_
  have hpair : (wψ.op.ranAdjunction (Type u)).homEquiv Xl.obj Xm.obj σψ ≫
      wψ.op.ran.map ((wφ.op.ranAdjunction (Type u)).homEquiv Xm.obj Xn.obj σφ) =
      ((wψ.op.ranAdjunction (Type u)).comp (wφ.op.ranAdjunction (Type u))).homEquiv
        Xl.obj Xn.obj (Functor.whiskerLeft wφ.op σψ ≫ σφ) :=
    ((Adjunction.homEquiv_naturality_right (wψ.op.ranAdjunction (Type u)) σψ
        ((wφ.op.ranAdjunction (Type u)).homEquiv Xm.obj Xn.obj σφ)).symm.trans
      (congrArg ((wψ.op.ranAdjunction (Type u)).homEquiv Xl.obj _)
        (Adjunction.homEquiv_naturality_left (wφ.op.ranAdjunction (Type u)) σψ σφ).symm)).trans
      (Adjunction.comp_homEquiv_apply (wψ.op.ranAdjunction (Type u)) (wφ.op.ranAdjunction (Type u))
        (Functor.whiskerLeft wφ.op σψ ≫ σφ)).symm
  have hcompositor : ((wψ.op.ranAdjunction (Type u)).comp
        (wφ.op.ranAdjunction (Type u))).homEquiv Xl.obj Xn.obj
          (Functor.whiskerLeft wφ.op σψ ≫ σφ) ≫
        (ranOpCompIso wφ wψ).inv.app Xn.obj =
      ((wφ.op ⋙ wψ.op).ranAdjunction (Type u)).homEquiv Xl.obj Xn.obj
        (Functor.whiskerLeft wφ.op σψ ≫ σφ) := by
    rw [ranOpCompIso_def]
    exact homEquiv_comp_rightAdjointUniq_inv _ _ _
  have hmain : (((wψ.op.ranAdjunction (Type u)).homEquiv Xl.obj Xm.obj σψ ≫
            wψ.op.ran.map ((wφ.op.ranAdjunction (Type u)).homEquiv Xm.obj Xn.obj σφ)) ≫
          (ranOpCompIso wφ wψ).inv.app Xn.obj) ≫
        ((cocontinuousPushforwardIsoOfEq Jn Jl h).hom.app Xn).hom =
      (wc.op.ranAdjunction (Type u)).homEquiv Xl.obj Xn.obj σc :=
    (congrArg (fun t => t ≫ ((cocontinuousPushforwardIsoOfEq Jn Jl h).hom.app Xn).hom)
        ((congrArg (fun t => t ≫ (ranOpCompIso wφ wψ).inv.app Xn.obj) hpair).trans
          hcompositor)).trans
      ((homEquiv_comp_cocontinuousPushforwardIsoOfEq Jn Jl h Xl.obj Xn
          (Functor.whiskerLeft wφ.op σψ ≫ σφ)).trans
        (congrArg ((wc.op.ranAdjunction (Type u)).homEquiv Xl.obj Xn.obj) hσ))
  refine Eq.trans ?_ hmain
  refine Eq.trans (congrArg (fun t =>
    (wψ.op.ranAdjunction (Type u)).homEquiv Xl.obj Xm.obj σψ ≫
      (wψ.op.ran.map ((wφ.op.ranAdjunction (Type u)).homEquiv Xm.obj Xn.obj σφ) ≫
        (t ≫ ((cocontinuousPushforwardIsoOfEq Jn Jl h).hom.app Xn).hom)))
    (sheafPushforwardCocontinuousCompIso_inv_app_hom Jn Jm Jl wφ wψ Xn)) ?_
  exact ((Category.assoc _ _ _).trans (Category.assoc _ _ _)).symm

end DirectImageComparisons

section CaseA

variable (C : SimplicialSite.{u})

/-- The unit law for the direct-image transition, case (A), on sections. -/
private theorem restrictTransition_inl_id (n : SimplexCategory)
    (F : Sheaf (totalTopology ⟨Sum.inl C⟩) (Type u)) (V : C.underlying.obj n) :
    ((restrictTransition ⟨Sum.inl C⟩ (𝟙 n)).app F).hom.app (op V) ≫
        ((pushforwardId ⟨Sum.inl C⟩ n).hom.app
          ((restrict ⟨Sum.inl C⟩ n).obj F)).hom.app (op V) =
      𝟙 (F.obj.obj (op ((CoGrothendieck.ι C.totalPseudofunctor (op n)).obj V))) := by
  let eI : (C.underlying.map (𝟙 n)).toFunctor ≅ 𝟭 (C.underlying.obj n) :=
    eqToIso (congrArg Cat.Hom.toFunctor (C.underlying.map_id n))
  have h1 : 𝟙 ((CoGrothendieck.ι C.totalPseudofunctor (op n)).obj V) =
      ⟨(𝟙 n).op, eI.inv.app V⟩ := by
    refine CoGrothendieck.Hom.ext _ _ rfl ?_
    show (C.totalPseudofunctor.mapId ⟨op (op n)⟩).inv.toNatTrans.app V = _
    simp [eI, SimplicialSite.totalPseudofunctor]
  refine (restrictTransition_inl_arrow C (𝟙 n) F (eI.inv.app V)).trans ?_
  rw [← h1]
  exact F.obj.map_id _

/-- The cocycle law for the direct-image transition, case (A), on sections. -/
private theorem restrictTransition_inl_comp {l m n : SimplexCategory} (ψ : l ⟶ m) (φ : m ⟶ n)
    (F : Sheaf (totalTopology ⟨Sum.inl C⟩) (Type u)) (V : C.underlying.obj l) :
    ((restrictTransition ⟨Sum.inl C⟩ ψ).app F).hom.app (op V) ≫
        ((transitionMorphism ⟨Sum.inl C⟩ ψ).pushforward.map
          ((restrictTransition ⟨Sum.inl C⟩ φ).app F)).hom.app (op V) ≫
        ((pushforwardCompSymm ⟨Sum.inl C⟩ ψ φ).hom.app
          ((restrict ⟨Sum.inl C⟩ n).obj F)).hom.app (op V) =
      ((restrictTransition ⟨Sum.inl C⟩ (ψ ≫ φ)).app F).hom.app (op V) := by
  let eC : (C.underlying.map ψ).toFunctor ⋙ (C.underlying.map φ).toFunctor ≅
      (C.underlying.map (ψ ≫ φ)).toFunctor :=
    eqToIso (congrArg Cat.Hom.toFunctor (C.underlying.map_comp ψ φ)).symm
  have he : eC.inv.app V =
      (C.totalPseudofunctor.mapComp ψ.op.op.toLoc φ.op.op.toLoc).hom.toNatTrans.app V := by
    simp [eC, SimplicialSite.totalPseudofunctor, Functor.toPseudofunctor'_mapComp,
      Cat.Hom₂.eqToHom_toNatTrans, eqToHom_app]
  have hcomp : (CoGrothendieck.ι C.totalPseudofunctor (op n)).map (eC.inv.app V) ≫
      (CoGrothendieck.ιNatTrans C.totalPseudofunctor φ.op).app
        ((C.underlying.map ψ).toFunctor.obj V) ≫
      (CoGrothendieck.ιNatTrans C.totalPseudofunctor ψ.op).app V =
      (CoGrothendieck.ιNatTrans C.totalPseudofunctor (ψ ≫ φ).op).app V := by
    rw [he]
    exact CoGrothendieck.ιNatTrans_app_comp_ιNatTrans_app C.totalPseudofunctor φ.op ψ.op V
  have hA : ((restrictTransition ⟨Sum.inl C⟩ ψ).app F).hom.app (op V) =
      F.obj.map ((CoGrothendieck.ιNatTrans C.totalPseudofunctor ψ.op).app V).op := rfl
  have h3 : F.obj.map (Quiver.Hom.op
        ((CoGrothendieck.ιNatTrans C.totalPseudofunctor ψ.op).app V)) ≫
      F.obj.map (Quiver.Hom.op
        ((CoGrothendieck.ι C.totalPseudofunctor (op n)).map (eC.inv.app V) ≫
          (CoGrothendieck.ιNatTrans C.totalPseudofunctor φ.op).app
            ((C.underlying.map ψ).toFunctor.obj V))) =
      F.obj.map (Quiver.Hom.op
        (((CoGrothendieck.ι C.totalPseudofunctor (op n)).map (eC.inv.app V) ≫
            (CoGrothendieck.ιNatTrans C.totalPseudofunctor φ.op).app
              ((C.underlying.map ψ).toFunctor.obj V)) ≫
          (CoGrothendieck.ιNatTrans C.totalPseudofunctor ψ.op).app V)) :=
    (F.obj.map_comp _ _).symm
  refine Eq.trans (congrArg (fun t =>
    ((restrictTransition ⟨Sum.inl C⟩ ψ).app F).hom.app (op V) ≫ t)
      (restrictTransition_inl_arrow C φ F (eC.inv.app V))) ?_
  rw [hA, ← CoGrothendieck.ι_map_comp_ιNatTrans_app C.totalPseudofunctor φ.op (eC.inv.app V)]
  exact h3.trans (congrArg (fun k => F.obj.map (Quiver.Hom.op k))
    ((Category.assoc _ _ _).trans hcomp))

end CaseA

section CaseB

variable (C : CocontinuousSimplicialSite.{u})

/-- The unit law for the direct-image transition, case (B). -/
private theorem restrictTransition_inr_id (n : SimplexCategory)
    (F : Sheaf (totalTopology ⟨Sum.inr C⟩) (Type u)) :
    (restrictTransition ⟨Sum.inr C⟩ (𝟙 n)).app F ≫
        (pushforwardId ⟨Sum.inr C⟩ n).hom.app ((restrict ⟨Sum.inr C⟩ n).obj F) =
      𝟙 ((restrict ⟨Sum.inr C⟩ n).obj F) :=
  @transpose_comp_pushforwardId _ _ (componentTopology ⟨Sum.inr C⟩ n) _
    (show (C.underlying.map (𝟙 n).op).toFunctor = 𝟭 _ from
      congrArg Cat.Hom.toFunctor (C.underlying.map_id (op n)))
    (C.isCocontinuous (𝟙 n).op) ((restrict ⟨Sum.inr C⟩ n).obj F) _
    (whiskerRight (NatTrans.op (Grothendieck.ιNatTrans (F := C.underlying) (𝟙 n).op)) F.obj)
    rfl (Grothendieck.whiskerRight_op_ιNatTrans_id (op n) F.obj)

/-- The cocycle law for the direct-image transition, case (B). -/
private theorem restrictTransition_inr_comp {l m n : SimplexCategory} (ψ : l ⟶ m) (φ : m ⟶ n)
    (F : Sheaf (totalTopology ⟨Sum.inr C⟩) (Type u)) :
    (restrictTransition ⟨Sum.inr C⟩ ψ).app F ≫
        (transitionMorphism ⟨Sum.inr C⟩ ψ).pushforward.map
          ((restrictTransition ⟨Sum.inr C⟩ φ).app F) ≫
        (pushforwardCompSymm ⟨Sum.inr C⟩ ψ φ).hom.app ((restrict ⟨Sum.inr C⟩ n).obj F) =
      (restrictTransition ⟨Sum.inr C⟩ (ψ ≫ φ)).app F :=
  @transpose_comp_pushforwardCompSymm _ _ _ _ _ _
    (componentTopology ⟨Sum.inr C⟩ l) (componentTopology ⟨Sum.inr C⟩ m)
    (componentTopology ⟨Sum.inr C⟩ n) _ _ _
    (congrArg Cat.Hom.toFunctor (C.underlying.map_comp φ.op ψ.op)).symm
    (C.isCocontinuous φ.op) (C.isCocontinuous ψ.op) (C.isCocontinuous (ψ ≫ φ).op)
    (@CategoryTheory.isCocontinuous_comp _ _ _ _ _ _ _ _
      (componentTopology ⟨Sum.inr C⟩ n) (componentTopology ⟨Sum.inr C⟩ m) _
      (C.isCocontinuous φ.op) (C.isCocontinuous ψ.op))
    ((restrict ⟨Sum.inr C⟩ l).obj F) ((restrict ⟨Sum.inr C⟩ m).obj F)
    ((restrict ⟨Sum.inr C⟩ n).obj F)
    (whiskerRight (NatTrans.op (Grothendieck.ιNatTrans (F := C.underlying) ψ.op)) F.obj)
    (whiskerRight (NatTrans.op (Grothendieck.ιNatTrans (F := C.underlying) φ.op)) F.obj)
    (whiskerRight (NatTrans.op (Grothendieck.ιNatTrans (F := C.underlying) (ψ ≫ φ).op)) F.obj)
    (Grothendieck.whiskerRight_op_ιNatTrans_comp φ.op ψ.op F.obj)

end CaseB

variable (S : SimplicialSiteSituation.{u})

/-- The unit law for the direct-image transition: the transition attached to an identity simplex
map is inverse to the canonical identification of the direct image along `f_𝟙` with the
identity. -/
theorem restrictTransition_id (n : SimplexCategory) (F : Sheaf S.totalTopology (Type u)) :
    (S.restrictTransition (𝟙 n)).app F ≫ (S.pushforwardId n).hom.app ((S.restrict n).obj F) =
      𝟙 ((S.restrict n).obj F) := by
  rcases S with ⟨C | C⟩
  · exact Sheaf.hom_ext (NatTrans.ext (funext fun V => restrictTransition_inl_id C n F V.unop))
  · exact restrictTransition_inr_id C n F

/-- The cocycle law for the direct-image transition: the transition attached to a composite
simplex map is the composite of the two transitions, compared by the canonical direct-image
compositor. -/
theorem restrictTransition_comp {l m n : SimplexCategory} (ψ : l ⟶ m) (φ : m ⟶ n)
    (F : Sheaf S.totalTopology (Type u)) :
    (S.restrictTransition ψ).app F ≫
        (S.transitionMorphism ψ).pushforward.map ((S.restrictTransition φ).app F) ≫
        (S.pushforwardCompSymm ψ φ).hom.app ((S.restrict n).obj F) =
      (S.restrictTransition (ψ ≫ φ)).app F := by
  rcases S with ⟨C | C⟩
  · exact Sheaf.hom_ext (NatTrans.ext (funext fun V => restrictTransition_inl_comp C ψ φ F V.unop))
  · exact restrictTransition_inr_comp C ψ φ F

/-- Transposing a composite whose first factor compares two left adjoints of one functor. -/
private theorem homEquiv_leftAdjointUniq_comp {A : Type u₁} [Category.{v₁} A] {B : Type u₂}
    [Category.{v₂} B] {P P' : A ⥤ B} {Q : B ⥤ A} (adj : P ⊣ Q) (adj' : P' ⊣ Q) {X : A} {Y : B}
    (g : P'.obj X ⟶ Y) :
    adj.homEquiv X Y ((Adjunction.leftAdjointUniq adj adj').hom.app X ≫ g) =
      adj'.homEquiv X Y g := by
  rw [Adjunction.homEquiv_unit, Functor.map_comp, ← Category.assoc,
    Adjunction.unit_leftAdjointUniq_hom_app, ← Adjunction.homEquiv_unit]

/-- The unit law for the inverse-image transition: the transition attached to an identity simplex
map is the canonical identification of `f_𝟙⁻¹` with the identity. -/
theorem fiberTransition_id (n : SimplexCategory) (F : Sheaf S.totalTopology (Type u)) :
    (fiberTransition S (𝟙 n)).app F =
      (canonicalIdentityComparison S n).hom.app ((S.restrict n).obj F) := by
  have hR := Adjunction.homEquiv_leftAdjointUniq_hom_app
    ((S.transitionMorphism (𝟙 n)).adj.ofNatIsoRight (S.pushforwardId n))
    (Adjunction.id (C := Sheaf (S.componentTopology n) (Type u))) ((S.restrict n).obj F)
  refine (((S.transitionMorphism (𝟙 n)).adj.ofNatIsoRight
    (S.pushforwardId n)).homEquiv _ _).injective (Eq.trans ?_ hR.symm)
  rw [Adjunction.homEquiv_ofNatIsoRight_apply, fiberTransition_adj]
  simpa using S.restrictTransition_id n F

/-- The cocycle law for the inverse-image transition: the transition attached to a composite
simplex map is the composite of the two transitions, compared by the canonical inverse-image
compositor. -/
theorem fiberTransition_comp {l m n : SimplexCategory} (ψ : l ⟶ m) (φ : m ⟶ n)
    (F : Sheaf S.totalTopology (Type u)) :
    (fiberTransition S (ψ ≫ φ)).app F =
      (canonicalCompositionComparison S ψ φ).hom.app ((S.restrict l).obj F) ≫
        (S.transitionMorphism φ).inverseImage.map ((fiberTransition S ψ).app F) ≫
          (fiberTransition S φ).app F := by
  have h := homEquiv_leftAdjointUniq_comp (S.transitionMorphism (ψ ≫ φ)).adj
    (((S.transitionMorphism ψ).adj.comp (S.transitionMorphism φ).adj).ofNatIsoRight
      (S.pushforwardCompSymm ψ φ))
    ((S.transitionMorphism φ).inverseImage.map ((fiberTransition S ψ).app F) ≫
      (fiberTransition S φ).app F)
  refine ((S.transitionMorphism (ψ ≫ φ)).adj.homEquiv _ _).injective ?_
  rw [fiberTransition_adj]
  refine Eq.symm (h.trans ?_)
  rw [Adjunction.homEquiv_ofNatIsoRight_apply]
  simp only [Adjunction.comp_homEquiv, Equiv.trans_apply]
  rw [Adjunction.homEquiv_naturality_left, Adjunction.homEquiv_naturality_right,
    fiberTransition_adj, fiberTransition_adj]
  exact S.restrictTransition_comp ψ φ F

end CategoryTheory.SimplicialSiteSituation

end
