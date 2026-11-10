module

public import StacksFrontier.AlgebraicGeometry.Spaces.Groupoids.GroupSpaces.TorsorsForIsomSheaf

/-!
# Changing the acting group of a torsor along an isomorphism

Let `T = (U, b, X)` be a torsor under the base change `G_U = U ×_{b, B} G` of a group algebraic
space `G` over `B`, trivialized by a family satisfying a covering property `P`.  Given a second
group algebraic space `G'` over `B'`, a morphism `b' : U ⟶ B'` and an isomorphism of group
objects `U ×_{b', B'} G' ≅ U ×_{b, B} G`, the action of `G_U` on `X` transported along that
isomorphism makes `(U, b', X)` a torsor under `G'_U` trivialized by the same family.  This is
`AlgebraicGeometry.Space.TorsorsFor.changeGroup`.

The case of interest is the comparison between a group algebraic space `G` over `B` and its base
change `H = U ×_{b, B} G` along a morphism `b : U ⟶ B` from an object of the site: for every
`s : V ⟶ U` the two groups `V ×_{s ∘ b, B} G` and `V ×_{s, U} H` are canonically isomorphic,
by `AlgebraicGeometry.Space.groupCompIso`.  So a torsor under `H` over `V` is the same thing as a
torsor under `G` over `V` whose section of `B` factors through `b`, and a morphism of torsors is
the same pair of underlying morphisms on either side.

## Main definitions

* `AlgebraicGeometry.Space.TorsorsFor.changeGroup`: the torsor with the transported action.
* `AlgebraicGeometry.Space.groupCompIso`: the isomorphism `V ×_{s ∘ b, B} G ≅ V ×_{s, U} H` of
  group algebraic spaces over `V`.

## Main results

* `AlgebraicGeometry.Space.TorsorsFor.actionMap_changeGroup`: the transported action is the old
  one precomposed with the isomorphism on the group factor.
* `AlgebraicGeometry.Space.groupCompIso_hom_fst_fst` and
  `AlgebraicGeometry.Space.groupCompIso_hom_snd`: the components of `groupCompIso`.
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits
open scoped MonoidalCategory MonObj

universe u

namespace AlgebraicGeometry.Space

variable {𝒞 : BigFppfSite.{u}} {S : Scheme.{u}} {hS : 𝒞.Contains S}
  {B B' : (BigFppfOver 𝒞 S hS)ᵒᵖ ⥤ Type u} {hB : IsAlgebraicSpace 𝒞 S hS B}
  {hB' : IsAlgebraicSpace 𝒞 S hS B'}
  {G : GroupAlgebraicSpace 𝒞 S hS B hB} {G' : GroupAlgebraicSpace 𝒞 S hS B' hB'}
  {P : CoveringPredicate 𝒞 S hS}

/-- Transporting an action along an isomorphism of monoid objects preserves the pseudo-torsor
condition: the shear map of the transported action is the old one precomposed with the
isomorphism on the group factor. -/
theorem isPseudoTorsor_ofIso_symm {E : Type*} [Category E] [CartesianMonoidalCategory E]
    {R R' M : E} [GrpObj R] [GrpObj R'] [ModObj R M] (e : R' ≅ R) [IsMonHom e.symm.hom]
    (h : AlgebraicGeometry.IsPseudoTorsor R M) :
    letI := ModObj.ofIso e.symm (Iso.refl M)
    AlgebraicGeometry.IsPseudoTorsor R' M := by
  let := ModObj.ofIso e.symm (Iso.refl M)
  have : IsIso (ModObj.leftSMul R M) := h
  have hs : ModObj.leftSMul R' M = (e.hom ▷ M) ≫ ModObj.leftSMul R M := by
    apply CartesianMonoidalCategory.hom_ext
    · simp only [ModObj.leftSMul_fst, Category.assoc]
      change (e.hom ⊗ₘ 𝟙 M) ≫ γ[R, M] ≫ 𝟙 M = (e.hom ▷ M) ≫ γ[R, M]
      simp
    · simp
  change IsIso (ModObj.leftSMul R' M)
  rw [hs]
  infer_instance

namespace TorsorsFor

/-- The isomorphism of underlying objects of an isomorphism of acting groups. -/
abbrev groupIsoX {V : BigFppfOver 𝒞 S hS} {σ : yoneda.obj V ⟶ B'} {τ : yoneda.obj V ⟶ B}
    (e : (fppfPullbackGroup hB' G' V σ).obj ≅ (fppfPullbackGroup hB G V τ).obj) :
    (fppfPullbackGroup hB' G' V σ).obj.X ≅ (fppfPullbackGroup hB G V τ).obj.X :=
  (Grp.forget _).mapIso e

variable (P) in
/-- The torsor `(U, b', X)` under `U ×_{b', B'} G'` obtained from a torsor `(U, b, X)` under
`U ×_{b, B} G` by transporting its action along an isomorphism of the two acting groups. It is
trivialized by the same family as `(U, b, X)`. -/
@[implicit_reducible]
def changeGroup (T : TorsorsFor hB G P) (σ : yoneda.obj T.base ⟶ B')
    (e : (fppfPullbackGroup hB' G' T.base σ).obj ≅ (fppfPullbackGroup hB G T.base T.sec).obj) :
    TorsorsFor hB' G' P where
  base := T.base
  sec := σ
  total := T.total
  isAlgebraicSpace := T.isAlgebraicSpace
  action :=
    letI : IsMonHom (groupIsoX e).symm.hom := e.inv.hom.isMonHom_hom
    ModObj.ofIso (groupIsoX e).symm (Iso.refl _)
  isTorsor :=
    letI : IsMonHom (groupIsoX e).symm.hom := e.inv.hom.isMonHom_hom
    ⟨isPseudoTorsor_ofIso_symm (groupIsoX e) T.isPseudoTorsor, T.isTorsor.2⟩

/-- The base of `changeGroup P T σ e` is the base of `T`. -/
@[simp]
theorem changeGroup_base (T : TorsorsFor hB G P) (σ : yoneda.obj T.base ⟶ B')
    (e : (fppfPullbackGroup hB' G' T.base σ).obj ≅ (fppfPullbackGroup hB G T.base T.sec).obj) :
    (changeGroup P T σ e).base = T.base :=
  rfl

/-- The section of `B'` of `changeGroup P T σ e` is `σ`. -/
@[simp]
theorem changeGroup_sec (T : TorsorsFor hB G P) (σ : yoneda.obj T.base ⟶ B')
    (e : (fppfPullbackGroup hB' G' T.base σ).obj ≅ (fppfPullbackGroup hB G T.base T.sec).obj) :
    (changeGroup P T σ e).sec = σ :=
  rfl

/-- The total space of `changeGroup P T σ e` is the total space of `T`. -/
@[simp]
theorem changeGroup_total (T : TorsorsFor hB G P) (σ : yoneda.obj T.base ⟶ B')
    (e : (fppfPullbackGroup hB' G' T.base σ).obj ≅ (fppfPullbackGroup hB G T.base T.sec).obj) :
    (changeGroup P T σ e).total = T.total :=
  rfl

/-- The action of `changeGroup` is the old action precomposed with the isomorphism of the acting
groups on the group factor. -/
theorem actionMap_changeGroup (T : TorsorsFor hB G P) (σ : yoneda.obj T.base ⟶ B')
    (e : (fppfPullbackGroup hB' G' T.base σ).obj ≅ (fppfPullbackGroup hB G T.base T.sec).obj) :
    actionMap (changeGroup P T σ e) = (e.hom.hom.hom ▷ T.total).left ≫ actionMap T := by
  change ((e.hom.hom.hom ⊗ₘ 𝟙 T.total) ≫ γ[T.group, T.total] ≫ 𝟙 T.total).left = _
  simp

/-- A morphism of total spaces lying over a morphism of bases is equivariant for the transported
actions as soon as it is equivariant for the old ones and the isomorphisms of the acting groups
commute with base change. -/
theorem smul_comp_changeGroup {T₁ T₂ : TorsorsFor hB G P}
    {σ₁ : yoneda.obj T₁.base ⟶ B'} {σ₂ : yoneda.obj T₂.base ⟶ B'}
    (e₁ : (fppfPullbackGroup hB' G' T₁.base σ₁).obj ≅
      (fppfPullbackGroup hB G T₁.base T₁.sec).obj)
    (e₂ : (fppfPullbackGroup hB' G' T₂.base σ₂).obj ≅
      (fppfPullbackGroup hB G T₂.base T₂.sec).obj)
    (f : T₁.base ⟶ T₂.base) (hf : yoneda.map f ≫ T₂.sec = T₁.sec)
    (hσ : yoneda.map f ≫ σ₂ = σ₁) (m : T₁.total.left ⟶ T₂.total.left)
    (hm : T₁.total.hom ≫ yoneda.map f = m ≫ T₂.total.hom)
    (hsm : actionMap T₁ ≫ m = actionBaseChange f hf m hm ≫ actionMap T₂)
    (he : e₁.hom.hom.hom.left ≫ groupBaseChange (T := T₁) (T' := T₂) f hf =
      groupBaseChange (T := changeGroup P T₁ σ₁ e₁) (T' := changeGroup P T₂ σ₂ e₂) f hσ ≫
        e₂.hom.hom.hom.left) :
    actionMap (changeGroup P T₁ σ₁ e₁) ≫ m =
      actionBaseChange (T := changeGroup P T₁ σ₁ e₁) (T' := changeGroup P T₂ σ₂ e₂) f hσ m hm ≫
        actionMap (changeGroup P T₂ σ₂ e₂) := by
  let w₁ : pullback (pullback.snd G'.obj.X.hom σ₁) T₁.total.hom ⟶
      pullback (pullback.snd G.obj.X.hom T₁.sec) T₁.total.hom :=
    pullback.map _ _ _ _ e₁.hom.hom.hom.left (𝟙 _) (𝟙 _)
      (by rw [Category.comp_id]; exact (Over.w e₁.hom.hom.hom).symm) (by simp)
  let w₂ : pullback (pullback.snd G'.obj.X.hom σ₂) T₂.total.hom ⟶
      pullback (pullback.snd G.obj.X.hom T₂.sec) T₂.total.hom :=
    pullback.map _ _ _ _ e₂.hom.hom.hom.left (𝟙 _) (𝟙 _)
      (by rw [Category.comp_id]; exact (Over.w e₂.hom.hom.hom).symm) (by simp)
  have hw₁ : (e₁.hom.hom.hom ▷ T₁.total).left = w₁ := rfl
  have hw₂ : (e₂.hom.hom.hom ▷ T₂.total).left = w₂ := rfl
  have key : w₁ ≫ actionBaseChange f hf m hm =
      actionBaseChange (T := changeGroup P T₁ σ₁ e₁) (T' := changeGroup P T₂ σ₂ e₂) f hσ m hm ≫
        w₂ := by
    have m₁f : w₁ ≫ pullback.fst _ _ =
        pullback.fst (pullback.snd G'.obj.X.hom σ₁) T₁.total.hom ≫ e₁.hom.hom.hom.left :=
      pullback.lift_fst _ _ _
    have m₂f : w₂ ≫ pullback.fst _ _ =
        pullback.fst (pullback.snd G'.obj.X.hom σ₂) T₂.total.hom ≫ e₂.hom.hom.hom.left :=
      pullback.lift_fst _ _ _
    have m₁s : w₁ ≫ pullback.snd _ _ =
        pullback.snd (pullback.snd G'.obj.X.hom σ₁) T₁.total.hom :=
      (pullback.lift_snd _ _ _).trans (Category.comp_id _)
    have m₂s : w₂ ≫ pullback.snd _ _ =
        pullback.snd (pullback.snd G'.obj.X.hom σ₂) T₂.total.hom :=
      (pullback.lift_snd _ _ _).trans (Category.comp_id _)
    have a₁f := actionBaseChange_fst f hf m hm
    have a₁s := actionBaseChange_snd f hf m hm
    have a₂f := actionBaseChange_fst (T := changeGroup P T₁ σ₁ e₁)
      (T' := changeGroup P T₂ σ₂ e₂) f hσ m hm
    have a₂s := actionBaseChange_snd (T := changeGroup P T₁ σ₁ e₁)
      (T' := changeGroup P T₂ σ₂ e₂) f hσ m hm
    let abc' := actionBaseChange (T := changeGroup P T₁ σ₁ e₁) (T' := changeGroup P T₂ σ₂ e₂)
      f hσ m hm
    apply pullback.hom_ext
    · have h1 : (w₁ ≫ actionBaseChange f hf m hm) ≫ pullback.fst _ _ =
          (pullback.fst (pullback.snd G'.obj.X.hom σ₁) T₁.total.hom ≫ e₁.hom.hom.hom.left) ≫
            groupBaseChange f hf :=
        (Category.assoc _ _ _).trans ((congrArg (w₁ ≫ ·) a₁f).trans
          ((Category.assoc _ _ _).symm.trans (congrArg (· ≫ groupBaseChange f hf) m₁f)))
      have h2 : (abc' ≫ w₂) ≫ pullback.fst _ _ =
          (pullback.fst (pullback.snd G'.obj.X.hom σ₁) T₁.total.hom ≫
            groupBaseChange (T := changeGroup P T₁ σ₁ e₁) (T' := changeGroup P T₂ σ₂ e₂) f hσ) ≫
              e₂.hom.hom.hom.left :=
        (Category.assoc _ _ _).trans ((congrArg (abc' ≫ ·) m₂f).trans
          ((Category.assoc _ _ _).symm.trans (congrArg (· ≫ e₂.hom.hom.hom.left) a₂f)))
      exact h1.trans ((Category.assoc _ _ _).trans
        ((congrArg (pullback.fst (pullback.snd G'.obj.X.hom σ₁) T₁.total.hom ≫ ·) he).trans
          ((Category.assoc _ _ _).symm.trans h2.symm)))
    · have h1 : (w₁ ≫ actionBaseChange f hf m hm) ≫ pullback.snd _ _ =
          pullback.snd (pullback.snd G'.obj.X.hom σ₁) T₁.total.hom ≫ m :=
        (Category.assoc _ _ _).trans ((congrArg (w₁ ≫ ·) a₁s).trans
          ((Category.assoc _ _ _).symm.trans (congrArg (· ≫ m) m₁s)))
      have h2 : (abc' ≫ w₂) ≫ pullback.snd _ _ =
          pullback.snd (pullback.snd G'.obj.X.hom σ₁) T₁.total.hom ≫ m :=
        (Category.assoc _ _ _).trans ((congrArg (abc' ≫ ·) m₂s).trans a₂s)
      exact h1.trans h2.symm
  have c₁ := actionMap_changeGroup T₁ σ₁ e₁
  have c₂ := actionMap_changeGroup T₂ σ₂ e₂
  exact (congrArg (· ≫ m) c₁).trans ((Category.assoc _ _ _).trans
    ((congrArg ((e₁.hom.hom.hom ▷ T₁.total).left ≫ ·) hsm).trans
      (((Category.assoc _ _ _).symm.trans (congrArg (· ≫ actionMap T₂) (hw₁ ▸ key))).trans
        ((Category.assoc _ _ _).trans (congrArg (actionBaseChange (T := changeGroup P T₁ σ₁ e₁)
          (T' := changeGroup P T₂ σ₂ e₂) f hσ m hm ≫ ·) (hw₂ ▸ c₂.symm))))))

variable (P) in
/-- A morphism between two torsors with changed acting groups, given by a morphism between the
original torsors and a compatibility of the two isomorphisms of acting groups with base change. -/
def changeGroupHom {T₁ T₂ : TorsorsFor hB G P} (φ : T₁ ⟶ T₂)
    {σ₁ : yoneda.obj T₁.base ⟶ B'} {σ₂ : yoneda.obj T₂.base ⟶ B'}
    (e₁ : (fppfPullbackGroup hB' G' T₁.base σ₁).obj ≅
      (fppfPullbackGroup hB G T₁.base T₁.sec).obj)
    (e₂ : (fppfPullbackGroup hB' G' T₂.base σ₂).obj ≅
      (fppfPullbackGroup hB G T₂.base T₂.sec).obj)
    (hσ : yoneda.map (Hom.base (T := T₁) (T' := T₂) φ) ≫ σ₂ = σ₁)
    (he : e₁.hom.hom.hom.left ≫
        groupBaseChange (Hom.base (T := T₁) (T' := T₂) φ) (Hom.comp_sec (T := T₁) (T' := T₂) φ) =
      groupBaseChange (T := changeGroup P T₁ σ₁ e₁) (T' := changeGroup P T₂ σ₂ e₂)
        (Hom.base (T := T₁) (T' := T₂) φ) hσ ≫ e₂.hom.hom.hom.left) :
    changeGroup P T₁ σ₁ e₁ ⟶ changeGroup P T₂ σ₂ e₂ where
  base := Hom.base (T := T₁) (T' := T₂) φ
  comp_sec := hσ
  map := Hom.map (T := T₁) (T' := T₂) φ
  isPullback := Hom.isPullback (T := T₁) (T' := T₂) φ
  smul_comp := smul_comp_changeGroup e₁ e₂ (Hom.base (T := T₁) (T' := T₂) φ)
    (Hom.comp_sec (T := T₁) (T' := T₂) φ) hσ (Hom.map (T := T₁) (T' := T₂) φ)
    (Hom.isPullback (T := T₁) (T' := T₂) φ).w.symm (Hom.smul_comp (T := T₁) (T' := T₂) φ) he

/-- The morphism of bases of `changeGroupHom P φ e₁ e₂ hσ he` is that of `φ`. -/
@[simp]
theorem changeGroupHom_base {T₁ T₂ : TorsorsFor hB G P} (φ : T₁ ⟶ T₂)
    {σ₁ : yoneda.obj T₁.base ⟶ B'} {σ₂ : yoneda.obj T₂.base ⟶ B'}
    (e₁ : (fppfPullbackGroup hB' G' T₁.base σ₁).obj ≅
      (fppfPullbackGroup hB G T₁.base T₁.sec).obj)
    (e₂ : (fppfPullbackGroup hB' G' T₂.base σ₂).obj ≅
      (fppfPullbackGroup hB G T₂.base T₂.sec).obj)
    (hσ : yoneda.map (Hom.base (T := T₁) (T' := T₂) φ) ≫ σ₂ = σ₁) (he) :
    Hom.base (T := changeGroup P T₁ σ₁ e₁) (T' := changeGroup P T₂ σ₂ e₂)
        (changeGroupHom P φ e₁ e₂ hσ he) =
      Hom.base (T := T₁) (T' := T₂) φ :=
  rfl

/-- The morphism of total spaces of `changeGroupHom P φ e₁ e₂ hσ he` is that of `φ`. -/
@[simp]
theorem changeGroupHom_map {T₁ T₂ : TorsorsFor hB G P} (φ : T₁ ⟶ T₂)
    {σ₁ : yoneda.obj T₁.base ⟶ B'} {σ₂ : yoneda.obj T₂.base ⟶ B'}
    (e₁ : (fppfPullbackGroup hB' G' T₁.base σ₁).obj ≅
      (fppfPullbackGroup hB G T₁.base T₁.sec).obj)
    (e₂ : (fppfPullbackGroup hB' G' T₂.base σ₂).obj ≅
      (fppfPullbackGroup hB G T₂.base T₂.sec).obj)
    (hσ : yoneda.map (Hom.base (T := T₁) (T' := T₂) φ) ≫ σ₂ = σ₁) (he) :
    Hom.map (T := changeGroup P T₁ σ₁ e₁) (T' := changeGroup P T₂ σ₂ e₂)
        (changeGroupHom P φ e₁ e₂ hσ he) =
      Hom.map (T := T₁) (T' := T₂) φ :=
  rfl

end TorsorsFor

/-! ### The comparison of the base changes of `G` and of `U ×_{b, B} G` -/

variable (hB G) in
/-- For `b : U ⟶ B` and `s : V ⟶ U`, the base change of `G` along `s ∘ b` and the base change of
`H = U ×_{b, B} G` along `s` are isomorphic group algebraic spaces over `V`, by the associativity
isomorphism of pullbacks. -/
def groupCompIso {U V : BigFppfOver 𝒞 S hS} (b : yoneda.obj U ⟶ B)
    (s : yoneda.obj V ⟶ yoneda.obj U) :
    (fppfPullbackGroup hB G V (s ≫ b)).obj ≅
      (fppfPullbackGroup (isAlgebraicSpace_yoneda 𝒞 S hS U) (fppfPullbackGroup hB G U b) V
        s).obj :=
  (Functor.mapGrpNatIso (Over.pullbackComp s b)).app G.obj ≪≫
    (Functor.mapGrpCompIso (F := Over.pullback b) (G := Over.pullback s)).app G.obj

/-- `groupCompIso` lies over `V`. -/
@[reassoc (attr := simp)]
theorem groupCompIso_hom_snd {U V : BigFppfOver 𝒞 S hS} (b : yoneda.obj U ⟶ B)
    (s : yoneda.obj V ⟶ yoneda.obj U) :
    (groupCompIso hB G b s).hom.hom.hom.left ≫ pullback.snd (pullback.snd G.obj.X.hom b) s =
      pullback.snd G.obj.X.hom (s ≫ b) :=
  Over.w (groupCompIso hB G b s).hom.hom.hom

/-- `groupCompIso` does not move the `G`-component. -/
@[reassoc (attr := simp)]
theorem groupCompIso_hom_fst_fst {U V : BigFppfOver 𝒞 S hS} (b : yoneda.obj U ⟶ B)
    (s : yoneda.obj V ⟶ yoneda.obj U) :
    (groupCompIso hB G b s).hom.hom.hom.left ≫ pullback.fst (pullback.snd G.obj.X.hom b) s ≫
        pullback.fst G.obj.X.hom b = pullback.fst G.obj.X.hom (s ≫ b) := by
  have e : (groupCompIso hB G b s).hom.hom.hom.left =
      ((Over.pullbackComp s b).hom.app G.obj.X).left := by
    change (((Over.pullbackComp s b).hom.app G.obj.X) ≫ 𝟙 _).left = _
    rw [Category.comp_id]
  have key : ∀ A : Over B, ((Over.pullbackComp s b).hom.app A).left ≫
      pullback.fst (pullback.snd A.hom b) s ≫ pullback.fst A.hom b =
        pullback.fst A.hom (s ≫ b) := by
    intro A
    have h := congrArg Over.Hom.left (conjugateEquiv_counit
      (Over.mapPullbackAdj (s ≫ b)) ((Over.mapPullbackAdj s).comp (Over.mapPullbackAdj b))
        (Over.mapComp s b).inv A)
    simp [Over.pullbackComp, conjugateIsoEquiv, Over.mapPullbackAdj_counit_app,
      Over.mapComp]
  rw [e]
  exact key G.obj.X

/-- Two maps into the base change of `U ×_{b, B} G` along `s : V ⟶ U` agree as soon as their
`G`-components and their `V`-components agree. -/
theorem pullbackGroupComp_hom_ext {U V : BigFppfOver 𝒞 S hS} (b : yoneda.obj U ⟶ B)
    (s : yoneda.obj V ⟶ yoneda.obj U) {Z : (BigFppfOver 𝒞 S hS)ᵒᵖ ⥤ Type u}
    {k k' : Z ⟶ pullback (pullback.snd G.obj.X.hom b) s}
    (h₁ : k ≫ pullback.fst _ s ≫ pullback.fst G.obj.X.hom b =
      k' ≫ pullback.fst _ s ≫ pullback.fst G.obj.X.hom b)
    (h₂ : k ≫ pullback.snd _ s = k' ≫ pullback.snd _ s) : k = k' := by
  refine pullback.hom_ext (pullback.hom_ext ?_ ?_) h₂
  · simpa only [Category.assoc] using h₁
  · simp only [Category.assoc, pullback.condition]
    rw [← Category.assoc, h₂, Category.assoc]


variable (hB G) in
/-- The underlying map of `groupCompIso`, with its source and target written as fibre products. -/
def groupCompMap {U V : BigFppfOver 𝒞 S hS} (b : yoneda.obj U ⟶ B)
    (s : yoneda.obj V ⟶ yoneda.obj U) :
    pullback G.obj.X.hom (s ≫ b) ⟶ pullback (pullback.snd G.obj.X.hom b) s :=
  (groupCompIso hB G b s).hom.hom.hom.left

variable (hB G) in
/-- The underlying map of the inverse of `groupCompIso`, with its source and target written as
fibre products. -/
def groupCompInv {U V : BigFppfOver 𝒞 S hS} (b : yoneda.obj U ⟶ B)
    (s : yoneda.obj V ⟶ yoneda.obj U) :
    pullback (pullback.snd G.obj.X.hom b) s ⟶ pullback G.obj.X.hom (s ≫ b) :=
  (groupCompIso hB G b s).inv.hom.hom.left

/-- `groupCompInv` is a left inverse of `groupCompMap`. -/
@[reassoc (attr := simp)]
theorem groupCompMap_inv {U V : BigFppfOver 𝒞 S hS} (b : yoneda.obj U ⟶ B)
    (s : yoneda.obj V ⟶ yoneda.obj U) :
    groupCompMap hB G b s ≫ groupCompInv hB G b s = 𝟙 _ :=
  congrArg (fun k => k.hom.hom.left) (groupCompIso hB G b s).hom_inv_id

/-- `groupCompInv` is a right inverse of `groupCompMap`. -/
@[reassoc (attr := simp)]
theorem groupCompInv_map {U V : BigFppfOver 𝒞 S hS} (b : yoneda.obj U ⟶ B)
    (s : yoneda.obj V ⟶ yoneda.obj U) :
    groupCompInv hB G b s ≫ groupCompMap hB G b s = 𝟙 _ :=
  congrArg (fun k => k.hom.hom.left) (groupCompIso hB G b s).inv_hom_id

/-- `groupCompMap` commutes with the projections to `V`. -/
@[reassoc (attr := simp)]
theorem groupCompMap_snd {U V : BigFppfOver 𝒞 S hS} (b : yoneda.obj U ⟶ B)
    (s : yoneda.obj V ⟶ yoneda.obj U) :
    groupCompMap hB G b s ≫ pullback.snd (pullback.snd G.obj.X.hom b) s =
      pullback.snd G.obj.X.hom (s ≫ b) :=
  groupCompIso_hom_snd b s

/-- `groupCompMap` commutes with the projections to `G`. -/
@[reassoc (attr := simp)]
theorem groupCompMap_fst_fst {U V : BigFppfOver 𝒞 S hS} (b : yoneda.obj U ⟶ B)
    (s : yoneda.obj V ⟶ yoneda.obj U) :
    groupCompMap hB G b s ≫ pullback.fst (pullback.snd G.obj.X.hom b) s ≫
        pullback.fst G.obj.X.hom b = pullback.fst G.obj.X.hom (s ≫ b) :=
  groupCompIso_hom_fst_fst b s

/-- `groupCompInv` commutes with the projections to `G`. -/
@[reassoc (attr := simp)]
theorem groupCompInv_fst {U V : BigFppfOver 𝒞 S hS} (b : yoneda.obj U ⟶ B)
    (s : yoneda.obj V ⟶ yoneda.obj U) :
    groupCompInv hB G b s ≫ pullback.fst G.obj.X.hom (s ≫ b) =
      pullback.fst (pullback.snd G.obj.X.hom b) s ≫ pullback.fst G.obj.X.hom b := by
  rw [← groupCompMap_fst_fst b s, groupCompInv_map_assoc]

/-- `groupCompInv` commutes with the projections to `V`. -/
@[reassoc (attr := simp)]
theorem groupCompInv_snd {U V : BigFppfOver 𝒞 S hS} (b : yoneda.obj U ⟶ B)
    (s : yoneda.obj V ⟶ yoneda.obj U) :
    groupCompInv hB G b s ≫ pullback.snd G.obj.X.hom (s ≫ b) =
      pullback.snd (pullback.snd G.obj.X.hom b) s := by
  rw [← groupCompMap_snd b s, groupCompInv_map_assoc]

variable (hB G) in
/-- Equal morphisms to `B` give equal base changes of `G`, as group objects. -/
def groupEqIso {V : BigFppfOver 𝒞 S hS} {σ σ' : yoneda.obj V ⟶ B} (h : σ = σ') :
    (fppfPullbackGroup hB G V σ).obj ≅ (fppfPullbackGroup hB G V σ').obj :=
  eqToIso (congrArg (fun τ => (fppfPullbackGroup hB G V τ).obj) h)

/-- The comparison isomorphisms commute with base change along a morphism `f : V₁ ⟶ V₂` of the
site. -/
theorem groupCompMap_naturality {U V₁ V₂ : BigFppfOver 𝒞 S hS} (b : yoneda.obj U ⟶ B)
    (f : V₁ ⟶ V₂) (s₁ : yoneda.obj V₁ ⟶ yoneda.obj U) (s₂ : yoneda.obj V₂ ⟶ yoneda.obj U)
    (hs : yoneda.map f ≫ s₂ = s₁) :
    groupCompMap hB G b s₁ ≫ pullback.map (pullback.snd G.obj.X.hom b) s₁
        (pullback.snd G.obj.X.hom b) s₂ (𝟙 _) (yoneda.map f) (𝟙 _) (by simp)
        (by simp [hs]) =
      pullback.map G.obj.X.hom (s₁ ≫ b) G.obj.X.hom (s₂ ≫ b) (𝟙 _) (yoneda.map f) (𝟙 _)
        (by simp) (by simp [← hs]) ≫ groupCompMap hB G b s₂ := by
  apply pullbackGroupComp_hom_ext b s₂
  · simp only [pullback.map, Category.assoc, Category.comp_id, groupCompMap_fst_fst,
      pullback.lift_fst, pullback.lift_fst_assoc]
  · simp only [pullback.map, Category.assoc, groupCompMap_snd, groupCompMap_snd_assoc,
      pullback.lift_snd]

/-- The inverse comparison isomorphisms commute with base change along a morphism
`f : V₁ ⟶ V₂` of the site. -/
theorem groupCompInv_naturality {U V₁ V₂ : BigFppfOver 𝒞 S hS} (b : yoneda.obj U ⟶ B)
    (f : V₁ ⟶ V₂) (s₁ : yoneda.obj V₁ ⟶ yoneda.obj U) (s₂ : yoneda.obj V₂ ⟶ yoneda.obj U)
    (hs : yoneda.map f ≫ s₂ = s₁) :
    groupCompInv hB G b s₁ ≫
        pullback.map G.obj.X.hom (s₁ ≫ b) G.obj.X.hom (s₂ ≫ b) (𝟙 _) (yoneda.map f) (𝟙 _)
          (by simp) (by simp [← hs]) =
      pullback.map (pullback.snd G.obj.X.hom b) s₁ (pullback.snd G.obj.X.hom b) s₂ (𝟙 _)
          (yoneda.map f) (𝟙 _) (by simp) (by simp [hs]) ≫ groupCompInv hB G b s₂ := by
  apply pullback.hom_ext
  · simp only [pullback.map, Category.assoc]
    rw [pullback.lift_fst, Category.comp_id, groupCompInv_fst, groupCompInv_fst,
      pullback.lift_fst_assoc, Category.comp_id]
  · simp only [pullback.map, Category.assoc]
    rw [pullback.lift_snd, groupCompInv_snd_assoc, groupCompInv_snd, pullback.lift_snd]

namespace TorsorsFor

variable {U : BigFppfOver 𝒞 S hS} {b : yoneda.obj U ⟶ B}

variable (P b) in
/-- A torsor under `V ×_{s, U} H`, for `H = U ×_{b, B} G`, read as a torsor under
`V ×_{s ∘ b, B} G`. -/
abbrev toBase (A : TorsorsFor (isAlgebraicSpace_yoneda 𝒞 S hS U) (fppfPullbackGroup hB G U b) P) :
    TorsorsFor hB G P :=
  changeGroup P A (A.sec ≫ b) (groupCompIso hB G b A.sec)

variable (P b) in
/-- A torsor under `V ×_{σ, B} G` whose section `σ` factors as `s ∘ b`, read as a torsor under
`V ×_{s, U} H` for `H = U ×_{b, B} G`. -/
abbrev ofBase (T : TorsorsFor hB G P) (s : yoneda.obj T.base ⟶ yoneda.obj U)
    (hs : s ≫ b = T.sec) :
    TorsorsFor (isAlgebraicSpace_yoneda 𝒞 S hS U) (fppfPullbackGroup hB G U b) P :=
  changeGroup P T s ((groupCompIso hB G b s).symm ≪≫ groupEqIso hB G hs)

variable (P b) in
/-- A morphism of torsors under `H = U ×_{b, B} G`, read as a morphism of torsors under `G`. -/
def toBaseHom {A₁ A₂ : TorsorsFor (isAlgebraicSpace_yoneda 𝒞 S hS U)
      (fppfPullbackGroup hB G U b) P} (φ : A₁ ⟶ A₂) :
    toBase P b A₁ ⟶ toBase P b A₂ :=
  changeGroupHom P φ _ _ (by rw [← Category.assoc, Hom.comp_sec (T := A₁) (T' := A₂) φ])
    (groupCompMap_naturality b (Hom.base (T := A₁) (T' := A₂) φ) A₁.sec A₂.sec
      (Hom.comp_sec (T := A₁) (T' := A₂) φ))

variable (P b) in
/-- A morphism of torsors under `G` whose sections factor through `b` compatibly, read as a
morphism of torsors under `H = U ×_{b, B} G`. -/
def ofBaseHom {T₁ T₂ : TorsorsFor hB G P} (φ : T₁ ⟶ T₂)
    (s₁ : yoneda.obj T₁.base ⟶ yoneda.obj U) (s₂ : yoneda.obj T₂.base ⟶ yoneda.obj U)
    (h₁ : s₁ ≫ b = T₁.sec) (h₂ : s₂ ≫ b = T₂.sec)
    (hs : yoneda.map (Hom.base (T := T₁) (T' := T₂) φ) ≫ s₂ = s₁) :
    ofBase P b T₁ s₁ h₁ ⟶ ofBase P b T₂ s₂ h₂ :=
  changeGroupHom P φ ((groupCompIso hB G b s₁).symm ≪≫ groupEqIso hB G h₁)
    ((groupCompIso hB G b s₂).symm ≪≫ groupEqIso hB G h₂) hs (by
    obtain ⟨base₁, sec₁, total₁, alg₁, act₁, tor₁⟩ := T₁
    obtain ⟨base₂, sec₂, total₂, alg₂, act₂, tor₂⟩ := T₂
    change yoneda.obj base₁ ⟶ yoneda.obj U at s₁
    change yoneda.obj base₂ ⟶ yoneda.obj U at s₂
    change s₁ ≫ b = sec₁ at h₁
    change s₂ ≫ b = sec₂ at h₂
    subst h₁ h₂
    exact groupCompInv_naturality b _ s₁ s₂ hs)

/-- The morphism of bases of `toBaseHom P b φ` is that of `φ`. -/
@[simp]
theorem toBaseHom_base {A₁ A₂ : TorsorsFor (isAlgebraicSpace_yoneda 𝒞 S hS U)
      (fppfPullbackGroup hB G U b) P} (φ : A₁ ⟶ A₂) :
    Hom.base (toBaseHom P b φ) = Hom.base (T := A₁) (T' := A₂) φ :=
  rfl

/-- The morphism of total spaces of `toBaseHom P b φ` is that of `φ`. -/
@[simp]
theorem toBaseHom_map {A₁ A₂ : TorsorsFor (isAlgebraicSpace_yoneda 𝒞 S hS U)
      (fppfPullbackGroup hB G U b) P} (φ : A₁ ⟶ A₂) :
    Hom.map (toBaseHom P b φ) = Hom.map (T := A₁) (T' := A₂) φ :=
  rfl

/-- The morphism of bases of `ofBaseHom P b φ s₁ s₂ h₁ h₂ hs` is that of `φ`. -/
@[simp]
theorem ofBaseHom_base {T₁ T₂ : TorsorsFor hB G P} (φ : T₁ ⟶ T₂)
    (s₁ : yoneda.obj T₁.base ⟶ yoneda.obj U) (s₂ : yoneda.obj T₂.base ⟶ yoneda.obj U)
    (h₁ : s₁ ≫ b = T₁.sec) (h₂ : s₂ ≫ b = T₂.sec)
    (hs : yoneda.map (Hom.base (T := T₁) (T' := T₂) φ) ≫ s₂ = s₁) :
    Hom.base (ofBaseHom P b φ s₁ s₂ h₁ h₂ hs) = Hom.base (T := T₁) (T' := T₂) φ :=
  rfl

/-- The morphism of total spaces of `ofBaseHom P b φ s₁ s₂ h₁ h₂ hs` is that of `φ`. -/
@[simp]
theorem ofBaseHom_map {T₁ T₂ : TorsorsFor hB G P} (φ : T₁ ⟶ T₂)
    (s₁ : yoneda.obj T₁.base ⟶ yoneda.obj U) (s₂ : yoneda.obj T₂.base ⟶ yoneda.obj U)
    (h₁ : s₁ ≫ b = T₁.sec) (h₂ : s₂ ≫ b = T₂.sec)
    (hs : yoneda.map (Hom.base (T := T₁) (T' := T₂) φ) ≫ s₂ = s₁) :
    Hom.map (ofBaseHom P b φ s₁ s₂ h₁ h₂ hs) = Hom.map (T := T₁) (T' := T₂) φ :=
  rfl

variable (P b) in
/-- Reading a torsor under `G` as a torsor under `H = U ×_{b, B} G` and back gives a torsor
isomorphic to the original one by the identity of its total space. -/
def toBaseOfBase (T : TorsorsFor hB G P) (s : yoneda.obj T.base ⟶ yoneda.obj U)
    (hs : s ≫ b = T.sec) : toBase P b (ofBase P b T s hs) ⟶ T where
  base := 𝟙 T.base
  comp_sec := by
    change yoneda.map (𝟙 T.base) ≫ T.sec = s ≫ b
    rw [CategoryTheory.Functor.map_id, Category.id_comp, hs]
  map := 𝟙 T.total.left
  isPullback := by simpa using IsPullback.id_horiz T.total.hom
  smul_comp := by
    obtain ⟨base, sec, X, alg, act, tor⟩ := T
    change yoneda.obj base ⟶ yoneda.obj U at s
    change s ≫ b = sec at hs
    subst hs
    let wE : pullback (pullback.snd G.obj.X.hom (s ≫ b)) X.hom ⟶
        pullback (pullback.snd (pullback.snd G.obj.X.hom b) s) X.hom :=
      pullback.map _ _ _ _ (groupCompMap hB G b s) (𝟙 _) (𝟙 _) (by simp) (by simp)
    have hid : ((groupEqIso hB G (rfl : s ≫ b = s ≫ b)).hom.hom.hom.left :
        pullback G.obj.X.hom (s ≫ b) ⟶ pullback G.obj.X.hom (s ≫ b)) =
          𝟙 (pullback G.obj.X.hom (s ≫ b)) := rfl
    let wF : pullback (pullback.snd (pullback.snd G.obj.X.hom b) s) X.hom ⟶
        pullback (pullback.snd G.obj.X.hom (s ≫ b)) X.hom :=
      pullback.map _ _ _ _ (groupCompInv hB G b s ≫
        (groupEqIso hB G (rfl : s ≫ b = s ≫ b)).hom.hom.hom.left) (𝟙 _) (𝟙 _)
        (by simp only [hid, Category.comp_id, groupCompInv_snd]) (by simp)
    let abc : pullback (pullback.snd G.obj.X.hom (s ≫ b)) X.hom ⟶
        pullback (pullback.snd G.obj.X.hom (s ≫ b)) X.hom :=
      pullback.map _ _ _ _ (pullback.map _ _ _ _ (𝟙 _) (yoneda.map (𝟙 base)) (𝟙 _)
        (by simp) (by simp)) (𝟙 _) (yoneda.map (𝟙 base)) (by simp [pullback.map])
        (by simp)
    have key : wE ≫ wF = abc := by
      simp only [wE, wF, abc]
      rw [pullback.map_comp]
      simp only [hid, Category.comp_id, groupCompMap_inv,
        CategoryTheory.Functor.map_id, pullback.map_id]
    have c₁ := actionMap_changeGroup (ofBase P b ⟨base, s ≫ b, X, alg, act, tor⟩ s rfl) (s ≫ b)
      (groupCompIso hB G b s)
    have c₂ := actionMap_changeGroup ⟨base, s ≫ b, X, alg, act, tor⟩ s
      ((groupCompIso hB G b s).symm ≪≫ groupEqIso hB G rfl)
    have e₁ : ((groupCompIso hB G b s).hom.hom.hom ▷ X).left = wE := rfl
    have e₂ : (((groupCompIso hB G b s).symm ≪≫ groupEqIso hB G rfl).hom.hom.hom ▷
        X).left = wF := rfl
    exact (Category.comp_id _).trans (c₁.trans ((congrArg (_ ≫ ·) c₂).trans
      ((Category.assoc _ _ _).symm.trans (congrArg (· ≫ _)
        ((congrArg₂ (· ≫ ·) e₁ e₂).trans key)))))

/-- The morphism of bases of `toBaseOfBase P b T s hs` is the identity. -/
@[simp]
theorem toBaseOfBase_base (T : TorsorsFor hB G P) (s : yoneda.obj T.base ⟶ yoneda.obj U)
    (hs : s ≫ b = T.sec) : Hom.base (toBaseOfBase P b T s hs) = 𝟙 T.base :=
  rfl

/-- The morphism of total spaces of `toBaseOfBase P b T s hs` is the identity. -/
@[simp]
theorem toBaseOfBase_map (T : TorsorsFor hB G P) (s : yoneda.obj T.base ⟶ yoneda.obj U)
    (hs : s ≫ b = T.sec) : Hom.map (toBaseOfBase P b T s hs) = 𝟙 T.total.left :=
  rfl

end TorsorsFor

end AlgebraicGeometry.Space

end
