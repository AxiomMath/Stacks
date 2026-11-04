module

public import StacksFrontier.Algebra.Category.ModuleCat.Sheaf.PullbackTensorSquare
public import StacksFrontier.Algebra.Category.ModuleCat.Sheaf.RingedToposPullback
public import StacksFrontier.CategoryTheory.Sites.Modules.Localization.LocalizedSquareModuleBaseChange
public import StacksFrontier.Algebra.Category.ModuleCat.Sheaf.RingedToposPushforwardIsoSections
public import StacksFrontier.Algebra.Category.ModuleCat.Sheaf.RingedToposPushforwardComp

/-!
# The two composite direct images around a 2-commutative square of ringed topoi

Let
```
              g'
  (Sh(𝒞'), 𝒪_{𝒞'}) ⟶ (Sh(𝒞), 𝒪_𝒞)
        | f'                | f
        v                   v
  (Sh(𝒟'), 𝒪_{𝒟'}) ⟶ (Sh(𝒟), 𝒪_𝒟)
              g
```
be a square of morphisms of ringed topoi commuting up to a 2-isomorphism `s : g ∘ f' ≅ f ∘ g'`.
The two composite direct images of sheaves of modules around the square are identified,
`f_* g'_* ≅ g_* f'_*` (`squarePushforwardModulesIso`), through the direct image along the common
composite. This file proves that this identification is the one matching the isomorphism
`(f')^* g^* ≅ (g')^* f^*` of the two composite pullbacks
(`AlgebraicGeometry.RingedToposHom.TwoIso.squarePullbackIso`) under the composite adjunctions:
the two composite units are carried to each other. Its middle part, the comparison of the
four-field direct images through the composite, is `s⁻¹` on underlying sheaves of sets, the two
outer parts being the identity there (in the namespace `AlgebraicGeometry.RingedToposHom`, this
is `TwoIso.moduleSheafFunctor_map_pushforwardModulesCompIso_squarePushforwardIso_hom_app`).

## Main definitions

* `AlgebraicGeometry.RingedToposHom.TwoIso.squarePushforwardModulesIso`.

## Main results

* `CategoryTheory.Adjunction.unit_comp_map_leftAdjointUniq_trans`: the abstract identity, for
  two factorizations of one adjunction.
* `CategoryTheory.Adjunction.unit_square_ofNatIsoRight`: the identity survives replacing the
  right adjoints by isomorphic ones.
* `AlgebraicGeometry.RingedToposHom.TwoIso.unit_comp_map_squarePullbackIso_hom_app`: the
  composite units around the square correspond.

## References

* [Stacks Project, Tag 03D8](https://stacks.math.columbia.edu/tag/03D8)
* [Stacks Project, Tag 04IC](https://stacks.math.columbia.edu/tag/04IC)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits

/-- The unit of `adj.ofNatIsoRight t` is the unit of `adj` followed by `t`. -/
private theorem unit_app_ofNatIsoRight {𝒜 : Type*} [Category 𝒜] {ℬ : Type*} [Category ℬ]
    {L : 𝒜 ⥤ ℬ} {R R' : ℬ ⥤ 𝒜} (adj : L ⊣ R) (t : R ≅ R') (K : 𝒜) :
    (adj.ofNatIsoRight t).unit.app K = adj.unit.app K ≫ t.hom.app (L.obj K) := by
  simp [Adjunction.ofNatIsoRight]

/-- **Two factorizations of one adjunction carry the composite units to each other.** Let
`adj : L ⊣ R`, and let `adj₁ : L₁ ⊣ R₁` and `adj₂ : L₂ ⊣ R₂` be two further adjunctions whose
right adjoints are identified with `R` by `e₁` and `e₂`. Then the comparison `L₁ ≅ L₂` through
`L` (the composite of the two `leftAdjointUniq` isomorphisms) carries the unit of `adj₁`, read
through `e₁`, to the unit of `adj₂`, read through `e₂`. -/
theorem CategoryTheory.Adjunction.unit_comp_map_leftAdjointUniq_trans
    {𝒜 : Type*} [Category 𝒜] {ℬ : Type*} [Category ℬ]
    {L L₁ L₂ : 𝒜 ⥤ ℬ} {R R₁ R₂ : ℬ ⥤ 𝒜} (adj : L ⊣ R) (adj₁ : L₁ ⊣ R₁) (adj₂ : L₂ ⊣ R₂)
    (e₁ : R₁ ≅ R) (e₂ : R₂ ≅ R) (K : 𝒜) :
    adj₁.unit.app K ≫ R₁.map
        ((((adj.ofNatIsoRight e₁.symm).leftAdjointUniq adj₁).symm ≪≫
          (adj.ofNatIsoRight e₂.symm).leftAdjointUniq adj₂).hom.app K) =
      adj₂.unit.app K ≫ (e₂.hom ≫ e₁.inv).app (L₂.obj K) := by
  have h₁ := Adjunction.unit_leftAdjointUniq_hom_app (adj.ofNatIsoRight e₁.symm) adj₁ K
  have h₂ := Adjunction.unit_leftAdjointUniq_hom_app (adj.ofNatIsoRight e₂.symm) adj₂ K
  rw [unit_app_ofNatIsoRight, Iso.symm_hom] at h₁ h₂
  rw [Iso.trans_hom, NatTrans.comp_app, Iso.symm_hom, R₁.map_comp, ← h₁, ← h₂]
  simp only [Category.assoc, ← R₁.map_comp_assoc, Iso.hom_inv_id_app, CategoryTheory.Functor.map_id,
    Category.id_comp, NatTrans.comp_app]
  rw [← e₁.inv.naturality, ← e₂.inv.naturality_assoc, Iso.inv_hom_id_app_assoc]

/-- **The unit identity of a square of adjunctions survives replacing the right adjoints by
isomorphic ones.** If the composite units of `L_g ⋙ L_f' ⊣ R_f' ⋙ R_g` and of
`L_f ⋙ L_g' ⊣ R_g' ⋙ R_f` are carried to each other by `m` and `e₂ ≫ e₁⁻¹`, then after replacing
each right adjoint `R` by an isomorphic `R'` (through `t`), they are carried to each other by `m`
and the conjugate of `e₂ ≫ e₁⁻¹` by the `t`. -/
theorem CategoryTheory.Adjunction.unit_square_ofNatIsoRight
    {𝒜 ℬ 𝒞 𝒟 : Type*} [Category 𝒜] [Category ℬ] [Category 𝒞] [Category 𝒟]
    {Lg : 𝒜 ⥤ ℬ} {Rg Rg₂ : ℬ ⥤ 𝒜} {Lf' : ℬ ⥤ 𝒟} {Rf' Rf'₂ : 𝒟 ⥤ ℬ}
    {Lf : 𝒜 ⥤ 𝒞} {Rf Rf₂ : 𝒞 ⥤ 𝒜} {Lg' : 𝒞 ⥤ 𝒟} {Rg' Rg'₂ : 𝒟 ⥤ 𝒞} {R : 𝒟 ⥤ 𝒜}
    (ag : Lg ⊣ Rg) (af' : Lf' ⊣ Rf') (af : Lf ⊣ Rf) (ag' : Lg' ⊣ Rg')
    (tg : Rg ≅ Rg₂) (tf' : Rf' ≅ Rf'₂) (tf : Rf ≅ Rf₂) (tg' : Rg' ≅ Rg'₂)
    (e₁ : Rf' ⋙ Rg ≅ R) (e₂ : Rg' ⋙ Rf ≅ R) (m : Lg ⋙ Lf' ⟶ Lf ⋙ Lg') (K : 𝒜)
    (h : (ag.comp af').unit.app K ≫ (Rf' ⋙ Rg).map (m.app K) =
      (af.comp ag').unit.app K ≫ (e₂.hom ≫ e₁.inv).app (Lg'.obj (Lf.obj K))) :
    (ag.ofNatIsoRight tg).unit.app K ≫ Rg₂.map ((af'.ofNatIsoRight tf').unit.app (Lg.obj K)) ≫
        Rg₂.map (Rf'₂.map (m.app K)) =
      (af.ofNatIsoRight tf).unit.app K ≫ Rf₂.map ((ag'.ofNatIsoRight tg').unit.app (Lf.obj K)) ≫
        ((Functor.isoWhiskerRight tg'.symm Rf₂ ≪≫ Functor.isoWhiskerLeft Rg' tf.symm) ≪≫ e₂ ≪≫
          e₁.symm ≪≫ (Functor.isoWhiskerRight tf' Rg ≪≫ Functor.isoWhiskerLeft Rf'₂ tg)).hom.app
          (Lg'.obj (Lf.obj K)) := by
  simp only [Adjunction.comp_unit_app, Functor.comp_map] at h
  simp only [unit_app_ofNatIsoRight]
  have e₃ : tg.hom.app (Lg.obj K) ≫ Rg₂.map (af'.unit.app (Lg.obj K) ≫
      tf'.hom.app (Lf'.obj (Lg.obj K))) ≫ Rg₂.map (Rf'₂.map (m.app K)) =
      Rg.map (af'.unit.app (Lg.obj K)) ≫ Rg.map (Rf'.map (m.app K)) ≫
        Rg.map (tf'.hom.app (Lg'.obj (Lf.obj K))) ≫ tg.hom.app (Rf'₂.obj (Lg'.obj (Lf.obj K))) := by
    rw [← Functor.map_comp, ← tg.hom.naturality]
    simp only [Functor.map_comp, Category.assoc]
    congr 1
    rw [← Functor.map_comp_assoc, ← Functor.map_comp_assoc, ← tf'.hom.naturality]
    rfl
  have e₄ : tf.hom.app (Lf.obj K) ≫ Rf₂.map (ag'.unit.app (Lf.obj K) ≫
      tg'.hom.app (Lg'.obj (Lf.obj K))) ≫ Rf₂.map (tg'.inv.app (Lg'.obj (Lf.obj K))) ≫
        tf.inv.app (Rg'.obj (Lg'.obj (Lf.obj K))) = Rf.map (ag'.unit.app (Lf.obj K)) := by
    rw [← Functor.map_comp_assoc, Category.assoc, Iso.hom_inv_id_app, ← tf.hom.naturality_assoc]
    simp
  simp only [Iso.trans_hom, Iso.symm_hom, NatTrans.comp_app, Functor.isoWhiskerRight_hom,
    Functor.isoWhiskerLeft_hom, Functor.whiskerRight_app, Functor.whiskerLeft_app, Category.assoc]
  rw [e₃, reassoc_of% e₄]
  simp only [← Category.assoc] at h ⊢
  rw [h]
  simp only [NatTrans.comp_app, Category.assoc]

namespace AlgebraicGeometry.RingedToposHom.TwoIso

open Stacks.Sheaves.RingedToposModules

universe u

variable {X' X Y' Y : RingedTopos.{u, u, u}}
  [X'.J.HasSheafCompose (forget RingCat.{u})] [X.J.HasSheafCompose (forget RingCat.{u})]
  [Y'.J.HasSheafCompose (forget RingCat.{u})] [Y.J.HasSheafCompose (forget RingCat.{u})]
  [X'.J.HasSheafCompose (forget₂ CommRingCat.{u} RingCat.{u})]
  [X.J.HasSheafCompose (forget₂ CommRingCat.{u} RingCat.{u})]
  [Y'.J.HasSheafCompose (forget₂ CommRingCat.{u} RingCat.{u})]
  [Y.J.HasSheafCompose (forget₂ CommRingCat.{u} RingCat.{u})]
  [X'.J.HasSheafCompose (forget AddCommGrpCat.{u})] [X.J.HasSheafCompose (forget AddCommGrpCat.{u})]
  [Y'.J.HasSheafCompose (forget AddCommGrpCat.{u})] [Y.J.HasSheafCompose (forget AddCommGrpCat.{u})]
  {f : RingedToposHom X Y} {g : RingedToposHom Y' Y} {f' : RingedToposHom X' Y'}
  {g' : RingedToposHom X' X} (s : TwoIso (g.comp f') (f.comp g'))

/-- **The two composite direct images around a 2-commutative square agree**:
`f_* ⋙ ... : g'_* ⋙ f_* ≅ f'_* ⋙ g_*` on sheaves of modules, through the direct image along the
common composite `g ∘ f'` (read through `s` for the factorization through `g'` and `f`). -/
def squarePushforwardModulesIso :
    g'.pushforwardModules ⋙ f.pushforwardModules ≅ f'.pushforwardModules ⋙ g.pushforwardModules :=
  (Functor.isoWhiskerRight g'.toModulesPushforwardIso.symm _ ≪≫
      Functor.isoWhiskerLeft _ f.toModulesPushforwardIso.symm) ≪≫
    Stacks.Sheaves.RingedToposModules.pushforwardModulesCompIso g'.toModulesHom f.toModulesHom
        (g.comp f').toModulesHom
      (squarePushforwardIso s) (fSharpSetComp_squarePushforwardIso s) ≪≫
    (Stacks.Sheaves.RingedToposModules.pushforwardModulesCompIso f'.toModulesHom g.toModulesHom
        (g.comp f').toModulesHom
      (toModulesHomPushforwardIso f' g) (fSharpSetComp_toModulesHomPushforwardIso f' g)).symm ≪≫
    (Functor.isoWhiskerRight f'.toModulesPushforwardIso _ ≪≫
      Functor.isoWhiskerLeft _ g.toModulesPushforwardIso)

variable [HasWeakSheafify X'.J AddCommGrpCat.{u}] [X'.J.WEqualsLocallyBijective AddCommGrpCat.{u}]
  [HasWeakSheafify X.J AddCommGrpCat.{u}] [X.J.WEqualsLocallyBijective AddCommGrpCat.{u}]
  [HasWeakSheafify Y'.J AddCommGrpCat.{u}] [Y'.J.WEqualsLocallyBijective AddCommGrpCat.{u}]
  [HasWeakSheafify Y.J AddCommGrpCat.{u}] [Y.J.WEqualsLocallyBijective AddCommGrpCat.{u}]

omit [HasWeakSheafify Y.J AddCommGrpCat.{u}] [Y.J.WEqualsLocallyBijective AddCommGrpCat.{u}] in
/-- **The composite units around the square correspond.** The unit of `g^* ⊣ g_*` followed by
`g_*` of the unit of `(f')^* ⊣ f'_*` and by `g_* f'_*` of the comparison
`(f')^* g^* ≅ (g')^* f^*` of the two composite pullbacks is the unit of `f^* ⊣ f_*` followed by
`f_*` of the unit of `(g')^* ⊣ g'_*` and by the comparison `f_* g'_* ≅ g_* f'_*` of the two
composite direct images. -/
theorem unit_comp_map_squarePullbackIso_hom_app
    (K : SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf Y.O)) :
    g.pullbackAdjPushforwardModules.unit.app K ≫
        g.pushforwardModules.map (f'.pullbackAdjPushforwardModules.unit.app
          (g.toModulesHom.pullbackModules.obj K)) ≫
        g.pushforwardModules.map (f'.pushforwardModules.map ((squarePullbackIso s).hom.app K)) =
      f.pullbackAdjPushforwardModules.unit.app K ≫
        f.pushforwardModules.map (g'.pullbackAdjPushforwardModules.unit.app
          (f.toModulesHom.pullbackModules.obj K)) ≫
        (squarePushforwardModulesIso s).hom.app
          (g'.toModulesHom.pullbackModules.obj (f.toModulesHom.pullbackModules.obj K)) := by
  have core := CategoryTheory.Adjunction.unit_comp_map_leftAdjointUniq_trans
    (Stacks.Sheaves.RingedToposModules.pullbackAdjPushforwardModules (g.comp f').toModulesHom)
    ((Stacks.Sheaves.RingedToposModules.pullbackAdjPushforwardModules g.toModulesHom).comp
      (Stacks.Sheaves.RingedToposModules.pullbackAdjPushforwardModules f'.toModulesHom))
    ((Stacks.Sheaves.RingedToposModules.pullbackAdjPushforwardModules f.toModulesHom).comp
      (Stacks.Sheaves.RingedToposModules.pullbackAdjPushforwardModules g'.toModulesHom))
    (Stacks.Sheaves.RingedToposModules.pushforwardModulesCompIso f'.toModulesHom g.toModulesHom
      (g.comp f').toModulesHom (toModulesHomPushforwardIso f' g)
      (fSharpSetComp_toModulesHomPushforwardIso f' g))
    (Stacks.Sheaves.RingedToposModules.pushforwardModulesCompIso g'.toModulesHom f.toModulesHom
      (g.comp f').toModulesHom (squarePushforwardIso s) (fSharpSetComp_squarePushforwardIso s)) K
  have hm : (squarePullbackIso s).hom.app K =
      ((((Stacks.Sheaves.RingedToposModules.pullbackAdjPushforwardModules
      (g.comp f').toModulesHom).ofNatIsoRight
        (Stacks.Sheaves.RingedToposModules.pushforwardModulesCompIso f'.toModulesHom g.toModulesHom
          (g.comp f').toModulesHom (toModulesHomPushforwardIso f' g)
          (fSharpSetComp_toModulesHomPushforwardIso f' g)).symm).leftAdjointUniq
      ((Stacks.Sheaves.RingedToposModules.pullbackAdjPushforwardModules g.toModulesHom).comp
        (Stacks.Sheaves.RingedToposModules.pullbackAdjPushforwardModules f'.toModulesHom))).symm ≪≫
      ((Stacks.Sheaves.RingedToposModules.pullbackAdjPushforwardModules
        (g.comp f').toModulesHom).ofNatIsoRight
        (Stacks.Sheaves.RingedToposModules.pushforwardModulesCompIso g'.toModulesHom f.toModulesHom
          (g.comp f').toModulesHom (squarePushforwardIso s)
          (fSharpSetComp_squarePushforwardIso s)).symm).leftAdjointUniq
      ((Stacks.Sheaves.RingedToposModules.pullbackAdjPushforwardModules f.toModulesHom).comp
        (Stacks.Sheaves.RingedToposModules.pullbackAdjPushforwardModules g'.toModulesHom))).hom.app
            K :=
    rfl
  have ha : ∀ {A B : RingedTopos.{u, u, u}} [A.J.HasSheafCompose (forget RingCat.{u})]
      [B.J.HasSheafCompose (forget RingCat.{u})]
      [A.J.HasSheafCompose (forget₂ CommRingCat.{u} RingCat.{u})]
      [B.J.HasSheafCompose (forget₂ CommRingCat.{u} RingCat.{u})]
      [A.J.HasSheafCompose (forget AddCommGrpCat.{u})]
      [B.J.HasSheafCompose (forget AddCommGrpCat.{u})]
      [HasWeakSheafify A.J AddCommGrpCat.{u}] [A.J.WEqualsLocallyBijective AddCommGrpCat.{u}]
      (h : RingedToposHom A B),
      h.pullbackAdjPushforwardModules =
        (Stacks.Sheaves.RingedToposModules.pullbackAdjPushforwardModules
            h.toModulesHom).ofNatIsoRight
          h.toModulesPushforwardIso := fun _ => rfl
  rw [ha g, ha f', ha f, ha g', hm]
  exact CategoryTheory.Adjunction.unit_square_ofNatIsoRight _ _ _ _ _ _ _ _ _ _ _ K core

end AlgebraicGeometry.RingedToposHom.TwoIso

end
