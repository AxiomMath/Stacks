module

public import StacksFrontier.Algebra.Category.ModuleCat.Sheaf.RingedToposPullbackLeftUnitality
public import StacksFrontier.Algebra.Category.ModuleCat.Sheaf.RingedToposPullbackModulesComp
public import StacksFrontier.Algebra.Category.ModuleCat.Sheaf.StalkPullbackAtAPointPairUnit
public import StacksFrontier.AlgebraicGeometry.Spaces.DerivedPullbackGeometricStalk
public import StacksFrontier.AlgebraicGeometry.Spaces.GeometricStalkStructureMapComp
public import StacksFrontier.AlgebraicGeometry.Spaces.Perfect.TorIndependentDerivedPullback
public import StacksFrontier.AlgebraicGeometry.Spaces.SmallEtaleDerivedModuleAdjunction
public import StacksFrontier.AlgebraicGeometry.Spaces.SmallEtaleInverseImageFiberComp
public import StacksFrontier.AlgebraicGeometry.Spaces.SmallEtaleModulePullbackComp
public import StacksFrontier.AlgebraicGeometry.Spaces.SmallEtaleStalkStructureMap
public import StacksFrontier.CategoryTheory.Sites.RingedLocalization.RingedToposHomModulesComparisonPullback

/-!
# Stacks 05V5 along a composite of morphisms of algebraic spaces

For morphisms `g₁ : X'' ⟶ X'`, `g₂ : X' ⟶ X` of algebraic spaces and a geometric point `x̄` of
`X''`, the comparison `M_{g₂g₁x̄} ⊗ 𝒪_{X'',x̄} ≅ ((g₁ ≫ g₂)^*M)_{x̄}` of Stacks 05V5 is the
comparison for `g₂`, extended to `𝒪_{X'',x̄}`, followed by the comparison for `g₁` and by
`g₁^*g₂^* ≅ (g₁ ≫ g₂)^*`.

The proof is generic over ringed topoi: the canonical map `f⁻¹G ⟶ f^*G`, `x ↦ 1 ⊗ x`, of a
morphism 2-isomorphic to a composite factors through those of the two factors
(`AlgebraicGeometry.RingedToposHom.pullbackOneTmul_comp`), and the comparisons at matched points
compose (`AlgebraicGeometry.RingedToposHom.stalkFunctorIso_inv_app_comp`).

## Main results

* `AlgebraicGeometry.RingedToposHom.pullbackOneTmul_comp`
* `AlgebraicGeometry.RingedToposHom.stalkFunctorIso_inv_app_comp`
* `AlgebraicGeometry.Space.pullbackStalkFunctorIso_comp_inv_app`

## References

* [Stacks Project, Tag 05V5](https://stacks.math.columbia.edu/tag/05V5)
* [Stacks Project, Tag 04K2](https://stacks.math.columbia.edu/tag/04K2)
-/

/- Instances that come into scope here only through the base versions of imported modules,
and that would change the elaboration below (universe joins, the small model of `D(R)`). -/
attribute [-instance] Stacks.SheafOfModules.coefficientSheafification

@[expose] public section

open CategoryTheory CategoryTheory.Limits
open Stacks.Sheaves.ToposPullback Stacks.Sheaves.ToposPushforward
open scoped TensorProduct ChangeOfRings

universe w v u v' u' v'' u''

namespace AlgebraicGeometry.RingedToposHom

section Unit

variable {X : RingedTopos.{v, u, w}} {Y : RingedTopos.{v', u', w}}
  [X.J.HasSheafCompose (forget₂ CommRingCat.{w} RingCat.{w})]
  [Y.J.HasSheafCompose (forget₂ CommRingCat.{w} RingCat.{w})]
  [X.J.HasSheafCompose (forget RingCat.{w})] [Y.J.HasSheafCompose (forget RingCat.{w})]
  [X.J.HasSheafCompose (forget AddCommGrpCat.{w})]
  [Y.J.HasSheafCompose (forget AddCommGrpCat.{w})]
  [HasWeakSheafify X.J AddCommGrpCat.{w}] [X.J.WEqualsLocallyBijective AddCommGrpCat.{w}]
  [HasWeakSheafify Y.J AddCommGrpCat.{w}] [Y.J.WEqualsLocallyBijective AddCommGrpCat.{w}]
  (f : RingedToposHom X Y)

/-- The canonical map `f⁻¹G ⟶ f^*G`, `x ↦ 1 ⊗ x`, on underlying sheaves of sets. -/
noncomputable abbrev pullbackOneTmul
    (G : SheafOfModules.{w} ((Stacks.SheafOfModules.Tensor.ringSheaf (J := Y.J) Y.O))) :
    f.toToposHom.inverseImage.obj
        (Sheaf.moduleSheaf ((Stacks.SheafOfModules.Tensor.ringSheaf Y.O)) G) ⟶
      Sheaf.moduleSheaf ((Stacks.SheafOfModules.Tensor.ringSheaf X.O))
        (f.toModulesHom.pullbackModules.obj G) :=
  (Sheaf.moduleSheafFunctor (inverseImageRingSheaf f.toToposHom
      ((Stacks.SheafOfModules.Tensor.ringSheaf Y.O)))).map
    ((Stacks.SheafOfModules.RingedToposPullback.structureAdjunction f.toModulesHom).unit.app
      ((Stacks.Sheaves.RingedToposModules.inverseImageModules f.toToposHom
        ((Stacks.SheafOfModules.Tensor.ringSheaf Y.O))).obj G))

omit [HasWeakSheafify Y.J AddCommGrpCat.{w}] [Y.J.WEqualsLocallyBijective AddCommGrpCat.{w}] in
/-- The unit of `f^* ⊣ f_*` on underlying sheaves of sets is the transpose of `x ↦ 1 ⊗ x`. -/
theorem moduleSheafFunctor_map_pullbackAdjPushforwardModules_unit_app_eq_homEquiv
    (G : SheafOfModules.{w} ((Stacks.SheafOfModules.Tensor.ringSheaf (J := Y.J) Y.O))) :
    (Sheaf.moduleSheafFunctor ((Stacks.SheafOfModules.Tensor.ringSheaf (J := Y.J) Y.O))).map
        ((pullbackAdjPushforwardModules f).unit.app G) =
      f.toToposHom.adj.homEquiv _ _ (f.pullbackOneTmul G) := by
  have h4 := (Stacks.SheafOfModules.RingedToposPullback.moduleSheafFunctor_map_pullbackUnit
    f.toModulesHom G).trans (f.toToposHom.adj.homEquiv_unit _ _ (f.pullbackOneTmul G)).symm
  exact Sheaf.hom_ext_sections fun V s =>
    congrArg (fun φ => (Sheaf.sectionsFunctor Y.J V).map φ s) h4

end Unit

section Comp

variable {X'' : RingedTopos.{v, u, w}} {X' : RingedTopos.{v', u', w}}
  {X : RingedTopos.{v'', u'', w}}
  [X''.J.HasSheafCompose (forget₂ CommRingCat.{w} RingCat.{w})]
  [X'.J.HasSheafCompose (forget₂ CommRingCat.{w} RingCat.{w})]
  [X.J.HasSheafCompose (forget₂ CommRingCat.{w} RingCat.{w})]
  [X''.J.HasSheafCompose (forget RingCat.{w})] [X'.J.HasSheafCompose (forget RingCat.{w})]
  [X.J.HasSheafCompose (forget RingCat.{w})]
  [X''.J.HasSheafCompose (forget AddCommGrpCat.{w})]
  [X'.J.HasSheafCompose (forget AddCommGrpCat.{w})]
  [X.J.HasSheafCompose (forget AddCommGrpCat.{w})]
  [HasWeakSheafify X''.J AddCommGrpCat.{w}] [X''.J.WEqualsLocallyBijective AddCommGrpCat.{w}]
  [HasWeakSheafify X'.J AddCommGrpCat.{w}] [X'.J.WEqualsLocallyBijective AddCommGrpCat.{w}]
  [HasWeakSheafify X.J AddCommGrpCat.{w}] [X.J.WEqualsLocallyBijective AddCommGrpCat.{w}]
  (f₁ : RingedToposHom X'' X') (f₂ : RingedToposHom X' X) (f : RingedToposHom X'' X)
  (τ : (f₂.comp f₁).toToposHom.pushforward ≅ f.toToposHom.pushforward)
  (hτ : (f₂.comp f₁).fSharpRing ≫
      pullbackRingSheafMapOfNatTrans X.J
        ((Stacks.SheafOfModules.Tensor.ringSheaf (J := X''.J) X''.O)) τ.hom = f.fSharpRing)

/-- The pullback along a 2-isomorphic morphism of ringed topoi: uniqueness of left adjoints of
the transported direct image. -/
noncomputable abbrev pullbackModulesTransport :
    (f₂.comp f₁).toModulesHom.pullbackModules ≅ f.toModulesHom.pullbackModules :=
  (pullbackAdjPushforwardModules (f₂.comp f₁)).leftAdjointUniq
    ((pullbackAdjPushforwardModules f).ofNatIsoRight
      (pushforwardModulesIsoOfNatIso (f₂.comp f₁) f τ hτ).symm)

omit [HasWeakSheafify X.J AddCommGrpCat.{w}] [X.J.WEqualsLocallyBijective AddCommGrpCat.{w}] in
/-- The unit of `f^* ⊣ f_*`, read through the 2-isomorphism and the comparison of direct images,
is the unit of the composite adjunction followed by the direct image of the comparison of
pullbacks. -/
theorem unit_comp_pushforwardModulesCompIso
    (M : SheafOfModules.{w} ((Stacks.SheafOfModules.Tensor.ringSheaf (J := X.J) X.O))) :
    (pullbackAdjPushforwardModules f).unit.app M ≫
        (pushforwardModulesIsoOfNatIso (f₂.comp f₁) f τ hτ).inv.app _ ≫
          (pushforwardModulesCompIso f₁ f₂).hom.app _ =
      ((pullbackAdjPushforwardModules f₂).comp (pullbackAdjPushforwardModules f₁)).unit.app M ≫
        (f₁.pushforwardModules ⋙ f₂.pushforwardModules).map
          (((pullbackModulesCompIso f₁ f₂).symm ≪≫
            pullbackModulesTransport f₁ f₂ f τ hτ).hom.app M) := by
  have h1 : (pullbackAdjPushforwardModules (f₂.comp f₁)).unit.app M ≫
      (pushforwardModulesCompIso f₁ f₂).hom.app _ ≫
        (f₁.pushforwardModules ⋙ f₂.pushforwardModules).map
          ((pullbackModulesCompIso f₁ f₂).hom.app M) =
      ((pullbackAdjPushforwardModules f₂).comp (pullbackAdjPushforwardModules f₁)).unit.app M :=
    (Category.assoc _ _ _).symm.trans (Adjunction.unit_leftAdjointUniq_hom_app
      ((pullbackAdjPushforwardModules (f₂.comp f₁)).ofNatIsoRight (pushforwardModulesCompIso f₁ f₂))
      ((pullbackAdjPushforwardModules f₂).comp (pullbackAdjPushforwardModules f₁)) M)
  have h2 : (pullbackAdjPushforwardModules (f₂.comp f₁)).unit.app M ≫
      (f₂.comp f₁).pushforwardModules.map ((pullbackModulesTransport f₁ f₂ f τ hτ).hom.app M) =
      (pullbackAdjPushforwardModules f).unit.app M ≫
        (pushforwardModulesIsoOfNatIso (f₂.comp f₁) f τ hτ).inv.app _ :=
    Adjunction.unit_leftAdjointUniq_hom_app (pullbackAdjPushforwardModules (f₂.comp f₁))
      ((pullbackAdjPushforwardModules f).ofNatIsoRight
        (pushforwardModulesIsoOfNatIso (f₂.comp f₁) f τ hτ).symm) M
  rw [← h1, Iso.trans_hom, NatTrans.comp_app, CategoryTheory.Functor.map_comp, Iso.symm_hom,
    Category.assoc, Category.assoc, ← CategoryTheory.Functor.map_comp_assoc, Iso.hom_inv_id_app,
    CategoryTheory.Functor.map_id, Category.id_comp,
    ← (pushforwardModulesCompIso f₁ f₂).hom.naturality, ← Category.assoc, ← h2, Category.assoc]

omit [HasWeakSheafify X.J AddCommGrpCat.{w}] [X.J.WEqualsLocallyBijective AddCommGrpCat.{w}] in
/-- The map `x ↦ 1 ⊗ x` of a morphism `f` 2-isomorphic to `f₂ ∘ f₁` factors as the comparison
`f⁻¹ ≅ f₁⁻¹f₂⁻¹`, the inverse image along `f₁` of the map of `f₂`, the map of `f₁`, and the
comparison `f₁^*f₂^* ≅ f^*`. -/
theorem pullbackOneTmul_comp
    (M : SheafOfModules.{w} ((Stacks.SheafOfModules.Tensor.ringSheaf (J := X.J) X.O))) :
    f.pullbackOneTmul M =
      ((conjugateIsoEquiv (f₂.comp f₁).toToposHom.adj f.toToposHom.adj).symm τ).hom.app
          (Sheaf.moduleSheaf ((Stacks.SheafOfModules.Tensor.ringSheaf X.O)) M) ≫
        f₁.toToposHom.inverseImage.map (f₂.pullbackOneTmul M) ≫
          f₁.pullbackOneTmul (f₂.toModulesHom.pullbackModules.obj M) ≫
            (Sheaf.moduleSheafFunctor ((Stacks.SheafOfModules.Tensor.ringSheaf X''.O))).map
              (((pullbackModulesCompIso f₁ f₂).symm ≪≫
                pullbackModulesTransport f₁ f₂ f τ hτ).hom.app M) := by
  have hk : f₂.pullbackOneTmul M = (f₂.toToposHom.adj.homEquiv
      (Sheaf.moduleSheaf ((Stacks.SheafOfModules.Tensor.ringSheaf X.O)) M)
      (Sheaf.moduleSheaf ((Stacks.SheafOfModules.Tensor.ringSheaf X'.O))
        (f₂.toModulesHom.pullbackModules.obj M))).symm
      ((Sheaf.moduleSheafFunctor ((Stacks.SheafOfModules.Tensor.ringSheaf (J := X.J) X.O))).map
        ((pullbackAdjPushforwardModules f₂).unit.app M)) := by
    rw [moduleSheafFunctor_map_pullbackAdjPushforwardModules_unit_app_eq_homEquiv,
      Equiv.symm_apply_apply]
  rw [hk]
  refine (Adjunction.conjugate_comp f₂.toToposHom.adj f₁.toToposHom.adj f.toToposHom.adj τ _ _ _
    ?_).symm
  rw [Adjunction.homEquiv_naturality_right,
    ← moduleSheafFunctor_map_pullbackAdjPushforwardModules_unit_app_eq_homEquiv f₁,
    ← moduleSheafFunctor_map_pullbackAdjPushforwardModules_unit_app_eq_homEquiv f]
  have e_rhs :
      (Sheaf.moduleSheafFunctor ((Stacks.SheafOfModules.Tensor.ringSheaf (J := X.J) X.O))).map
      (((pullbackAdjPushforwardModules f₂).comp (pullbackAdjPushforwardModules f₁)).unit.app M ≫
        (f₁.pushforwardModules ⋙ f₂.pushforwardModules).map
          (((pullbackModulesCompIso f₁ f₂).symm ≪≫
            pullbackModulesTransport f₁ f₂ f τ hτ).hom.app M)) =
      (Sheaf.moduleSheafFunctor ((Stacks.SheafOfModules.Tensor.ringSheaf (J := X.J) X.O))).map
          ((pullbackAdjPushforwardModules f₂).unit.app M) ≫
        f₂.toToposHom.pushforward.map
          ((Sheaf.moduleSheafFunctor
                ((Stacks.SheafOfModules.Tensor.ringSheaf (J := X'.J) X'.O))).map
              ((pullbackAdjPushforwardModules f₁).unit.app
                (f₂.toModulesHom.pullbackModules.obj M)) ≫
            f₁.toToposHom.pushforward.map
              ((Sheaf.moduleSheafFunctor
                  ((Stacks.SheafOfModules.Tensor.ringSheaf X''.O))).map
                (((pullbackModulesCompIso f₁ f₂).symm ≪≫
                  pullbackModulesTransport f₁ f₂ f τ hτ).hom.app M))) := by
    rw [Adjunction.comp_unit_app]
    refine Eq.trans (Sheaf.hom_ext_sections (m' :=
      (Sheaf.moduleSheafFunctor ((Stacks.SheafOfModules.Tensor.ringSheaf (J := X.J) X.O))).map
          ((pullbackAdjPushforwardModules f₂).unit.app M) ≫
        f₂.toToposHom.pushforward.map
          ((Sheaf.moduleSheafFunctor
                ((Stacks.SheafOfModules.Tensor.ringSheaf (J := X'.J) X'.O))).map
              ((pullbackAdjPushforwardModules f₁).unit.app
                (f₂.toModulesHom.pullbackModules.obj M))) ≫
        f₂.toToposHom.pushforward.map (f₁.toToposHom.pushforward.map
              ((Sheaf.moduleSheafFunctor
                  ((Stacks.SheafOfModules.Tensor.ringSheaf X''.O))).map
                (((pullbackModulesCompIso f₁ f₂).symm ≪≫
                  pullbackModulesTransport f₁ f₂ f τ hτ).hom.app M)))) fun _ _ => rfl) ?_
    exact congrArg (_ ≫ ·) (f₂.toToposHom.pushforward.map_comp _ _).symm
  have e_lhs :
      (Sheaf.moduleSheafFunctor ((Stacks.SheafOfModules.Tensor.ringSheaf (J := X.J) X.O))).map
      ((pullbackAdjPushforwardModules f).unit.app M ≫
        (pushforwardModulesIsoOfNatIso (f₂.comp f₁) f τ hτ).inv.app _ ≫
          (pushforwardModulesCompIso f₁ f₂).hom.app _) =
      (Sheaf.moduleSheafFunctor ((Stacks.SheafOfModules.Tensor.ringSheaf (J := X.J) X.O))).map
          ((pullbackAdjPushforwardModules f).unit.app M) ≫
        τ.inv.app (Sheaf.moduleSheaf ((Stacks.SheafOfModules.Tensor.ringSheaf X''.O))
          (f.toModulesHom.pullbackModules.obj M)) :=
    Sheaf.hom_ext_sections fun _ _ => rfl
  have hU' := e_lhs.symm.trans
    ((congrArg
      (Sheaf.moduleSheafFunctor ((Stacks.SheafOfModules.Tensor.ringSheaf (J := X.J) X.O))).map
      (unit_comp_pushforwardModulesCompIso f₁ f₂ f τ hτ M)).trans e_rhs)
  exact (Category.assoc _ _ _).symm.trans ((Iso.comp_inv_eq (τ.app _)).mp hU').symm

section Stalk

variable [LocallySmall.{w} X''.C] [LocallySmall.{w} X'.C] [LocallySmall.{w} X.C]
  (Φ'' : X''.J.Point.{w}) (Φ' : X'.J.Point.{w}) (Φ : X.J.Point.{w})

/-- An `eqToHom` between extensions of scalars along equal ring maps fixes `1 ⊗ m`. -/
theorem eqToHom_extendScalars_one_tmul {R S : Type w} [CommRing R] [CommRing S] {φ ψ : R →+* S}
    (h : φ = ψ) (N : ModuleCat.{w} R) (m : N) :
    eqToHom (congrArg (fun χ => (ModuleCat.extendScalars χ).obj N) h) ((1 : S) ⊗ₜ[R, φ] m) =
      (1 : S) ⊗ₜ[R, ψ] m := by
  subst h
  rfl

/-- A diagram chase in a category: the shape in which the fibre comparisons of a composite of
morphisms of topoi compose with the units `x ↦ 1 ⊗ x`. -/
theorem _root_.CategoryTheory.comp_eq_of_chase_inverseImage {C : Type*} [Category C]
    {P A₁ A₂ A₃ B₂ B₃ C₂ C₃ D R Q Q' : C}
    (e : P ⟶ Q) (E : Q ⟶ Q') (ιf : Q' ⟶ R) (a : P ⟶ A₁) (E₂ : A₁ ⟶ A₂) (i₂ : A₂ ⟶ A₃)
    (e₁A : A₂ ⟶ B₂) (e₁B : A₃ ⟶ B₃) (j : B₂ ⟶ B₃) (E₁A : B₂ ⟶ C₂) (E₁B : B₃ ⟶ C₃)
    (j' : C₂ ⟶ C₃) (i₁ : C₃ ⟶ D) (u : D ⟶ R) (ch : Q' ⟶ C₂) (ci : C₂ ⟶ Q')
    (n₁ : i₂ ≫ e₁B = e₁A ≫ j) (n₂ : j ≫ E₁B = E₁A ≫ j')
    (He : e ≫ E = a ≫ E₂ ≫ e₁A ≫ E₁A ≫ ci) (hci : ci ≫ ch = 𝟙 _)
    (hι : ιf = ch ≫ j' ≫ i₁ ≫ u) :
    e ≫ E ≫ ιf = a ≫ E₂ ≫ i₂ ≫ e₁B ≫ E₁B ≫ i₁ ≫ u := by
  rw [hι, ← Category.assoc e, He]
  simp only [Category.assoc, reassoc_of% hci, reassoc_of% n₁, reassoc_of% n₂]

/-- The image under a functor of the transport, along an equality of morphisms of topoi, of the
inverse image of a map. -/
theorem _root_.MorphismOfTopoi.map_inverseImage_map_eqToHom {E₀ F₀ : Type*} [Category E₀]
    [Category F₀] {T T' : MorphismOfTopoi E₀ F₀} (h : T = T') {G₀ : Type*} [Category G₀]
    (Fb : E₀ ⥤ G₀) {A B : F₀} (φ : A ⟶ B) :
    Fb.map (T'.inverseImage.map φ) ≫ Fb.map (eqToHom (congrArg
        (fun S : MorphismOfTopoi E₀ F₀ => S.inverseImage.obj B) h.symm)) =
      Fb.map (eqToHom (congrArg (fun S : MorphismOfTopoi E₀ F₀ => S.inverseImage.obj A) h.symm)) ≫
        Fb.map (T.inverseImage.map φ) := by
  subst h
  simp

/-- Identity transports inserted into a composite: the shape of the hypothesis on fibre
comparisons when the morphisms of topoi agree on the nose. -/
theorem _root_.CategoryTheory.comp_map_eqToHom_eq_of_refl {C C' D : Type*} [Category C]
    [Category C'] [Category D] (G : C ⥤ D) (G' : C' ⥤ D) {P : D} {A E : C} {B : C'}
    (u : P ⟶ G.obj A) (a : P ⟶ G'.obj B) (b : G'.obj B ⟶ G.obj E) (c : G.obj E ⟶ G.obj A)
    (p : A = A) (p₂ : B = B) (p₁ : E = E) (h : u = a ≫ b ≫ c) :
    u ≫ G.map (eqToHom p) = a ≫ G'.map (eqToHom p₂) ≫ b ≫ G.map (eqToHom p₁) ≫ c := by
  simp [h]

/-- A composite of five maps of modules evaluated at an element, computed one map at a time. -/
theorem _root_.ModuleCat.comp_apply_eq_of_apply_eq₅ {R : Type w} [Ring R]
    {M₀ M₁ M₂ M₃ M₄ M₅ : ModuleCat.{w} R} (a : M₀ ⟶ M₁) (b : M₁ ⟶ M₂) (c : M₂ ⟶ M₃)
    (d : M₃ ⟶ M₄) (e : M₄ ⟶ M₅) {x₀ : M₀} {x₁ : M₁} {x₂ : M₂} {x₃ : M₃} {x₄ : M₄} {x₅ : M₅}
    (ha : a x₀ = x₁) (hb : b x₁ = x₂) (hc : c x₂ = x₃) (hd : d x₃ = x₄) (he : e x₄ = x₅) :
    (a ≫ b ≫ c ≫ d ≫ e) x₀ = x₅ := by
  subst ha hb hc hd he
  rfl

omit [HasWeakSheafify X.J AddCommGrpCat.{w}] [X.J.WEqualsLocallyBijective AddCommGrpCat.{w}] in
/-- **Stacks 05V5 composes**, for an abstract composable pair of morphisms of ringed topoi and a
third one 2-isomorphic to the composite, at points whose fibre comparisons compose. -/
theorem stalkFunctorIso_inv_app_comp
    (k₁ : Stacks.Sheaves.RingedToposModules.RingedToposHom X'' X')
    (k₂ : Stacks.Sheaves.RingedToposModules.RingedToposHom X' X)
    (k : Stacks.Sheaves.RingedToposModules.RingedToposHom X'' X)
    (hk₁ : f₁.toModulesHom = k₁) (hk₂ : f₂.toModulesHom = k₂) (hk : f.toModulesHom = k)
    (hT₁ : f₁.toToposHom = k₁.toToposHom) (hT₂ : f₂.toToposHom = k₂.toToposHom)
    (hT : f.toToposHom = k.toToposHom)
    (e₁ : Φ'.sheafFiber (A := Type w) ≅ k₁.toToposHom.inverseImage ⋙ Φ''.sheafFiber (A := Type w))
    (e₂ : Φ.sheafFiber (A := Type w) ≅ k₂.toToposHom.inverseImage ⋙ Φ'.sheafFiber (A := Type w))
    (e : Φ.sheafFiber (A := Type w) ≅ k.toToposHom.inverseImage ⋙ Φ''.sheafFiber (A := Type w))
    (He : ∀ F : X.Topos, e.hom.app F ≫ (Φ''.sheafFiber (A := Type w)).map
        (eqToHom (congrArg (fun T : MorphismOfTopoi X''.Topos X.Topos => T.inverseImage.obj F)
          hT.symm)) =
      e₂.hom.app F ≫ (Φ'.sheafFiber (A := Type w)).map
        (eqToHom (congrArg (fun T : MorphismOfTopoi X'.Topos X.Topos => T.inverseImage.obj F)
          hT₂.symm)) ≫ e₁.hom.app (f₂.toToposHom.inverseImage.obj F) ≫
        (Φ''.sheafFiber (A := Type w)).map
          (eqToHom (congrArg (fun T : MorphismOfTopoi X''.Topos X'.Topos =>
            T.inverseImage.obj (f₂.toToposHom.inverseImage.obj F)) hT₁.symm)) ≫
        (Φ''.sheafFiber (A := Type w)).map
          (((conjugateIsoEquiv (f₂.comp f₁).toToposHom.adj f.toToposHom.adj).symm τ).inv.app F))
    (σ₁ : f₁.toModulesHom.pullbackModules ⋙ Stacks.sheafModuleFiberOfCommRing Φ'' X''.O ≅
      Stacks.sheafModuleFiberOfCommRing Φ' X'.O ⋙
        ModuleCat.extendScalars (Stacks.Sheaves.StalkPullback.stalkRingMap k₁ Φ'' Φ' e₁))
    (h₁ : f₁.toModulesHom.pullbackModules ⋙ Stacks.sheafModuleFiberOfCommRing Φ'' X''.O =
      Stacks.Sheaves.RingedToposModules.RingedToposHom.pullbackModules k₁ ⋙
        Stacks.sheafModuleFiberOfCommRing Φ'' X''.O)
    (hσ₁ : σ₁ = eqToIso h₁ ≪≫ Stacks.Sheaves.StalkPullback.stalkFunctorIso k₁ Φ'' Φ' e₁)
    (σ₂ : f₂.toModulesHom.pullbackModules ⋙ Stacks.sheafModuleFiberOfCommRing Φ' X'.O ≅
      Stacks.sheafModuleFiberOfCommRing Φ X.O ⋙
        ModuleCat.extendScalars (Stacks.Sheaves.StalkPullback.stalkRingMap k₂ Φ' Φ e₂))
    (h₂ : f₂.toModulesHom.pullbackModules ⋙ Stacks.sheafModuleFiberOfCommRing Φ' X'.O =
      Stacks.Sheaves.RingedToposModules.RingedToposHom.pullbackModules k₂ ⋙
        Stacks.sheafModuleFiberOfCommRing Φ' X'.O)
    (hσ₂ : σ₂ = eqToIso h₂ ≪≫ Stacks.Sheaves.StalkPullback.stalkFunctorIso k₂ Φ' Φ e₂)
    (σ : f.toModulesHom.pullbackModules ⋙ Stacks.sheafModuleFiberOfCommRing Φ'' X''.O ≅
      Stacks.sheafModuleFiberOfCommRing Φ X.O ⋙
        ModuleCat.extendScalars (Stacks.Sheaves.StalkPullback.stalkRingMap k Φ'' Φ e))
    (h : f.toModulesHom.pullbackModules ⋙ Stacks.sheafModuleFiberOfCommRing Φ'' X''.O =
      Stacks.Sheaves.RingedToposModules.RingedToposHom.pullbackModules k ⋙
        Stacks.sheafModuleFiberOfCommRing Φ'' X''.O)
    (hσ : σ = eqToIso h ≪≫ Stacks.Sheaves.StalkPullback.stalkFunctorIso k Φ'' Φ e)
    (hρ : Stacks.Sheaves.StalkPullback.stalkRingMap k Φ'' Φ e =
      (Stacks.Sheaves.StalkPullback.stalkRingMap k₁ Φ'' Φ' e₁).comp
        (Stacks.Sheaves.StalkPullback.stalkRingMap k₂ Φ' Φ e₂))
    (M : SheafOfModules.{w} ((Stacks.SheafOfModules.Tensor.ringSheaf (J := X.J) X.O))) :
    σ.inv.app M =
      eqToHom (congrArg (fun χ => (ModuleCat.extendScalars χ).obj
          ((Stacks.sheafModuleFiberOfCommRing Φ X.O).obj M)) hρ) ≫
        (ModuleCat.extendScalarsComp (Stacks.Sheaves.StalkPullback.stalkRingMap k₂ Φ' Φ e₂)
          (Stacks.Sheaves.StalkPullback.stalkRingMap k₁ Φ'' Φ' e₁)).hom.app _ ≫
        (ModuleCat.extendScalars (Stacks.Sheaves.StalkPullback.stalkRingMap k₁ Φ'' Φ' e₁)).map
          (σ₂.inv.app M) ≫
        σ₁.inv.app (f₂.toModulesHom.pullbackModules.obj M) ≫
        (Stacks.sheafModuleFiberOfCommRing Φ'' X''.O).map
          (((pullbackModulesCompIso f₁ f₂).symm ≪≫
            pullbackModulesTransport f₁ f₂ f τ hτ).hom.app M) := by
  refine ModuleCat.ExtendScalars.hom_ext fun m => ?_
  obtain ⟨z, rfl⟩ := (Stacks.Sheaves.StalkTransport.bijective_moduleStalkComparison Φ
    ((Stacks.SheafOfModules.Tensor.ringSheaf X.O)) M).2 m
  refine (Stacks.Sheaves.StalkPullback.iso_inv_app_one_tmul_of_eq_stalkFunctorIso Φ'' Φ f k hk hT
    e σ h hσ M z).trans ?_
  have s1 := eqToHom_extendScalars_one_tmul hρ ((Stacks.sheafModuleFiberOfCommRing Φ X.O).obj M)
    (Stacks.Sheaves.StalkTransport.moduleStalkComparison Φ
      ((Stacks.SheafOfModules.Tensor.ringSheaf X.O)) M z)
  have s2 := ModuleCat.extendScalarsComp_hom_app_one_tmul
    (Stacks.Sheaves.StalkPullback.stalkRingMap k₂ Φ' Φ e₂)
    (Stacks.Sheaves.StalkPullback.stalkRingMap k₁ Φ'' Φ' e₁)
    ((Stacks.sheafModuleFiberOfCommRing Φ X.O).obj M)
    (Stacks.Sheaves.StalkTransport.moduleStalkComparison Φ
      ((Stacks.SheafOfModules.Tensor.ringSheaf X.O)) M z)
  have s3 := (ModuleCat.ExtendScalars.map_tmul
    (Stacks.Sheaves.StalkPullback.stalkRingMap k₁ Φ'' Φ' e₁) (σ₂.inv.app M) 1 _).trans
    (congrArg (fun t => (1 : Stacks.ringFiber Φ'' X''.O.obj) ⊗ₜ[Stacks.ringFiber Φ' X'.O.obj,
      Stacks.Sheaves.StalkPullback.stalkRingMap k₁ Φ'' Φ' e₁] t)
      (Stacks.Sheaves.StalkPullback.iso_inv_app_one_tmul_of_eq_stalkFunctorIso Φ' Φ f₂ k₂ hk₂
        hT₂ e₂ σ₂ h₂ hσ₂ M z))
  let y := (Φ'.sheafFiber (A := Type w)).map (f₂.pullbackOneTmul M)
    ((Φ'.sheafFiber (A := Type w)).map
      (eqToHom (congrArg (fun T : MorphismOfTopoi X'.Topos X.Topos =>
        T.inverseImage.obj (Sheaf.moduleSheaf
          ((Stacks.SheafOfModules.Tensor.ringSheaf X.O)) M)) hT₂.symm))
      (e₂.hom.app _ z))
  have s4 := Stacks.Sheaves.StalkPullback.iso_inv_app_one_tmul_of_eq_stalkFunctorIso Φ'' Φ' f₁ k₁
    hk₁ hT₁ e₁ σ₁ h₁ hσ₁ (f₂.toModulesHom.pullbackModules.obj M) y
  have s5 := (Stacks.Sheaves.StalkTransport.moduleStalkComparison_naturality Φ''
    ((Stacks.SheafOfModules.Tensor.ringSheaf X''.O))
    (((pullbackModulesCompIso f₁ f₂).symm ≪≫ pullbackModulesTransport f₁ f₂ f τ hτ).hom.app M)
    ((Φ''.sheafFiber (A := Type w)).map (f₁.pullbackOneTmul (f₂.toModulesHom.pullbackModules.obj M))
      ((Φ''.sheafFiber (A := Type w)).map
        (eqToHom (congrArg (fun T : MorphismOfTopoi X''.Topos X'.Topos =>
          T.inverseImage.obj (Sheaf.moduleSheaf
            ((Stacks.SheafOfModules.Tensor.ringSheaf X'.O))
              (f₂.toModulesHom.pullbackModules.obj M)))
            hT₁.symm))
        (e₁.hom.app _ y)))).symm
  refine Eq.trans ?_ (ModuleCat.comp_apply_eq_of_apply_eq₅ _ _ _ _ _ s1 s2 s3 s4 s5).symm
  have hGII := (congrArg (Φ''.sheafFiber (A := Type w)).map
    (pullbackOneTmul_comp f₁ f₂ f τ hτ M)).trans
    (((Φ''.sheafFiber (A := Type w)).map_comp _ _).trans (congrArg (_ ≫ ·)
      (((Φ''.sheafFiber (A := Type w)).map_comp _ _).trans (congrArg (_ ≫ ·)
        ((Φ''.sheafFiber (A := Type w)).map_comp _ _)))))
  have hcomp : (Φ''.sheafFiber (A := Type w)).map
      (((conjugateIsoEquiv (f₂.comp f₁).toToposHom.adj f.toToposHom.adj).symm τ).inv.app
        (Sheaf.moduleSheaf ((Stacks.SheafOfModules.Tensor.ringSheaf X.O)) M)) ≫
      (Φ''.sheafFiber (A := Type w)).map
      (((conjugateIsoEquiv (f₂.comp f₁).toToposHom.adj f.toToposHom.adj).symm τ).hom.app
        (Sheaf.moduleSheaf ((Stacks.SheafOfModules.Tensor.ringSheaf X.O)) M)) = 𝟙 _ := by
    rw [← CategoryTheory.Functor.map_comp, Iso.inv_hom_id_app, CategoryTheory.Functor.map_id]
  have key := CategoryTheory.comp_eq_of_chase_inverseImage _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _
    (e₁.hom.naturality (f₂.pullbackOneTmul M))
    (MorphismOfTopoi.map_inverseImage_map_eqToHom hT₁ (Φ''.sheafFiber (A := Type w))
      (f₂.pullbackOneTmul M))
    (He (Sheaf.moduleSheaf ((Stacks.SheafOfModules.Tensor.ringSheaf X.O)) M))
    hcomp hGII
  have hz := ConcreteCategory.congr_hom key z
  simp only [ConcreteCategory.comp_apply] at hz
  exact congrArg (Stacks.Sheaves.StalkTransport.moduleStalkComparison Φ''
    ((Stacks.SheafOfModules.Tensor.ringSheaf X''.O)) (f.toModulesHom.pullbackModules.obj M)) hz

omit [HasWeakSheafify X.J AddCommGrpCat.{w}] [X.J.WEqualsLocallyBijective AddCommGrpCat.{w}] in
/-- `AlgebraicGeometry.RingedToposHom.stalkFunctorIso_inv_app_comp` for the four-field forms
`toRingedToposModulesHom`, whose underlying morphisms of topoi are those of the two-field ones. -/
theorem stalkFunctorIso_inv_app_comp_toRingedToposModulesHom
    (e₁ : Φ'.sheafFiber (A := Type w) ≅ f₁.toToposHom.inverseImage ⋙ Φ''.sheafFiber (A := Type w))
    (e₂ : Φ.sheafFiber (A := Type w) ≅ f₂.toToposHom.inverseImage ⋙ Φ'.sheafFiber (A := Type w))
    (e : Φ.sheafFiber (A := Type w) ≅ f.toToposHom.inverseImage ⋙ Φ''.sheafFiber (A := Type w))
    (He : ∀ F : X.Topos, e.hom.app F =
      e₂.hom.app F ≫ e₁.hom.app (f₂.toToposHom.inverseImage.obj F) ≫
        (Φ''.sheafFiber (A := Type w)).map
          (((conjugateIsoEquiv (f₂.comp f₁).toToposHom.adj f.toToposHom.adj).symm τ).inv.app F))
    (σ₁ : f₁.toModulesHom.pullbackModules ⋙ Stacks.sheafModuleFiberOfCommRing Φ'' X''.O ≅
      Stacks.sheafModuleFiberOfCommRing Φ' X'.O ⋙ ModuleCat.extendScalars
        (Stacks.Sheaves.StalkPullback.stalkRingMap f₁.toRingedToposModulesHom Φ'' Φ' e₁))
    (hσ₁ : σ₁ = eqToIso (congrArg (· ⋙ Stacks.sheafModuleFiberOfCommRing Φ'' X''.O)
        (pullbackModules_eq_pullbackModules_toRingedToposModulesHom f₁)) ≪≫
      Stacks.Sheaves.StalkPullback.stalkFunctorIso f₁.toRingedToposModulesHom Φ'' Φ' e₁)
    (σ₂ : f₂.toModulesHom.pullbackModules ⋙ Stacks.sheafModuleFiberOfCommRing Φ' X'.O ≅
      Stacks.sheafModuleFiberOfCommRing Φ X.O ⋙ ModuleCat.extendScalars
        (Stacks.Sheaves.StalkPullback.stalkRingMap f₂.toRingedToposModulesHom Φ' Φ e₂))
    (hσ₂ : σ₂ = eqToIso (congrArg (· ⋙ Stacks.sheafModuleFiberOfCommRing Φ' X'.O)
        (pullbackModules_eq_pullbackModules_toRingedToposModulesHom f₂)) ≪≫
      Stacks.Sheaves.StalkPullback.stalkFunctorIso f₂.toRingedToposModulesHom Φ' Φ e₂)
    (σ : f.toModulesHom.pullbackModules ⋙ Stacks.sheafModuleFiberOfCommRing Φ'' X''.O ≅
      Stacks.sheafModuleFiberOfCommRing Φ X.O ⋙ ModuleCat.extendScalars
        (Stacks.Sheaves.StalkPullback.stalkRingMap f.toRingedToposModulesHom Φ'' Φ e))
    (hσ : σ = eqToIso (congrArg (· ⋙ Stacks.sheafModuleFiberOfCommRing Φ'' X''.O)
        (pullbackModules_eq_pullbackModules_toRingedToposModulesHom f)) ≪≫
      Stacks.Sheaves.StalkPullback.stalkFunctorIso f.toRingedToposModulesHom Φ'' Φ e)
    (hρ : Stacks.Sheaves.StalkPullback.stalkRingMap f.toRingedToposModulesHom Φ'' Φ e =
      (Stacks.Sheaves.StalkPullback.stalkRingMap f₁.toRingedToposModulesHom Φ'' Φ' e₁).comp
        (Stacks.Sheaves.StalkPullback.stalkRingMap f₂.toRingedToposModulesHom Φ' Φ e₂))
    (M : SheafOfModules.{w} ((Stacks.SheafOfModules.Tensor.ringSheaf (J := X.J) X.O))) :
    σ.inv.app M =
      eqToHom (congrArg (fun χ => (ModuleCat.extendScalars χ).obj
          ((Stacks.sheafModuleFiberOfCommRing Φ X.O).obj M)) hρ) ≫
        (ModuleCat.extendScalarsComp
          (Stacks.Sheaves.StalkPullback.stalkRingMap f₂.toRingedToposModulesHom Φ' Φ e₂)
          (Stacks.Sheaves.StalkPullback.stalkRingMap f₁.toRingedToposModulesHom Φ'' Φ'
            e₁)).hom.app _ ≫
        (ModuleCat.extendScalars
          (Stacks.Sheaves.StalkPullback.stalkRingMap f₁.toRingedToposModulesHom Φ'' Φ' e₁)).map
          (σ₂.inv.app M) ≫
        σ₁.inv.app (f₂.toModulesHom.pullbackModules.obj M) ≫
        (Stacks.sheafModuleFiberOfCommRing Φ'' X''.O).map
          (((pullbackModulesCompIso f₁ f₂).symm ≪≫
            pullbackModulesTransport f₁ f₂ f τ hτ).hom.app M) := by
  refine stalkFunctorIso_inv_app_comp f₁ f₂ f τ hτ Φ'' Φ' Φ f₁.toRingedToposModulesHom
    f₂.toRingedToposModulesHom f.toRingedToposModulesHom
    (toModulesHom_eq_toRingedToposModulesHom f₁) (toModulesHom_eq_toRingedToposModulesHom f₂)
    (toModulesHom_eq_toRingedToposModulesHom f) rfl rfl rfl e₁ e₂ e (fun F => ?_) σ₁
    (congrArg (· ⋙ Stacks.sheafModuleFiberOfCommRing Φ'' X''.O)
      (pullbackModules_eq_pullbackModules_toRingedToposModulesHom f₁)) hσ₁ σ₂
    (congrArg (· ⋙ Stacks.sheafModuleFiberOfCommRing Φ' X'.O)
      (pullbackModules_eq_pullbackModules_toRingedToposModulesHom f₂)) hσ₂ σ
    (congrArg (· ⋙ Stacks.sheafModuleFiberOfCommRing Φ'' X''.O)
      (pullbackModules_eq_pullbackModules_toRingedToposModulesHom f)) hσ hρ M
  exact CategoryTheory.comp_map_eqToHom_eq_of_refl (Φ''.sheafFiber (A := Type w))
    (Φ'.sheafFiber (A := Type w)) (e.hom.app F) (e₂.hom.app F)
    (e₁.hom.app (f₂.toToposHom.inverseImage.obj F))
    ((Φ''.sheafFiber (A := Type w)).map
      (((conjugateIsoEquiv (f₂.comp f₁).toToposHom.adj f.toToposHom.adj).symm τ).inv.app F))
    _ _ _ (He F)

omit [HasWeakSheafify X.J AddCommGrpCat.{w}] [X.J.WEqualsLocallyBijective AddCommGrpCat.{w}] in
/-- `AlgebraicGeometry.RingedToposHom.stalkFunctorIso_inv_app_comp_toRingedToposModulesHom` with
the inverse-image comparison and the transported pullback given in any spelling. -/
theorem stalkFunctorIso_inv_app_comp_of_eq
    (e₁ : Φ'.sheafFiber (A := Type w) ≅ f₁.toToposHom.inverseImage ⋙ Φ''.sheafFiber (A := Type w))
    (e₂ : Φ.sheafFiber (A := Type w) ≅ f₂.toToposHom.inverseImage ⋙ Φ'.sheafFiber (A := Type w))
    (e : Φ.sheafFiber (A := Type w) ≅ f.toToposHom.inverseImage ⋙ Φ''.sheafFiber (A := Type w))
    (c : f.toToposHom.inverseImage ≅ f₂.toToposHom.inverseImage ⋙ f₁.toToposHom.inverseImage)
    (hc : (conjugateIsoEquiv (f₂.comp f₁).toToposHom.adj f.toToposHom.adj).symm τ = c)
    (He : ∀ F : X.Topos, e.hom.app F =
      e₂.hom.app F ≫ e₁.hom.app (f₂.toToposHom.inverseImage.obj F) ≫
        (Φ''.sheafFiber (A := Type w)).map (c.inv.app F))
    (PT : (f₂.comp f₁).toModulesHom.pullbackModules ≅ f.toModulesHom.pullbackModules)
    (hPT : pullbackModulesTransport f₁ f₂ f τ hτ = PT)
    (σ₁ : f₁.toModulesHom.pullbackModules ⋙ Stacks.sheafModuleFiberOfCommRing Φ'' X''.O ≅
      Stacks.sheafModuleFiberOfCommRing Φ' X'.O ⋙ ModuleCat.extendScalars
        (Stacks.Sheaves.StalkPullback.stalkRingMap f₁.toRingedToposModulesHom Φ'' Φ' e₁))
    (hσ₁ : σ₁ = eqToIso (congrArg (· ⋙ Stacks.sheafModuleFiberOfCommRing Φ'' X''.O)
        (pullbackModules_eq_pullbackModules_toRingedToposModulesHom f₁)) ≪≫
      Stacks.Sheaves.StalkPullback.stalkFunctorIso f₁.toRingedToposModulesHom Φ'' Φ' e₁)
    (σ₂ : f₂.toModulesHom.pullbackModules ⋙ Stacks.sheafModuleFiberOfCommRing Φ' X'.O ≅
      Stacks.sheafModuleFiberOfCommRing Φ X.O ⋙ ModuleCat.extendScalars
        (Stacks.Sheaves.StalkPullback.stalkRingMap f₂.toRingedToposModulesHom Φ' Φ e₂))
    (hσ₂ : σ₂ = eqToIso (congrArg (· ⋙ Stacks.sheafModuleFiberOfCommRing Φ' X'.O)
        (pullbackModules_eq_pullbackModules_toRingedToposModulesHom f₂)) ≪≫
      Stacks.Sheaves.StalkPullback.stalkFunctorIso f₂.toRingedToposModulesHom Φ' Φ e₂)
    (σ : f.toModulesHom.pullbackModules ⋙ Stacks.sheafModuleFiberOfCommRing Φ'' X''.O ≅
      Stacks.sheafModuleFiberOfCommRing Φ X.O ⋙ ModuleCat.extendScalars
        (Stacks.Sheaves.StalkPullback.stalkRingMap f.toRingedToposModulesHom Φ'' Φ e))
    (hσ : σ = eqToIso (congrArg (· ⋙ Stacks.sheafModuleFiberOfCommRing Φ'' X''.O)
        (pullbackModules_eq_pullbackModules_toRingedToposModulesHom f)) ≪≫
      Stacks.Sheaves.StalkPullback.stalkFunctorIso f.toRingedToposModulesHom Φ'' Φ e)
    (hρ : Stacks.Sheaves.StalkPullback.stalkRingMap f.toRingedToposModulesHom Φ'' Φ e =
      (Stacks.Sheaves.StalkPullback.stalkRingMap f₁.toRingedToposModulesHom Φ'' Φ' e₁).comp
        (Stacks.Sheaves.StalkPullback.stalkRingMap f₂.toRingedToposModulesHom Φ' Φ e₂))
    (M : SheafOfModules.{w} ((Stacks.SheafOfModules.Tensor.ringSheaf (J := X.J) X.O))) :
    σ.inv.app M =
      eqToHom (congrArg (fun χ => (ModuleCat.extendScalars χ).obj
          ((Stacks.sheafModuleFiberOfCommRing Φ X.O).obj M)) hρ) ≫
        (ModuleCat.extendScalarsComp
          (Stacks.Sheaves.StalkPullback.stalkRingMap f₂.toRingedToposModulesHom Φ' Φ e₂)
          (Stacks.Sheaves.StalkPullback.stalkRingMap f₁.toRingedToposModulesHom Φ'' Φ'
            e₁)).hom.app _ ≫
        (ModuleCat.extendScalars
          (Stacks.Sheaves.StalkPullback.stalkRingMap f₁.toRingedToposModulesHom Φ'' Φ' e₁)).map
          (σ₂.inv.app M) ≫
        σ₁.inv.app (f₂.toModulesHom.pullbackModules.obj M) ≫
        (Stacks.sheafModuleFiberOfCommRing Φ'' X''.O).map
          (((pullbackModulesCompIso f₁ f₂).symm ≪≫ PT).hom.app M) := by
  subst hc hPT
  exact stalkFunctorIso_inv_app_comp_toRingedToposModulesHom f₁ f₂ f τ hτ Φ'' Φ' Φ e₁ e₂ e He
    σ₁ hσ₁ σ₂ hσ₂ σ hσ hρ M

end Stalk

end Comp

end AlgebraicGeometry.RingedToposHom

namespace AlgebraicGeometry.Space

attribute [local instance 20000] AddCommGrpCat.FilteredColimits.forget_preservesFilteredColimits
attribute [local instance 5000] SmallEtale.instHasSheafify SmallEtale.instWEqualsLocallyBijective

variable {B : BigFppfSite.{u}} {S : Scheme.{u}} {hS : B.Contains S}
  {X'' X' X : AlgebraicSpaces B S hS}

/-- The homomorphisms of stalk rings along which Stacks 05V5 extends scalars compose. -/
theorem smallEtaleStalkPullbackRingMap_comp (g₁ : X'' ⟶ X') (g₂ : X' ⟶ X)
    (x : GeometricPoint B S hS X''.1) :
    smallEtaleStalkPullbackRingMap B S hS (g₁ ≫ g₂) x =
      (smallEtaleStalkPullbackRingMap B S hS g₁ x).comp
        (smallEtaleStalkPullbackRingMap B S hS g₂ (geometricPointMap g₁.hom x)) := by
  simp only [← stalkStructureMap_hom_eq_smallEtaleStalkPullbackRingMap_derived]
  exact stalkStructureMap_comp_hom B S hS g₁ g₂ x

/-- **Stacks 05V5 composes at geometric points.** For `g₁ : X'' ⟶ X'`, `g₂ : X' ⟶ X` and a
geometric point `x̄` of `X''`, the comparison `M_{x̄} ⊗ 𝒪_{X'',x̄} ≅ ((g₁ ≫ g₂)^*M)_{x̄}` is the
comparison for `g₂` at `g₁(x̄)`, extended to `𝒪_{X'',x̄}`, followed by the comparison for `g₁`
at `x̄` and the comparison `g₁^* g₂^* ≅ (g₁ ≫ g₂)^*`. -/
theorem pullbackStalkFunctorIso_comp_inv_app (g₁ : X'' ⟶ X') (g₂ : X' ⟶ X)
    (x : GeometricPoint B S hS X''.1)
    (M : SheafOfModules.{u} (ringedToposStructureRingSheaf B S hS X)) :
    (pullbackStalkFunctorIso (g₁ ≫ g₂) x).inv.app M =
      eqToHom (congrArg (fun χ => (ModuleCat.extendScalars χ).obj
          ((Stacks.sheafModuleFiberOfCommRing
            (etaleSitePoint B S hS X.1 (geometricPointMap g₂.hom (geometricPointMap g₁.hom x)) X.2)
            (smallEtaleRingedTopos B S hS X).O).obj M))
          (smallEtaleStalkPullbackRingMap_comp g₁ g₂ x)) ≫
        (ModuleCat.extendScalarsComp
          (smallEtaleStalkPullbackRingMap B S hS g₂ (geometricPointMap g₁.hom x))
          (smallEtaleStalkPullbackRingMap B S hS g₁ x)).hom.app _ ≫
        (ModuleCat.extendScalars (smallEtaleStalkPullbackRingMap B S hS g₁ x)).map
          ((pullbackStalkFunctorIso g₂ (geometricPointMap g₁.hom x)).inv.app M) ≫
        (pullbackStalkFunctorIso g₁ x).inv.app
          ((smallEtaleRingedToposHom B S hS g₂).toModulesHom.pullbackModules.obj M) ≫
        (Stacks.sheafModuleFiberOfCommRing (etaleSitePoint B S hS X''.1 x X''.2)
          (smallEtaleRingedTopos B S hS X'').O).map
          (((RingedToposHom.pullbackModulesCompIso (smallEtaleRingedToposHom B S hS g₁)
            (smallEtaleRingedToposHom B S hS g₂)).symm ≪≫
              pullbackModulesCompTransport B S hS g₁ g₂).hom.app M) :=
  RingedToposHom.stalkFunctorIso_inv_app_comp_of_eq
    (X'' := smallEtaleRingedTopos B S hS X'') (X' := smallEtaleRingedTopos B S hS X')
    (X := smallEtaleRingedTopos B S hS X)
    (smallEtaleRingedToposHom B S hS g₁) (smallEtaleRingedToposHom B S hS g₂)
    (smallEtaleRingedToposHom B S hS (g₁ ≫ g₂)) (smallToposMorphismTypeU_comp B S hS g₁ g₂)
    (smallEtaleRingedToposHom_comp_fSharpRing B S hS g₁ g₂)
    (etaleSitePoint B S hS X''.1 x X''.2)
    (etaleSitePoint B S hS X'.1 (geometricPointMap g₁.hom x) X'.2)
    (etaleSitePoint B S hS X.1 (geometricPointMap g₂.hom (geometricPointMap g₁.hom x)) X.2)
    (smallEtaleInverseImageFiberIso B S hS g₁ x)
    (smallEtaleInverseImageFiberIso B S hS g₂ (geometricPointMap g₁.hom x))
    (smallEtaleInverseImageFiberIso B S hS (g₁ ≫ g₂) x)
    (smallEtaleInverseImageCompIso B S hS g₁ g₂) rfl
    (smallEtaleInverseImageFiberIso_comp_hom_app B S hS g₁ g₂ x)
    (pullbackModulesCompTransport B S hS g₁ g₂) rfl
    (pullbackStalkFunctorIso g₁ x) rfl (pullbackStalkFunctorIso g₂ (geometricPointMap g₁.hom x)) rfl
    (pullbackStalkFunctorIso (g₁ ≫ g₂) x) rfl (smallEtaleStalkPullbackRingMap_comp g₁ g₂ x) M

end AlgebraicGeometry.Space
