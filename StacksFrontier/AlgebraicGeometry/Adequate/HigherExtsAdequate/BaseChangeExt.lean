module

public import StacksFrontier.AlgebraicGeometry.Adequate.AdequateFunctors.Descent
public import StacksFrontier.AlgebraicGeometry.Adequate.AdequateFunctors.Restriction
public import StacksFrontier.AlgebraicGeometry.Adequate.HigherExtsAdequate.Basic
public import StacksFrontier.AlgebraicGeometry.RestrictionExact.OverExact
public import StacksFrontier.CategoryTheory.Abelian.ExtAdjunction

/-!
# Extension groups of module-valued functors along a change of base ring

Let `f : A → A'` be a homomorphism of commutative rings. Restriction of a module-valued functor
from `A`-algebras to `A'`-algebras is left adjoint to the functor `G ↦ (B ↦ G(A' ⊗[A] B))`, and
both functors are exact. Consequently
`Ext^n(F, B ↦ G(A' ⊗[A] B)) ≃ Ext^n(F|_{A'}, G)` for every `n`, and these groups vanish in
positive degrees whenever `F|_{A'}` is projective.

## Main results

* `AdequateFunctor.presheafPushforwardAdjunction`: an adjunction `F ⊣ G` of index categories,
  compatible with the ring maps, makes the two pushforwards of presheaves of modules adjoint.
* `AdequateFunctor.restrictFunctorAdjunction`: restriction of module-valued functors is left
  adjoint to `G ↦ (B ↦ G(A' ⊗[A] B))`.
* `AdequateFunctor.preservesFiniteColimits_presheafPushforward`: pushforward of presheaves of
  modules is right exact (left exactness is
  `Stacks.AlgebraicGeometry.RestrictionExact.preservesFiniteLimits_presheafPushforward`).
* `AdequateFunctor.extMap_restrictFunctorAdjunction_bijective`: the comparison of extension
  groups along the adjunction is bijective in every degree.
* `AdequateFunctor.subsingleton_ext_pushforward_of_projective_restrictFunctor`: if `F|_{A'}` is
  projective then `Ext^{n+1}(F, B ↦ G(A' ⊗[A] B))` vanishes.

## Implementation notes

The algebras live in `CommAlgCat.{u}` with `A A' : Type u`, the universe of the existing
`AdequateFunctor.baseChangeFunctor` and `AdequateFunctor.pushforward`, and the values in
`Type (max (u + 1) w)`, so that the category of module-valued functors on `A'`-algebras has
enough injectives (`AdequateFunctor.moduleValuedFunctor_enoughInjectives`).

## References

* [Stacks Project, Tag 06V9](https://stacks.math.columbia.edu/tag/06V9)
* [Stacks Project, Tag 06VA](https://stacks.math.columbia.edu/tag/06VA)
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits Opposite

universe w t t' v₁ v₂ u₁ u₂ u

namespace AdequateFunctor

section PushforwardAdjunction

variable {C : Type u₁} [Category.{v₁} C] {D : Type u₂} [Category.{v₂} D] {F : C ⥤ D} {G : D ⥤ C}
  (adj : F ⊣ G) {S : Cᵒᵖ ⥤ RingCat.{u}} {R : Dᵒᵖ ⥤ RingCat.{u}}
  (φ : S ⟶ F.op ⋙ R) (ψ : R ⟶ G.op ⋙ S)
  (H₁ : ∀ Y : D, R.map (adj.counit.app Y).op = ψ.app (op Y) ≫ φ.app (op (G.obj Y)))
  (H₂ : ∀ X : C, φ.app (op X) ≫ ψ.app (op (F.obj X)) ≫ S.map (adj.unit.app X).op = 𝟙 _)

/-- The unit of `presheafPushforwardAdjunction`: restriction along the counit of `F ⊣ G`. -/
noncomputable def presheafPushforwardUnit :
    𝟭 (PresheafOfModules.{w} R) ⟶
      PresheafOfModules.pushforward.{w} φ ⋙ PresheafOfModules.pushforward.{w} ψ where
  app M :=
    { app Y := ModuleCat.ofHom (X := M.obj Y)
        (Y := ((PresheafOfModules.pushforward.{w} ψ).obj
          ((PresheafOfModules.pushforward.{w} φ).obj M)).obj Y)
        { toFun x := M.map (adj.counit.app Y.unop).op x
          map_add' x y := map_add (M.map (adj.counit.app Y.unop).op).hom x y
          map_smul' r x := by
            have h := congrArg (fun k => k.hom r) (H₁ Y.unop)
            simp only [RingCat.hom_comp, RingHom.comp_apply] at h
            exact (PresheafOfModules.map_smul M (adj.counit.app Y.unop).op r x).trans
              (congrArg (fun s => s • (M.map (adj.counit.app Y.unop).op x)) h) }
      naturality {Y Y'} g := by
        ext x
        change M.map (adj.counit.app Y'.unop).op (M.map g x) =
          M.map (F.map (G.map g.unop)).op (M.map (adj.counit.app Y.unop).op x)
        have key : g ≫ (adj.counit.app Y'.unop).op =
            (adj.counit.app Y.unop).op ≫ (F.map (G.map g.unop)).op :=
          Quiver.Hom.unop_inj (adj.counit.naturality g.unop).symm
        rw [← PresheafOfModules.map_comp_apply, ← PresheafOfModules.map_comp_apply]
        exact M.congr_map_apply key x }
  naturality := by
    intro M M' α
    refine PresheafOfModules.hom_ext fun Y => ?_
    ext x
    exact (PresheafOfModules.naturality_apply α (adj.counit.app Y.unop).op x).symm

/-- The counit of `presheafPushforwardAdjunction`: restriction along the unit of `F ⊣ G`. -/
noncomputable def presheafPushforwardCounit :
    PresheafOfModules.pushforward.{w} ψ ⋙ PresheafOfModules.pushforward.{w} φ ⟶
      𝟭 (PresheafOfModules.{w} S) where
  app N :=
    { app X := ModuleCat.ofHom
        (X := ((PresheafOfModules.pushforward.{w} φ).obj
          ((PresheafOfModules.pushforward.{w} ψ).obj N)).obj X) (Y := N.obj X)
        { toFun x := N.map (adj.unit.app X.unop).op x
          map_add' x y := map_add (N.map (adj.unit.app X.unop).op).hom x y
          map_smul' r x := by
            have h := congrArg (fun k => k.hom r) (H₂ X.unop)
            simp only [RingCat.hom_comp, RingHom.comp_apply, RingCat.hom_id,
              RingHom.id_apply] at h
            exact (PresheafOfModules.map_smul N (adj.unit.app X.unop).op
              ((ψ.app _).hom ((φ.app X).hom r)) x).trans
              (congrArg (fun s => s • (N.map (adj.unit.app X.unop).op x)) h) }
      naturality {X X'} g := by
        have key : (G.map (F.map g.unop)).op ≫ (adj.unit.app X'.unop).op =
            (adj.unit.app X.unop).op ≫ g :=
          Quiver.Hom.unop_inj (adj.unit.naturality g.unop).symm
        have h : ∀ y : N.obj (op (G.obj (F.obj X.unop))),
            N.map (adj.unit.app X'.unop).op (N.map (G.map (F.map g.unop)).op y) =
              N.map g (N.map (adj.unit.app X.unop).op y) := fun y => by
          rw [← PresheafOfModules.map_comp_apply, ← PresheafOfModules.map_comp_apply]
          exact N.congr_map_apply key y
        ext x
        exact h x }
  naturality := by
    intro N N' α
    refine PresheafOfModules.hom_ext fun X => ?_
    have h : ∀ y : N.obj (op (G.obj (F.obj X.unop))),
        N'.map (adj.unit.app X.unop).op (α.app _ y) =
          α.app X (N.map (adj.unit.app X.unop).op y) := fun y =>
      (PresheafOfModules.naturality_apply α (adj.unit.app X.unop).op y).symm
    ext x
    exact h x

/-- An adjunction `F ⊣ G` of index categories, compatible with the ring maps, makes the two
pushforwards of presheaves of modules adjoint. -/
noncomputable def presheafPushforwardAdjunction :
    PresheafOfModules.pushforward.{w} φ ⊣ PresheafOfModules.pushforward.{w} ψ where
  unit := presheafPushforwardUnit (adj := adj) (φ := φ) (ψ := ψ) H₁
  counit := presheafPushforwardCounit (adj := adj) (φ := φ) (ψ := ψ) H₂
  left_triangle_components M := by
    refine PresheafOfModules.hom_ext fun X => ?_
    have h : ∀ y : M.obj (op (F.obj X.unop)),
        M.map (F.map (adj.unit.app X.unop)).op (M.map (adj.counit.app (F.obj X.unop)).op y)
          = y := fun y => by
      rw [← PresheafOfModules.map_comp_apply, ← op_comp]
      exact (M.congr_map_apply (congrArg Quiver.Hom.op (adj.left_triangle_components X.unop))
        y).trans (by simp; rfl)
    ext x
    exact h x
  right_triangle_components N := by
    refine PresheafOfModules.hom_ext fun Y => ?_
    have h : ∀ y : N.obj (op (G.obj Y.unop)),
        N.map (adj.unit.app (G.obj Y.unop)).op (N.map (G.map (adj.counit.app Y.unop)).op y)
          = y := fun y => by
      rw [← PresheafOfModules.map_comp_apply, ← op_comp, adj.right_triangle_components]
      simp
      rfl
    ext x
    exact h x

end PushforwardAdjunction

section BaseChange

variable {A A' : Type u} [CommRing A] [CommRing A'] (f : A →+* A')

/-- The counit compatibility `H₁` of `presheafPushforwardAdjunction` for the opposite of the
base-change adjunction: the ring map along the counit is the composite of the base-change and
restriction ring maps. -/
lemma baseChangeRingDiagram_counit (Y : (CommAlgCat.{u} A)ᵒᵖ) :
    (algebraRingDiagram.{u} A).map ((baseChangeAdjunction f).op.counit.app Y).op =
      (baseChangeRingHom f).app (op Y) ≫
        (restrictRingDiagram.{u} f).app (op ((baseChangeFunctor f).op.obj Y)) := by
  ext x
  rfl

/-- The unit compatibility `H₂` of `presheafPushforwardAdjunction` for the base-change
adjunction: restriction, then base change, then the ring map along the unit, is the identity. -/
lemma baseChangeRingDiagram_unit (X : (CommAlgCat.{u} A')ᵒᵖ) :
    (restrictRingDiagram.{u} f).app (op X) ≫
        (baseChangeRingHom f).app (op ((restrictAlgebras f).op.obj X)) ≫
          (algebraRingDiagram.{u} A').map ((baseChangeAdjunction f).op.unit.app X).op =
      𝟙 _ := by
  ext x
  exact congrArg (fun g => g.hom x) ((baseChangeAdjunction f).right_triangle_components X.unop)

/-- Restriction of module-valued functors from `A`-algebras to `A'`-algebras is left adjoint to
`G ↦ (B ↦ G(A' ⊗[A] B))`. -/
noncomputable def restrictFunctorAdjunction :
    restrictFunctor.{w, u, u, u} f ⊣ PresheafOfModules.pushforward.{w} (baseChangeRingHom f) :=
  presheafPushforwardAdjunction (baseChangeAdjunction f).op (restrictRingDiagram.{u} f)
    (baseChangeRingHom f) (baseChangeRingDiagram_counit f) (baseChangeRingDiagram_unit f)

end BaseChange

section Exactness

variable {C : Type u₁} [Category.{v₁} C] {D : Type u₂} [Category.{v₂} D] {F : C ⥤ D}
  {S : Cᵒᵖ ⥤ RingCat.{u}} {R : Dᵒᵖ ⥤ RingCat.{u}}

/-- The pushforward of presheaves of modules preserves finite colimits: colimits are detected
by the evaluation functors, and each evaluation of the pushforward is an evaluation followed by
restriction of scalars. -/
theorem preservesFiniteColimits_presheafPushforward (φ : S ⟶ F.op ⋙ R) :
    PreservesFiniteColimits (PresheafOfModules.pushforward.{w} φ) := by
  refine ⟨fun _ _ _ => ⟨fun {_} => ⟨fun {_} hc => ⟨?_⟩⟩⟩⟩
  refine PresheafOfModules.evaluationJointlyReflectsColimits _ _ (fun X => ?_)
  exact isColimitOfPreserves (ModuleCat.restrictScalars (φ.app X).hom)
    (isColimitOfPreserves (PresheafOfModules.evaluation R (op (F.obj X.unop))) hc)

end Exactness


section Ext

variable {A A' : Type u} [CommRing A] [CommRing A'] (f : A →+* A')

/-- Restriction of module-valued functors along `f` is additive. -/
instance restrictFunctor_additive : (restrictFunctor.{w, u, u, u} f).Additive :=
  Stacks.AlgebraicGeometry.RestrictionExact.additive_presheafPushforward _

/-- Restriction of module-valued functors along `f` preserves finite limits. -/
instance restrictFunctor_preservesFiniteLimits :
    PreservesFiniteLimits (restrictFunctor.{w, u, u, u} f) :=
  Stacks.AlgebraicGeometry.RestrictionExact.preservesFiniteLimits_presheafPushforward _

/-- Restriction of module-valued functors along `f` preserves finite colimits. -/
instance restrictFunctor_preservesFiniteColimits :
    PreservesFiniteColimits (restrictFunctor.{w, u, u, u} f) :=
  preservesFiniteColimits_presheafPushforward _

/-- The functor `G ↦ (B ↦ G(A' ⊗[A] B))` is additive. -/
instance baseChangePushforward_additive :
    (PresheafOfModules.pushforward.{w} (baseChangeRingHom f)).Additive :=
  Stacks.AlgebraicGeometry.RestrictionExact.additive_presheafPushforward _

/-- The functor `G ↦ (B ↦ G(A' ⊗[A] B))` preserves finite limits. -/
instance baseChangePushforward_preservesFiniteLimits :
    PreservesFiniteLimits (PresheafOfModules.pushforward.{w} (baseChangeRingHom f)) :=
  Stacks.AlgebraicGeometry.RestrictionExact.preservesFiniteLimits_presheafPushforward _

/-- The functor `G ↦ (B ↦ G(A' ⊗[A] B))` preserves finite colimits. -/
instance baseChangePushforward_preservesFiniteColimits :
    PreservesFiniteColimits (PresheafOfModules.pushforward.{w} (baseChangeRingHom f)) :=
  preservesFiniteColimits_presheafPushforward _

attribute [local instance] moduleValuedFunctor_enoughInjectives in
/-- **Extension groups along a change of base ring.** For `f : A → A'`, a module-valued functor
`F` on `A`-algebras and a module-valued functor `G` on `A'`-algebras, applying restriction and
then the counit gives a bijection
`Ext^n(F, B ↦ G(A' ⊗[A] B)) ≃ Ext^n(F|_{A'}, G)`. -/
theorem extMap_restrictFunctorAdjunction_bijective
    [HasExt.{t} (ModuleValuedFunctor.{max (u + 1) w, u} A)]
    [HasExt.{t'} (ModuleValuedFunctor.{max (u + 1) w, u} A')]
    (F : ModuleValuedFunctor.{max (u + 1) w, u} A)
    (G : ModuleValuedFunctor.{max (u + 1) w, u} A') (n : ℕ) :
    Function.Bijective
      (Stacks.ExtAdjunction.extMap (restrictFunctorAdjunction.{max (u + 1) w} f) F G n) :=
  Stacks.ExtAdjunction.extMap_bijective _ F G n

/-- If the restriction of `F` to `A'`-algebras is projective, then the positive-degree extension
groups from `F` to every functor of the form `B ↦ G(A' ⊗[A] B)` vanish. -/
theorem subsingleton_ext_pushforward_of_projective_restrictFunctor
    [HasExt.{t} (ModuleValuedFunctor.{max (u + 1) w, u} A)]
    [HasExt.{t'} (ModuleValuedFunctor.{max (u + 1) w, u} A')]
    (F : ModuleValuedFunctor.{max (u + 1) w, u} A)
    (hF : Projective ((restrictFunctor.{max (u + 1) w, u, u, u} f).obj F))
    (G : ModuleValuedFunctor.{max (u + 1) w, u} A') (n : ℕ) :
    Subsingleton (Abelian.Ext.{t} F
      ((PresheafOfModules.pushforward.{max (u + 1) w} (baseChangeRingHom f)).obj G) (n + 1)) := by
  have : Subsingleton (Abelian.Ext.{t'} ((restrictFunctor.{max (u + 1) w, u, u, u} f).obj F) G
      (n + 1)) :=
    Abelian.Ext.subsingleton_of_projective _ _ n
  exact (extMap_restrictFunctorAdjunction_bijective f F G (n + 1)).1.subsingleton

end Ext

end AdequateFunctor
