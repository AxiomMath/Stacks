module

public import Mathlib.Algebra.Category.ModuleCat.Sheaf.PushforwardContinuous
public import StacksFrontier.CategoryTheory.Sites.Cohomology.Cech.ComplexOfAFamily

/-!
# The Čech complex of a family, with sheaves of modules as coefficients

Let `C` be a site with binary products, let `R` be a sheaf of rings on `C` and let `F` be a
sheaf of `R`-modules.  For an object `V` of `C` write `j_V : C/V ⟶ C` for the localization
morphism, so that `j_{V,*} j_V^{-1} F` is the sheaf of `R`-modules whose sections over `W` are
`F(V × W)`.  This file assembles those sheaves, as `V` varies, into a presheaf on `C` with
values in `SheafOfModules R`, and feeds that presheaf to `Stacks.CechSite.cechComplexFunctor`.

The result is a cochain complex **of sheaves of modules** whose degree-`p` term is

`∏_{(i_0, …, i_p)} j_{U_{i_0} ×_X ⋯ ×_X U_{i_p}, *} j^{-1} F`,

the product over the `(p+1)`-tuples of members of a family `{U_i → X}`, with the alternating
Čech differential.  This is the sheaf-level Čech complex, as opposed to the complexes of
*sections* built everywhere else under `StacksFrontier/CategoryTheory/Sites/Cohomology/Cech/`,
which land in the coefficient category.

## Main definitions

* `Stacks.CechSite.SheafLevel.directImage`: the functor `j_{V,*} j_V^{-1}` on sheaves of
  `R`-modules, for a fixed object `V`.
* `Stacks.CechSite.SheafLevel.restriction`: the transition map
  `j_{V,*} j_V^{-1} F ⟶ j_{W,*} j_W^{-1} F` attached to a morphism `W ⟶ V`, which is what makes
  the assignment `V ↦ j_{V,*} j_V^{-1} F` a presheaf.
* `Stacks.CechSite.SheafLevel.diagram`: that presheaf, functorially in `F`.
* `Stacks.CechSite.SheafLevel.complexFunctor`: the Čech complex of a family of morphisms with
  fixed target, with sheaves of modules as coefficients, as a functor of `F`.

## Implementation notes

The right adjoint `j_{V,*}` is not built here.  It is Mathlib's
`SheafOfModules.pushforward (SheafOfModules.pushforwardOver V)`, the right adjoint supplied by
`SheafOfModules.overPushforwardOverAdj`, and `j_V^{-1}` is `SheafOfModules.overFunctor`; the
local wrapper `Stacks.restrictionPushforwardAdjunction` of
`StacksFrontier/CategoryTheory/Sites/Modules/ExtensionByZeroUnitIso.lean` names the adjunction
between them.  That spelling is chosen over the ringed-topos
`AlgebraicGeometry.RingedSite.overFunctorAdjPushforwardModules` because the latter couples the
three universes of the site, whereas the small étale site has its objects one universe above
its modules.

What makes the transition maps cheap is that the sections are *literally* the sections of `F`
over a product: `(j_{V,*} j_V^{-1} F)(W)` and `F(V × W)` have the same underlying abelian
group on the nose, because `SheafOfModules.pushforwardOver` is pushforward along
`CategoryTheory.Over.star`, which sends `W` to `V × W`.  So `restriction` is `F` applied to
`Limits.prod.map f (𝟙 W)`, assembled by `PresheafOfModules.homMk` out of the whiskering of
`Limits.prod.functor.map f`; the `R`-linearity reduces to
`Limits.prod.map f (𝟙 W) ≫ Limits.prod.snd = Limits.prod.snd`, which is `starMap_comp_snd`.

That identity is proved by an explicit term rather than by `simp`, even though `prod.map_snd`
is a simp lemma of exactly its shape.  The reason is that `Limits.prod.functor` and the
infix `⨯` reach the binary product through different instance paths — the goal is reported as
not type-correct at `implicit` transparency, with `getLimitCone` left unfolded — so the simp
lemma does not match syntactically while the term does, its implicit arguments being fixed by
unification against the goal.

**What is not here: the quasi-isomorphism.**  The augmentation `F[0] ⟶ complexFunctor` is built
in `StacksFrontier.CategoryTheory.Sites.Cohomology.Cech.SheafLevelComplexAugmentation`, but no
exactness statement is proved anywhere, so neither file supplies a resolution.  The obligation
that remains is recorded in the module documentation of
`StacksFrontier.AlgebraicGeometry.Descent.AssociatedModule.SmallEtaleAcyclicResolutionPushforward`,
whose Leray acyclicity lemma consumes such a resolution as a hypothesis.

## References

* [Stacks Project, Tag 03AM](https://stacks.math.columbia.edu/tag/03AM)
* [Stacks Project, Tag 01XL](https://stacks.math.columbia.edu/tag/01XL)
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits Opposite

universe w v' u' v u

namespace Stacks.CechSite.SheafLevel

variable {C : Type u'} [Category.{v'} C] [HasBinaryProducts C]
  {J : GrothendieckTopology C} (R : Sheaf J RingCat.{u})
  [∀ V : C, HasWeakSheafify (J.over V) AddCommGrpCat.{u}]
  [∀ V : C, (J.over V).WEqualsLocallyBijective AddCommGrpCat.{u}]

/-- **The functor `j_{V,*} j_V^{-1}` on sheaves of modules.**  Restriction to the site
localized at `V` followed by the direct image back along the localization morphism; its
sections over `W` are the sections of the argument over `V × W`. -/
noncomputable abbrev directImage (V : C) :
    SheafOfModules.{u} R ⥤ SheafOfModules.{u} R :=
  SheafOfModules.overFunctor.{u} R V ⋙
    SheafOfModules.pushforward.{u} (SheafOfModules.pushforwardOver (R := R) V)

/-- Multiplying a morphism `f : W ⟶ V` by an object `X` is compatible with the second
projection: `prod.map f (𝟙 X) ≫ prod.snd = prod.snd`.  This is the identity that makes
`Stacks.CechSite.SheafLevel.restriction` `R`-linear, the two `R`-module structures being
restriction of scalars along the second projections. -/
theorem starMap_comp_snd {V W : C} (f : W ⟶ V) (X : C) :
    ((prod.functor (C := C)).map f).app X ≫ prod.snd = (prod.snd : W ⨯ X ⟶ X) :=
  (prod.map_snd f (𝟙 X)).trans (Category.comp_id _)

/-- **The transition map `j_{V,*} j_V^{-1} F ⟶ j_{W,*} j_W^{-1} F` of a morphism
`f : W ⟶ V`.**  On sections over `X` it is `F` applied to `prod.map f (𝟙 X)`, the map
`W × X ⟶ V × X`. -/
noncomputable def restriction (F : SheafOfModules.{u} R) {V W : C} (f : W ⟶ V) :
    (directImage R V).obj F ⟶ (directImage R W).obj F :=
  ⟨PresheafOfModules.homMk
    (Functor.whiskerRight (NatTrans.op ((prod.functor (C := C)).map f)) F.val.presheaf)
    (fun X r m => by
      refine (F.val.map_smul
        ((NatTrans.op ((prod.functor (C := C)).map f)).app X) _ m).trans ?_
      refine congrArg (fun ρ => ρ • _) ?_
      exact ConcreteCategory.congr_hom
        ((R.obj.map_comp _ _).symm.trans
          (congrArg R.obj.map
            (op_comp.symm.trans
              (congrArg Quiver.Hom.op (starMap_comp_snd f X.unop))))) r)⟩

omit [∀ V : C, HasWeakSheafify (J.over V) AddCommGrpCat.{u}]
  [∀ V : C, (J.over V).WEqualsLocallyBijective AddCommGrpCat.{u}] in
/-- The sections of `Stacks.CechSite.SheafLevel.restriction` are the restriction maps of `F`
along `prod.map f (𝟙 X)`, on the nose. -/
theorem restriction_apply (F : SheafOfModules.{u} R) {V W : C} (f : W ⟶ V) (X : Cᵒᵖ)
    (x : (directImage R V).obj F |>.val.obj X) :
    (ConcreteCategory.hom ((restriction R F f).val.app X)) x =
      (ConcreteCategory.hom
        (F.val.presheaf.map (((prod.functor (C := C)).map f).app X.unop).op)) x :=
  rfl

omit [∀ V : C, HasWeakSheafify (J.over V) AddCommGrpCat.{u}]
  [∀ V : C, (J.over V).WEqualsLocallyBijective AddCommGrpCat.{u}] in
/-- The transition map of an identity is the identity. -/
theorem restriction_id (F : SheafOfModules.{u} R) (V : C) : restriction R F (𝟙 V) = 𝟙 _ := by
  ext X x
  rw [restriction_apply]
  simp
  rfl

omit [∀ V : C, HasWeakSheafify (J.over V) AddCommGrpCat.{u}]
  [∀ V : C, (J.over V).WEqualsLocallyBijective AddCommGrpCat.{u}] in
/-- The transition maps compose contravariantly. -/
theorem restriction_comp (F : SheafOfModules.{u} R) {V W Z : C} (f : W ⟶ V) (g : Z ⟶ W) :
    restriction R F (g ≫ f) = restriction R F f ≫ restriction R F g := by
  ext X x
  simp only [restriction_apply, Functor.map_comp, op_comp, NatTrans.comp_app]
  rfl

omit [∀ V : C, HasWeakSheafify (J.over V) AddCommGrpCat.{u}]
  [∀ V : C, (J.over V).WEqualsLocallyBijective AddCommGrpCat.{u}] in
/-- The transition maps are natural in the sheaf of modules. -/
theorem restriction_naturality {F G : SheafOfModules.{u} R} (φ : F ⟶ G) {V W : C} (f : W ⟶ V) :
    restriction R F f ≫ (directImage R W).map φ =
      (directImage R V).map φ ≫ restriction R G f := by
  ext X x
  exact PresheafOfModules.naturality_apply φ.val
    ((NatTrans.op ((prod.functor (C := C)).map f)).app X) x

/-- **The Čech diagram of a sheaf of modules**: the presheaf on `C` sending `V` to
`j_{V,*} j_V^{-1} F`, with the transition maps of
`Stacks.CechSite.SheafLevel.restriction`. -/
noncomputable def diagramObj (F : SheafOfModules.{u} R) : Cᵒᵖ ⥤ SheafOfModules.{u} R where
  obj V := (directImage R V.unop).obj F
  map g := restriction R F g.unop
  map_id V := restriction_id R F V.unop
  map_comp g g' := restriction_comp R F g.unop g'.unop

/-- **The Čech diagram, functorially in the sheaf of modules.** -/
noncomputable def diagram :
    SheafOfModules.{u} R ⥤ (Cᵒᵖ ⥤ SheafOfModules.{u} R) where
  obj F := diagramObj R F
  map φ := { app V := (directImage R V.unop).map φ
             naturality := fun _ _ g => restriction_naturality R φ g.unop }
  map_id F := NatTrans.ext (funext fun V => (directImage R V.unop).map_id F)
  map_comp φ ψ := NatTrans.ext (funext fun V => (directImage R V.unop).map_comp φ ψ)

/-- **The Čech complex of a family of morphisms with fixed target, with sheaves of modules as
coefficients.**  Its degree-`p` term is the product, over the `(p+1)`-tuples `(i_0, …, i_p)` of
members of the family, of `j_{U_{i_0} ×_X ⋯ ×_X U_{i_p}, *} j^{-1} F`, and its differential is
the alternating Čech differential of `Stacks.CechSite.cechComplexFunctor`. -/
noncomputable def complexFunctor {X : C} (E : PreZeroHypercover.{w} X)
    [HasProducts.{w} (SheafOfModules.{u} R)]
    [∀ (n : ℕ) (i : Fin (n + 1) → E.I₀), HasProduct (fun a ↦ Over.mk (E.f (i a)))] :
    SheafOfModules.{u} R ⥤ CochainComplex (SheafOfModules.{u} R) ℕ :=
  diagram R ⋙ Stacks.CechSite.cechComplexFunctor E

end Stacks.CechSite.SheafLevel

end
