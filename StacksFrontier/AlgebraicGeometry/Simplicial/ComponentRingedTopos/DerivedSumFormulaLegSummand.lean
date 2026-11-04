module

public import StacksFrontier.AlgebraicGeometry.Simplicial.ComponentRingedTopos.DerivedModuleSumFormula
public import StacksFrontier.AlgebraicGeometry.Simplicial.ComponentRingedTopos.ModuleSumFormulaLegSituation
public import StacksFrontier.CategoryTheory.Sites.Simplicial.DerivedLiftedTransitionLeg

/-!
# The summand inclusions of a derived direct-sum formula built from canonical legs

Let `Fl : A ⥤ T` be exact with exact right adjoint `Rn : T ⥤ A`, let `Rm : T ⥤ B` be exact, let
`P : ι → A ⥤ B` be a finite family of exact functors, and let `e : Fl ⋙ Rm ≅ ⨁ P` present the
composite as their direct sum. Suppose each summand inclusion of `e` is the *canonical leg*
attached to a transition `τ i : Rn ⋙ P i ⟶ Rm`, namely the unit of `Fl ⊣ Rn` carried along `P i`
followed by `τ i` — this is what the componentwise direct-sum formula of Stacks 0D72 (6) asserts
about its own decomposition.

`CategoryTheory.derivedCompBiproductIso` carries `e` to the unbounded derived categories, and it
carries no description of its summand inclusions, being assembled from
`CategoryTheory.derivedCompIso` and `CategoryTheory.derivedBiproductIso`. This file supplies that
description: the `i`-th summand inclusion of the derived formula, followed by its inverse, is the
unit of the derived adjunction carried along the derived `P i`, followed by the derived transition.
It is the derived summand-inclusion statement in the generality in which it holds, and it is the
module-coefficient counterpart of
`CategoryTheory.SimplicialSiteSituation.derived_component_summand'`, which proves the same thing
for abelian coefficients one spelling at a time.

The last statement is in the shape the derived transitions of Stacks 0D9P actually have: they are
`CategoryTheory.liftedTransition`s, lifts along the localization of the homotopy category rather
than of the category of complexes, and the crossing is
`CategoryTheory.liftedTransition_eq_derivedNatTrans`.

The file closes with the one step of the module-coefficient instance that is not generic: the leg
equation of Stacks 0D72 (6) for sheaves of modules, read against the *biproduct* form
`CategoryTheory.SimplicialSiteSituation.moduleSumFormulaBiproduct` of the formula rather than its
coproduct form, which is the form the derived-category comparison consumes.

## Main results

* `CategoryTheory.biproduct_ι_derivedCompBiproductIso_inv`: the `i`-th summand inclusion of
  `CategoryTheory.derivedCompBiproductIso`, followed by its inverse, is the derived functor of the
  `i`-th summand inclusion of the sheaf-level presentation, read through the compositor.
* `CategoryTheory.biproduct_ι_derivedCompBiproductIso_inv_leg`: **the same with the summand
  inclusions of the sheaf-level presentation given as canonical legs** — then the summand inclusion
  of the derived formula is the unit of the derived adjunction carried along `P i`, followed by the
  compositor and the derived functor of `τ i`.
* `CategoryTheory.biproduct_ι_derivedCompBiproductIso_inv_liftedTransition`: **the same with the
  derived transition in its lifted form** and with the summands of the derived formula rewritten
  along identifications `LP i ≅ (P i).mapDerivedCategory` of the lifted derived functors with the
  degreewise ones. This is the shape that the derived summand inclusions of Stacks 0D72 (6) for
  sheaves of modules have.
* `CategoryTheory.SimplicialSiteSituation.biproduct_ι_moduleSumFormulaBiproduct_inv`: the leg
  equation of Stacks 0D72 (6) for sheaves of modules, read against the biproduct form of the
  formula. It is `CategoryTheory.SimplicialSiteSituation.ModuleSumFormulaLegEq` with the coproduct
  summand inclusion replaced by the biproduct one, which is the hypothesis the generic statement
  above asks for.

## Implementation notes

*Why the generic statements are stated for `CategoryTheory.derivedCompBiproductIso` and not for the
module formula.* `CategoryTheory.SimplicialSiteSituation.derivedModuleSumFormula` is
`CategoryTheory.SimplicialSiteSituation.derivedModuleSumFormulaMapDerivedCategory` — itself a
`CategoryTheory.derivedCompBiproductIso` — composed summandwise with
`CategoryTheory.SimplicialSiteSituation.derivedTransitionPullbackIsoMapDerivedCategory`, and those
two mention the exactness of the transition pullbacks through *different* witnesses: the formula
takes `PreservesFiniteColimits` from the right half of
`CategoryTheory.SimplicialSiteSituation.exactFunctor_transitionPullbackModules` and the
identification takes it from
`AlgebraicGeometry.RingedToposHom.pullbackModules_preservesFiniteColimits`. Those witnesses are
definitionally equal and not syntactically equal, and `CategoryTheory.Functor.mapDerivedCategory`
takes them as arguments, so a term written at one of them is accepted against the other only after
the kernel unfolds a localization. Each such crossing is affordable once in a declaration; the
instantiation of the statement below at the module formula needs more than one of them and does not
fit in a declaration's heartbeat budget. That is why the generic statements are kept separate from
the instantiation rather than being stated at the module formula directly.

*The universe of the derived categories is shared.*
`CategoryTheory.derivedNatTrans_leg_comp_derivedCompIso` is stated with one
`HasDerivedCategory.{w}` universe for all three categories, so the statements here are too.
Instantiating them needs the three categories supplied explicitly: with them left to unification
instance search for the first `HasDerivedCategory.{?w} ?A` runs while `?A` is still a metavariable
and fails.

*What the instantiation at the module formula is blocked on.* It is not the exactness witnesses but
the two spellings of a component's module category, together with
`CategoryTheory.HasDerivedCategory` being data rather than a proposition. The sheaf-level data this
statement consumes — `CategoryTheory.SimplicialSiteSituation.componentModuleLowerShriek`,
`…moduleSumFormulaBiproduct`, `…componentModuleTransition` — are stated at
`SheafOfModules (…componentRingSheaf …)`, while the derived-level data it consumes —
`…derivedTransitionPullback`, `…derivedTransitionComparison`,
`…derivedTransitionPullbackIsoMapDerivedCategory` — are stated at
`(…componentRingedTopos O ·).Modules`. The two categories are equal by `rfl`, and cheaply so, and
`CategoryTheory.Abelian` is available at either spelling; but the statement above ties all three
categories to one `HasDerivedCategory.{w}`, and that witness is a localization.

Instantiated with the three categories spelled as `SheafOfModules …`, every argument up to and
including `hleg` elaborates, and the `LP` and `cmp` arguments then ask the unifier to identify two
`HasDerivedCategory` witnesses, which exhausts a declaration's heartbeat budget at `whnf`.
Instantiated with them spelled as `… .Modules` there is no heartbeat cost at all, and instance
search fails outright instead, on `CategoryTheory.Abelian (…totalRingedTopos O).Modules`: search
unfolds only reducibly, so it cannot cross the projections of `…totalRingedTopos` to reach
`…hasSheafifyTotal`. Supplying that one instance by `inferInstanceAs` at the `SheafOfModules`
spelling makes every instance resolve and brings the heartbeat failure back, now between the
`HasDerivedCategory` built over the supplied `Abelian` and the one inside
`…derivedTransitionPullback`.

So the instantiation needs the derived-level data restated at the sheaf-level spelling, one
crossing to a declaration, so that a single `HasDerivedCategory` term serves all three categories.
No choice of exactness witnesses, and no type ascription on the conclusion, avoids it.

## References

* [Stacks Project, Tag 09WE](https://stacks.math.columbia.edu/tag/09WE)
* [Stacks Project, Tag 0D72](https://stacks.math.columbia.edu/tag/0D72)
* [Stacks Project, Tag 0D9P](https://stacks.math.columbia.edu/tag/0D9P)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits CategoryTheory.Functor AlgebraicGeometry
open Stacks.Cohomology.DerivedPushforward

universe u w

namespace CategoryTheory

attribute [local instance] CategoryTheory.Limits.comp_preservesFiniteLimits
  CategoryTheory.Limits.comp_preservesFiniteColimits

/-- **The summand inclusions of `CategoryTheory.derivedCompBiproductIso`.** The `i`-th summand
inclusion of the derived direct-sum formula, followed by the inverse of that formula, is the
derived functor of the `i`-th summand inclusion of the sheaf-level presentation `e`, followed by
the compositor of the derived functors of `F` and `G`.

This is formal: `CategoryTheory.derivedBiproductIso` has `CategoryTheory.Limits.biproduct.desc` of
the derived summand inclusions as its inverse. -/
theorem biproduct_ι_derivedCompBiproductIso_inv
    (A : Type*) [Category A] [Abelian A] [HasDerivedCategory A]
    (B : Type*) [Category B] [Abelian B] [HasDerivedCategory B]
    (C : Type*) [Category C] [Abelian C] [HasDerivedCategory C]
    (F : A ⥤ B) [F.Additive] [PreservesFiniteLimits F] [PreservesFiniteColimits F]
    (G : B ⥤ C) [G.Additive] [PreservesFiniteLimits G] [PreservesFiniteColimits G]
    {ι : Type*} [Fintype ι] (L : ι → A ⥤ C) [Limits.HasBiproduct L]
    [∀ i, (L i).Additive] [∀ i, PreservesFiniteLimits (L i)]
    [∀ i, PreservesFiniteColimits (L i)] (e : F ⋙ G ≅ ⨁ L) (X : DerivedCategory A) (i : ι) :
    Limits.biproduct.ι (fun j => (L j).mapDerivedCategory.obj X) i ≫
        (derivedCompBiproductIso A B C F G L e X).inv =
      (derivedNatTrans (L i) (F ⋙ G) (Limits.biproduct.ι L i ≫ e.inv)).app X ≫
        (derivedCompIso F G (F ⋙ G) (Iso.refl _)).hom.app X := by
  simp only [derivedCompBiproductIso, derivedBiproductIso, Iso.trans_inv, Iso.symm_inv,
    Iso.app_hom, Limits.biproduct.ι_desc_assoc]

/-- **The summand inclusions of `CategoryTheory.derivedCompBiproductIso`, when the sheaf-level
summand inclusions are the canonical legs.** Let `Fl ⊣ Rn` be an adjunction of exact functors, let
`Rm` and the `P i` be exact, let `τ i : Rn ⋙ P i ⟶ Rm` be transitions, and suppose the `i`-th
summand inclusion of `e : Fl ⋙ Rm ≅ ⨁ P` is the canonical leg attached to `τ i`. Then the `i`-th
summand inclusion of the derived formula is the unit of the derived adjunction
`CategoryTheory.Adjunction.mapDerivedCategory` carried along the derived `P i`, followed by the
compositor of `Rn` and `P i` and the derived functor of `τ i`.

This is `CategoryTheory.derivedNatTrans_leg_comp_derivedCompIso` fed into
`CategoryTheory.biproduct_ι_derivedCompBiproductIso_inv`. It is the content that Stacks 0D72 (6)
adds to the existence of the direct-sum formula. -/
theorem biproduct_ι_derivedCompBiproductIso_inv_leg
    (T : Type*) [Category T] [Abelian T] [HasDerivedCategory.{w} T]
    (A : Type*) [Category A] [Abelian A] [HasDerivedCategory.{w} A]
    (B : Type*) [Category B] [Abelian B] [HasDerivedCategory.{w} B]
    (Fl : A ⥤ T) [Fl.Additive] [PreservesFiniteLimits Fl] [PreservesFiniteColimits Fl]
    (Rn : T ⥤ A) [Rn.Additive] [PreservesFiniteLimits Rn] [PreservesFiniteColimits Rn]
    (Rm : T ⥤ B) [Rm.Additive] [PreservesFiniteLimits Rm] [PreservesFiniteColimits Rm]
    {ι : Type*} [Fintype ι] (P : ι → A ⥤ B) [Limits.HasBiproduct P]
    [∀ i, (P i).Additive] [∀ i, PreservesFiniteLimits (P i)]
    [∀ i, PreservesFiniteColimits (P i)]
    (e : Fl ⋙ Rm ≅ ⨁ P) (adj : Fl ⊣ Rn) (τ : ∀ i, Rn ⋙ P i ⟶ Rm)
    (hleg : ∀ i, Limits.biproduct.ι P i ≫ e.inv =
      Functor.whiskerRight adj.unit (P i) ≫ Functor.whiskerLeft Fl (τ i))
    (X : DerivedCategory A) (i : ι) :
    Limits.biproduct.ι (fun j => (P j).mapDerivedCategory.obj X) i ≫
        (derivedCompBiproductIso A T B Fl Rm P e X).inv =
      (P i).mapDerivedCategory.map ((Adjunction.mapDerivedCategory adj).unit.app X) ≫
        ((derivedCompIso Rn (P i) (Rn ⋙ P i) (Iso.refl _)).inv ≫
            derivedNatTrans (Rn ⋙ P i) Rm (τ i)).app (Fl.mapDerivedCategory.obj X) := by
  rw [biproduct_ι_derivedCompBiproductIso_inv, hleg i]
  exact derivedNatTrans_leg_comp_derivedCompIso T A B Fl Rn Rm (P i) adj (τ i) X

/-- **The summand inclusions of a derived direct-sum formula whose summands are lifted derived
functors and whose transitions are lifted transitions.** This is
`CategoryTheory.biproduct_ι_derivedCompBiproductIso_inv_leg` with two changes, both of which are
what the derived direct-sum formula of Stacks 0D72 (6) for sheaves of modules needs.

First, the summands of the derived formula are rewritten along identifications
`iso i : LP i ≅ (P i).mapDerivedCategory` of functors of derived categories produced as total left
derived functors with the degreewise ones; this is the summandwise composition that
`CategoryTheory.SimplicialSiteSituation.derivedModuleSumFormula` performs with
`…derivedTransitionPullbackIsoMapDerivedCategory`.

Second, the transition on the right-hand side is a `CategoryTheory.liftedTransition`, a lift along
the localization of the *homotopy* category, which is how the derived transitions of Stacks 0D9P
are built; the crossing to the `Q`-level machinery is
`CategoryTheory.liftedTransition_eq_derivedNatTrans`, and `hiso` is its hypothesis. The remaining
content is one naturality square of `iso i`. -/
theorem biproduct_ι_derivedCompBiproductIso_inv_liftedTransition
    (T : Type*) [Category T] [Abelian T] [HasDerivedCategory.{w} T]
    (A : Type*) [Category A] [Abelian A] [HasDerivedCategory.{w} A]
    (B : Type*) [Category B] [Abelian B] [HasDerivedCategory.{w} B]
    (Fl : A ⥤ T) [Fl.Additive] [PreservesFiniteLimits Fl] [PreservesFiniteColimits Fl]
    (Rn : T ⥤ A) [Rn.Additive] [PreservesFiniteLimits Rn] [PreservesFiniteColimits Rn]
    (Rm : T ⥤ B) [Rm.Additive] [PreservesFiniteLimits Rm] [PreservesFiniteColimits Rm]
    {ι : Type*} [Fintype ι] (P : ι → A ⥤ B) [Limits.HasBiproduct P]
    [∀ i, (P i).Additive] [∀ i, PreservesFiniteLimits (P i)]
    [∀ i, PreservesFiniteColimits (P i)]
    (e : Fl ⋙ Rm ≅ ⨁ P) (adj : Fl ⊣ Rn) (τ : ∀ i, Rn ⋙ P i ⟶ Rm)
    (hleg : ∀ i, Limits.biproduct.ι P i ≫ e.inv =
      Functor.whiskerRight adj.unit (P i) ≫ Functor.whiskerLeft Fl (τ i))
    (LP : ι → DerivedCategory A ⥤ DerivedCategory B)
    (cmp : ∀ i, DerivedCategory.Qh ⋙ LP i ⟶
      (P i).mapHomotopyCategory (ComplexShape.up ℤ) ⋙ DerivedCategory.Qh)
    (iso : ∀ i, LP i ≅ (P i).mapDerivedCategory)
    (hiso : ∀ i, Functor.whiskerLeft DerivedCategory.Qh (iso i).hom ≫
      (P i).mapDerivedCategoryFactorsh.hom = cmp i)
    (X : DerivedCategory A) (i : ι) :
    Limits.biproduct.ι (fun j => (LP j).obj X) i ≫
        (derivedCompBiproductIso A T B Fl Rm P e X ≪≫
          Limits.biproduct.mapIso fun j => ((iso j).app X).symm).inv =
      (LP i).map ((Adjunction.mapDerivedCategory adj).unit.app X) ≫
        (liftedTransition Rn.mapDerivedCategoryFactorsh (cmp i)
            Rm.mapDerivedCategoryFactorsh
            (mapHomotopyCategoryTransition (ComplexShape.up ℤ) Rn (P i) Rm (τ i))
            (HomotopyCategory.quasiIso T (ComplexShape.up ℤ))).app
          (Fl.mapDerivedCategory.obj X) := by
  have hbi : Limits.biproduct.ι (fun j => (LP j).obj X) i ≫
      (Limits.biproduct.mapIso fun j => ((iso j).app X).symm).inv =
      (iso i).hom.app X ≫
        Limits.biproduct.ι (fun j => (P j).mapDerivedCategory.obj X) i := by
    simp
  rw [Iso.trans_inv, ← Category.assoc, hbi, Category.assoc,
    biproduct_ι_derivedCompBiproductIso_inv_leg T A B Fl Rn Rm P e adj τ hleg X i,
    liftedTransition_eq_derivedNatTrans Rn (P i) Rm (τ i) (cmp i) (iso i) (hiso i)]
  simp only [NatTrans.comp_app, Functor.whiskerLeft_app]
  exact ((iso i).hom.naturality_assoc _ _).symm

end CategoryTheory

namespace CategoryTheory.SimplicialSiteSituation

attribute [local instance] hasSheafifyTotal
  CategoryTheory.GrothendieckTopology.wEqualsLocallyBijective_addCommGrpCat hasWeakSheafifyComponent
  wEqualsLocallyBijectiveComponent HasDerivedCategory.standard

variable (S : SimplicialSiteSituation.{u}) (O : Sheaf S.totalTopology CommRingCat.{u})

/-- **The leg equation of Stacks 0D72 (6) against the biproduct form of the formula.** Granted
`CategoryTheory.SimplicialSiteSituation.ModuleSumFormulaLegEq` — the leg equation as stated for the
coproduct form `CategoryTheory.SimplicialSiteSituation.moduleSumFormula`, which
`CategoryTheory.SimplicialSite.moduleSumFormulaLegEq_situation` proves in case (A) of Stacks 09WE —
the `φ`th *biproduct* summand inclusion of
`CategoryTheory.SimplicialSiteSituation.moduleSumFormulaBiproduct`, followed by the inverse of that
formula, is the canonical leg `CategoryTheory.SimplicialSiteSituation.moduleSumFormulaLeg`.

The biproduct form is the formula composed with
`CategoryTheory.Limits.biproduct.isoCoproduct`, and that comparison carries the biproduct summand
inclusion to the coproduct one, so this is the coproduct statement and nothing more. It is the
biproduct form that the derived-category comparison
`CategoryTheory.derivedCompBiproductIso` consumes, hence the form in which
`CategoryTheory.biproduct_ι_derivedCompBiproductIso_inv_liftedTransition` asks for it. -/
theorem biproduct_ι_moduleSumFormulaBiproduct_inv (hleg : S.ModuleSumFormulaLegEq O)
    {n m : SimplexCategory} (ψ : n ⟶ m) :
    letI : Limits.HasFiniteBiproducts
        (SheafOfModules.{u} (S.componentRingSheaf
            ((Stacks.SheafOfModules.Tensor.ringSheaf (J := S.totalTopology) O)) n) ⥤
          SheafOfModules.{u} (S.componentRingSheaf
              ((Stacks.SheafOfModules.Tensor.ringSheaf (J := S.totalTopology) O)) m)) :=
      Limits.HasFiniteBiproducts.of_hasFiniteProducts
    Limits.biproduct.ι (fun χ : n ⟶ m => S.transitionPullbackModules' O χ) ψ ≫
        (S.moduleSumFormulaBiproduct O n m).inv =
      S.moduleSumFormulaLeg O ψ := by
  let : Limits.HasFiniteBiproducts
      (SheafOfModules.{u} (S.componentRingSheaf
          ((Stacks.SheafOfModules.Tensor.ringSheaf (J := S.totalTopology) O)) n) ⥤
        SheafOfModules.{u} (S.componentRingSheaf
            ((Stacks.SheafOfModules.Tensor.ringSheaf (J := S.totalTopology) O)) m)) :=
    Limits.HasFiniteBiproducts.of_hasFiniteProducts
  refine Eq.trans ?_ (hleg ψ)
  rw [show (S.moduleSumFormulaBiproduct O n m).inv =
      (Limits.biproduct.isoCoproduct
          (fun χ : n ⟶ m => S.transitionPullbackModules' O χ)).hom ≫
        (S.moduleSumFormula O n m).inv from rfl]
  rw [← Category.assoc, Limits.biproduct.isoCoproduct_hom, Limits.biproduct.ι_desc]

end CategoryTheory.SimplicialSiteSituation

end
