module

public import StacksFrontier.CategoryTheory.Sites.Cohomology.DerivedPullback.PullbackToposUnitComparison
public import StacksFrontier.CategoryTheory.Sites.Cohomology.DerivedPullback.PullbackToposUnitorCoherence
public import StacksFrontier.Algebra.Category.ModuleCat.Sheaf.MonoidalStrictRightUnitor
public import StacksFrontier.Algebra.Category.ModuleCat.Sheaf.RingedToposPullbackCoherence

/-!
# The right-unitor coherence of Stacks 07A4 on a ringed topos

Let `f : (Sh(C), 𝒪_C) ⟶ (Sh(D), 𝒪_D)` be a morphism of ringed topoi presented by a functor `f.u`
of the underlying sites which is a morphism of sites. This file proves
`Stacks.Sheaves.DerivedPullback.PullbackToposRightUnitorCoherence`, the module-level right-unitor
coherence for the site-presented pullback: the comparison
`f^*(A ⊗_{𝒪_D} 𝒪_D) ⟶ f^*A ⊗_{𝒪_C} f^*𝒪_D` of Stacks 03EL, followed by `𝟙 ⊗ ν` for the unit
comparison `ν : f^*𝒪_D ⟶ 𝒪_C` of Mathlib's `SheafOfModules.pullbackObjUnitToUnit` and by the
right unitor of `Stacks.SheafOfModules.sheafTensorUnitNatIso`, is the pullback of the right
unitor. That proposition is stated — and was left open — in
`StacksFrontier.CategoryTheory.Sites.Cohomology.DerivedPullback.PullbackToposUnitorCoherence`.

## Main results

* `Stacks.Sheaves.DerivedPullback.pullbackToposRightUnitorCoherence`: **the right-unitor
  coherence of Stacks 07A4 holds**, unconditionally in the morphism of sites.

## Implementation notes

**What was missing, and what closed it.** The coherence for this library's *own* comparison and
unit comparison is `Stacks.SheafOfModules.RingedToposPullback.rightUnitality`, proved
unconditionally by a computation on the chain of bijections of Stacks 03EL. What the proposition
above asks for differs from it in three spellings, and each is now a lemma:

* the unit object and the right unitor. `Stacks.SheafOfModules.sheafTensorUnitNatIso` reads the
  unit law `- ⊗_𝒪 𝒪 ≅ 𝟭` off the *re-seated* monoidal structure, while `rightUnitality` is stated
  for the strict structure of Tag 01CA; the two right unitors agree by
  `Stacks.SheafOfModules.Strict.sheafTensorUnitNatIso_hom_app_eq`;
* the unit comparison. Mathlib's `SheafOfModules.pullbackObjUnitToUnit` and this library's
  `Stacks.Sheaves.RingedToposModules.pullbackModulesObjUnitIso` agree by
  `Stacks.Sheaves.DerivedPullback.pullbackModulesSiteIso_hom_app_unit_comp_pullbackObjUnitToUnit`;
* the pullback. `pullbackToposTensorMap` is the comparison of Stacks 03EL transported along
  `Stacks.Sheaves.DerivedPullback.pullbackModulesSiteIso`, so the coherence is the transport of
  `rightUnitality` along an isomorphism of the pullback functor. That transport is
  `transport_rightUnitality` below, a statement about two monoidal categories and an isomorphism
  of functors between them and about nothing else: `whisker_exchange` moves the comparison of the
  pullbacks past the unit comparison and `MonoidalCategory.rightUnitor_naturality` past the
  unitor, after which the two halves of the isomorphism cancel.

Nothing below is left unproved, no raised limit, no search tactic, and no hypothesis beyond the
ones the statement itself carries.

**One monoidal structure per composite, and what it costs.** The sheaf of rings over which the
sheaves of `𝒪_C`-modules are taken has one spelling here,
`Stacks.SheafOfModules.Tensor.ringSheaf X.O`, but *two* monoidal structures sit on sheaves of
modules over it: `Stacks.SheafOfModules.Strict.monoidalUnderlyingRingSheaf` and
`Stacks.SheafOfModules.Strict.monoidalCategory X.O.obj
(Stacks.SheafOfModules.Strict.isSheaf_ringSheaf X.O)`. They differ only in which proof of the
sheaf condition they carry, so they are equal by proof irrelevance and not syntactically equal,
and the monoidal units, whiskerings and unitors they produce are different terms. A composite
whose factors carry both is one in which the associativity pattern cannot be found, and matching
such a composite against a generic monoidal statement exhausts the unifier.

The structure used throughout is therefore the first one, which is the one
`Stacks.SheafOfModules.Strict.whiskerLeft_eq_tensorSheafBifunctor_map` and
`whiskerRight_eq_tensorSheafBifunctor_map` are stated at, so that the whiskerings of a composite
can be rewritten into the tensor bifunctor of Tag 0GMW. The *object* arguments of `◁`, `▷` and
`ρ_` and the functor `f.pullbackTopos` itself are still ascribed — a type ascription leaves the
term alone, so the ascribed statements mention the same morphisms. `unitComparisonAscribed` does
the same for Mathlib's `ν`, whose own source is spelled
`(SheafOfModules.pullback f^♯).obj (SheafOfModules.unit 𝒪_D)`. `lhs_eq` and `rhs_eq` are then the
two sides of the coherence, each crossing to the derived development's spelling exactly once,
inside a defeq-tolerant `congrArg`.

Because `Stacks.SheafOfModules.Tensor.ringSheaf` is a plain definition rather than an
abbreviation, the five universes of `Stacks.SheafOfModules.Tensor.sheafTensor` are written out
below: left implicit, the `omit` clauses no longer match the section binders they name.

## References

* [Stacks Project, Tag 07A4](https://stacks.math.columbia.edu/tag/07A4)
* [Stacks Project, Tag 03EL](https://stacks.math.columbia.edu/tag/03EL)
* [Stacks Project, Tag 03D6](https://stacks.math.columbia.edu/tag/03D6)
* [Stacks Project, Tag 01CA](https://stacks.math.columbia.edu/tag/01CA)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry MonoidalCategory
open Stacks.Sheaves.RingedToposModules

namespace Stacks.Sheaves.DerivedPullback

/-- **The transport of a right-unitality coherence along an isomorphism of the functor.** Given
two monoidal categories, two functors `P`, `Q` between them and an isomorphism `e : P ≅ Q`, a
right-unitality coherence for `P` with unit comparison `νg` gives one for `Q` with any unit
comparison `ν` whose composite with `e` is `νg`, the comparison of tensor products for `Q` being
the one for `P` transported along `e`.

Stated generically, so that the three monoidal rewrites happen where every object is a variable:
at the sheaves of modules of the application they involve several spellings of the structure
sheaf of the source, and `rw` does not find its patterns there. -/
private lemma transport_rightUnitality {D₁ D₂ : Type*} [Category D₁] [Category D₂]
    [MonoidalCategory D₁] [MonoidalCategory D₂]
    {P Q : D₁ ⥤ D₂} (e : P ≅ Q) (A : D₁)
    (c : P.obj (A ⊗ 𝟙_ D₁) ⟶ P.obj A ⊗ P.obj (𝟙_ D₁))
    (νg : P.obj (𝟙_ D₁) ⟶ 𝟙_ D₂) (ν : Q.obj (𝟙_ D₁) ⟶ 𝟙_ D₂)
    (hν : e.hom.app (𝟙_ D₁) ≫ ν = νg)
    (hru : P.map (ρ_ A).hom = c ≫ (P.obj A ◁ νg) ≫ (ρ_ (P.obj A)).hom) :
    (e.inv.app (A ⊗ 𝟙_ D₁) ≫ c ≫ (e.hom.app A ▷ P.obj (𝟙_ D₁)) ≫
        (Q.obj A ◁ e.hom.app (𝟙_ D₁))) ≫ (Q.obj A ◁ ν) ≫ (ρ_ (Q.obj A)).hom =
      Q.map (ρ_ A).hom := by
  have hru' : P.map (ρ_ A).hom ≫ e.hom.app A =
      c ≫ (P.obj A ◁ νg) ≫ (ρ_ (P.obj A)).hom ≫ e.hom.app A := by
    rw [hru, Category.assoc, Category.assoc]
  rw [Category.assoc, Category.assoc, Category.assoc,
    ← MonoidalCategory.whiskerLeft_comp_assoc, hν, ← whisker_exchange_assoc,
    MonoidalCategory.rightUnitor_naturality, ← hru', e.hom.naturality, ← Category.assoc,
    e.inv_hom_id_app, Category.id_comp]

section SiteMorphism

universe u

variable {X Y : RingedTopos.{u, u, u}}
  [X.J.HasSheafCompose (forget₂ CommRingCat.{u} RingCat.{u})]
  [Y.J.HasSheafCompose (forget₂ CommRingCat.{u} RingCat.{u})]
  [X.J.WEqualsLocallyBijective AddCommGrpCat.{u}] [Y.J.WEqualsLocallyBijective AddCommGrpCat.{u}]

attribute [local instance] Stacks.SheafOfModules.Strict.monoidalUnderlyingRingSheaf

/-- `Stacks.SheafOfModules.RingedToposPullback.rightUnitality`, the right-unitality coherence of
Stacks 03EL for the four-field pullback of Stacks 03D6, restated verbatim: the statement is that
field, character for character, so that it can be quoted below without the elaborator having to
decide anything. -/
private lemma strictRightUnitality (g : Stacks.Sheaves.RingedToposModules.RingedToposHom X Y)
    (A : SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf Y.O)) :
    g.pullbackModules.map (ρ_ A).hom =
      Stacks.SheafOfModules.RingedToposPullback.pullbackTensorComparison g A
          (𝟙_ (SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf Y.O))) ≫
        (g.pullbackModules.obj A ◁
            (Stacks.SheafOfModules.RingedToposPullback.pullbackUnitComparison g).hom) ≫
          (ρ_ (g.pullbackModules.obj A)).hom :=
  Stacks.SheafOfModules.RingedToposPullback.rightUnitality g A

variable [(Stacks.SheafOfModules.Tensor.sheafTensor.{u, u, u, u, u} X.O).Additive]
  [∀ M, ((Stacks.SheafOfModules.Tensor.sheafTensor.{u, u, u, u, u} X.O).obj M).Additive]
  [(Stacks.SheafOfModules.Tensor.sheafTensor.{u, u, u, u, u} Y.O).Additive]
  [∀ M, ((Stacks.SheafOfModules.Tensor.sheafTensor.{u, u, u, u, u} Y.O).obj M).Additive]
  [∀ (A B : CochainComplex (SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf X.O)) ℤ),
    HomologicalComplex.HasMapBifunctor A B
      (Stacks.SheafOfModules.Tensor.sheafTensor.{u, u, u, u, u} X.O) (ComplexShape.up ℤ)]
  [∀ (A B : CochainComplex (SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf Y.O)) ℤ),
    HomologicalComplex.HasMapBifunctor A B
      (Stacks.SheafOfModules.Tensor.sheafTensor.{u, u, u, u, u} Y.O) (ComplexShape.up ℤ)]
  (f : RingedToposSiteHom X Y)

/-- Mathlib's comparison `ν : f^*𝒪_D ⟶ 𝒪_C`, with its source and target ascribed at the monoidal
unit of Tag 01CA and at the spelling of the two structure sheaves that
`Stacks.Sheaves.DerivedPullback.pullbackModulesSiteIso` fixes. The ascription is forced: a
composite one factor of which ends at `f^*(𝟙_)` while the next begins at
`(SheafOfModules.pullback f^♯).obj (SheafOfModules.unit 𝒪_D)` is one in which `rw` cannot find
the associativity pattern, since matching it means deciding the equality of the two spellings of
the seam. -/
private def unitComparisonAscribed :
    (f.pullbackTopos : SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf Y.O) ⥤
          SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf X.O)).obj
        (𝟙_ (SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf Y.O))) ⟶
      𝟙_ (SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf X.O)) :=
  SheafOfModules.pullbackObjUnitToUnit.{u} f.fSharpRing

omit [(Stacks.SheafOfModules.Tensor.sheafTensor.{u, u, u, u, u} X.O).Additive]
  [∀ M, ((Stacks.SheafOfModules.Tensor.sheafTensor.{u, u, u, u, u} X.O).obj M).Additive]
  [(Stacks.SheafOfModules.Tensor.sheafTensor.{u, u, u, u, u} Y.O).Additive]
  [∀ M, ((Stacks.SheafOfModules.Tensor.sheafTensor.{u, u, u, u, u} Y.O).obj M).Additive]
  [∀ (A B : CochainComplex (SheafOfModules.{u}
    (Stacks.SheafOfModules.Tensor.ringSheaf X.O)) ℤ),
    HomologicalComplex.HasMapBifunctor A B
      (Stacks.SheafOfModules.Tensor.sheafTensor.{u, u, u, u, u} X.O) (ComplexShape.up ℤ)]
  [∀ (A B : CochainComplex (SheafOfModules.{u}
    (Stacks.SheafOfModules.Tensor.ringSheaf Y.O)) ℤ),
    HomologicalComplex.HasMapBifunctor A B
      (Stacks.SheafOfModules.Tensor.sheafTensor.{u, u, u, u, u} Y.O) (ComplexShape.up ℤ)] in
/-- `Stacks.Sheaves.DerivedPullback.pullbackModulesSiteIso_hom_app_unit_comp_pullbackObjUnitToUnit`
at the ascribed spellings. -/
private lemma unitComparison (hmos : f.u.IsMorphismOfSites Y.J X.J) :
    (pullbackModulesSiteIso f hmos).hom.app
        (𝟙_ (SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf Y.O))) ≫
        unitComparisonAscribed f =
      (Stacks.SheafOfModules.RingedToposPullback.pullbackUnitComparison
        (modulesHomOfSiteHom f hmos)).hom :=
  pullbackModulesSiteIso_hom_app_unit_comp_pullbackObjUnitToUnit f hmos

omit [(Stacks.SheafOfModules.Tensor.sheafTensor.{u, u, u, u, u} X.O).Additive]
  [∀ M, ((Stacks.SheafOfModules.Tensor.sheafTensor.{u, u, u, u, u} X.O).obj M).Additive]
  [(Stacks.SheafOfModules.Tensor.sheafTensor.{u, u, u, u, u} Y.O).Additive]
  [∀ M, ((Stacks.SheafOfModules.Tensor.sheafTensor.{u, u, u, u, u} Y.O).obj M).Additive]
  [∀ (A B : CochainComplex (SheafOfModules.{u}
    (Stacks.SheafOfModules.Tensor.ringSheaf X.O)) ℤ),
    HomologicalComplex.HasMapBifunctor A B
      (Stacks.SheafOfModules.Tensor.sheafTensor.{u, u, u, u, u} X.O) (ComplexShape.up ℤ)]
  [∀ (A B : CochainComplex (SheafOfModules.{u}
    (Stacks.SheafOfModules.Tensor.ringSheaf Y.O)) ℤ),
    HomologicalComplex.HasMapBifunctor A B
      (Stacks.SheafOfModules.Tensor.sheafTensor.{u, u, u, u, u} Y.O) (ComplexShape.up ℤ)] in
/-- **The left-hand side of the coherence, rewritten in the monoidal language of Tag 01CA.** The
comparison of Stacks 03EL for the site-presented pullback is the one for the four-field pullback
conjugated by the identification of the two, the action of the tensor bifunctor on the unit
comparison is a left whiskering, and the unit law of
`Stacks.SheafOfModules.sheafTensorUnitNatIso` is the right unitor. -/
private lemma lhs_eq (hmos : f.u.IsMorphismOfSites Y.J X.J)
    (A : SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf Y.O)) :
    pullbackToposTensorMap f hmos A
            (SheafOfModules.unit (Stacks.SheafOfModules.Tensor.ringSheaf Y.O)) ≫
          ((Stacks.SheafOfModules.Tensor.sheafTensor.{u, u, u, u, u} X.O).obj
              (f.pullbackTopos.obj A)).map
              (SheafOfModules.pullbackObjUnitToUnit.{u} f.fSharpRing) ≫
            (Stacks.SheafOfModules.sheafTensorUnitNatIso X.O).hom.app (f.pullbackTopos.obj A) =
      ((pullbackModulesSiteIso f hmos).inv.app
              ((A : SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf Y.O)) ⊗
                𝟙_ (SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf Y.O))) ≫
            Stacks.SheafOfModules.RingedToposPullback.pullbackTensorComparison
                (modulesHomOfSiteHom f hmos) A
                (𝟙_ (SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf Y.O))) ≫
              ((pullbackModulesSiteIso f hmos).hom.app A ▷
                  (modulesHomOfSiteHom f hmos).pullbackModules.obj
                    (𝟙_ (SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf Y.O)))) ≫
                ((f.pullbackTopos :
                    SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf Y.O) ⥤
                        SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf X.O)).obj A ◁
                  (pullbackModulesSiteIso f hmos).hom.app
                    (𝟙_ (SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf Y.O))))) ≫
        ((f.pullbackTopos : SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf Y.O) ⥤
                SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf X.O)).obj A ◁
            unitComparisonAscribed f) ≫
          (ρ_ ((f.pullbackTopos : SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf Y.O) ⥤
            SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf X.O)).obj A)).hom := by
  have hX : (Stacks.SheafOfModules.sheafTensorUnitNatIso X.O).hom.app (f.pullbackTopos.obj A) =
      (ρ_ ((f.pullbackTopos : SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf Y.O) ⥤
        SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf X.O)).obj A)).hom :=
    Stacks.SheafOfModules.Strict.sheafTensorUnitNatIso_hom_app_eq X.O (f.pullbackTopos.obj A)
  have hw : ((Stacks.SheafOfModules.Tensor.sheafTensor.{u, u, u, u, u} X.O).obj
          (f.pullbackTopos.obj A)).map
        (SheafOfModules.pullbackObjUnitToUnit.{u} f.fSharpRing) =
      ((f.pullbackTopos : SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf Y.O) ⥤
              SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf X.O)).obj A ◁
        unitComparisonAscribed f) :=
    ((Stacks.SheafOfModules.Strict.whiskerLeft_eq_tensorSheafBifunctor_map X.O
      (f.pullbackTopos.obj A)
      (SheafOfModules.pullbackObjUnitToUnit.{u} f.fSharpRing)).trans (by
        rw [CategoryTheory.Functor.map_id, CategoryTheory.NatTrans.id_app,
          Category.id_comp])).symm
  have hc : pullbackToposTensorMap f hmos A
        (SheafOfModules.unit (Stacks.SheafOfModules.Tensor.ringSheaf Y.O)) =
      (pullbackModulesSiteIso f hmos).inv.app
            ((A : SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf Y.O)) ⊗
              𝟙_ (SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf Y.O))) ≫
          Stacks.SheafOfModules.RingedToposPullback.pullbackTensorComparison
              (modulesHomOfSiteHom f hmos) A
              (𝟙_ (SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf Y.O))) ≫
            ((pullbackModulesSiteIso f hmos).hom.app A ▷
                (modulesHomOfSiteHom f hmos).pullbackModules.obj
                  (𝟙_ (SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf Y.O)))) ≫
              ((f.pullbackTopos : SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf Y.O) ⥤
                      SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf X.O)).obj A ◁
                (pullbackModulesSiteIso f hmos).hom.app
                  (𝟙_ (SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf Y.O)))) := by
    -- Both whiskerings are specialised before they are rewritten: at the plain definition
    -- `Stacks.SheafOfModules.Tensor.ringSheaf` the composite is not type-correct at `implicit`
    -- transparency, so `rw` cannot instantiate the metavariables of the general lemmas.
    rw [Stacks.SheafOfModules.Strict.whiskerRight_eq_tensorSheafBifunctor_map X.O
        ((pullbackModulesSiteIso f hmos).hom.app A)
        ((modulesHomOfSiteHom f hmos).pullbackModules.obj
          (𝟙_ (SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf Y.O)))),
      Stacks.SheafOfModules.Strict.whiskerLeft_eq_tensorSheafBifunctor_map X.O
        ((f.pullbackTopos : SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf Y.O) ⥤
            SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf X.O)).obj A)
        ((pullbackModulesSiteIso f hmos).hom.app
          (𝟙_ (SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf Y.O))))]
    -- The bifunctor form of a whiskering carries the identity in the other variable; dropping it
    -- is what leaves the two sides of `pullbackToposTensorMap` syntactically equal.
    simp only [CategoryTheory.Functor.map_id, CategoryTheory.NatTrans.id_app, Category.id_comp,
      Category.comp_id]
    rfl
  exact (congrArg (fun z => _ ≫ _ ≫ z) hX).trans
    ((congrArg (fun z => _ ≫ z ≫ (ρ_ ((f.pullbackTopos :
        SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf Y.O) ⥤
          SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf X.O)).obj A)).hom) hw).trans
      (congrArg (fun z => z ≫ ((f.pullbackTopos :
            SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf Y.O) ⥤
              SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf X.O)).obj A ◁
          unitComparisonAscribed f) ≫
        (ρ_ ((f.pullbackTopos : SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf Y.O) ⥤
          SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf X.O)).obj A)).hom) hc))

omit [X.J.HasSheafCompose (forget₂ CommRingCat.{u} RingCat.{u})]
  [(Stacks.SheafOfModules.Tensor.sheafTensor.{u, u, u, u, u} X.O).Additive]
  [∀ M, ((Stacks.SheafOfModules.Tensor.sheafTensor.{u, u, u, u, u} X.O).obj M).Additive]
  [(Stacks.SheafOfModules.Tensor.sheafTensor.{u, u, u, u, u} Y.O).Additive]
  [∀ M, ((Stacks.SheafOfModules.Tensor.sheafTensor.{u, u, u, u, u} Y.O).obj M).Additive]
  [∀ (A B : CochainComplex (SheafOfModules.{u}
    (Stacks.SheafOfModules.Tensor.ringSheaf X.O)) ℤ),
    HomologicalComplex.HasMapBifunctor A B
      (Stacks.SheafOfModules.Tensor.sheafTensor.{u, u, u, u, u} X.O) (ComplexShape.up ℤ)]
  [∀ (A B : CochainComplex (SheafOfModules.{u}
    (Stacks.SheafOfModules.Tensor.ringSheaf Y.O)) ℤ),
    HomologicalComplex.HasMapBifunctor A B
      (Stacks.SheafOfModules.Tensor.sheafTensor.{u, u, u, u, u} Y.O) (ComplexShape.up ℤ)] in
/-- The right-hand side of the coherence: the pullback of the unit law of
`Stacks.SheafOfModules.sheafTensorUnitNatIso` is the pullback of the right unitor of Tag 01CA. -/
private lemma rhs_eq (A : SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf Y.O)) :
    (f.pullbackTopos : SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf Y.O) ⥤
          SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf X.O)).map
        (ρ_ (A : SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf Y.O))).hom =
      f.pullbackTopos.map ((Stacks.SheafOfModules.sheafTensorUnitNatIso Y.O).hom.app A) :=
  congrArg (fun z => (f.pullbackTopos :
      SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf Y.O) ⥤
        SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf X.O)).map z)
    (Stacks.SheafOfModules.Strict.sheafTensorUnitNatIso_hom_app_eq Y.O A).symm

omit [(Stacks.SheafOfModules.Tensor.sheafTensor.{u, u, u, u, u} X.O).Additive]
  [∀ M, ((Stacks.SheafOfModules.Tensor.sheafTensor.{u, u, u, u, u} X.O).obj M).Additive]
  [(Stacks.SheafOfModules.Tensor.sheafTensor.{u, u, u, u, u} Y.O).Additive]
  [∀ M, ((Stacks.SheafOfModules.Tensor.sheafTensor.{u, u, u, u, u} Y.O).obj M).Additive]
  [∀ (A B : CochainComplex (SheafOfModules.{u}
    (Stacks.SheafOfModules.Tensor.ringSheaf X.O)) ℤ),
    HomologicalComplex.HasMapBifunctor A B
      (Stacks.SheafOfModules.Tensor.sheafTensor.{u, u, u, u, u} X.O) (ComplexShape.up ℤ)]
  [∀ (A B : CochainComplex (SheafOfModules.{u}
    (Stacks.SheafOfModules.Tensor.ringSheaf Y.O)) ℤ),
    HomologicalComplex.HasMapBifunctor A B
      (Stacks.SheafOfModules.Tensor.sheafTensor.{u, u, u, u, u} Y.O) (ComplexShape.up ℤ)] in
/-- **The module-level right-unitor coherence of Stacks 07A4 for the site-presented pullback.**
The comparison `f^*(A ⊗_{𝒪_D} 𝒪_D) ⟶ f^*A ⊗_{𝒪_C} f^*𝒪_D` of Stacks 03EL, followed by `𝟙 ⊗ ν`
for the unit comparison `ν : f^*𝒪_D ⟶ 𝒪_C` of `SheafOfModules.pullbackObjUnitToUnit` and by the
right unitor of `Stacks.SheafOfModules.sheafTensorUnitNatIso`, is the pullback of the right
unitor.

This inhabits `Stacks.Sheaves.DerivedPullback.PullbackToposRightUnitorCoherence`, the proposition
`StacksFrontier.CategoryTheory.Sites.Cohomology.DerivedPullback.PullbackToposUnitorCoherence` states
and leaves open. It is the transport of
`Stacks.SheafOfModules.RingedToposPullback.rightUnitality` along the identification of the two
pullbacks of sheaves of modules, the two unit comparisons and the two right unitors; see the
implementation notes for the three identifications. -/
theorem pullbackToposRightUnitorCoherence (hmos : f.u.IsMorphismOfSites Y.J X.J) :
    PullbackToposRightUnitorCoherence f hmos := by
  intro A
  have h1 := lhs_eq f hmos A
  have h2 := transport_rightUnitality (pullbackModulesSiteIso f hmos) A
      (Stacks.SheafOfModules.RingedToposPullback.pullbackTensorComparison
        (modulesHomOfSiteHom f hmos) A
        (𝟙_ (SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf Y.O))))
      (Stacks.SheafOfModules.RingedToposPullback.pullbackUnitComparison
        (modulesHomOfSiteHom f hmos)).hom
      (unitComparisonAscribed f) (unitComparison f hmos)
      (strictRightUnitality (modulesHomOfSiteHom f hmos) A)
  have h3 := rhs_eq f A
  exact (h1.trans h2).trans h3

end SiteMorphism

end Stacks.Sheaves.DerivedPullback

end
