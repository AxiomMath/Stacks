module

public import Mathlib.Algebra.Homology.DerivedCategory.Ext.Map
public import StacksFrontier.Topology.Sheaves.Cohomology.ModuleComparison.CompatibilityWithRestriction
public import StacksFrontier.Topology.Sheaves.Cohomology.DerivedFunctors.CompositeComparisonInDegreeZero
public import StacksCore.Tactic.StacksAttribute

/-!
# Stacks 01F1 part (1): the comparison itself, and its degree-zero normalization

Let `X` be a topological space, `R` a sheaf of rings on `X` and `U` an open of `X`.  The
cohomology of a sheaf of `R`-modules over `U` may be computed either by deriving the
module-valued sections functor and forgetting the module structure at the end, or by forgetting
the coefficient sheaf to a sheaf of abelian groups and deriving sections there.  Stacks 01F1
part (1) asserts that the two agree, naturally in the module sheaf and compatibly with
restriction to a smaller open.

`Stacks.Cohomology.ModuleComparison.canonicalSectionsForgetIso` is that comparison, built from
the canonical identification `rightDerivedEvaluationForgetIso` of the module-valued side with
the derived composite and from `ModuleSheafCohomology.sectionsComparisonIso`, the named — not
chosen — form of Stacks 03FD.  This file records the two remaining clauses of part (1) about
*that* object, so that all three clauses of part (1) speak about one comparison.

## Main results

* `rightDerivedSectionsForgetIso`: the comparison, in the shape of the statement of Stacks 01F1
  part (1).  It is `canonicalSectionsForgetIso` by definition, and
  `rightDerivedSectionsForgetIso_eq` records that.
* `canonicalSectionsForgetIso_zero` and `rightDerivedSectionsForgetIso_zero`: the degree-zero
  normalization.  In degree zero the comparison intertwines the canonical maps from ordinary
  sections to the zeroth right derived functors.

The third clause, compatibility with restriction, is
`Stacks.Cohomology.ModuleComparison.canonicalSectionsForgetIso_naturality_open` in
`StacksFrontier.Topology.Sheaves.Cohomology.ModuleComparison.CompatibilityWithRestriction`, and is
stated about the same object.

The last two sections of this file give *the canonical comparison in every degree* as an
explicit formula:

* `extDeltaFunctorMapComp`: pushing `Ext` forward along an exact functor `F` and precomposing
  with a morphism `b : X ⟶ F.obj Y` is a morphism of `δ`-functors
  `extDeltaFunctor (𝟭 B) Y ⟶ extDeltaFunctor F X`.
* `comparisonDeltaHomOfExt` and `comparisonDeltaHomOfExt_app_zero`: that morphism transported
  to the two sides of Stacks 03FD, and the computation of its degree-zero component.
* `comparisonIso_hom_eq_extMapComp`: **the comparison of Stacks 03FD as an explicit formula in
  every degree.**

## Implementation notes

The degree-zero normalization is the composite of the normalizations of the two halves.  For
`rightDerivedEvaluationForgetIso` that is
`Stacks.Cohomology.DerivedCompTransport.rightDerivedCompIso_zero`, whose right-hand side is the
isomorphism `e : F ⋙ G ≅ H` through which the comparison is built; here `e` is
`evaluationCompForgetIso`, which is `Iso.refl` because module-valued sections followed by
forgetting *is* forgetting the coefficient sheaf followed by sections.  For
`ModuleSheafCohomology.sectionsComparisonIso` it is
`ModuleSheafCohomology.toRightDerivedZero_comp_sectionsComparisonIso`, which holds because the
comparison is the morphism of `δ`-functors normalized in degree zero.

Nothing here is a case split on the degree: unlike a comparison assembled from `Exists.choose`
in positive degree, `canonicalSectionsForgetIso` is one formula valid in every degree, and the
degree-zero normalization is a theorem about it rather than a consequence of how degree zero was
defined.

`ModuleSheafCohomology.comparisonIso`, out of which `canonicalSectionsForgetIso` is built, is in
positive degree `DeltaFunctor.IsUniversal.isoOfIso`, constructed by effacement induction, and
its only characterization is `ModuleSheafCohomology.comparisonIso_hom_eq`: it is *the* morphism
of `δ`-functors normalized in degree zero.  `comparisonIso_hom_eq_extMapComp` removes that
limitation by exhibiting a morphism of `δ`-functors with the right degree-zero component and an
explicit formula — the `Ext`-level map `e ↦ Ext.mk₀ b ∘ F(e)` of `extDeltaFunctorMapComp`.  Its
`δ`-compatibility is `Ext.mapExactFunctor_comp`, `Ext.mapExactFunctor_extClass` and
`Ext.comp_assoc`, because the connecting morphism of `extDeltaFunctor` is composition on the
right with the `Ext`-class of a short exact sequence; the degree-zero component is naturality of
`β` evaluated at the identity of `Y`, which is `extZeroIsoCoyoneda_inv_comp_extMapComp`.

The formula applies verbatim to `ModuleSheafCohomology.sectionsComparisonIso`, hence to
`canonicalSectionsForgetIso`, by instantiating `comparisonIso_hom_eq_extMapComp` at the
corepresentation data that `sectionsComparisonIso` uses.

## References

* [Stacks Project, Tag 01F1](https://stacks.math.columbia.edu/tag/01F1)
* [Stacks Project, Tag 03FD](https://stacks.math.columbia.edu/tag/03FD)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits CategoryTheory.Abelian Opposite TopologicalSpace

universe u

namespace Stacks.Cohomology.ModuleComparison

open ModuleSheafCohomology

section Space

variable {X : Type u} [TopologicalSpace X]
  (R : Sheaf (Opens.grothendieckTopology X) RingCat.{u}) (U : Opens X)

/-- Cohomology over an open subset `U`, computed by deriving module-valued sections and then
forgetting the module structure, agrees canonically and naturally with cohomology computed after
forgetting the coefficient sheaf to an abelian sheaf.

This is `canonicalSectionsForgetIso`, in the shape in which Stacks 01F1 part (1) states it; the
degree-zero normalization is `rightDerivedSectionsForgetIso_zero` and the compatibility with
restriction is `canonicalSectionsForgetIso_naturality_open`. -/
@[stacks 01F1 "part (1)"]
def rightDerivedSectionsForgetIso (n : ℕ) :
    (SheafOfModules.evaluation R (op U)).rightDerived n ⋙
        forget₂ (ModuleCat.{u} (R.obj.obj (op U))) AddCommGrpCat.{u} ≅
      SheafOfModules.toSheaf R ⋙
        ((sheafSections (Opens.grothendieckTopology X) AddCommGrpCat.{u}).obj
          (op U)).rightDerived n :=
  canonicalSectionsForgetIso R U n

/-- The comparison of Stacks 01F1 part (1) *is* `canonicalSectionsForgetIso`, the object the
restriction clause `canonicalSectionsForgetIso_naturality_open` is stated about. -/
theorem rightDerivedSectionsForgetIso_eq (n : ℕ) :
    rightDerivedSectionsForgetIso R U n = canonicalSectionsForgetIso R U n := rfl

/-- **Stacks 01F1, part (1), degree-zero normalization.**  In degree zero the comparison
intertwines the canonical maps from ordinary sections to the zeroth right derived functors.

Both halves of `canonicalSectionsForgetIso` are normalized in degree zero:
`Stacks.Cohomology.DerivedCompTransport.rightDerivedCompIso_zero` for the canonical
identification of the module-valued side with the derived composite, where the isomorphism `e`
it produces on the right is the identity `evaluationCompForgetIso`, and
`ModuleSheafCohomology.toRightDerivedZero_comp_sectionsComparisonIso` for Stacks 03FD. -/
theorem canonicalSectionsForgetIso_zero :
    Functor.whiskerRight (SheafOfModules.evaluation R (op U)).toRightDerivedZero
          (forget₂ (ModuleCat.{u} (R.obj.obj (op U))) AddCommGrpCat.{u}) ≫
        (canonicalSectionsForgetIso R U 0).hom =
      Functor.whiskerLeft (SheafOfModules.toSheaf R)
        ((sheafSections (Opens.grothendieckTopology X) AddCommGrpCat.{u}).obj
          (op U)).toRightDerivedZero := by
  dsimp only [canonicalSectionsForgetIso]
  rw [Iso.trans_hom, ← Category.assoc]
  dsimp only [rightDerivedEvaluationForgetIso]
  rw [DerivedCompTransport.rightDerivedCompIso_zero]
  have hid : (evaluationCompForgetIso R U).hom ≫
        (SheafOfModules.toSheaf R ⋙
          (sheafSections (Opens.grothendieckTopology X) AddCommGrpCat.{u}).obj
            (op U)).toRightDerivedZero =
      (SheafOfModules.toSheaf R ⋙
        (sheafSections (Opens.grothendieckTopology X) AddCommGrpCat.{u}).obj
          (op U)).toRightDerivedZero := Category.id_comp _
  exact (eq_whisker hid _).trans
    (toRightDerivedZero_comp_sectionsComparisonIso (Opens.grothendieckTopology X) R U)

/-- In degree zero the comparison `rightDerivedSectionsForgetIso` intertwines the canonical maps
from ordinary sections to the zeroth right derived functors. -/
@[stacks 01F1 "part (1), degree-zero normalization"]
theorem rightDerivedSectionsForgetIso_zero :
    Functor.whiskerRight (SheafOfModules.evaluation R (op U)).toRightDerivedZero
          (forget₂ (ModuleCat.{u} (R.obj.obj (op U))) AddCommGrpCat.{u}) ≫
        (rightDerivedSectionsForgetIso R U 0).hom =
      Functor.whiskerLeft (SheafOfModules.toSheaf R)
        ((sheafSections (Opens.grothendieckTopology X) AddCommGrpCat.{u}).obj
          (op U)).toRightDerivedZero :=
  canonicalSectionsForgetIso_zero R U

end Space

/-! ### The canonical comparison in every degree, at the level of `Ext` -/

section ExtDelta

universe w uA uB

variable {A : Type uA} [Category.{w} A] [Abelian A] [HasExt.{w} A]
  {B : Type uB} [Category.{w} B] [Abelian B] [HasExt.{w} B]
  (F : B ⥤ A) [F.Additive] [PreservesFiniteLimits F] [PreservesFiniteColimits F]

/-- **Pushing an `Ext` class along an exact functor and precomposing with a morphism**, as an
additive map `Ext Y Z n →+ Ext X (F.obj Z) n`.  Given `b : X ⟶ F.obj Y`, a class
`e : Ext Y Z n` is sent to `Ext.mk₀ b` composed with the image `e.mapExactFunctor F` of `e`
under `F`. -/
def extMapCompHom {X : A} {Y : B} (b : X ⟶ F.obj Y) (n : ℕ) (Z : B) :
    Ext.{w} Y Z n →+ Ext.{w} X (F.obj Z) n :=
  ((Ext.mk₀ b).precomp (F.obj Z) (zero_add n)).comp (F.mapExtAddHom Y Z n)

/-- `extMapCompHom` on a class, unfolded. -/
@[simp]
lemma extMapCompHom_apply {X : A} {Y : B} (b : X ⟶ F.obj Y) (n : ℕ) (Z : B)
    (e : Ext.{w} Y Z n) :
    extMapCompHom F b n Z e = (Ext.mk₀ b).comp (e.mapExactFunctor F) (zero_add n) := rfl

/-- **`extMapCompHom` as a natural transformation `Ext Y (-) n ⟶ Ext X (F -) n`.**  Both
functors act on morphisms by composing on the right with `Ext.mk₀`, and `Ext.mapExactFunctor`
turns that composition into the composition with the image morphism
(`Ext.mapExactFunctor_comp` and `Ext.mapExactFunctor_mk₀`), so naturality is associativity of
`Ext`-composition. -/
def extMapComp {X : A} {Y : B} (b : X ⟶ F.obj Y) (n : ℕ) :
    𝟭 B ⋙ extFunctorObj Y n ⟶ F ⋙ extFunctorObj X n where
  app Z := AddCommGrpCat.ofHom (extMapCompHom F b n Z)
  naturality Z Z' g := by
    have key : ∀ e : Ext.{w} Y Z n,
        (Ext.mk₀ b).comp ((e.comp (Ext.mk₀ g) (add_zero n)).mapExactFunctor F) (zero_add n) =
          ((Ext.mk₀ b).comp (e.mapExactFunctor F) (zero_add n)).comp
            (Ext.mk₀ (F.map g)) (add_zero n) := by
      intro e
      rw [Ext.mapExactFunctor_comp, Ext.mapExactFunctor_mk₀]
      exact (Ext.comp_assoc_of_third_deg_zero (Ext.mk₀ b) (e.mapExactFunctor F)
        (Ext.mk₀ (F.map g)) (zero_add n)).symm
    ext e
    exact key e

/-- **The `Ext`-level morphism of `δ`-functors underlying Stacks 03FD.**  For `b : X ⟶ F.obj Y`,
pushing forward along the exact functor `F` and precomposing with `b` is a morphism of
`δ`-functors from `Ext Y (-)` to `Ext X (F -)`.

The connecting morphism of `extDeltaFunctor` is composition on the right with the `Ext`-class of
a short exact sequence, and `Ext.mapExactFunctor_extClass` says that `F` carries the class of
`S` to the class of `S.map F`; so the compatibility is again associativity of
`Ext`-composition.  This is the piece that turns the comparison of Stacks 03FD, which is
characterized only as *the* morphism of `δ`-functors normalized in degree zero, into a formula
valid in every degree. -/
def extDeltaFunctorMapComp {X : A} {Y : B} (b : X ⟶ F.obj Y) :
    extDeltaFunctor (𝟭 B) Y ⟶ extDeltaFunctor F X where
  app n := extMapComp F b n
  comm {S} hS n := by
    have := hS.mono_f
    have := hS.epi_g
    have key : ∀ e : Ext.{w} Y S.X₃ n,
        ((Ext.mk₀ b).comp (e.mapExactFunctor F) (zero_add n)).comp
            (hS.map_of_exact F).extClass rfl =
          (Ext.mk₀ b).comp ((e.comp hS.extClass rfl).mapExactFunctor F)
            (zero_add (n + 1)) := by
      intro e
      rw [Ext.mapExactFunctor_comp, Ext.mapExactFunctor_extClass]
      exact Ext.comp_assoc (Ext.mk₀ b) (e.mapExactFunctor F) (hS.map_of_exact F).extClass
        (zero_add n) rfl (by lia)
    ext e
    exact key e

/-- **`extMapComp` in degree zero is the transformation it was built from.**  Under the
identification `ModuleSheafCohomology.extZeroIsoCoyoneda` of `Ext (-) (-) 0` with morphisms, the
degree-zero component of `extMapComp F (τ.app Y (𝟙 Y))` is `τ` itself.

On a morphism `u : Y ⟶ Z` the left-hand side is `τ.app Y (𝟙 Y) ≫ F.map u`, and that it is
`τ.app Z u` is naturality of `τ` evaluated at the identity of `Y`. -/
@[reassoc]
lemma extZeroIsoCoyoneda_inv_comp_extMapComp {X : A} {Y : B}
    (τ : preadditiveCoyoneda.obj (op Y) ⟶ F ⋙ preadditiveCoyoneda.obj (op X)) :
    (extZeroIsoCoyoneda Y).inv ≫ extMapComp F (τ.app Y (𝟙 Y)) 0 ≫
        Functor.whiskerLeft F (extZeroIsoCoyoneda X).hom = τ := by
  refine NatTrans.ext (funext fun Z => ?_)
  have hmk : ∀ (b : X ⟶ F.obj Y) (u : Y ⟶ Z),
      Ext.addEquiv₀ ((Ext.mk₀ b).comp ((Ext.addEquiv₀.symm u).mapExactFunctor F)
        (zero_add 0)) = b ≫ F.map u := by
    intro b u
    have h1 : (Ext.addEquiv₀.symm u).mapExactFunctor F = Ext.mk₀ (F.map u) := by
      rw [Ext.addEquiv₀_symm_apply, Ext.mapExactFunctor_mk₀]
    rw [h1, Ext.mk₀_comp_mk₀]
    exact Ext.addEquiv₀.apply_symm_apply (b ≫ F.map u)
  have key : ∀ u : Y ⟶ Z, τ.app Z u = τ.app Y (𝟙 Y) ≫ F.map u := fun u =>
    (congrArg (fun t : Y ⟶ Z => τ.app Z t) (Category.id_comp u)).symm.trans
      (NatTrans.naturality_apply τ u (𝟙 Y))
  ext u
  exact (hmk (τ.app Y (𝟙 Y)) u).trans (key u).symm

end ExtDelta

/-! ### Stacks 03FD as an explicit formula in every degree -/

section ExtFormula

universe w uA uB

variable {A : Type uA} [Category.{w} A] [Abelian A] [HasExt.{w} A] [HasInjectiveResolutions A]
  {B : Type uB} [Category.{w} B] [Abelian B] [HasExt.{w} B] [HasInjectiveResolutions B]
  [EnoughInjectives B]
  (F : B ⥤ A) [F.Additive] [PreservesFiniteLimits F] [PreservesFiniteColimits F]
  (G : A ⥤ Ab.{w}) [G.Additive] [PreservesFiniteLimits G]
  (X : A) (α : G ≅ preadditiveCoyoneda.obj (op X)) (Y : B)
  (β : preadditiveCoyoneda.obj (op Y) ≅ F ⋙ preadditiveCoyoneda.obj (op X))

/-- The morphism `X ⟶ F.obj Y` underlying the identification `β` of maps out of `Y` with maps
out of `X` after `F`: the image of the identity of `Y`.  By naturality `β` is recovered from it
as `u ↦ compUnit ≫ F.map u`, which is `extZeroIsoCoyoneda_inv_comp_extMapComp`. -/
def compUnit : X ⟶ F.obj Y := β.hom.app Y (𝟙 Y)

/-- **The comparison of Stacks 03FD as a morphism of `δ`-functors coming from `Ext`.**  The
`Ext`-level morphism `extDeltaFunctorMapComp F (compUnit F X Y β)`, transported along the two
identifications of `Ext` with right-derived functors that define the two sides. -/
def comparisonDeltaHomOfExt :
    selfDerivedDeltaFunctor (F ⋙ G) Y (compCorepresentation F G X α Y β) ⟶
      derivedDeltaFunctor F G X α :=
  DeltaFunctor.ofIsoHom (extDeltaFunctor (𝟭 B) Y) (fun n => (F ⋙ G).rightDerived n)
      (fun n => extFunctorObjIsoRightDerived (F ⋙ G) Y
        (compCorepresentation F G X α Y β) n) ≫
    extDeltaFunctorMapComp F (compUnit F X Y β) ≫
    DeltaFunctor.ofIsoInv (extDeltaFunctor F X) (fun n => F ⋙ G.rightDerived n)
      (fun n => Functor.isoWhiskerLeft F (extFunctorObjIsoRightDerived G X α n))

omit [EnoughInjectives B] in
/-- The components of `comparisonDeltaHomOfExt`: in every degree, the `Ext`-level formula
conjugated by the identifications of `Ext` with right-derived functors. -/
lemma comparisonDeltaHomOfExt_app (n : ℕ) :
    (comparisonDeltaHomOfExt F G X α Y β).app n =
      (extFunctorObjIsoRightDerived (F ⋙ G) Y
            (compCorepresentation F G X α Y β) n).inv ≫
          extMapComp F (compUnit F X Y β) n ≫
          Functor.whiskerLeft F (extFunctorObjIsoRightDerived G X α n).hom := rfl

omit [EnoughInjectives B] in
/-- **The degree-zero component of `comparisonDeltaHomOfExt` is the canonical one.**  Both
identifications of `Ext` with right-derived functors are, in degree zero, the corepresentation
followed by left exactness, so after cancelling those the claim is
`extZeroIsoCoyoneda_inv_comp_extMapComp`. -/
lemma comparisonDeltaHomOfExt_app_zero :
    (comparisonDeltaHomOfExt F G X α Y β).app 0 =
      (ModuleSheafCohomology.degreeZeroIso F G).hom := by
  rw [comparisonDeltaHomOfExt_app, extFunctorObjIsoRightDerived_zero,
    extFunctorObjIsoRightDerived_zero, degreeZeroIso, compCorepresentation]
  simp only [Iso.trans_inv, Iso.trans_hom, Iso.symm_inv, Iso.symm_hom,
    Functor.isoWhiskerLeft_hom, Functor.whiskerLeft_comp, Category.assoc]
  refine whisker_eq _ ?_
  rw [compUnit, extZeroIsoCoyoneda_inv_comp_extMapComp_assoc, Iso.inv_hom_id_assoc,
    ← Category.assoc, ← Functor.whiskerLeft_comp, Iso.hom_inv_id, Functor.whiskerLeft_id',
    Category.id_comp]

/-- **Stacks 03FD as an explicit formula, in every degree.**  The comparison
`ModuleSheafCohomology.comparisonIso` is characterized only as *the* morphism of `δ`-functors
normalized in degree zero, and in positive degree its construction
(`DeltaFunctor.IsUniversal.isoOfIso`, i.e. effacement induction) gives no formula.  This
supplies one: the comparison is the `Ext`-level map `e ↦ Ext.mk₀ (compUnit) ∘ (F e)`, conjugated
by the two identifications of `Ext` with right-derived functors.

This is `ModuleSheafCohomology.comparisonIso_hom_eq` applied to `comparisonDeltaHomOfExt`,
whose degree-zero component is the canonical one by
`comparisonDeltaHomOfExt_app_zero`. -/
theorem comparisonIso_hom_eq_extMapComp
    (h : ∀ (I : B) [Injective I] (n : ℕ) (e : Ext.{w} X (F.obj I) (n + 1)), e = 0) (n : ℕ) :
    (comparisonIso F G X α Y β h n).hom =
      (extFunctorObjIsoRightDerived (F ⋙ G) Y
            (compCorepresentation F G X α Y β) n).inv ≫
          extMapComp F (compUnit F X Y β) n ≫
          Functor.whiskerLeft F (extFunctorObjIsoRightDerived G X α n).hom :=
  (comparisonIso_hom_eq F G X α Y β h (comparisonDeltaHomOfExt F G X α Y β)
        (comparisonDeltaHomOfExt_app_zero F G X α Y β) n).symm.trans
    (comparisonDeltaHomOfExt_app F G X α Y β n)

end ExtFormula

end Stacks.Cohomology.ModuleComparison

end
