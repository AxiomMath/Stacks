module

public import Mathlib.Algebra.Category.ModuleCat.AB
public import Mathlib.Algebra.Category.ModuleCat.ChangeOfRings
public import Mathlib.Algebra.Category.ModuleCat.Projective
public import Mathlib.Algebra.Homology.DerivedCategory.ExactFunctor
public import Mathlib.CategoryTheory.Abelian.GrothendieckAxioms.FunctorCategory
public import Mathlib.CategoryTheory.Adjunction.Additive
public import Mathlib.CategoryTheory.Adjunction.Evaluation
public import Mathlib.CategoryTheory.Adjunction.Unique
public import Mathlib.CategoryTheory.Adjunction.Whiskering
public import Mathlib.CategoryTheory.Functor.Derived.Adjunction
public import Mathlib.CategoryTheory.Functor.Derived.PointwiseLeftDerived
public import Mathlib.CategoryTheory.Localization.Predicate
public import Mathlib.CategoryTheory.Sites.Abelian
public import Mathlib.CategoryTheory.Triangulated.Adjunction
public import StacksFrontier.CategoryTheory.Sites.Cohomology.CategoryHomology.EvaluationToDerivedColimit
import StacksCore.Tactic.StacksAttribute

/-!
# Change of coefficient rings commutes with derived lower shriek on a chaotic site

Let `C` be a small category with the chaotic topology and let `π : Sh(C) ⟶ Sh(*)` be the point
morphism, so that lower shriek is the colimit over `Cᵒᵖ` (Stacks 08PF) and modules over the
constant sheaf of rings `B̲` are diagrams of `B`-modules on `Cᵒᵖ`
(`Stacks.ChaoticSite.constantModuleSheafEquivalence`). A ring map `f : B ⟶ B'` gives a
commutative square of ringed topoi
```
(Sh(C), B̲)  ←--h--  (Sh(C), B̲')
    |π                   |π'
   (*, B)   ←--f--     (*, B')
```
in which `h` and `f` are the identity geometric morphisms with the coefficient map `f` as
structure map, so that `h^*` and `f^*` are extension of scalars along `f`, degreewise on
diagrams respectively on modules. Stacks 08Q8 asserts `Lπ'_! ∘ Lh^* = Lf^* ∘ Lπ_!`.

Both sides are left adjoints: `Lh^* ⊣ h_*` and `Lπ'_! ⊣ π'^{-1}`, respectively `Lπ_! ⊣ π^{-1}`
and `Lf^* ⊣ f_*`, and the two composite right adjoints are the degreewise derived functors of
*one* underived functor, the constant diagram of the restriction of scalars. Uniqueness of left
adjoints therefore produces the isomorphism, with no comparison of the two left-hand sides
built by hand.

The derived functors in play exist unconditionally: extension of scalars is a right exact left
adjoint out of a category with enough projectives, which is Stacks 0794 at the projective
objects (`Stacks.CategoryHomology.hasPointwiseLeftDerivedFunctor_of_enoughProjectives`), and
the resulting derived adjunction is Stacks 09T5
(`Stacks.CategoryHomology.derivedAdjunctionOfEnoughProjectives`).

## Main definitions

* `Stacks.CategoryHomology.totalDerivedLeftAdjoint`: the total left derived functor of a right
  exact left adjoint out of an abelian category with enough projectives, with its comparison
  `totalDerivedLeftAdjointCounit` and its derived adjunction
  `totalDerivedLeftAdjointAdjunction`.
* `Stacks.ChaoticSite.pointExtendScalars` and `Stacks.ChaoticSite.diagramExtendScalars`:
  extension of scalars along `f`, on modules over the coefficient ring of the point and
  degreewise on diagrams over the site.
* `Stacks.ChaoticSite.derivedPointExtendScalars` and
  `Stacks.ChaoticSite.derivedDiagramExtendScalars`: their total left derived functors, `Lf^*`
  and `Lh^*`.

## Main results

* `Stacks.CategoryHomology.mapDerivedCategoryCompIsoOfNatIso`: two composites of degreewise
  derived functors of exact functors are isomorphic as soon as the underived composites are.
* `Stacks.ChaoticSite.derivedColimitExtendScalarsIso`: **Stacks 08Q8**.

## Implementation notes

The two coefficient rings are taken in a common universe `w` and the modules in `max u w`,
which is the convention under which
`Stacks.CategoryHomology.moduleDiagramsEnoughProjectives` and
`Stacks.CategoryHomology.hasExactColimitsOfShapeNatModuleCat` provide the hypotheses of Stacks
0794. Nothing in the argument couples the universes further.

`Stacks.CategoryHomology.totalDerivedColimit` is the instance of
`Stacks.CategoryHomology.totalDerivedLeftAdjoint` at the colimit functor, and
`Stacks.CategoryHomology.totalDerivedColimitAdjunction` the instance of
`totalDerivedLeftAdjointAdjunction` at `colimConstAdj`; the lower shriek side below uses those
rather than re-deriving them, so the derived lower shriek of 08Q8 is the same functor as the
one 08Q6 and 08Q7 are stated for.

## References

* [Stacks Project, Tag 08Q8](https://stacks.math.columbia.edu/tag/08Q8)
* [Stacks Project, Tag 08PF](https://stacks.math.columbia.edu/tag/08PF)
* [Stacks Project, Tag 03CZ](https://stacks.math.columbia.edu/tag/03CZ)
* [Stacks Project, Tag 0794](https://stacks.math.columbia.edu/tag/0794)
* [Stacks Project, Tag 09T5](https://stacks.math.columbia.edu/tag/09T5)
-/

public noncomputable section

open CategoryTheory CategoryTheory.Limits

namespace Stacks.CategoryHomology

universe w u

attribute [local instance] HasDerivedCategory.standard

/-! ### The total left derived functor of a right exact left adjoint -/

section TotalDerived

variable {A B : Type*} [Category* A] [Category* B] [Abelian A] [Abelian B]
  [HasDerivedCategory A] [HasDerivedCategory B]
  (F : A ⥤ B) [F.Additive] [PreservesFiniteColimits F] [EnoughProjectives A]
  [HasColimitsOfShape ℕ A] [HasColimitsOfShape ℕ B]
  [HasExactColimitsOfShape ℕ A] [HasExactColimitsOfShape ℕ B]
  [PreservesColimitsOfShape ℕ F]

/-- The total left derived functor of a right exact functor out of an abelian category with
enough projectives, between categories with exact countable filtered colimits which it
preserves. It exists by Stacks 0794 at the class of projective objects. -/
@[sga "4½ Etat_0 4.2.3" "clause a), special case"]
def totalDerivedLeftAdjoint : DerivedCategory A ⥤ DerivedCategory B :=
  have := hasPointwiseLeftDerivedFunctor_of_enoughProjectives F
  (F.mapHomotopyCategory (ComplexShape.up ℤ) ⋙ DerivedCategory.Qh).totalLeftDerived
    DerivedCategory.Qh (HomotopyCategory.quasiIso A (ComplexShape.up ℤ))

/-- The comparison transformation exhibiting `totalDerivedLeftAdjoint F` as a left derived
functor of `F`. -/
def totalDerivedLeftAdjointCounit :
    DerivedCategory.Qh ⋙ totalDerivedLeftAdjoint F ⟶
      F.mapHomotopyCategory (ComplexShape.up ℤ) ⋙ DerivedCategory.Qh :=
  have := hasPointwiseLeftDerivedFunctor_of_enoughProjectives F
  (F.mapHomotopyCategory (ComplexShape.up ℤ) ⋙ DerivedCategory.Qh).totalLeftDerivedCounit
    DerivedCategory.Qh (HomotopyCategory.quasiIso A (ComplexShape.up ℤ))

/-- The comparison transformation does exhibit `totalDerivedLeftAdjoint F` as a left derived
functor of `F`. -/
theorem totalDerivedLeftAdjoint_isLeftDerivedFunctor :
    (totalDerivedLeftAdjoint F).IsLeftDerivedFunctor (totalDerivedLeftAdjointCounit F)
      (HomotopyCategory.quasiIso A (ComplexShape.up ℤ)) := by
  have := hasPointwiseLeftDerivedFunctor_of_enoughProjectives F
  dsimp [totalDerivedLeftAdjoint, totalDerivedLeftAdjointCounit]
  infer_instance

/-- **Stacks 09T5 for a right exact left adjoint with enough projectives in the source**, at
the canonical model of the derived functor: the total left derived functor of `F` is left
adjoint to the degreewise derived functor of the exact right adjoint of `F`. -/
def totalDerivedLeftAdjointAdjunction {G : B ⥤ A} (adj : F ⊣ G) [G.Additive]
    [PreservesFiniteLimits G] [PreservesFiniteColimits G] :
    totalDerivedLeftAdjoint F ⊣ G.mapDerivedCategory :=
  have := totalDerivedLeftAdjoint_isLeftDerivedFunctor F
  derivedAdjunctionOfEnoughProjectives adj (totalDerivedLeftAdjoint F)
    (totalDerivedLeftAdjointCounit F)

end TotalDerived

/-! ### Comparing composites of degreewise derived functors -/

section Comparison

variable {C₁ C₂ C₃ C₄ : Type*} [Category* C₁] [Category* C₂] [Category* C₃] [Category* C₄]
  [Abelian C₁] [Abelian C₂] [Abelian C₃] [Abelian C₄]
  [HasDerivedCategory C₁] [HasDerivedCategory C₂] [HasDerivedCategory C₃]
  [HasDerivedCategory C₄]

/-- A composite of degreewise derived functors of exact functors is a lift, through the
localization `DerivedCategory.Q`, of the degreewise functor on complexes of the underived
composite. -/
@[instance_reducible]
private def mapDerivedCategoryCompLifting (F : C₁ ⥤ C₂) (G : C₂ ⥤ C₃)
    [F.Additive] [PreservesFiniteLimits F] [PreservesFiniteColimits F]
    [G.Additive] [PreservesFiniteLimits G] [PreservesFiniteColimits G] :
    Localization.Lifting DerivedCategory.Q
      (HomologicalComplex.quasiIso C₁ (ComplexShape.up ℤ))
      ((F ⋙ G).mapHomologicalComplex (ComplexShape.up ℤ) ⋙ DerivedCategory.Q)
      (F.mapDerivedCategory ⋙ G.mapDerivedCategory) :=
  ⟨(Functor.associator _ _ _).symm ≪≫
    Functor.isoWhiskerRight F.mapDerivedCategoryFactors G.mapDerivedCategory ≪≫
    Functor.associator _ _ _ ≪≫
    Functor.isoWhiskerLeft _ G.mapDerivedCategoryFactors ≪≫
    (Functor.associator _ _ _).symm⟩

/-- **Two composites of degreewise derived functors of exact functors are isomorphic as soon as
the underived composites are.** Both composites lift the degreewise functor on complexes of the
underived composite through the localization `DerivedCategory.Q`, and a lift is determined up
to isomorphism by what it lifts. -/
def mapDerivedCategoryCompIsoOfNatIso (F : C₁ ⥤ C₂) (G : C₂ ⥤ C₃) (F' : C₁ ⥤ C₄) (G' : C₄ ⥤ C₃)
    [F.Additive] [PreservesFiniteLimits F] [PreservesFiniteColimits F]
    [G.Additive] [PreservesFiniteLimits G] [PreservesFiniteColimits G]
    [F'.Additive] [PreservesFiniteLimits F'] [PreservesFiniteColimits F']
    [G'.Additive] [PreservesFiniteLimits G'] [PreservesFiniteColimits G']
    (e : F ⋙ G ≅ F' ⋙ G') :
    F.mapDerivedCategory ⋙ G.mapDerivedCategory ≅
      F'.mapDerivedCategory ⋙ G'.mapDerivedCategory :=
  have := mapDerivedCategoryCompLifting F G
  have := mapDerivedCategoryCompLifting F' G'
  Localization.liftNatIso DerivedCategory.Q
    (HomologicalComplex.quasiIso C₁ (ComplexShape.up ℤ))
    ((F ⋙ G).mapHomologicalComplex (ComplexShape.up ℤ) ⋙ DerivedCategory.Q)
    ((F' ⋙ G').mapHomologicalComplex (ComplexShape.up ℤ) ⋙ DerivedCategory.Q)
    _ _ (Functor.isoWhiskerRight (NatIso.mapHomologicalComplex e (ComplexShape.up ℤ))
      DerivedCategory.Q)

end Comparison

/-- The constant diagram of the image of an object is the image of the constant diagram: the
constant-diagram functor commutes with applying a functor to the values of a diagram. -/
private def constWhiskerRightIso {J : Type*} [Category* J] {A : Type*} [Category* A]
    {D : Type*} [Category* D] (F : A ⥤ D) :
    (Functor.const J : A ⥤ _) ⋙ (Functor.whiskeringRight J A D).obj F ≅
      F ⋙ (Functor.const J : D ⥤ _) :=
  NatIso.ofComponents (fun M => Functor.constComp J M F) (by intros; ext; simp)

end Stacks.CategoryHomology

namespace Stacks.ChaoticSite

universe w u

open Stacks.CategoryHomology

attribute [local instance] HasDerivedCategory.standard

/-! ### Extension of scalars at the point and on the site -/

section ChangeOfCoefficients

variable {B B' : Type w} [CommRing B] [CommRing B'] (f : B →+* B')

/-- Extension of scalars along `f`, on modules over the coefficient ring of the point: this is
`f^*` for the morphism `f : (*, B') ⟶ (*, B)` of ringed points. -/
abbrev pointExtendScalars.{w₁, u₁} {B B' : Type w₁} [CommRing B] [CommRing B']
    (g : B →+* B') : ModuleCat.{max u₁ w₁} B ⥤ ModuleCat.{max u₁ w₁} B' :=
  ModuleCat.extendScalars.{w₁, w₁, max u₁ w₁} g

/-- Restriction of scalars along `f`, on modules over the coefficient ring of the point: this
is `f_*`. -/
abbrev pointRestrictScalars.{w₁, u₁} {B B' : Type w₁} [CommRing B] [CommRing B']
    (g : B →+* B') : ModuleCat.{max u₁ w₁} B' ⥤ ModuleCat.{max u₁ w₁} B :=
  ModuleCat.restrictScalars.{max u₁ w₁} g

/-- **Stacks 03CZ at a point**: extension of scalars is left adjoint to restriction of
scalars. -/
abbrev pointChangeOfRingsAdjunction.{w₁, u₁} {B B' : Type w₁} [CommRing B] [CommRing B']
    (g : B →+* B') : pointExtendScalars.{w₁, u₁} g ⊣ pointRestrictScalars.{w₁, u₁} g :=
  ModuleCat.extendRestrictScalarsAdj g

/-- Extension of scalars along `f`, on modules over the point, is an additive functor. -/
instance pointExtendScalars_additive : (pointExtendScalars.{w, u} f).Additive :=
  (pointChangeOfRingsAdjunction.{w, u} f).left_adjoint_additive

variable (C : Type u) [SmallCategory C]

/-- Extension of scalars along `f`, degreewise on diagrams over the site: on a chaotic site
this is `h^*` for the coefficient morphism `h : (Sh(C), B̲') ⟶ (Sh(C), B̲)`, read through the
identification of modules over a constant sheaf of rings with diagrams of modules. -/
abbrev diagramExtendScalars :
    (Cᵒᵖ ⥤ ModuleCat.{max u w} B) ⥤ (Cᵒᵖ ⥤ ModuleCat.{max u w} B') :=
  (Functor.whiskeringRight Cᵒᵖ _ _).obj (pointExtendScalars.{w, u} f)

/-- Restriction of scalars along `f`, degreewise on diagrams over the site: this is `h_*`. -/
abbrev diagramRestrictScalars :
    (Cᵒᵖ ⥤ ModuleCat.{max u w} B') ⥤ (Cᵒᵖ ⥤ ModuleCat.{max u w} B) :=
  (Functor.whiskeringRight Cᵒᵖ _ _).obj (pointRestrictScalars.{w, u} f)

/-- **Stacks 03CZ on a chaotic site**, for the coefficient morphism of a ring map: degreewise
extension of scalars is left adjoint to degreewise restriction of scalars. -/
abbrev diagramChangeOfRingsAdjunction :
    diagramExtendScalars f C ⊣ diagramRestrictScalars f C :=
  Adjunction.whiskerRight Cᵒᵖ (pointChangeOfRingsAdjunction.{w, u} f)

/-- Degreewise extension of scalars along `f`, on diagrams over `C`, is an additive functor. -/
instance diagramExtendScalars_additive : (diagramExtendScalars f C).Additive :=
  (diagramChangeOfRingsAdjunction f C).left_adjoint_additive

/-- **Derived extension of scalars at the point**, `Lf^*`. Extension of scalars is a right
exact left adjoint out of a category with enough projectives, so its total left derived functor
exists unconditionally. -/
def derivedPointExtendScalars.{w₁, u₁} {B B' : Type w₁} [CommRing B] [CommRing B']
    (g : B →+* B') :
    DerivedCategory (ModuleCat.{max u₁ w₁} B) ⥤ DerivedCategory (ModuleCat.{max u₁ w₁} B') :=
  totalDerivedLeftAdjoint (pointExtendScalars.{w₁, u₁} g)

/-- **Derived extension of scalars on diagrams**, `Lh^*`. -/
def derivedDiagramExtendScalars :
    DerivedCategory (Cᵒᵖ ⥤ ModuleCat.{max u w} B) ⥤
      DerivedCategory (Cᵒᵖ ⥤ ModuleCat.{max u w} B') :=
  totalDerivedLeftAdjoint (diagramExtendScalars f C)

/-- `Lf^*` is left adjoint to the degreewise derived restriction of scalars. -/
def derivedPointExtendScalarsAdjunction.{w₁, u₁} {B B' : Type w₁} [CommRing B] [CommRing B']
    (g : B →+* B') :
    derivedPointExtendScalars.{w₁, u₁} g ⊣
      (pointRestrictScalars.{w₁, u₁} g).mapDerivedCategory :=
  totalDerivedLeftAdjointAdjunction (pointExtendScalars.{w₁, u₁} g)
    (pointChangeOfRingsAdjunction.{w₁, u₁} g)

/-- `Lh^*` is left adjoint to the degreewise derived restriction of scalars on diagrams. -/
def derivedDiagramExtendScalarsAdjunction :
    derivedDiagramExtendScalars f C ⊣ (diagramRestrictScalars f C).mapDerivedCategory :=
  totalDerivedLeftAdjointAdjunction (diagramExtendScalars f C)
    (diagramChangeOfRingsAdjunction f C)

/-- **Stacks 08Q8.** For a ring map `f : B ⟶ B'` and the resulting commutative square of
ringed topoi over a chaotic site, derived lower shriek to the point commutes with derived
extension of coefficients: `Lπ'_! ∘ Lh^* ≅ Lf^* ∘ Lπ_!`.

Both sides are left adjoint to the degreewise derived functor of the constant diagram of the
restriction of scalars, so they agree by uniqueness of left adjoints. -/
@[stacks 08Q8]
def derivedColimitExtendScalarsIso :
    derivedDiagramExtendScalars f C ⋙ totalDerivedColimit C (ModuleCat.{max u w} B') ≅
      totalDerivedColimit C (ModuleCat.{max u w} B) ⋙ derivedPointExtendScalars.{w, u} f :=
  Adjunction.leftAdjointUniq
    ((derivedDiagramExtendScalarsAdjunction f C).comp
      (totalDerivedColimitAdjunction C (ModuleCat.{max u w} B')))
    (((totalDerivedColimitAdjunction C (ModuleCat.{max u w} B)).comp
        (derivedPointExtendScalarsAdjunction.{w, u} f)).ofNatIsoRight
      (mapDerivedCategoryCompIsoOfNatIso
        (Functor.const Cᵒᵖ : ModuleCat.{max u w} B' ⥤ _) (diagramRestrictScalars f C)
        (pointRestrictScalars.{w, u} f) (Functor.const Cᵒᵖ)
        (constWhiskerRightIso (pointRestrictScalars.{w, u} f))).symm)

end ChangeOfCoefficients

end Stacks.ChaoticSite

end
