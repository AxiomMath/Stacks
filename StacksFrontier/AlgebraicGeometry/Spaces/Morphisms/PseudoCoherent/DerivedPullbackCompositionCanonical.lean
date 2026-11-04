module

public import StacksFrontier.AlgebraicGeometry.Spaces.Morphisms.PseudoCoherent.RelativelyPerfectHomDescent
public import StacksFrontier.AlgebraicGeometry.Spaces.SmallEtaleModulePullbackId
public import StacksFrontier.AlgebraicGeometry.Spaces.SmallEtaleModulePushforwardAssoc
public import StacksFrontier.AlgebraicGeometry.Spaces.SmallEtaleModulePushforwardUnitLaws
public import StacksFrontier.AlgebraicGeometry.Spaces.SmallEtaleTwoIsoAtlasReduction
public import StacksFrontier.CategoryTheory.Sites.Cohomology.DerivedPushforward.PullbackAdjunctionOfToposHom
public import StacksFrontier.CategoryTheory.Sites.Cohomology.DerivedPushforward.TwoIsoCoherenceOfToposHom
public import StacksFrontier.Topology.Sheaves.Cohomology.DerivedPushforward.CompositionAssociativity

/-!
# The canonical pseudofunctoriality of derived pullback on small étale topoi of spaces

For a morphism `f : X ⟶ Y` of algebraic spaces the derived pullback
`Lf^* : D(𝒪_Y) ⥤ D(𝒪_X)` of Stacks 06YY is taken along the morphism of small étale ringed topoi
of Stacks 03G8.  This file shows that it exists along every morphism, and assembles the
identifications `Lg^* ⋙ Lf^* ≅ L(f ≫ g)^*` of Stacks 0D6D and `L(𝟙 X)^* ≅ 𝟭` into a
`AlgebraicGeometry.Space.DerivedPullbackComposition`, with its associativity and unit
coherences proved.

## Main definitions

* `AlgebraicGeometry.Space.smallEtaleDerivedPullbackCompIsoOfTwoIso`: `Lg^* ⋙ Lf^* ≅ L(f ≫ g)^*`,
  the composition isomorphism of Stacks 0D6D for the morphisms of ringed topoi of `f` and `g`,
  followed by the derived pullback isomorphism of the 2-isomorphism of Stacks 03G8 comparing the
  composite of those morphisms with the morphism of ringed topoi of `f ≫ g`.
* `AlgebraicGeometry.Space.DerivedPullbackComposition.canonical`: the resulting
  pseudofunctoriality datum.

## Main results

* `AlgebraicGeometry.Space.hasLeftDerivedFunctor_smallEtaleModulePullbackOnHomotopy`: `Lf^*`
  exists along every morphism of algebraic spaces.
* `AlgebraicGeometry.Space.smallEtaleDerivedPullbackCompIsoOfTwoIso_assoc`: the cocycle identity.

## Implementation notes

The cocycle identity is assembled from three inputs: the cocycle identity of Stacks 0D6D for
morphisms of ringed topoi, read with the associator 2-isomorphism; the naturality of that
composition isomorphism in a 2-isomorphism of either factor; and the cocycle law of the
composition isomorphisms of direct images of the small étale topoi, Stacks 03G2, part (3).

The isomorphism `L(𝟙 X)^* ≅ 𝟭` is first obtained from the inverse image of modules along `𝟙 X`,
which is a left adjoint of the identity, and is then normalised against the composition
isomorphism at `(𝟙 X, 𝟙 X)` by `CategoryTheory.Functor.idIsoOfCompIso`; the unit coherence is
then the cocycle identity at `(𝟙 X, 𝟙 X, a)`.

## References

* [Stacks Project, Tag 0D6D](https://stacks.math.columbia.edu/tag/0D6D)
* [Stacks Project, Tag 06YY](https://stacks.math.columbia.edu/tag/06YY)
* [Stacks Project, Tag 03G8](https://stacks.math.columbia.edu/tag/03G8)
* [Stacks Project, Tag 03G2](https://stacks.math.columbia.edu/tag/03G2)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits
open Stacks.Cohomology.DerivedPullbackOfToposHom
open Stacks.Cohomology.DerivedPullbackCompositionOfToposHom
open Stacks.Cohomology.DerivedBaseChangeOfToposHom

namespace AlgebraicGeometry.Space

universe u

attribute [local instance 10000] HasDerivedCategory.standard

variable (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)

/-- **The derived pullback exists along every morphism of algebraic spaces**: degreewise pullback
of modules along the morphism of small étale ringed topoi, followed by localization, has an
everywhere-defined left derived functor. -/
instance hasLeftDerivedFunctor_smallEtaleModulePullbackOnHomotopy
    {X Y : AlgebraicSpaces B S hS} (f : X ⟶ Y) :
    (smallEtaleModulePullbackOnHomotopy B S hS f).HasLeftDerivedFunctor
      (smallEtaleModuleQuasiIso B S hS Y) :=
  hasLeftDerivedFunctor_pullbackOnHomotopy (smallEtaleRingedToposHom B S hS f)

/-- The derived pullback exists along a composite of morphisms of small étale ringed topoi of
algebraic spaces. -/
instance hasLeftDerivedFunctor_pullbackOnHomotopy_comp {X Y Z : AlgebraicSpaces B S hS}
    (f : X ⟶ Y) (g : Y ⟶ Z) :
    (pullbackOnHomotopy (RingedToposHom.comp.{u, u + 1, u, u, u + 1, u, u, u + 1, u}
      (smallEtaleRingedToposHom B S hS g)
      (smallEtaleRingedToposHom B S hS f))).HasLeftDerivedFunctor quasiIsoTarget :=
  hasLeftDerivedFunctor_pullbackOnHomotopy
    (RingedToposHom.comp.{u, u + 1, u, u, u + 1, u, u, u + 1, u}
      (smallEtaleRingedToposHom B S hS g) (smallEtaleRingedToposHom B S hS f))

/-- **Stacks 0D6D for the small étale topoi of algebraic spaces**: `Lg^* ⋙ Lf^* ≅ L(f ≫ g)^*`. -/
def smallEtaleDerivedPullbackCompIsoOfTwoIso {X Y Z : AlgebraicSpaces B S hS} (f : X ⟶ Y)
    (g : Y ⟶ Z) :
    smallEtaleDerivedModulePullback B S hS g ⋙ smallEtaleDerivedModulePullback B S hS f ≅
      smallEtaleDerivedModulePullback B S hS (f ≫ g) :=
  derivedPullbackCompIso (smallEtaleRingedToposHom B S hS f) (smallEtaleRingedToposHom B S hS g) ≪≫
    derivedPullbackIsoOfTwoIso (X' := smallEtaleRingedTopos B S hS X)
      (Y := smallEtaleRingedTopos B S hS Z) (smallEtaleRingedToposHom_compTwoIso B S hS f g)

/-- The components of `AlgebraicGeometry.Space.smallEtaleDerivedPullbackCompIsoOfTwoIso`. -/
theorem smallEtaleDerivedPullbackCompIsoOfTwoIso_hom_app {X Y Z : AlgebraicSpaces B S hS}
    (f : X ⟶ Y) (g : Y ⟶ Z) (M : DerivedCategory
      (SheafOfModules.{u} (ringedToposStructureRingSheaf B S hS Z))) :
    (smallEtaleDerivedPullbackCompIsoOfTwoIso B S hS f g).hom.app M =
      (derivedPullbackCompComparison (smallEtaleRingedToposHom B S hS f)
          (smallEtaleRingedToposHom B S hS g)).app M ≫
        (derivedPullbackIsoOfTwoIso (X' := smallEtaleRingedTopos B S hS X)
          (Y := smallEtaleRingedTopos B S hS Z)
          (smallEtaleRingedToposHom_compTwoIso B S hS f g)).hom.app M :=
  rfl

/-- The cocycle law of the 2-isomorphisms of Stacks 03G8 comparing composites of morphisms of
small étale ringed topoi with the morphism of ringed topoi of the composite. -/
theorem smallEtaleRingedToposHom_compTwoIso_assoc {V W Y Z : AlgebraicSpaces B S hS}
    (p : V ⟶ W) (t : W ⟶ Y) (a : Y ⟶ Z) :
    ((smallEtaleRingedToposHom_compTwoIso B S hS p t).whiskerRight
        (smallEtaleRingedToposHom B S hS a)).trans
        (smallEtaleRingedToposHom_compTwoIso B S hS (p ≫ t) a) =
      ((RingedToposHom.TwoIso.associator (smallEtaleRingedToposHom B S hS p)
          (smallEtaleRingedToposHom B S hS t) (smallEtaleRingedToposHom B S hS a)).trans
        ((smallEtaleRingedToposHom_compTwoIso B S hS t a).whiskerLeft
          (smallEtaleRingedToposHom B S hS p))).trans
        (smallEtaleRingedToposHom_compTwoIso B S hS p (t ≫ a)) := by
  refine RingedToposHom.TwoIso.ext_hom.{u, u + 1, u, u, u + 1, u}
    (NatTrans.ext (funext fun M ↦ ?_))
  simp only [RingedToposHom.TwoIso.whiskerRight, RingedToposHom.TwoIso.whiskerLeft,
    RingedToposHom.TwoIso.associator, RingedToposHom.TwoIso.trans,
    smallEtaleRingedToposHom_compTwoIso]
  exact smallToposMorphismTypeU_comp_assoc B S hS p t a M

/-- Four commuting cells paste: the shape of the cocycle identity below. -/
private theorem comp_four {E : Type*} [Category E] {P Q R T U Q' R' T' Q'' R'' : E}
    {a₁ : P ⟶ Q} {a₂ : Q ⟶ R} {a₃ : R ⟶ T} {a₄ : T ⟶ U} {b₁ : P ⟶ Q'} {b₂ : Q' ⟶ R'}
    {b₃ : R' ⟶ T'} {b₄ : T' ⟶ U} {c₁ : Q ⟶ Q''} {c₂ : Q'' ⟶ T} {d₁ : Q'' ⟶ R''}
    {d₂ : R'' ⟶ T'} {e₁ : Q' ⟶ R''}
    (hR : c₁ ≫ c₂ = a₂ ≫ a₃) (hT : c₂ ≫ a₄ = (d₁ ≫ d₂) ≫ b₄)
    (hA : a₁ ≫ c₁ ≫ d₁ = b₁ ≫ e₁) (hL : e₁ ≫ d₂ = b₂ ≫ b₃) :
    a₁ ≫ a₂ ≫ a₃ ≫ a₄ = b₁ ≫ b₂ ≫ b₃ ≫ b₄ := by
  rw [← reassoc_of% hR, hT, Category.assoc, reassoc_of% hA, ← reassoc_of% hL]

/-- **The cocycle identity for the composition isomorphisms of derived pullbacks** on the small
étale topoi of algebraic spaces. -/
theorem smallEtaleDerivedPullbackCompIsoOfTwoIso_assoc {V W Y Z : AlgebraicSpaces B S hS}
    (p : V ⟶ W) (t : W ⟶ Y) (a : Y ⟶ Z)
    (M : DerivedCategory (SheafOfModules.{u} (ringedToposStructureRingSheaf B S hS Z))) :
    (smallEtaleDerivedPullbackCompIsoOfTwoIso B S hS p t).hom.app
          ((smallEtaleDerivedModulePullback B S hS a).obj M) ≫
        (smallEtaleDerivedPullbackCompIsoOfTwoIso B S hS (p ≫ t) a).hom.app M =
      (smallEtaleDerivedModulePullback B S hS p).map
          ((smallEtaleDerivedPullbackCompIsoOfTwoIso B S hS t a).hom.app M) ≫
        (smallEtaleDerivedPullbackCompIsoOfTwoIso B S hS p (t ≫ a)).hom.app M := by
  have hR := derivedPullbackCompComparison_whiskerRight
    (smallEtaleRingedToposHom_compTwoIso B S hS p t) (smallEtaleRingedToposHom B S hS a) M
  have hL := derivedPullbackCompComparison_whiskerLeft (smallEtaleRingedToposHom B S hS p)
    (smallEtaleRingedToposHom_compTwoIso B S hS t a) M
  have hA := derivedPullbackCompComparison_assoc_associator (smallEtaleRingedToposHom B S hS p)
    (smallEtaleRingedToposHom B S hS t) (smallEtaleRingedToposHom B S hS a) M
  have hT := congrArg (fun e ↦ (derivedPullbackIsoOfTwoIso (X' := smallEtaleRingedTopos B S hS V)
    (Y := smallEtaleRingedTopos B S hS Z) e).hom.app M)
    (smallEtaleRingedToposHom_compTwoIso_assoc B S hS p t a)
  simp only [derivedPullbackIsoOfTwoIso_trans, Iso.trans_hom, NatTrans.comp_app] at hT
  simp only [smallEtaleDerivedPullbackCompIsoOfTwoIso_hom_app, Functor.map_comp, Category.assoc]
  exact comp_four hR hT hA hL

/-! ### The identity -/

/-- The inverse image of modules along the morphism of small étale ringed topoi of `𝟙 X` is the
identity functor: it is a left adjoint of the direct image along `𝟙 X`, which is the identity. -/
def smallEtalePullbackModulesIdIso (X : AlgebraicSpaces B S hS) :
    (smallEtaleRingedToposHom B S hS (𝟙 X)).toModulesHom.pullbackModules ≅
      𝟭 (SheafOfModules.{u} (ringedToposStructureRingSheaf B S hS X)) :=
  Adjunction.leftAdjointIdIso
    (RingedToposHom.pullbackAdjPushforwardModules (smallEtaleRingedToposHom B S hS (𝟙 X)))
    (RingedToposHom.pushforwardModulesIsoId (smallEtaleRingedToposHom B S hS (𝟙 X))
      (smallEtaleDirectImageIdIso B S hS X).symm
      ((forgetRing_map_fSharp B S hS (𝟙 X)).trans (structureSharpSet_id B S hS X))).symm

/-- **The derived pullback along an identity is the identity functor**, `L(𝟙 X)^* ≅ 𝟭`: both are
left derived functors of localization, the first because the inverse image of modules along
`𝟙 X` is the identity functor. -/
def smallEtaleDerivedModulePullbackIdIso (X : AlgebraicSpaces B S hS) :
    smallEtaleDerivedModulePullback B S hS (𝟙 X) ≅
      𝟭 (DerivedCategory (SheafOfModules.{u} (ringedToposStructureRingSheaf B S hS X))) :=
  letI := RingedToposHom.pullbackModules_additive (smallEtaleRingedToposHom B S hS (𝟙 X))
  letI := Functor.isLeftDerivedFunctor_of_inverts (smallEtaleModuleQuasiIso B S hS X)
    (𝟭 (DerivedCategory (SheafOfModules.{u} (ringedToposStructureRingSheaf B S hS X))))
    (Functor.rightUnitor DerivedCategory.Qh)
  Functor.leftDerivedNatIso (smallEtaleDerivedModulePullback B S hS (𝟙 X)) _
    (smallEtaleDerivedModulePullbackComparison B S hS (𝟙 X))
    (Functor.rightUnitor DerivedCategory.Qh).hom (smallEtaleModuleQuasiIso B S hS X)
    (Functor.isoWhiskerRight
        (Stacks.Homology.mapHomotopyCategoryIso (smallEtalePullbackModulesIdIso B S hS X)
            (ComplexShape.up ℤ) ≪≫
          Stacks.Cohomology.DerivedPushforwardAssociativity.mapHomotopyCategoryIdIso _ _)
        DerivedCategory.Qh ≪≫ Functor.leftUnitor _)

/-! ### The pseudofunctoriality datum -/

/-- The identification `Lg^* ⋙ Lf^* ≅ Lk^*` attached to a factorisation `f ≫ g = k`. -/
def smallEtaleDerivedPullbackFactorIso {X Y Z : AlgebraicSpaces B S hS} (f : X ⟶ Y)
    (g : Y ⟶ Z) (k : X ⟶ Z) (h : f ≫ g = k) :
    smallEtaleDerivedModulePullback B S hS g ⋙ smallEtaleDerivedModulePullback B S hS f ≅
      smallEtaleDerivedModulePullback B S hS k :=
  smallEtaleDerivedPullbackCompIsoOfTwoIso B S hS f g ≪≫
    eqToIso (congrArg (fun m : X ⟶ Z ↦ smallEtaleDerivedModulePullback B S hS m) h)

/-- The identifications of the factorisations of a threefold composite agree. -/
theorem smallEtaleDerivedPullbackFactorIso_assoc {V W Y Z : AlgebraicSpaces B S hS}
    (p : V ⟶ W) (t : W ⟶ Y) (a : Y ⟶ Z) (b : W ⟶ Z) (q : V ⟶ Y) (c : V ⟶ Z)
    (hb : t ≫ a = b) (hq : p ≫ t = q) (hc : q ≫ a = c) (hpb : p ≫ b = c)
    (M : DerivedCategory (SheafOfModules.{u} (ringedToposStructureRingSheaf B S hS Z))) :
    (smallEtaleDerivedPullbackFactorIso B S hS p t q hq).app
          ((smallEtaleDerivedModulePullback B S hS a).obj M) ≪≫
        (smallEtaleDerivedPullbackFactorIso B S hS q a c hc).app M =
      (smallEtaleDerivedModulePullback B S hS p).mapIso
          ((smallEtaleDerivedPullbackFactorIso B S hS t a b hb).app M) ≪≫
        (smallEtaleDerivedPullbackFactorIso B S hS p b c hpb).app M := by
  subst hb hq hpb
  refine Iso.ext ?_
  simp only [smallEtaleDerivedPullbackFactorIso, Iso.trans_hom, Iso.app_hom, eqToIso.hom,
    eqToHom_refl, Category.comp_id, Functor.mapIso_hom]
  exact smallEtaleDerivedPullbackCompIsoOfTwoIso_assoc B S hS p t a M

/-- The identification `L(𝟙 X)^* ≅ 𝟭`, normalised against the composition isomorphism at
`(𝟙 X, 𝟙 X)` so that the unit coherence holds. -/
def smallEtaleDerivedPullbackIdIso (X : AlgebraicSpaces B S hS) :
    smallEtaleDerivedModulePullback B S hS (𝟙 X) ≅
      𝟭 (DerivedCategory (SheafOfModules.{u} (ringedToposStructureRingSheaf B S hS X))) :=
  Functor.idIsoOfCompIso
    (smallEtaleDerivedPullbackFactorIso B S hS (𝟙 X) (𝟙 X) (𝟙 X) (Category.id_comp _))
    (smallEtaleDerivedModulePullbackIdIso B S hS X)

/-- The identification of a factorisation through an identity is the one the normalised
`L(𝟙 X)^* ≅ 𝟭` gives. -/
theorem smallEtaleDerivedPullbackFactorIso_id {X Z : AlgebraicSpaces B S hS} (a : X ⟶ Z)
    (h : 𝟙 X ≫ a = a) :
    smallEtaleDerivedPullbackFactorIso B S hS (𝟙 X) a a h =
      Functor.isoWhiskerLeft (smallEtaleDerivedModulePullback B S hS a)
          (smallEtaleDerivedPullbackIdIso B S hS X) ≪≫
        (smallEtaleDerivedModulePullback B S hS a).rightUnitor := by
  refine Functor.compIso_eq_isoWhiskerLeft_idIsoOfCompIso _ _ _ fun M ↦ ?_
  have key := congrArg Iso.hom (smallEtaleDerivedPullbackFactorIso_assoc B S hS (𝟙 X) (𝟙 X) a a
    (𝟙 X) a h (Category.id_comp _) h h M)
  simp only [Iso.trans_hom, Iso.app_hom, Functor.mapIso_hom] at key
  exact (Iso.cancel_iso_hom_right _ _
    ((smallEtaleDerivedPullbackFactorIso B S hS (𝟙 X) a a h).app M)).1 key

/-- **The canonical pseudofunctoriality of the derived pullback on the small étale topoi of
algebraic spaces**: the composition isomorphisms of Stacks 0D6D and the identification
`L(𝟙 X)^* ≅ 𝟭`, with their associativity and unit coherences. -/
def DerivedPullbackComposition.canonical : DerivedPullbackComposition B S hS where
  iso f g k h := smallEtaleDerivedPullbackFactorIso B S hS f g k h
  idIso X := smallEtaleDerivedPullbackIdIso B S hS X
  iso_assoc p t a b q c hb hq hc hpb M :=
    smallEtaleDerivedPullbackFactorIso_assoc B S hS p t a b q c hb hq hc hpb M
  iso_id a h := smallEtaleDerivedPullbackFactorIso_id B S hS a h

end AlgebraicGeometry.Space

end
