module

public import Mathlib.AlgebraicGeometry.Morphisms.Affine
public import Mathlib.AlgebraicGeometry.Morphisms.Flat
public import Mathlib.AlgebraicGeometry.Morphisms.UnderlyingMap
public import Mathlib.AlgebraicGeometry.Morphisms.UniversallyOpen
public import Mathlib.Data.Fin.VecNotation
public import Mathlib.Tactic.FinCases
public import StacksFrontier.AlgebraicGeometry.Groupoids.More.OverPullback
public import StacksFrontier.AlgebraicGeometry.Groupoids.Stabilizer.Restriction
public import StacksCore.Tactic.StacksAttribute

/-!
# Restricting a groupoid scheme over a field

For a groupoid scheme whose object scheme is the spectrum of a field, restriction along a
field extension gives a diagram all of whose morphisms are surjective, flat, and universally
open.  Each of the three properties is stable under base change and under composition, holds
for the restricting map and for the source and target maps because all four are morphisms
between spectra of fields, and therefore holds for every arrow of the diagram.  The canonical
map from the restricted arrow scheme to the original arrow scheme is also affine.

## Main definitions

* `AlgebraicGeometry.restrictionDiagramMorphisms` lists the distinct morphisms in the defining
  restriction diagram.

## Main results

* `AlgebraicGeometry.surjective_restrictionDiagramMorphisms` states their surjectivity.
* `AlgebraicGeometry.flat_restrictionDiagramMorphisms` states their flatness.
* `AlgebraicGeometry.universallyOpen_restrictionDiagramMorphisms` states their universal
  openness.
* `AlgebraicGeometry.isAffineHom_restrictionArrowsToArrows` states the additional affineness of
  the canonical map on arrows.

## Implementation notes

The twelve entries of `restrictionDiagramMorphisms` are, in order, the restricting map, the
source and target of the original groupoid, the two projections from each inner pullback, the
two projections from the outer pullback, the source and target of the restriction, and the
dotted map to the original arrow scheme.  Identifications with spectra of fields are expressed
by isomorphisms.  A morphism between these spectra is precisely the scheme map underlying a
field extension in the direction used by the source.

## References

* [Stacks Project, Tag 04LQ](https://stacks.math.columbia.edu/tag/04LQ)
-/

@[expose] public section

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits Stacks.Groupoids

universe u

namespace AlgebraicGeometry

/-- The distinct morphisms occurring in the defining diagram of the restriction of a
groupoid scheme. -/
public noncomputable def restrictionDiagramMorphisms {S : Scheme.{u}} (G : GroupoidScheme S)
    {U' : Over S} (g : U' ⟶ G.objects) : Fin 12 → Arrow Scheme.{u} :=
  ![Arrow.mk g.left,
    Arrow.mk G.source.left,
    Arrow.mk G.target.left,
    Arrow.mk (pullback.fst g G.target).left,
    Arrow.mk (pullback.snd g G.target).left,
    Arrow.mk (pullback.fst G.source g).left,
    Arrow.mk (pullback.snd G.source g).left,
    Arrow.mk (pullback.fst (pullback.snd g G.target) (pullback.fst G.source g)).left,
    Arrow.mk (pullback.snd (pullback.snd g G.target) (pullback.fst G.source g)).left,
    Arrow.mk (restrictionSource G g).left,
    Arrow.mk (restrictionTarget G g).left,
    Arrow.mk (restrictionArrowsToArrows G g).left]

/-- Every arrow of the restriction diagram has a property which is stable under base change and
composition and which holds for the restricting map and for the source and target maps. -/
private lemma restrictionDiagramMorphisms_property {S : Scheme.{u}}
    (P : MorphismProperty Scheme.{u}) [P.IsStableUnderBaseChange] [P.IsMultiplicative]
    (G : GroupoidScheme S) {U' : Over S} (g : U' ⟶ G.objects)
    (hg : P g.left) (hs : P G.source.left) (ht : P G.target.left)
    (i : Fin 12) : P (restrictionDiagramMorphisms G g i).hom := by
  have h1 := overFibreProduct_fst g G.target ht
  have h2 := overFibreProduct_snd g G.target hg
  have h3 := overFibreProduct_fst G.source g hg
  have h4 := overFibreProduct_snd G.source g hs
  have h5 := overFibreProduct_fst (pullback.snd g G.target) (pullback.fst G.source g) h3
  have h6 := overFibreProduct_snd (pullback.snd g G.target) (pullback.fst G.source g) h2
  have h7 := overFibreProduct_comp _ _ h6 h4
  have h8 := overFibreProduct_comp _ _ h5 h1
  have h9 := overFibreProduct_comp _ _ h5 h2
  fin_cases i <;> dsimp [restrictionDiagramMorphisms] <;> assumption

/-- A scheme isomorphic to the spectrum of a field has one point and is integral. -/
private lemma subsingleton_and_isIntegral_of_iso_spec {X : Scheme.{u}} (k : Type u) [Field k]
    (e : X ≅ Spec (.of k)) : Subsingleton X ∧ IsIntegral X :=
  ⟨e.hom.homeomorph.subsingleton, IsIntegral.of_isIso e.inv⟩

/-- Every morphism in the defining restriction diagram over a field extension is
surjective. -/
@[stacks 04LQ "surjectivity"]
public lemma surjective_restrictionDiagramMorphisms {S : Scheme.{u}} (G : GroupoidScheme S)
    {U' : Over S} (g : U' ⟶ G.objects) (k k' : Type u) [Field k] [Field k']
    (_ : G.objects.left ≅ Spec (.of k)) (_ : U'.left ≅ Spec (.of k'))
    (i : Fin 12) :
    Surjective ((restrictionDiagramMorphisms G g i).hom) := by
  obtain ⟨_, _⟩ := subsingleton_and_isIntegral_of_iso_spec k ‹G.objects.left ≅ Spec (.of k)›
  obtain ⟨_, _⟩ := subsingleton_and_isIntegral_of_iso_spec k' ‹U'.left ≅ Spec (.of k')›
  have : Nonempty G.arrows.left := Nonempty.map G.identity.left inferInstance
  exact restrictionDiagramMorphisms_property @Surjective G g inferInstance inferInstance
    inferInstance i

/-- Every morphism in the defining restriction diagram over a field extension is flat. -/
@[stacks 04LQ "flatness"]
public lemma flat_restrictionDiagramMorphisms {S : Scheme.{u}} (G : GroupoidScheme S)
    {U' : Over S} (g : U' ⟶ G.objects) (k k' : Type u) [Field k] [Field k']
    (_ : G.objects.left ≅ Spec (.of k)) (_ : U'.left ≅ Spec (.of k'))
    (i : Fin 12) :
    Flat ((restrictionDiagramMorphisms G g i).hom) := by
  obtain ⟨_, _⟩ := subsingleton_and_isIntegral_of_iso_spec k ‹G.objects.left ≅ Spec (.of k)›
  obtain ⟨_, _⟩ := subsingleton_and_isIntegral_of_iso_spec k' ‹U'.left ≅ Spec (.of k')›
  exact restrictionDiagramMorphisms_property @Flat G g inferInstance inferInstance
    inferInstance i

/-- Every morphism in the defining restriction diagram over a field extension is universally
open. -/
@[stacks 04LQ "universal openness"]
public lemma universallyOpen_restrictionDiagramMorphisms {S : Scheme.{u}}
    (G : GroupoidScheme S) {U' : Over S} (g : U' ⟶ G.objects)
    (k k' : Type u) [Field k] [Field k']
    (_ : G.objects.left ≅ Spec (.of k)) (_ : U'.left ≅ Spec (.of k'))
    (i : Fin 12) :
    UniversallyOpen ((restrictionDiagramMorphisms G g i).hom) := by
  obtain ⟨_, _⟩ := subsingleton_and_isIntegral_of_iso_spec k ‹G.objects.left ≅ Spec (.of k)›
  obtain ⟨_, _⟩ := subsingleton_and_isIntegral_of_iso_spec k' ‹U'.left ≅ Spec (.of k')›
  exact restrictionDiagramMorphisms_property @UniversallyOpen G g inferInstance
    inferInstance inferInstance i

/-- The dotted morphism from the arrow scheme of a restriction to the original arrow scheme
is affine. -/
@[stacks 04LQ "affineness of the dotted morphism"]
public lemma isAffineHom_restrictionArrowsToArrows {S : Scheme.{u}} (G : GroupoidScheme S)
    {U' : Over S} (g : U' ⟶ G.objects) (k k' : Type u) [Field k] [Field k']
    (_ : G.objects.left ≅ Spec (.of k)) (_ : U'.left ≅ Spec (.of k')) :
    IsAffineHom (restrictionArrowsToArrows G g).left := by
  obtain ⟨_, _⟩ := subsingleton_and_isIntegral_of_iso_spec k ‹G.objects.left ≅ Spec (.of k)›
  obtain ⟨_, _⟩ := subsingleton_and_isIntegral_of_iso_spec k' ‹U'.left ≅ Spec (.of k')›
  have : IsAffineHom (pullback.snd g G.target).left :=
    overFibreProduct_snd _ _ inferInstance
  have : IsAffineHom (pullback.fst G.source g).left :=
    overFibreProduct_fst _ _ inferInstance
  have hOuterFst : IsAffineHom
      (pullback.fst (pullback.snd g G.target) (pullback.fst G.source g)).left :=
    overFibreProduct_fst _ _ inferInstance
  have hcomp : MorphismProperty.IsStableUnderComposition @IsAffineHom :=
    (inferInstance :
      MorphismProperty.IsMultiplicative @IsAffineHom).toIsStableUnderComposition
  exact overFibreProduct_comp _ _ hOuterFst inferInstance

end AlgebraicGeometry
