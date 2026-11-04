module

public import Mathlib.CategoryTheory.Adjunction.Mates
public import StacksFrontier.AlgebraicGeometry.Spaces.Flat
public import StacksFrontier.AlgebraicGeometry.Spaces.Pushouts.FormalGlueingModulesKernel

/-!
# Flat base change in the formal glueing situation for quasi-coherent modules

Let `f : Y ⟶ X`, `Z ⊆ X` be the formal glueing situation of Stacks 0AEV, with `U = X ∖ Z`,
`V = Y ∖ f⁻¹(Z)` and with `j : U ⟶ X`, `j' : V ⟶ Y` the two open immersions.  Let `X' ⟶ X` be a
flat morphism of algebraic spaces and set `Z' = X' ×_X Z` and `Y' = X' ×_X Y`.  Stacks 0AEZ
asserts that the two pullbacks `QCoh(𝒪_X) ⟶ QCoh(𝒪_{X'})` and
`QCoh(Y → X, Z) ⟶ QCoh(Y' → X', Z')` are compatible with the functors of Stacks 0AEW and of
Stacks 0AEX.

This file supplies the base change itself: the data of the pulled-back situation, the
identification of `U'` and `V'` with the base changes of `U` and of `V`, the four comparisons of
inverse images attached to the four faces of the resulting cube, and the pullback of glueing
triples, which underlies the second of the two pullbacks the tag speaks about.  The
compatibility with the functor of Stacks 0AEW is then proved on the two module components of a
glueing triple; the overlap-isomorphism component, and the compatibility with the functor of
Stacks 0AEX, are not proved here, and the section on what is not proved says why.

## Main definitions

* `AlgebraicGeometry.Space.modulePullbackSquareComparison`: for a commutative square of
  algebraic spaces, the comparison `(g')^* ∘ f^* ≅ (f')^* ∘ g^*` of the two ways of transporting
  an `𝒪`-module around it, from the inverse-image composition law of Stacks 03LU.
* `AlgebraicGeometry.Space.moduleBaseChangeMap`: the base change map `g^*f_* ⟶ f'_*(g')^*` of a
  commutative square, as the mate of the comparison of the two composite direct images.
* `AlgebraicGeometry.Space.HasModuleFlatBaseChange`: invertibility of that map, as a property of
  the square.  This is **Stacks 073K, part (1) in degree zero**.
* `AlgebraicGeometry.Space.FormalGlueingSituation.FlatBaseChange`: **the base-change data of
  Stacks 0AEZ**, a flat morphism `X' ⟶ X` together with a second formal glueing situation whose
  spaces are the base changes of `Y`, `Z`, `U` and `V`.
* `AlgebraicGeometry.Space.FormalGlueingSituation.FlatBaseChange.openImmersionComparison`,
  `AlgebraicGeometry.Space.FormalGlueingSituation.FlatBaseChange.ambientMorphismComparison`,
  `AlgebraicGeometry.Space.FormalGlueingSituation.FlatBaseChange.overlapRestrictionComparison` and
  `AlgebraicGeometry.Space.FormalGlueingSituation.FlatBaseChange.openImmersionOverComparison`:
  the four faces of the cube, read on inverse images of `𝒪`-modules.  These are
  "pullback commutes with pullback", the first of the two inputs the source's proof uses.
* `AlgebraicGeometry.Space.FormalGlueingSituation.FlatBaseChange.pullbackGlueingComma`: **the
  pullback of glueing triples** underlying the pullback `QCoh(Y → X, Z) ⥤ QCoh(Y' → X', Z')` of
  Stacks 0AEZ, on the ambient comma category of Stacks 0AEW.
* `AlgebraicGeometry.Space.FormalGlueingSituation.FlatBaseChange.gHom` and
  `AlgebraicGeometry.Space.FormalGlueingSituation.FlatBaseChange.gYHom`: the morphisms `X' ⟶ X`
  and `Y' ⟶ Y` of the base change, read on underlying presheaves.
* `glueingDiagramComparisonLeft` and `glueingDiagramComparisonRight`, in the namespace
  `AlgebraicGeometry.Space.FormalGlueingSituation.FlatBaseChange`: the two module components of
  the comparison of the triple of Stacks 0AEW of a pulled-back `𝒪_X`-module with the pullback of
  its triple.

## Main results

* `AlgebraicGeometry.Space.openComplement_preimage`: the inverse image of an open complement is
  the open complement of the inverse image.  This is the generic form of
  `AlgebraicGeometry.Space.FormalGlueingSituation.V_eq_openComplement_preimage`.
* `AlgebraicGeometry.Space.FormalGlueingSituation.FlatBaseChange.ambientMorphism_comm`: the
  square `Y' ⟶ Y`, `X' ⟶ X` of the base change commutes on underlying presheaves.
* `AlgebraicGeometry.Space.FormalGlueingSituation.FlatBaseChange.U_eq` and
  `AlgebraicGeometry.Space.FormalGlueingSituation.FlatBaseChange.V_eq`: `U' = X' ×_X U` and
  `V' = Y' ×_Y V`, as subfunctors.  Only `Z' = X' ×_X Z` is assumed; that the two open parts of
  the pulled-back situation are the base changes of the two open parts of the original is a
  consequence, and it is what makes the cube above a cube.
* `isIso_pullbackGlueingComma_obj_hom` and `pullbackGlueingComma_obj_property`, in the
  namespace `AlgebraicGeometry.Space.FormalGlueingSituation.FlatBaseChange`: the pullback of a
  glueing triple again has an invertible structure arrow, and is again a glueing triple.  The
  second is the whole of what restricting the pullback to the glueing data of Stacks 0AEW asks
  for.

## What is not proved

The tag asserts two compatibilities.  The one with the functor of Stacks 0AEW is established on
the two module components of a glueing triple and on no more; the one with the functor of
Stacks 0AEX is not established at all.  Each gap is a separate missing input.

* Compatibility with the functor of **Stacks 0AEX** needs that flat pullback commutes with the
  direct image along a quasi-compact and quasi-separated morphism, which is **Stacks 073K**,
  part (1).  That tag is not proved in this development: what carries it is
  `AlgebraicGeometry.Space.BaseChangeDiagram.baseChangeMap`, which *constructs* the derived base
  change map of Stacks 0736 for a cartesian square of algebraic spaces and characterizes it, and
  which records that neither part (1) nor part (2) of Stacks 073K is proved.  The degree-zero
  shape in which this file would consume it is `HasModuleFlatBaseChange` below, which is
  therefore available only as a hypothesis.
* Compatibility with the functor of **Stacks 0AEW** needs no flatness, only
  "pullback commutes with pullback".  On the two module components of a glueing triple that is
  all it needs, and the two comparisons below supply it.  What is left is the third component,
  the isomorphism over the overlap, and for that the comparison is needed *coherently*.
  Written out, the square to
  be checked is an identity between two composites of the comparison
  `AlgebraicGeometry.Space.modulePullbackCompIso` of Stacks 03LU along three-fold composites
  `V' ⟶ U' ⟶ X' ⟶ X` and `V' ⟶ V ⟶ U ⟶ X`, so it is an instance of the associativity coherence
  of that comparison.  That coherence is **not** proved in this development: the "What is not
  done" section of
  `StacksFrontier/AlgebraicGeometry/Spaces/SmallEtaleModulePullbackComp.lean` records it as
  missing, together with the reason — the compatibility of
  `CategoryTheory.Adjunction.leftAdjointUniq` with whiskering, which Mathlib does not have.
  The four faces of the cube are supplied below, so what is missing is exactly the coherence
  between them and nothing else.

A third, smaller thing is left undone, and it is a measurement rather than a missing input.  The
restriction of `pullbackGlueingComma` to the glueing data of Stacks 0AEW is not assembled as a
functor `QCoh(Y → X, Z) ⥤ QCoh(Y' → X', Z')`.  The application of
`CategoryTheory.ObjectProperty.lift` that would do it exhausts the heartbeat budget at `whnf`,
with the property given explicitly as a named `CategoryTheory.ObjectProperty` and the
inclusion's type pinned; the cost is in the invertibility conjunct of the property, read through
the inclusion — merely *stating* `IsIso ((P.ι ⋙ pullbackGlueingComma).obj t).hom` for a
`t` in the glueing data already exhausts it, although the same statement with
`pullbackGlueingComma.obj t.obj` in place of the composite is cheap, and that is how
`pullbackGlueingComma_obj_property` is phrased.  Assembling the functor by hand instead, with
its two functor laws inherited from those of `pullbackGlueingComma` through
`CategoryTheory.ObjectProperty.hom_ext`, elaborates but exhausts the memory of the kernel on
those two laws.  Everything the lift consumes is proved — `pullbackGlueingComma_obj_property` is
exactly its hypothesis — so nothing mathematical is missing.  This is the same measurement that
the implementation notes of
`StacksFrontier/AlgebraicGeometry/Spaces/Pushouts/FormalGlueingModulesAdjunction.lean` record for
whole-functor identities at these concrete categories of modules.

## Implementation notes

The pulled-back situation is **given** rather than constructed.  Producing a
`AlgebraicGeometry.Space.FormalGlueingSituation` over `X'` from one over `X` would ask for the
stability under base change of quasi-compactness, quasi-separatedness, closedness, finite
presentation of the closed part, the isomorphism over the closed part, and flatness along its
inverse image; none of that is the content of Stacks 0AEZ, and the tag itself only says
"set `Z' = X' ×_X Z` and `Y' = X' ×_X Y`".  `FlatBaseChange` accordingly records the second
situation together with the cartesian identifications, which is what the two pullback functors
and the comparisons consume.  Of the open parts only the morphisms `U' ⟶ U` and `V' ⟶ V` are
carried; that they are base changes is proved, not assumed, from `Z' = X' ×_X Z` by
`U_eq` and `V_eq`.

The four comparisons are all instances of one construction,
`AlgebraicGeometry.Space.modulePullbackSquareComparison`, which is the pattern that
`AlgebraicGeometry.Space.FormalGlueingSituation.overlapPullbackComparison` already follows for
the glueing square itself: the inverse-image composition law of Stacks 03LU on each of the two
legs, interpolated by the transport along the equality of the two composites.

The pullback on glueing triples is `CategoryTheory.Comma.map` for the two comparisons over the
overlap, so its functoriality is a functoriality of comma categories and no functor law is
proved at the concrete categories of modules.  This is the discipline the files for
Stacks 0AEW, Stacks 0AEX and Stacks 0AEY record, for the reason given there.  The statement that
it restricts to the glueing data of Stacks 0AEW carries the inverse-image factor of Stacks 03DO
for `U' ⟶ U` and for `Y' ⟶ Y`, in exactly the shape in which
`AlgebraicGeometry.Space.HasLocalInverseImagePresentations` provides it, because the two outer
components of a glueing triple are required to be quasi-coherent and Stacks 03GA is conditional
here; the pullback `QCoh(𝒪_X) ⥤ QCoh(𝒪_{X'})` of the tag is
`AlgebraicGeometry.Space.quasicoherentPullback` for `X' ⟶ X`, under the same hypothesis, and is
not restated.

The module universe is the universe `u` of the schemes, because
`AlgebraicGeometry.Space.modulePullback` exists only there.

## References

* [Stacks Project, Tag 0AEZ](https://stacks.math.columbia.edu/tag/0AEZ)
* [Stacks Project, Tag 0AEV](https://stacks.math.columbia.edu/tag/0AEV)
* [Stacks Project, Tag 0AEW](https://stacks.math.columbia.edu/tag/0AEW)
* [Stacks Project, Tag 0AEX](https://stacks.math.columbia.edu/tag/0AEX)
* [Stacks Project, Tag 073K](https://stacks.math.columbia.edu/tag/073K)
* [Stacks Project, Tag 0736](https://stacks.math.columbia.edu/tag/0736)
* [Stacks Project, Tag 03LU](https://stacks.math.columbia.edu/tag/03LU)
* [Stacks Project, Tag 03GA](https://stacks.math.columbia.edu/tag/03GA)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits

universe u

namespace AlgebraicGeometry.Space

variable (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)

/-! ### Open complements and inverse images -/

/-- The inverse image of the open complement of a subfunctor is the open complement of its
inverse image: a section of the source lies in the first exactly when every restriction of its
image which factors through the subfunctor is over an empty scheme, and naturality turns that
into the defining condition of the second.

This is the generic form of
`AlgebraicGeometry.Space.FormalGlueingSituation.V_eq_openComplement_preimage`, which is the case
of the closed part of a formal glueing situation and the morphism glued along. -/
theorem openComplement_preimage {F G : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u} (T : Subfunctor G)
    (g : F ⟶ G) :
    (openComplement B S hS T).preimage g = openComplement B S hS (T.preimage g) := by
  ext A x
  simp only [openComplement, Subfunctor.preimage_obj, Set.mem_preimage]
  constructor <;> intro hx A' a ha <;> apply hx A' a <;>
    simpa only [NatTrans.naturality_apply] using ha

/-! ### The two comparisons attached to a commutative square -/

variable {B S hS}

section Square

variable {X Y X' Y' : AlgebraicSpaces B S hS} (f : X ⟶ Y) (g : Y' ⟶ Y) (f' : X' ⟶ Y')
    (g' : X' ⟶ X)

/-- **The comparison `(g')^* ∘ f^* ≅ (f')^* ∘ g^*` of inverse images around a commutative
square** of algebraic spaces: both composites are the inverse image along the common composite
`X' ⟶ Y` of the square, by the inverse-image half of Stacks 03LU.

This is the construction that
`AlgebraicGeometry.Space.FormalGlueingSituation.overlapPullbackComparison` performs for the
glueing square of Stacks 0AEV. -/
def modulePullbackSquareComparison (comm : g' ≫ f = f' ≫ g) :
    modulePullback B S hS f ⋙ modulePullback B S hS g' ≅
      modulePullback B S hS g ⋙ modulePullback B S hS f' :=
  modulePullbackCompIso B S hS g' f ≪≫
    eqToIso (congrArg (fun k : X' ⟶ Y => modulePullback B S hS k) comm) ≪≫
    (modulePullbackCompIso B S hS f' g).symm

/-- **The base change map `g^*f_* ⟶ f'_*(g')^*`** attached to a commutative square of algebraic
spaces: the mate, under the two adjunctions of Stacks 03LU for the two horizontal morphisms, of
the comparison `(g')_* ∘ f_* ≅ (f')_* ∘ g_*` of the two composite direct images around the
square.

No flatness is used: the map exists for every commutative square.  Flatness of `g` is what makes
it invertible, which is `AlgebraicGeometry.Space.HasModuleFlatBaseChange`. -/
def moduleBaseChangeMap (comm : g' ≫ f = f' ≫ g) :
    modulePushforward B S hS f ⋙ modulePullback B S hS g ⟶
      modulePullback B S hS g' ⋙ modulePushforward B S hS f' :=
  (mateEquiv (modulePullbackAdjunction B S hS g')
      (modulePullbackAdjunction B S hS g)).symm
    (TwoSquare.mk _ _ _ _
      ((modulePushforwardCompIso B S hS g' f).hom ≫
        eqToHom (congrArg (fun k : X' ⟶ Y => modulePushforward B S hS k) comm) ≫
        (modulePushforwardCompIso B S hS f' g).inv))

/-- **Stacks 073K, part (1) in degree zero**, as a property of a commutative square of algebraic
spaces: the base change map `g^*f_* ⟶ f'_*(g')^*` of
`AlgebraicGeometry.Space.moduleBaseChangeMap` is an isomorphism.

The source asserts this for a cartesian square whose `g` is flat and whose `f` is quasi-compact
and quasi-separated, in every degree of the derived direct image; the degree-zero clause is the
one the comparison of the two functors of formal glueing consumes.  It is not proved in this
development, so it appears as a hypothesis; see the section on what is not proved in the module
documentation. -/
def HasModuleFlatBaseChange (comm : g' ≫ f = f' ≫ g) : Prop :=
  IsIso (moduleBaseChangeMap f g f' g' comm)

end Square

namespace FormalGlueingSituation

/-! ### The base-change data of Stacks 0AEZ -/

/-- **The base-change data of Stacks 0AEZ**: a flat morphism `g : X' ⟶ X` out of the ambient
space of a second formal glueing situation `D'`, whose closed part is the inverse image of the
closed part of `D` and whose space over `X'` is the base change of the space over `X`, together
with the morphisms of the two open parts.

Only `Z' = X' ×_X Z` is required of the closed parts; that the open parts of `D'` are then the
base changes of the open parts of `D` is
`AlgebraicGeometry.Space.FormalGlueingSituation.FlatBaseChange.U_eq` and
`AlgebraicGeometry.Space.FormalGlueingSituation.FlatBaseChange.V_eq`.  The pulled-back situation
is given and not constructed; see the implementation notes. -/
structure FlatBaseChange (D D' : FormalGlueingSituation B S hS) where
  /-- The morphism `g : X' ⟶ X` of ambient spaces along which everything is pulled back. -/
  g : D'.spaceX ⟶ D.spaceX
  /-- It is flat. -/
  flat_g : IsFlat B S hS g.hom
  /-- The morphism `Y' ⟶ Y` over `g`. -/
  gY : D'.spaceY ⟶ D.spaceY
  /-- `Y' = X' ×_X Y`. -/
  isPullback_Y : IsPullback gY D'.ambientMorphism D.ambientMorphism g
  /-- `Z' = X' ×_X Z`. -/
  Z_eq : D'.Z = D.Z.preimage g.hom
  /-- The morphism `U' ⟶ U` of the open complements of the closed parts. -/
  gU : D'.spaceU ⟶ D.spaceU
  /-- `U' = X' ×_X U`. -/
  isPullback_U : IsPullback gU D'.openImmersion D.openImmersion g
  /-- The morphism `V' ⟶ V` of the open complements of the inverse images of the closed parts. -/
  gV : D'.spaceV ⟶ D.spaceV
  /-- `V' = Y' ×_Y V`. -/
  isPullback_V : IsPullback gV D'.openImmersionOver D.openImmersionOver gY
  /-- The base change is compatible with the restriction `f|_V` of the morphism glued along. -/
  overlapRestriction_comm : D'.overlapRestriction ≫ gU = gV ≫ D.overlapRestriction

namespace FlatBaseChange

variable {D D' : FormalGlueingSituation B S hS} (c : FlatBaseChange D D')

/-- The morphism `X' ⟶ X` of the base change, read on underlying presheaves. -/
def gHom : D'.X ⟶ D.X := c.g.hom

/-- The morphism `Y' ⟶ Y` of the base change, read on underlying presheaves. -/
def gYHom : D'.Y ⟶ D.Y := c.gY.hom

/-- `Z' = X' ×_X Z` on underlying presheaves. -/
theorem Z_eq' : D'.Z = D.Z.preimage c.gHom := c.Z_eq

/-- The square of ambient spaces commutes on underlying presheaves: pulling back `Y` and then
mapping to `X` is mapping to `X'` and then to `X`. -/
theorem ambientMorphism_comm : c.gYHom ≫ D.f = D'.f ≫ c.gHom :=
  congrArg (fun m : D'.spaceY ⟶ D.spaceX => m.hom) c.isPullback_Y.w

/-- **`U' = X' ×_X U`.**  The open complement of the closed part of the pulled-back situation is
the inverse image of the open complement of the closed part of the original: the closed parts
correspond by `Z' = X' ×_X Z`, and taking open complements commutes with inverse images by
`AlgebraicGeometry.Space.openComplement_preimage`. -/
theorem U_eq : D'.U = D.U.preimage c.gHom :=
  (congrArg (fun T : Subfunctor D'.X => openComplement B S hS T) c.Z_eq').trans
    (openComplement_preimage B S hS D.Z c.gHom).symm

/-- **`V' = Y' ×_Y V`.**  The open complement of the inverse image of the closed part of the
pulled-back situation is the inverse image of the open complement of the inverse image of the
closed part of the original.  Both are the inverse image of `U` along the composite `Y' ⟶ X`,
read around the two legs of the commuting square of ambient spaces. -/
theorem V_eq : D'.V = D.V.preimage c.gYHom := by
  have h : (D.U.preimage c.gHom).preimage D'.f = (D.U.preimage D.f).preimage c.gYHom := by
    rw [← Subfunctor.preimage_comp, ← Subfunctor.preimage_comp, c.ambientMorphism_comm]
  exact (congrArg (fun T : Subfunctor D'.X => T.preimage D'.f) c.U_eq).trans h

/-! ### The four faces of the cube -/

/-- The comparison `(g_U)^* ∘ j^* ≅ (j')^* ∘ g^*` over the face of the cube carrying the open
immersion of the complement of the closed part: "pullback commutes with pullback" for
`U' = X' ×_X U`. -/
def openImmersionComparison :
    modulePullback B S hS D.openImmersion ⋙ modulePullback B S hS c.gU ≅
      modulePullback B S hS c.g ⋙ modulePullback B S hS D'.openImmersion :=
  modulePullbackSquareComparison D.openImmersion c.g D'.openImmersion c.gU c.isPullback_U.w

/-- The comparison `(g_Y)^* ∘ f^* ≅ (f')^* ∘ g^*` over the face of the cube carrying the
morphism glued along: "pullback commutes with pullback" for `Y' = X' ×_X Y`. -/
def ambientMorphismComparison :
    modulePullback B S hS D.ambientMorphism ⋙ modulePullback B S hS c.gY ≅
      modulePullback B S hS c.g ⋙ modulePullback B S hS D'.ambientMorphism :=
  modulePullbackSquareComparison D.ambientMorphism c.g D'.ambientMorphism c.gY c.isPullback_Y.w

/-- The comparison `(f'|_{V'})^* ∘ (g_U)^* ≅ (g_V)^* ∘ (f|_V)^*` over the face of the cube
carrying the restriction of the morphism glued along to the two open complements.  It is the
left-hand transformation the pullback on glueing triples is built from. -/
def overlapRestrictionComparison :
    modulePullback B S hS c.gU ⋙ modulePullback B S hS D'.overlapRestriction ≅
      modulePullback B S hS D.overlapRestriction ⋙ modulePullback B S hS c.gV :=
  modulePullbackSquareComparison c.gU D.overlapRestriction c.gV D'.overlapRestriction
    c.overlapRestriction_comm

/-- The comparison `(g_V)^* ∘ (j')^* ≅ (j'')^* ∘ (g_Y)^*` over the face of the cube carrying the
open immersion of the complement of the inverse image of the closed part.  It is the right-hand
transformation the pullback on glueing triples is built from. -/
def openImmersionOverComparison :
    modulePullback B S hS D.openImmersionOver ⋙ modulePullback B S hS c.gV ≅
      modulePullback B S hS c.gY ⋙ modulePullback B S hS D'.openImmersionOver :=
  modulePullbackSquareComparison D.openImmersionOver c.gY D'.openImmersionOver c.gV
    c.isPullback_V.w

/-! ### The pullback of glueing data -/

/-- The pullback of glueing triples, on the ambient comma category of Stacks 0AEW: a triple
`(H, G, φ)` goes to `((g_U)^*H, (g_Y)^*G, ψ)`, where `ψ` is `(g_V)^*φ` read through the
comparisons of inverse images over the two faces of the cube meeting the overlap.

It is `CategoryTheory.Comma.map`, so its functoriality is that of comma categories. -/
def pullbackGlueingComma : D.moduleGlueingComma ⥤ D'.moduleGlueingComma :=
  Comma.map c.overlapRestrictionComparison.hom c.openImmersionOverComparison.hom

@[simp]
theorem pullbackGlueingComma_obj_left (t : D.moduleGlueingComma) :
    (c.pullbackGlueingComma.obj t).left = (modulePullback B S hS c.gU).obj t.left := rfl

@[simp]
theorem pullbackGlueingComma_obj_right (t : D.moduleGlueingComma) :
    (c.pullbackGlueingComma.obj t).right = (modulePullback B S hS c.gY).obj t.right := rfl

theorem pullbackGlueingComma_obj_hom (t : D.moduleGlueingComma) :
    (c.pullbackGlueingComma.obj t).hom =
      c.overlapRestrictionComparison.hom.app t.left ≫
        (modulePullback B S hS c.gV).map t.hom ≫
          c.openImmersionOverComparison.hom.app t.right :=
  rfl

/-- The structure arrow of the pullback of a glueing triple is again an isomorphism: it is the
inverse image of the structure arrow of the triple, conjugated by the two comparisons of inverse
images over the faces of the cube meeting the overlap, and those are isomorphisms. -/
theorem isIso_pullbackGlueingComma_obj_hom (t : D.moduleGlueingComma) (ht : IsIso t.hom) :
    IsIso (c.pullbackGlueingComma.obj t).hom := by
  have := ht
  rw [c.pullbackGlueingComma_obj_hom t]
  exact IsIso.comp_isIso' (NatIso.hom_app_isIso c.overlapRestrictionComparison t.left)
    (IsIso.comp_isIso' (Functor.map_isIso (modulePullback B S hS c.gV) t.hom)
      (NatIso.hom_app_isIso c.openImmersionOverComparison t.right))

/-- **The pullback of a glueing triple is again a glueing triple**: its structure arrow is
invertible, and its two components are quasi-coherent by Stacks 03GA for `U' ⟶ U` and for
`Y' ⟶ Y`.  This is the whole of what the restriction of the pullback to the glueing data of
Stacks 0AEW asks for.

The two hypotheses are the inverse-image factor of Stacks 03DO for `U' ⟶ U` and for `Y' ⟶ Y`,
under which Stacks 03GA is available in this development; they are needed because the two outer
components of a glueing triple are required to be quasi-coherent.  The companion pullback
`QCoh(𝒪_X) ⥤ QCoh(𝒪_{X'})` of the tag is `AlgebraicGeometry.Space.quasicoherentPullback` for
`g`, under the same hypothesis for `g`. -/
theorem pullbackGlueingComma_obj_property
    (hU : HasLocalInverseImagePresentations B S hS c.gU)
    (hY : HasLocalInverseImagePresentations B S hS c.gY) (t : D.moduleGlueingData) :
    IsIso (c.pullbackGlueingComma.obj t.obj).hom ∧
      (c.pullbackGlueingComma.obj t.obj).left.IsQuasicoherentOnSite ∧
      (c.pullbackGlueingComma.obj t.obj).right.IsQuasicoherentOnSite :=
  ⟨c.isIso_pullbackGlueingComma_obj_hom t.obj t.property.1,
    isQuasicoherentOnSite_modulePullback B S hS c.gU hU t.obj.left t.property.2.1,
    isQuasicoherentOnSite_modulePullback B S hS c.gY hY t.obj.right t.property.2.2⟩

/-! ### Compatibility with the functor of Stacks 0AEW -/

/-- Restricting an `𝒪_X`-module to `U` and then pulling it back to `U'` is pulling it back to
`X'` and then restricting to `U'`.  This is the `𝒪_{U'}`-component of the comparison of the
triple of Stacks 0AEW of a pulled-back module with the pullback of its triple. -/
def glueingDiagramComparisonLeft :
    (D.glueingDiagram ⋙ c.pullbackGlueingComma) ⋙ Comma.fst _ _ ≅
      (modulePullback B S hS c.g ⋙ D'.glueingDiagram) ⋙ Comma.fst _ _ :=
  c.openImmersionComparison

/-- Pulling an `𝒪_X`-module back to `Y` and then to `Y'` is pulling it back to `X'` and then to
`Y'`.  This is the `𝒪_{Y'}`-component of the comparison of the triple of Stacks 0AEW of a
pulled-back module with the pullback of its triple. -/
def glueingDiagramComparisonRight :
    (D.glueingDiagram ⋙ c.pullbackGlueingComma) ⋙ Comma.snd _ _ ≅
      (modulePullback B S hS c.g ⋙ D'.glueingDiagram) ⋙ Comma.snd _ _ :=
  c.ambientMorphismComparison

end FlatBaseChange

end FormalGlueingSituation

end AlgebraicGeometry.Space

end
