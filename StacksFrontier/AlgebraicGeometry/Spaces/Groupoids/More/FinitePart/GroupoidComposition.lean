module

public import StacksCore.Tactic.StacksAttribute
public import StacksFrontier.AlgebraicGeometry.Spaces.Groupoids.More.FinitePart.UniversalOpenGroupoidStructure

/-!
# The composition, the unit and the inverse of the finite part of a groupoid in algebraic spaces

Let `(U, R, s, t, c, e, i)` be a groupoid in algebraic spaces over `B` whose source and target
are separated and locally of finite type, and let `(U', Z_univ, s', t')` be the two structure
spaces of its finite part together with its source and target morphisms (Stacks 04RU, clauses
(1), (2) and part of (3)). This file builds the three remaining structure morphisms of the finite
part: the composition
`c' : Z_univ ×_{s', U', t'} Z_univ ⟶ Z_univ`, which on points is
`((u₁, Z₁, z₁), (u₂, Z₂, z₂)) ↦ (u₂, Z₂, c(z₁, z₂))`, the unit `e' : U' ⟶ Z_univ`, which on
points is `(u, Z) ↦ (u, Z, e(u))`, and the inverse `i' : Z_univ ⟶ Z_univ`, which on points is
`(u, Z, z) ↦ (t ∘ z, c(Z, i ∘ z), i(z))`.

The device which makes all three available is
`AlgebraicGeometry.Space.FinitePartUniversalOpen.targetPair_subspace_eq`: the open subspace of
the twisted pair `(t ∘ z, c(Z, i ∘ z))` over `Z_univ` is exactly the preimage of the universal
open subspace under the morphism `(y, r) ↦ (t'(y), r)` of ambient fibre products. In words, a
section `r` of `R` lies in the twisted pair at `y` precisely when the triple `(t'(y), r)` is a
section of `Z_univ`; this identifies the pair which the target morphism names with the pair the
twist produces, and it is proved by comparing the two cartesian squares which the universal
property `AlgebraicGeometry.Space.finiteOpenSubspaceEquiv` attaches to one and the same section
of the finite part presheaf.

## Main definitions

* `AlgebraicGeometry.Space.FinitePartUniversalOpen.arrowsInclusion`: the inclusion of the arrow
  space `Z_univ` of the finite part into the ambient fibre product `R ×_{s, U, g} U'`.
* `AlgebraicGeometry.Space.FinitePartUniversalOpen.objectsInclusion`: the inclusion of the
  object space of the finite part into the finite part presheaf, which is the morphism whose
  classified pair is the universal one.
* `AlgebraicGeometry.Space.FinitePartUniversalOpen.targetAmbientLift`: the morphism
  `R ×_{s, U, t ∘ z} Z_univ ⟶ R ×_{s, U, g} U'` of ambient fibre products which is `t'` on the
  base component and the identity on the arrow component.
* `AlgebraicGeometry.Space.FinitePartUniversalOpen.comp`: the composition morphism `c'` of the
  finite part.
* `AlgebraicGeometry.Space.FinitePartUniversalOpen.unitMap`: the unit morphism `e'` of the
  finite part.
* `AlgebraicGeometry.Space.FinitePartUniversalOpen.inverseMap`: the inverse morphism `i'` of the
  finite part.

## Main results

* `AlgebraicGeometry.Space.compose_inverseArrow_app`: composing the inverse of a section of the
  arrow space with that section returns the identity arrow at its source, `c(i(z), z) = e(s(z))`.
* `AlgebraicGeometry.Space.arrowsToBase_compose_app`: a composite of two sections of the arrow
  space lies over the same point of the base as its first entry.
* `AlgebraicGeometry.Space.FinitePartUniversalOpen.targetPair_subspace_eq`: the open subspace of
  the twisted pair is the preimage of the universal open subspace under `targetAmbientLift`.
* `AlgebraicGeometry.Space.FinitePartUniversalOpen.comp_hom_comp_source`: the source of a
  composite is the source of its second entry.
* `AlgebraicGeometry.Space.FinitePartUniversalOpen.comp_arrowMap_app`: the arrow of a composite
  is the composite of the arrows, `c'((u₁, Z₁, z₁), (u₂, Z₂, z₂)) = c(z₁, z₂)`, which is the
  compatibility of `c'` with `c` over the map `Z_univ ⟶ R`.
* `AlgebraicGeometry.Space.FinitePartUniversalOpen.comp_over`: the composition is a morphism
  over `B`, computed along the first projection, in the form the groupoid axiom asks for.
* `AlgebraicGeometry.Space.FinitePartUniversalOpen.unitMap_comp_source`: the unit is a section
  of the source morphism.
* `AlgebraicGeometry.Space.FinitePartUniversalOpen.inverseMap_comp_source` and
  `AlgebraicGeometry.Space.FinitePartUniversalOpen.inverseMap_comp_arrowMap`: the inverse
  exchanges the source with the target, and is the inverse of the given groupoid on arrows.
* `AlgebraicGeometry.Space.exists_lift_of_mem` and `AlgebraicGeometry.Space.mem_of_lift`: a
  section of a presheaf over a test object lies in a subfunctor exactly when the morphism out of
  the representable presheaf it names factors through that subfunctor.

## Implementation notes

Everything is carried by the data of a `FinitePartUniversalOpen G`, exactly as in the module
building the source and the target: no separatedness, finite type or étaleness hypothesis
appears, those having been consumed in producing the structure. Of its fields this file uses
`unit`, `unit_source`, `unit_identity`, `objects`, `objectProjection`, `objectsEquiv`,
`universalOpen` with `universalOpen_base`, `universalOpen_spec` and
`universalOpen_containsUnit`; it uses neither `objectProjection_etale`,
`objectProjection_spec` nor `universalOpen_closed`.

The three morphisms are built as factorisations through the universal open subspace, never by
choosing data out of an existence statement. For the unit that matters: the field
`universalOpen_containsUnit` is a bare existence statement, and what is extracted from it is
only the *proposition* that the range of the explicitly written unit section of the ambient
fibre product lies in the universal open subspace, after which
`CategoryTheory.Subfunctor.lift` supplies the morphism.

`AlgebraicGeometry.Space.FinitePartUniversalOpen.exists_targetSquares` is the engine of
`targetPair_subspace_eq`. It feeds one and the same section of the finite part presheaf — the
section named by `t'` at a point of `Z_univ`, which `target_comp_objectsInclusion` identifies
with the section named by the classifying morphism of the twisted pair — to the universal
property twice, once as a point of `U'` and once through the classifying morphism, and returns
the two resulting cartesian squares over the pair that section determines. Because that pair
lives over a *scheme* of the site, no base change of pairs along a morphism of algebraic spaces
is needed anywhere in this file: the universal property is stated for morphisms out of schemes
of the site, and the two squares it returns are all the comparison that is used. Sections are
handled in `exists_lift_targetPair_iff` as morphisms out of a representable presheaf rather
than as elements, so that the cartesian squares can be used by `CategoryTheory.IsPullback.lift`;
`exists_lift_of_mem` and `mem_of_lift` translate between the two descriptions.

The composition is the composite of three morphisms of ambient fibre products: the section
`(y₁, y₂) ↦ (y₂, z₁)` of the ambient fibre product of the twisted pair over `Z_univ`, the
untwisting isomorphism of
`StacksFrontier/AlgebraicGeometry/Spaces/Groupoids/More/FinitePart/GroupoidTwist.lean`, which
turns the arrow component into `c(z₁, z₂)`, and the canonical morphism of ambient fibre
products of the base change along `s'`. That this composite lands in the universal open
subspace is the identity `targetPair.subspace = universalOpen.subspace.preimage (untwist ≫ …)`,
which holds by the very definition of the twisted pair, together with
`compTwistedSection_comp_targetAmbientLift`, which says that the first morphism followed by
`targetAmbientLift` is the inclusion of `Z_univ` along the first projection — so that the
composability condition `s' ∘ pr₁ = t' ∘ pr₂` is what puts `z₁` in the twisted pair at `y₂`.

Each morphism of this file is given a name whose declared source and target are the ones its
neighbours use — `arrowsInclusion` for the inclusion of the arrow space into its ambient fibre
product, `compFst` and `compSnd` for the two projections of the fibre product on which the
composition is defined, `untwistAmbient` and `baseChangeAmbient` for the two morphisms the
composition is built from — and the identifications with the underlying unnamed composites are
separate lemmas. The reason is that the rewriting tactics check the type-correctness of a goal
at a transparency which unfolds neither the definition of the finite part's arrow space nor the
chosen fibre product of algebraic spaces: a goal mentioning, say,
`F.universalOpen.subspace.ι` to the right of a morphism into `F.arrows.obj` is rejected there
even though it elaborates. For the same reason the twisted ambient fibre product is written
over `F.targetPair.toBase` throughout, that being the form in which the open subspace of the
twisted pair carries it.

`AlgebraicGeometry.Space.compose_inverseArrow_app` is the one groupoid identity of the given
groupoid which this file needs and which the twisting module does not export; it is proved in
the evaluated groupoid from `CategoryTheory.Groupoid.comp_inv`.
`AlgebraicGeometry.Space.arrowsToBase_compose_app` is read off the target of a composite
rather than its source, since the target of a composite is the target of its *first* entry.

### What is not reached

The groupoid `(U', Z_univ, s', t', c')` is **not** assembled as an
`AlgebraicGeometry.GroupoidInAlgebraicSpaces`, and therefore neither is the canonical morphism
of groupoids of Stacks 04RU clause (3) as an
`AlgebraicGeometry.GroupoidInAlgebraicSpaces.Hom` (Stacks 043W part (2)). Of the fields of a
groupoid in algebraic spaces all are available here except `pointwiseGroupoid`, which asks for
a groupoid structure on the sections of `U'` over every test scheme whose arrows are the
sections of `Z_univ` with prescribed source and target. What is missing for it is, first, the
identity `t' ∘ c' = t' ∘ pr₁`, without which composition of arrows of that groupoid is not even
well defined: on points it is the cocycle identity
`c(c(Z₂, i ∘ z₂), i ∘ z₁) = c(Z₂, i ∘ c(z₁, z₂))` between open subspaces, and proving it needs
the pair classified by a morphism to `U'` to be compared along a morphism of *algebraic spaces*
rather than along a morphism out of a scheme of the site, which is the one comparison this file
avoids; and second, the associativity and unit identities of the composition of the given
groupoid read on sections, `c(c(a, b), d) = c(a, c(b, d))` and `c(z, e(s(z))) = z`, which the
twisting module establishes only inside private proofs. Accordingly the morphism of groupoids
of Stacks 04RU appears so far only as its two component morphisms `g` and `arrowMap`, the two
squares `arrowMap_comp_source` and `arrowMap_comp_target`, and the compatibility
`comp_arrowMap_app` of `c'` with `c`.

## References

* [Stacks Project, Tag 043W](https://stacks.math.columbia.edu/tag/043W)
* [Stacks Project, Tag 04PC](https://stacks.math.columbia.edu/tag/04PC)
* [Stacks Project, Tag 04PE](https://stacks.math.columbia.edu/tag/04PE)
* [Stacks Project, Tag 04RQ](https://stacks.math.columbia.edu/tag/04RQ)
* [Stacks Project, Tag 04RT](https://stacks.math.columbia.edu/tag/04RT)
* [Stacks Project, Tag 04RU](https://stacks.math.columbia.edu/tag/04RU)
* [Stacks Project, Tag 06K3](https://stacks.math.columbia.edu/tag/06K3)
* [Stacks Project, Tag 06K5](https://stacks.math.columbia.edu/tag/06K5)
-/

@[expose] public noncomputable section

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits Opposite

universe u v

/-- Pullbacks of presheaves on the big fppf site over `S`, given directly: instance search for
them times out under Lean v4.35.0. -/
local instance (priority := high) AlgebraicGeometry.Space.hasPullbacks_presheaf_groupoidComposition
    (B : AlgebraicGeometry.BigFppfSite.{u}) (S : AlgebraicGeometry.Scheme.{u})
    (hS : B.Contains S) :
    HasPullbacks ((AlgebraicGeometry.BigFppfOver B S hS)ᵒᵖ ⥤ Type u) :=
  Limits.functorCategoryHasLimitsOfShape

local instance (priority := high) AlgebraicGeometry.Space.hasPullback_presheaf_groupoidComposition
    (B : AlgebraicGeometry.BigFppfSite.{u}) (S : AlgebraicGeometry.Scheme.{u})
    (hS : B.Contains S)
    {X Y Z : (AlgebraicGeometry.BigFppfOver B S hS)ᵒᵖ ⥤ Type u} (f : X ⟶ Z) (g : Y ⟶ Z) :
    HasLimit (cospan f g) :=
  (AlgebraicGeometry.Space.hasPullbacks_presheaf_groupoidComposition B S hS).has_limit _

namespace AlgebraicGeometry.Space

/-! ### Sections of a subfunctor

A section of a presheaf over a test object lies in a subfunctor exactly when the morphism out of
the representable presheaf which it names factors through that subfunctor. Both directions are
used to pass between the membership statements defining a morphism into an open subspace and the
cartesian squares of the universal property of the finite part, which are statements about
morphisms.
-/

/-- A section of a presheaf lying in a subfunctor names a morphism out of the representable
presheaf which factors through that subfunctor. -/
public theorem exists_lift_of_mem {D : Type v} [Category.{u} D] {X : Dᵒᵖ ⥤ Type u}
    (Z : Subfunctor X) (V : D) (x : X.obj (op V)) (hx : x ∈ Z.obj (op V)) :
    ∃ m : yoneda.obj V ⟶ Z.toFunctor, m ≫ Z.ι = yonedaEquiv.symm x := by
  have hr : Subfunctor.range (yonedaEquiv.symm x) ≤ Z := by
    rw [Subfunctor.range_eq_ofSection, Equiv.apply_symm_apply, Subfunctor.ofSection_le_iff]
    exact hx
  exact ⟨Subfunctor.lift (yonedaEquiv.symm x) hr, Subfunctor.lift_ι (yonedaEquiv.symm x) hr⟩

/-- A section of a presheaf whose morphism out of the representable presheaf factors through a
subfunctor lies in that subfunctor. -/
public theorem mem_of_lift {D : Type v} [Category.{u} D] {X : Dᵒᵖ ⥤ Type u}
    (Z : Subfunctor X) (V : D) (x : X.obj (op V)) (m : yoneda.obj V ⟶ Z.toFunctor)
    (hm : m ≫ Z.ι = yonedaEquiv.symm x) : x ∈ Z.obj (op V) := by
  have h : x = Z.ι.app (op V) (yonedaEquiv m) := by
    rw [← yonedaEquiv_comp, hm, Equiv.apply_symm_apply]
  rw [h]
  exact (yonedaEquiv m).property

section Groupoid

variable {C : AlgebraicGeometry.BigFppfSite.{u}} {S : Scheme.{u}} {hS : C.Contains S}
  {B : AlgebraicGeometry.AlgebraicSpaces C S hS}

/-- Composing the inverse of a section of the arrow space with that section returns the identity
arrow at its source: on sections this is the cancellation `c(i(z), z) = e(s(z))`. -/
public theorem compose_inverseArrow_app
    (G : AlgebraicGeometry.GroupoidInAlgebraicSpaces C S hS B)
    (T : (AlgebraicGeometry.BigFppfOver C S hS)ᵒᵖ) (a : G.arrows.obj.obj T)
    (h : G.source.hom.app T (Deformation.inverseArrow G.toGroupoidInFunctors T a) =
      G.target.hom.app T a) :
    G.toGroupoidInFunctors.compose T
        (Deformation.inverseArrow G.toGroupoidInFunctors T a) a h =
      G.toGroupoidInFunctors.identity T (G.source.hom.app T a) := by
  set H := G.toGroupoidInFunctors
  let _ := H.evaluationGroupoid T
  set x : H.Evaluation T := H.source.app T a
  set y : H.Evaluation T := H.target.app T a
  set f₀ : x ⟶ y := (H.evaluationArrowEquiv T x y).symm ⟨a, rfl, rfl⟩
  have hval : (H.evaluationArrowEquiv T x y f₀).1 = a :=
    congrArg Subtype.val (Equiv.apply_symm_apply _ _)
  have hinv : (H.evaluationArrowEquiv T y x (Groupoid.inv f₀)).1 =
      Deformation.inverseArrow H T a := rfl
  have hcomp := H.evaluationArrowEquiv_comp T f₀ (Groupoid.inv f₀)
  rw [Groupoid.comp_inv, H.evaluationArrowEquiv_id] at hcomp
  exact (compose_congr G T _ _ _ _ h _ hinv.symm hval.symm).trans hcomp.symm

/-- A composite of two sections of the arrow space lies over the same point of the base as its
first entry, because the target of a composite is the target of its first entry. -/
public theorem arrowsToBase_compose_app
    (G : AlgebraicGeometry.GroupoidInAlgebraicSpaces C S hS B)
    (T : (AlgebraicGeometry.BigFppfOver C S hS)ᵒᵖ) (a b : G.arrows.obj.obj T)
    (h : G.source.hom.app T a = G.target.hom.app T b) :
    G.arrowsToBase.hom.app T (G.toGroupoidInFunctors.compose T a b h) =
      G.arrowsToBase.hom.app T a := by
  have htgt : G.target.hom ≫ G.objectsToBase.hom = G.arrowsToBase.hom :=
    congrArg (fun k : G.arrows ⟶ B => k.hom) G.target_over
  have e : ∀ x : G.arrows.obj.obj T, G.arrowsToBase.hom.app T x =
      G.objectsToBase.hom.app T (G.target.hom.app T x) := fun x =>
    (congrArg (fun k => k.app T x) htgt).symm
  exact ((e _).trans (congrArg (fun z => G.objectsToBase.hom.app T z)
    (target_comp_hom_app G T a b h))).trans (e a).symm

end Groupoid

namespace FinitePartUniversalOpen

variable {C : AlgebraicGeometry.BigFppfSite.{u}} {S : Scheme.{u}} {hS : C.Contains S}
  {B : AlgebraicGeometry.AlgebraicSpaces C S hS}
  {G : AlgebraicGeometry.GroupoidInAlgebraicSpaces C S hS B}

/-! ### The two inclusions of the structure spaces of the finite part -/

/-- The inclusion of the arrow space `Z_univ` of the finite part into the ambient fibre product
`R ×_{s, U, g} U'`, which is the inclusion of the universal open subspace read as a morphism out
of the arrow space. -/
public def arrowsInclusion (F : FinitePartUniversalOpen G) :
    F.arrows.obj ⟶ pullback F.universalOpen.toBase.hom G.source.hom :=
  F.universalOpen.subspace.ι

/-- The source morphism of the finite part is the first projection of the ambient fibre
product. -/
public theorem source_hom_eq (F : FinitePartUniversalOpen G) :
    F.source.hom =
      F.arrowsInclusion ≫ pullback.fst F.universalOpen.toBase.hom G.source.hom := rfl

/-- The map `Z_univ ⟶ R` on arrows is the second projection of the ambient fibre product. -/
public theorem arrowMap_hom_eq (F : FinitePartUniversalOpen G) :
    F.arrowMap.hom =
      F.arrowsInclusion ≫ pullback.snd F.universalOpen.toBase.hom G.source.hom := rfl

/-- A morphism into the arrow space whose inclusion into the ambient fibre product is `a` has
source `a` followed by the first projection. -/
private theorem comp_source_hom_eq_of_comp_arrowsInclusion (F : FinitePartUniversalOpen G)
    {X : (AlgebraicGeometry.BigFppfOver C S hS)ᵒᵖ ⥤ Type u} (k : X ⟶ F.arrows.obj)
    (a : X ⟶ pullback F.universalOpen.toBase.hom G.source.hom)
    (h : k ≫ F.arrowsInclusion = a) :
    k ≫ F.source.hom = a ≫ pullback.fst F.universalOpen.toBase.hom G.source.hom := by
  rw [F.source_hom_eq, ← Category.assoc, h]

/-- A morphism into the arrow space whose inclusion into the ambient fibre product is `a` has
arrow `a` followed by the second projection. -/
private theorem comp_arrowMap_hom_eq_of_comp_arrowsInclusion (F : FinitePartUniversalOpen G)
    {X : (AlgebraicGeometry.BigFppfOver C S hS)ᵒᵖ ⥤ Type u} (k : X ⟶ F.arrows.obj)
    (a : X ⟶ pullback F.universalOpen.toBase.hom G.source.hom)
    (h : k ≫ F.arrowsInclusion = a) :
    k ≫ F.arrowMap.hom = a ≫ pullback.snd F.universalOpen.toBase.hom G.source.hom := by
  rw [F.arrowMap_hom_eq, ← Category.assoc, h]

/-- The range of the inclusion of the arrow space is the universal open subspace. -/
public theorem range_arrowsInclusion (F : FinitePartUniversalOpen G) :
    Subfunctor.range F.arrowsInclusion = F.universalOpen.subspace :=
  Subfunctor.range_ι _

/-- The inclusion of the object space of the finite part into the finite part presheaf: the
morphism whose classified pair is the universal one. -/
public def objectsInclusion (F : FinitePartUniversalOpen G) :
    F.objects.obj ⟶
      (AlgebraicGeometry.Space.finiteOpenSubspacePresheaf C S hS G.source).toFunctor :=
  F.objectsEquiv.hom ≫
    (finitePartWithSection C S hS G.source F.unit F.unit_source).toSubfunctor.ι

/-- The pair classified by the inclusion of the object space is the universal pair. -/
public theorem objectsInclusion_spec (F : FinitePartUniversalOpen G) :
    (finiteOpenSubspaceEquiv C S hS G.source F.objects).1 F.objectsInclusion =
      F.universalOpen :=
  F.universalOpen_spec

/-- The target morphism followed by the inclusion of the object space into the finite part
presheaf is the classifying morphism of the twisted pair. -/
public theorem target_comp_objectsInclusion (F : FinitePartUniversalOpen G) :
    F.target.hom ≫ F.objectsInclusion = F.targetClassify := by
  change (Subfunctor.lift F.targetClassify F.targetClassify_range ≫ F.objectsEquiv.inv) ≫
    F.objectsEquiv.hom ≫
      (finitePartWithSection C S hS G.source F.unit F.unit_source).toSubfunctor.ι = _
  rw [Category.assoc, ← Category.assoc F.objectsEquiv.inv, Iso.inv_hom_id, Category.id_comp,
    Subfunctor.lift_ι]

/-! ### The twisted pair is the universal open subspace read at the target

The open subspace of the twisted pair `(t ∘ z, c(Z, i ∘ z))` over `Z_univ` consists of those
sections `r` of `R` for which the triple `(t'(y), r)` is a section of `Z_univ`. This is the
identification of the pair which the target morphism names with the pair which the twist
produces, and it is what gives the composition and the inverse of the finite part.
-/

/-- The morphism of ambient fibre products which is the target morphism on the base component
and the identity on the arrow component: on sections it sends `(y, r)` to `(t'(y), r)`. -/
public def targetAmbientLift (F : FinitePartUniversalOpen G) :
    pullback F.targetPair.toBase.hom G.source.hom ⟶
      pullback F.universalOpen.toBase.hom G.source.hom :=
  pullback.lift
    (pullback.fst F.targetPair.toBase.hom G.source.hom ≫ F.target.hom)
    (pullback.snd F.targetPair.toBase.hom G.source.hom) (by
      have h₁ : F.targetPair.toBase.hom = F.target.hom ≫ F.objectProjection.hom :=
        congrArg (fun k : F.arrows ⟶ G.objects => k.hom)
          (F.targetPair_toBase.trans F.arrowMap_comp_target)
      have h₂ : F.universalOpen.toBase.hom = F.objectProjection.hom :=
        congrArg (fun k : F.objects ⟶ G.objects => k.hom) F.universalOpen_base
      rw [Category.assoc, h₂, ← h₁]
      exact pullback.condition)

/-- The base component of the lift is the target morphism. -/
public theorem targetAmbientLift_fst (F : FinitePartUniversalOpen G) :
    F.targetAmbientLift ≫ pullback.fst F.universalOpen.toBase.hom G.source.hom =
      pullback.fst F.targetPair.toBase.hom G.source.hom ≫ F.target.hom :=
  pullback.lift_fst _ _ _

/-- The arrow component of the lift is unchanged. -/
public theorem targetAmbientLift_snd (F : FinitePartUniversalOpen G) :
    F.targetAmbientLift ≫ pullback.snd F.universalOpen.toBase.hom G.source.hom =
      pullback.snd F.targetPair.toBase.hom G.source.hom :=
  pullback.lift_snd _ _ _

/-- The base component of a section read through the lift, in the form in which the
cancellation laws of a fibre product present it. -/
public theorem comp_targetAmbientLift_fst (F : FinitePartUniversalOpen G)
    {X : (AlgebraicGeometry.BigFppfOver C S hS)ᵒᵖ ⥤ Type u}
    (k : X ⟶ pullback F.targetPair.toBase.hom G.source.hom) :
    (k ≫ F.targetAmbientLift) ≫ pullback.fst F.universalOpen.toBase.hom G.source.hom =
      (k ≫ pullback.fst F.targetPair.toBase.hom G.source.hom) ≫ F.target.hom :=
  ((Category.assoc _ _ _).trans
    (congrArg (fun z => k ≫ z) F.targetAmbientLift_fst)).trans (Category.assoc _ _ _).symm

/-- The arrow component of a section read through the lift, in the form in which the
cancellation laws of a fibre product present it. -/
public theorem comp_targetAmbientLift_snd (F : FinitePartUniversalOpen G)
    {X : (AlgebraicGeometry.BigFppfOver C S hS)ᵒᵖ ⥤ Type u}
    (k : X ⟶ pullback F.targetPair.toBase.hom G.source.hom) :
    (k ≫ F.targetAmbientLift) ≫ pullback.snd F.universalOpen.toBase.hom G.source.hom =
      k ≫ pullback.snd F.targetPair.toBase.hom G.source.hom :=
  (Category.assoc _ _ _).trans (congrArg (fun z => k ≫ z) F.targetAmbientLift_snd)

/-- **The two cartesian squares at a section of `Z_univ`.** The section of the finite part
presheaf named by the target morphism at a section `h` of `Z_univ` determines a pair over the
test scheme, and that one pair is simultaneously the restriction of the universal pair along
`t' ∘ h` and the restriction of the twisted pair along `h`; this returns the two cartesian
squares which the universal property attaches to those two descriptions. -/
public theorem exists_targetSquares (F : FinitePartUniversalOpen G)
    (V : AlgebraicGeometry.BigFppfOver C S hS) (h : yoneda.obj V ⟶ F.arrows.obj) :
    ∃ (q : AlgebraicGeometry.Space.FiniteOpenSubspace C S hS G.source
        (AlgebraicGeometry.schemeSpace V))
      (j₁ : q.subspace.toFunctor ⟶ F.universalOpen.subspace.toFunctor)
      (j₂ : q.subspace.toFunctor ⟶ F.targetPair.subspace.toFunctor),
      IsPullback (q.subspace.ι ≫ pullback.fst q.toBase.hom G.source.hom) j₁
          (h ≫ F.target.hom)
          (F.universalOpen.subspace.ι ≫
            pullback.fst F.universalOpen.toBase.hom G.source.hom) ∧
        IsPullback (q.subspace.ι ≫ pullback.fst q.toBase.hom G.source.hom) j₂ h
          (F.targetPair.subspace.ι ≫
            pullback.fst F.targetPair.toBase.hom G.source.hom) ∧
        j₁ ≫ F.universalOpen.subspace.ι ≫
            pullback.snd F.universalOpen.toBase.hom G.source.hom =
          q.subspace.ι ≫ pullback.snd q.toBase.hom G.source.hom ∧
        j₂ ≫ F.targetPair.subspace.ι ≫
            pullback.snd F.targetPair.toBase.hom G.source.hom =
          q.subspace.ι ≫ pullback.snd q.toBase.hom G.source.hom := by
  have hpair : F.objectsInclusion.app (op V) (yonedaEquiv (h ≫ F.target.hom)) =
      F.targetClassify.app (op V) (yonedaEquiv h) := by
    rw [yonedaEquiv_comp]
    exact congrArg
      (fun k : F.arrows.obj ⟶
          (AlgebraicGeometry.Space.finiteOpenSubspacePresheaf C S hS G.source).toFunctor =>
        k.app (op V) (yonedaEquiv h)) F.target_comp_objectsInclusion
  have spec₁ := (finiteOpenSubspaceEquiv C S hS G.source F.objects).2 F.objectsInclusion V
    (h ≫ F.target.hom)
  have spec₂ := (finiteOpenSubspaceEquiv C S hS G.source F.arrows).2 F.targetClassify V h
  rw [F.objectsInclusion_spec, hpair] at spec₁
  rw [show (finiteOpenSubspaceEquiv C S hS G.source F.arrows).1 F.targetClassify =
    F.targetPair from Equiv.apply_symm_apply _ _] at spec₂
  obtain ⟨-, j₁, sq₁, hj₁⟩ := spec₁
  obtain ⟨-, j₂, sq₂, hj₂⟩ := spec₂
  exact ⟨_, j₁, j₂, sq₁, sq₂, hj₁, hj₂⟩

/-- **A section of the twisted pair is a section of `Z_univ` at the target.** A morphism from a
representable presheaf to the ambient fibre product of the twisted pair factors through the open
subspace of that pair exactly when, read at the target, it factors through the universal open
subspace. -/
public theorem exists_lift_targetPair_iff (F : FinitePartUniversalOpen G)
    (V : AlgebraicGeometry.BigFppfOver C S hS)
    (k : yoneda.obj V ⟶ pullback F.targetPair.toBase.hom G.source.hom) :
    (∃ m : yoneda.obj V ⟶ F.targetPair.subspace.toFunctor,
        m ≫ F.targetPair.subspace.ι = k) ↔
      ∃ n : yoneda.obj V ⟶ F.universalOpen.subspace.toFunctor,
        n ≫ F.universalOpen.subspace.ι = k ≫ F.targetAmbientLift := by
  obtain ⟨q, j₁, j₂, sq₁, sq₂, hj₁, hj₂⟩ := F.exists_targetSquares V
    (k ≫ pullback.fst F.targetPair.toBase.hom G.source.hom)
  constructor
  · rintro ⟨m, hm⟩
    have hcond : 𝟙 (yoneda.obj V) ≫
        (k ≫ pullback.fst F.targetPair.toBase.hom G.source.hom) =
        m ≫ F.targetPair.subspace.ι ≫
          pullback.fst F.targetPair.toBase.hom G.source.hom := by
      rw [Category.id_comp, ← hm, Category.assoc]
    have e₁ : sq₂.lift (𝟙 (yoneda.obj V)) m hcond ≫
        q.subspace.ι ≫ pullback.fst q.toBase.hom G.source.hom = 𝟙 (yoneda.obj V) :=
      sq₂.lift_fst _ _ _
    have e₂ : sq₂.lift (𝟙 (yoneda.obj V)) m hcond ≫ j₂ = m := sq₂.lift_snd _ _ _
    refine ⟨sq₂.lift (𝟙 (yoneda.obj V)) m hcond ≫ j₁, pullback.hom_ext ?_ ?_⟩
    · rw [F.comp_targetAmbientLift_fst, Category.assoc, Category.assoc, ← sq₁.w]
      exact (Category.assoc _ _ _).symm.trans ((congrArg (· ≫ _) e₁).trans (Category.id_comp _))
    · rw [F.comp_targetAmbientLift_snd]
      simp only [Category.assoc]
      rw [hj₁, ← hj₂, reassoc_of% e₂, reassoc_of% hm]
  · rintro ⟨n, hn⟩
    have hcond : 𝟙 (yoneda.obj V) ≫
        ((k ≫ pullback.fst F.targetPair.toBase.hom G.source.hom) ≫ F.target.hom) =
        n ≫ F.universalOpen.subspace.ι ≫
          pullback.fst F.universalOpen.toBase.hom G.source.hom := by
      rw [Category.id_comp, ← F.comp_targetAmbientLift_fst, ← hn, Category.assoc]
    have e₁ : sq₁.lift (𝟙 (yoneda.obj V)) n hcond ≫
        q.subspace.ι ≫ pullback.fst q.toBase.hom G.source.hom = 𝟙 (yoneda.obj V) :=
      sq₁.lift_fst _ _ _
    have e₂ : sq₁.lift (𝟙 (yoneda.obj V)) n hcond ≫ j₁ = n := sq₁.lift_snd _ _ _
    refine ⟨sq₁.lift (𝟙 (yoneda.obj V)) n hcond ≫ j₂, pullback.hom_ext ?_ ?_⟩
    · rw [Category.assoc, Category.assoc, ← sq₂.w]
      exact (Category.assoc _ _ _).symm.trans ((congrArg (· ≫ _) e₁).trans (Category.id_comp _))
    · simp only [Category.assoc]
      rw [hj₂, ← hj₁, reassoc_of% e₂, ← Category.assoc, hn, F.comp_targetAmbientLift_snd]

/-- **The twisted pair is the universal open subspace read at the target.** The open subspace of
the pair `(t ∘ z, c(Z, i ∘ z))` over `Z_univ` is the preimage of the universal open subspace
under the morphism `(y, r) ↦ (t'(y), r)` of ambient fibre products. -/
public theorem targetPair_subspace_eq (F : FinitePartUniversalOpen G) :
    F.targetPair.subspace = F.universalOpen.subspace.preimage F.targetAmbientLift := by
  ext V x
  simp only [Subfunctor.preimage_obj, Set.mem_preimage]
  constructor
  · intro hx
    obtain ⟨m, hm⟩ := exists_lift_of_mem F.targetPair.subspace V.unop x hx
    obtain ⟨n, hn⟩ := (F.exists_lift_targetPair_iff V.unop (yonedaEquiv.symm x)).1 ⟨m, hm⟩
    refine mem_of_lift F.universalOpen.subspace V.unop _ n ?_
    rw [hn, yonedaEquiv_symm_naturality_right]
  · intro hx
    obtain ⟨n, hn⟩ := exists_lift_of_mem F.universalOpen.subspace V.unop _ hx
    obtain ⟨m, hm⟩ := (F.exists_lift_targetPair_iff V.unop (yonedaEquiv.symm x)).2
      ⟨n, by rw [hn, yonedaEquiv_symm_naturality_right]⟩
    exact mem_of_lift F.targetPair.subspace V.unop x m hm

/-! ### The composition of the finite part -/

/-- Untwisting by the tautological arrow, as a morphism of the ambient fibre products of the
twisted pair and of the base change of the universal pair along the source: on sections it sends
`(y, r)` to `(y, c(r, z))`. -/
public def untwistAmbient (F : FinitePartUniversalOpen G) :
    pullback F.targetPair.toBase.hom G.source.hom ⟶
      pullback (F.source ≫ F.universalOpen.toBase).hom G.source.hom :=
  untwistMap G F.arrowMap (F.source ≫ F.universalOpen.toBase) F.targetPair.toBase
    F.arrowMap_comp_source' F.targetPair_toBase.symm

/-- Untwisting does not move the base component. -/
public theorem untwistAmbient_fst (F : FinitePartUniversalOpen G) :
    F.untwistAmbient ≫
        pullback.fst (F.source ≫ F.universalOpen.toBase).hom G.source.hom =
      pullback.fst F.targetPair.toBase.hom G.source.hom :=
  untwistMap_fst G F.arrowMap (F.source ≫ F.universalOpen.toBase) F.targetPair.toBase
    F.arrowMap_comp_source' F.targetPair_toBase.symm

/-- The arrow component of an untwisted section is the composite with the tautological arrow. -/
public theorem untwistAmbient_snd (F : FinitePartUniversalOpen G) :
    F.untwistAmbient ≫
        pullback.snd (F.source ≫ F.universalOpen.toBase).hom G.source.hom =
      untwistPair G F.arrowMap F.targetPair.toBase F.targetPair_toBase.symm ≫ G.comp.hom :=
  untwistMap_snd G F.arrowMap (F.source ≫ F.universalOpen.toBase) F.targetPair.toBase
    F.arrowMap_comp_source' F.targetPair_toBase.symm

/-- The canonical morphism from the ambient fibre product of the base change of the universal
pair along the source to the ambient fibre product of the universal pair. -/
public def baseChangeAmbient (F : FinitePartUniversalOpen G) :
    pullback (F.source ≫ F.universalOpen.toBase).hom G.source.hom ⟶
      pullback F.universalOpen.toBase.hom G.source.hom :=
  AlgebraicGeometry.Space.baseChangeAmbientMap C S hS G.source F.universalOpen.toBase F.source

/-- The base component of that morphism is the source morphism. -/
public theorem baseChangeAmbient_fst (F : FinitePartUniversalOpen G) :
    F.baseChangeAmbient ≫ pullback.fst F.universalOpen.toBase.hom G.source.hom =
      pullback.fst (F.source ≫ F.universalOpen.toBase).hom G.source.hom ≫ F.source.hom :=
  (AlgebraicGeometry.Space.isPullback_baseChangeAmbientMap C S hS G.source
    F.universalOpen.toBase F.source).w

/-- That morphism does not move the arrow component. -/
public theorem baseChangeAmbient_snd (F : FinitePartUniversalOpen G) :
    F.baseChangeAmbient ≫ pullback.snd F.universalOpen.toBase.hom G.source.hom =
      pullback.snd (F.source ≫ F.universalOpen.toBase).hom G.source.hom :=
  AlgebraicGeometry.Space.baseChangeAmbientMap_comp_snd C S hS G.source
    F.universalOpen.toBase F.source

/-- The first projection of the fibre product `Z_univ ×_{s', U', t'} Z_univ` on which the
composition of the finite part is defined. -/
public def compFst (F : FinitePartUniversalOpen G) :
    (AlgebraicGeometry.AlgebraicSpaces.fiberProduct C S hS F.source F.target).obj ⟶
      F.arrows.obj :=
  pullback.fst F.source.hom F.target.hom

/-- The second projection of that fibre product. -/
public def compSnd (F : FinitePartUniversalOpen G) :
    (AlgebraicGeometry.AlgebraicSpaces.fiberProduct C S hS F.source F.target).obj ⟶
      F.arrows.obj :=
  pullback.snd F.source.hom F.target.hom

/-- The composability condition: the source of the first entry is the target of the second. -/
public theorem comp_condition (F : FinitePartUniversalOpen G) :
    F.compFst ≫ F.source.hom = F.compSnd ≫ F.target.hom :=
  pullback.condition

/-- The section `(y₁, y₂) ↦ (y₂, z₁)` of the ambient fibre product of the twisted pair over
`Z_univ`: the base component is the second entry of a composable pair and the arrow component is
the arrow of its first entry. -/
public def compTwistedSection (F : FinitePartUniversalOpen G) :
    (AlgebraicGeometry.AlgebraicSpaces.fiberProduct C S hS F.source F.target).obj ⟶
      pullback F.targetPair.toBase.hom G.source.hom :=
  pullback.lift F.compSnd (F.compFst ≫ F.arrowMap.hom) (by
    have h₁ : F.targetPair.toBase.hom = F.target.hom ≫ F.objectProjection.hom :=
      congrArg (fun k : F.arrows ⟶ G.objects => k.hom)
        (F.targetPair_toBase.trans F.arrowMap_comp_target)
    have h₂ : F.arrowMap.hom ≫ G.source.hom = F.source.hom ≫ F.objectProjection.hom :=
      congrArg (fun k : F.arrows ⟶ G.objects => k.hom) F.arrowMap_comp_source
    calc F.compSnd ≫ F.targetPair.toBase.hom
        = (F.compSnd ≫ F.target.hom) ≫ F.objectProjection.hom := by
            rw [h₁, Category.assoc]
      _ = (F.compFst ≫ F.source.hom) ≫ F.objectProjection.hom := by rw [F.comp_condition]
      _ = (F.compFst ≫ F.arrowMap.hom) ≫ G.source.hom := by
            simp only [Category.assoc, h₂])

/-- The base component of that section is the second entry. -/
public theorem compTwistedSection_fst (F : FinitePartUniversalOpen G) :
    F.compTwistedSection ≫ pullback.fst F.targetPair.toBase.hom G.source.hom = F.compSnd :=
  pullback.lift_fst _ _ _

/-- The arrow component of that section is the arrow of the first entry. -/
public theorem compTwistedSection_snd (F : FinitePartUniversalOpen G) :
    F.compTwistedSection ≫ pullback.snd F.targetPair.toBase.hom G.source.hom =
      F.compFst ≫ F.arrowMap.hom :=
  pullback.lift_snd _ _ _

/-- Reading that section at the target is the first entry itself: this is the composability
condition `s' ∘ pr₁ = t' ∘ pr₂`, and it is what puts the arrow of the first entry in the
twisted pair at the second entry. -/
public theorem compTwistedSection_comp_targetAmbientLift (F : FinitePartUniversalOpen G) :
    F.compTwistedSection ≫ F.targetAmbientLift = F.compFst ≫ F.arrowsInclusion := by
  apply pullback.hom_ext
  · exact (F.comp_targetAmbientLift_fst _).trans (by
      rw [F.compTwistedSection_fst, ← F.comp_condition,
        F.comp_source_hom_eq_of_comp_arrowsInclusion _ _ rfl])
  · exact ((F.comp_targetAmbientLift_snd _).trans F.compTwistedSection_snd).trans
      (F.comp_arrowMap_hom_eq_of_comp_arrowsInclusion _ _ rfl).symm

/-- The section of the twisted pair really is a section of its open subspace. -/
public theorem compTwistedSection_range (F : FinitePartUniversalOpen G) :
    Subfunctor.range F.compTwistedSection ≤ F.targetPair.subspace := by
  rw [F.targetPair_subspace_eq, ← Subfunctor.image_le_iff, ← Subfunctor.range_comp,
    F.compTwistedSection_comp_targetAmbientLift]
  exact (Subfunctor.range_comp_le _ _).trans (le_of_eq F.range_arrowsInclusion)

/-- The open subspace of the twisted pair is, by the very construction of the twist, the
preimage of the universal open subspace under untwisting followed by the canonical morphism of
ambient fibre products of the base change along the source. -/
public theorem targetPair_subspace_preimage (F : FinitePartUniversalOpen G) :
    F.targetPair.subspace =
      F.universalOpen.subspace.preimage (F.untwistAmbient ≫ F.baseChangeAmbient) := by
  rw [Subfunctor.preimage_comp]
  rfl

/-- The section of the ambient fibre product of the universal pair underlying the composition:
on sections it sends `((u₁, Z₁, z₁), (u₂, Z₂, z₂))` to the pair `((u₂, Z₂), c(z₁, z₂))`. -/
public def compAmbient (F : FinitePartUniversalOpen G) :
    (AlgebraicGeometry.AlgebraicSpaces.fiberProduct C S hS F.source F.target).obj ⟶
      pullback F.universalOpen.toBase.hom G.source.hom :=
  F.compTwistedSection ≫ F.untwistAmbient ≫ F.baseChangeAmbient

/-- The composition lands in the universal open subspace: the arrow `c(z₁, z₂)` lies in the
open subspace `Z₂` of the second entry. -/
public theorem compAmbient_range (F : FinitePartUniversalOpen G) :
    Subfunctor.range F.compAmbient ≤ F.universalOpen.subspace := by
  rw [compAmbient, Subfunctor.range_comp, Subfunctor.image_le_iff,
    ← F.targetPair_subspace_preimage]
  exact F.compTwistedSection_range

/-- The composition of the finite part as a morphism into the universal open subspace. -/
public def compArrows (F : FinitePartUniversalOpen G) :
    (AlgebraicGeometry.AlgebraicSpaces.fiberProduct C S hS F.source F.target).obj ⟶
      F.universalOpen.subspace.toFunctor :=
  Subfunctor.lift F.compAmbient F.compAmbient_range

/-- **The composition morphism `c'` of the finite part.** On sections it sends a composable
pair `((u₁, Z₁, z₁), (u₂, Z₂, z₂))`, so one with `(u₁, Z₁) = (t ∘ z₂, c(Z₂, i ∘ z₂))`, to the
triple `(u₂, Z₂, c(z₁, z₂))`. -/
public def comp (F : FinitePartUniversalOpen G) :
    AlgebraicGeometry.AlgebraicSpaces.fiberProduct C S hS F.source F.target ⟶ F.arrows :=
  ObjectProperty.homMk F.compArrows

/-- The underlying morphism of presheaves of the composition, read in the ambient fibre product,
is the section it was built from. -/
public theorem comp_hom_comp_arrowsInclusion (F : FinitePartUniversalOpen G) :
    F.comp.hom ≫ F.arrowsInclusion = F.compAmbient :=
  Subfunctor.lift_ι F.compAmbient F.compAmbient_range

/-- The source of a composite is the source of its second entry. -/
public theorem comp_hom_comp_source (F : FinitePartUniversalOpen G) :
    F.comp.hom ≫ F.source.hom = F.compSnd ≫ F.source.hom :=
  calc F.comp.hom ≫ F.source.hom
      = F.compAmbient ≫ pullback.fst F.universalOpen.toBase.hom G.source.hom :=
        F.comp_source_hom_eq_of_comp_arrowsInclusion _ _ F.comp_hom_comp_arrowsInclusion
    _ = F.compTwistedSection ≫ F.untwistAmbient ≫ F.baseChangeAmbient ≫
          pullback.fst F.universalOpen.toBase.hom G.source.hom := by
            simp only [compAmbient, Category.assoc]
    _ = F.compTwistedSection ≫ F.untwistAmbient ≫
          pullback.fst (F.source ≫ F.universalOpen.toBase).hom G.source.hom ≫
            F.source.hom := by rw [F.baseChangeAmbient_fst]
    _ = F.compTwistedSection ≫ (F.untwistAmbient ≫
          pullback.fst (F.source ≫ F.universalOpen.toBase).hom G.source.hom) ≫
            F.source.hom := by simp only [Category.assoc]
    _ = F.compTwistedSection ≫ pullback.fst F.targetPair.toBase.hom G.source.hom ≫
          F.source.hom := by rw [F.untwistAmbient_fst]
    _ = (F.compTwistedSection ≫ pullback.fst F.targetPair.toBase.hom G.source.hom) ≫
          F.source.hom := (Category.assoc _ _ _).symm
    _ = F.compSnd ≫ F.source.hom := by rw [F.compTwistedSection_fst]

/-- The two arrows of a composable pair of the finite part are composable in the given
groupoid. -/
public theorem comp_composable_app (F : FinitePartUniversalOpen G)
    (V : (AlgebraicGeometry.BigFppfOver C S hS)ᵒᵖ)
    (p : (AlgebraicGeometry.AlgebraicSpaces.fiberProduct C S hS F.source F.target).obj.obj V) :
    G.source.hom.app V (F.arrowMap.hom.app V (F.compFst.app V p)) =
      G.target.hom.app V (F.arrowMap.hom.app V (F.compSnd.app V p)) := by
  have hs : ∀ y : F.arrows.obj.obj V,
      G.source.hom.app V (F.arrowMap.hom.app V y) =
        F.objectProjection.hom.app V (F.source.hom.app V y) := fun y =>
    congrArg (fun k : F.arrows ⟶ G.objects => k.hom.app V y) F.arrowMap_comp_source
  have ht : ∀ y : F.arrows.obj.obj V,
      G.target.hom.app V (F.arrowMap.hom.app V y) =
        F.objectProjection.hom.app V (F.target.hom.app V y) := fun y =>
    congrArg (fun k : F.arrows ⟶ G.objects => k.hom.app V y) F.arrowMap_comp_target
  rw [hs, ht]
  exact congrArg (fun k => F.objectProjection.hom.app V (k.app V p)) F.comp_condition

/-- **The arrow of a composite is the composite of the arrows.** This is the compatibility of
the composition of the finite part with the composition of the given groupoid, which is the
condition on arrows of the canonical morphism of groupoids. -/
public theorem comp_arrowMap_app (F : FinitePartUniversalOpen G)
    (V : (AlgebraicGeometry.BigFppfOver C S hS)ᵒᵖ)
    (p : (AlgebraicGeometry.AlgebraicSpaces.fiberProduct C S hS F.source F.target).obj.obj V) :
    F.arrowMap.hom.app V (F.comp.hom.app V p) =
      G.toGroupoidInFunctors.compose V
        (F.arrowMap.hom.app V (F.compFst.app V p))
        (F.arrowMap.hom.app V (F.compSnd.app V p)) (F.comp_composable_app V p) := by
  set w := (untwistPair G F.arrowMap F.targetPair.toBase F.targetPair_toBase.symm).app V
    (F.compTwistedSection.app V p) with hw
  have hamb : F.arrowMap.hom.app V (F.comp.hom.app V p) = G.comp.hom.app V w := by
    have h₁ : F.arrowMap.hom.app V (F.comp.hom.app V p) =
        (pullback.snd F.universalOpen.toBase.hom G.source.hom).app V
          (F.arrowsInclusion.app V (F.comp.hom.app V p)) :=
      congrArg (fun k => k.app V (F.comp.hom.app V p)) F.arrowMap_hom_eq
    have h₂ : F.arrowsInclusion.app V (F.comp.hom.app V p) = F.compAmbient.app V p :=
      congrArg (fun k => k.app V p) F.comp_hom_comp_arrowsInclusion
    have h₃ : (pullback.snd F.universalOpen.toBase.hom G.source.hom).app V
        (F.compAmbient.app V p) = G.comp.hom.app V w := by
      have e₁ : (pullback.snd F.universalOpen.toBase.hom G.source.hom).app V
          (F.compAmbient.app V p) =
          (pullback.snd (F.source ≫ F.universalOpen.toBase).hom G.source.hom).app V
            (F.untwistAmbient.app V (F.compTwistedSection.app V p)) :=
        congrArg (fun k => k.app V p)
          (show F.compAmbient ≫ pullback.snd F.universalOpen.toBase.hom G.source.hom =
              F.compTwistedSection ≫ F.untwistAmbient ≫
                pullback.snd (F.source ≫ F.universalOpen.toBase).hom G.source.hom by
            simp only [compAmbient, Category.assoc, F.baseChangeAmbient_snd])
      have e₂ : (pullback.snd (F.source ≫ F.universalOpen.toBase).hom G.source.hom).app V
          (F.untwistAmbient.app V (F.compTwistedSection.app V p)) = G.comp.hom.app V w :=
        congrArg (fun k => k.app V (F.compTwistedSection.app V p)) F.untwistAmbient_snd
      exact e₁.trans e₂
    rw [h₁, h₂, h₃]
  have hfst : (pullback.fst G.source.hom G.target.hom).app V w =
      F.arrowMap.hom.app V (F.compFst.app V p) := by
    have e₁ : (pullback.fst G.source.hom G.target.hom).app V w =
        (pullback.snd F.targetPair.toBase.hom G.source.hom).app V
          (F.compTwistedSection.app V p) :=
      congrArg (fun k => k.app V (F.compTwistedSection.app V p))
        (untwistPair_fst G F.arrowMap F.targetPair.toBase F.targetPair_toBase.symm)
    exact e₁.trans (congrArg (fun k => k.app V p) F.compTwistedSection_snd)
  have hsnd : (pullback.snd G.source.hom G.target.hom).app V w =
      F.arrowMap.hom.app V (F.compSnd.app V p) := by
    have e₁ : (pullback.snd G.source.hom G.target.hom).app V w =
        F.arrowMap.hom.app V ((pullback.fst F.targetPair.toBase.hom G.source.hom).app V
          (F.compTwistedSection.app V p)) :=
      congrArg (fun k => k.app V (F.compTwistedSection.app V p))
        (untwistPair_snd G F.arrowMap F.targetPair.toBase F.targetPair_toBase.symm)
    exact e₁.trans (congrArg (fun z => F.arrowMap.hom.app V z)
      (congrArg (fun k => k.app V p) F.compTwistedSection_fst))
  have hcond := pullback_condition_app G.source.hom G.target.hom V w
  rw [hamb, comp_hom_app G V w hcond]
  exact compose_congr G V _ _ _ _ hcond (F.comp_composable_app V p) hfst hsnd

/-- The composition of the finite part is a morphism over the base `B`, computed along the
first projection, in the form the groupoid axiom asks for. -/
public theorem comp_over (F : FinitePartUniversalOpen G) :
    F.comp ≫ F.arrowsToBase =
      (ObjectProperty.homMk F.compFst :
        AlgebraicGeometry.AlgebraicSpaces.fiberProduct C S hS F.source F.target ⟶ F.arrows) ≫
        F.arrowsToBase := by
  apply ObjectProperty.hom_ext
  have h : F.comp.hom ≫ F.arrowMap.hom ≫ G.arrowsToBase.hom =
      F.compFst ≫ F.arrowMap.hom ≫ G.arrowsToBase.hom := by
    ext V p
    change G.arrowsToBase.hom.app V (F.arrowMap.hom.app V (F.comp.hom.app V p)) =
      G.arrowsToBase.hom.app V (F.arrowMap.hom.app V (F.compFst.app V p))
    rw [F.comp_arrowMap_app V p]
    exact arrowsToBase_compose_app G V _ _ (F.comp_composable_app V p)
  exact h

/-! ### The unit of the finite part -/

/-- The unit section of the ambient fibre product of the universal pair: on sections it sends a
pair `(u, Z)` to `((u, Z), e(u))`. -/
public def unitAmbient (F : FinitePartUniversalOpen G) :
    F.objects.obj ⟶ pullback F.universalOpen.toBase.hom G.source.hom :=
  pullback.lift (𝟙 F.objects.obj) (F.universalOpen.toBase.hom ≫ F.unit.hom) (by
    simp only [Category.id_comp, Category.assoc, F.unit_source, Category.comp_id])

/-- The base component of the unit section is the identity. -/
public theorem unitAmbient_fst (F : FinitePartUniversalOpen G) :
    F.unitAmbient ≫ pullback.fst F.universalOpen.toBase.hom G.source.hom =
      𝟙 F.objects.obj :=
  pullback.lift_fst _ _ _

/-- The arrow component of the unit section is the unit of the given groupoid. -/
public theorem unitAmbient_snd (F : FinitePartUniversalOpen G) :
    F.unitAmbient ≫ pullback.snd F.universalOpen.toBase.hom G.source.hom =
      F.universalOpen.toBase.hom ≫ F.unit.hom :=
  pullback.lift_snd _ _ _

/-- The unit section factors through the universal open subspace, which is the statement that
the universal pair contains the unit, read as a condition on the range of that section. -/
public theorem unitAmbient_range (F : FinitePartUniversalOpen G) :
    Subfunctor.range F.unitAmbient ≤ F.universalOpen.subspace := by
  obtain ⟨σ, hσ⟩ := F.universalOpen_containsUnit
  intro V z hz
  obtain ⟨z, rfl⟩ := hz
  have hvalue : F.unitAmbient.app V z = F.universalOpen.subspace.ι.app V (σ.app V z) :=
    (congrArg (fun k => k.app V z) hσ).symm
  rw [hvalue]
  exact (σ.app V z).property

/-- The unit of the finite part as a morphism into the universal open subspace. -/
public def unitArrows (F : FinitePartUniversalOpen G) :
    F.objects.obj ⟶ F.universalOpen.subspace.toFunctor :=
  Subfunctor.lift F.unitAmbient F.unitAmbient_range

/-- **The unit morphism `e'` of the finite part.** On sections it sends a pair `(u, Z)` to the
triple `(u, Z, e(u))`, which is a section of `Z_univ` because the universal pair contains the
unit. -/
public def unitMap (F : FinitePartUniversalOpen G) : F.objects ⟶ F.arrows :=
  ObjectProperty.homMk F.unitArrows

/-- The underlying morphism of presheaves of the unit, read in the ambient fibre product, is the
unit section it was built from. -/
public theorem unitMap_hom_comp_arrowsInclusion (F : FinitePartUniversalOpen G) :
    F.unitMap.hom ≫ F.arrowsInclusion = F.unitAmbient :=
  Subfunctor.lift_ι F.unitAmbient F.unitAmbient_range

/-- The unit of the finite part is a section of its source morphism. -/
public theorem unitMap_comp_source (F : FinitePartUniversalOpen G) :
    F.unitMap ≫ F.source = 𝟙 F.objects := by
  apply ObjectProperty.hom_ext
  exact (F.comp_source_hom_eq_of_comp_arrowsInclusion _ _
    F.unitMap_hom_comp_arrowsInclusion).trans F.unitAmbient_fst

/-- The arrow of the unit of the finite part is the unit of the given groupoid. -/
public theorem unitMap_comp_arrowMap (F : FinitePartUniversalOpen G) :
    F.unitMap ≫ F.arrowMap = F.universalOpen.toBase ≫ F.unit := by
  apply ObjectProperty.hom_ext
  exact (F.comp_arrowMap_hom_eq_of_comp_arrowsInclusion _ _
    F.unitMap_hom_comp_arrowsInclusion).trans F.unitAmbient_snd

/-- The unit morphism of the finite part is a morphism over the base `B`. -/
public theorem unitMap_over (F : FinitePartUniversalOpen G) :
    F.unitMap ≫ F.arrowsToBase = F.objectsToBase := by
  have hunit : F.unit ≫ G.source = 𝟙 G.objects := by
    apply ObjectProperty.hom_ext
    exact F.unit_source
  have hu : F.unit ≫ G.arrowsToBase = G.objectsToBase := by
    rw [show G.arrowsToBase = G.source ≫ G.objectsToBase from G.source_over.symm,
      ← Category.assoc, hunit, Category.id_comp]
  rw [arrowsToBase, ← Category.assoc, F.unitMap_comp_arrowMap, Category.assoc, hu,
    objectsToBase, show F.universalOpen.toBase = F.objectProjection from F.universalOpen_base]

/-! ### The inverse of the finite part -/

/-- The section `y ↦ (y, i(z))` of the ambient fibre product of the twisted pair over `Z_univ`:
the base component is the given section and the arrow component is the inverse of its arrow. -/
public def inverseSection (F : FinitePartUniversalOpen G) :
    F.arrows.obj ⟶ pullback F.targetPair.toBase.hom G.source.hom :=
  pullback.lift (𝟙 F.arrows.obj) (F.arrowMap.hom ≫ inverseHom G) (by
    have h₀ : F.targetPair.toBase.hom = F.arrowMap.hom ≫ G.target.hom :=
      congrArg (fun k : F.arrows ⟶ G.objects => k.hom) F.targetPair_toBase
    rw [Category.id_comp, h₀, Category.assoc, inverseHom_comp_source])

/-- The base component of that section is the identity. -/
public theorem inverseSection_fst (F : FinitePartUniversalOpen G) :
    F.inverseSection ≫ pullback.fst F.targetPair.toBase.hom G.source.hom =
      𝟙 F.arrows.obj :=
  pullback.lift_fst _ _ _

/-- The arrow component of that section is the inverse of the tautological arrow. -/
public theorem inverseSection_snd (F : FinitePartUniversalOpen G) :
    F.inverseSection ≫ pullback.snd F.targetPair.toBase.hom G.source.hom =
      F.arrowMap.hom ≫ inverseHom G :=
  pullback.lift_snd _ _ _

/-- The unit section of the ambient fibre product of the pair obtained from the universal pair
by base change along the source: on sections it sends a triple `(u, Z, z)` to
`((u, Z, z), e(u))`. -/
public def sourceUnitSection (F : FinitePartUniversalOpen G) :
    F.arrows.obj ⟶ pullback (F.source ≫ F.universalOpen.toBase).hom G.source.hom :=
  pullback.lift (𝟙 F.arrows.obj)
    ((F.source ≫ F.universalOpen.toBase).hom ≫ F.unit.hom) (by
      simp only [Category.id_comp, Category.assoc, F.unit_source, Category.comp_id])

/-- The base component of the unit section of the base-changed pair is the identity. -/
public theorem sourceUnitSection_fst (F : FinitePartUniversalOpen G) :
    F.sourceUnitSection ≫
        pullback.fst (F.source ≫ F.universalOpen.toBase).hom G.source.hom =
      𝟙 F.arrows.obj :=
  pullback.lift_fst _ _ _

/-- The arrow component of the unit section of the base-changed pair is the unit. -/
public theorem sourceUnitSection_snd (F : FinitePartUniversalOpen G) :
    F.sourceUnitSection ≫
        pullback.snd (F.source ≫ F.universalOpen.toBase).hom G.source.hom =
      (F.source ≫ F.universalOpen.toBase).hom ≫ F.unit.hom :=
  pullback.lift_snd _ _ _

/-- Reading the unit section of the base-changed pair in the ambient fibre product of the
universal pair gives the unit section there, read along the source. -/
public theorem sourceUnitSection_comp_baseChangeAmbient (F : FinitePartUniversalOpen G) :
    F.sourceUnitSection ≫ F.baseChangeAmbient = F.source.hom ≫ F.unitAmbient := by
  apply pullback.hom_ext
  · simp only [Category.assoc, F.baseChangeAmbient_fst, reassoc_of% F.sourceUnitSection_fst,
      F.unitAmbient_fst, Category.comp_id]
  · simp only [Category.assoc, F.baseChangeAmbient_snd, F.sourceUnitSection_snd,
      F.unitAmbient_snd]
    rw [ObjectProperty.FullSubcategory.comp_hom, Category.assoc]

/-- **The cancellation `c(i(z), z) = e(u)`** on the sections of the arrow space of the finite
part: composing the inverse of the tautological arrow with the tautological arrow returns the
unit at the object part of a triple. -/
public theorem inverseSection_comp_untwistPair_comp (F : FinitePartUniversalOpen G) :
    F.inverseSection ≫
        untwistPair G F.arrowMap F.targetPair.toBase F.targetPair_toBase.symm ≫ G.comp.hom =
      (F.source ≫ F.universalOpen.toBase).hom ≫ F.unit.hom := by
  ext V y
  have hfst : (pullback.fst F.targetPair.toBase.hom G.source.hom).app V
      (F.inverseSection.app V y) = y :=
    congrArg (fun k => k.app V y) F.inverseSection_fst
  have hsnd : (pullback.snd F.targetPair.toBase.hom G.source.hom).app V
      (F.inverseSection.app V y) =
      Deformation.inverseArrow G.toGroupoidInFunctors V (F.arrowMap.hom.app V y) :=
    (congrArg (fun k => k.app V y) F.inverseSection_snd).trans (inverseHom_app G V _)
  have hfstP : (pullback.fst G.source.hom G.target.hom).app V
      ((untwistPair G F.arrowMap F.targetPair.toBase F.targetPair_toBase.symm).app V
        (F.inverseSection.app V y)) =
      Deformation.inverseArrow G.toGroupoidInFunctors V (F.arrowMap.hom.app V y) :=
    (congrArg (fun k => k.app V (F.inverseSection.app V y))
      (untwistPair_fst G F.arrowMap F.targetPair.toBase F.targetPair_toBase.symm)).trans hsnd
  have hsndP : (pullback.snd G.source.hom G.target.hom).app V
      ((untwistPair G F.arrowMap F.targetPair.toBase F.targetPair_toBase.symm).app V
        (F.inverseSection.app V y)) = F.arrowMap.hom.app V y :=
    (congrArg (fun k => k.app V (F.inverseSection.app V y))
      (untwistPair_snd G F.arrowMap F.targetPair.toBase F.targetPair_toBase.symm)).trans
      (congrArg (fun z => F.arrowMap.hom.app V z) hfst)
  have hcond := pullback_condition_app G.source.hom G.target.hom V
    ((untwistPair G F.arrowMap F.targetPair.toBase F.targetPair_toBase.symm).app V
      (F.inverseSection.app V y))
  have hinv : G.source.hom.app V
      (Deformation.inverseArrow G.toGroupoidInFunctors V (F.arrowMap.hom.app V y)) =
      G.target.hom.app V (F.arrowMap.hom.app V y) := by
    rw [← hfstP, ← hsndP]
    exact hcond
  have hbase : (F.source ≫ F.universalOpen.toBase).hom.app V y =
      G.source.hom.app V (F.arrowMap.hom.app V y) :=
    (congrArg (fun k : F.arrows ⟶ G.objects => k.hom.app V y) F.arrowMap_comp_source').symm
  change G.comp.hom.app V
      ((untwistPair G F.arrowMap F.targetPair.toBase F.targetPair_toBase.symm).app V
        (F.inverseSection.app V y)) =
    F.unit.hom.app V ((F.source ≫ F.universalOpen.toBase).hom.app V y)
  rw [comp_hom_app G V _ hcond, compose_congr G V _ _ _ _ hcond hinv hfstP hsndP,
    compose_inverseArrow_app G V (F.arrowMap.hom.app V y) hinv, F.unit_identity, hbase]

/-- Untwisting the inverse section gives the unit section of the base-changed pair: on sections
this is the cancellation `c(i(z), z) = e(u)`. -/
public theorem inverseSection_comp_untwistAmbient (F : FinitePartUniversalOpen G) :
    F.inverseSection ≫ F.untwistAmbient = F.sourceUnitSection := by
  apply pullback.hom_ext
  · calc (F.inverseSection ≫ F.untwistAmbient) ≫
            pullback.fst (F.source ≫ F.universalOpen.toBase).hom G.source.hom
        = F.inverseSection ≫ F.untwistAmbient ≫
            pullback.fst (F.source ≫ F.universalOpen.toBase).hom G.source.hom :=
              Category.assoc _ _ _
      _ = F.inverseSection ≫ pullback.fst F.targetPair.toBase.hom G.source.hom :=
            congrArg (fun z => F.inverseSection ≫ z) F.untwistAmbient_fst
      _ = 𝟙 F.arrows.obj := F.inverseSection_fst
      _ = F.sourceUnitSection ≫
            pullback.fst (F.source ≫ F.universalOpen.toBase).hom G.source.hom :=
              F.sourceUnitSection_fst.symm
  · calc (F.inverseSection ≫ F.untwistAmbient) ≫
            pullback.snd (F.source ≫ F.universalOpen.toBase).hom G.source.hom
        = F.inverseSection ≫ F.untwistAmbient ≫
            pullback.snd (F.source ≫ F.universalOpen.toBase).hom G.source.hom :=
              Category.assoc _ _ _
      _ = F.inverseSection ≫
            untwistPair G F.arrowMap F.targetPair.toBase F.targetPair_toBase.symm ≫
              G.comp.hom :=
            congrArg (fun z => F.inverseSection ≫ z) F.untwistAmbient_snd
      _ = (F.source ≫ F.universalOpen.toBase).hom ≫ F.unit.hom :=
            F.inverseSection_comp_untwistPair_comp
      _ = F.sourceUnitSection ≫
            pullback.snd (F.source ≫ F.universalOpen.toBase).hom G.source.hom :=
              F.sourceUnitSection_snd.symm

/-- The inverse section is a section of the open subspace of the twisted pair. -/
public theorem inverseSection_range (F : FinitePartUniversalOpen G) :
    Subfunctor.range F.inverseSection ≤ F.targetPair.subspace := by
  rw [F.targetPair_subspace_preimage, ← Subfunctor.image_le_iff, ← Subfunctor.range_comp,
    ← Category.assoc, F.inverseSection_comp_untwistAmbient,
    F.sourceUnitSection_comp_baseChangeAmbient]
  exact (Subfunctor.range_comp_le _ _).trans F.unitAmbient_range

/-- The inverse section read at the target lands in the universal open subspace. -/
public theorem inverseSection_comp_targetAmbientLift_range (F : FinitePartUniversalOpen G) :
    Subfunctor.range (F.inverseSection ≫ F.targetAmbientLift) ≤
      F.universalOpen.subspace := by
  rw [Subfunctor.range_comp, Subfunctor.image_le_iff, ← F.targetPair_subspace_eq]
  exact F.inverseSection_range

/-- The inverse of the finite part as a morphism into the universal open subspace. -/
public def inverseArrows (F : FinitePartUniversalOpen G) :
    F.arrows.obj ⟶ F.universalOpen.subspace.toFunctor :=
  Subfunctor.lift (F.inverseSection ≫ F.targetAmbientLift)
    F.inverseSection_comp_targetAmbientLift_range

/-- **The inverse morphism `i'` of the finite part.** On sections it sends a triple
`(u, Z, z)` to the triple `(t ∘ z, c(Z, i ∘ z), i(z))`. -/
public def inverseMap (F : FinitePartUniversalOpen G) : F.arrows ⟶ F.arrows :=
  ObjectProperty.homMk F.inverseArrows

/-- The underlying morphism of presheaves of the inverse, read in the ambient fibre product, is
the inverse section read at the target. -/
public theorem inverseMap_hom_comp_arrowsInclusion (F : FinitePartUniversalOpen G) :
    F.inverseMap.hom ≫ F.arrowsInclusion = F.inverseSection ≫ F.targetAmbientLift :=
  Subfunctor.lift_ι (F.inverseSection ≫ F.targetAmbientLift)
    F.inverseSection_comp_targetAmbientLift_range

/-- The inverse of the finite part carries the source to the target. -/
public theorem inverseMap_comp_source (F : FinitePartUniversalOpen G) :
    F.inverseMap ≫ F.source = F.target := by
  apply ObjectProperty.hom_ext
  exact ((F.comp_source_hom_eq_of_comp_arrowsInclusion _ _
    F.inverseMap_hom_comp_arrowsInclusion).trans (F.comp_targetAmbientLift_fst _)).trans
    (by rw [F.inverseSection_fst, Category.id_comp])

/-- The arrow of the inverse of the finite part is the inverse of the given groupoid. -/
public theorem inverseMap_comp_arrowMap (F : FinitePartUniversalOpen G) :
    F.inverseMap.hom ≫ F.arrowMap.hom = F.arrowMap.hom ≫ inverseHom G :=
  ((F.comp_arrowMap_hom_eq_of_comp_arrowsInclusion _ _
    F.inverseMap_hom_comp_arrowsInclusion).trans (F.comp_targetAmbientLift_snd _)).trans
    F.inverseSection_snd

/-- The inverse morphism of the finite part is a morphism over the base `B`. -/
public theorem inverseMap_over (F : FinitePartUniversalOpen G) :
    F.inverseMap ≫ F.arrowsToBase = F.arrowsToBase := by
  apply ObjectProperty.hom_ext
  have hsrc : G.source.hom ≫ G.objectsToBase.hom = G.arrowsToBase.hom :=
    congrArg (fun k : G.arrows ⟶ B => k.hom) G.source_over
  have htgt : G.target.hom ≫ G.objectsToBase.hom = G.arrowsToBase.hom :=
    congrArg (fun k : G.arrows ⟶ B => k.hom) G.target_over
  have hG : inverseHom G ≫ G.arrowsToBase.hom = G.arrowsToBase.hom := by
    rw [← htgt, ← Category.assoc, inverseHom_comp_target, htgt, hsrc]
  change F.inverseMap.hom ≫ F.arrowMap.hom ≫ G.arrowsToBase.hom =
    F.arrowMap.hom ≫ G.arrowsToBase.hom
  rw [← Category.assoc, F.inverseMap_comp_arrowMap, Category.assoc, hG]

end FinitePartUniversalOpen

end AlgebraicGeometry.Space

end
