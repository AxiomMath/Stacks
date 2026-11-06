module

public import StacksFrontier.AlgebraicGeometry.Spaces.AffineHomTfae
public import StacksFrontier.AlgebraicGeometry.Spaces.Pushouts.FormalGlueingSpacesDescent
public import StacksFrontier.AlgebraicGeometry.Spaces.Pushouts.FormalGlueingSpacesFaithful

/-!
# Stacks 0AF4: its three clauses, and clauses (2) and (3) reduced to clause (1)

In a formal glueing situation `(f : Y ⟶ X, Z, U = X \ Z, V = Y \ f⁻¹(Z))`, Stacks 0AF4 asserts
that the restriction functor of Stacks 0AF3 cuts down to an equivalence of categories in three
cases: between algebraic spaces affine over `X` and glueing triples
`(U' ⟵ V' ⟶ Y')` whose three maps `U' ⟶ U`, `V' ⟶ V` and `Y' ⟶ Y` are affine; the same with
"closed immersion" in place of "affine"; and the same with "finite".

This module writes down the six full subcategories those three clauses name, restricts the
functor of Stacks 0AF3 to each of the three pairs, and carries out the source's own reduction of
clauses (2) and (3) to clause (1). What is left is clause (1) alone: granted it, clauses (2) and
(3) are proved here unconditionally.

## Main definitions

* `AlgebraicGeometry.Space.FormalGlueingSituation.affineOverX`,
  `AlgebraicGeometry.Space.FormalGlueingSituation.closedOverX` and
  `AlgebraicGeometry.Space.FormalGlueingSituation.finiteOverX`: the three conditions on a space
  over `X` naming the source categories of the three clauses of Stacks 0AF4.
* `AlgebraicGeometry.Space.FormalGlueingSituation.affineLegs`,
  `AlgebraicGeometry.Space.FormalGlueingSituation.closedLegs` and
  `AlgebraicGeometry.Space.FormalGlueingSituation.finiteLegs`: the three conditions on a
  glueing triple naming the target categories, each asking the condition of all three of
  `U' ⟶ U`, `V' ⟶ V` and `Y' ⟶ Y` exactly as the source states it.
* `AlgebraicGeometry.Space.FormalGlueingSituation.affineGlueingFunctor`,
  `AlgebraicGeometry.Space.FormalGlueingSituation.closedGlueingFunctor` and
  `AlgebraicGeometry.Space.FormalGlueingSituation.finiteGlueingFunctor`: the restrictions of the
  functor of Stacks 0AF3 to the three pairs — the "restricts to" of Stacks 0AF4.
* `AlgebraicGeometry.Space.FormalGlueingSituation.AffineEquivalence`: **clause (1) of
  Stacks 0AF4 as a named statement**, that the first of those three restrictions is an
  equivalence. It is the one assertion of the tag this library does not prove, and it is the
  hypothesis of the two reduction theorems below.

## Main results

* `AlgebraicGeometry.Space.FormalGlueingSituation.affineLegs_obj`,
  `AlgebraicGeometry.Space.FormalGlueingSituation.closedLegs_obj` and
  `AlgebraicGeometry.Space.FormalGlueingSituation.finiteLegs_obj`: the functor of Stacks 0AF3
  does land in the three subcategories, which is what makes the restrictions exist.
* `AlgebraicGeometry.Space.FormalGlueingSituation.faithful_affineGlueingFunctor`,
  `AlgebraicGeometry.Space.FormalGlueingSituation.faithful_closedGlueingFunctor` and
  `AlgebraicGeometry.Space.FormalGlueingSituation.faithful_finiteGlueingFunctor`: all three
  restrictions are faithful, with no hypothesis beyond the situation.
* `AlgebraicGeometry.Space.FormalGlueingSituation.closedOverX_le_affineOverX`,
  `AlgebraicGeometry.Space.FormalGlueingSituation.finiteOverX_le_affineOverX`,
  `AlgebraicGeometry.Space.FormalGlueingSituation.closedLegs_le_affineLegs` and
  `AlgebraicGeometry.Space.FormalGlueingSituation.finiteLegs_le_affineLegs`: the four categories
  of clauses (2) and (3) are subcategories of the two of clause (1), because a closed immersion
  and a finite morphism of algebraic spaces are affine.
* `AlgebraicGeometry.Space.FormalGlueingSituation.closedOverX_of_legs` and
  `AlgebraicGeometry.Space.FormalGlueingSituation.finiteOverX_of_legs`: the reverse direction of
  the source's criterion, read at a glueing triple — a space over `X` whose two legs are closed
  immersions, resp. finite, is a closed subspace of `X`, resp. finite over `X`.
* `AlgebraicGeometry.Space.FormalGlueingSituation.isEquivalence_closedGlueingFunctor` and
  `AlgebraicGeometry.Space.FormalGlueingSituation.isEquivalence_finiteGlueingFunctor`:
  **clauses (2) and (3) of Stacks 0AF4 from clause (1)**, with nothing else assumed. Their
  fullness and essential-surjectivity halves are
  `full_closedGlueingFunctor`, `full_finiteGlueingFunctor`,
  `essSurj_closedGlueingFunctor` and `essSurj_finiteGlueingFunctor` in the same namespace.

## Implementation notes

The two reduction theorems take `AffineEquivalence D` — clause (1) of the tag — as a hypothesis,
so they are not registered themselves. Stacks 0AF4 is registered, with clause (1) proved, on
`AlgebraicGeometry.Space.FormalGlueingSituation.affineGlueingFunctor_isEquivalence`,
`closedGlueingFunctor_isEquivalence` and `finiteGlueingFunctor_isEquivalence`
(`StacksFrontier.AlgebraicGeometry.Spaces.Pushouts.FormalGlueingSpacesRestrictedEquivalences`).

**What clause (1) still needs.** By the source's proof, clause (1) is Stacks 0AF0 — that the
functor of Stacks 0AEW is an equivalence `QCoh(𝒪_X) ≃ QCoh(Y → X, Z)` — transported along the
anti-equivalence of Stacks 081V between the algebraic spaces affine over `X` and the
quasi-coherent `𝒪_X`-algebras, whose inverse is the relative spectrum of Stacks 081W. Both
inputs are absent, in different ways:

* Stacks 0AF0 is nowhere stated. The adjunction it would upgrade is available, as
  `AlgebraicGeometry.Space.FormalGlueingSituation.glueingAdjunction` (Stacks 0AEY) in
  `StacksFrontier.AlgebraicGeometry.Spaces.Pushouts.FormalGlueingModulesUnconditional`, and 0AF0 is
  exactly the assertion that its unit and counit are invertible. The finite presentation of `Z`
  and the flatness of `f` along `f⁻¹(Z)` — the two hypotheses of Stacks 0AEV the adjunction does
  not use — are needed only for this.
* Stacks 081V is available only as the structure
  `AlgebraicGeometry.Space.AffineAlgebraAntiEquivalence` together with
  `AlgebraicGeometry.Space.BaseChangeCompatibility`, and neither has an inhabitant. Its two
  reduction files leave four assertions open: that
  `AlgebraicGeometry.Space.affineQuasicoherentPushforwardAlgebraFunctor` is an equivalence, and
  the three fields `algebraPullback_isQuasicoherent`, `baseChangeIso` and
  `baseChangeIso_canonical`.

Only clause (1) consumes Stacks 081V. Clauses (2) and (3) consume clause (1) and the two
fpqc-descent criteria, and nothing else — which is what the two reduction theorems below
establish.

The middle condition of each triple — on `V' ⟶ V` — is implied by the condition on `U' ⟶ U`,
since `V'` is by definition the base change of `U'` along `V ⟶ U` and all three properties are
stable under base change. It is nevertheless carried as a separate conjunct, because Stacks
0AF4 states it, and a subcategory cut out by two of the three conditions would be a different
subcategory from the one the tag names even though it has the same objects.

Each of the three `*_obj` lemmas is three applications of stability under base change, one per
leg, the middle leg being a base change of the left one. The three properties reach that
stability by three different routes: affineness by
`AlgebraicGeometry.Space.isAffineHom_of_isPullback`, finiteness by
`AlgebraicGeometry.Space.isFinite_of_isPullback`, and being a closed immersion through
`CategoryTheory.MorphismProperty.relative_isStableUnderBaseChange`, since
`AlgebraicGeometry.Space.IsClosedImmersion` is by definition a `MorphismProperty.presheaf` and
that is where its base-change stability lives; the packaged
`AlgebraicGeometry.Space.isClosedImmersion_of_isPullback` is stated for the category of
algebraic spaces over `S` rather than for morphisms of presheaves, which is the shape the legs
of a glueing triple have.

Faithfulness is inherited: `CategoryTheory.ObjectProperty.lift` of a faithful functor is
faithful, and the functor being lifted is the inclusion of a full subcategory followed by the
functor of Stacks 0AF3, which is faithful by
`AlgebraicGeometry.Space.FormalGlueingSituation.faithful_formalGlueingFunctor`.

## References

* [Stacks Project, Tag 02YU](https://stacks.math.columbia.edu/tag/02YU)
* [Stacks Project, Tag 03WF](https://stacks.math.columbia.edu/tag/03WF)
* [Stacks Project, Tag 03ZS](https://stacks.math.columbia.edu/tag/03ZS)
* [Stacks Project, Tag 0420](https://stacks.math.columbia.edu/tag/0420)
* [Stacks Project, Tag 0426](https://stacks.math.columbia.edu/tag/0426)
* [Stacks Project, Tag 081V](https://stacks.math.columbia.edu/tag/081V)
* [Stacks Project, Tag 081W](https://stacks.math.columbia.edu/tag/081W)
* [Stacks Project, Tag 0AEY](https://stacks.math.columbia.edu/tag/0AEY)
* [Stacks Project, Tag 0AF0](https://stacks.math.columbia.edu/tag/0AF0)
* [Stacks Project, Tag 0AF1](https://stacks.math.columbia.edu/tag/0AF1)
* [Stacks Project, Tag 0AF3](https://stacks.math.columbia.edu/tag/0AF3)
* [Stacks Project, Tag 0AF4](https://stacks.math.columbia.edu/tag/0AF4)
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits

universe u

namespace AlgebraicGeometry.Space.FormalGlueingSituation

variable {B : BigFppfSite.{u}} {S : Scheme.{u}} {hS : B.Contains S}

set_option synthInstance.maxHeartbeats 400000 in
/-- Pullbacks of presheaves on the big fppf site (instance search times out without this
shortcut). -/
local instance hasPullbacks_presheaf_formalGlueingSpacesEquivalence
    (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S) :
    HasPullbacks ((BigFppfOver B S hS)ᵒᵖ ⥤ Type u) := inferInstance

/-- A pullback of presheaves on the big fppf site, found directly from `HasPullbacks`. -/
local instance (priority := high) hasPullback_presheaf_formalGlueingSpacesEquivalence
    (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)
    {X Y Z : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u} (f : X ⟶ Z) (g : Y ⟶ Z) :
    HasLimit (cospan f g) :=
  HasLimitsOfShape.has_limit _

/-! ### The six subcategories named by the three clauses of Stacks 0AF4 -/

/-- Algebraic spaces over `X` that are affine over `X`: the source category of clause (1) of
**Stacks 0AF4**. -/
abbrev affineOverX (D : FormalGlueingSituation B S hS) : ObjectProperty (spacesOverX D) :=
  fun T ↦ IsAffineHom B S hS T.1.hom

/-- Algebraic spaces over `X` whose structure map is a closed immersion: the source category of
clause (2) of **Stacks 0AF4**. -/
abbrev closedOverX (D : FormalGlueingSituation B S hS) : ObjectProperty (spacesOverX D) :=
  fun T ↦ IsClosedImmersion B S hS T.1.hom

/-- Algebraic spaces finite over `X`: the source category of clause (3) of
**Stacks 0AF4**. -/
abbrev finiteOverX (D : FormalGlueingSituation B S hS) : ObjectProperty (spacesOverX D) :=
  fun T ↦ IsFinite B S hS T.1.hom

/-- Glueing triples `(U' ⟵ V' ⟶ Y')` with `U' ⟶ U`, `V' ⟶ V` and `Y' ⟶ Y` all affine: the
target category of clause (1) of **Stacks 0AF4**. -/
abbrev affineLegs (D : FormalGlueingSituation B S hS) : ObjectProperty (glueingData D) :=
  fun T ↦ IsAffineHom B S hS T.1.left.hom ∧
    IsAffineHom B S hS ((Over.pullback (D.U.fromPreimage D.f)).obj T.1.left).hom ∧
    IsAffineHom B S hS T.1.right.hom

/-- Glueing triples `(U' ⟵ V' ⟶ Y')` with `U' ⟶ U`, `V' ⟶ V` and `Y' ⟶ Y` all closed
immersions: the target category of clause (2) of **Stacks 0AF4**. -/
abbrev closedLegs (D : FormalGlueingSituation B S hS) : ObjectProperty (glueingData D) :=
  fun T ↦ IsClosedImmersion B S hS T.1.left.hom ∧
    IsClosedImmersion B S hS ((Over.pullback (D.U.fromPreimage D.f)).obj T.1.left).hom ∧
    IsClosedImmersion B S hS T.1.right.hom

/-- Glueing triples `(U' ⟵ V' ⟶ Y')` with `U' ⟶ U`, `V' ⟶ V` and `Y' ⟶ Y` all finite: the
target category of clause (3) of **Stacks 0AF4**. -/
abbrev finiteLegs (D : FormalGlueingSituation B S hS) : ObjectProperty (glueingData D) :=
  fun T ↦ IsFinite B S hS T.1.left.hom ∧
    IsFinite B S hS ((Over.pullback (D.U.fromPreimage D.f)).obj T.1.left).hom ∧
    IsFinite B S hS T.1.right.hom

/-! ### Being a closed immersion is stable under base change, for morphisms of presheaves -/

/-- Being a closed immersion of algebraic spaces is stable under base change, read for
morphisms of presheaves on the big fppf site rather than for morphisms of the category of
algebraic spaces over `S`: the legs of a glueing triple have the former shape. -/
theorem isClosedImmersion_presheaf_of_isPullback
    {F G F' G' : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u}
    {f : F ⟶ G} {g : G' ⟶ G} {p : F' ⟶ F} {q : F' ⟶ G'} (h : IsPullback p q f g)
    (hf : IsClosedImmersion B S hS f) : IsClosedImmersion B S hS q :=
  (MorphismProperty.relative_isStableUnderBaseChange (F := yoneda)
    (MorphismProperty.inverseImage
      (@AlgebraicGeometry.IsClosedImmersion.{u} : MorphismProperty Scheme.{u})
      (BigFppfOver.toScheme B S hS))).of_isPullback h hf

/-! ### The functor of Stacks 0AF3 lands in the three subcategories -/

/-- If `P` is stable under base change, all three legs of the glueing triple of a space over `X`
satisfy `P` as soon as its structure map does. -/
private theorem legs_obj_of_isPullback (D : FormalGlueingSituation B S hS) (T : spacesOverX D)
    {P : ∀ {F G : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u}, (F ⟶ G) → Prop}
    (H : ∀ {F G F' G' : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u} {f : F ⟶ G} {g : G' ⟶ G} {p : F' ⟶ F}
      {q : F' ⟶ G'}, IsPullback p q f g → P f → P q) (hT : P T.1.hom) :
    P ((formalGlueingFunctor D).1.obj T).1.left.hom ∧
      P ((Over.pullback (D.U.fromPreimage D.f)).obj ((formalGlueingFunctor D).1.obj T).1.left).hom ∧
      P ((formalGlueingFunctor D).1.obj T).1.right.hom :=
  ⟨H (IsPullback.of_hasPullback _ _) hT,
    H (IsPullback.of_hasPullback _ _) (H (IsPullback.of_hasPullback _ _) hT),
    H (IsPullback.of_hasPullback _ _) hT⟩

/-- A space affine over `X` has a glueing triple whose three maps are affine: each is a base
change of its structure map. -/
theorem affineLegs_obj (D : FormalGlueingSituation B S hS) (T : spacesOverX D)
    (hT : affineOverX D T) : affineLegs D ((formalGlueingFunctor D).1.obj T) :=
  legs_obj_of_isPullback D T isAffineHom_of_isPullback hT

/-- A closed subspace of `X` has a glueing triple whose three maps are closed immersions: each
is a base change of its structure map. -/
theorem closedLegs_obj (D : FormalGlueingSituation B S hS) (T : spacesOverX D)
    (hT : closedOverX D T) : closedLegs D ((formalGlueingFunctor D).1.obj T) :=
  legs_obj_of_isPullback D T isClosedImmersion_presheaf_of_isPullback hT

/-- A space finite over `X` has a glueing triple whose three maps are finite: each is a base
change of its structure map. -/
theorem finiteLegs_obj (D : FormalGlueingSituation B S hS) (T : spacesOverX D)
    (hT : finiteOverX D T) : finiteLegs D ((formalGlueingFunctor D).1.obj T) :=
  legs_obj_of_isPullback D T (isFinite_of_isPullback B S hS) hT

/-! ### The three restrictions of the functor of Stacks 0AF3 -/

/-- The restriction of the functor of Stacks 0AF3 to clause (1) of **Stacks 0AF4**: from
algebraic spaces affine over `X` to glueing triples with affine legs. -/
noncomputable def affineGlueingFunctor (D : FormalGlueingSituation B S hS) :
    (affineOverX D).FullSubcategory ⥤ (affineLegs D).FullSubcategory :=
  (affineLegs D).lift ((affineOverX D).ι ⋙ (formalGlueingFunctor D).1)
    fun T ↦ affineLegs_obj D T.1 T.2

/-- The restriction of the functor of Stacks 0AF3 to clause (2) of **Stacks 0AF4**: from closed
subspaces of `X` to glueing triples whose legs are closed immersions. -/
noncomputable def closedGlueingFunctor (D : FormalGlueingSituation B S hS) :
    (closedOverX D).FullSubcategory ⥤ (closedLegs D).FullSubcategory :=
  (closedLegs D).lift ((closedOverX D).ι ⋙ (formalGlueingFunctor D).1)
    fun T ↦ closedLegs_obj D T.1 T.2

/-- The restriction of the functor of Stacks 0AF3 to clause (3) of **Stacks 0AF4**: from
algebraic spaces finite over `X` to glueing triples with finite legs. -/
noncomputable def finiteGlueingFunctor (D : FormalGlueingSituation B S hS) :
    (finiteOverX D).FullSubcategory ⥤ (finiteLegs D).FullSubcategory :=
  (finiteLegs D).lift ((finiteOverX D).ι ⋙ (formalGlueingFunctor D).1)
    fun T ↦ finiteLegs_obj D T.1 T.2

/-! ### Faithfulness of the three restrictions -/

/-- The restriction of Stacks 0AF3 to spaces affine over `X` is faithful. -/
instance faithful_affineGlueingFunctor (D : FormalGlueingSituation B S hS) :
    (affineGlueingFunctor D).Faithful :=
  inferInstanceAs ((affineLegs D).lift ((affineOverX D).ι ⋙ (formalGlueingFunctor D).1) _).Faithful

/-- The restriction of Stacks 0AF3 to closed subspaces of `X` is faithful. -/
instance faithful_closedGlueingFunctor (D : FormalGlueingSituation B S hS) :
    (closedGlueingFunctor D).Faithful :=
  inferInstanceAs ((closedLegs D).lift ((closedOverX D).ι ⋙ (formalGlueingFunctor D).1) _).Faithful

/-- The restriction of Stacks 0AF3 to spaces finite over `X` is faithful. -/
instance faithful_finiteGlueingFunctor (D : FormalGlueingSituation B S hS) :
    (finiteGlueingFunctor D).Faithful :=
  inferInstanceAs ((finiteLegs D).lift ((finiteOverX D).ι ⋙ (formalGlueingFunctor D).1) _).Faithful

/-! ### Clauses (2) and (3) refine clause (1) -/

/-- A closed immersion of algebraic spaces is affine. This is what makes clause (2) of
**Stacks 0AF4** a statement about a subcategory of the one clause (1) speaks about, which is
how the source's proof reduces the one to the other. -/
theorem isAffineHom_of_isClosedImmersion {F G : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u} {f : F ⟶ G}
    (hf : IsClosedImmersion B S hS f) : IsAffineHom B S hS f :=
  isAffineHom_of_presheaf
    (MorphismProperty.relative_monotone (F := yoneda)
      (fun _ _ p hp ↦ by
        change AlgebraicGeometry.IsClosedImmersion ((BigFppfOver.toScheme B S hS).map p) at hp
        show AlgebraicGeometry.IsAffineHom ((BigFppfOver.toScheme B S hS).map p)
        have := hp
        exact inferInstance) f hf)

/-- A finite morphism of algebraic spaces is affine. This is what makes clause (3) of
**Stacks 0AF4** a statement about a subcategory of the one clause (1) speaks about. -/
theorem isAffineHom_of_isFinite {F G : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u} {f : F ⟶ G}
    (hf : IsFinite B S hS f) : IsAffineHom B S hS f :=
  (isAffineHom_iff_holdsOnAffineBaseChange f).2 fun Z hZ g ↦ by
    obtain ⟨V, p, i, hV, hfin, hpb⟩ := hf Z hZ g
    have := hfin
    exact ⟨V, p, i, hpb, hV, inferInstance⟩

/-- A closed subspace of `X` is affine over `X`: the source category of clause (2) of
**Stacks 0AF4** is a subcategory of the source category of clause (1). -/
theorem closedOverX_le_affineOverX (D : FormalGlueingSituation B S hS) :
    closedOverX D ≤ affineOverX D :=
  fun _ h ↦ isAffineHom_of_isClosedImmersion h

/-- A space finite over `X` is affine over `X`: the source category of clause (3) of
**Stacks 0AF4** is a subcategory of the source category of clause (1). -/
theorem finiteOverX_le_affineOverX (D : FormalGlueingSituation B S hS) :
    finiteOverX D ≤ affineOverX D :=
  fun _ h ↦ isAffineHom_of_isFinite h

/-- A glueing triple whose three legs are closed immersions has affine legs: the target
category of clause (2) of **Stacks 0AF4** is a subcategory of the target category of
clause (1). -/
theorem closedLegs_le_affineLegs (D : FormalGlueingSituation B S hS) :
    closedLegs D ≤ affineLegs D :=
  fun _ h ↦ ⟨isAffineHom_of_isClosedImmersion h.1,
    isAffineHom_of_isClosedImmersion h.2.1, isAffineHom_of_isClosedImmersion h.2.2⟩

/-- A glueing triple whose three legs are finite has affine legs: the target category of
clause (3) of **Stacks 0AF4** is a subcategory of the target category of clause (1). -/
theorem finiteLegs_le_affineLegs (D : FormalGlueingSituation B S hS) :
    finiteLegs D ≤ affineLegs D :=
  fun _ h ↦ ⟨isAffineHom_of_isFinite h.1,
    isAffineHom_of_isFinite h.2.1, isAffineHom_of_isFinite h.2.2⟩

/-! ### Fullness in clauses (2) and (3) follows from fullness in clause (1) -/

/-- If clause (1) is full, so is the restriction of Stacks 0AF3 to any smaller pair of source and
target subcategories. -/
private theorem full_lift_of_le (D : FormalGlueingSituation B S hS)
    {P : ObjectProperty (spacesOverX D)} {Q : ObjectProperty (glueingData D)}
    (hP : P ≤ affineOverX D)
    (hQ : ∀ T : P.FullSubcategory, Q ((formalGlueingFunctor D).1.obj T.obj))
    (h : (affineGlueingFunctor D).Full) : (Q.lift (P.ι ⋙ (formalGlueingFunctor D).1) hQ).Full := by
  constructor
  intro T₁ T₂ φ
  obtain ⟨ψ, hψ⟩ := h.map_surjective
    (X := ⟨T₁.obj, hP _ T₁.property⟩) (Y := ⟨T₂.obj, hP _ T₂.property⟩)
    (ObjectProperty.homMk φ.hom)
  exact ⟨ObjectProperty.homMk ψ.hom,
    ObjectProperty.hom_ext _ (congrArg InducedCategory.Hom.hom hψ :)⟩

/-- **The source's "fully faithfulness in part (2) follows from part (1)", for clause (2).**
A morphism between the glueing triples of two closed subspaces of `X` is a morphism between
their glueing triples read as triples with affine legs, so it comes from a morphism over `X` as
soon as clause (1) of **Stacks 0AF4** is full. -/
theorem full_closedGlueingFunctor (D : FormalGlueingSituation B S hS)
    (h : (affineGlueingFunctor D).Full) : (closedGlueingFunctor D).Full :=
  full_lift_of_le D (closedOverX_le_affineOverX D) _ h

/-- The same for clause (3): a morphism between the glueing triples of two spaces finite over
`X` comes from a morphism over `X` as soon as clause (1) of **Stacks 0AF4** is full. -/
theorem full_finiteGlueingFunctor (D : FormalGlueingSituation B S hS)
    (h : (affineGlueingFunctor D).Full) : (finiteGlueingFunctor D).Full :=
  full_lift_of_le D (finiteOverX_le_affineOverX D) _ h

/-! ### The two conditions as properties of morphisms of presheaves -/

/-- Being a closed immersion, as a property of morphisms of presheaves on the big fppf site of
`S`. The legs of a glueing triple are morphisms of presheaves, so this is the shape in which
the condition of clause (2) of **Stacks 0AF4** has to be transported along an isomorphism. -/
abbrev closedImmersionPresheaf (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S) :
    MorphismProperty ((BigFppfOver B S hS)ᵒᵖ ⥤ Type u) :=
  fun _ _ f ↦ IsClosedImmersion B S hS f

/-- Being finite, as a property of morphisms of presheaves on the big fppf site of `S`. -/
abbrev isFinitePresheaf (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S) :
    MorphismProperty ((BigFppfOver B S hS)ᵒᵖ ⥤ Type u) :=
  fun _ _ f ↦ IsFinite B S hS f

/-- Closed immersions of presheaves on the big fppf site of `S` are stable under base change. -/
instance : (closedImmersionPresheaf B S hS).IsStableUnderBaseChange where
  of_isPullback sq hf := isClosedImmersion_presheaf_of_isPullback sq hf

/-- Finite morphisms of presheaves on the big fppf site of `S` are stable under base change. -/
instance : (isFinitePresheaf B S hS).IsStableUnderBaseChange where
  of_isPullback sq hf := isFinite_of_isPullback B S hS sq hf

/-! ### Reading the restriction criterion at a glueing triple -/

/-- The second projection of a fibre product taken in the category of algebraic spaces over `S`
has a property of morphisms of presheaves exactly when the second projection of the fibre
product of the same cospan taken in presheaves does: the two are isomorphic over the cospan,
that category having its fibre products computed in presheaves. -/
theorem property_pullback_snd_hom_iff
    (P : MorphismProperty ((BigFppfOver B S hS)ᵒᵖ ⥤ Type u)) [P.RespectsIso]
    {X' G W : AlgebraicSpaces B S hS} (a : X' ⟶ W) (b : G ⟶ W) :
    P (pullback.snd a.hom b.hom) ↔ P (pullback.snd a b).hom := by
  have h1 : IsPullback (pullback.fst a.hom b.hom) (pullback.snd a.hom b.hom) a.hom b.hom :=
    IsPullback.of_hasPullback _ _
  have h2 : IsPullback (pullback.fst a b).hom (pullback.snd a b).hom a.hom b.hom :=
    AlgebraicSpaces.isPullback_hom B S hS (IsPullback.of_hasPullback a b)
  rw [← h1.isoIsPullback_hom_snd _ _ h2]
  exact P.cancel_left_of_respectsIso _ _

/-- **The reverse direction of the source's criterion, at a glueing triple.** A space over `X`
whose two restrictions — the two legs of its glueing triple — are closed immersions is itself a
closed subspace of `X`. This is `isClosedImmersion_iff_restrictions` read in the category
`Over X` rather than in the category of algebraic spaces over `S`. -/
theorem closedOverX_of_legs (D : FormalGlueingSituation B S hS) (T : spacesOverX D)
    (hU : IsClosedImmersion B S hS (pullback.snd T.1.hom D.U.ι))
    (hY : IsClosedImmersion B S hS (pullback.snd T.1.hom D.f)) : closedOverX D T :=
  (isClosedImmersion_iff_restrictions D (X' := ⟨T.1.left, T.2⟩) ⟨T.1.hom⟩).2
    ⟨(property_pullback_snd_hom_iff (closedImmersionPresheaf B S hS) _ _).1 hU,
      (property_pullback_snd_hom_iff (closedImmersionPresheaf B S hS) _ _).1 hY⟩

/-- The same for clause (3): a space over `X` whose two restrictions are finite is finite
over `X`. -/
theorem finiteOverX_of_legs (D : FormalGlueingSituation B S hS) (T : spacesOverX D)
    (hU : IsFinite B S hS (pullback.snd T.1.hom D.U.ι))
    (hY : IsFinite B S hS (pullback.snd T.1.hom D.f)) : finiteOverX D T :=
  (isFinite_iff_restrictions D (X' := ⟨T.1.left, T.2⟩) ⟨T.1.hom⟩).2
    ⟨(property_pullback_snd_hom_iff (isFinitePresheaf B S hS) _ _).1 hU,
      (property_pullback_snd_hom_iff (isFinitePresheaf B S hS) _ _).1 hY⟩

/-! ### Transporting the conditions on the legs along an isomorphism of glueing triples -/

/-- A property of morphisms stable under isomorphism passes from the structure map of the target
of an isomorphism in `Over W` to that of its source. -/
private theorem property_hom_of_iso_over
    (P : MorphismProperty ((BigFppfOver B S hS)ᵒᵖ ⥤ Type u)) [P.RespectsIso]
    {W : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u} {a b : Over W} (e : a ≅ b) (h : P b.hom) : P a.hom := by
  rw [← Over.w e.hom]
  exact (P.cancel_left_of_respectsIso ((Over.forget W).mapIso e).hom _).2 h

/-- An isomorphism of glueing triples carries a property of the left leg of its target, stable
under isomorphism, to the same property of the left leg of its source. -/
theorem property_legLeft_of_iso
    (P : MorphismProperty ((BigFppfOver B S hS)ᵒᵖ ⥤ Type u)) [P.RespectsIso]
    (D : FormalGlueingSituation B S hS) {A A' : glueingData D} (ε : A ≅ A')
    (h : P A'.1.left.hom) : P A.1.left.hom :=
  property_hom_of_iso_over P ((Comma.fst _ _).mapIso ((ObjectProperty.ι _).mapIso ε)) h

/-- An isomorphism of glueing triples carries a property of the right leg of its target, stable
under isomorphism, to the same property of the right leg of its source. -/
theorem property_legRight_of_iso
    (P : MorphismProperty ((BigFppfOver B S hS)ᵒᵖ ⥤ Type u)) [P.RespectsIso]
    (D : FormalGlueingSituation B S hS) {A A' : glueingData D} (ε : A ≅ A')
    (h : P A'.1.right.hom) : P A.1.right.hom :=
  property_hom_of_iso_over P ((Comma.snd _ _).mapIso ((ObjectProperty.ι _).mapIso ε)) h

/-! ### Essential surjectivity in clauses (2) and (3) follows from clause (1) -/

/-- **The source's reduction of clause (2) to clause (1).** Given a glueing triple whose three
legs are closed immersions, clause (1) of **Stacks 0AF4** produces a space affine over `X` with
that triple; its two restrictions are then closed immersions, so by `closedOverX_of_legs` — the
criterion resting on **Stacks 0420** — the space is a closed subspace of `X`, and the triple is
in the essential image of clause (2). -/
theorem essSurj_closedGlueingFunctor (D : FormalGlueingSituation B S hS)
    (h : (affineGlueingFunctor D).EssSurj) : (closedGlueingFunctor D).EssSurj := by
  refine ⟨fun G ↦ ?_⟩
  obtain ⟨T, ⟨e⟩⟩ := h.mem_essImage ⟨G.obj, closedLegs_le_affineLegs D _ G.property⟩
  have ε : ((formalGlueingFunctor D).1.obj T.obj) ≅ G.obj := (ObjectProperty.ι _).mapIso e
  have hT : closedOverX D T.obj :=
    closedOverX_of_legs D T.obj
      (property_legLeft_of_iso (closedImmersionPresheaf B S hS) D ε G.property.1)
      (property_legRight_of_iso (closedImmersionPresheaf B S hS) D ε G.property.2.2)
  exact ⟨⟨T.obj, hT⟩, ⟨(ObjectProperty.fullyFaithfulι (closedLegs D)).preimageIso ε⟩⟩

/-- The same for clause (3), by the criterion resting on **Stacks 0426**. -/
theorem essSurj_finiteGlueingFunctor (D : FormalGlueingSituation B S hS)
    (h : (affineGlueingFunctor D).EssSurj) : (finiteGlueingFunctor D).EssSurj := by
  refine ⟨fun G ↦ ?_⟩
  obtain ⟨T, ⟨e⟩⟩ := h.mem_essImage ⟨G.obj, finiteLegs_le_affineLegs D _ G.property⟩
  have ε : ((formalGlueingFunctor D).1.obj T.obj) ≅ G.obj := (ObjectProperty.ι _).mapIso e
  have hT : finiteOverX D T.obj :=
    finiteOverX_of_legs D T.obj
      (property_legLeft_of_iso (isFinitePresheaf B S hS) D ε G.property.1)
      (property_legRight_of_iso (isFinitePresheaf B S hS) D ε G.property.2.2)
  exact ⟨⟨T.obj, hT⟩, ⟨(ObjectProperty.fullyFaithfulι (finiteLegs D)).preimageIso ε⟩⟩

/-! ### Clause (1) as the one remaining input, and clauses (2) and (3) from it -/

/-- **Clause (1) of Stacks 0AF4**, as a named statement: the restriction of the functor of
Stacks 0AF3 to the algebraic spaces affine over `X` is an equivalence onto the glueing triples
whose three legs are affine.

This is the one assertion of Stacks 0AF4 that this library does not prove. By the source's own
proof it is Stacks 0AF0 — that the functor of Stacks 0AEW is an equivalence
`QCoh(𝒪_X) ≃ QCoh(Y → X, Z)` — transported along the anti-equivalence of Stacks 081V between
the spaces affine over `X` and the quasi-coherent `𝒪_X`-algebras, whose inverse is the relative
spectrum of Stacks 081W. Neither input is available: Stacks 0AF0 is nowhere stated, and
`AlgebraicGeometry.Space.AffineAlgebraAntiEquivalence` has no inhabitant. See this module's
implementation notes. -/
abbrev AffineEquivalence (D : FormalGlueingSituation B S hS) : Prop :=
  (affineGlueingFunctor D).IsEquivalence

/-- **Clause (2) of Stacks 0AF4 follows from clause (1).** This is the source's own reduction:
fully faithfulness in (2) follows from (1), and for essential surjectivity one reduces by (1) to
the criterion that `X' ⟶ X` is a closed immersion exactly when both `U ×_X X' ⟶ U` and
`Y ×_X X' ⟶ Y` are — which rests on **Stacks 0AF1** and **Stacks 0420** and is
`isClosedImmersion_iff_restrictions`.

The hypothesis `h` is clause (1) of the tag; the registered statement, with clause (1) proved,
is `AlgebraicGeometry.Space.FormalGlueingSituation.closedGlueingFunctor_isEquivalence`. -/
theorem isEquivalence_closedGlueingFunctor (D : FormalGlueingSituation B S hS)
    (h : AffineEquivalence D) : (closedGlueingFunctor D).IsEquivalence where
  faithful := faithful_closedGlueingFunctor D
  full := full_closedGlueingFunctor D h.full
  essSurj := essSurj_closedGlueingFunctor D h.essSurj

/-- **Clause (3) of Stacks 0AF4 follows from clause (1).** The source says "use the argument
proving (2)"; the criterion for finite morphisms rests on **Stacks 0426** instead of
**Stacks 0420** and is `isFinite_iff_restrictions`.

The registered statement, with clause (1) proved, is
`AlgebraicGeometry.Space.FormalGlueingSituation.finiteGlueingFunctor_isEquivalence`. -/
theorem isEquivalence_finiteGlueingFunctor (D : FormalGlueingSituation B S hS)
    (h : AffineEquivalence D) : (finiteGlueingFunctor D).IsEquivalence where
  faithful := faithful_finiteGlueingFunctor D
  full := full_finiteGlueingFunctor D h.full
  essSurj := essSurj_finiteGlueingFunctor D h.essSurj

end AlgebraicGeometry.Space.FormalGlueingSituation

end
