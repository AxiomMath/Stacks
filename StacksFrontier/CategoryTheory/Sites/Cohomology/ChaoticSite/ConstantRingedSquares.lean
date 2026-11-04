module

public import StacksFrontier.CategoryTheory.Sites.Cohomology.ChaoticSite.ConstantRingedToposMorphism
import StacksCore.Tactic.StacksAttribute

/-!
# Two commuting squares of constant-coefficient ringed topoi

Let `C` be a category with its chaotic topology, `π : (Sh(C), R̲) ⟶ (Sh(*), R)` the projection to
the ringed point, and `*` the one-object category. Two squares built from these commute.

**Change of coefficients.** A map of rings `φ : R ⟶ R'` gives a morphism of ringed topoi
`(Sh(C), R̲') ⟶ (Sh(C), R̲)` with identity underlying geometric morphism, and the square
```
(Sh(C), R̲')  --φ-->  (Sh(C), R̲)
    |π'                   |π
 (Sh(*), R')  --φ-->  (Sh(*), R)
```
commutes: the comparison of inverse images is the identity of the restriction functor along
`C ⥤ *`, and the two structure maps agree along its adjoint mate.

**Functoriality.** A functor `u : D ⥤ C` gives `g : (Sh(D), R̲) ⟶ (Sh(C), R̲)` and the triangle
```
(Sh(D), R̲)  --g-->  (Sh(C), R̲)
        \             /
       π_D          π_C
          (Sh(*), R)
```
commutes: the comparison is the canonical identification of restriction along `C ⥤ *` followed by
restriction along `u` with restriction along `D ⥤ *`, which exists because `u ⋙ star = star`.

Together these are the two squares of the double square of Stacks 08QN, before the polynomial
sites are put in. Neither needs anything about the sites beyond the chaotic topology, so both are
stated here for an arbitrary category.

## Main definitions

* `Stacks.ChaoticSite.constantCoefficientMorphism`: change of constant coefficients, with
  identity underlying geometric morphism.
* `Stacks.ChaoticSite.constantProjection`: the projection to the ringed point.
* `Stacks.ChaoticSite.coefficientSquareComparison` and
  `Stacks.ChaoticSite.functorialitySquareComparison`: the two comparison isomorphisms.
* `AlgebraicGeometry.RingedToposHom.SquareCommutes`: the commutation of a square of morphisms of
  ringed topoi along a given comparison of inverse images, as a proposition.

## Main results

* `Stacks.ChaoticSite.coefficientSquare_commutes`: the change-of-coefficients square commutes.
* `Stacks.ChaoticSite.functorialitySquare_commutes`: the functoriality triangle commutes.
* `Stacks.ChaoticSite.isTransport_coefficientSquareComparison` and
  `Stacks.ChaoticSite.isTransport_functorialitySquareComparison`: the two comparisons are the
  canonical ones and not some other isomorphism. Without these the two theorems above would be
  vacuous, since a square can be made to commute by choosing the comparison badly.
* `Stacks.ChaoticSite.sheafPushforwardContinuous_map_constantRingSheafMap`: the map of constant
  sheaves of sets induced by `φ` on `C` is the restriction along `C ⥤ *` of the one induced by
  `φ` on the point. This is the only genuinely mathematical input of the first square.

## Implementation notes

`Stacks.comp_eq_comp_of_isTransport` is why the first square needs almost no computation: three
of its four edges are transports between two presentations of one restriction functor, so the
square reduces to the single equation between its fourth edge and the restriction of the map
induced by `φ` on the point, which is
`Stacks.ChaoticSite.sheafPushforwardContinuous_map_constantRingSheafMap`. The second square needs
even less — every edge is a transport, so
`AlgebraicGeometry.RingedToposHom.ringedSquare_of_isTransport` applies directly.

The two squares are stated differently. The functoriality triangle writes its commutation
equation out. The change-of-coefficients square is stated as
`AlgebraicGeometry.RingedToposHom.SquareCommutes`, that same equation written once at abstract
morphisms, with `Stacks.ChaoticSite.coefficientSquare_mate_eq` recording the unfolded form. The
equation can perfectly well be *stated* at these concrete composites; what cannot be done is to
derive it there directly from
`AlgebraicGeometry.RingedToposHom.squareCommutes_of_fSharpInverseImageForget_eq`, which asks the
elaborator to identify two spellings of a composite that is well-typed only up to the
definitional equality between forgetting the ring operations and taking the direct image, and
exceeds the heartbeat limit. Proving it where both sides are `SquareCommutes` makes that
identification a single unfolding, and the unfolded form then follows for free. `SquareCommutes`
is a `def` of a `Prop` that unfolds to the equation by `rfl`, so nothing is weakened.

Every step here is taken in term mode against lemmas stated at abstract functors, because the two
sides of each equation are definitionally but not syntactically equal: a topos written as
`(constantRingedTopos C R).Topos` and the same topos written as `Sheaf (trivial C) (Type _)`
differ by an unfolding that `rw`, `change` and `simp` will not perform, since they type-check
their motive at `implicit` transparency while term-mode elaboration works at `default`. The
abstract lemmas of the `Stacks` namespace below exist exactly so that each such step happens
where the two spellings coincide. For the same reason
`Stacks.ChaoticSite.sheafPushforwardContinuous_map_constantRingSheafMap` is stated against
`CategoryTheory.Functor.sheafPushforwardContinuous` rather than against the inverse image of
`Stacks.ChaoticSite.constantProjection`: the latter is a `cast` along an equality of ringed topoi
and does not reduce, so the equation would not be `rfl`.

The functoriality square takes the two categories in one universe with one hom universe. That is
not a mathematical restriction of the statement so much as the shape the consumer needs: the two
polynomial sites of Stacks 08QN both live in `Type (u + 1)` with `Category.{u}`.

## References

* [Stacks Project, Tag 08QN](https://stacks.math.columbia.edu/tag/08QN)
* [Stacks Project, Tag 08PH](https://stacks.math.columbia.edu/tag/08PH)
-/

@[expose] public section

open CategoryTheory
open AlgebraicGeometry AlgebraicGeometry.RingedToposHom

namespace Stacks

/-- Composing with a functor that is the identity, on the right, changes nothing. Stated as an
equation between *given* functors rather than as `CategoryTheory.Functor.comp_id` so that it can
be applied in term mode: `rw` rejects `Functor.comp_id` on a goal whose two sides spell the same
universe level in two ways, because it re-type-checks the instantiated pattern at `implicit`
transparency. -/
theorem comp_eq_of_eq_id_right {A B : Type*} [Category* A] [Category* B] {F F₀ : A ⥤ B}
    (hF : F = F₀) {G : B ⥤ B} (hG : G = 𝟭 B) : F ⋙ G = F₀ := by
  subst hF
  subst hG
  exact Functor.comp_id _

/-- Composing with a functor that is the identity, on the left, changes nothing. The term-mode
counterpart of `CategoryTheory.Functor.id_comp`; see `Stacks.comp_eq_of_eq_id_right`. -/
theorem comp_eq_of_eq_id_left {A B : Type*} [Category* A] [Category* B] {G : A ⥤ A}
    (hG : G = 𝟭 A) {F F₀ : A ⥤ B} (hF : F = F₀) : G ⋙ F = F₀ := by
  subst hF
  subst hG
  exact Functor.id_comp _

/-- Two functors that are equal act the same on a morphism. Stated with `HEq` because the two
values live in types that depend on the functor. -/
theorem heq_map_of_eq {A B : Type*} [Category* A] [Category* B] {L L₀ : A ⥤ B} (h : L = L₀)
    {P Q : A} (ψ : P ⟶ Q) : HEq (L.map ψ) (L₀.map ψ) := by
  cases h
  rfl

/-- The forward direction of `CategoryTheory.eqToIso` is a transport.

This is `Stacks.IsTransport.eqToHom` with the `CategoryTheory.eqToIso` left in place, and it is
not a convenience. Applying `Stacks.IsTransport.eqToHom` to `(eqToIso h).hom` asks the unifier
to solve `eqToHom ?h =?= Iso.hom (eqToIso h)`, whose two sides have different heads; it unfolds
`eqToHom` to its `Eq.rec` and then tries to reduce `h` itself to `Eq.refl`, which on an equality
of sheaf-valued functors means evaluating the whole proof term. Here both sides are `Iso.hom`
applications, so congruence applies and no proof is ever reduced. -/
theorem isTransport_eqToIso_hom {C : Type*} [Category* C] {X Y : C} (h : X = Y) :
    IsTransport (eqToIso h).hom :=
  IsTransport.eqToHom h

/-- An equality of morphisms whose sources and targets are equal only up to transport, written in
the form `Stacks.comp_eq_comp_of_isTransport` consumes. -/
theorem eq_eqToHom_comp_comp_eqToHom {B : Type*} [Category* B] {S T V W : B} {b : S ⟶ T}
    {c : V ⟶ W} (h₁ : S = V) (h₂ : W = T) (h : HEq b c) :
    b = eqToHom h₁ ≫ c ≫ eqToHom h₂ := by
  cases h₁
  cases h₂
  simpa using eq_of_heq h

/-- **A square three of whose edges are transports.** If `α`, `ε` and `β` are transports then the
square `α ≫ b = ε ≫ c ≫ β` commutes as soon as `b` and `c` agree, which they can only do up to
transport since their sources and targets are merely equal. No 2-cell is computed: this is the
whole content of a square of ringed topoi whose only non-transport edge is a change of
coefficients. -/
theorem comp_eq_comp_of_isTransport {B : Type*} [Category* B] {U S V W T : B} {α : U ⟶ S}
    {b : S ⟶ T} {ε : U ⟶ V} {c : V ⟶ W} {β : W ⟶ T} (hα : IsTransport α) (hε : IsTransport ε)
    (hβ : IsTransport β) (hb : ∀ h₁ : S = V, ∀ h₂ : W = T, b = eqToHom h₁ ≫ c ≫ eqToHom h₂) :
    α ≫ b = ε ≫ c ≫ β := by
  obtain ⟨hUS, rfl⟩ := hα
  obtain ⟨hUV, rfl⟩ := hε
  obtain ⟨hWT, rfl⟩ := hβ
  cases hUS
  cases hUV
  cases hWT
  simpa using hb rfl rfl

end Stacks

namespace AlgebraicGeometry.RingedToposHom

universe v u w v' u'

variable {X : RingedTopos.{v, u, w}} {Y : RingedTopos.{v', u', w}}
  [X.J.HasSheafCompose (forget RingCat.{w})]
  [Y.J.HasSheafCompose (forget RingCat.{w})]
  [X.J.HasSheafCompose (forget₂ CommRingCat.{w} RingCat.{w})]
  [Y.J.HasSheafCompose (forget₂ CommRingCat.{w} RingCat.{w})]

/-- **The commutation of a square of morphisms of ringed topoi** `F, G : X ⟶ Y` with a given
comparison `e` of their inverse images: the structure map of `F`, followed by the adjoint mate of
`e`, is the structure map of `G`.

This is a definition and not a bare equation because the equation cannot be written down twice.
Its composite is well-typed only because forgetting the ring operations commutes with the direct
image, a definitional equality that the elaborator must discharge wherever the equation is
elaborated. With `F` and `G` abstract that costs nothing. With `F` and `G` concrete — composites
of a `cast` and of a change of coefficients, which is `ofInverseImageMap` of the identity
geometric morphism — it exhausts memory before any proof is even looked at. Writing the equation
once here, at abstract morphisms, and naming the result means a concrete square is stated by
substitution into a term already elaborated. -/
def SquareCommutes (F G : RingedToposHom X Y)
    (e : F.toToposHom.inverseImage ≅ G.toToposHom.inverseImage) : Prop :=
  Y.forgetRing.map F.fSharp ≫
    ((F.toToposHom.adj.ofNatIsoLeft e).rightAdjointUniq G.toToposHom.adj).hom.app
      (X.forgetRing.obj X.O) = Y.forgetRing.map G.fSharp

/-- **A square of ringed topoi commutes as soon as its two inverse-image structure maps agree
along the comparison.** This is `CategoryTheory.Adjunction.comp_rightAdjointUniq_hom_app_eq_iff`
packaged at the level of morphisms of ringed topoi, which is the level at which it can be applied
to concrete ones: invoking the adjunction lemma directly makes the elaborator unfold both
composites into `CategoryTheory.Adjunction.homEquiv` and compare the results.

`AlgebraicGeometry.RingedToposHom.ringedSquare_of_isTransport` is the special case in which both
structure maps and the comparison are transports, so that the hypothesis holds for free. -/
theorem squareCommutes_of_fSharpInverseImageForget_eq (F G : RingedToposHom X Y)
    (e : F.toToposHom.inverseImage ≅ G.toToposHom.inverseImage)
    (h : F.fSharpInverseImageForget =
      e.hom.app (Y.forgetRing.obj Y.O) ≫ G.fSharpInverseImageForget) :
    SquareCommutes F G e :=
  (Adjunction.comp_rightAdjointUniq_hom_app_eq_iff
    F.toToposHom.adj G.toToposHom.adj e _ _).mpr h

end AlgebraicGeometry.RingedToposHom

namespace Stacks.ChaoticSite

universe w v₁ u₁ wD vD uD

/-- Instance handle for the topology of a constant-coefficient ringed topos: instance search does
not see through the projection, so a goal phrased with `(constantRingedTopos C R).J` would not
find `Stacks.ChaoticSite.isContinuous_trivial`. -/
instance isContinuous_constantRingedTopos (C : Type u₁) (D : Type uD) [Category.{v₁} C]
    [Category.{vD} D] (g : D ⥤ C) (R : CommRingCat.{w}) (R' : CommRingCat.{wD}) :
    g.IsContinuous (constantRingedTopos D R').J (constantRingedTopos C R).J :=
  isContinuous_trivial C D g

/-- The same handle with the target written as the chaotic topology, which is the spelling the
comparison isomorphisms of this file produce on one side of each equation. -/
instance isContinuous_constantRingedTopos_source (C : Type u₁) (D : Type uD) [Category.{v₁} C]
    [Category.{vD} D] (g : D ⥤ C) (R' : CommRingCat.{wD}) :
    g.IsContinuous (constantRingedTopos D R').J (GrothendieckTopology.trivial C) :=
  isContinuous_trivial C D g

/-- The same handle with the source written as the chaotic topology. -/
instance isContinuous_constantRingedTopos_target (C : Type u₁) (D : Type uD) [Category.{v₁} C]
    [Category.{vD} D] (g : D ⥤ C) (R : CommRingCat.{w}) :
    g.IsContinuous (GrothendieckTopology.trivial D) (constantRingedTopos C R).J :=
  isContinuous_trivial C D g

/-! ### Change of constant coefficients -/

section Coefficient

variable (C : Type u₁) [Category.{v₁} C] {R R' : CommRingCat.{max w u₁ v₁}}

/-- The map of constant sheaves of commutative rings induced by a map of rings: `φ` on every
section. -/
noncomputable def constantRingSheafMap (φ : R ⟶ R') :
    constantRingSheaf C R ⟶ constantRingSheaf C R' :=
  (sheafBotEquivalence CommRingCat.{max w u₁ v₁}).inverse.map ((Functor.const Cᵒᵖ).map φ)

/-- **Change of constant coefficients.** A map of rings `φ : R ⟶ R'` induces a morphism of ringed
topoi `(Sh(C), R̲') ⟶ (Sh(C), R̲)` whose underlying geometric morphism is the identity and whose
structure map is the constant map `φ`. -/
noncomputable def constantCoefficientMorphism (φ : R ⟶ R') :
    RingedToposHom (constantRingedTopos C R') (constantRingedTopos C R) :=
  coefficientMorphism (GrothendieckTopology.trivial C) (constantRingSheafMap.{w, v₁, u₁} C φ)

/-- The inverse image of a change of constant coefficients is the identity functor. -/
theorem constantCoefficientMorphism_inverseImage (φ : R ⟶ R') :
    (constantCoefficientMorphism.{w, v₁, u₁} C φ).toToposHom.inverseImage =
      𝟭 (Sheaf (GrothendieckTopology.trivial C) (Type (max w u₁ v₁))) :=
  congrArg (fun m ↦ MorphismOfTopoi.inverseImage m)
    (coefficientMorphism_toToposHom (GrothendieckTopology.trivial C) _)

end Coefficient

/-! ### The projection to the ringed point -/

/-- The projection of a chaotic site to its ringed point, with constant coefficients: the
morphism of ringed topoi induced by the unique functor `C ⥤ *`. -/
noncomputable def constantProjection (C : Type u₁) [Category.{v₁} C]
    (R : CommRingCat.{max w u₁ v₁}) :
    RingedToposHom (constantRingedTopos C R)
      (constantRingedTopos (Discrete PUnit.{u₁ + 1}) R) :=
  constantRingedMorphismOnTrivial.{w, u₁, v₁, u₁, u₁} (Discrete PUnit.{u₁ + 1}) C
    (Functor.star C) R

/-- The inverse image of the projection is restriction along `C ⥤ *`; in particular it does not
depend on the coefficient ring. -/
theorem constantProjection_inverseImage (C : Type u₁) [Category.{v₁} C]
    (R : CommRingCat.{max w u₁ v₁}) :
    (constantProjection.{w} C R).toToposHom.inverseImage =
      (Functor.star C).sheafPushforwardContinuous (Type (max w u₁ v₁))
        (GrothendieckTopology.trivial C)
        (GrothendieckTopology.trivial (Discrete PUnit.{u₁ + 1})) :=
  constantRingedMorphismOnTrivial_inverseImage.{w, u₁, v₁, u₁, u₁} _ C (Functor.star C) R

/-- The inverse-image structure map of the projection is a transport. -/
theorem isTransport_constantProjection_fSharpInverseImageForget (C : Type u₁) [Category.{v₁} C]
    (R : CommRingCat.{max w u₁ v₁}) :
    Stacks.IsTransport (constantProjection.{w} C R).fSharpInverseImageForget :=
  isTransport_constantRingedMorphismOnTrivial_fSharpInverseImageForget.{w, u₁, v₁, u₁, u₁}
    _ C (Functor.star C) R

/-- **The map induced by `φ` on `C` is the restriction of the map induced by `φ` on the point.**
Both are `φ` on every section, so this is `rfl`; it is the only mathematical input of the
change-of-coefficients square.

Stated against `CategoryTheory.Functor.sheafPushforwardContinuous` rather than against
`(constantProjection C R).toToposHom.inverseImage`, which is a `cast` along an equality of ringed
topoi and therefore does not reduce. `Stacks.ChaoticSite.constantProjection_inverseImage` moves
the statement across, and `Stacks.heq_map_of_eq` carries a `map` across it. -/
theorem sheafPushforwardContinuous_map_constantRingSheafMap (C : Type u₁) [Category.{v₁} C]
    {R R' : CommRingCat.{max w u₁ v₁}} (φ : R ⟶ R') :
    (sheafCompose (GrothendieckTopology.trivial C) (forget CommRingCat.{max w u₁ v₁})).map
        (constantRingSheafMap.{w, v₁, u₁} C φ) =
      ((Functor.star C).sheafPushforwardContinuous (Type (max w u₁ v₁))
          (GrothendieckTopology.trivial C)
          (GrothendieckTopology.trivial (Discrete PUnit.{u₁ + 1}))).map
        ((sheafCompose (GrothendieckTopology.trivial (Discrete PUnit.{u₁ + 1}))
            (forget CommRingCat.{max w u₁ v₁})).map
          (constantRingSheafMap.{max w v₁, u₁, u₁} (Discrete PUnit.{u₁ + 1}) φ)) :=
  rfl

/-! ### The change-of-coefficients square -/

section CoefficientSquare

variable (C : Type u₁) [Category.{v₁} C] {R R' : CommRingCat.{max w u₁ v₁}} (φ : R ⟶ R')

/-- Down then across: the projection with coefficients `R`, after the coefficient change on
`C`. -/
noncomputable def coefficientSquareDownAcross :
    RingedToposHom (constantRingedTopos C R')
      (constantRingedTopos (Discrete PUnit.{u₁ + 1}) R) :=
  AlgebraicGeometry.RingedToposHom.comp (X := constantRingedTopos C R')
    (Y := constantRingedTopos C R)
    (Z := constantRingedTopos (Discrete PUnit.{u₁ + 1}) R)
    (constantProjection.{w} C R) (constantCoefficientMorphism.{w, v₁, u₁} C φ)

/-- Across then down: the coefficient change on the point, after the projection with coefficients
`R'`. -/
noncomputable def coefficientSquareAcrossDown :
    RingedToposHom (constantRingedTopos C R')
      (constantRingedTopos (Discrete PUnit.{u₁ + 1}) R) :=
  AlgebraicGeometry.RingedToposHom.comp (X := constantRingedTopos C R')
    (Y := constantRingedTopos (Discrete PUnit.{u₁ + 1}) R')
    (Z := constantRingedTopos (Discrete PUnit.{u₁ + 1}) R)
    (constantCoefficientMorphism.{max w v₁, u₁, u₁} (Discrete PUnit.{u₁ + 1}) φ)
    (constantProjection.{w} C R')

/-- The inverse image of the first composite is restriction along `C ⥤ *`: the coefficient change
contributes the identity geometric morphism. -/
theorem coefficientSquareDownAcross_inverseImage :
    (coefficientSquareDownAcross.{w} C φ).toToposHom.inverseImage =
      (Functor.star C).sheafPushforwardContinuous (Type (max w u₁ v₁))
        (GrothendieckTopology.trivial C)
        (GrothendieckTopology.trivial (Discrete PUnit.{u₁ + 1})) :=
  have h : (coefficientSquareDownAcross.{w} C φ).toToposHom.inverseImage =
      (constantProjection.{w} C R).toToposHom.inverseImage ⋙
        (constantCoefficientMorphism.{w, v₁, u₁} C φ).toToposHom.inverseImage := rfl
  h.trans (Stacks.comp_eq_of_eq_id_right (constantProjection_inverseImage.{w} C R)
    (constantCoefficientMorphism_inverseImage.{w, v₁, u₁} C φ))

/-- The inverse image of the second composite is the same restriction along `C ⥤ *`: the
projection's inverse image does not depend on the coefficient ring. -/
theorem coefficientSquareAcrossDown_inverseImage :
    (coefficientSquareAcrossDown.{w} C φ).toToposHom.inverseImage =
      (Functor.star C).sheafPushforwardContinuous (Type (max w u₁ v₁))
        (GrothendieckTopology.trivial C)
        (GrothendieckTopology.trivial (Discrete PUnit.{u₁ + 1})) :=
  have h : (coefficientSquareAcrossDown.{w} C φ).toToposHom.inverseImage =
      (constantCoefficientMorphism.{max w v₁, u₁, u₁}
          (Discrete PUnit.{u₁ + 1}) φ).toToposHom.inverseImage ⋙
        (constantProjection.{w} C R').toToposHom.inverseImage := rfl
  h.trans (Stacks.comp_eq_of_eq_id_left
    (constantCoefficientMorphism_inverseImage.{max w v₁, u₁, u₁} (Discrete PUnit.{u₁ + 1}) φ)
    (constantProjection_inverseImage.{w} C R'))

/-- The two composites have the same inverse image. -/
theorem coefficientSquare_inverseImage_eq :
    (coefficientSquareDownAcross.{w} C φ).toToposHom.inverseImage =
      (coefficientSquareAcrossDown.{w} C φ).toToposHom.inverseImage :=
  (coefficientSquareDownAcross_inverseImage.{w} C φ).trans
    (coefficientSquareAcrossDown_inverseImage.{w} C φ).symm

/-- The comparison of inverse images for the change-of-coefficients square. -/
noncomputable def coefficientSquareComparison :
    (coefficientSquareDownAcross.{w} C φ).toToposHom.inverseImage ≅
      (coefficientSquareAcrossDown.{w} C φ).toToposHom.inverseImage :=
  eqToIso (coefficientSquare_inverseImage_eq.{w} C φ)

/-- **The comparison is the canonical one.** It is the identity of the restriction functor along
`C ⥤ *`, not some other automorphism of it; this is what makes
`Stacks.ChaoticSite.coefficientSquare_commutes` a statement about the square rather than about a
choice. -/
@[stacks 08QN "change-of-coefficients square: the comparison is the canonical one"]
theorem isTransport_coefficientSquareComparison :
    Stacks.IsTransport (coefficientSquareComparison.{w} C φ).hom :=
  Stacks.isTransport_eqToIso_hom (coefficientSquare_inverseImage_eq.{w} C φ)

/-- The inverse-image structure map of the first composite: the projection's, restricted along
the coefficient change, followed by the coefficient change's own. -/
theorem coefficientSquareDownAcross_fSharpInverseImageForget :
    (coefficientSquareDownAcross.{w} C φ).fSharpInverseImageForget =
      (constantCoefficientMorphism.{w, v₁, u₁} C φ).toToposHom.inverseImage.map
          (constantProjection.{w} C R).fSharpInverseImageForget ≫
        (constantCoefficientMorphism.{w, v₁, u₁} C φ).fSharpInverseImageForget :=
  fSharpInverseImageForget_comp (constantProjection.{w} C R)
    (constantCoefficientMorphism.{w, v₁, u₁} C φ)

/-- The inverse-image structure map of the second composite: the coefficient change on the
point, restricted along `C ⥤ *`, followed by the projection's. -/
theorem coefficientSquareAcrossDown_fSharpInverseImageForget :
    (coefficientSquareAcrossDown.{w} C φ).fSharpInverseImageForget =
      (constantProjection.{w} C R').toToposHom.inverseImage.map
          (constantCoefficientMorphism.{max w v₁, u₁, u₁}
            (Discrete PUnit.{u₁ + 1}) φ).fSharpInverseImageForget ≫
        (constantProjection.{w} C R').fSharpInverseImageForget :=
  fSharpInverseImageForget_comp
    (constantCoefficientMorphism.{max w v₁, u₁, u₁} (Discrete PUnit.{u₁ + 1}) φ)
    (constantProjection.{w} C R')

/-- **The two coefficient changes are the same map.** The structure map of the coefficient change
on `C` is the restriction along `C ⥤ *` of the structure map of the coefficient change on the
point. This is the whole mathematical content of the square; everything else in it is a
transport. Stated with `HEq` because the two sources, and the two targets, are equal without
being syntactically equal. -/
theorem heq_constantCoefficientMorphism_fSharpInverseImageForget :
    HEq (constantCoefficientMorphism.{w, v₁, u₁} C φ).fSharpInverseImageForget
      ((constantProjection.{w} C R').toToposHom.inverseImage.map
        (constantCoefficientMorphism.{max w v₁, u₁, u₁}
          (Discrete PUnit.{u₁ + 1}) φ).fSharpInverseImageForget) :=
  ((heq_of_eq ((coefficientMorphism_fSharpInverseImageForget (GrothendieckTopology.trivial C)
          (constantRingSheafMap.{w, v₁, u₁} C φ)).trans
        (sheafPushforwardContinuous_map_constantRingSheafMap.{w} C φ))).trans
      (Stacks.heq_map_of_eq (constantProjection_inverseImage.{w} C R')
        ((sheafCompose (GrothendieckTopology.trivial (Discrete PUnit.{u₁ + 1}))
            (forget CommRingCat.{max w u₁ v₁})).map
          (constantRingSheafMap.{max w v₁, u₁, u₁} (Discrete PUnit.{u₁ + 1}) φ))).symm).trans
    (heq_of_eq (congrArg
      (fun m ↦ (constantProjection.{w} C R').toToposHom.inverseImage.map m)
      (coefficientMorphism_fSharpInverseImageForget
          (GrothendieckTopology.trivial (Discrete PUnit.{u₁ + 1}))
          (constantRingSheafMap.{max w v₁, u₁, u₁} (Discrete PUnit.{u₁ + 1}) φ)).symm))

/-- **The change-of-coefficients square commutes, in inverse-image form.** The inverse-image
structure map of the first composite is the comparison followed by that of the second. This is
the form in which the square can be checked: three of its four edges are transports, and the
fourth is `Stacks.ChaoticSite.heq_constantCoefficientMorphism_fSharpInverseImageForget`. -/
theorem coefficientSquare_fSharpInverseImageForget_eq :
    (coefficientSquareDownAcross.{w} C φ).fSharpInverseImageForget =
      (coefficientSquareComparison.{w} C φ).hom.app
          ((constantRingedTopos (Discrete PUnit.{u₁ + 1}) R).forgetRing.obj
            (constantRingedTopos (Discrete PUnit.{u₁ + 1}) R).O) ≫
        (coefficientSquareAcrossDown.{w} C φ).fSharpInverseImageForget :=
  (coefficientSquareDownAcross_fSharpInverseImageForget.{w} C φ).trans
    ((Stacks.comp_eq_comp_of_isTransport
          ((isTransport_constantProjection_fSharpInverseImageForget.{w} C R).map
            (constantCoefficientMorphism.{w, v₁, u₁} C φ).toToposHom.inverseImage)
          ((isTransport_coefficientSquareComparison.{w} C φ).app
            ((constantRingedTopos (Discrete PUnit.{u₁ + 1}) R).forgetRing.obj
              (constantRingedTopos (Discrete PUnit.{u₁ + 1}) R).O))
          (isTransport_constantProjection_fSharpInverseImageForget.{w} C R')
          (fun h₁ h₂ ↦ Stacks.eq_eqToHom_comp_comp_eqToHom h₁ h₂
            (heq_constantCoefficientMorphism_fSharpInverseImageForget.{w} C φ))).trans
      (congrArg
        (fun m ↦ (coefficientSquareComparison.{w} C φ).hom.app
            ((constantRingedTopos (Discrete PUnit.{u₁ + 1}) R).forgetRing.obj
              (constantRingedTopos (Discrete PUnit.{u₁ + 1}) R).O) ≫ m)
        (coefficientSquareAcrossDown_fSharpInverseImageForget.{w} C φ).symm))

/-- **The change-of-coefficients square commutes.** The structure map of the one composite,
transported along the adjoint mate of the canonical comparison, is the structure map of the
other; see `AlgebraicGeometry.RingedToposHom.SquareCommutes`, which is that equation. -/
@[stacks 08QN "the change-of-coefficients square of constant-coefficient ringed topoi"]
theorem coefficientSquare_commutes :
    SquareCommutes (X := constantRingedTopos C R')
      (Y := constantRingedTopos (Discrete PUnit.{u₁ + 1}) R)
      (coefficientSquareDownAcross.{w} C φ) (coefficientSquareAcrossDown.{w} C φ)
      (coefficientSquareComparison.{w} C φ) :=
  squareCommutes_of_fSharpInverseImageForget_eq (X := constantRingedTopos C R')
    (Y := constantRingedTopos (Discrete PUnit.{u₁ + 1}) R)
    (coefficientSquareDownAcross.{w} C φ) (coefficientSquareAcrossDown.{w} C φ)
    (coefficientSquareComparison.{w} C φ)
    (coefficientSquare_fSharpInverseImageForget_eq.{w} C φ)

/-- The change-of-coefficients square commutes, with the equation written out. This is
`Stacks.ChaoticSite.coefficientSquare_commutes` with
`AlgebraicGeometry.RingedToposHom.SquareCommutes` unfolded, and is the form to read; the two are
the same proposition. -/
theorem coefficientSquare_mate_eq :
    (constantRingedTopos (Discrete PUnit.{u₁ + 1}) R).forgetRing.map
        (coefficientSquareDownAcross.{w} C φ).fSharp ≫
      (((coefficientSquareDownAcross.{w} C φ).toToposHom.adj.ofNatIsoLeft
            (coefficientSquareComparison.{w} C φ)).rightAdjointUniq
          (coefficientSquareAcrossDown.{w} C φ).toToposHom.adj).hom.app
        ((constantRingedTopos C R').forgetRing.obj (constantRingedTopos C R').O) =
      (constantRingedTopos (Discrete PUnit.{u₁ + 1}) R).forgetRing.map
        (coefficientSquareAcrossDown.{w} C φ).fSharp :=
  coefficientSquare_commutes.{w} C φ

end CoefficientSquare

/-! ### The functoriality square -/

section FunctorialitySquare

variable (C D : Type u₁) [Category.{v₁} C] [Category.{v₁} D] (u : D ⥤ C)
  (R : CommRingCat.{max w u₁ v₁})

/-- The morphism of ringed topoi `(Sh(D), R̲) ⟶ (Sh(C), R̲)` induced by `u`. -/
noncomputable def constantFunctorMorphism :
    RingedToposHom (constantRingedTopos D R) (constantRingedTopos C R) :=
  constantRingedMorphismOnTrivial.{w, v₁, v₁, u₁, u₁} C D u R

/-- Across then down: the projection of `C`, after the morphism induced by `u`. -/
noncomputable def functorialitySquareAcrossDown :
    RingedToposHom (constantRingedTopos D R)
      (constantRingedTopos (Discrete PUnit.{u₁ + 1}) R) :=
  AlgebraicGeometry.RingedToposHom.comp (X := constantRingedTopos D R)
    (Y := constantRingedTopos C R)
    (Z := constantRingedTopos (Discrete PUnit.{u₁ + 1}) R)
    (constantProjection.{w} C R) (constantFunctorMorphism.{w} C D u R)

/-- The two composites' inverse images are restriction along `C ⥤ *` then along `u`, and
restriction along `D ⥤ *`. -/
theorem functorialitySquare_inverseImage_eq :
    (functorialitySquareAcrossDown.{w} C D u R).toToposHom.inverseImage =
      (Functor.star C).sheafPushforwardContinuous (Type (max w u₁ v₁))
          (GrothendieckTopology.trivial C)
          (GrothendieckTopology.trivial (Discrete PUnit.{u₁ + 1})) ⋙
        u.sheafPushforwardContinuous (Type (max w u₁ v₁))
          (GrothendieckTopology.trivial D) (GrothendieckTopology.trivial C) :=
  congrArg₂ (· ⋙ ·) (constantProjection_inverseImage.{w} C R)
    (constantRingedMorphismOnTrivial_inverseImage.{w, v₁, v₁, u₁, u₁} C D u R)

/-- The comparison of inverse images for the functoriality square: the canonical identification
of restriction along `C ⥤ *` then `u` with restriction along `D ⥤ *`, which exists because
`u ⋙ star = star`. -/
noncomputable def functorialitySquareComparison :
    (functorialitySquareAcrossDown.{w} C D u R).toToposHom.inverseImage ≅
      (constantProjection.{w} D R).toToposHom.inverseImage :=
  eqToIso (functorialitySquare_inverseImage_eq.{w} C D u R) ≪≫
    CategoryTheory.Functor.sheafPushforwardContinuousComp'
      (eqToIso (star_isFibredOneMorphism_of_functor C D u).comp_eq) (Type (max w u₁ v₁))
      (GrothendieckTopology.trivial D) (GrothendieckTopology.trivial C)
      (GrothendieckTopology.trivial (Discrete PUnit.{u₁ + 1})) ≪≫
    eqToIso (constantProjection_inverseImage.{w} D R).symm

/-- **The comparison is the canonical one**, hence a transport: it is built from the
identification `u ⋙ star = star` of the two functors to the point and nothing else. -/
@[stacks 08QN "functoriality triangle: the comparison is the canonical one"]
theorem isTransport_functorialitySquareComparison :
    Stacks.IsTransport (functorialitySquareComparison.{w} C D u R).hom :=
  (Stacks.isTransport_eqToIso_hom (functorialitySquare_inverseImage_eq.{w} C D u R)).comp
    ((CategoryTheory.Functor.isTransport_sheafPushforwardContinuousComp'_hom
      (star_isFibredOneMorphism_of_functor C D u).comp_eq _ _ _ _).comp
        (Stacks.isTransport_eqToIso_hom (constantProjection_inverseImage.{w} D R).symm))

/-- The inverse-image structure map of the composite is a transport. -/
theorem isTransport_functorialitySquareAcrossDown_fSharpInverseImageForget :
    Stacks.IsTransport
      (functorialitySquareAcrossDown.{w} C D u R).fSharpInverseImageForget :=
  Eq.mp (congrArg Stacks.IsTransport
      (fSharpInverseImageForget_comp (constantProjection.{w} C R)
        (constantFunctorMorphism.{w} C D u R)).symm)
    (((isTransport_constantProjection_fSharpInverseImageForget.{w} C R).map _).comp
      (isTransport_constantRingedMorphismOnTrivial_fSharpInverseImageForget.{w, v₁, v₁, u₁, u₁}
        C D u R))

/-- **The functoriality triangle commutes.** Every edge is a transport, so the structure map of
`π_C ∘ g` transported along the adjoint mate of the canonical comparison is the structure map of
`π_D`. -/
@[stacks 08QN "the functoriality triangle of constant-coefficient ringed topoi"]
theorem functorialitySquare_commutes :
    (constantRingedTopos (Discrete PUnit.{u₁ + 1}) R).forgetRing.map
        (functorialitySquareAcrossDown.{w} C D u R).fSharp ≫
      (((functorialitySquareAcrossDown.{w} C D u R).toToposHom.adj.ofNatIsoLeft
            (functorialitySquareComparison.{w} C D u R)).rightAdjointUniq
          (constantProjection.{w} D R).toToposHom.adj).hom.app
        ((constantRingedTopos D R).forgetRing.obj (constantRingedTopos D R).O) =
      (constantRingedTopos (Discrete PUnit.{u₁ + 1}) R).forgetRing.map
        (constantProjection.{w} D R).fSharp :=
  ringedSquare_of_isTransport _ _ (functorialitySquareComparison.{w} C D u R)
    (isTransport_functorialitySquareAcrossDown_fSharpInverseImageForget.{w} C D u R)
    (isTransport_constantProjection_fSharpInverseImageForget.{w} D R)
    (isTransport_functorialitySquareComparison.{w} C D u R)

end FunctorialitySquare

end Stacks.ChaoticSite

end
