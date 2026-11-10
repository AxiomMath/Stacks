module

public import Mathlib.Topology.Homeomorph.TransferInstance
public import StacksCore.Tactic.StacksAttribute
public import StacksFrontier.AlgebraicGeometry.Spaces.Extension
public import StacksFrontier.AlgebraicGeometry.Spaces.PointsBaseChange
public import StacksFrontier.AlgebraicGeometry.Spaces.PointsRepresented
public import StacksFrontier.AlgebraicGeometry.Spaces.PointsTopologyUnique
public import StacksFrontier.AlgebraicGeometry.Spaces.SmallerBase
public import StacksFrontier.AlgebraicGeometry.Topologies.ChangeOfSites.SliceAdjunction

/-!
# The points of an algebraic space do not depend on the base scheme

Let `g : S ⟶ S'` be a morphism of a big fppf site and let `F` be a presheaf on the big fppf
site of `S`. Stacks 03I5 part (2) views `F` as a presheaf on the big fppf site of `S'` by the
lower-shriek extension `CategoryTheory.OverShriek.relocalizePresheafFunctor g`, and Stacks
04SG says that this is an equivalence onto the presheaves over the representable presheaf of
`g`. This file transports the point set of Stacks 03BU and the point topology of Stacks 03BX
along that extension: the two point sets are in canonical bijection, and — for an algebraic
space — that bijection is a homeomorphism. So the point space of an algebraic space is
independent of the base scheme over which it is considered, which is what lets a statement
about the fibres of a morphism be checked after shrinking the base.

A section of the extension over `W` is a factorization `ψ : W ⟶ S` of the structure morphism
of `W` together with a section of `F` over `(W, ψ)`; reading off `ψ` is a morphism from the
extension to the representable presheaf of `g`, and that morphism is a fibre-product
projection whose base change along a further shrinking of the base is the extension of the
restriction. That square is the other half of the file.

## Main definitions

* `AlgebraicGeometry.Space.relocalizedSectionEquiv` describes a section of the lower-shriek
  extension as a factorization of the structure morphism together with a section.
* `AlgebraicGeometry.Space.relocalizedFieldPoint` and
  `AlgebraicGeometry.Space.originalFieldPoint` are the two transports of a field-valued point.
* `AlgebraicGeometry.Space.relocalizedPointsMap` and
  `AlgebraicGeometry.Space.originalPointsMap` are the induced maps on point sets, and
  `AlgebraicGeometry.Space.relocalizedPointsEquiv` is the resulting bijection.
* `CategoryTheory.OverShriek.viewStructureMap` is the morphism from the lower-shriek extension
  to the representable presheaf of `g`, and
  `CategoryTheory.OverShriek.viewBaseChangeMap` its base change along a further shrinking of
  the base.

## Main results

* `AlgebraicGeometry.Space.relocalizedPointsHomeomorph`: **Stacks 03BX** for a change of base
  scheme — the bijection on points is a homeomorphism for the point topologies.
* `AlgebraicGeometry.Space.relocalizedPointTopologyFamily`: the point topologies pulled back
  along the bijection form a family satisfying the three conditions of Stacks 03BX, which is
  how the homeomorphism is obtained.
* `AlgebraicGeometry.Space.presheaf_relocalized`: a relative property of a morphism of
  presheaves inherited by base change survives the lower-shriek extension.
* `CategoryTheory.OverShriek.viewBaseChange_isPullback` and
  `CategoryTheory.OverShriek.viewBaseChangeIso`: the lower-shriek extension of a restriction
  is the fibre product of the extension with the shrinking of the base.

## Implementation notes

`AlgebraicGeometry.Space.pointTopology` is defined for an arbitrary presheaf on the big fppf
site, so no algebraic-space hypothesis appears in the *statement* of any topology here. The
algebraicity of the source is still needed to *prove* that the transported topology is the
point topology, because the uniqueness statement of Stacks 03BX quantifies over algebraic
spaces; it therefore remains a hypothesis of
`AlgebraicGeometry.Space.relocalizedPointsHomeomorph`.

The injectivity of `AlgebraicGeometry.Space.relocalizedPointsMap` is obtained from the
backwards transport `AlgebraicGeometry.Space.originalFieldPoint`, which is a left inverse on
the nose rather than merely up to common extension.

## References

* [Stacks Project, Tag 03BX](https://stacks.math.columbia.edu/tag/03BX)
* [Stacks Project, Tag 03I5](https://stacks.math.columbia.edu/tag/03I5)
* [Stacks Project, Tag 0A1A](https://stacks.math.columbia.edu/tag/0A1A)
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits Opposite

universe u v

namespace CategoryTheory.Limits

/-- Cutting a fibre product in two: the fibre product of `f` with `r = q ≫ g` is the fibre
product of the projection of the fibre product of `f` and `g` with `q`. -/
noncomputable def pullback_point_compIso {C : Type u} [Category.{u} C] [HasPullbacks C]
    {X Y Z W : C} (f : X ⟶ Y) (g : Z ⟶ Y) (q : W ⟶ Z) (r : W ⟶ Y) (h : q ≫ g = r) :
    pullback f r ≅ pullback (pullback.snd f g) q :=
  (pullback.congrHom rfl h).symm ≪≫ (pullbackLeftPullbackSndIso f g q).symm

end CategoryTheory.Limits

namespace CategoryTheory.OverShriek

/-- Equal pairs with the same factorization have equal sections. -/
private theorem eq_of_sigma_mk_eq {C : Type v} [Category.{u} C] {X T : C}
    (F : (Over T)ᵒᵖ ⥤ Type u) {χ : X ⟶ T} {s t : F.obj (op (Over.mk χ))}
    (h : (⟨χ, s⟩ : Σ χ : X ⟶ T, F.obj (op (Over.mk χ))) = ⟨χ, t⟩) : s = t :=
  eq_of_heq (Sigma.mk.inj h).2

/-- The structural morphism of the lower-shriek extension: a section of
`CategoryTheory.OverShriek.relocalizePresheafFunctor g` over `A` is a factorization of the
structure morphism of `A` through the source of `g` together with a section over that
factorization, and this morphism reads off the factorization. -/
def viewStructureMap {C : Type v} [Category.{u} C] {S T : C} (g : T ⟶ S)
    (F : (Over T)ᵒᵖ ⥤ Type u) :
    (relocalizePresheafFunctor g).obj F ⟶ yoneda.obj (Over.mk g) where
  app A := ↾fun s => Over.homMk s.1.1 s.2
  naturality {A A'} a := by
    ext s
    rfl

/-- The comparison morphism exhibiting the lower-shriek extension of a restriction as a base
change: a factorization through `T'` followed by `h` is in particular a factorization
through `T`. -/
def viewBaseChangeMap {C : Type v} [Category.{u} C] {S T T' : C} (g : T ⟶ S) (h : T' ⟶ T)
    (F : (Over T)ᵒᵖ ⥤ Type u) :
    (relocalizePresheafFunctor (h ≫ g)).obj ((relocalizeRestrict h).obj F) ⟶
      (relocalizePresheafFunctor g).obj F where
  app A := ↾fun s => ⟨⟨s.1.1 ≫ h, s.1.2⟩, (Category.assoc _ _ _).trans s.2⟩
  naturality {A A'} a := by
    ext s
    exact Subtype.ext (sigmaMk_eq F s.1.2 _ _ rfl)

/-- **Base change of the lower-shriek extension.** The lower-shriek extension along `h ≫ g`
of the restriction of `F` along `h` is the fibre product of the lower-shriek extension of `F`
along `g` with the shrinking `T' ⟶ T` of the base, taken over the representable presheaf
of `g`. -/
@[sga "3 I 1.6.1" "partial"]
theorem viewBaseChange_isPullback {C : Type v} [Category.{u} C] {S T T' : C} (g : T ⟶ S)
    (h : T' ⟶ T) (F : (Over T)ᵒᵖ ⥤ Type u) :
    IsPullback (viewBaseChangeMap g h F)
      (viewStructureMap (h ≫ g) ((relocalizeRestrict h).obj F))
      (viewStructureMap g F)
      (yoneda.map (Over.homMk h rfl : Over.mk (h ≫ g) ⟶ Over.mk g)) := by
  apply IsPullback.of_forall_isPullback_app
  intro A
  apply (Types.isPullback_iff _ _ _ _).mpr
  refine ⟨by ext s; rfl, ?_, ?_⟩
  · rintro ⟨⟨ψ, s⟩, hs⟩ ⟨⟨φ, t⟩, ht⟩ ⟨h₁, h₂⟩
    obtain rfl : ψ = φ := congrArg Over.Hom.left h₂
    apply Subtype.ext
    obtain rfl : s = t := eq_of_sigma_mk_eq F (congrArg Subtype.val h₁)
    rfl
  · rintro ⟨⟨ψ, s⟩, hs⟩ b hb
    obtain rfl : ψ = b.left ≫ h := congrArg Over.Hom.left hb
    exact ⟨⟨⟨b.left, s⟩, b.w⟩, rfl, Over.OverMorphism.ext rfl⟩

/-- **Base change of the lower-shriek extension**, as an isomorphism with the chosen fibre
product: once the lower-shriek extension of `F` along `g` is identified with a presheaf `Q`
over the representable presheaf of `g`, the lower-shriek extension of the restriction of `F`
along `h` is the fibre product of `Q` with the shrinking `T' ⟶ T` of the base. -/
@[sga "3 I 1.6.1" "partial"]
noncomputable def viewBaseChangeIso {C : Type v} [Category.{u} C] {S T T' : C} (g : T ⟶ S)
    (h : T' ⟶ T) (F : (Over T)ᵒᵖ ⥤ Type u) (Q : (Over S)ᵒᵖ ⥤ Type u)
    (π : Q ⟶ yoneda.obj (Over.mk g))
    (e : (relocalizePresheafFunctor g).obj F ≅ Q)
    (he : e.hom ≫ π = viewStructureMap g F) :
    (relocalizePresheafFunctor (h ≫ g)).obj ((relocalizeRestrict h).obj F) ≅
      pullback π (yoneda.map (Over.homMk h rfl : Over.mk (h ≫ g) ⟶ Over.mk g)) := by
  have hp' : IsPullback (viewBaseChangeMap g h F ≫ e.hom)
      (viewStructureMap (h ≫ g) ((relocalizeRestrict h).obj F))
      π (yoneda.map (Over.homMk h rfl : Over.mk (h ≫ g) ⟶ Over.mk g)) := by
    apply (viewBaseChange_isPullback g h F).of_iso' (Iso.refl _) e.symm (Iso.refl _) (Iso.refl _)
    · simp
    · simp
    · simpa using (congrArg (fun t => e.inv ≫ t) he).symm
    · simp
  exact hp'.isoPullback

end CategoryTheory.OverShriek

namespace AlgebraicGeometry.Space

/-- A section of the lower-shriek extension of `F` along `k : S ⟶ S'` over an object `A` of
the big fppf site of `S'` is a factorization `ψ` of the structure morphism of `A` through `S`
together with a section of `F` over `(A, ψ)`. -/
def relocalizedSectionEquiv (B : BigFppfSite.{u}) (S S' : Scheme.{u}) (hS : B.Contains S)
    (hS' : B.Contains S') (k : B.obj hS ⟶ B.obj hS')
    (F : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u) (A : BigFppfOver B S' hS') :
    ((OverShriek.relocalizePresheafFunctor k).obj F).obj (op A) ≃
      {p : Σ ψ : A.left ⟶ B.obj hS, F.obj (op (Over.mk ψ)) // p.1 ≫ k = A.hom} := by
  dsimp [OverShriek.relocalizePresheafFunctor, OverShriek.presheaf,
    OverShriek.presheafFunctor, OverShriek.presheafFunctorToOver, OverShriek.fiberFunctor,
    OverShriek.fiber, OverShriek.presheafToYoneda, Functor.toOver,
    Functor.toCostructuredArrow]
  exact {
    toFun := fun x => ⟨x.1, by simpa using x.2⟩
    invFun := fun x => ⟨x.1, by simpa using x.2⟩
    left_inv _ := rfl
    right_inv _ := rfl }

variable (B : BigFppfSite.{u}) (S Z : Scheme.{u}) (hS : B.Contains S) (hZ : B.Contains Z)

/-- A field-valued point of `F` read as a field-valued point of the lower-shriek extension of
`F` along `g`: the same field spectrum, with its structure morphism composed with `g`. -/
noncomputable def relocalizedFieldPoint (g : B.obj hS ⟶ B.obj hZ)
    (F : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u) (p : FieldValuedPoint B S hS F) :
    FieldValuedPoint B Z hZ ((OverShriek.relocalizePresheafFunctor g).obj F) := by
  classical
  refine { carrier := p.carrier, field := p.field, contained := p.contained
           toBase := B.inclusion.map (p.siteObject.hom ≫ g), value := ?_ }
  let A : BigFppfOver B Z hZ := (Over.map g).obj p.siteObject
  change ((OverShriek.relocalizePresheafFunctor g).obj F).obj (op A)
  exact (relocalizedSectionEquiv B S Z hS hZ g F A).symm
    ⟨⟨p.siteObject.hom, p.value⟩, rfl⟩

/-- A field-valued point of the lower-shriek extension of `F` along `g` read as a field-valued
point of `F`: the factorization of its structure morphism through `S` carried by the section
is the structure morphism of the point of `F`. -/
noncomputable def originalFieldPoint (g : B.obj hS ⟶ B.obj hZ)
    (F : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u)
    (p : FieldValuedPoint B Z hZ ((OverShriek.relocalizePresheafFunctor g).obj F)) :
    FieldValuedPoint B S hS F := by
  classical
  let z := relocalizedSectionEquiv B S Z hS hZ g F p.siteObject p.value
  refine { carrier := p.carrier, field := p.field, contained := p.contained
           toBase := B.inclusion.map z.1.1, value := ?_ }
  change F.obj (op (Over.mk z.1.1))
  exact z.1.2

/-- Reading a field-valued point of `F` as one of the lower-shriek extension preserves
domination. -/
theorem dominates_relocalizedFieldPoint (g : B.obj hS ⟶ B.obj hZ)
    (F : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u) {p q : FieldValuedPoint B S hS F}
    (h : p.Dominates B S hS F q) :
    (relocalizedFieldPoint B S Z hS hZ g F p).Dominates B Z hZ _
      (relocalizedFieldPoint B S Z hS hZ g F q) := by
  obtain ⟨a, ha⟩ := h
  refine ⟨(Over.map g).map a, ?_⟩
  apply Subtype.ext
  change (⟨_, F.map (Over.homMk a.left rfl :
      Over.mk (a.left ≫ q.siteObject.hom) ⟶ q.siteObject).op q.value⟩ :
    Σ t : (B.obj p.contained) ⟶ B.obj hS, F.obj (op (Over.mk t))) =
    ⟨p.siteObject.hom, p.value⟩
  rw [← ha]
  exact OverShriek.sigmaMk_eq F q.value _ a rfl

/-- Reading a field-valued point of the lower-shriek extension as one of `F` preserves
domination. -/
theorem dominates_originalFieldPoint (g : B.obj hS ⟶ B.obj hZ)
    (F : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u)
    {p q : FieldValuedPoint B Z hZ ((OverShriek.relocalizePresheafFunctor g).obj F)}
    (h : p.Dominates B Z hZ _ q) :
    (originalFieldPoint B S Z hS hZ g F p).Dominates B S hS F
      (originalFieldPoint B S Z hS hZ g F q) := by
  obtain ⟨a, ha⟩ := h
  have hi : a.left ≫ q.value.1.1 = p.value.1.1 := congrArg (fun z => z.1.1) ha
  let b : (originalFieldPoint B S Z hS hZ g F p).siteObject ⟶
      (originalFieldPoint B S Z hS hZ g F q).siteObject := Over.homMk a.left hi
  refine ⟨b, ?_⟩
  have ht := OverShriek.sigmaMk_eq F q.value.1.2
    (Over.homMk a.left rfl : Over.mk (a.left ≫ q.value.1.1) ⟶ Over.mk q.value.1.1) b rfl
  exact OverShriek.eq_of_sigma_mk_eq F (ht.symm.trans (congrArg Subtype.val ha))

/-- The map on point sets induced by reading a presheaf on the big fppf site of `S` as one on
the big fppf site of `Z`. -/
noncomputable def relocalizedPointsMap (g : B.obj hS ⟶ B.obj hZ)
    (F : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u) :
    points B S hS F → points B Z hZ ((OverShriek.relocalizePresheafFunctor g).obj F) :=
  Quot.map (relocalizedFieldPoint B S Z hS hZ g F) (by
    rintro p q ⟨r, hp, hq⟩
    exact ⟨relocalizedFieldPoint B S Z hS hZ g F r,
      dominates_relocalizedFieldPoint B S Z hS hZ g F hp,
      dominates_relocalizedFieldPoint B S Z hS hZ g F hq⟩)

/-- The map on point sets induced by reading a presheaf on the big fppf site of `Z` lying over
`g` as one on the big fppf site of `S`. -/
noncomputable def originalPointsMap (g : B.obj hS ⟶ B.obj hZ)
    (F : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u) :
    points B Z hZ ((OverShriek.relocalizePresheafFunctor g).obj F) → points B S hS F :=
  Quot.map (originalFieldPoint B S Z hS hZ g F) (by
    rintro p q ⟨r, hp, hq⟩
    exact ⟨originalFieldPoint B S Z hS hZ g F r,
      dominates_originalFieldPoint B S Z hS hZ g F hp,
      dominates_originalFieldPoint B S Z hS hZ g F hq⟩)

/-- Every point of the lower-shriek extension comes from a point of `F`: the factorization
carried by a section is itself a field-valued point of `F`. -/
theorem relocalizedPointsMap_surjective (g : B.obj hS ⟶ B.obj hZ)
    (F : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u) :
    Function.Surjective (relocalizedPointsMap B S Z hS hZ g F) := by
  intro p
  induction p using Quot.inductionOn with | h p =>
  let q := originalFieldPoint B S Z hS hZ g F p
  refine ⟨q.class B S hS F, ?_⟩
  apply Quot.sound
  let r := relocalizedFieldPoint B S Z hS hZ g F q
  refine ⟨r, FieldValuedPoint.dominates_refl _ _ _ _ r, ?_⟩
  let a : r.siteObject ⟶ p.siteObject := Over.homMk (𝟙 _) (by
    apply ObjectProperty.hom_ext
    change (𝟙 _) ≫ p.toBase = _
    simp only [Category.id_comp]
    exact congrArg (fun t => B.inclusion.map t)
      (relocalizedSectionEquiv B S Z hS hZ g F p.siteObject p.value).2.symm)
  exact ⟨a, Subtype.ext (OverShriek.sigmaMk_eq_self F _ _ rfl)⟩

/-- Reading a point of `F` as a point of the lower-shriek extension is injective:
`AlgebraicGeometry.Space.originalPointsMap` is a left inverse. -/
theorem relocalizedPointsMap_injective (g : B.obj hS ⟶ B.obj hZ)
    (F : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u) :
    Function.Injective (relocalizedPointsMap B S Z hS hZ g F) := by
  apply Function.LeftInverse.injective (g := originalPointsMap B S Z hS hZ g F)
  intro x
  induction x using Quot.inductionOn with | h p => rfl

/-- The transport of points along a change of base scheme is natural in the presheaf. -/
theorem relocalizedPointsMap_naturality (g : B.obj hS ⟶ B.obj hZ)
    {F G : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u} (a : F ⟶ G) (x : points B S hS F) :
    relocalizedPointsMap B S Z hS hZ g G (pointsMap B S hS F a x) =
      pointsMap B Z hZ _ ((OverShriek.relocalizePresheafFunctor g).map a)
        (relocalizedPointsMap B S Z hS hZ g F x) := by
  induction x using Quot.inductionOn with | h p => rfl

/-- **Stacks 03BU for a change of base scheme.** The points of a presheaf on the big fppf site
of `S` are the points of its lower-shriek extension to the big fppf site of `Z`. -/
noncomputable def relocalizedPointsEquiv (g : B.obj hS ⟶ B.obj hZ)
    (F : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u) :
    points B S hS F ≃ points B Z hZ ((OverShriek.relocalizePresheafFunctor g).obj F) :=
  Equiv.ofBijective _ ⟨relocalizedPointsMap_injective B S Z hS hZ g F,
    relocalizedPointsMap_surjective B S Z hS hZ g F⟩

/-- Every morphism of the big fppf site of `Z` out of the lower-shriek extension of a
representable presheaf comes from a morphism of the big fppf site of `S`: the section
corresponding to it under Yoneda carries a factorization of the structure morphism, and that
factorization represents the source. -/
theorem exists_relocalized_yoneda_factorization (g : B.obj hS ⟶ B.obj hZ)
    (F : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u) (W : BigFppfOver B Z hZ)
    (a : yoneda.obj W ⟶ (OverShriek.relocalizePresheafFunctor g).obj F) :
    ∃ (U : BigFppfOver B S hS) (e : W ≅ (Over.map g).obj U) (b : yoneda.obj U ⟶ F),
      a = yoneda.map e.hom ≫ (relocalizedYonedaIso B (B.obj hS) (B.obj hZ) g U).inv ≫
        (OverShriek.relocalizePresheafFunctor g).map b := by
  let x := yonedaEquiv a
  let U : BigFppfOver B S hS := Over.mk x.1.1
  let e : W ≅ (Over.map g).obj U := Over.isoMk (Iso.refl _) x.2
  refine ⟨U, e, yonedaEquiv.symm x.1.2, ?_⟩
  apply yonedaEquiv.injective
  change x = _
  apply Subtype.ext
  change x.1 = ⟨_, F.map
    (Over.homMk (𝟙 W.left) rfl : Over.mk ((𝟙 W.left) ≫ x.1.1) ⟶ U).op x.1.2⟩
  exact (OverShriek.sigmaMk_eq_self F x.1.2 _ rfl).symm

/-- A relative property of morphisms of presheaves survives the lower-shriek extension, as
long as the property of scheme morphisms respects isomorphisms: a morphism out of a
representable presheaf into an extension factors through the extension of a representable
presheaf, so the representing fibre product can be formed on the big fppf site of `S` and
then extended. -/
theorem presheaf_relocalized (g : B.obj hS ⟶ B.obj hZ) (P : MorphismProperty Scheme.{u})
    [P.RespectsIso] {F G : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u} (a : F ⟶ G)
    (ha : (P.inverseImage (BigFppfOver.toScheme B S hS)).presheaf a) :
    (P.inverseImage (BigFppfOver.toScheme B Z hZ)).presheaf
      ((OverShriek.relocalizePresheafFunctor g).map a) := by
  let R := OverShriek.relocalizePresheafFunctor g
  have _ : PreservesLimitsOfShape WalkingCospan R :=
    relocalizePresheaf_preservesConnectedLimits g
  apply MorphismProperty.relative.of_exists
  intro W b
  obtain ⟨U, e, b', rfl⟩ := exists_relocalized_yoneda_factorization B S Z hS hZ g G W b
  let V := ha.rep.pullback b'
  let v := ha.rep.snd b'
  let c := ha.rep.fst b'
  let iU := (relocalizedYonedaIso B (B.obj hS) (B.obj hZ) g U).symm
  let iV := (relocalizedYonedaIso B (B.obj hS) (B.obj hZ) g V).symm
  refine ⟨(Over.map g).obj V, iV.hom ≫ R.map c, (Over.map g).map v ≫ e.inv, ?_, ?_⟩
  · apply ((ha.rep.isPullback b').map R).of_iso' iV (Iso.refl _)
      (yoneda.mapIso e ≪≫ iU) (Iso.refl _)
    · simp [c]
    · dsimp [iV, iU]
      rw [yoneda.map_comp]
      simp only [Category.assoc, ← Functor.map_comp_assoc, e.inv_hom_id]
      rw [Category.comp_id, Iso.inv_comp_eq, ← Category.assoc,
        ← relocalizedYonedaIso_naturality B (B.obj hS) (B.obj hZ) g v, Category.assoc,
        Iso.hom_inv_id, Category.comp_id]
    · simp [R]
    · simp [iU, R, Category.assoc]
  · change P ((BigFppfOver.toScheme B Z hZ).map ((Over.map g).map v ≫ e.inv))
    rw [Functor.map_comp]
    exact MorphismProperty.RespectsIso.postcomp P
      ((BigFppfOver.toScheme B Z hZ).map e.inv) _ (ha.property_snd b')

/-- The point topologies of the lower-shriek extensions, pulled back along
`AlgebraicGeometry.Space.relocalizedPointsEquiv`, form a family of topologies on the points of
the algebraic spaces over `S` satisfying the three conditions of Stacks 03BX. -/
noncomputable def relocalizedPointTopologyFamily (g : B.obj hS ⟶ B.obj hZ) :
    PointTopologyFamily B S hS := by
  let L := OverShriek.relocalizePresheafFunctor g
  let hL := isAlgebraicSpace_viewOver B S Z hS hZ g
  let τ := fun F : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u => pointTopology B Z hZ (L.obj F)
  let E := relocalizedPointsEquiv B S Z hS hZ g
  let t := fun (F : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u) (_ : IsAlgebraicSpace B S hS F) =>
    TopologicalSpace.induced (E F) (τ F)
  let H := fun F : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u => @Equiv.homeomorph _ _ (τ F) (E F)
  refine ⟨t, ?_, ?_, ?_⟩
  · intro U W
    let hU := isAlgebraicSpace_yoneda B S hS U
    let U' := (Over.map g).obj U
    let i := (relocalizedYonedaIso B (B.obj hS) (B.obj hZ) g U).symm
    let _ := t (yoneda.obj U) hU
    let _ := τ (yoneda.obj U)
    let _ := pointTopology B Z hZ (yoneda.obj U')
    let e := (H _).trans (pointsHomeomorphOfIso B Z hZ i).symm
    have he' (q : FieldValuedPoint B Z hZ (yoneda.obj U')) :
        schemePoint B S hS U (originalFieldPoint B S Z hS hZ g _
            (FieldValuedPoint.map B Z hZ _ i.hom q)) = schemePoint B Z hZ U' q :=
      rfl
    have eqp (q : FieldValuedPoint B Z hZ (yoneda.obj U')) :
        e.symm q.class = (originalFieldPoint B S Z hS hZ g _
            (FieldValuedPoint.map B Z hZ _ i.hom q)).class := by
      apply (E _).injective
      change (E _) ((E _).symm _) = _
      rw [Equiv.apply_symm_apply]
      have hl : Function.LeftInverse (originalPointsMap B S Z hS hZ g (yoneda.obj U))
          (E (yoneda.obj U)) := by
        intro x
        induction x using Quot.inductionOn with | h p => rfl
      exact (Function.LeftInverse.rightInverse_of_surjective hl (E _).surjective _).symm
    constructor
    · intro hW
      have ho := e.isOpenMap W hW
      obtain ⟨V, hV, hv⟩ := (pointTopologyFamily B Z hZ).scheme U' _ |>.mp ho
      refine ⟨V, hV, fun p => ?_⟩
      let q := FieldValuedPoint.map B Z hZ _ i.inv (relocalizedFieldPoint B S Z hS hZ g _ p)
      have hvq := hv q
      change (e p.class ∈ e '' W ↔ schemePoint B S hS U p ∈ V) at hvq
      simpa only [Set.mem_image, e.injective.eq_iff, exists_eq_right] using hvq
    · rintro ⟨V, hV, hv⟩
      have ho : @IsOpen _ (pointTopology B Z hZ (yoneda.obj U')) (e '' W) := by
        apply (pointTopologyFamily B Z hZ).scheme U' _ |>.mpr
        refine ⟨V, hV, fun q => ?_⟩
        rw [show q.class ∈ e '' W ↔ e.symm q.class ∈ W from
          ⟨by rintro ⟨x, hx, heq⟩; rw [← heq]; simpa using hx,
            fun h => ⟨e.symm _, h, e.apply_symm_apply _⟩⟩, eqp q]
        exact (hv _).trans (by rw [he' q])
      exact e.isOpen_image.mp ho
  · intro F G hF hG a
    let _ := t F hF
    let _ := t G hG
    let _ := τ F
    let _ := τ G
    have heq : pointsMap B S hS F a =
        (H G).symm ∘ pointsMap B Z hZ _ (L.map a) ∘ (H F) := by
      funext x
      exact (((E G).symm_apply_eq).mpr
        (relocalizedPointsMap_naturality B S Z hS hZ g a x).symm).symm
    rw [heq]
    exact (H G).symm.continuous.comp
      ((continuous_pointsMap B Z hZ (L.map a)).comp (H F).continuous)
  · intro F hF U a ha
    let hU := isAlgebraicSpace_yoneda B S hS U
    let U' := (Over.map g).obj U
    let i := (relocalizedYonedaIso B (B.obj hS) (B.obj hZ) g U).symm
    let _ := t F hF
    let _ := t (yoneda.obj U) hU
    let _ := τ F
    let _ := τ (yoneda.obj U)
    let _ := pointTopology B Z hZ (yoneda.obj U')
    let _ : MorphismProperty.RespectsIso (@Etale.{u}) :=
      MorphismProperty.IsStableUnderBaseChange.respectsIso
    have hLa := presheaf_relocalized B S Z hS hZ g (@Etale.{u}) a ha
    have hia : (MorphismProperty.inverseImage (@Etale.{u})
        (BigFppfOver.toScheme B Z hZ)).presheaf (i.hom ≫ L.map a) :=
      MorphismProperty.RespectsIso.precomp _ i.hom _ hLa
    have ho := (pointTopologyFamily B Z hZ).etale_isOpenMap (hL _ hF) U' (i.hom ≫ L.map a) hia
    have heq : pointsMap B S hS _ a =
        (H F).symm ∘ pointsMap B Z hZ _ (i.hom ≫ L.map a) ∘
          (pointsHomeomorphOfIso B Z hZ i).symm ∘ (H _) := by
      funext x
      simp only [Function.comp_apply, pointsMap_comp_apply]
      change _ = (E F).symm
        (pointsMap B Z hZ _ (L.map a) (pointsMap B Z hZ _ i.hom
          (pointsMap B Z hZ _ i.inv ((E _) x))))
      rw [← pointsMap_comp_apply B Z hZ i.inv i.hom, i.inv_hom_id, pointsMap_id, id_eq]
      exact (((E F).symm_apply_eq).mpr
        (relocalizedPointsMap_naturality B S Z hS hZ g a x).symm).symm
    rw [heq]
    exact (H F).symm.isOpenMap.comp
      (ho.comp ((pointsHomeomorphOfIso B Z hZ i).symm.isOpenMap.comp (H _).isOpenMap))

/-- **Stacks 03BX for a change of base scheme.** The canonical bijection between the points of
an algebraic space over `S` and the points of its lower-shriek extension to the big fppf site
of `Z` is a homeomorphism for the point topologies.

The transported topologies form a family satisfying the three conditions of Stacks 03BX, and
by the uniqueness in that tag the family is the point topology. -/
noncomputable def relocalizedPointsHomeomorph (g : B.obj hS ⟶ B.obj hZ)
    (F : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u) (hF : IsAlgebraicSpace B S hS F) :
    @Homeomorph (points B S hS F)
      (points B Z hZ ((OverShriek.relocalizePresheafFunctor g).obj F))
      (pointTopology B S hS F)
      (pointTopology B Z hZ ((OverShriek.relocalizePresheafFunctor g).obj F)) := by
  have he : pointTopologyFamily B S hS = relocalizedPointTopologyFamily B S Z hS hZ g :=
    PointTopologyFamily.eq B S hS _ _
  have ht := congrArg (fun T : PointTopologyFamily B S hS => T.topology F hF) he
  letI := pointTopology B Z hZ ((OverShriek.relocalizePresheafFunctor g).obj F)
  change @Homeomorph _ _ ((pointTopologyFamily B S hS).topology F hF) _
  rw [ht]
  exact (relocalizedPointsEquiv B S Z hS hZ g F).homeomorph

end AlgebraicGeometry.Space

end
