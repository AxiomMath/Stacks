module

public import StacksFrontier.Algebra.Category.ModuleCat.Sheaf.RingedToposTwoIsoUnitor
public import StacksFrontier.AlgebraicGeometry.Spaces.RepresentedSmallEtaleRingedToposTransport

/-!
# Conjugating a morphism of ringed topoi by the identification of the two readings of a chart

An object `U` of a big fppf site over `S` is at once a chart of the representable algebraic
space `yoneda.obj U` and a scheme of the big étale site
`AlgebraicGeometry.associatedBigEtaleSite B`, and
`AlgebraicGeometry.Space.representedSmallEtaleRingedToposHom` identifies the two readings of its
small étale ringed topos.  `AlgebraicGeometry.Space.schemeOfRepresentedRingedToposHom`
*conjugates* a morphism of the small étale ringed topoi of two representable algebraic spaces
into a morphism of the small étale ringed topoi of the two schemes, and the naturality square
`AlgebraicGeometry.Space.representedSmallEtaleRingedToposNaturality` says the identification is
natural in the chart.

This file says that the conjugation is invertible up to 2-isomorphism, and reads the naturality
square in conjugated form.  Both are what a consumer of Stacks 04KL needs: the recovery
theorems of `StacksFrontier/AlgebraicGeometry/EtaleCohomology/RecoveringMorphisms/` live over the
big étale site, so they are applied to the *conjugate* of a morphism of ringed topoi produced
over a big fppf site, and the 2-isomorphism they return has to be carried back to the
algebraic-spaces side.

## Main definitions

* `AlgebraicGeometry.RingedToposHom.TwoIso.ofInverseImageIsoForget`:
  `AlgebraicGeometry.RingedToposHom.TwoIso.ofInverseImageIso` with its compatibility condition
  read on underlying sheaves of sets.
* `AlgebraicGeometry.RingedToposHom.TwoIso.conjugateOfSquare` and `.conjugateUnconjugate`: the
  two generic computations in the 2-category of ringed topoi that the file runs on, with the
  four ringed topoi and all five morphisms as variables.
* `AlgebraicGeometry.Space.spaceOfSchemeRingedToposHom` and
  `…twoIsoSpaceOfSchemeRingedToposHom`: the conjugation inverse to
  `AlgebraicGeometry.Space.schemeOfRepresentedRingedToposHom`, and its action on
  2-isomorphisms.

## Main results

* `AlgebraicGeometry.Space.representedSmallEtaleRingedToposCompInverse` and
  `…InverseComp`: **the identification is an equivalence in the 2-category of ringed topoi** —
  both composites of the identification with the identification read from the other side are
  2-isomorphic to the identity morphism of ringed topoi.
* `AlgebraicGeometry.Space.twoIsoSpaceOfSchemeOfRepresentedRingedToposHom`: conjugating and
  conjugating back recovers a morphism up to 2-isomorphism.
* `AlgebraicGeometry.Space.reflectTwoIsoSchemeOfRepresentedRingedToposHom`: **a 2-isomorphism
  of the conjugates is reflected back to a 2-isomorphism of the originals.**
* `AlgebraicGeometry.Space.twoIsoSchemeOfSmallEtaleRingedToposHom`: **the conjugated naturality
  square** — the conjugate of the morphism of small étale ringed topoi of a represented
  morphism of algebraic spaces *is* the morphism of small étale ringed topoi of the underlying
  morphism of schemes, up to 2-isomorphism.
* `AlgebraicGeometry.Space.reflectTwoIsoSmallEtaleRingedToposHom`: the two previous results
  combined, which is the form Stacks 04KL consumes.

## Implementation notes

**No new geometry enters.**  The only geometric input of the naturality square is
`AlgebraicGeometry.Space.representedSmallEtaleBaseChangeComponent_inv_comp_snd`, and that is
already discharged in
`StacksFrontier/AlgebraicGeometry/Spaces/RepresentedSmallEtaleRingedToposTransport.lean`.
Everything here is the 2-category calculus of `AlgebraicGeometry.RingedToposHom.TwoIso` —
`associator`, `whiskerLeft`, `whiskerRight` and the two unitors of
`StacksFrontier/Algebra/Category/ModuleCat/Sheaf/RingedToposTwoIsoUnitor.lean` — together with the
two statements that the identification's two composites are 2-isomorphic to the identity.

Those two are both instances of
`AlgebraicGeometry.RingedToposHom.TwoIso.ofInverseImageIsoForget` on the unit, respectively the
counit, of `AlgebraicGeometry.Space.representedSmallEtaleSheafCongr`.  The *direct* images of
the identifications are `CategoryTheory.Functor.inv` of a restriction — a quasi-inverse produced
by `CategoryTheory.Functor.objPreimage`, hence by choice — so they have no description on
sections and the direct-image form of the comparison is not available; the inverse images, by
contrast, are restriction along the equivalence of sites and along its inverse on the nose, and
their comparison is the unit respectively the counit of
`CategoryTheory.Equivalence.sheafCongr`.  Both of those are the identity at the structure sheaf
by `rfl`, because the counit of the equivalence of *sites* is the identity
(`AlgebraicGeometry.Space.representedSmallEtaleEquivalence_counit_app`).

Two measurements worth keeping.  The compatibility condition of
`AlgebraicGeometry.RingedToposHom.TwoIso.ofInverseImageIso` is stated through
`X.forgetRing.map p.fSharpInverseImage`, whose type goes through the inverse image *of
commutative rings* along the morphism of topoi; at a composite morphism that exhausts the
elaborator's budget at `isDefEq`, while the same condition read on sheaves of sets costs
nothing — hence `…ofInverseImageIsoForget`.  And `rw [Category.comp_id]` cannot fire on the
resulting goal (the target is not type-correct at `implicit` transparency once the composite's
structure map has been rewritten), so the last step is a term-mode `Category.comp_id`.

Nothing here states a whole Stacks tag, so nothing here is registered.

## References

* [Stacks Project, Tag 03ED](https://stacks.math.columbia.edu/tag/03ED)
* [Stacks Project, Definition 18.2.2 (Tag 04IC)](https://stacks.math.columbia.edu/tag/04IC)
* [Stacks Project, Tag 04KL](https://stacks.math.columbia.edu/tag/04KL)
* [Stacks Project, Tag 04M6](https://stacks.math.columbia.edu/tag/04M6)
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits
open Stacks.Sheaves.ToposPullback Stacks.Sheaves.ToposPushforward

universe u

namespace AlgebraicGeometry.RingedToposHom

universe v₁ u₁ w₁ v₂ u₂

section Id

variable (X : RingedTopos.{v₁, u₁, w₁})
  [X.J.HasSheafCompose (forget RingCat.{w₁})]
  [X.J.HasSheafCompose (forget₂ CommRingCat.{w₁} RingCat.{w₁})]

/-- The inverse-image form of the structure map of the identity morphism of a ringed topos,
read on underlying sheaves of sets, is the identity. -/
theorem fSharpInverseImageForget_id :
    (RingedToposHom.id X).fSharpInverseImageForget = 𝟙 (X.forgetRing.obj X.O) := by
  refine Eq.trans ?_ (Category.id_comp _)
  refine Eq.trans ?_ (congrArg (fun m ↦ (𝟭 X.Topos).map m ≫ Adjunction.id.counit.app _)
    (forgetRing_map_id_fSharp X))
  rfl

end Id

section OfInverseImageIsoForget

variable {X : RingedTopos.{v₁, u₁, w₁}} {Y : RingedTopos.{v₂, u₂, w₁}}
  [X.J.HasSheafCompose (forget RingCat.{w₁})]
  [Y.J.HasSheafCompose (forget RingCat.{w₁})]
  [X.J.HasSheafCompose (forget₂ CommRingCat.{w₁} RingCat.{w₁})]
  [Y.J.HasSheafCompose (forget₂ CommRingCat.{w₁} RingCat.{w₁})]

/-- **`AlgebraicGeometry.RingedToposHom.TwoIso.ofInverseImageIso` with its compatibility
condition read through `AlgebraicGeometry.RingedToposHom.fSharpInverseImageForget`.**

The original form states the condition as an equation between composites of
`X.forgetRing.map p.fSharpInverseImage`, whose very type goes through
`Stacks.Sheaves.ToposPullback.inverseImageCommRingFunctor` of the morphism of topoi; the
spelling here stays among sheaves of sets throughout.  That matters at an instantiation where
the two morphisms are composites: deciding the type of the inverse image of commutative rings
along a composite morphism of topoi is what exhausts the elaborator's budget, while the
corresponding statement for sheaves of sets costs nothing. -/
noncomputable def TwoIso.ofInverseImageIsoForget {p q : RingedToposHom X Y}
    (α : q.toToposHom.inverseImage ≅ p.toToposHom.inverseImage)
    (h : α.hom.app (Y.forgetRing.obj Y.O) ≫ p.fSharpInverseImageForget =
      q.fSharpInverseImageForget) :
    TwoIso p q :=
  TwoIso.ofInverseImageIso α
    (((congrArg (fun m ↦ α.hom.app (Y.forgetRing.obj Y.O) ≫ m)
          (forgetRing_map_fSharpInverseImage_eq_fSharpInverseImageForget p)).trans h).trans
      (forgetRing_map_fSharpInverseImage_eq_fSharpInverseImageForget q).symm)

/-- A functor sends `u = 𝟙` followed by `v = 𝟙` to the identity: `F.map u ≫ v = 𝟙`. -/
private theorem map_comp_eq_id_of_eq_id {C D : Type*} [Category C] [Category D] (F : C ⥤ D)
    {A : C} {u : A ⟶ A} {v : F.obj A ⟶ F.obj A} (hu : u = 𝟙 A) (hv : v = 𝟙 _) :
    F.map u ≫ v = 𝟙 _ := by
  rw [hu, hv, F.map_id, Category.id_comp]

end OfInverseImageIsoForget

/-! ### Conjugating a morphism of ringed topoi by an equivalence

Two generic computations in the 2-category of ringed topoi, done once with the four ringed
topoi, the five morphisms and both 2-isomorphisms as variables.  Each is a chain of
`AlgebraicGeometry.RingedToposHom.TwoIso.associator`, `.whiskerLeft`, `.whiskerRight` and the
two unitors, and nothing else; at a geometric instantiation every argument is then an existing
2-isomorphism applied verbatim. -/

section Conjugation

universe vP uP wP vQ uQ wQ vR uR wR vT uT wT

variable {P : RingedTopos.{vP, uP, wP}} {Q : RingedTopos.{vQ, uQ, wQ}}
  {R : RingedTopos.{vR, uR, wR}} {T : RingedTopos.{vT, uT, wT}}
  [P.J.HasSheafCompose (forget RingCat.{wP})]
  [Q.J.HasSheafCompose (forget RingCat.{wQ})]
  [R.J.HasSheafCompose (forget RingCat.{wR})]
  [T.J.HasSheafCompose (forget RingCat.{wT})]
  [P.J.HasSheafCompose (forget₂ CommRingCat.{wP} RingCat.{wP})]
  [Q.J.HasSheafCompose (forget₂ CommRingCat.{wQ} RingCat.{wQ})]
  [R.J.HasSheafCompose (forget₂ CommRingCat.{wR} RingCat.{wR})]
  [T.J.HasSheafCompose (forget₂ CommRingCat.{wT} RingCat.{wT})]

/-- **A commuting square of ringed topoi, transposed across an equivalence.**  Let
`a : P ⟶ Q` and `a' : Q ⟶ P` be morphisms of ringed topoi with `a ∘ a'` 2-isomorphic to the
identity of `Q`.  Then a 2-isomorphism `b ∘ ψ ≅ f ∘ a` gives one `b ∘ ψ ∘ a' ≅ f`: the
conjugate of `ψ` is 2-isomorphic to `f`.

Only `a ∘ a' ≅ 1_Q` is needed, not the other triangle, and neither `a` nor `a'` has to be
invertible in any stronger sense. -/
noncomputable def TwoIso.conjugateOfSquare {a : RingedToposHom P Q} {a' : RingedToposHom Q P}
    {ψ : RingedToposHom P R} {b : RingedToposHom R T} {f : RingedToposHom Q T}
    (N : TwoIso (b.comp ψ) (f.comp a))
    (η : TwoIso (a.comp a') (RingedToposHom.id Q)) :
    TwoIso (b.comp (ψ.comp a')) f :=
  (TwoIso.associator a' ψ b).trans
    ((TwoIso.whiskerLeft a' N).trans
      ((TwoIso.associator a' a f).symm.trans
        ((TwoIso.whiskerRight η f).trans (TwoIso.compId f))))

/-- **Conjugating a morphism of ringed topoi and conjugating back recovers it up to
2-isomorphism.**  With `a' ∘ a` 2-isomorphic to the identity of `P` and `b' ∘ b` to the identity
of `R`, the double conjugate `b' ∘ (b ∘ ψ ∘ a') ∘ a` of `ψ : P ⟶ R` is 2-isomorphic to `ψ`.

This is what reflects a 2-isomorphism of conjugates back to one of the originals: conjugation
is functorial on 2-isomorphisms (two whiskerings), and this says the round trip is the
identity. -/
noncomputable def TwoIso.conjugateUnconjugate {a : RingedToposHom P Q}
    {a' : RingedToposHom Q P} {b : RingedToposHom R T} {b' : RingedToposHom T R}
    (ψ : RingedToposHom P R)
    (ηa : TwoIso (a'.comp a) (RingedToposHom.id P))
    (ηb : TwoIso (b'.comp b) (RingedToposHom.id R)) :
    TwoIso (b'.comp ((b.comp (ψ.comp a')).comp a)) ψ :=
  (TwoIso.whiskerRight (TwoIso.associator a (ψ.comp a') b).symm b').trans
    ((TwoIso.associator ((ψ.comp a').comp a) b b').trans
      ((TwoIso.whiskerLeft ((ψ.comp a').comp a) ηb).trans
        ((TwoIso.idComp ((ψ.comp a').comp a)).trans
          ((TwoIso.associator a a' ψ).symm.trans
            ((TwoIso.whiskerRight ηa ψ).trans (TwoIso.compId ψ))))))

end Conjugation

end AlgebraicGeometry.RingedToposHom

namespace AlgebraicGeometry.Space

variable (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S) (U : BigFppfOver B S hS)

/-- **The structure map of the identification read from the scheme side, in inverse-image form,
is the identity on underlying sheaves of sets.** -/
theorem forgetRing_map_representedSmallEtaleRingedToposInverse_fSharpInverseImage :
    (_root_.AlgebraicGeometry.RingedSite.toRingedTopos
        (_root_.AlgebraicGeometry.smallEtaleRingedSite (associatedBigEtaleSite B)
          ((BigFppfOver.toScheme B S hS).obj U) U.left.property)).forgetRing.map
        (representedSmallEtaleRingedToposInverse B S hS U).fSharpInverseImage = 𝟙 _ := by
  rw [representedSmallEtaleRingedToposInverse_fSharpInverseImage]
  rfl

/-- The same, in the spelling `AlgebraicGeometry.RingedToposHom.fSharpInverseImageForget`. -/
theorem representedSmallEtaleRingedToposInverse_fSharpInverseImageForget :
    (representedSmallEtaleRingedToposInverse B S hS U).fSharpInverseImageForget =
      𝟙 ((_root_.AlgebraicGeometry.RingedSite.toRingedTopos
          (_root_.AlgebraicGeometry.smallEtaleRingedSite (associatedBigEtaleSite B)
            ((BigFppfOver.toScheme B S hS).obj U) U.left.property)).forgetRing.obj
        (_root_.AlgebraicGeometry.RingedSite.toRingedTopos
          (_root_.AlgebraicGeometry.smallEtaleRingedSite (associatedBigEtaleSite B)
            ((BigFppfOver.toScheme B S hS).obj U) U.left.property)).O) :=
  (RingedToposHom.forgetRing_map_fSharpInverseImage_eq_fSharpInverseImageForget
      (representedSmallEtaleRingedToposInverse B S hS U)).symm.trans
    (forgetRing_map_representedSmallEtaleRingedToposInverse_fSharpInverseImage B S hS U)

/-- **The counit of the equivalence of the two small étale sheaf topoi of a chart is the
identity at the structure sheaf of the scheme.**  The counit of the equivalence of sites is the
identity (`AlgebraicGeometry.Space.representedSmallEtaleEquivalence_counit_app`), so restricting
the regular functions along it changes nothing. -/
theorem representedSmallEtaleSheafCongr_counitIso_inv_structureSheaf :
    (representedSmallEtaleSheafCongr B S hS U).counitIso.inv.app
        ((_root_.AlgebraicGeometry.RingedSite.toRingedTopos
            (_root_.AlgebraicGeometry.smallEtaleRingedSite (associatedBigEtaleSite B)
              ((BigFppfOver.toScheme B S hS).obj U) U.left.property)).forgetRing.obj
          (_root_.AlgebraicGeometry.RingedSite.toRingedTopos
            (_root_.AlgebraicGeometry.smallEtaleRingedSite (associatedBigEtaleSite B)
              ((BigFppfOver.toScheme B S hS).obj U) U.left.property)).O) = 𝟙 _ :=
  rfl

/-- **The unit of the equivalence of the two small étale sheaf topoi of a chart is the identity
at the structure sheaf of the algebraic space.**  This is
`AlgebraicGeometry.Space.representedSmallEtaleRestrictionAdjunction_counit_structureSheaf` read
on the forward direction of the unit isomorphism. -/
theorem representedSmallEtaleSheafCongr_unitIso_hom_structureSheaf :
    (representedSmallEtaleSheafCongr B S hS U).unitIso.hom.app
        ((smallEtaleRingedTopos B S hS
            ⟨yoneda.obj U, isAlgebraicSpace_yoneda B S hS U⟩).forgetRing.obj
          (smallEtaleRingedTopos B S hS
            ⟨yoneda.obj U, isAlgebraicSpace_yoneda B S hS U⟩).O) = 𝟙 _ :=
  rfl

/-- **The structure map of the scheme-side composite of the two identifications, in
inverse-image form on underlying sheaves of sets, is the identity.**  Each factor's is
(`AlgebraicGeometry.Space.representedSmallEtaleRingedToposHom_fSharpInverseImageForget` and
`…Inverse_fSharpInverseImageForget`), and the structure map of a composite is the composite of
the two (`AlgebraicGeometry.RingedToposHom.fSharpInverseImageForget_comp`). -/
theorem representedSmallEtaleRingedToposCompInverse_fSharpInverseImageForget :
    (RingedToposHom.comp.{u, u + 1, u, u, u + 1, u, u, u + 1, u}
        (representedSmallEtaleRingedToposHom B S hS U)
        (representedSmallEtaleRingedToposInverse B S hS U)).fSharpInverseImageForget = 𝟙 _ :=
  (RingedToposHom.fSharpInverseImageForget_comp
        (representedSmallEtaleRingedToposHom B S hS U)
        (representedSmallEtaleRingedToposInverse B S hS U)).trans
    (RingedToposHom.map_comp_eq_id_of_eq_id _
      (representedSmallEtaleRingedToposHom_fSharpInverseImageForget B S hS U)
      (representedSmallEtaleRingedToposInverse_fSharpInverseImageForget B S hS U))

/-- **The structure map of the space-side composite of the two identifications, in
inverse-image form on underlying sheaves of sets, is the identity.** -/
theorem representedSmallEtaleRingedToposInverseComp_fSharpInverseImageForget :
    (RingedToposHom.comp.{u, u + 1, u, u, u + 1, u, u, u + 1, u}
        (representedSmallEtaleRingedToposInverse B S hS U)
        (representedSmallEtaleRingedToposHom B S hS U)).fSharpInverseImageForget = 𝟙 _ :=
  (RingedToposHom.fSharpInverseImageForget_comp
        (representedSmallEtaleRingedToposInverse B S hS U)
        (representedSmallEtaleRingedToposHom B S hS U)).trans
    (RingedToposHom.map_comp_eq_id_of_eq_id _
      (representedSmallEtaleRingedToposInverse_fSharpInverseImageForget B S hS U)
      (representedSmallEtaleRingedToposHom_fSharpInverseImageForget B S hS U))

/-- **The identification of the two readings of a chart is an equivalence in the 2-category of
ringed topoi: the scheme-side composite is 2-isomorphic to the identity.**  The inverse image of
the composite is restriction along the equivalence of sites followed by restriction along the
inverse equivalence, which the counit of
`AlgebraicGeometry.Space.representedSmallEtaleSheafCongr` compares with the identity functor;
both structure maps are the identity on underlying sheaves of sets, and so is that counit at the
structure sheaf. -/
noncomputable def representedSmallEtaleRingedToposCompInverse :
    RingedToposHom.TwoIso.{u, u + 1, u, u, u + 1, u}
      (RingedToposHom.comp.{u, u + 1, u, u, u + 1, u, u, u + 1, u}
        (representedSmallEtaleRingedToposHom B S hS U)
        (representedSmallEtaleRingedToposInverse B S hS U))
      (RingedToposHom.id.{u, u + 1, u}
        (_root_.AlgebraicGeometry.RingedSite.toRingedTopos
          (_root_.AlgebraicGeometry.smallEtaleRingedSite (associatedBigEtaleSite B)
            ((BigFppfOver.toScheme B S hS).obj U) U.left.property))) :=
  RingedToposHom.TwoIso.ofInverseImageIsoForget.{u, u + 1, u, u, u + 1}
    (representedSmallEtaleSheafCongr B S hS U).counitIso.symm
    (by
      refine Eq.trans ?_ (RingedToposHom.fSharpInverseImageForget_id
        (_root_.AlgebraicGeometry.RingedSite.toRingedTopos
          (_root_.AlgebraicGeometry.smallEtaleRingedSite (associatedBigEtaleSite B)
            ((BigFppfOver.toScheme B S hS).obj U) U.left.property))).symm
      rw [representedSmallEtaleRingedToposCompInverse_fSharpInverseImageForget B S hS U]
      exact (Category.comp_id _).trans
        (representedSmallEtaleSheafCongr_counitIso_inv_structureSheaf B S hS U))

/-- **The identification of the two readings of a chart is an equivalence in the 2-category of
ringed topoi: the space-side composite is 2-isomorphic to the identity.**  This is the direction
that undoes the conjugation `AlgebraicGeometry.Space.schemeOfRepresentedRingedToposHom`. -/
noncomputable def representedSmallEtaleRingedToposInverseComp :
    RingedToposHom.TwoIso.{u, u + 1, u, u, u + 1, u}
      (RingedToposHom.comp.{u, u + 1, u, u, u + 1, u, u, u + 1, u}
        (representedSmallEtaleRingedToposInverse B S hS U)
        (representedSmallEtaleRingedToposHom B S hS U))
      (RingedToposHom.id.{u, u + 1, u}
        (smallEtaleRingedTopos B S hS ⟨yoneda.obj U, isAlgebraicSpace_yoneda B S hS U⟩)) :=
  RingedToposHom.TwoIso.ofInverseImageIsoForget.{u, u + 1, u, u, u + 1}
    (representedSmallEtaleSheafCongr B S hS U).unitIso
    (by
      refine Eq.trans ?_ (RingedToposHom.fSharpInverseImageForget_id
        (smallEtaleRingedTopos B S hS
          ⟨yoneda.obj U, isAlgebraicSpace_yoneda B S hS U⟩)).symm
      rw [representedSmallEtaleRingedToposInverseComp_fSharpInverseImageForget B S hS U]
      exact (Category.comp_id _).trans
        (representedSmallEtaleSheafCongr_unitIso_hom_structureSheaf B S hS U))

/-! ### Undoing the conjugation -/

variable (V : BigFppfOver B S hS)

/-- **A morphism of the small étale ringed topoi of the two schemes, read back between the small
étale ringed topoi of the two representable algebraic spaces.**  This is the conjugation inverse
to `AlgebraicGeometry.Space.schemeOfRepresentedRingedToposHom`: it conjugates by the
identifications taken in the other direction. -/
noncomputable def spaceOfSchemeRingedToposHom
    (χ : RingedToposHom
      (_root_.AlgebraicGeometry.RingedSite.toRingedTopos
        (_root_.AlgebraicGeometry.smallEtaleRingedSite (associatedBigEtaleSite B)
          ((BigFppfOver.toScheme B S hS).obj U) U.left.property))
      (_root_.AlgebraicGeometry.RingedSite.toRingedTopos
        (_root_.AlgebraicGeometry.smallEtaleRingedSite (associatedBigEtaleSite B)
          ((BigFppfOver.toScheme B S hS).obj V) V.left.property))) :
    RingedToposHom
      (smallEtaleRingedTopos B S hS ⟨yoneda.obj U, isAlgebraicSpace_yoneda B S hS U⟩)
      (smallEtaleRingedTopos B S hS ⟨yoneda.obj V, isAlgebraicSpace_yoneda B S hS V⟩) :=
  RingedToposHom.comp.{u, u + 1, u, u, u + 1, u, u, u + 1, u}
    (representedSmallEtaleRingedToposInverse B S hS V)
    (RingedToposHom.comp.{u, u + 1, u, u, u + 1, u, u, u + 1, u} χ
      (representedSmallEtaleRingedToposHom B S hS U))

/-- Conjugating back carries a 2-isomorphism to a 2-isomorphism.  Like
`AlgebraicGeometry.Space.twoIsoSchemeOfRepresentedRingedToposHom`, it is two whiskerings and
nothing else. -/
noncomputable def twoIsoSpaceOfSchemeRingedToposHom
    {χ₁ χ₂ : RingedToposHom
      (_root_.AlgebraicGeometry.RingedSite.toRingedTopos
        (_root_.AlgebraicGeometry.smallEtaleRingedSite (associatedBigEtaleSite B)
          ((BigFppfOver.toScheme B S hS).obj U) U.left.property))
      (_root_.AlgebraicGeometry.RingedSite.toRingedTopos
        (_root_.AlgebraicGeometry.smallEtaleRingedSite (associatedBigEtaleSite B)
          ((BigFppfOver.toScheme B S hS).obj V) V.left.property))}
    (t : RingedToposHom.TwoIso.{u, u + 1, u, u, u + 1, u} χ₁ χ₂) :
    RingedToposHom.TwoIso.{u, u + 1, u, u, u + 1, u}
      (spaceOfSchemeRingedToposHom B S hS U V χ₁)
      (spaceOfSchemeRingedToposHom B S hS U V χ₂) :=
  RingedToposHom.TwoIso.whiskerRight.{u, u + 1, u, u, u + 1, u, u, u + 1, u}
    (RingedToposHom.TwoIso.whiskerLeft.{u, u + 1, u, u, u + 1, u, u, u + 1, u}
      (representedSmallEtaleRingedToposHom B S hS U) t)
    (representedSmallEtaleRingedToposInverse B S hS V)

/-- **Conjugating a morphism of the small étale ringed topoi of two representable algebraic
spaces into the schemes side and back recovers it up to 2-isomorphism.**  This is
`AlgebraicGeometry.RingedToposHom.TwoIso.conjugateUnconjugate` at the two identifications,
whose space-side composites are 2-isomorphic to the identity by
`AlgebraicGeometry.Space.representedSmallEtaleRingedToposInverseComp`. -/
noncomputable def twoIsoSpaceOfSchemeOfRepresentedRingedToposHom
    (ψ : RingedToposHom
      (smallEtaleRingedTopos B S hS ⟨yoneda.obj U, isAlgebraicSpace_yoneda B S hS U⟩)
      (smallEtaleRingedTopos B S hS ⟨yoneda.obj V, isAlgebraicSpace_yoneda B S hS V⟩)) :
    RingedToposHom.TwoIso.{u, u + 1, u, u, u + 1, u}
      (spaceOfSchemeRingedToposHom B S hS U V
        (schemeOfRepresentedRingedToposHom B S hS U V ψ)) ψ :=
  RingedToposHom.TwoIso.conjugateUnconjugate.{u, u + 1, u, u, u + 1, u, u, u + 1, u, u, u + 1, u} ψ
    (representedSmallEtaleRingedToposInverseComp B S hS U)
    (representedSmallEtaleRingedToposInverseComp B S hS V)

/-- **A 2-isomorphism of the conjugates is reflected back to a 2-isomorphism of the
originals.**  This is the direction the proof of Stacks 04KL consumes: the recovery theorems of
`StacksFrontier/AlgebraicGeometry/EtaleCohomology/RecoveringMorphisms/` are applied to the
conjugate of a morphism of ringed topoi, and what is wanted is the 2-isomorphism back on the
algebraic-spaces side.

This is not what the Stacks 04M6 rigidity statements of the tree do, and it does not follow
from them: `AlgebraicGeometry.Space.eq_of_smallEtaleRingedToposHom_twoIso`
(`Spaces/SmallEtaleTwoIsoAffineCover.lean`), `…eq_of_twoIso_of_schemeSource`
(`Spaces/SmallEtaleTwoIsoAtlasReduction.lean`) and
`…exists_smallBaseChange_iso_of_twoIso` (`Spaces/SmallEtaleTwoIsoChartComparison.lean`) all
*consume* a 2-isomorphism of the canonical morphisms of two morphisms of algebraic spaces and
produce an equality of those morphisms.  Here the two morphisms of ringed topoi are arbitrary,
and what is produced is a 2-isomorphism. -/
noncomputable def reflectTwoIsoSchemeOfRepresentedRingedToposHom
    {ψ₁ ψ₂ : RingedToposHom
      (smallEtaleRingedTopos B S hS ⟨yoneda.obj U, isAlgebraicSpace_yoneda B S hS U⟩)
      (smallEtaleRingedTopos B S hS ⟨yoneda.obj V, isAlgebraicSpace_yoneda B S hS V⟩)}
    (t : RingedToposHom.TwoIso.{u, u + 1, u, u, u + 1, u}
      (schemeOfRepresentedRingedToposHom B S hS U V ψ₁)
      (schemeOfRepresentedRingedToposHom B S hS U V ψ₂)) :
    RingedToposHom.TwoIso.{u, u + 1, u, u, u + 1, u} ψ₁ ψ₂ :=
  (twoIsoSpaceOfSchemeOfRepresentedRingedToposHom B S hS U V ψ₁).symm.trans
    ((twoIsoSpaceOfSchemeRingedToposHom B S hS U V t).trans
      (twoIsoSpaceOfSchemeOfRepresentedRingedToposHom B S hS U V ψ₂))

/-! ### The conjugated form of the canonical morphism -/

variable (g : U ⟶ V)

/-- **THE CONJUGATED NATURALITY SQUARE: the conjugate of the morphism of small étale ringed
topoi of a represented morphism of algebraic spaces is the morphism of small étale ringed topoi
of the underlying morphism of schemes.**

This is `AlgebraicGeometry.Space.representedSmallEtaleRingedToposNaturalityOfMap` with the
identification for `U` cancelled against its inverse, by
`AlgebraicGeometry.RingedToposHom.TwoIso.conjugateOfSquare`.  It needs no new geometry. -/
noncomputable def twoIsoSchemeOfSmallEtaleRingedToposHom :
    RingedToposHom.TwoIso.{u, u + 1, u, u, u + 1, u}
      (schemeOfRepresentedRingedToposHom B S hS U V
        (smallEtaleRingedToposHom B S hS (representedSpaceMap B S hS g)))
      (_root_.AlgebraicGeometry.smallEtaleRingedToposHom (associatedBigEtaleSite B) g.left) :=
  RingedToposHom.TwoIso.conjugateOfSquare.{u, u + 1, u, u, u + 1, u, u, u + 1, u, u, u + 1, u}
    (representedSmallEtaleRingedToposNaturalityOfMap B S hS U V g)
    (representedSmallEtaleRingedToposCompInverse B S hS U)

/-- **The form Stacks 04KL consumes.**  A morphism of the small étale ringed topoi of two
representable algebraic spaces whose conjugate is 2-isomorphic to the morphism of small étale
ringed topoi of a morphism of schemes `g` is itself 2-isomorphic to the morphism of small étale
ringed topoi of the represented morphism of algebraic spaces of `g`.

The recovery theorem is applied to the conjugate, on the schemes side, and produces exactly
such a 2-isomorphism; this carries it back. -/
noncomputable def reflectTwoIsoSmallEtaleRingedToposHom
    {ψ : RingedToposHom
      (smallEtaleRingedTopos B S hS ⟨yoneda.obj U, isAlgebraicSpace_yoneda B S hS U⟩)
      (smallEtaleRingedTopos B S hS ⟨yoneda.obj V, isAlgebraicSpace_yoneda B S hS V⟩)}
    (t : RingedToposHom.TwoIso.{u, u + 1, u, u, u + 1, u}
      (schemeOfRepresentedRingedToposHom B S hS U V ψ)
      (_root_.AlgebraicGeometry.smallEtaleRingedToposHom (associatedBigEtaleSite B) g.left)) :
    RingedToposHom.TwoIso.{u, u + 1, u, u, u + 1, u} ψ
      (smallEtaleRingedToposHom B S hS (representedSpaceMap B S hS g)) :=
  reflectTwoIsoSchemeOfRepresentedRingedToposHom B S hS U V
    (t.trans (twoIsoSchemeOfSmallEtaleRingedToposHom B S hS U V g).symm)

end AlgebraicGeometry.Space

end
