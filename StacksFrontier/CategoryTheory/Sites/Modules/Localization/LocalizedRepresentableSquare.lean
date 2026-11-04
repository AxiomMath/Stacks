module

public import StacksFrontier.CategoryTheory.Sites.Modules.Localization.LocalizedRepresentableKey
import StacksCore.Tactic.StacksAttribute

/-!
# Stacks 04J7 part (4) read on the two localization squares

Let `(f, f♯) : (C, O) ⟶ (D, O')` be a morphism of ringed sites and `V` an object of `D`.
Stacks 04J9 compares the localization square of Stacks 04J1 with that of Stacks 04J8 through the
identifications of Stacks 04J3, and the source's proof cites two things: Stacks 04J7, that the
two localized morphisms `f'` agree, and Stacks 04J5, that the two relocalizations agree — each
together with its compatibility with the relevant square or triangle. This file supplies the
Stacks 04J7 half: the compatibility of Stacks 04J7 part (4) with the localization square of
Stacks 04J0 and that of Stacks 04IF, which is the hypothesis `hLocSquares` of
`AlgebraicGeometry.RingedSite.Hom.exists_relocalizedComparison`.

## Main results

* `AlgebraicGeometry.RingedSite.Hom.locSquareCompareSite_eq_locSquareCompareTopos`:
  **`hLocSquares`**, the compatibility of the two squares itself. The inverse-image identity it
  rests on is taken inside its proof: read on inverse images, Stacks 03CF's clause (b) followed
  by Stacks 04J3's identification at `V` restricted along `f'` is Stacks 04J3's identification at
  `u(V)` restricted along `f^{-1}`, followed by Stacks 04IF's comparison restricted along
  `compareMid` and by Stacks 04J7's comparison restricted along `j_{h_V^#}`. That is
  `AlgebraicGeometry.RingedSite.Hom.keyNat` — Stacks 04J7 part (4) at every sheaf on the target
  — with three of its five edges inverted.
* `AlgebraicGeometry.RingedSite.Hom.exists_relocalizedComparison_of_relocTriangles`:
  Stacks 04J9 with the Stacks 04J7 half of its input discharged, so that only the Stacks 04J5
  half remains a hypothesis.

## Implementation notes

**Why there is a calculus of conjugates here.** A 2-isomorphism of ringed topoi is an
isomorphism of the *direct* images, while every comparison in sight is an isomorphism of the
*inverse* images; `AlgebraicGeometry.RingedToposHom.TwoIso.ofInverseImageIso` converts one to the
other by `CategoryTheory.conjugateEquiv`. Both sides of `hLocSquares` are vertical composites of
whiskered 2-isomorphisms, so to compare them each has to be rewritten as a *single* conjugate;
`CategoryTheory.conjugateEquiv_comp` and the whiskering and associator lemmas of Mathlib's mates
file do that factor by factor, and then `conjugateEquiv` being injective reduces the
compatibility to the identity of inverse images above.

**Why the pieces are stated abstractly.** The identifications in the `Pieces` section are stated
with every ringed topos and every morphism abstract, and that is load-bearing. At the concrete
localizations of Stacks 04J7 the same identifications make the elaborator rediscover, once per
occurrence, that the inverse image of a composite is the composite of the inverse images and
that the relocalization triangle of Stacks 04J4 is strict on inverse images — both true on the
nose, both requiring two towers of localization data to be unfolded — and it does not finish
inside its budget. Proved abstractly each check is syntactic and instantiating is substitution.

The identity whiskered out of the relocalization triangle, which looks like it could be dropped,
cannot: it is what carries the two spellings of the localization at `h_{u(V)}^#` onto each
other. It is removed only inside
`AlgebraicGeometry.RingedSite.Hom.representableLocalizationInverseImageIso_inv_comp_triangle`,
where that identification is paid for once.

**Why the inverse-image identity is not a lemma of its own.** Both sides of the compatibility
reach the identity only after their associators have been dropped, and that associator-free
spelling of the 04IF side cannot be *written down*: a composite in which
`(j_{F!}^{-1} ∘ f'^{-1})^{-1}` meets Stacks 04J7's comparison with no associator between them
makes `≫` ask the elaborator to identify the inverse image of a composite of morphisms of ringed
topoi with the composite of the inverse images, and whnf of
`(RingedTopos.localizationMorphism …).toToposHom.inverseImage` descends through the localization
equivalence to `Functor.leftAdjoint` and `Classical.choice` on the way. On this base,
that single `≫` costs about 200,000 heartbeats, so the *signature* of a lemma stating the
identity is already over the whole budget — 251,303 heartbeats for the 04J0-to-04IF identity and
287,878 for the 04IF side's associator cancellation — and no proof could have made either
compile. With the associators in place every such join is syntactic (79,516 for the two sides
together), so the identity is taken inside
`AlgebraicGeometry.RingedSite.Hom.locSquareCompareSite_eq_locSquareCompareTopos`, where both
composites arrive instantiated from `Hom.locSquareCompareSite_e_hom_eq` and
`Hom.locSquareCompareTopos_e_hom_eq` and the associator-free midpoints are produced by the
cancellation steps themselves rather than by any written type.

## References

* [Stacks Project, Tag 04J7](https://stacks.math.columbia.edu/tag/04J7)
* [Stacks Project, Tag 04J9](https://stacks.math.columbia.edu/tag/04J9)
* [Stacks Project, Tag 04IF](https://stacks.math.columbia.edu/tag/04IF)
* [Stacks Project, Tag 04J0](https://stacks.math.columbia.edu/tag/04J0)
* [Stacks Project, Tag 04J3](https://stacks.math.columbia.edu/tag/04J3)
* [Stacks Project, Tag 04J4](https://stacks.math.columbia.edu/tag/04J4)
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits
open AlgebraicGeometry.RingedToposHom

universe u

namespace Stacks.CategoryTheory

open CategoryTheory

universe v₁ v₂ u₁ u₂

variable {A : Type u₁} [Category.{v₁} A] {B : Type u₂} [Category.{v₂} B]

/-- Transporting an adjunction along an isomorphism of its left adjoint and then comparing the
two right adjoints is conjugation along the inverse of that isomorphism. -/
theorem rightAdjointUniq_ofNatIsoLeft_left_hom {L₁ L₂ : A ⥤ B} {R₁ R₂ : B ⥤ A}
    (adj₁ : L₁ ⊣ R₁) (adj₂ : L₂ ⊣ R₂) (e : L₁ ≅ L₂) :
    (Adjunction.rightAdjointUniq (adj₁.ofNatIsoLeft e) adj₂).hom =
      conjugateEquiv adj₁ adj₂ e.inv := by
  ext F
  simp [Adjunction.rightAdjointUniq]

/-- Vertical composition of five conjugates. -/
theorem conjugateEquiv_comp₅ {L₁ L₂ L₃ L₄ L₅ L₆ : A ⥤ B} {R₁ R₂ R₃ R₄ R₅ R₆ : B ⥤ A}
    (adj₁ : L₁ ⊣ R₁) (adj₂ : L₂ ⊣ R₂) (adj₃ : L₃ ⊣ R₃) (adj₄ : L₄ ⊣ R₄) (adj₅ : L₅ ⊣ R₅)
    (adj₆ : L₆ ⊣ R₆) (α : L₂ ⟶ L₁) (β : L₃ ⟶ L₂) (γ : L₄ ⟶ L₃) (δ : L₅ ⟶ L₄) (ε : L₆ ⟶ L₅) :
    conjugateEquiv adj₁ adj₂ α ≫ conjugateEquiv adj₂ adj₃ β ≫ conjugateEquiv adj₃ adj₄ γ ≫
        conjugateEquiv adj₄ adj₅ δ ≫ conjugateEquiv adj₅ adj₆ ε =
      conjugateEquiv adj₁ adj₆ (ε ≫ δ ≫ γ ≫ β ≫ α) := by
  rw [conjugateEquiv_comp adj₄ adj₅ adj₆, conjugateEquiv_comp adj₃ adj₄ adj₆,
    conjugateEquiv_comp adj₂ adj₃ adj₆, conjugateEquiv_comp adj₁ adj₂ adj₆,
    Category.assoc, Category.assoc, Category.assoc]

/-- Vertical composition of five conjugates, with each factor identified. -/
theorem conjugateEquiv_comp₅_eq {L₁ L₂ L₃ L₄ L₅ L₆ : A ⥤ B} {R₁ R₂ R₃ R₄ R₅ R₆ : B ⥤ A}
    (adj₁ : L₁ ⊣ R₁) (adj₂ : L₂ ⊣ R₂) (adj₃ : L₃ ⊣ R₃) (adj₄ : L₄ ⊣ R₄) (adj₅ : L₅ ⊣ R₅)
    (adj₆ : L₆ ⊣ R₆) (α : L₂ ⟶ L₁) (β : L₃ ⟶ L₂) (γ : L₄ ⟶ L₃) (δ : L₅ ⟶ L₄) (ε : L₆ ⟶ L₅)
    {a : R₁ ⟶ R₂} {b : R₂ ⟶ R₃} {c : R₃ ⟶ R₄} {d : R₄ ⟶ R₅} {e : R₅ ⟶ R₆}
    (ha : conjugateEquiv adj₁ adj₂ α = a) (hb : conjugateEquiv adj₂ adj₃ β = b)
    (hc : conjugateEquiv adj₃ adj₄ γ = c) (hd : conjugateEquiv adj₄ adj₅ δ = d)
    (he : conjugateEquiv adj₅ adj₆ ε = e) :
    conjugateEquiv adj₁ adj₆ (ε ≫ δ ≫ γ ≫ β ≫ α) = a ≫ b ≫ c ≫ d ≫ e := by
  rw [← ha, ← hb, ← hc, ← hd, ← he,
    conjugateEquiv_comp₅ adj₁ adj₂ adj₃ adj₄ adj₅ adj₆]

/-- **A pentagon of isomorphisms, read on the inverses of two of its edges.** Given
`x ≫ y ≫ z = w ≫ t`, the composite `z⁻¹ ≫ y⁻¹` is `t⁻¹ ≫ w⁻¹ ≫ x`. -/
theorem inv_comp_eq_of_comp₃ {o₁ o₂ o₃ o₄ o₅ : A} (x : o₁ ≅ o₂) (y : o₂ ≅ o₃) (z : o₃ ≅ o₄)
    (w : o₁ ≅ o₅) (t : o₅ ≅ o₄) (h : x.hom ≫ y.hom ≫ z.hom = w.hom ≫ t.hom) :
    z.inv ≫ y.inv = t.inv ≫ w.inv ≫ x.hom := by
  have h' : y.hom ≫ z.hom = x.inv ≫ w.hom ≫ t.hom := by
    rw [← h]
    simp
  simpa using congrArg Iso.inv (Iso.ext (α := y ≪≫ z) (β := x.symm ≪≫ w ≪≫ t) h')

/-- A conjugate depends on the transformation only through its value. -/
theorem conjugateEquiv_of_eq {L₁ L₂ : A ⥤ B} {R₁ R₂ : B ⥤ A} (adj₁ : L₁ ⊣ R₁) (adj₂ : L₂ ⊣ R₂)
    {α β : L₂ ⟶ L₁} (h : α = β) :
    conjugateEquiv adj₁ adj₂ α = conjugateEquiv adj₁ adj₂ β :=
  congrArg _ h

section Associator

universe v₃ v₄ u₃ u₄

variable {C : Type u₃} [Category.{v₃} C] {D : Type u₄} [Category.{v₄} D]

/-- The associator of three functors is the identity: a composite of functors is associative on
the nose, and the associator's components are identities. -/
theorem associator_hom_eq_id (F : A ⥤ B) (G : B ⥤ C) (H : C ⥤ D) :
    (Functor.associator F G H).hom = 𝟙 _ := rfl

/-- The inverse associator of three functors is the identity. -/
theorem associator_inv_eq_id (F : A ⥤ B) (G : B ⥤ C) (H : C ⥤ D) :
    (Functor.associator F G H).inv = 𝟙 _ := rfl

/-- `inv_comp_eq_of_comp₃` with an endomorphism known to be the identity inserted after the
first factor on the right, which is the shape a whiskered identity leaves behind. -/
theorem inv_comp_eq_of_comp₃_mid {o₁ o₂ o₃ o₄ o₅ : A} (x : o₁ ≅ o₂) (y : o₂ ≅ o₃) (z : o₃ ≅ o₄)
    (w : o₁ ≅ o₅) (t : o₅ ≅ o₄) (m : o₅ ⟶ o₅) (hm : m = 𝟙 o₅)
    (h : x.hom ≫ y.hom ≫ z.hom = w.hom ≫ t.hom) :
    z.inv ≫ y.inv = (t.inv ≫ m) ≫ w.inv ≫ x.hom := by
  rw [hm, Category.comp_id]
  exact inv_comp_eq_of_comp₃ x y z w t h

end Associator

end Stacks.CategoryTheory

namespace AlgebraicGeometry.RingedToposHom

universe v₁ u₁ w₁ v₂ u₂ w₂

variable {A : RingedTopos.{v₁, u₁, w₁}} {B : RingedTopos.{v₂, u₂, w₂}}
  [A.J.HasSheafCompose (forget RingCat.{w₁})]
  [B.J.HasSheafCompose (forget RingCat.{w₂})]
  [A.J.HasSheafCompose (forget₂ CommRingCat.{w₁} RingCat.{w₁})]
  [B.J.HasSheafCompose (forget₂ CommRingCat.{w₂} RingCat.{w₂})]

/-- A 2-isomorphism of morphisms of ringed topoi is determined by the underlying isomorphism of
direct images: the compatibility with the structure maps is a proposition. -/
@[ext]
theorem TwoIso.ext {p q : RingedToposHom A B} {s s' : TwoIso p q} (h : s.e = s'.e) : s = s' := by
  cases s
  cases s'
  cases h
  rfl

/-- A 2-isomorphism of morphisms of ringed topoi is determined by the forward direction of the
underlying isomorphism of direct images. -/
theorem TwoIso.ext_hom {p q : RingedToposHom A B} {s s' : TwoIso p q}
    (h : s.e.hom = s'.e.hom) : s = s' :=
  TwoIso.ext (Iso.ext h)


/-! ### The pieces of a pasted square, each spelled as a conjugate

A 2-isomorphism of ringed topoi built by `TwoIso.ofInverseImageIso` has for its transformation
the conjugate of the comparison of inverse images it was built from, and the calculus of
2-isomorphisms — vertical composition, the two whiskerings, the associator — matches the
calculus of conjugates factor by factor. The identifications below record that, once per
operation.

Each is stated with every ringed topos and every morphism abstract, and that is load-bearing
rather than tidy. The same identifications written at the concrete localizations of Stacks 04J7
make the elaborator rediscover, once per occurrence, that the inverse image of a composite is
the composite of the inverse images and that the relocalization triangle of Stacks 04J4 is a
strict identity on inverse images — both true on the nose, both requiring two towers of
localization data to be unfolded — and it does not finish inside its budget. Proved abstractly
each check is syntactic, and instantiating is substitution. -/

section Pieces

attribute [local instance] AlgebraicGeometry.RingedTopos.isContinuous_elementPostcomp
  AlgebraicGeometry.RingedTopos.isCocontinuous_elementPostcomp

variable {P Q R S : RingedTopos.{u, u, u}}
  [P.J.HasSheafCompose (forget RingCat.{u})] [Q.J.HasSheafCompose (forget RingCat.{u})]
  [R.J.HasSheafCompose (forget RingCat.{u})] [S.J.HasSheafCompose (forget RingCat.{u})]
  [P.J.HasSheafCompose (forget₂ CommRingCat.{u} RingCat.{u})]
  [Q.J.HasSheafCompose (forget₂ CommRingCat.{u} RingCat.{u})]
  [R.J.HasSheafCompose (forget₂ CommRingCat.{u} RingCat.{u})]
  [S.J.HasSheafCompose (forget₂ CommRingCat.{u} RingCat.{u})]

/-- A 2-isomorphism built from a comparison of inverse images has that comparison's conjugate
for its transformation. -/
theorem conjugateEquiv_ofInverseImageIso_e_hom {p q : RingedToposHom P Q}
    (α : q.toToposHom.inverseImage ≅ p.toToposHom.inverseImage)
    (h : α.hom.app (Q.forgetRing.obj Q.O) ≫ P.forgetRing.map p.fSharpInverseImage =
      P.forgetRing.map q.fSharpInverseImage) :
    conjugateEquiv p.toToposHom.adj q.toToposHom.adj α.hom =
      (TwoIso.ofInverseImageIso α h).e.hom := rfl

/-- The associator of ringed topoi is the conjugate of the associator of the inverse images. -/
theorem conjugateEquiv_associator_e_hom (p : RingedToposHom P Q) (q : RingedToposHom Q R)
    (r : RingedToposHom R S) :
    conjugateEquiv (r.toToposHom.adj.comp (q.toToposHom.adj.comp p.toToposHom.adj))
        ((r.toToposHom.adj.comp q.toToposHom.adj).comp p.toToposHom.adj)
        (Functor.associator r.toToposHom.inverseImage q.toToposHom.inverseImage
          p.toToposHom.inverseImage).hom =
      (TwoIso.associator p q r).e.hom :=
  conjugateEquiv_associator_hom _ _ _

/-- The inverse associator of ringed topoi is the conjugate of the inverse associator of the
inverse images. -/
theorem conjugateEquiv_associator_symm_e_hom (p : RingedToposHom P Q) (q : RingedToposHom Q R)
    (r : RingedToposHom R S) :
    conjugateEquiv ((r.toToposHom.adj.comp q.toToposHom.adj).comp p.toToposHom.adj)
        (r.toToposHom.adj.comp (q.toToposHom.adj.comp p.toToposHom.adj))
        (Functor.associator r.toToposHom.inverseImage q.toToposHom.inverseImage
          p.toToposHom.inverseImage).inv =
      (TwoIso.associator p q r).symm.e.hom :=
  Stacks.CategoryTheory.conjugateEquiv_associator_inv _ _ _

/-- Whiskering a 2-isomorphism on the left by a morphism into its source is whiskering the
conjugated comparison of inverse images on the right. -/
theorem conjugateEquiv_twoIso_whiskerLeft (g : RingedToposHom P Q) {p q : RingedToposHom Q R}
    (s : TwoIso p q) {τ : q.toToposHom.inverseImage ⟶ p.toToposHom.inverseImage}
    (h : conjugateEquiv p.toToposHom.adj q.toToposHom.adj τ = s.e.hom) :
    conjugateEquiv (p.toToposHom.adj.comp g.toToposHom.adj)
        (q.toToposHom.adj.comp g.toToposHom.adj)
        (Functor.whiskerRight τ g.toToposHom.inverseImage) =
      (TwoIso.whiskerLeft g s).e.hom :=
  (conjugateEquiv_whiskerRight p.toToposHom.adj q.toToposHom.adj g.toToposHom.adj τ).trans
    (congrArg (fun z ↦ Functor.whiskerLeft g.toToposHom.pushforward z) h)

/-- Whiskering a 2-isomorphism on the right by a morphism out of its target is whiskering the
conjugated comparison of inverse images on the left. -/
theorem conjugateEquiv_twoIso_whiskerRight {p q : RingedToposHom P Q} (s : TwoIso p q)
    (g : RingedToposHom Q R) {τ : q.toToposHom.inverseImage ⟶ p.toToposHom.inverseImage}
    (h : conjugateEquiv p.toToposHom.adj q.toToposHom.adj τ = s.e.hom) :
    conjugateEquiv (g.toToposHom.adj.comp p.toToposHom.adj)
        (g.toToposHom.adj.comp q.toToposHom.adj)
        (Functor.whiskerLeft g.toToposHom.inverseImage τ) =
      (s.whiskerRight g).e.hom :=
  (conjugateEquiv_whiskerLeft p.toToposHom.adj q.toToposHom.adj g.toToposHom.adj τ).trans
    (congrArg (fun z ↦ Functor.whiskerRight z g.toToposHom.pushforward) h)

omit [Q.J.HasSheafCompose (forget RingCat)] [Q.J.HasSheafCompose (forget₂ CommRingCat RingCat)] in
/-- **The relocalization triangle of Stacks 04J4, inverted and whiskered, as a conjugate.** The
triangle is the identity on inverse images, so the conjugate is the identity whiskered by the
morphism it is composed with. -/
theorem conjugateEquiv_whiskerLeft_toposRelocalizationTriangle_symm {H K : Q.Topos} (a : H ⟶ K)
    (Φ : RingedToposHom P (Q.localizedRingedTopos H)) :
    conjugateEquiv
        (((Q.localizationMorphism K).toToposHom.adj.comp
            (Q.relocalizationMorphism a).toToposHom.adj).comp Φ.toToposHom.adj)
        ((Q.localizationMorphism H).toToposHom.adj.comp Φ.toToposHom.adj)
        (Functor.whiskerRight
          (𝟙 (Q.localizationMorphism H).toToposHom.inverseImage)
          Φ.toToposHom.inverseImage) =
      (TwoIso.whiskerLeft Φ (toposRelocalizationTriangle Q a).symm).e.hom :=
  conjugateEquiv_whiskerRight _ _ _ _

/-- The adjunction attached to a composite of morphisms of ringed topoi is the composite of the
two adjunctions, so a conjugate may be read at either spelling. -/
theorem conjugateEquiv_comp_adj {p₁ p₂ : RingedToposHom P Q} {q₁ q₂ : RingedToposHom Q R}
    (τ : (comp q₂ p₂).toToposHom.inverseImage ⟶ (comp q₁ p₁).toToposHom.inverseImage) :
    conjugateEquiv (q₁.toToposHom.adj.comp p₁.toToposHom.adj)
        (q₂.toToposHom.adj.comp p₂.toToposHom.adj) τ =
      conjugateEquiv (comp q₁ p₁).toToposHom.adj (comp q₂ p₂).toToposHom.adj τ := rfl

/-- **Stacks 04IF's square, as a conjugate.** -/
theorem localizedRingedToposSquare_e_hom_eq (g : RingedToposHom P Q) (G : Q.Topos) :
    conjugateEquiv
        ((Q.localizationMorphism G).toToposHom.adj.comp (g.localized G).toToposHom.adj)
        (g.toToposHom.adj.comp
          (P.localizationMorphism (g.toToposHom.inverseImage.obj G)).toToposHom.adj)
        (g.inverseImageCompLocalizationIso G).hom =
      (g.localizedRingedToposSquare G).e.hom := rfl

section CompositeWhiskering

variable {P' R' : RingedTopos.{u, u, u}}
  [P'.J.HasSheafCompose (forget RingCat.{u})] [R'.J.HasSheafCompose (forget RingCat.{u})]
  [P'.J.HasSheafCompose (forget₂ CommRingCat.{u} RingCat.{u})]
  [R'.J.HasSheafCompose (forget₂ CommRingCat.{u} RingCat.{u})]

/-- `conjugateEquiv_twoIso_whiskerRight` for a 2-isomorphism between two composites, with the
two composite adjunctions split. -/
theorem conjugateEquiv_twoIso_whiskerRight_comp {p₁ : RingedToposHom P Q}
    {q₁ : RingedToposHom Q R} {p₂ : RingedToposHom P P'} {q₂ : RingedToposHom P' R}
    (s : TwoIso (comp q₁ p₁) (comp q₂ p₂)) (g : RingedToposHom R S)
    {τ : q₂.toToposHom.inverseImage ⋙ p₂.toToposHom.inverseImage ⟶
      q₁.toToposHom.inverseImage ⋙ p₁.toToposHom.inverseImage}
    (h : conjugateEquiv (q₁.toToposHom.adj.comp p₁.toToposHom.adj)
      (q₂.toToposHom.adj.comp p₂.toToposHom.adj) τ = s.e.hom) :
    conjugateEquiv (g.toToposHom.adj.comp (q₁.toToposHom.adj.comp p₁.toToposHom.adj))
        (g.toToposHom.adj.comp (q₂.toToposHom.adj.comp p₂.toToposHom.adj))
        (Functor.whiskerLeft g.toToposHom.inverseImage τ) =
      (s.whiskerRight g).e.hom :=
  conjugateEquiv_twoIso_whiskerRight s g h

/-- `conjugateEquiv_twoIso_whiskerRight` for a 2-isomorphism out of a composite, with that
composite adjunction split. -/
theorem conjugateEquiv_twoIso_whiskerRight_comp_source {p₁ : RingedToposHom P Q}
    {q₁ : RingedToposHom Q R} {q : RingedToposHom P R} (s : TwoIso (comp q₁ p₁) q)
    (g : RingedToposHom R S)
    {τ : q.toToposHom.inverseImage ⟶
      q₁.toToposHom.inverseImage ⋙ p₁.toToposHom.inverseImage}
    (h : conjugateEquiv (q₁.toToposHom.adj.comp p₁.toToposHom.adj) q.toToposHom.adj τ =
      s.e.hom) :
    conjugateEquiv (g.toToposHom.adj.comp (q₁.toToposHom.adj.comp p₁.toToposHom.adj))
        (g.toToposHom.adj.comp q.toToposHom.adj)
        (Functor.whiskerLeft g.toToposHom.inverseImage τ) =
      (s.whiskerRight g).e.hom :=
  conjugateEquiv_twoIso_whiskerRight s g h

/-- `conjugateEquiv_twoIso_whiskerLeft` for a 2-isomorphism between two composites, with the two
composite adjunctions split. -/
theorem conjugateEquiv_twoIso_whiskerLeft_comp (g : RingedToposHom P Q)
    {p₁ : RingedToposHom Q R} {q₁ : RingedToposHom R S} {p₂ : RingedToposHom Q R'}
    {q₂ : RingedToposHom R' S} (s : TwoIso (comp q₁ p₁) (comp q₂ p₂))
    {τ : q₂.toToposHom.inverseImage ⋙ p₂.toToposHom.inverseImage ⟶
      q₁.toToposHom.inverseImage ⋙ p₁.toToposHom.inverseImage}
    (h : conjugateEquiv (q₁.toToposHom.adj.comp p₁.toToposHom.adj)
      (q₂.toToposHom.adj.comp p₂.toToposHom.adj) τ = s.e.hom) :
    conjugateEquiv ((q₁.toToposHom.adj.comp p₁.toToposHom.adj).comp g.toToposHom.adj)
        ((q₂.toToposHom.adj.comp p₂.toToposHom.adj).comp g.toToposHom.adj)
        (Functor.whiskerRight τ g.toToposHom.inverseImage) =
      (TwoIso.whiskerLeft g s).e.hom :=
  conjugateEquiv_twoIso_whiskerLeft g s h

end CompositeWhiskering

end Pieces

end AlgebraicGeometry.RingedToposHom

namespace AlgebraicGeometry.RingedSite

attribute [local instance] AlgebraicGeometry.RingedTopos.isContinuous_elementPostcomp
  AlgebraicGeometry.RingedTopos.isCocontinuous_elementPostcomp
  CategoryTheory.Functor.isContinuous_overPost_of_isContinuous

/-! The two composition operations are made reducible: every identification below has to read
the adjunction of a composite of morphisms of ringed topoi as the composite of the two
adjunctions, which holds by two projections once the composites unfold. -/
attribute [local implicit_reducible] AlgebraicGeometry.RingedToposHom.comp
  MorphismOfTopoi.comp

variable {X Y : RingedSite.{u, u, u}} (f : RingedSite.Hom X Y) (V : Y.C)

/-- The transformation of `localizationTwoIso Z U` is the conjugate of the inverse of
`representableLocalizationInverseImageIso Z U`, along the composite of the adjunctions of the
localization at `representableSheaf Z U` and of `representableLocalizationRingedMorphism Z U`. -/
theorem localizationTwoIso_e_hom_eq (Z : RingedSite.{u, u, u}) (U : Z.C) :
    conjugateEquiv
        ((RingedTopos.localizationMorphism Z.ringedTopos
            (representableSheaf Z U)).toToposHom.adj.comp
          (representableLocalizationRingedMorphism Z U).toToposHom.adj)
        (Z.localizationRingedToposHom U).toToposHom.adj
        (Z.representableLocalizationInverseImageIso U).inv =
      (localizationTwoIso Z U).e.hom := rfl

/-- `Hom.kapMid`'s transformation, written out as the composite of its three factors. -/
theorem Hom.kapMid_e_hom_comp :
    (f.kapMid V).e.hom =
      (TwoIso.associator (representableLocalizationRingedMorphism X (f.u.obj V))
            (X.ringedTopos.relocalizationMorphism
              (f.inverseImageRepresentableSheafIso V).inv)
            (RingedTopos.localizationMorphism X.ringedTopos
              (f.inverseImageRepresentableSheaf V))).e.hom ≫
        (TwoIso.whiskerLeft (representableLocalizationRingedMorphism X (f.u.obj V))
              (toposRelocalizationTriangle X.ringedTopos
                (f.inverseImageRepresentableSheafIso V).inv).symm).e.hom ≫
          (localizationTwoIso X (f.u.obj V)).e.hom := rfl

/-- **The middle identification's compatibility with the two localizations of the source, as a
conjugate.** `Hom.kapMid` is the conjugate of Stacks 04J3's comparison of inverse images at
`u(V)`, the relocalization triangle of Stacks 04J4 contributing the identity. -/
theorem Hom.kapMid_e_hom_eq :
    conjugateEquiv
        ((RingedTopos.localizationMorphism X.ringedTopos
            (f.inverseImageRepresentableSheaf V)).toToposHom.adj.comp
          ((X.ringedTopos.relocalizationMorphism
              (f.inverseImageRepresentableSheafIso V).inv).toToposHom.adj.comp
            (representableLocalizationRingedMorphism X (f.u.obj V)).toToposHom.adj))
        (X.localizationRingedToposHom (f.u.obj V)).toToposHom.adj
        ((X.representableLocalizationInverseImageIso (f.u.obj V)).inv ≫
          Functor.whiskerRight
              (𝟙 (RingedTopos.localizationMorphism X.ringedTopos
                (representableSheaf X (f.u.obj V))).toToposHom.inverseImage)
              (representableLocalizationRingedMorphism X
                (f.u.obj V)).toToposHom.inverseImage ≫
            (Functor.associator
              (RingedTopos.localizationMorphism X.ringedTopos
                (f.inverseImageRepresentableSheaf V)).toToposHom.inverseImage
              (X.ringedTopos.relocalizationMorphism
                (f.inverseImageRepresentableSheafIso V).inv).toToposHom.inverseImage
              (representableLocalizationRingedMorphism X
                (f.u.obj V)).toToposHom.inverseImage).hom) =
      (f.kapMid V).e.hom :=
  Eq.trans
    (Stacks.CategoryTheory.conjugateEquiv_comp₃_eq _ _ _ _ _ _ _
      (conjugateEquiv_associator_e_hom (representableLocalizationRingedMorphism X (f.u.obj V))
        (X.ringedTopos.relocalizationMorphism (f.inverseImageRepresentableSheafIso V).inv)
        (RingedTopos.localizationMorphism X.ringedTopos
          (f.inverseImageRepresentableSheaf V)))
      (conjugateEquiv_whiskerLeft_toposRelocalizationTriangle_symm
        (f.inverseImageRepresentableSheafIso V).inv
        (representableLocalizationRingedMorphism X (f.u.obj V)))
      (localizationTwoIso_e_hom_eq X (f.u.obj V)))
    (f.kapMid_e_hom_comp V).symm

/-- `Hom.localizedRingedSquare`'s transformation, as a comparison of right adjoints. -/
theorem Hom.localizedRingedSquare_e_hom_rightAdjointUniq :
    (f.localizedRingedSquare V).e.hom =
      (Adjunction.rightAdjointUniq
        (((Y.localizationRingedToposHom V).toToposHom.adj.comp
            (f.localizedRingedToposHom V).toToposHom.adj).ofNatIsoLeft
          (CategoryTheory.SliceTopos.overPullbackCompSheafPullbackOverPostIso Y.J X.J f.u V
            f.isMorphismOfSites))
        (f.ringedToposHom.toToposHom.adj.comp
          (X.localizationRingedToposHom (f.u.obj V)).toToposHom.adj)).hom := rfl

/-- **Stacks 04J0's square, as a conjugate.** The comparison of the two direct images is the
conjugate of Stacks 03CF's clause (b), inverted. -/
theorem Hom.localizedRingedSquare_e_hom_eq :
    conjugateEquiv
        ((Y.localizationRingedToposHom V).toToposHom.adj.comp
          (f.localizedRingedToposHom V).toToposHom.adj)
        (f.ringedToposHom.toToposHom.adj.comp
          (X.localizationRingedToposHom (f.u.obj V)).toToposHom.adj)
        (CategoryTheory.SliceTopos.overPullbackCompSheafPullbackOverPostIso Y.J X.J f.u V
          f.isMorphismOfSites).inv =
      (f.localizedRingedSquare V).e.hom :=
  (Stacks.CategoryTheory.rightAdjointUniq_ofNatIsoLeft_left_hom _ _ _).symm.trans
    (f.localizedRingedSquare_e_hom_rightAdjointUniq V).symm

/-- `Hom.locSquareCompareSite`'s transformation, as the composite of its three factors. -/
theorem Hom.locSquareCompareSite_e_hom_comp :
    (f.locSquareCompareSite V).e.hom =
      (TwoIso.associator (f.localizedRingedToposHom V)
            (representableLocalizationRingedMorphism Y V)
            (RingedTopos.localizationMorphism Y.ringedTopos
              (representableSheaf Y V))).e.hom ≫
        (TwoIso.whiskerLeft (f.localizedRingedToposHom V) (localizationTwoIso Y V)).e.hom ≫
          (f.localizedRingedSquare V).e.hom := rfl

/-- **The 04J0 side of Stacks 04J9's compatibility, as a conjugate.** -/
theorem Hom.locSquareCompareSite_e_hom_eq :
    conjugateEquiv
        ((RingedTopos.localizationMorphism Y.ringedTopos
            (representableSheaf Y V)).toToposHom.adj.comp
          ((representableLocalizationRingedMorphism Y V).toToposHom.adj.comp
            (f.localizedRingedToposHom V).toToposHom.adj))
        (f.ringedToposHom.toToposHom.adj.comp
          (X.localizationRingedToposHom (f.u.obj V)).toToposHom.adj)
        ((CategoryTheory.SliceTopos.overPullbackCompSheafPullbackOverPostIso Y.J X.J f.u V
              f.isMorphismOfSites).inv ≫
          Functor.whiskerRight (Y.representableLocalizationInverseImageIso V).inv
              (f.localizedRingedToposHom V).toToposHom.inverseImage ≫
            (Functor.associator
              (RingedTopos.localizationMorphism Y.ringedTopos
                (representableSheaf Y V)).toToposHom.inverseImage
              (representableLocalizationRingedMorphism Y V).toToposHom.inverseImage
              (f.localizedRingedToposHom V).toToposHom.inverseImage).hom) =
      (f.locSquareCompareSite V).e.hom :=
  Eq.trans
    (Stacks.CategoryTheory.conjugateEquiv_comp₃_eq _ _ _ _ _ _ _
      (conjugateEquiv_associator_e_hom (f.localizedRingedToposHom V)
        (representableLocalizationRingedMorphism Y V)
        (RingedTopos.localizationMorphism Y.ringedTopos (representableSheaf Y V)))
      (conjugateEquiv_twoIso_whiskerLeft (f.localizedRingedToposHom V)
        (localizationTwoIso Y V) (localizationTwoIso_e_hom_eq Y V))
      (f.localizedRingedSquare_e_hom_eq V))
    (f.locSquareCompareSite_e_hom_comp V).symm

/-- **Stacks 04J7 part (4), as a conjugate.** -/
theorem Hom.localizedComparisonTwoIso_e_hom_eq :
    conjugateEquiv
        ((representableLocalizationRingedMorphism Y V).toToposHom.adj.comp
          (f.localizedRingedToposHom V).toToposHom.adj)
        ((f.ringedToposHom.localized (representableSheaf Y V)).toToposHom.adj.comp
          (f.compareMid V).toToposHom.adj)
        (f.localizedRepresentableCompInverseImageIso V).hom =
      (f.localizedComparisonTwoIso V).e.hom := rfl

/-- `Hom.kapMid_e_hom_eq` with the relocalization and Stacks 04J3's identification at `u(V)`
contracted back into `compareMid`, which is the spelling the pasted square carries. -/
theorem Hom.kapMid_e_hom_eq' :
    conjugateEquiv
        ((RingedTopos.localizationMorphism X.ringedTopos
            (f.inverseImageRepresentableSheaf V)).toToposHom.adj.comp
          (f.compareMid V).toToposHom.adj)
        (X.localizationRingedToposHom (f.u.obj V)).toToposHom.adj
        ((X.representableLocalizationInverseImageIso (f.u.obj V)).inv ≫
          Functor.whiskerRight
              (𝟙 (RingedTopos.localizationMorphism X.ringedTopos
                (representableSheaf X (f.u.obj V))).toToposHom.inverseImage)
              (representableLocalizationRingedMorphism X
                (f.u.obj V)).toToposHom.inverseImage ≫
            (Functor.associator
              (RingedTopos.localizationMorphism X.ringedTopos
                (f.inverseImageRepresentableSheaf V)).toToposHom.inverseImage
              (X.ringedTopos.relocalizationMorphism
                (f.inverseImageRepresentableSheafIso V).inv).toToposHom.inverseImage
              (representableLocalizationRingedMorphism X
                (f.u.obj V)).toToposHom.inverseImage).hom) =
      (f.kapMid V).e.hom :=
  f.kapMid_e_hom_eq V

/-- `Hom.locSquareCompareTopos`'s transformation, as the composite of its five factors. -/
theorem Hom.locSquareCompareTopos_e_hom_comp :
    (f.locSquareCompareTopos V (f.localizedComparisonTwoIso V)).e.hom =
      ((f.localizedComparisonTwoIso V).whiskerRight
            (RingedTopos.localizationMorphism Y.ringedTopos
              (representableSheaf Y V))).e.hom ≫
        (TwoIso.associator (f.compareMid V)
              (f.ringedToposHom.localized (representableSheaf Y V))
              (RingedTopos.localizationMorphism Y.ringedTopos
                (representableSheaf Y V))).e.hom ≫
          (TwoIso.whiskerLeft (f.compareMid V)
                (f.ringedToposHom.localizedRingedToposSquare
                  (representableSheaf Y V))).e.hom ≫
            (TwoIso.associator (f.compareMid V)
                  (RingedTopos.localizationMorphism X.ringedTopos
                    (f.inverseImageRepresentableSheaf V))
                  f.ringedToposHom).symm.e.hom ≫
              ((f.kapMid V).whiskerRight f.ringedToposHom).e.hom := rfl

/-- **The 04IF side of Stacks 04J9's compatibility, as a conjugate.** -/
theorem Hom.locSquareCompareTopos_e_hom_eq :
    conjugateEquiv
        ((RingedTopos.localizationMorphism Y.ringedTopos
            (representableSheaf Y V)).toToposHom.adj.comp
          ((representableLocalizationRingedMorphism Y V).toToposHom.adj.comp
            (f.localizedRingedToposHom V).toToposHom.adj))
        (f.ringedToposHom.toToposHom.adj.comp
          (X.localizationRingedToposHom (f.u.obj V)).toToposHom.adj)
        (Functor.whiskerLeft f.ringedToposHom.toToposHom.inverseImage
            ((X.representableLocalizationInverseImageIso (f.u.obj V)).inv ≫
              Functor.whiskerRight
                  (𝟙 (RingedTopos.localizationMorphism X.ringedTopos
                    (representableSheaf X (f.u.obj V))).toToposHom.inverseImage)
                  (representableLocalizationRingedMorphism X
                    (f.u.obj V)).toToposHom.inverseImage ≫
                (Functor.associator
                  (RingedTopos.localizationMorphism X.ringedTopos
                    (f.inverseImageRepresentableSheaf V)).toToposHom.inverseImage
                  (X.ringedTopos.relocalizationMorphism
                    (f.inverseImageRepresentableSheafIso V).inv).toToposHom.inverseImage
                  (representableLocalizationRingedMorphism X
                    (f.u.obj V)).toToposHom.inverseImage).hom) ≫
          (Functor.associator f.ringedToposHom.toToposHom.inverseImage
                (RingedTopos.localizationMorphism X.ringedTopos
                  (f.inverseImageRepresentableSheaf V)).toToposHom.inverseImage
                (f.compareMid V).toToposHom.inverseImage).inv ≫
            Functor.whiskerRight
                (f.ringedToposHom.inverseImageCompLocalizationIso
                  (representableSheaf Y V)).hom
                (f.compareMid V).toToposHom.inverseImage ≫
              (Functor.associator
                    (RingedTopos.localizationMorphism Y.ringedTopos
                      (representableSheaf Y V)).toToposHom.inverseImage
                    (f.ringedToposHom.localized
                      (representableSheaf Y V)).toToposHom.inverseImage
                    (f.compareMid V).toToposHom.inverseImage).hom ≫
                Functor.whiskerLeft
                  (RingedTopos.localizationMorphism Y.ringedTopos
                    (representableSheaf Y V)).toToposHom.inverseImage
                  (f.localizedRepresentableCompInverseImageIso V).hom) =
      (f.locSquareCompareTopos V (f.localizedComparisonTwoIso V)).e.hom :=
  Eq.trans
    (Stacks.CategoryTheory.conjugateEquiv_comp₅_eq _ _ _ _ _ _ _ _ _ _ _
      (conjugateEquiv_twoIso_whiskerRight_comp (f.localizedComparisonTwoIso V)
        (RingedTopos.localizationMorphism Y.ringedTopos (representableSheaf Y V))
        (f.localizedComparisonTwoIso_e_hom_eq V))
      (conjugateEquiv_associator_e_hom (f.compareMid V)
        (f.ringedToposHom.localized (representableSheaf Y V))
        (RingedTopos.localizationMorphism Y.ringedTopos (representableSheaf Y V)))
      (conjugateEquiv_twoIso_whiskerLeft_comp (f.compareMid V)
        (f.ringedToposHom.localizedRingedToposSquare (representableSheaf Y V))
        (localizedRingedToposSquare_e_hom_eq f.ringedToposHom (representableSheaf Y V)))
      (conjugateEquiv_associator_symm_e_hom (f.compareMid V)
        (RingedTopos.localizationMorphism X.ringedTopos
          (f.inverseImageRepresentableSheaf V)) f.ringedToposHom)
      (conjugateEquiv_twoIso_whiskerRight_comp_source (f.kapMid V) f.ringedToposHom
        (f.kapMid_e_hom_eq' V)))
    (f.locSquareCompareTopos_e_hom_comp V).symm

/-! ### The inverse-image identity

Below this point the comparisons of inverse images are atoms. Every equation from here on — the
two associator cancellations, and the identity inside the compatibility itself — is an equation
*between* them, never inside them, and each is a composite of several whiskered
isomorphisms of functors between sheaf categories; left reducible, the elaborator descends into
the whole composite to check an identification two projections would settle. This is the same
measure, taken for the same reason, as in
`StacksFrontier/CategoryTheory/Sites/Modules/Localization/LocalizedRepresentableTwoIso.lean`. -/
attribute [local irreducible]
  AlgebraicGeometry.RingedToposHom.inverseImageCompLocalizationIso
  AlgebraicGeometry.RingedSite.representableLocalizationInverseImageIso
  AlgebraicGeometry.RingedSite.Hom.localizedRepresentableCompInverseImageIso
  CategoryTheory.SliceTopos.overPullbackCompSheafPullbackOverPostIso

/-- The 04J0 side's comparison of inverse images, with its associator dropped: the associator
of a composite of functors is the identity. -/
theorem Hom.locSquareCompareSite_alpha_eq :
    (CategoryTheory.SliceTopos.overPullbackCompSheafPullbackOverPostIso Y.J X.J f.u V
          f.isMorphismOfSites).inv ≫
        Functor.whiskerRight (Y.representableLocalizationInverseImageIso V).inv
            (f.localizedRingedToposHom V).toToposHom.inverseImage ≫
          (Functor.associator
            (RingedTopos.localizationMorphism Y.ringedTopos
              (representableSheaf Y V)).toToposHom.inverseImage
            (representableLocalizationRingedMorphism Y V).toToposHom.inverseImage
            (f.localizedRingedToposHom V).toToposHom.inverseImage).hom =
      (CategoryTheory.SliceTopos.overPullbackCompSheafPullbackOverPostIso Y.J X.J f.u V
            f.isMorphismOfSites).inv ≫
        Functor.whiskerRight (Y.representableLocalizationInverseImageIso V).inv
          (f.localizedRingedToposHom V).toToposHom.inverseImage :=
  CategoryTheory.comp_left_of_eq _
    (Eq.trans
      (CategoryTheory.comp_left_of_eq _
        (Stacks.CategoryTheory.associator_hom_eq_id _ _ _))
      (Category.comp_id _))

/-- The relocalization triangle of Stacks 04J4 contributes nothing to the middle
identification's comparison of inverse images: it is the identity whiskered by Stacks 04J3's
identification at `u(V)`, followed by an associator. -/
theorem Hom.representableLocalizationInverseImageIso_inv_comp_triangle :
    (X.representableLocalizationInverseImageIso (f.u.obj V)).inv ≫
        Functor.whiskerRight
            (𝟙 (RingedTopos.localizationMorphism X.ringedTopos
              (representableSheaf X (f.u.obj V))).toToposHom.inverseImage)
            (representableLocalizationRingedMorphism X
              (f.u.obj V)).toToposHom.inverseImage ≫
          (Functor.associator
            (RingedTopos.localizationMorphism X.ringedTopos
              (f.inverseImageRepresentableSheaf V)).toToposHom.inverseImage
            (X.ringedTopos.relocalizationMorphism
              (f.inverseImageRepresentableSheafIso V).inv).toToposHom.inverseImage
            (representableLocalizationRingedMorphism X
              (f.u.obj V)).toToposHom.inverseImage).hom =
      (X.representableLocalizationInverseImageIso (f.u.obj V)).inv :=
  Eq.trans
    (CategoryTheory.comp_left_of_eq _
      (Eq.trans
        (CategoryTheory.comp_right_of_eq (Functor.whiskerRight_id' _) _)
        (Eq.trans
          (CategoryTheory.comp_left_of_eq _
            (Stacks.CategoryTheory.associator_hom_eq_id _ _ _))
          (Category.comp_id _))))
    (Category.comp_id _)

/-- **Stacks 04J9's compatibility of the two localization squares.** The square of Stacks 04J0,
read through the identification of Stacks 04J3 at `V`, *is* the square of Stacks 04IF read
through Stacks 04J7's comparison of the two localized morphisms and the identification of
Stacks 04J3 at the middle corner. This is the hypothesis `hLocSquares` of
`AlgebraicGeometry.RingedSite.Hom.exists_relocalizedComparison`, discharged.

The two conjugate descriptions are applied *first*, so that both composites of inverse images
arrive instantiated from `Hom.locSquareCompareSite_e_hom_eq` and
`Hom.locSquareCompareTopos_e_hom_eq` instead of being written out here; the associators are then
dropped from the 04J0 side by `Hom.locSquareCompareSite_alpha_eq` and from the 04IF side by the
relocalization triangle together with `Stacks.CategoryTheory.associator_inv_eq_id` and
`Stacks.CategoryTheory.associator_hom_eq_id`, each step supplying the factor it does not touch as
`_`; and the identity of the two associator-free composites is `Hom.keyNat` with three of its
five edges inverted. Stated as a lemma of its own, that associator-free identity has a signature
the elaborator cannot even read inside its budget — see the implementation note at the top of
this file — so it is taken here, where no part of it is ever written as a type. -/
theorem Hom.locSquareCompareSite_eq_locSquareCompareTopos :
    f.locSquareCompareSite V =
      f.locSquareCompareTopos V (f.localizedComparisonTwoIso V) := by
  apply AlgebraicGeometry.RingedToposHom.TwoIso.ext_hom
  refine Eq.trans (f.locSquareCompareSite_e_hom_eq V).symm ?_
  refine Eq.trans ?_ (f.locSquareCompareTopos_e_hom_eq V)
  refine Stacks.CategoryTheory.conjugateEquiv_of_eq _ _ ?_
  refine Eq.trans (f.locSquareCompareSite_alpha_eq V) ?_
  refine Eq.trans ?_ (Eq.trans
      (CategoryTheory.comp_right_of_eq
        (congrArg
          (fun z ↦ Functor.whiskerLeft f.ringedToposHom.toToposHom.inverseImage z)
          (f.representableLocalizationInverseImageIso_inv_comp_triangle V)) _)
      (CategoryTheory.comp_left_of_eq _
        (Eq.trans
          (CategoryTheory.comp_right_of_eq
            (Stacks.CategoryTheory.associator_inv_eq_id _ _ _) _)
          (Eq.trans (Category.id_comp _)
            (CategoryTheory.comp_left_of_eq _
              (Eq.trans
                (CategoryTheory.comp_right_of_eq
                  (Stacks.CategoryTheory.associator_hom_eq_id _ _ _) _)
                (Category.id_comp _))))))).symm
  exact NatTrans.ext (funext fun A ↦
    Stacks.CategoryTheory.inv_comp_eq_of_comp₃
      ((f.localizedRepresentableCompInverseImageIso V).app
        ((RingedTopos.localizationMorphism Y.ringedTopos
          (representableSheaf Y V)).toToposHom.inverseImage.obj A))
      ((f.localizedRingedToposHom V).toToposHom.inverseImage.mapIso
        ((Y.representableLocalizationInverseImageIso V).app A))
      ((CategoryTheory.SliceTopos.overPullbackCompSheafPullbackOverPostIso Y.J X.J f.u V
        f.isMorphismOfSites).app A)
      ((f.compareMid V).toToposHom.inverseImage.mapIso
        ((f.ringedToposHom.inverseImageCompLocalizationIso (representableSheaf Y V)).app A).symm)
      ((X.representableLocalizationInverseImageIso (f.u.obj V)).app
        (f.ringedToposHom.toToposHom.inverseImage.obj A))
      (f.keyNat V A))

/-- **Stacks 04J9, with the Stacks 04J7 half of its input discharged.** The commutative diagram
of Stacks 04J1 and the commutative diagram of Stacks 04J8 agree via the identifications of
Stacks 04J3, given only the Stacks 04J5 half of what the source's proof cites:
`relocComparison`, the comparison of the two relocalizations as a 2-isomorphism of ringed topoi,
and `hRelocTriangles`, its compatibility with the relocalization triangle of Stacks 04IY and
that of Stacks 04J4.

This is `AlgebraicGeometry.RingedSite.Hom.exists_relocalizedComparison` with its other two
arguments supplied: `locComparison` is
`AlgebraicGeometry.RingedSite.Hom.localizedComparisonTwoIso`, Stacks 04J7 part (4), and
`hLocSquares` is `Hom.locSquareCompareSite_eq_locSquareCompareTopos` above.

It carries no `@[stacks 04J9]` attribute, and deliberately so: two of the source's four inputs
are still hypotheses here, so what is established is the implication, not Stacks 04J9. What this
repository carries of Stacks 04J9 unconditionally is still
`AlgebraicGeometry.RingedSite.Hom.relocalized_fSharpInverseImage_forget`, on structure maps, and
`AlgebraicGeometry.RingedSite.Hom.relocalizedCompInverseImageIso`, on inverse images. What
remains owed is the sheaf-morphism description of Stacks 04J5 part (4) — the upgrade of
`AlgebraicGeometry.RingedSite.Hom.relocCompareInverseImageIso` to a 2-isomorphism of ringed
topoi, and its compatibility with the two relocalization triangles. -/
theorem Hom.exists_relocalizedComparison_of_relocTriangles {U : X.C} (c : U ⟶ f.u.obj V)
    (relocComparison : AlgebraicGeometry.RingedToposHom.TwoIso
      (A := ringedTopos (X.over U))
      (B := RingedTopos.localizedRingedTopos X.ringedTopos
        (f.inverseImageRepresentableSheaf V))
      (AlgebraicGeometry.RingedToposHom.comp (X := ringedTopos (X.over U))
        (Y := ringedTopos (X.over (f.u.obj V)))
        (Z := RingedTopos.localizedRingedTopos X.ringedTopos
          (f.inverseImageRepresentableSheaf V))
        (f.compareMid V) (X.relocalizationRingedToposHom c))
      (AlgebraicGeometry.RingedToposHom.comp (X := ringedTopos (X.over U))
        (Y := RingedTopos.localizedRingedTopos X.ringedTopos (representableSheaf X U))
        (Z := RingedTopos.localizedRingedTopos X.ringedTopos
          (f.inverseImageRepresentableSheaf V))
        (X.ringedTopos.relocalizationMorphism (f.relocalizationSheafMap c))
        (representableLocalizationRingedMorphism X U)))
    (hRelocTriangles :
      f.relocTriangleCompareSite c = f.relocTriangleCompareTopos c relocComparison) :
    f.RelocalizedComparisonStatement c :=
  f.exists_relocalizedComparison c relocComparison (f.localizedComparisonTwoIso V)
    hRelocTriangles (f.locSquareCompareSite_eq_locSquareCompareTopos V)

end AlgebraicGeometry.RingedSite

end
