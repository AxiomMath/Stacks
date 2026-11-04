module

public import StacksFrontier.CategoryTheory.TwoFibreProduct.CancellationFiller
public import StacksFrontier.CategoryTheory.TwoFibreProduct.PostcomposeSnd
public import StacksFrontier.CategoryTheory.TwoFibreProduct.StrictTwoCommSq

/-!
# Comparing the two cancellations that a base change of a 2-commutative square produces
(Stacks 003O, 02XD)

Fix a cospan `bb' : 𝒱' ⟶ 𝒴`, `bb : 𝒱 ⟶ 𝒴` of categories fibred in groupoids and a 1-morphism
`ff : 𝒳 ⟶ 𝒴`, together with `aa' : 𝒰' ⟶ 𝒳`, `hh' : 𝒰' ⟶ 𝒱'` and an invertible
`ee' : hh' ≫ bb' ≅ aa' ≫ ff`. Let `Q` be a 2-commutative square over the cospan `(bb, ff)`
(**Stacks 003O**) and let `mm` be a pre-morphism from `Q` to the canonical 2-fibre product
`𝒱 ×_𝒴 𝒳` of that cospan.

There are then two 2-commutative squares over the cospan `(bb', bb)`, and the main result of this
file is the pre-morphism of Stacks 003O between them.

* The first is the second-factor cancellation of Stacks 02XD applied to the canonical square
  `𝒱 ×_𝒴 𝒳` along `aa'` — that is the square whose apex is `(𝒱 ×_𝒴 𝒳) ×_𝒳 𝒰'` — read over
  `(bb, bb')` by replacing its second leg `aa' ≫ ff` with `bb'` along `ee'`
  (`CategoryTheory.Bicategory.TwoCommSq.postcomposeSnd`) and then exchanging the two legs.
* The second is the *first*-factor cancellation of Stacks 02XD applied to the inner square
  `(𝒱 ×_𝒴 𝒳) ×_𝒳 𝒰'` along `mm`, read over `(bb', bb)` by comparing both legs with the cospan
  (`CategoryTheory.Bicategory.TwoCommSq.postcompose`).

The comparison is the outer projection of the second apex onto the first, and both of its
comparison 2-cells of Stacks 003O are built out of `mm`'s own: the first is an identity, and the
second is the filler of the outer product together with `mm.isoFst`. Its one compatibility square
is the whole mathematical content, and it is exactly `mm`'s compatibility square, one instance of
the exchange law, and two cancellations of an invertible 2-cell against its inverse.

## Main definitions

* `CategoryTheory.CatFiberedInGroupoids.cancelFstPostcomposePreHom`: the comparison above.

## Main results

* `CategoryTheory.CatFiberedInGroupoids.compat_strict`: the compatibility square of Stacks 003O
  for an arbitrary pre-morphism, with its two associators gone — the converse of
  `CategoryTheory.CatFiberedInGroupoids.preHomOfStrict`.
* `CategoryTheory.CatFiberedInGroupoids.cancelFstSquare_iso_hom`,
  `CategoryTheory.CatFiberedInGroupoids.cancelSndSquare_iso_inv`: the filler of each Stacks 02XD
  cancellation as a three-factor composite of 2-cells.
* `CategoryTheory.CatFiberedInGroupoids.postcomposeSnd_swap_iso_hom`: the filler of a square read
  over a cospan with its second leg changed and its two legs then exchanged.

## Implementation notes

This 2-category is strict, so each of the fillers above is a composite of whiskerings with no
associator in it; but then two consecutive factors of such a composite are typed through
*different* bracketings of one and the same 1-morphism, and the composite is therefore not
type-correct at the `implicit` transparency level at which Lean checks implicit arguments. The
consequence is that neither `rw` nor `simp` can act anywhere inside
such a composite: the motive it would need is rejected. (It is the same obstruction as the two
instance paths to the hom-quiver of an induced bicategory, recorded in
`StacksFrontier.CategoryTheory.TwoFibreProduct.StrictTwoCommSq`; the bracketing is the other half of
it.)

Two devices get around it, and together they are the whole technique of this file.

1. **Name the bookkeeping in a plain category.** `comp_cancel_of`, `chain_collapse` and
   `id_chain` are statements about abstract objects and morphisms of an abstract category, where
   `simp` has no bracketing to trip over; they are then *applied*, and application checks up to
   definitional equality, where bracketing is free. This is the pattern of
   `CategoryTheory.CatFiberedInGroupoids.inv_comp_eq_comp_inv` and
   `CategoryTheory.CatFiberedInGroupoids.map_id_comp_id_eq`, used for the same reason.
2. **State the compatibility square in plain variables.** `cancelFstPostcompose_compat` mentions
   no 2-fibre product and no change of cospan: it is an identity between composites of
   whiskerings of abstract 1-morphisms and 2-cells. Every projection and filler of the squares
   involved is definitionally one of its variables, so the field is discharged by applying it.

For the same reason the file contains no `rw` or `simp` acting under a whiskering. Where a
cancellation is against a whole composite it is supplied as a term, with `congrArg`.

No `@[stacks]` attribute, and in particular no `@[stacks 02XD]`: that tag stays on
`CategoryTheory.Limits.CategoricalPullback.assocComp` in
`StacksFrontier.CategoryTheory.TwoFibreProduct.Cancellation`, as the records of the two cancellation
files already rule for their own statements. Nothing here asserts a sentence of Stacks 003O or
02XD; these are comparisons between objects those tags provide.

## References

* [Stacks Project, Tag 003O](https://stacks.math.columbia.edu/tag/003O)
* [Stacks Project, Tag 003Q](https://stacks.math.columbia.edu/tag/003Q)
* [Stacks Project, Tag 02XD](https://stacks.math.columbia.edu/tag/02XD)
-/

@[expose] public section

open CategoryTheory CategoryTheory.Bicategory CategoryTheory.Limits

namespace CategoryTheory.CatFiberedInGroupoids

universe v₁ v₂ u₁ u₂

variable {C : Type u₁} [Category.{v₁} C]
  {𝒵 𝒰 𝒱 𝒱' 𝒳 𝒴 𝒰' 𝒥 𝒢 ℰ 𝒬 :
    CatFiberedInGroupoids.{v₁, max v₁ v₂, u₁, max (max u₁ u₂) (max v₁ v₂)} C}

/-! ### Fillers and compatibility squares, with the associators gone -/

/-- **The compatibility square of Stacks 003O for a pre-morphism, without its two associators.**
In the strict 2-category of categories fibred in groupoids both associators of the condition are
identity 2-cells, and this is the condition with them cancelled. It is the converse of
`CategoryTheory.CatFiberedInGroupoids.preHomOfStrict`, and it is what lets a consumer feed the
compatibility square of a given pre-morphism to a statement written in the associator-free
form. -/
theorem compat_strict {p : 𝒱 ⟶ 𝒴} {q : 𝒳 ⟶ 𝒴} {T S : Bicategory.TwoCommSq p q}
    (u : Bicategory.TwoCommSq.PreHom T S) :
    T.iso.hom ≫ u.isoSnd.hom ▷ q = u.isoFst.hom ▷ p ≫ u.hom ◁ S.iso.hom := by
  have h := u.compat
  change T.iso.hom ≫ (u.isoSnd.hom ▷ q) ≫ 𝟙 ((u.hom ≫ S.snd) ≫ q)
      = (u.isoFst.hom ▷ p) ≫ 𝟙 (u.hom ≫ S.fst ≫ p) ≫ (u.hom ◁ S.iso.hom) at h
  have h2 : T.iso.hom ≫ u.isoSnd.hom ▷ q
      = u.isoFst.hom ▷ p ≫ 𝟙 (u.hom ≫ S.fst ≫ p) ≫ u.hom ◁ S.iso.hom := by simpa using h
  exact h2.trans (congrArg (fun t => u.isoFst.hom ▷ p ≫ t) (Category.id_comp (u.hom ◁ S.iso.hom)))

/-- **The filler of the first-factor cancellation of Stacks 02XD, as a composite of three
whiskerings.** This is `CategoryTheory.CatFiberedInGroupoids.cancelFstSquare_iso` read on the
`hom` component, with the three associators that the strict 2-category makes identities already
cancelled. -/
theorem cancelFstSquare_iso_hom (g : 𝒵 ⟶ 𝒴) (f : 𝒳 ⟶ 𝒴) (c : 𝒰 ⟶ 𝒵) (G : 𝒰 ⟶ 𝒴)
    (θ : c ≫ g ≅ G) :
    (cancelFstSquare.{v₁, v₂, u₁, u₂} g f c G θ).iso.hom
      = ((twoFibreProductSquare.{v₁, v₂, u₁, u₂}
            (twoFibreProductSquare.{v₁, v₂, u₁, u₂} g f).fst c).fst
            ◁ (twoFibreProductSquare.{v₁, v₂, u₁, u₂} g f).iso.inv)
        ≫ ((twoFibreProductSquare.{v₁, v₂, u₁, u₂}
            (twoFibreProductSquare.{v₁, v₂, u₁, u₂} g f).fst c).iso.hom ▷ g)
        ≫ ((twoFibreProductSquare.{v₁, v₂, u₁, u₂}
            (twoFibreProductSquare.{v₁, v₂, u₁, u₂} g f).fst c).snd ◁ θ.hom) := rfl

/-- **The inverse filler of the second-factor cancellation of Stacks 02XD, as a composite of
three whiskerings.** The `inv` companion of
`CategoryTheory.CatFiberedInGroupoids.cancelSndSquare_iso`, which is the direction a consumer
reading the square through `CategoryTheory.Bicategory.TwoCommSq.swap` needs. -/
theorem cancelSndSquare_iso_inv (g : 𝒵 ⟶ 𝒴) (f : 𝒳 ⟶ 𝒴) (c : 𝒰 ⟶ 𝒳) (G : 𝒰 ⟶ 𝒴)
    (θ : c ≫ f ≅ G) :
    (cancelSndSquare.{v₁, v₂, u₁, u₂} g f c G θ).iso.inv
      = (((twoFibreProductSquare.{v₁, v₂, u₁, u₂}
            (twoFibreProductSquare.{v₁, v₂, u₁, u₂} g f).snd c).snd ◁ θ.inv)
          ≫ ((twoFibreProductSquare.{v₁, v₂, u₁, u₂}
            (twoFibreProductSquare.{v₁, v₂, u₁, u₂} g f).snd c).iso.inv ▷ f))
        ≫ ((twoFibreProductSquare.{v₁, v₂, u₁, u₂}
            (twoFibreProductSquare.{v₁, v₂, u₁, u₂} g f).snd c).fst
            ◁ (twoFibreProductSquare.{v₁, v₂, u₁, u₂} g f).iso.inv) := rfl

/-- **The filler of a square read over a cospan with its second leg changed and its two legs then
exchanged.** The exchange inverts the filler of
`CategoryTheory.Bicategory.TwoCommSq.postcomposeSnd`, whose associator is an identity here, so
what is left is the comparison 2-cell of the cospan whiskered by the second leg followed by the
inverse of the given filler. -/
theorem postcomposeSnd_swap_iso_hom {F : 𝒱 ⟶ 𝒴} {G : 𝒰 ⟶ 𝒴} (Z : Bicategory.TwoCommSq F G)
    {q : 𝒱' ⟶ 𝒴} (τ : 𝒰 ⟶ 𝒱') (δ : τ ≫ q ≅ G) :
    (Z.postcomposeSnd τ δ).swap.iso.hom = (Z.snd ◁ δ.hom) ≫ Z.iso.inv :=
  congrArg (· ≫ Z.iso.inv) (Category.id_comp (Z.snd ◁ δ.hom))

/-! ### Bookkeeping, named in a plain category -/

/-- Cancelling the second half of a four-term composite: if `d ≫ e = a ≫ b` and `e ≫ c` is the
identity, then `a ≫ b ≫ c = d`. Stated for an abstract category so that the associativity
rearrangement is available to `rw`, which it is not inside a composite of whiskerings. -/
private theorem comp_cancel_of {D : Type*} [Category D] {P Q R S : D}
    (a : P ⟶ Q) (b : Q ⟶ R) (c : R ⟶ S) (d : P ⟶ S) (e : S ⟶ R)
    (h1 : d ≫ e = a ≫ b) (h2 : e ≫ c = 𝟙 S) : a ≫ b ≫ c = d := by
  rw [← Category.assoc, ← h1, Category.assoc, h2, Category.comp_id]

/-- Collapsing the middle of a seven-term composite in two steps. Stated for an abstract category
for the same reason as `comp_cancel_of`. -/
private theorem chain_collapse {D : Type*} [Category D] {X0 X1 X2 X3 X4 X5 X6 X7 : D}
    (a : X0 ⟶ X1) (b1 : X1 ⟶ X2) (b2 : X2 ⟶ X3) (b3 : X3 ⟶ X4) (c : X4 ⟶ X5)
    (d1 : X5 ⟶ X6) (d2 : X6 ⟶ X7) (m : X3 ⟶ X6) (h1 : X2 ⟶ X7)
    (hm : b3 ≫ c ≫ d1 = m) (hh : b2 ≫ m ≫ d2 = h1) :
    (a ≫ (b1 ≫ b2 ≫ b3) ≫ c) ≫ d1 ≫ d2 = a ≫ b1 ≫ h1 := by
  rw [← hh, ← hm]; simp

/-- Removing the two identities that a strict bicategory's unitors and associators leave in a
composite of three factors. Stated for an abstract category for the same reason as
`comp_cancel_of`. -/
private theorem id_chain {D : Type*} [Category D] {X0 X1 X2 X3 : D}
    (a : X0 ⟶ X1) (b1 : X1 ⟶ X2) (h1 : X2 ⟶ X3) :
    𝟙 X0 ≫ a ≫ (𝟙 X1 ≫ b1) ≫ h1 = a ≫ b1 ≫ h1 := by simp

/-! ### The compatibility square, in plain variables -/

/-- **The compatibility square of Stacks 003O for
`CategoryTheory.CatFiberedInGroupoids.cancelFstPostcomposePreHom`, with every 2-fibre product
abstracted away.** `jf`, `js`, `ji` are the two legs and the filler of the canonical square
`𝒱 ×_𝒴 𝒳`; `gf`, `gs`, `gi` those of the second-factor cancellation `(𝒱 ×_𝒴 𝒳) ×_𝒳 𝒰'`; `qf`,
`qs`, `qi` those of the given square `Q`; `mh`, `mf`, `ms` the data of the given pre-morphism and
`hm` its compatibility square; and `ef`, `es`, `ei` the two legs and the filler of the outer
product over `mh`.

The content is `hm`, one instance of the exchange law, and two cancellations of an invertible
2-cell against its inverse. -/
private theorem cancelFstPostcompose_compat
    (bb : 𝒱 ⟶ 𝒴) (bb' : 𝒱' ⟶ 𝒴) (ff : 𝒳 ⟶ 𝒴) (aa' : 𝒰' ⟶ 𝒳) (hh' : 𝒰' ⟶ 𝒱')
    (ee' : hh' ≫ bb' ≅ aa' ≫ ff)
    (jf : 𝒥 ⟶ 𝒱) (js : 𝒥 ⟶ 𝒳) (ji : jf ≫ bb ≅ js ≫ ff)
    (gf : 𝒢 ⟶ 𝒥) (gs : 𝒢 ⟶ 𝒰') (gi : gf ≫ js ≅ gs ≫ aa')
    (qf : 𝒬 ⟶ 𝒱) (qs : 𝒬 ⟶ 𝒳) (qi : qf ≫ bb ≅ qs ≫ ff)
    (mh : 𝒬 ⟶ 𝒥) (mf : qf ≅ mh ≫ jf) (ms : qs ≅ mh ≫ js)
    (ef : ℰ ⟶ 𝒢) (es : ℰ ⟶ 𝒬) (ei : ef ≫ gf ≅ es ≫ mh)
    (hm : qi.hom ≫ ms.hom ▷ ff = mf.hom ▷ bb ≫ mh ◁ ji.hom) :
    ((ef ≫ gs) ◁ ee'.hom ≫ (ef ◁ gi.inv ≫ ei.hom ▷ js ≫ es ◁ ms.inv) ▷ ff ≫ es ◁ qi.inv)
        ≫ (es ◁ mf.hom ≫ ei.inv ▷ jf) ▷ bb
      = 𝟙 ((ef ≫ gs) ≫ hh') ▷ bb'
        ≫ ef ◁ (gs ◁ ee'.hom ≫ (gs ◁ 𝟙 (aa' ≫ ff) ≫ gi.inv ▷ ff) ≫ gf ◁ ji.inv) := by
  have hqi : qi.inv ≫ mf.hom ▷ bb = ms.hom ▷ ff ≫ mh ◁ ji.inv :=
    inv_comp_eq_comp_inv qi (whiskerLeftIso mh ji) _ _ hm.symm
  have hqi2 : ms.inv ▷ ff ≫ qi.inv ≫ mf.hom ▷ bb = mh ◁ ji.inv := by
    rw [hqi]
    exact Iso.inv_hom_id_assoc (whiskerRightIso ms ff) (mh ◁ ji.inv)
  have hdist : es ◁ (ms.inv ▷ ff ≫ qi.inv ≫ mf.hom ▷ bb)
      = es ◁ (ms.inv ▷ ff) ≫ es ◁ qi.inv ≫ es ◁ (mf.hom ▷ bb) := by
    rw [whiskerLeft_comp, whiskerLeft_comp]
  have hmid : (es ◁ ms.inv) ▷ ff ≫ es ◁ qi.inv ≫ (es ◁ mf.hom) ▷ bb
      = (es ≫ mh) ◁ ji.inv :=
    hdist.symm.trans (congrArg (fun t => es ◁ t) hqi2)
  have hex : (ei.hom ▷ js) ▷ ff ≫ ((es ≫ mh) ◁ ji.inv) ≫ (ei.inv ▷ jf) ▷ bb
      = (ef ≫ gf) ◁ ji.inv :=
    comp_cancel_of _ _ _ _ (ei.hom ▷ (jf ≫ bb)) (whisker_exchange ei.hom ji.inv)
      (whiskerRightIso ei (jf ≫ bb)).hom_inv_id
  have hL : ((ef ≫ gs) ◁ ee'.hom ≫ (ef ◁ gi.inv ≫ ei.hom ▷ js ≫ es ◁ ms.inv) ▷ ff
          ≫ es ◁ qi.inv) ≫ (es ◁ mf.hom ≫ ei.inv ▷ jf) ▷ bb
      = (ef ≫ gs) ◁ ee'.hom ≫ (ef ◁ gi.inv) ▷ ff ≫ (ef ≫ gf) ◁ ji.inv := by
    rw [show (ef ◁ gi.inv ≫ ei.hom ▷ js ≫ es ◁ ms.inv) ▷ ff
          = (ef ◁ gi.inv) ▷ ff ≫ (ei.hom ▷ js) ▷ ff ≫ (es ◁ ms.inv) ▷ ff from
        (comp_whiskerRight (ef ◁ gi.inv) (ei.hom ▷ js ≫ es ◁ ms.inv) ff).trans
          (congrArg (fun t => (ef ◁ gi.inv) ▷ ff ≫ t)
            (comp_whiskerRight (ei.hom ▷ js) (es ◁ ms.inv) ff)),
      comp_whiskerRight (es ◁ mf.hom) (ei.inv ▷ jf) bb]
    exact chain_collapse _ _ _ _ _ _ _ _ _ hmid hex
  have hR : 𝟙 ((ef ≫ gs) ≫ hh') ▷ bb'
        ≫ ef ◁ (gs ◁ ee'.hom ≫ (gs ◁ 𝟙 (aa' ≫ ff) ≫ gi.inv ▷ ff) ≫ gf ◁ ji.inv)
      = (ef ≫ gs) ◁ ee'.hom ≫ (ef ◁ gi.inv) ▷ ff ≫ (ef ≫ gf) ◁ ji.inv := by
    rw [id_whiskerRight ((ef ≫ gs) ≫ hh') bb',
      show ef ◁ (gs ◁ ee'.hom ≫ (gs ◁ 𝟙 (aa' ≫ ff) ≫ gi.inv ▷ ff) ≫ gf ◁ ji.inv)
          = ef ◁ (gs ◁ ee'.hom)
            ≫ (ef ◁ (gs ◁ 𝟙 (aa' ≫ ff)) ≫ ef ◁ (gi.inv ▷ ff)) ≫ ef ◁ (gf ◁ ji.inv) from
        (whiskerLeft_comp ef (gs ◁ ee'.hom)
            ((gs ◁ 𝟙 (aa' ≫ ff) ≫ gi.inv ▷ ff) ≫ gf ◁ ji.inv)).trans
          (congrArg (fun t => ef ◁ (gs ◁ ee'.hom) ≫ t)
            ((whiskerLeft_comp ef (gs ◁ 𝟙 (aa' ≫ ff) ≫ gi.inv ▷ ff) (gf ◁ ji.inv)).trans
              (congrArg (fun t => t ≫ ef ◁ (gf ◁ ji.inv))
                (whiskerLeft_comp ef (gs ◁ 𝟙 (aa' ≫ ff)) (gi.inv ▷ ff)))))]
    exact id_chain _ _ _
  exact hL.trans hR.symm

/-! ### The comparison -/

/-- **The comparison of the two cancellations a base change of a 2-commutative square produces
(Stacks 003O).** Let `Q` be a 2-commutative square over the cospan `(bb, ff)` and `mm` a
pre-morphism from `Q` to the canonical 2-fibre product `𝒱 ×_𝒴 𝒳`. The first-factor cancellation
of Stacks 02XD along `mm`, read over the cospan `(bb', bb)`, maps to the second-factor
cancellation along `aa'`, read over the same cospan by changing its second leg along `ee'` and
exchanging the two legs, by the outer projection — with the first comparison 2-cell of
Stacks 003O an identity and the second built from the filler of the outer product and `mm`'s own
first comparison 2-cell.

Both squares have `bb'` and `bb` as the cospan, so a chase that compares two 1-morphisms into the
canonical 2-fibre product `𝒱' ×_𝒴 𝒱` may compose this with other pre-morphisms rather than prove
a compatibility square by hand. The underlying 1-morphism is the outer projection, on the nose,
which is what a chase needs when that projection carries a property of its own. -/
def cancelFstPostcomposePreHom (bb : 𝒱 ⟶ 𝒴) (bb' : 𝒱' ⟶ 𝒴) (ff : 𝒳 ⟶ 𝒴) (aa' : 𝒰' ⟶ 𝒳)
    (hh' : 𝒰' ⟶ 𝒱') (ee' : hh' ≫ bb' ≅ aa' ≫ ff)
    (Q : Bicategory.TwoCommSq bb ff)
    (mm : Bicategory.TwoCommSq.PreHom Q (twoFibreProductSquare.{v₁, v₂, u₁, u₂} bb ff)) :
    Bicategory.TwoCommSq.PreHom
      ((cancelFstSquare.{v₁, v₂, u₁, u₂}
          (twoFibreProductSquare.{v₁, v₂, u₁, u₂} bb ff).snd aa' mm.hom Q.snd
          mm.isoSnd.symm).postcompose ff hh' Q.fst ee' Q.iso)
      ((cancelSndSquare.{v₁, v₂, u₁, u₂} bb ff aa' (aa' ≫ ff)
          (Iso.refl (aa' ≫ ff))).postcomposeSnd hh' ee').swap :=
  preHomOfStrict.{v₁, v₂, u₁, u₂}
    (twoFibreProductSquare.{v₁, v₂, u₁, u₂}
      (twoFibreProductSquare.{v₁, v₂, u₁, u₂}
        (twoFibreProductSquare.{v₁, v₂, u₁, u₂} bb ff).snd aa').fst mm.hom).fst
    (Iso.refl _)
    (Bicategory.whiskerLeftIso
        (twoFibreProductSquare.{v₁, v₂, u₁, u₂}
          (twoFibreProductSquare.{v₁, v₂, u₁, u₂}
            (twoFibreProductSquare.{v₁, v₂, u₁, u₂} bb ff).snd aa').fst mm.hom).snd mm.isoFst
      ≪≫ Bicategory.whiskerRightIso
        (twoFibreProductSquare.{v₁, v₂, u₁, u₂}
          (twoFibreProductSquare.{v₁, v₂, u₁, u₂}
            (twoFibreProductSquare.{v₁, v₂, u₁, u₂} bb ff).snd aa').fst mm.hom).iso.symm
        (twoFibreProductSquare.{v₁, v₂, u₁, u₂} bb ff).fst)
    (by
      rw [postcompose_iso_hom_strict.{v₁, v₂, u₁, u₂},
        cancelFstSquare_iso_hom.{v₁, v₂, u₁, u₂},
        postcomposeSnd_swap_iso_hom.{v₁, v₂, u₁, u₂},
        cancelSndSquare_iso_inv.{v₁, v₂, u₁, u₂}]
      exact cancelFstPostcompose_compat.{v₁, v₂, u₁, u₂} bb bb' ff aa' hh' ee'
        (twoFibreProductSquare.{v₁, v₂, u₁, u₂} bb ff).fst
        (twoFibreProductSquare.{v₁, v₂, u₁, u₂} bb ff).snd
        (twoFibreProductSquare.{v₁, v₂, u₁, u₂} bb ff).iso
        (twoFibreProductSquare.{v₁, v₂, u₁, u₂}
          (twoFibreProductSquare.{v₁, v₂, u₁, u₂} bb ff).snd aa').fst
        (twoFibreProductSquare.{v₁, v₂, u₁, u₂}
          (twoFibreProductSquare.{v₁, v₂, u₁, u₂} bb ff).snd aa').snd
        (twoFibreProductSquare.{v₁, v₂, u₁, u₂}
          (twoFibreProductSquare.{v₁, v₂, u₁, u₂} bb ff).snd aa').iso
        Q.fst Q.snd Q.iso mm.hom mm.isoFst mm.isoSnd
        (twoFibreProductSquare.{v₁, v₂, u₁, u₂}
          (twoFibreProductSquare.{v₁, v₂, u₁, u₂}
            (twoFibreProductSquare.{v₁, v₂, u₁, u₂} bb ff).snd aa').fst mm.hom).fst
        (twoFibreProductSquare.{v₁, v₂, u₁, u₂}
          (twoFibreProductSquare.{v₁, v₂, u₁, u₂}
            (twoFibreProductSquare.{v₁, v₂, u₁, u₂} bb ff).snd aa').fst mm.hom).snd
        (twoFibreProductSquare.{v₁, v₂, u₁, u₂}
          (twoFibreProductSquare.{v₁, v₂, u₁, u₂}
            (twoFibreProductSquare.{v₁, v₂, u₁, u₂} bb ff).snd aa').fst mm.hom).iso
        (compat_strict.{v₁, v₂, u₁, u₂} mm))

end CategoryTheory.CatFiberedInGroupoids

end
