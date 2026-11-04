module

public import StacksFrontier.CategoryTheory.TwoFibreProduct.Pasting

/-!
# Changing a cospan leg by a 2-isomorphism

A 2-commutative square (**Stacks 003O**) over a cospan `(f, g)` in a `(2,1)`-category has a
filler `fst ≫ f ≅ snd ≫ g`, so it depends on the two legs of the cospan *on the nose*. Every
base-change argument that reaches its cospan through the filler of another square, however,
produces that leg only up to an invertible 2-morphism: the two squares being compared are
squares over cospans whose legs agree only up to a 2-isomorphism.

This file supplies the missing permanence property: a 2-commutative square over `(f, g)` can be
reindexed along an invertible 2-morphism `θ : f ≅ f'` into a square over `(f', g)`, and a
2-fibre product (**Stacks 003Q**) stays one under that reindexing.

## Main definitions

* `CategoryTheory.Bicategory.TwoCommSq.reindexFst`: the same apex and the same two projections,
  read as a square over `(f', g)`.
* `CategoryTheory.Bicategory.TwoCommSq.reindexSnd`: the same, for the second leg of the cospan.

## Main results

* `CategoryTheory.Bicategory.isTwoFibreProduct_reindexFst`
* `CategoryTheory.Bicategory.isTwoFibreProduct_reindexSnd`

## Implementation notes

Reindexing changes neither the apex nor the two projections of a square, so a pre-morphism of
squares over `(f', g)` and a pre-morphism of the reindexed squares over `(f, g)` carry *literally
the same data* — an underlying 1-morphism and two comparison 2-isomorphisms — and differ only in
the Stacks 003O compatibility square they are asked to satisfy. Those two compatibility squares
are equivalent (`reindexFst_compat_iff`), by the exchange law for whiskerings followed by
naturality of the associator in its last argument. So reindexing is implemented as a pair of
mutually inverse maps on pre-morphisms, `TwoCommSq.PreHom.reindexFst` and
`TwoCommSq.PreHom.unreindexFst`, whose round trips are `rfl` by structure eta together with
proof irrelevance of the compatibility field, and which descend to the quotient because the
2-cell equivalence is stated against projections that reindexing leaves alone.

`reindexFst_compat_iff` is deliberately stated for bare 1- and 2-morphisms rather than for the
two squares: with the squares in the statement the goal is not type-correct at `implicit`
transparency, because `(S.reindexFst θ).snd` and `S.snd` are only equal by unfolding, and then
neither `rw [Category.assoc]` nor `rw [whiskerLeft_comp]` fires. In the bare form every rewrite
applies on the nose, and the two squares meet the lemma at `exact`-level unification, where
unfolding is available.

That equivalence is what makes the terminality transport cheap. Reindexing is *not* strictly
involutive on objects: `(P.reindexFst θ).reindexFst θ.symm` and `P` have the same apex and the
same projections but fillers agreeing only up to `θ.hom ≫ θ.inv = 𝟙 f`, so they are equal only
propositionally, and transporting terminality along a round trip would mean transporting
`IsTerminal` across that equality. Terminality of `P.reindexFst θ` is therefore proved
*directly*: a test square `S` over `(f', g)` is reindexed backwards to `S.reindexFst θ.symm` over
`(f, g)`, where the hypothesis supplies a unique morphism to `P`, and `reindexFstHom` carries it
forward to a morphism `S ⟶ P.reindexFst θ`; uniqueness is `unreindexFstHom` applied to an
arbitrary morphism. No equality of squares, and hence no transport of `IsTerminal`, occurs.

Reindexing the second leg of the cospan is reindexing the first, conjugated by
`CategoryTheory.Bicategory.TwoCommSq.swap`.

## References

* [Stacks Project, Tag 003O](https://stacks.math.columbia.edu/tag/003O)
* [Stacks Project, Tag 003Q](https://stacks.math.columbia.edu/tag/003Q)
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits

namespace CategoryTheory.Bicategory

universe w v u

variable {A : Type u} [Bicategory.{w, v} A]

/-! ### Reindexing the first leg of the cospan -/

section ReindexFst

variable {X Y Z : A} {f f' : X ⟶ Z} {g : Y ⟶ Z}

/-- Whiskering an invertible 2-morphism `θ : f ≅ f'` past a comparison 2-cell `η : p ⟶ u ≫ v`:
the exchange law moves `θ⁻¹` from the source of `η` to its target, and naturality of the
associator in its last argument then splits it off the composite `u ≫ v`. -/
private theorem whiskerLeft_inv_whiskerRight_associator {W V : A} (u : W ⟶ V) (v : V ⟶ X)
    {p : W ⟶ X} (η : p ⟶ u ≫ v) (θ : f ≅ f') :
    p ◁ θ.inv ≫ η ▷ f ≫ (α_ u v f).hom
      = η ▷ f' ≫ (α_ u v f').hom ≫ u ◁ v ◁ θ.inv := by
  rw [whisker_exchange_assoc, associator_naturality_right]

/-- **The Stacks 003O compatibility square is insensitive to reindexing a cospan leg.**
Data consisting of a 1-morphism `u` of apexes and two comparison 2-cells `aFst`, `aSnd`
satisfies the compatibility square for the two squares `(tfst, tsnd, tfst ◁ θ.hom ≫ tiso)` over
`(f, g)` and `(sfst, ssnd, siso)` over `(f, g)` exactly when it satisfies it for the two squares
`(tfst, tsnd, tiso)` over `(f', g)` and `(sfst, ssnd, sfst ◁ θ.inv ≫ siso)` over `(f', g)`.

Stated for bare 1- and 2-morphisms so that it applies to a 2-commutative square and its
reindexing in either direction; see the implementation notes of this file. -/
theorem reindexFst_compat_iff {W V : A} (θ : f ≅ f') (u : W ⟶ V)
    (tfst : W ⟶ X) (tsnd : W ⟶ Y) (sfst : V ⟶ X) (ssnd : V ⟶ Y)
    (tiso : tfst ≫ f' ⟶ tsnd ≫ g) (siso : sfst ≫ f ⟶ ssnd ≫ g)
    (aFst : tfst ⟶ u ≫ sfst) (aSnd : tsnd ⟶ u ≫ ssnd) :
    ((tfst ◁ θ.hom ≫ tiso) ≫ (aSnd ▷ g) ≫ (α_ u ssnd g).hom =
        (aFst ▷ f) ≫ (α_ u sfst f).hom ≫ (u ◁ siso)) ↔
      (tiso ≫ (aSnd ▷ g) ≫ (α_ u ssnd g).hom =
        (aFst ▷ f') ≫ (α_ u sfst f').hom ≫ (u ◁ (sfst ◁ θ.inv ≫ siso))) := by
  have hR : tfst ◁ θ.inv ≫ (aFst ▷ f) ≫ (α_ u sfst f).hom ≫ (u ◁ siso)
      = (aFst ▷ f') ≫ (α_ u sfst f').hom ≫ (u ◁ (sfst ◁ θ.inv ≫ siso)) := by
    rw [whiskerLeft_comp, reassoc_of% whiskerLeft_inv_whiskerRight_associator u sfst aFst θ]
  rw [Category.assoc, ← hR]
  constructor
  · intro h
    rw [← h, whiskerLeft_inv_hom_assoc]
  · intro h
    rw [h, whiskerLeft_hom_inv_assoc]

/-- **Reindexing a 2-commutative square along a 2-isomorphism of the first cospan leg.**
Given a square `P` over the cospan `(f, g)` and an invertible 2-morphism `θ : f ≅ f'`, the same
apex and the same two projections form a 2-commutative square over `(f', g)`, whose filler is
that of `P` precomposed with `θ⁻¹` whiskered into the first projection. -/
def TwoCommSq.reindexFst (P : TwoCommSq f g) (θ : f ≅ f') : TwoCommSq f' g where
  pt := P.pt
  fst := P.fst
  snd := P.snd
  iso := (whiskerLeftIso P.fst θ).symm ≪≫ P.iso

/-- The apex of `P.reindexFst θ` is the apex of `P`. -/
@[simp]
theorem TwoCommSq.reindexFst_pt (P : TwoCommSq f g) (θ : f ≅ f') : (P.reindexFst θ).pt = P.pt :=
  rfl

/-- The first projection of `P.reindexFst θ` is the first projection of `P`. -/
@[simp]
theorem TwoCommSq.reindexFst_fst (P : TwoCommSq f g) (θ : f ≅ f') : (P.reindexFst θ).fst = P.fst :=
  rfl

/-- The second projection of `P.reindexFst θ` is the second projection of `P`. -/
@[simp]
theorem TwoCommSq.reindexFst_snd (P : TwoCommSq f g) (θ : f ≅ f') : (P.reindexFst θ).snd = P.snd :=
  rfl

/-- The filler of `P.reindexFst θ` is `P.fst ◁ θ.inv ≫ P.iso.hom`. -/
@[simp]
theorem TwoCommSq.reindexFst_iso_hom (P : TwoCommSq f g) (θ : f ≅ f') :
    (P.reindexFst θ).iso.hom = P.fst ◁ θ.inv ≫ P.iso.hom :=
  rfl

/-- The inverse filler of `P.reindexFst θ` is `P.iso.inv ≫ P.fst ◁ θ.hom`. -/
@[simp]
theorem TwoCommSq.reindexFst_iso_inv (P : TwoCommSq f g) (θ : f ≅ f') :
    (P.reindexFst θ).iso.inv = P.iso.inv ≫ P.fst ◁ θ.hom :=
  rfl

/-- A pre-morphism of 2-commutative squares `T.reindexFst θ.symm ⟶ S` over `(f, g)`, read as a
pre-morphism `T ⟶ S.reindexFst θ` over `(f', g)`. The underlying 1-morphism and the two
comparison 2-isomorphisms are unchanged; only the compatibility square is re-proved. -/
def TwoCommSq.PreHom.reindexFst (θ : f ≅ f') {T : TwoCommSq f' g} {S : TwoCommSq f g}
    (m : TwoCommSq.PreHom (T.reindexFst θ.symm) S) : TwoCommSq.PreHom T (S.reindexFst θ) where
  hom := m.hom
  isoFst := m.isoFst
  isoSnd := m.isoSnd
  compat := (reindexFst_compat_iff θ m.hom T.fst T.snd S.fst S.snd T.iso.hom S.iso.hom
    m.isoFst.hom m.isoSnd.hom).mp m.compat

/-- The inverse of `CategoryTheory.Bicategory.TwoCommSq.PreHom.reindexFst`: a pre-morphism
`T ⟶ S.reindexFst θ` over `(f', g)`, read as a pre-morphism `T.reindexFst θ.symm ⟶ S` over
`(f, g)`. -/
def TwoCommSq.PreHom.unreindexFst (θ : f ≅ f') {T : TwoCommSq f' g} {S : TwoCommSq f g}
    (m : TwoCommSq.PreHom T (S.reindexFst θ)) : TwoCommSq.PreHom (T.reindexFst θ.symm) S where
  hom := m.hom
  isoFst := m.isoFst
  isoSnd := m.isoSnd
  compat := (reindexFst_compat_iff θ m.hom T.fst T.snd S.fst S.snd T.iso.hom S.iso.hom
    m.isoFst.hom m.isoSnd.hom).mpr m.compat

/-- Reindexing a pre-morphism and reading it back gives it again: neither operation touches the
data, and the compatibility square is a proof. -/
theorem TwoCommSq.PreHom.reindexFst_unreindexFst (θ : f ≅ f') {T : TwoCommSq f' g}
    {S : TwoCommSq f g} (m : TwoCommSq.PreHom T (S.reindexFst θ)) :
    (m.unreindexFst θ).reindexFst θ = m :=
  rfl

/-- Reindexing respects the 2-cell equivalence of pre-morphisms: the mediating 2-cell is the
same one, and the two conditions it satisfies are stated against projections that reindexing
does not change. -/
theorem TwoCommSq.PreHom.reindexFst_rel (θ : f ≅ f') {T : TwoCommSq f' g} {S : TwoCommSq f g}
    {m n : TwoCommSq.PreHom (T.reindexFst θ.symm) S} (h : TwoCommSq.PreHom.Rel m n) :
    TwoCommSq.PreHom.Rel (m.reindexFst θ) (n.reindexFst θ) :=
  h

/-- The analogue of `CategoryTheory.Bicategory.TwoCommSq.PreHom.reindexFst_rel` for
`CategoryTheory.Bicategory.TwoCommSq.PreHom.unreindexFst`. -/
theorem TwoCommSq.PreHom.unreindexFst_rel (θ : f ≅ f') {T : TwoCommSq f' g} {S : TwoCommSq f g}
    {m n : TwoCommSq.PreHom T (S.reindexFst θ)} (h : TwoCommSq.PreHom.Rel m n) :
    TwoCommSq.PreHom.Rel (m.unreindexFst θ) (n.unreindexFst θ) :=
  h

/-- Reindexing, on a hom-set of the category of 2-commutative squares. -/
def reindexFstHom (θ : f ≅ f') {T : TwoCommSq f' g} {S : TwoCommSq f g}
    (h : T.reindexFst θ.symm ⟶ S) : T ⟶ S.reindexFst θ :=
  Quotient.map (TwoCommSq.PreHom.reindexFst θ)
    (fun _ _ h => TwoCommSq.PreHom.reindexFst_rel θ h) h

/-- The inverse of `CategoryTheory.Bicategory.reindexFstHom`, on a hom-set of the category of
2-commutative squares. -/
def unreindexFstHom (θ : f ≅ f') {T : TwoCommSq f' g} {S : TwoCommSq f g}
    (h : T ⟶ S.reindexFst θ) : T.reindexFst θ.symm ⟶ S :=
  Quotient.map (TwoCommSq.PreHom.unreindexFst θ)
    (fun _ _ h => TwoCommSq.PreHom.unreindexFst_rel θ h) h

/-- `CategoryTheory.Bicategory.reindexFstHom` is a retraction of
`CategoryTheory.Bicategory.unreindexFstHom`. This is the only thing the terminality transport
needs: it makes every morphism into `S.reindexFst θ` the image of one into `S`. -/
theorem reindexFstHom_unreindexFstHom (θ : f ≅ f') {T : TwoCommSq f' g} {S : TwoCommSq f g}
    (h : T ⟶ S.reindexFst θ) : reindexFstHom θ (unreindexFstHom θ h) = h := by
  refine Quotient.inductionOn (s := TwoCommSq.PreHom.setoid T (S.reindexFst θ))
    (motive := fun h => reindexFstHom θ (unreindexFstHom θ h) = h) h fun m => ?_
  rfl

/-- **A 2-fibre product stays one when the first leg of its cospan is changed by an invertible
2-morphism.** If `P` is a 2-fibre product of the cospan `(f, g)` and `θ : f ≅ f'`, then
`P.reindexFst θ` is a 2-fibre product of `(f', g)`. -/
def isTwoFibreProduct_reindexFst {P : TwoCommSq f g} (θ : f ≅ f')
    (hP : IsTwoFibreProduct P) : IsTwoFibreProduct (P.reindexFst θ) :=
  @IsTerminal.ofUniqueHom _ TwoCommSq.category _
    (fun S => reindexFstHom θ (hP.from (S.reindexFst θ.symm)))
    (fun _ m => (reindexFstHom_unreindexFstHom θ m).symm.trans
      (congrArg (reindexFstHom θ) (hP.hom_ext (unreindexFstHom θ m) (hP.from _))))

end ReindexFst

/-! ### Reindexing the second leg of the cospan -/

section ReindexSnd

variable {X Y Z : A} {f : X ⟶ Z} {g g' : Y ⟶ Z}

/-- **Reindexing a 2-commutative square along a 2-isomorphism of the second cospan leg.**
This is `CategoryTheory.Bicategory.TwoCommSq.reindexFst` conjugated by
`CategoryTheory.Bicategory.TwoCommSq.swap`. -/
def TwoCommSq.reindexSnd (P : TwoCommSq f g) (θ : g ≅ g') : TwoCommSq f g' :=
  (P.swap.reindexFst θ).swap

/-- The apex of `P.reindexSnd θ` is the apex of `P`. -/
@[simp]
theorem TwoCommSq.reindexSnd_pt (P : TwoCommSq f g) (θ : g ≅ g') : (P.reindexSnd θ).pt = P.pt :=
  rfl

/-- The first projection of `P.reindexSnd θ` is the first projection of `P`. -/
@[simp]
theorem TwoCommSq.reindexSnd_fst (P : TwoCommSq f g) (θ : g ≅ g') : (P.reindexSnd θ).fst = P.fst :=
  rfl

/-- The second projection of `P.reindexSnd θ` is the second projection of `P`. -/
@[simp]
theorem TwoCommSq.reindexSnd_snd (P : TwoCommSq f g) (θ : g ≅ g') : (P.reindexSnd θ).snd = P.snd :=
  rfl

/-- The filler of `P.reindexSnd θ` is `P.iso.hom ≫ P.snd ◁ θ.hom`. -/
@[simp]
theorem TwoCommSq.reindexSnd_iso_hom (P : TwoCommSq f g) (θ : g ≅ g') :
    (P.reindexSnd θ).iso.hom = P.iso.hom ≫ P.snd ◁ θ.hom :=
  rfl

/-- The inverse filler of `P.reindexSnd θ` is `P.snd ◁ θ.inv ≫ P.iso.inv`. -/
@[simp]
theorem TwoCommSq.reindexSnd_iso_inv (P : TwoCommSq f g) (θ : g ≅ g') :
    (P.reindexSnd θ).iso.inv = P.snd ◁ θ.inv ≫ P.iso.inv :=
  rfl

/-- **A 2-fibre product stays one when the second leg of its cospan is changed by an invertible
2-morphism.** If `P` is a 2-fibre product of the cospan `(f, g)` and `θ : g ≅ g'`, then
`P.reindexSnd θ` is a 2-fibre product of `(f, g')`. -/
noncomputable def isTwoFibreProduct_reindexSnd {P : TwoCommSq f g} (θ : g ≅ g')
    (hP : IsTwoFibreProduct P) : IsTwoFibreProduct (P.reindexSnd θ) :=
  isTwoFibreProduct_swap (isTwoFibreProduct_reindexFst θ (isTwoFibreProduct_swap hP))

end ReindexSnd

end CategoryTheory.Bicategory

end
