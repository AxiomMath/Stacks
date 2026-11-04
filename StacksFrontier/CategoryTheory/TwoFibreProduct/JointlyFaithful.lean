module

public import StacksFrontier.CategoryTheory.TwoFibreProduct.Defs

/-!
# The two legs of a 2-fibre product are jointly faithful

Let `P` be a 2-fibre product of a cospan `f : x ⟶ z`, `g : y ⟶ z` in a bicategory
(`CategoryTheory.Bicategory.IsTwoFibreProduct`), that is, a terminal object of the category of
2-commutative squares over `(f, g)`. Two 1-morphisms `p q : t ⟶ P.pt` that agree after composing
with each projection, compatibly with the filler of `P`, are 2-isomorphic, by a 2-isomorphism
inducing the two given comparison 2-cells.

## Main definitions

* `CategoryTheory.Bicategory.TwoCommSq.precompose`: a 2-commutative square reindexed along a
  1-morphism into its apex.
* `CategoryTheory.Bicategory.TwoCommSq.PreHom.ofPrecompose` and
  `CategoryTheory.Bicategory.TwoCommSq.PreHom.ofPrecomposeCells`: two pre-morphisms out of a
  reindexed square.

## Main results

* `CategoryTheory.Bicategory.twoFibreProduct_jointlyFaithful`: compatible comparison 2-cells
  `p ≫ P.fst ≅ q ≫ P.fst` and `p ≫ P.snd ≅ q ≫ P.snd` are induced by a 2-isomorphism `p ≅ q`.
* `CategoryTheory.Bicategory.twoFibreProduct_twoIso_of_legs`: the same, forgetting which
  2-isomorphism it is.
* `CategoryTheory.Bicategory.twoFibreProduct_twoIso_of_preHom`: two pre-morphisms out of one
  square into a 2-fibre product have 2-isomorphic underlying 1-morphisms, by a 2-isomorphism
  inducing their comparison 2-cells.

## References

* [Stacks Project, Tag 003O](https://stacks.math.columbia.edu/tag/003O)
* [Stacks Project, Tag 003Q](https://stacks.math.columbia.edu/tag/003Q)
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits

namespace CategoryTheory.Bicategory

universe w v u

variable {B : Type u} [Bicategory.{w, v} B] {x y z : B} {f : x ⟶ z} {g : y ⟶ z}

/-- The 2-commutative square `P` over `(f, g)` reindexed along `p : t ⟶ P.pt`: the square with
apex `t`, legs `p ≫ P.fst` and `p ≫ P.snd`, and the filler of `P` whiskered by `p`. -/
@[implicit_reducible]
def TwoCommSq.precompose (P : TwoCommSq f g) {t : B} (p : t ⟶ P.pt) : TwoCommSq f g where
  pt := t
  fst := p ≫ P.fst
  snd := p ≫ P.snd
  iso := α_ p P.fst f ≪≫ whiskerLeftIso p P.iso ≪≫ (α_ p P.snd g).symm

/-- The filler of a reindexed square, as a 2-cell: the filler of the given square whiskered by
the reindexing 1-morphism, between the two associators. -/
@[simp]
theorem TwoCommSq.precompose_iso_hom (P : TwoCommSq f g) {t : B} (p : t ⟶ P.pt) :
    (P.precompose p).iso.hom
      = (α_ p P.fst f).hom ≫ (p ◁ P.iso.hom) ≫ (α_ p P.snd g).inv := rfl

/-- The 1-morphism `p : t ⟶ P.pt` as a pre-morphism of 2-commutative squares
`P.precompose p ⟶ P`, with both comparison 2-cells the identity. -/
def TwoCommSq.PreHom.ofPrecompose (P : TwoCommSq f g) {t : B} (p : t ⟶ P.pt) :
    TwoCommSq.PreHom (P.precompose p) P where
  hom := p
  isoFst := Iso.refl _
  isoSnd := Iso.refl _
  compat := by simp

/-- If `q : t ⟶ P.pt` agrees with `p : t ⟶ P.pt` after composing with each projection of `P`, by
2-cells `θ₁`, `θ₂` compatible with the filler of `P`, then `q` is a pre-morphism of
2-commutative squares `P.precompose p ⟶ P` whose comparison 2-cells are `θ₁` and `θ₂`. -/
def TwoCommSq.PreHom.ofPrecomposeCells (P : TwoCommSq f g) {t : B} (p q : t ⟶ P.pt)
    (θ₁ : p ≫ P.fst ≅ q ≫ P.fst) (θ₂ : p ≫ P.snd ≅ q ≫ P.snd)
    (hcompat : (P.precompose p).iso.hom ≫ θ₂.hom ▷ g
      = θ₁.hom ▷ f ≫ (P.precompose q).iso.hom) :
    TwoCommSq.PreHom (P.precompose p) P where
  hom := q
  isoFst := θ₁
  isoSnd := θ₂
  compat := by
    simp only [TwoCommSq.precompose_iso_hom, Category.assoc] at hcompat ⊢
    rw [reassoc_of% hcompat]
    simp

/-- Let `P` be a 2-fibre product of `(f, g)` and let `p q : t ⟶ P.pt` be two 1-morphisms into
its apex. Comparison 2-cells `θ₁ : p ≫ P.fst ≅ q ≫ P.fst` and `θ₂ : p ≫ P.snd ≅ q ≫ P.snd` that
are compatible with the filler of `P` are induced by a 2-isomorphism `p ≅ q`. -/
theorem twoFibreProduct_jointlyFaithful {P : TwoCommSq f g} (hP : IsTwoFibreProduct P) {t : B}
    (p q : t ⟶ P.pt) (θ₁ : p ≫ P.fst ≅ q ≫ P.fst) (θ₂ : p ≫ P.snd ≅ q ≫ P.snd)
    (hcompat : (P.precompose p).iso.hom ≫ θ₂.hom ▷ g
      = θ₁.hom ▷ f ≫ (P.precompose q).iso.hom) :
    ∃ θ : p ≅ q, θ.hom ▷ P.fst = θ₁.hom ∧ θ.hom ▷ P.snd = θ₂.hom := by
  obtain ⟨θ, h1, h2⟩ := _root_.Quotient.exact (hP.hom_ext
    (_root_.Quotient.mk _ (TwoCommSq.PreHom.ofPrecompose P p))
    (_root_.Quotient.mk _ (TwoCommSq.PreHom.ofPrecomposeCells P p q θ₁ θ₂ hcompat)))
  simp only [TwoCommSq.PreHom.ofPrecompose, TwoCommSq.PreHom.ofPrecomposeCells,
    Iso.refl_hom, Category.id_comp] at h1 h2
  exact ⟨θ, h1, h2⟩

/-- Two 1-morphisms into the apex of a 2-fibre product that agree after composing with each
projection, compatibly with the filler, are 2-isomorphic. -/
theorem twoFibreProduct_twoIso_of_legs {P : TwoCommSq f g} (hP : IsTwoFibreProduct P) {t : B}
    (p q : t ⟶ P.pt) (θ₁ : p ≫ P.fst ≅ q ≫ P.fst) (θ₂ : p ≫ P.snd ≅ q ≫ P.snd)
    (hcompat : (P.precompose p).iso.hom ≫ θ₂.hom ▷ g
      = θ₁.hom ▷ f ≫ (P.precompose q).iso.hom) :
    Nonempty (p ≅ q) :=
  ⟨(twoFibreProduct_jointlyFaithful hP p q θ₁ θ₂ hcompat).choose⟩

/-- Two pre-morphisms of 2-commutative squares out of one square and into a 2-fibre product have
2-isomorphic underlying 1-morphisms, by a 2-isomorphism inducing their comparison 2-cells. -/
theorem twoFibreProduct_twoIso_of_preHom {P : TwoCommSq f g} (hP : IsTwoFibreProduct P)
    {X : TwoCommSq f g} (u v : TwoCommSq.PreHom X P) :
    ∃ θ : u.hom ≅ v.hom, u.isoFst.hom ≫ θ.hom ▷ P.fst = v.isoFst.hom ∧
      u.isoSnd.hom ≫ θ.hom ▷ P.snd = v.isoSnd.hom :=
  _root_.Quotient.exact (hP.hom_ext (_root_.Quotient.mk _ u) (_root_.Quotient.mk _ v))

end CategoryTheory.Bicategory

end
