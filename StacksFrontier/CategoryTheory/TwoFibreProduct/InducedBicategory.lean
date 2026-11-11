module

public import StacksCore.Tactic.StacksAttribute
public import StacksFrontier.CategoryTheory.TwoFibreProduct.Defs
public import StacksFrontier.CategoryTheory.TwoFibreProduct.IsTwoFibreProductOfEquivalence
public import Mathlib.CategoryTheory.Bicategory.InducedBicategory

/-!
# 2-fibre products in a full sub-2-category

Let `C` be a bicategory and `F : B → C` a map, and give `B` the induced bicategory structure
`CategoryTheory.Bicategory.InducedBicategory C F`, whose 1-morphisms and 2-morphisms are all of
those of `C` between the images. A 2-commutative square over a cospan of the induced bicategory
then has an *underlying* square over the image cospan in `C`, and a pre-morphism of squares
upstairs has an underlying pre-morphism of the squares downstairs.

Both passages are bijective, because `InducedBicategory` is *full* on 1-morphisms and
2-morphisms: they are plain re-wrappings of one-field structures, so each round trip is `rfl`.
Consequently a square whose underlying square is a 2-fibre product in `C` is itself a 2-fibre
product in the induced bicategory — the formal argument the Stacks project uses whenever it
notes that a 2-fibre product computed in a larger 2-category is also one in a full
sub-2-category.

## Main definitions

* `CategoryTheory.Bicategory.TwoCommSq.underlying`: the underlying square in `C`.
* `CategoryTheory.Bicategory.TwoCommSq.PreHom.underlying`,
  `CategoryTheory.Bicategory.TwoCommSq.PreHom.ofUnderlying`: the two directions on
  pre-morphisms (Stacks 003O), mutually inverse on the nose.
* `CategoryTheory.Bicategory.TwoCommSq.homUnderlying`,
  `CategoryTheory.Bicategory.TwoCommSq.homOfUnderlying`: the induced maps on the morphisms of
  the category of 2-commutative squares, i.e. on pre-morphisms modulo the 2-cell equivalence.
* `CategoryTheory.Bicategory.InducedBicategory.isoHom`: the 2-isomorphism of `C` underlying a
  2-isomorphism of the induced bicategory, the inverse of Mathlib's
  `CategoryTheory.Bicategory.InducedBicategory.isoMk`.

## Main results

* `CategoryTheory.Bicategory.isTwoFibreProduct_of_underlying`: a full sub-2-category inherits
  the 1-truncated 2-fibre products of the ambient one.
* `CategoryTheory.Bicategory.isTwoFibreProduct_underlying`: the converse, in the presence of a
  witness that the cospan has a 2-fibre product of the ambient bicategory underneath it.
* `CategoryTheory.Bicategory.isFinalTwoCommSq_of_underlying` and
  `CategoryTheory.Bicategory.legsDetectTwoCells_of_underlying`: the same inheritance for the
  2-fibre products of Stacks 003Q (final objects, with the uniqueness of the 2-isomorphism), and
  for the detection of 2-cells by the two legs.

## Implementation notes

The only arithmetic in the file is that `CategoryTheory.Bicategory.InducedBicategory.Hom` and
`.Hom₂` are **one-field structures**, not type synonyms, so a 1-morphism or 2-morphism of the
induced bicategory is reached from one of `C` by a `.hom` projection in one direction and by
`InducedBicategory.mkHom` / `.mkHom₂` in the other, and identities, composition, whiskering and
the associator are all transported by those constructors definitionally. That is what makes the
`compat` field of `CategoryTheory.Bicategory.TwoCommSq.PreHom` — the one condition of Stacks
003O with content — pass in both directions by a single `congrArg` or a single
`InducedBicategory.hom₂_ext`.

In `InducedBicategory.isoHom e`, and likewise in `congrArg InducedBicategory.Hom₂.hom h`, the
implicit 1-morphisms are determined by the *argument*; if instead the expected type is allowed
to drive them, the unifier solves `?f.hom =?= a.hom.hom` by taking `?f` to be the structure
literal `{ hom := a.hom.hom }` rather than `a.hom`, and the application is then rejected with a
type mismatch that names two syntactically distinct but definitionally equal 1-morphisms. Where
that happens, pass the 1-morphisms explicitly, as `rel_underlying_iff` does.

## References

* [Stacks Project, Tag 003O](https://stacks.math.columbia.edu/tag/003O)
* [Stacks Project, Tag 003Q](https://stacks.math.columbia.edu/tag/003Q)
-/

@[expose] public section

open CategoryTheory.Limits

namespace CategoryTheory.Bicategory

universe w v u₁ u₂

variable {B : Type u₂} {C : Type u₁} [Bicategory.{w, v} C] {F : B → C}

namespace InducedBicategory

/-- The 2-isomorphism of `C` underlying a 2-isomorphism of an induced bicategory; the inverse
of `CategoryTheory.Bicategory.InducedBicategory.isoMk`. -/
def isoHom {X Y : InducedBicategory C F} {f g : X ⟶ Y} (e : f ≅ g) : f.hom ≅ g.hom where
  hom := e.hom.hom
  inv := e.inv.hom
  hom_inv_id := congrArg Hom₂.hom e.hom_inv_id
  inv_hom_id := congrArg Hom₂.hom e.inv_hom_id

end InducedBicategory

variable {x y z : InducedBicategory C F} {f : x ⟶ z} {g : y ⟶ z}

/-- The 2-commutative square of `C` underlying a 2-commutative square of an induced bicategory:
the apex is its image and the two legs and the filler are its own, since the induced bicategory
has the 1-morphisms and 2-morphisms of `C`. -/
def TwoCommSq.underlying (P : TwoCommSq f g) : TwoCommSq f.hom g.hom where
  pt := F P.pt
  fst := P.fst.hom
  snd := P.snd.hom
  iso := InducedBicategory.isoHom P.iso

/-- The pre-morphism of the underlying squares (Stacks 003O) induced by a pre-morphism of
squares of an induced bicategory. -/
def TwoCommSq.PreHom.underlying {T S : TwoCommSq f g} (a : TwoCommSq.PreHom T S) :
    TwoCommSq.PreHom T.underlying S.underlying where
  hom := a.hom.hom
  isoFst := InducedBicategory.isoHom a.isoFst
  isoSnd := InducedBicategory.isoHom a.isoSnd
  compat := congrArg InducedBicategory.Hom₂.hom a.compat

/-- A pre-morphism of the underlying squares, read back as a pre-morphism of the squares of the
induced bicategory. This is where fullness is used: no condition on the 1-morphism or on the
two comparison 2-morphisms has to be checked. -/
def TwoCommSq.PreHom.ofUnderlying {T S : TwoCommSq f g}
    (a : TwoCommSq.PreHom T.underlying S.underlying) : TwoCommSq.PreHom T S where
  hom := InducedBicategory.mkHom a.hom
  isoFst := InducedBicategory.isoMk a.isoFst
  isoSnd := InducedBicategory.isoMk a.isoSnd
  compat := InducedBicategory.hom₂_ext a.compat

/-- Reading a pre-morphism of squares downstairs and then back up returns it unchanged. -/
theorem TwoCommSq.PreHom.ofUnderlying_underlying {T S : TwoCommSq f g}
    (a : TwoCommSq.PreHom T S) : a.underlying.ofUnderlying = a := rfl

/-- Reading a pre-morphism of the underlying squares upstairs and then back down returns it
unchanged. -/
theorem TwoCommSq.PreHom.underlying_ofUnderlying {T S : TwoCommSq f g}
    (a : TwoCommSq.PreHom T.underlying S.underlying) : a.ofUnderlying.underlying = a := rfl

/-- The 2-cell equivalence of Stacks 003O is detected on the underlying pre-morphisms, in both
directions: the mediating 2-isomorphism of one is the mediating 2-isomorphism of the other. -/
theorem TwoCommSq.PreHom.rel_underlying_iff {T S : TwoCommSq f g}
    (a b : TwoCommSq.PreHom T S) :
    TwoCommSq.PreHom.Rel a.underlying b.underlying ↔ TwoCommSq.PreHom.Rel a b := by
  constructor
  · rintro ⟨θ, h₁, h₂⟩
    exact ⟨InducedBicategory.isoMk θ, InducedBicategory.hom₂_ext h₁,
      InducedBicategory.hom₂_ext h₂⟩
  · rintro ⟨θ, h₁, h₂⟩
    exact ⟨InducedBicategory.isoHom (f := a.hom) (g := b.hom) θ,
      congrArg InducedBicategory.Hom₂.hom h₁,
      congrArg InducedBicategory.Hom₂.hom h₂⟩

/-- A morphism of the category of 2-commutative squares of an induced bicategory, read as one of
the underlying squares. -/
def TwoCommSq.homUnderlying {T S : TwoCommSq f g} (m : T ⟶ S) :
    T.underlying ⟶ S.underlying :=
  _root_.Quotient.map TwoCommSq.PreHom.underlying
    (fun _ _ h => (TwoCommSq.PreHom.rel_underlying_iff _ _).2 h) m

/-- A morphism of the category of 2-commutative squares of `C` between two underlying squares,
read as one of the squares upstairs. -/
def TwoCommSq.homOfUnderlying {T S : TwoCommSq f g} (m : T.underlying ⟶ S.underlying) :
    T ⟶ S :=
  _root_.Quotient.map TwoCommSq.PreHom.ofUnderlying
    (fun _ _ h => (TwoCommSq.PreHom.rel_underlying_iff _ _).1
      (by rwa [TwoCommSq.PreHom.underlying_ofUnderlying,
        TwoCommSq.PreHom.underlying_ofUnderlying])) m

/-- `TwoCommSq.homUnderlying` is injective, witnessed by `TwoCommSq.homOfUnderlying`. -/
theorem TwoCommSq.homOfUnderlying_homUnderlying {T S : TwoCommSq f g} (m : T ⟶ S) :
    TwoCommSq.homOfUnderlying (TwoCommSq.homUnderlying m) = m := by
  induction m using _root_.Quotient.inductionOn with
  | h a =>
    exact congrArg (_root_.Quotient.mk (TwoCommSq.PreHom.setoid T S))
      (TwoCommSq.PreHom.ofUnderlying_underlying a)

/-- `TwoCommSq.homUnderlying` is surjective, witnessed by `TwoCommSq.homOfUnderlying`: the second
round trip, so that reading a morphism of 2-commutative squares downstairs is a bijection and not
merely an injection. This is what lets a universal property be carried between *two* induced
bicategories over one ambient bicategory, rather than only down from the ambient one. -/
theorem TwoCommSq.homUnderlying_homOfUnderlying {T S : TwoCommSq f g}
    (m : T.underlying ⟶ S.underlying) :
    TwoCommSq.homUnderlying (TwoCommSq.homOfUnderlying (T := T) (S := S) m) = m := by
  induction m using _root_.Quotient.inductionOn with
  | h a =>
    exact congrArg (_root_.Quotient.mk (TwoCommSq.PreHom.setoid T.underlying S.underlying))
      (TwoCommSq.PreHom.underlying_ofUnderlying a)

/-- **A full sub-2-category inherits the 1-truncated 2-fibre products of the ambient one.** If the
square of `C` underlying a 2-commutative square of an induced bicategory is a terminal object of
the quotient category of squares (`CategoryTheory.Bicategory.IsTwoFibreProduct`), then so is the
square itself: the comparison morphism out of any test square is
the one supplied downstairs, read upstairs, and it is unique because reading a morphism
downstairs is injective. -/
noncomputable def isTwoFibreProduct_of_underlying {P : TwoCommSq f g}
    (hP : IsTwoFibreProduct P.underlying) : IsTwoFibreProduct P :=
  IsTerminal.ofUniqueHom (fun T => TwoCommSq.homOfUnderlying (hP.from T.underlying))
    (fun T m => by
      rw [← hP.hom_ext (TwoCommSq.homUnderlying m) (hP.from T.underlying),
        TwoCommSq.homOfUnderlying_homUnderlying])

/-- The 2-morphisms of pre-morphisms of squares (Stacks 003O (4)) of an induced bicategory are
those of the underlying pre-morphisms: the induced bicategory has all 2-morphisms of `C`. -/
def TwoCommSq.PreHom.hom₂UnderlyingEquiv {T S : TwoCommSq f g} (a b : TwoCommSq.PreHom T S) :
    a.Hom₂ b ≃ a.underlying.Hom₂ b.underlying where
  toFun δ :=
    { hom := δ.hom.hom
      isoFst_hom_comp := congrArg InducedBicategory.Hom₂.hom δ.isoFst_hom_comp
      isoSnd_hom_comp := congrArg InducedBicategory.Hom₂.hom δ.isoSnd_hom_comp }
  invFun δ :=
    { hom := InducedBicategory.mkHom₂ δ.hom
      isoFst_hom_comp := InducedBicategory.hom₂_ext δ.isoFst_hom_comp
      isoSnd_hom_comp := InducedBicategory.hom₂_ext δ.isoSnd_hom_comp }
  left_inv _ := rfl
  right_inv _ := rfl

/-- **A full sub-2-category inherits the 2-fibre products of the ambient one, in the sense of
Stacks 003Q.** If the square of `C` underlying a 2-commutative square of an induced bicategory is
a final object of the 2-category of 2-commutative diagrams, then so is the square itself: the
1-morphisms and the 2-morphisms of Stacks 003O upstairs are exactly those downstairs. -/
noncomputable def isFinalTwoCommSq_of_underlying {P : TwoCommSq f g}
    (hP : IsFinalTwoCommSq P.underlying) : IsFinalTwoCommSq P where
  preHom T := TwoCommSq.PreHom.ofUnderlying (hP.preHom T.underlying)
  uniqueHom₂ a b :=
    letI := hP.uniqueHom₂ a.underlying b.underlying
    (TwoCommSq.PreHom.hom₂UnderlyingEquiv a b).unique

/-- Detection of 2-cells by the legs passes from the square underlying a 2-commutative square of
an induced bicategory to the square itself. -/
theorem legsDetectTwoCells_of_underlying {P : TwoCommSq f g}
    (hd : P.underlying.LegsDetectTwoCells) : P.LegsDetectTwoCells :=
  fun _ a b η θ hfst hsnd => InducedBicategory.hom₂_ext
    (hd (a := a.hom) (b := b.hom) η.hom θ.hom (congrArg InducedBicategory.Hom₂.hom hfst)
      (congrArg InducedBicategory.Hom₂.hom hsnd))

/-- **A 2-fibre product in a full sub-2-category closed under the construction has a 2-fibre
product underneath it.** Let `P` be a 2-fibre product of a cospan of an induced bicategory and
suppose that *some* square `R` of the induced bicategory over the same cospan has a 2-fibre
product of the ambient bicategory underneath it. Then the square underlying `P` is a 2-fibre
product of the ambient bicategory too.

The hypothesis on `R` cannot be dropped: without it `P` is only terminal among the squares whose
apex lies in the sub-2-category, which says nothing about the squares whose apex does not. This is
the converse of `CategoryTheory.Bicategory.isTwoFibreProduct_of_underlying`, and it is a converse
only in the presence of that closure witness. -/
noncomputable def isTwoFibreProduct_underlying {P : TwoCommSq f g} (R : TwoCommSq f g)
    (hP : IsTwoFibreProduct P) (hR : IsTwoFibreProduct R.underlying) :
    IsTwoFibreProduct P.underlying := by
  refine Nonempty.some ?_
  have a : TwoCommSq.PreHom R P := _root_.Quotient.out (hP.from R)
  have b : TwoCommSq.PreHom P R :=
    _root_.Quotient.out ((isTwoFibreProduct_of_underlying hR).from P)
  obtain ⟨θ, -, -⟩ :=
    _root_.Quotient.exact (hP.hom_ext (_root_.Quotient.mk _ (b.comp a)) (𝟙 P))
  exact ⟨isTwoFibreProduct_of_section hR a.underlying b.hom.hom
    (InducedBicategory.isoHom (f := (b.comp a).hom) (g := (TwoCommSq.PreHom.id P).hom) θ)⟩

end CategoryTheory.Bicategory

end
