module

public import StacksFrontier.CategoryTheory.TwoFibreProduct.Defs
public import StacksFrontier.CategoryTheory.TwoFibreProduct.PostcomposeSnd
public import StacksFrontier.CategoryTheory.TwoFibreProduct.Swap

/-!
# Pasting of 2-fibre products

In a `(2,1)`-category a 2-fibre product of a cospan (**Stacks 003Q**) is a terminal object of the
category of 2-commutative squares over that cospan (**Stacks 003O**). This file records the
permanence property of that notion which every base-change and composition argument about
morphisms of algebraic stacks runs on: *pasting*. Given a square `S` over a cospan and a square
`T` over the inner cospan cut out by one of its legs, the outer rectangle is a 2-commutative
square over the composed cospan, and it is a 2-fibre product as soon as `S` and `T` are:

```text
        T.fst         S.fst
  T.pt --------> S.pt -------> x
   |              |            |
T.snd|          S.snd|         | f
   v              v            v
   t -----k-----> y -----g---> z
```

Equivalently, and this is how a consumer reads it: *a base change of a base change is a base
change*, so a property of 1-morphisms stable under base change that `f` has is inherited by the
leg `T.fst ≫ S.fst` of the rectangle in one step rather than two.

This is the bicategorical form of the horizontal pasting law for cartesian squares,
`CategoryTheory.IsPullback.paste_horiz`. The statement is about an arbitrary bicategory, so it
applies verbatim to the 2-category of algebraic stacks over a base — which is a
`CategoryTheory.Bicategory.InducedBicategory` — to categories fibred in groupoids, and to the
2-category of 1-categories. Nothing here is specific to a concrete model of the 2-fibre product:
`IsTwoFibreProduct` is the abstract notion of **Stacks 003Q**, terminality in the category of
**Stacks 003O**, and the proofs use nothing but that universal property, so there is no size,
existence or representability hypothesis anywhere.

This is **not** Stacks 02XD, and the difference is worth stating because the two are easy to
confuse. Stacks 02XD —
`CategoryTheory.CatFiberedInGroupoids.isTwoFibreProduct_cancelSndSquare` and its
algebraic-stacks form
`AlgebraicGeometry.Stack.isTwoFibreProduct_cancelSndSquareAlgebraicStacks` — *cancels* a middle
factor: it recognises one *canonical* iterated apex `(𝒵 ×_𝒴 𝒳) ×_𝒳 𝒰` as a 2-fibre product of
the outer cospan. Here both squares are **arbitrary**, the pasting is a construction on squares
rather than a recognition of a canonical apex, and the conclusion is about the composed leg,
which is what a base-change argument needs.

The symmetry of 2-commutative squares that the second-leg and first-leg forms are conjugate
under is `CategoryTheory.Bicategory.TwoCommSq.swap`, in
`StacksFrontier.CategoryTheory.TwoFibreProduct.Swap`, which this file re-exports.

## Main definitions

* `CategoryTheory.Bicategory.TwoCommSq.pasteFst`: the outer rectangle, pasting along the first
  projection.
* `CategoryTheory.Bicategory.TwoCommSq.paste`: the outer rectangle, pasting on the second leg.
* `CategoryTheory.Bicategory.TwoCommSq.pasteSnd`: the same square as
  `CategoryTheory.Bicategory.TwoCommSq.paste`, with both squares explicit; the latter is the form
  to cite.
* `CategoryTheory.Bicategory.TwoCommSq.PreHom.paste`: pasting is functorial in the inner square.

## Main results

* `CategoryTheory.Bicategory.isTwoFibreProduct_pasteFst`
* `CategoryTheory.Bicategory.isTwoFibreProduct_paste`
* `CategoryTheory.Bicategory.isTwoFibreProduct_pasteSnd`
* `CategoryTheory.Bicategory.paste_prehom_rel`: the uniqueness half, that any two pre-morphisms
  into the pasted rectangle are equivalent for the 2-cell equivalence of Stacks 003O.

## Implementation notes

Both orientations are proved directly, by terminality rather than by transport along an
equivalence, and the two proofs are independent of each other; they are kept apart because the
shape of the inner cospan a consumer has in hand is what decides which one applies, and
translating between them costs an application of
`CategoryTheory.Bicategory.TwoCommSq.swap` on the inner square.

For `CategoryTheory.Bicategory.isTwoFibreProduct_pasteFst`, both halves of the terminality
argument use the *same* pre-morphism, built in two steps from the two universal properties: a
test square `S` over `(k ≫ g, f)` reassociates to a square `pasteOuterSq` over `(g, f)`, whose
unique pre-morphism `p` to `P` supplies the second projection of a square `pasteInnerSq` over
`(k, P.fst)`, whose unique pre-morphism `q` to `Q` is the one wanted. `pasteFstPreHom` packages
that construction with its compatibility square, and both halves call it; factoring it out this
way is what keeps the file inside the default elaboration budget, since stated inline the
compatibility square would be elaborated twice.

The compatibility computation is bicategorical bookkeeping: the two given compatibility squares
are reassociated into the shape the goal needs (`hp'`, `hq'`), `whisker_exchange` commutes the
whiskering of `q.isoSnd` past `P.iso` (`hswap`), and the remaining identities between composites
of associators are closed by the `bicategory` tactic. Uniqueness compares an arbitrary
pre-morphism `m` into the pasted square with the constructed one by pushing `m` back through the
two universal properties: it induces a pre-morphism `p'` to `P` over the outer square and a
pre-morphism `q'` to `Q` over the inner square, each equivalent to the chosen one by terminality,
and the two resulting 2-cells compose to the one exhibiting the equivalence of `m` with
`pasteFstPreHom ..`.

For `CategoryTheory.Bicategory.isTwoFibreProduct_paste` the two halves are quite different.

*Uniqueness* is the half with content, and it is the composite of two applications of the given
universal properties. Two pre-morphisms `F, G : Z ⟶ S.paste T` are first read over the inner
cospan — `CategoryTheory.Bicategory.lowerPreHom`, which post-composes the second leg with `k` —
where terminality of `S` makes them agree and produces a comparison
`ν : F.hom ≫ T.fst ≅ G.hom ≫ T.fst`. That comparison is exactly the first comparison 2-cell of a
second pair of pre-morphisms, out of `CategoryTheory.Bicategory.innerOf` into `T`, where
terminality of `T` produces the 2-cell `θ : F.hom ≅ G.hom` the conclusion needs. The last step is
associator naturality in `θ`, which is why `(α_ G.hom T.fst S.fst).inv` is cancelled as a mono at
the end.

*Existence* is assembled from pieces that already carry their own compatibility squares, so it
costs no new coherence: `CategoryTheory.Bicategory.TwoCommSq.PreHom.postcomposeSnd` reads a
pre-morphism over the inner cospan, `CategoryTheory.Bicategory.lowerPasteToBase` is the canonical
pre-morphism out of a pasted rectangle, and `CategoryTheory.Bicategory.TwoCommSq.PreHom.comp`
glues them. `CategoryTheory.Bicategory.lowerPreHom` is *defined* as that composite for the same
reason — defining it by hand would have meant proving its compatibility square twice.

Two coherence computations remain, and both are stated with every 2-cell abstract
(`paste_compat_aux`, `toPaste_compat_aux`) so that no structure projection is in the way of the
`bicategory` tactic. Each needs exactly one step that tactic cannot take: for the pasted
pre-morphism it is the exchange law, moving the comparison on the first leg past the filler of
`S`; for the identity comparison it is solving the given compatibility square for the filler of
`Z`, which cancels an isomorphism rather than a coherence cell.

`TwoCommSq.paste` is marked `@[reducible]` rather than `@[implicit_reducible]`, and the stronger
attribute is load-bearing. The apex of a pasted square is `T.pt`, so a 2-cell such as
`F.hom ◁ 𝟙 (T.fst ≫ S.fst)` has its middle object forced to `(S.paste T).pt` by the type of
`F.hom` while the identity's object is typed at `T.pt`. Under `@[implicit_reducible]` alone, the
two are definitionally equal but `simp` and `rw` work at `reducible` transparency and cannot see
it: `rw [whiskerLeft_id]` is refused against a goal that prints the pattern verbatim,
and `simp [whiskerLeft_id]` reports the lemma unused. `@[reducible]` closes the gap; `show` would
not, because the mismatch is in the type of a subterm and not in the goal's own spelling.

## References

* [Stacks Project, Tag 003O](https://stacks.math.columbia.edu/tag/003O)
* [Stacks Project, Tag 003Q](https://stacks.math.columbia.edu/tag/003Q)
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits

namespace CategoryTheory.Bicategory

universe w v u

variable {A : Type u} [Bicategory.{w, v} A]

/-! ### Pasting along the first projection -/

section Paste

variable {X Y Z T : A} {g : Z ⟶ Y} {f : X ⟶ Y}

/-- **Pasting two 2-commutative squares.** Given a square `P` over the cospan `(g, f)` and a
square `Q` over the cospan `(k, P.fst)`, the outer rectangle is a 2-commutative square over
`(k ≫ g, f)`: its projections are `Q.fst` and `Q.snd ≫ P.snd`, and its filler is the composite
of the two fillers, reassociated. -/
def TwoCommSq.pasteFst (P : TwoCommSq g f) {k : T ⟶ Z} (Q : TwoCommSq k P.fst) :
    TwoCommSq (k ≫ g) f where
  pt := Q.pt
  fst := Q.fst
  snd := Q.snd ≫ P.snd
  iso := (α_ Q.fst k g).symm ≪≫ whiskerRightIso Q.iso g ≪≫ α_ Q.snd P.fst g ≪≫
    whiskerLeftIso Q.snd P.iso ≪≫ (α_ Q.snd P.snd f).symm

/-- The first projection of a rectangle pasted along the first projection is the first projection
of the inner square. -/
theorem TwoCommSq.pasteFst_fst (P : TwoCommSq g f) {k : T ⟶ Z} (Q : TwoCommSq k P.fst) :
    (P.pasteFst Q).fst = Q.fst := rfl

/-- A test square over `(k ≫ g, f)`, read as a test square over `(g, f)` by composing its first
projection with `k`. -/
abbrev pasteOuterSq (k : T ⟶ Z) (S : TwoCommSq (k ≫ g) f) : TwoCommSq g f where
  pt := S.pt
  fst := S.fst ≫ k
  snd := S.snd
  iso := α_ S.fst k g ≪≫ S.iso

/-- A test square over `(k, P.fst)` built from a pre-morphism of the reassociated test square to
`P`: its second projection is the underlying 1-morphism of that pre-morphism and its filler is
that pre-morphism's first comparison 2-cell. -/
abbrev pasteInnerSq (P : TwoCommSq g f) {k : T ⟶ Z} {S : TwoCommSq (k ≫ g) f}
    (p : TwoCommSq.PreHom (pasteOuterSq k S) P) : TwoCommSq k P.fst where
  pt := S.pt
  fst := S.fst
  snd := p.hom
  iso := p.isoFst

/-- The pre-morphism from a test square `S` to the pasted square, assembled from a pre-morphism
`p` to `P` over the reassociated square and a pre-morphism `q` to `Q` over the inner square. -/
def pasteFstPreHom (P : TwoCommSq g f) {k : T ⟶ Z} (Q : TwoCommSq k P.fst)
    {S : TwoCommSq (k ≫ g) f} (p : TwoCommSq.PreHom (pasteOuterSq k S) P)
    (q : TwoCommSq.PreHom (pasteInnerSq P p) Q) :
    TwoCommSq.PreHom S (P.pasteFst Q) where
  hom := q.hom
  isoFst := q.isoFst
  isoSnd := p.isoSnd ≪≫ whiskerRightIso q.isoSnd P.snd ≪≫ α_ q.hom Q.snd P.snd
  compat := by
    have hp' : S.iso.hom ≫ p.isoSnd.hom ▷ f ≫ (α_ p.hom P.snd f).hom =
        (α_ S.fst k g).symm.hom ≫ (p.isoFst.hom ▷ g) ≫ (α_ p.hom P.fst g).hom ≫
          p.hom ◁ P.iso.hom := by
      calc
        _ = (α_ S.fst k g).symm.hom ≫ ((α_ S.fst k g).hom ≫ S.iso.hom) ≫
            (p.isoSnd.hom ▷ f) ≫ (α_ p.hom P.snd f).hom := by
          dsimp
          bicategory
        _ = _ := congrArg (fun e => (α_ S.fst k g).symm.hom ≫ e) p.compat
    have hq' : p.isoFst.hom ≫ q.isoSnd.hom ▷ P.fst ≫ (α_ q.hom Q.snd P.fst).hom =
        (q.isoFst.hom ▷ k) ≫ (α_ q.hom Q.fst k).hom ≫ q.hom ◁ Q.iso.hom := q.compat
    have hq_nat : (q.isoSnd.hom ▷ P.snd ▷ f) ≫ ((α_ q.hom Q.snd P.snd).hom ▷ f) ≫
          (α_ q.hom (Q.snd ≫ P.snd) f).hom =
        (α_ p.hom P.snd f).hom ≫ q.isoSnd.hom ▷ (P.snd ≫ f) ≫
          (α_ q.hom Q.snd (P.snd ≫ f)).hom ≫ q.hom ◁ (α_ Q.snd P.snd f).symm.hom := by
      dsimp
      bicategory
    have hswap : p.hom ◁ P.iso.hom ≫ q.isoSnd.hom ▷ (P.snd ≫ f) =
        q.isoSnd.hom ▷ (P.fst ≫ g) ≫ (q.hom ≫ Q.snd) ◁ P.iso.hom :=
      whisker_exchange q.isoSnd.hom P.iso.hom
    have hq_nat_fst : (q.isoSnd.hom ▷ P.fst ▷ g) ≫ ((α_ q.hom Q.snd P.fst).hom ▷ g) ≫
          (α_ q.hom (Q.snd ≫ P.fst) g).hom =
        (α_ p.hom P.fst g).hom ≫ q.isoSnd.hom ▷ (P.fst ≫ g) ≫
          (α_ q.hom Q.snd (P.fst ≫ g)).hom ≫ q.hom ◁ (α_ Q.snd P.fst g).symm.hom := by
      dsimp
      bicategory
    have hq'_g : p.isoFst.hom ▷ g ≫ q.isoSnd.hom ▷ P.fst ▷ g ≫
          (α_ q.hom Q.snd P.fst).hom ▷ g =
        q.isoFst.hom ▷ k ▷ g ≫ (α_ q.hom Q.fst k).hom ▷ g ≫ (q.hom ◁ Q.iso.hom) ▷ g := by
      simpa only [comp_whiskerRight] using congrArg (fun e => e ▷ g) hq'
    have htail : (q.hom ≫ Q.snd) ◁ P.iso.hom ≫ (α_ q.hom Q.snd (P.snd ≫ f)).hom ≫
          q.hom ◁ (α_ Q.snd P.snd f).symm.hom =
        (α_ q.hom Q.snd (P.fst ≫ g)).hom ≫ q.hom ◁ (α_ Q.snd P.fst g).symm.hom ≫
          q.hom ◁ (α_ Q.snd P.fst g).hom ≫ q.hom ◁ Q.snd ◁ P.iso.hom ≫
          q.hom ◁ (α_ Q.snd P.snd f).symm.hom := by
      dsimp
      bicategory
    simp only [TwoCommSq.pasteFst, Iso.trans_hom, whiskerLeftIso_hom, whiskerRightIso_hom,
      Iso.symm_hom, comp_whiskerRight, Category.assoc]
    rw [hq_nat, reassoc_of% hp', reassoc_of% hswap, htail, ← reassoc_of% hq_nat_fst,
      reassoc_of% hq'_g]
    dsimp [TwoCommSq.pasteFst]
    bicategory

-- the uniqueness half states the comparison 2-cells of `m` against the projections of `Q`, whose
-- hom-category is the pasted square's only up to unfolding `pasteFst`; without this the goals are
-- type-incorrect at `implicit` transparency and neither `simp` nor `rw` fires on them
attribute [local implicit_reducible] TwoCommSq.pasteFst in
/-- **The pasted square is a 2-fibre product.** If `P` is a 2-fibre product of `(g, f)` and `Q`
is a 2-fibre product of `(k, P.fst)`, then the outer rectangle `P.pasteFst Q` is a 2-fibre
product of `(k ≫ g, f)`. -/
noncomputable def isTwoFibreProduct_pasteFst (P : TwoCommSq g f) (hP : IsTwoFibreProduct P)
    {k : T ⟶ Z} (Q : TwoCommSq k P.fst) (hQ : IsTwoFibreProduct Q) :
    IsTwoFibreProduct (P.pasteFst Q) := by
  refine IsTerminal.ofUniqueHom
    (fun S => _root_.Quotient.mk _ (pasteFstPreHom P Q
      (Quotient.out (hP.from (pasteOuterSq k S)))
      (Quotient.out (hQ.from (pasteInnerSq P (Quotient.out (hP.from (pasteOuterSq k S))))))))
    fun S m => ?_
  induction m using _root_.Quotient.inductionOn with
  | h m =>
  set p := Quotient.out (hP.from (pasteOuterSq k S))
  set q := Quotient.out (hQ.from (pasteInnerSq P p))
  -- `m` seen as a pre-morphism to `P` over the reassociated test square
  let p' : TwoCommSq.PreHom (pasteOuterSq k S) P :=
    { hom := m.hom ≫ Q.snd
      isoFst := whiskerRightIso m.isoFst k ≪≫ α_ m.hom Q.fst k ≪≫
        whiskerLeftIso m.hom Q.iso ≪≫ (α_ m.hom Q.snd P.fst).symm
      isoSnd := m.isoSnd ≪≫ (α_ m.hom Q.snd P.snd).symm
      compat := by
        have hM : S.iso.hom ≫ (m.isoSnd.hom ▷ f) ≫ (α_ m.hom (Q.snd ≫ P.snd) f).hom =
            (m.isoFst.hom ▷ (k ≫ g)) ≫ (α_ m.hom Q.fst (k ≫ g)).hom ≫
              m.hom ◁ ((α_ Q.fst k g).inv ≫ Q.iso.hom ▷ g ≫ (α_ Q.snd P.fst g).hom ≫
                Q.snd ◁ P.iso.hom ≫ (α_ Q.snd P.snd f).inv) := m.compat
        calc ((α_ S.fst k g).hom ≫ S.iso.hom) ≫
              ((m.isoSnd.hom ≫ (α_ m.hom Q.snd P.snd).inv) ▷ f) ≫
                (α_ (m.hom ≫ Q.snd) P.snd f).hom
            = (α_ S.fst k g).hom ≫ (S.iso.hom ≫ (m.isoSnd.hom ▷ f) ≫
                (α_ m.hom (Q.snd ≫ P.snd) f).hom) ≫ m.hom ◁ (α_ Q.snd P.snd f).hom ≫
                  (α_ m.hom Q.snd (P.snd ≫ f)).inv := by
              bicategory
          _ = (α_ S.fst k g).hom ≫ ((m.isoFst.hom ▷ (k ≫ g)) ≫
                (α_ m.hom Q.fst (k ≫ g)).hom ≫ m.hom ◁ ((α_ Q.fst k g).inv ≫
                  Q.iso.hom ▷ g ≫ (α_ Q.snd P.fst g).hom ≫ Q.snd ◁ P.iso.hom ≫
                    (α_ Q.snd P.snd f).inv)) ≫ m.hom ◁ (α_ Q.snd P.snd f).hom ≫
                      (α_ m.hom Q.snd (P.snd ≫ f)).inv := by
              rw [hM]
          _ = ((m.isoFst.hom ▷ k ≫ (α_ m.hom Q.fst k).hom ≫ m.hom ◁ Q.iso.hom ≫
                (α_ m.hom Q.snd P.fst).inv) ▷ g) ≫ (α_ (m.hom ≫ Q.snd) P.fst g).hom ≫
                  (m.hom ≫ Q.snd) ◁ P.iso.hom := by
              bicategory }
  obtain ⟨θP, hPF, hPS⟩ :=
    _root_.Quotient.exact (hP.hom_ext (_root_.Quotient.mk _ p') (_root_.Quotient.mk _ p))
  -- `m` seen as a pre-morphism to `Q` over the inner test square
  let q' : TwoCommSq.PreHom (pasteInnerSq P p) Q :=
    { hom := m.hom
      isoFst := m.isoFst
      isoSnd := θP.symm
      compat := by
        have hp'F : p'.isoFst.hom = m.isoFst.hom ▷ k ≫ (α_ m.hom Q.fst k).hom ≫
            m.hom ◁ Q.iso.hom ≫ (α_ m.hom Q.snd P.fst).inv := rfl
        change p.isoFst.hom ≫ (θP.inv ▷ P.fst) ≫ (α_ m.hom Q.snd P.fst).hom =
          (m.isoFst.hom ▷ k) ≫ (α_ m.hom Q.fst k).hom ≫ (m.hom ◁ Q.iso.hom)
        rw [← hPF, hp'F]
        simp only [Category.assoc]
        rw [reassoc_of% (hom_inv_whiskerRight θP P.fst)]
        simp }
  obtain ⟨θQ, hQF, hQS⟩ :=
    _root_.Quotient.exact (hQ.hom_ext (_root_.Quotient.mk _ q') (_root_.Quotient.mk _ q))
  refine _root_.Quotient.sound ⟨θQ, hQF, ?_⟩
  have hpS : p.isoSnd.hom =
      (m.isoSnd.hom ≫ (α_ m.hom Q.snd P.snd).inv) ≫ θP.hom ▷ P.snd := hPS.symm
  have hqS : q.isoSnd.hom = θP.inv ≫ θQ.hom ▷ Q.snd := hQS.symm
  change m.isoSnd.hom ≫ θQ.hom ▷ (Q.snd ≫ P.snd) =
    p.isoSnd.hom ≫ q.isoSnd.hom ▷ P.snd ≫ (α_ q.hom Q.snd P.snd).hom
  rw [hpS, hqS, comp_whiskerRight]
  simp only [Category.assoc]
  rw [reassoc_of% (hom_inv_whiskerRight θP P.snd),
    associator_naturality_left θQ.hom Q.snd P.snd, Iso.inv_hom_id_assoc]

end Paste

/-! ### Pasting on the second leg -/

section PasteOnSnd

variable {x y z t : A} {f : x ⟶ z} {g : y ⟶ z} {k : t ⟶ y}

/-- **The pasted rectangle.** Given a 2-commutative square `S` over the cospan `(f, g)` and a
2-commutative square `T` over the inner cospan `(S.snd, k)`, the outer rectangle is a
2-commutative square over `(f, k ≫ g)`: its apex is that of `T`, its first leg the composite
`T.fst ≫ S.fst`, its second leg `T.snd`, and its filler the pasted composite of the two given
fillers. **Stacks 003O.** -/
@[reducible]
def TwoCommSq.paste (S : TwoCommSq f g) (T : TwoCommSq S.snd k) : TwoCommSq f (k ≫ g) where
  pt := T.pt
  fst := T.fst ≫ S.fst
  snd := T.snd
  iso := α_ T.fst S.fst f ≪≫ whiskerLeftIso T.fst S.iso ≪≫ (α_ T.fst S.snd g).symm ≪≫
    whiskerRightIso T.iso g ≪≫ α_ T.snd k g

/-- The first leg of a pasted rectangle. -/
theorem TwoCommSq.paste_fst (S : TwoCommSq f g) (T : TwoCommSq S.snd k) :
    (S.paste T).fst = T.fst ≫ S.fst := rfl

/-- The second leg of a pasted rectangle. -/
theorem TwoCommSq.paste_snd (S : TwoCommSq f g) (T : TwoCommSq S.snd k) :
    (S.paste T).snd = T.snd := rfl

/-- The filler of a pasted rectangle, written out. It holds by `rfl`, but it is stated because
`simp` does not unfold the `hom` projections of the `whiskerLeftIso` and `whiskerRightIso` in the
definition, both of which are plain `def`s. -/
theorem TwoCommSq.paste_iso_hom (S : TwoCommSq f g) (T : TwoCommSq S.snd k) :
    (S.paste T).iso.hom = (α_ T.fst S.fst f).hom ≫ (T.fst ◁ S.iso.hom) ≫
      (α_ T.fst S.snd g).inv ≫ (T.iso.hom ▷ g) ≫ (α_ T.snd k g).hom := rfl

/-- **A square over the outer cospan, read over the inner one.** A 2-commutative square over
`(f, k ≫ g)` becomes one over `(f, g)` by post-composing its second leg with `k`. This is
`CategoryTheory.Bicategory.TwoCommSq.postcomposeSnd` at the identity comparison, and it is the
operation under which an arbitrary square over the outer cospan is compared with `S`. -/
@[implicit_reducible]
def TwoCommSq.lower (Z : TwoCommSq f (k ≫ g)) : TwoCommSq f g :=
  Z.postcomposeSnd k (Iso.refl (k ≫ g))

/-- The filler of `CategoryTheory.Bicategory.TwoCommSq.lower`, written out. -/
theorem TwoCommSq.lower_iso_hom (Z : TwoCommSq f (k ≫ g)) :
    (TwoCommSq.lower Z).iso.hom = Z.iso.hom ≫ (Z.snd ◁ (𝟙 (k ≫ g))) ≫ (α_ Z.snd k g).inv := rfl

/-- The compatibility square of Stacks 003O for a pasted pre-morphism, with every 2-cell
abstract. -/
private theorem paste_compat_aux {w₁ w₂ s tt xx yy zz : A}
    (p : w₁ ⟶ w₂) (a₁ : w₁ ⟶ s) (b₁ : w₁ ⟶ tt) (a₂ : w₂ ⟶ s) (b₂ : w₂ ⟶ tt)
    (sf : s ⟶ xx) (ss : s ⟶ yy) (kk : tt ⟶ yy) (ff : xx ⟶ zz) (gg : yy ⟶ zz)
    (σ : sf ≫ ff ⟶ ss ≫ gg) (τ₁ : a₁ ≫ ss ⟶ b₁ ≫ kk) (τ₂ : a₂ ≫ ss ⟶ b₂ ≫ kk)
    (φ : a₁ ⟶ p ≫ a₂) (ψ : b₁ ⟶ p ≫ b₂)
    (hu : τ₁ ≫ (ψ ▷ kk) ≫ (α_ p b₂ kk).hom = (φ ▷ ss) ≫ (α_ p a₂ ss).hom ≫ (p ◁ τ₂)) :
    ((α_ a₁ sf ff).hom ≫ (a₁ ◁ σ) ≫ (α_ a₁ ss gg).inv ≫ (τ₁ ▷ gg) ≫ (α_ b₁ kk gg).hom) ≫
        (ψ ▷ (kk ≫ gg)) ≫ (α_ p b₂ (kk ≫ gg)).hom
      = (((φ ▷ sf) ≫ (α_ p a₂ sf).hom) ▷ ff) ≫ (α_ p (a₂ ≫ sf) ff).hom ≫
        (p ◁ ((α_ a₂ sf ff).hom ≫ (a₂ ◁ σ) ≫ (α_ a₂ ss gg).inv ≫ (τ₂ ▷ gg) ≫
          (α_ b₂ kk gg).hom)) :=
  calc ((α_ a₁ sf ff).hom ≫ (a₁ ◁ σ) ≫ (α_ a₁ ss gg).inv ≫ (τ₁ ▷ gg) ≫ (α_ b₁ kk gg).hom) ≫
        (ψ ▷ (kk ≫ gg)) ≫ (α_ p b₂ (kk ≫ gg)).hom
      = ((α_ a₁ sf ff).hom ≫ (a₁ ◁ σ) ≫ (α_ a₁ ss gg).inv) ≫
          ((τ₁ ≫ (ψ ▷ kk) ≫ (α_ p b₂ kk).hom) ▷ gg) ≫
            (α_ p (b₂ ≫ kk) gg).hom ≫ (p ◁ (α_ b₂ kk gg).hom) := by bicategory
    _ = ((α_ a₁ sf ff).hom ≫ (a₁ ◁ σ) ≫ (α_ a₁ ss gg).inv) ≫
          (((φ ▷ ss) ≫ (α_ p a₂ ss).hom ≫ (p ◁ τ₂)) ▷ gg) ≫
            (α_ p (b₂ ≫ kk) gg).hom ≫ (p ◁ (α_ b₂ kk gg).hom) := by rw [hu]
    _ = (α_ a₁ sf ff).hom ≫ ((a₁ ◁ σ) ≫ (φ ▷ (ss ≫ gg))) ≫
          (α_ (p ≫ a₂) ss gg).inv ≫ ((α_ p a₂ ss).hom ▷ gg) ≫ ((p ◁ τ₂) ▷ gg) ≫
            (α_ p (b₂ ≫ kk) gg).hom ≫ (p ◁ (α_ b₂ kk gg).hom) := by bicategory
    _ = (α_ a₁ sf ff).hom ≫ ((φ ▷ (sf ≫ ff)) ≫ ((p ≫ a₂) ◁ σ)) ≫
          (α_ (p ≫ a₂) ss gg).inv ≫ ((α_ p a₂ ss).hom ▷ gg) ≫ ((p ◁ τ₂) ▷ gg) ≫
            (α_ p (b₂ ≫ kk) gg).hom ≫ (p ◁ (α_ b₂ kk gg).hom) := by
        rw [whisker_exchange]
    _ = (((φ ▷ sf) ≫ (α_ p a₂ sf).hom) ▷ ff) ≫ (α_ p (a₂ ≫ sf) ff).hom ≫
          (p ◁ ((α_ a₂ sf ff).hom ≫ (a₂ ◁ σ) ≫ (α_ a₂ ss gg).inv ≫ (τ₂ ▷ gg) ≫
            (α_ b₂ kk gg).hom)) := by bicategory

/-- The compatibility square of Stacks 003O for the identity comparison into a pasting, with
every 2-cell abstract. -/
private theorem toPaste_compat_aux {q s tt xx yy zz : A}
    (c : q ⟶ s) (aa : q ⟶ xx) (bb : q ⟶ tt) (sf : s ⟶ xx) (ss : s ⟶ yy) (kk : tt ⟶ yy)
    (ff : xx ⟶ zz) (gg : yy ⟶ zz)
    (ι : aa ≫ ff ⟶ bb ≫ (kk ≫ gg)) (χ : aa ⟶ c ≫ sf) (ω : bb ≫ kk ≅ c ≫ ss)
    (σ : sf ≫ ff ⟶ ss ≫ gg)
    (hA : (ι ≫ (bb ◁ (𝟙 (kk ≫ gg))) ≫ (α_ bb kk gg).inv) ≫ (ω.hom ▷ gg) ≫
        (α_ c ss gg).hom = (χ ▷ ff) ≫ (α_ c sf ff).hom ≫ (c ◁ σ)) :
    ι ≫ ((λ_ bb).inv ▷ (kk ≫ gg)) ≫ (α_ (𝟙 q) bb (kk ≫ gg)).hom
      = ((χ ≫ (λ_ (c ≫ sf)).inv) ▷ ff) ≫ (α_ (𝟙 q) (c ≫ sf) ff).hom ≫
        ((𝟙 q) ◁ ((α_ c sf ff).hom ≫ (c ◁ σ) ≫ (α_ c ss gg).inv ≫ (ω.inv ▷ gg) ≫
          (α_ bb kk gg).hom)) := by
  have hι : ι = ((χ ▷ ff) ≫ (α_ c sf ff).hom ≫ (c ◁ σ)) ≫
      ((α_ c ss gg).inv ≫ (ω.inv ▷ gg) ≫ (α_ bb kk gg).hom) := by
    rw [← hA]
    simp
  rw [hι]
  simp only [Category.assoc]
  bicategory

/-- **Pasting is functorial in the inner square.** A pre-morphism of 2-commutative squares over
the inner cospan `(S.snd, k)` induces one between the pasted rectangles: the same 1-morphism,
with its first comparison 2-cell whiskered by `S.fst` and its second unchanged. **Stacks 003O.** -/
def TwoCommSq.PreHom.paste (S : TwoCommSq f g) {T₁ T₂ : TwoCommSq S.snd k}
    (u : TwoCommSq.PreHom T₁ T₂) : TwoCommSq.PreHom (S.paste T₁) (S.paste T₂) where
  hom := u.hom
  isoFst := whiskerRightIso u.isoFst S.fst ≪≫ α_ u.hom T₂.fst S.fst
  isoSnd := u.isoSnd
  compat := by
    rw [TwoCommSq.paste_iso_hom, TwoCommSq.paste_iso_hom]
    exact paste_compat_aux u.hom T₁.fst T₁.snd T₂.fst T₂.snd S.fst S.snd k f g S.iso.hom
      T₁.iso.hom T₂.iso.hom u.isoFst.hom u.isoSnd.hom u.compat

/-- **The canonical pre-morphism out of a pasted rectangle, read over the inner cospan.** The
rectangle `S.paste T` read over `(f, g)` has first leg `T.fst ≫ S.fst` and second leg
`T.snd ≫ k`, so `T.fst` compares it with `S` itself: the first comparison 2-cell is an identity
and the second is the filler of `T` read backwards. **Stacks 003O.** -/
def lowerPasteToBase (S : TwoCommSq f g) (T : TwoCommSq S.snd k) :
    TwoCommSq.PreHom (TwoCommSq.lower (S.paste T)) S where
  hom := T.fst
  isoFst := Iso.refl (T.fst ≫ S.fst)
  isoSnd := T.iso.symm
  compat := by
    change (TwoCommSq.lower (S.paste T)).iso.hom ≫ (T.iso.inv ▷ g) ≫ (α_ T.fst S.snd g).hom
        = (𝟙 (T.fst ≫ S.fst) ▷ f) ≫ (α_ T.fst S.fst f).hom ≫ (T.fst ◁ S.iso.hom)
    rw [TwoCommSq.lower_iso_hom, TwoCommSq.paste_iso_hom]
    dsimp only [TwoCommSq.paste]
    simp

variable {S : TwoCommSq f g} {T : TwoCommSq S.snd k}

section Uniqueness

variable (Z : TwoCommSq f (k ≫ g)) (F : TwoCommSq.PreHom Z (S.paste T))

/-- **An arbitrary pre-morphism into a pasted rectangle, read over the inner cospan.** Defined
as the composite of `CategoryTheory.Bicategory.TwoCommSq.PreHom.postcomposeSnd` with
`CategoryTheory.Bicategory.lowerPasteToBase`, so that its compatibility square of Stacks 003O is
not proved a second time. -/
def lowerPreHom : TwoCommSq.PreHom (TwoCommSq.lower Z) S :=
  (F.postcomposeSnd k (Iso.refl (k ≫ g))).comp (lowerPasteToBase S T)

/-- The 1-morphism underlying `CategoryTheory.Bicategory.lowerPreHom`. -/
theorem lowerPreHom_hom : (lowerPreHom Z F).hom = F.hom ≫ T.fst := rfl

/-- The first comparison 2-cell of `CategoryTheory.Bicategory.lowerPreHom`, with the identity
whiskering of the composite's own first comparison discharged. -/
theorem lowerPreHom_isoFst_hom :
    (lowerPreHom Z F).isoFst.hom = F.isoFst.hom ≫ (α_ F.hom T.fst S.fst).inv := by
  change F.isoFst.hom ≫ (F.hom ◁ (𝟙 (T.fst ≫ S.fst))) ≫ (α_ F.hom T.fst S.fst).inv = _
  rw [whiskerLeft_id, Category.id_comp]

/-- The second comparison 2-cell of `CategoryTheory.Bicategory.lowerPreHom`, named because it is
the 2-cell both terminality arguments are stated over. -/
def lowerIsoSnd : Z.snd ≫ k ≅ (F.hom ≫ T.fst) ≫ S.snd := (lowerPreHom Z F).isoSnd

/-- `CategoryTheory.Bicategory.lowerIsoSnd` is the second comparison 2-cell, by definition. -/
theorem lowerPreHom_isoSnd : (lowerPreHom Z F).isoSnd = lowerIsoSnd Z F := rfl

/-- `CategoryTheory.Bicategory.lowerIsoSnd`, written out. -/
theorem lowerIsoSnd_hom : (lowerIsoSnd Z F).hom = (F.isoSnd.hom ▷ k) ≫
    (α_ F.hom T.snd k).hom ≫ (F.hom ◁ T.iso.inv) ≫ (α_ F.hom T.fst S.snd).inv := by
  simp [lowerIsoSnd, lowerPreHom, TwoCommSq.PreHom.comp, TwoCommSq.PreHom.postcomposeSnd,
    lowerPasteToBase, TwoCommSq.paste_snd]

/-- **Reading `CategoryTheory.Bicategory.lowerIsoSnd` forwards through the filler of `T`.** This
is the one identity both compatibility squares of
`CategoryTheory.Bicategory.innerPreHom` reduce to. -/
theorem lowerIsoSnd_hom_comp :
    (lowerIsoSnd Z F).hom ≫ (α_ F.hom T.fst S.snd).hom ≫ (F.hom ◁ T.iso.hom)
      = (F.isoSnd.hom ▷ k) ≫ (α_ F.hom T.snd k).hom := by
  rw [lowerIsoSnd_hom]
  simp

/-- **The square over the inner cospan carried by a pre-morphism into a pasted rectangle.** Its
apex is that of `Z`, its first leg the composite `F.hom ≫ T.fst` and its second leg `Z.snd`;
this is the square at which terminality of `T` is applied. **Stacks 003O.** -/
@[implicit_reducible]
def innerOf : TwoCommSq S.snd k where
  pt := Z.pt
  fst := F.hom ≫ T.fst
  snd := Z.snd
  iso := (lowerIsoSnd Z F).symm

/-- **A pre-morphism out of `CategoryTheory.Bicategory.innerOf` carried by a comparison of the
two first legs.** Both pre-morphisms the uniqueness argument compares are of this shape: the one
built from `F` takes the identity comparison, and the one built from `G` takes the comparison
that terminality of `S` supplies. **Stacks 003O.** -/
def innerPreHom (G : TwoCommSq.PreHom Z (S.paste T)) (ν : (F.hom ≫ T.fst) ≅ (G.hom ≫ T.fst))
    (hν : (lowerIsoSnd Z F).hom ≫ (ν.hom ▷ S.snd) = (lowerIsoSnd Z G).hom) :
    TwoCommSq.PreHom (innerOf Z F) T where
  hom := G.hom
  isoFst := ν
  isoSnd := G.isoSnd
  compat := by
    change (lowerIsoSnd Z F).symm.hom ≫ _ = _
    rw [show ν.hom ▷ S.snd = (lowerIsoSnd Z F).inv ≫ (lowerIsoSnd Z G).hom by
      rw [← hν]
      simp]
    simp only [Iso.symm_hom, Category.assoc]
    rw [lowerIsoSnd_hom_comp Z G]

end Uniqueness

/-- **Any two pre-morphisms into a pasted rectangle are equivalent.** This is the uniqueness
half of the universal property of `CategoryTheory.Bicategory.TwoCommSq.paste`, stated for the
2-cell equivalence of Stacks 003O rather than for the quotient, and it is where both given
universal properties are used. -/
theorem paste_prehom_rel (hS : IsTwoFibreProduct S) (hT : IsTwoFibreProduct T)
    {Z : TwoCommSq f (k ≫ g)} (F G : TwoCommSq.PreHom Z (S.paste T)) :
    TwoCommSq.PreHom.Rel F G := by
  -- `S` is terminal, so the two pre-morphisms read over the inner cospan agree.
  have hrelS := twoFibreProductPreHom_rel hS (lowerPreHom Z F) (lowerPreHom Z G)
  obtain ⟨ν, ha, hb⟩ : ∃ ν : (F.hom ≫ T.fst) ≅ (G.hom ≫ T.fst),
      (lowerPreHom Z F).isoFst.hom ≫ (ν.hom ▷ S.fst) = (lowerPreHom Z G).isoFst.hom ∧
        (lowerIsoSnd Z F).hom ≫ (ν.hom ▷ S.snd) = (lowerIsoSnd Z G).hom := hrelS
  rw [lowerPreHom_isoFst_hom, lowerPreHom_isoFst_hom] at ha
  -- `T` is terminal, so the two pre-morphisms out of `innerOf Z F` agree.
  have hrefl : (lowerIsoSnd Z F).hom ≫ ((Iso.refl (F.hom ≫ T.fst)).hom ▷ S.snd)
      = (lowerIsoSnd Z F).hom := by simp [id_whiskerRight]
  have hrelT := twoFibreProductPreHom_rel hT (innerPreHom Z F F (Iso.refl (F.hom ≫ T.fst)) hrefl)
    (innerPreHom Z F G ν hb)
  obtain ⟨θ, hc, hd⟩ : ∃ θ : F.hom ≅ G.hom,
      𝟙 (F.hom ≫ T.fst) ≫ (θ.hom ▷ T.fst) = ν.hom ∧
        F.isoSnd.hom ≫ (θ.hom ▷ T.snd) = G.isoSnd.hom := hrelT
  refine ⟨θ, ?_, hd⟩
  rw [← (by simpa using hc : θ.hom ▷ T.fst = ν.hom)] at ha
  have ha' : (F.isoFst.hom ≫ (α_ F.hom T.fst S.fst).inv) ≫ ((θ.hom ▷ T.fst) ▷ S.fst)
      = G.isoFst.hom ≫ (α_ G.hom T.fst S.fst).inv := ha
  change F.isoFst.hom ≫ (θ.hom ▷ (T.fst ≫ S.fst)) = G.isoFst.hom
  rw [show (F.isoFst.hom ≫ (α_ F.hom T.fst S.fst).inv) ≫ ((θ.hom ▷ T.fst) ▷ S.fst)
      = (F.isoFst.hom ≫ (θ.hom ▷ (T.fst ≫ S.fst))) ≫ (α_ G.hom T.fst S.fst).inv by
    simp only [Category.assoc]
    congr 1
    bicategory] at ha'
  exact (cancel_mono (α_ G.hom T.fst S.fst).inv).mp ha'

section Existence

variable (hS : IsTwoFibreProduct S) (hT : IsTwoFibreProduct T) (Z : TwoCommSq f (k ≫ g))

/-- **The pre-morphism into `S` that terminality supplies**, for an arbitrary square over the
outer cospan read over the inner one. A representative of the morphism of Stacks 003O is chosen,
which is why this and everything built on it is `noncomputable`; the choice is immaterial because
`CategoryTheory.Bicategory.paste_prehom_rel` makes the resulting pre-morphism unique anyway. -/
noncomputable def canLower : TwoCommSq.PreHom (TwoCommSq.lower Z) S :=
  (hS.from (TwoCommSq.lower Z)).out

/-- **The square over the inner cospan built from `CategoryTheory.Bicategory.canLower`.** Its
first leg is the 1-morphism into `S` just chosen and its filler is that pre-morphism's second
comparison 2-cell, read backwards. **Stacks 003O.** -/
noncomputable def innerSq : TwoCommSq S.snd k where
  pt := Z.pt
  fst := (canLower hS Z).hom
  snd := Z.snd
  iso := (canLower hS Z).isoSnd.symm

/-- **An arbitrary square over the outer cospan compares to the pasting of
`CategoryTheory.Bicategory.innerSq` by the identity 1-morphism.** The two squares have the same
apex and the same second leg, and their first legs are compared by the pre-morphism
`CategoryTheory.Bicategory.canLower` supplies. **Stacks 003O.** -/
noncomputable def toPasteInner : TwoCommSq.PreHom Z (S.paste (innerSq hS Z)) where
  hom := 𝟙 Z.pt
  isoFst := (canLower hS Z).isoFst ≪≫ (λ_ ((canLower hS Z).hom ≫ S.fst)).symm
  isoSnd := (λ_ Z.snd).symm
  compat := by
    rw [TwoCommSq.paste_iso_hom]
    exact toPaste_compat_aux (canLower hS Z).hom Z.fst Z.snd S.fst S.snd k f g Z.iso.hom
      (canLower hS Z).isoFst.hom (canLower hS Z).isoSnd S.iso.hom
      (by
        rw [← TwoCommSq.lower_iso_hom]
        exact (canLower hS Z).compat)

/-- **The pre-morphism from an arbitrary square over the outer cospan into a pasted rectangle.**
The existence half of the universal property, assembled as the composite of
`CategoryTheory.Bicategory.toPasteInner` with the pasting of the pre-morphism terminality of `T`
supplies. -/
noncomputable def pastePreHom : TwoCommSq.PreHom Z (S.paste T) :=
  (toPasteInner hS Z).comp (TwoCommSq.PreHom.paste S (hT.from (innerSq hS Z)).out)

end Existence

/-- **Pasting of 2-fibre products (Stacks 003Q).** If `S` is a 2-fibre product of the cospan
`(f, g)` and `T` is a 2-fibre product of the inner cospan `(S.snd, k)`, then the pasted
rectangle `S.paste T` is a 2-fibre product of the outer cospan `(f, k ≫ g)`.

Read as a statement about base change: the base change of a base change is a base change. In
particular the leg `T.fst ≫ S.fst` of the rectangle inherits every property of `f` that is
stable under base change, in one application rather than two, and the universal properties of the
two given squares are the only hypotheses — there is no size, existence or representability
condition, and the bicategory is arbitrary. -/
noncomputable def isTwoFibreProduct_paste (hS : IsTwoFibreProduct S) (hT : IsTwoFibreProduct T) :
    IsTwoFibreProduct (S.paste T) :=
  IsTerminal.ofUniqueHom (fun Z => Quotient.mk _ (pastePreHom hS hT Z))
    (fun _ m => Quotient.inductionOn m fun F =>
      Quotient.sound (paste_prehom_rel hS hT F _))

end PasteOnSnd

/-! ### Pasting along the second projection -/

section PasteSnd

variable {X Y Z T : A} {g : Y ⟶ Z} {k : T ⟶ Z} {f : X ⟶ Y}

/-- **Pasting two 2-commutative squares along the second projection.** Given a square `Q` over
the cospan `(k, g)` and a square `R` over the cospan `(Q.snd, f)`, the outer rectangle is a
2-commutative square over `(k, f ≫ g)`.

This is `CategoryTheory.Bicategory.TwoCommSq.paste` with both squares explicit, and it is that
square on the nose, not merely isomorphic to it; `TwoCommSq.paste` is the form to cite. -/
@[reducible]
def TwoCommSq.pasteSnd (Q : TwoCommSq k g) (R : TwoCommSq Q.snd f) : TwoCommSq k (f ≫ g) :=
  Q.paste R

/-- **The square pasted along the second projection is a 2-fibre product.** If `Q` is a 2-fibre
product of `(k, g)` and `R` is a 2-fibre product of `(Q.snd, f)`, then `Q.pasteSnd R` is a
2-fibre product of `(k, f ≫ g)`. This is
`CategoryTheory.Bicategory.isTwoFibreProduct_paste` with both squares explicit. -/
noncomputable def isTwoFibreProduct_pasteSnd (Q : TwoCommSq k g) (hQ : IsTwoFibreProduct Q)
    (R : TwoCommSq Q.snd f) (hR : IsTwoFibreProduct R) :
    IsTwoFibreProduct (Q.pasteSnd R) :=
  isTwoFibreProduct_paste hQ hR

end PasteSnd

end CategoryTheory.Bicategory

end
