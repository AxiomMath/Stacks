module

public import StacksFrontier.CategoryTheory.FiberedInGroupoids.Representability.EquivalenceOverComp
public import StacksFrontier.CategoryTheory.TwoFibreProduct.OverIso

/-!
# A triple 2-fibre product over a base as a category of composable pairs

Fix a base category `𝒞` and categories `𝒜`, `ℬ`, `ℰ`, `𝒮` over `𝒞`, with 1-morphisms
`F : 𝒜 ⥤ 𝒮`, `G : ℬ ⥤ 𝒮` and `H : ℰ ⥤ 𝒮`. Write

```text
ℛ  = 𝒜 ×_{F, 𝒮, G} ℬ,      ℛ' = ℬ ×_{G, 𝒮, H} ℰ,      ℛ₀ = 𝒜 ×_{F, 𝒮, H} ℰ
```

for the three 2-fibre products over `𝒞` of Stacks 0040
(`CategoryTheory.TwoFibreProductOver`). This file compares the *triple* product

```text
(𝒜 ×_𝒮 ℬ) ×_𝒮 ℰ = ℛ ×_{pr₁ ⋙ G, 𝒮, H} ℰ
```

with the category of *composable pairs*

```text
ℛ ×_{pr₁, ℬ, pr₀} ℛ'
```

and constructs the outer projection of the latter to `ℛ₀`. Over a fixed object `U` of `𝒞` an
object of the triple product is a triple `((a, b, α), c, β)` with `α : F a ≅ G b` and
`β : G b ≅ H c`, while an object of the category of composable pairs is a pair
`((a, b, α), (b', c, β))` together with an isomorphism `γ : b ≅ b'`; the comparison takes the
former to `((a, b, α), (b, c, β))` with the identity as that isomorphism, and the outer
projection takes the latter to `(a, c, β ∘ G γ ∘ α)`.

This is the over-`𝒞` form of the repeated application of Stacks 02XC and 02XD that
Stacks 04T4 (2) uses, together with the outer projection of Stacks 04S7 appearing in
Stacks 04T4 (3). The absolute versions, for Mathlib's
`CategoryTheory.Limits.CategoricalPullback`, are
`CategoryTheory.Limits.CategoricalPullback.assoc` and
`CategoryTheory.Limits.CategoricalPullback.pr₀₂`; they do not give these,
because the comparison isomorphism of an object is arbitrary in the absolute product and
vertical in the relative one, and the two notions are inequivalent.

## Main definitions

* `CategoryTheory.TwoFibreProductOver.TripleCat` and
  `CategoryTheory.TwoFibreProductOver.ComposablePairCat`: the two categories.
* `CategoryTheory.TwoFibreProductOver.composableOfTriple` and
  `CategoryTheory.TwoFibreProductOver.tripleOfComposable`: the comparison functors.
* `CategoryTheory.TwoFibreProductOver.outerProjection`: the outer projection
  `ℛ ×_ℬ ℛ' ⥤ ℛ₀`.

## Main results

* `CategoryTheory.TwoFibreProductOver.composableEquivalenceOver`: the comparison is an
  equivalence in the 2-category of categories over `𝒞`, in the sense of
  `StacksRepresentableCFG.EquivalenceOver`.
* `CategoryTheory.TwoFibreProductOver.outerProjection_comp_structureFunctor`: the outer
  projection is strictly over `𝒞`.

## Implementation notes

The unit and the counit are written out rather than obtained from a general criterion, so
that the forward 1-morphism of `composableEquivalenceOver` is literally
`composableOfTriple`: the explicit description of that functor on objects is what a consumer
of this comparison needs.

Only `G` is required to be over `𝒞` (`hG : G ⋙ p𝒮 = pℬ`): it is used to see that the image
under `G` of the comparison isomorphism `γ : b ≅ b'`, which is vertical in `ℬ`, is vertical
in `𝒮`. Nothing is required of `F` or `H`.
-/

@[expose] public section

open CategoryTheory

namespace CategoryTheory.TwoFibreProductOver

universe vC vA vB vE vS uC uA uB uE uS

attribute [local implicit_reducible] fst snd structureFunctor

variable {𝒞 : Type uC} [Category.{vC} 𝒞] {𝒜 : Type uA} [Category.{vA} 𝒜]
  {ℬ : Type uB} [Category.{vB} ℬ] {ℰ : Type uE} [Category.{vE} ℰ]
  {𝒮 : Type uS} [Category.{vS} 𝒮]

section Vertical

variable {p𝒳 : 𝒜 ⥤ 𝒞} {p𝒴 : ℬ ⥤ 𝒞} {p𝒮 : 𝒮 ⥤ 𝒞} {F : 𝒜 ⥤ 𝒮} {G : ℬ ⥤ 𝒮}

/-- The comparison isomorphism of an object of a 2-fibre product over `𝒞` is vertical over
any object of `𝒞` equal to its base. -/
lemma isHomLift_iso_hom {P : TwoFibreProductOver p𝒳 p𝒴 p𝒮 F G} {U : 𝒞} (h : P.base = U) :
    p𝒮.IsHomLift (𝟙 U) P.iso.hom := h ▸ P.vertical

end Vertical

variable (p𝒜 : 𝒜 ⥤ 𝒞) (pℬ : ℬ ⥤ 𝒞) (pℰ : ℰ ⥤ 𝒞) (p𝒮 : 𝒮 ⥤ 𝒞)
  (F : 𝒜 ⥤ 𝒮) (G : ℬ ⥤ 𝒮) (H : ℰ ⥤ 𝒮)

/-- The triple 2-fibre product `(𝒜 ×_𝒮 ℬ) ×_𝒮 ℰ` over `𝒞`, bracketed at the left: an
object over `U` is a triple `((a, b, α), c, β)` with `α : F a ≅ G b` and `β : G b ≅ H c`,
all of `a`, `b`, `c` over `U` and both isomorphisms vertical. -/
abbrev TripleCat : Type (max uC uA uB uE vS) :=
  TwoFibreProductOver (structureFunctor p𝒜 pℬ p𝒮 F G) pℰ p𝒮
    (snd p𝒜 pℬ p𝒮 F G ⋙ G) H

/-- The category of pairs of objects of `ℛ = 𝒜 ×_𝒮 ℬ` and `ℛ' = ℬ ×_𝒮 ℰ` *composable* over
`ℬ`: an object over `U` is a pair `((a, b, α), (b', c, β))` together with a vertical
isomorphism `b ≅ b'`. -/
abbrev ComposablePairCat : Type (max uC uA uB uE vS vB) :=
  TwoFibreProductOver (structureFunctor p𝒜 pℬ p𝒮 F G)
    (structureFunctor pℬ pℰ p𝒮 G H) pℬ (snd p𝒜 pℬ p𝒮 F G) (fst pℬ pℰ p𝒮 G H)

variable {p𝒜 pℬ pℰ p𝒮 F G H}

section Comparison

/-- The comparison `(𝒜 ×_𝒮 ℬ) ×_𝒮 ℰ ⥤ ℛ ×_ℬ ℛ'`, sending `((a, b, α), c, β)` to the
composable pair `((a, b, α), (b, c, β))` whose middle comparison isomorphism is the
identity of `b`. -/
def composableOfTriple :
    TripleCat p𝒜 pℬ pℰ p𝒮 F G H ⥤ ComposablePairCat p𝒜 pℬ pℰ p𝒮 F G H where
  obj P :=
    { base := P.base
      x := P.x
      y :=
        { base := P.base
          x := P.x.y
          y := P.y
          hx := P.x.hy.trans P.hx
          hy := P.hy
          iso := P.iso
          vertical := P.vertical }
      hx := P.hx
      hy := rfl
      iso := Iso.refl P.x.y
      vertical := IsHomLift.id (P.x.hy.trans P.hx) }
  map {P Q} f :=
    { hbase := f.hbase
      a := f.a
      b :=
        { hbase := f.hbase
          a := f.a.b
          b := f.b
          ha := isHomLift_b f.a f.hbase f.ha
          hb := f.hb
          w := f.w }
      ha := f.ha
      hb := structureFunctor_isHomLift _ f.hbase (isHomLift_b f.a f.hbase f.ha)
      w := (by rw [Category.comp_id, Category.id_comp] :
        f.a.b ≫ 𝟙 Q.x.y = 𝟙 P.x.y ≫ f.a.b) }
  map_id _ := rfl
  map_comp _ _ := rfl

/-- The comparison `composableOfTriple` keeps the base object. -/
@[simp] lemma composableOfTriple_obj_base (P : TripleCat p𝒜 pℬ pℰ p𝒮 F G H) :
    (composableOfTriple.obj P).base = P.base := rfl

/-- The first factor of `composableOfTriple.obj P` is the inner pair `P.x`. -/
@[simp] lemma composableOfTriple_obj_x (P : TripleCat p𝒜 pℬ pℰ p𝒮 F G H) :
    (composableOfTriple.obj P).x = P.x := rfl

/-- The first object of the second factor of `composableOfTriple.obj P` is `P.x.y`. -/
@[simp] lemma composableOfTriple_obj_y_x (P : TripleCat p𝒜 pℬ pℰ p𝒮 F G H) :
    (composableOfTriple.obj P).y.x = P.x.y := rfl

/-- The second object of the second factor of `composableOfTriple.obj P` is `P.y`. -/
@[simp] lemma composableOfTriple_obj_y_y (P : TripleCat p𝒜 pℬ pℰ p𝒮 F G H) :
    (composableOfTriple.obj P).y.y = P.y := rfl

/-- The comparison isomorphism of the second factor of `composableOfTriple.obj P` is `P.iso`. -/
@[simp] lemma composableOfTriple_obj_y_iso (P : TripleCat p𝒜 pℬ pℰ p𝒮 F G H) :
    (composableOfTriple.obj P).y.iso = P.iso := rfl

/-- The middle comparison isomorphism of `composableOfTriple.obj P` is the identity. -/
@[simp] lemma composableOfTriple_obj_iso (P : TripleCat p𝒜 pℬ pℰ p𝒮 F G H) :
    (composableOfTriple.obj P).iso = Iso.refl P.x.y := rfl

/-- The first component of `composableOfTriple.map f` is `f.a`. -/
@[simp] lemma composableOfTriple_map_a {P Q : TripleCat p𝒜 pℬ pℰ p𝒮 F G H} (f : P ⟶ Q) :
    (composableOfTriple.map f).a = f.a := rfl

/-- The first component of the second component of `composableOfTriple.map f` is `f.a.b`. -/
@[simp] lemma composableOfTriple_map_b_a {P Q : TripleCat p𝒜 pℬ pℰ p𝒮 F G H} (f : P ⟶ Q) :
    (composableOfTriple.map f).b.a = f.a.b := rfl

/-- The second component of the second component of `composableOfTriple.map f` is `f.b`. -/
@[simp] lemma composableOfTriple_map_b_b {P Q : TripleCat p𝒜 pℬ pℰ p𝒮 F G H} (f : P ⟶ Q) :
    (composableOfTriple.map f).b.b = f.b := rfl

/-- The comparison is strictly over `𝒞`. -/
@[simp] lemma composableOfTriple_comp_structureFunctor :
    composableOfTriple (p𝒜 := p𝒜) (pℬ := pℬ) (pℰ := pℰ) (p𝒮 := p𝒮) (F := F) (G := G)
        (H := H) ⋙
      structureFunctor (structureFunctor p𝒜 pℬ p𝒮 F G) (structureFunctor pℬ pℰ p𝒮 G H) pℬ
        (snd p𝒜 pℬ p𝒮 F G) (fst pℬ pℰ p𝒮 G H) =
    structureFunctor (structureFunctor p𝒜 pℬ p𝒮 F G) pℰ p𝒮 (snd p𝒜 pℬ p𝒮 F G ⋙ G) H := rfl

/-- The comparison `ℛ ×_ℬ ℛ' ⥤ (𝒜 ×_𝒮 ℬ) ×_𝒮 ℰ` in the other direction, sending a
composable pair `((a, b, α), (b', c, β))` with middle isomorphism `γ : b ≅ b'` to the
triple `((a, b, α), c, β ∘ G γ)`. -/
def tripleOfComposable (hG : G ⋙ p𝒮 = pℬ) :
    ComposablePairCat p𝒜 pℬ pℰ p𝒮 F G H ⥤ TripleCat p𝒜 pℬ pℰ p𝒮 F G H where
  obj Q :=
    { base := Q.base
      x := Q.x
      y := Q.y.y
      hx := Q.hx
      hy := Q.y.hy.trans Q.hy
      iso := G.mapIso Q.iso ≪≫ Q.y.iso
      vertical := by
        have h₁ : pℬ.IsHomLift (𝟙 Q.base) Q.iso.hom := Q.vertical
        have h₂ : p𝒮.IsHomLift (𝟙 Q.base) (G.map Q.iso.hom) :=
          Functor.isHomLift_map_of_comp_eq hG (𝟙 Q.base) Q.iso.hom
        have h₃ : p𝒮.IsHomLift (𝟙 Q.base) Q.y.iso.hom := isHomLift_iso_hom Q.hy
        exact (inferInstance :
          p𝒮.IsHomLift (𝟙 Q.base) (G.map Q.iso.hom ≫ Q.y.iso.hom)) }
  map {P Q} g :=
    { hbase := g.hbase
      a := g.a
      b := g.b.b
      ha := g.ha
      hb := isHomLift_b g.b g.hbase g.hb
      w := by
        have h₁ : g.a.b ≫ Q.iso.hom = P.iso.hom ≫ g.b.a := g.w
        have h₂ : G.map g.b.a ≫ Q.y.iso.hom = P.y.iso.hom ≫ H.map g.b.b := g.b.w
        exact (by rw [← Category.assoc, ← G.map_comp, h₁, G.map_comp, Category.assoc, h₂,
            Category.assoc] :
          G.map g.a.b ≫ (G.map Q.iso.hom ≫ Q.y.iso.hom)
            = (G.map P.iso.hom ≫ P.y.iso.hom) ≫ H.map g.b.b) }
  map_id _ := rfl
  map_comp _ _ := rfl

/-- The comparison `tripleOfComposable` keeps the base object. -/
@[simp] lemma tripleOfComposable_obj_base (hG : G ⋙ p𝒮 = pℬ)
    (Q : ComposablePairCat p𝒜 pℬ pℰ p𝒮 F G H) :
    ((tripleOfComposable hG).obj Q).base = Q.base := rfl

/-- The inner pair of `(tripleOfComposable hG).obj Q` is the first factor `Q.x`. -/
@[simp] lemma tripleOfComposable_obj_x (hG : G ⋙ p𝒮 = pℬ)
    (Q : ComposablePairCat p𝒜 pℬ pℰ p𝒮 F G H) :
    ((tripleOfComposable hG).obj Q).x = Q.x := rfl

/-- The last object of `(tripleOfComposable hG).obj Q` is `Q.y.y`. -/
@[simp] lemma tripleOfComposable_obj_y (hG : G ⋙ p𝒮 = pℬ)
    (Q : ComposablePairCat p𝒜 pℬ pℰ p𝒮 F G H) :
    ((tripleOfComposable hG).obj Q).y = Q.y.y := rfl

/-- The comparison isomorphism of `(tripleOfComposable hG).obj Q` is the image under `G` of the
middle isomorphism of `Q`, followed by the comparison isomorphism `Q.y.iso`. -/
@[simp] lemma tripleOfComposable_obj_iso (hG : G ⋙ p𝒮 = pℬ)
    (Q : ComposablePairCat p𝒜 pℬ pℰ p𝒮 F G H) :
    ((tripleOfComposable hG).obj Q).iso = G.mapIso Q.iso ≪≫ Q.y.iso := rfl

/-- The first component of `(tripleOfComposable hG).map g` is `g.a`. -/
@[simp] lemma tripleOfComposable_map_a (hG : G ⋙ p𝒮 = pℬ)
    {P Q : ComposablePairCat p𝒜 pℬ pℰ p𝒮 F G H} (g : P ⟶ Q) :
    ((tripleOfComposable hG).map g).a = g.a := rfl

/-- The second component of `(tripleOfComposable hG).map g` is `g.b.b`. -/
@[simp] lemma tripleOfComposable_map_b (hG : G ⋙ p𝒮 = pℬ)
    {P Q : ComposablePairCat p𝒜 pℬ pℰ p𝒮 F G H} (g : P ⟶ Q) :
    ((tripleOfComposable hG).map g).b = g.b.b := rfl

/-- The component of `composableUnit` at `P`: both components are identities, only the
comparison isomorphism `β` of `P` having been replaced by `β ∘ G(𝟙 b)`. -/
noncomputable def composableUnitApp (hG : G ⋙ p𝒮 = pℬ)
    (P : TripleCat p𝒜 pℬ pℰ p𝒮 F G H) :
    P ≅ (composableOfTriple ⋙ tripleOfComposable hG).obj P :=
  isoMkVertical (U := P.base) (Iso.refl P.x) (Iso.refl P.y)
    (IsHomLift.id P.hx) (IsHomLift.id P.hy)
    ((by rw [G.map_id, H.map_id, Category.id_comp, Category.id_comp, Category.comp_id] :
      G.map (𝟙 P.x.y) ≫ G.map (𝟙 P.x.y) ≫ P.iso.hom = P.iso.hom ≫ H.map (𝟙 P.y)))

/-- The unit of `composableEquivalenceOver`: on `((a, b, α), c, β)` the round trip changes
only the comparison isomorphism `β` into `β ∘ G(𝟙 b)`, so the unit has identity
components. -/
noncomputable def composableUnit (hG : G ⋙ p𝒮 = pℬ) :
    𝟭 (TripleCat p𝒜 pℬ pℰ p𝒮 F G H) ≅
      composableOfTriple ⋙ tripleOfComposable hG :=
  NatIso.ofComponents (composableUnitApp hG) (fun {P Q} f =>
    Hom.ext'
      ((by rw [Category.comp_id, Category.id_comp] : f.a ≫ 𝟙 Q.x = 𝟙 P.x ≫ f.a))
      ((by rw [Category.comp_id, Category.id_comp] : f.b ≫ 𝟙 Q.y = 𝟙 P.y ≫ f.b)))

/-- The component of `composableCounit` at `Q`: the identity on the first factor, and the
middle comparison isomorphism `γ` of `Q` on the second. -/
noncomputable def composableCounitApp (hG : G ⋙ p𝒮 = pℬ)
    (Q : ComposablePairCat p𝒜 pℬ pℰ p𝒮 F G H) :
    (tripleOfComposable hG ⋙ composableOfTriple).obj Q ≅ Q :=
  isoMkVertical (U := Q.base) (Iso.refl Q.x)
    (isoMkVertical (U := Q.base) Q.iso (Iso.refl Q.y.y) Q.vertical
      (IsHomLift.id (Q.y.hy.trans Q.hy))
      ((by rw [H.map_id, Category.comp_id] :
        G.map Q.iso.hom ≫ Q.y.iso.hom
          = (G.map Q.iso.hom ≫ Q.y.iso.hom) ≫ H.map (𝟙 Q.y.y))))
    (IsHomLift.id Q.hx)
    (structureFunctor_isHomLift _ (𝟙 Q.base) Q.vertical)
    rfl

/-- The counit of `composableEquivalenceOver`: on a composable pair with middle isomorphism
`γ : b ≅ b'` the round trip replaces `b'` by `b` and `γ` by the identity, and the counit is
`γ` itself in the second factor. -/
noncomputable def composableCounit (hG : G ⋙ p𝒮 = pℬ) :
    tripleOfComposable hG ⋙ composableOfTriple ≅
      𝟭 (ComposablePairCat p𝒜 pℬ pℰ p𝒮 F G H) :=
  NatIso.ofComponents (composableCounitApp hG) (fun {P Q} g =>
    Hom.ext'
      ((by rw [Category.comp_id, Category.id_comp] : g.a ≫ 𝟙 Q.x = 𝟙 P.x ≫ g.a))
      (Hom.ext'
        ((g.w : g.a.b ≫ Q.iso.hom = P.iso.hom ≫ g.b.a))
        ((by rw [Category.comp_id, Category.id_comp] :
          g.b.b ≫ 𝟙 Q.y.y = 𝟙 P.y.y ≫ g.b.b))))

/-- **The over-`𝒞` form of Stacks 02XC and 02XD, in the shape Stacks 04T4 (2) uses.** The
triple 2-fibre product `(𝒜 ×_𝒮 ℬ) ×_𝒮 ℰ` over `𝒞` is equivalent, in the 2-category of
categories over `𝒞`, to the category `ℛ ×_ℬ ℛ'` of composable pairs, by the comparison
`composableOfTriple`. -/
noncomputable def composableEquivalenceOver (hG : G ⋙ p𝒮 = pℬ) :
    StacksRepresentableCFG.EquivalenceOver
      (structureFunctor (structureFunctor p𝒜 pℬ p𝒮 F G) pℰ p𝒮
        (snd p𝒜 pℬ p𝒮 F G ⋙ G) H)
      (structureFunctor (structureFunctor p𝒜 pℬ p𝒮 F G) (structureFunctor pℬ pℰ p𝒮 G H) pℬ
        (snd p𝒜 pℬ p𝒮 F G) (fst pℬ pℰ p𝒮 G H)) where
  hom := ⟨composableOfTriple, composableOfTriple_comp_structureFunctor⟩
  inv := ⟨tripleOfComposable hG, rfl⟩
  unitIso := composableUnit hG
  counitIso := composableCounit hG
  unit_over := by
    refine StacksRepresentableCFG.whiskerRight_eq_eqToHom _ _ _ (fun P => ?_)
    exact structureFunctor_isHomLift _ (𝟙 P.base) (IsHomLift.id P.hx)
  counit_over := by
    refine StacksRepresentableCFG.whiskerRight_eq_eqToHom _ _ _ (fun Q => ?_)
    exact structureFunctor_isHomLift _ (𝟙 Q.base) (IsHomLift.id Q.hx)

end Comparison

section OuterProjection

/-- **The over-`𝒞` form of the outer projection of Stacks 04S7.** The functor
`ℛ ×_ℬ ℛ' ⥤ ℛ₀ = 𝒜 ×_𝒮 ℰ` forgetting the middle factor: a composable pair
`((a, b, α), (b', c, β))` with middle isomorphism `γ : b ≅ b'` is sent to
`(a, c, β ∘ G γ ∘ α)`. -/
def outerProjection (hG : G ⋙ p𝒮 = pℬ) :
    ComposablePairCat p𝒜 pℬ pℰ p𝒮 F G H ⥤ TwoFibreProductOver p𝒜 pℰ p𝒮 F H where
  obj Q :=
    { base := Q.base
      x := Q.x.x
      y := Q.y.y
      hx := Q.x.hx.trans Q.hx
      hy := Q.y.hy.trans Q.hy
      iso := Q.x.iso ≪≫ G.mapIso Q.iso ≪≫ Q.y.iso
      vertical := by
        have h₀ : p𝒮.IsHomLift (𝟙 Q.base) Q.x.iso.hom := isHomLift_iso_hom Q.hx
        have h₁ : pℬ.IsHomLift (𝟙 Q.base) Q.iso.hom := Q.vertical
        have h₂ : p𝒮.IsHomLift (𝟙 Q.base) (G.map Q.iso.hom) :=
          Functor.isHomLift_map_of_comp_eq hG (𝟙 Q.base) Q.iso.hom
        have h₃ : p𝒮.IsHomLift (𝟙 Q.base) Q.y.iso.hom := isHomLift_iso_hom Q.hy
        exact (inferInstance : p𝒮.IsHomLift (𝟙 Q.base)
          (Q.x.iso.hom ≫ G.map Q.iso.hom ≫ Q.y.iso.hom)) }
  map {P Q} g :=
    { hbase := g.hbase
      a := g.a.a
      b := g.b.b
      ha := isHomLift_a g.a g.hbase g.ha
      hb := isHomLift_b g.b g.hbase g.hb
      w := by
        have h₀ : F.map g.a.a ≫ Q.x.iso.hom = P.x.iso.hom ≫ G.map g.a.b := g.a.w
        have h₁ : g.a.b ≫ Q.iso.hom = P.iso.hom ≫ g.b.a := g.w
        have h₂ : G.map g.b.a ≫ Q.y.iso.hom = P.y.iso.hom ≫ H.map g.b.b := g.b.w
        have key : G.map g.a.b ≫ G.map Q.iso.hom ≫ Q.y.iso.hom
            = G.map P.iso.hom ≫ P.y.iso.hom ≫ H.map g.b.b := by
          rw [← Category.assoc, ← G.map_comp, h₁, G.map_comp, Category.assoc, h₂]
        exact (by rw [← Category.assoc, h₀, Category.assoc, key, Category.assoc,
            ← Category.assoc (G.map P.iso.hom)] :
          F.map g.a.a ≫ Q.x.iso.hom ≫ G.map Q.iso.hom ≫ Q.y.iso.hom
            = (P.x.iso.hom ≫ G.map P.iso.hom ≫ P.y.iso.hom) ≫ H.map g.b.b) }
  map_id _ := rfl
  map_comp _ _ := rfl

/-- The outer projection keeps the base object. -/
@[simp] lemma outerProjection_obj_base (hG : G ⋙ p𝒮 = pℬ)
    (Q : ComposablePairCat p𝒜 pℬ pℰ p𝒮 F G H) :
    ((outerProjection hG).obj Q).base = Q.base := rfl

/-- The first object of `(outerProjection hG).obj Q` is `Q.x.x`. -/
@[simp] lemma outerProjection_obj_x (hG : G ⋙ p𝒮 = pℬ)
    (Q : ComposablePairCat p𝒜 pℬ pℰ p𝒮 F G H) :
    ((outerProjection hG).obj Q).x = Q.x.x := rfl

/-- The second object of `(outerProjection hG).obj Q` is `Q.y.y`. -/
@[simp] lemma outerProjection_obj_y (hG : G ⋙ p𝒮 = pℬ)
    (Q : ComposablePairCat p𝒜 pℬ pℰ p𝒮 F G H) :
    ((outerProjection hG).obj Q).y = Q.y.y := rfl

/-- The first component of `(outerProjection hG).map g` is `g.a.a`. -/
@[simp] lemma outerProjection_map_a (hG : G ⋙ p𝒮 = pℬ)
    {P Q : ComposablePairCat p𝒜 pℬ pℰ p𝒮 F G H} (g : P ⟶ Q) :
    ((outerProjection hG).map g).a = g.a.a := rfl

/-- The second component of `(outerProjection hG).map g` is `g.b.b`. -/
@[simp] lemma outerProjection_map_b (hG : G ⋙ p𝒮 = pℬ)
    {P Q : ComposablePairCat p𝒜 pℬ pℰ p𝒮 F G H} (g : P ⟶ Q) :
    ((outerProjection hG).map g).b = g.b.b := rfl

/-- The outer projection is strictly over `𝒞`. -/
@[simp] lemma outerProjection_comp_structureFunctor (hG : G ⋙ p𝒮 = pℬ) :
    outerProjection (p𝒜 := p𝒜) (pℬ := pℬ) (pℰ := pℰ) (p𝒮 := p𝒮) (F := F) (G := G)
        (H := H) hG ⋙ structureFunctor p𝒜 pℰ p𝒮 F H =
      structureFunctor (structureFunctor p𝒜 pℬ p𝒮 F G) (structureFunctor pℬ pℰ p𝒮 G H) pℬ
        (snd p𝒜 pℬ p𝒮 F G) (fst pℬ pℰ p𝒮 G H) := rfl

end OuterProjection

end CategoryTheory.TwoFibreProductOver

end
