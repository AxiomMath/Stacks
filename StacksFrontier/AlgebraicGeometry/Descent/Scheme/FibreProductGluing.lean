module

public import StacksFrontier.AlgebraicGeometry.Descent.Scheme.SingleMorphismAction

/-!
# Descent data for a family, from gluing data on the literal fibre products

`AlgebraicGeometry.DescentData` asks for its gluing isomorphisms as isomorphisms between binary
products taken in `CategoryTheory.Over S`, and for its cocycle condition as a diagram on a
left-associated triple product written with `CategoryTheory.Limits.prodMapLastTwo` and
`CategoryTheory.Limits.prodMapFirstThird`.  Gluing data, on the other hand, arise on the literal
fibre products of schemes: an isomorphism `V i ×_S X j ≅ X i ×_S V j` over `X i ×_S X j`, with
the cocycle condition read on generalized points.  This file is the passage from the second
shape to the first, for a family of morphisms indexed by an arbitrary type.

## Main definitions

* `AlgebraicGeometry.DescentData.fibreAct` is the action determined by gluing data on the fibre
  products: a point of `V i` and a point of `X j` lying over one point of `S` produce a point of
  `V j`.
* `AlgebraicGeometry.DescentData.FibreCocycle` is the cocycle condition on that action.
* `AlgebraicGeometry.DescentData.fibreGluingHom` and
  `AlgebraicGeometry.DescentData.fibreGluingIso` carry a morphism, respectively an isomorphism,
  of the fibre products to the shape the field `gluing` asks for.
* `AlgebraicGeometry.DescentData.ofFibreGluing` is **the constructor**: a descent datum for a
  family of morphisms, from a family of isomorphisms of the literal fibre products.

## Main results

* `AlgebraicGeometry.DescentData.cocycle_of_prodLift_snd`: **the cocycle diagram of a family
  follows from one equation per triple of indices.**  Two of the three components of the diagram
  hold for any family of candidate gluing maps lying over the pairwise bases; only the component
  landing in the third object says anything, and what it says is that acting twice is acting
  once.
* `AlgebraicGeometry.DescentData.ofFibreGluing_obj` and
  `AlgebraicGeometry.DescentData.ofFibreGluing_gluingPullbackIso_hom` read the input data back
  off the constructed datum, the latter through
  `AlgebraicGeometry.DescentData.gluingPullbackIso`, which is the coordinate system the
  effectivity machinery is phrased in.

## Implementation notes

The comparison between the two coordinate systems is
`CategoryTheory.Over.prodLeftIsoPullback` at each slot, and the whole content of the translation
is that it is compatible with both projections.  Conjugating by it turns a morphism of fibre
products into a morphism of `S`-schemes — the condition `ht₁`, that the morphism lie over the
first factor of the pairwise base, is exactly what makes the conjugate a morphism over `S` — and
a pair of generalized points of a product in `Over S` into a pair of generalized points of the
fibre product, which is
`AlgebraicGeometry.DescentData.left_prodLift_comp_prodLeftIsoPullback`.

The cocycle condition is handled by evaluating both sides of the diagram at the universal
generalized point of the triple product, where
`CategoryTheory.Limits.prodLift_triple_eq_id` says that the triple of projections is the
identity.  The two components landing in `X i ⨯ X j` are then formal consequences of `ht₁` and
`ht₂`, and the one landing in `V k` is the action law.  This is why the constructor asks for the
cocycle condition on generalized points and not as a diagram: a diagram would have to name a
spelling of the triple fibre product, and the three projections of the universal point of
whichever spelling is chosen are exactly a triple of generalized points.

For one morphism this is `AlgebraicGeometry.DescentDatum.ofPullbackIso`, which is the case
`ι = Unit` and is defined from the declarations here.

## References

* [Stacks Project, Tag 023W](https://stacks.math.columbia.edu/tag/023W)
* [Stacks Project, Tag 02VQ](https://stacks.math.columbia.edu/tag/02VQ)
-/

@[expose] public section

noncomputable section

open CategoryTheory CategoryTheory.Limits

universe u v

namespace AlgebraicGeometry.DescentData

variable {ι : Type v} {S : Scheme.{u}} {X : ι → Scheme.{u}}

/-! ### The action of gluing data on the fibre products -/

section Act

variable (f : ∀ i, X i ⟶ S) (V : ∀ i, Over (X i))
  (t : ∀ i j, pullback ((V i).hom ≫ f i) (f j) ⟶ pullback (f i) ((V j).hom ≫ f j))

/-- **The action determined by gluing data on the literal fibre products.**  A point `v` of
`V i` and a point `x` of `X j` lying over one point of `S` name a point of `V i ×_S X j`; the
`V j`-component of its image under the gluing map is a point of `V j`, lying over `x` by
`AlgebraicGeometry.DescentData.fibreAct_comp_hom`. -/
def fibreAct (i j : ι) {Z : Scheme.{u}} (v : Z ⟶ (V i).left) (x : Z ⟶ X j)
    (h : v ≫ (V i).hom ≫ f i = x ≫ f j) : Z ⟶ (V j).left :=
  pullback.lift v x h ≫ t i j ≫ pullback.snd (f i) ((V j).hom ≫ f j)

/-- **The point produced by the action lies over the acting point.** -/
lemma fibreAct_comp_hom (i j : ι)
    (ht₂ : t i j ≫ pullback.snd (f i) ((V j).hom ≫ f j) ≫ (V j).hom =
      pullback.snd ((V i).hom ≫ f i) (f j))
    {Z : Scheme.{u}} (v : Z ⟶ (V i).left) (x : Z ⟶ X j)
    (h : v ≫ (V i).hom ≫ f i = x ≫ f j) :
    fibreAct f V t i j v x h ≫ (V j).hom = x := by
  rw [fibreAct, Category.assoc, Category.assoc, ht₂, pullback.lift_snd]

/-- The action depends on its two points only through their values, not through the proof that
they lie over one point of `S`. -/
lemma fibreAct_congr (i j : ι) {Z : Scheme.{u}} {v v' : Z ⟶ (V i).left} {x x' : Z ⟶ X j}
    (hv : v = v') (hx : x = x') (h : v ≫ (V i).hom ≫ f i = x ≫ f j)
    (h' : v' ≫ (V i).hom ≫ f i = x' ≫ f j) :
    fibreAct f V t i j v x h = fibreAct f V t i j v' x' h' := by
  subst hv; subst hx; rfl

/-- The action commutes with change of test scheme. -/
lemma comp_fibreAct (i j : ι) {Z Z' : Scheme.{u}} (k : Z' ⟶ Z) (v : Z ⟶ (V i).left)
    (x : Z ⟶ X j) (h : v ≫ (V i).hom ≫ f i = x ≫ f j)
    (h' : (k ≫ v) ≫ (V i).hom ≫ f i = (k ≫ x) ≫ f j) :
    k ≫ fibreAct f V t i j v x h = fibreAct f V t i j (k ≫ v) (k ≫ x) h' := by
  have hk : k ≫ pullback.lift v x h = pullback.lift (k ≫ v) (k ≫ x) h' :=
    pullback.hom_ext (by rw [Category.assoc, pullback.lift_fst, pullback.lift_fst])
      (by rw [Category.assoc, pullback.lift_snd, pullback.lift_snd])
  rw [fibreAct, fibreAct, ← Category.assoc, hk]

/-- The point produced by the action lies over a second acting point as soon as the two acting
points lie over one point of `S`.  This is the side condition of the second action in the cocycle
condition. -/
lemma fibreAct_comp_hom_comp (i j k : ι)
    (ht₂ : t i j ≫ pullback.snd (f i) ((V j).hom ≫ f j) ≫ (V j).hom =
      pullback.snd ((V i).hom ≫ f i) (f j))
    {Z : Scheme.{u}} (v : Z ⟶ (V i).left) (x : Z ⟶ X j) (y : Z ⟶ X k)
    (hv : v ≫ (V i).hom ≫ f i = x ≫ f j) (hw : x ≫ f j = y ≫ f k) :
    fibreAct f V t i j v x hv ≫ (V j).hom ≫ f j = y ≫ f k := by
  rw [← Category.assoc, fibreAct_comp_hom f V t i j ht₂, hw]

/-- **The cocycle condition on the action of gluing data on the fibre products**: acting by a
point of `X j` and then by a point of `X k` is acting by the point of `X k` directly. -/
def FibreCocycle : Prop :=
  ∀ (i j k : ι) {Z : Scheme.{u}} (v : Z ⟶ (V i).left) (x : Z ⟶ X j) (y : Z ⟶ X k)
    (hv : v ≫ (V i).hom ≫ f i = x ≫ f j) (hw : x ≫ f j = y ≫ f k)
    (hvx : fibreAct f V t i j v x hv ≫ (V j).hom ≫ f j = y ≫ f k),
      fibreAct f V t j k (fibreAct f V t i j v x hv) y hvx =
        fibreAct f V t i k v y (hv.trans hw)

end Act

/-! ### From the fibre products to the products in `Over S` -/

section Transport

variable (f : ∀ i, X i ⟶ S) (V : ∀ i, Over (X i))

/-- **A pair of generalized points of a product in `Over S` is a pair of generalized points of
the literal fibre product.** -/
lemma left_prodLift_comp_prodLeftIsoPullback (i j : ι) {T : Over S}
    (v : T ⟶ (Over.map (f i)).obj (V i)) (x : T ⟶ Over.mk (f j)) :
    Over.Hom.left (prod.lift v x) ≫
        (Over.prodLeftIsoPullback ((Over.map (f i)).obj (V i)) (Over.mk (f j))).hom =
      pullback.lift v.left x.left ((Over.w v).trans (Over.w x).symm) := by
  refine pullback.hom_ext ?_ ?_
  · rw [Category.assoc, Over.prodLeftIsoPullback_hom_fst, ← Over.comp_left, prod.lift_fst]
    exact (pullback.lift_fst _ _ _).symm
  · rw [Category.assoc, Over.prodLeftIsoPullback_hom_snd, ← Over.comp_left, prod.lift_snd]
    exact (pullback.lift_snd _ _ _).symm

variable (t : ∀ i j, pullback ((V i).hom ≫ f i) (f j) ⟶ pullback (f i) ((V j).hom ≫ f j))

/-- **The conjugate of a gluing map of the fibre products preserves the first component of the
pairwise base.**  This is the condition that makes the conjugate a morphism of `S`-schemes, and
it is also the first of the two conditions a gluing isomorphism obeys. -/
lemma conjugate_comp_fst (i j : ι)
    (ht₁ : t i j ≫ pullback.fst (f i) ((V j).hom ≫ f j) =
      pullback.fst ((V i).hom ≫ f i) (f j) ≫ (V i).hom) :
    ((Over.prodLeftIsoPullback ((Over.map (f i)).obj (V i)) (Over.mk (f j))).hom ≫ t i j ≫
          (Over.prodLeftIsoPullback (Over.mk (f i))
            ((Over.map (f j)).obj (V j))).inv) ≫
        Over.Hom.left (prod.fst : Over.mk (f i) ⨯ (Over.map (f j)).obj (V j) ⟶
          Over.mk (f i)) =
      Over.Hom.left (prod.fst : (Over.map (f i)).obj (V i) ⨯ Over.mk (f j) ⟶
        (Over.map (f i)).obj (V i)) ≫ (V i).hom := by
  have htgt : (Over.prodLeftIsoPullback (Over.mk (f i))
          ((Over.map (f j)).obj (V j))).inv ≫
        Over.Hom.left (prod.fst : Over.mk (f i) ⨯ (Over.map (f j)).obj (V j) ⟶
          Over.mk (f i)) =
      pullback.fst (f i) ((V j).hom ≫ f j) :=
    Over.prodLeftIsoPullback_inv_fst _ _
  have hsrc : (Over.prodLeftIsoPullback ((Over.map (f i)).obj (V i)) (Over.mk (f j))).hom ≫
        pullback.fst ((V i).hom ≫ f i) (f j) =
      Over.Hom.left (prod.fst : (Over.map (f i)).obj (V i) ⨯ Over.mk (f j) ⟶
        (Over.map (f i)).obj (V i)) :=
    Over.prodLeftIsoPullback_hom_fst _ _
  simp only [Category.assoc]
  rw [htgt, ht₁, ← Category.assoc, hsrc]

/-- **The conjugate of a gluing map of the fibre products preserves the second component of the
pairwise base.** -/
lemma conjugate_comp_snd (i j : ι)
    (ht₂ : t i j ≫ pullback.snd (f i) ((V j).hom ≫ f j) ≫ (V j).hom =
      pullback.snd ((V i).hom ≫ f i) (f j)) :
    ((Over.prodLeftIsoPullback ((Over.map (f i)).obj (V i)) (Over.mk (f j))).hom ≫ t i j ≫
          (Over.prodLeftIsoPullback (Over.mk (f i))
            ((Over.map (f j)).obj (V j))).inv) ≫
        Over.Hom.left (prod.snd : Over.mk (f i) ⨯ (Over.map (f j)).obj (V j) ⟶
          (Over.map (f j)).obj (V j)) ≫ (V j).hom =
      Over.Hom.left (prod.snd : (Over.map (f i)).obj (V i) ⨯ Over.mk (f j) ⟶
        Over.mk (f j)) := by
  have htgt : (Over.prodLeftIsoPullback (Over.mk (f i))
          ((Over.map (f j)).obj (V j))).inv ≫
        Over.Hom.left (prod.snd : Over.mk (f i) ⨯ (Over.map (f j)).obj (V j) ⟶
          (Over.map (f j)).obj (V j)) =
      pullback.snd (f i) ((V j).hom ≫ f j) :=
    Over.prodLeftIsoPullback_inv_snd _ _
  have hsrc : (Over.prodLeftIsoPullback ((Over.map (f i)).obj (V i)) (Over.mk (f j))).hom ≫
        pullback.snd ((V i).hom ≫ f i) (f j) =
      Over.Hom.left (prod.snd : (Over.map (f i)).obj (V i) ⨯ Over.mk (f j) ⟶
        Over.mk (f j)) :=
    Over.prodLeftIsoPullback_hom_snd _ _
  simp only [Category.assoc]
  rw [← Category.assoc
    (Over.prodLeftIsoPullback (Over.mk (f i)) ((Over.map (f j)).obj (V j))).inv,
    htgt, ht₂, hsrc]

/-- **A candidate gluing map in the product formalism from one on the literal fibre products.**
A morphism `V i ×_S X j ⟶ X i ×_S V j` of schemes carrying the projection to `X i` to the
projection of the first factor composed with the structure map of `V i` is a morphism of
`S`-schemes, so it defines a morphism of the products taken in `Over S`. -/
def fibreGluingHom (i j : ι)
    (ht₁ : t i j ≫ pullback.fst (f i) ((V j).hom ≫ f j) =
      pullback.fst ((V i).hom ≫ f i) (f j) ≫ (V i).hom) :
    (Over.map (f i)).obj (V i) ⨯ Over.mk (f j) ⟶
      Over.mk (f i) ⨯ (Over.map (f j)).obj (V j) :=
  Over.homMk
    ((Over.prodLeftIsoPullback ((Over.map (f i)).obj (V i)) (Over.mk (f j))).hom ≫ t i j ≫
      (Over.prodLeftIsoPullback (Over.mk (f i)) ((Over.map (f j)).obj (V j))).inv) (by
    have hP2 : Over.Hom.left
          (prod.fst : Over.mk (f i) ⨯ (Over.map (f j)).obj (V j) ⟶ Over.mk (f i)) ≫ f i =
        (Over.mk (f i) ⨯ (Over.map (f j)).obj (V j)).hom := Over.w prod.fst
    have hP1 : Over.Hom.left
          (prod.fst : (Over.map (f i)).obj (V i) ⨯ Over.mk (f j) ⟶
            (Over.map (f i)).obj (V i)) ≫ ((V i).hom ≫ f i) =
        ((Over.map (f i)).obj (V i) ⨯ Over.mk (f j)).hom := Over.w prod.fst
    rw [← hP2, ← hP1, ← Category.assoc, conjugate_comp_fst f V t i j ht₁, Category.assoc])

/-- The underlying morphism of schemes of the candidate gluing map built from fibre-product data
is the given one, conjugated by the two comparison isomorphisms. -/
lemma fibreGluingHom_left (i j : ι)
    (ht₁ : t i j ≫ pullback.fst (f i) ((V j).hom ≫ f j) =
      pullback.fst ((V i).hom ≫ f i) (f j) ≫ (V i).hom) :
    Over.Hom.left (fibreGluingHom f V t i j ht₁) =
      (Over.prodLeftIsoPullback ((Over.map (f i)).obj (V i)) (Over.mk (f j))).hom ≫ t i j ≫
        (Over.prodLeftIsoPullback (Over.mk (f i)) ((Over.map (f j)).obj (V j))).inv := rfl

/-- The candidate gluing map built from fibre-product data preserves the first component of the
pairwise base. -/
lemma fibreGluingHom_comp_fst (i j : ι)
    (ht₁ : t i j ≫ pullback.fst (f i) ((V j).hom ≫ f j) =
      pullback.fst ((V i).hom ≫ f i) (f j) ≫ (V i).hom) :
    fibreGluingHom f V t i j ht₁ ≫ prod.fst = prod.fst ≫ structureMap (f i) (V i) :=
  Over.OverMorphism.ext (conjugate_comp_fst f V t i j ht₁)

/-- The candidate gluing map built from fibre-product data preserves the second component of the
pairwise base. -/
lemma fibreGluingHom_comp_snd_structureMap (i j : ι)
    (ht₁ : t i j ≫ pullback.fst (f i) ((V j).hom ≫ f j) =
      pullback.fst ((V i).hom ≫ f i) (f j) ≫ (V i).hom)
    (ht₂ : t i j ≫ pullback.snd (f i) ((V j).hom ≫ f j) ≫ (V j).hom =
      pullback.snd ((V i).hom ≫ f i) (f j)) :
    fibreGluingHom f V t i j ht₁ ≫ prod.snd ≫ structureMap (f j) (V j) = prod.snd :=
  Over.OverMorphism.ext (conjugate_comp_snd f V t i j ht₂)

/-- **The two actions agree.**  Evaluating the candidate gluing map of
`AlgebraicGeometry.DescentData.fibreGluingHom` at a pair of generalized points of the product in
`Over S` and taking the second component is the action
`AlgebraicGeometry.DescentData.fibreAct` of the fibre-product data. -/
lemma left_prodLift_comp_fibreGluingHom_comp_snd (i j : ι)
    (ht₁ : t i j ≫ pullback.fst (f i) ((V j).hom ≫ f j) =
      pullback.fst ((V i).hom ≫ f i) (f j) ≫ (V i).hom) {T : Over S}
    (v : T ⟶ (Over.map (f i)).obj (V i)) (x : T ⟶ Over.mk (f j)) :
    Over.Hom.left (prod.lift v x ≫ fibreGluingHom f V t i j ht₁ ≫ prod.snd) =
      fibreAct f V t i j v.left x.left ((Over.w v).trans (Over.w x).symm) := by
  have htgt : (Over.prodLeftIsoPullback (Over.mk (f i))
          ((Over.map (f j)).obj (V j))).inv ≫
        Over.Hom.left (prod.snd : Over.mk (f i) ⨯ (Over.map (f j)).obj (V j) ⟶
          (Over.map (f j)).obj (V j)) =
      pullback.snd (f i) ((V j).hom ≫ f j) :=
    Over.prodLeftIsoPullback_inv_snd _ _
  rw [Over.comp_left, Over.comp_left, fibreGluingHom_left f V t i j ht₁]
  simp only [Category.assoc]
  rw [htgt, ← Category.assoc (Over.Hom.left (prod.lift v x)),
    left_prodLift_comp_prodLeftIsoPullback f V i j v x]
  rfl

end Transport

/-! ### The cocycle diagram from one equation per triple of indices -/

section Cocycle

variable (f : ∀ i, X i ⟶ S) (V : ∀ i, Over (X i))
  (Φ : ∀ i j, (Over.map (f i)).obj (V i) ⨯ Over.mk (f j) ⟶
    Over.mk (f i) ⨯ (Over.map (f j)).obj (V j))

/-- **The cocycle diagram of a family follows from one equation per triple of indices.**  For a
family of candidate gluing maps lying over the pairwise bases, the two components of the cocycle
diagram landing in `X i ⨯ X j` hold automatically; the component landing in `V k` says that
acting twice is acting once, which is the hypothesis `h3`. -/
lemma cocycle_of_prodLift_snd
    (h1 : ∀ i j, Φ i j ≫ prod.fst = prod.fst ≫ structureMap (f i) (V i))
    (h2 : ∀ i j, Φ i j ≫ prod.snd ≫ structureMap (f j) (V j) = prod.snd)
    (h3 : ∀ (i j k : ι) {T : Over S} (v : T ⟶ (Over.map (f i)).obj (V i))
      (x : T ⟶ Over.mk (f j)) (y : T ⟶ Over.mk (f k)),
        prod.lift (prod.lift v x ≫ Φ i j ≫ prod.snd) y ≫ Φ j k ≫ prod.snd =
          prod.lift v y ≫ Φ i k ≫ prod.snd)
    (i j k : ι) :
    prod.map (Φ i j) (𝟙 (Over.mk (f k))) ≫ prodMapLastTwo (Φ j k) =
      prodMapFirstThird (Φ i k) := by
  obtain ⟨v, hv⟩ : ∃ v : ((Over.map (f i)).obj (V i) ⨯ Over.mk (f j)) ⨯ Over.mk (f k) ⟶
      (Over.map (f i)).obj (V i), v = prod.fst ≫ prod.fst := ⟨_, rfl⟩
  obtain ⟨x, hx⟩ : ∃ x : ((Over.map (f i)).obj (V i) ⨯ Over.mk (f j)) ⨯ Over.mk (f k) ⟶
      Over.mk (f j), x = prod.fst ≫ prod.snd := ⟨_, rfl⟩
  have huniv : prod.lift (prod.lift v x)
      (prod.snd : ((Over.map (f i)).obj (V i) ⨯ Over.mk (f j)) ⨯ Over.mk (f k) ⟶
        Over.mk (f k)) = 𝟙 _ := by
    rw [hv, hx]; exact prodLift_triple_eq_id _ _ _
  have hL1 : prod.lift (prod.lift v x) prod.snd ≫ prod.map (Φ i j) (𝟙 (Over.mk (f k))) ≫
      prodMapLastTwo (Φ j k) ≫ prod.fst = prod.lift (v ≫ structureMap (f i) (V i)) x := by
    simp only [prodMapLastTwo, prod.associator_hom, prod.associator_inv]
    refine prod.hom_ext ?_ ?_
    · simp [prod.comp_lift, ← prod.lift_fst_comp_snd_comp, h1]
    · simp [prod.comp_lift, ← prod.lift_fst_comp_snd_comp, h1, h2]
  have hR1 : prod.lift (prod.lift v x) prod.snd ≫ prodMapFirstThird (Φ i k) ≫ prod.fst =
      prod.lift (v ≫ structureMap (f i) (V i)) x := by
    simp only [prodMapFirstThird, prodMapLastTwo, prod.associator_hom, prod.associator_inv,
      prod.braiding_hom]
    refine prod.hom_ext ?_ ?_
    · simp [prod.comp_lift, ← prod.lift_fst_comp_snd_comp, h1]
    · simp [prod.comp_lift, ← prod.lift_fst_comp_snd_comp]
  have hL2 : prod.lift (prod.lift v x) prod.snd ≫ prod.map (Φ i j) (𝟙 (Over.mk (f k))) ≫
        prodMapLastTwo (Φ j k) ≫ prod.snd =
      prod.lift (prod.lift v x ≫ Φ i j ≫ prod.snd) prod.snd ≫ Φ j k ≫ prod.snd := by
    simp only [prodMapLastTwo, prod.associator_hom, prod.associator_inv]
    simp [prod.comp_lift, prod.comp_lift_assoc, ← prod.lift_fst_comp_snd_comp]
  have hR2 : prod.lift (prod.lift v x) prod.snd ≫ prodMapFirstThird (Φ i k) ≫ prod.snd =
      prod.lift v prod.snd ≫ Φ i k ≫ prod.snd := by
    simp only [prodMapFirstThird, prodMapLastTwo, prod.associator_hom, prod.associator_inv,
      prod.braiding_hom]
    simp [prod.comp_lift, prod.comp_lift_assoc, ← prod.lift_fst_comp_snd_comp]
  rw [huniv, Category.id_comp] at hL1 hR1 hL2 hR2
  refine prod.hom_ext ?_ ?_
  · rw [Category.assoc, hL1, hR1]
  · rw [Category.assoc, hL2, hR2, h3 i j k v x prod.snd]

end Cocycle

/-! ### The constructor -/

section Constructor

variable (f : ∀ i, X i ⟶ S) (V : ∀ i, Over (X i))
  (t : ∀ i j, pullback ((V i).hom ≫ f i) (f j) ≅ pullback (f i) ((V j).hom ≫ f j))

/-- **An isomorphism of the products taken in `Over S` from one of the literal fibre products.**
This is `AlgebraicGeometry.DescentData.fibreGluingHom` for an isomorphism; the underlying
morphism of `S`-schemes is unchanged. -/
def fibreGluingOverIso
    (ht₁ : ∀ i j, (t i j).hom ≫ pullback.fst (f i) ((V j).hom ≫ f j) =
      pullback.fst ((V i).hom ≫ f i) (f j) ≫ (V i).hom) (i j : ι) :
    (Over.map (f i)).obj (V i) ⨯ Over.mk (f j) ≅
      Over.mk (f i) ⨯ (Over.map (f j)).obj (V j) :=
  Over.isoMk
    (Over.prodLeftIsoPullback ((Over.map (f i)).obj (V i)) (Over.mk (f j)) ≪≫ t i j ≪≫
      (Over.prodLeftIsoPullback (Over.mk (f i)) ((Over.map (f j)).obj (V j))).symm)
    (Over.w (fibreGluingHom f V (fun a b ↦ (t a b).hom) i j (ht₁ i j)))

/-- The underlying morphism of `S`-schemes of
`AlgebraicGeometry.DescentData.fibreGluingOverIso` is
`AlgebraicGeometry.DescentData.fibreGluingHom`. -/
lemma fibreGluingOverIso_hom
    (ht₁ : ∀ i j, (t i j).hom ≫ pullback.fst (f i) ((V j).hom ≫ f j) =
      pullback.fst ((V i).hom ≫ f i) (f j) ≫ (V i).hom) (i j : ι) :
    (fibreGluingOverIso f V t ht₁ i j).hom =
      fibreGluingHom f V (fun a b ↦ (t a b).hom) i j (ht₁ i j) := rfl

/-- **A gluing isomorphism in the product formalism from one on the literal fibre products**,
read as an isomorphism over the pairwise base `X i ×_S X j`, which is the shape the field
`AlgebraicGeometry.DescentData.gluing` asks for. -/
def fibreGluingIso
    (ht₁ : ∀ i j, (t i j).hom ≫ pullback.fst (f i) ((V j).hom ≫ f j) =
      pullback.fst ((V i).hom ≫ f i) (f j) ≫ (V i).hom)
    (ht₂ : ∀ i j, (t i j).hom ≫ pullback.snd (f i) ((V j).hom ≫ f j) ≫ (V j).hom =
      pullback.snd ((V i).hom ≫ f i) (f j)) (i j : ι) :
    Over.mk (prod.map (structureMap (f i) (V i)) (𝟙 (Over.mk (f j)))) ≅
      Over.mk (prod.map (𝟙 (Over.mk (f i))) (structureMap (f j) (V j))) :=
  Over.isoMk (fibreGluingOverIso f V t ht₁ i j) (by
    rw [fibreGluingOverIso_hom f V t ht₁ i j]
    simp only [Over.mk_hom]
    refine prod.hom_ext ?_ ?_
    · rw [Category.assoc, prod.map_fst, Category.comp_id, prod.map_fst]
      exact fibreGluingHom_comp_fst f V (fun a b ↦ (t a b).hom) i j (ht₁ i j)
    · rw [Category.assoc, prod.map_snd, prod.map_snd, Category.comp_id]
      exact fibreGluingHom_comp_snd_structureMap f V (fun a b ↦ (t a b).hom) i j (ht₁ i j)
        (ht₂ i j))

/-- The underlying morphism of `S`-schemes of `AlgebraicGeometry.DescentData.fibreGluingIso`. -/
lemma fibreGluingIso_hom_left
    (ht₁ : ∀ i j, (t i j).hom ≫ pullback.fst (f i) ((V j).hom ≫ f j) =
      pullback.fst ((V i).hom ≫ f i) (f j) ≫ (V i).hom)
    (ht₂ : ∀ i j, (t i j).hom ≫ pullback.snd (f i) ((V j).hom ≫ f j) ≫ (V j).hom =
      pullback.snd ((V i).hom ≫ f i) (f j)) (i j : ι) :
    (fibreGluingIso f V t ht₁ ht₂ i j).hom.left =
      fibreGluingHom f V (fun a b ↦ (t a b).hom) i j (ht₁ i j) := rfl

/-- **A descent datum for a family of morphisms, from gluing data on the literal fibre
products.**  Let `f i : X i ⟶ S` be a family of morphisms of schemes and `V i` a scheme over
each `X i`.  Given isomorphisms

```
t i j : V i ×_S X j ≅ X i ×_S V j
```

over the pairwise bases — that is, carrying the two projections to `X i` and to `X j` to each
other, `ht₁` and `ht₂` — satisfying the cocycle condition in the form `(v · x) · y = v · y` for
generalized points, this is the descent datum relative to `f` with component `V i` at `i` and
those gluing isomorphisms. -/
def ofFibreGluing
    (ht₁ : ∀ i j, (t i j).hom ≫ pullback.fst (f i) ((V j).hom ≫ f j) =
      pullback.fst ((V i).hom ≫ f i) (f j) ≫ (V i).hom)
    (ht₂ : ∀ i j, (t i j).hom ≫ pullback.snd (f i) ((V j).hom ≫ f j) ≫ (V j).hom =
      pullback.snd ((V i).hom ≫ f i) (f j))
    (hcoc : FibreCocycle f V fun i j ↦ (t i j).hom) : DescentData f where
  obj i := V i
  gluing i j := fibreGluingIso f V t ht₁ ht₂ i j
  cocycle i j k := by
    have key := cocycle_of_prodLift_snd f V
      (fun a b ↦ fibreGluingHom f V (fun c d ↦ (t c d).hom) a b (ht₁ a b))
      (fun a b ↦ fibreGluingHom_comp_fst f V (fun c d ↦ (t c d).hom) a b (ht₁ a b))
      (fun a b ↦ fibreGluingHom_comp_snd_structureMap f V (fun c d ↦ (t c d).hom) a b
        (ht₁ a b) (ht₂ a b))
      (by
        intro a b c T w y z
        apply Over.OverMorphism.ext
        rw [left_prodLift_comp_fibreGluingHom_comp_snd f V (fun c d ↦ (t c d).hom) b c
            (ht₁ b c),
          left_prodLift_comp_fibreGluingHom_comp_snd f V (fun c d ↦ (t c d).hom) a c
            (ht₁ a c)]
        refine Eq.trans (fibreAct_congr f V (fun c d ↦ (t c d).hom) b c
          (left_prodLift_comp_fibreGluingHom_comp_snd f V (fun c d ↦ (t c d).hom) a b
            (ht₁ a b) w y) rfl _
          (fibreAct_comp_hom_comp f V (fun c d ↦ (t c d).hom) a b c (ht₂ a b)
            w.left y.left z.left ((Over.w w).trans (Over.w y).symm)
            ((Over.w y).trans (Over.w z).symm))) ?_
        exact hcoc a b c w.left y.left z.left ((Over.w w).trans (Over.w y).symm)
          ((Over.w y).trans (Over.w z).symm) _) i j k
    exact key

/-- The component at `i` of the datum assembled from fibre-product gluing data is the given
scheme over `X i`. -/
lemma ofFibreGluing_obj
    (ht₁ : ∀ i j, (t i j).hom ≫ pullback.fst (f i) ((V j).hom ≫ f j) =
      pullback.fst ((V i).hom ≫ f i) (f j) ≫ (V i).hom)
    (ht₂ : ∀ i j, (t i j).hom ≫ pullback.snd (f i) ((V j).hom ≫ f j) ≫ (V j).hom =
      pullback.snd ((V i).hom ≫ f i) (f j))
    (hcoc : FibreCocycle f V fun i j ↦ (t i j).hom) (i : ι) :
    (ofFibreGluing f V t ht₁ ht₂ hcoc).obj i = V i := rfl

/-- The gluing isomorphism of the datum assembled from fibre-product gluing data is
`AlgebraicGeometry.DescentData.fibreGluingIso`. -/
lemma ofFibreGluing_gluing
    (ht₁ : ∀ i j, (t i j).hom ≫ pullback.fst (f i) ((V j).hom ≫ f j) =
      pullback.fst ((V i).hom ≫ f i) (f j) ≫ (V i).hom)
    (ht₂ : ∀ i j, (t i j).hom ≫ pullback.snd (f i) ((V j).hom ≫ f j) ≫ (V j).hom =
      pullback.snd ((V i).hom ≫ f i) (f j))
    (hcoc : FibreCocycle f V fun i j ↦ (t i j).hom) (i j : ι) :
    (ofFibreGluing f V t ht₁ ht₂ hcoc).gluing i j = fibreGluingIso f V t ht₁ ht₂ i j := rfl

/-- **The gluing isomorphism of the datum assembled from fibre-product gluing data, read on the
literal fibre products, is the given one.**  This is what makes the datum usable in the
formalism of `AlgebraicGeometry.DescentData.gluingPullbackIso`, which the effectivity and
canonical-datum machinery is phrased in. -/
lemma ofFibreGluing_gluingPullbackIso_hom
    (ht₁ : ∀ i j, (t i j).hom ≫ pullback.fst (f i) ((V j).hom ≫ f j) =
      pullback.fst ((V i).hom ≫ f i) (f j) ≫ (V i).hom)
    (ht₂ : ∀ i j, (t i j).hom ≫ pullback.snd (f i) ((V j).hom ≫ f j) ≫ (V j).hom =
      pullback.snd ((V i).hom ≫ f i) (f j))
    (hcoc : FibreCocycle f V fun i j ↦ (t i j).hom) (i j : ι) :
    ((ofFibreGluing f V t ht₁ ht₂ hcoc).gluingPullbackIso i j).hom = (t i j).hom := by
  have h : ((ofFibreGluing f V t ht₁ ht₂ hcoc).gluingPullbackIso i j).hom =
      (Over.prodLeftIsoPullback ((Over.map (f i)).obj (V i)) (Over.mk (f j))).inv ≫
        ((Over.prodLeftIsoPullback ((Over.map (f i)).obj (V i)) (Over.mk (f j))).hom ≫
            (t i j).hom ≫
            (Over.prodLeftIsoPullback (Over.mk (f i))
              ((Over.map (f j)).obj (V j))).inv) ≫
          (Over.prodLeftIsoPullback (Over.mk (f i)) ((Over.map (f j)).obj (V j))).hom := rfl
  rw [h, Category.assoc, Iso.inv_hom_id_assoc, Category.assoc, Iso.inv_hom_id,
    Category.comp_id]

end Constructor

end AlgebraicGeometry.DescentData

end
