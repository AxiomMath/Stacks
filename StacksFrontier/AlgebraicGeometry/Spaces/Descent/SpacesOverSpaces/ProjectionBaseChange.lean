module

public import Mathlib.CategoryTheory.Limits.Constructions.Over.Basic
public import Mathlib.CategoryTheory.Limits.Constructions.Over.Products
public import Mathlib.CategoryTheory.Limits.Shapes.Pullback.IsPullback.Basic
public import StacksCore.Tactic.StacksAttribute
public import StacksFrontier.AlgebraicGeometry.Spaces.FormallySmooth.Descent
public import StacksFrontier.AlgebraicGeometry.Spaces.Representable.Bootstrap.Stability

/-!
# Descent data read as maps between the base changes along the two projections

Let `Y ⟶ X` be a morphism of algebraic spaces and let `V ⟶ Y` be an algebraic space over `Y`.
The pairwise fibre product `V ×_X Y` is the base change of `V` along the first projection
`pr₀ : Y ×_X Y ⟶ Y`, and `Y ×_X V` is the base change of `V` along the second projection
`pr₁ : Y ×_X Y ⟶ Y`. Consequently the gluing isomorphism `φ : V ×_X Y ≅ Y ×_X V` of a descent
datum relative to `Y ⟶ X` is the same thing as an isomorphism `pr₀^* V ≅ pr₁^* V` of algebraic
spaces over `Y ×_X Y`.

## Main definitions

* `CategoryTheory.Limits.prodMapIdIsoPullbackFst` identifies `W ×_T B` over `A ×_T B` with the
  base change of `W ⟶ A` along the first projection, and
  `CategoryTheory.Limits.idProdMapIsoPullbackSnd` identifies `A ×_T W` with the base change
  along the second projection; `CategoryTheory.Limits.prodFstFstIsoPullback` and
  `CategoryTheory.Limits.prodFstSndIsoPullback` are the analogues on a triple product.
* `AlgebraicGeometry.Space.Descent.gluingProjEquiv` is the resulting bijection between the two
  presentations of a gluing isomorphism.
* `AlgebraicGeometry.Space.Descent.DescentData.projGluing` is the gluing isomorphism of a
  descent datum read as an isomorphism `pr₀^* V_i ≅ pr₁^* V_j` over `X i ×_T X j`, and
  `AlgebraicGeometry.Space.Descent.DescentData.projGluing01`,
  `AlgebraicGeometry.Space.Descent.DescentData.projGluing12` and
  `AlgebraicGeometry.Space.Descent.DescentData.projGluing02` are its base changes to the triple
  fibre product.

## Main results

* `CategoryTheory.Limits.IsPullback.of_prod_fst_fst` and
  `CategoryTheory.Limits.IsPullback.of_prod_fst_snd` are the cartesian squares exhibiting the
  two factors of a triple product as base changes along the projections.
* `AlgebraicGeometry.Space.Descent.DescentData.gluing_eq_projGluing_symm` recovers the gluing
  isomorphism from its projection form, so the two presentations carry the same data.
* `AlgebraicGeometry.Space.Descent.DescentData.projGluing01_comp_projGluing12` is the cocycle
  condition in the form `pr₀₂^* φ_ik = pr₁₂^* φ_jk ∘ pr₀₁^* φ_ij`.

## Implementation notes

Fibre products over the common target `T` are binary products in `Over T`, so the base change
of `W ⟶ A` along `pr₀ : A ⨯ B ⟶ A` is the pullback `pullback (prod.fst) (W ⟶ A)` taken in
`Over T`, viewed as an object of `Over (A ⨯ B)` through its first projection. As in the
definition of a descent datum, no algebraicity hypothesis is imposed on these fibre products
themselves. The triple fibre product is the left-associated product `(A ⨯ B) ⨯ E`, and the
three base-changed gluing maps are obtained by conjugating the product-form maps
`prod.map · (𝟙 _)`, `CategoryTheory.Limits.prodMapLastTwo` and
`CategoryTheory.Limits.prodMapFirstThird` with those identifications.

## References

* [Stacks Project, Tag 0ADH](https://stacks.math.columbia.edu/tag/0ADH)
-/

@[expose] public section

noncomputable section

open CategoryTheory CategoryTheory.Limits

universe v u

namespace CategoryTheory.Limits

variable {C : Type u} [Category.{v} C] [HasBinaryProducts C]

section BaseChange

variable [HasPullbacks C] {W A B : C}

/-- The fibre product `W ×_T B`, viewed over `A ×_T B`, is the base change of `g : W ⟶ A`
along the first projection `A ×_T B ⟶ A`. -/
def prodMapIdIsoPullbackFst (g : W ⟶ A) (B : C) :
    Over.mk (prod.map g (𝟙 B)) ≅
      Over.mk (pullback.fst (prod.fst : A ⨯ B ⟶ A) g) :=
  Over.isoMk (IsPullback.of_prod_fst_with_id g B).flip.isoPullback (by simp)

/-- The fibre product `A ×_T W`, viewed over `A ×_T B`, is the base change of `g : W ⟶ B`
along the second projection `A ×_T B ⟶ B`. -/
def idProdMapIsoPullbackSnd (A : C) (g : W ⟶ B) :
    Over.mk (prod.map (𝟙 A) g) ≅
      Over.mk (pullback.fst (prod.snd : A ⨯ B ⟶ B) g) :=
  Over.isoMk (CategoryTheory.IsPullback.of_prod_snd_with_id g A).flip.isoPullback (by simp)

/-- The identification `prodMapIdIsoPullbackFst` followed by the second pullback projection
is the first product projection `W ⨯ B ⟶ W`. -/
@[reassoc (attr := simp)]
lemma prodMapIdIsoPullbackFst_hom_left_snd (g : W ⟶ A) (B : C) :
    (prodMapIdIsoPullbackFst g B).hom.left ≫ pullback.snd _ _ = (prod.fst : W ⨯ B ⟶ W) :=
  IsPullback.isoPullback_hom_snd _

/-- The inverse of `prodMapIdIsoPullbackFst` followed by the first product projection
`W ⨯ B ⟶ W` is the second pullback projection. -/
@[reassoc (attr := simp)]
lemma prodMapIdIsoPullbackFst_inv_left_fst (g : W ⟶ A) (B : C) :
    (prodMapIdIsoPullbackFst g B).inv.left ≫ (prod.fst : W ⨯ B ⟶ W) = pullback.snd _ _ :=
  IsPullback.isoPullback_inv_snd _

/-- The identification `idProdMapIsoPullbackSnd` followed by the second pullback projection
is the second product projection `A ⨯ W ⟶ W`. -/
@[reassoc (attr := simp)]
lemma idProdMapIsoPullbackSnd_hom_left_snd (A : C) (g : W ⟶ B) :
    (idProdMapIsoPullbackSnd A g).hom.left ≫ pullback.snd _ _ = (prod.snd : A ⨯ W ⟶ W) :=
  IsPullback.isoPullback_hom_snd _

/-- The inverse of `idProdMapIsoPullbackSnd` followed by the second product projection
`A ⨯ W ⟶ W` is the second pullback projection. -/
@[reassoc (attr := simp)]
lemma idProdMapIsoPullbackSnd_inv_left_snd (A : C) (g : W ⟶ B) :
    (idProdMapIsoPullbackSnd A g).inv.left ≫ (prod.snd : A ⨯ W ⟶ W) = pullback.snd _ _ :=
  IsPullback.isoPullback_inv_snd _

/-- Over `A ×_T B`, an isomorphism `W ×_T B ≅ A ×_T W'` is the same thing as an isomorphism
between the base change of `W` along the first projection and the base change of `W'` along
the second projection. -/
def prodGluingEquivPullbackGluing {W' : C} (g : W ⟶ A) (g' : W' ⟶ B) :
    (Over.mk (prod.map g (𝟙 B)) ≅ Over.mk (prod.map (𝟙 A) g')) ≃
      (Over.mk (pullback.fst (prod.fst : A ⨯ B ⟶ A) g) ≅
        Over.mk (pullback.fst (prod.snd : A ⨯ B ⟶ B) g')) where
  toFun e := (prodMapIdIsoPullbackFst g B).symm ≪≫ e ≪≫ idProdMapIsoPullbackSnd A g'
  invFun e := prodMapIdIsoPullbackFst g B ≪≫ e ≪≫ (idProdMapIsoPullbackSnd A g').symm
  left_inv e := by apply Iso.ext; simp
  right_inv e := by apply Iso.ext; simp

end BaseChange

section TripleBaseChange

/-- Applying the identity of `B ⨯ E` to the last two factors of `(A ⨯ B) ⨯ E` gives the
identity. -/
@[simp]
lemma prodMapLastTwo_id (A B E : C) :
    prodMapLastTwo (A := A) (𝟙 (B ⨯ E)) = 𝟙 ((A ⨯ B) ⨯ E) := by
  apply prod.hom_ext
  · apply prod.hom_ext <;> simp [prodMapLastTwo]
  · simp [prodMapLastTwo]

/-- Applying the identity of `A ⨯ E` to the first and third factors of `(A ⨯ B) ⨯ E` gives the
identity. -/
@[simp]
lemma prodMapFirstThird_id (A B E : C) :
    prodMapFirstThird (B := B) (𝟙 (A ⨯ E)) = 𝟙 ((A ⨯ B) ⨯ E) := by
  apply prod.hom_ext
  · apply prod.hom_ext <;> simp [prodMapFirstThird, prodMapLastTwo]
  · simp [prodMapFirstThird, prodMapLastTwo]

/-- `(W ×_T B) ×_T E` is the base change of `g : W ⟶ A` along the projection
`(A ×_T B) ×_T E ⟶ A` onto the first factor. -/
lemma IsPullback.of_prod_fst_fst {W A : C} (g : W ⟶ A) (B E : C) :
    IsPullback (prod.fst ≫ prod.fst : (W ⨯ B) ⨯ E ⟶ W)
      (prod.map (prod.map g (𝟙 B)) (𝟙 E)) g
      (prod.fst ≫ prod.fst : (A ⨯ B) ⨯ E ⟶ A) :=
  (IsPullback.of_prod_fst_with_id (prod.map g (𝟙 B)) E).paste_horiz
    (IsPullback.of_prod_fst_with_id g B)

/-- `(A ×_T W) ×_T E` is the base change of `g : W ⟶ B` along the projection
`(A ×_T B) ×_T E ⟶ B` onto the second factor. -/
lemma IsPullback.of_prod_fst_snd {W B : C} (A : C) (g : W ⟶ B) (E : C) :
    IsPullback (prod.fst ≫ prod.snd : (A ⨯ W) ⨯ E ⟶ W)
      (prod.map (prod.map (𝟙 A) g) (𝟙 E)) g
      (prod.fst ≫ prod.snd : (A ⨯ B) ⨯ E ⟶ B) :=
  (IsPullback.of_prod_fst_with_id (prod.map (𝟙 A) g) E).paste_horiz
    (CategoryTheory.IsPullback.of_prod_snd_with_id g A)

variable [HasPullbacks C]

/-- Over `(A ×_T B) ×_T E`, the fibre product `(W ×_T B) ×_T E` is the base change of
`g : W ⟶ A` along the projection onto the first factor. -/
def prodFstFstIsoPullback {W A : C} (g : W ⟶ A) (B E : C) :
    Over.mk (prod.map (prod.map g (𝟙 B)) (𝟙 E)) ≅
      Over.mk (pullback.fst (prod.fst ≫ prod.fst : (A ⨯ B) ⨯ E ⟶ A) g) :=
  Over.isoMk (IsPullback.of_prod_fst_fst g B E).flip.isoPullback (by simp)

/-- Over `(A ×_T B) ×_T E`, the fibre product `(A ×_T W) ×_T E` is the base change of
`g : W ⟶ B` along the projection onto the second factor. -/
def prodFstSndIsoPullback {W B : C} (A : C) (g : W ⟶ B) (E : C) :
    Over.mk (prod.map (prod.map (𝟙 A) g) (𝟙 E)) ≅
      Over.mk (pullback.fst (prod.fst ≫ prod.snd : (A ⨯ B) ⨯ E ⟶ B) g) :=
  Over.isoMk (IsPullback.of_prod_fst_snd A g E).flip.isoPullback (by simp)

end TripleBaseChange

end CategoryTheory.Limits

namespace AlgebraicGeometry.Space.Descent

variable {B : BigFppfSite.{u}} {S : Scheme.{u}} {hS : B.Contains S}

variable {ι : Type v} {X : ι → (BigFppfOver B S hS)ᵒᵖ ⥤ Type u}
    {T : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u} (f : ∀ i, X i ⟶ T)

/-- The base change of an algebraic space `V` over `X i` along the first projection
`X i ×_T X j ⟶ X i`, viewed as an algebraic space over `X i ×_T X j`. -/
abbrev projFstObj (i j : ι) (V : Over (X i)) :
    Over (Over.mk (f i) ⨯ Over.mk (f j)) :=
  Over.mk (pullback.fst (prod.fst : Over.mk (f i) ⨯ Over.mk (f j) ⟶ Over.mk (f i))
    (structureMap (f i) V))

/-- The base change of an algebraic space `V` over `X j` along the second projection
`X i ×_T X j ⟶ X j`, viewed as an algebraic space over `X i ×_T X j`. -/
abbrev projSndObj (i j : ι) (V : Over (X j)) :
    Over (Over.mk (f i) ⨯ Over.mk (f j)) :=
  Over.mk (pullback.fst (prod.snd : Over.mk (f i) ⨯ Over.mk (f j) ⟶ Over.mk (f j))
    (structureMap (f j) V))

/-- Over the pairwise fibre product `X i ×_T X j`, an isomorphism `V_i ×_T X_j ≅ X_i ×_T V_j`
is the same thing as an isomorphism `pr₀^* V_i ≅ pr₁^* V_j` of the two base changes along the
projections. -/
@[stacks 0ADH "the two presentations of the gluing isomorphism of a descent datum"]
def gluingProjEquiv (i j : ι) (Vi : Over (X i)) (Vj : Over (X j)) :
    (Over.mk (prod.map (structureMap (f i) Vi) (𝟙 (Over.mk (f j)))) ≅
        Over.mk (prod.map (𝟙 (Over.mk (f i))) (structureMap (f j) Vj))) ≃
      (projFstObj f i j Vi ≅ projSndObj f i j Vj) :=
  prodGluingEquivPullbackGluing _ _

/-- The base change of an algebraic space `V` over `X i` along the projection
`(X i ×_T X j) ×_T X k ⟶ X i`. -/
abbrev projTripleFstObj (i j k : ι) (V : Over (X i)) :
    Over ((Over.mk (f i) ⨯ Over.mk (f j)) ⨯ Over.mk (f k)) :=
  Over.mk (pullback.fst (prod.fst ≫ prod.fst :
    (Over.mk (f i) ⨯ Over.mk (f j)) ⨯ Over.mk (f k) ⟶ Over.mk (f i)) (structureMap (f i) V))

/-- The base change of an algebraic space `V` over `X j` along the projection
`(X i ×_T X j) ×_T X k ⟶ X j`. -/
abbrev projTripleSndObj (i j k : ι) (V : Over (X j)) :
    Over ((Over.mk (f i) ⨯ Over.mk (f j)) ⨯ Over.mk (f k)) :=
  Over.mk (pullback.fst (prod.fst ≫ prod.snd :
    (Over.mk (f i) ⨯ Over.mk (f j)) ⨯ Over.mk (f k) ⟶ Over.mk (f j)) (structureMap (f j) V))

/-- The base change of an algebraic space `V` over `X k` along the projection
`(X i ×_T X j) ×_T X k ⟶ X k`. -/
abbrev projTripleTrdObj (i j k : ι) (V : Over (X k)) :
    Over ((Over.mk (f i) ⨯ Over.mk (f j)) ⨯ Over.mk (f k)) :=
  Over.mk (pullback.fst (prod.snd :
    (Over.mk (f i) ⨯ Over.mk (f j)) ⨯ Over.mk (f k) ⟶ Over.mk (f k)) (structureMap (f k) V))

namespace DescentData

variable {f} {hT : IsAlgebraicSpace B S hS T} {hX : ∀ i, IsAlgebraicSpace B S hS (X i)}

/-- The gluing isomorphism of a descent datum, read as an isomorphism `pr₀^* V_i ≅ pr₁^* V_j`
of algebraic spaces over the pairwise fibre product `X i ×_T X j`. -/
@[stacks 0ADH "the gluing isomorphism read as a map pr₀^* V ⟶ pr₁^* V"]
def projGluing (D : DescentData f hT hX) (i j : ι) :
    projFstObj f i j (D.obj i) ≅ projSndObj f i j (D.obj j) :=
  gluingProjEquiv f i j (D.obj i) (D.obj j) (D.gluing i j)

/-- The underlying map of the projection form of the gluing isomorphism. -/
lemma projGluing_hom_left (D : DescentData f hT hX) (i j : ι) :
    (D.projGluing i j).hom.left =
      (prodMapIdIsoPullbackFst (structureMap (f i) (D.obj i)) (Over.mk (f j))).inv.left ≫
        (D.gluing i j).hom.left ≫
          (idProdMapIsoPullbackSnd (Over.mk (f i)) (structureMap (f j) (D.obj j))).hom.left :=
  rfl

/-- The projection form of the gluing isomorphism lies over the pairwise fibre product. -/
@[reassoc (attr := simp)]
lemma projGluing_hom_left_fst (D : DescentData f hT hX) (i j : ι) :
    (D.projGluing i j).hom.left ≫ pullback.fst _ _ = pullback.fst _ _ :=
  Over.w (D.projGluing i j).hom

/-- The gluing isomorphism of a descent datum is recovered from its projection form. -/
lemma gluing_eq_projGluing_symm (D : DescentData f hT hX) (i j : ι) :
    (gluingProjEquiv f i j (D.obj i) (D.obj j)).symm (D.projGluing i j) = D.gluing i j :=
  (gluingProjEquiv f i j (D.obj i) (D.obj j)).symm_apply_apply _

/-- The gluing isomorphism is a map over the pairwise fibre product. -/
lemma gluing_hom_left_comp (D : DescentData f hT hX) (i j : ι) :
    (D.gluing i j).hom.left ≫
        prod.map (𝟙 (Over.mk (f i))) (structureMap (f j) (D.obj j)) =
      prod.map (structureMap (f i) (D.obj i)) (𝟙 (Over.mk (f j))) :=
  Over.w (D.gluing i j).hom

/-- Applying `φ_ij` to the first two factors of a triple fibre product is a map over that
triple fibre product. -/
lemma gluing_prodMapId_comp (D : DescentData f hT hX) (i j k : ι) :
    prod.map (D.gluing i j).hom.left (𝟙 (Over.mk (f k))) ≫
        prod.map (prod.map (𝟙 (Over.mk (f i))) (structureMap (f j) (D.obj j)))
          (𝟙 (Over.mk (f k))) =
      prod.map (prod.map (structureMap (f i) (D.obj i)) (𝟙 (Over.mk (f j))))
        (𝟙 (Over.mk (f k))) := by
  rw [prod.map_map, Category.comp_id, D.gluing_hom_left_comp i j]

/-- Applying `φ_jk` to the last two factors of a triple fibre product is a map over that
triple fibre product. -/
lemma gluing_prodMapLastTwo_comp (D : DescentData f hT hX) (i j k : ι) :
    prodMapLastTwo (A := Over.mk (f i)) (D.gluing j k).hom.left ≫
        prod.map (𝟙 (Over.mk (f i) ⨯ Over.mk (f j))) (structureMap (f k) (D.obj k)) =
      prod.map (prod.map (𝟙 (Over.mk (f i))) (structureMap (f j) (D.obj j)))
        (𝟙 (Over.mk (f k))) := by
  simpa using (prodMapLastTwo_naturality (𝟙 (Over.mk (f i))) (structureMap (f j) (D.obj j))
    (𝟙 (Over.mk (f k))) (𝟙 (Over.mk (f j))) (structureMap (f k) (D.obj k))
    (D.gluing j k).hom.left (𝟙 (Over.mk (f j) ⨯ Over.mk (f k)))
    (by simpa using (D.gluing_hom_left_comp j k).symm)).symm

/-- Applying `φ_ik` to the first and last factors of a triple fibre product is a map over that
triple fibre product. -/
lemma gluing_prodMapFirstThird_comp (D : DescentData f hT hX) (i j k : ι) :
    prodMapFirstThird (B := Over.mk (f j)) (D.gluing i k).hom.left ≫
        prod.map (𝟙 (Over.mk (f i) ⨯ Over.mk (f j))) (structureMap (f k) (D.obj k)) =
      prod.map (prod.map (structureMap (f i) (D.obj i)) (𝟙 (Over.mk (f j))))
        (𝟙 (Over.mk (f k))) := by
  simpa only [prodMapFirstThird_id, Category.comp_id, prod.map_id_id] using
    (prodMapFirstThird_naturality (structureMap (f i) (D.obj i)) (𝟙 (Over.mk (f j)))
    (𝟙 (Over.mk (f k))) (𝟙 (Over.mk (f i))) (structureMap (f k) (D.obj k))
    (D.gluing i k).hom.left (𝟙 (Over.mk (f i) ⨯ Over.mk (f k)))
    (by rw [Category.comp_id]; exact (D.gluing_hom_left_comp i k).symm)).symm

/-- The gluing isomorphism `φ_ij` pulled back to the triple fibre product along `pr₀₁`,
in product form. -/
def gluingTriple01 (D : DescentData f hT hX) (i j k : ι) :
    Over.mk (prod.map (prod.map (structureMap (f i) (D.obj i)) (𝟙 (Over.mk (f j))))
        (𝟙 (Over.mk (f k)))) ⟶
      Over.mk (prod.map (prod.map (𝟙 (Over.mk (f i))) (structureMap (f j) (D.obj j)))
        (𝟙 (Over.mk (f k)))) :=
  Over.homMk (prod.map (D.gluing i j).hom.left (𝟙 (Over.mk (f k))))
    (D.gluing_prodMapId_comp i j k)

/-- The gluing isomorphism `φ_jk` pulled back to the triple fibre product along `pr₁₂`,
in product form. -/
def gluingTriple12 (D : DescentData f hT hX) (i j k : ι) :
    Over.mk (prod.map (prod.map (𝟙 (Over.mk (f i))) (structureMap (f j) (D.obj j)))
        (𝟙 (Over.mk (f k)))) ⟶
      Over.mk (prod.map (𝟙 (Over.mk (f i) ⨯ Over.mk (f j))) (structureMap (f k) (D.obj k))) :=
  Over.homMk (prodMapLastTwo (D.gluing j k).hom.left)
    (D.gluing_prodMapLastTwo_comp i j k)

/-- The gluing isomorphism `φ_ik` pulled back to the triple fibre product along `pr₀₂`,
in product form. -/
def gluingTriple02 (D : DescentData f hT hX) (i j k : ι) :
    Over.mk (prod.map (prod.map (structureMap (f i) (D.obj i)) (𝟙 (Over.mk (f j))))
        (𝟙 (Over.mk (f k)))) ⟶
      Over.mk (prod.map (𝟙 (Over.mk (f i) ⨯ Over.mk (f j))) (structureMap (f k) (D.obj k))) :=
  Over.homMk (prodMapFirstThird (D.gluing i k).hom.left)
    (D.gluing_prodMapFirstThird_comp i j k)

/-- The cocycle condition, in product form on the triple fibre product. -/
lemma gluingTriple01_comp_gluingTriple12 (D : DescentData f hT hX) (i j k : ι) :
    D.gluingTriple01 i j k ≫ D.gluingTriple12 i j k = D.gluingTriple02 i j k :=
  Over.OverMorphism.ext (D.cocycle i j k)

/-- The gluing isomorphism `φ_ij` read as a map `pr₀^* V_i ⟶ pr₁^* V_j` of base changes to
the triple fibre product. -/
def projGluing01 (D : DescentData f hT hX) (i j k : ι) :
    projTripleFstObj f i j k (D.obj i) ⟶ projTripleSndObj f i j k (D.obj j) :=
  (prodFstFstIsoPullback (structureMap (f i) (D.obj i)) (Over.mk (f j)) (Over.mk (f k))).inv ≫
    D.gluingTriple01 i j k ≫
      (prodFstSndIsoPullback (Over.mk (f i)) (structureMap (f j) (D.obj j))
        (Over.mk (f k))).hom

/-- The gluing isomorphism `φ_jk` read as a map `pr₁^* V_j ⟶ pr₂^* V_k` of base changes to
the triple fibre product. -/
def projGluing12 (D : DescentData f hT hX) (i j k : ι) :
    projTripleSndObj f i j k (D.obj j) ⟶ projTripleTrdObj f i j k (D.obj k) :=
  (prodFstSndIsoPullback (Over.mk (f i)) (structureMap (f j) (D.obj j)) (Over.mk (f k))).inv ≫
    D.gluingTriple12 i j k ≫
      (idProdMapIsoPullbackSnd (Over.mk (f i) ⨯ Over.mk (f j))
        (structureMap (f k) (D.obj k))).hom

/-- The gluing isomorphism `φ_ik` read as a map `pr₀^* V_i ⟶ pr₂^* V_k` of base changes to
the triple fibre product. -/
def projGluing02 (D : DescentData f hT hX) (i j k : ι) :
    projTripleFstObj f i j k (D.obj i) ⟶ projTripleTrdObj f i j k (D.obj k) :=
  (prodFstFstIsoPullback (structureMap (f i) (D.obj i)) (Over.mk (f j)) (Over.mk (f k))).inv ≫
    D.gluingTriple02 i j k ≫
      (idProdMapIsoPullbackSnd (Over.mk (f i) ⨯ Over.mk (f j))
        (structureMap (f k) (D.obj k))).hom

/-- The cocycle condition of a descent datum, read on base changes along the projections of
the triple fibre product: `pr₀₂^* φ_ik = pr₁₂^* φ_jk ∘ pr₀₁^* φ_ij`. -/
@[stacks 0ADH "the cocycle condition in the form pr₀₂^* φ = pr₁₂^* φ ∘ pr₀₁^* φ"]
theorem projGluing01_comp_projGluing12 (D : DescentData f hT hX) (i j k : ι) :
    D.projGluing01 i j k ≫ D.projGluing12 i j k = D.projGluing02 i j k := by
  rw [projGluing01, projGluing12, projGluing02,
    ← D.gluingTriple01_comp_gluingTriple12 i j k]
  simp

end DescentData

end AlgebraicGeometry.Space.Descent

end
