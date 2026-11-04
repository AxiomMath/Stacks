module

public import Mathlib.AlgebraicGeometry.Limits
public import Mathlib.CategoryTheory.Limits.Constructions.Over.Products
public import StacksCore.Tactic.StacksAttribute

/-!
# Descent data for a family of morphisms of schemes

For a family of morphisms of schemes `f i : X i ⟶ S` with common target, a descent datum
consists of a scheme over each `X i`, an isomorphism over each pairwise fibre product
`X i ×_S X j` between the two ways of pulling those schemes back, and the cocycle condition
on each triple fibre product. A morphism of descent data is a family of morphisms over the
`X i` commuting with the gluing isomorphisms.

## Main definitions

* `AlgebraicGeometry.structureMap` views the structure morphism of an `X`-scheme as a
  morphism of `S`-schemes.
* `AlgebraicGeometry.DescentData` is a descent datum for a family of morphisms of schemes.
* `AlgebraicGeometry.DescentData.Hom` is a morphism of descent data; descent data for a
  fixed family form a category.
* `AlgebraicGeometry.DescentData.evaluation` evaluates a descent datum at one member of the
  family.
* `CategoryTheory.Limits.prodMapLastTwo` and `CategoryTheory.Limits.prodMapFirstThird`
  apply a map to two of the three factors of a left-associated triple product.

## Main results

* `AlgebraicGeometry.DescentData.gluing_hom_fst` and
  `AlgebraicGeometry.DescentData.gluing_hom_snd_structureMap` say that a gluing isomorphism
  preserves the pairwise base.
* `CategoryTheory.Limits.prodMapLastTwo_naturality` and
  `CategoryTheory.Limits.prodMapFirstThird_naturality` are the naturality squares for those
  two product maps.

## Implementation notes

Products are taken in `Over S`: the canonical isomorphism
`CategoryTheory.Over.prodLeftIsoPullback` identifies their underlying schemes with fibre
products over `S`, compatibly with both projections. Thus `gluing` is an isomorphism over
`X i ×_S X j`, not merely over `S`. Its underlying map is available as `gluingIso`, and
`gluingPullbackIso` transports it to the source's literal fibre products. The two ways
around the triangle on a triple product are expressed using product associativity and
symmetry, with `prodMapLastTwo` and `prodMapFirstThird` inserting the unchanged factor. No
diagonal identity or extra naturality condition is imposed.

The component `obj i : Over (X i)` exposes the scheme as `(obj i).left` and its structure
map as `(obj i).hom`. The category instance, componentwise extensionality and the evaluation
functors let equivalences, pullback functors and their faithfulness be stated directly.

## References

* [Stacks Project, Tag 023W](https://stacks.math.columbia.edu/tag/023W)
-/

@[expose] public section

noncomputable section

universe u v

namespace CategoryTheory.Limits

section Products

variable {C : Type*} [Category C] [HasBinaryProducts C]

/-- Apply a map to the last two factors of a left-associated triple product. -/
abbrev prodMapLastTwo {A B C' D E : C} (φ : B ⨯ C' ⟶ D ⨯ E) :
    (A ⨯ B) ⨯ C' ⟶ (A ⨯ D) ⨯ E :=
  (prod.associator A B C').hom ≫ prod.map (𝟙 A) φ ≫ (prod.associator A D E).inv

/-- Apply a map to the first and third factors, leaving the middle factor unchanged. -/
abbrev prodMapFirstThird {A B C' D E : C} (φ : A ⨯ C' ⟶ D ⨯ E) :
    (A ⨯ B) ⨯ C' ⟶ (D ⨯ B) ⨯ E :=
  prodMapLastTwo (prod.braiding B C').hom ≫ prod.map φ (𝟙 B) ≫
    prodMapLastTwo (prod.braiding E B).hom

end Products

section ProductNaturality

variable {C : Type*} [Category C] [HasBinaryProducts C]
variable {A B C₀ D E A' B' C' D' E' : C}

/-- Naturality of `prodMapLastTwo` in all five factors. -/
lemma prodMapLastTwo_naturality
    (a : A ⟶ A') (b : B ⟶ B') (c : C₀ ⟶ C')
    (d : D ⟶ D') (e : E ⟶ E') (φ : B ⨯ C₀ ⟶ D ⨯ E)
    (ψ : B' ⨯ C' ⟶ D' ⨯ E')
    (h : prod.map b c ≫ ψ = φ ≫ prod.map d e) :
    prod.map (prod.map a b) c ≫ prodMapLastTwo ψ =
      prodMapLastTwo φ ≫ prod.map (prod.map a d) e := by
  have hn : prod.map a (prod.map d e) ≫ (prod.associator A' D' E').inv =
      (prod.associator A D E).inv ≫ prod.map (prod.map a d) e := by
    apply prod.hom_ext
    · apply prod.hom_ext <;> simp
    · simp
  dsimp only [prodMapLastTwo]
  rw [prod.associator_naturality_assoc]
  rw [← Category.assoc (prod.map a _) (prod.map (𝟙 A') ψ), prod.map_map]
  simp only [Category.comp_id]
  rw [h]
  rw [show prod.map a (φ ≫ prod.map d e) =
    prod.map (𝟙 A) φ ≫ prod.map a (prod.map d e) by simp]
  simp only [Category.assoc]
  rw [hn]

/-- Naturality of `prodMapFirstThird` in all five factors. -/
lemma prodMapFirstThird_naturality
    (a : A ⟶ A') (b : B ⟶ B') (c : C₀ ⟶ C')
    (d : D ⟶ D') (e : E ⟶ E') (φ : A ⨯ C₀ ⟶ D ⨯ E)
    (ψ : A' ⨯ C' ⟶ D' ⨯ E')
    (h : prod.map a c ≫ ψ = φ ≫ prod.map d e) :
    prod.map (prod.map a b) c ≫ prodMapFirstThird ψ =
      prodMapFirstThird φ ≫ prod.map (prod.map d b) e := by
  have h' := congrArg (fun t ↦ (prod.lift (prod.fst ≫ prod.fst) prod.snd :
    (A ⨯ B) ⨯ C₀ ⟶ A ⨯ C₀) ≫ t) h
  apply prod.hom_ext
  · apply prod.hom_ext
    · simpa [prodMapFirstThird, prodMapLastTwo, prod.comp_lift, prod.comp_lift_assoc,
        ← prod.lift_fst_comp_snd_comp] using congrArg (· ≫ prod.fst) h'
    · simp [prodMapFirstThird, prodMapLastTwo, prod.comp_lift, prod.comp_lift_assoc,
        ← prod.lift_fst_comp_snd_comp]
  · simpa [prodMapFirstThird, prodMapLastTwo, prod.comp_lift, prod.comp_lift_assoc,
      ← prod.lift_fst_comp_snd_comp] using congrArg (· ≫ prod.snd) h'

end ProductNaturality

end CategoryTheory.Limits

namespace AlgebraicGeometry

open CategoryTheory Limits

variable {ι : Type v} {S : Scheme.{u}} {X : ι → Scheme.{u}} (f : ∀ i, X i ⟶ S)

/-- The structure map of an `X`-scheme, viewed as a map of `S`-schemes. -/
abbrev structureMap {X S : Scheme.{u}} (f : X ⟶ S) (V : Over X) :
    (Over.map f).obj V ⟶ Over.mk f :=
  Over.homMk V.hom

/-- Descent data for schemes relative to a family of morphisms with common target. -/
@[stacks 023W "(1) descent data",
  stacks 02VQ "the gluing isomorphisms read over the pairwise fibre product, with the cocycle",
  stacks 02VP "remark reading the gluing isomorphism as pr_0^*V → pr_1^*V over X ×_S X",
  sga "3 IV 2.1" "descent datum"]
structure DescentData where
  /-- The scheme over each member of the family. -/
  obj (i : ι) : Over (X i)
  /-- The gluing isomorphism, as an isomorphism over the pairwise fibre product. -/
  gluing (i j : ι) :
    Over.mk (prod.map (structureMap (f i) (obj i)) (𝟙 (Over.mk (f j)))) ≅
      Over.mk (prod.map (𝟙 (Over.mk (f i))) (structureMap (f j) (obj j)))
  /-- Commutativity of the triangle over each triple fibre product. -/
  cocycle (i j k : ι) :
    prod.map (gluing i j).hom.left (𝟙 (Over.mk (f k))) ≫
        prodMapLastTwo (gluing j k).hom.left =
      prodMapFirstThird (gluing i k).hom.left

namespace DescentData

variable {f}

/-- The gluing isomorphism viewed as an isomorphism of `S`-schemes. -/
abbrev gluingIso (D : DescentData f) (i j : ι) :
    (Over.map (f i)).obj (D.obj i) ⨯ Over.mk (f j) ≅
      Over.mk (f i) ⨯ (Over.map (f j)).obj (D.obj j) :=
  (Over.forget _).mapIso (D.gluing i j)

/-- The gluing map preserves the first component of the pairwise base. -/
@[reassoc (attr := simp)]
lemma gluing_hom_fst (D : DescentData f) (i j : ι) :
    (D.gluing i j).hom.left ≫ prod.fst =
      prod.fst ≫ structureMap (f i) (D.obj i) := by
  simpa using congrArg (fun g ↦ g ≫ prod.fst) (Over.w (D.gluing i j).hom)

/-- The gluing map preserves the second component of the pairwise base. -/
@[reassoc (attr := simp)]
lemma gluing_hom_snd_structureMap (D : DescentData f) (i j : ι) :
    (D.gluing i j).hom.left ≫ prod.snd ≫ structureMap (f j) (D.obj j) = prod.snd := by
  simpa using congrArg (fun g ↦ g ≫ prod.snd) (Over.w (D.gluing i j).hom)

/-- The gluing isomorphism on the literal scheme fibre products `V_i ×_S X_j`
and `X_i ×_S V_j`. -/
abbrev gluingPullbackIso (D : DescentData f) (i j : ι) :
    pullback ((D.obj i).hom ≫ f i) (f j) ≅
      pullback (f i) ((D.obj j).hom ≫ f j) :=
  (Over.prodLeftIsoPullback ((Over.map (f i)).obj (D.obj i)) (Over.mk (f j))).symm ≪≫
    (Over.forget S).mapIso (D.gluingIso i j) ≪≫
    Over.prodLeftIsoPullback (Over.mk (f i)) ((Over.map (f j)).obj (D.obj j))

/-- A morphism of descent data is a family of maps over the family members,
compatible with the gluing isomorphisms. -/
@[ext, stacks 023W "(2) morphisms of descent data"]
structure Hom (D E : DescentData f) where
  /-- The map over each member of the family. -/
  hom (i : ι) : D.obj i ⟶ E.obj i
  /-- The compatibility square on each pairwise fibre product. -/
  comm (i j : ι) :
    prod.map ((Over.map (f i)).map (hom i)) (𝟙 (Over.mk (f j))) ≫
        (E.gluing i j).hom.left =
      (D.gluing i j).hom.left ≫
        prod.map (𝟙 (Over.mk (f i))) ((Over.map (f j)).map (hom j))

/-- Descent data relative to `f` form a category, with identities and composition computed
componentwise. -/
instance : Category (DescentData f) where
  Hom := Hom
  id D := { hom := fun i ↦ 𝟙 (D.obj i), comm := by intros; simp }
  comp φ ψ :=
    { hom := fun i ↦ φ.hom i ≫ ψ.hom i
      comm := by
        intro i j; simp only [Functor.map_comp, prod.map_comp_id, prod.map_id_comp]
        rw [Category.assoc, ψ.comm, ← Category.assoc, φ.comm, Category.assoc] }
  id_comp := by intros; apply Hom.ext; funext i; exact Category.id_comp _
  comp_id := by intros; apply Hom.ext; funext i; exact Category.comp_id _
  assoc := by intros; apply Hom.ext; funext i; exact Category.assoc _ _ _

/-- The component of the identity morphism of descent data is the identity. -/
@[simp]
lemma id_hom (D : DescentData f) (i : ι) : (𝟙 D : D ⟶ D).hom i = 𝟙 (D.obj i) := rfl

/-- The component of a composite of morphisms of descent data is the composite of the
components. -/
@[simp]
lemma comp_hom {D E F : DescentData f} (φ : D ⟶ E) (ψ : E ⟶ F) (i : ι) :
    (φ ≫ ψ).hom i = φ.hom i ≫ ψ.hom i := rfl

/-- Morphisms of descent data are determined by their components. -/
@[ext]
lemma hom_ext {D E : DescentData f} {φ ψ : D ⟶ E}
    (h : ∀ i, φ.hom i = ψ.hom i) : φ = ψ := Hom.ext (funext h)

/-- Evaluation at a member of the family, as a functor to schemes over that member. -/
@[simps, implicit_reducible]
def evaluation (i : ι) : DescentData f ⥤ Over (X i) where
  obj D := D.obj i
  map φ := φ.hom i

/-- A product of two morphisms of `S`-schemes, read on the literal fibre products through
`CategoryTheory.Over.prodLeftIsoPullback`, is the induced map of fibre products. -/
lemma prodMap_left {A B C D : Over S} (a : A ⟶ C) (b : B ⟶ D) :
    (Over.prodLeftIsoPullback A B).inv ≫ (prod.map a b).left ≫
        (Over.prodLeftIsoPullback C D).hom =
      pullback.map A.hom B.hom C.hom D.hom a.left b.left (𝟙 S) (by simp) (by simp) := by
  apply pullback.hom_ext <;>
    simp only [Category.assoc, Over.prodLeftIsoPullback_hom_fst, Over.prodLeftIsoPullback_hom_snd,
      pullback.map, pullback.lift_fst, pullback.lift_snd] <;>
    (first
      | rw [← Over.comp_left, prod.map_fst, Over.comp_left]
      | rw [← Over.comp_left, prod.map_snd, Over.comp_left]) <;>
    simp

end DescentData

end AlgebraicGeometry
