module

public import Mathlib.CategoryTheory.Filtered.Basic
public import Mathlib.CategoryTheory.Limits.Shapes.Images

/-!
# Reindexing a filtered colimit by the images of a cofinal family of arrows

Let `D : I ⥤ C` be a diagram over a filtered category with colimit cocone `c`, and let `P` be a
property of arrows of `I` such that every object of `I` is the source of an arrow with that
property. The arrows with property `P` form a filtered full subcategory of `Arrow I`, the
assignment sending such an arrow `f` to the image of `D.map f` is a functor on it, and the
obvious cocone from that functor to `c.pt` is again a colimit cocone.

So a filtered colimit may be rewritten as a filtered colimit of *images* of its transition maps,
at the price of reindexing by arrows rather than by objects. This is the mechanism of the proof of
Stacks 0F0M: there `P` is the property of a transition map that it vanishes on the stalk at a
geometric point, and the images inherit that vanishing while remaining constructible.

## Main definitions

* `CategoryTheory.Limits.arrowImageDiagram` — the diagram of images, indexed by the arrows of `I`
  with property `P`.
* `CategoryTheory.Limits.arrowImageCocone` — its cocone with apex `c.pt`.

## Main results

* `CategoryTheory.Limits.isFiltered_arrowFullSubcategory` — the index category is filtered.
* `CategoryTheory.Limits.isColimitArrowImageCocone` — the cocone is a colimit cocone.

## Implementation notes

The hypothesis that every object is the source of an arrow with property `P` is taken as data — a
function `n` on objects together with arrows `φ i : i ⟶ n i` — so that nothing is chosen from a
bare existence statement.

Both constructions of a morphism in the index category are the same one,
`CategoryTheory.Limits.arrowFullSubcategoryHom`: out of an arrow `f : a ⟶ b` and a map
`u : b ⟶ k`, the square with legs `f ≫ u` and `u ≫ φ k` goes from `f` to `φ k`. Filteredness
uses it for an upper bound of two targets and for an object equalising two right legs.

The monomorphism out of and the epimorphism into the value of the diagram are given names,
`arrowImageι` and `arrowImageFactor`, typed by the value of the diagram rather than by the image
itself; the two agree only up to unfolding the diagram, and naming them keeps every rewrite in the
proofs below between terms of literally the same type.

The proof that the cocone is a colimit never descends to elements: a cocone on the diagram of
images induces a cocone on `D` by precomposing with the factorisations through the images, and the
two universal properties match up because `arrowImageι` is a monomorphism.
-/

@[expose] public noncomputable section

namespace CategoryTheory.Limits

universe v₁ u₁ v u

variable {I : Type u₁} [Category.{v₁} I] {C : Type u} [Category.{v} C]

/-- Out of an arrow `f : a ⟶ b` with property `P` and a map `u : b ⟶ k`, the commutative square
with legs `f ≫ u` and `u ≫ φ k` is a morphism in the full subcategory of arrows with property
`P`, from `f` to `φ k`. -/
public def arrowFullSubcategoryHom (P : ObjectProperty (Arrow I)) {n : I → I}
    (φ : ∀ i, i ⟶ n i) (hφ : ∀ i, P (Arrow.mk (φ i))) (X : P.FullSubcategory) {k : I}
    (u : X.obj.right ⟶ k) :
    X ⟶ (⟨Arrow.mk (φ k), hφ k⟩ : P.FullSubcategory) :=
  ObjectProperty.homMk (Arrow.homMk (X.obj.hom ≫ u) (u ≫ φ k) (by simp))

/-- The left leg of `arrowFullSubcategoryHom P φ hφ X u` is `X.obj.hom ≫ u`. -/
@[simp]
public theorem arrowFullSubcategoryHom_hom_left (P : ObjectProperty (Arrow I)) {n : I → I}
    (φ : ∀ i, i ⟶ n i) (hφ : ∀ i, P (Arrow.mk (φ i))) (X : P.FullSubcategory) {k : I}
    (u : X.obj.right ⟶ k) :
    (arrowFullSubcategoryHom P φ hφ X u).hom.left = X.obj.hom ≫ u :=
  rfl

/-- The right leg of `arrowFullSubcategoryHom P φ hφ X u` is `u ≫ φ k`. -/
@[simp]
public theorem arrowFullSubcategoryHom_hom_right (P : ObjectProperty (Arrow I)) {n : I → I}
    (φ : ∀ i, i ⟶ n i) (hφ : ∀ i, P (Arrow.mk (φ i))) (X : P.FullSubcategory) {k : I}
    (u : X.obj.right ⟶ k) :
    (arrowFullSubcategoryHom P φ hφ X u).hom.right = u ≫ φ k :=
  rfl

/-- **The arrows with property `P` form a filtered category** when every object of the filtered
category `I` is the source of such an arrow. Two arrows are dominated by the chosen arrow out of
an upper bound of their targets, and two parallel squares are equalised by the chosen arrow out of
an object equalising their right legs. -/
public theorem isFiltered_arrowFullSubcategory [IsFiltered I] (P : ObjectProperty (Arrow I))
    {n : I → I} (φ : ∀ i, i ⟶ n i) (hφ : ∀ i, P (Arrow.mk (φ i))) :
    IsFiltered P.FullSubcategory where
  cocone_objs X Y :=
    ⟨⟨Arrow.mk (φ (IsFiltered.max X.obj.right Y.obj.right)),
        hφ (IsFiltered.max X.obj.right Y.obj.right)⟩,
      arrowFullSubcategoryHom P φ hφ X (IsFiltered.leftToMax _ _),
      arrowFullSubcategoryHom P φ hφ Y (IsFiltered.rightToMax _ _), trivial⟩
  cocone_maps X Y σ τ :=
    ⟨⟨Arrow.mk (φ (IsFiltered.coeq σ.hom.right τ.hom.right)),
        hφ (IsFiltered.coeq σ.hom.right τ.hom.right)⟩,
      arrowFullSubcategoryHom P φ hφ Y (IsFiltered.coeqHom σ.hom.right τ.hom.right), by
        refine ObjectProperty.hom_ext P (Arrow.hom_ext _ _ ?_ ?_)
        · simp only [ObjectProperty.FullSubcategory.comp_hom, Arrow.comp_left,
            arrowFullSubcategoryHom_hom_left, ← Category.assoc, σ.hom.w, τ.hom.w]
          rw [Category.assoc, Category.assoc, IsFiltered.coeq_condition]
        · simp only [ObjectProperty.FullSubcategory.comp_hom, Arrow.comp_right,
            arrowFullSubcategoryHom_hom_right, ← Category.assoc,
            IsFiltered.coeq_condition σ.hom.right τ.hom.right]⟩
  nonempty := by
    have : Nonempty I := IsFiltered.nonempty
    exact ⟨⟨Arrow.mk (φ (Classical.arbitrary I)), hφ _⟩⟩

variable [HasImages C] [HasImageMaps C]

/-- **The diagram of images of the transition maps** with property `P`: an arrow `f` of `I`
satisfying `P` is sent to the image of `D.map f`. -/
public def arrowImageDiagram (P : ObjectProperty (Arrow I)) (D : I ⥤ C) :
    P.FullSubcategory ⥤ C :=
  P.ι ⋙ D.mapArrow ⋙ im

variable (P : ObjectProperty (Arrow I)) (D : I ⥤ C)

/-- The monomorphism from the value of `arrowImageDiagram` at an arrow `f` into the value of `D`
at the target of `f`. -/
public def arrowImageι (X : P.FullSubcategory) :
    (arrowImageDiagram P D).obj X ⟶ D.obj X.obj.right :=
  image.ι (D.map X.obj.hom)

/-- `arrowImageι P D X` is a monomorphism, being the inclusion of an image. -/
public instance mono_arrowImageι (X : P.FullSubcategory) : Mono (arrowImageι P D X) :=
  inferInstanceAs (Mono (image.ι (D.map X.obj.hom)))

/-- The epimorphism from the value of `D` at the source of an arrow `f` onto the value of
`arrowImageDiagram` at `f`. -/
public def arrowImageFactor (X : P.FullSubcategory) :
    D.obj X.obj.left ⟶ (arrowImageDiagram P D).obj X :=
  factorThruImage (D.map X.obj.hom)

/-- The factorisation of `D.map f` through its image: `arrowImageFactor` followed by
`arrowImageι` is `D.map f`. -/
@[reassoc, simp]
public theorem arrowImageFactor_ι (X : P.FullSubcategory) :
    arrowImageFactor P D X ≫ arrowImageι P D X = D.map X.obj.hom :=
  image.fac _

/-- The transition map of `arrowImageDiagram` along `σ : X ⟶ Y`, followed by the inclusion of the
image at `Y`, is the inclusion at `X` followed by `D.map σ.hom.right`. -/
@[reassoc]
public theorem arrowImageDiagram_map_ι {X Y : P.FullSubcategory} (σ : X ⟶ Y) :
    (arrowImageDiagram P D).map σ ≫ arrowImageι P D Y =
      arrowImageι P D X ≫ D.map σ.hom.right :=
  image.map_ι _

/-- **The cocone on the diagram of images** with apex the apex of a cocone on `D`: the image of
`D.map f` sits inside the value of `D` at the target of `f`, which maps to the apex. -/
public abbrev arrowImageCocone (c : Cocone D) : Cocone (arrowImageDiagram P D) where
  pt := c.pt
  ι :=
    { app X := arrowImageι P D X ≫ c.ι.app X.obj.right
      naturality := by
        intro X Y σ
        dsimp only [Functor.const_obj_obj, Functor.const_obj_map]
        rw [Category.comp_id, arrowImageDiagram_map_ι_assoc, c.w] }

/-- The leg of `arrowImageCocone P D c` at `X` is `arrowImageι P D X ≫ c.ι.app X.obj.right`. -/
public theorem arrowImageCocone_ι_app (c : Cocone D) (X : P.FullSubcategory) :
    (arrowImageCocone P D c).ι.app X = arrowImageι P D X ≫ c.ι.app X.obj.right :=
  rfl

section IsColimit

variable [IsFiltered I] {n : I → I} (φ : ∀ i, i ⟶ n i) (hφ : ∀ i, P (Arrow.mk (φ i)))

/-- The cocone on `D` attached to a cocone on the diagram of images: at `i`, factor `D.map (φ i)`
through its image and then use the given cocone. -/
private def descCocone (t : Cocone (arrowImageDiagram P D)) : Cocone D where
  pt := t.pt
  ι :=
    { app i := arrowImageFactor P D ⟨Arrow.mk (φ i), hφ i⟩ ≫
        t.ι.app ⟨Arrow.mk (φ i), hφ i⟩
      naturality := by
        intro i j g
        obtain ⟨m, p, β, hkey⟩ := IsFiltered.span (φ i) (g ≫ φ j)
        have hstep :
            (D.map g ≫ arrowImageFactor P D (⟨Arrow.mk (φ j), hφ j⟩ : P.FullSubcategory)) ≫
                (arrowImageDiagram P D).map (arrowFullSubcategoryHom P φ hφ
                  (⟨Arrow.mk (φ j), hφ j⟩ : P.FullSubcategory) β) =
              arrowImageFactor P D (⟨Arrow.mk (φ i), hφ i⟩ : P.FullSubcategory) ≫
                (arrowImageDiagram P D).map (arrowFullSubcategoryHom P φ hφ
                  (⟨Arrow.mk (φ i), hφ i⟩ : P.FullSubcategory) p) := by
          refine (cancel_mono (arrowImageι P D
            (⟨Arrow.mk (φ m), hφ m⟩ : P.FullSubcategory))).mp ?_
          simp only [Category.assoc, arrowImageDiagram_map_ι, arrowImageFactor_ι_assoc,
            arrowFullSubcategoryHom_hom_right, Arrow.mk_hom, ← Functor.map_comp]
          exact congrArg D.map
            (by simpa only [Category.assoc] using (congrArg (· ≫ φ m) hkey).symm)
        dsimp only [Functor.const_obj_obj, Functor.const_obj_map]
        rw [Category.comp_id,
          ← t.w (arrowFullSubcategoryHom P φ hφ
            (⟨Arrow.mk (φ j), hφ j⟩ : P.FullSubcategory) β),
          ← t.w (arrowFullSubcategoryHom P φ hφ
            (⟨Arrow.mk (φ i), hφ i⟩ : P.FullSubcategory) p)]
        simp only [← Category.assoc]
        rw [hstep] }

include hφ in
/-- **The cocone on the diagram of images is a colimit cocone.** Together with
`CategoryTheory.Limits.isFiltered_arrowFullSubcategory` this exhibits the apex of any filtered
colimit as a filtered colimit of the images of the transition maps with property `P`. -/
public theorem isColimitArrowImageCocone {c : Cocone D} (hc : IsColimit c) :
    Nonempty (IsColimit (arrowImageCocone P D c)) := by
  refine ⟨{ desc t := hc.desc (descCocone P D φ hφ t), fac := ?_, uniq := ?_ }⟩
  · intro t X
    have hstep : arrowImageι P D X ≫
          arrowImageFactor P D (⟨Arrow.mk (φ X.obj.right), hφ X.obj.right⟩ : P.FullSubcategory) =
        (arrowImageDiagram P D).map (arrowFullSubcategoryHom P φ hφ X (𝟙 X.obj.right)) := by
      refine (cancel_mono (arrowImageι P D
        (⟨Arrow.mk (φ X.obj.right), hφ X.obj.right⟩ : P.FullSubcategory))).mp ?_
      simp only [Category.assoc, arrowImageDiagram_map_ι, arrowImageFactor_ι,
        arrowFullSubcategoryHom_hom_right, Arrow.mk_hom, Category.id_comp]
    have h1 : (arrowImageι P D X ≫ c.ι.app X.obj.right) ≫
        hc.desc (descCocone P D φ hφ t) = t.ι.app X := by
      rw [Category.assoc, hc.fac]
      change arrowImageι P D X ≫ arrowImageFactor P D
          (⟨Arrow.mk (φ X.obj.right), hφ X.obj.right⟩ : P.FullSubcategory) ≫
          t.ι.app ⟨Arrow.mk (φ X.obj.right), hφ X.obj.right⟩ = t.ι.app X
      rw [← t.w (arrowFullSubcategoryHom P φ hφ X (𝟙 X.obj.right)), ← Category.assoc, hstep]
    exact h1
  · intro t f hf
    refine hc.uniq (descCocone P D φ hφ t) f fun i => ?_
    have key : arrowImageFactor P D (⟨Arrow.mk (φ i), hφ i⟩ : P.FullSubcategory) ≫
        (arrowImageCocone P D c).ι.app ⟨Arrow.mk (φ i), hφ i⟩ = c.ι.app i := by
      rw [arrowImageCocone_ι_app, ← Category.assoc, arrowImageFactor_ι]
      exact c.w (φ i)
    change c.ι.app i ≫ f = arrowImageFactor P D (⟨Arrow.mk (φ i), hφ i⟩ : P.FullSubcategory) ≫
      t.ι.app ⟨Arrow.mk (φ i), hφ i⟩
    rw [← hf ⟨Arrow.mk (φ i), hφ i⟩, ← Category.assoc, key]

end IsColimit

end CategoryTheory.Limits

end
