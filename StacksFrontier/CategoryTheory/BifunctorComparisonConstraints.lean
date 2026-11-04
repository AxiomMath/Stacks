module

public import StacksFrontier.CategoryTheory.BifunctorProdMap

/-!
# A comparison of two bifunctors is compatible with their constraints, from the models

Let `P : C ⥤ D` be a functor, let `A` and `B` be bifunctors on `C` and on `D`, and let
`α : A ⋙ P ⟶ P.prod P ⋙ B` be a comparison between them, as in
`StacksFrontier.CategoryTheory.BifunctorProdMap`.  Suppose `A` and `B` carry associativity and
commutativity constraints.  This file reduces the compatibility of `α` with those constraints
to the same compatibility for a family of *model* comparisons — morphisms
`c : A.obj (X, Y) ⟶ XY` out of the bifunctor into objects on which the constraints are already
computed.

The reduction is the diagram chase that the derived pullback–tensor comparison of
[Stacks, Tag 079U] is proved compatible with the constraints of the monoidal derived category of
[Stacks, Tag 0FPT] by: on a pair of K-flat complexes both sides of such a compatibility are
computed by ordinary total tensor complexes, where the constraints are the associator and the
Koszul symmetry of complexes, and the identification of `α` with the model comparison there is
the only geometric input.  Nothing in this file mentions complexes, derived categories or ringed
spaces, and each hypothesis is one commuting square.

## Main results

* `CategoryTheory.bifunctor_comparison_assoc_of_models`: **the associativity compatibility.**
  Given the model identification of `α` at the four pairs the associativity square involves, the
  associativity law for the model comparisons on both sides, the naturality of the target
  constraint, and the identity linking the two models of the triple tensor product, the
  comparison carries the associativity constraint of `A` to that of `B`.
* `CategoryTheory.bifunctor_comparison_braiding_of_models`: **the commutativity
  compatibility**, the same way.
* `CategoryTheory.bifunctor_comparison_model_comp_left`,
  `bifunctor_comparison_model_comp_right`: a model identification of `α` composed with a
  naturality square of the target models is again a model identification, for the composed
  model comparison.  This is how the model identification at a pair `(XY, Z)`, whose target
  model is `B.obj (XY', Z')`, is read against a *different* model `XY''` of `XY`.

## Implementation notes

*Where the content is.*  Both chases cancel one morphism — the composite of the target models
in the right-hand corner of the square, which is an isomorphism in every application — and then
rewrite each side down to the same composite of `P.map`s.  The associativity chase takes nine
rewrites, the commutativity one four.  No constraint is assumed invertible and no coherence
diagram is checked: the associativity law of the models is a hypothesis, not a consequence.

*Why the hypotheses are shaped as they are.*  Each is stated in the form in which the geometric
application has it.  The model identification is written
`α.app (X, Y) ≫ B.map (nX ×ₘ nY) ≫ cXY = P.map cXY' ≫ nXY`, with the *comparison composed onto
the front* rather than as an equation between `α.app (X, Y)` and a composite of inverses, which
is how [Stacks, Tag 079U] is available on K-flat representatives.  The naturality of the target
constraint is in the merged two- and three-variable form that a monoidal category supplies
directly.

*Why the models of the triple tensor product need a linking hypothesis.*  The two model
comparisons out of `A.obj (A.obj (X, Y), Z)` and `A.obj (X, A.obj (Y, Z))` land in two different
objects, and the associativity constraint of `A` relates them only through a morphism of those
objects — `gA` below.  Its image under `P` is matched with the corresponding morphism `gB` on the
target side by `hg`, which in the application is the associativity coherence of the comparison of
[Stacks, Tag 01CD] on complexes.
-/

@[expose] public section

open scoped CategoryTheory.Prod

namespace CategoryTheory

universe v₁ v₂ u₁ u₂

variable {C : Type u₁} [Category.{v₁} C] {D : Type u₂} [Category.{v₂} D] {P : C ⥤ D}
  (A : C × C ⥤ C) (B : D × D ⥤ D) (α : A ⋙ P ⟶ P.prod P ⋙ B)

/-! ### Re-reading a model identification against a further model -/

/-- A composition in the first factor of a bifunctor splits off, with the second factor kept. -/
private theorem bifunctor_map_comp_left_id_right {C₁ C₂ D₁ : Type*} [Category C₁] [Category C₂]
    [Category D₁] (B : C₁ × C₂ ⥤ D₁) {P P' P'' : C₁} {Q Q' : C₂} (x : P ⟶ P') (y : P' ⟶ P'')
    (z : Q ⟶ Q') : B.map ((x ≫ y) ×ₘ z) = B.map (x ×ₘ z) ≫ B.map (y ×ₘ 𝟙 Q') := by
  simpa using bifunctor_map_comp_both B x y z (𝟙 Q')

/-- A composition in the second factor of a bifunctor splits off, with the first factor kept. -/
private theorem bifunctor_map_comp_right_id_left {C₁ C₂ D₁ : Type*} [Category C₁] [Category C₂]
    [Category D₁] (B : C₁ × C₂ ⥤ D₁) {P P' : C₁} {Q Q' Q'' : C₂} (x : P ⟶ P') (y : Q ⟶ Q')
    (z : Q' ⟶ Q'') : B.map (x ×ₘ (y ≫ z)) = B.map (x ×ₘ y) ≫ B.map (𝟙 P' ×ₘ z) := by
  simpa using bifunctor_map_comp_both B x (𝟙 P') y z

/-- **A model identification of `α`, composed with a naturality square in the first variable.**
If `α` at `(X, Y)` is computed by the models `nX`, `nY` and the comparison `c`, and if `c` is
natural along a further morphism `t` of the first model, then `α` at `(X, Y)` is computed by the
models `nX ≫ t`, `nY` and the comparison `c₂`, with the model of `A.obj (X, Y)` composed with the
morphism `s` the naturality square produces. -/
lemma bifunctor_comparison_model_comp_left {X Y : C} {X' Y' X'' XY XY₂ : D} {XY' : C}
    {nX : P.obj X ⟶ X'} {nY : P.obj Y ⟶ Y'} {c : B.obj (X', Y') ⟶ XY}
    {cA : A.obj (X, Y) ⟶ XY'} {nXY : P.obj XY' ⟶ XY}
    {t : X' ⟶ X''} {c₂ : B.obj (X'', Y') ⟶ XY₂} {s : XY ⟶ XY₂}
    (hα : α.app (X, Y) ≫ B.map (nX ×ₘ nY) ≫ c = P.map cA ≫ nXY)
    (hnat : B.map (t ×ₘ 𝟙 Y') ≫ c₂ = c ≫ s) :
    α.app (X, Y) ≫ B.map ((nX ≫ t) ×ₘ nY) ≫ c₂ = P.map cA ≫ nXY ≫ s := by
  rw [bifunctor_map_comp_left_id_right]
  simp only [Category.assoc]
  rw [hnat, reassoc_of% hα]

/-- **A model identification of `α`, composed with a naturality square in the second variable**;
the companion of `CategoryTheory.bifunctor_comparison_model_comp_left`. -/
lemma bifunctor_comparison_model_comp_right {X Y : C} {X' Y' Y'' XY XY₂ : D} {XY' : C}
    {nX : P.obj X ⟶ X'} {nY : P.obj Y ⟶ Y'} {c : B.obj (X', Y') ⟶ XY}
    {cA : A.obj (X, Y) ⟶ XY'} {nXY : P.obj XY' ⟶ XY}
    {t : Y' ⟶ Y''} {c₂ : B.obj (X', Y'') ⟶ XY₂} {s : XY ⟶ XY₂}
    (hα : α.app (X, Y) ≫ B.map (nX ×ₘ nY) ≫ c = P.map cA ≫ nXY)
    (hnat : B.map (𝟙 X' ×ₘ t) ≫ c₂ = c ≫ s) :
    α.app (X, Y) ≫ B.map (nX ×ₘ (nY ≫ t)) ≫ c₂ = P.map cA ≫ nXY ≫ s := by
  rw [bifunctor_map_comp_right_id_left]
  simp only [Category.assoc]
  rw [hnat, reassoc_of% hα]

/-! ### The commutativity compatibility -/

/-- **A comparison of bifunctors carries a commutativity constraint to a commutativity
constraint, as soon as its models do.**

`sA` and `sB` are the two constraints, `sBP` the target one read at the images of `P`.  The
models are `cXY : B.obj (X', Y') ⟶ XY` and `cYX`, with `gB : XY ⟶ YX` the model of the target
constraint and `gA` the model of the source one; `hA` and `hB` are the compatibility of the
models with the constraints, `hs` the naturality of `sB`, `hX` and `hY` the model
identifications of `α`, and `hg` the identity linking `gA` with `gB`.

The chase cancels the right-hand model comparison and rewrites both sides to
`P.map cA ≫ nXY ≫ gB`. -/
lemma bifunctor_comparison_braiding_of_models {X Y : C} {XY' YX' : C} {X' Y' XY YX : D}
    (sA : A.obj (X, Y) ⟶ A.obj (Y, X))
    (sB : B.obj (X', Y') ⟶ B.obj (Y', X'))
    (sBP : B.obj (P.obj X, P.obj Y) ⟶ B.obj (P.obj Y, P.obj X))
    {nX : P.obj X ⟶ X'} {nY : P.obj Y ⟶ Y'}
    {cA : A.obj (X, Y) ⟶ XY'} {cA' : A.obj (Y, X) ⟶ YX'} {gA : XY' ⟶ YX'}
    {cXY : B.obj (X', Y') ⟶ XY} {cYX : B.obj (Y', X') ⟶ YX} {gB : XY ⟶ YX}
    {nXY : P.obj XY' ⟶ XY} {nYX : P.obj YX' ⟶ YX}
    (hmono : Mono (B.map (nY ×ₘ nX) ≫ cYX))
    (hA : sA ≫ cA' = cA ≫ gA)
    (hB : sB ≫ cYX = cXY ≫ gB)
    (hs : B.map (nX ×ₘ nY) ≫ sB = sBP ≫ B.map (nY ×ₘ nX))
    (hX : α.app (X, Y) ≫ B.map (nX ×ₘ nY) ≫ cXY = P.map cA ≫ nXY)
    (hY : α.app (Y, X) ≫ B.map (nY ×ₘ nX) ≫ cYX = P.map cA' ≫ nYX)
    (hg : nXY ≫ gB = P.map gA ≫ nYX) :
    P.map sA ≫ α.app (Y, X) = α.app (X, Y) ≫ sBP := by
  apply (cancel_mono (B.map (nY ×ₘ nX) ≫ cYX)).1
  simp only [Category.assoc]
  rw [hY, ← P.map_comp_assoc, hA, P.map_comp, Category.assoc, ← hg, ← reassoc_of% hs, hB,
    reassoc_of% hX]

/-! ### The associativity compatibility -/

/-- **A comparison of bifunctors carries an associativity constraint to an associativity
constraint, as soon as its models do.**

`aA` and `aB` are the two constraints, `aBP` the target one read at the images of `P`.  The four
model comparisons `cXY`, `cYZ`, `cXYZ`, `cX_YZ` on the target side, and `cA`, `cA'`, `cA''`,
`cA'''` on the source side, are related to the constraints by `hA` and `hB`; `ha` is the
naturality of `aB` in all three variables, the four `hα`s are the model identifications of `α`,
and `hg` links the two models `gA`, `gB` of the re-bracketing of the triple tensor product.

The chase cancels the composite of the target models in the lower right corner and rewrites both
sides to `P.map aA ≫ P.map (A.map (𝟙 X ×ₘ cA')) ≫ P.map cA''' ≫ nX_YZ`. -/
lemma bifunctor_comparison_assoc_of_models {X Y Z : C} {XY' YZ' XYZ' X_YZ' : C}
    {X' Y' Z' XY YZ XYZ X_YZ : D}
    (aA : A.obj (A.obj (X, Y), Z) ⟶ A.obj (X, A.obj (Y, Z)))
    (aB : B.obj (B.obj (X', Y'), Z') ⟶ B.obj (X', B.obj (Y', Z')))
    (aBP : B.obj (B.obj (P.obj X, P.obj Y), P.obj Z) ⟶
      B.obj (P.obj X, B.obj (P.obj Y, P.obj Z)))
    {nX : P.obj X ⟶ X'} {nY : P.obj Y ⟶ Y'} {nZ : P.obj Z ⟶ Z'}
    {cA : A.obj (X, Y) ⟶ XY'} {cA' : A.obj (Y, Z) ⟶ YZ'}
    {cA'' : A.obj (XY', Z) ⟶ XYZ'} {cA''' : A.obj (X, YZ') ⟶ X_YZ'} {gA : XYZ' ⟶ X_YZ'}
    {cXY : B.obj (X', Y') ⟶ XY} {cYZ : B.obj (Y', Z') ⟶ YZ}
    {cXYZ : B.obj (XY, Z') ⟶ XYZ} {cX_YZ : B.obj (X', YZ) ⟶ X_YZ} {gB : XYZ ⟶ X_YZ}
    {nXY : P.obj XY' ⟶ XY} {nYZ : P.obj YZ' ⟶ YZ}
    {nXYZ : P.obj XYZ' ⟶ XYZ} {nX_YZ : P.obj X_YZ' ⟶ X_YZ}
    (hmono : Mono (B.map (nX ×ₘ (B.map (nY ×ₘ nZ) ≫ cYZ)) ≫ cX_YZ))
    (hA : A.map (cA ×ₘ 𝟙 Z) ≫ cA'' ≫ gA = aA ≫ A.map (𝟙 X ×ₘ cA') ≫ cA''')
    (hB : B.map (cXY ×ₘ 𝟙 Z') ≫ cXYZ ≫ gB = aB ≫ B.map (𝟙 X' ×ₘ cYZ) ≫ cX_YZ)
    (ha : B.map (B.map (nX ×ₘ nY) ×ₘ nZ) ≫ aB =
      aBP ≫ B.map (nX ×ₘ B.map (nY ×ₘ nZ)))
    (hXY : α.app (X, Y) ≫ B.map (nX ×ₘ nY) ≫ cXY = P.map cA ≫ nXY)
    (hYZ : α.app (Y, Z) ≫ B.map (nY ×ₘ nZ) ≫ cYZ = P.map cA' ≫ nYZ)
    (hXYZ : α.app (XY', Z) ≫ B.map (nXY ×ₘ nZ) ≫ cXYZ = P.map cA'' ≫ nXYZ)
    (hX_YZ : α.app (X, YZ') ≫ B.map (nX ×ₘ nYZ) ≫ cX_YZ = P.map cA''' ≫ nX_YZ)
    (hg : nXYZ ≫ gB = P.map gA ≫ nX_YZ) :
    α.app (A.obj (X, Y), Z) ≫ B.map (α.app (X, Y) ×ₘ 𝟙 (P.obj Z)) ≫ aBP =
      P.map aA ≫ α.app (X, A.obj (Y, Z)) ≫ B.map (𝟙 (P.obj X) ×ₘ α.app (Y, Z)) := by
  -- The naturality of `α` at the two morphisms the square re-brackets along, with the identity
  -- component already reduced.
  have hnatX : α.app (X, A.obj (Y, Z)) ≫ B.map (𝟙 (P.obj X) ×ₘ P.map cA') =
      P.map (A.map (𝟙 X ×ₘ cA')) ≫ α.app (X, YZ') := by
    rw [← P.map_id X]
    exact (bifunctor_comparison_naturality A B α (𝟙 X) cA').symm
  have hnatZ : α.app (A.obj (X, Y), Z) ≫ B.map (P.map cA ×ₘ 𝟙 (P.obj Z)) =
      P.map (A.map (cA ×ₘ 𝟙 Z)) ≫ α.app (XY', Z) := by
    rw [← P.map_id Z]
    exact (bifunctor_comparison_naturality A B α cA (𝟙 Z)).symm
  -- The three ways the bifunctor applied to a pair of composites splits, each stated at the
  -- spelling the goal presents.
  apply (cancel_mono (B.map (nX ×ₘ (B.map (nY ×ₘ nZ) ≫ cYZ)) ≫ cX_YZ)).1
  simp only [Category.assoc]
  -- The right-hand side, down to `P.map aA ≫ P.map (A.map (𝟙 X ×ₘ cA')) ≫ P.map cA''' ≫ nX_YZ`.
  rw [← reassoc_of% (bifunctor_map_comp_right B nX (α.app (Y, Z))
        (B.map (nY ×ₘ nZ) ≫ cYZ)), hYZ, bifunctor_map_comp_right B nX (P.map cA') nYZ]
  simp only [Category.assoc]
  rw [reassoc_of% hnatX, hX_YZ]
  -- The left-hand side, down to the same thing.
  rw [bifunctor_map_comp_right_id_left]
  simp only [Category.assoc]
  rw [← reassoc_of% ha, ← hB, ← reassoc_of% (bifunctor_map_comp_left_id_right B _ cXY nZ),
    ← reassoc_of% (bifunctor_map_comp_left B (α.app (X, Y)) _ nZ), hXY,
    bifunctor_map_comp_left B (P.map cA) nXY nZ]
  simp only [Category.assoc]
  rw [reassoc_of% hnatZ, reassoc_of% hXYZ, hg, ← P.map_comp_assoc, ← P.map_comp_assoc,
    ← P.map_comp_assoc, ← P.map_comp_assoc]
  simp only [Category.assoc]
  rw [hA]

end CategoryTheory

end
