module

public import StacksFrontier.CategoryTheory.BifunctorComparisonConstraints

/-!
# The associativity models of a comparison of bifunctors, in five bundles

`CategoryTheory.bifunctor_comparison_assoc_of_models` takes nine hypotheses, and in a geometric
application each of them is a long equation between composites in a derived category.  This file
groups them into five propositions — the laws relating the models to the two constraints, the
model identifications of the comparison at the two *pairs*, the two model identifications at the
*triples*, and the identity linking the two models of the triple tensor product — and restates
the chase for the five bundles.

## Main definitions

* `CategoryTheory.AssocModelLaws`: the associativity law of the source models, the associativity
  law of the target models, and the naturality of the target constraint.
* `CategoryTheory.AssocModelPairs`: the model identifications of the comparison at `(X, Y)` and
  at `(Y, Z)`.
* `CategoryTheory.AssocModelTripleLeft`, `CategoryTheory.AssocModelTripleRight`: the model
  identifications at `(XY', Z)` and at `(X, YZ')`.
* `CategoryTheory.AssocModelLink`: the identity linking the two models of the triple tensor
  product.

## Main results

* `CategoryTheory.bifunctor_comparison_assoc_of_bundles`:
  `CategoryTheory.bifunctor_comparison_assoc_of_models`, with its nine hypotheses read off the
  five bundles.

## Implementation notes

*Why the bundles exist.*  The reason is mechanical and not mathematical: the chase is applied
once, to a comparison of derived tensor bifunctors on the derived categories of modules on two
ringed spaces, and elaborating the nine arguments of that one application in a single
declaration exceeds the heartbeat budget, which is per declaration.  Nothing can be dropped and
no argument is ill-typed; the application simply has to be paid for in instalments.  Each bundle
is built in its own declaration, and the arguments of
`CategoryTheory.bifunctor_comparison_assoc_of_bundles` are then terms whose types are already
fully elaborated, so the implicit objects and maps are read off them by matching rather than
solved for.  How finely the nine have to be grouped is a measurement and not a judgement: with
the two model identifications at the triples and the linking identity in one bundle the budget
is still exceeded, and with each of the three in a bundle of its own it is not.

*Why the objects and maps are explicit parameters of the bundles.*  So that a caller can name
them once, in a declaration of its own, and the five bundles it then proves carry no
metavariables.  With them implicit the caller would be back to solving for all eleven objects
and sixteen maps while checking the fields, which is the cost the bundles exist to split.
-/

@[expose] public section

open scoped CategoryTheory.Prod

namespace CategoryTheory

universe v₁ v₂ u₁ u₂

variable {C : Type u₁} [Category.{v₁} C] {D : Type u₂} [Category.{v₂} D] (P : C ⥤ D)
  (A : C × C ⥤ C) (B : D × D ⥤ D)

/-! ### The five bundles -/

/-- **The two associativity laws of the models, and the naturality of the target constraint.**
`aA` and `aB` are the two associativity constraints and `aBP` is the target one read at the
images of `P`; the four model comparisons on each side are related to the constraints by `hA` and
`hB`, and `ha` is the naturality of `aB` in all three variables.  Nothing here mentions the
comparison `α`. -/
structure AssocModelLaws {X Y Z : C} {XY' YZ' XYZ' X_YZ' : C} {X' Y' Z' XY YZ XYZ X_YZ : D}
    (aA : A.obj (A.obj (X, Y), Z) ⟶ A.obj (X, A.obj (Y, Z)))
    (aB : B.obj (B.obj (X', Y'), Z') ⟶ B.obj (X', B.obj (Y', Z')))
    (aBP : B.obj (B.obj (P.obj X, P.obj Y), P.obj Z) ⟶
      B.obj (P.obj X, B.obj (P.obj Y, P.obj Z)))
    (nX : P.obj X ⟶ X') (nY : P.obj Y ⟶ Y') (nZ : P.obj Z ⟶ Z')
    (cA : A.obj (X, Y) ⟶ XY') (cA' : A.obj (Y, Z) ⟶ YZ')
    (cA'' : A.obj (XY', Z) ⟶ XYZ') (cA''' : A.obj (X, YZ') ⟶ X_YZ') (gA : XYZ' ⟶ X_YZ')
    (cXY : B.obj (X', Y') ⟶ XY) (cYZ : B.obj (Y', Z') ⟶ YZ)
    (cXYZ : B.obj (XY, Z') ⟶ XYZ) (cX_YZ : B.obj (X', YZ) ⟶ X_YZ) (gB : XYZ ⟶ X_YZ) :
    Prop where
  /-- The source models carry the source constraint to the re-bracketing `gA`. -/
  hA : A.map (cA ×ₘ 𝟙 Z) ≫ cA'' ≫ gA = aA ≫ A.map (𝟙 X ×ₘ cA') ≫ cA'''
  /-- The target models carry the target constraint to the re-bracketing `gB`. -/
  hB : B.map (cXY ×ₘ 𝟙 Z') ≫ cXYZ ≫ gB = aB ≫ B.map (𝟙 X' ×ₘ cYZ) ≫ cX_YZ
  /-- The target constraint is natural in all three variables. -/
  ha : B.map (B.map (nX ×ₘ nY) ×ₘ nZ) ≫ aB = aBP ≫ B.map (nX ×ₘ B.map (nY ×ₘ nZ))

/-- **The model identifications of the comparison at the two pairs** the associativity square
tensors: `(X, Y)` and `(Y, Z)`. -/
structure AssocModelPairs (α : A ⋙ P ⟶ P.prod P ⋙ B) {X Y Z : C} {XY' YZ' : C}
    {X' Y' Z' XY YZ : D}
    (nX : P.obj X ⟶ X') (nY : P.obj Y ⟶ Y') (nZ : P.obj Z ⟶ Z')
    (cA : A.obj (X, Y) ⟶ XY') (cA' : A.obj (Y, Z) ⟶ YZ')
    (cXY : B.obj (X', Y') ⟶ XY) (cYZ : B.obj (Y', Z') ⟶ YZ)
    (nXY : P.obj XY' ⟶ XY) (nYZ : P.obj YZ' ⟶ YZ) : Prop where
  /-- `α` at `(X, Y)` is computed by the models. -/
  hXY : α.app (X, Y) ≫ B.map (nX ×ₘ nY) ≫ cXY = P.map cA ≫ nXY
  /-- `α` at `(Y, Z)` is computed by the models. -/
  hYZ : α.app (Y, Z) ≫ B.map (nY ×ₘ nZ) ≫ cYZ = P.map cA' ≫ nYZ

/-- **The model identification of the comparison at the triple `(XY', Z)`.**  The model
comparison out of `A.obj (XY', Z)` is read against the model `XY` of `A.obj (X, Y)`, not against
the image of `XY'`, which is why `nXY` occurs. -/
structure AssocModelTripleLeft (α : A ⋙ P ⟶ P.prod P ⋙ B) {Z : C} {XY' XYZ' : C}
    {Z' XY XYZ : D}
    (nZ : P.obj Z ⟶ Z') (cA'' : A.obj (XY', Z) ⟶ XYZ') (cXYZ : B.obj (XY, Z') ⟶ XYZ)
    (nXY : P.obj XY' ⟶ XY) (nXYZ : P.obj XYZ' ⟶ XYZ) : Prop where
  /-- `α` at `(XY', Z)` is computed by the models. -/
  hXYZ : α.app (XY', Z) ≫ B.map (nXY ×ₘ nZ) ≫ cXYZ = P.map cA'' ≫ nXYZ

/-- **The model identification of the comparison at the triple `(X, YZ')`**; the companion of
`CategoryTheory.AssocModelTripleLeft`. -/
structure AssocModelTripleRight (α : A ⋙ P ⟶ P.prod P ⋙ B) {X : C} {YZ' X_YZ' : C}
    {X' YZ X_YZ : D}
    (nX : P.obj X ⟶ X') (cA''' : A.obj (X, YZ') ⟶ X_YZ') (cX_YZ : B.obj (X', YZ) ⟶ X_YZ)
    (nYZ : P.obj YZ' ⟶ YZ) (nX_YZ : P.obj X_YZ' ⟶ X_YZ) : Prop where
  /-- `α` at `(X, YZ')` is computed by the models. -/
  hX_YZ : α.app (X, YZ') ≫ B.map (nX ×ₘ nYZ) ≫ cX_YZ = P.map cA''' ≫ nX_YZ

/-- **The identity linking the two models of the triple tensor product.**  The two model
comparisons out of `A.obj (A.obj (X, Y), Z)` and `A.obj (X, A.obj (Y, Z))` land in different
objects, and this matches the re-bracketing `gA` of the source models with the re-bracketing
`gB` of the target ones. -/
structure AssocModelLink {XYZ' X_YZ' : C} {XYZ X_YZ : D} (gA : XYZ' ⟶ X_YZ') (gB : XYZ ⟶ X_YZ)
    (nXYZ : P.obj XYZ' ⟶ XYZ) (nX_YZ : P.obj X_YZ' ⟶ X_YZ) : Prop where
  /-- The two re-bracketings of the triple tensor product agree on the models. -/
  hg : nXYZ ≫ gB = P.map gA ≫ nX_YZ

/-! ### The chase, read off the bundles -/

variable {P A B}

/-- **A comparison of bifunctors carries an associativity constraint to an associativity
constraint, as soon as its models do** — `CategoryTheory.bifunctor_comparison_assoc_of_models`
with its nine hypotheses read off `CategoryTheory.AssocModelLaws`,
`CategoryTheory.AssocModelPairs`, `CategoryTheory.AssocModelTripleLeft`,
`CategoryTheory.AssocModelTripleRight` and `CategoryTheory.AssocModelLink`. -/
lemma bifunctor_comparison_assoc_of_bundles {α : A ⋙ P ⟶ P.prod P ⋙ B} {X Y Z : C}
    {XY' YZ' XYZ' X_YZ' : C} {X' Y' Z' XY YZ XYZ X_YZ : D}
    {aA : A.obj (A.obj (X, Y), Z) ⟶ A.obj (X, A.obj (Y, Z))}
    {aB : B.obj (B.obj (X', Y'), Z') ⟶ B.obj (X', B.obj (Y', Z'))}
    {aBP : B.obj (B.obj (P.obj X, P.obj Y), P.obj Z) ⟶
      B.obj (P.obj X, B.obj (P.obj Y, P.obj Z))}
    {nX : P.obj X ⟶ X'} {nY : P.obj Y ⟶ Y'} {nZ : P.obj Z ⟶ Z'}
    {cA : A.obj (X, Y) ⟶ XY'} {cA' : A.obj (Y, Z) ⟶ YZ'}
    {cA'' : A.obj (XY', Z) ⟶ XYZ'} {cA''' : A.obj (X, YZ') ⟶ X_YZ'} {gA : XYZ' ⟶ X_YZ'}
    {cXY : B.obj (X', Y') ⟶ XY} {cYZ : B.obj (Y', Z') ⟶ YZ}
    {cXYZ : B.obj (XY, Z') ⟶ XYZ} {cX_YZ : B.obj (X', YZ) ⟶ X_YZ} {gB : XYZ ⟶ X_YZ}
    {nXY : P.obj XY' ⟶ XY} {nYZ : P.obj YZ' ⟶ YZ}
    {nXYZ : P.obj XYZ' ⟶ XYZ} {nX_YZ : P.obj X_YZ' ⟶ X_YZ}
    (hmono : Mono (B.map (nX ×ₘ (B.map (nY ×ₘ nZ) ≫ cYZ)) ≫ cX_YZ))
    (laws : AssocModelLaws P A B aA aB aBP nX nY nZ cA cA' cA'' cA''' gA cXY cYZ cXYZ cX_YZ gB)
    (pairs : AssocModelPairs P A B α nX nY nZ cA cA' cXY cYZ nXY nYZ)
    (left : AssocModelTripleLeft P A B α nZ cA'' cXYZ nXY nXYZ)
    (right : AssocModelTripleRight P A B α nX cA''' cX_YZ nYZ nX_YZ)
    (link : AssocModelLink P gA gB nXYZ nX_YZ) :
    α.app (A.obj (X, Y), Z) ≫ B.map (α.app (X, Y) ×ₘ 𝟙 (P.obj Z)) ≫ aBP =
      P.map aA ≫ α.app (X, A.obj (Y, Z)) ≫ B.map (𝟙 (P.obj X) ×ₘ α.app (Y, Z)) :=
  bifunctor_comparison_assoc_of_models A B α aA aB aBP hmono laws.hA laws.hB laws.ha
    pairs.hXY pairs.hYZ left.hXYZ right.hX_YZ link.hg

end CategoryTheory

end
