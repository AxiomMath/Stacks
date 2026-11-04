module

public import StacksFrontier.Topology.Sheaves.Cohomology.KFlat.StalkCriterion
import StacksCore.Tactic.EgaSgaAttribute

/-!
# The stalk functor carries the tensor product of sheaves of modules to the tensor product of
modules, bifunctorially

Let `(Y, 𝒪_Y)` be a ringed space and let `y` be a point of `Y`.  Tag 01CB identifies the stalk of
a tensor product of sheaves of modules with the tensor product of the stalks,

`(F ⊗_{𝒪_Y} G)_y ≅ F_y ⊗_{𝒪_{Y,y}} G_y`,

and `Stacks.SheafOfModules.KFlatStalkCriterion.stalkTensorIso` is that identification in the
spelling `AlgebraicGeometry.SheafOfModules.stalkFunctor` uses.  This file assembles it, together
with the two naturality statements that accompany it there, into a single natural isomorphism of
bifunctors

`(− ⊗_{𝒪_Y} −) ⋙ (−)_y ≅ ((−)_y × (−)_y) ⋙ (− ⊗_{𝒪_{Y,y}} −)`

on `Mod(𝒪_Y) × Mod(𝒪_Y)`.

## Main results

* `Stacks.SheafOfModules.KFlatStalkCriterion.stalkTensorIso_naturality`: the identification of
  Tag 01CB is natural in the pair of its two arguments at once.
* `Stacks.SheafOfModules.KFlatStalkCriterion.stalkTensorNatIso`: the natural isomorphism of
  bifunctors displayed above.

## Why this is wanted

`stalkTensorIso` is stated objectwise and its naturality is recorded in each variable separately,
by `stalkTensorIso_naturality_left` and `stalkTensorIso_naturality_right`.  Those two are what a
consumer working one object at a time needs, and they are what the K-flatness criterion of
Stacks 06YB uses.  A consumer working with the tensor product *as a bifunctor* needs instead one
isomorphism of functors on the product category, and no such statement existed: every occurrence
of `stalkTensorIso` in this development is at a pair of fixed objects.

The shape built here is the shape in which an isomorphism of tensor bifunctors is consumed by the
transport of an internal hom along an equivalence —
`Stacks.Cohomology.DerivedInternalHomPullback.EquivalenceTranspose.internalHomTransportIsoCurried`
of `StacksFrontier.Topology.Sheaves.Cohomology.DerivedPushforward.InternalHomEquivalenceTransport`,
which takes an equivalence `E`, two tensor bifunctors, two tensor–internal-hom bijections with
their three naturality clauses each, and an isomorphism of bifunctors `E(a ⊗ b) ≅ E a ⊗ E b`, and
produces the identification of the two internal homs.

This is **not** that input, and it carries no `@[stacks]` attribute beyond Tag 01CB's own.  Three
things stand between the two, and the third is worth recording because it is easy to miss.  The
identification the transport consumes is on *derived* categories, so a descent along the K-flat
localizations is needed — the pattern of
`Stacks.Cohomology.DerivedSectionsOnAPoint.onePointDerivedTensorIso` and of
`Stacks.Cohomology.DerivedInternalHomPullback.tensorBridge`.  The equivalence it consumes at a
point of a ringed space is `Stacks.Cohomology.DerivedInternalHomStalk.pointStalkModulesEquiv`,
whose functor is the stalk functor of the *one-point* space followed by restriction of scalars
along the germ map, rather than the stalk functor appearing here.  And that transport module does
not currently elaborate: `InternalHomEquivalenceTransport` fails with an
ambiguous term at its crossing lemmas and
`StacksFrontier.Topology.Sheaves.Cohomology.DerivedPushforward.InternalHomStalkTransportClauses`,
which supplies the six naturality clauses, fails with `maximum recursion depth` at three of them.
So nothing downstream can use the transport until those two are repaired, and this file
deliberately imports neither.

## Implementation notes

The naturality square at a morphism `(f, g)` of the product category is obtained from the two
one-variable statements and nothing else: `CategoryTheory.Functor.uncurry` sends `(f, g)` to
`(T.map f).app G ≫ (T.obj F').map g`, so the square splits as the right-variable square at `F'`
followed by the left-variable square at `G`.  No new compatibility of Tag 01CB is proved here.

## References

* [Stacks Project, Tag 01CB](https://stacks.math.columbia.edu/tag/01CB)
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits TopologicalSpace MonoidalCategory Opposite

universe u

noncomputable section

namespace Stacks.SheafOfModules.KFlatStalkCriterion

attribute [local implicit_reducible] CategoryTheory.sheafCompose
  AlgebraicGeometry.SheafedSpace.sheaf

variable (Y : AlgebraicGeometry.RingedSpace.{u, u}) (x : Y.carrier)

/-- The stalk ring `𝒪_{Y,y}`, in the `RingCat`-valued spelling `stalkTensorIso` is stated at. -/
abbrev stalkTensorRing : RingCat.{u} :=
  TopCat.Presheaf.stalk (C := RingCat.{u})
    (Stacks.SheafOfModules.TensorStalkRingedSpace.O Y) x

/-- The tensor product of sheaves of `𝒪_Y`-modules, followed by the stalk at `x`. -/
abbrev stalkOfTensor :
    SheafOfModules.{u} (structureSheafRing Y) × SheafOfModules.{u} (structureSheafRing Y) ⥤
      ModuleCat.{u} (stalkTensorRing Y x) :=
  Functor.uncurry.obj (Stacks.SheafOfModules.Tensor.sheafTensor ⟨(Y).presheaf, (Y).IsSheaf⟩) ⋙
    AlgebraicGeometry.SheafOfModules.stalkFunctor (structureSheafRing Y) x

/-- The two stalks at `x`, followed by the tensor product of `𝒪_{Y,x}`-modules. -/
abbrev tensorOfStalks :
    SheafOfModules.{u} (structureSheafRing Y) × SheafOfModules.{u} (structureSheafRing Y) ⥤
      ModuleCat.{u} (stalkTensorRing Y x) :=
  (AlgebraicGeometry.SheafOfModules.stalkFunctor (structureSheafRing Y) x).prod
      (AlgebraicGeometry.SheafOfModules.stalkFunctor (structureSheafRing Y) x) ⋙
    Functor.uncurry.obj (MonoidalCategory.curriedTensor (ModuleCat.{u} (stalkTensorRing Y x)))

/-- **The identification of Tag 01CB is natural in both of its arguments at once.**  For
`f : F ⟶ F'` and `g : G ⟶ G'` the square

`(F ⊗ G)_x ⟶ (F' ⊗ G')_x`, `(F ⊗ G)_x ≅ F_x ⊗ G_x`, `F_x ⊗ G_x ⟶ F'_x ⊗ G'_x`

commutes.  This is `stalkTensorIso_naturality_right` at `F'` followed by
`stalkTensorIso_naturality_left` at `G`; the morphism `(f, g)` of the product category acts on the
uncurried tensor product as `(T.map f).app G ≫ (T.obj F').map g`, which is exactly that
factorisation. -/
theorem stalkTensorIso_naturality
    {F F' G G' : SheafOfModules.{u} (structureSheafRing Y)} (f : F ⟶ F') (g : G ⟶ G') :
    (stalkOfTensor Y x).map
          (show ((F, G) : SheafOfModules.{u} (structureSheafRing Y) ×
            SheafOfModules.{u} (structureSheafRing Y)) ⟶ (F', G') from (f, g)) ≫
        (stalkTensorIso Y x F' G').hom =
      (stalkTensorIso Y x F G).hom ≫
        (tensorOfStalks Y x).map
          (show ((F, G) : SheafOfModules.{u} (structureSheafRing Y) ×
            SheafOfModules.{u} (structureSheafRing Y)) ⟶ (F', G') from (f, g)) := by
  have hL : (stalkOfTensor Y x).map
        (show ((F, G) : SheafOfModules.{u} (structureSheafRing Y) ×
          SheafOfModules.{u} (structureSheafRing Y)) ⟶ (F', G') from (f, g)) =
      (AlgebraicGeometry.SheafOfModules.stalkFunctor (structureSheafRing Y) x).map
        (((Stacks.SheafOfModules.Tensor.sheafTensor ⟨(Y).presheaf, (Y).IsSheaf⟩).map f).app G ≫
          ((Stacks.SheafOfModules.Tensor.sheafTensor ⟨(Y).presheaf, (Y).IsSheaf⟩).obj F').map g) :=
    rfl
  have hR : (tensorOfStalks Y x).map
        (show ((F, G) : SheafOfModules.{u} (structureSheafRing Y) ×
          SheafOfModules.{u} (structureSheafRing Y)) ⟶ (F', G') from (f, g)) =
      ((MonoidalCategory.curriedTensor (ModuleCat.{u} (stalkTensorRing Y x))).map
            ((AlgebraicGeometry.SheafOfModules.stalkFunctor (structureSheafRing Y) x).map f)).app
          ((AlgebraicGeometry.SheafOfModules.stalkFunctor (structureSheafRing Y) x).obj G) ≫
        ((MonoidalCategory.curriedTensor (ModuleCat.{u} (stalkTensorRing Y x))).obj
            ((AlgebraicGeometry.SheafOfModules.stalkFunctor
              (structureSheafRing Y) x).obj F')).map
          ((AlgebraicGeometry.SheafOfModules.stalkFunctor (structureSheafRing Y) x).map g) := rfl
  rw [hL, hR]
  refine (congrArg (· ≫ (stalkTensorIso Y x F' G').hom)
    ((AlgebraicGeometry.SheafOfModules.stalkFunctor (structureSheafRing Y) x).map_comp
      (((Stacks.SheafOfModules.Tensor.sheafTensor ⟨(Y).presheaf, (Y).IsSheaf⟩).map f).app G)
      (((Stacks.SheafOfModules.Tensor.sheafTensor ⟨(Y).presheaf, (Y).IsSheaf⟩).obj F').map
        g))).trans ?_
  rw [Category.assoc, stalkTensorIso_naturality_right, ← Category.assoc,
    stalkTensorIso_naturality_left, Category.assoc]

/-- **The stalk functor carries the tensor product of sheaves of modules to the tensor product of
modules, as an isomorphism of bifunctors.**  For a ringed space `Y` and a point `x` of `Y`,

`(− ⊗_{𝒪_Y} −) ⋙ (−)_x ≅ ((−)_x × (−)_x) ⋙ (− ⊗_{𝒪_{Y,x}} −)`

on `Mod(𝒪_Y) × Mod(𝒪_Y)`.  Its component at a pair `(F, G)` is the identification of Tag 01CB,
`stalkTensorIso`. -/
@[ega "0 4.1.5" "special case", ega "0 4.3.3"]
def stalkTensorNatIso : stalkOfTensor Y x ≅ tensorOfStalks Y x :=
  NatIso.ofComponents (fun P => stalkTensorIso Y x P.1 P.2)
    (fun {_ _} f => stalkTensorIso_naturality Y x f.1 f.2)

/-- The component of `stalkTensorNatIso` at a pair is the identification of Tag 01CB. -/
theorem stalkTensorNatIso_hom_app (F G : SheafOfModules.{u} (structureSheafRing Y)) :
    (stalkTensorNatIso Y x).hom.app (F, G) = (stalkTensorIso Y x F G).hom := rfl

end Stacks.SheafOfModules.KFlatStalkCriterion

end

end
