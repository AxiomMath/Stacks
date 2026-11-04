module

public import StacksFrontier.Topology.Sheaves.Cohomology.DerivedPullback.LeftComparisonAlongAComposite
public import
  StacksFrontier.Topology.Sheaves.Cohomology.DerivedPullback.PullbackTensorIsoAlongAComposite
public import StacksFrontier.Topology.Sheaves.Cohomology.DerivedPullback.KFlatPairDescent

/-!
# The pullback-tensor comparison is compatible with composition

Let `f : (X, 𝒪_X) ⟶ (Y, 𝒪_Y)` and `g : (Y, 𝒪_Y) ⟶ (Z, 𝒪_Z)` be morphisms of ringed spaces.
`Stacks.Cohomology.DerivedPullbackTensor.derivedPullbackTensorIso` is the comparison of
Stacks 079U,

`Lf^*(K ⊗^L_{𝒪_Y} L) ≅ Lf^*K ⊗^L_{𝒪_X} Lf^*L`.

This file proves that it is compatible with composition of morphisms of ringed spaces: the
composition isomorphism `Lg^* ⋙ Lf^* ≅ L(f ≫ g)^*` of Stacks 0D5S carries the comparison for
`f ≫ g` to the derived pullback along `f` of the comparison for `g`, followed by the comparison
for `f` and the composition isomorphism in each tensor factor.

## Main results

* `Stacks.Cohomology.DerivedPullbackTensor.derivedPullbackTensorIso_comp`: **Stacks 079U is
  compatible with composition**, as an equality of natural transformations
  `(K ⊗^L L) ↦ Lf^*Lg^*K ⊗^L Lf^*Lg^*L` on `D(𝒪_Z) × D(𝒪_Z)`.
* `Stacks.Cohomology.DerivedPullbackTensor.derivedPullbackTensorIso_comp_app_of_kFlat`: the same
  identity at a pair of K-flat cochain complexes, which is what the previous result descends
  from.  Every comparison in sight is computed by an ordinary total tensor complex there, so the
  identity reduces to the composition law for those; this is
  `Stacks.Cohomology.DerivedPullbackTensor.tensorComparison_comp_of_models` at the three model
  identities.
* `Stacks.Cohomology.DerivedPullbackTensor.map_pullbackTensorComplexNatIso_comp` and
  `Stacks.Cohomology.DerivedPullbackTensor.derivedPullbackNatTrans_naturality_tensorComplex`:
  the two remaining hypotheses of that assembly — the composition law for the comparison of
  total tensor complexes, read in the derived category, and naturality of the comparison
  `Lf^*(QM) ⟶ Q(f^*M)` along it.

## Implementation notes

*Why the two auxiliary lemmas exist.*  Both are immediate: the first is
`Stacks.PullbackTensorComposition.pullbackTensorComplexNatIso_comp` carried along
`DerivedCategory.Q`, the second is a `naturality` field.  They are stated separately because the
assembly below consumes them as hypotheses, and a hypothesis supplied as a named lemma is
*instantiated* from the environment, whereas the same hypothesis written out inline at the
application site has to be *elaborated* from syntax.  The two are not comparable in cost here:
the terms involved are maps between total tensor complexes of pullbacks, and deciding the
definitional equalities their composability needs is what the elaboration time of this
development consists of.  Writing
`(derivedPullbackNatTrans f).naturality ((pullbackTensorComplexNatIso g).hom.app (K, L))` inline
in the assembly puts it over the budget this library is held to; naming it, as
`derivedPullbackNatTrans_naturality_tensorComplex`, brings the assembly well inside it.

*Spelling the comparison of total tensor complexes.*  It has two names,
`Stacks.Cohomology.DerivedPullbackTensor.pullbackTensorComplexNatIso` as an isomorphism of
bifunctors and `Stacks.Cohomology.DerivedPullbackTensor.pullbackTensorComplexIsoOfIsIso` as an
isomorphism of complexes, equal by `rfl`.  Which one a statement uses is not a matter of taste:
the first has its source and target spelled through
`Stacks.Cohomology.DerivedPullbackTensor.totalComplexPair`, the second through
`Stacks.SheafOfModules.Tensor.tensorComplex`, and a composite that mixes the two spellings makes
the elaborator reconcile them.  Everything here is spelled through the bifunctor isomorphism,
which is the spelling the model identities of
`StacksFrontier.Topology.Sheaves.Cohomology.DerivedPullback.PullbackTensorIsoAlongAComposite`
and the naturality statements of
`StacksFrontier.Topology.Sheaves.Cohomology.DerivedPullback.LeftComparisonAlongAComposite`
already use.

*Where the chase is.*  Nowhere here: the diagram chase is
`Stacks.Cohomology.DerivedPullbackTensor.tensorComparison_comp_of_models`, carried out for
arbitrary categories, bifunctors and transformations, and the descent from K-flat
representatives to all of `D(𝒪_Z) × D(𝒪_Z)` is
`Stacks.Cohomology.DerivedPullbackTensor.natTrans_ext_of_kFlat`.  This file only instantiates
them.

## References

* [Stacks Project, Tag 079U](https://stacks.math.columbia.edu/tag/079U)
* [Stacks Project, Tag 0D5S](https://stacks.math.columbia.edu/tag/0D5S)
* [Stacks Project, Tag 01CD](https://stacks.math.columbia.edu/tag/01CD)
* [Stacks Project, Tag 06YS](https://stacks.math.columbia.edu/tag/06YS)
* [Stacks Project, Tag 06YU](https://stacks.math.columbia.edu/tag/06YU)
-/

@[expose] public noncomputable section

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits TopologicalSpace
open Stacks.SheafOfModules.KFlatPullback (kFlat_modulePullback_unconditional)
open scoped CategoryTheory.Prod

namespace Stacks.Cohomology.DerivedPullbackTensor

universe u

/-- **A two-factor composite of images is a three-factor one**, given the identity between the
composites and a respelling of the last factor.  Stated abstractly and applied by unification:
the concrete morphisms are maps between total tensor complexes, and performing the three
`CategoryTheory.Functor.map_comp` rewrites on them would require abstracting such a subterm into
a rewrite motive. -/
lemma map_comp_eq_of_comp_eq {C D : Type*} [Category C] [Category D] (F : C ⥤ D)
    {A B E U V : C} {a : A ⟶ B} {b : B ⟶ E} {p : A ⟶ U} {q : U ⟶ V} {r r' : V ⟶ E}
    (h : p ≫ q ≫ r' = a ≫ b) (hr : r = r') :
    F.map a ≫ F.map b = F.map p ≫ F.map q ≫ F.map r := by
  subst hr
  rw [← F.map_comp, ← F.map_comp, ← F.map_comp, h]

attribute [local instance] HasDerivedCategory.standard

-- The attribute of `PullbackTensorComparison.lean`: the pullback development and the
-- tensor-product development name the structure sheaf of a ringed space differently, and a
-- statement mixing them — which every statement here does — is not type-correct at `implicit`
-- transparency unless both spellings are unfolded there.  `structureSheafRing` is
-- `@[instance_reducible]` and so already is; its reduct stops at an explicit-constructor
-- projection, and the two Mathlib definitions bridging that to `(sheafCompose _ _).obj X.sheaf`
-- are deliberately NOT unfolded here — this file sits at the elaboration budget, and granting
-- them costs more than the one declaration below gains.
attribute [local implicit_reducible] StacksDraft.KFlat.modulePullback

section Transport

variable {X Y Z : RingedSpace.{u, u}} (f : X ⟶ Y) (g : Y ⟶ Z)
  [HasSheafify (Opens.grothendieckTopology X.carrier) AddCommGrpCat.{u}]
  [(Opens.grothendieckTopology X.carrier).WEqualsLocallyBijective AddCommGrpCat.{u}]

/-- **The composition law for the comparison of total tensor complexes, read in the derived
category.**  `Stacks.PullbackTensorComposition.pullbackTensorComplexNatIso_comp` says that
`f^*Tot(K ⊗ L) ≅ Tot(f^*K ⊗ f^*L)` is compatible with composition; this is that identity carried
along `DerivedCategory.Q`, with the tensor action on the pair of composition isomorphisms
`f^*g^* ≅ (f ≫ g)^*` spelled through
`Stacks.Cohomology.DerivedPullbackTensor.totalComplexPair` rather than through
`CategoryTheory.HomologicalComplex.mapBifunctorMap`.

That is the spelling in which naturality of the canonical map to the ordinary total tensor
complex is available (`derivedToTensorNatTrans_naturality_prod`), and so the spelling the
assembly below needs; the two differ by
`Stacks.Cohomology.DerivedPullbackTensor.totalComplexPair_map`. -/
theorem map_pullbackTensorComplexNatIso_comp
    (K L : CochainComplex (AlgebraicGeometry.RingedSpace.KFlatDerivedPullback.Modules Z) ℤ) :
    DerivedCategory.Q.map
          ((Stacks.PullbackTensorComposition.pullbackComplexCompIso f g).hom.app
            ((totalComplexPair
              (Stacks.SheafOfModules.Tensor.sheafTensor Z.sheaf)).obj (K, L))) ≫
        DerivedCategory.Q.map ((pullbackTensorComplexNatIso (f ≫ g)).hom.app (K, L)) =
      DerivedCategory.Q.map
          ((pullbackComplex f).map ((pullbackTensorComplexNatIso g).hom.app (K, L))) ≫
        DerivedCategory.Q.map ((pullbackTensorComplexNatIso f).hom.app
            ((pullbackComplex g).obj K, (pullbackComplex g).obj L)) ≫
          DerivedCategory.Q.map
            ((totalComplexPair (Stacks.SheafOfModules.Tensor.sheafTensor X.sheaf)).map
              ((Stacks.PullbackTensorComposition.pullbackComplexCompIso f g).hom.app K ×ₘ
                (Stacks.PullbackTensorComposition.pullbackComplexCompIso f g).hom.app L)) :=
  map_comp_eq_of_comp_eq DerivedCategory.Q
    (Stacks.PullbackTensorComposition.pullbackTensorComplexNatIso_comp f g K L)
    (totalComplexPair_map _ _ _)

end Transport

section Naturality

variable {X Y Z : RingedSpace.{u, u}} (f : X ⟶ Y) (g : Y ⟶ Z)
  [HasSheafify (Opens.grothendieckTopology X.carrier) AddCommGrpCat.{u}]
  [(Opens.grothendieckTopology X.carrier).WEqualsLocallyBijective AddCommGrpCat.{u}]
  [HasSheafify (Opens.grothendieckTopology Y.carrier) AddCommGrpCat.{u}]
  [(Opens.grothendieckTopology Y.carrier).WEqualsLocallyBijective AddCommGrpCat.{u}]

/-- **The comparison `Lf^*(QM) ⟶ Q(f^*M)` is natural along the comparison of total tensor
complexes for `g`.**  This is the `naturality` field of
`Stacks.Cohomology.DerivedPullbackTensor.derivedPullbackNatTrans` at
`g^*Tot(K ⊗_{𝒪_Z} L) ⟶ Tot(g^*K ⊗_{𝒪_Y} g^*L)`, with the two functor compositions reduced.  It
is recorded as a lemma because the assembly below takes it as a hypothesis, and a hypothesis
read off the environment costs nothing beyond its instantiation. -/
theorem derivedPullbackNatTrans_naturality_tensorComplex
    (K L : CochainComplex (AlgebraicGeometry.RingedSpace.KFlatDerivedPullback.Modules Z) ℤ) :
    (Stacks.Cohomology.DerivedAdjunctionOnRingedSpaces.derivedPullback f).map
          (DerivedCategory.Q.map ((pullbackTensorComplexNatIso g).hom.app (K, L))) ≫
        (derivedPullbackNatTrans f).app
          ((totalComplexPair (Stacks.SheafOfModules.Tensor.sheafTensor Y.sheaf)).obj
            ((pullbackComplex g).obj K, (pullbackComplex g).obj L)) =
      (derivedPullbackNatTrans f).app
          ((pullbackComplex g).obj
            ((totalComplexPair (Stacks.SheafOfModules.Tensor.sheafTensor Z.sheaf)).obj (K, L))) ≫
        DerivedCategory.Q.map
          ((pullbackComplex f).map ((pullbackTensorComplexNatIso g).hom.app (K, L))) :=
  (derivedPullbackNatTrans f).naturality _

end Naturality

section Composite

variable {X Y Z : RingedSpace.{u, u}} (f : X ⟶ Y) (g : Y ⟶ Z)
  [HasSheafify (Opens.grothendieckTopology X.carrier) AddCommGrpCat.{u}]
  [(Opens.grothendieckTopology X.carrier).WEqualsLocallyBijective AddCommGrpCat.{u}]
  [HasSheafify (Opens.grothendieckTopology Y.carrier) AddCommGrpCat.{u}]
  [(Opens.grothendieckTopology Y.carrier).WEqualsLocallyBijective AddCommGrpCat.{u}]
  [HasSheafify (Opens.grothendieckTopology Z.carrier) AddCommGrpCat.{u}]
  [(Opens.grothendieckTopology Z.carrier).WEqualsLocallyBijective AddCommGrpCat.{u}]

/-- **Stacks 079U is compatible with composition, at a pair of K-flat complexes.**  For K-flat
cochain complexes `K, L` of `𝒪_Z`-modules, the composition isomorphism
`Lg^* ⋙ Lf^* ≅ L(f ≫ g)^*` of Stacks 0D5S, followed by the comparison

`L(f ≫ g)^*(QK ⊗^L_{𝒪_Z} QL) ≅ L(f ≫ g)^*(QK) ⊗^L_{𝒪_X} L(f ≫ g)^*(QL)`

of Stacks 079U, is the derived pullback along `f` of the comparison for `g`, followed by the
comparison for `f` and by the composition isomorphism in each tensor factor.

Each of the three comparisons is computed on K-flat representatives by the ordinary total tensor
complex — `derivedPullbackTensorIso_hom_app_comp_derivedToTensor` — so the identity follows from
the composition law for those models, which is what
`Stacks.Cohomology.DerivedPullbackTensor.tensorComparison_comp_of_models` chases.  Its remaining
hypotheses are the two monomorphisms it cancels, the composition law for
`Stacks.Cohomology.DerivedPullbackTensor.derivedPullbackNatTrans` in each tensor factor and at
the total tensor complex, naturality of the canonical map to the ordinary total tensor complex
along the composition isomorphism on complexes, and the two lemmas above.  The degreewise
pullbacks `g^*K`, `g^*L` are K-flat by Stacks 06YC, which is what lets the model identity for
`f` be used at them. -/
theorem derivedPullbackTensorIso_comp_app_of_kFlat
    (K L : CochainComplex (AlgebraicGeometry.RingedSpace.KFlatDerivedPullback.Modules Z) ℤ)
    (hK : AlgebraicGeometry.RingedSpace.KFlatDerivedPullback.KFlat Z K)
    (hL : AlgebraicGeometry.RingedSpace.KFlatDerivedPullback.KFlat Z L) :
    (Stacks.DerivedPullback.Composition.derivedPullbackCompIsoCanonical f g).hom.app
          ((Functor.uncurry.obj
              (Stacks.DerivedTensor.RingedSite.derivedTensorProductFunctor Z.sheaf)).obj
            (DerivedCategory.Q.obj K, DerivedCategory.Q.obj L)) ≫
        (derivedPullbackTensorIso (f ≫ g)).hom.app
          (DerivedCategory.Q.obj K, DerivedCategory.Q.obj L) =
      (Stacks.Cohomology.DerivedAdjunctionOnRingedSpaces.derivedPullback f).map
          ((derivedPullbackTensorIso g).hom.app
            (DerivedCategory.Q.obj K, DerivedCategory.Q.obj L)) ≫
        (derivedPullbackTensorIso f).hom.app
            ((Stacks.Cohomology.DerivedAdjunctionOnRingedSpaces.derivedPullback g).obj
                (DerivedCategory.Q.obj K),
              (Stacks.Cohomology.DerivedAdjunctionOnRingedSpaces.derivedPullback g).obj
                (DerivedCategory.Q.obj L)) ≫
          (Functor.uncurry.obj
                (Stacks.DerivedTensor.RingedSite.derivedTensorProductFunctor X.sheaf)).map
              ((Stacks.DerivedPullback.Composition.derivedPullbackCompIsoCanonical f g).hom.app
                  (DerivedCategory.Q.obj K) ×ₘ
                (Stacks.DerivedPullback.Composition.derivedPullbackCompIsoCanonical f g).hom.app
                  (DerivedCategory.Q.obj L)) := by
  -- The assembled term is handed over through a `have` rather than written as the body: that
  -- computes its type from its arguments and then checks the two against each other once,
  -- where elaborating it against the goal unifies the two side by side and does not finish
  -- inside the heartbeat budget.  The three model identities below are ascribed `: _` for the
  -- same reason one step down.  Each is an equality between composites of maps out of a total
  -- tensor complex, and the slot it fills in the chase is only partly determined when it is
  -- reached; propagating that half-solved slot inward makes the elaborator decide the
  -- definitional equalities of the whole composite argument by argument, whereas `: _`
  -- elaborates the identity on its own — its type is fully determined by `f`, `g`, `K`, `L` —
  -- and compares the two finished terms once.
  have h := tensorComparison_comp_of_models
    (Stacks.DerivedPullback.Composition.derivedPullbackCompIsoCanonical f g).hom
    (derivedPullbackTensorIso g).hom (derivedPullbackTensorIso f).hom
    (derivedPullbackTensorIso (f ≫ g)).hom
    (DerivedCategory.Q.obj K) (DerivedCategory.Q.obj L)
    (mono_derivedTensor_map_derivedPullbackNatTrans_app f g K L hK hL)
    (mono_derivedToTensorNatTrans_app_pullbackComplex f g K L hK hL)
    (derivedPullbackCompIsoCanonical_hom_app_comp_derivedPullbackNatTrans f g K)
    (derivedPullbackCompIsoCanonical_hom_app_comp_derivedPullbackNatTrans f g L)
    (derivedPullbackCompIsoCanonical_hom_app_comp_derivedPullbackNatTrans f g
      ((totalComplexPair (Stacks.SheafOfModules.Tensor.sheafTensor Z.sheaf)).obj (K, L)))
    (derivedPullbackNatTrans_naturality_tensorComplex f g K L)
    (derivedToTensorNatTrans_naturality_prod X
      ((Stacks.PullbackTensorComposition.pullbackComplexCompIso f g).hom.app K)
      ((Stacks.PullbackTensorComposition.pullbackComplexCompIso f g).hom.app L))
    (derivedPullbackTensorIso_hom_app_comp_derivedToTensor g K L hK hL : _)
    (derivedPullbackTensorIso_hom_app_comp_derivedToTensor f ((pullbackComplex g).obj K)
      ((pullbackComplex g).obj L) (kFlat_modulePullback_unconditional g K hK)
      (kFlat_modulePullback_unconditional g L hL) : _)
    (derivedPullbackTensorIso_hom_app_comp_derivedToTensor (f ≫ g) K L hK hL : _)
    (map_pullbackTensorComplexNatIso_comp f g K L)
  exact h

/-- **Stacks 079U is compatible with composition of morphisms of ringed spaces.**  For
composable morphisms of ringed spaces `f : X ⟶ Y` and `g : Y ⟶ Z`, the composition isomorphism
`Lg^* ⋙ Lf^* ≅ L(f ≫ g)^*` of Stacks 0D5S, followed by the comparison

`L(f ≫ g)^*(K ⊗^L_{𝒪_Z} L) ≅ L(f ≫ g)^*K ⊗^L_{𝒪_X} L(f ≫ g)^*L`

of Stacks 079U, is the derived pullback along `f` of the comparison for `g`, followed by the
comparison for `f` and by the composition isomorphism in each tensor factor — as an identity of
natural transformations on `D(𝒪_Z) × D(𝒪_Z)`, with no hypothesis on the objects.

Both sides are transformations out of `(K, L) ↦ Lf^*Lg^*(K ⊗^L_{𝒪_Z} L)`, and `D(𝒪_Z)` is the
localization of the K-flat objects of the homotopy category at the quasi-isomorphisms
(Stacks 06YS), so they agree as soon as they agree at a pair of K-flat representatives:
`derivedPullbackTensorIso_comp_app_of_kFlat` through
`Stacks.Cohomology.DerivedPullbackTensor.natTrans_ext_of_kFlat`. -/
/- No `stacks` attribute: Stacks 079U is covered, unclaused, by
`Stacks.Cohomology.DerivedPullbackTensor.derivedPullbackTensorIso`
(`DerivedPullback/PullbackTensorComparison.lean:494`), and Stacks 0D5S by
`Stacks.DerivedPullback.Composition.isIso_derivedPullbackCompComparisonCanonical`
(`DerivedPullback/CompositionUnconditional.lean:152`). A bare attribute claims the whole tag,
so a clause here would assert full and partial coverage of the same tag at once. -/
theorem derivedPullbackTensorIso_comp :
    Functor.whiskerLeft
          (Functor.uncurry.obj
            (Stacks.DerivedTensor.RingedSite.derivedTensorProductFunctor Z.sheaf))
          (Stacks.DerivedPullback.Composition.derivedPullbackCompIsoCanonical f g).hom ≫
        (derivedPullbackTensorIso (f ≫ g)).hom =
      Functor.whiskerRight (derivedPullbackTensorIso g).hom
          (Stacks.Cohomology.DerivedAdjunctionOnRingedSpaces.derivedPullback f) ≫
        Functor.whiskerLeft
            ((Stacks.Cohomology.DerivedAdjunctionOnRingedSpaces.derivedPullback g).prod
              (Stacks.Cohomology.DerivedAdjunctionOnRingedSpaces.derivedPullback g))
            (derivedPullbackTensorIso f).hom ≫
          Functor.whiskerRight
            (NatTrans.prod
              (Stacks.DerivedPullback.Composition.derivedPullbackCompIsoCanonical f g).hom
              (Stacks.DerivedPullback.Composition.derivedPullbackCompIsoCanonical f g).hom)
            (Functor.uncurry.obj
              (Stacks.DerivedTensor.RingedSite.derivedTensorProductFunctor X.sheaf)) :=
  natTrans_ext_of_kFlat Z _ _ fun K L hK hL =>
    derivedPullbackTensorIso_comp_app_of_kFlat f g K L hK hL

end Composite

end Stacks.Cohomology.DerivedPullbackTensor

end
