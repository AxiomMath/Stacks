module

public import StacksFrontier.CategoryTheory.Sites.Cohomology.DerivedTensor.TotalComplexNaturality
public import StacksFrontier.CategoryTheory.Sites.Cohomology.InternalHom.CompositionRestriction
public import StacksFrontier.CategoryTheory.Sites.Cohomology.InternalHom.DerivedTensorDual
public import StacksFrontier.CategoryTheory.Sites.Cohomology.StrictlyPerfect.CompositionStructureSheafMiddle
public import StacksFrontier.Topology.Sheaves.Cohomology.InternalHom.DerivedCompositionModels
public import StacksFrontier.Topology.Sheaves.Cohomology.InternalHom.StrictlyPerfectHomKFlatSite
public import StacksFrontier.CategoryTheory.Sites.Cohomology.InternalHom.EvaluationPerfect
public import StacksFrontier.Topology.Sheaves.Cohomology.InternalHomEvaluation.EvaluationModels
import StacksCore.Tactic.EgaSgaAttribute

/-!
# The canonical map `M ⊗^L K^∨ ⟶ RSheafHom(K, M)` at a perfect `K`, on a ringed site

Let `X` be a ringed site and let `K`, `M` be objects of `D(O)` with `K` **perfect**. The canonical
map of Stacks 08JD

`Φ : M ⊗^L_O K^∨ ⟶ RSheafHom(K, M)`

is an isomorphism. This is the third assertion of **Stacks 08DQ**, and
`isIso_derivedTensorDualToSheafHom_of_isPerfect` below proves it with `X.IsPerfect K` as its only
hypothesis. Nothing is assumed of `M`.

## Main results

* `AlgebraicGeometry.RingedSite.isIso_Q_map_tensorTotalMap_left_of_isKFlat_right`: tensoring a
  quasi-isomorphism on the right with a K-flat complex keeps it one. This is the companion of
  `AlgebraicGeometry.RingedSite.isIso_Q_map_tensorTotalMap_right` on the other side, read off the
  *right* K-flat comparison of Stacks 06YU, which asks nothing of the left factor.
* `AlgebraicGeometry.RingedSite.restrictComplexStructureSheafIsoAt`: the restriction of the
  structure sheaf complex to a slice is the structure sheaf complex of the slice.
* `AlgebraicGeometry.RingedSite.tensorTotalMap_comp_compositionMap_eq` and
  `AlgebraicGeometry.RingedSite.compositionMapOfModels_restrict_square`: the restriction square
  for the complex-level model of the composition morphism of Stacks 0A98.
* `AlgebraicGeometry.RingedSite.isIso_derivedSheafHomComposition_of_isFiniteFreeSummand`: the
  **globally strictly perfect case**, at a ringed site and with no slice in sight.
* `..._of_isStrictlyPerfect`, the local step: see
  `quasiIso_restrictComplexMap_compositionMapOfModels_of_isStrictlyPerfect` below.
* `AlgebraicGeometry.RingedSite.isIso_derivedSheafHomComposition_structureSheaf_of_isPerfect`:
  the composition morphism of Stacks 0A98 at intermediate object the structure sheaf is
  invertible at a perfect source.
* `AlgebraicGeometry.RingedSite.isIso_derivedTensorDualToSheafHom_of_isPerfect`: **Stacks 08DQ,
  third assertion.**

## The shape of the argument

Invertibility of the composition morphism is replaced, once and for all, by quasi-isomorphy of a
morphism of *complexes* — `AlgebraicGeometry.RingedSite.compositionMapOfModels`, the composition
morphism of Stacks 0A91 precomposed in the right tensor factor with a K-flat model of
`RSheafHom(K, J)` — at one choice of models, by
`isIso_derivedSheafHomComposition_of_coversTop` of
`StacksFrontier.Topology.Sheaves.Cohomology.InternalHom.DerivedCompositionModels`. That bypasses any
compatibility of the *derived* morphism with restriction to a slice, which the library does not
have; quasi-isomorphy of a morphism of complexes is local on the site, so it may be checked over
the members of the covering furnished by perfectness. This is the route
`StacksFrontier.CategoryTheory.Sites.Cohomology.InternalHom.EvaluationPerfect` takes for the
sibling assertion Stacks 0G40, transposed to composition.

Over a member `U` of the covering the restriction square
`compositionMapOfModels_restrict_square` identifies the restricted morphism with the one formed
over `U`, up to three invertible flanking morphisms: the comparison
`tensorTotalOverIso` of the total tensor complex, and the comparisons of Stacks 08JB for the
internal Hom complexes of the pairs `(J, I)` and `(K, I)`. Reading the criterion backwards over
`U` turns the restricted morphism into invertibility of derived composition over `U` at the
restricted models, and the strictly perfect model `P` of `K|_U` is substituted for `K|_U` there by
the transport of invertibility along isomorphisms of the three objects.

The criterion is then read *forwards* over `U` at `P`, with a different K-flat model of the right
tensor factor: the dual `SheafHom(P, O|_U[0])`, which is K-flat by the ringed-site form of
Stacks 0GM5 (`isKFlat_sheafHomComplex_of_isKFlat` of
`StacksFrontier.Topology.Sheaves.Cohomology.InternalHom.StrictlyPerfectHomKFlatSite`) and which maps
quasi-isomorphically to `SheafHom(P, J|_U)` because `P` is strictly perfect. Dinaturality of the
composition morphism in the intermediate object then moves the augmentation `O|_U[0] ⟶ J|_U` out
of the right tensor factor and into the left one, leaving the composition morphism at intermediate
object the structure sheaf itself, which is a quasi-isomorphism at a strictly perfect source by
`compositionMap_structureSheafMiddle_quasiIso_of_isFiniteFreeSummand` of
`StacksFrontier.CategoryTheory.Sites.Cohomology.StrictlyPerfect.CompositionStructureSheafMiddle`.

That last move is why `isIso_Q_map_tensorTotalMap_left_of_isKFlat_right` is needed and why the
existing one-sided statements do not suffice: dinaturality lands the quasi-isomorphism in the
*left* tensor slot, with the K-flat complex `SheafHom(P, O|_U[0])` on the right, and
`isIso_Q_map_tensorTotalMap_right` has the K-flat factor on the left while
`isIso_Q_map_tensorTotalMap_left` wants both left complexes K-flat — here they are internal Hom
complexes into a K-injective complex, and neither is.

## Implementation notes

The intermediate complex is a K-injective *resolution* `J` of the structure sheaf complex rather
than the chosen K-injective model, because the local step needs an actual chain map
`O[0] ⟶ J` and not merely an isomorphism of their classes: the augmentation is what dinaturality
absorbs.

`restrictComplexStructureSheafIsoAt` is stated here rather than reused from
`StacksFrontier.CategoryTheory.Sites.Cohomology.Perfect.Duals`, where the same isomorphism is
`restrictStructureSheafComplexIso`: that file is pinned to `RingedSite.{0, 0, 0}` because it joins
the derived internal Hom cluster to the perfectness cluster through declarations available only
there, and this one is needed at the diagonal `RingedSite.{u, u, u}` of Section 34.

## References

* [Stacks Project, Lemma 20.50.5 (Tag 08DQ)](https://stacks.math.columbia.edu/tag/08DQ)
* [Stacks Project, Tag 08JD](https://stacks.math.columbia.edu/tag/08JD)
* [Stacks Project, Tag 0A98](https://stacks.math.columbia.edu/tag/0A98)
* [Stacks Project, Tag 0A91](https://stacks.math.columbia.edu/tag/0A91)
* [Stacks Project, Tag 0GM5](https://stacks.math.columbia.edu/tag/0GM5)
* [Stacks Project, Tag 08JB](https://stacks.math.columbia.edu/tag/08JB)
* [Stacks Project, Lemma 20.26.6 (Tag 06YU)](https://stacks.math.columbia.edu/tag/06YU)
* [Stacks Project, Definition 20.48.1 (Tag 08G5)](https://stacks.math.columbia.edu/tag/08G5)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry Opposite
open Stacks.SheafOfModules.Tensor

universe u

namespace AlgebraicGeometry.RingedSite

attribute [local instance] HasDerivedCategory.standard
attribute [local instance] ringSheafSectionsCommRing presheafOfModulesMonoidalCategory
  curriedTensorPreservesZeroMorphisms curriedTensorObjPreservesZeroMorphisms

variable (X : RingedSite.{u, u, u})
  [HasSheafify X.J AddCommGrpCat.{u}]
  [X.J.WEqualsLocallyBijective AddCommGrpCat.{u}]
  [∀ V : X.C, HasSheafify (X.J.over V) AddCommGrpCat.{u}]
  [∀ V : X.C, (X.J.over V).WEqualsLocallyBijective AddCommGrpCat.{u}]
  [∀ V : X.C, (X.J.over V).HasSheafCompose (forget₂ RingCat.{u} AddCommGrpCat.{u})]
  [∀ V : X.C, (X.J.over V).HasSheafCompose (forget₂ CommRingCat.{u} RingCat.{u})]
  [(sheafTensor.{u, u, u, u, u} X.O).Additive]
  [∀ A, ((sheafTensor.{u, u, u, u, u} X.O).obj A).Additive]
  [∀ (K₁ K₂ : CochainComplex
      (SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf.{u, u, u} X.O)) ℤ),
    HomologicalComplex.HasMapBifunctor K₁ K₂ (sheafTensor.{u, u, u, u, u} X.O) (ComplexShape.up ℤ)]

section Kit

omit [∀ V : X.C, HasSheafify (X.J.over V) AddCommGrpCat.{u}]
  [∀ V : X.C, (X.J.over V).WEqualsLocallyBijective AddCommGrpCat.{u}]
  [∀ V : X.C, (X.J.over V).HasSheafCompose (forget₂ RingCat.{u} AddCommGrpCat.{u})]
  [∀ V : X.C, (X.J.over V).HasSheafCompose (forget₂ CommRingCat.{u} RingCat.{u})] in
/-- **The right K-flat comparison of Stacks 06YU, read on total complexes, is natural in the
arbitrary left complex.** No K-flatness is asked of either left complex: that is the point of the
right-hand one-sided comparison, which is what makes this applicable to the internal Hom
complexes into a K-injective complex that the composition morphism of Stacks 0A98 puts in its
left tensor factor. -/
theorem comparisonRight_tensorTotal_naturality_left
    {A A₀ Z : CochainComplex (SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf X.O)) ℤ}
    (c : A ⟶ A₀)
    (hZ : Stacks.SheafOfModules.IsKFlat X.O Z) :
    ((Stacks.SheafOfModules.derivedTensorProductFunctor X).map
            (DerivedCategory.Q.map c)).app (DerivedCategory.Q.obj Z) ≫
        ((Stacks.SheafOfModules.canonicalDerivedTensorProduct X).comparisonRight A₀ Z hZ).hom ≫
          DerivedCategory.Q.map (tensorTotalIsoTensorComplex X A₀ Z).inv =
      ((Stacks.SheafOfModules.canonicalDerivedTensorProduct X).comparisonRight A Z hZ).hom ≫
        DerivedCategory.Q.map (tensorTotalIsoTensorComplex X A Z).inv ≫
        DerivedCategory.Q.map (tensorTotalMap X c (𝟙 Z)) := by
  have sq3 : ((Stacks.SheafOfModules.derivedTensorProductFunctor X).map
            (DerivedCategory.Q.map c)).app (DerivedCategory.Q.obj Z) ≫
        ((Stacks.SheafOfModules.canonicalDerivedTensorProduct X).comparisonRight A₀ Z hZ).hom =
      ((Stacks.SheafOfModules.canonicalDerivedTensorProduct X).comparisonRight A Z hZ).hom ≫
        DerivedCategory.Q.map (HomologicalComplex.mapBifunctorMap c (𝟙 Z)
          (Stacks.SheafOfModules.Tensor.sheafTensor.{u, u, u, u, u} X.O) (ComplexShape.up ℤ)) := by
    simpa using
      (Stacks.SheafOfModules.canonicalDerivedTensorProduct X).comparisonRight_naturality
        c (𝟙 Z) hZ hZ
  have sq4 : DerivedCategory.Q.map (HomologicalComplex.mapBifunctorMap c (𝟙 Z)
          (Stacks.SheafOfModules.Tensor.sheafTensor.{u, u, u, u, u} X.O) (ComplexShape.up ℤ)) ≫
        DerivedCategory.Q.map (tensorTotalIsoTensorComplex X A₀ Z).inv =
      DerivedCategory.Q.map (tensorTotalIsoTensorComplex X A Z).inv ≫
        DerivedCategory.Q.map (tensorTotalMap X c (𝟙 Z)) := by
    refine Eq.trans (Eq.trans (DerivedCategory.Q.map_comp _ _).symm ?_)
      (DerivedCategory.Q.map_comp _ _)
    exact congrArg DerivedCategory.Q.map
      (tensorTotalIsoTensorComplex_naturality X c (𝟙 Z)).symm
  exact CategoryTheory.square_comp' sq3 sq4

omit [∀ V : X.C, HasSheafify (X.J.over V) AddCommGrpCat.{u}]
  [∀ V : X.C, (X.J.over V).WEqualsLocallyBijective AddCommGrpCat.{u}]
  [∀ V : X.C, (X.J.over V).HasSheafCompose (forget₂ RingCat.{u} AddCommGrpCat.{u})]
  [∀ V : X.C, (X.J.over V).HasSheafCompose (forget₂ CommRingCat.{u} RingCat.{u})] in
/-- **Tensoring on the right with a K-flat complex preserves quasi-isomorphy in the left slot.**
The companion of `AlgebraicGeometry.RingedSite.isIso_Q_map_tensorTotalMap_right`, which has the
K-flat factor on the left, and the statement that
`AlgebraicGeometry.RingedSite.isIso_Q_map_tensorTotalMap_left` does *not* give: that one asks
both left complexes to be K-flat, because it is read off the left-hand comparison. -/
theorem isIso_Q_map_tensorTotalMap_left_of_isKFlat_right
    {A A₀ Z : CochainComplex (SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf X.O)) ℤ}
    (c : A ⟶ A₀)
    (hc : IsIso (DerivedCategory.Q.map c))
    (hZ : Stacks.SheafOfModules.IsKFlat X.O Z) :
    IsIso (DerivedCategory.Q.map (tensorTotalMap X c (𝟙 Z))) := by
  have := hc
  have h := comparisonRight_tensorTotal_naturality_left X c hZ
  have h2 : IsIso (DerivedCategory.Q.map (tensorTotalIsoTensorComplex X A Z).inv ≫
      DerivedCategory.Q.map (tensorTotalMap X c (𝟙 Z))) := by
    refine IsIso.of_isIso_fac_left
      (f := ((Stacks.SheafOfModules.canonicalDerivedTensorProduct X).comparisonRight A Z hZ).hom)
      (h := ((Stacks.SheafOfModules.derivedTensorProductFunctor X).map
          (DerivedCategory.Q.map c)).app (DerivedCategory.Q.obj Z) ≫
        (((Stacks.SheafOfModules.canonicalDerivedTensorProduct X).comparisonRight A₀ Z hZ).hom ≫
        DerivedCategory.Q.map (tensorTotalIsoTensorComplex X A₀ Z).inv)) (Eq.symm ?_)
    simpa using h
  exact IsIso.of_isIso_comp_left
    (DerivedCategory.Q.map (tensorTotalIsoTensorComplex X A Z).inv) _

/-- **The restriction of the structure sheaf complex to the slice over `U` is the structure sheaf
complex of the slice.** Restriction is additive and carries the structure sheaf to the structure
sheaf, so it commutes with placing a module in degree zero.

This is the statement of `AlgebraicGeometry.RingedSite.restrictStructureSheafComplexIso` at the
diagonal `RingedSite.{u, u, u}`; that one is pinned to `RingedSite.{0, 0, 0}` by the file it
lives in. -/
def restrictComplexStructureSheafIsoAt (U : X.C) :
    restrictComplex X (structureSheafComplex X) U ≅ structureSheafComplex (X.over U) :=
  (HomologicalComplex.singleMapHomologicalComplex
    (SheafOfModules.overFunctor.{u} (Stacks.SheafOfModules.Tensor.ringSheaf X.O) U)
    (ComplexShape.up ℤ) 0).app _

omit [∀ V : X.C, HasSheafify (X.J.over V) AddCommGrpCat.{u}]
  [∀ V : X.C, (X.J.over V).WEqualsLocallyBijective AddCommGrpCat.{u}]
  [∀ V : X.C, (X.J.over V).HasSheafCompose (forget₂ RingCat.{u} AddCommGrpCat.{u})]
  [∀ V : X.C, (X.J.over V).HasSheafCompose (forget₂ CommRingCat.{u} RingCat.{u})]
  [HasSheafify X.J AddCommGrpCat.{u}]
  [X.J.WEqualsLocallyBijective AddCommGrpCat.{u}]
  [(sheafTensor.{u, u, u, u, u} X.O).Additive]
  [∀ A, ((sheafTensor.{u, u, u, u, u} X.O).obj A).Additive]
  [∀ (K₁ K₂ : CochainComplex
      (SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf.{u, u, u} X.O)) ℤ),
    HomologicalComplex.HasMapBifunctor K₁ K₂ (sheafTensor.{u, u, u, u, u} X.O)
      (ComplexShape.up ℤ)] in
/-- **A morphism in the left tensor factor splits off the complex-level model of the composition
morphism.** Both sides send a homogeneous local pure tensor to the composite of the two images,
and the identity is pure bifunctoriality of `tensorTotalMap`: it is what lets the flanking
comparison of the left tensor factor be separated from
`AlgebraicGeometry.RingedSite.compositionMapOfModels`. -/
theorem tensorTotalMap_comp_compositionMap_eq
    (K J I : CochainComplex (SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf X.O)) ℤ)
    {W H : CochainComplex (SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf X.O)) ℤ}
    (g : W ⟶ (sheafHomComplex X J I).obj) (f : H ⟶ (sheafHomComplex X K J).obj) :
    tensorTotalMap X g f ≫ compositionMap X K J I =
      tensorTotalMap X g (𝟙 H) ≫ compositionMapOfModels X K J I f := by
  rw [compositionMapOfModels, ← Category.assoc, tensorTotalMap_comp, Category.comp_id,
    Category.id_comp]

omit [∀ V : X.C, HasSheafify (X.J.over V) AddCommGrpCat.{u}]
  [∀ V : X.C, (X.J.over V).WEqualsLocallyBijective AddCommGrpCat.{u}]
  [∀ V : X.C, (X.J.over V).HasSheafCompose (forget₂ RingCat.{u} AddCommGrpCat.{u})]
  [∀ V : X.C, (X.J.over V).HasSheafCompose (forget₂ CommRingCat.{u} RingCat.{u})] in
/-- **The globally strictly perfect case of the third assertion of Stacks 08DQ**, at the level of
the composition morphism of Stacks 0A98 and with no slice in sight. Let `P` have only finitely
many nonzero terms, each a direct summand of a finite free `O`-module, let `I` be K-injective and
let `aug : O[0] ⟶ J` be a quasi-isomorphism into a K-injective `J`. Then

`RSheafHom(QJ, QI) ⊗^L_O RSheafHom(QP, QJ) ⟶ RSheafHom(QP, QI)`

is invertible.

The invertibility criterion is applied at the dual `SheafHom(P, O[0])` as the K-flat model of the
right tensor factor: it is K-flat by the ringed-site form of Stacks 0GM5, and it maps
quasi-isomorphically to `SheafHom(P, J)` because `P` is strictly perfect. Dinaturality of the
composition morphism in the intermediate object then replaces `J` by `O[0]`, moving the
augmentation into the left tensor factor, where tensoring with the K-flat dual keeps it a
quasi-isomorphism; what is left is the composition morphism at intermediate object the structure
sheaf, a quasi-isomorphism at a strictly perfect source. -/
theorem isIso_derivedSheafHomComposition_of_isFiniteFreeSummand
    (T : Stacks.SheafOfModules.DerivedTensorProduct X) (Hd : DerivedInternalHom X)
    (P J I : CochainComplex (SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf X.O)) ℤ)
    [J.IsKInjective] [I.IsKInjective]
    (hbdd : {i : ℤ | ¬ IsZero (P.X i)}.Finite)
    (hterm : ∀ i, IsFiniteFreeSummand X (P.X i))
    (aug : structureSheafComplex X ⟶ J) (haug : QuasiIso aug) :
    IsIso (derivedSheafHomComposition X T Hd (DerivedCategory.Q.obj P)
      (DerivedCategory.Q.obj J) (DerivedCategory.Q.obj I)) := by
  have := haug
  have hdualkf : Stacks.SheafOfModules.IsKFlat X.O
      (sheafHomComplex X P (structureSheafComplex X)).obj :=
    isKFlat_sheafHomComplex_of_isKFlat X P (structureSheafComplex X) hbdd hterm
      (Stacks.SheafOfModules.isKFlat_single_unit X.O)
  have hmodq : QuasiIso (homMap X (𝟙 P) aug) :=
    homMap_quasiIso_of_isFiniteFreeSummand X aug P hbdd hterm
  refine (isIso_derivedSheafHomComposition_iff_quasiIso_ofModels X T Hd P J I
    (sheafHomComplex X P (structureSheafComplex X)).obj hdualkf (homMap X (𝟙 P) aug)
    inferInstance).2 ?_
  have hdin : compositionMapOfModels X P J I (homMap X (𝟙 P) aug) =
      tensorTotalMap X (homMap X aug (𝟙 I))
          (𝟙 (sheafHomComplex X P (structureSheafComplex X)).obj) ≫
        compositionMap X P (structureSheafComplex X) I :=
    compositionMap_dinatural_middle X P aug I
  have h2 : QuasiIso (tensorTotalMap X (homMap X aug (𝟙 I))
      (𝟙 (sheafHomComplex X P (structureSheafComplex X)).obj)) :=
    (DerivedCategory.isIso_Q_map_iff_quasiIso _ _).1
      (isIso_Q_map_tensorTotalMap_left_of_isKFlat_right X (homMap X aug (𝟙 I))
        ((DerivedCategory.isIso_Q_map_iff_quasiIso _ _).2 (homMap_quasiIso X (𝟙 I) aug)) hdualkf)
  have h3 : QuasiIso (compositionMap X P (structureSheafComplex X) I) :=
    compositionMap_structureSheafMiddle_quasiIso_of_isFiniteFreeSummand X P I hbdd hterm
  rw [hdin]
  infer_instance

end Kit

section Slice

variable (U : X.C)

omit [∀ V : X.C, (X.J.over V).HasSheafCompose (forget₂ RingCat.{u} AddCommGrpCat.{u})]
  [∀ V : X.C, (X.J.over V).HasSheafCompose (forget₂ CommRingCat.{u} RingCat.{u})] in
/-- **The complex-level model of the composition morphism of Stacks 0A98 commutes with
restriction to a localized ringed site.** This is
`AlgebraicGeometry.RingedSite.compositionMap_restrict_square` with the K-flat model of the right
tensor factor carried along: the extra factor `tensorTotalMap (𝟙) f` restricts by the naturality
of `tensorTotalOverIso`, and the two `tensorTotalMap`s then merge. -/
theorem compositionMapOfModels_restrict_square
    (E J I : CochainComplex (SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf X.O)) ℤ)
    {H : CochainComplex (SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf X.O)) ℤ}
    (f : H ⟶ (sheafHomComplex X E J).obj) :
    restrictComplexMap X U (compositionMapOfModels X E J I f) ≫
        (derivedHomRestriction X U).complexMap E I =
      (tensorTotalOverIso X U (sheafHomComplex X J I).obj H).hom ≫
        tensorTotalMap (X.over U) ((derivedHomRestriction X U).complexMap J I)
            (restrictComplexMap X U f ≫ (derivedHomRestriction X U).complexMap E J) ≫
          compositionMap (X.over U) (restrictComplex X E U) (restrictComplex X J U)
            (restrictComplex X I U) := by
  have hmc : restrictComplexMap X U (compositionMapOfModels X E J I f) =
      restrictComplexMap X U (tensorTotalMap X (𝟙 (sheafHomComplex X J I).obj) f) ≫
        restrictComplexMap X U (compositionMap X E J I) :=
    CategoryTheory.Functor.map_comp _ _ _
  have hnat : restrictComplexMap X U (tensorTotalMap X (𝟙 (sheafHomComplex X J I).obj) f) ≫
        (tensorTotalOverIso X U (sheafHomComplex X J I).obj
          (sheafHomComplex X E J).obj).hom =
      (tensorTotalOverIso X U (sheafHomComplex X J I).obj H).hom ≫
        tensorTotalMap (X.over U)
          (𝟙 (restrictComplex X (sheafHomComplex X J I).obj U))
          (restrictComplexMap X U f) := by
    refine Eq.trans (tensorTotalOverIso_naturality X U
      (𝟙 (sheafHomComplex X J I).obj) f) ?_
    exact congrArg (fun z => (tensorTotalOverIso X U (sheafHomComplex X J I).obj H).hom ≫
      tensorTotalMap (X.over U) z (restrictComplexMap X U f))
      (CategoryTheory.Functor.map_id _ _)
  have hmerge := (tensorTotalMap_comp (X.over U)
      (𝟙 (restrictComplex X (sheafHomComplex X J I).obj U))
      ((derivedHomRestriction X U).complexMap J I) (restrictComplexMap X U f)
      ((derivedHomRestriction X U).complexMap E J)).trans
    (congrArg (fun z => tensorTotalMap (X.over U) z (restrictComplexMap X U f ≫
        (derivedHomRestriction X U).complexMap E J))
      (Category.id_comp ((derivedHomRestriction X U).complexMap J I)))
  have hglue := (Category.assoc _ _ _).symm.trans (congrArg
    (fun z => z ≫ compositionMap (X.over U) (restrictComplex X E U) (restrictComplex X J U)
      (restrictComplex X I U)) hmerge)
  refine Eq.trans (congrArg (fun z => z ≫ (derivedHomRestriction X U).complexMap E I) hmc) ?_
  refine Eq.trans (Category.assoc _ _ _) ?_
  refine Eq.trans (congrArg (fun z => restrictComplexMap X U
      (tensorTotalMap X (𝟙 (sheafHomComplex X J I).obj) f) ≫ z)
    (compositionMap_restrict_square_hom X U E J I)) ?_
  exact CategoryTheory.square_comp' hnat hglue

omit [∀ V : X.C, (X.J.over V).HasSheafCompose (forget₂ RingCat.{u} AddCommGrpCat.{u})]
  [∀ V : X.C, (X.J.over V).HasSheafCompose (forget₂ CommRingCat.{u} RingCat.{u})] in
/-- **The local step of the third assertion of Stacks 08DQ.** Over a member `U` of a covering on
which the source acquires a strictly perfect model `P`, the complex-level model of the
composition morphism of Stacks 0A98 at intermediate object a K-injective resolution `J` of the
structure sheaf complex restricts to a quasi-isomorphism.

The hypotheses are the data of the models: `J` and `I` are K-injective, `aug` is the augmentation
of `J` over the structure sheaf complex, `f` is a quasi-isomorphism from a complex whose
restriction to `U` is K-flat, and `qP` is the quasi-isomorphism from the strictly perfect model
to the restriction of the source.

Only the restriction of `H` to `U` is required K-flat, not `H` itself: the global criterion needs
`H` K-flat as well, but that is the caller's business, and stating it here would be a hypothesis
the proof does not use. -/
theorem quasiIso_restrictComplexMap_compositionMapOfModels_of_isStrictlyPerfect
    {E J I H : CochainComplex (SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf X.O)) ℤ}
    [J.IsKInjective] [I.IsKInjective]
    (aug : structureSheafComplex X ⟶ J) (haug : QuasiIso aug)
    (f : H ⟶ (sheafHomComplex X E J).obj) (hf : QuasiIso f)
    (hHU : @Stacks.SheafOfModules.IsKFlat.{u, u, u} _ _ _ (X.over U).O
      (inferInstance : HasWeakSheafify (X.J.over U) AddCommGrpCat.{u})
      (inferInstance : (X.J.over U).WEqualsLocallyBijective AddCommGrpCat.{u})
      (sheafTensor_additive.{u, u, u, u, u} (X.over U).O)
      (fun module => sheafTensor_obj_additive.{u, u, u, u, u} (X.over U).O module)
      (fun first second => hasMapBifunctor_sheafTensor (X.over U).O first second)
      (restrictComplex X H U))
    {P : CochainComplex
      (SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf (X.over U).O)) ℤ}
    (hP : IsStrictlyPerfect ((Stacks.SheafOfModules.Tensor.ringSheaf X.O).over U) P)
    (qP : P ⟶ restrictComplex X E U) (hqP : QuasiIso qP) :
    QuasiIso (restrictComplexMap X U (compositionMapOfModels X E J I f)) := by
  let := sheafTensor_additive.{u, u, u, u, u} (X.over U).O
  let : ∀ module : SheafOfModules.{u} (ringSheaf (X.over U).O),
      ((sheafTensor.{u, u, u, u, u} (X.over U).O).obj module).Additive :=
    fun module => sheafTensor_obj_additive.{u, u, u, u, u} (X.over U).O module
  let : ∀ first second : CochainComplex (SheafOfModules.{u} (ringSheaf (X.over U).O)) ℤ,
      HomologicalComplex.HasMapBifunctor first second
        (sheafTensor.{u, u, u, u, u} (X.over U).O) (ComplexShape.up ℤ) :=
    fun first second => hasMapBifunctor_sheafTensor (X.over U).O first second
  have := haug
  have := hf
  have := hqP
  have hph : (SheafOfModules.overFunctor.{u}
      (Stacks.SheafOfModules.Tensor.ringSheaf X.O) U).PreservesHomology :=
    Stacks.SheafOfModules.preservesHomology_overFunctor U
  have hJU : (show CochainComplex
      (SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf (X.over U).O)) ℤ from
      restrictComplex X J U).IsKInjective :=
    Stacks.Cohomology.Localization.isKInjective_over X.J
      (Stacks.SheafOfModules.Tensor.ringSheaf X.O) U J
  have hIU : (show CochainComplex
      (SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf (X.over U).O)) ℤ from
      restrictComplex X I U).IsKInjective :=
    Stacks.Cohomology.Localization.isKInjective_over X.J
      (Stacks.SheafOfModules.Tensor.ringSheaf X.O) U I
  have hterm : ∀ i, IsFiniteFreeSummand (X.over U) (P.X i) := fun i =>
    IsDirectSummandOfFiniteFree.isFiniteFreeSummand (X.over U) (hP.termDirectSummand i)
  -- instance search does not see these through the restriction, so state them once
  have hqi : ∀ {A B : CochainComplex
      (SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf (X.over U).O)) ℤ}
      (g : A ⟶ B) [IsIso g], QuasiIso g := fun g _ => inferInstance
  have hqc : ∀ {A B C : CochainComplex
      (SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf (X.over U).O)) ℤ}
      (g : A ⟶ B) (h : B ⟶ C), QuasiIso g → QuasiIso h → QuasiIso (g ≫ h) :=
    fun _ _ _ _ => inferInstance
  have hresaug : QuasiIso (restrictComplexMap X U aug) := inferInstance
  have hresf : QuasiIso (restrictComplexMap X U f) := inferInstance
  have hcmEI : IsIso ((derivedHomRestriction X U).complexMap E I) :=
    isIso_of_isInternalHomRestrictionMap X U E I _
      ((derivedHomRestriction X U).complexMap_isRestriction E I)
  have hcmJI : IsIso ((derivedHomRestriction X U).complexMap J I) :=
    isIso_of_isInternalHomRestrictionMap X U J I _
      ((derivedHomRestriction X U).complexMap_isRestriction J I)
  have hcmEJ : IsIso ((derivedHomRestriction X U).complexMap E J) :=
    isIso_of_isInternalHomRestrictionMap X U E J _
      ((derivedHomRestriction X U).complexMap_isRestriction E J)
  -- derived composition over `U` is invertible at the strictly perfect model, with the
  -- augmentation of the structure sheaf complex of the slice over `J|_U`
  have hPcomp : IsIso (derivedSheafHomComposition (X.over U)
      (Stacks.SheafOfModules.canonicalDerivedTensorProduct (X.over U))
      (canonicalDerivedInternalHom (X.over U)) (DerivedCategory.Q.obj P)
      (DerivedCategory.Q.obj (restrictComplex X J U))
      (DerivedCategory.Q.obj (restrictComplex X I U))) :=
    isIso_derivedSheafHomComposition_of_isFiniteFreeSummand (X.over U)
      (Stacks.SheafOfModules.canonicalDerivedTensorProduct (X.over U))
      (canonicalDerivedInternalHom (X.over U)) P (restrictComplex X J U)
      (restrictComplex X I U) hP.bounded hterm
      ((restrictComplexStructureSheafIsoAt X U).inv ≫ restrictComplexMap X U aug)
      (hqc _ _ (@hqi _ _ _ (Iso.isIso_inv _)) hresaug)
  -- transport the source to the restriction of `E`
  have hEcomp := isIso_derivedSheafHomComposition_of_iso (X.over U)
    (Stacks.SheafOfModules.canonicalDerivedTensorProduct (X.over U))
    (canonicalDerivedInternalHom (X.over U))
    (@asIso _ _ _ _ _ ((DerivedCategory.isIso_Q_map_iff_quasiIso _ _).2 hqP))
    (Iso.refl _) (Iso.refl _) hPcomp
  -- and read the criterion backwards at the restricted models
  have hloc : QuasiIso (compositionMapOfModels (X.over U) (restrictComplex X E U)
      (restrictComplex X J U) (restrictComplex X I U)
      (restrictComplexMap X U f ≫ (derivedHomRestriction X U).complexMap E J)) :=
    (isIso_derivedSheafHomComposition_iff_quasiIso_ofModels (X.over U)
      (Stacks.SheafOfModules.canonicalDerivedTensorProduct (X.over U))
      (canonicalDerivedInternalHom (X.over U)) (restrictComplex X E U)
      (restrictComplex X J U) (restrictComplex X I U) (restrictComplex X H U) hHU _
      ((DerivedCategory.isIso_Q_map_iff_quasiIso _ _).2
        (hqc _ _ hresf (@hqi _ _ _ hcmEJ)))).1 hEcomp
  -- transfer across the restriction square
  have hsqsplit := (compositionMapOfModels_restrict_square X U E J I f).trans
    (congrArg (fun z => (tensorTotalOverIso X U (sheafHomComplex X J I).obj H).hom ≫ z)
      (tensorTotalMap_comp_compositionMap_eq (X.over U) (restrictComplex X E U)
        (restrictComplex X J U) (restrictComplex X I U)
        ((derivedHomRestriction X U).complexMap J I)
        (restrictComplexMap X U f ≫ (derivedHomRestriction X U).complexMap E J)))
  have httm : QuasiIso (tensorTotalMap (X.over U) ((derivedHomRestriction X U).complexMap J I)
      (𝟙 (restrictComplex X H U))) :=
    @hqi _ _ _ (isIso_tensorTotalMap_hom_id (X.over U) (@asIso _ _ _ _ _ hcmJI) _)
  have hQ : QuasiIso (restrictComplexMap X U (compositionMapOfModels X E J I f) ≫
      (derivedHomRestriction X U).complexMap E I) := by
    rw [hsqsplit]
    exact hqc _ _ (@hqi _ _ _ (Iso.isIso_hom _)) (hqc _ _ httm hloc)
  exact (quasiIso_iff_comp_right _ _ (hφ' := @hqi _ _ _ hcmEI)).1 hQ

end Slice

section Perfect

variable (T : Stacks.SheafOfModules.DerivedTensorProduct X)

omit [∀ V : X.C, (X.J.over V).HasSheafCompose (forget₂ RingCat.{u} AddCommGrpCat.{u})] in
/-- **The composition morphism of Stacks 0A98 at intermediate object the structure sheaf is
invertible at a perfect source.** For objects `K`, `M` of `D(O)` with `K` perfect,

`RSheafHom(O, M) ⊗^L_O K^∨ ⟶ RSheafHom(K, M)`

is an isomorphism. The only hypothesis is `X.IsPerfect K`, the site-level notion of Stacks 08G5;
nothing is assumed of `M`.

The intermediate complex is the K-injective *resolution* of the structure sheaf complex, so that
its augmentation is available as a chain map to the local step; the K-flat model of the right
tensor factor is a resolution of `SheafHom(A₀, J)` whose restriction to every member of every
covering is K-flat. -/
theorem isIso_derivedSheafHomComposition_structureSheaf_of_isPerfect
    (Hd : DerivedInternalHom X)
    (K M : DerivedCategory (SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf X.O)))
    (hK : X.IsPerfect K) :
    IsIso (derivedSheafHomComposition X T Hd K (derivedStructureSheaf X) M) := by
  obtain ⟨A₀, hA₀, ⟨eA₀⟩⟩ := hK
  obtain ⟨κ, V, hV, hPs⟩ := exists_coversTop_isStrictlyPerfect_of_isPerfectComplex X A₀ hA₀
  obtain ⟨H, f, hHkf, hHflat, hHq, hHepi, hHrestr⟩ :=
    Stacks.SheafOfModules.KFlatRestriction.exists_kFlatResolution_restriction_forall X.O
      (sheafHomComplex X A₀ ((kInjectiveResolution X).obj (structureSheafComplex X))).obj
  have haug : QuasiIso ((kInjectiveAugmentation X).app (structureSheafComplex X)) :=
    inferInstance
  have hQf : IsIso (DerivedCategory.Q.map f) := inferInstance
  have hQaug : IsIso (DerivedCategory.Q.map
      ((kInjectiveAugmentation X).app (structureSheafComplex X))) := inferInstance
  refine isIso_derivedSheafHomComposition_of_coversTop X T Hd A₀
    ((kInjectiveResolution X).obj (structureSheafComplex X)) (kInjectiveModel X M) H
    K (derivedStructureSheaf X) M hHkf f hQf eA₀ (@asIso _ _ _ _ _ hQaug).symm
    (kInjectiveModelIso X M) hV fun i => ?_
  obtain ⟨P, hPsp, qP, hqP⟩ := hPs i
  exact quasiIso_restrictComplexMap_compositionMapOfModels_of_isStrictlyPerfect X (V i)
    ((kInjectiveAugmentation X).app (structureSheafComplex X)) haug f hHq (hHrestr (V i))
    hPsp qP hqP

omit [∀ V : X.C, (X.J.over V).HasSheafCompose (forget₂ RingCat.{u} AddCommGrpCat.{u})] in
/-- **Stacks 08DQ, third assertion.** Let `X` be a ringed site, let `K` be a **perfect** object of
`D(O)` and let `M` be any object. The canonical map of Stacks 08JD

`Φ : M ⊗^L_O K^∨ ⟶ RSheafHom(K, M)`

is an isomorphism.

The only hypothesis is `X.IsPerfect K`, the site-level notion of Stacks 08G5: there is a complex
representing `K` and a covering of the site on each member of which the restriction of that
complex receives a quasi-isomorphism from a strictly perfect complex. Nothing is assumed of `M`.

`Φ` is by definition the composition morphism of Stacks 0A98 at intermediate object the structure
sheaf, precomposed with the identification of `M` with `RSheafHom(O, M)`, so this is the previous
theorem with an isomorphism in front.

The instances in the ambient variable block are setup, not hypotheses: a ringed site whose slices
admit sheafification and on which the tensor product of sheaves of modules is additive and
totalisable is what it takes for the objects in the statement — the derived tensor product, the
derived dual, and their restrictions to the slices appearing in the definition of perfection — to
exist at all. -/
@[sga "6 I 7.7" "more general"]
theorem isIso_derivedTensorDualToSheafHom_of_isPerfect
    (L M : DerivedCategory (SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf X.O)))
    (hL : X.IsPerfect L) :
    IsIso (derivedTensorDualToSheafHom X T L M) := by
  have hcomp : IsIso (derivedSheafHomComposition X T (derivedInternalHomOfBifunctor X) L
      (derivedStructureSheaf X) M) :=
    isIso_derivedSheafHomComposition_structureSheaf_of_isPerfect X T
      (derivedInternalHomOfBifunctor X) L M hL
  have hpre : IsIso ((T.tensor.map (derivedStructureSheafHomIso X M).inv).app
      (derivedDual X L)) := by
    have : IsIso (T.tensor.map (derivedStructureSheafHomIso X M).inv) := Functor.map_isIso _ _
    infer_instance
  show IsIso ((T.tensor.map (derivedStructureSheafHomIso X M).inv).app (derivedDual X L) ≫
    derivedSheafHomComposition X T (derivedInternalHomOfBifunctor X) L
      (derivedStructureSheaf X) M)
  infer_instance

end Perfect

end AlgebraicGeometry.RingedSite

end
