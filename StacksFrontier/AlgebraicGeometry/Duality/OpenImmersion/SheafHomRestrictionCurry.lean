module

public import StacksFrontier.AlgebraicGeometry.Duality.DerivedTilde.AffineDualizingSlice
public import StacksFrontier.CategoryTheory.Monoidal.ProjectionFormulaComparisonMap
public import StacksFrontier.CategoryTheory.Monoidal.InternalHomTransferEquivalence
public import StacksFrontier.AlgebraicGeometry.Duality.OpenImmersion.SheafHomRestrictionNaturality
public import StacksFrontier.AlgebraicGeometry.Duality.TwistedInverseImageDuality
public import StacksFrontier.AlgebraicGeometry.PseudoCoherent.RelativeTorIndependentBaseChange
public import StacksFrontier.CategoryTheory.Sites.Cohomology.InternalHom.SliceDerivedSheafHomTransposeIsIso
public import StacksFrontier.Topology.Sheaves.Cohomology.DerivedPushforward.InternalHomPullbackMap

/-!
# The derived internal Hom restricted to an open, through the currying bijection

Let `g : A ⟶ B` be a morphism of schemes and `μ : Lg^*(P ⊗ᴸ Q) ≅ Lg^*P ⊗ᴸ Lg^*Q` the comparison of
[Stacks, Tag 079U]. The *canonical map* of [Stacks, Tag 08I3]

`Lg^* R𝓗om(P, Z) ⟶ R𝓗om(Lg^*P, Lg^*Z)`

is the morphism whose transpose under the tensor–internal-Hom bijection of [Stacks, Tag 08J8] is
`μ⁻¹` followed by `Lg^*` of the evaluation morphism. By construction it is compatible with
currying: for `θ : W ⟶ R𝓗om(P, Z)`, the transpose of `Lg^*θ` followed by the canonical map is
`μ⁻¹` followed by `Lg^*` of the transpose of `θ`. For an open immersion `g` it is an isomorphism
([Stacks, Tag 08DL]): restriction to the open `g(A)` has the left adjoint extension by zero,
whose unit is invertible and which satisfies the projection formula [Stacks, Tag 0GL1], and
`A ≅ g(A)` is an isomorphism of schemes.

## Implementation notes

The canonical map is the construction of
`Stacks.Cohomology.DerivedInternalHomPullback.derivedPullbackSheafHomMap` (Tag 08I3),
`Stacks.Cohomology.DerivedInternalHomPullback.Transpose.homComparison`, at the standard model of
`D(𝒪)` used by the duality formula of [Stacks, Tag 0AU2]. Its tensor comparison `μ` uses the
identification `ProjectionFormulaLocallySmall.standardTensorIso` of the two derived tensor
products, the one the projection formula map `projectionMap` uses, where
`derivedPullbackSheafHomMap` uses `Stacks.Cohomology.DerivedInternalHomPullback.tensorBridge`.

`Stacks.SheafOfModules.derivedSheafHomOpenImmersionIso` is another isomorphism
`Lg^* R𝓗om(P, Z) ≅ R𝓗om(Lg^*P, Lg^*Z)`, assembled from the restriction of internal Hom complexes
to a slice site and the transport along `overEquiv` and `A ≅ g(A)`. No compatibility of that
isomorphism with the derived tensor product is available, which is why the canonical map is used
where currying is needed: it is the isomorphism `Stacks.Duality.UpperShriekDuality.pullSheafHomIso`
through which [Stacks, Tag 0AU2] restricts to opens. The two are not
compared here.

## Main definitions

* `Stacks.Duality.TwistedInverseImageDuality.pullTensorNatIso` — `μ`, at the derived tensor
  product of [Stacks, Tag 08J8].
* `Stacks.Duality.TwistedInverseImageDuality.pullSheafHomMap` — the canonical map.
* `Stacks.Duality.TwistedInverseImageDuality.pullIsoRestrictD` — `Lg^*` as restriction to the
  slice site over `g(A)` followed by two equivalences.

## Main results

* `Stacks.Duality.TwistedInverseImageDuality.curry_pull_map_comp_pullSheafHomMap` — the
  compatibility with currying.
* `Stacks.Duality.TwistedInverseImageDuality.isIso_pullSheafHomMap` — [Stacks, Tag 08DL] through
  the canonical map.

## References

* [Stacks Project, Tag 08DL](https://stacks.math.columbia.edu/tag/08DL)
* [Stacks Project, Tag 08I3](https://stacks.math.columbia.edu/tag/08I3)
* [Stacks Project, Tag 08J8](https://stacks.math.columbia.edu/tag/08J8)
* [Stacks Project, Tag 079U](https://stacks.math.columbia.edu/tag/079U)
-/

@[expose] public noncomputable section

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits Opposite

universe u

namespace Stacks.Duality.TwistedInverseImageDuality

attribute [local instance 10000] HasDerivedCategory.standard

/-! ### The comparison of tensor products and the canonical map -/

section Canonical

variable {A B : Scheme.{u}} (g : A ⟶ B)

/-- **`Lg^*(P ⊗ᴸ Q) ≅ Lg^*P ⊗ᴸ Lg^*Q`** ([Stacks, Tag 079U],
`Stacks.Cohomology.DerivedPullbackTensor.derivedPullbackTensorIso`), at the derived tensor product
of [Stacks, Tag 08J8], through `ProjectionFormulaLocallySmall.standardTensorIso` as in
`projectionMap`. -/
def pullTensorNatIso :
    Functor.uncurry.obj (tensor B) ⋙ pull g ≅
      (pull g).prod (pull g) ⋙ Functor.uncurry.obj (tensor A) :=
  Functor.isoWhiskerRight
      (Functor.uncurry.mapIso (ProjectionFormulaLocallySmall.standardTensorIso B)).symm (pull g) ≪≫
    Stacks.Cohomology.DerivedPullbackTensor.derivedPullbackTensorIso g.toLRSHom.toShHom ≪≫
    Functor.isoWhiskerLeft ((pull g).prod (pull g))
      (Functor.uncurry.mapIso (ProjectionFormulaLocallySmall.standardTensorIso A))

/-- `pullTensorNatIso` at a pair of objects. -/
abbrev pullTensorIso (P Q : Std B) :
    (pull g).obj (((tensor B).obj P).obj Q) ≅
      ((tensor A).obj ((pull g).obj P)).obj ((pull g).obj Q) :=
  (pullTensorNatIso g).app (P, Q)

/-- The isomorphism `pullTensorIso g P Q` is natural in `P`. -/
theorem pullTensorIso_naturality_left {P P' : Std B} (f : P ⟶ P') (Q : Std B) :
    (pull g).map (((tensor B).map f).app Q) ≫ (pullTensorIso g P' Q).hom =
      (pullTensorIso g P Q).hom ≫ ((tensor A).map ((pull g).map f)).app ((pull g).obj Q) := by
  have h := (pullTensorNatIso g).hom.naturality (X := (P, Q)) (Y := (P', Q)) (f, 𝟙 Q)
  change (pull g).map (((tensor B).map f).app Q ≫ ((tensor B).obj P').map (𝟙 Q)) ≫ _ = _ ≫
      (((tensor A).map ((pull g).map f)).app ((pull g).obj Q) ≫
        ((tensor A).obj ((pull g).obj P')).map ((pull g).map (𝟙 Q))) at h
  rwa [CategoryTheory.Functor.map_id, Category.comp_id, CategoryTheory.Functor.map_id,
    CategoryTheory.Functor.map_id, Category.comp_id] at h

/-- The isomorphism `pullTensorIso g P Q` is natural in `Q`. -/
theorem pullTensorIso_naturality_right (P : Std B) {Q Q' : Std B} (f : Q ⟶ Q') :
    (pull g).map (((tensor B).obj P).map f) ≫ (pullTensorIso g P Q').hom =
      (pullTensorIso g P Q).hom ≫ ((tensor A).obj ((pull g).obj P)).map ((pull g).map f) := by
  have h := (pullTensorNatIso g).hom.naturality (X := (P, Q)) (Y := (P, Q')) (𝟙 P, f)
  change (pull g).map (((tensor B).map (𝟙 P)).app Q ≫ ((tensor B).obj P).map f) ≫ _ = _ ≫
      (((tensor A).map ((pull g).map (𝟙 P))).app ((pull g).obj Q) ≫
        ((tensor A).obj ((pull g).obj P)).map ((pull g).map f)) at h
  rwa [CategoryTheory.Functor.map_id, NatTrans.id_app, Category.id_comp,
    CategoryTheory.Functor.map_id, CategoryTheory.Functor.map_id, NatTrans.id_app,
    Category.id_comp] at h

/-- The evaluation morphism `R𝓗om(P, Z) ⊗ᴸ P ⟶ Z`, the transpose of the identity. -/
abbrev evaluation {X : Scheme.{u}} (P Z : Std X) :
    ((tensor X).obj (((sheafHom X).obj (op P)).obj Z)).obj P ⟶ Z :=
  Stacks.Cohomology.DerivedInternalHomPullback.Transpose.evaluation (sheafHom X)
    (Functor.uncurry.obj (tensor X)) (curry X) P Z

/-- The evaluation morphism `evaluation P Z` is the transpose under `curry` of the identity of
`R𝓗om(P, Z)`. -/
theorem evaluation_eq {X : Scheme.{u}} (P Z : Std X) : evaluation P Z = curry X _ P Z (𝟙 _) :=
  rfl

/-- The transpose of `θ : W ⟶ R𝓗om(P, Z)` is `θ ⊗ P` followed by the evaluation morphism. -/
theorem curry_eq_tensor_map_comp_evaluation {X : Scheme.{u}} {W P Z : Std X}
    (θ : W ⟶ ((sheafHom X).obj (op P)).obj Z) :
    curry X W P Z θ = ((tensor X).map θ).app P ≫ evaluation P Z := by
  rw [evaluation_eq, ← curry_naturality_left, Category.comp_id]

/-- **The canonical map `Lg^* R𝓗om(P, Z) ⟶ R𝓗om(Lg^*P, Lg^*Z)`** of [Stacks, Tag 08I3]: the
construction `Stacks.Cohomology.DerivedInternalHomPullback.Transpose.homComparison` of
`Stacks.Cohomology.DerivedInternalHomPullback.derivedPullbackSheafHomMap`, at the standard model
and the tensor product of [Stacks, Tag 08J8] with `pullTensorNatIso`: the transpose of `μ⁻¹`
followed by `Lg^*` of the evaluation morphism. -/
def pullSheafHomMap (P Z : Std B) :
    (pull g).obj (((sheafHom B).obj (op P)).obj Z) ⟶
      ((sheafHom A).obj (op ((pull g).obj P))).obj ((pull g).obj Z) :=
  Stacks.Cohomology.DerivedInternalHomPullback.Transpose.homComparison (pull g) (sheafHom B)
    (sheafHom A) (Functor.uncurry.obj (tensor B)) (Functor.uncurry.obj (tensor A)) (curry B)
    (curry A) (pullTensorNatIso g) P Z

/-- The transpose under `curry` of the canonical map `pullSheafHomMap g P Z` is the inverse of
`pullTensorIso g _ P` followed by `Lg^*` of the evaluation morphism. -/
theorem curry_pullSheafHomMap (P Z : Std B) :
    curry A _ _ _ (pullSheafHomMap g P Z) =
      (pullTensorIso g _ P).inv ≫ (pull g).map (evaluation P Z) :=
  Stacks.Cohomology.DerivedInternalHomPullback.Transpose.homComparison_adjoint (pull g)
    (sheafHom B) (sheafHom A) (Functor.uncurry.obj (tensor B)) (Functor.uncurry.obj (tensor A))
    (curry B) (curry A) (pullTensorNatIso g) P Z

/-- **The canonical map is compatible with currying** ([Stacks, Tag 08J8]): for
`θ : W ⟶ R𝓗om(P, Z)`, the transpose of `Lg^*θ` followed by the canonical map is `μ⁻¹` followed
by `Lg^*` of the transpose of `θ`. -/
theorem curry_pull_map_comp_pullSheafHomMap {W P Z : Std B}
    (θ : W ⟶ ((sheafHom B).obj (op P)).obj Z) :
    curry A _ _ _ ((pull g).map θ ≫ pullSheafHomMap g P Z) =
      (pullTensorIso g W P).inv ≫ (pull g).map (curry B W P Z θ) := by
  rw [curry_naturality_left, curry_pullSheafHomMap]
  have key := (CommSq.mk (pullTensorIso_naturality_left g θ P)).vert_inv.w
  rw [curry_eq_tensor_map_comp_evaluation, Functor.map_comp, ← Category.assoc, key, Category.assoc]

/-- **The canonical map is natural in the first variable.** -/
theorem pullSheafHomMap_naturality {P P' : Std B} (l : P' ⟶ P) (Z : Std B) :
    (pull g).map (((sheafHom B).map l.op).app Z) ≫ pullSheafHomMap g P' Z =
      pullSheafHomMap g P Z ≫ ((sheafHom A).map ((pull g).map l).op).app ((pull g).obj Z) := by
  apply (curry A _ _ _).injective
  rw [curry_pull_map_comp_pullSheafHomMap, curry_naturality_middle, curry_pullSheafHomMap]
  have h1 : curry B _ P' Z (((sheafHom B).map l.op).app Z) =
      ((tensor B).obj _).map l ≫ evaluation P Z := by
    rw [evaluation_eq, ← curry_naturality_middle, Category.id_comp]
  have key := (CommSq.mk (pullTensorIso_naturality_right g
    (((sheafHom B).obj (op P)).obj Z) l)).vert_inv.w
  rw [h1, Functor.map_comp, ← Category.assoc, ← key, Category.assoc]

end Canonical

/-! ### For an open immersion the canonical map is an isomorphism -/

section OpenImmersion

open Stacks.SheafOfModules.OverEquivTensor Stacks.SheafOfModules.PullbackIsoTensor
  Stacks.Cohomology.SliceDerivedSheafHom

variable {A B : Scheme.{u}} (g : A ⟶ B) [IsOpenImmersion g]

/-- Restriction along an open immersion `g` is restriction to the slice site over `g(A)`,
followed by the equivalences `overEquiv` and the pullback along `A ≅ g(A)`. -/
def pullIsoRestrictD :
    pull g ≅ restrictD (Stacks.SheafOfModules.ringedSite B.sheaf) g.opensRange ⋙
      ((overEquivDerivedEquivalence B g.opensRange).trans
        (pullbackDerivedEquivalence g.isoOpensRange.hom)).functor :=
  (Scheme.Modules.derivedRestrictIsoDerivedPullback g).symm ≪≫
    Stacks.SheafOfModules.derivedRestrictFactorIso g ≪≫
    Functor.isoWhiskerRight (Stacks.SheafOfModules.derivedOverFunctorEquiv g.opensRange).symm _ ≪≫
    Functor.associator _ _ _ ≪≫
    Functor.isoWhiskerLeft _ (Functor.isoWhiskerLeft _
      (restrictFunctorDerivedIsoPullback g.isoOpensRange.hom))

/-- **[Stacks, Tag 08DL] through the canonical map**: for an open immersion `g`, the canonical
map `Lg^* R𝓗om(P, Z) ⟶ R𝓗om(Lg^*P, Lg^*Z)` is an isomorphism. -/
theorem isIso_pullSheafHomMap (P Z : Std B) : IsIso (pullSheafHomMap g P Z) := by
  have := Stacks.DerivedTensor.ExtensionByZero.isIso_derivedAdjunction_unit
    (Stacks.SheafOfModules.ringedSite B.sheaf) g.opensRange
  have he : ∀ {X : Scheme.{u}} (P Z W : Std X), Function.Bijective
      (fun h : W ⟶ ((sheafHom X).obj (op P)).obj Z => ((tensor X).map h).app P ≫
        evaluation P Z) := by
    intro X P Z W
    simpa only [← curry_eq_tensor_map_comp_evaluation] using (curry X W P Z).bijective
  refine CategoryTheory.InternalHomTransfer.isIso_of_tensorHomBijective_of_iso_comp
    (tensor B) (tensor A) (pullTensorIso g)
    (Stacks.SheafOfModules.derivedTensorProductFunctor
      ((Stacks.SheafOfModules.ringedSite B.sheaf).over g.opensRange))
    (Stacks.DerivedTensor.ExtensionByZero.derivedAdjunction
      (Stacks.SheafOfModules.ringedSite B.sheaf) g.opensRange)
    ((overEquivDerivedEquivalence B g.opensRange).trans
      (pullbackDerivedEquivalence g.isoOpensRange.hom)) (pullIsoRestrictD g)
    (projectionIso (Stacks.SheafOfModules.ringedSite B.sheaf) g.opensRange)
    (fun A' B' => (pullbackDerivedEquivalence g.isoOpensRange.hom).functor.mapIso
        (((overEquivDerivedTensorNatIso B g.opensRange).app A').app B') ≪≫
      (((pullbackDerivedTensorNatIso g.isoOpensRange.hom).app _).app _))
    (fun f Q => pullTensorIso_naturality_left g f Q) (evaluation P Z) (he P Z)
    (evaluation ((pull g).obj P) ((pull g).obj Z)) (he _ _) (pullSheafHomMap g P Z) ?_
  rw [← curry_eq_tensor_map_comp_evaluation, curry_pullSheafHomMap]

end OpenImmersion

end Stacks.Duality.TwistedInverseImageDuality

end
