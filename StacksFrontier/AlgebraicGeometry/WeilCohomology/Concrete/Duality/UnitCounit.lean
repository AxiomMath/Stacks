module

public import StacksFrontier.AlgebraicGeometry.WeilCohomology.Concrete.DualityZigZag
public import StacksFrontier.AlgebraicGeometry.WeilCohomology.Concrete.EquidimensionalGraph
public import StacksFrontier.AlgebraicGeometry.WeilCohomology.Concrete.EquidimensionalTensor
public import StacksFrontier.AlgebraicGeometry.WeilCohomology.Concrete.TensorCategory
public import StacksFrontier.AlgebraicGeometry.WeilCohomology.Concrete.TensorClosedSubscheme

/-!
# The motive of a smooth projective scheme is self-dual up to a twist

Let `k` be a field and let `X` be a smooth projective scheme over `k` which is equidimensional of
dimension `d`. Stacks 0FGI shows that `h(X)(d)` is a left dual of `h(X)` in the category `M_k` of
Chow motives, with unit and counit both the class of the diagonal:

* `η = [Δ] ∈ Hom(𝟏, h(X) ⊗ h(X)(d)) = Corr^d(Spec k, X × X)`,
* `ε = [Δ] ∈ Hom(h(X)(d) ⊗ h(X), 𝟏) = Corr^{-d}(X × X, Spec k)`.

This file defines `η` and `ε` as morphisms of the category of correspondences and proves the two
triangle identities there; the duality in `M_k` follows by
`CategoryTheory.GradedCategory.TwistedKaroubi.exactPairingOfObj`.

## Main definitions

* `Stacks.WeilCohomology.dualityUnit`: `η`, the class of `x ↦ (⋆, (x, x))` in
  `Corr^d(Spec k, X × X)`.
* `Stacks.WeilCohomology.dualityCounit`: `ε`, the class of `x ↦ ((x, x), ⋆)` in
  `Corr^{-d}(X × X, Spec k)`.

## Main results

* `Stacks.WeilCohomology.dualityUnit_mem_grade`, `Stacks.WeilCohomology.dualityCounit_mem_grade`:
  `η` has degree `d` and `ε` has degree `-d`.
* `Stacks.WeilCohomology.dualityUnit_tensorHom_associator_tensorHom_dualityCounit`: the first
  triangle identity `(η ⊗ 1) ≫ α ≫ (1 ⊗ ε) = λ ≫ ρ⁻¹`.
* `Stacks.WeilCohomology.tensorHom_dualityUnit_associator_tensorHom_dualityCounit`: the second
  triangle identity `(1 ⊗ η) ≫ α⁻¹ ≫ (ε ⊗ 1) = ρ ≫ λ⁻¹`.

## Implementation notes

The source computes the composite of `[Δ] ⊗ 1` with `1 ⊗ [Δ]` on the product of five factors,
where the two cycles meet in the small diagonal. Here each of the three correspondences of a
triangle identity is first read as the class of an explicit smooth closed subscheme of a product
(`η ⊗ 1` and `1 ⊗ ε` by `Stacks.WeilCohomology.tensorBlock_closedSubscheme`, the associator as
the graph of the associativity isomorphism), composition with the graph of an isomorphism is a
change of coordinates (`Stacks.WeilCohomology.compositionInt_graph_right_of_isIso`), and the last
composition is the transversal intersection computed in
`StacksFrontier.AlgebraicGeometry.WeilCohomology.Concrete.DualityZigZag`, whose fibre product over
the middle factor is the small diagonal. The unit constraints are graphs as well, and their
composite is the class of the same small diagonal.

Equidimensionality of `X` of dimension `d` is the hypothesis `RelativeDimension X.obj.hom d`;
`X` may be empty. Smoothness and properness of `X` enter through the proper-intersection formula
(Stacks 0FFD) used in every composition, and through the identification of correspondences with
Chow classes of the products.

## Organisation

This is the first part of `StacksFrontier.AlgebraicGeometry.WeilCohomology.Concrete.Duality`:
it defines `η` and `ε` and computes the classes of the pieces of the triangle identities and
the components of the constraints. The composites on the products are computed in
`StacksFrontier.AlgebraicGeometry.WeilCohomology.Concrete.Duality.TriangleComposites`, and the
triangle identities are proved in
`StacksFrontier.AlgebraicGeometry.WeilCohomology.Concrete.Duality.TriangleIdentities`.

## References

* [Stacks Project, Tag 0FGI](https://stacks.math.columbia.edu/tag/0FGI)
* [Stacks Project, Tag 0FFP](https://stacks.math.columbia.edu/tag/0FFP)
-/

@[expose] public noncomputable section

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits MonoidalCategory Stacks.Chow

universe u

namespace Stacks.WeilCohomology

/-- Transport along an equality of degrees commutes with the equidimensional identification
`Corrʳ(X, Y) ≃ CH_{e-r}(X × Y) ⊗ ℚ`. -/
theorem corrEquivCorrespondence_corrCongr {k : Type u} [Field k] {X Y : Scheme.{u}}
    (sX : X ⟶ (fieldChowSituation k).S) (sY : Y ⟶ (fieldChowSituation k).S) [Smooth sX]
    [IsSeparated sX] [Smooth sY] [IsSeparated sY] {d e : ℕ} (hX : RelativeDimension sX d)
    (hY : RelativeDimension sY e) {r r' : ℤ} (h : r = r') (c : Corr k sX sY r) :
    corrEquivCorrespondence k sX sY hX hY r' (corrCongr k sX sY h c) =
      correspondenceCongr k sX sY h (corrEquivCorrespondence k sX sY hX hY r c) := by
  subst h
  rw [corrCongr_rfl]
  induction (corrEquivCorrespondence k sX sY hX hY r c) using TensorProduct.induction_on with
  | zero => simp
  | tmul q α => rw [correspondenceCongr_tmul]; rfl
  | add a b ha hb => rw [map_add, ← ha, ← hb]

variable (k : Type u) [Field k]

namespace CorrespondenceCategory

variable {k}

/-- A homogeneous morphism of the category of correspondences read in an equal degree. -/
theorem of_eq_of_corrCongr {X Y : (SmoothProjectiveScheme k).FullSubcategory} {r r' : ℤ}
    (h : r = r')
    (c : SmoothProjectiveCorr X Y r) :
    DirectSum.of (fun i ↦ SmoothProjectiveCorr X Y i) r c =
      DirectSum.of (fun i ↦ SmoothProjectiveCorr X Y i) r'
        ((SmoothProjectiveCorr.toCorr X Y r').symm
          (corrCongr k X.obj.hom Y.obj.hom h (SmoothProjectiveCorr.toCorr X Y r c))) :=
  (of_toCorr_symm_corrCongr h c).symm

/-- Two homogeneous morphisms of the category of correspondences between equidimensional schemes
agree as soon as their classes on the product agree, read in a common degree. -/
theorem of_eq_of_corrEquivCorrespondence {X Y : (SmoothProjectiveScheme k).FullSubcategory}
    {d e : ℕ}
    (hX : RelativeDimension X.obj.hom d) (hY : RelativeDimension Y.obj.hom e) {r r' : ℤ}
    (h : r = r') (c : SmoothProjectiveCorr X Y r) (c' : SmoothProjectiveCorr X Y r')
    (H : correspondenceCongr k X.obj.hom Y.obj.hom h
        (corrEquivCorrespondence k X.obj.hom Y.obj.hom hX hY r
          (SmoothProjectiveCorr.toCorr _ _ _ c)) =
      corrEquivCorrespondence k X.obj.hom Y.obj.hom hX hY r'
        (SmoothProjectiveCorr.toCorr _ _ _ c')) :
    DirectSum.of (fun i ↦ SmoothProjectiveCorr X Y i) r c =
      DirectSum.of (fun i ↦ SmoothProjectiveCorr X Y i) r' c' := by
  rw [of_eq_of_corrCongr h]
  congr 1
  apply (SmoothProjectiveCorr.toCorr X Y r').injective
  apply (corrEquivCorrespondence k X.obj.hom Y.obj.hom hX hY r').injective
  rwa [LinearEquiv.apply_symm_apply, corrEquivCorrespondence_corrCongr]

end CorrespondenceCategory

open CorrespondenceCategory

variable {k} (X : (SmoothProjectiveScheme k).FullSubcategory) {d : ℕ}
    (hX : RelativeDimension X.obj.hom d)

/-! ### The unit and the counit -/

/-- The diagonal as a closed subscheme of `Spec k × (X × X)`: `x ↦ (⋆, (x, x))`. -/
def unitDiagonal : X.obj.left ⟶ Limits.pullback
    (𝟙_ ((SmoothProjectiveScheme k).FullSubcategory)).obj.hom
    (X ⊗ X).obj.hom :=
  pullback.lift X.obj.hom (pullback.diagonal X.obj.hom) (by
    change X.obj.hom ≫ 𝟙 _ = pullback.diagonal X.obj.hom ≫ pullback.fst _ _ ≫ X.obj.hom
    rw [pullback.diagonal_fst_assoc, Category.comp_id])

/-- The diagonal as a closed subscheme of `(X × X) × Spec k`: `x ↦ ((x, x), ⋆)`. -/
def counitDiagonal : X.obj.left ⟶ Limits.pullback (X ⊗ X).obj.hom
    (𝟙_ ((SmoothProjectiveScheme k).FullSubcategory)).obj.hom :=
  pullback.lift (pullback.diagonal X.obj.hom) X.obj.hom (by
    change pullback.diagonal X.obj.hom ≫ pullback.fst _ _ ≫ X.obj.hom = X.obj.hom ≫ 𝟙 _
    rw [pullback.diagonal_fst_assoc, Category.comp_id])

/-- The first component of `x ↦ (⋆, (x, x))` is the structure morphism of `X`. -/
@[reassoc (attr := simp)] theorem unitDiagonal_fst :
    unitDiagonal X ≫ pullback.fst (𝟙_ ((SmoothProjectiveScheme k).FullSubcategory)).obj.hom
        (X ⊗ X).obj.hom =
      X.obj.hom :=
  pullback.lift_fst _ _ _

/-- The second component of `x ↦ (⋆, (x, x))` is the diagonal `x ↦ (x, x)`. -/
@[reassoc (attr := simp)] theorem unitDiagonal_snd :
    unitDiagonal X ≫ pullback.snd (𝟙_ ((SmoothProjectiveScheme k).FullSubcategory)).obj.hom
        (X ⊗ X).obj.hom =
      pullback.diagonal X.obj.hom :=
  pullback.lift_snd _ _ _

/-- The first component of `x ↦ ((x, x), ⋆)` is the diagonal `x ↦ (x, x)`. -/
@[reassoc (attr := simp)] theorem counitDiagonal_fst :
    counitDiagonal X ≫ pullback.fst (X ⊗ X).obj.hom
        (𝟙_ ((SmoothProjectiveScheme k).FullSubcategory)).obj.hom =
      pullback.diagonal X.obj.hom :=
  pullback.lift_fst _ _ _

/-- The second component of `x ↦ ((x, x), ⋆)` is the structure morphism of `X`. -/
@[reassoc (attr := simp)] theorem counitDiagonal_snd :
    counitDiagonal X ≫ pullback.snd (X ⊗ X).obj.hom
        (𝟙_ ((SmoothProjectiveScheme k).FullSubcategory)).obj.hom =
      X.obj.hom :=
  pullback.lift_snd _ _ _

/-- The diagonal `x ↦ (⋆, (x, x))` is a closed immersion. -/
theorem isClosedImmersion_unitDiagonal : IsClosedImmersion (unitDiagonal X) := by
  refine isClosedImmersion_of_retraction _
    (pullback.snd (𝟙_ ((SmoothProjectiveScheme k).FullSubcategory)).obj.hom (X ⊗ X).obj.hom ≫
      pullback.fst X.obj.hom X.obj.hom)
    (by rw [unitDiagonal_snd_assoc, pullback.diagonal_fst]) X.obj.hom
    (prodBase (𝟙_ ((SmoothProjectiveScheme k).FullSubcategory)).obj.hom (X ⊗ X).obj.hom) ?_
  have c := pullback.condition (f := (𝟙_ ((SmoothProjectiveScheme k).FullSubcategory)).obj.hom)
    (g := (X ⊗ X).obj.hom)
  rw [Category.assoc]
  exact c.symm

/-- The diagonal `x ↦ ((x, x), ⋆)` is a closed immersion. -/
theorem isClosedImmersion_counitDiagonal : IsClosedImmersion (counitDiagonal X) := by
  refine isClosedImmersion_of_retraction _
    (pullback.fst (X ⊗ X).obj.hom (𝟙_ ((SmoothProjectiveScheme k).FullSubcategory)).obj.hom ≫
      pullback.fst X.obj.hom X.obj.hom)
    (by rw [counitDiagonal_fst_assoc, pullback.diagonal_fst]) X.obj.hom
    (prodBase (X ⊗ X).obj.hom (𝟙_ ((SmoothProjectiveScheme k).FullSubcategory)).obj.hom) ?_
  rw [Category.assoc]
  rfl

attribute [local instance] isClosedImmersion_unitDiagonal isClosedImmersion_counitDiagonal

/-- `Spec k` has dimension `0`. -/
theorem relativeDimension_tensorUnit :
    RelativeDimension (𝟙_ ((SmoothProjectiveScheme k).FullSubcategory)).obj.hom 0 :=
  relativeDimension_identity _

/-- `X × X` has dimension `d + d`. -/
theorem relativeDimension_tensorSelf (hX : RelativeDimension X.obj.hom d) :
    RelativeDimension (X ⊗ X).obj.hom (d + d) :=
  relativeDimension_prodBase k X.obj.hom X.obj.hom hX hX

/-- **The unit of the duality**, `η = [Δ] ∈ Corr^d(Spec k, X × X)`, the class of the diagonal
`x ↦ (⋆, (x, x))`, as a degree-`d` correspondence. -/
def dualityUnitCorr : SmoothProjectiveCorr (𝟙_ ((SmoothProjectiveScheme k).FullSubcategory))
    (X ⊗ X) d :=
  (SmoothProjectiveCorr.toCorr _ _ _).symm
    ((corrEquivCorrespondence k _ _ (relativeDimension_tensorUnit (k := k))
      (relativeDimension_tensorSelf X hX) d).symm
      ((1 : ℚ) ⊗ₜ[ℤ] QuotientAddGroup.mk (cycleAssociatedToClosedSubscheme (fieldChowSituation k)
        (prodBase _ _) (unitDiagonal X) (((d + d : ℕ) : ℤ) - d))))

/-- **The counit of the duality**, `ε = [Δ] ∈ Corr^{-d}(X × X, Spec k)`, the class of the diagonal
`x ↦ ((x, x), ⋆)`, as a degree-`(-d)` correspondence. -/
def dualityCounitCorr : SmoothProjectiveCorr (X ⊗ X)
    (𝟙_ ((SmoothProjectiveScheme k).FullSubcategory)) (-d) :=
  (SmoothProjectiveCorr.toCorr _ _ _).symm
    ((corrEquivCorrespondence k _ _ (relativeDimension_tensorSelf X hX)
      (relativeDimension_tensorUnit (k := k)) (-d)).symm
      ((1 : ℚ) ⊗ₜ[ℤ] QuotientAddGroup.mk (cycleAssociatedToClosedSubscheme (fieldChowSituation k)
        (prodBase _ _) (counitDiagonal X) (((0 : ℕ) : ℤ) - -d))))

/-- **The unit of the duality** `η : 𝟏 ⟶ X ⊗ X` in the category of correspondences. -/
def dualityUnit : CorrespondenceCategory.tensorUnit (k := k) ⟶
    CorrespondenceCategory.tensorObj (GradedCompositionData.Obj.mk X : CorrespondenceCategory k)
      (GradedCompositionData.Obj.mk X) :=
  DirectSum.of (fun i ↦ SmoothProjectiveCorr _ _ i) (d : ℤ) (dualityUnitCorr X hX)

/-- **The counit of the duality** `ε : X ⊗ X ⟶ 𝟏` in the category of correspondences. -/
def dualityCounit :
    CorrespondenceCategory.tensorObj (GradedCompositionData.Obj.mk X : CorrespondenceCategory k)
      (GradedCompositionData.Obj.mk X) ⟶ CorrespondenceCategory.tensorUnit (k := k) :=
  DirectSum.of (fun i ↦ SmoothProjectiveCorr _ _ i) (-(d : ℤ)) (dualityCounitCorr X hX)

/-- The unit of the duality has degree `d`. -/
theorem dualityUnit_mem_grade :
    dualityUnit X hX ∈ GradedCategory.grade (R := ℚ) _ _ (d : ℤ) :=
  (GradedCompositionData.mem_grade_iff _).2 ⟨_, rfl⟩

/-- The counit of the duality has degree `-d`. -/
theorem dualityCounit_mem_grade :
    dualityCounit X hX ∈ GradedCategory.grade (R := ℚ) _ _ (-(d : ℤ)) :=
  (GradedCompositionData.mem_grade_iff _).2 ⟨_, rfl⟩

/-! ### The classes of the pieces of the triangle identities -/

section Pieces

attribute [local instance] isClosedImmersion_graphMorphism

/-- The unit, read in `CH_d(Spec k × (X × X)) ⊗ ℚ`, is the class of the diagonal. -/
theorem corrEquivCorrespondence_dualityUnitCorr :
    corrEquivCorrespondence k _ _ (relativeDimension_tensorUnit (k := k))
        (relativeDimension_tensorSelf X hX) d
        (SmoothProjectiveCorr.toCorr _ _ _ (dualityUnitCorr X hX)) =
      (1 : ℚ) ⊗ₜ[ℤ] QuotientAddGroup.mk (cycleAssociatedToClosedSubscheme (fieldChowSituation k)
        (prodBase _ _) (unitDiagonal X) (((d + d : ℕ) : ℤ) - d)) :=
  (corrEquivCorrespondence k _ _ (relativeDimension_tensorUnit (k := k))
    (relativeDimension_tensorSelf X hX) d).apply_symm_apply _

/-- The counit, read in `CH_d((X × X) × Spec k) ⊗ ℚ`, is the class of the diagonal. -/
theorem corrEquivCorrespondence_dualityCounitCorr :
    corrEquivCorrespondence k _ _ (relativeDimension_tensorSelf X hX)
        (relativeDimension_tensorUnit (k := k)) (-d)
        (SmoothProjectiveCorr.toCorr _ _ _ (dualityCounitCorr X hX)) =
      (1 : ℚ) ⊗ₜ[ℤ] QuotientAddGroup.mk (cycleAssociatedToClosedSubscheme (fieldChowSituation k)
        (prodBase _ _) (counitDiagonal X) (((0 : ℕ) : ℤ) - -d)) :=
  (corrEquivCorrespondence k _ _ (relativeDimension_tensorSelf X hX)
    (relativeDimension_tensorUnit (k := k)) (-d)).apply_symm_apply _

/-- The identity of `X`, read in `CH_d(X × X) ⊗ ℚ`, is the class of the diagonal. -/
theorem corrEquivCorrespondence_correspondenceDiagonal :
    corrEquivCorrespondence k X.obj.hom X.obj.hom hX hX 0
        (SmoothProjectiveCorr.toCorr _ _ _ (correspondenceDiagonal k X)) =
      (1 : ℚ) ⊗ₜ[ℤ] QuotientAddGroup.mk (cycleAssociatedToClosedSubscheme (fieldChowSituation k)
        (prodBase X.obj.hom X.obj.hom) (graphMorphism X.obj.hom X.obj.hom (𝟙 _)
          (Category.id_comp _)) ((d : ℤ) - 0)) :=
  corrEquivCorrespondence_diagonalCorr k X.obj.hom hX

/-- The diagonal `x ↦ (⋆, (x, x))` lies over `Spec k` by the structure morphism of `X`. -/
theorem unitDiagonal_prodBase :
    unitDiagonal X ≫ prodBase (𝟙_ ((SmoothProjectiveScheme k).FullSubcategory)).obj.hom
        (X ⊗ X).obj.hom =
      X.obj.hom := by
  rw [prodBase, unitDiagonal_fst_assoc]; rfl

/-- The diagonal `x ↦ ((x, x), ⋆)` lies over `Spec k` by the structure morphism of `X`. -/
theorem counitDiagonal_prodBase :
    counitDiagonal X ≫ prodBase (X ⊗ X).obj.hom
        (𝟙_ ((SmoothProjectiveScheme k).FullSubcategory)).obj.hom =
      X.obj.hom := by
  rw [prodBase, counitDiagonal_fst_assoc]
  exact pullback.diagonal_fst_assoc _ _

/-- The graph of the identity of `X` lies over `Spec k` by the structure morphism of `X`. -/
theorem graphMorphism_id_prodBase :
    graphMorphism X.obj.hom X.obj.hom (𝟙 _) (Category.id_comp _) ≫
      prodBase X.obj.hom X.obj.hom = X.obj.hom := by
  rw [prodBase, ← Category.assoc, graphMorphism_fst, Category.id_comp]

/-- `Spec k × X` has dimension `0 + d`. -/
theorem relativeDimension_unitTensor (hX : RelativeDimension X.obj.hom d) :
    RelativeDimension (𝟙_ ((SmoothProjectiveScheme k).FullSubcategory) ⊗ X).obj.hom (0 + d) :=
  relativeDimension_of_eq rfl ((Nat.add_comm d 0) ▸
    relativeDimension_prodBase k _ X.obj.hom (relativeDimension_tensorUnit (k := k)) hX)

/-- `(X × X) × X` has dimension `(d + d) + d`. -/
theorem relativeDimension_tensorSelfTensor (hX : RelativeDimension X.obj.hom d) :
    RelativeDimension ((X ⊗ X) ⊗ X).obj.hom ((d + d) + d) :=
  relativeDimension_of_eq rfl ((Nat.add_comm d (d + d)) ▸
    relativeDimension_prodBase k _ X.obj.hom (relativeDimension_tensorSelf X hX) hX)

/-- `X × (X × X)` has dimension `d + (d + d)`. -/
theorem relativeDimension_tensorTensorSelf (hX : RelativeDimension X.obj.hom d) :
    RelativeDimension (X ⊗ (X ⊗ X)).obj.hom (d + (d + d)) :=
  relativeDimension_of_eq rfl ((Nat.add_comm (d + d) d) ▸
    relativeDimension_prodBase k X.obj.hom _ hX (relativeDimension_tensorSelf X hX))

/-- `X × Spec k` has dimension `d + 0`. -/
theorem relativeDimension_tensorUnitRight (hX : RelativeDimension X.obj.hom d) :
    RelativeDimension (X ⊗ 𝟙_ ((SmoothProjectiveScheme k).FullSubcategory)).obj.hom (d + 0) :=
  relativeDimension_of_eq rfl ((Nat.add_comm 0 d) ▸
    relativeDimension_prodBase k X.obj.hom _ hX (relativeDimension_tensorUnit (k := k)))

/-- The product of the diagonal `x ↦ (⋆, (x, x))` with the graph of the identity is a closed
immersion. -/
instance : IsClosedImmersion (tensorEmbedding _ _ _ _ (unitDiagonal X)
    (graphMorphism X.obj.hom X.obj.hom (𝟙 _) (Category.id_comp _))
    (unitDiagonal_prodBase X) (graphMorphism_id_prodBase X)) :=
  isClosedImmersion_tensorEmbedding _ _ _ _ _ _ _ _

/-- The product of the graph of the identity with the diagonal `x ↦ ((x, x), ⋆)` is a closed
immersion. -/
instance : IsClosedImmersion (tensorEmbedding _ _ _ _
    (graphMorphism X.obj.hom X.obj.hom (𝟙 _) (Category.id_comp _)) (counitDiagonal X)
    (graphMorphism_id_prodBase X) (counitDiagonal_prodBase X)) :=
  isClosedImmersion_tensorEmbedding _ _ _ _ _ _ _ _

/-- The tensor product of two correspondences, each the class of a smooth closed subscheme, is the
class of the product of the subschemes. -/
private theorem corrEquivCorrespondence_tensor_closedSubscheme {X X' Y Y' : Scheme.{u}}
    {sX : X ⟶ (fieldChowSituation k).S} {sX' : X' ⟶ (fieldChowSituation k).S}
    {sY : Y ⟶ (fieldChowSituation k).S} {sY' : Y' ⟶ (fieldChowSituation k).S}
    [Smooth sX] [Smooth sX'] [Smooth sY] [Smooth sY']
    [IsProper sX] [IsProper sX'] [IsProper sY] [IsProper sY'] {d d' e e' : ℕ}
    (hX : RelativeDimension sX d) (hX' : RelativeDimension sX' d') (hY : RelativeDimension sY e)
    (hY' : RelativeDimension sY' e') (hXX : RelativeDimension (prodBase sX sX') (d + d'))
    (hYY : RelativeDimension (prodBase sY sY') (e + e')) {r r' : ℤ} (c : Corr k sX sY r)
    (c' : Corr k sX' sY' r') {A A' : Scheme.{u}} (a : A ⟶ Limits.pullback sX sY)
    [IsClosedImmersion a] (a' : A' ⟶ Limits.pullback sX' sY') [IsClosedImmersion a']
    {qA : A ⟶ (fieldChowSituation k).S} {qA' : A' ⟶ (fieldChowSituation k).S} [Smooth qA]
    [Smooth qA'] (hqA : a ≫ prodBase sX sY = qA) (hqA' : a' ≫ prodBase sX' sY' = qA')
    {nA nA' : ℕ} (hA : RelativeDimension qA nA) (hA' : RelativeDimension qA' nA')
    (hnA : (nA : ℤ) = e - r) (hnA' : (nA' : ℤ) = e' - r')
    (hc : corrEquivCorrespondence k sX sY hX hY r c =
      (1 : ℚ) ⊗ₜ[ℤ] QuotientAddGroup.mk (cycleAssociatedToClosedSubscheme (fieldChowSituation k)
        (prodBase sX sY) a ((e : ℤ) - r)))
    (hc' : corrEquivCorrespondence k sX' sY' hX' hY' r' c' =
      (1 : ℚ) ⊗ₜ[ℤ] QuotientAddGroup.mk (cycleAssociatedToClosedSubscheme (fieldChowSituation k)
        (prodBase sX' sY') a' ((e' : ℤ) - r'))) :
    haveI := isClosedImmersion_tensorEmbedding sX sX' sY sY' a a' hqA hqA'
    corrEquivCorrespondence k (prodBase sX sX') (prodBase sY sY') hXX hYY (r + r')
        (tensor k sX sX' sY sY' (canonicalDiagonalClassFamily k) r r' c c') =
      (1 * 1 : ℚ) ⊗ₜ[ℤ] QuotientAddGroup.mk (cycleAssociatedToClosedSubscheme
        (fieldChowSituation k) (tensorBase sX sX' sY sY')
        (tensorEmbedding sX sX' sY sY' a a' hqA hqA')
        (((e + e' : ℕ) : ℤ) - (r + r'))) := by
  refine (corrEquivCorrespondence_tensor k (canonicalDiagonalClassFamily k) sX sX' sY sY'
    (canonicalDiagonalClassFamily_isoInvariant k) hX hX' hY hY' hXX hYY r r' c c').trans ?_
  rw [hc, hc']
  exact tensorBlock_closedSubscheme k sX sX' sY sY' hX hX' hY hY' r r' a a' hqA hqA' hA hA' hnA
    hnA' 1 1

/-- **`η ⊗ 1` is the class of `X × X` in `(Spec k × X) × ((X × X) × X)`**, embedded by
`(x, y) ↦ ((⋆, y), ((x, x), y))`. -/
theorem corrEquivCorrespondence_tensorCorr_dualityUnit :
    corrEquivCorrespondence k _ _ (relativeDimension_unitTensor X hX)
        (relativeDimension_tensorSelfTensor X hX) ((d : ℤ) + 0)
        (SmoothProjectiveCorr.toCorr _ _ _
          (tensorCorr (d : ℤ) 0 (dualityUnitCorr X hX) (correspondenceDiagonal k X))) =
      (1 : ℚ) ⊗ₜ[ℤ] QuotientAddGroup.mk (cycleAssociatedToClosedSubscheme (fieldChowSituation k)
        (tensorBase _ _ _ _) (tensorEmbedding _ _ _ _ (unitDiagonal X)
          (graphMorphism X.obj.hom X.obj.hom (𝟙 _) (Category.id_comp _))
          (unitDiagonal_prodBase X) (graphMorphism_id_prodBase X))
        ((((d + d) + d : ℕ) : ℤ) - (d + 0))) := by
  refine (corrEquivCorrespondence_tensor_closedSubscheme (relativeDimension_tensorUnit (k := k))
    hX (relativeDimension_tensorSelf X hX) hX (relativeDimension_unitTensor X hX)
    (relativeDimension_tensorSelfTensor X hX) _ _ (unitDiagonal X)
    (graphMorphism X.obj.hom X.obj.hom (𝟙 _) (Category.id_comp _)) (unitDiagonal_prodBase X)
    (graphMorphism_id_prodBase X) hX hX (by push_cast; ring) (by simp)
    (corrEquivCorrespondence_dualityUnitCorr X hX)
    (corrEquivCorrespondence_correspondenceDiagonal X hX)).trans ?_
  rw [one_mul]
  rfl

/-- **`1 ⊗ ε` is the class of `X × X` in `(X × (X × X)) × (X × Spec k)`**, embedded by
`(x, y) ↦ ((x, (y, y)), (x, ⋆))`. -/
theorem corrEquivCorrespondence_tensorCorr_dualityCounit :
    corrEquivCorrespondence k _ _ (relativeDimension_tensorTensorSelf X hX)
        (relativeDimension_tensorUnitRight X hX) (0 + -(d : ℤ))
        (SmoothProjectiveCorr.toCorr _ _ _
          (tensorCorr 0 (-(d : ℤ)) (correspondenceDiagonal k X) (dualityCounitCorr X hX))) =
      (1 * 1 : ℚ) ⊗ₜ[ℤ] QuotientAddGroup.mk (cycleAssociatedToClosedSubscheme
        (fieldChowSituation k) (tensorBase _ _ _ _) (tensorEmbedding _ _ _ _
          (graphMorphism X.obj.hom X.obj.hom (𝟙 _) (Category.id_comp _)) (counitDiagonal X)
          (graphMorphism_id_prodBase X) (counitDiagonal_prodBase X))
        (((d + 0 : ℕ) : ℤ) - (0 + -d))) := by
  exact corrEquivCorrespondence_tensor_closedSubscheme hX (relativeDimension_tensorSelf X hX) hX
    (relativeDimension_tensorUnit (k := k)) (relativeDimension_tensorTensorSelf X hX)
    (relativeDimension_tensorUnitRight X hX) _ _
    (graphMorphism X.obj.hom X.obj.hom (𝟙 _) (Category.id_comp _))
    (counitDiagonal X) (graphMorphism_id_prodBase X) (counitDiagonal_prodBase X) hX hX
    (by simp) (by simp) (corrEquivCorrespondence_correspondenceDiagonal X hX)
    (corrEquivCorrespondence_dualityCounitCorr X hX)

/-- The product of the graph of the identity with the diagonal `x ↦ (⋆, (x, x))` is a closed
immersion. -/
instance : IsClosedImmersion (tensorEmbedding _ _ _ _
    (graphMorphism X.obj.hom X.obj.hom (𝟙 _) (Category.id_comp _)) (unitDiagonal X)
    (graphMorphism_id_prodBase X) (unitDiagonal_prodBase X)) :=
  isClosedImmersion_tensorEmbedding _ _ _ _ _ _ _ _

/-- The product of the diagonal `x ↦ ((x, x), ⋆)` with the graph of the identity is a closed
immersion. -/
instance : IsClosedImmersion (tensorEmbedding _ _ _ _ (counitDiagonal X)
    (graphMorphism X.obj.hom X.obj.hom (𝟙 _) (Category.id_comp _))
    (counitDiagonal_prodBase X) (graphMorphism_id_prodBase X)) :=
  isClosedImmersion_tensorEmbedding _ _ _ _ _ _ _ _

/-- **`1 ⊗ η` is the class of `X × X` in `(X × Spec k) × (X × (X × X))`**, embedded by
`(y, a) ↦ ((y, ⋆), (y, (a, a)))`. -/
theorem corrEquivCorrespondence_tensorCorr_dualityUnit_right :
    corrEquivCorrespondence k _ _ (relativeDimension_tensorUnitRight X hX)
        (relativeDimension_tensorTensorSelf X hX) (0 + (d : ℤ))
        (SmoothProjectiveCorr.toCorr _ _ _
          (tensorCorr 0 (d : ℤ) (correspondenceDiagonal k X) (dualityUnitCorr X hX))) =
      (1 * 1 : ℚ) ⊗ₜ[ℤ] QuotientAddGroup.mk (cycleAssociatedToClosedSubscheme
        (fieldChowSituation k) (tensorBase _ _ _ _) (tensorEmbedding _ _ _ _
          (graphMorphism X.obj.hom X.obj.hom (𝟙 _) (Category.id_comp _)) (unitDiagonal X)
          (graphMorphism_id_prodBase X) (unitDiagonal_prodBase X))
        (((d + (d + d) : ℕ) : ℤ) - (0 + d))) := by
  exact corrEquivCorrespondence_tensor_closedSubscheme hX (relativeDimension_tensorUnit (k := k))
    hX (relativeDimension_tensorSelf X hX) (relativeDimension_tensorUnitRight X hX)
    (relativeDimension_tensorTensorSelf X hX) _ _
    (graphMorphism X.obj.hom X.obj.hom (𝟙 _) (Category.id_comp _))
    (unitDiagonal X) (graphMorphism_id_prodBase X) (unitDiagonal_prodBase X) hX hX
    (by simp) (by push_cast; ring) (corrEquivCorrespondence_correspondenceDiagonal X hX)
    (corrEquivCorrespondence_dualityUnitCorr X hX)

/-- **`ε ⊗ 1` is the class of `X × X` in `((X × X) × X) × (Spec k × X)`**, embedded by
`(b, z) ↦ (((b, b), z), (⋆, z))`. -/
theorem corrEquivCorrespondence_tensorCorr_dualityCounit_left :
    corrEquivCorrespondence k _ _ (relativeDimension_tensorSelfTensor X hX)
        (relativeDimension_unitTensor X hX) (-(d : ℤ) + 0)
        (SmoothProjectiveCorr.toCorr _ _ _
          (tensorCorr (-(d : ℤ)) 0 (dualityCounitCorr X hX) (correspondenceDiagonal k X))) =
      (1 * 1 : ℚ) ⊗ₜ[ℤ] QuotientAddGroup.mk (cycleAssociatedToClosedSubscheme
        (fieldChowSituation k) (tensorBase _ _ _ _) (tensorEmbedding _ _ _ _ (counitDiagonal X)
          (graphMorphism X.obj.hom X.obj.hom (𝟙 _) (Category.id_comp _))
          (counitDiagonal_prodBase X) (graphMorphism_id_prodBase X))
        (((0 + d : ℕ) : ℤ) - (-d + 0))) := by
  exact corrEquivCorrespondence_tensor_closedSubscheme (relativeDimension_tensorSelf X hX) hX
    (relativeDimension_tensorUnit (k := k)) hX (relativeDimension_tensorSelfTensor X hX)
    (relativeDimension_unitTensor X hX) (SmoothProjectiveCorr.toCorr _ _ _ (dualityCounitCorr X hX))
    (SmoothProjectiveCorr.toCorr _ _ _ (correspondenceDiagonal k X)) (counitDiagonal X)
    (graphMorphism X.obj.hom X.obj.hom (𝟙 _) (Category.id_comp _)) (counitDiagonal_prodBase X)
    (graphMorphism_id_prodBase X) hX hX (by simp) (by simp)
    (corrEquivCorrespondence_dualityCounitCorr X hX)
    (corrEquivCorrespondence_correspondenceDiagonal X hX)

end Pieces

/-! ### The constraints of smooth projective schemes on points -/

section Constraints

attribute [local instance] Over.cartesianMonoidalCategory Over.braidedCategory

variable (Y Z : (SmoothProjectiveScheme k).FullSubcategory)

/-- The associator `((x, y), z) ↦ (x, (y, z))`, followed by the projection to `X`, is `x`. -/
@[reassoc (attr := simp)]
theorem associator_hom_hom_left_fst :
    (α_ X Y Z).hom.hom.left ≫ pullback.fst X.obj.hom (Y ⊗ Z).obj.hom =
      pullback.fst (X ⊗ Y).obj.hom Z.obj.hom ≫ pullback.fst X.obj.hom Y.obj.hom :=
  Over.associator_hom_left_fst X.obj Y.obj Z.obj

/-- The associator `((x, y), z) ↦ (x, (y, z))`, followed by the projection to `Y`, is `y`. -/
@[reassoc (attr := simp)]
theorem associator_hom_hom_left_snd_fst :
    (α_ X Y Z).hom.hom.left ≫ pullback.snd X.obj.hom (Y ⊗ Z).obj.hom ≫
        pullback.fst Y.obj.hom Z.obj.hom =
      pullback.fst (X ⊗ Y).obj.hom Z.obj.hom ≫ pullback.snd X.obj.hom Y.obj.hom :=
  Over.associator_hom_left_snd_fst X.obj Y.obj Z.obj

/-- The associator `((x, y), z) ↦ (x, (y, z))`, followed by the projection to `Z`, is `z`. -/
@[reassoc (attr := simp)]
theorem associator_hom_hom_left_snd_snd :
    (α_ X Y Z).hom.hom.left ≫ pullback.snd X.obj.hom (Y ⊗ Z).obj.hom ≫
        pullback.snd Y.obj.hom Z.obj.hom =
      pullback.snd (X ⊗ Y).obj.hom Z.obj.hom :=
  Over.associator_hom_left_snd_snd X.obj Y.obj Z.obj

/-- The inverse associator `(x, (y, z)) ↦ ((x, y), z)`, followed by the projection to `X`, is
`x`. -/
@[reassoc (attr := simp)]
theorem associator_inv_hom_left_fst_fst :
    (α_ X Y Z).inv.hom.left ≫ pullback.fst (X ⊗ Y).obj.hom Z.obj.hom ≫
        pullback.fst X.obj.hom Y.obj.hom =
      pullback.fst X.obj.hom (Y ⊗ Z).obj.hom :=
  Over.associator_inv_left_fst_fst X.obj Y.obj Z.obj

/-- The inverse associator `(x, (y, z)) ↦ ((x, y), z)`, followed by the projection to `Y`, is
`y`. -/
@[reassoc (attr := simp)]
theorem associator_inv_hom_left_fst_snd :
    (α_ X Y Z).inv.hom.left ≫ pullback.fst (X ⊗ Y).obj.hom Z.obj.hom ≫
        pullback.snd X.obj.hom Y.obj.hom =
      pullback.snd X.obj.hom (Y ⊗ Z).obj.hom ≫ pullback.fst Y.obj.hom Z.obj.hom :=
  Over.associator_inv_left_fst_snd X.obj Y.obj Z.obj

/-- The inverse associator `(x, (y, z)) ↦ ((x, y), z)`, followed by the second projection, is
`z`. -/
@[reassoc (attr := simp)]
theorem associator_inv_hom_left_snd :
    (α_ X Y Z).inv.hom.left ≫ pullback.snd (X ⊗ Y).obj.hom Z.obj.hom =
      pullback.snd X.obj.hom (Y ⊗ Z).obj.hom ≫ pullback.snd Y.obj.hom Z.obj.hom :=
  Over.associator_inv_left_snd X.obj Y.obj Z.obj

/-- The left unitor `Spec k × X ⟶ X` is the second projection. -/
theorem leftUnitor_hom_hom_left :
    (λ_ X).hom.hom.left = pullback.snd
        (𝟙_ ((SmoothProjectiveScheme k).FullSubcategory)).obj.hom X.obj.hom :=
  rfl

/-- The first component of the inverse left unitor `X ⟶ Spec k × X` is the structure morphism. -/
@[reassoc (attr := simp)]
theorem leftUnitor_inv_hom_left_fst :
    (λ_ X).inv.hom.left ≫ pullback.fst
        (𝟙_ ((SmoothProjectiveScheme k).FullSubcategory)).obj.hom X.obj.hom =
      X.obj.hom :=
  Over.leftUnitor_inv_left_fst X.obj

/-- The second component of the inverse left unitor `X ⟶ Spec k × X` is the identity. -/
@[reassoc (attr := simp)]
theorem leftUnitor_inv_hom_left_snd :
    (λ_ X).inv.hom.left ≫ pullback.snd
        (𝟙_ ((SmoothProjectiveScheme k).FullSubcategory)).obj.hom X.obj.hom =
      𝟙 _ :=
  Over.leftUnitor_inv_left_snd X.obj

/-- The right unitor `X × Spec k ⟶ X` is the first projection. -/
theorem rightUnitor_hom_hom_left :
    (ρ_ X).hom.hom.left = pullback.fst X.obj.hom
        (𝟙_ ((SmoothProjectiveScheme k).FullSubcategory)).obj.hom :=
  rfl

/-- The first component of the inverse right unitor `X ⟶ X × Spec k` is the identity. -/
@[reassoc (attr := simp)]
theorem rightUnitor_inv_hom_left_fst :
    (ρ_ X).inv.hom.left ≫ pullback.fst X.obj.hom
        (𝟙_ ((SmoothProjectiveScheme k).FullSubcategory)).obj.hom =
      𝟙 _ :=
  Over.rightUnitor_inv_left_fst X.obj

/-- The second component of the inverse right unitor `X ⟶ X × Spec k` is the structure
morphism. -/
@[reassoc (attr := simp)]
theorem rightUnitor_inv_hom_left_snd :
    (ρ_ X).inv.hom.left ≫ pullback.snd X.obj.hom
        (𝟙_ ((SmoothProjectiveScheme k).FullSubcategory)).obj.hom =
      X.obj.hom :=
  Over.rightUnitor_inv_left_snd X.obj

end Constraints


/-! The maps `pointSnd`, `diagFstPair`, `sndDiagPair`, `fstPoint`, `unitTensorMap` and
`tensorCounitMap`, read with the structure morphisms of the products of smooth projective
schemes. -/

/-- The first component of `(x, y) ↦ (⋆, y)` is the structure morphism of `y`. -/
@[reassoc] theorem pointSnd_fst' :
    pointSnd k X.obj.hom ≫ pullback.fst
        (𝟙_ ((SmoothProjectiveScheme k).FullSubcategory)).obj.hom X.obj.hom =
      pullback.snd X.obj.hom X.obj.hom ≫ X.obj.hom :=
  pointSnd_fst k X.obj.hom
/-- The second component of `(x, y) ↦ (⋆, y)` is `y`. -/
@[reassoc] theorem pointSnd_snd' :
    pointSnd k X.obj.hom ≫ pullback.snd
        (𝟙_ ((SmoothProjectiveScheme k).FullSubcategory)).obj.hom X.obj.hom =
      pullback.snd X.obj.hom X.obj.hom :=
  pointSnd_snd k X.obj.hom
/-- The first component of `(x, y) ↦ (x, (x, y))` is `x`. -/
@[reassoc] theorem diagFstPair_fst' :
    diagFstPair k X.obj.hom ≫ pullback.fst X.obj.hom (X ⊗ X).obj.hom =
      pullback.fst X.obj.hom X.obj.hom :=
  diagFstPair_fst k X.obj.hom
/-- The second component of `(x, y) ↦ (x, (x, y))` is `(x, y)`. -/
@[reassoc] theorem diagFstPair_snd' :
    diagFstPair k X.obj.hom ≫ pullback.snd X.obj.hom (X ⊗ X).obj.hom = 𝟙 _ :=
  diagFstPair_snd k X.obj.hom
/-- The first component of `(u, v) ↦ (u, (v, v))` is `u`. -/
@[reassoc] theorem sndDiagPair_fst' :
    sndDiagPair k X.obj.hom ≫ pullback.fst X.obj.hom (X ⊗ X).obj.hom =
      pullback.fst X.obj.hom X.obj.hom :=
  sndDiagPair_fst k X.obj.hom
/-- The second component of `(u, v) ↦ (u, (v, v))` is `(v, v)`. -/
@[reassoc] theorem sndDiagPair_snd' :
    sndDiagPair k X.obj.hom ≫ pullback.snd X.obj.hom (X ⊗ X).obj.hom =
      pullback.snd X.obj.hom X.obj.hom ≫ pullback.diagonal X.obj.hom :=
  sndDiagPair_snd k X.obj.hom
/-- The first component of `(u, v) ↦ (u, ⋆)` is `u`. -/
@[reassoc] theorem fstPoint_fst' :
    fstPoint k X.obj.hom ≫ pullback.fst X.obj.hom
        (𝟙_ ((SmoothProjectiveScheme k).FullSubcategory)).obj.hom =
      pullback.fst X.obj.hom X.obj.hom :=
  fstPoint_fst k X.obj.hom
/-- The second component of `(u, v) ↦ (u, ⋆)` is the structure morphism of `u`. -/
@[reassoc] theorem fstPoint_snd' :
    fstPoint k X.obj.hom ≫ pullback.snd X.obj.hom
        (𝟙_ ((SmoothProjectiveScheme k).FullSubcategory)).obj.hom =
      pullback.fst X.obj.hom X.obj.hom ≫ X.obj.hom :=
  fstPoint_snd k X.obj.hom
/-- The first component of `unitTensorMap` in `Spec k × X` is `pointSnd`. -/
@[reassoc] theorem unitTensorMap_fst' :
    unitTensorMap k X.obj.hom ≫ pullback.fst
        (𝟙_ ((SmoothProjectiveScheme k).FullSubcategory) ⊗ X).obj.hom
      (X ⊗ (X ⊗ X)).obj.hom = pointSnd k X.obj.hom :=
  unitTensorMap_fst k X.obj.hom
/-- The second component of `unitTensorMap` in `X × (X × X)` is `diagFstPair`. -/
@[reassoc] theorem unitTensorMap_snd' :
    unitTensorMap k X.obj.hom ≫ pullback.snd
        (𝟙_ ((SmoothProjectiveScheme k).FullSubcategory) ⊗ X).obj.hom
      (X ⊗ (X ⊗ X)).obj.hom = diagFstPair k X.obj.hom :=
  unitTensorMap_snd k X.obj.hom
/-- The first component of `tensorCounitMap` in `X × (X × X)` is `sndDiagPair`. -/
@[reassoc] theorem tensorCounitMap_fst' :
    tensorCounitMap k X.obj.hom ≫ pullback.fst (prodBase X.obj.hom (X ⊗ X).obj.hom)
      (prodBase X.obj.hom (𝟙_ ((SmoothProjectiveScheme k).FullSubcategory)).obj.hom)
          = sndDiagPair k X.obj.hom :=
  tensorCounitMap_fst k X.obj.hom
/-- The second component of `tensorCounitMap` in `X × Spec k` is `fstPoint`. -/
@[reassoc] theorem tensorCounitMap_snd' :
    tensorCounitMap k X.obj.hom ≫ pullback.snd (prodBase X.obj.hom (X ⊗ X).obj.hom)
      (prodBase X.obj.hom (𝟙_ ((SmoothProjectiveScheme k).FullSubcategory)).obj.hom)
          = fstPoint k X.obj.hom :=
  tensorCounitMap_snd k X.obj.hom

end Stacks.WeilCohomology

end
