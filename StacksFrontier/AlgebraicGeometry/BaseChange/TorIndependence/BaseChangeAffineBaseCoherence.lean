module

public import StacksFrontier.AlgebraicGeometry.BaseChange.TorIndependence.BaseChangeAffineBaseTensor
public import StacksFrontier.AlgebraicGeometry.BaseChange.TorIndependence.ProjectionFormulaInterchanged
public import StacksFrontier.AlgebraicGeometry.DerivedQCoh.StructureSheafAsADerivedUnit
public import StacksFrontier.CategoryTheory.Adjunction.BaseChangeProjectionFormulaCoherence
public import StacksFrontier.Topology.Sheaves.Cohomology.DerivedPushforward.BaseChangeProjectionFormula
public import StacksFrontier.Topology.Sheaves.Cohomology.DerivedPushforward.ProjectionFormulaBaseChange
public import StacksFrontier.Topology.Sheaves.Cohomology.DerivedPushforward.ProjectionFormulaClosedEmbedding

/-!
# Derived base change over an affine base, reduced to the transposed square at the unit

Let

```
X' --g'--> X
|          |
f'         f
v          v
S' --g---> S
```

be a Cartesian square of schemes with `f` quasi-compact and quasi-separated and `S`, `S'`
affine, and let `K` be a complex on `X` with quasi-coherent cohomology. The derived base-change
map of [Stacks, Tag 08HY] at `K`, and `Rg_*` of it, are invertible provided the derived
base-change map of the transposed square is invertible at `𝒪_{S'}[0]`; the statements take that
invertibility as a hypothesis.

## Main results

* `AlgebraicGeometry.isIso_adjunctionTensorMap_of_quasicoherent`: the projection-formula map
  `CategoryTheory.adjunctionTensorMap` of the derived adjunction of a quasi-compact
  quasi-separated morphism is invertible at complexes with quasi-coherent cohomology.
* `AlgebraicGeometry.unitTrivialization` and `AlgebraicGeometry.isIso_unitTrivialization`: the
  trivialization `Lf^*(𝒪_S[0]) ⊗^𝐋_{𝒪_X} K ⟶ K` and its invertibility.
* `Stacks.AffineProjectionFormula.tensorComparisonCompatible_symm`: the compatibility of the four
  tensor comparisons around a square is symmetric in the two ways around it.
* `Stacks.CategoryTheory.BaseChange.map_congr` and
  `Stacks.CategoryTheory.BaseChange.isIso_map_of_iso`: the base-change map of a square of
  adjunctions depends on its two identifications only through their difference, and its
  invertibility transports along an isomorphism of the object.
* `AlgebraicGeometry.transposedDerivedBaseChangeMap_eq` and
  `AlgebraicGeometry.isIso_map_derivedPullback_singleUnit_of_isIso_transposed`: the abstract
  base-change map at `Lg^*(𝒪_S[0])` is the derived base-change map for the transposed square at
  `𝒪_{S'}[0]`.
* `AlgebraicGeometry.isIso_derivedPushforward_map_derivedBaseChangeMap_of_isIso_unitBaseChange`:
  `Rg_*` of the derived base-change map at `K` is invertible if the base-change map of the
  transposed square at `Lg^*(𝒪_S[0])` is.
* `AlgebraicGeometry.isIso_derivedBaseChangeMap_of_isIso_unitBaseChange`: under the same
  hypothesis, the derived base-change map at `K` is invertible.
* `AlgebraicGeometry.isIso_derivedBaseChangeMap_of_isIso_transposedUnitBaseChange`: the derived
  base-change map at `K` is invertible if the derived base-change map of the transposed square
  at `𝒪_{S'}[0]` is.

## References

* [Stacks Project, Tag 06YU](https://stacks.math.columbia.edu/tag/06YU)
* [Stacks Project, Tag 079U](https://stacks.math.columbia.edu/tag/079U)
* [Stacks Project, Tag 079W](https://stacks.math.columbia.edu/tag/079W)
* [Stacks Project, Tag 08D5](https://stacks.math.columbia.edu/tag/08D5)
* [Stacks Project, Tag 08DW](https://stacks.math.columbia.edu/tag/08DW)
* [Stacks Project, Tag 08EU](https://stacks.math.columbia.edu/tag/08EU)
* [Stacks Project, Tag 08HY](https://stacks.math.columbia.edu/tag/08HY)
* [Stacks Project, Tag 08IB](https://stacks.math.columbia.edu/tag/08IB)
* [Stacks Project, Tag 0B6B](https://stacks.math.columbia.edu/tag/0B6B)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry
open scoped CategoryTheory.Prod
open Stacks.Cohomology.DerivedAdjunctionOnRingedSpaces (derivedPullback derivedPushforward
  derivedAdjunction)
open Stacks.DerivedTensor.RingedSite (derivedTensorProductFunctor)
open Stacks.Cohomology.DerivedProjectionFormula (pullbackTensorComparison projectionFormulaMap
  singleUnit)
open Stacks.DerivedPullback.Composition (derivedPullbackCompIsoCanonical)

universe v₁ v₂ u₁ u₂ u

/-! ### The compatibility of four tensor comparisons is symmetric -/

namespace Stacks.AffineProjectionFormula

section Symmetry

/-- **Conjugating a square of a bifunctor by an isomorphism of functors.**  For an isomorphism
`t : P ≅ Q` of functors into a category carrying a bifunctor `B`, a two-factor morphism
`P Z ⟶ B(P M, P N)` and one `Q Z ⟶ B(Q M, Q N)` that agree after transport along `t` also agree
after transport along `t⁻¹`. -/
theorem bifunctor_conjugate_symm {C : Type u₁} {D : Type u₂} [Category.{v₁} C] [Category.{v₂} D]
    (B : D × D ⥤ D) {P Q : C ⥤ D} (t : P ≅ Q) {M N Z : C} {W W' : D}
    (a : P.obj Z ⟶ W) (b : W ⟶ B.obj (P.obj M, P.obj N))
    (c : Q.obj Z ⟶ W') (d : W' ⟶ B.obj (Q.obj M, Q.obj N))
    (h : a ≫ b ≫ B.map (t.hom.app M ×ₘ t.hom.app N) = t.hom.app Z ≫ c ≫ d) :
    c ≫ d ≫ B.map (t.inv.app M ×ₘ t.inv.app N) = t.inv.app Z ≫ a ≫ b := by
  have h2 : c ≫ d = t.inv.app Z ≫ a ≫ b ≫ B.map (t.hom.app M ×ₘ t.hom.app N) := by
    simp [h]
  rw [reassoc_of% h2, Stacks.CategoryTheory.BaseChange.bifunctorSplitBoth, t.hom_inv_id_app,
    t.hom_inv_id_app, Stacks.CategoryTheory.BaseChange.bifunctorMapProdId, Category.comp_id]

variable {A₀ : Type u₁} {B₀ : Type u₂} {A₀' : Type u₁} {B₀' : Type u₂}

/-- **The compatibility of the four tensor comparisons around a square is symmetric in the two
ways around the square.**  Exchanging the roles of the two directions exchanges `eg` with `ef`,
the bifunctor on the second corner with the one on the third, and each comparison with its
partner; the resulting assertion is the conjugate of the original by the identification of the
two composites, which is an isomorphism. -/
theorem tensorComparisonCompatible_symm {S₀ T₀ S₀' T₀' : Type*}
    [Category S₀] [Category T₀] [Category S₀'] [Category T₀']
    {Lf : S₀ ⥤ T₀} {Lf' : S₀' ⥤ T₀'} {Lg : S₀ ⥤ S₀'} {Lg' : T₀ ⥤ T₀'} {Lc : S₀ ⥤ T₀'}
    (eg : Lg ⋙ Lf' ≅ Lc) (ef : Lf ⋙ Lg' ≅ Lc)
    (A : S₀ × S₀ ⥤ S₀) (A' : S₀' × S₀' ⥤ S₀') (B : T₀ × T₀ ⥤ T₀) (B' : T₀' × T₀' ⥤ T₀')
    (αf : A ⋙ Lf ⟶ Lf.prod Lf ⋙ B) (αf' : A' ⋙ Lf' ⟶ Lf'.prod Lf' ⋙ B')
    (αg : A ⋙ Lg ⟶ Lg.prod Lg ⋙ A') (αg' : B ⋙ Lg' ⟶ Lg'.prod Lg' ⋙ B')
    (M N : S₀) (h : TensorComparisonCompatible eg ef A A' B B' αf αf' αg αg' M N) :
    TensorComparisonCompatible ef eg A B A' B' αg αg' αf αf' M N :=
  bifunctor_conjugate_symm B' (squareCompositeIso eg ef)
    (Lf'.map (αg.app (M, N))) (αf'.app (Lg.obj M, Lg.obj N))
    (Lg'.map (αf.app (M, N))) (αg'.app (Lf.obj M, Lf.obj N)) h

end Symmetry

end Stacks.AffineProjectionFormula

/-! ### The base change map of a square of adjunctions, transported -/

namespace Stacks.CategoryTheory.BaseChange

section Transport

variable {A : Type*} {B : Type*} {A' : Type*} {B' : Type*}
  [Category A] [Category B] [Category A'] [Category B']
  {Lf : A ⥤ B} {Rf : B ⥤ A} {Lf' : A' ⥤ B'} {Rf' : B' ⥤ A'}
  {Lg : A ⥤ A'} {Lg' : B ⥤ B'}

/-- **The base change map depends on the two identifications only through their difference.**
Two pairs of identifications `(eg, ef)` and `(eg', ef')` with `eg.hom ≫ ef.inv = eg'.hom ≫ ef'.inv`
give the same base change map. -/
theorem map_congr {Lc Lc' : A ⥤ B'} (adjf : Lf ⊣ Rf) (adjf' : Lf' ⊣ Rf')
    (eg : Lg ⋙ Lf' ≅ Lc) (ef : Lf ⋙ Lg' ≅ Lc)
    (eg' : Lg ⋙ Lf' ≅ Lc') (ef' : Lf ⋙ Lg' ≅ Lc')
    (h : eg.hom ≫ ef.inv = eg'.hom ≫ ef'.inv) (K : B) :
    map adjf adjf' eg ef K = map adjf adjf' eg' ef' K := by
  rw [map, map, twoSquare, twoSquare, pullbackComparison, pullbackComparison, h]

/-- **Invertibility of the base change map transports along an isomorphism of the object**: if
`K ≅ L` and the base change map at `L` is invertible, so is the one at `K`. -/
theorem isIso_map_of_iso {Lc : A ⥤ B'} (adjf : Lf ⊣ Rf) (adjf' : Lf' ⊣ Rf')
    (eg : Lg ⋙ Lf' ≅ Lc) (ef : Lf ⋙ Lg' ≅ Lc) {K L : B} (u : K ≅ L)
    (h : IsIso (map adjf adjf' eg ef L)) : IsIso (map adjf adjf' eg ef K) := by
  have : IsIso (map adjf adjf' eg ef K ≫ Rf'.map (Lg'.map u.hom)) := by
    rw [← map_naturality adjf adjf' eg ef u.hom]
    infer_instance
  exact IsIso.of_isIso_comp_right (map adjf adjf' eg ef K) (Rf'.map (Lg'.map u.hom))

end Transport

end Stacks.CategoryTheory.BaseChange

namespace AlgebraicGeometry

attribute [local instance 100000] HasDerivedCategory.standard

/-! ### The projection formula at `CategoryTheory.adjunctionTensorMap` -/

/-- **[Stacks, Tag 08EU] written at `CategoryTheory.adjunctionTensorMap`.**  For a quasi-compact
quasi-separated morphism of schemes `h : W ⟶ Y` and complexes `E` on `W` and `A` on `Y` with
quasi-coherent cohomology, the abstract projection-formula map of the derived adjunction is
invertible. -/
theorem isIso_adjunctionTensorMap_of_quasicoherent {W Y : Scheme.{u}} (h : W ⟶ Y)
    [QuasiCompact h] [QuasiSeparated h]
    (E : DerivedCategory (SheafOfModules.{u} (structureSheafRing W.toRingedSpace)))
    (hE : ∀ j : ℤ, ((DerivedCategory.homologyFunctor
      (SheafOfModules.{u} (structureSheafRing W.toRingedSpace)) j).obj E).IsQuasicoherent)
    (A : DerivedCategory (SheafOfModules.{u} (structureSheafRing Y.toRingedSpace)))
    (hA : ∀ j : ℤ, ((DerivedCategory.homologyFunctor
      (SheafOfModules.{u} (structureSheafRing Y.toRingedSpace)) j).obj A).IsQuasicoherent) :
    IsIso (CategoryTheory.adjunctionTensorMap (derivedAdjunction h.toLRSHom.toShHom)
      (Functor.uncurry.obj (derivedTensorProductFunctor Y.toRingedSpace.sheaf))
      (Functor.uncurry.obj (derivedTensorProductFunctor W.toRingedSpace.sheaf))
      (pullbackTensorComparison h.toLRSHom.toShHom) E A) := by
  rw [← Stacks.Cohomology.DerivedProjectionFormula.projectionFormulaMap_eq]
  exact Stacks.Cohomology.DerivedProjectionFormula.isIso_projectionFormulaMap_quasiCoherent
    h E hE A hA

/-! ### The trivialization by the structure sheaf -/

variable {X' X S' S : Scheme.{u}} {g' : X' ⟶ X} {f' : X' ⟶ S'} {f : X ⟶ S} {g : S' ⟶ S}

/-- **The trivialization `Lf^*(𝒪_S[0]) ⊗^𝐋_{𝒪_X} K ⟶ K`**: the identification
`Lf^*(𝒪_S[0]) ≅ 𝒪_X[0]` in the first tensor factor, followed by the left unit law of `⊗^𝐋`. -/
def unitTrivialization (f : X ⟶ S)
    (K : DerivedCategory (SheafOfModules.{u} (structureSheafRing X.toRingedSpace))) :
    (Functor.uncurry.obj (derivedTensorProductFunctor X.toRingedSpace.sheaf)).obj
        ((derivedPullback f.toLRSHom.toShHom).obj (singleUnit S.toRingedSpace), K) ⟶ K :=
  (Functor.uncurry.obj (derivedTensorProductFunctor X.toRingedSpace.sheaf)).map
      (((Stacks.RingedSpace.derivedPullbackSingleUnitIso f.toLRSHom.toShHom).hom ×ₘ 𝟙 K :
        (((derivedPullback f.toLRSHom.toShHom).obj (singleUnit S.toRingedSpace), K) : _ × _) ⟶
          (singleUnit X.toRingedSpace, K))) ≫
    (Stacks.RingedSpace.derivedTensorLeftUnitIso X.toRingedSpace K).hom

/-- **The trivialization by the structure sheaf is invertible.** -/
theorem isIso_unitTrivialization (f : X ⟶ S)
    (K : DerivedCategory (SheafOfModules.{u} (structureSheafRing X.toRingedSpace))) :
    IsIso (unitTrivialization f K) := by
  rw [unitTrivialization]
  exact IsIso.comp_isIso' (Stacks.CategoryTheory.BaseChange.isIso_bifunctor_map_left
    (Functor.uncurry.obj (derivedTensorProductFunctor X.toRingedSpace.sheaf))
    (Stacks.RingedSpace.derivedPullbackSingleUnitIso f.toLRSHom.toShHom).hom
    (Stacks.RingedSpace.derivedPullbackSingleUnitIso f.toLRSHom.toShHom).isIso_hom K)
    (Stacks.RingedSpace.derivedTensorLeftUnitIso X.toRingedSpace K).isIso_hom

/-! ### The transposed base-change map at the structure sheaf -/

/-- **The derived base-change map of the transposed square is the abstract base-change map of the
square of derived adjunctions read with `g` vertical.** -/
theorem transposedDerivedBaseChangeMap_eq
    (sq : g'.toLRSHom.toShHom ≫ f.toLRSHom.toShHom =
      f'.toLRSHom.toShHom ≫ g.toLRSHom.toShHom)
    (W : DerivedCategory (SheafOfModules.{u} (structureSheafRing S'.toRingedSpace))) :
    Stacks.Cohomology.DerivedBaseChange.derivedBaseChangeMap f'.toLRSHom.toShHom
        g'.toLRSHom.toShHom g.toLRSHom.toShHom f.toLRSHom.toShHom sq.symm W =
      Stacks.CategoryTheory.BaseChange.map
        (derivedAdjunction g.toLRSHom.toShHom) (derivedAdjunction g'.toLRSHom.toShHom)
        (derivedPullbackCompIsoCanonical g'.toLRSHom.toShHom f.toLRSHom.toShHom)
        (Stacks.Cohomology.DerivedBaseChange.derivedPullbackCompIsoLeft g'.toLRSHom.toShHom
          f'.toLRSHom.toShHom f.toLRSHom.toShHom g.toLRSHom.toShHom sq) W := by
  rw [Stacks.Cohomology.DerivedBaseChange.derivedBaseChangeMap_eq_baseChangeMap]
  refine Stacks.CategoryTheory.BaseChange.map_congr _ _ _ _ _ _ ?_ W
  simp only [Stacks.Cohomology.DerivedBaseChange.derivedPullbackCompIsoLeft, Iso.trans_hom,
    Iso.trans_inv, Category.assoc, eqToIso.hom, eqToIso.inv]

/-- **The transposed base-change map at `Lg^*(𝒪_S[0])`.** Granted that the derived base-change
map of the *transposed* square at `𝒪_{S'}[0]` is invertible (the hypothesis `h`), so is the
abstract base-change map of the square of derived adjunctions at `Lg^*(𝒪_S[0])`. -/
theorem isIso_map_derivedPullback_singleUnit_of_isIso_transposed
    (sq : g'.toLRSHom.toShHom ≫ f.toLRSHom.toShHom =
      f'.toLRSHom.toShHom ≫ g.toLRSHom.toShHom)
    (h : IsIso (Stacks.Cohomology.DerivedBaseChange.derivedBaseChangeMap f'.toLRSHom.toShHom
      g'.toLRSHom.toShHom g.toLRSHom.toShHom f.toLRSHom.toShHom sq.symm
      (singleUnit S'.toRingedSpace))) :
    IsIso (Stacks.CategoryTheory.BaseChange.map
      (derivedAdjunction g.toLRSHom.toShHom) (derivedAdjunction g'.toLRSHom.toShHom)
      (derivedPullbackCompIsoCanonical g'.toLRSHom.toShHom f.toLRSHom.toShHom)
      (Stacks.Cohomology.DerivedBaseChange.derivedPullbackCompIsoLeft g'.toLRSHom.toShHom
        f'.toLRSHom.toShHom f.toLRSHom.toShHom g.toLRSHom.toShHom sq)
      ((derivedPullback g.toLRSHom.toShHom).obj (singleUnit S.toRingedSpace))) := by
  refine Stacks.CategoryTheory.BaseChange.isIso_map_of_iso _ _ _ _
    (Stacks.RingedSpace.derivedPullbackSingleUnitIso g.toLRSHom.toShHom) ?_
  rwa [← transposedDerivedBaseChangeMap_eq sq]

/-! ### Invertibility of the derived base-change map -/

/-- **`Rg_*` of the derived base-change map is invertible, granted the transposed base-change map
at `Lg^*(𝒪_S[0])`.**  For a Cartesian square of schemes with `f` quasi-compact and
quasi-separated and both bases affine, and for a complex `K` on `X` with quasi-coherent
cohomology, `Rg_*` of the derived base-change map at `K` is invertible provided the base-change
map of the transposed square of derived adjunctions at `Lg^*(𝒪_S[0])` is invertible, which is
the hypothesis `hθ`. -/
theorem isIso_derivedPushforward_map_derivedBaseChangeMap_of_isIso_unitBaseChange
    [IsAffine S] [IsAffine S'] (hsq : IsPullback g' f' f g)
    (hqc : QuasiCompact f) (hqs : QuasiSeparated f)
    (sq : g'.toLRSHom.toShHom ≫ f.toLRSHom.toShHom =
      f'.toLRSHom.toShHom ≫ g.toLRSHom.toShHom)
    (K : DerivedCategory (SheafOfModules.{u} (structureSheafRing X.toRingedSpace)))
    (hK : ∀ j : ℤ, ((DerivedCategory.homologyFunctor
      (SheafOfModules.{u} (structureSheafRing X.toRingedSpace)) j).obj K).IsQuasicoherent)
    (hθ : IsIso (Stacks.CategoryTheory.BaseChange.map
      (derivedAdjunction g.toLRSHom.toShHom) (derivedAdjunction g'.toLRSHom.toShHom)
      (derivedPullbackCompIsoCanonical g'.toLRSHom.toShHom f.toLRSHom.toShHom)
      (Stacks.Cohomology.DerivedBaseChange.derivedPullbackCompIsoLeft g'.toLRSHom.toShHom
        f'.toLRSHom.toShHom f.toLRSHom.toShHom g.toLRSHom.toShHom sq)
      ((derivedPullback g.toLRSHom.toShHom).obj (singleUnit S.toRingedSpace)))) :
    IsIso ((derivedPushforward g.toLRSHom.toShHom).map
      (Stacks.Cohomology.DerivedBaseChange.derivedBaseChangeMap g'.toLRSHom.toShHom
        f'.toLRSHom.toShHom f.toLRSHom.toShHom g.toLRSHom.toShHom sq K)) := by
  have : IsAffineHom g := isAffineHom_of_isAffine g
  have : IsAffineHom g' := isAffineHom_of_isPullback_right hsq
  have : QuasiCompact f' := MorphismProperty.of_isPullback (P := @QuasiCompact) hsq hqc
  have : QuasiSeparated f' := MorphismProperty.of_isPullback (P := @QuasiSeparated) hsq hqs
  have hJ : ∀ j : ℤ, ((DerivedCategory.homologyFunctor
      (SheafOfModules.{u} (structureSheafRing S.toRingedSpace)) j).obj
      (singleUnit S.toRingedSpace)).IsQuasicoherent := fun j =>
    Stacks.AlgebraicGeometry.AffinePushforwardTExactness.isQuasicoherent_homology_singleFunctor_obj
      0 _ (Stacks.AlgebraicGeometry.AffineQcohPushforward.isQuasicoherent_unit S) j
  have hLgJ : ∀ j : ℤ, ((DerivedCategory.homologyFunctor
      (SheafOfModules.{u} (structureSheafRing S'.toRingedSpace)) j).obj
      ((derivedPullback g.toLRSHom.toShHom).obj
        (singleUnit S.toRingedSpace))).IsQuasicoherent :=
    Stacks.Duality.isQuasicoherent_homology_derivedPullback_anyModel g _ hJ
  have hRfK : ∀ j : ℤ, ((DerivedCategory.homologyFunctor
      (SheafOfModules.{u} (structureSheafRing S.toRingedSpace)) j).obj
      ((derivedPushforward f.toLRSHom.toShHom).obj K)).IsQuasicoherent :=
    isQuasicoherent_homologyFunctor_derivedPushforward f K hK
  have hLf'LgJ : ∀ j : ℤ, ((DerivedCategory.homologyFunctor
      (SheafOfModules.{u} (structureSheafRing X'.toRingedSpace)) j).obj
      ((derivedPullback f'.toLRSHom.toShHom).obj
        ((derivedPullback g.toLRSHom.toShHom).obj
          (singleUnit S.toRingedSpace)))).IsQuasicoherent :=
    Stacks.Duality.isQuasicoherent_homology_derivedPullback_anyModel f' _ hLgJ
  have hsqc : ∀ M N : DerivedCategory
      (SheafOfModules.{u} (structureSheafRing S.toRingedSpace)),
      Stacks.AffineProjectionFormula.TensorComparisonCompatible
        (derivedPullbackCompIsoCanonical g'.toLRSHom.toShHom f.toLRSHom.toShHom)
        (Stacks.Cohomology.DerivedBaseChange.derivedPullbackCompIsoLeft g'.toLRSHom.toShHom
          f'.toLRSHom.toShHom f.toLRSHom.toShHom g.toLRSHom.toShHom sq)
        (Functor.uncurry.obj (derivedTensorProductFunctor S.toRingedSpace.sheaf))
        (Functor.uncurry.obj (derivedTensorProductFunctor X.toRingedSpace.sheaf))
        (Functor.uncurry.obj (derivedTensorProductFunctor S'.toRingedSpace.sheaf))
        (Functor.uncurry.obj (derivedTensorProductFunctor X'.toRingedSpace.sheaf))
        (pullbackTensorComparison g.toLRSHom.toShHom)
        (pullbackTensorComparison g'.toLRSHom.toShHom)
        (pullbackTensorComparison f.toLRSHom.toShHom)
        (pullbackTensorComparison f'.toLRSHom.toShHom) M N := fun M N =>
    Stacks.AffineProjectionFormula.tensorComparisonCompatible_symm _ _ _ _ _ _ _ _ _ _ M N
      (Stacks.Cohomology.DerivedProjectionFormula.tensorComparisonCompatible_of_comparisonSquare
        _ _ _ _ _ _ _ _
        (Stacks.Cohomology.DerivedRelativeCupProduct.derivedPullbackTensorIso_comparison_square
          g'.toLRSHom.toShHom f'.toLRSHom.toShHom f.toLRSHom.toShHom g.toLRSHom.toShHom sq)
        M N)
  rw [Stacks.Cohomology.DerivedBaseChange.derivedBaseChangeMap_eq_baseChangeMap]
  exact Stacks.CategoryTheory.BaseChange.isIso_pushforward_map_of_isIso_adjunctionTensorMapRight
    (derivedAdjunction f.toLRSHom.toShHom) (derivedAdjunction f'.toLRSHom.toShHom)
    (derivedAdjunction g.toLRSHom.toShHom) (derivedAdjunction g'.toLRSHom.toShHom)
    (Stacks.Cohomology.DerivedBaseChange.derivedPullbackCompIsoLeft g'.toLRSHom.toShHom
      f'.toLRSHom.toShHom f.toLRSHom.toShHom g.toLRSHom.toShHom sq)
    (derivedPullbackCompIsoCanonical g'.toLRSHom.toShHom f.toLRSHom.toShHom)
    (Functor.uncurry.obj (derivedTensorProductFunctor S.toRingedSpace.sheaf))
    (Functor.uncurry.obj (derivedTensorProductFunctor X.toRingedSpace.sheaf))
    (Functor.uncurry.obj (derivedTensorProductFunctor S'.toRingedSpace.sheaf))
    (Functor.uncurry.obj (derivedTensorProductFunctor X'.toRingedSpace.sheaf))
    (pullbackTensorComparison f.toLRSHom.toShHom)
    (pullbackTensorComparison f'.toLRSHom.toShHom)
    (pullbackTensorComparison g.toLRSHom.toShHom)
    (pullbackTensorComparison g'.toLRSHom.toShHom)
    (singleUnit S.toRingedSpace) K (unitTrivialization f K)
    (isIso_unitTrivialization f K)
    (isIso_adjunctionTensorMapRight_of_quasicoherent f hqc hqs K (singleUnit S.toRingedSpace)
      hK hJ)
    (Stacks.Cohomology.DerivedProjectionFormula.isIso_pullbackTensorComparison_app
      f.toLRSHom.toShHom _)
    (Stacks.Cohomology.DerivedProjectionFormula.isIso_pullbackTensorComparison_app
      g.toLRSHom.toShHom _)
    (Stacks.Cohomology.DerivedProjectionFormula.isIso_pullbackTensorComparison_app
      g'.toLRSHom.toShHom _)
    (Stacks.Cohomology.DerivedProjectionFormula.isIso_pullbackTensorComparison_app
      g'.toLRSHom.toShHom _)
    (isIso_adjunctionTensorMap_of_quasicoherent g _ hLgJ _ hRfK)
    (isIso_adjunctionTensorMap_of_quasicoherent g' _ hLf'LgJ _
      (Stacks.Duality.isQuasicoherent_homology_derivedPullback_anyModel f _ hRfK))
    (isIso_adjunctionTensorMap_of_quasicoherent g' _ hLf'LgJ _ hK)
    hθ
    (hsqc _ _) (hsqc _ _)
    (isIso_adjunctionTensorMapRight_of_quasicoherent f hqc hqs K _ hK
      (isQuasicoherent_homologyFunctor_derivedPushforward_of_isAffineHom g _ hLgJ))

/-- **[Stacks, Tag 08IB] over an affine base, granted the transposed base-change map at
`Lg^*(𝒪_S[0])`.**  For a Cartesian square of schemes with `f` quasi-compact and
quasi-separated and both bases affine, and for a complex `K` on `X` with quasi-coherent
cohomology, the derived base-change map at `K` is invertible provided the base-change map of the
transposed square of derived adjunctions at `Lg^*(𝒪_S[0])` is invertible, which is the hypothesis
`hθ`. -/
theorem isIso_derivedBaseChangeMap_of_isIso_unitBaseChange
    [IsAffine S] [IsAffine S'] (hsq : IsPullback g' f' f g)
    (hqc : QuasiCompact f) (hqs : QuasiSeparated f)
    (sq : g'.toLRSHom.toShHom ≫ f.toLRSHom.toShHom =
      f'.toLRSHom.toShHom ≫ g.toLRSHom.toShHom)
    (K : DerivedCategory (SheafOfModules.{u} (structureSheafRing X.toRingedSpace)))
    (hK : ∀ j : ℤ, ((DerivedCategory.homologyFunctor
      (SheafOfModules.{u} (structureSheafRing X.toRingedSpace)) j).obj K).IsQuasicoherent)
    (hθ : IsIso (Stacks.CategoryTheory.BaseChange.map
      (derivedAdjunction g.toLRSHom.toShHom) (derivedAdjunction g'.toLRSHom.toShHom)
      (derivedPullbackCompIsoCanonical g'.toLRSHom.toShHom f.toLRSHom.toShHom)
      (Stacks.Cohomology.DerivedBaseChange.derivedPullbackCompIsoLeft g'.toLRSHom.toShHom
        f'.toLRSHom.toShHom f.toLRSHom.toShHom g.toLRSHom.toShHom sq)
      ((derivedPullback g.toLRSHom.toShHom).obj (singleUnit S.toRingedSpace)))) :
    IsIso (Stacks.Cohomology.DerivedBaseChange.derivedBaseChangeMap g'.toLRSHom.toShHom
      f'.toLRSHom.toShHom f.toLRSHom.toShHom g.toLRSHom.toShHom sq K) :=
  isIso_derivedBaseChangeMap_of_isIso_derivedPushforward_map hsq hqc hqs sq K hK
    (isIso_derivedPushforward_map_derivedBaseChangeMap_of_isIso_unitBaseChange hsq hqc hqs sq K hK
      hθ)

/-- **[Stacks, Tag 08IB] over an affine base, reduced to one geometric input.**  For a Cartesian
square of schemes with `f` quasi-compact and quasi-separated and both bases affine, and for a
complex `K` on `X` with quasi-coherent cohomology, the derived base-change map of
[Stacks, Tag 08HY] is invertible as soon as the derived base-change map of the **transposed**
square is invertible at the single complex `𝒪_{S'}[0]`, which is the hypothesis `hunit`. -/
theorem isIso_derivedBaseChangeMap_of_isIso_transposedUnitBaseChange
    [IsAffine S] [IsAffine S'] (hsq : IsPullback g' f' f g)
    (hqc : QuasiCompact f) (hqs : QuasiSeparated f)
    (sq : g'.toLRSHom.toShHom ≫ f.toLRSHom.toShHom =
      f'.toLRSHom.toShHom ≫ g.toLRSHom.toShHom)
    (K : DerivedCategory (SheafOfModules.{u} (structureSheafRing X.toRingedSpace)))
    (hK : ∀ j : ℤ, ((DerivedCategory.homologyFunctor
      (SheafOfModules.{u} (structureSheafRing X.toRingedSpace)) j).obj K).IsQuasicoherent)
    (hunit : IsIso (Stacks.Cohomology.DerivedBaseChange.derivedBaseChangeMap
      f'.toLRSHom.toShHom g'.toLRSHom.toShHom g.toLRSHom.toShHom f.toLRSHom.toShHom sq.symm
      (singleUnit S'.toRingedSpace))) :
    IsIso (Stacks.Cohomology.DerivedBaseChange.derivedBaseChangeMap g'.toLRSHom.toShHom
      f'.toLRSHom.toShHom f.toLRSHom.toShHom g.toLRSHom.toShHom sq K) :=
  isIso_derivedBaseChangeMap_of_isIso_unitBaseChange hsq hqc hqs sq K hK
    (isIso_map_derivedPullback_singleUnit_of_isIso_transposed sq hunit)

end AlgebraicGeometry

end
