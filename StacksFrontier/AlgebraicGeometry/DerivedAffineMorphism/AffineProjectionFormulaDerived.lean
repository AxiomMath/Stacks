module

public import StacksFrontier.Algebra.Homology.TotalComplexOneRow
public import StacksFrontier.Algebra.Category.ModuleCat.Sheaf.SheafTensorAdditiveOnOpens
public import StacksFrontier.Topology.Sheaves.Modules.Quasicoherent
public import StacksFrontier.AlgebraicGeometry.DerivedAffineMorphism.AffinePushforwardComparisonQ
public import StacksFrontier.AlgebraicGeometry.DerivedAffineMorphism.CanonicalPullbackPushforwardMap
public import StacksFrontier.AlgebraicGeometry.DerivedQCoh.QuasicoherentKFlatModel
public import StacksFrontier.AlgebraicGeometry.Duality.ProjectionFormulaLocal
public import
  StacksFrontier.Topology.Sheaves.Cohomology.DerivedPushforward.ClosedEmbeddingProjectionFormulaDerived
public import StacksFrontier.AlgebraicGeometry.CoherentOfFiniteType.Basis
import StacksFrontier.CategoryTheory.Sites.Cohomology.DerivedTensor.TensorSymmetry
import StacksFrontier.CategoryTheory.Sites.Modules.TensorUnit
import StacksCore.Tactic.StacksAttribute

/-!
# The projection formula for an affine morphism, in the derived category

Let `f : X ⟶ Y` be an affine morphism of schemes.  This file proves the *affine case* of
[Stacks, Tag 08I9]: the canonical morphism

`Rf_*𝒪_X ⊗^𝐋_{𝒪_Y} K ⟶ Rf_*Lf^*K`

is invertible — with the genuine derived pullback and the genuine derived tensor product — for
every `K` in `D(𝒪_Y)` which is the class of a K-flat cochain complex of *quasi-coherent*
`𝒪_Y`-modules, and hence for every `K` in `D_QCoh(𝒪_Y)` when `Y` is a spectrum.

Nothing here is new mathematics.  The argument is the one carried out for a closed embedding in
`ClosedEmbeddingProjectionFormulaDerived`, run at the three inputs an affine morphism supplies in
place of the closed embedding's:

* the *termwise* projection formula `f_*G ⊗_{𝒪_Y} H ≅ f_*(G ⊗_{𝒪_X} f^*H)`, which for an affine
  morphism and quasi-coherent `G` and `H` is [Stacks, Tag 0FZE],
  `Stacks.AlgebraicGeometry.ProjectionFormula.isIso_projectionFormulaMap`;
* that `f_*` commutes with the totalization of the bicomplex `(p, q) ↦ A^p ⊗_{𝒪_X} f^*B^q`.  For
  a closed embedding this is preservation of arbitrary direct sums, which is **false** for a
  general affine morphism on arbitrary `𝒪_X`-modules.  What is used instead is
  `HomologicalComplex₂.TotalMap.isIso_totalMap_of_isZero_row`: the bicomplex has a single
  nonzero row, because the source complex of the tag is `𝒪_X[0]`, and an additive functor
  commutes with such a totalization unconditionally;
* that `Q(f_*C^•) ⟶ Rf_*(QC^•)` is invertible, which for an affine morphism and a complex of
  quasi-coherent modules is [Stacks, Tag 0G9N],
  `AlgebraicGeometry.isIso_pushforwardComparisonQ_of_isAffineHom`.

The transposition engine, the comparisons of [Stacks, Tag 06YU], [Stacks, Tag 079U] and
[Stacks, Tag 0FP0], and the mate identity are shared verbatim with the closed-embedding case:
`isIso_projectionFormulaMap_Q_of_iso`, in the namespace
`Stacks.Cohomology.ClosedEmbeddingProjectionFormulaComplexes`, takes the three inputs above as
parameters, and `projectionFormulaTotalIso_mate` carries no hypothesis on `f` at all.

## Main results

* `isIso_totalMap_modulePushforward_of_isZero_row`, in the namespace
  `Stacks.Cohomology.AffineProjectionFormulaComplexes`: **`f_*` commutes with the totalization
  of a bicomplex with a single nonzero row**, for an arbitrary morphism of ringed spaces.
* `Stacks.Cohomology.AffineProjectionFormulaComplexes.complexProjectionFormulaIsoOfIsIso`:
  **the projection formula at the level of complexes**,
  `Tot(f_*A^• ⊗_{𝒪_Y} B^•) ≅ f_* Tot(A^• ⊗_{𝒪_X} f^*B^•)`, from degreewise invertibility of the
  ordinary projection-formula morphism together with `A^•` having a single nonzero term.  Again
  no hypothesis on `f`.
* `AlgebraicGeometry.AffineProjectionFormula.isIso_projectionFormulaMap_Q_unit_of_isAffineHom`:
  **[Stacks, Tag 08EU] at `E = 𝒪_X[0]` for an affine morphism**, on a K-flat representative with
  quasi-coherent terms.
* `AlgebraicGeometry.AffineProjectionFormula.isIso_pullbackPushforwardTensorMap_of_kFlatModel`:
  **the morphism of [Stacks, Tag 08I9] is invertible** for an affine morphism of schemes and any
  `K` admitting a K-flat representative with quasi-coherent terms.  There is no hypothesis on the
  base.
* `AlgebraicGeometry.AffineProjectionFormula.isIso_pullbackPushforwardTensorMap_of_isAffineHom`:
  **the affine case of [Stacks, Tag 08I9]** over a spectrum: for `f : X ⟶ Spec R` affine and an
  arbitrary `K` in `D_QCoh(𝒪_{Spec R})`, the morphism `Rf_*𝒪_X ⊗^𝐋 K ⟶ Rf_*Lf^*K` is
  invertible.  The representative comes from
  `AlgebraicGeometry.StandardModel.exists_kFlat_isQuasicoherent_model`.

## What of [Stacks, Tag 08I9] is not here

The tag is for an affine morphism over an *arbitrary* base `S`, and its proof is local on `S`.
The localization half is closed, unconditionally, by
`Stacks.Cohomology.DerivedProjectionFormula.isIso_pullbackPushforwardTensorMap_of_openCover`: the
morphism for `f` is invertible as soon as the morphism for each `f|_{U_i}` is, over an open cover
of `S`.  Composing that with the affine case below needs the affine case at the restricted base
`U_i`, which is an affine *scheme* but not a spectrum, and the K-flat quasi-coherent
representative of `AlgebraicGeometry.StandardModel.exists_kFlat_isQuasicoherent_model` is
available only over `Spec R`.  That existence statement is transported along
`AlgebraicGeometry.Scheme.isoSpec` in
`StacksFrontier/AlgebraicGeometry/DerivedQCoh/QuasicoherentKFlatModelAffine.lean`, which is all the
composition needs: `isIso_pullbackPushforwardTensorMap_of_kFlatModel` was stated so that it
would be.  **The tag is closed**, in
`StacksFrontier/AlgebraicGeometry/DerivedAffineMorphism/AffineProjectionFormulaGeneralBase.lean`, by
`AlgebraicGeometry.AffineProjectionFormula.isIso_pullbackPushforwardTensorMap_unconditional`; it
is not closed in this file, which proves only the second of the two steps.

## Implementation notes

*`HasDerivedCategory.standard` is installed at priority `10000`*, as in
`StacksFrontier/AlgebraicGeometry/DerivedAffineMorphism/AffinePushforwardComparisonQ.lean`: the
locally small models of `StacksFrontier.Homology.DerivedCategory.LocallySmall` are global instances
and beat a default-priority local attribute, and the two inputs this file takes from the
quasi-coherent theory are stated at the standard model.

*The reducibility attributes* are those of the module
`…DerivedPushforward.ClosedEmbeddingProjectionFormulaComplexes`, for the same reason: instance
search matches up to reducible unfolding only, and the library spells the sheaf of rings of a
ringed space in three ways which the attributes collapse.

*What the attributes do not collapse* is `Stacks.SheafOfModules.Tensor.ringSheaf`, a plain `def`,
against `structureSheafRing`.  Three consequences are dealt with the way the closed-embedding
counterpart deals with them, and no further transparency is relaxed anywhere.
`HomologicalComplex₂.TotalMap.mapBicomplex` is given its `C` and `D` explicitly, so that the
`Functor.Additive` goal it raises is stated at the spelling `modulePushforward` is declared at
rather than at the one its `Stacks.SheafOfModules.Tensor.sheafTensor`-built bicomplex argument
carries; `(Opens.grothendieckTopology ·.carrier).WEqualsLocallyBijective AddCommGrpCat` is seated
from `Stacks.AssociatedSheaf.moduleSheafifyWEqualsLocallyBijective` wherever
`HomologicalComplex₂.hasTotal_of_iso` or `HomologicalComplex₂.total.mapIso` is used, instance
search otherwise exhausting its budget on it; and a step whose instances would have to be
synthesised across the gap is either applied with every argument explicit, or lifted out into
`isIso_of_isIso_comm_sq`, where the objects are bare variables.

## References

* [Stacks Project, Tag 06YU](https://stacks.math.columbia.edu/tag/06YU)
* [Stacks Project, Tag 08EU](https://stacks.math.columbia.edu/tag/08EU)
* [Stacks Project, Tag 08I9](https://stacks.math.columbia.edu/tag/08I9)
* [Stacks Project, Tag 0B53](https://stacks.math.columbia.edu/tag/0B53)
* [Stacks Project, Tag 0FZE](https://stacks.math.columbia.edu/tag/0FZE)
* [Stacks Project, Tag 0G9N](https://stacks.math.columbia.edu/tag/0G9N)
-/

@[expose] public noncomputable section

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits TopologicalSpace
open RingedSpaceModuleAdjunction Stacks.RingedSpace Stacks.ProjectionFormula
open Stacks.SheafOfModules.Tensor (sheafTensor tensorComplex)
open Stacks.Cohomology.ClosedEmbeddingProjectionFormulaComplexes
open Stacks.Cohomology.DerivedPullbackTensor (pullbackComplex)
open Stacks.Cohomology.NaiveCupProductOnRingedSpaces (pushforwardComplex)
open Stacks.Cohomology.CupProductAndDerivedPushforwardOnRingedSpaces (pushforwardComparisonQ
  pushforwardComparisonQ_naturality)
open Stacks.Cohomology.DerivedAdjunctionOnRingedSpaces (derivedPushforward derivedPullback)
open scoped Stacks.Topology.SheafTensorAdditiveOnOpens
open scoped CategoryTheory.Prod

universe u

/-! ### The complex-level projection formula, with the morphism's inputs as parameters -/

namespace Stacks.Cohomology.AffineProjectionFormulaComplexes

attribute [local instance 10000] HasDerivedCategory.standard

attribute [local implicit_reducible] structureSheafRing TopCat.Sheaf
attribute [local instance_reducible] CategoryTheory.sheafCompose
  AlgebraicGeometry.SheafedSpace.sheaf

variable {X Y : RingedSpace.{u, u}} (f : X ⟶ Y)

/-- **A bifunctor preserving zero morphisms kills a zero object in its first variable.**  Stated
for a bare bifunctor because that is all that is used: the identity of `(F.obj M).obj W` is the
component at `W` of `F` applied to the identity of `M`, which is zero. -/
lemma isZero_bifunctor_obj_obj {C D E : Type*} [Category C] [Category D] [Category E]
    [HasZeroMorphisms C] [HasZeroMorphisms E] (F : C ⥤ D ⥤ E) [F.PreservesZeroMorphisms]
    {M : C} (hM : IsZero M) (W : D) : IsZero ((F.obj M).obj W) := by
  rw [IsZero.iff_id_eq_zero]
  have h : (F.map (𝟙 M)).app W = 𝟙 ((F.obj M).obj W) := by rw [F.map_id]; rfl
  rw [← h, hM.eq_of_src (𝟙 M) 0, F.map_zero]
  rfl

/-- **The tensor product of a zero `𝒪_X`-module with anything is zero.** -/
lemma isZero_sheafTensor_obj_obj {M : SheafOfModules.{u} (structureSheafRing X)} (hM : IsZero M)
    (W : SheafOfModules.{u} (structureSheafRing X)) :
    IsZero (((sheafTensor X.sheaf).obj M).obj W) :=
  isZero_bifunctor_obj_obj (sheafTensor X.sheaf) hM W

/-- **`f_*` commutes with the totalization of a bicomplex with a single nonzero row**, for an
*arbitrary* morphism of ringed spaces: the comparison `Tot(f_*K) ⟶ f_* Tot(K)` of
`HomologicalComplex₂.TotalMap.totalMap` is an isomorphism as soon as `K.X p` is the zero complex
for every `p ≠ p₀`.

This is the affine counterpart of
`Stacks.Cohomology.ClosedEmbeddingPushforward.isIso_totalMap_modulePushforward`, which gets the
same conclusion for an unrestricted bicomplex from `f_*` preserving arbitrary direct sums.  That
preservation holds for a closed embedding and fails for a general affine morphism, whereas the
hypothesis here asks nothing of `f`: an additive functor commutes with a coproduct all but one
of whose summands is zero, which is
`HomologicalComplex₂.TotalMap.isIso_totalMap_of_isZero_row`. -/
theorem isIso_totalMap_modulePushforward_of_isZero_row
    (K : HomologicalComplex₂ (SheafOfModules.{u} (structureSheafRing X))
      (ComplexShape.up ℤ) (ComplexShape.up ℤ))
    [K.HasTotal (ComplexShape.up ℤ)]
    [HomologicalComplex₂.HasTotal
      (HomologicalComplex₂.TotalMap.mapBicomplex (modulePushforward f) K)
      (ComplexShape.up ℤ)]
    (p₀ : ℤ) (hz : ∀ p, p ≠ p₀ → ∀ q, IsZero ((K.X p).X q)) :
    IsIso (HomologicalComplex₂.TotalMap.totalMap (c₁₂ := ComplexShape.up ℤ)
      (modulePushforward f) K) :=
  HomologicalComplex₂.TotalMap.isIso_totalMap_of_isZero_row (modulePushforward f) K p₀ hz

/-- **The projection formula termwise on a pair of complexes**, as an isomorphism of bicomplexes,
from degreewise invertibility of the ordinary projection-formula morphism.

This is
`Stacks.Cohomology.ClosedEmbeddingProjectionFormulaComplexes.projectionBicomplexIso` with the
closed embedding replaced by the hypothesis `hP` it is used through; the two families of squares
are the two one-sided naturalities, which carry no hypothesis on `f`. -/
def projectionBicomplexIsoOfIsIso
    (A : CochainComplex (SheafOfModules.{u} (structureSheafRing X)) ℤ)
    (B : CochainComplex (SheafOfModules.{u} (structureSheafRing Y)) ℤ)
    (hP : ∀ p q : ℤ, IsIso (projectionFormulaMap' f (A.X p) (B.X q))) :
    (((sheafTensor Y.sheaf).mapBifunctorHomologicalComplex (.up ℤ) (.up ℤ)).obj
        (((modulePushforward f).mapHomologicalComplex (.up ℤ)).obj A)).obj B ≅
      (letI : (modulePushforward f).Additive :=
        modulePushforward_additive f
       HomologicalComplex₂.TotalMap.mapBicomplex
        (C := SheafOfModules.{u} (structureSheafRing X))
        (D := SheafOfModules.{u} (structureSheafRing Y)) (modulePushforward f)
        ((((sheafTensor X.sheaf).mapBifunctorHomologicalComplex (.up ℤ) (.up ℤ)).obj A).obj
          (((modulePullback f).mapHomologicalComplex (.up ℤ)).obj B))) :=
  have : (modulePushforward f).Additive :=
    modulePushforward_additive f
  HomologicalComplex.Hom.isoOfComponents
    (fun i => HomologicalComplex.Hom.isoOfComponents
      (fun j => @asIso _ _ _ _ _ (hP i j))
      (fun j j' _ => (projectionFormulaMap'_natural_right f (A.X i) (B.d j j')).symm))
    (fun i i' _ => by
      ext j : 1
      exact (projectionFormulaMap'_natural_left f (A.d i i') (B.X j)).symm)

/-- **The projection formula at the level of complexes, for a source complex with a single
nonzero term.**  For an arbitrary morphism of ringed spaces `f : X ⟶ Y`, arbitrary cochain
complexes `A^•` on `X` and `B^•` on `Y` with `A^p = 0` for `p ≠ p₀`, and degreewise invertibility
`hP` of the ordinary projection-formula morphism,

`Tot(f_*A^• ⊗_{𝒪_Y} B^•) ≅ f_* Tot(A^• ⊗_{𝒪_X} f^*B^•)`.

There is no flatness or boundedness hypothesis, and no hypothesis on `f`.  This is
`Stacks.Cohomology.ClosedEmbeddingProjectionFormulaComplexes.complexProjectionFormulaIso` with
its two uses of the closed embedding — the termwise isomorphism and the commutation of `f_*` with
the totalization — replaced by `hP` and by the single-nonzero-row hypothesis. -/
def complexProjectionFormulaIsoOfIsIso
    (A : CochainComplex (SheafOfModules.{u} (structureSheafRing X)) ℤ)
    (B : CochainComplex (SheafOfModules.{u} (structureSheafRing Y)) ℤ)
    (hP : ∀ p q : ℤ, IsIso (projectionFormulaMap' f (A.X p) (B.X q)))
    (p₀ : ℤ) (hA : ∀ p, p ≠ p₀ → IsZero (A.X p)) :
    ((tensorComplex Y.sheaf).obj
        (((modulePushforward f).mapHomologicalComplex (.up ℤ)).obj A)).obj B ≅
      ((modulePushforward f).mapHomologicalComplex (.up ℤ)).obj
        (((tensorComplex X.sheaf).obj A).obj
          (((modulePullback f).mapHomologicalComplex (.up ℤ)).obj B)) := by
  letI : (modulePushforward f).Additive :=
    modulePushforward_additive f
  letI : (Opens.grothendieckTopology Y.carrier).WEqualsLocallyBijective AddCommGrpCat.{u} :=
    Stacks.AssociatedSheaf.moduleSheafifyWEqualsLocallyBijective.{u, u} Y
  letI : (Opens.grothendieckTopology X.carrier).WEqualsLocallyBijective AddCommGrpCat.{u} :=
    Stacks.AssociatedSheaf.moduleSheafifyWEqualsLocallyBijective.{u, u} X
  let e := projectionBicomplexIsoOfIsIso f A B hP
  letI := HomologicalComplex₂.hasTotal_of_iso e (.up ℤ)
  have h := isIso_totalMap_modulePushforward_of_isZero_row f
    ((((sheafTensor X.sheaf).mapBifunctorHomologicalComplex (.up ℤ) (.up ℤ)).obj A).obj
      (((modulePullback f).mapHomologicalComplex (.up ℤ)).obj B)) p₀
    (fun p hp q => isZero_sheafTensor_obj_obj (hA p hp) _)
  exact HomologicalComplex₂.total.mapIso e (.up ℤ) ≪≫ @asIso _ _ _ _ _ h

/-- **The summand formula for `complexProjectionFormulaIsoOfIsIso`.**  On the `(p, q)` summand it
is the termwise projection-formula morphism at `A^p` and `B^q`, followed by `f_*` of the `(p, q)`
summand inclusion on the other side.

This is `ι_total_map_comp_totalMap` at `G = f_*` and `φ = projectionBicomplexIsoOfIsIso`, exactly
as `ι_complexProjectionFormulaIso_hom` is for the closed-embedding case; it is the hypothesis
`hΦ` of `isIso_projectionFormulaMap_Q_of_iso` and of `projectionFormulaTotalIso_mate`. -/
lemma ι_complexProjectionFormulaIsoOfIsIso_hom
    (A : CochainComplex (AlgebraicGeometry.RingedSpace.KFlatDerivedPullback.Modules X) ℤ)
    (B : CochainComplex (AlgebraicGeometry.RingedSpace.KFlatDerivedPullback.Modules Y) ℤ)
    (hP : ∀ p q : ℤ, IsIso (projectionFormulaMap' f (A.X p) (B.X q)))
    (p₀ : ℤ) (hA : ∀ p, p ≠ p₀ → IsZero (A.X p))
    (p q n : ℤ) (hpq : p + q = n) :
    HomologicalComplex₂.ιTotal
          ((((sheafTensor Y.sheaf).mapBifunctorHomologicalComplex (.up ℤ) (.up ℤ)).obj
            ((pushforwardComplex f).obj A)).obj B)
          (.up ℤ) p q n hpq ≫
        (complexProjectionFormulaIsoOfIsIso f A B hP p₀ hA).hom.f n =
      projectionFormulaMap' f (A.X p) (B.X q) ≫
        (StacksDraft.KFlat.modulePushforward f).map
          (HomologicalComplex₂.ιTotal
            ((((sheafTensor X.sheaf).mapBifunctorHomologicalComplex (.up ℤ) (.up ℤ)).obj A).obj
              ((pullbackComplex f).obj B))
            (.up ℤ) p q n hpq) := by
  let : (modulePushforward f).Additive :=
    modulePushforward_additive f
  let : (Opens.grothendieckTopology Y.carrier).WEqualsLocallyBijective AddCommGrpCat.{u} :=
    Stacks.AssociatedSheaf.moduleSheafifyWEqualsLocallyBijective.{u, u} Y
  let : (Opens.grothendieckTopology X.carrier).WEqualsLocallyBijective AddCommGrpCat.{u} :=
    Stacks.AssociatedSheaf.moduleSheafifyWEqualsLocallyBijective.{u, u} X
  let : (StacksDraft.KFlat.modulePushforward f).Additive :=
    StacksDraft.KFlat.modulePushforward_additive f
  let := HomologicalComplex₂.hasTotal_of_iso (projectionBicomplexIsoOfIsIso f A B hP) (.up ℤ)
  exact ι_total_map_comp_totalMap (c₁₂ := ComplexShape.up ℤ)
    (StacksDraft.KFlat.modulePushforward f)
    ((((sheafTensor X.sheaf).mapBifunctorHomologicalComplex (.up ℤ) (.up ℤ)).obj A).obj
      ((pullbackComplex f).obj B))
    ((((sheafTensor Y.sheaf).mapBifunctorHomologicalComplex (.up ℤ) (.up ℤ)).obj
      ((pushforwardComplex f).obj A)).obj B)
    (projectionBicomplexIsoOfIsIso f A B hP).hom p q n hpq

section OneSpace

variable (Z : RingedSpace.{u, u})

/-- **A zero sheaf of modules is quasi-coherent.**  Quasi-coherence is closed under isomorphism
and the free module on the empty index type is both zero and quasi-coherent. -/
lemma isQuasicoherent_of_isZero {M : SheafOfModules.{u} (structureSheafRing Z)} (hM : IsZero M) :
    M.IsQuasicoherent := by
  have hfree : IsZero (SheafOfModules.free (R := structureSheafRing Z) PEmpty) := by
    rw [IsZero.iff_id_eq_zero]
    exact Sigma.hom_ext _ _ fun n => n.elim
  exact (_root_.SheafOfModules.isQuasicoherent (structureSheafRing Z)).prop_of_iso
    (hfree.iso hM) inferInstance

/-- **The terms of `𝒪_Z[0]` are quasi-coherent**: in degree zero the term is the structure sheaf,
quasi-coherent by `Stacks.AlgebraicGeometry.CoherentOfFiniteType.isQuasicoherent_unit`, and in
every other degree it is zero. -/
lemma isQuasicoherent_unitComplex_X (n : ℤ) : ((unitComplex Z).X n).IsQuasicoherent := by
  by_cases h : n = 0
  · subst h
    exact (_root_.SheafOfModules.isQuasicoherent (structureSheafRing Z)).prop_of_iso
      (HomologicalComplex.singleObjXSelf (ComplexShape.up ℤ) 0
        (_root_.SheafOfModules.unit (structureSheafRing Z))).symm
      Stacks.AlgebraicGeometry.CoherentOfFiniteType.isQuasicoherent_unit
  · exact isQuasicoherent_of_isZero Z
      (HomologicalComplex.isZero_single_obj_X (ComplexShape.up ℤ) 0 _ n h)

/-- **`Tot(𝒪_Z[0] ⊗_{𝒪_Z} C^•) ≅ C^•`**: the Koszul symmetry followed by the unit law of the
total tensor complex. -/
def unitTensorComplexIso
    (C : CochainComplex (SheafOfModules.{u} (structureSheafRing Z)) ℤ) :
    ((tensorComplex Z.sheaf).obj (unitComplex Z)).obj C ≅ C :=
  Stacks.SheafOfModules.Tensor.tensorComplexFlipIso Z.sheaf (unitComplex Z) C ≪≫
    Stacks.SheafOfModules.tensorComplexUnitIso Z.sheaf C

end OneSpace

/-- **One side of a commuting square of isomorphisms is invertible when the other is.**  Stated
for a bare category and bare morphisms, with the two vertical isomorphisms given as `Iso`s and
the invertibility of the far side as an explicit argument: every instance the proof needs is then
on a variable, so nothing has to be synthesised at the spelling of a consumer's objects.  That is
what lets `isIso_pushforwardComparisonQ_of_iso` apply it by `exact`, across the definitional
equality between `SheafOfModules (structureSheafRing ·)` and
`AlgebraicGeometry.RingedSpace.KFlatDerivedPullback.Modules ·`. -/
private lemma isIso_of_isIso_comm_sq {D : Type*} [Category D] {A₁ B₁ A₂ B₂ : D}
    (a : A₁ ≅ A₂) (b : B₁ ≅ B₂) (g₁ : A₁ ⟶ B₁) (g₂ : A₂ ⟶ B₂) (hg₂ : IsIso g₂)
    (hsq : a.hom ≫ g₂ = g₁ ≫ b.hom) : IsIso g₁ := by
  let := hg₂
  have key : g₁ = a.hom ≫ g₂ ≫ b.inv := by
    rw [← Category.assoc, hsq, Category.assoc, b.hom_inv_id, Category.comp_id]
  rw [key]
  infer_instance

/-- **Invertibility of `Q(f_*C^•) ⟶ Rf_*(QC^•)` only depends on the isomorphism class of `C^•`.**
The comparison is natural in the complex, so conjugating by `Q(f_*e)` and `Rf_*(Qe)` carries one
instance of it to another.  That conjugation is `isIso_of_isIso_comm_sq`, whose square is
`pushforwardComparisonQ_naturality` at `e.hom`. -/
lemma isIso_pushforwardComparisonQ_of_iso
    {C C' : CochainComplex (AlgebraicGeometry.RingedSpace.KFlatDerivedPullback.Modules X) ℤ}
    (e : C ≅ C') (h : IsIso (pushforwardComparisonQ f C')) :
    IsIso (pushforwardComparisonQ f C) :=
  isIso_of_isIso_comm_sq
    (DerivedCategory.Q.mapIso ((pushforwardComplex f).mapIso e))
    ((derivedPushforward f).mapIso (DerivedCategory.Q.mapIso e))
    (pushforwardComparisonQ f C) (pushforwardComparisonQ f C') h
    (pushforwardComparisonQ_naturality f e.hom)

end Stacks.Cohomology.AffineProjectionFormulaComplexes

/-! ### The affine case -/

namespace AlgebraicGeometry.AffineProjectionFormula

open Stacks.Cohomology.AffineProjectionFormulaComplexes
open Stacks.Cohomology.DerivedProjectionFormula (projectionFormulaMap
  isIso_projectionFormulaMap_congr_left isIso_projectionFormulaMap_congr_right
  pullbackPushforwardTensorMap' isIso_pullbackPushforwardTensorMap)

section Bridge

attribute [local implicit_reducible] AlgebraicGeometry.Scheme.Modules structureSheafRing
  TopCat.Sheaf
attribute [local instance_reducible] CategoryTheory.sheafCompose
  AlgebraicGeometry.SheafedSpace.sheaf

variable {X Y : Scheme.{u}} (f : X ⟶ Y)

/-- **[Stacks, Tag 0FZE] at the `Stacks.ProjectionFormula.projectionFormulaMap'` spelling.**  For
an affine morphism of schemes and quasi-coherent modules the ordinary projection-formula morphism
`f_*G ⊗_{𝒪_Y} H ⟶ f_*(G ⊗_{𝒪_X} f^*H)` is invertible.

`Stacks.AlgebraicGeometry.ProjectionFormula.projectionFormulaMap` and
`Stacks.ProjectionFormula.projectionFormulaMap'` are the same morphism: both are
`CategoryTheory.adjunctionTensorMap` for the adjunction `f^* ⊣ f_*` and the comparison of
[Stacks, Tag 01CD], and the two files that construct them differ only in which of the library's
spellings of the category of modules on a ringed space they write it at.  Rewriting each by its
own `_eq` lemma puts both at `adjunctionTensorMap`, where the match is immediate; asking the
definitional-equality check to cross the two spellings unaided exhausts the elaboration budget.

This section is kept outside the reducibility attributes below for the same reason. -/
@[sga "3 VIB 11.1" "more general"]
lemma isIso_projectionFormulaMap'_of_isAffineHom [IsAffineHom f] (G : X.Modules) (H : Y.Modules)
    (hG : G.IsQuasicoherent) (hH : H.IsQuasicoherent) :
    IsIso (Stacks.ProjectionFormula.projectionFormulaMap' f.toLRSHom.toShHom G H) := by
  have h := Stacks.AlgebraicGeometry.ProjectionFormula.isIso_projectionFormulaMap f G H hG hH
  rw [Stacks.AlgebraicGeometry.ProjectionFormula.projectionFormulaMap_eq f G H] at h
  rw [Stacks.ProjectionFormula.projectionFormulaMap'_eq f.toLRSHom.toShHom G H]
  exact h

end Bridge

attribute [local instance 10000] HasDerivedCategory.standard

attribute [local implicit_reducible] AlgebraicGeometry.Scheme.Modules structureSheafRing
  TopCat.Sheaf
attribute [local instance_reducible] CategoryTheory.sheafCompose
  AlgebraicGeometry.SheafedSpace.sheaf

variable {X Y : Scheme.{u}} (f : X ⟶ Y)

/-- **[Stacks, Tag 08EU] at `E = 𝒪_X[0]` for an affine morphism of schemes**, on a K-flat
representative with quasi-coherent terms: the projection-formula morphism of [Stacks, Tag 0B53]

`Rf_*𝒪_X ⊗^𝐋_{𝒪_Y} QB^• ⟶ Rf_*(𝒪_X ⊗^𝐋_{𝒪_X} Lf^*(QB^•))`

is invertible whenever `B^•` is K-flat with quasi-coherent terms.  There is no hypothesis on the
base `Y` and no boundedness hypothesis on `B^•`.

This is `isIso_projectionFormulaMap_Q_of_iso` with its four parameters supplied by the affine
inputs: `complexProjectionFormulaIsoOfIsIso` and its summand formula for `Φ` and `hΦ` — the
degreewise input being [Stacks, Tag 0FZE] and the single-nonzero-row input being that `𝒪_X[0]` is
concentrated in degree zero — and [Stacks, Tag 0G9N] twice for `hQA` and `hQT`, the second through
the identification `Tot(𝒪_X[0] ⊗_{𝒪_X} f^*B^•) ≅ f^*B^•` and quasi-coherence of `f^*B^q`, which
is [Stacks, Tag 01BG]. -/
theorem isIso_projectionFormulaMap_Q_unit_of_isAffineHom [IsAffineHom f]
    (B : CochainComplex Y.Modules ℤ) (hBq : ∀ q : ℤ, (B.X q).IsQuasicoherent)
    (hB : Stacks.Cohomology.KFlatDerivedPullback.KFlatComplex Y.toRingedSpace B) :
    IsIso (projectionFormulaMap f.toLRSHom.toShHom
      (DerivedCategory.Q.obj (unitComplex X.toRingedSpace)) (DerivedCategory.Q.obj B)) := by
  have hP : ∀ p q : ℤ, IsIso (Stacks.ProjectionFormula.projectionFormulaMap'
      f.toLRSHom.toShHom ((unitComplex X.toRingedSpace).X p) (B.X q)) := fun p q =>
    isIso_projectionFormulaMap'_of_isAffineHom f _ _ (isQuasicoherent_unitComplex_X _ p) (hBq q)
  have hA : ∀ p, p ≠ (0 : ℤ) → IsZero ((unitComplex X.toRingedSpace).X p) := fun p hp =>
    HomologicalComplex.isZero_single_obj_X (ComplexShape.up ℤ) 0 _ p hp
  have hpull : ∀ q : ℤ,
      ((((modulePullback f.toLRSHom.toShHom).mapHomologicalComplex
        (ComplexShape.up ℤ)).obj B).X q).IsQuasicoherent := fun q =>
    have : (B.X q).IsQuasicoherent := hBq q
    AlgebraicGeometry.SheafOfModules.modulePullback_isQuasicoherent _ (B.X q)
  have hQT : IsIso (pushforwardComparisonQ f.toLRSHom.toShHom
      (((tensorComplex X.toRingedSpace.sheaf).obj (unitComplex X.toRingedSpace)).obj
        ((pullbackComplex f.toLRSHom.toShHom).obj B))) :=
    isIso_pushforwardComparisonQ_of_iso f.toLRSHom.toShHom
      (unitTensorComplexIso X.toRingedSpace ((pullbackComplex f.toLRSHom.toShHom).obj B))
      (isIso_pushforwardComparisonQ_of_isAffineHom f _ hpull)
  exact isIso_projectionFormulaMap_Q_of_iso f.toLRSHom.toShHom (unitComplex X.toRingedSpace) B
    (complexProjectionFormulaIsoOfIsIso f.toLRSHom.toShHom _ B hP 0 hA)
    (ι_complexProjectionFormulaIsoOfIsIso_hom f.toLRSHom.toShHom _ B hP 0 hA)
    (isIso_pushforwardComparisonQ_of_isAffineHom f _
      (isQuasicoherent_unitComplex_X X.toRingedSpace)) hQT hB

/-- **The morphism of [Stacks, Tag 08I9] is invertible for an affine morphism of schemes and any
`K` with a K-flat quasi-coherent model.**  If `K` in `D(𝒪_Y)` is isomorphic to `QB^•` for a
K-flat cochain complex `B^•` of quasi-coherent `𝒪_Y`-modules, then

`Rf_*𝒪_X ⊗^𝐋_{𝒪_Y} K ⟶ Rf_*Lf^*K`

is invertible, with the genuine derived pullback and the genuine derived tensor product.  There
is no hypothesis on the base and no boundedness hypothesis.

Invertibility of the morphism of [Stacks, Tag 08I9] is invertibility of the
projection-formula morphism of [Stacks, Tag 0B53] at the source complex `𝒪_X[0]`, by
`Stacks.Cohomology.DerivedProjectionFormula.isIso_pullbackPushforwardTensorMap`, and that is
`isIso_projectionFormulaMap_Q_unit_of_isAffineHom` transported along the two representations by
`isIso_projectionFormulaMap_congr_left` and `isIso_projectionFormulaMap_congr_right`. -/
theorem isIso_pullbackPushforwardTensorMap_of_kFlatModel [IsAffineHom f]
    (K : DerivedCategory (SheafOfModules.{u} (structureSheafRing Y.toRingedSpace)))
    (B : CochainComplex Y.Modules ℤ) (hBq : ∀ q : ℤ, (B.X q).IsQuasicoherent)
    (hB : Stacks.Cohomology.KFlatDerivedPullback.KFlatComplex Y.toRingedSpace B)
    (e : DerivedCategory.Q.obj B ≅ K) :
    IsIso (pullbackPushforwardTensorMap' f.toLRSHom.toShHom K) := by
  refine (isIso_pullbackPushforwardTensorMap f.toLRSHom.toShHom K).2 ?_
  refine (isIso_projectionFormulaMap_congr_right f.toLRSHom.toShHom _ e).1 ?_
  refine isIso_projectionFormulaMap_congr_left f.toLRSHom.toShHom
    ((DerivedCategory.singleFunctorIsoCompQ
      (SheafOfModules.{u} (structureSheafRing X.toRingedSpace)) 0).app
      (SheafOfModules.unit (structureSheafRing X.toRingedSpace))) _ |>.2 ?_
  exact isIso_projectionFormulaMap_Q_unit_of_isAffineHom f B hBq hB

/-- **The affine case of [Stacks, Tag 08I9], over a spectrum.**  Let `f : X ⟶ Spec R` be an
affine morphism of schemes and let `K` be an object of `D_QCoh(𝒪_{Spec R})`, that is, an object
of `D(𝒪_{Spec R})` all of whose cohomology sheaves are quasi-coherent.  Then the canonical
morphism

`Rf_*𝒪_X ⊗^𝐋_{𝒪_{Spec R}} K ⟶ Rf_*Lf^*K`

is an isomorphism, with the genuine derived pullback `Lf^*` and the genuine derived tensor
product `⊗^𝐋`.  There is no boundedness, flatness or finiteness hypothesis on `K`.

This is the second of the two steps of the source's proof of [Stacks, Tag 08I9].  Every object of
`D_QCoh(𝒪_{Spec R})` is the class of a K-flat complex of quasi-coherent modules, which is
`AlgebraicGeometry.StandardModel.exists_kFlat_isQuasicoherent_model` — the affine dictionary of
[Stacks, Tag 06Z0] followed by a K-flat resolution over `R` and degreewise sheafification — and
on such a representative the statement is
`isIso_pullbackPushforwardTensorMap_of_kFlatModel`.

**The first step, that the question is local on the base, is
`Stacks.Cohomology.DerivedProjectionFormula.isIso_pullbackPushforwardTensorMap_of_openCover` and
is not used here.**  Composing the two gives the tag for an arbitrary base, which is
`AlgebraicGeometry.AffineProjectionFormula.isIso_pullbackPushforwardTensorMap_unconditional`; the
K-flat quasi-coherent representative over an affine scheme that is not a spectrum, which the
restriction of a cover of a general base to an affine open produces, is
`AlgebraicGeometry.exists_kFlat_isQuasicoherent_model_of_isAffine`.

This declaration carries NO `@[stacks 08I9]` attribute. It is the affine case over a spectrum —
the second of the two steps of the source's proof — and a tag belongs only on a declaration
stating the whole of it. The declaration that does so is
`AlgebraicGeometry.AffineProjectionFormula.isIso_pullbackPushforwardTensorMap_unconditional`. -/
theorem isIso_pullbackPushforwardTensorMap_of_isAffineHom {R : CommRingCat.{u}} {W : Scheme.{u}}
    (g : W ⟶ Spec R) [IsAffineHom g] (K : DerivedCategory (Spec R).Modules)
    (hK : ∀ n : ℤ,
      ((DerivedCategory.homologyFunctor (Spec R).Modules n).obj K).IsQuasicoherent) :
    IsIso (pullbackPushforwardTensorMap' g.toLRSHom.toShHom K) := by
  obtain ⟨C, hCq, -, hCk, ⟨e⟩⟩ :=
    AlgebraicGeometry.StandardModel.exists_kFlat_isQuasicoherent_model R K hK
  exact isIso_pullbackPushforwardTensorMap_of_kFlatModel g K C hCq hCk e

end AlgebraicGeometry.AffineProjectionFormula

end
