module

public import StacksFrontier.AlgebraicGeometry.DerivedQCoh.ShiftedStructureSheafTensor
public import StacksFrontier.Topology.Sheaves.Cohomology.DerivedPullback.PullbackTensorCommShiftLegs
public import StacksFrontier.Topology.Sheaves.Cohomology.DerivedPullback.PullbackTensorComplexCoherence
public import StacksFrontier.Topology.Sheaves.Cohomology.DerivedPushforward.ProjectionFormulaUnitCoherence
public import StacksFrontier.Homology.TotalComplexTransportSingle
public import StacksFrontier.Topology.Sheaves.Cohomology.DerivedPullback.SingleUnitComposition
public import StacksFrontier.Topology.Sheaves.Cohomology.DerivedPullback.TotalTensorComplexAlongAComposite

/-!
# The derived pullback carries the degree identification of the cup product to itself

Let `f : (X, 𝒪_X) ⟶ (Y, 𝒪_Y)` be a morphism of ringed spaces and `a, b : ℤ`. The square

```
Lf^*(𝒪_Y[-a-b]) --Lf^*(χ_Y)--> Lf^*(𝒪_Y[-a] ⊗^𝐋 𝒪_Y[-b]) --079U--> Lf^*𝒪_Y[-a] ⊗^𝐋 Lf^*𝒪_Y[-b]
      |                                                                       |
      | ν                                                                     | ν ⊗ ν
      v                                                                       v
 𝒪_X[-a-b] ------------------------------ χ_X ------------------------> 𝒪_X[-a] ⊗^𝐋 𝒪_X[-b]
```

commutes, where `χ` is the degree identification `Stacks.RingedSpace.shiftedUnitTensorIso`, the
top right arrow is the comparison of [Stacks, Tag 079U] and `ν` is the identification
`Stacks.RingedSpace.derivedPullbackShiftedUnitIso` of [Stacks, Tag 01CD] in a shifted degree.

## Main results

* `Stacks.RingedSpace.derivedPullbackShiftedUnitIso_hom_eq`: `ν` in degree `p` is the comparison
  `Lf^*(QK) ⟶ Q(f^*K)` at the complex `𝒪_Y[-p]` followed by the image of the degreewise
  identification `f^*(𝒪_Y[-p]) ≅ 𝒪_X[-p]`.
* `Stacks.RingedSpace.derivedPullbackShiftedUnitIso_comp_shiftedUnitTensorIso`: the square above.

## Implementation notes

All four corners are images of K-flat single complexes, at which the derived pullback, the
derived tensor product and the comparison of Tag 079U are computed by complexes. The
commutation of `Lf^*` with the shift that `ν` is built from is moved onto complexes by the shift
compatibility of `Lf^*(QK) ⟶ Q(f^*K)`, and the square of complexes that remains is checked in
the single degree `a + b`, where it is the left unit coherence of the monoidal structure of `f^*`
on modules. Each step is stated for arbitrary categories, functors and morphisms, and applied by
unification.

## References

* [Stacks Project, Tag 079U](https://stacks.math.columbia.edu/tag/079U)
* [Stacks Project, Tag 0FNH](https://stacks.math.columbia.edu/tag/0FNH)
* [Stacks Project, Tag 01CD](https://stacks.math.columbia.edu/tag/01CD)
* [Stacks Project, Tag 06YJ](https://stacks.math.columbia.edu/tag/06YJ)
-/

@[expose] public noncomputable section

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits MonoidalCategory TopologicalSpace
open Stacks.DerivedTensor.RingedSite
open Stacks.Cohomology.DerivedAdjunctionOnRingedSpaces
open Stacks.Cohomology.DerivedPullbackTensor
open Functor.LaxMonoidal Functor.OplaxMonoidal
open scoped CategoryTheory.Prod

universe u

namespace Stacks.RingedSpace

section Abstract

variable {CY CX DY DX : Type*} [Category CY] [Category CX] [Category DY] [Category DX]

/-- **A shift conjugation moved across a transformation compatible with the shift.** Let
`θ : QY ⋙ L ⟶ P ⋙ QX` commute with the shift by `n`, and let `σY : s0Y⟦n⟧ ≅ spY` and
`σX : s0X⟦n⟧ ≅ spX`. Conjugating `θ.app s0Y ≫ QX.map φ0` by the commutation of `L` with the
shift and by the images of `σY` and `σX` gives `θ.app spY` followed by the image of the
corresponding conjugate of `φ0` on the source side. -/
theorem shift_conj_comp_of_commShift [HasShift CY ℤ] [HasShift CX ℤ] [HasShift DY ℤ]
    [HasShift DX ℤ] (QY : CY ⥤ DY) (QX : CX ⥤ DX) (L : DY ⥤ DX) (P : CY ⥤ CX)
    [QY.CommShift ℤ] [QX.CommShift ℤ] [L.CommShift ℤ] [P.CommShift ℤ]
    (θ : QY ⋙ L ⟶ P ⋙ QX) [NatTrans.CommShift θ ℤ] (n : ℤ) {s0Y spY : CY} {s0X spX : CX}
    (σY : s0Y⟦n⟧ ≅ spY) (σX : s0X⟦n⟧ ≅ spX) (φ0 : P.obj s0Y ⟶ s0X) :
    L.map (QY.map σY.inv ≫ (QY.commShiftIso n).hom.app s0Y) ≫
        (L.commShiftIso n).hom.app (QY.obj s0Y) ≫ (θ.app s0Y ≫ QX.map φ0)⟦n⟧' ≫
          (QX.commShiftIso n).inv.app s0X ≫ QX.map σX.hom =
      θ.app spY ≫ QX.map (P.map σY.inv ≫ (P.commShiftIso n).hom.app s0Y ≫ φ0⟦n⟧' ≫ σX.hom) := by
  have h₁ := NatTrans.shift_app_comm θ n s0Y
  rw [Functor.commShiftIso_comp_hom_app, Functor.commShiftIso_comp_hom_app] at h₁
  simp only [Category.assoc] at h₁
  have h₂ : L.map (QY.map σY.inv) ≫ θ.app (s0Y⟦n⟧) = θ.app spY ≫ QX.map (P.map σY.inv) :=
    θ.naturality σY.inv
  have h₃ : (QX.map φ0)⟦n⟧' ≫ (QX.commShiftIso n).inv.app s0X =
      (QX.commShiftIso n).inv.app (P.obj s0Y) ≫ QX.map (φ0⟦n⟧') :=
    ((QX.commShiftIso n).inv.naturality φ0)
  simp only [Functor.map_comp, Category.assoc]
  rw [reassoc_of% h₁, reassoc_of% h₃, Iso.hom_inv_id_app_assoc, reassoc_of% h₂]

/-- **The tensor square on models.** Let `θ : QY ⋙ L ⟶ P ⋙ QX`, let `tY`, `tX`, `tP` be maps from
tensor products of images to images of model tensor products, the first two invertible, and let
the comparison `c` satisfy `hc` — it is the left model comparison followed by the inverse of the
right one. If each `κ` is `θ` followed by the image of a model map `φ`, if `tX` is natural along
the two factors `φa`, `φb` as `htnat` says, and if the model maps satisfy `hcx`, then the square
of the degree identifications `QX.map τX.inv ≫ inv tX` and `QY.map τY.inv ≫ inv tY` commutes
with `c` and `κ`. -/
theorem tensor_square_of_models (QY : CY ⥤ DY) (QX : CX ⥤ DX) (L : DY ⥤ DX) (P : CY ⥤ CX)
    (θ : QY ⋙ L ⟶ P ⋙ QX) (TY : DY ⥤ DY ⥤ DY) (TX : DX ⥤ DX ⥤ DX)
    {sa sb sab tot : CY} {xa xb xab totx totp : CX}
    (tY : (TY.obj (QY.obj sa)).obj (QY.obj sb) ⟶ QY.obj tot) [IsIso tY]
    (tX : (TX.obj (QX.obj xa)).obj (QX.obj xb) ⟶ QX.obj totx) [IsIso tX]
    (tP : (TX.obj (QX.obj (P.obj sa))).obj (QX.obj (P.obj sb)) ⟶ QX.obj totp)
    (τY : tot ≅ sab) (τX : totx ≅ xab) (μ : P.obj tot ≅ totp)
    (φa : P.obj sa ⟶ xa) (φb : P.obj sb ⟶ xb) (φab : P.obj sab ⟶ xab) (Φ : totp ⟶ totx)
    (htnat : (TX.map (QX.map φa)).app (QX.obj (P.obj sb)) ≫
        (TX.obj (QX.obj xa)).map (QX.map φb) ≫ tX = tP ≫ QX.map Φ)
    (hcx : μ.hom ≫ Φ ≫ τX.hom = P.map τY.hom ≫ φab)
    (c : L.obj ((TY.obj (QY.obj sa)).obj (QY.obj sb)) ⟶
      (TX.obj (L.obj (QY.obj sa))).obj (L.obj (QY.obj sb)))
    (hc : c ≫ (TX.map (θ.app sa)).app (L.obj (QY.obj sb)) ≫
        (TX.obj (QX.obj (P.obj sa))).map (θ.app sb) ≫ tP ≫ QX.map μ.inv =
      L.map tY ≫ θ.app tot)
    (κa : L.obj (QY.obj sa) ⟶ QX.obj xa) (κb : L.obj (QY.obj sb) ⟶ QX.obj xb)
    (κab : L.obj (QY.obj sab) ⟶ QX.obj xab)
    (hκa : κa = θ.app sa ≫ QX.map φa) (hκb : κb = θ.app sb ≫ QX.map φb)
    (hκab : κab = θ.app sab ≫ QX.map φab) :
    κab ≫ QX.map τX.inv ≫ inv tX =
      L.map (QY.map τY.inv ≫ inv tY) ≫ c ≫ (TX.map κa).app (L.obj (QY.obj sb)) ≫
        (TX.obj (QX.obj xa)).map κb := by
  subst hκa hκb hκab
  have hcx' : φab ≫ τX.inv = P.map τY.inv ≫ μ.hom ≫ Φ := by
    rw [← cancel_epi (P.map τY.hom), ← P.map_comp_assoc, τY.hom_inv_id, P.map_id,
      Category.id_comp, ← reassoc_of% hcx, τX.hom_inv_id, Category.comp_id]
  have hc' : c ≫ (TX.map (θ.app sa)).app (L.obj (QY.obj sb)) ≫
      (TX.obj (QX.obj (P.obj sa))).map (θ.app sb) ≫ tP = L.map tY ≫ θ.app tot ≫ QX.map μ.hom := by
    rw [← reassoc_of% hc, ← QX.map_comp, μ.inv_hom_id, QX.map_id, Category.comp_id]
  have hint : (TX.map (QX.map φa)).app (L.obj (QY.obj sb)) ≫
      (TX.obj (QX.obj xa)).map (θ.app sb) =
      (TX.obj (QX.obj (P.obj sa))).map (θ.app sb) ≫
        (TX.map (QX.map φa)).app (QX.obj (P.obj sb)) :=
    ((TX.map (QX.map φa)).naturality (θ.app sb)).symm
  have hnat : L.map (QY.map τY.inv) ≫ θ.app tot = θ.app sab ≫ QX.map (P.map τY.inv) :=
    θ.naturality τY.inv
  rw [← cancel_mono tX]
  simp only [Functor.map_comp, Functor.map_inv, NatTrans.comp_app, Category.assoc,
    IsIso.inv_hom_id, Category.comp_id]
  rw [reassoc_of% hint, htnat, reassoc_of% hc', IsIso.inv_hom_id_assoc, reassoc_of% hnat,
    ← QX.map_comp, ← QX.map_comp, ← QX.map_comp, hcx']

/-- Reassociating a morphism followed by the images of two morphisms under a functor. -/
theorem comp_map_comp_map {C D : Type*} [Category C] [Category D] (G : C ⥤ D) {A : D}
    {x y z : C} (u : A ⟶ G.obj x) (v : x ⟶ y) (w : y ⟶ z) :
    (u ≫ G.map v) ≫ G.map w = u ≫ G.map (v ≫ w) := by
  rw [Category.assoc, G.map_comp]

/-- The component of a morphism of complexes in a degree `i`, read in an equal degree `j`. -/
theorem hom_f_eq_of_eq {V : Type*} [Category V] [Limits.HasZeroMorphisms V]
    {c : ComplexShape ℤ} {K L : HomologicalComplex V c} (φ : K ⟶ L) {i j : ℤ} (h : i = j) :
    φ.f i = (K.XIsoOfEq h).hom ≫ φ.f j ≫ (L.XIsoOfEq h).inv := by
  subst h
  simp

end Abstract

section ComplexLevel

attribute [local instance] monoidalModules symmetricModules monoidalPreadditiveModules
  monoidalClosedModules hasTensorModules modulePullback_preservesAntidiagonalCoproducts
  abelianModulesSheafTensor liftMonoidal

attribute [local implicit_reducible] TopCat.Sheaf structureSheafRing
  StacksDraft.KFlat.modulePullback CategoryTheory.sheafCompose
  AlgebraicGeometry.SheafedSpace.sheaf Stacks.SheafOfModules.Tensor.ringSheaf

variable {X Y : RingedSpace.{u, u}} (f : X ⟶ Y)
  [HasSheafify (Opens.grothendieckTopology X.carrier) AddCommGrpCat.{u}]
  [(Opens.grothendieckTopology X.carrier).WEqualsLocallyBijective AddCommGrpCat.{u}]
  [HasSheafify (Opens.grothendieckTopology Y.carrier) AddCommGrpCat.{u}]
  [(Opens.grothendieckTopology Y.carrier).WEqualsLocallyBijective AddCommGrpCat.{u}]

/-- The comparison `f^*(A ⊗_{𝒪_Y} B) ≅ f^*A ⊗_{𝒪_X} f^*B` of [Stacks, Tag 01CD], at the spelling of
the tensor product of sheaves of modules. -/
def pullbackComparisonIso (A B : AlgebraicGeometry.RingedSpace.KFlatDerivedPullback.Modules Y) :
    (StacksDraft.KFlat.modulePullback f).obj
        (((Stacks.SheafOfModules.Tensor.sheafTensor ⟨(Y).presheaf, (Y).IsSheaf⟩).obj A).obj B) ≅
      ((Stacks.SheafOfModules.Tensor.sheafTensor ⟨(X).presheaf, (X).IsSheaf⟩).obj
        ((StacksDraft.KFlat.modulePullback f).obj A)).obj ((StacksDraft.KFlat.modulePullback f).obj B) :=
  comparisonAppIso f A B

/-- The comparison `f^*𝒪_Y ≅ 𝒪_X`, at the spelling of the tensor product of sheaves of modules. -/
def pullbackUnitIso :
    (StacksDraft.KFlat.modulePullback f).obj
        (SheafOfModules.unit (Stacks.SheafOfModules.Tensor.ringSheaf Y.sheaf)) ≅
      SheafOfModules.unit (Stacks.SheafOfModules.Tensor.ringSheaf X.sheaf) :=
  RingedSpaceModuleAdjunction.modulePullbackObjUnitIso f

/-- `f^*(𝒪_Y[-p]) ≅ 𝒪_X[-p]` on complexes: the degreewise pullback of a single complex is a
single complex, and `f^*𝒪_Y ≅ 𝒪_X`. -/
def pullbackShiftedUnitComplexIso (p : ℤ) :
    (pullbackComplex f).obj (shiftedUnitComplex Y p) ≅ shiftedUnitComplex X p :=
  Functor.singleMapIso (StacksDraft.KFlat.modulePullback f) (pullbackUnitIso f) p

/-- The comparison of total tensor complexes on the summand `(p, q)`, at the spelling of
`pullbackComparisonIso`. -/
theorem ι_pullbackTensorComplexIsoOfIsIso_hom'
    (K L : CochainComplex (AlgebraicGeometry.RingedSpace.KFlatDerivedPullback.Modules Y) ℤ)
    (p q n : ℤ)
    (h : ComplexShape.π (ComplexShape.up ℤ) (ComplexShape.up ℤ) (ComplexShape.up ℤ) (p, q) = n) :
    (StacksDraft.KFlat.modulePullback f).map
          (HomologicalComplex.ιMapBifunctor K L
            (Stacks.SheafOfModules.Tensor.sheafTensor ⟨(Y).presheaf, (Y).IsSheaf⟩) (ComplexShape.up ℤ) p q n h) ≫
        (pullbackTensorComplexIsoOfIsIso f K L).hom.f n =
      (pullbackComparisonIso f (K.X p) (L.X q)).hom ≫
        HomologicalComplex.ιMapBifunctor ((pullbackComplex f).obj K) ((pullbackComplex f).obj L)
          (Stacks.SheafOfModules.Tensor.sheafTensor ⟨(X).presheaf, (X).IsSheaf⟩) (ComplexShape.up ℤ) p q n h :=
  ι_pullbackTensorComplexIsoOfIsIso_hom f K L p q n h

/-- The left unit coherence of `f^*` on the structure sheaf, in the shape the comparison of total
complexes consumes. -/
theorem comparisonAppIso_unit_leftUnitor :
    (comparisonAppIso f (𝟙_ (AlgebraicGeometry.RingedSpace.KFlatDerivedPullback.Modules Y))
          (𝟙_ (AlgebraicGeometry.RingedSpace.KFlatDerivedPullback.Modules Y))).hom ≫
        ((Stacks.SheafOfModules.Tensor.sheafTensor ⟨(X).presheaf, (X).IsSheaf⟩).map
          (RingedSpaceModuleAdjunction.modulePullbackObjUnitIso f).hom).app
          ((StacksDraft.KFlat.modulePullback f).obj
            (𝟙_ (AlgebraicGeometry.RingedSpace.KFlatDerivedPullback.Modules Y))) ≫
        ((Stacks.SheafOfModules.Tensor.sheafTensor ⟨(X).presheaf, (X).IsSheaf⟩).obj
          (𝟙_ (AlgebraicGeometry.RingedSpace.KFlatDerivedPullback.Modules X))).map
          (RingedSpaceModuleAdjunction.modulePullbackObjUnitIso f).hom ≫
        (λ_ (𝟙_ (AlgebraicGeometry.RingedSpace.KFlatDerivedPullback.Modules X))).hom =
      (StacksDraft.KFlat.modulePullback f).map
          (λ_ (𝟙_ (AlgebraicGeometry.RingedSpace.KFlatDerivedPullback.Modules Y))).hom ≫
        (RingedSpaceModuleAdjunction.modulePullbackObjUnitIso f).hom := by
  have hδ : δ (StacksDraft.KFlat.modulePullback f)
      (𝟙_ (AlgebraicGeometry.RingedSpace.KFlatDerivedPullback.Modules Y))
      (𝟙_ (AlgebraicGeometry.RingedSpace.KFlatDerivedPullback.Modules Y)) =
      (comparisonAppIso f (𝟙_ (AlgebraicGeometry.RingedSpace.KFlatDerivedPullback.Modules Y))
        (𝟙_ (AlgebraicGeometry.RingedSpace.KFlatDerivedPullback.Modules Y))).hom :=
    isComparisonTensorator_sheafTensor f _ _
  have hε : ε (StacksDraft.KFlat.modulePullback f) =
      (RingedSpaceModuleAdjunction.modulePullbackObjUnitIso f).inv :=
    isComparisonUnit_sheafTensor f
  have hη : η (StacksDraft.KFlat.modulePullback f) =
      (RingedSpaceModuleAdjunction.modulePullbackObjUnitIso f).hom := by
    rw [← cancel_mono (ε (StacksDraft.KFlat.modulePullback f)), Functor.Monoidal.η_ε, hε,
      Iso.hom_inv_id]
  have hnat : ((Stacks.SheafOfModules.Tensor.sheafTensor ⟨(X).presheaf, (X).IsSheaf⟩).obj
        (𝟙_ (AlgebraicGeometry.RingedSpace.KFlatDerivedPullback.Modules X))).map
        (RingedSpaceModuleAdjunction.modulePullbackObjUnitIso f).hom ≫
        (λ_ (𝟙_ (AlgebraicGeometry.RingedSpace.KFlatDerivedPullback.Modules X))).hom =
      (λ_ ((StacksDraft.KFlat.modulePullback f).obj
          (𝟙_ (AlgebraicGeometry.RingedSpace.KFlatDerivedPullback.Modules Y)))).hom ≫
        (RingedSpaceModuleAdjunction.modulePullbackObjUnitIso f).hom :=
    MonoidalCategory.leftUnitor_naturality
      (C := AlgebraicGeometry.RingedSpace.KFlatDerivedPullback.Modules X)
      (RingedSpaceModuleAdjunction.modulePullbackObjUnitIso f).hom
  rw [Functor.Monoidal.map_leftUnitor, hδ, hη, hnat]
  rfl

/-- The left unit coherence of `f^*` on the structure sheaf, at the spelling of
`pullbackComparisonIso`, `pullbackUnitIso` and `Stacks.RingedSpace.unitTensorUnitIso`. -/
theorem pullbackComparisonIso_unit :
    (pullbackComparisonIso f (SheafOfModules.unit (Stacks.SheafOfModules.Tensor.ringSheaf Y.sheaf))
          (SheafOfModules.unit (Stacks.SheafOfModules.Tensor.ringSheaf Y.sheaf))).hom ≫
        ((Stacks.SheafOfModules.Tensor.sheafTensor ⟨(X).presheaf, (X).IsSheaf⟩).map (pullbackUnitIso f).hom).app
          ((StacksDraft.KFlat.modulePullback f).obj
            (SheafOfModules.unit (Stacks.SheafOfModules.Tensor.ringSheaf Y.sheaf))) ≫
        ((Stacks.SheafOfModules.Tensor.sheafTensor ⟨(X).presheaf, (X).IsSheaf⟩).obj
          (SheafOfModules.unit (Stacks.SheafOfModules.Tensor.ringSheaf X.sheaf))).map
          (pullbackUnitIso f).hom ≫ (unitTensorUnitIso X).hom =
      (StacksDraft.KFlat.modulePullback f).map (unitTensorUnitIso Y).hom ≫
        (pullbackUnitIso f).hom :=
  comparisonAppIso_unit_leftUnitor f

/-- The comparison of total tensor complexes at two shifted structure sheaves, on the summand
`(a, b)`. -/
theorem ι_pullbackTensorComplexIsoOfIsIso_shiftedUnit (a b : ℤ) :
    (StacksDraft.KFlat.modulePullback f).map
          (HomologicalComplex.ιMapBifunctor (shiftedUnitComplex Y a) (shiftedUnitComplex Y b)
            (Stacks.SheafOfModules.Tensor.sheafTensor ⟨(Y).presheaf, (Y).IsSheaf⟩) (ComplexShape.up ℤ) a b (a + b)
            rfl) ≫
        (pullbackTensorComplexIsoOfIsIso f (shiftedUnitComplex Y a)
          (shiftedUnitComplex Y b)).hom.f (a + b) =
      (pullbackComparisonIso f ((shiftedUnitComplex Y a).X a)
          ((shiftedUnitComplex Y b).X b)).hom ≫
        HomologicalComplex.ιMapBifunctor ((pullbackComplex f).obj (shiftedUnitComplex Y a))
          ((pullbackComplex f).obj (shiftedUnitComplex Y b))
          (Stacks.SheafOfModules.Tensor.sheafTensor ⟨(X).presheaf, (X).IsSheaf⟩) (ComplexShape.up ℤ) a b (a + b) rfl :=
  ι_pullbackTensorComplexIsoOfIsIso_hom' f _ _ a b (a + b) rfl

/-- The comparison of total complexes of [Stacks, Tag 01CD] at two shifted structure sheaves,
against the identifications of both total complexes with a shifted structure sheaf. -/
theorem pullbackTensorComplexIso_shiftedUnit (a b : ℤ) :
    (pullbackTensorComplexIsoOfIsIso f (shiftedUnitComplex Y a) (shiftedUnitComplex Y b)).hom ≫
        HomologicalComplex.mapBifunctorMap (pullbackShiftedUnitComplexIso f a).hom
          (pullbackShiftedUnitComplexIso f b).hom
          (Stacks.SheafOfModules.Tensor.sheafTensor ⟨(X).presheaf, (X).IsSheaf⟩) (ComplexShape.up ℤ) ≫
        (shiftedUnitComplexTensorIso X a b).hom =
      (pullbackComplex f).map (shiftedUnitComplexTensorIso Y a b).hom ≫
        (pullbackShiftedUnitComplexIso f (a + b)).hom := by
  haveI : (StacksDraft.KFlat.modulePullback f).Additive :=
    StacksDraft.KFlat.modulePullback_additive f
  refine Functor.total_single_single_comp
    (Stacks.SheafOfModules.Tensor.sheafTensor ⟨(Y).presheaf, (Y).IsSheaf⟩)
    (Stacks.SheafOfModules.Tensor.sheafTensor ⟨(X).presheaf, (X).IsSheaf⟩) (StacksDraft.KFlat.modulePullback f)
    (pullbackComparisonIso f) ?_ ?_ (pullbackUnitIso f) (unitTensorUnitIso Y) (unitTensorUnitIso X)
    ?_ a b (pullbackTensorComplexIsoOfIsIso f (shiftedUnitComplex Y a)
      (shiftedUnitComplex Y b)).hom ?_
  · exact fun {_ _} w B => comparisonAppIso_naturality_left f w B
  · exact fun A {_ _} w => comparisonAppIso_naturality_right f A w
  · exact pullbackComparisonIso_unit f
  · exact ι_pullbackTensorComplexIsoOfIsIso_shiftedUnit f a b

end ComplexLevel

section Concrete

attribute [local instance] HasDerivedCategory.standard

open Stacks.Cohomology.DerivedProjectionFormula (pullbackTensorComparison
  pullbackTensorComparison_app_q_of_kFlat)
open Stacks.Cohomology.KFlatDerivedPullback (derivedPullback_commShift)

attribute [local instance] modulePullback_preservesAntidiagonalCoproducts

attribute [local implicit_reducible] TopCat.Sheaf structureSheafRing
  StacksDraft.KFlat.modulePullback CategoryTheory.sheafCompose
  AlgebraicGeometry.SheafedSpace.sheaf Stacks.SheafOfModules.Tensor.ringSheaf

variable {X Y : RingedSpace.{u, u}} (f : X ⟶ Y)
  [HasSheafify (Opens.grothendieckTopology X.carrier) AddCommGrpCat.{u}]
  [(Opens.grothendieckTopology X.carrier).WEqualsLocallyBijective AddCommGrpCat.{u}]
  [HasSheafify (Opens.grothendieckTopology Y.carrier) AddCommGrpCat.{u}]
  [(Opens.grothendieckTopology Y.carrier).WEqualsLocallyBijective AddCommGrpCat.{u}]

/-- **The identification `Lf^*(𝒪_Y[0]) ≅ 𝒪_X[0]` on representatives**: it is the comparison
`Lf^*(QK) ⟶ Q(f^*K)` at `K = 𝒪_Y[0]` followed by the image of `pullbackShiftedUnitComplexIso`. -/
theorem derivedPullbackSingleUnitIso_hom_eq :
    (derivedPullbackSingleUnitIso f).hom =
      (derivedPullbackNatTrans f).app (shiftedUnitComplex Y 0) ≫
        DerivedCategory.Q.map (pullbackShiftedUnitComplexIso f 0).hom := by
  have h : (derivedPullbackSingleUnitIso f).hom =
      (Stacks.Cohomology.FlatSingleDerivedPullback.derivedPullbackSingleIso f
          (SheafOfModules.unit (Stacks.SheafOfModules.Tensor.ringSheaf Y.sheaf))
          (isFlat_unit_of_ringedSpace Y)).hom ≫
        (DerivedCategory.singleFunctor _ 0).map (pullbackObjUnitIso f).hom := rfl
  rw [h, StacksDraft.UnitPullbackComposition.derivedPullbackSingleIso_hom]
  exact comp_map_comp_map DerivedCategory.Q _ _ _

/-- The shift isomorphism `𝒪_Z[0]⟦-p⟧ ≅ 𝒪_Z[-p]` of the complexes. -/
abbrev shiftedUnitComplexShiftIso (Z : RingedSpace.{u, u}) (p : ℤ) :
    (shiftedUnitComplex Z 0)⟦-p⟧ ≅ shiftedUnitComplex Z p :=
  ((CochainComplex.singleFunctors _).shiftIso (-p) p 0 (by omega)).app _

/-- `shiftedUnitShiftIso` is the image of the shift isomorphism of the complexes, read through
the commutation of `Q` with the shift. -/
theorem shiftedUnitShiftIso_inv_eq (Z : RingedSpace.{u, u}) (p : ℤ) :
    (shiftedUnitShiftIso Z p).inv =
      DerivedCategory.Q.map (shiftedUnitComplexShiftIso Z p).inv ≫
        (DerivedCategory.Q.commShiftIso (-p)).hom.app (shiftedUnitComplex Z 0) :=
  SingleFunctors.postcomp_shiftIso_inv_app ..

/-- The same, for the forward direction. -/
theorem shiftedUnitShiftIso_hom_eq (Z : RingedSpace.{u, u}) (p : ℤ) :
    (shiftedUnitShiftIso Z p).hom =
      (DerivedCategory.Q.commShiftIso (-p)).inv.app (shiftedUnitComplex Z 0) ≫
        DerivedCategory.Q.map (shiftedUnitComplexShiftIso Z p).hom :=
  SingleFunctors.postcomp_shiftIso_hom_app ..

/-- The degreewise pullback of the shift isomorphism of the single complexes, against the
comparison `pullbackShiftedUnitComplexIso` in degrees `0` and `p`. -/
theorem pullbackShiftedUnitComplexIso_shift (p : ℤ) :
    (pullbackComplex f).map (shiftedUnitComplexShiftIso Y p).inv ≫
        ((pullbackComplex f).commShiftIso (-p)).hom.app (shiftedUnitComplex Y 0) ≫
        (pullbackShiftedUnitComplexIso f 0).hom⟦-p⟧' ≫ (shiftedUnitComplexShiftIso X p).hom =
      (pullbackShiftedUnitComplexIso f p).hom := by
  apply HomologicalComplex.to_single_hom_ext
  simp [shiftedUnitComplexShiftIso, pullbackShiftedUnitComplexIso, Functor.singleMapIso,
    pullbackUnitIso, CochainComplex.singleFunctors, HomologicalComplex.singleObjXSelf,
    HomologicalComplex.singleObjXIsoOfEq, HomologicalComplex.single_map_f_self, eqToHom_map,
    hom_f_eq_of_eq _ (add_neg_cancel p), HomologicalComplex.XIsoOfEq]

/-- **The identification `Lf^*(𝒪_Y[-p]) ≅ 𝒪_X[-p]` on representatives**: it is the comparison
`Lf^*(QK) ⟶ Q(f^*K)` at `K = 𝒪_Y[-p]` followed by the image of
`pullbackShiftedUnitComplexIso`. The commutation of `Lf^*` with the shift it is built from is
moved onto complexes by the shift compatibility of the comparison. -/
theorem derivedPullbackShiftedUnitIso_hom_eq (p : ℤ) :
    (derivedPullbackShiftedUnitIso f p).hom =
      (derivedPullbackNatTrans f).app (shiftedUnitComplex Y p) ≫
        DerivedCategory.Q.map (pullbackShiftedUnitComplexIso f p).hom := by
  letI := derivedPullback_commShift f
  letI := derivedPullbackNatTrans_commShift f
  have h : (derivedPullbackShiftedUnitIso f p).hom =
      (derivedPullback f).map (shiftedUnitShiftIso Y p).inv ≫
        ((derivedPullback f).commShiftIso (-p)).hom.app (shiftedUnitObject Y 0) ≫
        ((derivedPullbackSingleUnitIso f).hom)⟦-p⟧' ≫ (shiftedUnitShiftIso X p).hom := rfl
  rw [h, shiftedUnitShiftIso_inv_eq, shiftedUnitShiftIso_hom_eq,
    derivedPullbackSingleUnitIso_hom_eq]
  exact (shift_conj_comp_of_commShift DerivedCategory.Q DerivedCategory.Q (derivedPullback f)
    (pullbackComplex f) (derivedPullbackNatTrans f) (-p) (shiftedUnitComplexShiftIso Y p)
    (shiftedUnitComplexShiftIso X p) (pullbackShiftedUnitComplexIso f 0).hom).trans
    (congrArg (fun g => (derivedPullbackNatTrans f).app (shiftedUnitComplex Y p) ≫
      DerivedCategory.Q.map g) (pullbackShiftedUnitComplexIso_shift f p))

/-- **The derived pullback carries the degree identification of the cup product on `Y` to the
one on `X`.** For a morphism of ringed spaces `f : X ⟶ Y` and `a, b : ℤ`, the identification
`𝒪[-a-b] ≅ 𝒪[-a] ⊗^𝐋 𝒪[-b]` of `shiftedUnitTensorIso` on `X` and the derived pullback of the
one on `Y` agree, through the comparison of [Stacks, Tag 079U] and the identifications
`Lf^*(𝒪_Y[-p]) ≅ 𝒪_X[-p]`. -/
theorem derivedPullbackShiftedUnitIso_comp_shiftedUnitTensorIso (a b : ℤ) :
    (derivedPullbackShiftedUnitIso f (a + b)).hom ≫ (shiftedUnitTensorIso X a b).hom =
      (derivedPullback f).map (shiftedUnitTensorIso Y a b).hom ≫
        (pullbackTensorComparison f).app (shiftedUnitObject Y a, shiftedUnitObject Y b) ≫
        ((derivedTensorProductFunctor X.sheaf).map (derivedPullbackShiftedUnitIso f a).hom).app
          ((derivedPullback f).obj (shiftedUnitObject Y b)) ≫
        ((derivedTensorProductFunctor X.sheaf).obj (shiftedUnitObject X a)).map
          (derivedPullbackShiftedUnitIso f b).hom := by
  have hKa := Stacks.SheafOfModules.isKFlat_single_obj_unit (toRingedSite Y).O a
  have hKb := Stacks.SheafOfModules.isKFlat_single_obj_unit (toRingedSite Y).O b
  have hc := pullbackTensorComparison_app_q_of_kFlat f (shiftedUnitComplex Y a)
    (shiftedUnitComplex Y b) hKa hKb
  have hrc := isIso_rightComparison_app f (shiftedUnitComplex Y a) (shiftedUnitComplex Y b) hKa hKb
  have hlc := isIso_leftComparison_app f (shiftedUnitComplex Y a) (shiftedUnitComplex Y b) hKa hKb
  have hmodel : (modelComparison f (shiftedUnitComplex Y a) (shiftedUnitComplex Y b) hKa hKb).hom ≫
      (rightComparison f).app (shiftedUnitComplex Y a, shiftedUnitComplex Y b) =
      (leftComparison f).app (shiftedUnitComplex Y a, shiftedUnitComplex Y b) := by
    dsimp only [modelComparison, Iso.trans_hom, asIso_hom, Iso.symm_hom, asIso_inv]
    rw [Category.assoc, IsIso.inv_hom_id, Category.comp_id]
  rw [← hc] at hmodel
  haveI := isIso_toTensor_shiftedUnitComplex Y a b
  haveI := isIso_toTensor_shiftedUnitComplex X a b
  dsimp only [rightComparison, leftComparison, NatTrans.comp_app, Functor.whiskerRight_app,
    Functor.whiskerLeft_app, derivedToTensorNatTrans, NatTrans.prod, Functor.prod_obj,
    Functor.uncurry_obj_map, Functor.uncurry_obj_obj, Functor.comp_obj, Functor.comp_map] at hmodel
  simp only [Category.assoc] at hmodel
  rw [pullbackTensorComplexNatIso_inv_app] at hmodel
  exact tensor_square_of_models DerivedCategory.Q DerivedCategory.Q (derivedPullback f)
    (pullbackComplex f) (derivedPullbackNatTrans f) (derivedTensorProductFunctor Y.sheaf)
    (derivedTensorProductFunctor X.sheaf)
    ((canonicalDerivedTensorProduct Y.sheaf).toTensor (shiftedUnitComplex Y a)
      (shiftedUnitComplex Y b))
    ((canonicalDerivedTensorProduct X.sheaf).toTensor (shiftedUnitComplex X a)
      (shiftedUnitComplex X b))
    ((canonicalDerivedTensorProduct X.sheaf).toTensor
      ((pullbackComplex f).obj (shiftedUnitComplex Y a))
      ((pullbackComplex f).obj (shiftedUnitComplex Y b)))
    (shiftedUnitComplexTensorIso Y a b) (shiftedUnitComplexTensorIso X a b)
    (pullbackTensorComplexIsoOfIsIso f (shiftedUnitComplex Y a) (shiftedUnitComplex Y b))
    (pullbackShiftedUnitComplexIso f a).hom (pullbackShiftedUnitComplexIso f b).hom
    (pullbackShiftedUnitComplexIso f (a + b)).hom
    (HomologicalComplex.mapBifunctorMap (pullbackShiftedUnitComplexIso f a).hom
      (pullbackShiftedUnitComplexIso f b).hom
      (Stacks.SheafOfModules.Tensor.sheafTensor ⟨(X).presheaf, (X).IsSheaf⟩) (ComplexShape.up ℤ))
    ((canonicalDerivedTensorProduct X.sheaf).toTensor_naturality _ _)
    (pullbackTensorComplexIso_shiftedUnit f a b)
    _ hmodel _ _ _ (derivedPullbackShiftedUnitIso_hom_eq f a)
    (derivedPullbackShiftedUnitIso_hom_eq f b) (derivedPullbackShiftedUnitIso_hom_eq f (a + b))

end Concrete

end Stacks.RingedSpace

end
