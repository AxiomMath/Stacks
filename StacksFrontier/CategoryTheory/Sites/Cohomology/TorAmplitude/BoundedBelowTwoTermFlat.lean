module

public import Mathlib.Algebra.Homology.DerivedCategory.SingleTriangle
public import StacksFrontier.CategoryTheory.Sites.Cohomology.TorAmplitude.BoundedBelowTensor
public import StacksFrontier.CategoryTheory.Sites.Cohomology.Simplicial.SimplicialFlatResolution
public import StacksFrontier.Algebra.Category.ModuleCat.Sheaf.FlatRetract

/-!
# Flat dimension at most one bounds the derived tensor product of bounded below objects

Let `(C, O)` be a ringed site on which every `O`-module `G` has a resolution
`0 ⟶ K ⟶ P ⟶ G ⟶ 0` by two flat modules (for instance the constant sheaf of rings `ℤ` on any
site). Then every object `W` of `D(O)` whose cohomology vanishes below `b` has Tor amplitude in
`[b - 1, ∞]`, and for `E` with cohomology vanishing below `a` the cohomology of `E ⊗^L_O W`
vanishes below `a + b - 1`.

For the first statement, tensor `W` with the distinguished triangle `K[0] ⟶ P[0] ⟶ G[0] ⟶`: a flat
module in degree `0` is K-flat, so `W ⊗^L_O P[0]` and `W ⊗^L_O K[0]` are total tensor complexes of
a representative of `W` vanishing below `b` with a module in degree `0`, and vanish below `b`; the
triangle puts `W ⊗^L_O G[0]` in degrees `≥ b - 1`. The second statement then follows from a K-flat
representative of `W` vanishing below `b - 1` (Stacks 0F1M), which computes the derived tensor
product with any left factor.

## Main results

* `Stacks.SheafOfModules.DerivedTensorProduct.isGE_tensor_singleFunctor_of_isFlat`
* `Stacks.SheafOfModules.DerivedTensorProduct.hasTorAmplitudeGE_of_isGE_of_twoTermFlat`
* `Stacks.SheafOfModules.DerivedTensorProduct.isGE_tensor_of_isGE_of_twoTermFlat`

## References

* [Stacks Project, Tag 0F1M](https://stacks.math.columbia.edu/tag/0F1M)
* [Stacks Project, Tag 06YQ](https://stacks.math.columbia.edu/tag/06YQ)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits CategoryTheory.Pretriangulated AlgebraicGeometry

universe u d

namespace Stacks.SheafOfModules.DerivedTensorProduct

variable {X : RingedSite.{u, u, u}}
  [HasSheafify X.J AddCommGrpCat.{u}]
  [X.J.WEqualsLocallyBijective AddCommGrpCat.{u}]
  [HasDerivedCategory.{d} (RingedSite.Modules.{u, u, u} X)]
  [(Stacks.SheafOfModules.Tensor.sheafTensor.{u, u, u, u, u} X.O).Additive]
  [∀ M, ((Stacks.SheafOfModules.Tensor.sheafTensor.{u, u, u, u, u} X.O).obj M).Additive]
  [∀ (K L : CochainComplex (RingedSite.Modules.{u, u, u} X) ℤ),
    HomologicalComplex.HasMapBifunctor K L (Stacks.SheafOfModules.Tensor.sheafTensor X.O)
      (ComplexShape.up ℤ)]

omit [HasDerivedCategory.{d} (RingedSite.Modules.{u, u, u} X)] in
/-- A flat module placed in degree `0` is a K-flat complex (Stacks 06YQ). -/
theorem isKFlat_single_of_isFlat (P : RingedSite.Modules.{u, u, u} X)
    (hP : AlgebraicGeometry.SheafOfModules.IsFlat.{u, u, u, u} (O := X.O) P) :
    IsKFlat X.O ((HomologicalComplex.single _ (ComplexShape.up ℤ) 0).obj P) := by
  refine kFlat_of_boundedAbove_of_flat X.O _ ⟨0, inferInstance⟩ fun i => ?_
  by_cases h : i = 0
  · subst h
    exact Stacks.SheafOfModules.FlatRetract.isFlat_of_iso X.O
      (HomologicalComplex.singleObjXSelf (ComplexShape.up ℤ) 0 P).symm hP
  · exact Stacks.SimplicialModules.isFlat_of_isZero X.O
      (HomologicalComplex.isZero_single_obj_X (ComplexShape.up ℤ) 0 P i h)

/-- **Tensoring a bounded below object with a flat module in degree `0` keeps the bound.** If the
cohomology of `W` vanishes below `b` and `P` is flat, so does that of `W ⊗^L_O P[0]`: `P[0]` is
K-flat, so the derived tensor product is the total tensor complex of a representative of `W`
vanishing below `b` with `P[0]`. -/
theorem isGE_tensor_singleFunctor_of_isFlat (T : DerivedTensorProduct.{u, u, u, d} X)
    (W : RingedSite.DerivedModules.{u, u, u, d} X) (b : ℤ) (hW : W.IsGE b)
    (P : RingedSite.Modules.{u, u, u} X)
    (hP : AlgebraicGeometry.SheafOfModules.IsFlat.{u, u, u, u} (O := X.O) P) :
    ((T.tensor.obj W).obj ((DerivedCategory.singleFunctor _ 0).obj P)).IsGE b := by
  have := hW
  obtain ⟨Z, hZ, ⟨eZ⟩⟩ := W.exists_iso_Q_obj_of_isGE b
  have := hZ
  have hS := isKFlat_single_of_isFlat P hP
  have hTot : (DerivedCategory.Q.obj (HomologicalComplex.mapBifunctor Z
      ((HomologicalComplex.single _ (ComplexShape.up ℤ) 0).obj P)
      (Stacks.SheafOfModules.Tensor.sheafTensor X.O) (ComplexShape.up ℤ))).IsGE (b + 0) := by
    rw [DerivedCategory.isGE_Q_obj_iff]
    have := isStrictlyGE_mapBifunctor Z
      ((HomologicalComplex.single _ (ComplexShape.up ℤ) 0).obj P) b 0
    infer_instance
  rw [add_zero] at hTot
  exact DerivedCategory.TStructure.t.isGE_of_iso (X := DerivedCategory.Q.obj
    (HomologicalComplex.mapBifunctor Z ((HomologicalComplex.single _ (ComplexShape.up ℤ) 0).obj P)
      (Stacks.SheafOfModules.Tensor.sheafTensor X.O) (ComplexShape.up ℤ)))
    ((T.comparisonRight Z _ hS).symm ≪≫
      (T.tensor.obj (DerivedCategory.Q.obj Z)).mapIso
        ((DerivedCategory.singleFunctorIsoCompQ _ 0).app P).symm ≪≫
      (T.tensor.mapIso eZ.symm).app _) b

/-- The hypothesis that every module `G` has a resolution `0 ⟶ K ⟶ P ⟶ G ⟶ 0` by two flat
modules. -/
def HasTwoTermFlatResolutions (X : RingedSite.{u, u, u})
    [HasSheafify X.J AddCommGrpCat.{u}] [X.J.WEqualsLocallyBijective AddCommGrpCat.{u}] : Prop :=
  ∀ G : RingedSite.Modules.{u, u, u} X, ∃ S : ShortComplex (RingedSite.Modules.{u, u, u} X),
    S.ShortExact ∧ AlgebraicGeometry.SheafOfModules.IsFlat.{u, u, u, u} (O := X.O) S.X₁ ∧
      AlgebraicGeometry.SheafOfModules.IsFlat.{u, u, u, u} (O := X.O) S.X₂ ∧ Nonempty (S.X₃ ≅ G)

/-- **Flat dimension at most one gives Tor amplitude `[b - 1, ∞]` to `D^{≥ b}`.** If every module
has a resolution by two flat modules, every object of `D(O)` whose cohomology vanishes below `b`
has Tor amplitude in `[b - 1, ∞]`. -/
theorem hasTorAmplitudeGE_of_isGE_of_twoTermFlat (T : DerivedTensorProduct.{u, u, u, d} X)
    (h2 : HasTwoTermFlatResolutions X) (W : RingedSite.DerivedModules.{u, u, u, d} X) (b : ℤ)
    (hW : W.IsGE b) : HasTorAmplitudeGE T W (b - 1) := by
  intro G i hi
  obtain ⟨S, hS, hK, hP, ⟨e⟩⟩ := h2 G
  let := T.commShift₂.commShiftObj W
  have := T.exact_right W
  have hT := (T.tensor.obj W).map_distinguished _ hS.singleTriangle_distinguished
  have hT' := rot_of_distTriang _ hT
  have h₁ : ((T.tensor.obj W).obj ((DerivedCategory.singleFunctor _ 0).obj S.X₂)).IsGE (b - 1) :=
    have := isGE_tensor_singleFunctor_of_isFlat T W b hW S.X₂ hP
    DerivedCategory.TStructure.t.isGE_of_ge _ (b - 1) b (by omega)
  have h₃ : ((((T.tensor.obj W).obj
      ((DerivedCategory.singleFunctor _ 0).obj S.X₁))⟦(1 : ℤ)⟧)).IsGE (b - 1) := by
    have := isGE_tensor_singleFunctor_of_isFlat T W b hW S.X₁ hK
    exact DerivedCategory.TStructure.t.isGE_shift _ b 1 (b - 1)
  have hG : ((T.tensor.obj W).obj ((DerivedCategory.singleFunctor _ 0).obj S.X₃)).IsGE (b - 1) :=
    DerivedCategory.TStructure.t.isGE₂ _ hT' (b - 1) h₁ h₃
  have hG' : ((T.tensor.obj W).obj ((DerivedCategory.singleFunctor _ 0).obj G)).IsGE (b - 1) :=
    DerivedCategory.TStructure.t.isGE_of_iso
      ((T.tensor.obj W).mapIso ((DerivedCategory.singleFunctor _ 0).mapIso e)) (b - 1)
  exact DerivedCategory.isZero_of_isGE _ (b - 1) i hi

/-- **Flat dimension at most one bounds the derived tensor product of bounded below objects.** If
every module has a resolution by two flat modules, and the cohomology of `E` and `W` vanishes
below `a` and below `b`, then that of `E ⊗^L_O W` vanishes below `a + b - 1`: `W` has Tor
amplitude in `[b - 1, ∞]`, so it is represented by a K-flat complex vanishing below `b - 1`
(Stacks 0F1M), which computes the derived tensor product with a representative of `E` vanishing
below `a`. -/
theorem isGE_tensor_of_isGE_of_twoTermFlat (T : DerivedTensorProduct.{u, u, u, d} X)
    (h2 : HasTwoTermFlatResolutions X) (E W : RingedSite.DerivedModules.{u, u, u, d} X)
    (a b : ℤ) (hE : E.IsGE a) (hW : W.IsGE b) :
    ((T.tensor.obj E).obj W).IsGE (a + b - 1) := by
  obtain ⟨P, hPflat, -, hPzero, ⟨eP⟩⟩ :=
    (hasTorAmplitudeGE_iff_exists_kFlatRepresentative T W (b - 1)).1
      (hasTorAmplitudeGE_of_isGE_of_twoTermFlat T h2 W b hW)
  have := hE
  obtain ⟨Z, hZ, ⟨eZ⟩⟩ := E.exists_iso_Q_obj_of_isGE a
  have := hZ
  have hPGE : CochainComplex.IsStrictlyGE P (b - 1) := by
    rw [CochainComplex.isStrictlyGE_iff]; exact hPzero
  have hTot : (DerivedCategory.Q.obj (HomologicalComplex.mapBifunctor Z P
      (Stacks.SheafOfModules.Tensor.sheafTensor X.O) (ComplexShape.up ℤ))).IsGE (a + (b - 1)) := by
    rw [DerivedCategory.isGE_Q_obj_iff]
    have := isStrictlyGE_mapBifunctor Z P a (b - 1)
    infer_instance
  rw [← add_sub_assoc] at hTot
  exact DerivedCategory.TStructure.t.isGE_of_iso (X := DerivedCategory.Q.obj
    (HomologicalComplex.mapBifunctor Z P (Stacks.SheafOfModules.Tensor.sheafTensor X.O)
      (ComplexShape.up ℤ)))
    ((T.comparisonRight Z P hPflat).symm ≪≫ (T.tensor.obj (DerivedCategory.Q.obj Z)).mapIso eP ≪≫
      (T.tensor.mapIso eZ.symm).app W) (a + b - 1)

end Stacks.SheafOfModules.DerivedTensorProduct

end
