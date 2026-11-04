module

public import StacksFrontier.AlgebraicGeometry.BaseChange.TorIndependence.DerivedBaseChangeGlobal
public import StacksFrontier.AlgebraicGeometry.DerivedAffineMorphism.PushforwardTExactness
public import StacksFrontier.AlgebraicGeometry.Duality.DerivedPushforward.QuasicoherentWeakSerre
public import StacksFrontier.Homology.DerivedCategory.IsZero
import StacksCore.Tactic.StacksAttribute

/-!
# [Stacks, Tag 08I8]: the derived direct image along an affine morphism reflects isomorphisms

Let `f : W ⟶ Y` be an affine morphism of schemes.  A morphism `α : E ⟶ F` of complexes of
`𝒪_W`-modules with quasi-coherent cohomology is invertible in `D(𝒪_W)` as soon as `Rf_*α` is
invertible in `D(𝒪_Y)`.  That is [Stacks, Tag 08I8], the assertion that

`Rf_* : D_QCoh(𝒪_W) ⥤ D_QCoh(𝒪_Y)`

reflects isomorphisms.

The proof is the cone.  Complexes with quasi-coherent cohomology form a strictly full saturated
triangulated subcategory of `D(𝒪_W)`
(`Stacks.AlgebraicGeometry.QuasicoherentWeakSerre.derivedQuasicoherent_isTriangulated`), so `α`
fits into a distinguished triangle `E ⟶ F ⟶ C ⟶ E⟦1⟧` whose third vertex again has
quasi-coherent cohomology.  `Rf_*` is exact, being the right adjoint of the exact functor `Lf^*`,
so it carries that triangle to a distinguished one, in which `Rf_*α` invertible forces
`Rf_*C = 0`.  Along an affine morphism the direct image detects vanishing of cohomology on
complexes with quasi-coherent cohomology — `H^i(Rf_*C) = f_*H^i(C)` and `f_*` is conservative on
quasi-coherent modules, which is
`Stacks.AlgebraicGeometry.AffinePushforwardTExactness.isZero_homology_derivedPushforward_iff` —
so every `H^i(C)` vanishes, `C = 0`, and `α` is invertible.

## Main results

* `Stacks.AlgebraicGeometry.AffinePushforwardTExactness.isIso_of_isIso_derivedPushforward`:
  **[Stacks, Tag 08I8]**.

## Implementation notes

The source reduces to a morphism of affine schemes by working locally on the base and then reads
the two quasi-coherent derived categories off [Stacks, Tag 06Z0];
`AlgebraicGeometry.reflectsIsomorphisms_derivedQuasicoherentPushforward_specMap` is that reduced
case, at the functor `AlgebraicGeometry.derivedQuasicoherentPushforward` and the locally small
model.  No localization is needed here, because the t-exactness of `Rf_*` along an affine
morphism is already available at an arbitrary base.

The model of the derived category is `CategoryTheory.HasDerivedCategory.standard`, made a local
instance, which is the model
`Stacks.Cohomology.DerivedAdjunctionOnRingedSpaces.derivedPushforward` and the base-change
development are read at.  The shift datum on `Rf_*` and its exactness are
`Stacks.Cohomology.DerivedAdjunctionOnRingedSpaces.derivedPushforwardCommShift` and
`Stacks.Cohomology.DerivedAdjunctionOnRingedSpaces.derivedPushforward_isTriangulated`, reused
rather than rebuilt; they have to be seated as local instances before the statement of exactness
typechecks.

## References

* [Stacks Project, Tag 08I8](https://stacks.math.columbia.edu/tag/08I8)
* [Stacks Project, Tag 01XC](https://stacks.math.columbia.edu/tag/01XC)
* [Stacks Project, Tag 06Z0](https://stacks.math.columbia.edu/tag/06Z0)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits CategoryTheory.Pretriangulated
open AlgebraicGeometry
open Stacks.Cohomology.DerivedAdjunctionOnRingedSpaces (derivedPushforward)

universe u

namespace Stacks.AlgebraicGeometry.AffinePushforwardTExactness

attribute [local instance 10000] HasDerivedCategory.standard

attribute [local instance]
  Stacks.Cohomology.DerivedAdjunctionOnRingedSpaces.derivedPushforwardCommShift
  Stacks.Cohomology.DerivedAdjunctionOnRingedSpaces.derivedPushforward_isTriangulated

variable {W Y : Scheme.{u}}

/-- **[Stacks, Tag 08I8].**  Let `f : W ⟶ Y` be an affine morphism of schemes and let
`α : E ⟶ F` be a morphism of `D(𝒪_W)` between complexes whose cohomology sheaves are
quasi-coherent.  If the derived direct image `Rf_*α` is invertible in `D(𝒪_Y)`, then `α` is
invertible.  This is the assertion that `Rf_* : D_QCoh(𝒪_W) ⥤ D_QCoh(𝒪_Y)` reflects
isomorphisms. -/
@[stacks 08I8]
theorem isIso_of_isIso_derivedPushforward (f : W ⟶ Y) [IsAffineHom f]
    {E F : DerivedCategory W.Modules}
    (hE : ∀ i : ℤ, ((DerivedCategory.homologyFunctor W.Modules i).obj E).IsQuasicoherent)
    (hF : ∀ i : ℤ, ((DerivedCategory.homologyFunctor W.Modules i).obj F).IsQuasicoherent)
    (α : E ⟶ F)
    (h : IsIso ((derivedPushforward f.toLRSHom.toShHom).map α)) : IsIso α := by
  have : (DerivedCategoryB.derivedCategoryB (A := W.Modules)
      (SheafOfModules.isQuasicoherent W.ringCatSheaf)).IsTriangulated :=
    DerivedCategoryB.derivedCategoryB_isTriangulated _
      (Stacks.AlgebraicGeometry.QuasicoherentWeakSerre.isQuasicoherent_isWeakSerre W)
  obtain ⟨C, hC, b, c, hT⟩ := ObjectProperty.distinguished_cocone_triangle
    (P := DerivedCategoryB.derivedCategoryB (A := W.Modules)
      (SheafOfModules.isQuasicoherent W.ringCatSheaf)) α hE hF
  have hTd := (derivedPushforward f.toLRSHom.toShHom).map_distinguished _ hT
  have hz : IsZero ((derivedPushforward f.toLRSHom.toShHom).obj C) :=
    (Triangle.isZero₃_iff_isIso₁ _ hTd).2 h
  have hzC : IsZero C := by
    rw [DerivedCategory.isZero_iff_forall_isZero_homology]
    intro n
    refine (isZero_homology_derivedPushforward_iff f C (fun i => hC i) n).1 ?_
    exact Functor.map_isZero (DerivedCategory.homologyFunctor Y.Modules n) hz
  exact (Triangle.isZero₃_iff_isIso₁ _ hT).1 hzC

end Stacks.AlgebraicGeometry.AffinePushforwardTExactness

end
