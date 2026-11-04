module

public import StacksFrontier.AlgebraicGeometry.Perfect.RelativeExt.RestrictRelativeExt
public import StacksFrontier.AlgebraicGeometry.Perfect.RelativeExt.PartACore

/-!
# Assembling the comparison maps of [Stacks, Tag 08IF] (A) over an open subscheme

This file names the maps in which [Stacks, Tag 08IF] (A) is stated — functoriality in the
quasi-coherent `𝒪_S`-module `ℱ` and the boundary maps of short exact sequences, on both sides —
and assembles the comparison maps

`α^i_ℱ : Ext^i_{𝒪_X}(E, 𝒢 ⊗ f^*ℱ) ⟶ H^i(S, K ⊗^L ℱ)`

from an open immersion `j : U ⟶ X` and a perfect approximation `P ⟶ E|_U` on `U`: restriction
to `U` (`Stacks.Cohomology.RelativeExt.restrictRelativeExt`) followed by the comparison maps of
`Stacks.Cohomology.RelativeExt.partAMap` on `U`. The only inputs left open here are the
geometric ones: the approximation, the projection formula on `U`, and the bijectivity of the
restriction, which the proof of [Stacks, Tag 08IF] obtains from Tags 08ES, 08EU and the support
of `𝒢`.

## Main definitions

* `Stacks.Cohomology.RelativeExt.relativeExtMap`, `baseTensorMap`: functoriality in `ℱ`.
* `Stacks.Cohomology.RelativeExt.relativeExtBoundaryMap`, `baseTensorBoundaryMap`: the boundary
  maps.

## Main results

* `Stacks.Cohomology.RelativeExt.exists_comparison_of_open`: the assembly.
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry RingedSpaceModuleAdjunction
open TopologicalSpace

universe u

namespace Stacks.Cohomology.RelativeExt

attribute [local instance] HasDerivedCategory.standard hasSheafifyOpensSpace
  wEqualsLocallyBijectiveOpensSpace

variable {X S : Scheme.{u}}

section Maps

variable (f : X ⟶ S) (G : CochainComplex (TModules X.toRingedSpace) ℤ) (E : DStd X) (i : ℤ)

/-- **Functoriality of `Ext^i_{𝒪_X}(E, 𝒢 ⊗ f^*ℱ)` in `ℱ`.** -/
def relativeExtMap {F F' : SheafOfModules.{u} (structureSheafRing S.toRingedSpace)}
    (v : F ⟶ F') : relativeExtGroup f G E F i →+ relativeExtGroup f G E F' i where
  toFun y := y ≫ (DerivedCategory.Q.map ((relativeExtTargetFunctor f.toLRSHom.toShHom G).map v))⟦i⟧'
  map_zero' := zero_comp
  map_add' _ _ := Preadditive.add_comp _ _ _ _ _ _

/-- **Functoriality of `H^i(S, K ⊗^L ℱ)` in `ℱ`.** -/
def baseTensorMap (K : DStd S) {F F' : SheafOfModules.{u} (structureSheafRing S.toRingedSpace)}
    (v : F ⟶ F') : baseTensorGroup K F i →+ baseTensorGroup K F' i where
  toFun z := z ≫ (((Stacks.DerivedTensor.RingedSite.derivedTensorProductFunctor
    S.toRingedSpace.sheaf).obj K).map ((DerivedCategory.singleFunctor _ 0).map v))⟦i⟧'
  map_zero' := zero_comp
  map_add' _ _ := Preadditive.add_comp _ _ _ _ _ _

variable {f G} in
/-- **The boundary map `Ext^n_{𝒪_X}(E, 𝒢 ⊗ f^*ℱ₃) ⟶ Ext^m_{𝒪_X}(E, 𝒢 ⊗ f^*ℱ₁)`**, `1 + n = m`, of a
short exact sequence `0 ⟶ ℱ₁ ⟶ ℱ₂ ⟶ ℱ₃ ⟶ 0`: composition with the connecting morphism of the
short exact sequence of complexes `0 ⟶ 𝒢 ⊗ f^*ℱ₁ ⟶ 𝒢 ⊗ f^*ℱ₂ ⟶ 𝒢 ⊗ f^*ℱ₃ ⟶ 0`. -/
def relativeExtBoundaryMap (hG : IsBoundedFlatOver f.toLRSHom.toShHom G)
    {A : ShortComplex (SheafOfModules.{u} (structureSheafRing S.toRingedSpace))}
    (hA : A.ShortExact) (n m : ℤ) (h : 1 + n = m) :
    relativeExtGroup f G E A.X₃ n → relativeExtGroup f G E A.X₁ m :=
  fun y => y.comp (relativeExtBoundary hG hA) h

/-- **The boundary map `H^n(S, K ⊗^L ℱ₃) ⟶ H^m(S, K ⊗^L ℱ₁)`**, `1 + n = m`, of a short exact
sequence `0 ⟶ ℱ₁ ⟶ ℱ₂ ⟶ ℱ₃ ⟶ 0`: composition with the connecting morphism of the
distinguished triangle `K ⊗^L ℱ₁ ⟶ K ⊗^L ℱ₂ ⟶ K ⊗^L ℱ₃ ⟶ (K ⊗^L ℱ₁)[1]`. -/
def baseTensorBoundaryMap (K : DStd S)
    {A : ShortComplex (SheafOfModules.{u} (structureSheafRing S.toRingedSpace))}
    (hA : A.ShortExact) (n m : ℤ) (h : 1 + n = m) :
    baseTensorGroup K A.X₃ n → baseTensorGroup K A.X₁ m :=
  fun z => z.comp (@ShiftedHom.map _ _ _ _ _ _ _ _ _ _ _ hA.singleδ _
    (derivedTensorObj_commShift S.toRingedSpace K)) h

end Maps

/-- **`𝒢 ⊗ f^*ℱ` lies in `D^{≥ b}`** when `𝒢` vanishes in degrees `< b`. -/
theorem isGE_relativeExtTarget (f : X ⟶ S) (G : CochainComplex (TModules X.toRingedSpace) ℤ)
    (b : ℤ) (hb : G.IsStrictlyGE b) (F : SheafOfModules.{u} (structureSheafRing S.toRingedSpace)) :
    (DerivedCategory.Q.obj ((relativeExtTargetFunctor f.toLRSHom.toShHom G).obj F)).IsGE b := by
  have : ((relativeExtTargetFunctor f.toLRSHom.toShHom G).obj F).IsStrictlyGE b :=
    (CochainComplex.isStrictlyGE_iff _ b).2 fun i hi =>
      ((Stacks.SheafOfModules.Tensor.sheafTensor.{u, u, u, u, u} X.sheaf).map_isZero
        ((CochainComplex.isStrictlyGE_iff G b).1 hb i hi)).obj _
  rw [DerivedCategory.isGE_Q_obj_iff]
  infer_instance

section Assembly

variable (f : X ⟶ S) {U : Scheme.{u}} (j : U ⟶ X) [IsOpenImmersion j]
  {G : CochainComplex (TModules X.toRingedSpace) ℤ} (hG : IsBoundedFlatOver f.toLRSHom.toShHom G)
  (E : DStd X)

include hG in
/-- **The comparison maps of [Stacks, Tag 08IF] (A), from an approximation on an open.** Let
`j : U ⟶ X` be an open immersion such that restriction to `U` is bijective on the relative `Ext`
groups, `P` a perfect object of `D(𝒪_U)` at which the projection formula holds on `D_QCoh(𝒪_S)`,
and `p : P ⟶ E|_U` an approximation from `b - m - 1`, where `𝒢` vanishes in degrees `< b`. Then
`K = R(f|_U)_*(P^∨ ⊗^L 𝒢|_U)` carries maps `α^i_ℱ`, functorial in the quasi-coherent `ℱ`,
compatible with boundary maps, and bijective for `i ≤ m`. -/
theorem exists_comparison_of_open (P : DStd U)
    (hP : (Stacks.SheafOfModules.ringedSite U.toRingedSpace.sheaf).IsPerfect P)
    (hPF : ∀ N, qcohDerived S N →
      IsIso (Stacks.Cohomology.DerivedProjectionFormula.projectionFormulaMap
        (j ≫ f).toLRSHom.toShHom (stageSource (G := restrictComplex j G) P) N))
    (p : P ⟶ (restrictDerived j).obj E) (b m : ℤ) (hb : G.IsStrictlyGE b)
    (hp : ∀ k : ℤ, b - m - 1 < k → IsIso ((DerivedCategory.homologyFunctor _ k).map p))
    (he : Epi ((DerivedCategory.homologyFunctor _ (b - m - 1)).map p))
    (hres : ∀ (F : SheafOfModules.{u} (structureSheafRing S.toRingedSpace)) (i : ℤ),
      Function.Bijective (restrictRelativeExt f j G E F i)) :
    ∃ α : ∀ (i : ℤ) (F : SheafOfModules.{u} (structureSheafRing S.toRingedSpace)),
        F.IsQuasicoherent → (relativeExtGroup f G E F i →+
          baseTensorGroup (stageK (j ≫ f).toLRSHom.toShHom (G := restrictComplex j G) P) F i),
      (∀ (i : ℤ) (F F' : SheafOfModules.{u} (structureSheafRing S.toRingedSpace))
          (hF : F.IsQuasicoherent) (hF' : F'.IsQuasicoherent) (v : F ⟶ F')
          (y : relativeExtGroup f G E F i),
        α i F' hF' (relativeExtMap f G E i v y) =
          baseTensorMap i (stageK (j ≫ f).toLRSHom.toShHom (G := restrictComplex j G) P) v
            (α i F hF y)) ∧
      (∀ (A : ShortComplex (SheafOfModules.{u} (structureSheafRing S.toRingedSpace)))
          (hA : A.ShortExact) (h₁ : A.X₁.IsQuasicoherent) (h₃ : A.X₃.IsQuasicoherent)
          (n m' : ℤ) (h : 1 + n = m') (y : relativeExtGroup f G E A.X₃ n),
        α m' A.X₁ h₁ (relativeExtBoundaryMap E hG hA n m' h y) =
          baseTensorBoundaryMap (stageK (j ≫ f).toLRSHom.toShHom (G := restrictComplex j G) P)
            hA n m' h (α n A.X₃ h₃ y)) ∧
      (∀ (i : ℤ), i ≤ m → ∀ (F : SheafOfModules.{u} (structureSheafRing S.toRingedSpace))
          (hF : F.IsQuasicoherent), Function.Bijective (α i F hF)) := by
  have hGU := isBoundedFlatOver_restrictComplex (f := f) (j := j) hG
  refine ⟨fun i F hF => (partAMap (j ≫ f) hGU P hP hPF p i F hF).comp
    (restrictRelativeExt f j G E F i), ?_, ?_, ?_⟩
  · intro i F F' hF hF' v y
    show partAMap (j ≫ f) hGU P hP hPF p i F' hF' (restrictRelativeExt f j G E F' i
      (y ≫ (DerivedCategory.Q.map ((relativeExtTargetFunctor f.toLRSHom.toShHom G).map v))⟦i⟧')) =
        partAMap (j ≫ f) hGU P hP hPF p i F hF (restrictRelativeExt f j G E F i y) ≫ _
    rw [restrictRelativeExt_naturality, partAMap_naturality]
  · intro A hA h₁ h₃ n m' h y
    show partAMap (j ≫ f) hGU P hP hPF p m' A.X₁ h₁ (restrictRelativeExt f j G E A.X₁ m'
      (y.comp (relativeExtBoundary hG hA) h)) = ShiftedHom.comp
        (partAMap (j ≫ f) hGU P hP hPF p n A.X₃ h₃ (restrictRelativeExt f j G E A.X₃ n y)) _ h
    exact (congrArg (partAMap (j ≫ f) hGU P hP hPF p m' A.X₁ h₁)
      (restrictRelativeExt_boundary f j hG E hA n m' h y)).trans
        (partAMap_boundary (j ≫ f) hGU P hP hPF p hA h₁ h₃ n m' h _)
  · intro i hi F hF
    have hbU := isStrictlyGE_restrictComplex (j := j) b hb
    exact (partAMap_bijective (j ≫ f) hGU P hP hPF p b m hp he F hF
      (isGE_relativeExtTarget (j ≫ f) (restrictComplex j G) b hbU F) i hi).comp (hres F i)

end Assembly

end Stacks.Cohomology.RelativeExt

end
