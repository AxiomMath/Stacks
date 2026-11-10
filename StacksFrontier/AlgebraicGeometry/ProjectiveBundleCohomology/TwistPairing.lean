module

public import StacksFrontier.AlgebraicGeometry.ProjectiveBundleCohomology.TopRow
public import StacksFrontier.Topology.Sheaves.Modules.TensorAndDuals.InternalHom

/-!
# The multiplication pairing between the twists and the symmetric powers

Let `π : 𝐏(E) ⟶ S` be the projective bundle of a quasi-coherent `𝒪_S`-module `E`, with twists
given by a `Stacks.AlgebraicGeometry.RelativeProjTwists.TwistData`. The canonical maps
`Sym^k(E) ⟶ π_* 𝒪(k)` of Tag 01NR have adjoints `π^* Sym^k(E) ⟶ 𝒪(k)`, and multiplication of
the twists gives the pairing

`𝒪(d) ⊗ π^* Sym^k(E) ⟶ 𝒪(d + k)`,

and its curried form `𝒪(d) ⟶ SheafHom(π^* Sym^k(E), 𝒪(d + k))`.

## Main definitions

* `Stacks.AlgebraicGeometry.ProjectiveBundleCohomology.psiFlat`: `π^* Sym^k(E) ⟶ 𝒪(k)`.
* `Stacks.AlgebraicGeometry.ProjectiveBundleCohomology.twistPairing`: the pairing.
* `Stacks.AlgebraicGeometry.ProjectiveBundleCohomology.twistPairingCurry`: its curried form.

## Main results

* `Stacks.AlgebraicGeometry.ProjectiveBundleCohomology.twistPairingCurry_apply`: on sections,
  the curried pairing multiplies a section of `𝒪(d)` with the image of a section of
  `π^* Sym^k(E)`.
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits TopologicalSpace Opposite AlgebraicGeometry
open Stacks.AlgebraicGeometry.RelativeProjBridge Stacks.AlgebraicGeometry.RelativeProj
open Stacks.AlgebraicGeometry.RelativeProjTwists
open Stacks.SheafOfModules.TensorStalkRingedSpace

universe u

namespace Stacks.AlgebraicGeometry.ProjectiveBundleCohomology

variable {S : Scheme.{u}} (E : S.Modules) [E.IsQuasicoherent]
  (hqc : Stacks.SymGraded.IsQuasicoherentPieces E)
  (D : TwistData (Stacks.SymGraded.schemeSheafGradedAlgebra E hqc))

/-- The adjoint `π^* Sym^k(E) ⟶ 𝒪(k)` of the canonical map `Sym^k(E) ⟶ π_* 𝒪(k)`. -/
def psiFlat (k : ℕ) :
    (Scheme.Modules.pullback
          (relativeProj (Stacks.SymGraded.schemeSheafGradedAlgebra E hqc)).toBase).obj
        ((Stacks.SymGraded.schemeSheafGradedAlgebra E hqc).piece (k : ℤ)) ⟶
      D.algebra.piece (k : ℤ) :=
  ((Scheme.Modules.pullbackPushforwardAdjunction
    (relativeProj (Stacks.SymGraded.schemeSheafGradedAlgebra E hqc)).toBase).homEquiv _ _).symm
    (D.ψ k)

/-- **The multiplication pairing** `𝒪(d) ⊗ π^* Sym^k(E) ⟶ 𝒪(e)`, `e = d + k`. -/
def twistPairing (k : ℕ) (d e : ℤ) (he : d + k = e) :
    ((Stacks.SheafOfModules.Tensor.sheafTensor
      ⟨(bundle E hqc).toRingedSpace.presheaf, (bundle E hqc).toRingedSpace.IsSheaf⟩).obj
        (D.algebra.piece d)).obj
        ((Scheme.Modules.pullback
          (relativeProj (Stacks.SymGraded.schemeSheafGradedAlgebra E hqc)).toBase).obj
          ((Stacks.SymGraded.schemeSheafGradedAlgebra E hqc).piece (k : ℤ))) ⟶
      D.algebra.piece e :=
  ((Stacks.SheafOfModules.Tensor.sheafTensor
      ⟨(bundle E hqc).toRingedSpace.presheaf, (bundle E hqc).toRingedSpace.IsSheaf⟩).obj
        (D.algebra.piece d)).map (psiFlat E hqc D k) ≫
    twistMul D d k ≫ eqToHom (congrArg D.algebra.piece he)

/-- **The multiplication pairing, curried**: `𝒪(d) ⟶ SheafHom(π^* Sym^k(E), 𝒪(e))`. -/
def twistPairingCurry (k : ℕ) (d e : ℤ) (he : d + k = e) :
    D.algebra.piece d ⟶ Stacks.SheafOfModules.sheafHomSpace (bundle E hqc).toRingedSpace
      ((Scheme.Modules.pullback
          (relativeProj (Stacks.SymGraded.schemeSheafGradedAlgebra E hqc)).toBase).obj
          ((Stacks.SymGraded.schemeSheafGradedAlgebra E hqc).piece (k : ℤ)))
      (D.algebra.piece e) :=
  Stacks.SheafOfModules.tensorHomEquiv _ _ _ _ (twistPairing E hqc D k d e he)

omit [E.IsQuasicoherent] in
/-- On sections over `U`, the curried pairing sends a section `c` of `𝒪(d)` and a section `t`
of `π^* Sym^k(E)` to the product of `c` with the image of `t` in `𝒪(k)`, viewed in `𝒪(e)`. -/
theorem twistPairingCurry_apply (k : ℕ) (d e : ℤ) (he : d + k = e) (U : (bundle E hqc).Opens)
    (c : Γ(D.algebra.piece d, U))
    (t : Γ((Scheme.Modules.pullback
          (relativeProj (Stacks.SymGraded.schemeSheafGradedAlgebra E hqc)).toBase).obj
          ((Stacks.SymGraded.schemeSheafGradedAlgebra E hqc).piece (k : ℤ)), U)) :
    ((((twistPairingCurry E hqc D k d e he).val.app (op U)).hom c).app
        (op (Over.mk (𝟙 U)))).hom t =
      (eqToHom (congrArg D.algebra.piece he)).val.app (op U)
        ((D.algebra.mul d k).app (op U) c ((psiFlat E hqc D k).val.app (op U) t)) := by
  refine (Stacks.SheafOfModules.tensorHomEquiv_isTensorCurry _ (twistPairing E hqc D k d e he)
    U c t).trans ?_
  have h1 := tensorSheafMap_app_toTensorSheafSection (bundle E hqc).toRingedSpace _ _ _ _
    (𝟙 (D.algebra.piece d)) (psiFlat E hqc D k) U c t
  have h2 := SheafOfModules.GradedAlgebra.mulSheaf_unit
    (J := Opens.grothendieckTopology
      (relativeProj (Stacks.SymGraded.schemeSheafGradedAlgebra E hqc)).scheme)
    (Osharp := (relativeProj (Stacks.SymGraded.schemeSheafGradedAlgebra E hqc)).scheme.sheaf)
    D.algebra d k (op U) c ((psiFlat E hqc D k).val.app (op U) t)
  have hmap := Stacks.SheafOfModules.Tensor.sheafTensor_uncurry_map
    ⟨(bundle E hqc).toRingedSpace.presheaf, (bundle E hqc).toRingedSpace.IsSheaf⟩
    (𝟙 (D.algebra.piece d)) (psiFlat E hqc D k)
  replace h1 := (congrArg (fun m => (m.val.app (op U)).hom
    (toTensorSheafSection (bundle E hqc).toRingedSpace _ _ (op U) (c ⊗ₜ t))) hmap).symm.trans h1
  exact (congrArg (fun z => (eqToHom (congrArg D.algebra.piece he)).val.app (op U)
    ((twistMul D d k).val.app (op U) z)) h1).trans (congrArg _ h2)

end Stacks.AlgebraicGeometry.ProjectiveBundleCohomology

end
