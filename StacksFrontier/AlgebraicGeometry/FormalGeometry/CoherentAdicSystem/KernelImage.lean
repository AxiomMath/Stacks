module

public import Mathlib.CategoryTheory.Limits.Shapes.Images
public import Mathlib.CategoryTheory.Limits.Shapes.ZeroMorphisms
public import StacksFrontier.AlgebraicGeometry.FormalGeometry.CoherentAdicSystem

/-!
# The levelwise kernel images of a morphism of coherent adic systems

Let `X` be a scheme, `ℐ` a quasi-coherent ideal sheaf and `α : F ⟶ G` a morphism of coherent adic
systems along `ℐ`. Taking kernels termwise does not produce an adic system: the kernels
`ker(α_l)` need not surject onto one another along the transition maps of `F`. The repair, which
is how the kernel in `Coh(X, ℐ)` is eventually built, is to look instead at the *image* in `F_m`
of `ker(α_l)` for `l ≥ m`. These images form a decreasing family of subobjects of `F_m` as `l`
grows, and the kernel system is assembled from their eventual value.

This file introduces that family and records its basic structure: each kernel image sits inside
`F_m` and is killed by `α_m`, the image taken at a higher level `l` factors through the one taken
at an intermediate level `k`, and a kernel image at a fixed level `l` maps down the tower of
transition maps of `F` compatibly with the inclusions. The stabilization in `l`, which is the
substance of the construction, is not proved here.

## Main definitions

* `Stacks.Coherent.kernelImageAt` — the image in `F_m` of the kernel of `α` at level `l ≥ m`.
* `Stacks.Coherent.kernelImageAtIncl` — its inclusion into `F_m`.
* `Stacks.Coherent.kernelImageAtProject` — the induced map between the kernel images at a fixed
  level `l` taken in two terms `F_m ⟶ F_n`.

## Main results

* `Stacks.Coherent.kernelImageAtIncl_comp` — a kernel image is annihilated by `α`.
* `Stacks.Coherent.kernelImageAt_hasMap` — the kernel image computed from a higher level factors
  through the one computed from a lower level, over `F_m`.
* `Stacks.Coherent.kernelImageAtProject_comp` — the projection between kernel images commutes
  with the transition map of `F` on the inclusions.

## Implementation notes

The system is indexed by `ℕᵒᵖ` and is zero-indexed: term `n` represents the Stacks source's
`F_{n+1}`.

The monotonicity hypothesis `m ≤ l` is an explicit argument of `kernelImageAt`, so two kernel
images at the same pair of levels are the same object on the nose only when the proofs agree;
all statements below therefore name the proof they use, built from the hypotheses in scope by
`Nat.le_trans`.

## References

* [Stacks Project, Tag 087X](https://stacks.math.columbia.edu/tag/087X)
-/

@[expose] public noncomputable section

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits Opposite
open scoped AlgebraicGeometry

universe u

attribute [local instance] AlgebraicGeometry.Scheme.Modules.submoduleCompleteLattice

namespace Stacks.Coherent

variable {X : Scheme.{u}} (I : X.IdealSheafData) {F G : CoherentAdicSystems I}

/-- The image in the `m`-th term of `F` of the kernel of `α` at level `l ≥ m`, taken along the
transition map `F_l ⟶ F_m`. -/
public def kernelImageAt (α : F ⟶ G) (m l : ℕ) (h : m ≤ l) : X.Modules :=
  image (kernel.ι (α.hom.app (op l)) ≫ F.obj.map (homOfLE h).op)

/-- The inclusion of a levelwise kernel image into the term of `F` containing it. -/
public def kernelImageAtIncl (α : F ⟶ G) (m l : ℕ) (h : m ≤ l) :
    kernelImageAt I α m l h ⟶ F.obj.obj (op m) :=
  image.ι _

/-- A levelwise kernel image is annihilated by `α`: it is the image of a map that `α` kills,
by naturality of `α` along the transition `F_l ⟶ F_m`. -/
public theorem kernelImageAtIncl_comp (α : F ⟶ G) (m l : ℕ) (h : m ≤ l) :
    kernelImageAtIncl I α m l h ≫ α.hom.app (op m) = 0 := by
  refine image_ι_comp_eq_zero
    (f := kernel.ι (α.hom.app (op l)) ≫ F.obj.map (homOfLE h).op) ?_
  rw [Category.assoc, α.hom.naturality]
  simp

/-- The kernel image in `F_m` computed from a level `l` factors through the one computed from an
intermediate level `k`, compatibly with the inclusions into `F_m`: the kernels themselves map
`ker(α_l) ⟶ ker(α_k)` over the transition `F_l ⟶ F_k`. -/
public theorem kernelImageAt_hasMap (α : F ⟶ G) (m k l : ℕ) (hmk : m ≤ k) (hkl : k ≤ l) :
    ∃ j : kernelImageAt I α m l (hmk.trans hkl) ⟶ kernelImageAt I α m k hmk,
      j ≫ kernelImageAtIncl I α m k hmk = kernelImageAtIncl I α m l (hmk.trans hkl) := by
  let a := kernel.ι (α.hom.app (op l)) ≫ F.obj.map (homOfLE (hmk.trans hkl)).op
  let b := kernel.ι (α.hom.app (op k)) ≫ F.obj.map (homOfLE hmk).op
  let v := kernel.map (α.hom.app (op l)) (α.hom.app (op k))
    (F.obj.map (homOfLE hkl).op) (G.obj.map (homOfLE hkl).op)
    (α.hom.naturality (homOfLE hkl).op).symm
  have hv : v ≫ b = a := by
    have hcomp : (homOfLE hkl).op ≫ (homOfLE hmk).op =
        (homOfLE (hmk.trans hkl)).op := Subsingleton.elim _ _
    dsimp only [v, b, a]
    rw [kernel.map, kernel.lift_ι_assoc, Category.assoc, ← F.obj.map_comp, hcomp]
  let d : MonoFactorisation a :=
    { I := image b
      m := image.ι b
      e := v ≫ factorThruImage b
      fac := by rw [Category.assoc, image.fac, hv] }
  exact ⟨image.lift d, image.lift_fac d⟩

/-- The kernel image at a fixed level `l`, taken in the term `F_m`, maps to the one taken in any
lower term `F_n`, through the transition map `F_m ⟶ F_n`. -/
public def kernelImageAtProject (α : F ⟶ G) (n m l : ℕ) (hnm : n ≤ m) (hml : m ≤ l) :
    kernelImageAt I α m l hml ⟶ kernelImageAt I α n l (hnm.trans hml) :=
  image.map
    (f := Arrow.mk (kernel.ι (α.hom.app (op l)) ≫ F.obj.map (homOfLE hml).op))
    (g := Arrow.mk (kernel.ι (α.hom.app (op l)) ≫ F.obj.map (homOfLE (hnm.trans hml)).op))
    (Arrow.homMk' (𝟙 _) (F.obj.map (homOfLE hnm).op) (by
      have hcomp : (homOfLE hml).op ≫ (homOfLE hnm).op =
          (homOfLE (hnm.trans hml)).op := Subsingleton.elim _ _
      rw [Category.id_comp, Category.assoc, ← F.obj.map_comp, hcomp]))

/-- The projection between kernel images is compatible with the inclusions: it covers the
transition map `F_m ⟶ F_n`. -/
public theorem kernelImageAtProject_comp (α : F ⟶ G) (n m l : ℕ) (hnm : n ≤ m) (hml : m ≤ l) :
    kernelImageAtProject I α n m l hnm hml ≫ kernelImageAtIncl I α n l (hnm.trans hml) =
      kernelImageAtIncl I α m l hml ≫ F.obj.map (homOfLE hnm).op :=
  image.map_ι _

end Stacks.Coherent

end
