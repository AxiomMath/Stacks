module

public import StacksFrontier.AlgebraicGeometry.Spaces.CoherentAdicSystem

/-!
# The levelwise kernel images of a morphism of coherent adic systems on an algebraic space

Let `F` be an algebraic space over a scheme `S`, let `𝓘 ⊆ 𝒪_F` be a sheaf of ideals on its small
étale ringed site and let `α : E ⟶ E'` be a morphism of the category `Coh(F, 𝓘)` of coherent
adic systems. For `l ≥ m` this file defines the abelian image `CategoryTheory.Abelian.image` in
`E_m` of `ker α_l` along the transition map `E_l ⟶ E_m`. Each kernel image sits inside `E_m` and
is killed by `α_m`, the image taken at a higher level `l` factors through the one taken at an
intermediate level `k`, and a kernel image at a fixed level `l` maps down the tower of transition
maps of `E` compatibly with the inclusions.

## Main definitions

* `AlgebraicGeometry.Space.kernelImageAt` — the image in `E_m` of the kernel of `α` at a level
  `l ≥ m`.
* `AlgebraicGeometry.Space.kernelImageAtIncl` — its inclusion into `E_m`.
* `AlgebraicGeometry.Space.kernelImageAtProject` — the induced map between the kernel images at a
  fixed level `l` taken in two terms `E_m ⟶ E_n`.

## Main results

* `AlgebraicGeometry.Space.kernelImageAtIncl_comp` — a kernel image is annihilated by `α`.
* `AlgebraicGeometry.Space.kernelImageAt_hasMap` — the kernel image computed from a higher level
  factors through the one computed from a lower level, over `E_m`.
* `AlgebraicGeometry.Space.kernelImageAtProject_comp` — the projection between kernel images
  commutes with the transition map of `E` on the inclusions.

## References

* [Stacks Project, Tag 087X](https://stacks.math.columbia.edu/tag/087X)
* [Stacks Project, Tag 089P](https://stacks.math.columbia.edu/tag/089P)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits Opposite

universe u

namespace AlgebraicGeometry.Space

variable (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)
    (F : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u) (hF : IsAlgebraicSpace B S hS F)
    (𝓘 : (SheafOfModules.unit
      ((Stacks.SheafOfModules.Tensor.ringSheaf (smallEtaleRingedSite B S hS F hF).O))).Submodule)
    {E E' : CoherentAdicSystems B S hS F hF 𝓘}

set_option synthInstance.maxHeartbeats 200000

/-! ### The kernel image at a level -/

/-- The image in the `m`-th term of `E` of the kernel of `α` at a level `l ≥ m`, taken along the
transition map `E_l ⟶ E_m`. -/
def kernelImageAt (α : E ⟶ E') (m l : ℕ) (h : m ≤ l) : Modules.{u, u} B S hS F hF :=
  Abelian.image (kernel.ι (α.hom.app (op l)) ≫ E.obj.map (homOfLE h).op)

/-- The inclusion of a levelwise kernel image into the term of `E` containing it. -/
def kernelImageAtIncl (α : E ⟶ E') (m l : ℕ) (h : m ≤ l) :
    kernelImageAt B S hS F hF 𝓘 α m l h ⟶ E.obj.obj (op m) :=
  Abelian.image.ι (kernel.ι (α.hom.app (op l)) ≫ E.obj.map (homOfLE h).op)

/-- A levelwise kernel image is a subobject of the term of `E` containing it. -/
instance mono_kernelImageAtIncl (α : E ⟶ E') (m l : ℕ) (h : m ≤ l) :
    Mono (kernelImageAtIncl B S hS F hF 𝓘 α m l h) :=
  inferInstanceAs (Mono (Abelian.image.ι
    (kernel.ι (α.hom.app (op l)) ≫ E.obj.map (homOfLE h).op)))

/-- A levelwise kernel image is annihilated by `α`. -/
theorem kernelImageAtIncl_comp (α : E ⟶ E') (m l : ℕ) (h : m ≤ l) :
    kernelImageAtIncl B S hS F hF 𝓘 α m l h ≫ α.hom.app (op m) = 0 := by
  refine Abelian.image_ι_comp_eq_zero
    (f := kernel.ι (α.hom.app (op l)) ≫ E.obj.map (homOfLE h).op) ?_
  rw [Category.assoc, α.hom.naturality, kernel.condition_assoc, zero_comp]

/-! ### Comparison between kernel images -/

/-- Composing two transition maps of `E` gives the transition map of the composite. -/
private theorem map_homOfLE_comp_map_homOfLE (E : CoherentAdicSystems B S hS F hF 𝓘)
    {n m l : ℕ} (hnm : n ≤ m) (hml : m ≤ l) :
    E.obj.map (homOfLE hml).op ≫ E.obj.map (homOfLE hnm).op =
      E.obj.map (homOfLE (hnm.trans hml)).op := by
  rw [← E.obj.map_comp]
  rfl

/-- The kernel image in `E_m` computed from a level `l` factors through the one computed from an
intermediate level `k`, compatibly with the inclusions into `E_m`. -/
theorem kernelImageAt_hasMap (α : E ⟶ E') (m k l : ℕ) (hmk : m ≤ k) (hkl : k ≤ l) :
    ∃ j : kernelImageAt B S hS F hF 𝓘 α m l (hmk.trans hkl) ⟶
        kernelImageAt B S hS F hF 𝓘 α m k hmk,
      j ≫ kernelImageAtIncl B S hS F hF 𝓘 α m k hmk =
        kernelImageAtIncl B S hS F hF 𝓘 α m l (hmk.trans hkl) := by
  let a := kernel.ι (α.hom.app (op l)) ≫ E.obj.map (homOfLE (hmk.trans hkl)).op
  let b := kernel.ι (α.hom.app (op k)) ≫ E.obj.map (homOfLE hmk).op
  let v := kernel.map (α.hom.app (op l)) (α.hom.app (op k))
    (E.obj.map (homOfLE hkl).op) (E'.obj.map (homOfLE hkl).op)
    (α.hom.naturality (homOfLE hkl).op).symm
  have hv : v ≫ b = a := by
    dsimp only [v, b, a]
    rw [kernel.map, kernel.lift_ι_assoc, Category.assoc,
      map_homOfLE_comp_map_homOfLE B S hS F hF 𝓘 E]
  exact ⟨kernel.lift (cokernel.π b) (Abelian.image.ι a) (Abelian.image_ι_comp_eq_zero
    (by rw [← hv, Category.assoc, cokernel.condition, comp_zero])), kernel.lift_ι _ _ _⟩

/-- The transition maps of `E` carry the kernel image at a fixed level `l` taken in the term `E_m`
into the one taken in any lower term `E_n`. -/
theorem kernelImageAt_comp_map_comp_cokernel_π (α : E ⟶ E') (n m l : ℕ) (hnm : n ≤ m)
    (hml : m ≤ l) :
    (kernel.ι (α.hom.app (op l)) ≫ E.obj.map (homOfLE hml).op) ≫
        (E.obj.map (homOfLE hnm).op ≫
          cokernel.π (kernel.ι (α.hom.app (op l)) ≫
            E.obj.map (homOfLE (hnm.trans hml)).op)) = 0 := by
  rw [← Category.assoc, Category.assoc (kernel.ι (α.hom.app (op l))),
    map_homOfLE_comp_map_homOfLE B S hS F hF 𝓘 E, cokernel.condition]

/-- The inclusion of the kernel image at level `l` taken in `E_m`, followed by the transition map
`E_m ⟶ E_n`, lands in the kernel image at level `l` taken in `E_n`. -/
theorem kernelImageAtIncl_comp_map_comp_cokernel_π (α : E ⟶ E') (n m l : ℕ) (hnm : n ≤ m)
    (hml : m ≤ l) :
    (kernelImageAtIncl B S hS F hF 𝓘 α m l hml ≫ E.obj.map (homOfLE hnm).op) ≫
        cokernel.π (kernel.ι (α.hom.app (op l)) ≫
          E.obj.map (homOfLE (hnm.trans hml)).op) = 0 := by
  rw [Category.assoc]
  exact Abelian.image_ι_comp_eq_zero
    (kernelImageAt_comp_map_comp_cokernel_π B S hS F hF 𝓘 α n m l hnm hml)

/-- The kernel image at a fixed level `l`, taken in the term `E_m`, maps to the one taken in any
lower term `E_n`, through the transition map `E_m ⟶ E_n`. -/
def kernelImageAtProject (α : E ⟶ E') (n m l : ℕ) (hnm : n ≤ m) (hml : m ≤ l) :
    kernelImageAt B S hS F hF 𝓘 α m l hml ⟶
      kernelImageAt B S hS F hF 𝓘 α n l (hnm.trans hml) :=
  kernel.lift
    (cokernel.π (kernel.ι (α.hom.app (op l)) ≫ E.obj.map (homOfLE (hnm.trans hml)).op))
    (kernelImageAtIncl B S hS F hF 𝓘 α m l hml ≫ E.obj.map (homOfLE hnm).op)
    (kernelImageAtIncl_comp_map_comp_cokernel_π B S hS F hF 𝓘 α n m l hnm hml)

/-- The projection between kernel images is compatible with the inclusions: it covers the
transition map `E_m ⟶ E_n`. -/
theorem kernelImageAtProject_comp (α : E ⟶ E') (n m l : ℕ) (hnm : n ≤ m) (hml : m ≤ l) :
    kernelImageAtProject B S hS F hF 𝓘 α n m l hnm hml ≫
        kernelImageAtIncl B S hS F hF 𝓘 α n l (hnm.trans hml) =
      kernelImageAtIncl B S hS F hF 𝓘 α m l hml ≫ E.obj.map (homOfLE hnm).op :=
  kernel.lift_ι _ _ _

end AlgebraicGeometry.Space

end
