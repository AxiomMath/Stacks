module

public import StacksFrontier.AlgebraicGeometry.FormalGeometry.CoherentAdicSystem.KernelImage
public import StacksFrontier.AlgebraicGeometry.FormalGeometry.CoherentAdicSystem.KernelStabilization

/-!
# The stabilized kernel image system of a morphism of coherent adic systems

Let `X` be a Noetherian scheme, `ℐ` a quasi-coherent ideal sheaf and `α : F ⟶ G` a morphism of
coherent adic systems along `ℐ`. Termwise kernels do not form an adic system, so the kernel in
`Coh(X, ℐ)` is built from the subobjects `kernelImageAt ℐ α m l ⊆ F_m`, the images in `F_m` of
`ker(α_l)` for `l ≥ m`. These shrink as `l` grows and, by
`Stacks.Coherent.kernelImages_eventuallyConstant`, stop shrinking: for each `m` there is a level
past which the kernel image in `F_m` no longer depends on the level it is computed from.

This file names that eventual value. For each `m` a stabilization level is chosen once and for
all, and `stableKernelImage ℐ α m` is the kernel image computed there; past that level every
kernel image in `F_m` is identified with it by an isomorphism over `F_m`. The resulting
subobjects of the terms of `F` inherit transition maps: to compare the stable images at `n ≤ m`
one passes to a level above both stabilization levels, where the projection
`Stacks.Coherent.kernelImageAtProject` between the kernel images at a single level is available,
and transports it back along the identifications. These maps are compatible with the inclusions
into `F`, are the identity at `n = m` and compose, so they assemble into an inverse system
`stableKernelImageSystem ℐ α` indexed by `ℕᵒᵖ` which is a subsystem of `F` annihilated by `α`.
Each of its terms is coherent, being the image of a map of coherent modules.

## Main definitions

* `Stacks.Coherent.kernelStableLevel` — the chosen level at which the kernel images in `F_m` have
  stabilized.
* `Stacks.Coherent.stableKernelImage` — the eventual value of the kernel images in `F_m`.
* `Stacks.Coherent.stableKernelImageIncl` — its inclusion into `F_m`.
* `Stacks.Coherent.stableKernelImageIso` — the identification of the kernel image computed from
  any level past the stabilization level with the stable kernel image.
* `Stacks.Coherent.stableKernelImage_project` — the transition map of the stable kernel images.
* `Stacks.Coherent.stableKernelImageSystem` — the inverse system they form.
* `Stacks.Coherent.stableKernelImageSystemIncl` — its inclusion into `F`.

## Main results

* `Stacks.Coherent.stableKernelImageIso_hom_comp` and
  `Stacks.Coherent.stableKernelImageIso_inv_comp` — the identification lies over the inclusions
  into `F_m`.
* `Stacks.Coherent.stableKernelImageIncl_comp` and
  `Stacks.Coherent.stableKernelImageSystemIncl_comp` — the stable kernel images are annihilated
  by `α`.
* `Stacks.Coherent.stableKernelImage_isCoherent` — every stable kernel image is coherent.
* `Stacks.Coherent.stableKernelImage_project_comp` — the transition maps cover the transition
  maps of `F`.
* `Stacks.Coherent.stableKernelImage_project_self` and
  `Stacks.Coherent.stableKernelImage_project_trans` — they are functorial.
* `Stacks.Coherent.stableKernelImage_hom_ext` and
  `Stacks.Coherent.stableKernelImageProjectAt_eq` — a morphism into a stable kernel image is
  determined by its composite with the inclusion, so the transition map does not depend on the
  common level it was computed at.

## Implementation notes

The system is indexed by `ℕᵒᵖ` and is zero-indexed: term `n` represents the Stacks source's
`F_{n+1}`.

The stabilization level is a genuine choice: `Stacks.Coherent.kernelImages_eventuallyConstant`
only asserts the existence of a constant past which the kernel images agree, and
`Stacks.Coherent.kernelStabilizationConstant` picks one. Nothing downstream should unfold that
choice; `Stacks.Coherent.stableKernelImageIso` together with
`Stacks.Coherent.stableKernelImageIso_hom_comp` is the complete interface, and it says exactly
what the stable kernel image is: the common value, over `F_m`, of the kernel images computed from
all sufficiently large levels.

The monotonicity hypothesis of `Stacks.Coherent.kernelImageAt` is an explicit argument, so every
statement below names the proof it uses; since these are proofs of a proposition, two kernel
images at the same pair of levels are the same object whichever proof is named.

## References

* [Stacks Project, Tag 087X](https://stacks.math.columbia.edu/tag/087X)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits Opposite AlgebraicGeometry
open scoped AlgebraicGeometry

universe u

attribute [local instance] AlgebraicGeometry.Scheme.Modules.submoduleCompleteLattice

namespace Stacks.Coherent

variable {X : Scheme.{u}} [IsNoetherian X] (I : X.IdealSheafData) {F G : CoherentAdicSystems I}

/-! ### The stabilization level -/

/-- A constant past which the kernel images in the term `F_m` no longer depend on the level they
are computed from, chosen once and for all from
`Stacks.Coherent.kernelImages_eventuallyConstant`. -/
public def kernelStabilizationConstant (α : F ⟶ G) (m : ℕ) : ℕ :=
  Classical.choose (kernelImages_eventuallyConstant I α m)

/-- The level at which the kernel images in the term `F_m` have stabilized. -/
public def kernelStableLevel (α : F ⟶ G) (m : ℕ) : ℕ :=
  m + kernelStabilizationConstant I α m

/-- The stabilization level of the term `F_m` lies above `m`, so a kernel image may be taken
there. -/
public theorem le_kernelStableLevel (α : F ⟶ G) (m : ℕ) : m ≤ kernelStableLevel I α m :=
  Nat.le_add_right m _

/-- A level above the stabilization levels of both `F_n` and `F_m`, where the stable kernel
images at the two levels may be compared. -/
public def commonKernelStableLevel (α : F ⟶ G) (n m : ℕ) : ℕ :=
  max (kernelStableLevel I α n) (kernelStableLevel I α m)

/-- The common stabilization level lies above the stabilization level of `F_n`. -/
public theorem left_le_commonKernelStableLevel (α : F ⟶ G) (n m : ℕ) :
    kernelStableLevel I α n ≤ commonKernelStableLevel I α n m :=
  le_max_left _ _

/-- The common stabilization level lies above the stabilization level of `F_m`. -/
public theorem right_le_commonKernelStableLevel (α : F ⟶ G) (n m : ℕ) :
    kernelStableLevel I α m ≤ commonKernelStableLevel I α n m :=
  le_max_right _ _

/-! ### The stable kernel image -/

/-- **The stable kernel image at level `m`**: the eventual value, as the level `l` grows, of the
image in `F_m` of the kernel of `α_l`. It is realized as the kernel image computed from the
stabilization level of `F_m`. -/
public def stableKernelImage (α : F ⟶ G) (m : ℕ) : X.Modules :=
  kernelImageAt I α m (kernelStableLevel I α m) (le_kernelStableLevel I α m)

/-- The inclusion of the stable kernel image into the term of `F` containing it. -/
public def stableKernelImageIncl (α : F ⟶ G) (m : ℕ) :
    stableKernelImage I α m ⟶ F.obj.obj (op m) :=
  kernelImageAtIncl I α m (kernelStableLevel I α m) (le_kernelStableLevel I α m)

/-- The stable kernel image is a subobject of the term containing it. -/
public instance mono_stableKernelImageIncl (α : F ⟶ G) (m : ℕ) :
    Mono (stableKernelImageIncl I α m) :=
  inferInstanceAs (Mono (kernelImageAtIncl I α m (kernelStableLevel I α m)
    (le_kernelStableLevel I α m)))

/-- A morphism into a stable kernel image is determined by its composite with the inclusion into
the ambient term. -/
public theorem stableKernelImage_hom_ext (α : F ⟶ G) {m : ℕ} {M : X.Modules}
    {u v : M ⟶ stableKernelImage I α m}
    (h : u ≫ stableKernelImageIncl I α m = v ≫ stableKernelImageIncl I α m) : u = v :=
  (cancel_mono (stableKernelImageIncl I α m)).mp h

/-- The stable kernel image is annihilated by `α`, being a kernel image. -/
public theorem stableKernelImageIncl_comp (α : F ⟶ G) (m : ℕ) :
    stableKernelImageIncl I α m ≫ α.hom.app (op m) = 0 :=
  kernelImageAtIncl_comp I α m (kernelStableLevel I α m) (le_kernelStableLevel I α m)

/-- **Every stable kernel image is coherent**, being the image of a morphism between coherent
modules: the terms of a coherent adic system are coherent and coherent modules are closed under
kernels and images. -/
public theorem stableKernelImage_isCoherent (α : F ⟶ G) (m : ℕ) :
    (stableKernelImage I α m).IsCoherent := by
  have hcohF : ∀ n : ℕ, (F.obj.obj (op n)).IsCoherent := F.property.isCoherent
  have hcohG : ∀ n : ℕ, (G.obj.obj (op n)).IsCoherent := G.property.isCoherent
  have hcohker : ∀ n : ℕ, (kernel (α.hom.app (op n))).IsCoherent := fun n =>
    AlgebraicGeometry.CoherentAbelian.isCoherent_kernel (α.hom.app (op n))
  exact isCoherent_image _

/-- **The stabilization, as an identification.** Past the stabilization level of `F_m`, the
kernel image in `F_m` computed from level `l` is identified with the stable kernel image by a
chosen isomorphism; `Stacks.Coherent.stableKernelImageIso_hom_comp` records that it lies over
the inclusions into `F_m`. -/
public def stableKernelImageIso (α : F ⟶ G) (m l : ℕ) (h : kernelStableLevel I α m ≤ l) :
    kernelImageAt I α m l ((le_kernelStableLevel I α m).trans h) ≅ stableKernelImage I α m :=
  Classical.choose (Classical.choose_spec (kernelImages_eventuallyConstant I α m) l h)

/-- The identification of a kernel image with the stable kernel image is compatible with their
inclusions into `F_m`. -/
public theorem stableKernelImageIso_hom_comp (α : F ⟶ G) (m l : ℕ)
    (h : kernelStableLevel I α m ≤ l) :
    (stableKernelImageIso I α m l h).hom ≫ stableKernelImageIncl I α m =
      kernelImageAtIncl I α m l ((le_kernelStableLevel I α m).trans h) :=
  Classical.choose_spec (Classical.choose_spec (kernelImages_eventuallyConstant I α m) l h)

/-- The inverse of the identification of a kernel image with the stable kernel image is likewise
compatible with the inclusions into `F_m`. -/
public theorem stableKernelImageIso_inv_comp (α : F ⟶ G) (m l : ℕ)
    (h : kernelStableLevel I α m ≤ l) :
    (stableKernelImageIso I α m l h).inv ≫
        kernelImageAtIncl I α m l ((le_kernelStableLevel I α m).trans h) =
      stableKernelImageIncl I α m := by
  rw [← stableKernelImageIso_hom_comp I α m l h, ← Category.assoc, Iso.inv_hom_id,
    Category.id_comp]

/-! ### The transition maps -/

/-- The comparison map between the stable kernel images at `n ≤ m`, computed at a prescribed
level `l` above both stabilization levels: the projection between the kernel images at level `l`,
transported along the identifications of
`Stacks.Coherent.stableKernelImageIso`. By
`Stacks.Coherent.stableKernelImageProjectAt_eq` it does not depend on `l`. -/
public def stableKernelImageProjectAt (α : F ⟶ G) (n m l : ℕ) (hnm : n ≤ m)
    (hn : kernelStableLevel I α n ≤ l) (hm : kernelStableLevel I α m ≤ l) :
    stableKernelImage I α m ⟶ stableKernelImage I α n :=
  (stableKernelImageIso I α m l hm).inv ≫
    kernelImageAtProject I α n m l hnm ((le_kernelStableLevel I α m).trans hm) ≫
    (stableKernelImageIso I α n l hn).hom

/-- The comparison map computed at a common stable level is compatible with the inclusions: it
covers the transition map `F_m ⟶ F_n`. -/
public theorem stableKernelImageProjectAt_comp (α : F ⟶ G) (n m l : ℕ) (hnm : n ≤ m)
    (hn : kernelStableLevel I α n ≤ l) (hm : kernelStableLevel I α m ≤ l) :
    stableKernelImageProjectAt I α n m l hnm hn hm ≫ stableKernelImageIncl I α n =
      stableKernelImageIncl I α m ≫ F.obj.map (homOfLE hnm).op := by
  show ((stableKernelImageIso I α m l hm).inv ≫
      kernelImageAtProject I α n m l hnm ((le_kernelStableLevel I α m).trans hm) ≫
      (stableKernelImageIso I α n l hn).hom) ≫ stableKernelImageIncl I α n =
    stableKernelImageIncl I α m ≫ F.obj.map (homOfLE hnm).op
  rw [Category.assoc, Category.assoc, stableKernelImageIso_hom_comp,
    kernelImageAtProject_comp, ← Category.assoc, stableKernelImageIso_inv_comp]

/-- **The transition map of the stable kernel images.** The stable kernel image in `F_m` maps to
the one in `F_n` for `n ≤ m`, over the transition map `F_m ⟶ F_n`. -/
public def stableKernelImage_project (α : F ⟶ G) (n m : ℕ) (hnm : n ≤ m) :
    stableKernelImage I α m ⟶ stableKernelImage I α n :=
  stableKernelImageProjectAt I α n m (commonKernelStableLevel I α n m) hnm
    (left_le_commonKernelStableLevel I α n m) (right_le_commonKernelStableLevel I α n m)

/-- The transition map of the stable kernel images covers the transition map of `F`. -/
public theorem stableKernelImage_project_comp (α : F ⟶ G) (n m : ℕ) (hnm : n ≤ m) :
    stableKernelImage_project I α n m hnm ≫ stableKernelImageIncl I α n =
      stableKernelImageIncl I α m ≫ F.obj.map (homOfLE hnm).op :=
  stableKernelImageProjectAt_comp I α n m (commonKernelStableLevel I α n m) hnm
    (left_le_commonKernelStableLevel I α n m) (right_le_commonKernelStableLevel I α n m)

/-- The comparison map between stable kernel images is independent of the common stable level it
is computed at, since a morphism over the transition map of `F` is unique. -/
public theorem stableKernelImageProjectAt_eq (α : F ⟶ G) (n m l : ℕ) (hnm : n ≤ m)
    (hn : kernelStableLevel I α n ≤ l) (hm : kernelStableLevel I α m ≤ l) :
    stableKernelImageProjectAt I α n m l hnm hn hm = stableKernelImage_project I α n m hnm :=
  stableKernelImage_hom_ext I α
    ((stableKernelImageProjectAt_comp I α n m l hnm hn hm).trans
      (stableKernelImage_project_comp I α n m hnm).symm)

/-- The transition map of the stable kernel images at a level with itself is the identity. -/
public theorem stableKernelImage_project_self (α : F ⟶ G) (n : ℕ) :
    stableKernelImage_project I α n n le_rfl = 𝟙 (stableKernelImage I α n) := by
  refine stableKernelImage_hom_ext I α ?_
  rw [stableKernelImage_project_comp, Category.id_comp]
  simp

/-- The transition maps of the stable kernel images compose. -/
public theorem stableKernelImage_project_trans (α : F ⟶ G) (a b c : ℕ) (hab : a ≤ b)
    (hbc : b ≤ c) :
    stableKernelImage_project I α b c hbc ≫ stableKernelImage_project I α a b hab =
      stableKernelImage_project I α a c (hab.trans hbc) := by
  refine stableKernelImage_hom_ext I α ?_
  rw [Category.assoc, stableKernelImage_project_comp, ← Category.assoc,
    stableKernelImage_project_comp, stableKernelImage_project_comp, Category.assoc,
    ← F.obj.map_comp]
  rfl

/-! ### The stable kernel image system -/

/-- **The inverse system of stable kernel images** of a morphism of coherent adic systems, with
the transition maps of `Stacks.Coherent.stableKernelImage_project`. Its terms are coherent, by
`Stacks.Coherent.stableKernelImage_isCoherent`; it is the underlying system of the kernel of `α`
in `Coh(X, ℐ)`. -/
public def stableKernelImageSystem (α : F ⟶ G) : ℕᵒᵖ ⥤ X.Modules where
  obj n := stableKernelImage I α n.unop
  map {n m} f := stableKernelImage_project I α m.unop n.unop (leOfHom f.unop)
  map_id n := stableKernelImage_project_self I α n.unop
  map_comp f g :=
    (stableKernelImage_project_trans I α _ _ _ (leOfHom g.unop) (leOfHom f.unop)).symm

/-- The system of stable kernel images is a subsystem of `F`, through the inclusions of the
stable kernel images into the terms of `F`. -/
public def stableKernelImageSystemIncl (α : F ⟶ G) : stableKernelImageSystem I α ⟶ F.obj where
  app n := stableKernelImageIncl I α n.unop
  naturality {n m} f := stableKernelImage_project_comp I α m.unop n.unop (leOfHom f.unop)

/-- **The system of stable kernel images is annihilated by `α`**, levelwise by
`Stacks.Coherent.stableKernelImageIncl_comp`. -/
public theorem stableKernelImageSystemIncl_comp (α : F ⟶ G) :
    stableKernelImageSystemIncl I α ≫ α.hom = 0 := by
  refine NatTrans.ext (funext fun n => ?_)
  exact stableKernelImageIncl_comp I α n.unop

end Stacks.Coherent

end
