module

public import StacksFrontier.AlgebraicGeometry.Spaces.CoherentAdicKernelImageStabilization
public import StacksFrontier.AlgebraicGeometry.Spaces.CoherentCompletionAlgebraization

/-!
# The stabilized kernel image system of a morphism of coherent adic systems on an algebraic space

Let `F` be a Noetherian algebraic space over a scheme `S`, let `𝓘 ⊆ 𝒪_F` be a quasi-coherent
sheaf of ideals on its small étale ringed site and let `α : E ⟶ E'` be a morphism of coherent
`𝓘`-adic systems.  Termwise kernels do not form an adic system, so the kernel in `Coh(F, 𝓘)` is
built from the subobjects `AlgebraicGeometry.Space.kernelImageAt B S hS F hF 𝓘 α m l ⊆ E_m`, the
images in `E_m` of `ker α_l` for `l ≥ m`.  These shrink as `l` grows and, by
`AlgebraicGeometry.Space.kernelImages_eventuallyConstant`, stop shrinking: for each `m` there is
a level past which the kernel image in `E_m` no longer depends on the level it is computed from.

This file names that eventual value.  For each `m` a stabilization level is chosen once and for
all, and `AlgebraicGeometry.Space.stableKernelImage` is the kernel image computed there; past
that level every kernel image in `E_m` is identified with it by an isomorphism over `E_m`.  The
resulting subobjects of the terms of `E` inherit transition maps: to compare the stable images at
`n ≤ m` one passes to a level above both stabilization levels, where the projection
`AlgebraicGeometry.Space.kernelImageAtProject` between the kernel images at a single level is
available, and transports it back along the identifications.  These maps are compatible with the
inclusions into `E`, are the identity at `n = m` and compose, so they assemble into an inverse
system `AlgebraicGeometry.Space.stableKernelImageSystem` indexed by `ℕᵒᵖ` which is a subsystem of
`E` annihilated by `α`.  Each of its terms is coherent and cartesian on affine charts, and the
term at `m` is annihilated by `𝓘 ^ (m + 1)`, being a subobject of `E_m`.

This is the space-level analogue of
`StacksFrontier.AlgebraicGeometry.FormalGeometry.CoherentAdicSystem.StableKernelImage`.

## Main definitions

* `AlgebraicGeometry.Space.kernelStableLevel` — the chosen level at which the kernel images in
  `E_m` have stabilized.
* `AlgebraicGeometry.Space.stableKernelImage` — the eventual value of the kernel images in `E_m`.
* `AlgebraicGeometry.Space.stableKernelImageIncl` — its inclusion into `E_m`.
* `AlgebraicGeometry.Space.stableKernelImageIso` — the identification of the kernel image
  computed from any level past the stabilization level with the stable kernel image.
* `AlgebraicGeometry.Space.stableKernelImage_project` — the transition map of the stable kernel
  images.
* `AlgebraicGeometry.Space.stableKernelImageSystem` — the inverse system they form.
* `AlgebraicGeometry.Space.stableKernelImageSystemIncl` — its inclusion into `E`.

## Main results

* `AlgebraicGeometry.Space.stableKernelImageIso_hom_comp` and
  `AlgebraicGeometry.Space.stableKernelImageIso_inv_comp` — the identification lies over the
  inclusions into `E_m`.
* `AlgebraicGeometry.Space.stableKernelImageIncl_comp` and
  `AlgebraicGeometry.Space.stableKernelImageSystemIncl_comp` — the stable kernel images are
  annihilated by `α`.
* `AlgebraicGeometry.Space.isCoherent_stableKernelImage` and
  `AlgebraicGeometry.Space.isCartesianOnAffineCharts_stableKernelImage` — every stable kernel
  image is coherent, and cartesian on affine charts.
* `AlgebraicGeometry.Space.stableKernelImage_idealPowerMultiple_eq_bot` — the stable kernel image
  at level `m` is annihilated by `𝓘 ^ (m + 1)`.
* `AlgebraicGeometry.Space.stableKernelImage_project_comp` — the transition maps cover the
  transition maps of `E`.
* `AlgebraicGeometry.Space.stableKernelImage_project_self` and
  `AlgebraicGeometry.Space.stableKernelImage_project_trans` — they are functorial.
* `AlgebraicGeometry.Space.stableKernelImage_hom_ext` and
  `AlgebraicGeometry.Space.stableKernelImageProjectAt_eq` — a morphism into a stable kernel image
  is determined by its composite with the inclusion, so the transition map does not depend on the
  common level it was computed at.

## Implementation notes

The system is indexed by `ℕᵒᵖ` and is zero-indexed: the term at `n` is the Stacks source's
`E_{n + 1}`.

The stabilization level is a genuine choice:
`AlgebraicGeometry.Space.kernelImages_eventuallyConstant` only asserts the existence of a constant
past which the kernel images agree, and
`AlgebraicGeometry.Space.kernelStabilizationConstant` picks one.  Nothing downstream should
unfold that choice; `AlgebraicGeometry.Space.stableKernelImageIso` together with
`AlgebraicGeometry.Space.stableKernelImageIso_hom_comp` is the complete interface, and it says
exactly what the stable kernel image is: the common value, over `E_m`, of the kernel images
computed from all sufficiently large levels.

The Noetherian hypothesis of Stacks 089P is carried as the pair of explicit arguments `hZ`, `hN`
spelling `AlgebraicGeometry.Space.IsNoetherian`, together with quasi-coherence of `𝓘` in the form
`AlgebraicGeometry.Space.IsCartesianOnAffineCharts`, exactly as
`AlgebraicGeometry.Space.kernelImages_eventuallyConstant` needs them; every declaration below
therefore takes them, since the chosen stabilization level does.  Two choices made from two
different proofs of the same existential agree, proofs of a proposition being definitionally
equal, so nothing depends on which proof is supplied.

The monotonicity hypothesis of `AlgebraicGeometry.Space.kernelImageAt` is an explicit argument, so
every statement below names the proof it uses; since these are proofs of a proposition, two kernel
images at the same pair of levels are the same object whichever proof is named.

### What this is not

The system of stable kernel images is **not** a coherent adic system: its term at `n` need not be
the quotient of its term at `n + 1` by `𝓘 ^ (n + 1)`.  Making it one is the second
stabilization of Stacks 087X, which is
`AlgebraicGeometry.Space.stableKernelImageQuotientMap_eventually_isIso` in
`StacksFrontier.AlgebraicGeometry.Spaces.CoherentAdicStableKernelQuotient`, and the kernel object it
produces is `AlgebraicGeometry.Space.coherentAdicKernel`.

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

/-- **The image of a morphism of coherent `𝒪_F`-modules is coherent.**  The abelian image is the
kernel of the projection onto the cokernel, and coherent modules on an algebraic space are closed
under both kernels and cokernels. -/
theorem isCoherent_abelianImage {M N : Modules.{u, u} B S hS F hF}
    (hM : IsCoherent B S hS F hF M) (hN : IsCoherent B S hS F hF N) (f : M ⟶ N) :
    IsCoherent B S hS F hF (Abelian.image f) :=
  isCoherent_kernel B S hS F hF hN (isCoherent_cokernel B S hS F hF hM hN f) (cokernel.π f)

end AlgebraicGeometry.Space

namespace AlgebraicGeometry.Space

variable (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)
    (F : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u) (hF : IsAlgebraicSpace B S hS F)
    (𝓘 : (SheafOfModules.unit
      ((Stacks.SheafOfModules.Tensor.ringSheaf (smallEtaleRingedSite B S hS F hF).O))).Submodule)
    {E E' : CoherentAdicSystems B S hS F hF 𝓘}

/-- Every levelwise kernel image of a morphism of coherent adic systems is coherent, being the
image of a morphism between coherent modules: the terms of a coherent adic system are coherent and
coherent modules are closed under kernels and images. -/
theorem isCoherent_kernelImageAt (α : E ⟶ E') (m l : ℕ) (h : m ≤ l) :
    IsCoherent B S hS F hF (kernelImageAt B S hS F hF 𝓘 α m l h) :=
  isCoherent_abelianImage B S hS F hF
    (isCoherent_kernel B S hS F hF (E.property.1 l) (E'.property.1 l) (α.hom.app (op l)))
    (E.property.1 m) _

end AlgebraicGeometry.Space

namespace AlgebraicGeometry.Space

variable (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)
    (F : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u) (hF : IsAlgebraicSpace B S hS F)
    (𝓘 : (SheafOfModules.unit
      ((Stacks.SheafOfModules.Tensor.ringSheaf (smallEtaleRingedSite B S hS F hF).O))).Submodule)
    (hZ : B.Contains (⊤_ Scheme.{u})) (hN : IsNoetherian B S hS hZ F)
    (hIcart : IsCartesianOnAffineCharts 𝓘.toSheafOfModules)
    {E E' : CoherentAdicSystems B S hS F hF 𝓘}

/-! ### The stabilization level -/

/-- A constant past which the kernel images in the term `E_m` no longer depend on the level they
are computed from, chosen once and for all from
`AlgebraicGeometry.Space.kernelImages_eventuallyConstant`. -/
def kernelStabilizationConstant (α : E ⟶ E') (m : ℕ) : ℕ :=
  Classical.choose (kernelImages_eventuallyConstant B S hS F hF 𝓘 hZ hN hIcart α m)

/-- The level at which the kernel images in the term `E_m` have stabilized. -/
def kernelStableLevel (α : E ⟶ E') (m : ℕ) : ℕ :=
  m + kernelStabilizationConstant B S hS F hF 𝓘 hZ hN hIcart α m

/-- The stabilization level of the term `E_m` lies above `m`, so a kernel image may be taken
there. -/
theorem le_kernelStableLevel (α : E ⟶ E') (m : ℕ) :
    m ≤ kernelStableLevel B S hS F hF 𝓘 hZ hN hIcart α m :=
  Nat.le_add_right m _

/-- A level above the stabilization levels of both `E_n` and `E_m`, where the stable kernel images
at the two levels may be compared. -/
def commonKernelStableLevel (α : E ⟶ E') (n m : ℕ) : ℕ :=
  max (kernelStableLevel B S hS F hF 𝓘 hZ hN hIcart α n)
    (kernelStableLevel B S hS F hF 𝓘 hZ hN hIcart α m)

/-- The common stabilization level lies above the stabilization level of `E_n`. -/
theorem left_le_commonKernelStableLevel (α : E ⟶ E') (n m : ℕ) :
    kernelStableLevel B S hS F hF 𝓘 hZ hN hIcart α n ≤
      commonKernelStableLevel B S hS F hF 𝓘 hZ hN hIcart α n m :=
  le_max_left _ _

/-- The common stabilization level lies above the stabilization level of `E_m`. -/
theorem right_le_commonKernelStableLevel (α : E ⟶ E') (n m : ℕ) :
    kernelStableLevel B S hS F hF 𝓘 hZ hN hIcart α m ≤
      commonKernelStableLevel B S hS F hF 𝓘 hZ hN hIcart α n m :=
  le_max_right _ _

/-! ### The stable kernel image -/

/-- **The stable kernel image at level `m`**: the eventual value, as the level `l` grows, of the
image in `E_m` of the kernel of `α_l`.  It is realized as the kernel image computed from the
stabilization level of `E_m`. -/
def stableKernelImage (α : E ⟶ E') (m : ℕ) : Modules.{u, u} B S hS F hF :=
  kernelImageAt B S hS F hF 𝓘 α m (kernelStableLevel B S hS F hF 𝓘 hZ hN hIcart α m)
    (le_kernelStableLevel B S hS F hF 𝓘 hZ hN hIcart α m)

/-- The inclusion of the stable kernel image into the term of `E` containing it. -/
def stableKernelImageIncl (α : E ⟶ E') (m : ℕ) :
    stableKernelImage B S hS F hF 𝓘 hZ hN hIcart α m ⟶ E.obj.obj (op m) :=
  kernelImageAtIncl B S hS F hF 𝓘 α m (kernelStableLevel B S hS F hF 𝓘 hZ hN hIcart α m)
    (le_kernelStableLevel B S hS F hF 𝓘 hZ hN hIcart α m)

/-- The stable kernel image is a subobject of the term containing it. -/
instance mono_stableKernelImageIncl (α : E ⟶ E') (m : ℕ) :
    Mono (stableKernelImageIncl B S hS F hF 𝓘 hZ hN hIcart α m) :=
  inferInstanceAs (Mono (kernelImageAtIncl B S hS F hF 𝓘 α m
    (kernelStableLevel B S hS F hF 𝓘 hZ hN hIcart α m)
    (le_kernelStableLevel B S hS F hF 𝓘 hZ hN hIcart α m)))

/-- A morphism into a stable kernel image is determined by its composite with the inclusion into
the ambient term. -/
theorem stableKernelImage_hom_ext (α : E ⟶ E') {m : ℕ} {M : Modules.{u, u} B S hS F hF}
    {u v : M ⟶ stableKernelImage B S hS F hF 𝓘 hZ hN hIcart α m}
    (h : u ≫ stableKernelImageIncl B S hS F hF 𝓘 hZ hN hIcart α m =
      v ≫ stableKernelImageIncl B S hS F hF 𝓘 hZ hN hIcart α m) : u = v :=
  (cancel_mono (stableKernelImageIncl B S hS F hF 𝓘 hZ hN hIcart α m)).mp h

/-- The stable kernel image is annihilated by `α`, being a kernel image. -/
theorem stableKernelImageIncl_comp (α : E ⟶ E') (m : ℕ) :
    stableKernelImageIncl B S hS F hF 𝓘 hZ hN hIcart α m ≫ α.hom.app (op m) = 0 :=
  kernelImageAtIncl_comp B S hS F hF 𝓘 α m
    (kernelStableLevel B S hS F hF 𝓘 hZ hN hIcart α m)
    (le_kernelStableLevel B S hS F hF 𝓘 hZ hN hIcart α m)

/-- **Every stable kernel image is coherent**, being a levelwise kernel image. -/
theorem isCoherent_stableKernelImage (α : E ⟶ E') (m : ℕ) :
    IsCoherent B S hS F hF (stableKernelImage B S hS F hF 𝓘 hZ hN hIcart α m) :=
  isCoherent_kernelImageAt B S hS F hF 𝓘 α m _ _

/-- **Every stable kernel image is cartesian on affine charts**, being a levelwise kernel
image. -/
theorem isCartesianOnAffineCharts_stableKernelImage (α : E ⟶ E') (m : ℕ) :
    IsCartesianOnAffineCharts (stableKernelImage B S hS F hF 𝓘 hZ hN hIcart α m) :=
  isCartesianOnAffineCharts_kernelImageAt B S hS F hF 𝓘 α m _ _

/-- **The stable kernel image at level `m` is annihilated by `𝓘 ^ (m + 1)`**, being a subobject of
the term `E_m`, which is. -/
theorem stableKernelImage_idealPowerMultiple_eq_bot (α : E ⟶ E') (m : ℕ) :
    idealPowerMultiple B S hS F hF 𝓘 (m + 1)
        (stableKernelImage B S hS F hF 𝓘 hZ hN hIcart α m) = ⊥ :=
  idealPowerMultiple_eq_bot_of_mono B S hS F hF 𝓘
    (stableKernelImageIncl B S hS F hF 𝓘 hZ hN hIcart α m) (m + 1) (E.property.2.1 m)

/-- **The stabilization, as an identification.**  Past the stabilization level of `E_m`, the kernel
image in `E_m` computed from level `l` is identified with the stable kernel image by a chosen
isomorphism; `AlgebraicGeometry.Space.stableKernelImageIso_hom_comp` records that it lies over the
inclusions into `E_m`. -/
def stableKernelImageIso (α : E ⟶ E') (m l : ℕ)
    (h : kernelStableLevel B S hS F hF 𝓘 hZ hN hIcart α m ≤ l) :
    kernelImageAt B S hS F hF 𝓘 α m l
        ((le_kernelStableLevel B S hS F hF 𝓘 hZ hN hIcart α m).trans h) ≅
      stableKernelImage B S hS F hF 𝓘 hZ hN hIcart α m :=
  Classical.choose (Classical.choose_spec
    (kernelImages_eventuallyConstant B S hS F hF 𝓘 hZ hN hIcart α m) l h)

/-- The identification of a kernel image with the stable kernel image is compatible with their
inclusions into `E_m`. -/
theorem stableKernelImageIso_hom_comp (α : E ⟶ E') (m l : ℕ)
    (h : kernelStableLevel B S hS F hF 𝓘 hZ hN hIcart α m ≤ l) :
    (stableKernelImageIso B S hS F hF 𝓘 hZ hN hIcart α m l h).hom ≫
        stableKernelImageIncl B S hS F hF 𝓘 hZ hN hIcart α m =
      kernelImageAtIncl B S hS F hF 𝓘 α m l
        ((le_kernelStableLevel B S hS F hF 𝓘 hZ hN hIcart α m).trans h) :=
  Classical.choose_spec (Classical.choose_spec
    (kernelImages_eventuallyConstant B S hS F hF 𝓘 hZ hN hIcart α m) l h)

/-- The inverse of the identification of a kernel image with the stable kernel image is likewise
compatible with the inclusions into `E_m`. -/
theorem stableKernelImageIso_inv_comp (α : E ⟶ E') (m l : ℕ)
    (h : kernelStableLevel B S hS F hF 𝓘 hZ hN hIcart α m ≤ l) :
    (stableKernelImageIso B S hS F hF 𝓘 hZ hN hIcart α m l h).inv ≫
        kernelImageAtIncl B S hS F hF 𝓘 α m l
          ((le_kernelStableLevel B S hS F hF 𝓘 hZ hN hIcart α m).trans h) =
      stableKernelImageIncl B S hS F hF 𝓘 hZ hN hIcart α m := by
  rw [← stableKernelImageIso_hom_comp B S hS F hF 𝓘 hZ hN hIcart α m l h, ← Category.assoc,
    Iso.inv_hom_id, Category.id_comp]

/-! ### The transition maps -/

/-- The comparison map between the stable kernel images at `n ≤ m`, computed at a prescribed level
`l` above both stabilization levels: the projection between the kernel images at level `l`,
transported along the identifications of
`AlgebraicGeometry.Space.stableKernelImageIso`.  By
`AlgebraicGeometry.Space.stableKernelImageProjectAt_eq` it does not depend on `l`. -/
def stableKernelImageProjectAt (α : E ⟶ E') (n m l : ℕ) (hnm : n ≤ m)
    (hn : kernelStableLevel B S hS F hF 𝓘 hZ hN hIcart α n ≤ l)
    (hm : kernelStableLevel B S hS F hF 𝓘 hZ hN hIcart α m ≤ l) :
    stableKernelImage B S hS F hF 𝓘 hZ hN hIcart α m ⟶
      stableKernelImage B S hS F hF 𝓘 hZ hN hIcart α n :=
  (stableKernelImageIso B S hS F hF 𝓘 hZ hN hIcart α m l hm).inv ≫
    kernelImageAtProject B S hS F hF 𝓘 α n m l hnm
      ((le_kernelStableLevel B S hS F hF 𝓘 hZ hN hIcart α m).trans hm) ≫
    (stableKernelImageIso B S hS F hF 𝓘 hZ hN hIcart α n l hn).hom

/-- The comparison map computed at a common stable level is compatible with the inclusions: it
covers the transition map `E_m ⟶ E_n`. -/
theorem stableKernelImageProjectAt_comp (α : E ⟶ E') (n m l : ℕ) (hnm : n ≤ m)
    (hn : kernelStableLevel B S hS F hF 𝓘 hZ hN hIcart α n ≤ l)
    (hm : kernelStableLevel B S hS F hF 𝓘 hZ hN hIcart α m ≤ l) :
    stableKernelImageProjectAt B S hS F hF 𝓘 hZ hN hIcart α n m l hnm hn hm ≫
        stableKernelImageIncl B S hS F hF 𝓘 hZ hN hIcart α n =
      stableKernelImageIncl B S hS F hF 𝓘 hZ hN hIcart α m ≫ E.obj.map (homOfLE hnm).op := by
  change ((stableKernelImageIso B S hS F hF 𝓘 hZ hN hIcart α m l hm).inv ≫
      kernelImageAtProject B S hS F hF 𝓘 α n m l hnm
        ((le_kernelStableLevel B S hS F hF 𝓘 hZ hN hIcart α m).trans hm) ≫
      (stableKernelImageIso B S hS F hF 𝓘 hZ hN hIcart α n l hn).hom) ≫
      stableKernelImageIncl B S hS F hF 𝓘 hZ hN hIcart α n =
    stableKernelImageIncl B S hS F hF 𝓘 hZ hN hIcart α m ≫ E.obj.map (homOfLE hnm).op
  rw [Category.assoc, Category.assoc, stableKernelImageIso_hom_comp,
    kernelImageAtProject_comp, ← Category.assoc, stableKernelImageIso_inv_comp]

/-- **The transition map of the stable kernel images.**  The stable kernel image in `E_m` maps to
the one in `E_n` for `n ≤ m`, over the transition map `E_m ⟶ E_n`. -/
def stableKernelImage_project (α : E ⟶ E') (n m : ℕ) (hnm : n ≤ m) :
    stableKernelImage B S hS F hF 𝓘 hZ hN hIcart α m ⟶
      stableKernelImage B S hS F hF 𝓘 hZ hN hIcart α n :=
  stableKernelImageProjectAt B S hS F hF 𝓘 hZ hN hIcart α n m
    (commonKernelStableLevel B S hS F hF 𝓘 hZ hN hIcart α n m) hnm
    (left_le_commonKernelStableLevel B S hS F hF 𝓘 hZ hN hIcart α n m)
    (right_le_commonKernelStableLevel B S hS F hF 𝓘 hZ hN hIcart α n m)

/-- The transition map of the stable kernel images covers the transition map of `E`. -/
theorem stableKernelImage_project_comp (α : E ⟶ E') (n m : ℕ) (hnm : n ≤ m) :
    stableKernelImage_project B S hS F hF 𝓘 hZ hN hIcart α n m hnm ≫
        stableKernelImageIncl B S hS F hF 𝓘 hZ hN hIcart α n =
      stableKernelImageIncl B S hS F hF 𝓘 hZ hN hIcart α m ≫ E.obj.map (homOfLE hnm).op :=
  stableKernelImageProjectAt_comp B S hS F hF 𝓘 hZ hN hIcart α n m
    (commonKernelStableLevel B S hS F hF 𝓘 hZ hN hIcart α n m) hnm
    (left_le_commonKernelStableLevel B S hS F hF 𝓘 hZ hN hIcart α n m)
    (right_le_commonKernelStableLevel B S hS F hF 𝓘 hZ hN hIcart α n m)

/-- The comparison map between stable kernel images is independent of the common stable level it is
computed at, since a morphism over the transition map of `E` is unique. -/
theorem stableKernelImageProjectAt_eq (α : E ⟶ E') (n m l : ℕ) (hnm : n ≤ m)
    (hn : kernelStableLevel B S hS F hF 𝓘 hZ hN hIcart α n ≤ l)
    (hm : kernelStableLevel B S hS F hF 𝓘 hZ hN hIcart α m ≤ l) :
    stableKernelImageProjectAt B S hS F hF 𝓘 hZ hN hIcart α n m l hnm hn hm =
      stableKernelImage_project B S hS F hF 𝓘 hZ hN hIcart α n m hnm :=
  stableKernelImage_hom_ext B S hS F hF 𝓘 hZ hN hIcart α
    ((stableKernelImageProjectAt_comp B S hS F hF 𝓘 hZ hN hIcart α n m l hnm hn hm).trans
      (stableKernelImage_project_comp B S hS F hF 𝓘 hZ hN hIcart α n m hnm).symm)

/-- The transition map of the stable kernel images at a level with itself is the identity. -/
theorem stableKernelImage_project_self (α : E ⟶ E') (n : ℕ) :
    stableKernelImage_project B S hS F hF 𝓘 hZ hN hIcart α n n le_rfl =
      𝟙 (stableKernelImage B S hS F hF 𝓘 hZ hN hIcart α n) := by
  refine stableKernelImage_hom_ext B S hS F hF 𝓘 hZ hN hIcart α ?_
  rw [stableKernelImage_project_comp, Category.id_comp]
  simp

/-- The transition maps of the stable kernel images compose. -/
theorem stableKernelImage_project_trans (α : E ⟶ E') (a b c : ℕ) (hab : a ≤ b) (hbc : b ≤ c) :
    stableKernelImage_project B S hS F hF 𝓘 hZ hN hIcart α b c hbc ≫
        stableKernelImage_project B S hS F hF 𝓘 hZ hN hIcart α a b hab =
      stableKernelImage_project B S hS F hF 𝓘 hZ hN hIcart α a c (hab.trans hbc) := by
  refine stableKernelImage_hom_ext B S hS F hF 𝓘 hZ hN hIcart α ?_
  rw [Category.assoc, stableKernelImage_project_comp, ← Category.assoc,
    stableKernelImage_project_comp, stableKernelImage_project_comp, Category.assoc,
    ← E.obj.map_comp]
  rfl

/-! ### The stable kernel image system -/

/-- **The inverse system of stable kernel images** of a morphism of coherent adic systems, with the
transition maps of `AlgebraicGeometry.Space.stableKernelImage_project`.  Its terms are coherent, by
`AlgebraicGeometry.Space.isCoherent_stableKernelImage`; the kernel of `α` in `Coh(F, 𝓘)` is
assembled from it, but it is not itself a coherent adic system — see the module documentation. -/
def stableKernelImageSystem (α : E ⟶ E') : ℕᵒᵖ ⥤ Modules.{u, u} B S hS F hF where
  obj n := stableKernelImage B S hS F hF 𝓘 hZ hN hIcart α n.unop
  map {n m} f := stableKernelImage_project B S hS F hF 𝓘 hZ hN hIcart α m.unop n.unop
    (leOfHom f.unop)
  map_id n := stableKernelImage_project_self B S hS F hF 𝓘 hZ hN hIcart α n.unop
  map_comp f g := (stableKernelImage_project_trans B S hS F hF 𝓘 hZ hN hIcart α _ _ _
    (leOfHom g.unop) (leOfHom f.unop)).symm

/-- The system of stable kernel images is a subsystem of `E`, through the inclusions of the stable
kernel images into the terms of `E`. -/
def stableKernelImageSystemIncl (α : E ⟶ E') :
    stableKernelImageSystem B S hS F hF 𝓘 hZ hN hIcart α ⟶ E.obj where
  app n := stableKernelImageIncl B S hS F hF 𝓘 hZ hN hIcart α n.unop
  naturality {n m} f := stableKernelImage_project_comp B S hS F hF 𝓘 hZ hN hIcart α m.unop n.unop
    (leOfHom f.unop)

/-- **The system of stable kernel images is annihilated by `α`**, levelwise by
`AlgebraicGeometry.Space.stableKernelImageIncl_comp`. -/
theorem stableKernelImageSystemIncl_comp (α : E ⟶ E') :
    stableKernelImageSystemIncl B S hS F hF 𝓘 hZ hN hIcart α ≫ α.hom = 0 := by
  refine NatTrans.ext (funext fun n => ?_)
  exact stableKernelImageIncl_comp B S hS F hF 𝓘 hZ hN hIcart α n.unop

end AlgebraicGeometry.Space

end
