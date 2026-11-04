module

public import StacksFrontier.AlgebraicGeometry.Spaces.ClosedImmersionStructureSharpInverseImage
public import StacksFrontier.AlgebraicGeometry.Spaces.ConormalModuleBaseChangeCartesian
public import StacksFrontier.AlgebraicGeometry.Spaces.InverseImageStructureSheafMap
public import StacksFrontier.AlgebraicGeometry.Spaces.SmallEtaleFlatTopos
public import StacksFrontier.AlgebraicGeometry.Spaces.SmallEtaleRingedToposHomInverseImage
public import StacksFrontier.AlgebraicGeometry.Spaces.Thickenings.BaseChangeOrder
public import StacksFrontier.AlgebraicGeometry.Spaces.Thickenings.ConormalModuleInverseImageKernel
public import StacksFrontier.Deformation.AlgebraExtension.Basic
public import StacksFrontier.AlgebraicGeometry.Size.CoveringsSupplement
public import StacksFrontier.AlgebraicGeometry.Spaces.Category
public import StacksFrontier.AlgebraicGeometry.Spaces.CoveringComparison
public import StacksFrontier.AlgebraicGeometry.Spaces.LocallyPrincipalPullbackSupplement
public import StacksFrontier.AlgebraicGeometry.Spaces.OpenSiteObject
public import StacksFrontier.AlgebraicGeometry.Spaces.Points
public import StacksFrontier.AlgebraicGeometry.Spaces.Thickenings.EtaleToposSupplement
public import StacksFrontier.Topology.Dimension.KrullSupplement
public import StacksFrontier.Topology.Sheaves.Functors.Module.PullbackCompSupplement

/-!
# The square-zero extension of a first-order thickening of algebraic spaces

Let `Z ⊆ X` be a first-order thickening of algebraic spaces over `S`, with inclusion
`i : Z ⟶ X`, and let `g : X ⟶ Y` be a morphism of algebraic spaces. On the small étale site of
`Z` the inverse image `i^{-1}𝒪_X` of the structure sheaf of the ambient space, with the
inverse-image form `i^♯ : i^{-1}𝒪_X ⟶ 𝒪_Z` of the structure map, is an extension

`0 ⟶ 𝒞_{Z/X} ⟶ i^{-1}𝒪_X ⟶ 𝒪_Z ⟶ 0`

of `(i ≫ g)^{-1}𝒪_Y`-algebras of `𝒪_Z` by the conormal module `𝒞_{Z/X}`.

## Main definitions

* `Deformation.AlgebraExtension.ofKernelInclusion`: an extension from a locally surjective
  reduction and an inclusion of a module onto its square-zero kernel.
* `Deformation.AlgebraExtension.transportKernel`: an extension by `ℳ` read as one by `𝒩` along
  `ℳ ≅ 𝒩`, with `Deformation.AlgebraExtension.transportKernelMapAlong` the comparison.
* `AlgebraicGeometry.Space.firstOrderAlgebraExtension`: the extension above, with algebra
  structure `AlgebraicGeometry.Space.inverseImageStructureSheafMap` (the inverse image along `i`
  of `g^♯`).
* `AlgebraicGeometry.Space.flatFirstOrderAlgebraExtension`: for the upper row of a fibre product
  square along a flat morphism, the same extension with its kernel identified with the pullback
  `f^*𝒞_{Z'/X'}` of the ideal of the lower row.
* `AlgebraicGeometry.Space.flatFirstOrderAlgebraExtensionOfIsFlat`: the same extension when `q`
  is flat as a morphism of algebraic spaces.

## Main results

* `AlgebraicGeometry.Space.firstOrderAlgebraExtension_reduction` and
  `AlgebraicGeometry.Space.firstOrderAlgebraExtension_extension`: the middle term and the
  reduction are `i^{-1}𝒪_X` and `i^♯`.

## References

* [Stacks Project, Tag 0D17](https://stacks.math.columbia.edu/tag/0D17)
* [Stacks Project, Tag 04CQ](https://stacks.math.columbia.edu/tag/04CQ)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits

universe u v w

namespace Deformation.AlgebraExtension

variable {C : Type v} [Category.{w} C] {J : GrothendieckTopology C}
  [J.HasSheafCompose (forget₂ CommRingCat.{u} RingCat.{u})]
  {A O : Sheaf J CommRingCat.{u}} {a : A ⟶ O}
  {M : SheafOfModules.{u} ((sheafCompose J (forget₂ CommRingCat.{u} RingCat.{u})).obj O)}

/-- **An extension from a reduction and an inclusion of its kernel.** A locally surjective map
`r : 𝒪' ⟶ 𝒪` of `𝒜`-algebras, together with a map `ι : ℳ ⟶ 𝒪'` of `𝒪'`-modules (for the
module structure on `ℳ` through the ring-level form `r'` of `r`) which is injective on sections,
lands in the kernel of `r` and exhausts it, and whose image has square zero, is an extension of
`𝒜`-algebras of `𝒪` by `ℳ`.

The ring-level form `r'` is any morphism equal to `r` after forgetting commutativity. -/
def ofKernelInclusion (E : Sheaf J CommRingCat.{u}) (r : E ⟶ O)
    (hr : Presheaf.IsLocallySurjective J r.hom) (α : A ⟶ E) (hα : α ≫ r = a)
    (r' : (sheafCompose J (forget₂ CommRingCat.{u} RingCat.{u})).obj E ⟶
      (sheafCompose J (forget₂ CommRingCat.{u} RingCat.{u})).obj O)
    (hr' : (sheafCompose J (forget₂ CommRingCat.{u} RingCat.{u})).map r = r')
    (ι : (SheafOfModules.restrictScalars r').obj M ⟶
      SheafOfModules.unit ((sheafCompose J (forget₂ CommRingCat.{u} RingCat.{u})).obj E))
    (hzero : ∀ (U : Cᵒᵖ) (m : M.val.obj U), r'.hom.app U (ι.val.app U m) = 0)
    (hexists : ∀ (U : Cᵒᵖ) (x : E.obj.obj U), r.hom.app U x = 0 →
      ∃ m : M.val.obj U, (ι.val.app U m : E.obj.obj U) = x)
    (hinj : ∀ U : Cᵒᵖ, Function.Injective (ι.val.app U))
    (hsq : ∀ (U : Cᵒᵖ) (x y : E.obj.obj U), r.hom.app U x = 0 → r.hom.app U y = 0 →
      x * y = 0) :
    AlgebraExtension a M where
  extension := E
  reduction := r
  locallySurjective := hr
  squareZero U := by
    rw [pow_two, eq_bot_iff]
    exact Ideal.mul_le.2 fun x hx y hy => (Ideal.mem_bot).2 (hsq U x y hx hy)
  algebraMap := α
  algebraMap_reduction := hα
  kernelInclusion := hr' ▸ ι
  kernelZero U m := by
    subst hr'
    exact hzero U m
  kernelUniversal U x hx := by
    subst hr'
    obtain ⟨m, hm⟩ := hexists U x hx
    exact ⟨m, hm, fun n hn => hinj U (hn.trans hm.symm)⟩

variable {N : SheafOfModules.{u} ((sheafCompose J (forget₂ CommRingCat.{u} RingCat.{u})).obj O)}

/-- **An extension by `ℳ` read as an extension by `𝒩`**, along an isomorphism `e : ℳ ≅ 𝒩` of
`𝒪`-modules: the same middle term, reduction and algebra structure, with the kernel identified
with `𝒩` through `e⁻¹`. -/
def transportKernel (P : AlgebraExtension a M) (e : M ≅ N) : AlgebraExtension a N where
  extension := P.extension
  reduction := P.reduction
  locallySurjective := P.locallySurjective
  squareZero := P.squareZero
  algebraMap := P.algebraMap
  algebraMap_reduction := P.algebraMap_reduction
  kernelInclusion :=
    (SheafOfModules.restrictScalars
      ((sheafCompose J (forget₂ CommRingCat.{u} RingCat.{u})).map P.reduction)).map e.inv ≫
      P.kernelInclusion
  kernelZero U n := P.kernelZero U (e.inv.val.app U n)
  kernelUniversal U x hx := by
    obtain ⟨m, hm, hmu⟩ := P.kernelUniversal U x hx
    refine ⟨e.hom.val.app U m, ?_, fun n hn => ?_⟩
    · change P.incl (e.inv.val.app U (e.hom.val.app U m)) = x
      rw [← SheafOfModules.comp_val_app_apply, e.hom_inv_id]
      exact hm
    · have h := hmu (e.inv.val.app U n) hn
      rw [← h, ← SheafOfModules.comp_val_app_apply, e.inv_hom_id]
      rfl

/-- The identity of the middle term is a morphism of extensions along `e` from `P` to its
transport along `e`. -/
def transportKernelMapAlong (P : AlgebraExtension a M) (e : M ≅ N) :
    MapAlong e.hom P (P.transportKernel e) where
  hom := 𝟙 _
  reduction_comm := Category.id_comp _
  algebraMap_comm := Category.comp_id _
  kernel_comm U m := by
    change P.incl m = P.incl (e.inv.val.app U (e.hom.val.app U m))
    rw [← SheafOfModules.comp_val_app_apply, e.hom_inv_id]
    rfl

end Deformation.AlgebraExtension

namespace AlgebraicGeometry.Space

variable (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)
  {X Y : AlgebraicSpaces B S hS} (Z : ClosedSubspaces B S hS X.1)

/-- The reduction `i^♯ : i^{-1}𝒪_X ⟶ 𝒪_Z`, forgetting commutativity, is the ring-level
inverse-image form `structureSharpRingInverseImage` of the structure map. -/
theorem forget₂_map_structureSharpInverseImage (f : X ⟶ Y) :
    (sheafCompose (SmallEtale.topology B S hS X.1) (forget₂ CommRingCat.{u} RingCat.{u})).map
        (structureSharpInverseImage B S hS f) =
      structureSharpRingInverseImage B S hS f :=
  fSharpInverseImage_eq_structureSharpRingInverseImage B S hS f

/-- **The extension of a first-order thickening.** For a first-order thickening `Z ⊆ X` with
inclusion `i` and a morphism `g : X ⟶ Y`, the inverse image `i^{-1}𝒪_X` with the reduction
`i^♯ : i^{-1}𝒪_X ⟶ 𝒪_Z` is an extension of `(i ≫ g)^{-1}𝒪_Y`-algebras of `𝒪_Z` by the conormal
module `𝒞_{Z/X}`, on the small étale site of `Z`. -/
def firstOrderAlgebraExtension (hZ : IsFirstOrderThickening B S hS X Z.1) (g : X ⟶ Y) :
    Deformation.AlgebraExtension
      (J := SmallEtale.topology B S hS Z.1.toFunctor)
      (structureSharpInverseImage B S hS (subspaceInclusion B S hS X Z ≫ g))
      (conormalModule B S hS X Z) :=
  Deformation.AlgebraExtension.ofKernelInclusion (J := SmallEtale.topology B S hS Z.1.toFunctor)
    (A := inverseImageStructureSheaf B S hS (subspaceInclusion B S hS X Z ≫ g))
    (O := (smallEtaleRingedTopos B S hS ⟨Z.1.toFunctor, Z.2.1⟩).O)
    (M := conormalModule B S hS X Z)
    (inverseImageStructureSheaf B S hS (subspaceInclusion B S hS X Z))
    (structureSharpInverseImage B S hS (subspaceInclusion B S hS X Z))
    (isLocallySurjective_structureSharpInverseImage B S hS (subspaceInclusion B S hS X Z) Z.2.2)
    (inverseImageStructureSheafMap B S hS (subspaceInclusion B S hS X Z) g)
    (inverseImageStructureSheafMap_comp_structureSharpInverseImage B S hS _ g)
    (structureSharpRingInverseImage B S hS (subspaceInclusion B S hS X Z))
    (forget₂_map_structureSharpInverseImage B S hS _)
    (conormalInverseImageι B S hS Z hZ)
    (app_conormalInverseImageι_eq_zero B S hS Z hZ)
    (fun U x hx => exists_conormalInverseImageι_eq B S hS Z hZ U x (by
      rw [← forget₂_map_structureSharpInverseImage]; exact hx))
    (conormalInverseImageι_injective B S hS Z hZ)
    (fun U x y hx hy => mul_eq_zero_of_structureSharpRingInverseImage_app_eq_zero B S hS Z hZ U
      x y (by rw [← forget₂_map_structureSharpInverseImage]; exact hx)
      (by rw [← forget₂_map_structureSharpInverseImage]; exact hy))

/-- The middle term of the extension of a first-order thickening is `i^{-1}𝒪_X`. -/
@[simp]
theorem firstOrderAlgebraExtension_extension (hZ : IsFirstOrderThickening B S hS X Z.1)
    (g : X ⟶ Y) :
    (firstOrderAlgebraExtension B S hS Z hZ g).extension =
      inverseImageStructureSheaf B S hS (subspaceInclusion B S hS X Z) :=
  rfl

/-- The reduction of the extension of a first-order thickening is `i^♯`. -/
@[simp]
theorem firstOrderAlgebraExtension_reduction (hZ : IsFirstOrderThickening B S hS X Z.1)
    (g : X ⟶ Y) :
    (firstOrderAlgebraExtension B S hS Z hZ g).reduction =
      structureSharpInverseImage B S hS (subspaceInclusion B S hS X Z) :=
  rfl

/-- The algebra structure of the extension of a first-order thickening is the inverse image
of `g^♯`. -/
@[simp]
theorem firstOrderAlgebraExtension_algebraMap (hZ : IsFirstOrderThickening B S hS X Z.1)
    (g : X ⟶ Y) :
    (firstOrderAlgebraExtension B S hS Z hZ g).algebraMap =
      inverseImageStructureSheafMap B S hS (subspaceInclusion B S hS X Z) g :=
  rfl

/-! ### Flat deformations: the ideal is pulled back from the base -/

section Flat

variable {X' : AlgebraicSpaces B S hS} (Z' : ClosedSubspaces B S hS X'.1) (q : X ⟶ X')
  (f : (⟨Z.1.toFunctor, Z.2.1⟩ : AlgebraicSpaces B S hS) ⟶
    (⟨Z'.1.toFunctor, Z'.2.1⟩ : AlgebraicSpaces B S hS))

/-- The upper closed subspace of a fibre product square whose lower closed subspace is a
first-order thickening is a first-order thickening. -/
theorem isFirstOrderThickening_of_isPullback (hcart : IsPullback Z.1.ι f.hom q.hom Z'.1.ι)
    (hZ' : IsFirstOrderThickening B S hS X' Z'.1) : IsFirstOrderThickening B S hS X Z.1 := by
  rw [closedSubspaces_eq_preimageSubspace_of_isPullback B S hS Z Z' q f hcart]
  exact isFirstOrderThickening_preimage B S hS Z'.1 q hZ'

/-- **The extension of a flat first-order deformation, by the pulled-back ideal.** Let
```
Z --i--→ X
|        |
f        q
↓        ↓
Z' -i'-→ X'
```
be a fibre product square of algebraic spaces whose horizontal arrows are the inclusions of
closed subspaces, with `Z' ⊆ X'` a first-order thickening and `q` flat as a morphism of small
étale ringed topoi, and let `g : X ⟶ Y`. Then `i^{-1}𝒪_X ⟶ 𝒪_Z` is an extension of
`(i ≫ g)^{-1}𝒪_Y`-algebras of `𝒪_Z` by `f^*𝒞_{Z'/X'}`: the extension of the first-order
thickening `Z ⊆ X` (`AlgebraicGeometry.Space.firstOrderAlgebraExtension`) with its kernel
`𝒞_{Z/X}` identified with `f^*𝒞_{Z'/X'}` through the conormal map. -/
def flatFirstOrderAlgebraExtension
    (hsq : subspaceInclusion B S hS X Z ≫ q = f ≫ subspaceInclusion B S hS X' Z')
    (hcart : IsPullback Z.1.ι f.hom q.hom Z'.1.ι)
    (hq : (smallEtaleRingedToposHom B S hS q).IsFlat)
    (hZ' : IsFirstOrderThickening B S hS X' Z'.1) (g : X ⟶ Y) :
    Deformation.AlgebraExtension
      (J := SmallEtale.topology B S hS Z.1.toFunctor)
      (structureSharpInverseImage B S hS (subspaceInclusion B S hS X Z ≫ g))
      ((modulePullback B S hS f).obj (conormalModule B S hS X' Z')) :=
  haveI := isIso_conormalMap_of_isPullback_of_isFlat B S hS Z Z' q f hsq hcart hq
  (firstOrderAlgebraExtension B S hS Z
      (isFirstOrderThickening_of_isPullback B S hS Z Z' q f hcart hZ') g).transportKernel
    (asIso (conormalMap B S hS Z Z' q f hsq)).symm

/-- **The extension of a flat first-order deformation, for a flat morphism of algebraic
spaces.** `AlgebraicGeometry.Space.flatFirstOrderAlgebraExtension` with `q` flat as a morphism
of algebraic spaces. -/
def flatFirstOrderAlgebraExtensionOfIsFlat
    (hsq : subspaceInclusion B S hS X Z ≫ q = f ≫ subspaceInclusion B S hS X' Z')
    (hcart : IsPullback Z.1.ι f.hom q.hom Z'.1.ι) (hq : IsFlat B S hS q.hom)
    (hZ' : IsFirstOrderThickening B S hS X' Z'.1) (g : X ⟶ Y) :
    Deformation.AlgebraExtension
      (J := SmallEtale.topology B S hS Z.1.toFunctor)
      (structureSharpInverseImage B S hS (subspaceInclusion B S hS X Z ≫ g))
      ((modulePullback B S hS f).obj (conormalModule B S hS X' Z')) :=
  flatFirstOrderAlgebraExtension B S hS Z Z' q f hsq hcart
    ((isFlat_iff_smallEtaleRingedToposHom_isFlat B S hS q).1 hq) hZ' g

end Flat

end AlgebraicGeometry.Space

end
