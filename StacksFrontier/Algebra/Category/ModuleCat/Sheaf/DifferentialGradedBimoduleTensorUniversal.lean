module

public import StacksFrontier.Algebra.Category.ModuleCat.Sheaf.DifferentialGradedBimoduleTensor
public import StacksFrontier.Algebra.Category.ModuleCat.Sheaf.DifferentialGradedTensor
public import StacksFrontier.Algebra.Category.ModuleCat.Sheaf.SliceFamilyPresheaf
public import StacksFrontier.Algebra.Category.ModuleCat.Sheaf.SliceSheafification

/-!
# `M ⊗_A N` is the tensor product of `M` and `N`

Let `O` be a sheaf of commutative rings on a site, let `A` and `B` be sheaves of differential
graded `O`-algebras, let `M` be a right differential graded `A`-module and let `N` be a
differential graded `(A, B)`-bimodule. The right differential graded `B`-module
`SheafOfModules.RelativeTensor.dgTensorRight M N` is `M ⊗_A N`, and this file checks every
clause of `SheafOfModules.IsTensorProduct` for it: the multiplication map `(x, y) ↦ x ⊗ y` is
bilinear over the sheaf of rings, compatible with restriction and `A`-balanced, the right
`B`-action is `(x ⊗ y) b = x ⊗ y b`, the differential obeys the signed Leibniz rule
`d (x ⊗ y) = d x ⊗ y + (-1)^i x ⊗ d y`, and composition with the multiplication map is a
bijection from the degree-`n` local homomorphisms out of `M ⊗_A N` onto the `A`-balanced
bilinear families of degree `n`. Letting `M` vary gives the tensor product functor
`- ⊗_A N` on right differential graded `A`-modules.

## Main definitions

* `SheafOfModules.IsTensorProductCore` is `SheafOfModules.IsTensorProduct` with the universal
  property removed: the multiplication map and its seven laws.
* `SheafOfModules.IsTensorProductCore.toIsTensorProduct` reassembles a tensor product from a
  core together with the universal property, so the two are jointly equivalent to
  `SheafOfModules.IsTensorProduct`.
* `SheafOfModules.RelativeTensor.compTmul` composes a degree-`n` local homomorphism out of
  `M ⊗_A N` with the multiplication map, and `SheafOfModules.RelativeTensor.descLocalHom` is
  the inverse construction, the descent of an `A`-balanced bilinear family.
* `SheafOfModules.RelativeTensor.descZ` descends an `A`-balanced bilinear family into the
  presheaf of slice families of the target, and `SheafOfModules.RelativeTensor.descSlice`
  transposes that descent to a morphism over the slice site at `U`.
* `SheafOfModules.RelativeTensor.dgTensorRightFunctor` is the functor `- ⊗_A N` from right
  differential graded `A`-modules to right differential graded `B`-modules, and
  `SheafOfModules.RelativeTensor.dgTensorRightMap` is its action on morphisms.

## Main results

* `SheafOfModules.RelativeTensor.isTensorProductDgTensorRight`: **`M ⊗_A N` is the tensor
  product of `M` and `N`**, with multiplication map the local section `x ⊗ y`. Its universal
  property is `SheafOfModules.RelativeTensor.universalDgTensorRight`, whose two halves are
  `compTmul_descLocalHom` and `descLocalHom_compTmul`.
* `SheafOfModules.RelativeTensor.tensorFunctorDataDgTensorRight`: **the tensor products with a
  fixed bimodule `N` assemble into a functor** `- ⊗_A N` acting on local sections by
  `x ⊗ y ↦ f x ⊗ y`.
* `SheafOfModules.RelativeTensor.isTensorProductCoreDgTensorRight`: the clauses other than the
  universal property. `SheafOfModules.RelativeTensor.dgTensorRight_tmul_balanced`,
  `dgTensorRight_tmul_rightMul` and `dgTensorRight_tmul_d` are the three of them carrying a
  degree transport: the `A`-balancing, the right `B`-action and the signed Leibniz rule.
* `SheafOfModules.RelativeTensor.descSlice_tmul` and
  `SheafOfModules.RelativeTensor.descSlice_smul`: the descent over the slice site sends
  `x ⊗ y` to the given balanced bilinear family and is `B`-linear.

## Implementation notes

The multiplication map is `SheafOfModules.RelativeTensor.tmul` at the index `(i, j)` of total
degree `i + j`, read through the canonical balanced bilinear family
`SheafOfModules.RelativeTensor.tmulBalanced`, which is where its bilinearity, its naturality and
its `A`-balancing come from. Degrees are carried as in
`StacksFrontier/Algebra/Category/ModuleCat/Sheaf/DifferentialGradedTensor.lean`: the total degree of
a local section `x ⊗ y` is `i + j` on the nose, so the clauses whose two sides have
propositionally equal total degrees are stated with `HEq` or with
`SheafOfModules.gradedCast`, and `SheafOfModules.RelativeTensor.tmul_heq` is what compares two
local sections `x ⊗ y` across such an equality.

**How the universal property is proved.** Composition with the multiplication map goes in the
easy direction. Its inverse asks for a degree-`n` homomorphism out of `M ⊗_A N` over the slice
site at `U` from an `A`-balanced bilinear family given only on the objects `V ⟶ U`, and degree
`k` of `M ⊗_A N` is a sheafification of a cokernel of a coproduct, whose sections cannot be
written down; the descent `SheafOfModules.RelativeTensor.Balanced.desc` is moreover *global*,
producing a morphism over the whole site. The two gaps are bridged by `Stacks.sliceFamily`, the
presheaf of slice families of `StacksFrontier/Algebra/Category/ModuleCat/Sheaf/
SliceFamilyPresheaf.lean`: a morphism into it on the whole site *is* a morphism over the slice
site, so the balanced family descends globally into the slice families of `L` and is then
evaluated at the identity. The resulting morphism of presheaves of modules over the slice site
is transposed across the sheafification unit by
`PresheafOfModules.homEquivOfIsLocallyBijective`, which applies because the unit stays locally
bijective after restriction to a slice site — the content of
`Stacks.SheafOfModules.SliceSheafification`.

Both halves of the bijection, and the `B`-linearity of the descent, are statements about
arbitrary local sections of a sheafification, so none can be checked on pure tensors directly.
Each is reduced to pure tensors in two steps: a bilinear map into a separated presheaf of
modules is determined by its restriction along a locally surjective morphism
(`Stacks.BilinearMap.app_eq_of_isLocallySurjective`, and `Stacks.eq_of_forall_lift` for the
one-variable statement), which brings the statement down to the presheaf-level tensor product;
there it is an identity between morphisms out of a cokernel of a coproduct, reduced by
`CategoryTheory.Limits.cancel_epi`, `CategoryTheory.Limits.Sigma.hom_ext` and
`PresheafOfModules.tensorObj_hom_ext` to a pure tensor. This is the shape of
`SheafOfModules.RelativeTensor.actPre_comp_descZ`, `descSlice_smul`, `descZ_compTmul` and
`gradedTensorMapRight_smul`.

Target degrees are carried as parameters with a proof, as in
`SheafOfModules.LocalHom`: `descZ`, `descSlice` and their lemmas take the target degree `d`
together with `m + n = d` rather than using `m + n` on the nose, so that the `B`-linearity of
the descent compares two sections of one and the same sheaf and needs no transport.

**Universes: why `max u v` and not the free `max u v z` of
`StacksFrontier/Algebra/Category/ModuleCat/Sheaf/GradedBimoduleTensorAction.lean`.**
`SheafOfModules.RelativeTensor.dgTensorRight` is available at every universe at least as large
as the site's, and this file is its instance at the site's own. What pins it is the slice site:
`descSlice` inverts `PresheafOfModules.homEquivOfIsLocallyBijective` for the restricted
sheafification unit, and the sheaf it lands in is `((L.complex.X d).over U).isSheaf`, which
needs `(J.over U).WEqualsLocallyBijective AddCommGrpCat` at the module universe. The only
instance supplying that is the one of `Mathlib/CategoryTheory/Sites/LocallyBijective.lean`,
whose concrete category must have carriers in `Type (max u v)` for a site `C : Type u` with
`Category.{v} C`; on `Over U` that reads `max (max u v) v = max u v` and never a larger
universe. `StacksFrontier/Algebra/Category/ModuleCat/Sheaf/TensorSheafOverSlice.lean` records that
the slice topology's sheafification hypotheses do not follow from the site's, so there is no
other route. Generalizing this file would mean adding
`[(J.over U).WEqualsLocallyBijective AddCommGrpCat.{max u v z}]` as a hypothesis, which is a
weaker statement, not a more general one.

`actPre_comp_mapPreRight` names the universe levels of its `actPre`, whose module universe is
`max u v z` with `z := max u v` here; `max u v ?z =?= max u v` is postponed rather than solved
by `Lean.Meta.isLevelDefEqAux`, and in that proof the postponed constraints cost more than
200000 heartbeats.

## References

* [Stacks Project, Tag 0FRM](https://stacks.math.columbia.edu/tag/0FRM)
* [Stacks Project, Tag 0FRQ](https://stacks.math.columbia.edu/tag/0FRQ)
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits CategoryTheory.Sheaf

open scoped TensorProduct

universe t a w z s v u

namespace SheafOfModules

section Core

variable {C : Type u} [Category.{v} C] {J : GrothendieckTopology C} {R : Sheaf J RingCat.{t}}
  {A B : DifferentialGradedAlgebra.{t, a} R}

/-- The multiplication map of a tensor product `M ⊗_A N` and its seven laws: the clauses of
`SheafOfModules.IsTensorProduct` other than the universal property. -/
structure IsTensorProductCore (M : DifferentialGradedModule.{t, a, w} A)
    (N : DifferentialGradedBimodule.{t, a, z} A B)
    (T : DifferentialGradedModule.{t, a, s} B) where
  /-- The universal multiplication map `M^i × N^j → T^{i + j}` on local sections. -/
  tmul (i j : ℤ) (U : Cᵒᵖ) :
    (M.complex.X i).val.obj U →+ (N.complex.X j).val.obj U →+ (T.complex.X (i + j)).val.obj U
  /-- The multiplication is linear over the sheaf of rings in the first variable. -/
  tmul_smul_left (i j : ℤ) (U : Cᵒᵖ) (r : R.obj.obj U) (x : (M.complex.X i).val.obj U)
      (y : (N.complex.X j).val.obj U) :
    tmul i j U (r • x) y = r • tmul i j U x y
  /-- The multiplication is linear over the sheaf of rings in the second variable. -/
  tmul_smul_right (i j : ℤ) (U : Cᵒᵖ) (r : R.obj.obj U) (x : (M.complex.X i).val.obj U)
      (y : (N.complex.X j).val.obj U) :
    tmul i j U x (r • y) = r • tmul i j U x y
  /-- The multiplication commutes with restriction. -/
  tmul_naturality (i j : ℤ) {U V : Cᵒᵖ} (g : U ⟶ V) (x : (M.complex.X i).val.obj U)
      (y : (N.complex.X j).val.obj U) :
    (T.complex.X (i + j)).val.map g (tmul i j U x y) =
      tmul i j V ((M.complex.X i).val.map g x) ((N.complex.X j).val.map g y)
  /-- The multiplication is `A`-balanced: `x a ⊗ y = x ⊗ a y`. -/
  tmul_balanced (i p j : ℤ) (U : Cᵒᵖ) (x : (M.complex.X i).val.obj U)
      (a : (A.complex.X p).val.obj U) (y : (N.complex.X j).val.obj U) :
    HEq (tmul (i + p) j U ((M.mul i p).app U x a) y)
      (tmul i (p + j) U x ((N.leftMul p j).app U a y))
  /-- The right `B`-action on `T` is `(x ⊗ y) b = x ⊗ y b`. -/
  tmul_rightMul (i j p : ℤ) (U : Cᵒᵖ) (x : (M.complex.X i).val.obj U)
      (y : (N.complex.X j).val.obj U) (b : (B.complex.X p).val.obj U) :
    HEq ((T.mul (i + j) p).app U (tmul i j U x y) b)
      (tmul i (j + p) U x ((N.rightMul j p).app U y b))
  /-- The differential of `T` obeys the signed Leibniz rule
  `d (x ⊗ y) = d x ⊗ y + (-1)^i x ⊗ d y`. -/
  tmul_d (i j : ℤ) (U : Cᵒᵖ) (x : (M.complex.X i).val.obj U)
      (y : (N.complex.X j).val.obj U) :
    (T.complex.d (i + j) (i + j + 1)).val.app U (tmul i j U x y) =
      gradedCast (fun q ↦ (T.complex.X q).val.obj U) (add_right_comm i 1 j)
          (tmul (i + 1) j U ((M.complex.d i (i + 1)).val.app U x) y) +
        (Int.negOnePow i : ℤ) •
          gradedCast (fun q ↦ (T.complex.X q).val.obj U) (add_assoc i j 1).symm
            (tmul i (j + 1) U x ((N.complex.d j (j + 1)).val.app U y))

/-- A core together with the universal property of composition with its multiplication map is a
tensor product. -/
def IsTensorProductCore.toIsTensorProduct {M : DifferentialGradedModule.{t, a, w} A}
    {N : DifferentialGradedBimodule.{t, a, z} A B} {T : DifferentialGradedModule.{t, a, s} B}
    (core : IsTensorProductCore M N T)
    (universal : ∀ (L : DifferentialGradedModule.{t, a, s} B) (n : ℤ) (U : C),
      LocalHom T L n U ≃ LocalBalancedBilinear M N L n U)
    (universal_app : ∀ (L : DifferentialGradedModule.{t, a, s} B) (n : ℤ) (U : C)
      (f : LocalHom T L n U) (i j k : ℤ) (hijk : i + j + n = k) (V : Over U)
      (x : (M.complex.X i).val.obj (Opposite.op V.left))
      (y : (N.complex.X j).val.obj (Opposite.op V.left)),
      (universal L n U f).app i j k hijk V x y =
        f.app (i + j) k hijk V (core.tmul i j (Opposite.op V.left) x y)) :
    IsTensorProduct M N T where
  tmul := core.tmul
  tmul_smul_left := core.tmul_smul_left
  tmul_smul_right := core.tmul_smul_right
  tmul_naturality := core.tmul_naturality
  tmul_balanced := core.tmul_balanced
  tmul_rightMul := core.tmul_rightMul
  tmul_d := core.tmul_d
  universal := universal
  universal_app := universal_app

/-- The core of a tensor product: its multiplication map and the seven laws. -/
def IsTensorProduct.toCore {M : DifferentialGradedModule.{t, a, w} A}
    {N : DifferentialGradedBimodule.{t, a, z} A B} {T : DifferentialGradedModule.{t, a, s} B}
    (hT : IsTensorProduct M N T) : IsTensorProductCore M N T where
  tmul := hT.tmul
  tmul_smul_left := hT.tmul_smul_left
  tmul_smul_right := hT.tmul_smul_right
  tmul_naturality := hT.tmul_naturality
  tmul_balanced := hT.tmul_balanced
  tmul_rightMul := hT.tmul_rightMul
  tmul_d := hT.tmul_d

end Core

section HeqCongr

variable {C : Type u} [Category.{v} C] {J : GrothendieckTopology C} {R : Sheaf J RingCat.{t}}
  {A' : DifferentialGradedAlgebra.{t, a} R}

/-- A degree-`n` map of the underlying graded modules takes heterogeneously equal local
sections of propositionally equal degrees to the same value. -/
theorem LocalGradedHom.app_heq_congr {K : DifferentialGradedModule.{t, a, w} A'}
    {L : DifferentialGradedModule.{t, a, z} A'} {n : ℤ} {U : C}
    (f : LocalGradedHom K L n U) {i i' j : ℤ} (hii' : i = i') (hij : i + n = j)
    (hij' : i' + n = j) (V : Over U)
    {x : (K.complex.X i).val.obj (Opposite.op V.left)}
    {x' : (K.complex.X i').val.obj (Opposite.op V.left)} (hx : HEq x x') :
    f.app i j hij V x = f.app i' j hij' V x' := by
  subst hii'
  obtain rfl := eq_of_heq hx
  rfl

end HeqCongr


namespace RelativeTensor

open Stacks

variable {C : Type u} [Category.{v} C] {J : GrothendieckTopology C}
  [J.HasSheafCompose (forget₂ CommRingCat.{t} RingCat.{t})] {Osharp : Sheaf J CommRingCat.{t}}

section Heq

variable [J.WEqualsLocallyBijective AddCommGrpCat.{max u v}]
  [HasWeakSheafify J AddCommGrpCat.{max u v}]
  {A : GradedAlgebra.{t, max u v} (toRingCat J Osharp)}
  (P : GradedModule.{t, max u v, max u v} A) (N : LeftGradedModule.{t, max u v, max u v} A)

/-- Local sections `x ⊗ y` of propositionally equal total degrees, with corresponding indices
and heterogeneously equal arguments, are heterogeneously equal. -/
theorem tmul_heq {n n' : ℤ} (hn : n = n') {p : TensorIndex n} {p' : TensorIndex n'}
    (hp : p.1 = p'.1) (X : Cᵒᵖ) {x : (P.piece p.1.1).val.obj X}
    {x' : (P.piece p'.1.1).val.obj X} (hx : HEq x x') {y : (N.piece p.1.2).val.obj X}
    {y' : (N.piece p'.1.2).val.obj X} (hy : HEq y y') :
    HEq (tmul P N n p X x y) (tmul P N n' p' X x' y') := by
  subst hn
  obtain rfl : p = p' := Subtype.ext hp
  obtain rfl := eq_of_heq hx
  obtain rfl := eq_of_heq hy
  rfl

end Heq

variable {A B : DifferentialGradedAlgebra.{t, max u v} (toRingCat J Osharp)}
  (M : DifferentialGradedModule.{t, max u v, max u v} A)
  (N : DifferentialGradedBimodule.{t, max u v, max u v} A B)
  [J.WEqualsLocallyBijective AddCommGrpCat.{max u v}]
  [HasWeakSheafify J AddCommGrpCat.{max u v}]

/-- The index `(i, j)` of the summand of total degree `i + j`. -/
abbrev tensorIndexPair (i j : ℤ) : TensorIndex (i + j) := ⟨(i, j), rfl⟩

/-- **The multiplication map of `M ⊗_A N`**: the local section `x ⊗ y`, biadditive in `x` and
`y`. -/
noncomputable def dgTmul (i j : ℤ) (U : Cᵒᵖ) :
    (M.complex.X i).val.obj U →+ (N.complex.X j).val.obj U →+
      ((dgTensorRight M N).complex.X (i + j)).val.obj U :=
  ((tmulBalanced (gP M) N.toGradedBimodule.toLeftGradedModule (i + j)).app
    (tensorIndexPair i j)).app U

/-- The multiplication map of `M ⊗_A N` sends `(x, y)` to the local section `x ⊗ y` at the
index `(i, j)`. -/
@[simp]
theorem dgTmul_apply (i j : ℤ) (U : Cᵒᵖ) (x : (M.complex.X i).val.obj U)
    (y : (N.complex.X j).val.obj U) :
    dgTmul M N i j U x y =
      tmul (gP M) N.toGradedBimodule.toLeftGradedModule (i + j) (tensorIndexPair i j) U x y :=
  rfl

/-- The multiplication map of `M ⊗_A N` is linear over the sheaf of rings in the first
variable. -/
theorem dgTensorRight_tmul_smul_left (i j : ℤ) (U : Cᵒᵖ)
    (r : (toRingCat J Osharp).obj.obj U) (x : (M.complex.X i).val.obj U)
    (y : (N.complex.X j).val.obj U) :
    dgTmul M N i j U (r • x) y = r • dgTmul M N i j U x y :=
  ((tmulBalanced (gP M) N.toGradedBimodule.toLeftGradedModule (i + j)).app
    (tensorIndexPair i j)).map_smul_left U r x y

/-- The multiplication map of `M ⊗_A N` is linear over the sheaf of rings in the second
variable. -/
theorem dgTensorRight_tmul_smul_right (i j : ℤ) (U : Cᵒᵖ)
    (r : (toRingCat J Osharp).obj.obj U) (x : (M.complex.X i).val.obj U)
    (y : (N.complex.X j).val.obj U) :
    dgTmul M N i j U x (r • y) = r • dgTmul M N i j U x y :=
  ((tmulBalanced (gP M) N.toGradedBimodule.toLeftGradedModule (i + j)).app
    (tensorIndexPair i j)).map_smul_right U r x y

/-- The multiplication map of `M ⊗_A N` commutes with restriction. -/
theorem dgTensorRight_tmul_naturality (i j : ℤ) {U V : Cᵒᵖ} (g : U ⟶ V)
    (x : (M.complex.X i).val.obj U) (y : (N.complex.X j).val.obj U) :
    ((dgTensorRight M N).complex.X (i + j)).val.map g (dgTmul M N i j U x y) =
      dgTmul M N i j V ((M.complex.X i).val.map g x) ((N.complex.X j).val.map g y) :=
  ((tmulBalanced (gP M) N.toGradedBimodule.toLeftGradedModule (i + j)).app
    (tensorIndexPair i j)).naturality g x y

/-- **The multiplication map of `M ⊗_A N` is `A`-balanced**: `x a ⊗ y = x ⊗ a y`. -/
theorem dgTensorRight_tmul_balanced (i p j : ℤ) (U : Cᵒᵖ) (x : (M.complex.X i).val.obj U)
    (aa : (A.complex.X p).val.obj U) (y : (N.complex.X j).val.obj U) :
    HEq (dgTmul M N (i + p) j U ((M.mul i p).app U x aa) y)
      (dgTmul M N i (p + j) U x ((N.leftMul p j).app U aa y)) := by
  refine HEq.trans (heq_of_eq ((tmulBalanced (gP M) N.toGradedBimodule.toLeftGradedModule
    (i + p + j)).balanced ⟨(i, p, j), rfl⟩ U x aa y)) ?_
  exact tmul_heq (gP M) N.toGradedBimodule.toLeftGradedModule (add_assoc i p j) rfl U
    HEq.rfl HEq.rfl

/-- **The right `B`-action on `M ⊗_A N`**: `(x ⊗ y) b = x ⊗ y b`. -/
theorem dgTensorRight_tmul_rightMul (i j p : ℤ) (U : Cᵒᵖ) (x : (M.complex.X i).val.obj U)
    (y : (N.complex.X j).val.obj U) (b : (B.complex.X p).val.obj U) :
    HEq (((dgTensorRight M N).mul (i + j) p).app U (dgTmul M N i j U x y) b)
      (dgTmul M N i (j + p) U x ((N.rightMul j p).app U y b)) := by
  refine HEq.trans (heq_of_eq (dgTensorRight_mul_tmul M N (i + j) p
    (tensorIndexPair i j) U x y b)) ?_
  exact tmul_heq (gP M) N.toGradedBimodule.toLeftGradedModule (add_assoc i j p) rfl U
    HEq.rfl HEq.rfl

/-- **The signed Leibniz rule for the differential of `M ⊗_A N`**:
`d (x ⊗ y) = d x ⊗ y + (-1)^i x ⊗ d y`. -/
theorem dgTensorRight_tmul_d (i j : ℤ) (U : Cᵒᵖ) (x : (M.complex.X i).val.obj U)
    (y : (N.complex.X j).val.obj U) :
    ((dgTensorRight M N).complex.d (i + j) (i + j + 1)).val.app U (dgTmul M N i j U x y) =
      gradedCast (fun q ↦ ((dgTensorRight M N).complex.X q).val.obj U) (add_right_comm i 1 j)
          (dgTmul M N (i + 1) j U ((M.complex.d i (i + 1)).val.app U x) y) +
        (Int.negOnePow i : ℤ) •
          gradedCast (fun q ↦ ((dgTensorRight M N).complex.X q).val.obj U)
            (add_assoc i j 1).symm
            (dgTmul M N i (j + 1) U x ((N.complex.d j (j + 1)).val.app U y)) := by
  refine (dgTensorRight_d_tmul M N (i + j) (tensorIndexPair i j) U x y).trans ?_
  refine congrArg₂ (fun u u' ↦ u + (Int.negOnePow i : ℤ) • u') (eq_of_heq ?_) (eq_of_heq ?_)
  · exact HEq.trans (tmul_heq (gP M) N.toGradedBimodule.toLeftGradedModule
      (add_right_comm i 1 j).symm rfl U HEq.rfl HEq.rfl)
      (gradedCast_heq (fun q ↦ ((dgTensorRight M N).complex.X q).val.obj U)
        (add_right_comm i 1 j) _).symm
  · exact HEq.trans (tmul_heq (gP M) N.toGradedBimodule.toLeftGradedModule
      (add_assoc i j 1) rfl U HEq.rfl HEq.rfl)
      (gradedCast_heq (fun q ↦ ((dgTensorRight M N).complex.X q).val.obj U)
        (add_assoc i j 1).symm _).symm

/-- **`M ⊗_A N` satisfies every clause of the tensor product of `M` and `N` except the
universal property**: its multiplication map is the local section `x ⊗ y`. -/
noncomputable def isTensorProductCoreDgTensorRight :
    IsTensorProductCore M N (dgTensorRight M N) where
  tmul := dgTmul M N
  tmul_smul_left := dgTensorRight_tmul_smul_left M N
  tmul_smul_right := dgTensorRight_tmul_smul_right M N
  tmul_naturality i j {_ _} g x y := dgTensorRight_tmul_naturality M N i j g x y
  tmul_balanced := dgTensorRight_tmul_balanced M N
  tmul_rightMul := dgTensorRight_tmul_rightMul M N
  tmul_d := dgTensorRight_tmul_d M N

/-! ### The universal property

A degree-`n` local homomorphism out of `M ⊗_A N` over the slice site at `U` is built from an
`A`-balanced bilinear family by descending it, globally on the site, into the presheaf of slice
families `Stacks.sliceFamily` of the target, restricting that descent to the slice site and
evaluating it at the identity. -/

section Universal

variable {M N}
variable {L : DifferentialGradedModule.{t, max u v, max u v} B} {n : ℤ} {U : C}

/-- The slice family of values of a local balanced bilinear family at a pair of local
sections. -/
noncomputable def balZApp (α : LocalBalancedBilinear M N L n U) (i j d : ℤ)
    (hd : i + j + n = d) (W : Cᵒᵖ) (x : (M.complex.X i).val.obj W)
    (y : (N.complex.X j).val.obj W) : (sliceFamily (L.complex.X d).val U).obj W :=
  zMk (fun X k g => α.app i j d hd (Over.mk g) (Stacks.restr (M.complex.X i).val k x)
      (Stacks.restr (N.complex.X j).val k y))
    (fun X Y k g h => by
      refine Eq.trans (α.naturality i j d hd (V := Over.mk g) (W := Over.mk (h.unop ≫ g))
        (Over.homMk h.unop) (Stacks.restr (M.complex.X i).val k x)
        (Stacks.restr (N.complex.X j).val k y)) ?_
      rw [← Stacks.restr_restr (M.complex.X i).val k h x,
        ← Stacks.restr_restr (N.complex.X j).val k h y]
      rfl)

omit [J.WEqualsLocallyBijective AddCommGrpCat.{max u v}]
  [HasWeakSheafify J AddCommGrpCat.{max u v}] in
/-- The component of `balZApp α i j d hd W x y` at `k : W ⟶ X` and `g : X ⟶ U` is the value of
`α` at `g` on the restrictions of `x` and `y` along `k`. -/
@[simp]
theorem zApp_balZApp (α : LocalBalancedBilinear M N L n U) (i j d : ℤ) (hd : i + j + n = d)
    (W : Cᵒᵖ) (x : (M.complex.X i).val.obj W) (y : (N.complex.X j).val.obj W) {X : Cᵒᵖ}
    (k : W ⟶ X) (g : X.unop ⟶ U) :
    zApp (balZApp α i j d hd W x y) k g =
      α.app i j d hd (Over.mk g) (Stacks.restr (M.complex.X i).val k x)
        (Stacks.restr (N.complex.X j).val k y) := rfl

omit [J.WEqualsLocallyBijective AddCommGrpCat.{max u v}]
  [HasWeakSheafify J AddCommGrpCat.{max u v}] in
/-- The slice family `balZApp α i j d hd W x y` is additive in `x`. -/
theorem balZApp_add_left (α : LocalBalancedBilinear M N L n U) (i j d : ℤ)
    (hd : i + j + n = d) (W : Cᵒᵖ) (x x' : (M.complex.X i).val.obj W)
    (y : (N.complex.X j).val.obj W) :
    balZApp α i j d hd W (x + x') y =
      balZApp α i j d hd W x y + balZApp α i j d hd W x' y :=
  zApp_ext fun X k g => by
    rw [zApp_add, zApp_balZApp, zApp_balZApp, zApp_balZApp, Stacks.restr_add,
      (α.app i j d hd (Over.mk g)).map_add]
    rfl

omit [J.WEqualsLocallyBijective AddCommGrpCat.{max u v}]
  [HasWeakSheafify J AddCommGrpCat.{max u v}] in
/-- The slice family `balZApp α i j d hd W x y` is additive in `y`. -/
theorem balZApp_add_right (α : LocalBalancedBilinear M N L n U) (i j d : ℤ)
    (hd : i + j + n = d) (W : Cᵒᵖ) (x : (M.complex.X i).val.obj W)
    (y y' : (N.complex.X j).val.obj W) :
    balZApp α i j d hd W x (y + y') =
      balZApp α i j d hd W x y + balZApp α i j d hd W x y' :=
  zApp_ext fun X k g => by
    rw [zApp_add, zApp_balZApp, zApp_balZApp, zApp_balZApp, Stacks.restr_add, map_add]

omit [J.WEqualsLocallyBijective AddCommGrpCat.{max u v}]
  [HasWeakSheafify J AddCommGrpCat.{max u v}] in
/-- The slice family `balZApp α i j d hd W x y` is linear over the sheaf of rings in `x`. -/
theorem balZApp_smul_left (α : LocalBalancedBilinear M N L n U) (i j d : ℤ)
    (hd : i + j + n = d) (W : Cᵒᵖ) (r : (toRingCat J Osharp).obj.obj W)
    (x : (M.complex.X i).val.obj W) (y : (N.complex.X j).val.obj W) :
    balZApp α i j d hd W (r • x) y = r • balZApp α i j d hd W x y :=
  zApp_ext fun X k g => by
    rw [zApp_smul, zApp_balZApp, zApp_balZApp, Stacks.restr_smul, α.map_smul_left]

omit [J.WEqualsLocallyBijective AddCommGrpCat.{max u v}]
  [HasWeakSheafify J AddCommGrpCat.{max u v}] in
/-- The slice family `balZApp α i j d hd W x y` is linear over the sheaf of rings in `y`. -/
theorem balZApp_smul_right (α : LocalBalancedBilinear M N L n U) (i j d : ℤ)
    (hd : i + j + n = d) (W : Cᵒᵖ) (r : (toRingCat J Osharp).obj.obj W)
    (x : (M.complex.X i).val.obj W) (y : (N.complex.X j).val.obj W) :
    balZApp α i j d hd W x (r • y) = r • balZApp α i j d hd W x y :=
  zApp_ext fun X k g => by
    rw [zApp_smul, zApp_balZApp, zApp_balZApp, Stacks.restr_smul, α.map_smul_right]

omit [J.WEqualsLocallyBijective AddCommGrpCat.{max u v}]
  [HasWeakSheafify J AddCommGrpCat.{max u v}] in
/-- The slice family `balZApp α i j d hd W x y` commutes with restriction along `W ⟶ W'`. -/
theorem balZApp_restr (α : LocalBalancedBilinear M N L n U) (i j d : ℤ) (hd : i + j + n = d)
    {W W' : Cᵒᵖ} (f : W ⟶ W') (x : (M.complex.X i).val.obj W)
    (y : (N.complex.X j).val.obj W) :
    Stacks.restr (sliceFamily (L.complex.X d).val U) f (balZApp α i j d hd W x y) =
      balZApp α i j d hd W' (Stacks.restr (M.complex.X i).val f x)
        (Stacks.restr (N.complex.X j).val f y) :=
  zApp_ext fun X k g => by
    rw [zApp_restr, zApp_balZApp, zApp_balZApp,
      ← Stacks.restr_restr (M.complex.X i).val f k x,
      ← Stacks.restr_restr (N.complex.X j).val f k y]

/-- A local balanced bilinear family, read as a bilinear family of slice families. -/
noncomputable def balZBil (α : LocalBalancedBilinear M N L n U) (i j d : ℤ)
    (hd : i + j + n = d) :
    Stacks.BilinearMap (M.complex.X i).val (N.complex.X j).val
      (sliceFamily (L.complex.X d).val U) where
  app W := AddMonoidHom.mk'
    (fun x => AddMonoidHom.mk' (fun y => balZApp α i j d hd W x y)
      (fun y y' => balZApp_add_right α i j d hd W x y y'))
    (fun x x' => AddMonoidHom.ext fun y => balZApp_add_left α i j d hd W x x' y)
  map_smul_left W r x y := balZApp_smul_left α i j d hd W r x y
  map_smul_right W r x y := balZApp_smul_right α i j d hd W r x y
  naturality {_W _W'} f x y := balZApp_restr α i j d hd f x y

omit [J.WEqualsLocallyBijective AddCommGrpCat.{max u v}]
  [HasWeakSheafify J AddCommGrpCat.{max u v}] in
/-- The bilinear family `balZBil α i j d hd` sends `(x, y)` to `balZApp α i j d hd W x y`. -/
@[simp]
theorem balZBil_app (α : LocalBalancedBilinear M N L n U) (i j d : ℤ) (hd : i + j + n = d)
    (W : Cᵒᵖ) (x : (M.complex.X i).val.obj W) (y : (N.complex.X j).val.obj W) :
    (balZBil α i j d hd).app W x y = balZApp α i j d hd W x y := rfl

omit [J.WEqualsLocallyBijective AddCommGrpCat.{max u v}]
  [HasWeakSheafify J AddCommGrpCat.{max u v}] in
/-- **The values of a local balanced bilinear family are `A`-balanced**: `x a` against `y` and
`x` against `a y` give the same slice family. -/
theorem balZApp_balanced (α : LocalBalancedBilinear M N L n U) (i p j d : ℤ)
    (hd : i + p + j + n = d) (X : Cᵒᵖ) (x : (M.complex.X i).val.obj X)
    (a : (A.complex.X p).val.obj X) (y : (N.complex.X j).val.obj X) :
    balZApp α (i + p) j d (by omega) X ((M.mul i p).app X x a) y =
      balZApp α i (p + j) d (by omega) X x ((N.leftMul p j).app X a y) :=
  zApp_ext fun Y k g => by
    rw [zApp_balZApp, zApp_balZApp, (M.mul i p).restr_bil k x a,
      (N.leftMul p j).restr_bil k a y]
    exact α.balanced i p j d hd (Over.mk g) _ _ _

omit [J.WEqualsLocallyBijective AddCommGrpCat.{max u v}]
  [HasWeakSheafify J AddCommGrpCat.{max u v}] in
/-- **The values of a local balanced bilinear family are `B`-linear in the second variable**:
`y b` gives the slice family of `y` acted on by `b`. -/
theorem balZApp_rightMul (α : LocalBalancedBilinear M N L n U) (i j p d : ℤ)
    (hd : i + j + n = d) (W : Cᵒᵖ) (x : (M.complex.X i).val.obj W)
    (y : (N.complex.X j).val.obj W) (b : (B.complex.X p).val.obj W) :
    balZApp α i (j + p) (d + p) (by omega) W x ((N.rightMul j p).app W y b) =
      (sliceFamilyBil (L.mul d p) U).app W (balZApp α i j d hd W x y) b :=
  zApp_ext fun Y k g => by
    rw [zApp_sliceFamilyBil, zApp_balZApp, zApp_balZApp, (N.rightMul j p).restr_bil k y b]
    exact α.map_rightMul i j p d hd (Over.mk g) _ _ _

/-- The balanced bilinear family of slice families attached to a local balanced bilinear
family. -/
noncomputable def balZ (α : LocalBalancedBilinear M N L n U) (m d : ℤ) (hd : m + n = d) :
    Balanced (gP M) N.toGradedBimodule.toLeftGradedModule
      (sliceFamily (L.complex.X d).val U) m where
  app p := balZBil α p.1.1 p.1.2 d (by have := p.2; omega)
  balanced i X x a y :=
    balZApp_balanced α i.1.1 i.1.2.1 i.1.2.2 d (by have := i.2; omega) X x a y

/-- Restriction of presheaves of modules to the slice site over `U`. -/
noncomputable abbrev sliceRestrict (U : C) :
    PresheafOfModules.{max u v} (toRingCat J Osharp).obj ⥤
      PresheafOfModules.{max u v} ((toRingCat J Osharp).over U).obj :=
  Stacks.SheafOfModules.SliceSheafification.presheafOverFunctor.{max u v} (toRingCat J Osharp) U

/-- Evaluation of a slice family at the identity: the morphism of presheaves of modules on the
slice site over `U` from the restriction of the presheaf of slice families of `Lp` to the
restriction of `Lp`. -/
noncomputable def evSlice (Lp : SheafOfModules.{max u v} (toRingCat J Osharp)) (U : C) :
    (sliceRestrict U).obj (sliceFamily Lp.val U) ⟶ (sliceRestrict U).obj Lp.val where
  app V := ModuleCat.ofHom (X := ((sliceRestrict U).obj (sliceFamily Lp.val U)).obj V)
      (Y := ((sliceRestrict U).obj Lp.val).obj V)
    { toFun := fun z => zApp z (𝟙 (Opposite.op V.unop.left)) V.unop.hom
      map_add' := fun z z' => zApp_add z z' _ _
      map_smul' := fun r z => zApp_id_smul (L := Lp.val) (U := U)
        (W := Opposite.op V.unop.left) r z V.unop.hom }
  naturality {V V'} f := by
    refine ModuleCat.hom_ext (LinearMap.ext fun z => ?_)
    change zApp (L := Lp.val) (U := U) z (f.unop.left.op ≫ 𝟙 _) V'.unop.hom =
      Stacks.restr Lp.val f.unop.left.op (zApp (L := Lp.val) (U := U) z (𝟙 _) V.unop.hom)
    refine Eq.trans ?_ (zApp_naturality (L := Lp.val) (U := U)
      (W := Opposite.op V.unop.left) z (𝟙 (Opposite.op V.unop.left)) V.unop.hom
      f.unop.left.op).symm
    rw [Category.comp_id, Category.id_comp]
    exact congrArg (zApp (L := Lp.val) (U := U) z f.unop.left.op) (Over.w f.unop).symm

/-- The sheafification unit of degree `m` of the presheaf-level tensor product, restricted to
the slice site over `U`. -/
noncomputable abbrev sliceUnit (m : ℤ) (U : C) :
    (sliceRestrict U).obj (gradedTensorPre (gP M) N.toGradedBimodule.toLeftGradedModule m) ⟶
      (sliceRestrict U).obj
        (gradedTensor (gP M) N.toGradedBimodule.toLeftGradedModule m).val :=
  (sliceRestrict U).map
    (gradedTensorUnit (gP M) N.toGradedBimodule.toLeftGradedModule m)

/-- The sheafification unit restricted to the slice site over `U` is locally surjective. -/
instance isLocallySurjective_sliceUnit (m : ℤ) (U : C) :
    PresheafOfModules.IsLocallySurjective (J.over U) (sliceUnit (M := M) (N := N) m U) := by
  have h : Presheaf.IsLocallySurjective (J.over U) (Functor.whiskerLeft (Over.forget U).op
      (CategoryTheory.toSheafify J
        (gradedTensorPre (gP M) N.toGradedBimodule.toLeftGradedModule m).presheaf)) :=
    Presheaf.isLocallySurjective_whisker (J.over U) J (Over.forget U) _
  exact h

/-- The sheafification unit restricted to the slice site over `U` is locally injective. -/
instance isLocallyInjective_sliceUnit (m : ℤ) (U : C) :
    PresheafOfModules.IsLocallyInjective (J.over U) (sliceUnit (M := M) (N := N) m U) := by
  have h : Presheaf.IsLocallyInjective (J.over U) (Functor.whiskerLeft (Over.forget U).op
      (CategoryTheory.toSheafify J
        (gradedTensorPre (gP M) N.toGradedBimodule.toLeftGradedModule m).presheaf)) :=
    Presheaf.isLocallyInjective_whisker (J.over U) J (Over.forget U) _
  exact h

/-- The morphism of presheaves of modules out of degree `m` of the presheaf-level tensor
product into the slice families of `L` in degree `d`, descended from a local balanced bilinear
family. -/
noncomputable def descZ (α : LocalBalancedBilinear M N L n U) (m d : ℤ) (hd : m + n = d) :
    gradedTensorPre (gP M) N.toGradedBimodule.toLeftGradedModule m ⟶
      sliceFamily (L.complex.X d).val U :=
  (balZ α m d hd).descPre

omit [J.WEqualsLocallyBijective AddCommGrpCat.{max u v}]
  [HasWeakSheafify J AddCommGrpCat.{max u v}] in
/-- The descent `descZ α m d hd` sends the presheaf-level pure tensor `x ⊗ y` at the index `p`
to the slice family `balZApp α p.1.1 p.1.2 d _ X x y`. -/
theorem descZ_tmulPre (α : LocalBalancedBilinear M N L n U) (m d : ℤ) (hd : m + n = d)
    (p : TensorIndex m) (X : Cᵒᵖ) (x : ((gP M).piece p.1.1).val.obj X)
    (y : (N.toGradedBimodule.toLeftGradedModule.piece p.1.2).val.obj X) :
    PresheafOfModules.Hom.app (descZ α m d hd) X
        (tmulPre (gP M) N.toGradedBimodule m p X x y) =
      balZApp α p.1.1 p.1.2 d (by have := p.2; omega) X x y :=
  (PresheafOfModules.hom_congr_apply (balZ α m d hd).gradedTensorπ_descPre X _).trans
    ((balZ α m d hd).tensorSumDesc_tmul p X x y)

omit [J.WEqualsLocallyBijective AddCommGrpCat.{max u v}]
  [HasWeakSheafify J AddCommGrpCat.{max u v}] in
/-- The component at `k : X ⟶ Y` and `g : Y ⟶ U` of the descent of the presheaf-level pure
tensor `x ⊗ y` is the value of `α` at `g` on the restrictions of `x` and `y` along `k`. -/
theorem zApp_descZ_tmulPre (α : LocalBalancedBilinear M N L n U) (m d : ℤ) (hd : m + n = d)
    (p : TensorIndex m) (X : Cᵒᵖ) (x : ((gP M).piece p.1.1).val.obj X)
    (y : (N.toGradedBimodule.toLeftGradedModule.piece p.1.2).val.obj X) {Y : Cᵒᵖ} (k : X ⟶ Y)
    (g : Y.unop ⟶ U) :
    zApp (PresheafOfModules.Hom.app (descZ α m d hd) X
        (tmulPre (gP M) N.toGradedBimodule m p X x y)) k g =
      α.app p.1.1 p.1.2 d (by have := p.2; omega) (Over.mk g)
        (Stacks.restr (M.complex.X p.1.1).val k x)
        (Stacks.restr (N.complex.X p.1.2).val k y) :=
  Eq.trans (congrArg (fun z => zApp z k g) (descZ_tmulPre α m d hd p X x y))
    (zApp_balZApp α p.1.1 p.1.2 d (by have := p.2; omega) X x y k g)

/-- The morphism of presheaves of modules on the slice site over `U` out of the restriction of
degree `m` of the presheaf-level tensor product into the restriction of `L` in degree `d`. -/
noncomputable def descSliceRaw (α : LocalBalancedBilinear M N L n U) (m d : ℤ)
    (hd : m + n = d) :
    (sliceRestrict U).obj (gradedTensorPre (gP M) N.toGradedBimodule.toLeftGradedModule m) ⟶
      (sliceRestrict U).obj (L.complex.X d).val :=
  (sliceRestrict U).map (descZ α m d hd) ≫ evSlice (L.complex.X d) U

/-- **The descent of a local balanced bilinear family over the slice site at `U`**: the
morphism out of degree `m` of `M ⊗_A N` restricted to the slice site, adjoint to the morphism
into the slice families. -/
noncomputable def descSlice (α : LocalBalancedBilinear M N L n U) (m d : ℤ) (hd : m + n = d) :
    (sliceRestrict U).obj (gradedTensor (gP M) N.toGradedBimodule.toLeftGradedModule m).val ⟶
      (sliceRestrict U).obj (L.complex.X d).val :=
  (PresheafOfModules.homEquivOfIsLocallyBijective (f := sliceUnit (M := M) (N := N) m U)
    ((L.complex.X d).over U).isSheaf).symm (descSliceRaw α m d hd)

/-- The descent over the slice site, on a local section coming from the presheaf level. -/
theorem descSlice_unit (α : LocalBalancedBilinear M N L n U) (m d : ℤ) (hd : m + n = d)
    (V : Over U) (s : (gradedTensorPre (gP M) N.toGradedBimodule.toLeftGradedModule m).obj
      (Opposite.op V.left)) :
    PresheafOfModules.Hom.app (descSlice α m d hd) (Opposite.op V)
        (PresheafOfModules.Hom.app
          (gradedTensorUnit (gP M) N.toGradedBimodule.toLeftGradedModule m)
          (Opposite.op V.left) s) =
      zApp (PresheafOfModules.Hom.app (descZ α m d hd) (Opposite.op V.left) s)
        (𝟙 (Opposite.op V.left)) V.hom :=
  PresheafOfModules.hom_congr_apply
    ((PresheafOfModules.homEquivOfIsLocallyBijective (f := sliceUnit (M := M) (N := N) m U)
      ((L.complex.X d).over U).isSheaf).apply_symm_apply (descSliceRaw α m d hd))
    (Opposite.op V) s

/-- **The descent over the slice site, on a local section `x ⊗ y`**: it is the given balanced
bilinear family. -/
theorem descSlice_tmul (α : LocalBalancedBilinear M N L n U) (m d : ℤ) (hd : m + n = d)
    (p : TensorIndex m) (V : Over U)
    (x : (M.complex.X p.1.1).val.obj (Opposite.op V.left))
    (y : (N.complex.X p.1.2).val.obj (Opposite.op V.left)) :
    PresheafOfModules.Hom.app (descSlice α m d hd) (Opposite.op V)
        (tmul (gP M) N.toGradedBimodule.toLeftGradedModule m p (Opposite.op V.left) x y) =
      α.app p.1.1 p.1.2 d (by have := p.2; omega) V x y := by
  refine Eq.trans (descSlice_unit α m d hd V
    (tmulPre (gP M) N.toGradedBimodule m p (Opposite.op V.left) x y)) ?_
  refine Eq.trans (zApp_descZ_tmulPre α m d hd p (Opposite.op V.left) x y
    (𝟙 (Opposite.op V.left)) V.hom) ?_
  rw [Stacks.restr_id, Stacks.restr_id]
  rfl

/-- A bilinear map of presheaves of modules, restricted to the slice site over `U`. -/
def bilOver {P₁ P₂ P₃ : PresheafOfModules.{max u v} (toRingCat J Osharp).obj}
    (β : Stacks.BilinearMap P₁ P₂ P₃) (U : C) :
    Stacks.BilinearMap ((sliceRestrict U).obj P₁) ((sliceRestrict U).obj P₂)
      ((sliceRestrict U).obj P₃) where
  app V := β.app ((Over.forget U).op.obj V)
  map_smul_left V := β.map_smul_left ((Over.forget U).op.obj V)
  map_smul_right V := β.map_smul_right ((Over.forget U).op.obj V)
  naturality f := β.naturality ((Over.forget U).op.map f)

omit [J.WEqualsLocallyBijective AddCommGrpCat.{max u v}]
  [HasWeakSheafify J AddCommGrpCat.{max u v}] in
/-- **The descent into the slice families is `B`-linear** at the presheaf level: acting by `b`
before descending is acting by `b` afterwards. -/
theorem actPre_comp_descZ (α : LocalBalancedBilinear M N L n U) (i j p : ℤ)
    (hj : i + n = j) :
    actPre (gP M) N.toGradedBimodule i p (i + p) rfl ≫
        bilinHomMap (B.complex.X p).val (descZ α (i + p) (j + p) (by omega)) =
      ofBilinHom ((sliceFamilyBil (L.mul j p) U).compLeft (descZ α i j hj)) := by
  refine (cancel_epi (gradedTensorπ (gP M) N.toGradedBimodule.toLeftGradedModule i)).mp
    (Limits.Sigma.hom_ext _ _ fun q => ?_)
  refine PresheafOfModules.tensorObj_hom_ext fun X x y => ?_
  refine hApp_ext fun W f b => ?_
  change PresheafOfModules.Hom.app (descZ α (i + p) (j + p) (by omega)) W
      (hApp (PresheafOfModules.Hom.app (actPre (gP M) N.toGradedBimodule i p (i + p) rfl) X
        (tmulPre (gP M) N.toGradedBimodule i q X x y)) f b) =
    (sliceFamilyBil (L.mul j p) U).app W (PresheafOfModules.Hom.app (descZ α i j hj) W
      (Stacks.restr (gradedTensorPre (gP M) N.toGradedBimodule.toLeftGradedModule i) f
        (tmulPre (gP M) N.toGradedBimodule i q X x y))) b
  rw [actPre_tmulPre, tmulPre_restr, descZ_tmulPre, descZ_tmulPre]
  exact balZApp_rightMul α q.1.1 q.1.2 p j (by have := q.2; omega) W
    (Stacks.restr (M.complex.X q.1.1).val f x) (Stacks.restr (N.complex.X q.1.2).val f y) b

omit [J.WEqualsLocallyBijective AddCommGrpCat.{max u v}]
  [HasWeakSheafify J AddCommGrpCat.{max u v}] in
/-- The descent into the slice families is `B`-linear, read on local sections. -/
theorem descZ_actPre_apply (α : LocalBalancedBilinear M N L n U) (i j p : ℤ) (hj : i + n = j)
    (X : Cᵒᵖ)
    (z : (gradedTensorPre (gP M) N.toGradedBimodule.toLeftGradedModule i).obj X)
    (b : (B.complex.X p).val.obj X) :
    PresheafOfModules.Hom.app (descZ α (i + p) (j + p) (by omega)) X
        (hApp (PresheafOfModules.Hom.app
          (actPre (gP M) N.toGradedBimodule i p (i + p) rfl) X z) (𝟙 X) b) =
      (sliceFamilyBil (L.mul j p) U).app X
        (PresheafOfModules.Hom.app (descZ α i j hj) X z) b := by
  refine Eq.trans (congrArg (fun w => hApp w (𝟙 X) b)
    (PresheafOfModules.hom_congr_apply (actPre_comp_descZ α i j p hj) X z)) ?_
  exact congrArg (fun w => (sliceFamilyBil (L.mul j p) U).app X
      (PresheafOfModules.Hom.app (descZ α i j hj) X w) b)
    (Stacks.restr_id (gradedTensorPre (gP M) N.toGradedBimodule.toLeftGradedModule i) z)

/-- **The descent over the slice site is `B`-linear**: it sends `s b` to `(descent of s) b`. -/
theorem descSlice_smul (α : LocalBalancedBilinear M N L n U) (i j p : ℤ) (hj : i + n = j)
    (V : Over U)
    (s : ((dgTensorRight M N).complex.X i).val.obj (Opposite.op V.left))
    (b : (B.complex.X p).val.obj (Opposite.op V.left)) :
    PresheafOfModules.Hom.app (descSlice α (i + p) (j + p) (by omega)) (Opposite.op V)
        (((dgTensorRight M N).mul i p).app (Opposite.op V.left) s b) =
      (L.mul j p).app (Opposite.op V.left)
        (PresheafOfModules.Hom.app (descSlice α i j hj) (Opposite.op V) s) b := by
  refine Stacks.BilinearMap.app_eq_of_isLocallySurjective
    ((L.complex.X (j + p)).over U).isSheaf.isSeparated (sliceUnit (M := M) (N := N) i U)
    ((bilOver ((dgTensorRight M N).mul i p) U).postcomp
      (descSlice α (i + p) (j + p) (by omega)))
    ((bilOver (L.mul j p) U).compLeft (descSlice α i j hj)) ?_ (Opposite.op V) s b
  intro W z b'
  change PresheafOfModules.Hom.app (descSlice α (i + p) (j + p) (by omega))
      (Opposite.op W.unop)
      ((gradedTensorRight (gP M) N.toGradedBimodule).smul i p (Opposite.op W.unop.left)
        (PresheafOfModules.Hom.app
          (gradedTensorUnit (gP M) N.toGradedBimodule.toLeftGradedModule i)
          (Opposite.op W.unop.left) z) b') =
    (L.mul j p).app (Opposite.op W.unop.left)
      (PresheafOfModules.Hom.app (descSlice α i j hj) (Opposite.op W.unop)
        (PresheafOfModules.Hom.app
          (gradedTensorUnit (gP M) N.toGradedBimodule.toLeftGradedModule i)
          (Opposite.op W.unop.left) z)) b'
  rw [gradedTensorRight_smul_unit M N i p (Opposite.op W.unop.left) z b',
    descSlice_unit α i j hj W.unop z,
    descSlice_unit α (i + p) (j + p) (by omega) W.unop _,
    descZ_actPre_apply α i j p hj (Opposite.op W.unop.left) z b',
    zApp_id_sliceFamilyBil (L.mul j p) U
      (PresheafOfModules.Hom.app (descZ α i j hj) (Opposite.op W.unop.left) z) b'
      W.unop.hom]

/-! ### Composition with the multiplication map, and the bijection -/

/-- The multiplication map of `M ⊗_A N` is additive in the first variable. -/
theorem dgTmul_add_left (i j : ℤ) (X : Cᵒᵖ) (x x' : (M.complex.X i).val.obj X)
    (y : (N.complex.X j).val.obj X) :
    dgTmul M N i j X (x + x') y = dgTmul M N i j X x y + dgTmul M N i j X x' y := by
  rw [map_add]
  rfl

/-- The value of the composition of a local homomorphism with the multiplication map. -/
noncomputable def compTmulApp (f : LocalHom (dgTensorRight M N) L n U) (i j k : ℤ)
    (hijk : i + j + n = k) (V : Over U)
    (x : (M.complex.X i).val.obj (Opposite.op V.left))
    (y : (N.complex.X j).val.obj (Opposite.op V.left)) :
    (L.complex.X k).val.obj (Opposite.op V.left) :=
  f.app (i + j) k hijk V (dgTmul M N i j (Opposite.op V.left) x y)

/-- The composition of a local homomorphism with the multiplication map is additive in the first
variable. -/
theorem compTmulApp_add_left (f : LocalHom (dgTensorRight M N) L n U) (i j k : ℤ)
    (hijk : i + j + n = k) (V : Over U)
    (x x' : (M.complex.X i).val.obj (Opposite.op V.left))
    (y : (N.complex.X j).val.obj (Opposite.op V.left)) :
    compTmulApp f i j k hijk V (x + x') y =
      compTmulApp f i j k hijk V x y + compTmulApp f i j k hijk V x' y :=
  Eq.trans (congrArg (f.app (i + j) k hijk V)
      (dgTmul_add_left i j (Opposite.op V.left) x x' y))
    (map_add (f.app (i + j) k hijk V) _ _)

/-- The composition of a local homomorphism with the multiplication map is additive in the
second variable. -/
theorem compTmulApp_add_right (f : LocalHom (dgTensorRight M N) L n U) (i j k : ℤ)
    (hijk : i + j + n = k) (V : Over U)
    (x : (M.complex.X i).val.obj (Opposite.op V.left))
    (y y' : (N.complex.X j).val.obj (Opposite.op V.left)) :
    compTmulApp f i j k hijk V x (y + y') =
      compTmulApp f i j k hijk V x y + compTmulApp f i j k hijk V x y' :=
  Eq.trans (congrArg (f.app (i + j) k hijk V)
      (map_add (dgTmul M N i j (Opposite.op V.left) x) y y'))
    (map_add (f.app (i + j) k hijk V) _ _)

/-- The composition of a local homomorphism with the multiplication map is linear over the sheaf
of rings in the first variable. -/
theorem compTmulApp_smul_left (f : LocalHom (dgTensorRight M N) L n U) (i j k : ℤ)
    (hijk : i + j + n = k) (V : Over U) (r : (toRingCat J Osharp).obj.obj (Opposite.op V.left))
    (x : (M.complex.X i).val.obj (Opposite.op V.left))
    (y : (N.complex.X j).val.obj (Opposite.op V.left)) :
    compTmulApp f i j k hijk V (r • x) y = r • compTmulApp f i j k hijk V x y :=
  Eq.trans (congrArg (f.app (i + j) k hijk V)
      (dgTensorRight_tmul_smul_left M N i j (Opposite.op V.left) r x y))
    (f.map_smul (i + j) k hijk V r _)

/-- The composition of a local homomorphism with the multiplication map is linear over the sheaf
of rings in the second variable. -/
theorem compTmulApp_smul_right (f : LocalHom (dgTensorRight M N) L n U) (i j k : ℤ)
    (hijk : i + j + n = k) (V : Over U) (r : (toRingCat J Osharp).obj.obj (Opposite.op V.left))
    (x : (M.complex.X i).val.obj (Opposite.op V.left))
    (y : (N.complex.X j).val.obj (Opposite.op V.left)) :
    compTmulApp f i j k hijk V x (r • y) = r • compTmulApp f i j k hijk V x y :=
  Eq.trans (congrArg (f.app (i + j) k hijk V)
      (dgTensorRight_tmul_smul_right M N i j (Opposite.op V.left) r x y))
    (f.map_smul (i + j) k hijk V r _)

/-- The composition of a local homomorphism with the multiplication map commutes with
restriction along a morphism `W ⟶ V` of the slice category over `U`. -/
theorem compTmulApp_naturality (f : LocalHom (dgTensorRight M N) L n U) (i j k : ℤ)
    (hijk : i + j + n = k) {V W : Over U} (g : W ⟶ V)
    (x : (M.complex.X i).val.obj (Opposite.op V.left))
    (y : (N.complex.X j).val.obj (Opposite.op V.left)) :
    (L.complex.X k).val.map g.left.op (compTmulApp f i j k hijk V x y) =
      compTmulApp f i j k hijk W ((M.complex.X i).val.map g.left.op x)
        ((N.complex.X j).val.map g.left.op y) :=
  Eq.trans (f.naturality (i + j) k hijk g (dgTmul M N i j (Opposite.op V.left) x y))
    (congrArg (f.app (i + j) k hijk W)
      (dgTensorRight_tmul_naturality M N i j g.left.op x y))

/-- **Composition of a degree-`n` local homomorphism out of `M ⊗_A N` with the multiplication
map**: the forward direction of the universal property. -/
noncomputable def compTmul (f : LocalHom (dgTensorRight M N) L n U) :
    LocalBalancedBilinear M N L n U where
  app i j k hijk V := AddMonoidHom.mk'
    (fun x => AddMonoidHom.mk' (fun y => compTmulApp f i j k hijk V x y)
      (fun y y' => compTmulApp_add_right f i j k hijk V x y y'))
    (fun x x' => AddMonoidHom.ext fun y => compTmulApp_add_left f i j k hijk V x x' y)
  map_smul_left i j k hijk V r x y := compTmulApp_smul_left f i j k hijk V r x y
  map_smul_right i j k hijk V r x y := compTmulApp_smul_right f i j k hijk V r x y
  naturality i j k hijk {V W} g x y := compTmulApp_naturality f i j k hijk g x y
  balanced i p j k hijk V x a y :=
    LocalGradedHom.app_heq_congr f.toLocalGradedHom (add_assoc i p j) hijk (by omega) V
      (dgTensorRight_tmul_balanced M N i p j (Opposite.op V.left) x a y)
  map_rightMul i j p k hijk V x y b :=
    Eq.trans (LocalGradedHom.app_heq_congr f.toLocalGradedHom (add_assoc i j p).symm
        (by omega) (by omega) V
        (dgTensorRight_tmul_rightMul M N i j p (Opposite.op V.left) x y b).symm)
      (f.isLinear (i + j) k hijk p V (dgTmul M N i j (Opposite.op V.left) x y) b)

/-- The balanced bilinear family `compTmul f` sends `(x, y)` to `f (x ⊗ y)`. -/
@[simp]
theorem compTmul_app (f : LocalHom (dgTensorRight M N) L n U) (i j k : ℤ)
    (hijk : i + j + n = k) (V : Over U) (x : (M.complex.X i).val.obj (Opposite.op V.left))
    (y : (N.complex.X j).val.obj (Opposite.op V.left)) :
    (compTmul f).app i j k hijk V x y =
      f.app (i + j) k hijk V (dgTmul M N i j (Opposite.op V.left) x y) := rfl

/-- The descent over the slice site, read as a map on sections over an object of the slice
site. -/
noncomputable def descSliceApp (α : LocalBalancedBilinear M N L n U) (m d : ℤ) (hd : m + n = d)
    (V : Over U) :
    ((dgTensorRight M N).complex.X m).val.obj (Opposite.op V.left) ⟶
      (L.complex.X d).val.obj (Opposite.op V.left) :=
  PresheafOfModules.Hom.app (descSlice α m d hd) (Opposite.op V)

/-- **The degree-`n` local homomorphism out of `M ⊗_A N` descended from a local balanced
bilinear family.** -/
noncomputable def descLocalHom (α : LocalBalancedBilinear M N L n U) :
    LocalHom (dgTensorRight M N) L n U where
  app i j hij V := (ConcreteCategory.hom (descSliceApp α i j hij V)).toAddMonoidHom
  map_smul i j hij V r x :=
    map_smul (ConcreteCategory.hom (descSliceApp α i j hij V)) r x
  naturality i j hij {_V _W} g x :=
    (PresheafOfModules.naturality_apply (descSlice α i j hij) g.op x).symm
  isLinear i j hij p V x b := descSlice_smul α i j p hij V x b

/-- The local homomorphism `descLocalHom α` acts on sections over `V` as the descent
`descSlice α i j hij` evaluated at `V`. -/
@[simp]
theorem descLocalHom_app (α : LocalBalancedBilinear M N L n U) (i j : ℤ) (hij : i + n = j)
    (V : Over U) (x : ((dgTensorRight M N).complex.X i).val.obj (Opposite.op V.left)) :
    (descLocalHom α).app i j hij V x =
      PresheafOfModules.Hom.app (descSlice α i j hij) (Opposite.op V) x := rfl

/-- **The universal property of `M ⊗_A N`, descent**: the descent of a local balanced bilinear
family composes with the multiplication map to give that family back. -/
theorem compTmul_descLocalHom (α : LocalBalancedBilinear M N L n U) :
    compTmul (descLocalHom α) = α :=
  LocalBalancedBilinear.ext fun i j k hijk V x y =>
    descSlice_tmul α (i + j) k hijk (tensorIndexPair i j) V x y

/-- The slice family of values of a local homomorphism at a local section of the
presheaf-level tensor product. -/
noncomputable def psiZApp (f : LocalHom (dgTensorRight M N) L n U) (i j : ℤ) (hij : i + n = j)
    (W : Cᵒᵖ) (w : (gradedTensorPre (gP M) N.toGradedBimodule.toLeftGradedModule i).obj W) :
    (sliceFamily (L.complex.X j).val U).obj W :=
  zMk (fun X k g => f.app i j hij (Over.mk g)
      (PresheafOfModules.Hom.app
        (gradedTensorUnit (gP M) N.toGradedBimodule.toLeftGradedModule i) X
        (Stacks.restr (gradedTensorPre (gP M) N.toGradedBimodule.toLeftGradedModule i) k w)))
    (fun X Y k g h => by
      refine Eq.trans (f.naturality i j hij (V := Over.mk g) (W := Over.mk (h.unop ≫ g))
        (Over.homMk h.unop) _) ?_
      refine congrArg (f.app i j hij (Over.mk (h.unop ≫ g))) ?_
      refine Eq.trans (Stacks.restr_app
        (gradedTensorUnit (gP M) N.toGradedBimodule.toLeftGradedModule i) h _).symm ?_
      exact congrArg (PresheafOfModules.Hom.app
        (gradedTensorUnit (gP M) N.toGradedBimodule.toLeftGradedModule i) Y)
        (Stacks.restr_restr (gradedTensorPre (gP M) N.toGradedBimodule.toLeftGradedModule i)
          k h w))

/-- The component of `psiZApp f i j hij W w` at `k : W ⟶ X` and `g : X ⟶ U` is the value of `f`
at `g` on the image under the sheafification unit of the restriction of `w` along `k`. -/
@[simp]
theorem zApp_psiZApp (f : LocalHom (dgTensorRight M N) L n U) (i j : ℤ) (hij : i + n = j)
    (W : Cᵒᵖ) (w : (gradedTensorPre (gP M) N.toGradedBimodule.toLeftGradedModule i).obj W)
    {X : Cᵒᵖ} (k : W ⟶ X) (g : X.unop ⟶ U) :
    zApp (psiZApp f i j hij W w) k g =
      f.app i j hij (Over.mk g)
        (PresheafOfModules.Hom.app
          (gradedTensorUnit (gP M) N.toGradedBimodule.toLeftGradedModule i) X
          (Stacks.restr (gradedTensorPre (gP M)
            N.toGradedBimodule.toLeftGradedModule i) k w)) := rfl

/-- The slice family `psiZApp f i j hij W w` is additive in `w`. -/
theorem psiZApp_add (f : LocalHom (dgTensorRight M N) L n U) (i j : ℤ) (hij : i + n = j)
    (W : Cᵒᵖ)
    (w w' : (gradedTensorPre (gP M) N.toGradedBimodule.toLeftGradedModule i).obj W) :
    psiZApp f i j hij W (w + w') = psiZApp f i j hij W w + psiZApp f i j hij W w' :=
  zApp_ext fun X k g => by
    simp only [zApp_add, zApp_psiZApp, Stacks.restr_add, map_add]
    exact map_add _ _ _

/-- The slice family `psiZApp f i j hij W w` is linear over the sheaf of rings in `w`. -/
theorem psiZApp_smul (f : LocalHom (dgTensorRight M N) L n U) (i j : ℤ) (hij : i + n = j)
    (W : Cᵒᵖ) (r : (toRingCat J Osharp).obj.obj W)
    (w : (gradedTensorPre (gP M) N.toGradedBimodule.toLeftGradedModule i).obj W) :
    psiZApp f i j hij W (r • w) = r • psiZApp f i j hij W w :=
  zApp_ext fun X k g => by
    rw [zApp_smul, zApp_psiZApp, zApp_psiZApp, Stacks.restr_smul, map_smul]
    exact f.map_smul i j hij (Over.mk g) _ _

/-- The slice family `psiZApp f i j hij W w` commutes with restriction along `W ⟶ W'`. -/
theorem psiZApp_restr (f : LocalHom (dgTensorRight M N) L n U) (i j : ℤ) (hij : i + n = j)
    {W W' : Cᵒᵖ} (h : W ⟶ W')
    (w : (gradedTensorPre (gP M) N.toGradedBimodule.toLeftGradedModule i).obj W) :
    psiZApp f i j hij W' (Stacks.restr (gradedTensorPre (gP M)
        N.toGradedBimodule.toLeftGradedModule i) h w) =
      Stacks.restr (sliceFamily (L.complex.X j).val U) h (psiZApp f i j hij W w) :=
  zApp_ext fun X k g => by
    rw [zApp_restr, zApp_psiZApp, zApp_psiZApp,
      Stacks.restr_restr (gradedTensorPre (gP M)
        N.toGradedBimodule.toLeftGradedModule i) h k w]

/-- A degree-`n` local homomorphism out of `M ⊗_A N`, read as a morphism of presheaves of
modules into the slice families of `L`. -/
noncomputable def psiZ (f : LocalHom (dgTensorRight M N) L n U) (i j : ℤ) (hij : i + n = j) :
    gradedTensorPre (gP M) N.toGradedBimodule.toLeftGradedModule i ⟶
      sliceFamily (L.complex.X j).val U where
  app W := ModuleCat.ofHom
    (X := (gradedTensorPre (gP M) N.toGradedBimodule.toLeftGradedModule i).obj W)
    (Y := (sliceFamily (L.complex.X j).val U).obj W)
    { toFun := psiZApp f i j hij W
      map_add' := psiZApp_add f i j hij W
      map_smul' := psiZApp_smul f i j hij W }
  naturality {_W _W'} h :=
    ModuleCat.hom_ext (LinearMap.ext fun w => psiZApp_restr f i j hij h w)

/-- **A local homomorphism out of `M ⊗_A N` is the descent of its composition with the
multiplication map**, at the level of the slice families. -/
theorem descZ_compTmul (f : LocalHom (dgTensorRight M N) L n U) (i j : ℤ) (hij : i + n = j) :
    descZ (compTmul f) i j hij = psiZ f i j hij := by
  refine (cancel_epi (gradedTensorπ (gP M) N.toGradedBimodule.toLeftGradedModule i)).mp
    (Limits.Sigma.hom_ext _ _ fun q => ?_)
  refine PresheafOfModules.tensorObj_hom_ext fun X x y => ?_
  change PresheafOfModules.Hom.app (descZ (compTmul f) i j hij) X
      (tmulPre (gP M) N.toGradedBimodule i q X x y) =
    psiZApp f i j hij X (tmulPre (gP M) N.toGradedBimodule i q X x y)
  refine zApp_ext fun Y k g => ?_
  refine Eq.trans (zApp_descZ_tmulPre (compTmul f) i j hij q X x y k g) ?_
  refine Eq.trans ?_ (zApp_psiZApp f i j hij X
    (tmulPre (gP M) N.toGradedBimodule i q X x y) k g).symm
  refine Eq.trans (LocalGradedHom.app_heq_congr f.toLocalGradedHom q.2
    (by have := q.2; omega) hij (Over.mk g)
    (tmul_heq (gP M) N.toGradedBimodule.toLeftGradedModule
      (p := tensorIndexPair q.1.1 q.1.2) (p' := q) q.2 rfl Y HEq.rfl HEq.rfl)) ?_
  exact congrArg (f.app i j hij (Over.mk g))
    (congrArg (PresheafOfModules.Hom.app
        (gradedTensorUnit (gP M) N.toGradedBimodule.toLeftGradedModule i) Y)
      (tmulPre_restr (gP M) N.toGradedBimodule i q k x y)).symm

/-- **The universal property of `M ⊗_A N`, uniqueness**: a degree-`n` local homomorphism out of
`M ⊗_A N` is the descent of its composition with the multiplication map. -/
theorem descLocalHom_compTmul (f : LocalHom (dgTensorRight M N) L n U) :
    descLocalHom (compTmul f) = f :=
  LocalHom.ext fun i j hij V x => by
    refine Stacks.eq_of_forall_lift ((L.complex.X j).over U).isSheaf.isSeparated
      (sliceUnit (M := M) (N := N) i U) x _ _ ?_
    intro Y h w hw
    have hw' : PresheafOfModules.Hom.app (sliceUnit (M := M) (N := N) i U) Y w =
        Stacks.restr ((sliceRestrict U).obj
          (gradedTensor (gP M) N.toGradedBimodule.toLeftGradedModule i).val) h x := hw
    refine Eq.trans (Stacks.restr_app (descSlice (compTmul f) i j hij) h x).symm ?_
    rw [← hw']
    refine Eq.trans (descSlice_unit (compTmul f) i j hij Y.unop w) ?_
    refine Eq.trans (congrArg (fun z => zApp z (𝟙 (Opposite.op Y.unop.left)) Y.unop.hom)
      (PresheafOfModules.hom_congr_apply (descZ_compTmul f i j hij)
        (Opposite.op Y.unop.left) w)) ?_
    refine Eq.trans (zApp_psiZApp f i j hij (Opposite.op Y.unop.left) w
      (𝟙 (Opposite.op Y.unop.left)) Y.unop.hom) ?_
    refine Eq.trans (congrArg (f.app i j hij (Over.mk Y.unop.hom))
      (congrArg (PresheafOfModules.Hom.app
          (gradedTensorUnit (gP M) N.toGradedBimodule.toLeftGradedModule i)
          (Opposite.op Y.unop.left))
        (Stacks.restr_id (gradedTensorPre (gP M)
          N.toGradedBimodule.toLeftGradedModule i) w))) ?_
    refine Eq.trans (congrArg (f.app i j hij (Over.mk Y.unop.hom)) hw') ?_
    exact (f.naturality i j hij (V := V) (W := Y.unop) h.unop x).symm

end Universal

/-- **The universal property of `M ⊗_A N`**: composing a degree-`n` local homomorphism out of
`M ⊗_A N` with the multiplication map is a bijection onto the `A`-balanced bilinear families of
degree `n`. -/
noncomputable def universalDgTensorRight (L : DifferentialGradedModule.{t, max u v, max u v} B)
    (n : ℤ) (U : C) :
    LocalHom (dgTensorRight M N) L n U ≃ LocalBalancedBilinear M N L n U where
  toFun := compTmul
  invFun := descLocalHom
  left_inv := descLocalHom_compTmul
  right_inv := compTmul_descLocalHom

/-- **`M ⊗_A N` is the tensor product of `M` and `N`**: it satisfies every clause of
`SheafOfModules.IsTensorProduct`, with multiplication map the local section `x ⊗ y`. -/
noncomputable def isTensorProductDgTensorRight :
    IsTensorProduct M N (dgTensorRight M N) :=
  (isTensorProductCoreDgTensorRight M N).toIsTensorProduct (universalDgTensorRight M N)
    (fun _ _ _ f i j k hijk V x y => compTmul_app f i j k hijk V x y)

/-! ### The tensor product functor

The functoriality of `M ⊗_A N` in `M` at the level of complexes is
`SheafOfModules.RelativeTensor.dgTensorFunctor`; what is added here is that it commutes with the
right action of `B`, which makes it a functor to right differential graded `B`-modules. -/

section Functoriality

variable {M' : DifferentialGradedModule.{t, max u v, max u v} A}

omit [J.WEqualsLocallyBijective AddCommGrpCat.{max u v}]
  [HasWeakSheafify J AddCommGrpCat.{max u v}] in
/-- The functoriality of the presheaf-level tensor product, on a local section `x ⊗ y`. -/
theorem mapPreRight_tmulPre (hh : gP M ⟶ gP M') (m : ℤ) (q : TensorIndex m) (X : Cᵒᵖ)
    (x : ((gP M).piece q.1.1).val.obj X)
    (y : (N.toGradedBimodule.toLeftGradedModule.piece q.1.2).val.obj X) :
    PresheafOfModules.Hom.app
        (gradedTensorMapPreRight hh N.toGradedBimodule.toLeftGradedModule m) X
        (tmulPre (gP M) N.toGradedBimodule m q X x y) =
      tmulPre (gP M') N.toGradedBimodule m q X
        (PresheafOfModules.Hom.app (hh.app q.1.1).val X x) y :=
  Eq.trans (PresheafOfModules.hom_congr_apply'
      (gradedTensorπ_gradedTensorMapPreRight hh N.toGradedBimodule.toLeftGradedModule m) X _)
    (congrArg (PresheafOfModules.Hom.app
        (gradedTensorπ (gP M') N.toGradedBimodule.toLeftGradedModule m) X)
      (tensorSumMapRight_tensorSumι_apply hh N.toGradedBimodule.toLeftGradedModule q X x y))

omit [J.WEqualsLocallyBijective AddCommGrpCat.{max u v}]
  [HasWeakSheafify J AddCommGrpCat.{max u v}] in
/-- **The functoriality of the presheaf-level tensor product commutes with the right action of
`B`**. -/
theorem actPre_comp_mapPreRight (hh : gP M ⟶ gP M') (m i : ℤ) :
    actPre.{t, v, u, max u v} (gP M) N.toGradedBimodule m i (m + i) rfl ≫
        bilinHomMap (B.complex.X i).val
          (gradedTensorMapPreRight hh N.toGradedBimodule.toLeftGradedModule (m + i)) =
      gradedTensorMapPreRight hh N.toGradedBimodule.toLeftGradedModule m ≫
        actPre.{t, v, u, max u v} (gP M') N.toGradedBimodule m i (m + i) rfl := by
  refine (cancel_epi (gradedTensorπ (gP M) N.toGradedBimodule.toLeftGradedModule m)).mp
    (Limits.Sigma.hom_ext _ _ fun q => ?_)
  refine PresheafOfModules.tensorObj_hom_ext fun X x y => ?_
  refine hApp_ext fun V f b => ?_
  change PresheafOfModules.Hom.app
      (gradedTensorMapPreRight hh N.toGradedBimodule.toLeftGradedModule (m + i)) V
      (hApp (PresheafOfModules.Hom.app
        (actPre.{t, v, u, max u v} (gP M) N.toGradedBimodule m i (m + i) rfl) X
        (tmulPre (gP M) N.toGradedBimodule m q X x y)) f b) =
    hApp (PresheafOfModules.Hom.app
      (actPre.{t, v, u, max u v} (gP M') N.toGradedBimodule m i (m + i) rfl) X
      (PresheafOfModules.Hom.app
        (gradedTensorMapPreRight hh N.toGradedBimodule.toLeftGradedModule m) X
        (tmulPre (gP M) N.toGradedBimodule m q X x y))) f b
  rw [actPre_tmulPre, mapPreRight_tmulPre, mapPreRight_tmulPre, actPre_tmulPre,
    Stacks.restr_app (hh.app q.1.1).val f x]

/-- The functoriality of the tensor product, on a local section coming from the presheaf
level. -/
theorem gradedTensorMapRight_unit (hh : gP M ⟶ gP M') (m : ℤ) (X : Cᵒᵖ)
    (w : (gradedTensorPre (gP M) N.toGradedBimodule.toLeftGradedModule m).obj X) :
    PresheafOfModules.Hom.app
        (gradedTensorMapRight hh N.toGradedBimodule.toLeftGradedModule m).val X
        (PresheafOfModules.Hom.app
          (gradedTensorUnit (gP M) N.toGradedBimodule.toLeftGradedModule m) X w) =
      PresheafOfModules.Hom.app
        (gradedTensorUnit (gP M') N.toGradedBimodule.toLeftGradedModule m) X
        (PresheafOfModules.Hom.app
          (gradedTensorMapPreRight hh N.toGradedBimodule.toLeftGradedModule m) X w) :=
  PresheafOfModules.unit_naturality_apply (α := 𝟙 (toRingCat J Osharp).obj)
    (φ := gradedTensorMapPreRight hh N.toGradedBimodule.toLeftGradedModule m) X w

/-- **The functoriality of `M ⊗_A N` commutes with the right action of `B`**. -/
theorem gradedTensorMapRight_smul (hh : gP M ⟶ gP M') (m i : ℤ) (X : Cᵒᵖ)
    (s : (gradedTensor (gP M) N.toGradedBimodule.toLeftGradedModule m).val.obj X)
    (b : (B.complex.X i).val.obj X) :
    PresheafOfModules.Hom.app
        (gradedTensorMapRight hh N.toGradedBimodule.toLeftGradedModule (m + i)).val X
        ((gradedTensorRight (gP M) N.toGradedBimodule).smul m i X s b) =
      (gradedTensorRight (gP M') N.toGradedBimodule).smul m i X
        (PresheafOfModules.Hom.app
          (gradedTensorMapRight hh N.toGradedBimodule.toLeftGradedModule m).val X s) b := by
  have hsurj : PresheafOfModules.IsLocallySurjective J
      (gradedTensorUnit (gP M) N.toGradedBimodule.toLeftGradedModule m) :=
    PresheafOfModules.isLocallySurjective_sheafificationAdjunction_unit_app
      (α := 𝟙 (toRingCat J Osharp).obj) _
  refine Stacks.BilinearMap.app_eq_of_isLocallySurjective
    (gradedTensor (gP M') N.toGradedBimodule.toLeftGradedModule (m + i)).isSheaf.isSeparated
    (gradedTensorUnit (gP M) N.toGradedBimodule.toLeftGradedModule m)
    (((gradedTensorRight (gP M) N.toGradedBimodule).smulBil m i).postcomp
      (gradedTensorMapRight hh N.toGradedBimodule.toLeftGradedModule (m + i)).val)
    (((gradedTensorRight (gP M') N.toGradedBimodule).smulBil m i).compLeft
      (gradedTensorMapRight hh N.toGradedBimodule.toLeftGradedModule m).val) ?_ X s b
  intro W z b'
  change PresheafOfModules.Hom.app
      (gradedTensorMapRight hh N.toGradedBimodule.toLeftGradedModule (m + i)).val W
      ((gradedTensorRight (gP M) N.toGradedBimodule).smul m i W
        (PresheafOfModules.Hom.app
          (gradedTensorUnit (gP M) N.toGradedBimodule.toLeftGradedModule m) W z) b') =
    (gradedTensorRight (gP M') N.toGradedBimodule).smul m i W
      (PresheafOfModules.Hom.app
        (gradedTensorMapRight hh N.toGradedBimodule.toLeftGradedModule m).val W
        (PresheafOfModules.Hom.app
          (gradedTensorUnit (gP M) N.toGradedBimodule.toLeftGradedModule m) W z)) b'
  rw [gradedTensorRight_smul_unit M N m i W z b', gradedTensorMapRight_unit,
    gradedTensorMapRight_unit, gradedTensorRight_smul_unit M' N m i W _ b']
  exact congrArg (PresheafOfModules.Hom.app
      (gradedTensorUnit (gP M') N.toGradedBimodule.toLeftGradedModule (m + i)) W)
    (congrArg (fun w => hApp w (𝟙 W) b')
      (PresheafOfModules.hom_congr_apply (actPre_comp_mapPreRight M N hh m i) W z))

/-- **The morphism `M ⊗_A N ⟶ M' ⊗_A N` of right differential graded `B`-modules** induced by a
morphism of right differential graded `A`-modules. -/
noncomputable def dgTensorRightMap (h : M ⟶ M') : dgTensorRight M N ⟶ dgTensorRight M' N where
  toHomologicalComplex := (dgTensorFunctor N.toLeftDifferentialGradedModule).map h
  map_mul m i X x y := gradedTensorMapRight_smul M N (gMap h) m i X x y

/-- In degree `m`, the morphism `M ⊗_A N ⟶ M' ⊗_A N` induced by `h` is the map
`gradedTensorMapRight` of degree `m` induced by `h`. -/
@[simp]
theorem dgTensorRightMap_f (h : M ⟶ M') (m : ℤ) :
    (dgTensorRightMap M N h).toHomologicalComplex.f m =
      gradedTensorMapRight (gMap h) (gN N.toLeftDifferentialGradedModule) m := rfl

end Functoriality

/-- **The tensor product functor `- ⊗_A N`** from right differential graded `A`-modules to
right differential graded `B`-modules. -/
@[stacks 0FRP "the functor - ⊗_A N : Mod(A, d) ⥤ Mod(B, d) for a dg (A, B)-bimodule N"]
noncomputable def dgTensorRightFunctor
    (N : DifferentialGradedBimodule.{t, max u v, max u v} A B) :
    DifferentialGradedModule.{t, max u v, max u v} A ⥤
      DifferentialGradedModule.{t, max u v, max u v} B where
  obj Q := dgTensorRight Q N
  map h := dgTensorRightMap _ N h
  map_id Q := DifferentialGradedModule.Hom.ext fun m => by
    refine Eq.trans (dgTensorRightMap_f Q N (𝟙 Q) m).symm ?_
    change ((dgTensorFunctor N.toLeftDifferentialGradedModule).map (𝟙 Q)).f m = _
    rw [(dgTensorFunctor N.toLeftDifferentialGradedModule).map_id]
    rfl
  map_comp {Q Q' Q''} h h' := DifferentialGradedModule.Hom.ext fun m => by
    refine Eq.trans (dgTensorRightMap_f Q N (h ≫ h') m).symm ?_
    change ((dgTensorFunctor N.toLeftDifferentialGradedModule).map (h ≫ h')).f m = _
    rw [(dgTensorFunctor N.toLeftDifferentialGradedModule).map_comp]
    rfl

/-- **The tensor product with a fixed differential graded `(A, B)`-bimodule `N`**, as a functor
on right differential graded `A`-modules whose values are tensor products. -/
noncomputable def tensorFunctorDataDgTensorRight
    (N : DifferentialGradedBimodule.{t, max u v, max u v} A B) : TensorFunctorData A B N where
  functor := dgTensorRightFunctor N
  isTensorProduct Q := isTensorProductDgTensorRight Q N
  map_spec {_Q _Q'} h i j X x y :=
    gradedTensorMapRight_tmul (gMap h) (gN N.toLeftDifferentialGradedModule) (i + j)
      (tensorIndexPair i j) X x y

end RelativeTensor

end SheafOfModules

end
