module

public import StacksFrontier.Algebra.Category.ModuleCat.Sheaf.GradedExtensionByZero
public import StacksFrontier.Algebra.Category.ModuleCat.Sheaf.GradedRelativeTensor
public import StacksFrontier.CategoryTheory.Sites.Modules.RingedSite
public import StacksCore.Tactic.StacksAttribute

/-!
# Extension by zero and the relative tensor product of graded modules

Let `(C, O)` be a ringed site, let `U` be an object of `C` and let
`j : (Sh(C/U), O_U) ⟶ (Sh(C), O)` be the localization morphism. Let `A` be a sheaf of graded
`O`-algebras and `A_U = j^*A` its restriction to the slice site. For a right graded
`A_U`-module `M` and a left graded `A`-module `N` the source asserts

`j_!M ⊗_A N = j_!(M ⊗_{A_U} N|_U)`

as graded `O`-modules, functorially in `M` and in `N`. This file proves it, in each degree, as
an isomorphism of sheaves of `O`-modules.

## Main definitions

* `SheafOfModules.bilinearOver` reads a bilinear map of sheaves of modules on the slice site,
  and `SheafOfModules.LeftGradedModule.actionBilinear` packages the left action of a left
  graded module as a bilinear map.
* `SheafOfModules.RelativeTensor.Balanced.restrictAlongUnit` restricts a balanced bilinear
  family out of `(j_!M, N)` to one out of `(M, N|_U)`, by evaluating on the local sections
  supplied by the unit of `j_{U!} ⊣ j_U^*`, and
  `SheafOfModules.RelativeTensor.Balanced.extendByZero` is the inverse construction.
* `SheafOfModules.extendTensorHom` and `SheafOfModules.extendTensorInv` are the two comparison
  morphisms between `j_!M ⊗_A N` and `j_!(M ⊗_{A_U} N|_U)` in a fixed degree.

## Main results

* `SheafOfModules.extendTensorIso`: **Tag 0FRB.** In every degree `n`,
  `j_!M ⊗_A N ≅ j_!(M ⊗_{A_U} N|_U)` as sheaves of `O`-modules.
* `SheafOfModules.extendTensorHom_naturality_left` and
  `SheafOfModules.extendTensorHom_naturality_right`: that isomorphism is natural in `M` and in
  `N`, which is the functoriality the source asserts.
* `SheafOfModules.extendTensorHom_tmul_unit`: the isomorphism sends `j_!x ⊗ y` to `j_!(x ⊗ y)`,
  which is what pins it down.

## Implementation notes

**Which objects the statement is about.** `M ⊗_{A_U} N|_U` and `j_!M ⊗_A N` are the relative
tensor products of
`StacksFrontier/Algebra/Category/ModuleCat/Sheaf/GradedRelativeTensor.lean`: degree `n` is the
associated sheaf of the cokernel of the balance map
`⨁_{r + s + t = n} P^r ⊗_O A^s ⊗_O N^t → ⨁_{p + q = n} P^p ⊗_O N^q`, which is the presentation
the source computes with. The two sides live over different sites, `C` and `C/U`; the slice
one is read through the identification `toRingCat (J.over U) (O|_U) = (toRingCat J O)|_U`,
which holds on the nose.

**How the isomorphism is produced.** The source moves `j_!` through the presentation using the
identity `j_!(M_1 ⊗_{O_U} A|_U) = j_!M_1 ⊗_O A` of Tag 0E8I. That identity is in the library
only as an isomorphism of functors obtained from uniqueness of left adjoints, with no formula
on local sections, so it cannot be matched against the balance maps. The route taken here is
the one the source offers as its alternative, "redo the Yoneda argument": both sides are
compared through the balanced bilinear families they co-represent. The universal property of
the relative tensor product — `SheafOfModules.RelativeTensor.Balanced.desc` and
`SheafOfModules.RelativeTensor.gradedTensor_hom_ext` — is in `GradedRelativeTensor.lean`, and
the bijection between the balanced families of the two sides is
`SheafOfModules.RelativeTensor.Balanced.restrictAlongUnit` and `extendByZero` below.

**Why extending a balanced family needs more than the adjunction.** Restricting along the unit
of `j_{U!} ⊣ j_U^*` is immediate; extending is not, because a balanced family out of `j_!M` is
a *bilinear* datum and the unit sections are not all the sections of `j_!M`. The input is
`StacksFrontier/Algebra/Category/ModuleCat/Sheaf/ExtensionByZeroBilinear.lean`, whose
`SheafOfModules.extendBilinear` extends a bilinear map out of `M` to one out of `j_!M` and
whose `extendedBilinear_ext` and `extendedTrilinear_hext` recognise such a map, respectively
such a law, from its values on the unit sections.

**Base and universes.** The ringed site is unbundled as a sheaf of commutative rings `O` on an
arbitrary site. The module universe is `max u v m`, forced by the extension-by-zero adjunction,
and the homogeneous pieces of `A`, of `M` and of `N` all live in it, which the relative tensor
product forces. The slice site carries its own sheafification hypotheses, without which the
right-hand side is not defined.

## References

* [Stacks Project, Tag 0FRB](https://stacks.math.columbia.edu/tag/0FRB)
* [Stacks Project, Tag 0FR2](https://stacks.math.columbia.edu/tag/0FR2)
* [Stacks Project, Tag 0FQZ](https://stacks.math.columbia.edu/tag/0FQZ)
* [Stacks Project, Tag 0E8I](https://stacks.math.columbia.edu/tag/0E8I)
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits CategoryTheory.Sheaf Opposite
open scoped TensorProduct

universe m w v u

namespace SheafOfModules

section Generic

universe t p q s v₁ u₁

variable {D : Type u₁} [Category.{v₁} D] {K : GrothendieckTopology D} {R : Sheaf K RingCat.{t}}

/-- A bilinear map of sheaves of modules, read on the slice site at `U`. -/
noncomputable def bilinearOver {P : SheafOfModules.{p} R} {F : SheafOfModules.{q} R}
    {G : SheafOfModules.{s} R} (b : BilinearMap P F G) (U : D) :
    BilinearMap (P.over U) (F.over U) (G.over U) where
  app V := b.app (op V.unop.left)
  map_smul_left V r x y := b.map_smul_left (op V.unop.left) r x y
  map_smul_right V r x y := b.map_smul_right (op V.unop.left) r x y
  naturality f x y := b.naturality f.unop.left.op x y

/-- The left action of a left graded module, as a bilinear map. -/
def LeftGradedModule.actionBilinear {B : GradedAlgebra.{t, p} R}
    (N : LeftGradedModule.{t, p, q} B) (i n : ℤ) :
    BilinearMap (B.piece i) (N.piece n) (N.piece (i + n)) where
  app := N.smul i n
  map_smul_left := N.smul_smul_left i n
  map_smul_right := N.smul_smul_right i n
  naturality := N.smul_naturality i n

end Generic

variable {C : Type u} [Category.{v} C] {J : GrothendieckTopology C}
  (O : Sheaf J CommRingCat.{w}) (U : C)
  [J.HasSheafCompose (forget₂ CommRingCat.{w} RingCat.{w})]
  [(J.over U).HasSheafCompose (forget₂ CommRingCat.{w} RingCat.{w})]
  [HasWeakSheafify J AddCommGrpCat.{max u v m}]
  [J.WEqualsLocallyBijective AddCommGrpCat.{max u v m}]
  (A : GradedAlgebra.{w, max u v m} ((Stacks.SheafOfModules.Tensor.ringSheaf (J := J)) O))

variable {M : GradedModule.{w, max u v m, max u v m} (A.over U)}
  {N : LeftGradedModule.{w, max u v m, max u v m} A}
  (K : SheafOfModules.{max u v m} ((Stacks.SheafOfModules.Tensor.ringSheaf (J := J)) O)) {n : ℤ}

/-- Restriction of a balanced family out of `(j_!M, N)` along the unit. -/
noncomputable def RelativeTensor.Balanced.restrictAlongUnit
    (β : RelativeTensor.Balanced (gradedExtensionByZero.{m} O U A M) N K.val n) :
    RelativeTensor.Balanced (J := J.over U) (Osharp := O.over U) M (N.over U)
      (K.over U).val n where
  app p := (bilinearOver (β.app p) U).compLeft
    ((extendSheafAdjunction.{m} O U).unit.app (M.piece p.1.1)).val
  balanced i V x a y :=
    ((β.app (RelativeTensor.leftIndex i)).congr_left (op V.unop.left)
        (gradedExtendedAction_unit.{m} O U A M i.1.1 i.1.2.1 V x a).symm y).trans
      (β.balanced i (op V.unop.left) _ a y)

/-- Extension by zero of a balanced family. -/
noncomputable def RelativeTensor.Balanced.extendByZero
    (β : RelativeTensor.Balanced (J := J.over U) (Osharp := O.over U) M (N.over U)
      (K.over U).val n) :
    RelativeTensor.Balanced (gradedExtensionByZero.{m} O U A M) N K.val n where
  app p := extendBilinear.{m, w, v, u} O U (β.app p)
  balanced i V x a y := by
    refine eq_of_heq (extendedTrilinear_hext.{m, w, v, u} O U rfl
      (trilinearCompLeft (gradedExtendedAction.{m} O U A M i.1.1 i.1.2.1)
        (extendBilinear.{m, w, v, u} O U (β.app (RelativeTensor.leftIndex i))))
      (trilinearCompRight
        (extendBilinear.{m, w, v, u} O U (β.app (RelativeTensor.rightIndex i)))
        (N.actionBilinear i.1.2.1 i.1.2.2)) ?_ V x a y)
    intro W z c d
    refine heq_of_eq (Eq.trans
      ((extendBilinear.{m, w, v, u} O U (β.app (RelativeTensor.leftIndex i))).congr_left
        (op W.unop.left) (gradedExtendedAction_unit.{m} O U A M i.1.1 i.1.2.1 W z c) d) ?_)
    refine Eq.trans (extendBilinear_unit.{m, w, v, u} O U
      (β.app (RelativeTensor.leftIndex i)) W (M.smul i.1.1 i.1.2.1 W z c) d) ?_
    exact (β.balanced i W z c d).trans
      (extendBilinear_unit.{m, w, v, u} O U (β.app (RelativeTensor.rightIndex i)) W z
        (N.smul i.1.2.1 i.1.2.2 (op W.unop.left) c d)).symm

section Iso

variable [HasWeakSheafify (J.over U) AddCommGrpCat.{max u v m}]
  [(J.over U).WEqualsLocallyBijective AddCommGrpCat.{max u v m}]
  (M : GradedModule.{w, max u v m, max u v m} (A.over U))
  (N : LeftGradedModule.{w, max u v m, max u v m} A)

/-- Degree `n` of `M ⊗_{A_U} N|_U`, a sheaf of `O_U`-modules. -/
noncomputable abbrev sliceTensor (n : ℤ) :
    SheafOfModules.{max u v m} (((Stacks.SheafOfModules.Tensor.ringSheaf (J := J)) O).over U) :=
  RelativeTensor.gradedTensor (J := J.over U) (Osharp := O.over U) M (N.over U) n

/-- Degree `n` of `j_!M ⊗_A N`, a sheaf of `O`-modules. -/
noncomputable abbrev extendTensor (n : ℤ) :
    SheafOfModules.{max u v m} ((Stacks.SheafOfModules.Tensor.ringSheaf (J := J)) O) :=
  RelativeTensor.gradedTensor (gradedExtensionByZero.{m} O U A M) N n

/-- The balanced family `(x, y) ↦ x ⊗ y` of `M ⊗_{A_U} N|_U`, pushed into
`j_!(M ⊗_{A_U} N|_U)` along the unit of `j_{U!} ⊣ j_U^*`. -/
noncomputable def sliceTmulUnitBalanced (n : ℤ) :
    RelativeTensor.Balanced (J := J.over U) (Osharp := O.over U) M (N.over U)
      (((extendSheaf.{m} O U).obj (sliceTensor.{m} O U A M N n)).over U).val n :=
  (RelativeTensor.tmulBalanced (J := J.over U) (Osharp := O.over U) M (N.over U) n).postcomp
    ((extendSheafAdjunction.{m} O U).unit.app (sliceTensor.{m} O U A M N n)).val

/-- The comparison morphism `j_!M ⊗_A N ⟶ j_!(M ⊗_{A_U} N|_U)` in degree `n`. -/
noncomputable def extendTensorHom (n : ℤ) :
    extendTensor.{m} O U A M N n ⟶ (extendSheaf.{m} O U).obj (sliceTensor.{m} O U A M N n) :=
  ((sliceTmulUnitBalanced.{m} O U A M N n).extendByZero O U A
    ((extendSheaf.{m} O U).obj (sliceTensor.{m} O U A M N n))).desc
      (gradedExtensionByZero.{m} O U A M) N

/-- The adjoint transpose of the inverse comparison: the morphism
`M ⊗_{A_U} N|_U ⟶ (j_!M ⊗_A N)|_U` descending the balanced family `(x, y) ↦ j_!x ⊗ y`. -/
noncomputable def extendTensorInvTranspose (n : ℤ) :
    sliceTensor.{m} O U A M N n ⟶ (extendTensor.{m} O U A M N n).over U :=
  RelativeTensor.Balanced.desc (J := J.over U) (Osharp := O.over U) M (N.over U)
    ((RelativeTensor.tmulBalanced (gradedExtensionByZero.{m} O U A M) N n).restrictAlongUnit
      O U A (extendTensor.{m} O U A M N n))

/-- The comparison morphism `j_!(M ⊗_{A_U} N|_U) ⟶ j_!M ⊗_A N` in degree `n`. -/
noncomputable def extendTensorInv (n : ℤ) :
    (extendSheaf.{m} O U).obj (sliceTensor.{m} O U A M N n) ⟶ extendTensor.{m} O U A M N n :=
  ((extendSheafAdjunction.{m} O U).homEquiv (sliceTensor.{m} O U A M N n)
    (extendTensor.{m} O U A M N n)).symm (extendTensorInvTranspose.{m} O U A M N n)

/-- `extendTensorHom` on the local section `j_!x ⊗ y`. -/
theorem extendTensorHom_tmul_unit (n : ℤ) (p : TensorIndex n)
    (V : (Over U)ᵒᵖ) (z : (M.piece p.1.1).val.obj V)
    (y : (N.piece p.1.2).val.obj (op V.unop.left)) :
    PresheafOfModules.Hom.app (extendTensorHom.{m} O U A M N n).val (op V.unop.left)
        (RelativeTensor.tmul (gradedExtensionByZero.{m} O U A M) N n p (op V.unop.left)
          (PresheafOfModules.Hom.app
            ((extendSheafAdjunction.{m} O U).unit.app (M.piece p.1.1)).val V z) y) =
      PresheafOfModules.Hom.app
        ((extendSheafAdjunction.{m} O U).unit.app (sliceTensor.{m} O U A M N n)).val V
        (RelativeTensor.tmul (J := J.over U) (Osharp := O.over U) M (N.over U) n p V z y) :=
  (RelativeTensor.Balanced.desc_tmul (gradedExtensionByZero.{m} O U A M) N
    ((sliceTmulUnitBalanced.{m} O U A M N n).extendByZero O U A
      ((extendSheaf.{m} O U).obj (sliceTensor.{m} O U A M N n))) p (op V.unop.left) _ y).trans
    (extendBilinear_unit.{m, w, v, u} O U
      ((sliceTmulUnitBalanced.{m} O U A M N n).app p) V z y)

/-- The inverse comparison on the local sections supplied by the unit. -/
theorem extendTensorInv_unit (n : ℤ) (V : (Over U)ᵒᵖ)
    (w : (sliceTensor.{m} O U A M N n).val.obj V) :
    PresheafOfModules.Hom.app (extendTensorInv.{m} O U A M N n).val (op V.unop.left)
        (PresheafOfModules.Hom.app
          ((extendSheafAdjunction.{m} O U).unit.app (sliceTensor.{m} O U A M N n)).val V w) =
      PresheafOfModules.Hom.app (extendTensorInvTranspose.{m} O U A M N n).val V w :=
  congrArg (fun s => PresheafOfModules.Hom.app s.val V w)
    (((extendSheafAdjunction.{m} O U).homEquiv (sliceTensor.{m} O U A M N n)
      (extendTensor.{m} O U A M N n)).apply_symm_apply
        (extendTensorInvTranspose.{m} O U A M N n))

/-- The adjoint transpose of the inverse comparison on the local section `x ⊗ y`. -/
theorem extendTensorInvTranspose_tmul (n : ℤ) (p : TensorIndex n)
    (V : (Over U)ᵒᵖ) (z : (M.piece p.1.1).val.obj V)
    (y : (N.piece p.1.2).val.obj (op V.unop.left)) :
    PresheafOfModules.Hom.app (extendTensorInvTranspose.{m} O U A M N n).val V
        (RelativeTensor.tmul (J := J.over U) (Osharp := O.over U) M (N.over U) n p V z y) =
      RelativeTensor.tmul (gradedExtensionByZero.{m} O U A M) N n p (op V.unop.left)
        (PresheafOfModules.Hom.app
          ((extendSheafAdjunction.{m} O U).unit.app (M.piece p.1.1)).val V z) y :=
  RelativeTensor.Balanced.desc_tmul (J := J.over U) (Osharp := O.over U) M (N.over U)
    ((RelativeTensor.tmulBalanced (gradedExtensionByZero.{m} O U A M) N n).restrictAlongUnit
      O U A (extendTensor.{m} O U A M N n)) p V z y

/-- The comparison `j_!M ⊗_A N ⟶ j_!(M ⊗_{A_U} N|_U)` followed by its inverse is the
identity. -/
theorem extendTensorHom_comp_inv (n : ℤ) :
    extendTensorHom.{m} O U A M N n ≫ extendTensorInv.{m} O U A M N n = 𝟙 _ := by
  refine RelativeTensor.gradedTensor_hom_ext (gradedExtensionByZero.{m} O U A M) N
    fun p X x y ↦ ?_
  refine extendedBilinear_ext.{m, w, v, u} O U
    (((RelativeTensor.tmulBalanced (gradedExtensionByZero.{m} O U A M) N n).app p).postcomp
      (extendTensorHom.{m} O U A M N n ≫ extendTensorInv.{m} O U A M N n).val)
    ((RelativeTensor.tmulBalanced (gradedExtensionByZero.{m} O U A M) N n).app p) ?_ X x y
  intro V z y'
  have h1 := extendTensorHom_tmul_unit.{m} O U A M N n p V z y'
  have h2 := extendTensorInv_unit.{m} O U A M N n V
    (RelativeTensor.tmul (J := J.over U) (Osharp := O.over U) M (N.over U) n p V z y')
  have h3 := extendTensorInvTranspose_tmul.{m} O U A M N n p V z y'
  exact (congrArg (PresheafOfModules.Hom.app (extendTensorInv.{m} O U A M N n).val
    (op V.unop.left)) h1).trans (h2.trans h3)

/-- The comparison `j_!(M ⊗_{A_U} N|_U) ⟶ j_!M ⊗_A N` followed by its inverse is the
identity. -/
theorem extendTensorInv_comp_hom (n : ℤ) :
    extendTensorInv.{m} O U A M N n ≫ extendTensorHom.{m} O U A M N n = 𝟙 _ := by
  refine ((extendSheafAdjunction.{m} O U).homEquiv (sliceTensor.{m} O U A M N n)
    ((extendSheaf.{m} O U).obj (sliceTensor.{m} O U A M N n))).injective ?_
  rw [(extendSheafAdjunction.{m} O U).homEquiv_id]
  refine RelativeTensor.gradedTensor_hom_ext (J := J.over U) (Osharp := O.over U) M (N.over U)
    fun p V z y ↦ ?_
  have h1 := extendTensorInv_unit.{m} O U A M N n V
    (RelativeTensor.tmul (J := J.over U) (Osharp := O.over U) M (N.over U) n p V z y)
  have h2 := extendTensorInvTranspose_tmul.{m} O U A M N n p V z y
  have h3 := extendTensorHom_tmul_unit.{m} O U A M N n p V z y
  exact (congrArg (PresheafOfModules.Hom.app (extendTensorHom.{m} O U A M N n).val
    (op V.unop.left)) h1).trans ((congrArg (PresheafOfModules.Hom.app
      (extendTensorHom.{m} O U A M N n).val (op V.unop.left)) h2).trans h3)

/-- **Tag 0FRB.** In every degree `n` the relative tensor product of the extension by zero of
a right graded `A_U`-module `M` with a left graded `A`-module `N` is the extension by zero of
the relative tensor product of `M` with the restriction of `N`:
`j_!M ⊗_A N = j_!(M ⊗_{A_U} N|_U)` as sheaves of `O`-modules. The isomorphism sends the local
section `j_!x ⊗ y` to `j_!(x ⊗ y)`, and it is natural in `M` and in `N` by
`SheafOfModules.extendTensorHom_naturality_left` and `..._naturality_right`. -/
@[stacks 0FRB "j_! M ⊗_A N = j_!(M ⊗_{A_U} N|_U) as graded O-modules"]
noncomputable def extendTensorIso (n : ℤ) :
    extendTensor.{m} O U A M N n ≅
      (extendSheaf.{m} O U).obj (sliceTensor.{m} O U A M N n) where
  hom := extendTensorHom.{m} O U A M N n
  inv := extendTensorInv.{m} O U A M N n
  hom_inv_id := extendTensorHom_comp_inv.{m} O U A M N n
  inv_hom_id := extendTensorInv_comp_hom.{m} O U A M N n

/-- **Tag 0FRB, functoriality in the left graded module.** The identification
`j_!M ⊗_A N = j_!(M ⊗_{A_U} N|_U)` commutes with a homomorphism `N ⟶ N'` of left graded
`A`-modules. -/
@[stacks 0FRB "functoriality of j_! M ⊗_A N = j_!(M ⊗_{A_U} N|_U) in N"]
theorem extendTensorHom_naturality_right {N' : LeftGradedModule.{w, max u v m, max u v m} A}
    (f : N ⟶ N') (n : ℤ) :
    RelativeTensor.gradedTensorMap (gradedExtensionByZero.{m} O U A M) f n ≫
        extendTensorHom.{m} O U A M N' n =
      extendTensorHom.{m} O U A M N n ≫ (extendSheaf.{m} O U).map
        (RelativeTensor.gradedTensorMap (J := J.over U) (Osharp := O.over U) M
          (LeftGradedModule.overMap f U) n) := by
  refine RelativeTensor.gradedTensor_hom_ext (gradedExtensionByZero.{m} O U A M) N
    fun p X x y ↦ ?_
  refine extendedBilinear_ext.{m, w, v, u} O U
    (((RelativeTensor.tmulBalanced (gradedExtensionByZero.{m} O U A M) N n).app p).postcomp
      (RelativeTensor.gradedTensorMap (gradedExtensionByZero.{m} O U A M) f n ≫
        extendTensorHom.{m} O U A M N' n).val)
    (((RelativeTensor.tmulBalanced (gradedExtensionByZero.{m} O U A M) N n).app p).postcomp
      (extendTensorHom.{m} O U A M N n ≫ (extendSheaf.{m} O U).map
        (RelativeTensor.gradedTensorMap (J := J.over U) (Osharp := O.over U) M
          (LeftGradedModule.overMap f U) n)).val) ?_ X x y
  intro V z y'
  have hl := RelativeTensor.gradedTensorMap_tmul (gradedExtensionByZero.{m} O U A M) f n p
    (op V.unop.left)
    (PresheafOfModules.Hom.app
      ((extendSheafAdjunction.{m} O U).unit.app (M.piece p.1.1)).val V z) y'
  have hl2 := extendTensorHom_tmul_unit.{m} O U A M N' n p V z
    (PresheafOfModules.Hom.app (f.app p.1.2).val (op V.unop.left) y')
  have hr := extendTensorHom_tmul_unit.{m} O U A M N n p V z y'
  have hr2 : PresheafOfModules.Hom.app ((extendSheaf.{m} O U).map
        (RelativeTensor.gradedTensorMap (J := J.over U) (Osharp := O.over U) M
          (LeftGradedModule.overMap f U) n)).val (op V.unop.left)
      (PresheafOfModules.Hom.app
        ((extendSheafAdjunction.{m} O U).unit.app (sliceTensor.{m} O U A M N n)).val V
        (RelativeTensor.tmul (J := J.over U) (Osharp := O.over U) M (N.over U) n p V z y')) =
      PresheafOfModules.Hom.app
        ((extendSheafAdjunction.{m} O U).unit.app (sliceTensor.{m} O U A M N' n)).val V
        (PresheafOfModules.Hom.app
          (RelativeTensor.gradedTensorMap (J := J.over U) (Osharp := O.over U) M
            (LeftGradedModule.overMap f U) n).val V
          (RelativeTensor.tmul (J := J.over U) (Osharp := O.over U) M (N.over U) n p V z y')) :=
    congrArg (fun s => PresheafOfModules.Hom.app s.val V
        (RelativeTensor.tmul (J := J.over U) (Osharp := O.over U) M (N.over U) n p V z y'))
      ((extendSheafAdjunction.{m} O U).unit.naturality
        (RelativeTensor.gradedTensorMap (J := J.over U) (Osharp := O.over U) M
          (LeftGradedModule.overMap f U) n)).symm
  have hr3 := RelativeTensor.gradedTensorMap_tmul (J := J.over U) (Osharp := O.over U) M
    (LeftGradedModule.overMap f U) n p V z y'
  exact ((congrArg (PresheafOfModules.Hom.app
      (extendTensorHom.{m} O U A M N' n).val (op V.unop.left)) hl).trans hl2).trans
    (((congrArg (PresheafOfModules.Hom.app
        ((extendSheaf.{m} O U).map (RelativeTensor.gradedTensorMap (J := J.over U)
          (Osharp := O.over U) M (LeftGradedModule.overMap f U) n)).val
        (op V.unop.left)) hr).trans (hr2.trans (congrArg (PresheafOfModules.Hom.app
          ((extendSheafAdjunction.{m} O U).unit.app
            (sliceTensor.{m} O U A M N' n)).val V) hr3))).symm)

/-- **Tag 0FRB, functoriality in the right graded module.** The identification
`j_!M ⊗_A N = j_!(M ⊗_{A_U} N|_U)` commutes with a homomorphism `M ⟶ M'` of right graded
`A_U`-modules. -/
@[stacks 0FRB "functoriality of j_! M ⊗_A N = j_!(M ⊗_{A_U} N|_U) in M"]
theorem extendTensorHom_naturality_left {M' : GradedModule.{w, max u v m, max u v m} (A.over U)}
    (h : M ⟶ M') (n : ℤ) :
    RelativeTensor.gradedTensorMapRight (gradedExtensionByZeroMap.{m} O U A h) N n ≫
        extendTensorHom.{m} O U A M' N n =
      extendTensorHom.{m} O U A M N n ≫ (extendSheaf.{m} O U).map
        (RelativeTensor.gradedTensorMapRight (J := J.over U) (Osharp := O.over U) h
          (N.over U) n) := by
  refine RelativeTensor.gradedTensor_hom_ext (gradedExtensionByZero.{m} O U A M) N
    fun p X x y ↦ ?_
  refine extendedBilinear_ext.{m, w, v, u} O U
    (((RelativeTensor.tmulBalanced (gradedExtensionByZero.{m} O U A M) N n).app p).postcomp
      (RelativeTensor.gradedTensorMapRight (gradedExtensionByZeroMap.{m} O U A h) N n ≫
        extendTensorHom.{m} O U A M' N n).val)
    (((RelativeTensor.tmulBalanced (gradedExtensionByZero.{m} O U A M) N n).app p).postcomp
      (extendTensorHom.{m} O U A M N n ≫ (extendSheaf.{m} O U).map
        (RelativeTensor.gradedTensorMapRight (J := J.over U) (Osharp := O.over U) h
          (N.over U) n)).val) ?_ X x y
  intro V z y'
  have hu : PresheafOfModules.Hom.app
        ((extendSheaf.{m} O U).map (h.app p.1.1)).val (op V.unop.left)
        (PresheafOfModules.Hom.app
          ((extendSheafAdjunction.{m} O U).unit.app (M.piece p.1.1)).val V z) =
      PresheafOfModules.Hom.app
        ((extendSheafAdjunction.{m} O U).unit.app (M'.piece p.1.1)).val V
        (PresheafOfModules.Hom.app (h.app p.1.1).val V z) :=
    (congrArg (fun s => PresheafOfModules.Hom.app s.val V z)
      ((extendSheafAdjunction.{m} O U).unit.naturality (h.app p.1.1))).symm
  have hl := RelativeTensor.gradedTensorMapRight_tmul
    (gradedExtensionByZeroMap.{m} O U A h) N n p (op V.unop.left)
    (PresheafOfModules.Hom.app
      ((extendSheafAdjunction.{m} O U).unit.app (M.piece p.1.1)).val V z) y'
  have hl2 := extendTensorHom_tmul_unit.{m} O U A M' N n p V
    (PresheafOfModules.Hom.app (h.app p.1.1).val V z) y'
  have hr := extendTensorHom_tmul_unit.{m} O U A M N n p V z y'
  have hr2 : PresheafOfModules.Hom.app ((extendSheaf.{m} O U).map
        (RelativeTensor.gradedTensorMapRight (J := J.over U) (Osharp := O.over U) h
          (N.over U) n)).val (op V.unop.left)
      (PresheafOfModules.Hom.app
        ((extendSheafAdjunction.{m} O U).unit.app (sliceTensor.{m} O U A M N n)).val V
        (RelativeTensor.tmul (J := J.over U) (Osharp := O.over U) M (N.over U) n p V z y')) =
      PresheafOfModules.Hom.app
        ((extendSheafAdjunction.{m} O U).unit.app (sliceTensor.{m} O U A M' N n)).val V
        (PresheafOfModules.Hom.app
          (RelativeTensor.gradedTensorMapRight (J := J.over U) (Osharp := O.over U) h
            (N.over U) n).val V
          (RelativeTensor.tmul (J := J.over U) (Osharp := O.over U) M (N.over U) n p V z y')) :=
    congrArg (fun s => PresheafOfModules.Hom.app s.val V
        (RelativeTensor.tmul (J := J.over U) (Osharp := O.over U) M (N.over U) n p V z y'))
      ((extendSheafAdjunction.{m} O U).unit.naturality
        (RelativeTensor.gradedTensorMapRight (J := J.over U) (Osharp := O.over U) h
          (N.over U) n)).symm
  have hr3 := RelativeTensor.gradedTensorMapRight_tmul (J := J.over U) (Osharp := O.over U) h
    (N.over U) n p V z y'
  refine Eq.trans (congrArg (PresheafOfModules.Hom.app
    (extendTensorHom.{m} O U A M' N n).val (op V.unop.left)) (hl.trans
      (congrArg (fun s => RelativeTensor.tmul (gradedExtensionByZero.{m} O U A M') N n p
        (op V.unop.left) s y') hu))) ?_
  refine hl2.trans ?_
  exact (((congrArg (PresheafOfModules.Hom.app
      ((extendSheaf.{m} O U).map (RelativeTensor.gradedTensorMapRight (J := J.over U)
        (Osharp := O.over U) h (N.over U) n)).val (op V.unop.left)) hr).trans
    (hr2.trans (congrArg (PresheafOfModules.Hom.app
      ((extendSheafAdjunction.{m} O U).unit.app
        (sliceTensor.{m} O U A M' N n)).val V) hr3))).symm)

end Iso

end SheafOfModules

end
