module

public import StacksFrontier.Algebra.Category.ModuleCat.Sheaf.DifferentialGradedRelativeTensor
public import StacksFrontier.Algebra.Category.ModuleCat.Sheaf.DifferentialGradedCone
public import Mathlib.Algebra.Homology.HomotopyCategory.ShiftSequence
import StacksCore.Tactic.EgaSgaAttribute

/-!
# Flatness and K-flatness of a shifted differential graded module

Let `O` be a sheaf of commutative rings on a site, let `A` be a sheaf of differential graded
`O`-algebras and let `P` be a right differential graded `A`-module. A shift of `P` only relabels
degrees and multiplies the differential by a sign, so degree `n` of `P[k] ⊗_A N` is degree
`n + k` of `P ⊗_A N`, naturally in the left differential graded `A`-module `N`. Consequently
`P[k]` is flat as a graded module as soon as `P` is, and is K-flat as soon as `P` is.

## Main definitions

* `SheafOfModules.RelativeTensor.IsGradedShift` is the datum identifying degree `n` of a right
  graded module `Q` with degree `n + k` of another one `P`, compatibly with the right actions.
* `SheafOfModules.RelativeTensor.IsGradedShift.gradedTensorIso` is the identification
  `(Q ⊗_A N)^n ≅ (P ⊗_A N)^{n + k}`.
* `SheafOfModules.RelativeTensor.IsDifferentialGradedShift` adds to `IsGradedShift` the
  compatibility with the differentials, where the sign `(-1)^k` appears, and
  `SheafOfModules.RelativeTensor.IsDifferentialGradedShift.dgTensorIso` assembles the degreewise
  identifications into an isomorphism of complexes `Q ⊗_A N ≅ (P ⊗_A N)[k]`.

## Main results

* `SheafOfModules.RelativeTensor.IsGradedShift.gradedTensorHom_naturality`: the identification
  is natural in `N`.
* `SheafOfModules.RelativeTensor.IsGradedShift.isGradedFlat`: a degree shift of a flat right
  graded module is flat.
* `SheafOfModules.RelativeTensor.IsDifferentialGradedShift.isKFlat`: a degree shift of a K-flat
  right differential graded module is K-flat.
* `SheafOfModules.DifferentialGradedModule.isGradedFlat_shift` and
  `SheafOfModules.DifferentialGradedModule.isKFlat_shift`: the degree-one shift of a right
  differential graded module is flat as a graded module, respectively K-flat, as soon as the
  module is.

## Implementation notes

The shift is taken as data rather than constructed: `IsGradedShift` records a family of
isomorphisms `Q^n ≅ P^p` indexed by *equalities* `n + k = p` rather than one isomorphism
`Q^n ≅ P^{n + k}`. The two carry the same information, but the first lets every degree
bookkeeping step choose the spelling of the target degree it needs, so the construction below
has no transport in it beyond the two lemmas
`SheafOfModules.RelativeTensor.IsGradedShift.e_hom_congr` and `e_inv_congr`, which compare the
identifications attached to two spellings of one degree.

K-flatness is transported through the shift of complexes rather than degreewise, because
acyclicity of a shifted cochain complex is the shift sequence of the homology functor
(`CategoryTheory.Functor.shiftIso`) and needs no further computation.

The isomorphism on tensor products is built from the universal property of the relative tensor
product (`SheafOfModules.RelativeTensor.Balanced.desc` and
`SheafOfModules.RelativeTensor.gradedTensor_hom_ext`), not by reindexing the direct sums of the
presentation: the balanced family is `(x, y) ↦ x ⊗ y` read through the identification, and every
identity below is checked on local sections `x ⊗ y`.

## References

* [Stacks Project, Tag 0FRM](https://stacks.math.columbia.edu/tag/0FRM)
* [Stacks Project, Tag 0FRY](https://stacks.math.columbia.edu/tag/0FRY)
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits CategoryTheory.Sheaf

universe t m v u

namespace SheafOfModules

variable {C : Type u} [Category.{v} C] {J : GrothendieckTopology C}
  [J.HasSheafCompose (forget₂ CommRingCat.{t} RingCat.{t})] {Osharp : Sheaf J CommRingCat.{t}}

/-! ### Local sections of transported and scaled morphisms

The two lemmas here are the universe-polymorphic forms of
`SheafOfModules.zsmul_val_app` and `SheafOfModules.eqToHom_val_app`, whose module universe is
tied to the universe of the sheaf of rings. The relative tensor product keeps the two
independent, so it needs these. -/

namespace ShiftFlat

omit [J.HasSheafCompose (forget₂ CommRingCat.{t} RingCat.{t})]

variable {R : Sheaf J RingCat.{t}}

/-- An integer multiple of a morphism of sheaves of modules acts on local sections as that
multiple of its action. -/
theorem zsmul_val_app {M N : SheafOfModules.{m} R} (c : ℤ) (φ : M ⟶ N) (U : Cᵒᵖ)
    (z : M.val.obj U) :
    PresheafOfModules.Hom.app (c • φ).val U z =
      c • PresheafOfModules.Hom.app φ.val U z :=
  map_zsmul (AddMonoidHom.mk' (fun ψ : M ⟶ N ↦ PresheafOfModules.Hom.app ψ.val U z)
    fun _ _ ↦ rfl) c φ

/-- A composite of morphisms of sheaves of modules acts on local sections by acting in turn. -/
private theorem comp_val_app_apply {X Y Z : SheafOfModules.{m} R} (f : X ⟶ Y) (g : Y ⟶ Z)
    (U : Cᵒᵖ) (x : X.val.obj U) :
    PresheafOfModules.Hom.app (f ≫ g).val U x =
      PresheafOfModules.Hom.app g.val U (PresheafOfModules.Hom.app f.val U x) :=
  PresheafOfModules.comp_app_apply f.val g.val U x

/-- Transport of a family of sheaves of modules along an equality of indices acts on local
sections as `SheafOfModules.gradedCast`. -/
theorem eqToHom_val_app {ι : Type*} (Y : ι → SheafOfModules.{m} R) {i j : ι} (h : i = j)
    (U : Cᵒᵖ) (y : (Y i).val.obj U) :
    PresheafOfModules.Hom.app (eqToHom (congrArg Y h)).val U y =
      gradedCast (fun q ↦ (Y q).val.obj U) h y := by
  subst h
  rfl

/-- Transport of a differential along an equality of complexes, read on local sections. -/
theorem d_val_app_of_eq {T T' : CochainComplex (SheafOfModules.{m} R) ℤ} (hT : T = T')
    (a b : ℤ) (U : Cᵒᵖ) (x : (T.X a).val.obj U) :
    PresheafOfModules.Hom.app
        (eqToHom (congrArg (fun S : CochainComplex (SheafOfModules.{m} R) ℤ ↦ S.X b) hT)).val U
        (PresheafOfModules.Hom.app (T.d a b).val U x) =
      PresheafOfModules.Hom.app (T'.d a b).val U
        (PresheafOfModules.Hom.app
          (eqToHom (congrArg (fun S : CochainComplex (SheafOfModules.{m} R) ℤ ↦ S.X a) hT)).val U
          x) := by
  cases hT
  rfl

/-- The differential of a cochain complex which is the `k`-th shift of another one, read through
the identification of the terms: it is `(-1)^k` times the differential of that one. -/
theorem shifted_d_val_app {T T' : CochainComplex (SheafOfModules.{m} R) ℤ} (k : ℤ)
    (hT : T = (CochainComplex.shiftFunctor (SheafOfModules.{m} R) k).obj T')
    (n n₁ p p₁ : ℤ) (hn : n + 1 = n₁) (hp : n + k = p) (hp₁ : n₁ + k = p₁)
    (U : Cᵒᵖ) (x : (T.X n).val.obj U) :
    PresheafOfModules.Hom.app
        (eqToHom ((congrArg (fun S : CochainComplex (SheafOfModules.{m} R) ℤ ↦ S.X n₁) hT).trans
          (congrArg T'.X hp₁))).val U
        (PresheafOfModules.Hom.app (T.d n n₁).val U x) =
      (Int.negOnePow k : ℤ) • PresheafOfModules.Hom.app (T'.d p p₁).val U
        (PresheafOfModules.Hom.app
          (eqToHom ((congrArg (fun S : CochainComplex (SheafOfModules.{m} R) ℤ ↦ S.X n) hT).trans
            (congrArg T'.X hp))).val U x) := by
  cases hT
  subst hn
  subst hp₁
  subst hp
  exact zsmul_val_app _ _ U x

/-- A bilinear map read through an identification of its source and of its target: if the two
bilinear maps have the same action on sections up to the transports, the transport of a value of
the first is the value of the second. -/
theorem bilinear_transport {M₁ M₂ : SheafOfModules.{m} R} {K : SheafOfModules.{m} R}
    {P₁ P₂ : SheafOfModules.{m} R} (hM : M₁ = M₂) (hP : P₁ = P₂)
    (β₁ : Stacks.BilinearMap M₁.val K.val P₁.val)
    (β₂ : Stacks.BilinearMap M₂.val K.val P₂.val) (U : Cᵒᵖ)
    (hβ : HEq (β₁.app U) (β₂.app U)) (x : M₁.val.obj U) (y : K.val.obj U) :
    PresheafOfModules.Hom.app (eqToHom hP).val U (β₁.app U x y) =
      β₂.app U (PresheafOfModules.Hom.app (eqToHom hM).val U x) y := by
  cases hM
  cases hP
  rw [eq_of_heq hβ]
  rfl

end ShiftFlat

/-! ### Acyclicity of a shifted cochain complex -/

/-- A shift of an acyclic cochain complex in an abelian category is acyclic. -/
theorem acyclic_shiftFunctor_obj {B : Type*} [Category* B] [Abelian B] (k : ℤ)
    {T : CochainComplex B ℤ} (hT : T.Acyclic) :
    ((CochainComplex.shiftFunctor B k).obj T).Acyclic := by
  intro i
  rw [HomologicalComplex.exactAt_iff_isZero_homology]
  refine (Iso.isZero_iff
    (((HomologicalComplex.homologyFunctor B (ComplexShape.up ℤ) 0).shiftIso k i (k + i)
      rfl).app T)).2 ?_
  exact (HomologicalComplex.exactAt_iff_isZero_homology _ _).1 (hT (k + i))

namespace RelativeTensor

/-! ### Degree shifts of right graded modules -/

section Graded

variable {A : GradedAlgebra.{t, m} (toRingCat J Osharp)}

/-- The datum exhibiting a right graded `A`-module `Q` as the degree `k` shift of a right graded
`A`-module `P`: degree `n` of `Q` is degree `n + k` of `P`, compatibly with the right actions. -/
structure IsGradedShift (k : ℤ) (Q P : GradedModule.{t, m, m} A) where
  /-- Degree `n` of `Q` is degree `p` of `P`, for every integer `p` equal to `n + k`. -/
  e {n p : ℤ} (h : n + k = p) : Q.piece n ≅ P.piece p
  /-- The identification carries the right action of `Q` to the right action of `P`. -/
  e_smul {n i p : ℤ} (h : n + k = p) (U : Cᵒᵖ) (x : (Q.piece n).val.obj U)
      (y : (A.piece i).val.obj U) :
    PresheafOfModules.Hom.app (e (show n + i + k = p + i by omega)).hom.val U
        (Q.smul n i U x y) =
      P.smul p i U (PresheafOfModules.Hom.app (e h).hom.val U x) y

namespace IsGradedShift

variable {k : ℤ} {Q P : GradedModule.{t, m, m} A} (D : IsGradedShift k Q P)

/-- The identifications attached to two spellings of the same target degree agree. -/
theorem e_hom_congr {n p p' : ℤ} (h : n + k = p) (h' : n + k = p') (hp : p = p')
    (U : Cᵒᵖ) (x : (Q.piece n).val.obj U) :
    PresheafOfModules.Hom.app (D.e h').hom.val U x =
      gradedCast (fun j ↦ (P.piece j).val.obj U) hp
        (PresheafOfModules.Hom.app (D.e h).hom.val U x) := by
  cases hp
  rfl

/-- The inverse identifications attached to two spellings of the same source degree agree. -/
theorem e_inv_congr {n n' p : ℤ} (h : n + k = p) (h' : n' + k = p) (hn : n = n')
    (U : Cᵒᵖ) (x : (P.piece p).val.obj U) :
    PresheafOfModules.Hom.app (D.e h').inv.val U x =
      gradedCast (fun j ↦ (Q.piece j).val.obj U) hn
        (PresheafOfModules.Hom.app (D.e h).inv.val U x) := by
  cases hn
  rfl

/-- The identification of degree `n` of `Q` with degree `p` of `P` is a bijection on sections. -/
theorem e_inv_hom_apply {n p : ℤ} (h : n + k = p) (U : Cᵒᵖ) (x : (Q.piece n).val.obj U) :
    PresheafOfModules.Hom.app (D.e h).inv.val U
        (PresheafOfModules.Hom.app (D.e h).hom.val U x) = x :=
  (PresheafOfModules.comp_app_apply (D.e h).hom.val (D.e h).inv.val U x).symm.trans
    (PresheafOfModules.hom_congr_apply
      (congrArg SheafOfModules.Hom.val (D.e h).hom_inv_id) U x)

/-- The identification of degree `p` of `P` with degree `n` of `Q` is a bijection on sections. -/
theorem e_hom_inv_apply {n p : ℤ} (h : n + k = p) (U : Cᵒᵖ) (x : (P.piece p).val.obj U) :
    PresheafOfModules.Hom.app (D.e h).hom.val U
        (PresheafOfModules.Hom.app (D.e h).inv.val U x) = x :=
  (PresheafOfModules.comp_app_apply (D.e h).inv.val (D.e h).hom.val U x).symm.trans
    (PresheafOfModules.hom_congr_apply
      (congrArg SheafOfModules.Hom.val (D.e h).inv_hom_id) U x)

end IsGradedShift

section Sheafify

variable [J.WEqualsLocallyBijective AddCommGrpCat.{m}] [HasWeakSheafify J AddCommGrpCat.{m}]

/-- A local section `x ⊗ y` of the relative tensor product is unchanged when the degree of its
first factor is transported along an equality of integers. -/
theorem tmul_congr_fst (P : GradedModule.{t, m, m} A) (N : LeftGradedModule.{t, m, m} A)
    {n a a' q : ℤ} (ha : a = a') (h : a + q = n) (X : Cᵒᵖ)
    (x : (P.piece a).val.obj X) (y : (N.piece q).val.obj X) :
    tmul P N n ⟨(a', q), by omega⟩ X
        (gradedCast (fun j ↦ (P.piece j).val.obj X) ha x) y =
      tmul P N n ⟨(a, q), h⟩ X x y := by
  cases ha
  rfl

namespace IsGradedShift

variable {k : ℤ} {Q P : GradedModule.{t, m, m} A} (D : IsGradedShift k Q P)
  (N : LeftGradedModule.{t, m, m} A)

/-- The bilinear map `(x, y) ↦ x ⊗ y` on the summand of index `q`, read through the
identification of degree `q.1` of `Q` with degree `q.1 + k` of `P`. -/
noncomputable def shiftBilinear {n p : ℤ} (h : n + k = p) (q : TensorIndex n) :
    Stacks.BilinearMap (Q.piece q.1.1).val (N.piece q.1.2).val (gradedTensor P N p).val :=
  ((tmulBalanced P N p).app ⟨(q.1.1 + k, q.1.2), by have := q.2; omega⟩).compLeft
    (D.e (rfl : q.1.1 + k = q.1.1 + k)).hom.val

/-- `shiftBilinear` sends `(x, y)` to the local section `e x ⊗ y` of degree `n + k` of
`P ⊗_A N`. -/
@[simp]
theorem shiftBilinear_app {n p : ℤ} (h : n + k = p) (q : TensorIndex n) (X : Cᵒᵖ)
    (x : (Q.piece q.1.1).val.obj X) (y : (N.piece q.1.2).val.obj X) :
    (D.shiftBilinear N h q).app X x y =
      tmul P N p ⟨(q.1.1 + k, q.1.2), by have := q.2; omega⟩ X
        (PresheafOfModules.Hom.app (D.e (rfl : q.1.1 + k = q.1.1 + k)).hom.val X x) y := rfl

/-- The bilinear map `(x, y) ↦ x ⊗ y` on the summand of index `q`, read through the
identification of degree `q.1` of `P` with degree `q.1 - k` of `Q`. -/
noncomputable def unshiftBilinear {n p : ℤ} (h : n + k = p) (q : TensorIndex p) :
    Stacks.BilinearMap (P.piece q.1.1).val (N.piece q.1.2).val (gradedTensor Q N n).val :=
  ((tmulBalanced Q N n).app ⟨(q.1.1 - k, q.1.2), by have := q.2; omega⟩).compLeft
    (D.e (show q.1.1 - k + k = q.1.1 by omega)).inv.val

/-- `unshiftBilinear` sends `(x, y)` to the local section `e⁻¹ x ⊗ y` of degree `n` of
`Q ⊗_A N`. -/
@[simp]
theorem unshiftBilinear_app {n p : ℤ} (h : n + k = p) (q : TensorIndex p) (X : Cᵒᵖ)
    (x : (P.piece q.1.1).val.obj X) (y : (N.piece q.1.2).val.obj X) :
    (D.unshiftBilinear N h q).app X x y =
      tmul Q N n ⟨(q.1.1 - k, q.1.2), by have := q.2; omega⟩ X
        (PresheafOfModules.Hom.app
          (D.e (show q.1.1 - k + k = q.1.1 by omega)).inv.val X x) y := rfl

/-- The balanced family `(x, y) ↦ x ⊗ y` out of `Q` and `N` in total degree `n`, with values in
degree `n + k` of `P ⊗_A N`. -/
noncomputable def shiftBalanced {n p : ℤ} (h : n + k = p) :
    Balanced Q N (gradedTensor P N p).val n where
  app q := D.shiftBilinear N h q
  balanced i X x a y := by
    have key := (tmulBalanced P N p).balanced
      (⟨(i.1.1 + k, i.1.2.1, i.1.2.2), by
        change i.1.1 + k + i.1.2.1 + i.1.2.2 = p
        have := i.2; omega⟩ : RelationIndex p) X
      (PresheafOfModules.Hom.app (D.e (rfl : i.1.1 + k = i.1.1 + k)).hom.val X x) a y
    rw [shiftBilinear_app, shiftBilinear_app,
      D.e_hom_congr (show i.1.1 + i.1.2.1 + k = i.1.1 + k + i.1.2.1 by omega) rfl
        (show i.1.1 + k + i.1.2.1 = i.1.1 + i.1.2.1 + k by omega) X (Q.smul i.1.1 i.1.2.1 X x a),
      D.e_smul (rfl : i.1.1 + k = i.1.1 + k) X x a,
      tmul_congr_fst P N (show i.1.1 + k + i.1.2.1 = i.1.1 + i.1.2.1 + k by omega)
        (show i.1.1 + k + i.1.2.1 + i.1.2.2 = p by have := i.2; omega)]
    exact key

/-- The balanced family `(x, y) ↦ x ⊗ y` out of `P` and `N` in total degree `p = n + k`, with
values in degree `n` of `Q ⊗_A N`. -/
noncomputable def unshiftBalanced {n p : ℤ} (h : n + k = p) :
    Balanced P N (gradedTensor Q N n).val p where
  app q := D.unshiftBilinear N h q
  balanced i X x a y := by
    have key := (tmulBalanced Q N n).balanced
      (⟨(i.1.1 - k, i.1.2.1, i.1.2.2), by
        change i.1.1 - k + i.1.2.1 + i.1.2.2 = n
        have := i.2; omega⟩ : RelationIndex n) X
      (PresheafOfModules.Hom.app
        (D.e (show i.1.1 - k + k = i.1.1 by omega)).inv.val X x) a y
    have hback : PresheafOfModules.Hom.app
          (D.e (show i.1.1 - k + i.1.2.1 + k = i.1.1 + i.1.2.1 by omega)).hom.val X
          (Q.smul (i.1.1 - k) i.1.2.1 X
            (PresheafOfModules.Hom.app
              (D.e (show i.1.1 - k + k = i.1.1 by omega)).inv.val X x) a) =
        P.smul i.1.1 i.1.2.1 X x a := by
      refine (D.e_smul (show i.1.1 - k + k = i.1.1 by omega) X
        (PresheafOfModules.Hom.app
          (D.e (show i.1.1 - k + k = i.1.1 by omega)).inv.val X x) a).trans ?_
      exact congrArg (fun z ↦ P.smul i.1.1 i.1.2.1 X z a)
        (D.e_hom_inv_apply (show i.1.1 - k + k = i.1.1 by omega) X x)
    have hpush : PresheafOfModules.Hom.app
          (D.e (show i.1.1 - k + i.1.2.1 + k = i.1.1 + i.1.2.1 by omega)).inv.val X
          (P.smul i.1.1 i.1.2.1 X x a) =
        Q.smul (i.1.1 - k) i.1.2.1 X
          (PresheafOfModules.Hom.app
            (D.e (show i.1.1 - k + k = i.1.1 by omega)).inv.val X x) a := by
      rw [← hback]
      exact D.e_inv_hom_apply (show i.1.1 - k + i.1.2.1 + k = i.1.1 + i.1.2.1 by omega) X _
    rw [unshiftBilinear_app, unshiftBilinear_app,
      D.e_inv_congr (show i.1.1 - k + i.1.2.1 + k = i.1.1 + i.1.2.1 by omega)
        (show i.1.1 + i.1.2.1 - k + k = i.1.1 + i.1.2.1 by omega)
        (show i.1.1 - k + i.1.2.1 = i.1.1 + i.1.2.1 - k by omega) X
        (P.smul i.1.1 i.1.2.1 X x a),
      hpush,
      tmul_congr_fst Q N (show i.1.1 - k + i.1.2.1 = i.1.1 + i.1.2.1 - k by omega)
        (show i.1.1 - k + i.1.2.1 + i.1.2.2 = n by have := i.2; omega)]
    exact key

/-- Degree `n` of `Q ⊗_A N`, mapped to degree `p = n + k` of `P ⊗_A N`. -/
noncomputable def gradedTensorHom {n p : ℤ} (h : n + k = p) :
    gradedTensor Q N n ⟶ gradedTensor P N p :=
  (D.shiftBalanced N h).desc Q N

/-- Degree `p = n + k` of `P ⊗_A N`, mapped to degree `n` of `Q ⊗_A N`. -/
noncomputable def gradedTensorInv {n p : ℤ} (h : n + k = p) :
    gradedTensor P N p ⟶ gradedTensor Q N n :=
  (D.unshiftBalanced N h).desc P N

/-- `gradedTensorHom` sends a local section `x ⊗ y` to `e x ⊗ y`. -/
theorem gradedTensorHom_tmul {n p : ℤ} (h : n + k = p) (q : TensorIndex n) (X : Cᵒᵖ)
    (x : (Q.piece q.1.1).val.obj X) (y : (N.piece q.1.2).val.obj X) :
    PresheafOfModules.Hom.app (D.gradedTensorHom N h).val X (tmul Q N n q X x y) =
      tmul P N p ⟨(q.1.1 + k, q.1.2), by have := q.2; omega⟩ X
        (PresheafOfModules.Hom.app (D.e (rfl : q.1.1 + k = q.1.1 + k)).hom.val X x) y :=
  (D.shiftBalanced N h).desc_tmul Q N q X x y

/-- `gradedTensorInv` sends a local section `x ⊗ y` to `e⁻¹ x ⊗ y`. -/
theorem gradedTensorInv_tmul {n p : ℤ} (h : n + k = p) (q : TensorIndex p) (X : Cᵒᵖ)
    (x : (P.piece q.1.1).val.obj X) (y : (N.piece q.1.2).val.obj X) :
    PresheafOfModules.Hom.app (D.gradedTensorInv N h).val X (tmul P N p q X x y) =
      tmul Q N n ⟨(q.1.1 - k, q.1.2), by have := q.2; omega⟩ X
        (PresheafOfModules.Hom.app
          (D.e (show q.1.1 - k + k = q.1.1 by omega)).inv.val X x) y :=
  (D.unshiftBalanced N h).desc_tmul P N q X x y

/-- `gradedTensorInv` is a left inverse of `gradedTensorHom`. -/
theorem gradedTensorHom_gradedTensorInv {n p : ℤ} (h : n + k = p) :
    D.gradedTensorHom N h ≫ D.gradedTensorInv N h = 𝟙 _ := by
  refine gradedTensor_hom_ext Q N fun q X x y ↦ ?_
  rw [ShiftFlat.comp_val_app_apply, D.gradedTensorHom_tmul N h q X x y,
    D.gradedTensorInv_tmul N h ⟨(q.1.1 + k, q.1.2), by have := q.2; omega⟩ X,
    D.e_inv_congr (rfl : q.1.1 + k = q.1.1 + k)
      (show q.1.1 + k - k + k = q.1.1 + k by omega)
      (show q.1.1 = q.1.1 + k - k by omega) X,
    tmul_congr_fst Q N (show q.1.1 = q.1.1 + k - k by omega) q.2,
    D.e_inv_hom_apply (rfl : q.1.1 + k = q.1.1 + k) X x]
  rfl

/-- `gradedTensorInv` is a right inverse of `gradedTensorHom`. -/
theorem gradedTensorInv_gradedTensorHom {n p : ℤ} (h : n + k = p) :
    D.gradedTensorInv N h ≫ D.gradedTensorHom N h = 𝟙 _ := by
  refine gradedTensor_hom_ext P N fun q X x y ↦ ?_
  rw [ShiftFlat.comp_val_app_apply, D.gradedTensorInv_tmul N h q X x y,
    D.gradedTensorHom_tmul N h ⟨(q.1.1 - k, q.1.2), by have := q.2; omega⟩ X,
    D.e_hom_congr (show q.1.1 - k + k = q.1.1 by omega)
      (rfl : q.1.1 - k + k = q.1.1 - k + k)
      (show q.1.1 = q.1.1 - k + k by omega) X,
    tmul_congr_fst P N (show q.1.1 = q.1.1 - k + k by omega) q.2,
    D.e_hom_inv_apply (show q.1.1 - k + k = q.1.1 by omega) X x]
  rfl

/-- **Degree `n` of `Q ⊗_A N` is degree `n + k` of `P ⊗_A N`.** -/
noncomputable def gradedTensorIso {n p : ℤ} (h : n + k = p) :
    gradedTensor Q N n ≅ gradedTensor P N p where
  hom := D.gradedTensorHom N h
  inv := D.gradedTensorInv N h
  hom_inv_id := D.gradedTensorHom_gradedTensorInv N h
  inv_hom_id := D.gradedTensorInv_gradedTensorHom N h

/-- The map from degree `n` of `Q ⊗_A N` to degree `n + k` of `P ⊗_A N` is an isomorphism. -/
instance isIso_gradedTensorHom {n p : ℤ} (h : n + k = p) :
    IsIso (D.gradedTensorHom N h) :=
  ⟨D.gradedTensorInv N h, D.gradedTensorHom_gradedTensorInv N h,
    D.gradedTensorInv_gradedTensorHom N h⟩

/-- **The identification of degree `n` of `Q ⊗_A N` with degree `n + k` of `P ⊗_A N` is natural
in `N`.** -/
theorem gradedTensorHom_naturality {N₁ N₂ : LeftGradedModule.{t, m, m} A} (f : N₁ ⟶ N₂)
    {n p : ℤ} (h : n + k = p) :
    D.gradedTensorHom N₁ h ≫ gradedTensorMap P f p =
      gradedTensorMap Q f n ≫ D.gradedTensorHom N₂ h := by
  refine gradedTensor_hom_ext Q N₁ fun q X x y ↦ ?_
  rw [ShiftFlat.comp_val_app_apply, ShiftFlat.comp_val_app_apply,
    D.gradedTensorHom_tmul N₁ h q X x y, gradedTensorMap_tmul,
    gradedTensorMap_tmul, D.gradedTensorHom_tmul N₂ h q X x _]

include D in
/-- **A degree shift of a flat right graded module is flat.** -/
theorem isGradedFlat (hP : IsGradedFlat P) : IsGradedFlat Q := by
  intro N₁ N₂ N₃ f g hfg hSE n
  obtain ⟨z, hz⟩ := hP N₁ N₂ N₃ f g hfg hSE (n + k)
  have key : gradedTensorMap Q f n ≫ gradedTensorMap Q g n ≫
      D.gradedTensorHom N₃ (rfl : n + k = n + k) = 0 := by
    rw [← D.gradedTensorHom_naturality g (rfl : n + k = n + k), ← Category.assoc,
      ← D.gradedTensorHom_naturality f (rfl : n + k = n + k), Category.assoc, z, comp_zero]
  have hzero : gradedTensorMap Q f n ≫ gradedTensorMap Q g n = 0 := by
    rw [← cancel_mono (D.gradedTensorHom N₃ (rfl : n + k = n + k)), zero_comp, Category.assoc]
    exact key
  refine ⟨hzero, ShortComplex.shortExact_of_iso (ShortComplex.isoMk
    (D.gradedTensorIso N₁ (rfl : n + k = n + k))
    (D.gradedTensorIso N₂ (rfl : n + k = n + k))
    (D.gradedTensorIso N₃ (rfl : n + k = n + k))
    (D.gradedTensorHom_naturality f (rfl : n + k = n + k))
    (D.gradedTensorHom_naturality g (rfl : n + k = n + k))).symm hz⟩

end IsGradedShift

end Sheafify

end Graded

/-! ### Degree shifts of right differential graded modules -/

section DifferentialGraded

variable [J.WEqualsLocallyBijective AddCommGrpCat.{m}] [HasSheafify J AddCommGrpCat.{m}]
  {A : DifferentialGradedAlgebra.{t, m} (toRingCat J Osharp)}

/-- A local section `x ⊗ y` of the relative tensor product is linear in the first factor. -/
theorem tmul_zsmul_left (P : GradedModule.{t, m, m} A.toGradedAlgebra)
    (N : LeftGradedModule.{t, m, m} A.toGradedAlgebra) (n : ℤ) (q : TensorIndex n) (X : Cᵒᵖ)
    (c : ℤ) (x : (P.piece q.1.1).val.obj X) (y : (N.piece q.1.2).val.obj X) :
    tmul P N n q X (c • x) y = c • tmul P N n q X x y := by
  show PresheafOfModules.Hom.app (gradedTensorUnit P N n) X
      (PresheafOfModules.Hom.app (gradedTensorπ P N n) X
        (PresheafOfModules.Hom.app (tensorSumι P N q) X ((c • x) ⊗ₜ y))) = _
  rw [PresheafOfModules.app_tmul_zsmul_left]
  simp only [map_zsmul]
  rfl

/-- The differential of a right differential graded module, read as a morphism between the
homogeneous pieces of the underlying right graded module. -/
noncomputable def gdP (P : DifferentialGradedModule.{t, m, m} A) (a : ℤ) :
    (gP P).piece a ⟶ (gP P).piece (a + 1) :=
  P.complex.d a (a + 1)

/-- The differential of a left differential graded module, read as a morphism between the
homogeneous pieces of the underlying left graded module. -/
noncomputable def gdN (N : LeftDifferentialGradedModule.{t, m, m} A) (b : ℤ) :
    (gN N).piece b ⟶ (gN N).piece (b + 1) :=
  N.complex.d b (b + 1)

/-- **The differential of `P ⊗_A N` on a local section `x ⊗ y`**: it is
`dx ⊗ y + (-1)^{deg x} x ⊗ dy`. -/
theorem dgTensor_d_tmul_of_eq (P : DifferentialGradedModule.{t, m, m} A)
    (N : LeftDifferentialGradedModule.{t, m, m} A) {a b n n' : ℤ} (hab : a + b = n)
    (hn : n + 1 = n') (X : Cᵒᵖ)
    (u : ((gP P).piece a).val.obj X) (w : ((gN N).piece b).val.obj X) :
    PresheafOfModules.Hom.app ((dgTensor P N).d n n').val X
        (tmul (gP P) (gN N) n ⟨(a, b), hab⟩ X u w) =
      tmul (gP P) (gN N) n' ⟨(a + 1, b), by omega⟩ X
          (PresheafOfModules.Hom.app (gdP P a).val X u) w +
        (Int.negOnePow a : ℤ) •
          tmul (gP P) (gN N) n' ⟨(a, b + 1), by omega⟩ X u
            (PresheafOfModules.Hom.app (gdN N b).val X w) := by
  subst hn
  have hd : (dgTensor P N).d n (n + 1) =
      (PresheafOfModules.sheafification (R := toRingCat J Osharp)
        (𝟙 (toRingCat J Osharp).obj)).map (dgTensorDiffPre P N n) :=
    congrArg (fun φ ↦ (PresheafOfModules.sheafification (R := toRingCat J Osharp)
      (𝟙 (toRingCat J Osharp).obj)).map φ) (CochainComplex.of_d _ _ n)
  rw [hd]
  refine (PresheafOfModules.unit_naturality_apply (α := 𝟙 (toRingCat J Osharp).obj)
    (φ := dgTensorDiffPre P N n) X _).trans ?_
  refine (congrArg (PresheafOfModules.Hom.app (gradedTensorUnit (gP P) (gN N) (n + 1)) X)
    (PresheafOfModules.hom_congr_apply' (gradedTensorπ_dgTensorDiffPre (P := P) N n) X
      (PresheafOfModules.Hom.app (tensorSumι (gP P) (gN N) (⟨(a, b), hab⟩ : TensorIndex n)) X
        (u ⊗ₜ w)))).trans ?_
  refine (congrArg (fun v ↦ PresheafOfModules.Hom.app
      (gradedTensorUnit (gP P) (gN N) (n + 1)) X
      (PresheafOfModules.Hom.app (gradedTensorπ (gP P) (gN N) (n + 1)) X v))
    (dgTensorSumDiff_tensorSumι_apply P N (⟨(a, b), hab⟩ : TensorIndex n) X u w)).trans ?_
  simp only [map_add, map_zsmul]
  rfl

/-- The datum exhibiting a right differential graded `A`-module `Q` as the degree `k` shift of a
right differential graded `A`-module `P`: a degree shift of the underlying right graded modules
which carries the differential of `Q` to `(-1)^k` times that of `P`. -/
structure IsDifferentialGradedShift (k : ℤ) (Q P : DifferentialGradedModule.{t, m, m} A) where
  /-- The underlying degree shift of right graded modules. -/
  toIsGradedShift : IsGradedShift k (gP Q) (gP P)
  /-- The identification carries the differential of `Q` to `(-1)^k` times that of `P`. -/
  e_d {n p : ℤ} (h : n + k = p) (U : Cᵒᵖ) (x : ((gP Q).piece n).val.obj U) :
    PresheafOfModules.Hom.app
        (toIsGradedShift.e (show n + 1 + k = p + 1 by omega)).hom.val U
        (PresheafOfModules.Hom.app (gdP Q n).val U x) =
      (Int.negOnePow k : ℤ) • PresheafOfModules.Hom.app (gdP P p).val U
        (PresheafOfModules.Hom.app (toIsGradedShift.e h).hom.val U x)

namespace IsDifferentialGradedShift

variable {k : ℤ} {Q P : DifferentialGradedModule.{t, m, m} A}
  (D : IsDifferentialGradedShift k Q P) (N : LeftDifferentialGradedModule.{t, m, m} A)

/-- The identification of degree `n` of `Q ⊗_A N` with degree `n + k` of `P ⊗_A N` carries the
differential of `Q ⊗_A N` to `(-1)^k` times that of `P ⊗_A N`, which is the differential of the
`k`-th shift of that complex. -/
theorem gradedTensorHom_comm (n : ℤ) :
    D.toIsGradedShift.gradedTensorHom (gN N) (rfl : n + k = n + k) ≫
        ((Int.negOnePow k : ℤ) • (dgTensor P N).d (n + k) (n + 1 + k)) =
      (dgTensor Q N).d n (n + 1) ≫
        D.toIsGradedShift.gradedTensorHom (gN N) (rfl : n + 1 + k = n + 1 + k) := by
  refine gradedTensor_hom_ext (gP Q) (gN N) fun q X u w ↦ ?_
  have hsign : (Int.negOnePow k : ℤ) * (Int.negOnePow (q.1.1 + k) : ℤ) =
      (Int.negOnePow q.1.1 : ℤ) := by
    rw [← Units.val_mul, ← Int.negOnePow_add]
    exact congrArg Units.val ((Int.negOnePow_eq_iff _ _).2 ⟨k, by ring⟩)
  have hphi := D.toIsGradedShift.gradedTensorHom_tmul (gN N) (rfl : n + k = n + k) q X u w
  have hdP := dgTensor_d_tmul_of_eq P N
    (show q.1.1 + k + q.1.2 = n + k by have := q.2; omega)
    (show n + k + 1 = n + 1 + k by omega) X
    (PresheafOfModules.Hom.app
      (D.toIsGradedShift.e (rfl : q.1.1 + k = q.1.1 + k)).hom.val X u) w
  have hdQ := dgTensor_d_tmul_of_eq Q N q.2 rfl X u w
  refine ((ShiftFlat.comp_val_app_apply _ _ X _).trans (ShiftFlat.zsmul_val_app _ _ X _)).trans
    (Eq.trans ?_ (ShiftFlat.comp_val_app_apply _ _ X _).symm)
  refine (congrArg (fun z : (gradedTensor (gP P) (gN N) (n + k)).val.obj X ↦
    (Int.negOnePow k : ℤ) • PresheafOfModules.Hom.app
      ((dgTensor P N).d (n + k) (n + 1 + k)).val X z) hphi).trans ?_
  refine (congrArg (fun z : (gradedTensor (gP P) (gN N) (n + 1 + k)).val.obj X ↦
    (Int.negOnePow k : ℤ) • z) hdP).trans ?_
  refine Eq.trans ?_ (congrArg
    (fun z : (gradedTensor (gP Q) (gN N) (n + 1)).val.obj X ↦
      PresheafOfModules.Hom.app (D.toIsGradedShift.gradedTensorHom (gN N)
        (rfl : n + 1 + k = n + 1 + k)).val X z) hdQ).symm
  simp only [map_add, map_zsmul, smul_add, smul_smul, hsign,
    D.toIsGradedShift.gradedTensorHom_tmul (gN N) (rfl : n + 1 + k = n + 1 + k)
      ⟨(q.1.1 + 1, q.1.2), by have := q.2; omega⟩ X,
    D.toIsGradedShift.gradedTensorHom_tmul (gN N) (rfl : n + 1 + k = n + 1 + k)
      ⟨(q.1.1, q.1.2 + 1), by have := q.2; omega⟩ X,
    D.toIsGradedShift.e_hom_congr (show q.1.1 + 1 + k = q.1.1 + k + 1 by omega)
      (rfl : q.1.1 + 1 + k = q.1.1 + 1 + k)
      (show q.1.1 + k + 1 = q.1.1 + 1 + k by omega) X,
    tmul_congr_fst (gP P) (gN N) (show q.1.1 + k + 1 = q.1.1 + 1 + k by omega)
      (show q.1.1 + k + 1 + q.1.2 = n + 1 + k by have := q.2; omega),
    D.e_d (rfl : q.1.1 + k = q.1.1 + k) X u]
  refine congrArg₂ (fun v w' ↦ v + w') ?_ rfl
  exact (tmul_zsmul_left (gP P) (gN N) (n + 1 + k)
    ⟨(q.1.1 + k + 1, q.1.2), by have := q.2; omega⟩ X (Int.negOnePow k : ℤ) _ w).symm

/-- **The relative tensor product of a degree `k` shift is the degree `k` shift of the relative
tensor product**, as complexes of `O`-modules: `Q ⊗_A N ≅ (P ⊗_A N)[k]`. -/
@[ega "II 2.1.2" "special case"]
noncomputable def dgTensorIso :
    dgTensor Q N ≅
      (CochainComplex.shiftFunctor (SheafOfModules.{m} (toRingCat J Osharp)) k).obj
        (dgTensor P N) :=
  HomologicalComplex.Hom.isoOfComponents
    (fun n ↦ D.toIsGradedShift.gradedTensorIso (gN N) (rfl : n + k = n + k))
    (fun i j hij ↦ by
      obtain rfl : i + 1 = j := hij
      exact D.gradedTensorHom_comm N i)

include D in
/-- **A degree shift of a K-flat right differential graded module is K-flat.** -/
theorem isKFlat (hP : IsKFlat P) : IsKFlat Q := by
  intro N hN i
  rw [HomologicalComplex.exactAt_iff_isZero_homology]
  refine (Iso.isZero_iff ((HomologicalComplex.homologyFunctor
    (SheafOfModules.{m} (toRingCat J Osharp)) (ComplexShape.up ℤ) i).mapIso
      (D.dgTensorIso N))).2 ?_
  exact (HomologicalComplex.exactAt_iff_isZero_homology _ i).1
    (acyclic_shiftFunctor_obj k (hP N hN) i)

end IsDifferentialGradedShift

end DifferentialGraded

end RelativeTensor

/-! ### The degree-one shift of a right differential graded module -/

namespace DifferentialGradedModule

variable [J.WEqualsLocallyBijective AddCommGrpCat.{m}] [HasSheafify J AddCommGrpCat.{m}]
  {A : DifferentialGradedAlgebra.{t, m} (toRingCat J Osharp)}

omit [J.WEqualsLocallyBijective AddCommGrpCat.{m}] [HasSheafify J AddCommGrpCat.{m}] in
/-- Degree `n` of the degree-one shift of a right differential graded module is degree `n + 1`
of that module. -/
theorem shift_piece_eq (P : DifferentialGradedModule.{t, m, m} A) {n p : ℤ} (h : n + 1 = p) :
    (RelativeTensor.gP (shift P)).piece n = (RelativeTensor.gP P).piece p :=
  (congrArg (fun T : CochainComplex (SheafOfModules.{m} (toRingCat J Osharp)) ℤ ↦ T.X n)
    (shiftPackage P).shifted_complex).trans (congrArg P.complex.X h)

/-- **The degree-one shift of a right differential graded module is its degree-one shift as a
right graded module**: the identification of `(P[1])^n` with `P^{n + 1}` carries the right
action. -/
noncomputable def isGradedShift_shift (P : DifferentialGradedModule.{t, m, m} A) :
    RelativeTensor.IsGradedShift 1 (RelativeTensor.gP (shift P)) (RelativeTensor.gP P) where
  e h := eqToIso (shift_piece_eq P h)
  e_smul {n i p} h U x y := by
    have hβ : HEq (((shift P).mul n i).app U) ((P.mul p i).app U) := by
      subst h
      exact (shiftPackage P).shifted_action n i U
    exact SheafOfModules.ShiftFlat.bilinear_transport (shift_piece_eq P h)
      (shift_piece_eq P (show n + i + 1 = p + i by omega))
      ((shift P).mul n i) (P.mul p i) U hβ x y

omit [J.WEqualsLocallyBijective AddCommGrpCat.{m}] [HasSheafify J AddCommGrpCat.{m}] in
/-- The differential of the degree-one shift is `-1` times the differential of the module, read
through the identification of the homogeneous pieces. -/
theorem shift_gdP_app (P : DifferentialGradedModule.{t, m, m} A) (n : ℤ) (U : Cᵒᵖ)
    (x : ((RelativeTensor.gP (shift P)).piece n).val.obj U) :
    PresheafOfModules.Hom.app
        (eqToHom (shift_piece_eq P (show n + 1 + 1 = n + 1 + 1 from rfl))).val U
        (PresheafOfModules.Hom.app (RelativeTensor.gdP (shift P) n).val U x) =
      (Int.negOnePow 1 : ℤ) • PresheafOfModules.Hom.app
        (RelativeTensor.gdP P (n + 1)).val U
        (PresheafOfModules.Hom.app
          (eqToHom (shift_piece_eq P (show n + 1 = n + 1 from rfl))).val U x) :=
  (SheafOfModules.ShiftFlat.d_val_app_of_eq (shiftPackage P).shifted_complex n (n + 1) U
    x).trans (SheafOfModules.ShiftFlat.zsmul_val_app _ _ U _)

/-- **The degree-one shift of a right differential graded module is its degree-one shift as a
differential graded module**: the identification of `(P[1])^n` with `P^{n + 1}` carries the
right action, and carries the differential of `P[1]` to `-1` times that of `P`. -/
noncomputable def isDifferentialGradedShift_shift (P : DifferentialGradedModule.{t, m, m} A) :
    RelativeTensor.IsDifferentialGradedShift 1 (shift P) P where
  toIsGradedShift := isGradedShift_shift P
  e_d {n p} h U x := by
    subst h
    exact shift_gdP_app P n U x

/-- **The degree-one shift of a right differential graded module whose underlying right graded
module is flat has flat underlying right graded module.** -/
theorem isGradedFlat_shift (P : DifferentialGradedModule.{t, m, m} A)
    (hP : RelativeTensor.IsGradedFlat (RelativeTensor.gP P)) :
    RelativeTensor.IsGradedFlat (RelativeTensor.gP (shift P)) :=
  (isGradedShift_shift P).isGradedFlat hP

/-- **The degree-one shift of a K-flat right differential graded module is K-flat.** -/
theorem isKFlat_shift (P : DifferentialGradedModule.{t, m, m} A)
    (hP : RelativeTensor.IsKFlat P) : RelativeTensor.IsKFlat (shift P) :=
  (isDifferentialGradedShift_shift P).isKFlat hP

end DifferentialGradedModule

end SheafOfModules

end
