module

public import StacksFrontier.Algebra.Category.ModuleCat.Sheaf.FreeSheafStalkBasis
public import StacksFrontier.Algebra.Category.ModuleCat.Sheaf.KoszulStalk
public import Mathlib.Algebra.Homology.Additive
public import StacksCore.Tactic.StacksAttribute

/-!
# The Koszul differential of a sheaf of modules, and its stalks

Let `O♯` be a sheaf of commutative rings on a site `(C, J)`, let `F` be a sheaf of `O♯`-modules
and let `A` be a package of the tensor, exterior and symmetric algebras of `F` in the sense of
Stacks Section 17.21. Stacks Tag 062K attaches to a morphism `φ : F ⟶ O♯` the *Koszul complex*
of `φ`: the exterior algebra `⋀(F)` equipped with the unique degree `-1` derivation `d` whose
value on a degree-one generator is `φ` followed by the inclusion of the structure sheaf in
degree zero.

This file takes that data as a hypothesis — `Stacks.RegularSequence.KoszulChainData` — and
proves the two things a stalkwise comparison of Koszul complexes needs:

* **the alternating-sum formula**: on an ordered exterior product of tautological generators of a
  finite free sheaf of modules, `d` is the usual alternating sum
  `d(e_{i₀} ∧ ⋯ ∧ e_{i_n}) = ∑ₖ (-1)^k f_{i_k} · (e_{i₀} ∧ ⋯ ∧ ê_{i_k} ∧ ⋯ ∧ e_{i_n})`;
* **differential compatibility at a stalk**: under the comparison
  `(⋀ⁿ(O♯ʳ))_x ≅ ⋀ⁿ_{O_x}((O_x)ʳ)` of Stacks Tag 01CH, the map induced on stalks by `d` is the
  ring-level Koszul differential of the sequence of germs.

The second is the statement the stalkwise regularity criterion of Stacks Tag 063C rests on.

## Why the Koszul data is a hypothesis

Stacks Tag 062K asserts the existence and uniqueness of the Koszul differential; that existence
theorem is not proved in this development, so there is no term of its type to work with. Taking
the differential, the Leibniz rule, the value on a generator and the associated chain complex as
hypotheses is therefore forced, and it is also *stronger* than working with a chosen term: every
statement below holds of any Koszul differential whatsoever. Six fields are taken — `d`,
`d_mul`, `d_generator`, `chain`, `chain_X`, `chain_d` — rather than the whole package of Tag
062K, which is again strictly stronger: square-zeroness, graded commutativity, uniqueness and
the differential-graded-algebra presentation are never used.

## Main definitions

* `Stacks.RegularSequence.KoszulChainData`: the Koszul differential of `φ` as data — the
  degree-lowering morphisms, the graded Leibniz rule, the value on a degree-one generator, and
  the associated `ℤ`-indexed chain complex of sheaves of modules.
* `Stacks.RegularSequence.extTotal`: the exterior algebra read as a graded algebra of presheaves
  of modules, so that `Stacks.GradedAlgebra.Total` — the ungraded realization, an honest ring of
  sections — applies to it.
* `Stacks.RegularSequence.KoszulChainData.dTotal`: the Koszul differential assembled into a
  single linear endomorphism of that ring of sections.
* `Stacks.RegularSequence.KoszulChainData.dNat`: the Koszul differential as a morphism
  `⋀^{n+1} F ⟶ ⋀ⁿ F` of the nonnegative-degree exterior powers.
* `Stacks.RegularSequence.stalkAddHom` and `stalkLin`: the map induced on stalks by a morphism of
  presheaves of modules, as an additive map and as a map of modules over the stalk of `O♯`.

## Main results

* `Stacks.RegularSequence.KoszulChainData.dTotal_mul_degOne`: **the Leibniz rule in the ungraded
  realization**, for a left factor of degree one. Every degree transport of the graded Leibniz
  rule disappears here, because the inclusion of a homogeneous component into the ungraded
  realization absorbs it.
* `Stacks.RegularSequence.KoszulChainData.dTotal_incl_homogeneousProdLeft`: **the alternating-sum
  formula**, in the ungraded realization, for an ordered product of degree-one sections whose
  differentials are multiples of the unit.
* `Stacks.RegularSequence.KoszulChainData.dNat_exteriorBasisSection`: the same formula for the
  exterior products of the tautological generators of a finite free sheaf of modules, read in
  the graded piece.
* `Stacks.RegularSequence.exteriorKoszulStalkEquiv_germ_dNat`: the germ of the differential of an
  exterior basis product is the ring-level Koszul differential of the corresponding wedge of
  standard basis vectors.
* `Stacks.RegularSequence.exteriorKoszulStalkEquiv_stalkLin`: **differential compatibility at a
  stalk** — the map induced on stalks by the Koszul differential is, under the comparison of Tag
  01CH, the Koszul differential of the sequence of germs.
* `Stacks.RegularSequence.KoszulChainData.chain_d_natCast`: the differential of the associated
  chain complex from degree `n + 1` to degree `n` is `dNat n`, so the stalk statement is a
  statement about that complex.
* `Stacks.RegularSequence.KoszulChainData.isZero_chain_X_of_neg`: that complex vanishes in
  negative degrees.

## Implementation notes

What is forced and what is chosen.

* **The ungraded realization is the whole technique.** The graded Leibniz rule of Tag 062K is
  stated with two `Stacks.degCast` degree transports, and the ordered exterior product
  `Stacks.RegularSequence.exteriorBasisSection` carries one more in its own definition. Pushing
  the whole computation into `Stacks.GradedAlgebra.Total`, where multiplication is the honest
  ring multiplication of a `DirectSum.GRing` and `Stacks.GradedAlgebra.incl_degCast` erases every
  transport, makes the induction *cast-free*: the Leibniz rule becomes
  `D(xy) = (Dx)y - x(Dy)` for `x` of degree one, and the index bookkeeping is then exactly the
  one `Koszul.contraction_ιMulti` performs on the ring side
  (`Fin.succ_succAbove_zero` and `Fin.succ_succAbove_succ`). Returning to the graded piece is one
  application of injectivity of `Stacks.GradedAlgebra.incl`.
* The single universe `u` carrying the space, the sections of `O♯` and the sections of every
  module in the last two sections is forced by `TopCat.Presheaf.stalk`, exactly as in
  `StacksFrontier.Algebra.Category.ModuleCat.Sheaf.KoszulStalk`. The site universes of the first
  section, which mentions no stalk, are independent. Nothing is narrowed.
* The map induced on stalks is built here rather than taken from
  `AlgebraicGeometry.SheafOfModules.stalkMap`
  (`StacksFrontier.Topology.Sheaves.Modules.Colimits`, which carries Tag 01AH) because that one is
  linear over the stalk of the `RingCat`-valued presheaf `O♯ ⋙ forget₂ CommRingCat RingCat`,
  whereas the module structure Mathlib puts on the stalk of a presheaf of modules — and hence
  `SheafOfModules.TensorExteriorSymmetricAlgebras.exteriorPowerStalkEquiv` and everything in
  `FreeSheafStalkBasis` — is over the stalk of the `CommRingCat`-valued `O♯`. The two stalks are
  isomorphic and not equal. `Stacks.RegularSequence.stalkLin` is the `CommRingCat`-stalk form;
  its scalar compatibility goes through `Stacks.SheafOfModules.germAddHom_smul`, i.e.
  `PresheafOfModules.germ_smul` used as a term and never `map_smul`, which is what keeps this
  file free of any raised transparency or heartbeat option.
* `Stacks.RegularSequence.unitScalar` is a `def` with an ascribed result type, not a type
  ascription: `(SheafOfModules.unit R).val.obj U` and `R.obj.obj U` are the same type, but
  instance search does not unfold the former, so a type ascription would not retype the scalar
  for the `Module` instance.
* The `variable` line of the last section writes `KoszulChainData.{u, u, u}` rather than
  `KoszulChainData`. This is not a narrowing — all three universes of the structure are `u` there
  anyway, forced by the stalk — but an elaboration-order workaround: in a `variable` binder whose
  earlier entries fix the site data only through the explicit bundle argument, the structure's
  three universe metavariables are solved as `0` before the bundle is looked at, and the binder
  fails with a `Quiver.Hom.{0, 1}` type mismatch. Writing them out fixes it; naming the arguments
  (`(A := A)`) does not.
* `d_generator` is stated exactly as Tag 062K states it, through the degree-zero identification
  of the tensor algebra and the exterior quotient map;
  `Stacks.RegularSequence.KoszulChainData.d_exteriorGenerator` is the form actually used, where
  the value is a scalar multiple of the exterior unit.
* No `@[stacks]` attribute. Tag 062K asserts existence and uniqueness of the Koszul
  differential, and this file proves neither: it assumes the differential and computes with it.
  The germ formula it feeds is the degree-`n` exterior clause of Tag 01CH, carried by
  `SheafOfModules.exteriorAlgebra_stalk` in
  `StacksFrontier.Algebra.Category.ModuleCat.Sheaf.ExteriorStalkUngraded`.

## References

* [Stacks Project, Section 17.21](https://stacks.math.columbia.edu/tag/01CF)
* [Stacks Project, Tag 01CH](https://stacks.math.columbia.edu/tag/01CH)
* [Stacks Project, Tag 062K](https://stacks.math.columbia.edu/tag/062K)
* [Stacks Project, Tag 063C](https://stacks.math.columbia.edu/tag/063C)
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits CategoryTheory.Sheaf Opposite TopologicalSpace

universe v u w

namespace Stacks.RegularSequence

/-! ### The Koszul differential over an arbitrary bundle of algebras -/

section General

variable {C : Type u} [Category.{v} C] {J : GrothendieckTopology C}
  [J.HasSheafCompose (forget₂ CommRingCat.{w} RingCat.{w})]
  {Osharp : Sheaf J CommRingCat.{w}}
  [J.WEqualsLocallyBijective AddCommGrpCat.{w}] [HasWeakSheafify J AddCommGrpCat.{w}]
  {F : SheafOfModules.{w} (toRingCat J Osharp)}

/-- The exterior algebra of a bundle of algebras, read as a graded algebra of presheaves of
modules. This is the form in which the ungraded realization `Stacks.GradedAlgebra.Total` — the
direct sum of the homogeneous components over an object of the site, with its ring structure —
applies to it. -/
noncomputable abbrev extTotal (A : SheafOfModules.TensorExteriorSymmetricAlgebras J F) :
    Stacks.GradedAlgebra fun i : ℤ => (A.exterior.piece i).val :=
  A.exterior.toPresheafGradedAlgebra

variable {A : SheafOfModules.TensorExteriorSymmetricAlgebras J F}

/-- The inclusion of a homogeneous component into the ungraded realization commutes with
negation. -/
theorem extIncl_neg (U : Cᵒᵖ) (i : ℤ) (x : (A.exterior.piece i).val.obj U) :
    (extTotal A).incl i (-x) = -(extTotal A).incl i x := by
  have h := Stacks.GradedAlgebra.incl_add (extTotal A) (X := U) i x (-x)
  rw [add_neg_cancel, Stacks.GradedAlgebra.incl_zero] at h
  exact eq_neg_of_add_eq_zero_left (by rw [add_comm]; exact h.symm)

/-- Multiplication in the ungraded realization, written with the multiplication of the bundle's
exterior algebra. -/
theorem extIncl_mul (U : Cᵒᵖ) (i j : ℤ) (x : (A.exterior.piece i).val.obj U)
    (y : (A.exterior.piece j).val.obj U) :
    (extTotal A).incl i x * (extTotal A).incl j y =
      (extTotal A).incl (i + j) ((A.exterior.mul i j).app U x y) :=
  Stacks.GradedAlgebra.incl_mul_incl (extTotal A) i j x y

/-- The unit of the ungraded realization is the exterior unit in degree zero. -/
theorem extOne_eq_incl (U : Cᵒᵖ) :
    (1 : (extTotal A).Total U) = (extTotal A).incl 0 (A.exterior.one.eval U) :=
  Stacks.GradedAlgebra.one_eq_incl (extTotal A) U

/-- The ordered left-handed product of degree-one sections, read in the ungraded realization,
splits off its first factor. The degree transport of
`Stacks.GradedAlgebra.homogeneousProdLeft` disappears. -/
theorem extIncl_homogeneousProdLeft_succ (U : Cᵒᵖ) (n : ℕ)
    (z : Fin (n + 1) → (A.exterior.piece 1).val.obj U) :
    (extTotal A).incl ((n + 1 : ℕ) : ℤ) ((extTotal A).homogeneousProdLeft U (n + 1) z) =
      (extTotal A).incl 1 (z 0) *
        (extTotal A).incl ((n : ℕ) : ℤ)
          ((extTotal A).homogeneousProdLeft U n fun j => z j.succ) := by
  rw [extIncl_mul, Stacks.GradedAlgebra.homogeneousProdLeft,
    Stacks.GradedAlgebra.incl_degCast (extTotal A)
      (show (1 : ℤ) + (n : ℤ) = ((n + 1 : ℕ) : ℤ) by omega)]
  rfl

/-- The empty ordered product is the unit of the ungraded realization. -/
theorem extIncl_homogeneousProdLeft_zero (U : Cᵒᵖ)
    (z : Fin 0 → (A.exterior.piece 1).val.obj U) :
    (extTotal A).incl ((0 : ℕ) : ℤ) ((extTotal A).homogeneousProdLeft U 0 z) =
      (1 : (extTotal A).Total U) :=
  (extOne_eq_incl U).symm

/-- Reindexing an ordered product after dropping the factor at `k.succ`: the first factor is
unchanged and the remaining ones are the product over the drop at `k`. This is the index
bookkeeping of `Fin.succAbove` on the sheaf side. -/
theorem extIncl_mul_succAbove_succ (U : Cᵒᵖ) (m : ℕ)
    (z : Fin (m + 2) → (A.exterior.piece 1).val.obj U) (k : Fin (m + 1)) :
    (extTotal A).incl 1 (z 0) *
        (extTotal A).incl ((m : ℕ) : ℤ)
          ((extTotal A).homogeneousProdLeft U m fun j => z (k.succAbove j).succ) =
      (extTotal A).incl ((m + 1 : ℕ) : ℤ)
        ((extTotal A).homogeneousProdLeft U (m + 1) fun j => z (k.succ.succAbove j)) := by
  rw [extIncl_homogeneousProdLeft_succ U m fun j => z (k.succ.succAbove j)]
  simp only [Fin.succ_succAbove_zero, Fin.succ_succAbove_succ]

omit [J.WEqualsLocallyBijective AddCommGrpCat.{w}] [HasWeakSheafify J AddCommGrpCat.{w}] in
/-- Transport along an equality of degrees, read on sections, is `Stacks.degCast`. -/
theorem eqToHom_val_app_eq_degCast (Y : ℤ → SheafOfModules.{w} (toRingCat J Osharp))
    {i j : ℤ} (h : i = j) (U : Cᵒᵖ) (y : (Y i).val.obj U) :
    (eqToHom (congrArg Y h)).val.app U y =
      Stacks.degCast (F := fun k => ((Y k).val.obj U : Type w)) h y := by
  subst h; rfl

/-- The inclusion of a homogeneous component into the ungraded realization, bundled as a linear
map so that `map_sum` and `map_smul` apply to it. -/
noncomputable def extInclLin (U : Cᵒᵖ) (i : ℤ) :
    (A.exterior.piece i).val.obj U →ₗ[(toRingCat J Osharp).obj.obj U] (extTotal A).Total U where
  toFun := (extTotal A).incl i
  map_add' := Stacks.GradedAlgebra.incl_add (extTotal A) i
  map_smul' r x := Stacks.GradedAlgebra.incl_smul (extTotal A) i r x

/-- `extInclLin U i` is the inclusion of the degree-`i` component. -/
theorem extInclLin_apply (U : Cᵒᵖ) (i : ℤ) (x : (A.exterior.piece i).val.obj U) :
    extInclLin (A := A) U i x = (extTotal A).incl i x := rfl

/-- The scalar attached to a local section by a morphism into the unit sheaf of modules.

This is a `def` with an ascribed result type, not a type ascription: `(SheafOfModules.unit R)`
`.val.obj U` and `R.obj.obj U` are the same type, but instance search does not unfold the former,
so a type ascription would leave the scalar unusable for the `Module` instance. -/
noncomputable def unitScalar (φ : F ⟶ SheafOfModules.unit (toRingCat J Osharp)) (U : Cᵒᵖ)
    (e : F.val.obj U) : (toRingCat J Osharp).obj.obj U :=
  φ.val.app U e

omit [J.WEqualsLocallyBijective AddCommGrpCat.{w}] [HasWeakSheafify J AddCommGrpCat.{w}] in
/-- An isomorphism of sheaves of modules is inverse to its inverse, read on sections. -/
theorem iso_hom_val_app_inv_val_app {M N : SheafOfModules.{w} (toRingCat J Osharp)} (i : M ≅ N)
    (U : Cᵒᵖ) (y : N.val.obj U) : i.hom.val.app U (i.inv.val.app U y) = y := by
  have h : (SheafOfModules.Hom.val (i.inv ≫ i.hom)).app U y
      = (SheafOfModules.Hom.val (𝟙 N)).app U y := by rw [i.inv_hom_id]
  exact h

/-- **The Koszul differential of `φ` as data**: the degree-lowering morphisms of the exterior
algebra, the graded Leibniz rule, the value on a degree-one generator, and the `ℤ`-indexed chain
complex they assemble into.

These are six of the fields of the package Stacks Tag 062K constructs. Taking them as a
hypothesis is forced — the existence theorem of Tag 062K is not available here — and is stronger
than working with a chosen package: nothing below uses square-zeroness, graded commutativity,
uniqueness, or the differential-graded-algebra presentation. -/
structure KoszulChainData (A : SheafOfModules.TensorExteriorSymmetricAlgebras J F)
    (φ : F ⟶ SheafOfModules.unit (toRingCat J Osharp)) where
  /-- The differential lowers the exterior degree by one. -/
  d : ∀ n : ℤ, A.exterior.piece n ⟶ A.exterior.piece (n - 1)
  /-- The graded Leibniz rule on local homogeneous sections. -/
  d_mul : ∀ (n m : ℤ) (U : Cᵒᵖ) (a : (A.exterior.piece n).val.obj U)
      (b : (A.exterior.piece m).val.obj U),
    (d (n + m)).val.app U ((A.exterior.mul n m).app U a b) =
      Stacks.degCast (F := fun q : ℤ => ((A.exterior.piece q).val.obj U : Type w))
          (by ring : (n - 1) + m = n + m - 1)
          ((A.exterior.mul (n - 1) m).app U ((d n).val.app U a) b) +
        (Int.negOnePow n : ℤ) •
          Stacks.degCast (F := fun q : ℤ => ((A.exterior.piece q).val.obj U : Type w))
            (by ring : n + (m - 1) = n + m - 1)
            ((A.exterior.mul n (m - 1)).app U a ((d m).val.app U b))
  /-- On a degree-one generator the differential is the given module map, followed by the
  inclusion of the structure sheaf in degree zero. -/
  d_generator : ∀ (U : Cᵒᵖ) (e : F.val.obj U),
    (d 1).val.app U (A.exteriorGenerator.val.app U e) =
      (A.tensorToExterior.app 0).val.app U
        ((A.tensorPieceIso 0).inv.val.app U (φ.val.app U e))
  /-- The associated homological chain complex. -/
  chain : ChainComplex (SheafOfModules.{w} (toRingCat J Osharp)) ℤ
  /-- Its degree-`n` term is the degree-`n` exterior power. -/
  chain_X : ∀ n : ℤ, chain.X n = A.exterior.piece n
  /-- Its differential is the Koszul differential on the exterior power. -/
  chain_d : ∀ n : ℤ,
    eqToHom (chain_X n).symm ≫ chain.d n (n - 1) ≫ eqToHom (chain_X (n - 1)) = d n

namespace KoszulChainData

variable {φ : F ⟶ SheafOfModules.unit (toRingCat J Osharp)} (K : KoszulChainData A φ)

/-- The degree-`i` component of the Koszul differential, followed by the inclusion into the
ungraded realization, as a linear map. -/
noncomputable def dTotalLin (U : Cᵒᵖ) (i : ℤ) :
    (A.exterior.piece i).val.obj U →ₗ[(toRingCat J Osharp).obj.obj U] (extTotal A).Total U where
  toFun x := (extTotal A).incl (i - 1) ((K.d i).val.app U x)
  map_add' x y := by rw [map_add, Stacks.GradedAlgebra.incl_add]
  map_smul' r x := by rw [RingHom.id_apply, map_smul, Stacks.GradedAlgebra.incl_smul]

/-- **The Koszul differential in the ungraded realization**: the linear endomorphism of the ring
of sections of the exterior algebra over `U` assembled from the homogeneous components of `d`. -/
noncomputable def dTotal (U : Cᵒᵖ) :
    (extTotal A).Total U →ₗ[(toRingCat J Osharp).obj.obj U] (extTotal A).Total U :=
  DirectSum.toModule _ ℤ _ (K.dTotalLin U)

/-- On the image of a homogeneous component of degree `i`, the ungraded differential is the
degree-`i` component of `d` followed by the inclusion of degree `i - 1`. -/
theorem dTotal_incl (U : Cᵒᵖ) (i : ℤ) (x : (A.exterior.piece i).val.obj U) :
    K.dTotal U ((extTotal A).incl i x) =
      (extTotal A).incl (i - 1) ((K.d i).val.app U x) :=
  DirectSum.toModule_lof _ (φ := K.dTotalLin U) i x

/-- **The Leibniz rule in the ungraded realization**, for a left factor of degree one. Both
degree transports of the graded Leibniz rule are absorbed by
`Stacks.GradedAlgebra.incl_degCast`, so this identity is cast-free. -/
theorem dTotal_mul_degOne (U : Cᵒᵖ) (m : ℤ) (a : (A.exterior.piece 1).val.obj U)
    (b : (A.exterior.piece m).val.obj U) :
    K.dTotal U ((extTotal A).incl 1 a * (extTotal A).incl m b) =
      K.dTotal U ((extTotal A).incl 1 a) * (extTotal A).incl m b -
        (extTotal A).incl 1 a * K.dTotal U ((extTotal A).incl m b) := by
  rw [extIncl_mul, K.dTotal_incl, K.d_mul 1 m U a b,
    Stacks.GradedAlgebra.incl_add, Int.negOnePow_one,
    show ((-1 : ℤˣ) : ℤ) = -1 from rfl, neg_one_zsmul, extIncl_neg,
    Stacks.GradedAlgebra.incl_degCast, Stacks.GradedAlgebra.incl_degCast,
    ← extIncl_mul, ← extIncl_mul, K.dTotal_incl, K.dTotal_incl]
  exact (sub_eq_add_neg _ _).symm

/-- **The differential of a degree-one generator is its scalar times the exterior unit.** This is
the `d_generator` field read through the degree-zero identification of the exterior algebra. -/
theorem d_exteriorGenerator (U : Cᵒᵖ) (e : F.val.obj U) :
    (K.d 1).val.app U (A.exteriorGenerator.val.app U e) =
      unitScalar φ U e • A.exterior.one.eval U := by
  have hc : A.tensorPieceZeroIsoUnit.hom.val.app U
      ((A.tensorPieceIso 0).inv.val.app U (φ.val.app U e)) = unitScalar φ U e :=
    iso_hom_val_app_inv_val_app (A.tensorPieceIso 0) U (φ.val.app U e)
  rw [K.d_generator U e, ← A.tensorPieceZeroIsoUnit_smul_one U _ _ hc, map_smul,
    A.tensorToExterior.map_one U]

/-- The ungraded differential kills the unit, because the exterior algebra has no sections in
degree `-1`. -/
theorem dTotal_one (U : Cᵒᵖ) : K.dTotal U (1 : (extTotal A).Total U) = 0 := by
  rw [extOne_eq_incl, K.dTotal_incl,
    A.exteriorPiece_eq_zero_of_neg (0 - 1) (by norm_num) U
      ((K.d 0).val.app U (A.exterior.one.eval U))]
  exact Stacks.GradedAlgebra.incl_zero (extTotal A) _

/-- The ungraded differential of a degree-one section whose differential is a multiple of the
unit. -/
theorem dTotal_incl_one_of_eq (U : Cᵒᵖ) (a : (A.exterior.piece 1).val.obj U)
    (c : (toRingCat J Osharp).obj.obj U)
    (ha : (K.d 1).val.app U a = c • A.exterior.one.eval U) :
    K.dTotal U ((extTotal A).incl 1 a) = c • (1 : (extTotal A).Total U) := by
  rw [K.dTotal_incl, ha, Stacks.GradedAlgebra.incl_smul]
  exact congrArg (fun t : (extTotal A).Total U => c • t) (extOne_eq_incl U).symm

/-- **The alternating-sum formula for the Koszul differential on an ordered product of degree-one
sections**, in the ungraded realization.

This is the induction from the graded Leibniz rule and the value of the differential on a
generator. It runs in the ungraded realization precisely so that no degree transport occurs: the
index bookkeeping is then `Fin.succ_succAbove_zero` and `Fin.succ_succAbove_succ`, exactly as in
the ring-level `Koszul.contraction_ιMulti`. -/
theorem dTotal_incl_homogeneousProdLeft (U : Cᵒᵖ) (n : ℕ) :
    ∀ (z : Fin (n + 1) → (A.exterior.piece 1).val.obj U)
      (g : Fin (n + 1) → (toRingCat J Osharp).obj.obj U),
      (∀ j, (K.d 1).val.app U (z j) = g j • A.exterior.one.eval U) →
      K.dTotal U ((extTotal A).incl ((n + 1 : ℕ) : ℤ)
          ((extTotal A).homogeneousProdLeft U (n + 1) z)) =
        ∑ k : Fin (n + 1), ((-1 : (toRingCat J Osharp).obj.obj U) ^ (k : ℕ) * g k) •
          (extTotal A).incl ((n : ℕ) : ℤ)
            ((extTotal A).homogeneousProdLeft U n fun j => z (k.succAbove j)) := by
  induction n with
  | zero =>
    intro z g hz
    rw [extIncl_homogeneousProdLeft_succ U 0 z, extIncl_homogeneousProdLeft_zero,
      mul_one, K.dTotal_incl_one_of_eq U (z 0) (g 0) (hz 0), Fin.sum_univ_one,
      extIncl_homogeneousProdLeft_zero]
    norm_num
  | succ m ih =>
    intro z g hz
    have hsum : (extTotal A).incl 1 (z 0) *
        (∑ k : Fin (m + 1), ((-1 : (toRingCat J Osharp).obj.obj U) ^ (k : ℕ) * g k.succ) •
          (extTotal A).incl ((m : ℕ) : ℤ)
            ((extTotal A).homogeneousProdLeft U m fun j => z (k.succAbove j).succ)) =
        ∑ k : Fin (m + 1), ((-1 : (toRingCat J Osharp).obj.obj U) ^ (k : ℕ) * g k.succ) •
          (extTotal A).incl ((m + 1 : ℕ) : ℤ)
            ((extTotal A).homogeneousProdLeft U (m + 1) fun j => z (k.succ.succAbove j)) := by
      rw [Finset.mul_sum]
      exact Finset.sum_congr rfl fun k _ => by
        rw [Stacks.GradedAlgebra.mul_smul_eq, extIncl_mul_succAbove_succ U m z k]
    have hrhs : ∑ k : Fin (m + 1 + 1),
          ((-1 : (toRingCat J Osharp).obj.obj U) ^ (k : ℕ) * g k) •
            (extTotal A).incl ((m + 1 : ℕ) : ℤ)
              ((extTotal A).homogeneousProdLeft U (m + 1) fun j => z (k.succAbove j)) =
        g 0 • (extTotal A).incl ((m + 1 : ℕ) : ℤ)
            ((extTotal A).homogeneousProdLeft U (m + 1) fun j => z j.succ) -
          ∑ k : Fin (m + 1), ((-1 : (toRingCat J Osharp).obj.obj U) ^ (k : ℕ) * g k.succ) •
            (extTotal A).incl ((m + 1 : ℕ) : ℤ)
              ((extTotal A).homogeneousProdLeft U (m + 1) fun j => z (k.succ.succAbove j)) := by
      rw [Fin.sum_univ_succ, Fin.succAbove_zero, sub_eq_add_neg, ← Finset.sum_neg_distrib]
      simp only [Fin.val_zero, pow_zero, one_mul, Fin.val_succ, pow_succ]
      refine congrArg (fun t => g 0 • (extTotal A).incl ((m + 1 : ℕ) : ℤ)
          ((extTotal A).homogeneousProdLeft U (m + 1) fun j => z j.succ) + t) ?_
      refine Finset.sum_congr rfl fun k _ => ?_
      rw [← neg_smul]
      congr 1
      ring
    rw [extIncl_homogeneousProdLeft_succ U (m + 1) z, K.dTotal_mul_degOne,
      K.dTotal_incl_one_of_eq U (z 0) (g 0) (hz 0),
      ih (fun j => z j.succ) (fun j => g j.succ) (fun j => hz j.succ),
      Stacks.GradedAlgebra.smul_mul_eq, one_mul, hsum, hrhs]

/-- **The Koszul differential as a morphism of the nonnegative-degree exterior powers**,
`⋀^{n+1} F ⟶ ⋀ⁿ F`. The degree transport is part of the definition: `d` lowers
`((n + 1 : ℕ) : ℤ)` to `((n + 1 : ℕ) : ℤ) - 1`, which is only propositionally
`((n : ℕ) : ℤ)`. -/
noncomputable def dNat (n : ℕ) : A.exteriorPower (n + 1) ⟶ A.exteriorPower n :=
  K.d ((n + 1 : ℕ) : ℤ) ≫
    eqToHom (congrArg A.exterior.piece (show ((n + 1 : ℕ) : ℤ) - 1 = ((n : ℕ) : ℤ) by omega))

/-- The inclusion of `K.dNat n y` into the ungraded realization is the ungraded differential
of the inclusion of `y`. -/
theorem extIncl_dNat (U : Cᵒᵖ) (n : ℕ) (y : (A.exteriorPower (n + 1)).val.obj U) :
    (extTotal A).incl ((n : ℕ) : ℤ) ((K.dNat n).val.app U y) =
      K.dTotal U ((extTotal A).incl ((n + 1 : ℕ) : ℤ) y) := by
  have h : ((n + 1 : ℕ) : ℤ) - 1 = ((n : ℕ) : ℤ) := by omega
  rw [K.dTotal_incl, dNat, SheafOfModules.comp_val]
  exact (congrArg ((extTotal A).incl _) (eqToHom_val_app_eq_degCast A.exterior.piece h U _)).trans
    (Stacks.GradedAlgebra.incl_degCast (extTotal A) h _)

/-- **The differential of the associated chain complex, in nonnegative degrees**: from degree
`n + 1` to degree `n` it is `Stacks.RegularSequence.KoszulChainData.dNat`. This is what makes the
stalk comparison below a statement about `chain`. -/
theorem chain_d_natCast (n : ℕ) :
    eqToHom (K.chain_X ((n + 1 : ℕ) : ℤ)).symm ≫ K.chain.d ((n + 1 : ℕ) : ℤ) ((n : ℕ) : ℤ) ≫
        eqToHom (K.chain_X ((n : ℕ) : ℤ)) = K.dNat n := by
  have h : ((n + 1 : ℕ) : ℤ) - 1 = ((n : ℕ) : ℤ) := by omega
  rw [dNat, ← K.chain_d ((n + 1 : ℕ) : ℤ),
    ← HomologicalComplex.d_comp_XIsoOfEq_hom K.chain h ((n + 1 : ℕ) : ℤ)]
  simp only [HomologicalComplex.XIsoOfEq, eqToIso.hom, Category.assoc, eqToHom_trans]

/-- **The associated chain complex vanishes in negative degrees.** This is the ingredient a
comparison of `ℤ`-indexed complexes needs in order to be concentrated in nonnegative degrees; it
could not be stated before the chain data was available, since it is a statement about
`chain`. -/
theorem isZero_chain_X_of_neg {n : ℤ} (hn : n < 0) : IsZero (K.chain.X n) := by
  rw [K.chain_X n]
  exact Stacks.SheafOfModules.isZero_exteriorPiece_of_neg A hn

end KoszulChainData

end General

/-! ### The map induced on stalks by a morphism of presheaves of modules -/

section Stalks

open Stacks.SheafOfModules

variable {X : TopCat.{u}} {R : X.Presheaf CommRingCat.{u}}
  {M N : PresheafOfModules.{u} (R ⋙ forget₂ CommRingCat RingCat)}

/-- Every element of the stalk is the germ of a section, with the section read in the module
spelling `M.obj (op U)` rather than in `M.presheaf.obj (op U)`. The two types are equal, and
only the former carries the `Module` structure that instance search finds. -/
theorem exists_germAddHom_eq (M : PresheafOfModules.{u} (R ⋙ forget₂ CommRingCat RingCat))
    {x : ↥X} (m : ↑(TopCat.Presheaf.stalk M.presheaf x)) :
    ∃ (U : Opens ↥X) (hx : x ∈ U) (s : M.obj (op U)), germAddHom M U hx s = m := by
  obtain ⟨U, hx, s, hs⟩ := TopCat.Presheaf.exists_germ_eq M.presheaf m
  exact ⟨U, hx, s, hs⟩

/-- The additive map induced on stalks by a morphism of presheaves of modules. -/
noncomputable def stalkAddHom (ψ : M ⟶ N) (x : ↥X) :
    ↑(TopCat.Presheaf.stalk M.presheaf x) →+ ↑(TopCat.Presheaf.stalk N.presheaf x) :=
  ((TopCat.Presheaf.stalkFunctor AddCommGrpCat.{u} x).map
    ((PresheafOfModules.toPresheaf _).map ψ)).hom

/-- The map induced on stalks sends the germ of a section `s` to the germ of `ψ s`. -/
theorem stalkAddHom_germAddHom (ψ : M ⟶ N) {x : ↥X} (U : Opens ↥X) (hx : x ∈ U)
    (s : M.obj (op U)) :
    stalkAddHom ψ x (germAddHom M U hx s) = germAddHom N U hx (ψ.app (op U) s) :=
  TopCat.Presheaf.stalkFunctor_map_germ_apply U x hx
    ((PresheafOfModules.toPresheaf _).map ψ) s

/-- The induced map on stalks is linear over the stalk of the sheaf of rings. The scalar crossing
goes through `Stacks.SheafOfModules.germAddHom_smul`, that is through
`PresheafOfModules.germ_smul` as a term, and never through `map_smul`. -/
theorem stalkAddHom_smul (ψ : M ⟶ N) (x : ↥X) (c : ↑(TopCat.Presheaf.stalk R x))
    (m : ↑(TopCat.Presheaf.stalk M.presheaf x)) :
    stalkAddHom ψ x (c • m) = c • stalkAddHom ψ x m := by
  obtain ⟨V, hV, a, rfl⟩ := TopCat.Presheaf.exists_germ_eq R c
  obtain ⟨U, hU, s, rfl⟩ := exists_germAddHom_eq M m
  have hW : x ∈ (U ⊓ V : Opens ↥X) := ⟨hU, hV⟩
  have ha : R.germ (U ⊓ V : Opens ↥X) x hW (R.map (homOfLE inf_le_right).op a) =
      R.germ V x hV a := R.germ_res_apply (homOfLE inf_le_right) x hW a
  have hs : germAddHom M (U ⊓ V : Opens ↥X) hW (resAddHom M (inf_le_left : U ⊓ V ≤ U) s) =
      germAddHom M U hU s := germAddHom_resAddHom M inf_le_left hW s
  rw [← ha, ← hs, ← germAddHom_smul, stalkAddHom_germAddHom, map_smul,
    germAddHom_smul, stalkAddHom_germAddHom]

/-- **The map induced on stalks by a morphism of presheaves of modules**, as a map of modules
over the stalk of the sheaf of commutative rings. -/
noncomputable def stalkLin (ψ : M ⟶ N) (x : ↥X) :
    ↑(TopCat.Presheaf.stalk M.presheaf x) →ₗ[↑(TopCat.Presheaf.stalk R x)]
      ↑(TopCat.Presheaf.stalk N.presheaf x) where
  toFun := stalkAddHom ψ x
  map_add' := map_add _
  map_smul' := stalkAddHom_smul ψ x

/-- The linear map induced on stalks sends the germ of a section `s` to the germ of `ψ s`. -/
theorem stalkLin_germAddHom (ψ : M ⟶ N) {x : ↥X} (U : Opens ↥X) (hx : x ∈ U)
    (s : M.obj (op U)) :
    stalkLin ψ x (germAddHom M U hx s) = germAddHom N U hx (ψ.app (op U) s) :=
  stalkAddHom_germAddHom ψ U hx s

end Stalks

/-! ### The Koszul differential of a sequence of global sections, at sections and at a stalk -/

section Free

variable {X : TopCat.{u}} {Osharp : Sheaf (Opens.grothendieckTopology ↥X) CommRingCat.{u}}
  {r : ℕ}

variable {A : SheafOfModules.TensorExteriorSymmetricAlgebras (Opens.grothendieckTopology ↥X)
    (koszulFreeSheaf Osharp r)}

variable {φ : koszulFreeSheaf Osharp r ⟶
    SheafOfModules.unit (toRingCat (Opens.grothendieckTopology ↥X) Osharp)}

variable (K : KoszulChainData.{u, u, u} A φ)

/-- **The alternating-sum formula on the exterior basis, at sections.** The differential of the
ordered exterior product of the tautological generators indexed by `i` is the alternating sum of
the scalars of those generators times the products with one factor dropped. -/
theorem dNat_exteriorBasisSection (n : ℕ) (U : Opens ↥X) (i : Fin (n + 1) → Fin r) :
    (K.dNat n).val.app (op U) (exteriorBasisSection A U (n + 1) i) =
      ∑ k : Fin (n + 1),
        ((-1 : (toRingCat (Opens.grothendieckTopology ↥X) Osharp).obj.obj (op U)) ^ (k : ℕ) *
            unitScalar φ (op U) ((SheafOfModules.freeSection (ULift.up (i k))).eval (op U))) •
          exteriorBasisSection A U n fun j => i (k.succAbove j) := by
  have hz : ∀ j : Fin (n + 1), (K.d 1).val.app (op U) (exteriorGen A U (i j)) =
      unitScalar φ (op U) ((SheafOfModules.freeSection (ULift.up (i j))).eval (op U)) •
        A.exterior.one.eval (op U) :=
    fun j => K.d_exteriorGenerator (op U) _
  refine Stacks.GradedAlgebra.incl_inj_of_proj (extTotal A) ?_
  rw [K.extIncl_dNat]
  refine Eq.trans (K.dTotal_incl_homogeneousProdLeft (op U) n _ _ hz) ?_
  conv_rhs => rw [← extInclLin_apply (A := A) (op U) ((n : ℕ) : ℤ), map_sum]
  exact Finset.sum_congr rfl fun k _ =>
    (map_smul (extInclLin (A := A) (op U) ((n : ℕ) : ℤ)) _ _).symm

variable (f : Fin r → Osharp.obj.obj (op (⊤ : Opens ↥X)))
  (hφ : ∀ k : Fin r,
    ((SheafOfModules.unit (toRingCat (Opens.grothendieckTopology ↥X) Osharp)).freeHomEquiv φ
      (ULift.up k)).val (op (⊤ : Opens ↥X)) = f k)

include hφ in
/-- The germ of the scalar attached to the `k`-th tautological generator is the germ of the
`k`-th member of the sequence. -/
theorem germ_unitScalar_freeSection {x : ↥X} (U : Opens ↥X) (hx : x ∈ U) (k : Fin r) :
    TopCat.Presheaf.germ Osharp.obj U x hx
        (unitScalar φ (op U) ((SheafOfModules.freeSection (ULift.up k)).eval (op U))) =
      TopCat.Presheaf.germ Osharp.obj (⊤ : Opens ↥X) x (Opens.mem_top x) (f k) := by
  have hres : unitScalar φ (op U) ((SheafOfModules.freeSection (ULift.up k)).eval (op U)) =
      Osharp.obj.map (homOfLE (le_top : U ≤ ⊤)).op (f k) := by
    rw [← hφ k]
    exact (PresheafOfModules.sections_property
      ((SheafOfModules.unit (toRingCat (Opens.grothendieckTopology ↥X) Osharp)).freeHomEquiv φ
        (ULift.up k)) (homOfLE (le_top : U ≤ ⊤)).op).symm
  rw [hres]
  exact TopCat.Presheaf.germ_res_apply Osharp.obj (homOfLE le_top) x hx (f k)

include hφ in
/-- **The germ of the differential of an exterior basis product is the ring-level Koszul
differential of the corresponding wedge of standard basis vectors.** -/
theorem exteriorKoszulStalkEquiv_germ_dNat (n : ℕ) {x : ↥X} (U : Opens ↥X) (hx : x ∈ U)
    (i : Fin (n + 1) → Fin r) :
    Stacks.SheafOfModules.exteriorKoszulStalkEquiv A n x
        (TopCat.Presheaf.germ (A.exteriorPower n).val.presheaf U x hx
          ((K.dNat n).val.app (op U) (exteriorBasisSection A U (n + 1) i))) =
      Koszul.d (Koszul.seqDual fun k =>
          TopCat.Presheaf.germ Osharp.obj (⊤ : Opens ↥X) x (Opens.mem_top x) (f k)) n
        (exteriorPower.ιMulti ↑(TopCat.Presheaf.stalk Osharp.obj x) (n + 1)
          fun j => Pi.single (i j) 1) := by
  rw [dNat_exteriorBasisSection K n U i, koszulD_ιMulti]
  refine Eq.trans (congrArg (Stacks.SheafOfModules.exteriorKoszulStalkEquiv A n x)
    (map_sum (Stacks.SheafOfModules.germAddHom (A.exteriorPower n).val U hx) _
      Finset.univ)) ?_
  rw [map_sum]
  refine Finset.sum_congr rfl fun k _ => ?_
  rw [Stacks.SheafOfModules.germAddHom_apply,
    Stacks.SheafOfModules.exteriorKoszulStalkEquiv_germ_smul_exteriorBasisSection A n U hx,
    Koszul.seqDual_single, map_mul, map_pow, map_neg, map_one,
    germ_unitScalar_freeSection f hφ U hx (i k)]

include hφ in
/-- **Differential compatibility at a stalk.** Under the comparison
`(⋀ⁿ(O♯ʳ))_x ≅ ⋀ⁿ_{O_x}((O_x)ʳ)` of Stacks Tag 01CH, the map induced on stalks by the Koszul
differential of `φ` is the ring-level Koszul differential of the sequence of germs of `f`. -/
theorem exteriorKoszulStalkEquiv_stalkLin (n : ℕ) (x : ↥X)
    (m : ↑(TopCat.Presheaf.stalk (A.exteriorPower (n + 1)).val.presheaf x)) :
    Stacks.SheafOfModules.exteriorKoszulStalkEquiv A n x (stalkLin (K.dNat n).val x m) =
      Koszul.d (Koszul.seqDual fun k =>
          TopCat.Presheaf.germ Osharp.obj (⊤ : Opens ↥X) x (Opens.mem_top x) (f k)) n
        (Stacks.SheafOfModules.exteriorKoszulStalkEquiv A (n + 1) x m) := by
  have key : (Stacks.SheafOfModules.exteriorKoszulStalkEquiv A n x).toLinearMap.comp
        ((stalkLin (K.dNat n).val x).comp
          (Stacks.SheafOfModules.exteriorKoszulStalkEquiv A (n + 1) x).symm.toLinearMap) =
      Koszul.d (Koszul.seqDual fun k =>
        TopCat.Presheaf.germ Osharp.obj (⊤ : Opens ↥X) x (Opens.mem_top x) (f k)) n := by
    refine Module.Basis.ext (wedgeBasis ↑(TopCat.Presheaf.stalk Osharp.obj x) r (n + 1))
      fun t => ?_
    have hb : (wedgeBasis ↑(TopCat.Presheaf.stalk Osharp.obj x) r (n + 1)) t =
        exteriorPower.ιMulti ↑(TopCat.Presheaf.stalk Osharp.obj x) (n + 1)
          fun j => Pi.single (wedgeIndex (n + 1) t j) 1 :=
      wedgeBasis_apply ↑(TopCat.Presheaf.stalk Osharp.obj x) r (n + 1) t
    have hsymm : (Stacks.SheafOfModules.exteriorKoszulStalkEquiv A (n + 1) x).symm
          (exteriorPower.ιMulti ↑(TopCat.Presheaf.stalk Osharp.obj x) (n + 1)
            fun j => Pi.single (wedgeIndex (n + 1) t j) 1) =
        TopCat.Presheaf.germ (A.exteriorPower (n + 1)).val.presheaf (⊤ : Opens ↥X) x
          (Opens.mem_top x)
          (exteriorBasisSection A (⊤ : Opens ↥X) (n + 1) (wedgeIndex (n + 1) t)) :=
      (LinearEquiv.symm_apply_eq _).2
        (Stacks.SheafOfModules.exteriorKoszulStalkEquiv_germ_exteriorBasisSection A (n + 1)
          (⊤ : Opens ↥X) (Opens.mem_top x) (wedgeIndex (n + 1) t)).symm
    simp only [LinearMap.comp_apply, LinearEquiv.coe_coe]
    rw [hb, hsymm]
    refine Eq.trans (congrArg (Stacks.SheafOfModules.exteriorKoszulStalkEquiv A n x)
      (stalkLin_germAddHom (K.dNat n).val (⊤ : Opens ↥X) (Opens.mem_top x)
        (exteriorBasisSection A (⊤ : Opens ↥X) (n + 1) (wedgeIndex (n + 1) t)))) ?_
    exact exteriorKoszulStalkEquiv_germ_dNat K f hφ n (⊤ : Opens ↥X) (Opens.mem_top x)
      (wedgeIndex (n + 1) t)
  have h := DFunLike.congr_fun key
    (Stacks.SheafOfModules.exteriorKoszulStalkEquiv A (n + 1) x m)
  simp only [LinearMap.comp_apply, LinearEquiv.coe_coe, LinearEquiv.symm_apply_apply] at h
  exact h

end Free

end Stacks.RegularSequence

end
