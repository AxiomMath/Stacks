module

public import Mathlib.LinearAlgebra.TensorAlgebra.ToTensorPower
public import StacksFrontier.Algebra.Category.ModuleCat.Sheaf.SectionwiseAlgebras
public import StacksFrontier.Algebra.Category.ModuleCat.Sheaf.TensorAlgebraConstruction
public import StacksFrontier.Algebra.Category.ModuleCat.Sheaf.TensorExteriorSymmetricAlgebras
public import StacksFrontier.LinearAlgebra.TensorAlgebra.SemilinearMap
public import StacksFrontier.LinearAlgebra.TensorAlgebra.ToTensorPowerRange

/-!
# Towards an inhabitant of the tensor-exterior-symmetric bundle

`SheafOfModules.TensorExteriorSymmetricAlgebras J F` (in
`StacksFrontier.Algebra.Category.ModuleCat.Sheaf.TensorExteriorSymmetricAlgebras`) bundles the three
graded algebras Stacks Section 17.21 attaches to a sheaf of modules `F`. Its tensor and exterior
halves are built, as sheafifications of sectionwise algebras, in
`StacksFrontier.Algebra.Category.ModuleCat.Sheaf.SectionwiseAlgebras`. This file supplies three more
of the inputs an inhabitant of that bundle needs:

1. **the symmetric sectionwise algebra** — the family `U ↦ Symⁿ_{O(U)}(F(U))` of
   `PresheafOfModules.symPow` made into a `Stacks.GradedAlgebra`, with its degree-one generator
   and the commutation of that generator, sheafified to
   `SheafOfModules.sectionwiseSymmetricAlgebra`; this is the symmetric analogue of the tensor and
   exterior algebras of `SectionwiseAlgebras`;
2. **the binary decomposition of the tensor algebra** — `TensorAlgebra.mulGradedPieceEquiv`, that
   multiplication `Tⁱ ⊗_R Tʲ → Tⁱ⁺ʲ` inside `TensorAlgebra R M` is an isomorphism, and
   `PresheafOfModules.tensorPowTensorIso`, the same sectionwise over a site. The latter is the
   `e2` hypothesis of `SheafOfModules.tensorPowerSheafifyIso`;
3. **the two low-degree identifications** — `TensorAlgebra.gradedPieceZeroEquiv` and
   `gradedPieceOneEquiv`, and the sectionwise `PresheafOfModules.tensorPowZeroIso` and
   `tensorPowOneIso`. The second of these gives the `e1` hypothesis of
   `tensorPowerSheafifyIso` outright.

It does **not** construct an inhabitant of the bundle; see the implementation notes for exactly
what is still missing.

## Main definitions

* `TensorAlgebra.toTensorPower` and `TensorAlgebra.gradedPieceEquiv`: **the degree-`n` piece of
  the tensor algebra is the `n`-th tensor power `⨂[R]^n M`.**
* `TensorAlgebra.mulGradedPieceEquiv` and `mulGradedPieceEquivOfEq`: **multiplication identifies
  `Tⁱ ⊗_R Tʲ` with `Tⁱ⁺ʲ`.**
* `TensorAlgebra.gradedPieceZeroEquiv` and `gradedPieceOneEquiv`: the degree-zero and degree-one
  pieces are the base ring and the module.
* `PresheafOfModules.tensorPowTensorIso`, `tensorPowZeroIso` and `tensorPowOneIso`: the three
  previous identifications, sectionwise over a site, as isomorphisms of presheaves of modules.
* `SheafOfModules.sheafifyTensorPowOneIso` and `SheafOfModules.tensorPowRecursionIso`: the `e1`
  and `e2` hypotheses of `SheafOfModules.tensorPowerSheafifyIso`, discharged for the family of
  sectionwise tensor powers.
* `PresheafOfModules.symPowGradedAlgebra`: **the sectionwise symmetric algebra of a presheaf of
  modules**, as an `ℕ`-graded algebra of presheaves of modules, with `symPowGen` its degree-one
  generator, `symPowMul` its multiplication and `symPowOne` its unit.
* `SheafOfModules.sectionwiseSymmetricAlgebra`: **the symmetric algebra of a sheaf of modules**,
  as a sheaf of graded algebras, with `sectionwiseSymmetricAlgebraGen` its degree-one generator.
* `SymPow.one_mem_symmetricPower`, `ι_mem_symmetricPower`, `mul_mem_symmetricPower`: the grading
  data of the symmetric algebra in the elementary form a sectionwise graded algebra needs.

## Main results

* `TensorAlgebra.mulGradedPieceEquiv_tmul` and `mulGradedPieceEquivOfEq_tmul`: the isomorphism
  `Tⁱ ⊗ Tʲ ≅ Tⁱ⁺ʲ` is multiplication, read on pure tensors. This is what pins it down.
* `SheafOfModules.pairwiseCommutes_sectionwiseSymmetricAlgebraGen`: the degree-one generator of
  the sheafified symmetric algebra commutes pairwise — the first component of
  `SheafOfModules.GradedAlgebra.IsSymmetricAlgebra`, and the analogue of
  `SheafOfModules.squareZero_sectionwiseExteriorAlgebraGen`.
* `SheafOfModules.sectionwiseSymmetricAlgebra_piece_eq_zero_of_neg`: the symmetric algebra is
  concentrated in nonnegative degrees. This is the `symmetricPiece_eq_zero_of_neg` field of
  `SheafOfModules.TensorExteriorSymmetricAlgebras`, discharged for this algebra.

## Implementation notes

**What is here and what is not.** This file does **not** construct an inhabitant of
`SheafOfModules.TensorExteriorSymmetricAlgebras`. Two things are still missing for that.

The first is the *presheaf-level universal property* that
`Stacks.GradedAlgebra.isUniversal_sheafify` consumes: for a sheaf of graded algebras `B` and a
degree-one generator `κ` of it, a unique `Stacks.GradedAlgebra.UnitalHom A (B.restrictScalars α)`
carrying the sectionwise generator to `κ` on unit images. Its algebraic content is
`TensorAlgebra.lift`, `ExteriorAlgebra.lift` and `SymmetricAlgebra.liftComm` into
`Stacks.GradedAlgebra.Total`, the ungraded realization of `B.restrictScalars α`, followed by the
projection `Stacks.GradedAlgebra.proj` onto a homogeneous component; uniqueness is
`Submodule.pow_induction_on_left'` on the degree-`n` piece. Nothing below is specialized in
anticipation of it.

The second is the degree-zero comparison
`(moduleSheafification J a).obj (PresheafOfModules.unit (O ⋙ forget₂ CommRingCat RingCat)) ≅
SheafOfModules.unit (toRingCat J Osharp)`, the `e0` hypothesis of
`SheafOfModules.tensorPowerSheafifyIso`. `PresheafOfModules.tensorPowZeroIso` below reduces it to
that statement about the *unit* presheaf, which is a statement about sheafification alone: the
sheafification of a presheaf of modules along a locally bijective morphism of presheaves of rings
carries the free presheaf of rank one to the free sheaf of rank one. The route is
`SheafOfModules.toSheaf`, which reflects isomorphisms, together with
`(presheafToSheaf J AddCommGrpCat).IsLocalization J.W` and
`GrothendieckTopology.W_iff_isLocallyBijective`.

**Why the degree of the symmetric commutation law is a variable.** `symPowMul_self_comm` is
stated for an arbitrary degree `i` rather than for the numeral `1`, even though `i = 1` is the
only case used. With the numeral in place the elaborator reconciles the two sides of the equation
by `isDefEq`, which unfolds the `Submodule` power `SymPow.symmetricPower (1 + 1)` and, through
it, the reducible quotient `SymmetricAlgebra` — Mathlib defines `SymmetricAlgebra R M` as an
`abbrev` for a `RingCon` quotient of `TensorAlgebra R M` — and does not terminate inside the
heartbeat limit. With `i` a variable the `Submodule` power cannot reduce and the statement
elaborates at once; instantiating `i := 1` at the point of use substitutes into an already
elaborated statement and costs nothing. No heartbeat limit is raised anywhere below.

**The retyping declarations.** As in
`StacksFrontier.Algebra.Category.ModuleCat.Sheaf.SectionwiseAlgebras`, every piece of data of the
symmetric sectionwise algebra is introduced through an auxiliary declaration whose type is
already spelled at `(symPow n F).obj X` rather than at
`SymPow.symmetricPower n (O(X)) (F(X))`: `symPowMulApp`, `symPowOneSection`, `symPowGenApp`,
`symPow_ext` and `symPowMulApp_coe`. The two types are definitionally equal, and the comparison
is cheap in a position where the expected type is given and ruinous where it is not, for the
reason just described. The tensor-algebra half of this file needs no such interposition.

**Universes.** In the symmetric half the ring universe `w` and the module universe are not
independent: `SymmetricAlgebra R M` for `R : Type w` and `M : Type a` lives in
`Type (max w a)`, so everything is stated for modules in `max w a`, exactly as
`PresheafOfModules.symPow` is. The same holds for the tensor-power half. The degree-zero
identification `tensorPowZeroIso` is stated with the module universe equal to `w`, which is
forced and not chosen: `PresheafOfModules.unit` of a presheaf of rings in universe `w` is a
presheaf of modules in universe `w`. In the purely algebraic half the universes of `R` and `M`
are independent.

**No `@[stacks]` tag.** Tag 0FQW is the definition of a sheaf of graded algebras, carried by
`SheafOfModules.GradedAlgebra`; Tag 01CG is the symmetric-power sheafification statement, which
is not proved here. Everything below is infrastructure for Section 17.21 rather than the content
of a tag.

## References

* [Stacks Project, Section 17.21](https://stacks.math.columbia.edu/tag/01CF)
* [Stacks Project, Tag 0FQW](https://stacks.math.columbia.edu/tag/0FQW)
* [Stacks Project, Tag 01CG](https://stacks.math.columbia.edu/tag/01CG)
-/

@[expose] public section

open CategoryTheory Opposite

open scoped TensorProduct DirectSum

universe v u a w

/-! ### The graded pieces of the tensor algebra are the tensor powers -/

namespace TensorAlgebra

section Pow

variable {R : Type*} [CommSemiring R] {M : Type*} [AddCommMonoid M] [Module R M]

/-- An element of the degree-`n` piece of the tensor algebra is sent by
`TensorAlgebra.toDirectSum` into the degree-`n` summand. -/
theorem toDirectSum_mem_of (n : ℕ) {x : TensorAlgebra R M} (hx : x ∈ gradedPiece R n M) :
    ∃ y : ⨂[R]^n M, toDirectSum x = DirectSum.of (fun k => ⨂[R]^k M) n y := by
  induction hx using Submodule.pow_induction_on_left' with
  | algebraMap r =>
      exact ⟨_, by rw [AlgHom.commutes, DirectSum.algebraMap_apply]⟩
  | add x y i _ _ ihx ihy =>
      obtain ⟨p, hp⟩ := ihx
      obtain ⟨q, hq⟩ := ihy
      exact ⟨p + q, by rw [map_add, hp, hq, map_add]⟩
  | mem_mul m hm i x _ ih =>
      obtain ⟨m₀, rfl⟩ := hm
      obtain ⟨q, hq⟩ := ih
      refine ⟨TensorPower.cast R M (Nat.add_comm 1 i)
        (TensorPower.mulEquiv ((PiTensorProduct.tprod R fun _ : Fin 1 => m₀) ⊗ₜ[R] q)), ?_⟩
      rw [map_mul, hq, toDirectSum_ι, DirectSum.of_mul_of]
      exact DirectSum.of_eq_of_gradedMonoid_eq
        (TensorPower.gradedMonoid_eq_of_cast (Nat.add_comm 1 i) rfl)

/-- A product of `n` elements of the form `ι R m` lies in the degree-`n` piece of the tensor
algebra. -/
theorem prod_ofFn_ι_mem (n : ℕ) (x : Fin n → M) :
    (List.ofFn fun i => ι R (x i)).prod ∈ gradedPiece R n M := by
  induction n with
  | zero => simp only [List.ofFn_zero, List.prod_nil]; exact one_mem_gradedPiece
  | succ n ih =>
      rw [List.ofFn_succ, List.prod_cons]
      have h := mul_mem_gradedPiece (ι_mem_gradedPiece (R := R) (x 0)) (ih fun i => x i.succ)
      rwa [Nat.add_comm 1 n] at h

/-- The image of the `n`-th tensor power in the tensor algebra lies in the degree-`n` piece. -/
theorem toTensorAlgebra_mem_gradedPiece (n : ℕ) (z : ⨂[R]^n M) :
    TensorPower.toTensorAlgebra z ∈ gradedPiece R n M := by
  induction z using PiTensorProduct.induction_on with
  | smul_tprod r f =>
      rw [map_smul, TensorPower.toTensorAlgebra_tprod, tprod_apply]
      exact Submodule.smul_mem _ r (prod_ofFn_ι_mem n f)
  | add x y hx hy => rw [map_add]; exact Submodule.add_mem _ hx hy

/-- The degree-`n` component of `TensorAlgebra.toDirectSum`. -/
noncomputable def toTensorPower (n : ℕ) : TensorAlgebra R M →ₗ[R] ⨂[R]^n M :=
  (DirectSum.component R ℕ (fun k => ⨂[R]^k M) n).comp toDirectSum.toLinearMap

/-- `TensorAlgebra.toTensorPower n x` is the degree-`n` component of `toDirectSum x`. -/
theorem toTensorPower_apply (n : ℕ) (x : TensorAlgebra R M) :
    toTensorPower n x =
      DirectSum.component R ℕ (fun k => ⨂[R]^k M) n (toDirectSum x) := rfl

/-- If `toDirectSum x` is concentrated in degree `n` with component `y`, then
`TensorAlgebra.toTensorPower n x = y`. -/
theorem toTensorPower_of (n : ℕ) (y : ⨂[R]^n M) {x : TensorAlgebra R M}
    (hx : toDirectSum x = DirectSum.of (fun k => ⨂[R]^k M) n y) : toTensorPower n x = y := by
  rw [toTensorPower_apply, hx, ← DirectSum.lof_eq_of R]
  exact DirectSum.component.lof_self (M := fun k => ⨂[R]^k M) R n y

/-- For `x` in the degree-`n` piece, `toDirectSum x` is the degree-`n` summand
`toTensorPower n x`. -/
theorem toDirectSum_eq_of (n : ℕ) {x : TensorAlgebra R M} (hx : x ∈ gradedPiece R n M) :
    toDirectSum x = DirectSum.of (fun k => ⨂[R]^k M) n (toTensorPower n x) := by
  obtain ⟨y, hy⟩ := toDirectSum_mem_of n hx
  rw [toTensorPower_of n y hy, hy]

/-- `TensorAlgebra.toTensorPower n` is a left inverse of `TensorPower.toTensorAlgebra` on the
`n`-th tensor power. -/
theorem toTensorPower_toTensorAlgebra (n : ℕ) (z : ⨂[R]^n M) :
    toTensorPower n (TensorPower.toTensorAlgebra z) = z := by
  induction z using PiTensorProduct.induction_on with
  | smul_tprod r f =>
      rw [map_smul, TensorPower.toTensorAlgebra_tprod, map_smul]
      exact congrArg (fun z => r • z)
        (toTensorPower_of n _ (toDirectSum_tensorPower_tprod f))
  | add x y hx hy => rw [map_add, map_add, hx, hy]

/-- On the degree-`n` piece of the tensor algebra, `TensorPower.toTensorAlgebra` is a left
inverse of `TensorAlgebra.toTensorPower n`. -/
theorem toTensorAlgebra_toTensorPower (n : ℕ) {x : TensorAlgebra R M}
    (hx : x ∈ gradedPiece R n M) :
    TensorPower.toTensorAlgebra (toTensorPower n x) = x := by
  rw [← ofDirectSum_of (toTensorPower n x), ← toDirectSum_eq_of n hx, ofDirectSum_toDirectSum]

/-- **The degree-`n` piece of the tensor algebra is the `n`-th tensor power.** The identification
is `TensorAlgebra.toDirectSum` in one direction and `TensorPower.toTensorAlgebra` in the other. -/
noncomputable def gradedPieceEquiv (n : ℕ) : gradedPiece R n M ≃ₗ[R] ⨂[R]^n M where
  toFun x := toTensorPower n (x : TensorAlgebra R M)
  map_add' _ _ := map_add (toTensorPower n) _ _
  map_smul' r _ := map_smul (toTensorPower n) r _
  invFun z := ⟨TensorPower.toTensorAlgebra z, toTensorAlgebra_mem_gradedPiece n z⟩
  left_inv x := Subtype.ext (toTensorAlgebra_toTensorPower n x.2)
  right_inv z := toTensorPower_toTensorAlgebra n z

/-- `TensorAlgebra.gradedPieceEquiv n` is `TensorAlgebra.toTensorPower n` on the underlying
element. -/
@[simp]
theorem gradedPieceEquiv_apply (n : ℕ) (x : gradedPiece R n M) :
    gradedPieceEquiv n x = toTensorPower n (x : TensorAlgebra R M) := rfl

/-- The inverse of `TensorAlgebra.gradedPieceEquiv n` is `TensorPower.toTensorAlgebra`. -/
@[simp]
theorem gradedPieceEquiv_symm_apply (n : ℕ) (z : ⨂[R]^n M) :
    ((gradedPieceEquiv (R := R) (M := M) n).symm z : TensorAlgebra R M) =
      TensorPower.toTensorAlgebra z := rfl

/-- The identification of the graded pieces with the tensor powers is multiplicative: it carries
the product in the tensor algebra to `TensorPower.mulEquiv`. -/
theorem gradedPieceEquiv_mul (i j : ℕ) (x : gradedPiece R i M) (y : gradedPiece R j M) :
    gradedPieceEquiv (i + j) ⟨(x : TensorAlgebra R M) * (y : TensorAlgebra R M),
        mul_mem_gradedPiece x.2 y.2⟩ =
      TensorPower.mulEquiv (gradedPieceEquiv i x ⊗ₜ[R] gradedPieceEquiv j y) := by
  refine toTensorPower_of (i + j) _ ?_
  rw [map_mul, toDirectSum_eq_of i x.2, toDirectSum_eq_of j y.2, DirectSum.of_mul_of]
  rfl

/-- **Multiplication in the tensor algebra identifies `Tⁱ ⊗ Tʲ` with `Tⁱ⁺ʲ`.** -/
noncomputable def mulGradedPieceEquiv (i j : ℕ) :
    gradedPiece R i M ⊗[R] gradedPiece R j M ≃ₗ[R] gradedPiece R (i + j) M :=
  (TensorProduct.congr (gradedPieceEquiv i) (gradedPieceEquiv j)).trans
    (TensorPower.mulEquiv.trans (gradedPieceEquiv (i + j)).symm)

/-- `TensorAlgebra.mulGradedPieceEquiv` sends `x ⊗ₜ y` to the product `x * y`. -/
@[simp]
theorem mulGradedPieceEquiv_tmul (i j : ℕ) (x : gradedPiece R i M) (y : gradedPiece R j M) :
    (mulGradedPieceEquiv i j (x ⊗ₜ[R] y) : TensorAlgebra R M) =
      (x : TensorAlgebra R M) * (y : TensorAlgebra R M) := by
  have h : TensorPower.mulEquiv (gradedPieceEquiv i x ⊗ₜ[R] gradedPieceEquiv j y) =
      gradedPieceEquiv (i + j) ⟨(x : TensorAlgebra R M) * (y : TensorAlgebra R M),
        mul_mem_gradedPiece x.2 y.2⟩ := (gradedPieceEquiv_mul i j x y).symm
  change ((gradedPieceEquiv (i + j)).symm
    (TensorPower.mulEquiv (gradedPieceEquiv i x ⊗ₜ[R] gradedPieceEquiv j y)) :
      TensorAlgebra R M) = _
  rw [h, LinearEquiv.symm_apply_apply]

/-- **The degree-zero piece of the tensor algebra is the base ring**, by injectivity of the
structure map. -/
noncomputable def gradedPieceZeroEquiv : R ≃ₗ[R] gradedPiece R 0 M :=
  (LinearEquiv.ofInjective (Algebra.linearMap R (TensorAlgebra R M))
      (algebraMap_leftInverse M).injective).trans
    (LinearEquiv.ofEq _ _ (by
      simp only [gradedPiece, pow_zero]
      exact (Submodule.one_eq_range (R := R) (A := TensorAlgebra R M)).symm))

/-- `TensorAlgebra.gradedPieceZeroEquiv` sends `r` to `algebraMap R _ r`. -/
@[simp]
theorem gradedPieceZeroEquiv_apply (r : R) :
    (gradedPieceZeroEquiv (M := M) r : TensorAlgebra R M) = algebraMap R _ r := rfl

/-- **The degree-one piece of the tensor algebra is the module**, by injectivity of `ι`. -/
noncomputable def gradedPieceOneEquiv : M ≃ₗ[R] gradedPiece R 1 M :=
  (LinearEquiv.ofInjective (ι R : M →ₗ[R] TensorAlgebra R M) ι_leftInverse.injective).trans
    (LinearEquiv.ofEq _ _ (pow_one _).symm)

/-- `TensorAlgebra.gradedPieceOneEquiv` sends `m` to `ι R m`. -/
@[simp]
theorem gradedPieceOneEquiv_apply (m : M) :
    (gradedPieceOneEquiv (R := R) m : TensorAlgebra R M) = ι R m := rfl

/-- `TensorAlgebra.mulGradedPieceEquiv` with the degree of the target given as a separate
parameter together with the equation fixing it. -/
noncomputable def mulGradedPieceEquivOfEq (i j k : ℕ) (h : i + j = k) :
    gradedPiece R i M ⊗[R] gradedPiece R j M ≃ₗ[R] gradedPiece R k M :=
  match k, h with
  | _, rfl => mulGradedPieceEquiv i j

/-- `TensorAlgebra.mulGradedPieceEquivOfEq` sends `x ⊗ₜ y` to the product `x * y`. -/
theorem mulGradedPieceEquivOfEq_tmul (i j k : ℕ) (h : i + j = k) (x : gradedPiece R i M)
    (y : gradedPiece R j M) :
    (mulGradedPieceEquivOfEq i j k h (x ⊗ₜ[R] y) : TensorAlgebra R M) =
      (x : TensorAlgebra R M) * (y : TensorAlgebra R M) := by
  subst h
  exact mulGradedPieceEquiv_tmul i j x y

end Pow

end TensorAlgebra

/-! ### The tensor-power recursion, sectionwise -/

namespace PresheafOfModules

section TensorPowRecursion

variable {C : Type u} [Category.{v} C] {O : Cᵒᵖ ⥤ CommRingCat.{w}}
  (F : PresheafOfModules.{max w a} (O ⋙ forget₂ _ RingCat))

/-- `TensorAlgebra.mulGradedPieceEquivOfEq` with its type spelled at the sections of
`PresheafOfModules.tensorPow` and of `PresheafOfModules.tensorObj`. -/
noncomputable def tensorPowMulEquivApp (i j k : ℕ) (h : i + j = k) (X : Cᵒᵖ) :
    ((tensorObj (tensorPow i F) (tensorPow j F)).obj X ≃ₗ[(O ⋙ forget₂ _ RingCat).obj X]
      (tensorPow k F).obj X) :=
  TensorAlgebra.mulGradedPieceEquivOfEq i j k h

/-- **Multiplication identifies the objectwise tensor product of two sectionwise tensor powers
with the sectionwise tensor power of the sum of the degrees.** -/
noncomputable def tensorPowTensorIso (i j k : ℕ) (h : i + j = k) :
    tensorObj (tensorPow i F) (tensorPow j F) ≅ tensorPow k F :=
  PresheafOfModules.isoMk (fun X => (tensorPowMulEquivApp F i j k h X).toModuleIso)
    fun {X Y} f => by
      refine ModuleCat.tensor_ext fun x y => ?_
      change tensorPowMulEquivApp F i j k h Y
          ((tensorObj (tensorPow i F) (tensorPow j F)).restrictₛₗ f (x ⊗ₜ y)) =
        (tensorPow k F).restrictₛₗ f (tensorPowMulEquivApp F i j k h X (x ⊗ₜ y))
      rw [tensorObj_restrictₛₗ_tmul]
      refine Subtype.ext ?_
      refine Eq.trans (TensorAlgebra.mulGradedPieceEquivOfEq_tmul i j k h _ _) ?_
      refine Eq.trans ?_ (congrArg
        (TensorAlgebra.mapₛₗ ((O ⋙ forget₂ _ RingCat).map f).hom (F.restrictₛₗ f))
        (TensorAlgebra.mulGradedPieceEquivOfEq_tmul i j k h
          (tensorPowSections i F X x) (tensorPowSections j F X y))).symm
      exact (map_mul _ _ _).symm

/-- `TensorAlgebra.gradedPieceOneEquiv` with its type spelled at the sections of
`PresheafOfModules.tensorPow`. -/
noncomputable def tensorPowOneApp (X : Cᵒᵖ) :
    F.obj X ≃ₗ[(O ⋙ forget₂ _ RingCat).obj X] (tensorPow 1 F).obj X :=
  TensorAlgebra.gradedPieceOneEquiv

/-- **The first sectionwise tensor power is the presheaf itself.** -/
noncomputable def tensorPowOneIso : F ≅ tensorPow 1 F :=
  PresheafOfModules.isoMk (fun X => (tensorPowOneApp F X).toModuleIso) fun {X Y} f => by
    refine ModuleCat.hom_ext (LinearMap.ext fun m => Subtype.ext ?_)
    exact (TensorAlgebra.mapₛₗ_ι ((O ⋙ forget₂ _ RingCat).map f).hom (F.restrictₛₗ f) m).symm

/-- The sectionwise tensor-power recursion `Tᵏ ≅ Tⁱ ⊗ Tʲ` for `i + j = k`, the inverse of
`PresheafOfModules.tensorPowTensorIso`. -/
noncomputable def tensorPowIsoTensor (i j k : ℕ) (h : i + j = k) :
    tensorPow k F ≅ tensorObj (tensorPow i F) (tensorPow j F) :=
  (tensorPowTensorIso F i j k h).symm

end TensorPowRecursion

section TensorPowZero

variable {C : Type u} [Category.{v} C] {O : Cᵒᵖ ⥤ CommRingCat.{w}}
  (F : PresheafOfModules.{w} (O ⋙ forget₂ _ RingCat))

/-- `TensorAlgebra.gradedPieceZeroEquiv` with its type spelled at the sections of
`PresheafOfModules.unit` and of `PresheafOfModules.tensorPow`. -/
noncomputable def tensorPowZeroApp (X : Cᵒᵖ) :
    (PresheafOfModules.unit (O ⋙ forget₂ _ RingCat)).obj X ≃ₗ[(O ⋙ forget₂ _ RingCat).obj X]
      (tensorPow 0 F).obj X :=
  TensorAlgebra.gradedPieceZeroEquiv

/-- **The zeroth sectionwise tensor power is the free presheaf of modules of rank one.** -/
noncomputable def tensorPowZeroIso :
    PresheafOfModules.unit (O ⋙ forget₂ _ RingCat) ≅ tensorPow 0 F :=
  PresheafOfModules.isoMk (fun X => (tensorPowZeroApp F X).toModuleIso) fun {X Y} f => by
    refine ModuleCat.hom_ext (LinearMap.ext fun r => Subtype.ext ?_)
    exact (TensorAlgebra.mapₛₗ_algebraMap ((O ⋙ forget₂ _ RingCat).map f).hom
      (F.restrictₛₗ f) r).symm

end TensorPowZero

end PresheafOfModules

/-! ### Grading data for the symmetric algebra -/

namespace SymPow

section Grading

variable {R : Type*} [CommRing R] {M : Type*} [AddCommGroup M] [Module R M]

/-- The unit of the symmetric algebra lies in the degree-zero symmetric power. -/
theorem one_mem_symmetricPower : (1 : SymmetricAlgebra R M) ∈ symmetricPower 0 R M := by
  have h : symmetricPower 0 R M = 1 := pow_zero _
  rw [h]
  exact Submodule.mem_one.2 ⟨1, map_one _⟩

/-- The image of `SymmetricAlgebra.ι` lies in the degree-one symmetric power. -/
theorem ι_mem_symmetricPower (m : M) :
    SymmetricAlgebra.ι R M m ∈ symmetricPower 1 R M := by
  have h : symmetricPower 1 R M = LinearMap.range (SymmetricAlgebra.ι R M) := pow_one _
  rw [h]
  exact LinearMap.mem_range_self _ m

/-- The product of elements of the symmetric powers of degrees `i` and `j` lies in the symmetric
power of degree `i + j`. -/
theorem mul_mem_symmetricPower {i j : ℕ} {x y : SymmetricAlgebra R M}
    (hx : x ∈ symmetricPower i R M) (hy : y ∈ symmetricPower j R M) :
    x * y ∈ symmetricPower (i + j) R M :=
  SymmetricAlgebra.symmetricPower_mul_symmetricPower_le R M i j (Submodule.mul_mem_mul hx hy)

end Grading

end SymPow

/-! ### The sectionwise symmetric algebra as a graded algebra of presheaves of modules -/

namespace PresheafOfModules

section SymPowAlgebra

variable {C : Type u} [Category.{v} C] {O : Cᵒᵖ ⥤ CommRingCat.{w}}
  (F : PresheafOfModules.{max w a} (O ⋙ forget₂ _ RingCat))

/-- The multiplication of the sectionwise symmetric algebra, on sections. -/
noncomputable def symPowMulSections (i j : ℕ) (X : Cᵒᵖ) :
    SymPow.symmetricPower i ((O ⋙ forget₂ _ RingCat).obj X) (F.obj X) →+
      SymPow.symmetricPower j ((O ⋙ forget₂ _ RingCat).obj X) (F.obj X) →+
        SymPow.symmetricPower (i + j) ((O ⋙ forget₂ _ RingCat).obj X) (F.obj X) where
  toFun x :=
    { toFun := fun y => ⟨(x : SymmetricAlgebra _ _) * (y : SymmetricAlgebra _ _),
        SymPow.mul_mem_symmetricPower x.2 y.2⟩
      map_zero' := Subtype.ext (by simp)
      map_add' := fun y y' => Subtype.ext (by simp [mul_add]) }
  map_zero' := AddMonoidHom.ext fun y => Subtype.ext (by simp)
  map_add' x x' := AddMonoidHom.ext fun y => Subtype.ext (by simp [add_mul])

/-- `PresheafOfModules.symPowMulSections` is the product in the symmetric algebra. -/
@[simp]
theorem symPowMulSections_coe (i j : ℕ) (X : Cᵒᵖ)
    (x : SymPow.symmetricPower i ((O ⋙ forget₂ _ RingCat).obj X) (F.obj X))
    (y : SymPow.symmetricPower j ((O ⋙ forget₂ _ RingCat).obj X) (F.obj X)) :
    (symPowMulSections F i j X x y :
      SymmetricAlgebra ((O ⋙ forget₂ _ RingCat).obj X) (F.obj X)) = x * y := rfl

/-- `PresheafOfModules.symPowMulSections` with its type spelled at the sections of `symPow`. -/
noncomputable def symPowMulApp (i j : ℕ) (X : Cᵒᵖ) :
    (symPow i F).obj X →+ (symPow j F).obj X →+ (symPow (i + j) F).obj X :=
  symPowMulSections F i j X

/-- Two local sections of a sectionwise symmetric power agree as soon as they do in the
symmetric algebra. -/
theorem symPow_ext {n : ℕ} {X : Cᵒᵖ} {x y : (symPow n F).obj X}
    (h : (symPowSections n F X x :
        SymmetricAlgebra ((O ⋙ forget₂ _ RingCat).obj X) (F.obj X)) =
      (symPowSections n F X y :
        SymmetricAlgebra ((O ⋙ forget₂ _ RingCat).obj X) (F.obj X))) :
    x = y := Subtype.ext h

/-- `PresheafOfModules.symPowMulApp` is the product in the symmetric algebra. -/
@[simp]
theorem symPowMulApp_coe (i j : ℕ) (X : Cᵒᵖ) (x : (symPow i F).obj X)
    (y : (symPow j F).obj X) :
    (symPowSections (i + j) F X (symPowMulApp F i j X x y) :
        SymmetricAlgebra ((O ⋙ forget₂ _ RingCat).obj X) (F.obj X)) =
      (symPowSections i F X x :
          SymmetricAlgebra ((O ⋙ forget₂ _ RingCat).obj X) (F.obj X)) *
        (symPowSections j F X y :
          SymmetricAlgebra ((O ⋙ forget₂ _ RingCat).obj X) (F.obj X)) := rfl

/-- Commutativity of the multiplication of the sectionwise symmetric algebra in two equal
degrees. -/
theorem symPowMulApp_self_comm (i : ℕ) (X : Cᵒᵖ) (x y : (symPow i F).obj X) :
    symPowMulApp F i i X x y = symPowMulApp F i i X y x := by
  refine symPow_ext F ?_
  rw [symPowMulApp_coe, symPowMulApp_coe]
  exact mul_comm _ _

/-- The multiplication of the sectionwise symmetric algebra. -/
noncomputable def symPowMul (i j : ℕ) :
    Stacks.BilinearMap (symPow i F) (symPow j F) (symPow (i + j) F) :=
  { app := symPowMulApp F i j
    map_smul_left := fun _ _ _ _ => Subtype.ext (smul_mul_assoc _ _ _)
    map_smul_right := fun _ _ _ _ => Subtype.ext (mul_smul_comm _ _ _)
    naturality := fun _ _ _ => Subtype.ext (map_mul _ _ _) }

/-- The unit of the sectionwise symmetric algebra over an object of the site, retyped. -/
noncomputable def symPowOneSection (X : Cᵒᵖ) : (symPow 0 F).obj X :=
  (⟨1, SymPow.one_mem_symmetricPower⟩ :
    SymPow.symmetricPower 0 ((O ⋙ forget₂ _ RingCat).obj X) (F.obj X))

/-- The unit of the sectionwise symmetric algebra. -/
noncomputable def symPowOne : (symPow 0 F).sections :=
  PresheafOfModules.sectionsMk (symPowOneSection F) fun {_ _} _ => Subtype.ext (map_one _)

/-- The symmetric analogue of `PresheafOfModules.heq_tensorPow`. -/
theorem heq_symPow {m n : ℕ} (hmn : m = n) {X : Cᵒᵖ}
    {x : (symPow m F).obj X} {y : (symPow n F).obj X}
    (h : (symPowSections m F X x :
        SymmetricAlgebra ((O ⋙ forget₂ _ RingCat).obj X) (F.obj X)) =
      (symPowSections n F X y :
        SymmetricAlgebra ((O ⋙ forget₂ _ RingCat).obj X) (F.obj X))) :
    HEq x y := by
  subst hmn
  exact heq_of_eq (Subtype.ext h)

/-- **The sectionwise symmetric algebra of a presheaf of modules**, as an `ℕ`-graded algebra of
presheaves of modules on the family of sectionwise symmetric powers. -/
noncomputable def symPowGradedAlgebra : Stacks.GradedAlgebra (fun n : ℕ => symPow n F) :=
  { mul := symPowMul F
    one := symPowOne F
    mul_assoc := fun i j k _ _ _ _ => heq_symPow F (Nat.add_assoc i j k) (mul_assoc _ _ _)
    one_mul := fun i _ _ => heq_symPow F (Nat.zero_add i) (one_mul _)
    mul_one := fun i _ _ => heq_symPow F (Nat.add_zero i) (mul_one _) }

/-- `SymmetricAlgebra.ι` with its codomain spelled at the sections of `symPow 1 F`, retyped. -/
noncomputable def symPowGenApp (X : Cᵒᵖ) :
    F.obj X →ₗ[(O ⋙ forget₂ _ RingCat).obj X] (symPow 1 F).obj X :=
  (SymmetricAlgebra.ι ((O ⋙ forget₂ _ RingCat).obj X) (F.obj X)).codRestrict
    (SymPow.symmetricPower 1 ((O ⋙ forget₂ _ RingCat).obj X) (F.obj X))
    (fun m => SymPow.ι_mem_symmetricPower m)

/-- The degree-one generator of the sectionwise symmetric algebra. -/
noncomputable def symPowGen : F ⟶ symPow 1 F where
  app X := ModuleCat.ofHom (symPowGenApp F X)
  naturality f := ModuleCat.hom_ext (LinearMap.ext fun m => Subtype.ext
    (SymmetricAlgebra.mapₛₗ_ι ((O ⋙ forget₂ _ RingCat).map f).hom (F.restrictₛₗ f) m).symm)

/-- `PresheafOfModules.symPowGen` sends a section `m` to `SymmetricAlgebra.ι _ _ m`. -/
@[simp]
theorem symPowGen_coe (X : Cᵒᵖ) (m : F.obj X) :
    (symPowSections 1 F X (PresheafOfModules.Hom.app (symPowGen F) X m) :
      SymmetricAlgebra ((O ⋙ forget₂ _ RingCat).obj X) (F.obj X)) =
      SymmetricAlgebra.ι _ _ m := rfl

/-- The multiplication of `PresheafOfModules.symPowGradedAlgebra` over `X` is
`PresheafOfModules.symPowMulApp`. -/
theorem symPowGradedAlgebra_mul_app (i j : ℕ) (X : Cᵒᵖ) :
    ((symPowGradedAlgebra F).mul i j).app X = symPowMulApp F i j X := rfl

/-- **The multiplication of the sectionwise symmetric algebra is commutative in two equal
degrees.** -/
theorem symPowMul_self_comm (i : ℕ) (X : Cᵒᵖ) (x y : (symPow i F).obj X) :
    ((symPowGradedAlgebra F).mul i i).app X x y =
      ((symPowGradedAlgebra F).mul i i).app X y x := by
  rw [symPowGradedAlgebra_mul_app]
  exact symPowMulApp_self_comm F i X x y

end SymPowAlgebra

end PresheafOfModules

/-! ### The sheafified sectionwise symmetric algebra -/

namespace SheafOfModules

section SymmetricSheafify

open CategoryTheory.Sheaf

variable {C : Type u} [Category.{v} C] (J : GrothendieckTopology C)
  [J.HasSheafCompose (forget₂ CommRingCat.{w} RingCat.{w})]
  {O : Cᵒᵖ ⥤ CommRingCat.{w}} {Osharp : Sheaf J CommRingCat.{w}} (a : O ⟶ Osharp.obj)
  [Presheaf.IsLocallyInjective J (toRingCatMap J a)]
  [Presheaf.IsLocallySurjective J (toRingCatMap J a)]
  [J.WEqualsLocallyBijective AddCommGrpCat.{w}] [HasWeakSheafify J AddCommGrpCat.{w}]
  (F : PresheafOfModules.{w} (O ⋙ forget₂ CommRingCat RingCat))

/-- **The symmetric algebra of a sheaf of modules, as a sheaf of graded algebras.** -/
noncomputable def sectionwiseSymmetricAlgebra : GradedAlgebra.{w, w} (toRingCat J Osharp) :=
  (PresheafOfModules.symPowGradedAlgebra F).extend.sheafify (toRingCatMap J a)

/-- The degree-one generator of `SheafOfModules.sectionwiseSymmetricAlgebra`. -/
noncomputable def sectionwiseSymmetricAlgebraGen :
    (PresheafOfModules.moduleSheafification J a).obj F ⟶
      (sectionwiseSymmetricAlgebra J a F).piece 1 :=
  (PresheafOfModules.symPowGradedAlgebra F).extend.sheafifyGen (toRingCatMap J a)
    (PresheafOfModules.symPowGen F)

/-- **The degree-one sections of the symmetric algebra commute pairwise.** -/
theorem pairwiseCommutes_sectionwiseSymmetricAlgebraGen :
    GradedAlgebra.PairwiseCommutes (sectionwiseSymmetricAlgebraGen J a F) :=
  (PresheafOfModules.symPowGradedAlgebra F).extend.pairwiseCommutes_sheafifyGen
    (toRingCatMap J a) (PresheafOfModules.symPowGen F)
    fun X _ _ => PresheafOfModules.symPowMul_self_comm F 1 X _ _

/-- **The symmetric algebra is concentrated in nonnegative degrees.** -/
theorem sectionwiseSymmetricAlgebra_piece_eq_zero_of_neg {n : ℤ} (hn : n < 0) (X : Cᵒᵖ)
    (x : ((sectionwiseSymmetricAlgebra J a F).piece n).val.obj X) : x = 0 :=
  (PresheafOfModules.symPowGradedAlgebra F).extend.sheafify_piece_eq_zero
    (toRingCatMap J a) n (fun Y m => Stacks.GradedAlgebra.extendFamily_section_eq_zero hn Y m) X x

end SymmetricSheafify

section TensorPowerHypotheses

open CategoryTheory.Sheaf

variable {C : Type u} [Category.{v} C] (J : GrothendieckTopology C)
  [J.HasSheafCompose (forget₂ CommRingCat.{w} RingCat.{w})]
  {O : Cᵒᵖ ⥤ CommRingCat.{w}} {Osharp : Sheaf J CommRingCat.{w}} (a : O ⟶ Osharp.obj)
  [Presheaf.IsLocallyInjective J (toRingCatMap J a)]
  [Presheaf.IsLocallySurjective J (toRingCatMap J a)]
  [J.WEqualsLocallyBijective AddCommGrpCat.{w}] [HasWeakSheafify J AddCommGrpCat.{w}]
  (F : PresheafOfModules.{w} (O ⋙ forget₂ CommRingCat RingCat))

/-- **The `e1` hypothesis of `SheafOfModules.tensorPowerSheafifyIso`** for the family of
sectionwise tensor powers: the sheafification of the first tensor power is the sheafification
of `F`. -/
noncomputable def sheafifyTensorPowOneIso :
    (PresheafOfModules.moduleSheafification J a).obj (PresheafOfModules.tensorPow 1 F) ≅
      (PresheafOfModules.moduleSheafification J a).obj F :=
  (PresheafOfModules.moduleSheafification J a).mapIso (PresheafOfModules.tensorPowOneIso F).symm

/-- **The `e2` hypothesis of `SheafOfModules.tensorPowerSheafifyIso`** for the family of
sectionwise tensor powers: the tensor-power recursion. -/
noncomputable def tensorPowRecursionIso (n : ℕ) :
    PresheafOfModules.tensorPow (n + 2) F ≅
      PresheafOfModules.tensorObj (PresheafOfModules.tensorPow 1 F)
        (PresheafOfModules.tensorPow (n + 1) F) :=
  PresheafOfModules.tensorPowIsoTensor F 1 (n + 1) (n + 2) (by omega)

end TensorPowerHypotheses

end SheafOfModules
